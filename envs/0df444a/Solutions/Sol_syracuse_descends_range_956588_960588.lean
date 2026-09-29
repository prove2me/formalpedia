-- Prove2me | solution 1 for syracuse_descends_range_956588_960588
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:01.108546+00:00
-- url     : https://prove2.me/submissions/b0453dec-ea7a-4984-ba98-fc5347a60d19

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


theorem B2424917 : Blo 956588 2424917 := bbase (se 8 (by rfl) ⟨14208, by rfl⟩ : syracuseStep 2424917 = 28417) (by norm_num)
theorem B1212509 : Blo 956588 1212509 := bbase (se 3 (by rfl) ⟨227345, by rfl⟩ : syracuseStep 1212509 = 454691) (by norm_num)
theorem B1212565 : Blo 956588 1212565 := bbase (se 6 (by rfl) ⟨28419, by rfl⟩ : syracuseStep 1212565 = 56839) (by norm_num)
theorem B1310957 : Blo 956588 1310957 := bbase (se 3 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 1310957 = 491609) (by norm_num)
theorem B1212661 : Blo 956588 1212661 := bbase (se 5 (by rfl) ⟨56843, by rfl⟩ : syracuseStep 1212661 = 113687) (by norm_num)
theorem B2588981 : Blo 956588 2588981 := bbase (se 5 (by rfl) ⟨121358, by rfl⟩ : syracuseStep 2588981 = 242717) (by norm_num)
theorem B2457973 : Blo 956588 2457973 := bbase (se 5 (by rfl) ⟨115217, by rfl⟩ : syracuseStep 2457973 = 230435) (by norm_num)
theorem B1212833 : Blo 956588 1212833 := bbase (se 2 (by rfl) ⟨454812, by rfl⟩ : syracuseStep 1212833 = 909625) (by norm_num)
theorem B2425261 : Blo 956588 2425261 := bbase (se 3 (by rfl) ⟨454736, by rfl⟩ : syracuseStep 2425261 = 909473) (by norm_num)
theorem B7274933 : Blo 956588 7274933 := bbase (se 5 (by rfl) ⟨341012, by rfl⟩ : syracuseStep 7274933 = 682025) (by norm_num)
theorem B4850117 : Blo 956588 4850117 := bbase (se 4 (by rfl) ⟨454698, by rfl⟩ : syracuseStep 4850117 = 909397) (by norm_num)
theorem B1212889 : Blo 956588 1212889 := bbase (se 2 (by rfl) ⟨454833, by rfl⟩ : syracuseStep 1212889 = 909667) (by norm_num)
theorem B2425373 : Blo 956588 2425373 := bbase (se 3 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 2425373 = 909515) (by norm_num)
theorem B1212985 : Blo 956588 1212985 := bbase (se 2 (by rfl) ⟨454869, by rfl⟩ : syracuseStep 1212985 = 909739) (by norm_num)
theorem B2589349 : Blo 956588 2589349 := bbase (se 4 (by rfl) ⟨242751, by rfl⟩ : syracuseStep 2589349 = 485503) (by norm_num)
theorem B2425565 : Blo 956588 2425565 := bbase (se 3 (by rfl) ⟨454793, by rfl⟩ : syracuseStep 2425565 = 909587) (by norm_num)
theorem B1213157 : Blo 956588 1213157 := bbase (se 4 (by rfl) ⟨113733, by rfl⟩ : syracuseStep 1213157 = 227467) (by norm_num)
theorem B1213213 : Blo 956588 1213213 := bbase (se 3 (by rfl) ⟨227477, by rfl⟩ : syracuseStep 1213213 = 454955) (by norm_num)
theorem B1213309 : Blo 956588 1213309 := bbase (se 3 (by rfl) ⟨227495, by rfl⟩ : syracuseStep 1213309 = 454991) (by norm_num)
theorem B1213481 : Blo 956588 1213481 := bbase (se 2 (by rfl) ⟨455055, by rfl⟩ : syracuseStep 1213481 = 910111) (by norm_num)
theorem B2425909 : Blo 956588 2425909 := bbase (se 5 (by rfl) ⟨113714, by rfl⟩ : syracuseStep 2425909 = 227429) (by norm_num)
theorem B1213537 : Blo 956588 1213537 := bbase (se 2 (by rfl) ⟨455076, by rfl⟩ : syracuseStep 1213537 = 910153) (by norm_num)
theorem B4097141 : Blo 956588 4097141 := bbase (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) (by norm_num)
theorem B2426021 : Blo 956588 2426021 := bbase (se 4 (by rfl) ⟨227439, by rfl⟩ : syracuseStep 2426021 = 454879) (by norm_num)
theorem B1213633 : Blo 956588 1213633 := bbase (se 2 (by rfl) ⟨455112, by rfl⟩ : syracuseStep 1213633 = 910225) (by norm_num)
theorem B7996757 : Blo 956588 7996757 := bbase (se 12 (by rfl) ⟨2928, by rfl⟩ : syracuseStep 7996757 = 5857) (by norm_num)
theorem B2426213 : Blo 956588 2426213 := bbase (se 4 (by rfl) ⟨227457, by rfl⟩ : syracuseStep 2426213 = 454915) (by norm_num)
theorem B1213805 : Blo 956588 1213805 := bbase (se 3 (by rfl) ⟨227588, by rfl⟩ : syracuseStep 1213805 = 455177) (by norm_num)
theorem B1213861 : Blo 956588 1213861 := bbase (se 4 (by rfl) ⟨113799, by rfl⟩ : syracuseStep 1213861 = 227599) (by norm_num)
theorem B3638789 : Blo 956588 3638789 := bbase (se 4 (by rfl) ⟨341136, by rfl⟩ : syracuseStep 3638789 = 682273) (by norm_num)
theorem B1213957 : Blo 956588 1213957 := bbase (se 4 (by rfl) ⟨113808, by rfl⟩ : syracuseStep 1213957 = 227617) (by norm_num)
theorem B1312405 : Blo 956588 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B1214129 : Blo 956588 1214129 := bbase (se 2 (by rfl) ⟨455298, by rfl⟩ : syracuseStep 1214129 = 910597) (by norm_num)
theorem B2426557 : Blo 956588 2426557 := bbase (se 3 (by rfl) ⟨454979, by rfl⟩ : syracuseStep 2426557 = 909959) (by norm_num)
theorem B4851413 : Blo 956588 4851413 := bbase (se 7 (by rfl) ⟨56852, by rfl⟩ : syracuseStep 4851413 = 113705) (by norm_num)
theorem B1214185 : Blo 956588 1214185 := bbase (se 2 (by rfl) ⟨455319, by rfl⟩ : syracuseStep 1214185 = 910639) (by norm_num)
theorem B1967885 : Blo 956588 1967885 := bbase (se 3 (by rfl) ⟨368978, by rfl⟩ : syracuseStep 1967885 = 737957) (by norm_num)
theorem B3639077 : Blo 956588 3639077 := bbase (se 4 (by rfl) ⟨341163, by rfl⟩ : syracuseStep 3639077 = 682327) (by norm_num)
theorem B2426669 : Blo 956588 2426669 := bbase (se 3 (by rfl) ⟨455000, by rfl⟩ : syracuseStep 2426669 = 910001) (by norm_num)
theorem B2590517 : Blo 956588 2590517 := bbase (se 5 (by rfl) ⟨121430, by rfl⟩ : syracuseStep 2590517 = 242861) (by norm_num)
theorem B5834549 : Blo 956588 5834549 := bbase (se 5 (by rfl) ⟨273494, by rfl⟩ : syracuseStep 5834549 = 546989) (by norm_num)
theorem B1214281 : Blo 956588 1214281 := bbase (se 2 (by rfl) ⟨455355, by rfl⟩ : syracuseStep 1214281 = 910711) (by norm_num)
theorem B2426861 : Blo 956588 2426861 := bbase (se 3 (by rfl) ⟨455036, by rfl⟩ : syracuseStep 2426861 = 910073) (by norm_num)
theorem B1214453 : Blo 956588 1214453 := bbase (se 5 (by rfl) ⟨56927, by rfl⟩ : syracuseStep 1214453 = 113855) (by norm_num)
theorem B1214509 : Blo 956588 1214509 := bbase (se 3 (by rfl) ⟨227720, by rfl⟩ : syracuseStep 1214509 = 455441) (by norm_num)
theorem B1214605 : Blo 956588 1214605 := bbase (se 3 (by rfl) ⟨227738, by rfl⟩ : syracuseStep 1214605 = 455477) (by norm_num)
theorem B1640749 : Blo 956588 1640749 := bbase (se 3 (by rfl) ⟨307640, by rfl⟩ : syracuseStep 1640749 = 615281) (by norm_num)
theorem B1214777 : Blo 956588 1214777 := bbase (se 2 (by rfl) ⟨455541, by rfl⟩ : syracuseStep 1214777 = 911083) (by norm_num)
theorem B2427205 : Blo 956588 2427205 := bbase (se 4 (by rfl) ⟨227550, by rfl⟩ : syracuseStep 2427205 = 455101) (by norm_num)
theorem B1149265 : Blo 956588 1149265 := bbase (se 2 (by rfl) ⟨430974, by rfl⟩ : syracuseStep 1149265 = 861949) (by norm_num)
theorem B1214833 : Blo 956588 1214833 := bbase (se 2 (by rfl) ⟨455562, by rfl⟩ : syracuseStep 1214833 = 911125) (by norm_num)
theorem B1149337 : Blo 956588 1149337 := bbase (se 2 (by rfl) ⟨431001, by rfl⟩ : syracuseStep 1149337 = 862003) (by norm_num)
theorem B2394541 : Blo 956588 2394541 := bbase (se 3 (by rfl) ⟨448976, by rfl⟩ : syracuseStep 2394541 = 897953) (by norm_num)
theorem B2427317 : Blo 956588 2427317 := bbase (se 5 (by rfl) ⟨113780, by rfl⟩ : syracuseStep 2427317 = 227561) (by norm_num)
theorem B1214929 : Blo 956588 1214929 := bbase (se 2 (by rfl) ⟨455598, by rfl⟩ : syracuseStep 1214929 = 911197) (by norm_num)
theorem B1149457 : Blo 956588 1149457 := bbase (se 2 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 1149457 = 862093) (by norm_num)
theorem B2427509 : Blo 956588 2427509 := bbase (se 5 (by rfl) ⟨113789, by rfl⟩ : syracuseStep 2427509 = 227579) (by norm_num)
theorem B1215101 : Blo 956588 1215101 := bbase (se 3 (by rfl) ⟨227831, by rfl⟩ : syracuseStep 1215101 = 455663) (by norm_num)
theorem B1215157 : Blo 956588 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B1215253 : Blo 956588 1215253 := bbase (se 6 (by rfl) ⟨28482, by rfl⟩ : syracuseStep 1215253 = 56965) (by norm_num)
theorem B4098917 : Blo 956588 4098917 := bbase (se 4 (by rfl) ⟨384273, by rfl⟩ : syracuseStep 4098917 = 768547) (by norm_num)
theorem B1149841 : Blo 956588 1149841 := bbase (se 2 (by rfl) ⟨431190, by rfl⟩ : syracuseStep 1149841 = 862381) (by norm_num)
theorem B1215425 : Blo 956588 1215425 := bbase (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) (by norm_num)
theorem B3640261 : Blo 956588 3640261 := bbase (se 4 (by rfl) ⟨341274, by rfl⟩ : syracuseStep 3640261 = 682549) (by norm_num)
theorem B2427853 : Blo 956588 2427853 := bbase (se 3 (by rfl) ⟨455222, by rfl⟩ : syracuseStep 2427853 = 910445) (by norm_num)
theorem B4852709 : Blo 956588 4852709 := bbase (se 4 (by rfl) ⟨454941, by rfl⟩ : syracuseStep 4852709 = 909883) (by norm_num)
theorem B2558965 : Blo 956588 2558965 := bbase (se 5 (by rfl) ⟨119951, by rfl⟩ : syracuseStep 2558965 = 239903) (by norm_num)
theorem B1215481 : Blo 956588 1215481 := bbase (se 2 (by rfl) ⟨455805, by rfl⟩ : syracuseStep 1215481 = 911611) (by norm_num)
theorem B2427965 : Blo 956588 2427965 := bbase (se 3 (by rfl) ⟨455243, by rfl⟩ : syracuseStep 2427965 = 910487) (by norm_num)
theorem B4099157 : Blo 956588 4099157 := bbase (se 8 (by rfl) ⟨24018, by rfl⟩ : syracuseStep 4099157 = 48037) (by norm_num)
theorem B1215577 : Blo 956588 1215577 := bbase (se 2 (by rfl) ⟨455841, by rfl⟩ : syracuseStep 1215577 = 911683) (by norm_num)
theorem B3640565 : Blo 956588 3640565 := bbase (se 5 (by rfl) ⟨170651, by rfl⟩ : syracuseStep 3640565 = 341303) (by norm_num)
theorem B2428157 : Blo 956588 2428157 := bbase (se 3 (by rfl) ⟨455279, by rfl⟩ : syracuseStep 2428157 = 910559) (by norm_num)
theorem B1051913 : Blo 956588 1051913 := bbase (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) (by norm_num)
theorem B4918805 : Blo 956588 4918805 := bbase (se 6 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 4918805 = 230569) (by norm_num)
theorem B1150529 : Blo 956588 1150529 := bbase (se 2 (by rfl) ⟨431448, by rfl⟩ : syracuseStep 1150529 = 862897) (by norm_num)
theorem B2428501 : Blo 956588 2428501 := bbase (se 8 (by rfl) ⟨14229, by rfl⟩ : syracuseStep 2428501 = 28459) (by norm_num)
theorem B2428613 : Blo 956588 2428613 := bbase (se 4 (by rfl) ⟨227682, by rfl⟩ : syracuseStep 2428613 = 455365) (by norm_num)
theorem B5181205 : Blo 956588 5181205 := bbase (se 6 (by rfl) ⟨121434, by rfl⟩ : syracuseStep 5181205 = 242869) (by norm_num)
theorem B1052461 : Blo 956588 1052461 := bbase (se 3 (by rfl) ⟨197336, by rfl⟩ : syracuseStep 1052461 = 394673) (by norm_num)
theorem B2428805 : Blo 956588 2428805 := bbase (se 4 (by rfl) ⟨227700, by rfl⟩ : syracuseStep 2428805 = 455401) (by norm_num)
theorem B11636693 : Blo 956588 11636693 := bbase (se 7 (by rfl) ⟨136367, by rfl⟩ : syracuseStep 11636693 = 272735) (by norm_num)
theorem B1151129 : Blo 956588 1151129 := bbase (se 2 (by rfl) ⟨431673, by rfl⟩ : syracuseStep 1151129 = 863347) (by norm_num)
theorem B2429149 : Blo 956588 2429149 := bbase (se 3 (by rfl) ⟨455465, by rfl⟩ : syracuseStep 2429149 = 910931) (by norm_num)
theorem B4854005 : Blo 956588 4854005 := bbase (se 5 (by rfl) ⟨227531, by rfl⟩ : syracuseStep 4854005 = 455063) (by norm_num)
theorem B3281141 : Blo 956588 3281141 := bbase (se 5 (by rfl) ⟨153803, by rfl⟩ : syracuseStep 3281141 = 307607) (by norm_num)
theorem B5902645 : Blo 956588 5902645 := bbase (se 5 (by rfl) ⟨276686, by rfl⟩ : syracuseStep 5902645 = 553373) (by norm_num)
theorem B2429261 : Blo 956588 2429261 := bbase (se 3 (by rfl) ⟨455486, by rfl⟩ : syracuseStep 2429261 = 910973) (by norm_num)
theorem B1151437 : Blo 956588 1151437 := bbase (se 3 (by rfl) ⟨215894, by rfl⟩ : syracuseStep 1151437 = 431789) (by norm_num)
theorem B2429453 : Blo 956588 2429453 := bbase (se 3 (by rfl) ⟨455522, by rfl⟩ : syracuseStep 2429453 = 911045) (by norm_num)
theorem B1151533 : Blo 956588 1151533 := bbase (se 3 (by rfl) ⟨215912, by rfl⟩ : syracuseStep 1151533 = 431825) (by norm_num)
theorem B1151581 : Blo 956588 1151581 := bbase (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) (by norm_num)
theorem B2429797 : Blo 956588 2429797 := bbase (se 4 (by rfl) ⟨227793, by rfl⟩ : syracuseStep 2429797 = 455587) (by norm_num)
theorem B1872821 : Blo 956588 1872821 := bbase (se 5 (by rfl) ⟨87788, by rfl⟩ : syracuseStep 1872821 = 175577) (by norm_num)
theorem B2429909 : Blo 956588 2429909 := bbase (se 7 (by rfl) ⟨28475, by rfl⟩ : syracuseStep 2429909 = 56951) (by norm_num)
theorem B2430101 : Blo 956588 2430101 := bbase (se 6 (by rfl) ⟨56955, by rfl⟩ : syracuseStep 2430101 = 113911) (by norm_num)
theorem B2725093 : Blo 956588 2725093 := bbase (se 4 (by rfl) ⟨255477, by rfl⟩ : syracuseStep 2725093 = 510955) (by norm_num)
theorem B3642677 : Blo 956588 3642677 := bbase (se 5 (by rfl) ⟨170750, by rfl⟩ : syracuseStep 3642677 = 341501) (by norm_num)
theorem B4101445 : Blo 956588 4101445 := bbase (se 4 (by rfl) ⟨384510, by rfl⟩ : syracuseStep 4101445 = 769021) (by norm_num)
theorem B4920725 : Blo 956588 4920725 := bbase (se 6 (by rfl) ⟨115329, by rfl⟩ : syracuseStep 4920725 = 230659) (by norm_num)
theorem B1480117 : Blo 956588 1480117 := bbase (se 5 (by rfl) ⟨69380, by rfl⟩ : syracuseStep 1480117 = 138761) (by norm_num)
theorem B2430445 : Blo 956588 2430445 := bbase (se 3 (by rfl) ⟨455708, by rfl⟩ : syracuseStep 2430445 = 911417) (by norm_num)
theorem B4855301 : Blo 956588 4855301 := bbase (se 4 (by rfl) ⟨455184, by rfl⟩ : syracuseStep 4855301 = 910369) (by norm_num)
theorem B3642965 : Blo 956588 3642965 := bbase (se 8 (by rfl) ⟨21345, by rfl⟩ : syracuseStep 3642965 = 42691) (by norm_num)
theorem B2430557 : Blo 956588 2430557 := bbase (se 3 (by rfl) ⟨455729, by rfl⟩ : syracuseStep 2430557 = 911459) (by norm_num)
theorem B3282565 : Blo 956588 3282565 := bbase (se 4 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 3282565 = 615481) (by norm_num)
theorem B1021577 : Blo 956588 1021577 := bbase (se 2 (by rfl) ⟨383091, by rfl⟩ : syracuseStep 1021577 = 766183) (by norm_num)
theorem B1152797 : Blo 956588 1152797 := bbase (se 3 (by rfl) ⟨216149, by rfl⟩ : syracuseStep 1152797 = 432299) (by norm_num)
theorem B2430749 : Blo 956588 2430749 := bbase (se 3 (by rfl) ⟨455765, by rfl⟩ : syracuseStep 2430749 = 911531) (by norm_num)
theorem B1021825 : Blo 956588 1021825 := bbase (se 2 (by rfl) ⟨383184, by rfl⟩ : syracuseStep 1021825 = 766369) (by norm_num)
theorem B1152965 : Blo 956588 1152965 := bbase (se 4 (by rfl) ⟨108090, by rfl⟩ : syracuseStep 1152965 = 216181) (by norm_num)
theorem B2431093 : Blo 956588 2431093 := bbase (se 5 (by rfl) ⟨113957, by rfl⟩ : syracuseStep 2431093 = 227915) (by norm_num)
theorem B2431205 : Blo 956588 2431205 := bbase (se 4 (by rfl) ⟨227925, by rfl⟩ : syracuseStep 2431205 = 455851) (by norm_num)
theorem B1153273 : Blo 956588 1153273 := bbase (se 2 (by rfl) ⟨432477, by rfl⟩ : syracuseStep 1153273 = 864955) (by norm_num)
theorem B1022269 : Blo 956588 1022269 := bbase (se 3 (by rfl) ⟨191675, by rfl⟩ : syracuseStep 1022269 = 383351) (by norm_num)
theorem B17733973 : Blo 956588 17733973 := bbase (se 10 (by rfl) ⟨25977, by rfl⟩ : syracuseStep 17733973 = 51955) (by norm_num)
theorem B1022329 : Blo 956588 1022329 := bbase (se 2 (by rfl) ⟨383373, by rfl⟩ : syracuseStep 1022329 = 766747) (by norm_num)
theorem B2431397 : Blo 956588 2431397 := bbase (se 4 (by rfl) ⟨227943, by rfl⟩ : syracuseStep 2431397 = 455887) (by norm_num)
theorem B1153489 : Blo 956588 1153489 := bbase (se 2 (by rfl) ⟨432558, by rfl⟩ : syracuseStep 1153489 = 865117) (by norm_num)
theorem B2628053 : Blo 956588 2628053 := bbase (se 7 (by rfl) ⟨30797, by rfl⟩ : syracuseStep 2628053 = 61595) (by norm_num)
theorem B2300413 : Blo 956588 2300413 := bbase (se 3 (by rfl) ⟨431327, by rfl⟩ : syracuseStep 2300413 = 862655) (by norm_num)
theorem B1022645 : Blo 956588 1022645 := bbase (se 5 (by rfl) ⟨47936, by rfl⟩ : syracuseStep 1022645 = 95873) (by norm_num)
theorem B2726597 : Blo 956588 2726597 := bbase (se 4 (by rfl) ⟨255618, by rfl⟩ : syracuseStep 2726597 = 511237) (by norm_num)
theorem B3644149 : Blo 956588 3644149 := bbase (se 5 (by rfl) ⟨170819, by rfl⟩ : syracuseStep 3644149 = 341639) (by norm_num)
theorem B1153801 : Blo 956588 1153801 := bbase (se 2 (by rfl) ⟨432675, by rfl⟩ : syracuseStep 1153801 = 865351) (by norm_num)
theorem B4856597 : Blo 956588 4856597 := bbase (se 6 (by rfl) ⟨113826, by rfl⟩ : syracuseStep 4856597 = 227653) (by norm_num)
theorem B4102933 : Blo 956588 4102933 := bbase (se 6 (by rfl) ⟨96162, by rfl⟩ : syracuseStep 4102933 = 192325) (by norm_num)
theorem B4102949 : Blo 956588 4102949 := bbase (se 4 (by rfl) ⟨384651, by rfl⟩ : syracuseStep 4102949 = 769303) (by norm_num)
theorem B1940285 : Blo 956588 1940285 := bbase (se 3 (by rfl) ⟨363803, by rfl⟩ : syracuseStep 1940285 = 727607) (by norm_num)
theorem B1973077 : Blo 956588 1973077 := bbase (se 9 (by rfl) ⟨5780, by rfl⟩ : syracuseStep 1973077 = 11561) (by norm_num)
theorem B7773077 : Blo 956588 7773077 := bbase (se 6 (by rfl) ⟨182181, by rfl⟩ : syracuseStep 7773077 = 364363) (by norm_num)
theorem B6134741 : Blo 956588 6134741 := bbase (se 7 (by rfl) ⟨71891, by rfl⟩ : syracuseStep 6134741 = 143783) (by norm_num)
theorem B1842149 : Blo 956588 1842149 := bbase (se 4 (by rfl) ⟨172701, by rfl⟩ : syracuseStep 1842149 = 345403) (by norm_num)
theorem B3644453 : Blo 956588 3644453 := bbase (se 4 (by rfl) ⟨341667, by rfl⟩ : syracuseStep 3644453 = 683335) (by norm_num)
theorem B1023089 : Blo 956588 1023089 := bbase (se 2 (by rfl) ⟨383658, by rfl⟩ : syracuseStep 1023089 = 767317) (by norm_num)
theorem B1023149 : Blo 956588 1023149 := bbase (se 3 (by rfl) ⟨191840, by rfl⟩ : syracuseStep 1023149 = 383681) (by norm_num)
theorem B1023277 : Blo 956588 1023277 := bbase (se 3 (by rfl) ⟨191864, by rfl⟩ : syracuseStep 1023277 = 383729) (by norm_num)
theorem B4562453 : Blo 956588 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B3939877 : Blo 956588 3939877 := bbase (se 4 (by rfl) ⟨369363, by rfl⟩ : syracuseStep 3939877 = 738727) (by norm_num)
theorem B2301605 : Blo 956588 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B2334413 : Blo 956588 2334413 := bbase (se 3 (by rfl) ⟨437702, by rfl⟩ : syracuseStep 2334413 = 875405) (by norm_num)
theorem B1023721 : Blo 956588 1023721 := bbase (se 2 (by rfl) ⟨383895, by rfl⟩ : syracuseStep 1023721 = 767791) (by norm_num)
theorem B1023841 : Blo 956588 1023841 := bbase (se 2 (by rfl) ⟨383940, by rfl⟩ : syracuseStep 1023841 = 767881) (by norm_num)
theorem B2301797 : Blo 956588 2301797 := bbase (se 4 (by rfl) ⟨215793, by rfl⟩ : syracuseStep 2301797 = 431587) (by norm_num)
theorem B7282709 : Blo 956588 7282709 := bbase (se 6 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 7282709 = 341377) (by norm_num)
theorem B4857893 : Blo 956588 4857893 := bbase (se 4 (by rfl) ⟨455427, by rfl⟩ : syracuseStep 4857893 = 910855) (by norm_num)
theorem B3285029 : Blo 956588 3285029 := bbase (se 4 (by rfl) ⟨307971, by rfl⟩ : syracuseStep 3285029 = 615943) (by norm_num)
theorem B1024093 : Blo 956588 1024093 := bbase (se 3 (by rfl) ⟨192017, by rfl⟩ : syracuseStep 1024093 = 384035) (by norm_num)
theorem B1024097 : Blo 956588 1024097 := bbase (se 2 (by rfl) ⟨384036, by rfl⟩ : syracuseStep 1024097 = 768073) (by norm_num)
theorem B4923605 : Blo 956588 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B2728181 : Blo 956588 2728181 := bbase (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) (by norm_num)
theorem B1614269 : Blo 956588 1614269 := bbase (se 3 (by rfl) ⟨302675, by rfl⟩ : syracuseStep 1614269 = 605351) (by norm_num)
theorem B5448181 : Blo 956588 5448181 := bbase (se 5 (by rfl) ⟨255383, by rfl⟩ : syracuseStep 5448181 = 510767) (by norm_num)
theorem B1614397 : Blo 956588 1614397 := bbase (se 3 (by rfl) ⟨302699, by rfl⟩ : syracuseStep 1614397 = 605399) (by norm_num)
theorem B1614485 : Blo 956588 1614485 := bbase (se 6 (by rfl) ⟨37839, by rfl⟩ : syracuseStep 1614485 = 75679) (by norm_num)
theorem B1024661 : Blo 956588 1024661 := bbase (se 6 (by rfl) ⟨24015, by rfl⟩ : syracuseStep 1024661 = 48031) (by norm_num)
theorem B12264149 : Blo 956588 12264149 := bbase (se 7 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 12264149 = 287441) (by norm_num)
theorem B1614613 : Blo 956588 1614613 := bbase (se 6 (by rfl) ⟨37842, by rfl⟩ : syracuseStep 1614613 = 75685) (by norm_num)
theorem B1024849 : Blo 956588 1024849 := bbase (se 2 (by rfl) ⟨384318, by rfl⟩ : syracuseStep 1024849 = 768637) (by norm_num)
theorem B1614701 : Blo 956588 1614701 := bbase (se 3 (by rfl) ⟨302756, by rfl⟩ : syracuseStep 1614701 = 605513) (by norm_num)
theorem B2728853 : Blo 956588 2728853 := bbase (se 6 (by rfl) ⟨63957, by rfl⟩ : syracuseStep 2728853 = 127915) (by norm_num)
theorem B1614829 : Blo 956588 1614829 := bbase (se 3 (by rfl) ⟨302780, by rfl⟩ : syracuseStep 1614829 = 605561) (by norm_num)
theorem B1614917 : Blo 956588 1614917 := bbase (se 4 (by rfl) ⟨151398, by rfl⟩ : syracuseStep 1614917 = 302797) (by norm_num)
theorem B3646565 : Blo 956588 3646565 := bbase (se 4 (by rfl) ⟨341865, by rfl⟩ : syracuseStep 3646565 = 683731) (by norm_num)
theorem B12297365 : Blo 956588 12297365 := bbase (se 6 (by rfl) ⟨288219, by rfl⟩ : syracuseStep 12297365 = 576439) (by norm_num)
theorem B1615045 : Blo 956588 1615045 := bbase (se 4 (by rfl) ⟨151410, by rfl⟩ : syracuseStep 1615045 = 302821) (by norm_num)
theorem B2073853 : Blo 956588 2073853 := bbase (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) (by norm_num)
theorem B1615133 : Blo 956588 1615133 := bbase (se 3 (by rfl) ⟨302837, by rfl⟩ : syracuseStep 1615133 = 605675) (by norm_num)
theorem B4859189 : Blo 956588 4859189 := bbase (se 5 (by rfl) ⟨227774, by rfl⟩ : syracuseStep 4859189 = 455549) (by norm_num)
theorem B2729285 : Blo 956588 2729285 := bbase (se 4 (by rfl) ⟨255870, by rfl⟩ : syracuseStep 2729285 = 511741) (by norm_num)
theorem B3646853 : Blo 956588 3646853 := bbase (se 4 (by rfl) ⟨341892, by rfl⟩ : syracuseStep 3646853 = 683785) (by norm_num)
theorem B6235541 : Blo 956588 6235541 := bbase (se 6 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 6235541 = 292291) (by norm_num)
theorem B1615261 : Blo 956588 1615261 := bbase (se 3 (by rfl) ⟨302861, by rfl⟩ : syracuseStep 1615261 = 605723) (by norm_num)
theorem B1615349 : Blo 956588 1615349 := bbase (se 5 (by rfl) ⟨75719, by rfl⟩ : syracuseStep 1615349 = 151439) (by norm_num)
theorem B1615477 : Blo 956588 1615477 := bbase (se 5 (by rfl) ⟨75725, by rfl⟩ : syracuseStep 1615477 = 151451) (by norm_num)
theorem B1025669 : Blo 956588 1025669 := bbase (se 4 (by rfl) ⟨96156, by rfl⟩ : syracuseStep 1025669 = 192313) (by norm_num)
theorem B1615565 : Blo 956588 1615565 := bbase (se 3 (by rfl) ⟨302918, by rfl⟩ : syracuseStep 1615565 = 605837) (by norm_num)
theorem B1943309 : Blo 956588 1943309 := bbase (se 3 (by rfl) ⟨364370, by rfl⟩ : syracuseStep 1943309 = 728741) (by norm_num)
theorem B1615693 : Blo 956588 1615693 := bbase (se 3 (by rfl) ⟨302942, by rfl⟩ : syracuseStep 1615693 = 605885) (by norm_num)
theorem B10921877 : Blo 956588 10921877 := bbase (se 6 (by rfl) ⟨255981, by rfl⟩ : syracuseStep 10921877 = 511963) (by norm_num)
theorem B1615781 : Blo 956588 1615781 := bbase (se 4 (by rfl) ⟨151479, by rfl⟩ : syracuseStep 1615781 = 302959) (by norm_num)
theorem B1091497 : Blo 956588 1091497 := bbase (se 2 (by rfl) ⟨409311, by rfl⟩ : syracuseStep 1091497 = 818623) (by norm_num)
theorem B1091561 : Blo 956588 1091561 := bbase (se 2 (by rfl) ⟨409335, by rfl⟩ : syracuseStep 1091561 = 818671) (by norm_num)
theorem B9218069 : Blo 956588 9218069 := bbase (se 6 (by rfl) ⟨216048, by rfl⟩ : syracuseStep 9218069 = 432097) (by norm_num)
theorem B1615909 : Blo 956588 1615909 := bbase (se 4 (by rfl) ⟨151491, by rfl⟩ : syracuseStep 1615909 = 302983) (by norm_num)
theorem B2730037 : Blo 956588 2730037 := bbase (se 5 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 2730037 = 255941) (by norm_num)
theorem B2304085 : Blo 956588 2304085 := bbase (se 8 (by rfl) ⟨13500, by rfl⟩ : syracuseStep 2304085 = 27001) (by norm_num)
theorem B1615997 : Blo 956588 1615997 := bbase (se 3 (by rfl) ⟨302999, by rfl⟩ : syracuseStep 1615997 = 605999) (by norm_num)
theorem B1616125 : Blo 956588 1616125 := bbase (se 3 (by rfl) ⟨303023, by rfl⟩ : syracuseStep 1616125 = 606047) (by norm_num)
theorem B1943813 : Blo 956588 1943813 := bbase (se 4 (by rfl) ⟨182232, by rfl⟩ : syracuseStep 1943813 = 364465) (by norm_num)
theorem B1616213 : Blo 956588 1616213 := bbase (se 10 (by rfl) ⟨2367, by rfl⟩ : syracuseStep 1616213 = 4735) (by norm_num)
theorem B3451253 : Blo 956588 3451253 := bbase (se 5 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 3451253 = 323555) (by norm_num)
theorem B5450165 : Blo 956588 5450165 := bbase (se 5 (by rfl) ⟨255476, by rfl⟩ : syracuseStep 5450165 = 510953) (by norm_num)
theorem B1616341 : Blo 956588 1616341 := bbase (se 7 (by rfl) ⟨18941, by rfl⟩ : syracuseStep 1616341 = 37883) (by norm_num)
theorem B1616429 : Blo 956588 1616429 := bbase (se 3 (by rfl) ⟨303080, by rfl⟩ : syracuseStep 1616429 = 606161) (by norm_num)
theorem B4860485 : Blo 956588 4860485 := bbase (se 4 (by rfl) ⟨455670, by rfl⟩ : syracuseStep 4860485 = 911341) (by norm_num)
theorem B6564469 : Blo 956588 6564469 := bbase (se 5 (by rfl) ⟨307709, by rfl⟩ : syracuseStep 6564469 = 615419) (by norm_num)
theorem B1616557 : Blo 956588 1616557 := bbase (se 3 (by rfl) ⟨303104, by rfl⟩ : syracuseStep 1616557 = 606209) (by norm_num)
theorem B2304749 : Blo 956588 2304749 := bbase (se 3 (by rfl) ⟨432140, by rfl⟩ : syracuseStep 2304749 = 864281) (by norm_num)
theorem B1616645 : Blo 956588 1616645 := bbase (se 4 (by rfl) ⟨151560, by rfl⟩ : syracuseStep 1616645 = 303121) (by norm_num)
theorem B1944445 : Blo 956588 1944445 := bbase (se 3 (by rfl) ⟨364583, by rfl⟩ : syracuseStep 1944445 = 729167) (by norm_num)
theorem B1616773 : Blo 956588 1616773 := bbase (se 4 (by rfl) ⟨151572, by rfl⟩ : syracuseStep 1616773 = 303145) (by norm_num)
theorem B1682317 : Blo 956588 1682317 := bbase (se 3 (by rfl) ⟨315434, by rfl⟩ : syracuseStep 1682317 = 630869) (by norm_num)
theorem B1616861 : Blo 956588 1616861 := bbase (se 3 (by rfl) ⟨303161, by rfl⟩ : syracuseStep 1616861 = 606323) (by norm_num)
theorem B1616989 : Blo 956588 1616989 := bbase (se 3 (by rfl) ⟨303185, by rfl⟩ : syracuseStep 1616989 = 606371) (by norm_num)
theorem B1846381 : Blo 956588 1846381 := bbase (se 3 (by rfl) ⟨346196, by rfl⟩ : syracuseStep 1846381 = 692393) (by norm_num)
theorem B1617077 : Blo 956588 1617077 := bbase (se 5 (by rfl) ⟨75800, by rfl⟩ : syracuseStep 1617077 = 151601) (by norm_num)
theorem B4598981 : Blo 956588 4598981 := bbase (se 4 (by rfl) ⟨431154, by rfl⟩ : syracuseStep 4598981 = 862309) (by norm_num)
theorem B3452165 : Blo 956588 3452165 := bbase (se 4 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 3452165 = 647281) (by norm_num)
theorem B1617205 : Blo 956588 1617205 := bbase (se 5 (by rfl) ⟨75806, by rfl⟩ : syracuseStep 1617205 = 151613) (by norm_num)
theorem B1944965 : Blo 956588 1944965 := bbase (se 4 (by rfl) ⟨182340, by rfl⟩ : syracuseStep 1944965 = 364681) (by norm_num)
theorem B1617293 : Blo 956588 1617293 := bbase (se 3 (by rfl) ⟨303242, by rfl⟩ : syracuseStep 1617293 = 606485) (by norm_num)
theorem B1617421 : Blo 956588 1617421 := bbase (se 3 (by rfl) ⟨303266, by rfl⟩ : syracuseStep 1617421 = 606533) (by norm_num)
theorem B1617509 : Blo 956588 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B1748645 : Blo 956588 1748645 := bbase (se 4 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 1748645 = 327871) (by norm_num)
theorem B1617637 : Blo 956588 1617637 := bbase (se 4 (by rfl) ⟨151653, by rfl⟩ : syracuseStep 1617637 = 303307) (by norm_num)
theorem B2043701 : Blo 956588 2043701 := bbase (se 5 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 2043701 = 191597) (by norm_num)
theorem B1617725 : Blo 956588 1617725 := bbase (se 3 (by rfl) ⟨303323, by rfl⟩ : syracuseStep 1617725 = 606647) (by norm_num)
theorem B4861781 : Blo 956588 4861781 := bbase (se 9 (by rfl) ⟨14243, by rfl⟩ : syracuseStep 4861781 = 28487) (by norm_num)
theorem B1617853 : Blo 956588 1617853 := bbase (se 3 (by rfl) ⟨303347, by rfl⟩ : syracuseStep 1617853 = 606695) (by norm_num)
theorem B1617941 : Blo 956588 1617941 := bbase (se 6 (by rfl) ⟨37920, by rfl⟩ : syracuseStep 1617941 = 75841) (by norm_num)
theorem B2043949 : Blo 956588 2043949 := bbase (se 3 (by rfl) ⟨383240, by rfl⟩ : syracuseStep 2043949 = 766481) (by norm_num)
theorem B2306141 : Blo 956588 2306141 := bbase (se 3 (by rfl) ⟨432401, by rfl⟩ : syracuseStep 2306141 = 864803) (by norm_num)
theorem B1618069 : Blo 956588 1618069 := bbase (se 6 (by rfl) ⟨37923, by rfl⟩ : syracuseStep 1618069 = 75847) (by norm_num)
theorem B2306237 : Blo 956588 2306237 := bbase (se 3 (by rfl) ⟨432419, by rfl⟩ : syracuseStep 2306237 = 864839) (by norm_num)
theorem B1618157 : Blo 956588 1618157 := bbase (se 3 (by rfl) ⟨303404, by rfl⟩ : syracuseStep 1618157 = 606809) (by norm_num)
theorem B1093933 : Blo 956588 1093933 := bbase (se 3 (by rfl) ⟨205112, by rfl⟩ : syracuseStep 1093933 = 410225) (by norm_num)
theorem B1618285 : Blo 956588 1618285 := bbase (se 3 (by rfl) ⟨303428, by rfl⟩ : syracuseStep 1618285 = 606857) (by norm_num)
theorem B1618373 : Blo 956588 1618373 := bbase (se 4 (by rfl) ⟨151722, by rfl⟩ : syracuseStep 1618373 = 303445) (by norm_num)
theorem B2044453 : Blo 956588 2044453 := bbase (se 4 (by rfl) ⟨191667, by rfl⟩ : syracuseStep 2044453 = 383335) (by norm_num)
theorem B1618501 : Blo 956588 1618501 := bbase (se 4 (by rfl) ⟨151734, by rfl⟩ : syracuseStep 1618501 = 303469) (by norm_num)
theorem B5452373 : Blo 956588 5452373 := bbase (se 8 (by rfl) ⟨31947, by rfl⟩ : syracuseStep 5452373 = 63895) (by norm_num)
theorem B1618589 : Blo 956588 1618589 := bbase (se 3 (by rfl) ⟨303485, by rfl⟩ : syracuseStep 1618589 = 606971) (by norm_num)
theorem B8205077 : Blo 956588 8205077 := bbase (se 6 (by rfl) ⟨192306, by rfl⟩ : syracuseStep 8205077 = 384613) (by norm_num)
theorem B1618717 : Blo 956588 1618717 := bbase (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) (by norm_num)
theorem B2732885 : Blo 956588 2732885 := bbase (se 9 (by rfl) ⟨8006, by rfl⟩ : syracuseStep 2732885 = 16013) (by norm_num)
theorem B1618805 : Blo 956588 1618805 := bbase (se 5 (by rfl) ⟨75881, by rfl⟩ : syracuseStep 1618805 = 151763) (by norm_num)
theorem B1618933 : Blo 956588 1618933 := bbase (se 5 (by rfl) ⟨75887, by rfl⟩ : syracuseStep 1618933 = 151775) (by norm_num)
theorem B1553429 : Blo 956588 1553429 := bbase (se 6 (by rfl) ⟨36408, by rfl⟩ : syracuseStep 1553429 = 72817) (by norm_num)
theorem B1619021 : Blo 956588 1619021 := bbase (se 3 (by rfl) ⟨303566, by rfl⟩ : syracuseStep 1619021 = 607133) (by norm_num)
theorem B2765957 : Blo 956588 2765957 := bbase (se 4 (by rfl) ⟨259308, by rfl⟩ : syracuseStep 2765957 = 518617) (by norm_num)
theorem B1455293 : Blo 956588 1455293 := bbase (se 3 (by rfl) ⟨272867, by rfl⟩ : syracuseStep 1455293 = 545735) (by norm_num)
theorem B3880133 : Blo 956588 3880133 := bbase (se 4 (by rfl) ⟨363762, by rfl⟩ : syracuseStep 3880133 = 727525) (by norm_num)
theorem B1619149 : Blo 956588 1619149 := bbase (se 3 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 1619149 = 607181) (by norm_num)
theorem B1455341 : Blo 956588 1455341 := bbase (se 3 (by rfl) ⟨272876, by rfl⟩ : syracuseStep 1455341 = 545753) (by norm_num)
theorem B1455365 : Blo 956588 1455365 := bbase (se 4 (by rfl) ⟨136440, by rfl⟩ : syracuseStep 1455365 = 272881) (by norm_num)
theorem B1619237 : Blo 956588 1619237 := bbase (se 4 (by rfl) ⟨151803, by rfl⟩ : syracuseStep 1619237 = 303607) (by norm_num)
theorem B2667845 : Blo 956588 2667845 := bbase (se 4 (by rfl) ⟨250110, by rfl⟩ : syracuseStep 2667845 = 500221) (by norm_num)
theorem B2045341 : Blo 956588 2045341 := bbase (se 3 (by rfl) ⟨383501, by rfl⟩ : syracuseStep 2045341 = 767003) (by norm_num)
theorem B1619365 : Blo 956588 1619365 := bbase (se 4 (by rfl) ⟨151815, by rfl⟩ : syracuseStep 1619365 = 303631) (by norm_num)
theorem B1619453 : Blo 956588 1619453 := bbase (se 3 (by rfl) ⟨303647, by rfl⟩ : syracuseStep 1619453 = 607295) (by norm_num)
theorem B1619581 : Blo 956588 1619581 := bbase (se 3 (by rfl) ⟨303671, by rfl⟩ : syracuseStep 1619581 = 607343) (by norm_num)
theorem B1619669 : Blo 956588 1619669 := bbase (se 7 (by rfl) ⟨18980, by rfl⟩ : syracuseStep 1619669 = 37961) (by norm_num)
theorem B1816357 : Blo 956588 1816357 := bbase (se 4 (by rfl) ⟨170283, by rfl⟩ : syracuseStep 1816357 = 340567) (by norm_num)
theorem B1455949 : Blo 956588 1455949 := bbase (se 3 (by rfl) ⟨272990, by rfl⟩ : syracuseStep 1455949 = 545981) (by norm_num)
theorem B1619797 : Blo 956588 1619797 := bbase (se 9 (by rfl) ⟨4745, by rfl⟩ : syracuseStep 1619797 = 9491) (by norm_num)
theorem B2045837 : Blo 956588 2045837 := bbase (se 3 (by rfl) ⟨383594, by rfl⟩ : syracuseStep 2045837 = 767189) (by norm_num)
theorem B1619885 : Blo 956588 1619885 := bbase (se 3 (by rfl) ⟨303728, by rfl⟩ : syracuseStep 1619885 = 607457) (by norm_num)
theorem B1816501 : Blo 956588 1816501 := bbase (se 5 (by rfl) ⟨85148, by rfl⟩ : syracuseStep 1816501 = 170297) (by norm_num)
theorem B2734069 : Blo 956588 2734069 := bbase (se 5 (by rfl) ⟨128159, by rfl⟩ : syracuseStep 2734069 = 256319) (by norm_num)
theorem B1620013 : Blo 956588 1620013 := bbase (se 3 (by rfl) ⟨303752, by rfl⟩ : syracuseStep 1620013 = 607505) (by norm_num)
theorem B1554509 : Blo 956588 1554509 := bbase (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) (by norm_num)
theorem B1816661 : Blo 956588 1816661 := bbase (se 8 (by rfl) ⟨10644, by rfl⟩ : syracuseStep 1816661 = 21289) (by norm_num)
theorem B1620101 : Blo 956588 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B2734229 : Blo 956588 2734229 := bbase (se 6 (by rfl) ⟨64083, by rfl⟩ : syracuseStep 2734229 = 128167) (by norm_num)
theorem B1816805 : Blo 956588 1816805 := bbase (se 4 (by rfl) ⟨170325, by rfl⟩ : syracuseStep 1816805 = 340651) (by norm_num)
theorem B1620229 : Blo 956588 1620229 := bbase (se 4 (by rfl) ⟨151896, by rfl⟩ : syracuseStep 1620229 = 303793) (by norm_num)
theorem B1620317 : Blo 956588 1620317 := bbase (se 3 (by rfl) ⟨303809, by rfl⟩ : syracuseStep 1620317 = 607619) (by norm_num)
theorem B2734469 : Blo 956588 2734469 := bbase (se 4 (by rfl) ⟨256356, by rfl⟩ : syracuseStep 2734469 = 512713) (by norm_num)
theorem B5257685 : Blo 956588 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B1620445 : Blo 956588 1620445 := bbase (se 3 (by rfl) ⟨303833, by rfl⟩ : syracuseStep 1620445 = 607667) (by norm_num)
theorem B1817093 : Blo 956588 1817093 := bbase (se 4 (by rfl) ⟨170352, by rfl⟩ : syracuseStep 1817093 = 340705) (by norm_num)
theorem B1620533 : Blo 956588 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B2734661 : Blo 956588 2734661 := bbase (se 4 (by rfl) ⟨256374, by rfl⟩ : syracuseStep 2734661 = 512749) (by norm_num)
theorem B1817245 : Blo 956588 1817245 := bbase (se 3 (by rfl) ⟨340733, by rfl⟩ : syracuseStep 1817245 = 681467) (by norm_num)
theorem B2079389 : Blo 956588 2079389 := bbase (se 3 (by rfl) ⟨389885, by rfl⟩ : syracuseStep 2079389 = 779771) (by norm_num)
theorem B1620661 : Blo 956588 1620661 := bbase (se 5 (by rfl) ⟨75968, by rfl⟩ : syracuseStep 1620661 = 151937) (by norm_num)
theorem B2046725 : Blo 956588 2046725 := bbase (se 4 (by rfl) ⟨191880, by rfl⟩ : syracuseStep 2046725 = 383761) (by norm_num)
theorem B1620749 : Blo 956588 1620749 := bbase (se 3 (by rfl) ⟨303890, by rfl⟩ : syracuseStep 1620749 = 607781) (by norm_num)
theorem B27671381 : Blo 956588 27671381 := bbase (se 9 (by rfl) ⟨81068, by rfl⟩ : syracuseStep 27671381 = 162137) (by norm_num)
theorem B1457021 : Blo 956588 1457021 := bbase (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) (by norm_num)
theorem B2046845 : Blo 956588 2046845 := bbase (se 3 (by rfl) ⟨383783, by rfl⟩ : syracuseStep 2046845 = 767567) (by norm_num)
theorem B1620877 : Blo 956588 1620877 := bbase (se 3 (by rfl) ⟨303914, by rfl⟩ : syracuseStep 1620877 = 607829) (by norm_num)
theorem B2243477 : Blo 956588 2243477 := bbase (se 6 (by rfl) ⟨52581, by rfl⟩ : syracuseStep 2243477 = 105163) (by norm_num)
theorem B1817549 : Blo 956588 1817549 := bbase (se 3 (by rfl) ⟨340790, by rfl⟩ : syracuseStep 1817549 = 681581) (by norm_num)
theorem B1620965 : Blo 956588 1620965 := bbase (se 4 (by rfl) ⟨151965, by rfl⟩ : syracuseStep 1620965 = 303931) (by norm_num)
theorem B4602901 : Blo 956588 4602901 := bbase (se 6 (by rfl) ⟨107880, by rfl⟩ : syracuseStep 4602901 = 215761) (by norm_num)
theorem B4668661 : Blo 956588 4668661 := bbase (se 5 (by rfl) ⟨218843, by rfl⟩ : syracuseStep 4668661 = 437687) (by norm_num)
theorem B1555957 : Blo 956588 1555957 := bbase (se 5 (by rfl) ⟨72935, by rfl⟩ : syracuseStep 1555957 = 145871) (by norm_num)
theorem B2047477 : Blo 956588 2047477 := bbase (se 5 (by rfl) ⟨95975, by rfl⟩ : syracuseStep 2047477 = 191951) (by norm_num)
theorem B7290485 : Blo 956588 7290485 := bbase (se 5 (by rfl) ⟨341741, by rfl⟩ : syracuseStep 7290485 = 683483) (by norm_num)
theorem B1818301 : Blo 956588 1818301 := bbase (se 3 (by rfl) ⟨340931, by rfl⟩ : syracuseStep 1818301 = 681863) (by norm_num)
theorem B1228601 : Blo 956588 1228601 := bbase (se 2 (by rfl) ⟨460725, by rfl⟩ : syracuseStep 1228601 = 921451) (by norm_num)
theorem B1818445 : Blo 956588 1818445 := bbase (se 3 (by rfl) ⟨340958, by rfl⟩ : syracuseStep 1818445 = 681917) (by norm_num)
theorem B4440005 : Blo 956588 4440005 := bbase (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) (by norm_num)
theorem B1818605 : Blo 956588 1818605 := bbase (se 3 (by rfl) ⟨340988, by rfl⟩ : syracuseStep 1818605 = 681977) (by norm_num)
theorem B1818749 : Blo 956588 1818749 := bbase (se 3 (by rfl) ⟨341015, by rfl⟩ : syracuseStep 1818749 = 682031) (by norm_num)
theorem B3457237 : Blo 956588 3457237 := bbase (se 7 (by rfl) ⟨40514, by rfl⟩ : syracuseStep 3457237 = 81029) (by norm_num)
theorem B2048365 : Blo 956588 2048365 := bbase (se 3 (by rfl) ⟨384068, by rfl⟩ : syracuseStep 2048365 = 768137) (by norm_num)
theorem B3457397 : Blo 956588 3457397 := bbase (se 5 (by rfl) ⟨162065, by rfl⟩ : syracuseStep 3457397 = 324131) (by norm_num)
theorem B1229197 : Blo 956588 1229197 := bbase (se 3 (by rfl) ⟨230474, by rfl⟩ : syracuseStep 1229197 = 460949) (by norm_num)
theorem B1819037 : Blo 956588 1819037 := bbase (se 3 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 1819037 = 682139) (by norm_num)
theorem B2048485 : Blo 956588 2048485 := bbase (se 4 (by rfl) ⟨192045, by rfl⟩ : syracuseStep 2048485 = 384091) (by norm_num)
theorem B1819189 : Blo 956588 1819189 := bbase (se 5 (by rfl) ⟨85274, by rfl⟩ : syracuseStep 1819189 = 170549) (by norm_num)
theorem B1557053 : Blo 956588 1557053 := bbase (se 3 (by rfl) ⟨291947, by rfl⟩ : syracuseStep 1557053 = 583895) (by norm_num)
theorem B2048741 : Blo 956588 2048741 := bbase (se 4 (by rfl) ⟨192069, by rfl⟩ : syracuseStep 2048741 = 384139) (by norm_num)
theorem B8176373 : Blo 956588 8176373 := bbase (se 5 (by rfl) ⟨383267, by rfl⟩ : syracuseStep 8176373 = 766535) (by norm_num)
theorem B1819493 : Blo 956588 1819493 := bbase (se 4 (by rfl) ⟨170577, by rfl⟩ : syracuseStep 1819493 = 341155) (by norm_num)
theorem B15516629 : Blo 956588 15516629 := bbase (se 7 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 15516629 = 363671) (by norm_num)
theorem B1557469 : Blo 956588 1557469 := bbase (se 3 (by rfl) ⟨292025, by rfl⟩ : syracuseStep 1557469 = 584051) (by norm_num)
theorem B1459253 : Blo 956588 1459253 := bbase (se 5 (by rfl) ⟨68402, by rfl⟩ : syracuseStep 1459253 = 136805) (by norm_num)
theorem B3228821 : Blo 956588 3228821 := bbase (se 6 (by rfl) ⟨75675, by rfl⟩ : syracuseStep 3228821 = 151351) (by norm_num)
theorem B4670693 : Blo 956588 4670693 := bbase (se 4 (by rfl) ⟨437877, by rfl⟩ : syracuseStep 4670693 = 875755) (by norm_num)
theorem B1459453 : Blo 956588 1459453 := bbase (se 3 (by rfl) ⟨273647, by rfl⟩ : syracuseStep 1459453 = 547295) (by norm_num)
theorem B3065141 : Blo 956588 3065141 := bbase (se 5 (by rfl) ⟨143678, by rfl⟩ : syracuseStep 3065141 = 287357) (by norm_num)
theorem B3229253 : Blo 956588 3229253 := bbase (se 4 (by rfl) ⟨302742, by rfl⟩ : syracuseStep 3229253 = 605485) (by norm_num)
theorem B1820245 : Blo 956588 1820245 := bbase (se 8 (by rfl) ⟨10665, by rfl⟩ : syracuseStep 1820245 = 21331) (by norm_num)
theorem B2049629 : Blo 956588 2049629 := bbase (se 3 (by rfl) ⟨384305, by rfl⟩ : syracuseStep 2049629 = 768611) (by norm_num)
theorem B1296037 : Blo 956588 1296037 := bbase (se 4 (by rfl) ⟨121503, by rfl⟩ : syracuseStep 1296037 = 243007) (by norm_num)
theorem B1820389 : Blo 956588 1820389 := bbase (se 4 (by rfl) ⟨170661, by rfl⟩ : syracuseStep 1820389 = 341323) (by norm_num)
theorem B8406773 : Blo 956588 8406773 := bbase (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) (by norm_num)
theorem B2049869 : Blo 956588 2049869 := bbase (se 3 (by rfl) ⟨384350, by rfl⟩ : syracuseStep 2049869 = 768701) (by norm_num)
theorem B1820549 : Blo 956588 1820549 := bbase (se 4 (by rfl) ⟨170676, by rfl⟩ : syracuseStep 1820549 = 341353) (by norm_num)
theorem B3229685 : Blo 956588 3229685 := bbase (se 5 (by rfl) ⟨151391, by rfl⟩ : syracuseStep 3229685 = 302783) (by norm_num)
theorem B1820693 : Blo 956588 1820693 := bbase (se 6 (by rfl) ⟨42672, by rfl⟩ : syracuseStep 1820693 = 85345) (by norm_num)
theorem B1231085 : Blo 956588 1231085 := bbase (se 3 (by rfl) ⟨230828, by rfl⟩ : syracuseStep 1231085 = 461657) (by norm_num)
theorem B6310133 : Blo 956588 6310133 := bbase (se 5 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 6310133 = 591575) (by norm_num)
theorem B1362205 : Blo 956588 1362205 := bbase (se 3 (by rfl) ⟨255413, by rfl⟩ : syracuseStep 1362205 = 510827) (by norm_num)
theorem B1820981 : Blo 956588 1820981 := bbase (se 5 (by rfl) ⟨85358, by rfl⟩ : syracuseStep 1820981 = 170717) (by norm_num)
theorem B2050373 : Blo 956588 2050373 := bbase (se 4 (by rfl) ⟨192222, by rfl⟩ : syracuseStep 2050373 = 384445) (by norm_num)
theorem B2050381 : Blo 956588 2050381 := bbase (se 3 (by rfl) ⟨384446, by rfl⟩ : syracuseStep 2050381 = 768893) (by norm_num)
theorem B3230117 : Blo 956588 3230117 := bbase (se 4 (by rfl) ⟨302823, by rfl⟩ : syracuseStep 3230117 = 605647) (by norm_num)
theorem B1821133 : Blo 956588 1821133 := bbase (se 3 (by rfl) ⟨341462, by rfl⟩ : syracuseStep 1821133 = 682925) (by norm_num)
theorem B3459557 : Blo 956588 3459557 := bbase (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) (by norm_num)
theorem B3066437 : Blo 956588 3066437 := bbase (se 4 (by rfl) ⟨287478, by rfl⟩ : syracuseStep 3066437 = 574957) (by norm_num)
theorem B1231537 : Blo 956588 1231537 := bbase (se 2 (by rfl) ⟨461826, by rfl⟩ : syracuseStep 1231537 = 923653) (by norm_num)
theorem B7785173 : Blo 956588 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B1821437 : Blo 956588 1821437 := bbase (se 3 (by rfl) ⟨341519, by rfl⟩ : syracuseStep 1821437 = 683039) (by norm_num)
theorem B6146837 : Blo 956588 6146837 := bbase (se 6 (by rfl) ⟨144066, by rfl⟩ : syracuseStep 6146837 = 288133) (by norm_num)
theorem B1231697 : Blo 956588 1231697 := bbase (se 2 (by rfl) ⟨461886, by rfl⟩ : syracuseStep 1231697 = 923773) (by norm_num)
theorem B3230549 : Blo 956588 3230549 := bbase (se 9 (by rfl) ⟨9464, by rfl⟩ : syracuseStep 3230549 = 18929) (by norm_num)
theorem B4606901 : Blo 956588 4606901 := bbase (se 5 (by rfl) ⟨215948, by rfl⟩ : syracuseStep 4606901 = 431897) (by norm_num)
theorem B969721 : Blo 956588 969721 := bbase (se 2 (by rfl) ⟨363645, by rfl⟩ : syracuseStep 969721 = 727291) (by norm_num)
theorem B4148261 : Blo 956588 4148261 := bbase (se 4 (by rfl) ⟨388899, by rfl⟩ : syracuseStep 4148261 = 777799) (by norm_num)
theorem B1362997 : Blo 956588 1362997 := bbase (se 5 (by rfl) ⟨63890, by rfl⟩ : syracuseStep 1362997 = 127781) (by norm_num)
theorem B8735957 : Blo 956588 8735957 := bbase (se 7 (by rfl) ⟨102374, by rfl⟩ : syracuseStep 8735957 = 204749) (by norm_num)
theorem B4607189 : Blo 956588 4607189 := bbase (se 7 (by rfl) ⟨53990, by rfl⟩ : syracuseStep 4607189 = 107981) (by norm_num)
theorem B3230981 : Blo 956588 3230981 := bbase (se 4 (by rfl) ⟨302904, by rfl⟩ : syracuseStep 3230981 = 605809) (by norm_num)
theorem B1363333 : Blo 956588 1363333 := bbase (se 4 (by rfl) ⟨127812, by rfl⟩ : syracuseStep 1363333 = 255625) (by norm_num)
theorem B2051509 : Blo 956588 2051509 := bbase (se 5 (by rfl) ⟨96164, by rfl⟩ : syracuseStep 2051509 = 192329) (by norm_num)
theorem B1822189 : Blo 956588 1822189 := bbase (se 3 (by rfl) ⟨341660, by rfl⟩ : syracuseStep 1822189 = 683321) (by norm_num)
theorem B970309 : Blo 956588 970309 := bbase (se 4 (by rfl) ⟨90966, by rfl⟩ : syracuseStep 970309 = 181933) (by norm_num)
theorem B1363549 : Blo 956588 1363549 := bbase (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) (by norm_num)
theorem B1822333 : Blo 956588 1822333 := bbase (se 3 (by rfl) ⟨341687, by rfl⟩ : syracuseStep 1822333 = 683375) (by norm_num)
theorem B1166981 : Blo 956588 1166981 := bbase (se 4 (by rfl) ⟨109404, by rfl⟩ : syracuseStep 1166981 = 218809) (by norm_num)
theorem B3231413 : Blo 956588 3231413 := bbase (se 5 (by rfl) ⟨151472, by rfl⟩ : syracuseStep 3231413 = 302945) (by norm_num)
theorem B1036001 : Blo 956588 1036001 := bbase (se 2 (by rfl) ⟨388500, by rfl⟩ : syracuseStep 1036001 = 777001) (by norm_num)
theorem B1822493 : Blo 956588 1822493 := bbase (se 3 (by rfl) ⟨341717, by rfl⟩ : syracuseStep 1822493 = 683435) (by norm_num)
theorem B1724237 : Blo 956588 1724237 := bbase (se 3 (by rfl) ⟨323294, by rfl⟩ : syracuseStep 1724237 = 646589) (by norm_num)
theorem B1822637 : Blo 956588 1822637 := bbase (se 3 (by rfl) ⟨341744, by rfl⟩ : syracuseStep 1822637 = 683489) (by norm_num)
theorem B1363925 : Blo 956588 1363925 := bbase (se 7 (by rfl) ⟨15983, by rfl⟩ : syracuseStep 1363925 = 31967) (by norm_num)
theorem B3231845 : Blo 956588 3231845 := bbase (se 4 (by rfl) ⟨302985, by rfl⟩ : syracuseStep 3231845 = 605971) (by norm_num)
theorem B1822925 : Blo 956588 1822925 := bbase (se 3 (by rfl) ⟨341798, by rfl⟩ : syracuseStep 1822925 = 683597) (by norm_num)
theorem B3887461 : Blo 956588 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B1823077 : Blo 956588 1823077 := bbase (se 4 (by rfl) ⟨170913, by rfl⟩ : syracuseStep 1823077 = 341827) (by norm_num)
theorem B3068293 : Blo 956588 3068293 := bbase (se 4 (by rfl) ⟨287652, by rfl⟩ : syracuseStep 3068293 = 575305) (by norm_num)
theorem B971233 : Blo 956588 971233 := bbase (se 2 (by rfl) ⟨364212, by rfl⟩ : syracuseStep 971233 = 728425) (by norm_num)
theorem B3232277 : Blo 956588 3232277 := bbase (se 6 (by rfl) ⟨75756, by rfl⟩ : syracuseStep 3232277 = 151513) (by norm_num)
theorem B1823381 : Blo 956588 1823381 := bbase (se 6 (by rfl) ⟨42735, by rfl⟩ : syracuseStep 1823381 = 85471) (by norm_num)
theorem B3232709 : Blo 956588 3232709 := bbase (se 4 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 3232709 = 606133) (by norm_num)
theorem B2184509 : Blo 956588 2184509 := bbase (se 3 (by rfl) ⟨409595, by rfl⟩ : syracuseStep 2184509 = 819191) (by norm_num)
theorem B972109 : Blo 956588 972109 := bbase (se 3 (by rfl) ⟨182270, by rfl⟩ : syracuseStep 972109 = 364541) (by norm_num)
theorem B1365349 : Blo 956588 1365349 := bbase (se 4 (by rfl) ⟨128001, by rfl⟩ : syracuseStep 1365349 = 256003) (by norm_num)
theorem B3233141 : Blo 956588 3233141 := bbase (se 5 (by rfl) ⟨151553, by rfl⟩ : syracuseStep 3233141 = 303107) (by norm_num)
theorem B2053565 : Blo 956588 2053565 := bbase (se 3 (by rfl) ⟨385043, by rfl⟩ : syracuseStep 2053565 = 770087) (by norm_num)
theorem B2184653 : Blo 956588 2184653 := bbase (se 3 (by rfl) ⟨409622, by rfl⟩ : syracuseStep 2184653 = 819245) (by norm_num)
theorem B8410837 : Blo 956588 8410837 := bbase (se 7 (by rfl) ⟨98564, by rfl⟩ : syracuseStep 8410837 = 197129) (by norm_num)
theorem B3495653 : Blo 956588 3495653 := bbase (se 4 (by rfl) ⟨327717, by rfl⟩ : syracuseStep 3495653 = 655435) (by norm_num)
theorem B3233573 : Blo 956588 3233573 := bbase (se 4 (by rfl) ⟨303147, by rfl⟩ : syracuseStep 3233573 = 606295) (by norm_num)
theorem B972653 : Blo 956588 972653 := bbase (se 3 (by rfl) ⟨182372, by rfl⟩ : syracuseStep 972653 = 364745) (by norm_num)
theorem B972685 : Blo 956588 972685 := bbase (se 3 (by rfl) ⟨182378, by rfl⟩ : syracuseStep 972685 = 364757) (by norm_num)
theorem B2152349 : Blo 956588 2152349 := bbase (se 3 (by rfl) ⟨403565, by rfl⟩ : syracuseStep 2152349 = 807131) (by norm_num)
theorem B1365941 : Blo 956588 1365941 := bbase (se 5 (by rfl) ⟨64028, by rfl⟩ : syracuseStep 1365941 = 128057) (by norm_num)
theorem B2185157 : Blo 956588 2185157 := bbase (se 4 (by rfl) ⟨204858, by rfl⟩ : syracuseStep 2185157 = 409717) (by norm_num)
theorem B2152421 : Blo 956588 2152421 := bbase (se 4 (by rfl) ⟨201789, by rfl⟩ : syracuseStep 2152421 = 403579) (by norm_num)
theorem B1366021 : Blo 956588 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B2152493 : Blo 956588 2152493 := bbase (se 3 (by rfl) ⟨403592, by rfl⟩ : syracuseStep 2152493 = 807185) (by norm_num)
theorem B1169485 : Blo 956588 1169485 := bbase (se 3 (by rfl) ⟨219278, by rfl⟩ : syracuseStep 1169485 = 438557) (by norm_num)
theorem B2152565 : Blo 956588 2152565 := bbase (se 5 (by rfl) ⟨100901, by rfl⟩ : syracuseStep 2152565 = 201803) (by norm_num)
theorem B1366141 : Blo 956588 1366141 := bbase (se 3 (by rfl) ⟨256151, by rfl⟩ : syracuseStep 1366141 = 512303) (by norm_num)
theorem B2152637 : Blo 956588 2152637 := bbase (se 3 (by rfl) ⟨403619, by rfl⟩ : syracuseStep 2152637 = 807239) (by norm_num)
theorem B3234005 : Blo 956588 3234005 := bbase (se 7 (by rfl) ⟨37898, by rfl⟩ : syracuseStep 3234005 = 75797) (by norm_num)
theorem B1366237 : Blo 956588 1366237 := bbase (se 3 (by rfl) ⟨256169, by rfl⟩ : syracuseStep 1366237 = 512339) (by norm_num)
theorem B5462261 : Blo 956588 5462261 := bbase (se 5 (by rfl) ⟨256043, by rfl⟩ : syracuseStep 5462261 = 512087) (by norm_num)
theorem B1726717 : Blo 956588 1726717 := bbase (se 3 (by rfl) ⟨323759, by rfl⟩ : syracuseStep 1726717 = 647519) (by norm_num)
theorem B2152709 : Blo 956588 2152709 := bbase (se 4 (by rfl) ⟨201816, by rfl⟩ : syracuseStep 2152709 = 403633) (by norm_num)
theorem B2152781 : Blo 956588 2152781 := bbase (se 3 (by rfl) ⟨403646, by rfl⟩ : syracuseStep 2152781 = 807293) (by norm_num)
theorem B2152853 : Blo 956588 2152853 := bbase (se 6 (by rfl) ⟨50457, by rfl⟩ : syracuseStep 2152853 = 100915) (by norm_num)
theorem B2152925 : Blo 956588 2152925 := bbase (se 3 (by rfl) ⟨403673, by rfl⟩ : syracuseStep 2152925 = 807347) (by norm_num)
theorem B2152997 : Blo 956588 2152997 := bbase (se 4 (by rfl) ⟨201843, by rfl⟩ : syracuseStep 2152997 = 403687) (by norm_num)
theorem B2153069 : Blo 956588 2153069 := bbase (se 3 (by rfl) ⟨403700, by rfl⟩ : syracuseStep 2153069 = 807401) (by norm_num)
theorem B3234437 : Blo 956588 3234437 := bbase (se 4 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 3234437 = 606457) (by norm_num)
theorem B2153141 : Blo 956588 2153141 := bbase (se 5 (by rfl) ⟨100928, by rfl⟩ : syracuseStep 2153141 = 201857) (by norm_num)
theorem B1366733 : Blo 956588 1366733 := bbase (se 3 (by rfl) ⟨256262, by rfl⟩ : syracuseStep 1366733 = 512525) (by norm_num)
theorem B2153213 : Blo 956588 2153213 := bbase (se 3 (by rfl) ⟨403727, by rfl⟩ : syracuseStep 2153213 = 807455) (by norm_num)
theorem B2153285 : Blo 956588 2153285 := bbase (se 4 (by rfl) ⟨201870, by rfl⟩ : syracuseStep 2153285 = 403741) (by norm_num)
theorem B2153357 : Blo 956588 2153357 := bbase (se 3 (by rfl) ⟨403754, by rfl⟩ : syracuseStep 2153357 = 807509) (by norm_num)
theorem B5823413 : Blo 956588 5823413 := bbase (se 5 (by rfl) ⟨272972, by rfl⟩ : syracuseStep 5823413 = 545945) (by norm_num)
theorem B2153429 : Blo 956588 2153429 := bbase (se 7 (by rfl) ⟨25235, by rfl⟩ : syracuseStep 2153429 = 50471) (by norm_num)
theorem B2186261 : Blo 956588 2186261 := bbase (se 6 (by rfl) ⟨51240, by rfl⟩ : syracuseStep 2186261 = 102481) (by norm_num)
theorem B2153501 : Blo 956588 2153501 := bbase (se 3 (by rfl) ⟨403781, by rfl⟩ : syracuseStep 2153501 = 807563) (by norm_num)
theorem B3234869 : Blo 956588 3234869 := bbase (se 5 (by rfl) ⟨151634, by rfl⟩ : syracuseStep 3234869 = 303269) (by norm_num)
theorem B2153573 : Blo 956588 2153573 := bbase (se 4 (by rfl) ⟨201897, by rfl⟩ : syracuseStep 2153573 = 403795) (by norm_num)
theorem B2153645 : Blo 956588 2153645 := bbase (se 3 (by rfl) ⟨403808, by rfl⟩ : syracuseStep 2153645 = 807617) (by norm_num)
theorem B5823701 : Blo 956588 5823701 := bbase (se 7 (by rfl) ⟨68246, by rfl⟩ : syracuseStep 5823701 = 136493) (by norm_num)
theorem B2153717 : Blo 956588 2153717 := bbase (se 5 (by rfl) ⟨100955, by rfl⟩ : syracuseStep 2153717 = 201911) (by norm_num)
theorem B1367285 : Blo 956588 1367285 := bbase (se 5 (by rfl) ⟨64091, by rfl⟩ : syracuseStep 1367285 = 128183) (by norm_num)
theorem B4087093 : Blo 956588 4087093 := bbase (se 5 (by rfl) ⟨191582, by rfl⟩ : syracuseStep 4087093 = 383165) (by norm_num)
theorem B2153789 : Blo 956588 2153789 := bbase (se 3 (by rfl) ⟨403835, by rfl⟩ : syracuseStep 2153789 = 807671) (by norm_num)
theorem B1039697 : Blo 956588 1039697 := bbase (se 2 (by rfl) ⟨389886, by rfl⟩ : syracuseStep 1039697 = 779773) (by norm_num)
theorem B2153861 : Blo 956588 2153861 := bbase (se 4 (by rfl) ⟨201924, by rfl⟩ : syracuseStep 2153861 = 403849) (by norm_num)
theorem B2153933 : Blo 956588 2153933 := bbase (se 3 (by rfl) ⟨403862, by rfl⟩ : syracuseStep 2153933 = 807725) (by norm_num)
theorem B3235301 : Blo 956588 3235301 := bbase (se 4 (by rfl) ⟨303309, by rfl⟩ : syracuseStep 3235301 = 606619) (by norm_num)
theorem B2154005 : Blo 956588 2154005 := bbase (se 6 (by rfl) ⟨50484, by rfl⟩ : syracuseStep 2154005 = 100969) (by norm_num)
theorem B2154077 : Blo 956588 2154077 := bbase (se 3 (by rfl) ⟨403889, by rfl⟩ : syracuseStep 2154077 = 807779) (by norm_num)
theorem B2154149 : Blo 956588 2154149 := bbase (se 4 (by rfl) ⟨201951, by rfl⟩ : syracuseStep 2154149 = 403903) (by norm_num)
theorem B2154221 : Blo 956588 2154221 := bbase (se 3 (by rfl) ⟨403916, by rfl⟩ : syracuseStep 2154221 = 807833) (by norm_num)
theorem B2154293 : Blo 956588 2154293 := bbase (se 5 (by rfl) ⟨100982, by rfl⟩ : syracuseStep 2154293 = 201965) (by norm_num)
theorem B2154365 : Blo 956588 2154365 := bbase (se 3 (by rfl) ⟨403943, by rfl⟩ : syracuseStep 2154365 = 807887) (by norm_num)
theorem B4611973 : Blo 956588 4611973 := bbase (se 4 (by rfl) ⟨432372, by rfl⟩ : syracuseStep 4611973 = 864745) (by norm_num)
theorem B3235733 : Blo 956588 3235733 := bbase (se 6 (by rfl) ⟨75837, by rfl⟩ : syracuseStep 3235733 = 151675) (by norm_num)
theorem B2154437 : Blo 956588 2154437 := bbase (se 4 (by rfl) ⟨201978, by rfl⟩ : syracuseStep 2154437 = 403957) (by norm_num)
theorem B2154509 : Blo 956588 2154509 := bbase (se 3 (by rfl) ⟨403970, by rfl⟩ : syracuseStep 2154509 = 807941) (by norm_num)
theorem B2154581 : Blo 956588 2154581 := bbase (se 8 (by rfl) ⟨12624, by rfl⟩ : syracuseStep 2154581 = 25249) (by norm_num)
theorem B2154653 : Blo 956588 2154653 := bbase (se 3 (by rfl) ⟨403997, by rfl⟩ : syracuseStep 2154653 = 807995) (by norm_num)
theorem B2154725 : Blo 956588 2154725 := bbase (se 4 (by rfl) ⟨202005, by rfl⟩ : syracuseStep 2154725 = 404011) (by norm_num)
theorem B2154797 : Blo 956588 2154797 := bbase (se 3 (by rfl) ⟨404024, by rfl⟩ : syracuseStep 2154797 = 808049) (by norm_num)
theorem B3236165 : Blo 956588 3236165 := bbase (se 4 (by rfl) ⟨303390, by rfl⟩ : syracuseStep 3236165 = 606781) (by norm_num)
theorem B6906197 : Blo 956588 6906197 := bbase (se 10 (by rfl) ⟨10116, by rfl⟩ : syracuseStep 6906197 = 20233) (by norm_num)
theorem B2154869 : Blo 956588 2154869 := bbase (se 5 (by rfl) ⟨101009, by rfl⟩ : syracuseStep 2154869 = 202019) (by norm_num)
theorem B2154941 : Blo 956588 2154941 := bbase (se 3 (by rfl) ⟨404051, by rfl⟩ : syracuseStep 2154941 = 808103) (by norm_num)
theorem B3072485 : Blo 956588 3072485 := bbase (se 4 (by rfl) ⟨288045, by rfl⟩ : syracuseStep 3072485 = 576091) (by norm_num)
theorem B2155013 : Blo 956588 2155013 := bbase (se 4 (by rfl) ⟨202032, by rfl⟩ : syracuseStep 2155013 = 404065) (by norm_num)
theorem B2155085 : Blo 956588 2155085 := bbase (se 3 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 2155085 = 808157) (by norm_num)
theorem B2155157 : Blo 956588 2155157 := bbase (se 6 (by rfl) ⟨50511, by rfl⟩ : syracuseStep 2155157 = 101023) (by norm_num)
theorem B2155229 : Blo 956588 2155229 := bbase (se 3 (by rfl) ⟨404105, by rfl⟩ : syracuseStep 2155229 = 808211) (by norm_num)
theorem B3236597 : Blo 956588 3236597 := bbase (se 5 (by rfl) ⟨151715, by rfl⟩ : syracuseStep 3236597 = 303431) (by norm_num)
theorem B2155301 : Blo 956588 2155301 := bbase (se 4 (by rfl) ⟨202059, by rfl⟩ : syracuseStep 2155301 = 404119) (by norm_num)
theorem B7267157 : Blo 956588 7267157 := bbase (se 9 (by rfl) ⟨21290, by rfl⟩ : syracuseStep 7267157 = 42581) (by norm_num)
theorem B2909029 : Blo 956588 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B2155373 : Blo 956588 2155373 := bbase (se 3 (by rfl) ⟨404132, by rfl⟩ : syracuseStep 2155373 = 808265) (by norm_num)
theorem B2155445 : Blo 956588 2155445 := bbase (se 5 (by rfl) ⟨101036, by rfl⟩ : syracuseStep 2155445 = 202073) (by norm_num)
theorem B2909125 : Blo 956588 2909125 := bbase (se 4 (by rfl) ⟨272730, by rfl⟩ : syracuseStep 2909125 = 545461) (by norm_num)
theorem B2155517 : Blo 956588 2155517 := bbase (se 3 (by rfl) ⟨404159, by rfl⟩ : syracuseStep 2155517 = 808319) (by norm_num)
theorem B1532981 : Blo 956588 1532981 := bbase (se 5 (by rfl) ⟨71858, by rfl⟩ : syracuseStep 1532981 = 143717) (by norm_num)
theorem B2155589 : Blo 956588 2155589 := bbase (se 4 (by rfl) ⟨202086, by rfl⟩ : syracuseStep 2155589 = 404173) (by norm_num)
theorem B1729621 : Blo 956588 1729621 := bbase (se 8 (by rfl) ⟨10134, by rfl⟩ : syracuseStep 1729621 = 20269) (by norm_num)
theorem B2155661 : Blo 956588 2155661 := bbase (se 3 (by rfl) ⟨404186, by rfl⟩ : syracuseStep 2155661 = 808373) (by norm_num)
theorem B3237029 : Blo 956588 3237029 := bbase (se 4 (by rfl) ⟨303471, by rfl⟩ : syracuseStep 3237029 = 606943) (by norm_num)
theorem B2155733 : Blo 956588 2155733 := bbase (se 7 (by rfl) ⟨25262, by rfl⟩ : syracuseStep 2155733 = 50525) (by norm_num)
theorem B1434893 : Blo 956588 1434893 := bbase (se 3 (by rfl) ⟨269042, by rfl⟩ : syracuseStep 1434893 = 538085) (by norm_num)
theorem B2155805 : Blo 956588 2155805 := bbase (se 3 (by rfl) ⟨404213, by rfl⟩ : syracuseStep 2155805 = 808427) (by norm_num)
theorem B1434917 : Blo 956588 1434917 := bbase (se 4 (by rfl) ⟨134523, by rfl⟩ : syracuseStep 1434917 = 269047) (by norm_num)
theorem B1434941 : Blo 956588 1434941 := bbase (se 3 (by rfl) ⟨269051, by rfl⟩ : syracuseStep 1434941 = 538103) (by norm_num)
theorem B1434965 : Blo 956588 1434965 := bbase (se 12 (by rfl) ⟨525, by rfl⟩ : syracuseStep 1434965 = 1051) (by norm_num)
theorem B2155877 : Blo 956588 2155877 := bbase (se 4 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 2155877 = 404227) (by norm_num)
theorem B1434989 : Blo 956588 1434989 := bbase (se 3 (by rfl) ⟨269060, by rfl⟩ : syracuseStep 1434989 = 538121) (by norm_num)
theorem B1435013 : Blo 956588 1435013 := bbase (se 4 (by rfl) ⟨134532, by rfl⟩ : syracuseStep 1435013 = 269065) (by norm_num)
theorem B1435037 : Blo 956588 1435037 := bbase (se 3 (by rfl) ⟨269069, by rfl⟩ : syracuseStep 1435037 = 538139) (by norm_num)
theorem B2155949 : Blo 956588 2155949 := bbase (se 3 (by rfl) ⟨404240, by rfl⟩ : syracuseStep 2155949 = 808481) (by norm_num)
theorem B1435061 : Blo 956588 1435061 := bbase (se 5 (by rfl) ⟨67268, by rfl⟩ : syracuseStep 1435061 = 134537) (by norm_num)
theorem B1435085 : Blo 956588 1435085 := bbase (se 3 (by rfl) ⟨269078, by rfl⟩ : syracuseStep 1435085 = 538157) (by norm_num)
theorem B1435109 : Blo 956588 1435109 := bbase (se 4 (by rfl) ⟨134541, by rfl⟩ : syracuseStep 1435109 = 269083) (by norm_num)
theorem B2156021 : Blo 956588 2156021 := bbase (se 5 (by rfl) ⟨101063, by rfl⟩ : syracuseStep 2156021 = 202127) (by norm_num)
theorem B1435133 : Blo 956588 1435133 := bbase (se 3 (by rfl) ⟨269087, by rfl⟩ : syracuseStep 1435133 = 538175) (by norm_num)
theorem B1664509 : Blo 956588 1664509 := bbase (se 3 (by rfl) ⟨312095, by rfl⟩ : syracuseStep 1664509 = 624191) (by norm_num)
theorem B1435157 : Blo 956588 1435157 := bbase (se 6 (by rfl) ⟨33636, by rfl⟩ : syracuseStep 1435157 = 67273) (by norm_num)
theorem B1435181 : Blo 956588 1435181 := bbase (se 3 (by rfl) ⟨269096, by rfl⟩ : syracuseStep 1435181 = 538193) (by norm_num)
theorem B2156093 : Blo 956588 2156093 := bbase (se 3 (by rfl) ⟨404267, by rfl⟩ : syracuseStep 2156093 = 808535) (by norm_num)
theorem B1435205 : Blo 956588 1435205 := bbase (se 4 (by rfl) ⟨134550, by rfl⟩ : syracuseStep 1435205 = 269101) (by norm_num)
theorem B26240597 : Blo 956588 26240597 := bbase (se 8 (by rfl) ⟨153753, by rfl⟩ : syracuseStep 26240597 = 307507) (by norm_num)
theorem B3237461 : Blo 956588 3237461 := bbase (se 8 (by rfl) ⟨18969, by rfl⟩ : syracuseStep 3237461 = 37939) (by norm_num)
theorem B1435229 : Blo 956588 1435229 := bbase (se 3 (by rfl) ⟨269105, by rfl⟩ : syracuseStep 1435229 = 538211) (by norm_num)
theorem B1435253 : Blo 956588 1435253 := bbase (se 5 (by rfl) ⟨67277, by rfl⟩ : syracuseStep 1435253 = 134555) (by norm_num)
theorem B2156165 : Blo 956588 2156165 := bbase (se 4 (by rfl) ⟨202140, by rfl⟩ : syracuseStep 2156165 = 404281) (by norm_num)
theorem B1435277 : Blo 956588 1435277 := bbase (se 3 (by rfl) ⟨269114, by rfl⟩ : syracuseStep 1435277 = 538229) (by norm_num)
theorem B1435301 : Blo 956588 1435301 := bbase (se 4 (by rfl) ⟨134559, by rfl⟩ : syracuseStep 1435301 = 269119) (by norm_num)
theorem B1435325 : Blo 956588 1435325 := bbase (se 3 (by rfl) ⟨269123, by rfl⟩ : syracuseStep 1435325 = 538247) (by norm_num)
theorem B1533629 : Blo 956588 1533629 := bbase (se 3 (by rfl) ⟨287555, by rfl⟩ : syracuseStep 1533629 = 575111) (by norm_num)
theorem B2156237 : Blo 956588 2156237 := bbase (se 3 (by rfl) ⟨404294, by rfl⟩ : syracuseStep 2156237 = 808589) (by norm_num)
theorem B1435349 : Blo 956588 1435349 := bbase (se 7 (by rfl) ⟨16820, by rfl⟩ : syracuseStep 1435349 = 33641) (by norm_num)
theorem B1435373 : Blo 956588 1435373 := bbase (se 3 (by rfl) ⟨269132, by rfl⟩ : syracuseStep 1435373 = 538265) (by norm_num)
theorem B1435397 : Blo 956588 1435397 := bbase (se 4 (by rfl) ⟨134568, by rfl⟩ : syracuseStep 1435397 = 269137) (by norm_num)
theorem B2156309 : Blo 956588 2156309 := bbase (se 6 (by rfl) ⟨50538, by rfl⟩ : syracuseStep 2156309 = 101077) (by norm_num)
theorem B1435421 : Blo 956588 1435421 := bbase (se 3 (by rfl) ⟨269141, by rfl⟩ : syracuseStep 1435421 = 538283) (by norm_num)
theorem B1435445 : Blo 956588 1435445 := bbase (se 5 (by rfl) ⟨67286, by rfl⟩ : syracuseStep 1435445 = 134573) (by norm_num)
theorem B1435469 : Blo 956588 1435469 := bbase (se 3 (by rfl) ⟨269150, by rfl⟩ : syracuseStep 1435469 = 538301) (by norm_num)
theorem B2156381 : Blo 956588 2156381 := bbase (se 3 (by rfl) ⟨404321, by rfl⟩ : syracuseStep 2156381 = 808643) (by norm_num)
theorem B1435493 : Blo 956588 1435493 := bbase (se 4 (by rfl) ⟨134577, by rfl⟩ : syracuseStep 1435493 = 269155) (by norm_num)
theorem B1435517 : Blo 956588 1435517 := bbase (se 3 (by rfl) ⟨269159, by rfl⟩ : syracuseStep 1435517 = 538319) (by norm_num)
theorem B1435541 : Blo 956588 1435541 := bbase (se 6 (by rfl) ⟨33645, by rfl⟩ : syracuseStep 1435541 = 67291) (by norm_num)
theorem B2156453 : Blo 956588 2156453 := bbase (se 4 (by rfl) ⟨202167, by rfl⟩ : syracuseStep 2156453 = 404335) (by norm_num)
theorem B1435565 : Blo 956588 1435565 := bbase (se 3 (by rfl) ⟨269168, by rfl⟩ : syracuseStep 1435565 = 538337) (by norm_num)
theorem B1435589 : Blo 956588 1435589 := bbase (se 4 (by rfl) ⟨134586, by rfl⟩ : syracuseStep 1435589 = 269173) (by norm_num)
theorem B1435613 : Blo 956588 1435613 := bbase (se 3 (by rfl) ⟨269177, by rfl⟩ : syracuseStep 1435613 = 538355) (by norm_num)
theorem B2156525 : Blo 956588 2156525 := bbase (se 3 (by rfl) ⟨404348, by rfl⟩ : syracuseStep 2156525 = 808697) (by norm_num)
theorem B1435637 : Blo 956588 1435637 := bbase (se 5 (by rfl) ⟨67295, by rfl⟩ : syracuseStep 1435637 = 134591) (by norm_num)
theorem B3893237 : Blo 956588 3893237 := bbase (se 5 (by rfl) ⟨182495, by rfl⟩ : syracuseStep 3893237 = 364991) (by norm_num)
theorem B3237893 : Blo 956588 3237893 := bbase (se 4 (by rfl) ⟨303552, by rfl⟩ : syracuseStep 3237893 = 607105) (by norm_num)
theorem B1435661 : Blo 956588 1435661 := bbase (se 3 (by rfl) ⟨269186, by rfl⟩ : syracuseStep 1435661 = 538373) (by norm_num)
theorem B1435685 : Blo 956588 1435685 := bbase (se 4 (by rfl) ⟨134595, by rfl⟩ : syracuseStep 1435685 = 269191) (by norm_num)
theorem B2156597 : Blo 956588 2156597 := bbase (se 5 (by rfl) ⟨101090, by rfl⟩ : syracuseStep 2156597 = 202181) (by norm_num)
theorem B1435709 : Blo 956588 1435709 := bbase (se 3 (by rfl) ⟨269195, by rfl⟩ : syracuseStep 1435709 = 538391) (by norm_num)
theorem B1435733 : Blo 956588 1435733 := bbase (se 8 (by rfl) ⟨8412, by rfl⟩ : syracuseStep 1435733 = 16825) (by norm_num)
theorem B1435757 : Blo 956588 1435757 := bbase (se 3 (by rfl) ⟨269204, by rfl⟩ : syracuseStep 1435757 = 538409) (by norm_num)
theorem B1108081 : Blo 956588 1108081 := bbase (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) (by norm_num)
theorem B4843637 : Blo 956588 4843637 := bbase (se 5 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 4843637 = 454091) (by norm_num)
theorem B2156669 : Blo 956588 2156669 := bbase (se 3 (by rfl) ⟨404375, by rfl⟩ : syracuseStep 2156669 = 808751) (by norm_num)
theorem B1435781 : Blo 956588 1435781 := bbase (se 4 (by rfl) ⟨134604, by rfl⟩ : syracuseStep 1435781 = 269209) (by norm_num)
theorem B1435805 : Blo 956588 1435805 := bbase (se 3 (by rfl) ⟨269213, by rfl⟩ : syracuseStep 1435805 = 538427) (by norm_num)
theorem B1730717 : Blo 956588 1730717 := bbase (se 3 (by rfl) ⟨324509, by rfl⟩ : syracuseStep 1730717 = 649019) (by norm_num)
theorem B1435829 : Blo 956588 1435829 := bbase (se 5 (by rfl) ⟨67304, by rfl⟩ : syracuseStep 1435829 = 134609) (by norm_num)
theorem B3893429 : Blo 956588 3893429 := bbase (se 5 (by rfl) ⟨182504, by rfl⟩ : syracuseStep 3893429 = 365009) (by norm_num)
theorem B2156741 : Blo 956588 2156741 := bbase (se 4 (by rfl) ⟨202194, by rfl⟩ : syracuseStep 2156741 = 404389) (by norm_num)
theorem B1435853 : Blo 956588 1435853 := bbase (se 3 (by rfl) ⟨269222, by rfl⟩ : syracuseStep 1435853 = 538445) (by norm_num)
theorem B1435877 : Blo 956588 1435877 := bbase (se 4 (by rfl) ⟨134613, by rfl⟩ : syracuseStep 1435877 = 269227) (by norm_num)
theorem B4090085 : Blo 956588 4090085 := bbase (se 4 (by rfl) ⟨383445, by rfl⟩ : syracuseStep 4090085 = 766891) (by norm_num)
theorem B1435901 : Blo 956588 1435901 := bbase (se 3 (by rfl) ⟨269231, by rfl⟩ : syracuseStep 1435901 = 538463) (by norm_num)
theorem B2156813 : Blo 956588 2156813 := bbase (se 3 (by rfl) ⟨404402, by rfl⟩ : syracuseStep 2156813 = 808805) (by norm_num)
theorem B1435925 : Blo 956588 1435925 := bbase (se 6 (by rfl) ⟨33654, by rfl⟩ : syracuseStep 1435925 = 67309) (by norm_num)
theorem B1435949 : Blo 956588 1435949 := bbase (se 3 (by rfl) ⟨269240, by rfl⟩ : syracuseStep 1435949 = 538481) (by norm_num)
theorem B1435973 : Blo 956588 1435973 := bbase (se 4 (by rfl) ⟨134622, by rfl⟩ : syracuseStep 1435973 = 269245) (by norm_num)
theorem B2156885 : Blo 956588 2156885 := bbase (se 10 (by rfl) ⟨3159, by rfl⟩ : syracuseStep 2156885 = 6319) (by norm_num)
theorem B1435997 : Blo 956588 1435997 := bbase (se 3 (by rfl) ⟨269249, by rfl⟩ : syracuseStep 1435997 = 538499) (by norm_num)
theorem B1436021 : Blo 956588 1436021 := bbase (se 5 (by rfl) ⟨67313, by rfl⟩ : syracuseStep 1436021 = 134627) (by norm_num)
theorem B1436045 : Blo 956588 1436045 := bbase (se 3 (by rfl) ⟨269258, by rfl⟩ : syracuseStep 1436045 = 538517) (by norm_num)
theorem B2156957 : Blo 956588 2156957 := bbase (se 3 (by rfl) ⟨404429, by rfl⟩ : syracuseStep 2156957 = 808859) (by norm_num)
theorem B1436069 : Blo 956588 1436069 := bbase (se 4 (by rfl) ⟨134631, by rfl⟩ : syracuseStep 1436069 = 269263) (by norm_num)
theorem B3238325 : Blo 956588 3238325 := bbase (se 5 (by rfl) ⟨151796, by rfl⟩ : syracuseStep 3238325 = 303593) (by norm_num)
theorem B1436093 : Blo 956588 1436093 := bbase (se 3 (by rfl) ⟨269267, by rfl⟩ : syracuseStep 1436093 = 538535) (by norm_num)
theorem B1436117 : Blo 956588 1436117 := bbase (se 7 (by rfl) ⟨16829, by rfl⟩ : syracuseStep 1436117 = 33659) (by norm_num)
theorem B2157029 : Blo 956588 2157029 := bbase (se 4 (by rfl) ⟨202221, by rfl⟩ : syracuseStep 2157029 = 404443) (by norm_num)
theorem B1436141 : Blo 956588 1436141 := bbase (se 3 (by rfl) ⟨269276, by rfl⟩ : syracuseStep 1436141 = 538553) (by norm_num)
theorem B1436165 : Blo 956588 1436165 := bbase (se 4 (by rfl) ⟨134640, by rfl⟩ : syracuseStep 1436165 = 269281) (by norm_num)
theorem B1436189 : Blo 956588 1436189 := bbase (se 3 (by rfl) ⟨269285, by rfl⟩ : syracuseStep 1436189 = 538571) (by norm_num)
theorem B2157101 : Blo 956588 2157101 := bbase (se 3 (by rfl) ⟨404456, by rfl⟩ : syracuseStep 2157101 = 808913) (by norm_num)
theorem B1436213 : Blo 956588 1436213 := bbase (se 5 (by rfl) ⟨67322, by rfl⟩ : syracuseStep 1436213 = 134645) (by norm_num)
theorem B1436237 : Blo 956588 1436237 := bbase (se 3 (by rfl) ⟨269294, by rfl⟩ : syracuseStep 1436237 = 538589) (by norm_num)
theorem B1436261 : Blo 956588 1436261 := bbase (se 4 (by rfl) ⟨134649, by rfl⟩ : syracuseStep 1436261 = 269299) (by norm_num)
theorem B2157173 : Blo 956588 2157173 := bbase (se 5 (by rfl) ⟨101117, by rfl⟩ : syracuseStep 2157173 = 202235) (by norm_num)
theorem B1436285 : Blo 956588 1436285 := bbase (se 3 (by rfl) ⟨269303, by rfl⟩ : syracuseStep 1436285 = 538607) (by norm_num)
theorem B1436309 : Blo 956588 1436309 := bbase (se 6 (by rfl) ⟨33663, by rfl⟩ : syracuseStep 1436309 = 67327) (by norm_num)
theorem B1534621 : Blo 956588 1534621 := bbase (se 3 (by rfl) ⟨287741, by rfl⟩ : syracuseStep 1534621 = 575483) (by norm_num)
theorem B1436333 : Blo 956588 1436333 := bbase (se 3 (by rfl) ⟨269312, by rfl⟩ : syracuseStep 1436333 = 538625) (by norm_num)
theorem B2157245 : Blo 956588 2157245 := bbase (se 3 (by rfl) ⟨404483, by rfl⟩ : syracuseStep 2157245 = 808967) (by norm_num)
theorem B1436357 : Blo 956588 1436357 := bbase (se 4 (by rfl) ⟨134658, by rfl⟩ : syracuseStep 1436357 = 269317) (by norm_num)
theorem B1436381 : Blo 956588 1436381 := bbase (se 3 (by rfl) ⟨269321, by rfl⟩ : syracuseStep 1436381 = 538643) (by norm_num)
theorem B1436405 : Blo 956588 1436405 := bbase (se 5 (by rfl) ⟨67331, by rfl⟩ : syracuseStep 1436405 = 134663) (by norm_num)
theorem B2157317 : Blo 956588 2157317 := bbase (se 4 (by rfl) ⟨202248, by rfl⟩ : syracuseStep 2157317 = 404497) (by norm_num)
theorem B1436429 : Blo 956588 1436429 := bbase (se 3 (by rfl) ⟨269330, by rfl⟩ : syracuseStep 1436429 = 538661) (by norm_num)
theorem B1436453 : Blo 956588 1436453 := bbase (se 4 (by rfl) ⟨134667, by rfl⟩ : syracuseStep 1436453 = 269335) (by norm_num)
theorem B1436477 : Blo 956588 1436477 := bbase (se 3 (by rfl) ⟨269339, by rfl⟩ : syracuseStep 1436477 = 538679) (by norm_num)
theorem B2157389 : Blo 956588 2157389 := bbase (se 3 (by rfl) ⟨404510, by rfl⟩ : syracuseStep 2157389 = 809021) (by norm_num)
theorem B1436501 : Blo 956588 1436501 := bbase (se 9 (by rfl) ⟨4208, by rfl⟩ : syracuseStep 1436501 = 8417) (by norm_num)
theorem B3238757 : Blo 956588 3238757 := bbase (se 4 (by rfl) ⟨303633, by rfl⟩ : syracuseStep 3238757 = 607267) (by norm_num)
theorem B1436525 : Blo 956588 1436525 := bbase (se 3 (by rfl) ⟨269348, by rfl⟩ : syracuseStep 1436525 = 538697) (by norm_num)
theorem B1436549 : Blo 956588 1436549 := bbase (se 4 (by rfl) ⟨134676, by rfl⟩ : syracuseStep 1436549 = 269353) (by norm_num)
theorem B2157461 : Blo 956588 2157461 := bbase (se 6 (by rfl) ⟨50565, by rfl⟩ : syracuseStep 2157461 = 101131) (by norm_num)
theorem B1436573 : Blo 956588 1436573 := bbase (se 3 (by rfl) ⟨269357, by rfl⟩ : syracuseStep 1436573 = 538715) (by norm_num)
theorem B1436597 : Blo 956588 1436597 := bbase (se 5 (by rfl) ⟨67340, by rfl⟩ : syracuseStep 1436597 = 134681) (by norm_num)
theorem B1436621 : Blo 956588 1436621 := bbase (se 3 (by rfl) ⟨269366, by rfl⟩ : syracuseStep 1436621 = 538733) (by norm_num)
theorem B2157533 : Blo 956588 2157533 := bbase (se 3 (by rfl) ⟨404537, by rfl⟩ : syracuseStep 2157533 = 809075) (by norm_num)
theorem B1076197 : Blo 956588 1076197 := bbase (se 4 (by rfl) ⟨100893, by rfl⟩ : syracuseStep 1076197 = 201787) (by norm_num)
theorem B1436645 : Blo 956588 1436645 := bbase (se 4 (by rfl) ⟨134685, by rfl⟩ : syracuseStep 1436645 = 269371) (by norm_num)
theorem B1436669 : Blo 956588 1436669 := bbase (se 3 (by rfl) ⟨269375, by rfl⟩ : syracuseStep 1436669 = 538751) (by norm_num)
theorem B1076233 : Blo 956588 1076233 := bbase (se 2 (by rfl) ⟨403587, by rfl⟩ : syracuseStep 1076233 = 807175) (by norm_num)
theorem B1436693 : Blo 956588 1436693 := bbase (se 6 (by rfl) ⟨33672, by rfl⟩ : syracuseStep 1436693 = 67345) (by norm_num)
theorem B2157605 : Blo 956588 2157605 := bbase (se 4 (by rfl) ⟨202275, by rfl⟩ : syracuseStep 2157605 = 404551) (by norm_num)
theorem B1076269 : Blo 956588 1076269 := bbase (se 3 (by rfl) ⟨201800, by rfl⟩ : syracuseStep 1076269 = 403601) (by norm_num)
theorem B1436717 : Blo 956588 1436717 := bbase (se 3 (by rfl) ⟨269384, by rfl⟩ : syracuseStep 1436717 = 538769) (by norm_num)
theorem B1436741 : Blo 956588 1436741 := bbase (se 4 (by rfl) ⟨134694, by rfl⟩ : syracuseStep 1436741 = 269389) (by norm_num)
theorem B1076305 : Blo 956588 1076305 := bbase (se 2 (by rfl) ⟨403614, by rfl⟩ : syracuseStep 1076305 = 807229) (by norm_num)
theorem B1436765 : Blo 956588 1436765 := bbase (se 3 (by rfl) ⟨269393, by rfl⟩ : syracuseStep 1436765 = 538787) (by norm_num)
theorem B1535069 : Blo 956588 1535069 := bbase (se 3 (by rfl) ⟨287825, by rfl⟩ : syracuseStep 1535069 = 575651) (by norm_num)
theorem B2157677 : Blo 956588 2157677 := bbase (se 3 (by rfl) ⟨404564, by rfl⟩ : syracuseStep 2157677 = 809129) (by norm_num)
theorem B1076341 : Blo 956588 1076341 := bbase (se 5 (by rfl) ⟨50453, by rfl⟩ : syracuseStep 1076341 = 100907) (by norm_num)
theorem B9202805 : Blo 956588 9202805 := bbase (se 5 (by rfl) ⟨431381, by rfl⟩ : syracuseStep 9202805 = 862763) (by norm_num)
theorem B1436789 : Blo 956588 1436789 := bbase (se 5 (by rfl) ⟨67349, by rfl⟩ : syracuseStep 1436789 = 134699) (by norm_num)
theorem B1436813 : Blo 956588 1436813 := bbase (se 3 (by rfl) ⟨269402, by rfl⟩ : syracuseStep 1436813 = 538805) (by norm_num)
theorem B1076377 : Blo 956588 1076377 := bbase (se 2 (by rfl) ⟨403641, by rfl⟩ : syracuseStep 1076377 = 807283) (by norm_num)
theorem B1436837 : Blo 956588 1436837 := bbase (se 4 (by rfl) ⟨134703, by rfl⟩ : syracuseStep 1436837 = 269407) (by norm_num)
theorem B2157749 : Blo 956588 2157749 := bbase (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) (by norm_num)
theorem B1076413 : Blo 956588 1076413 := bbase (se 3 (by rfl) ⟨201827, by rfl⟩ : syracuseStep 1076413 = 403655) (by norm_num)
theorem B1436861 : Blo 956588 1436861 := bbase (se 3 (by rfl) ⟨269411, by rfl⟩ : syracuseStep 1436861 = 538823) (by norm_num)
theorem B4091093 : Blo 956588 4091093 := bbase (se 7 (by rfl) ⟨47942, by rfl⟩ : syracuseStep 4091093 = 95885) (by norm_num)
theorem B1436885 : Blo 956588 1436885 := bbase (se 7 (by rfl) ⟨16838, by rfl⟩ : syracuseStep 1436885 = 33677) (by norm_num)
theorem B1076449 : Blo 956588 1076449 := bbase (se 2 (by rfl) ⟨403668, by rfl⟩ : syracuseStep 1076449 = 807337) (by norm_num)
theorem B1436909 : Blo 956588 1436909 := bbase (se 3 (by rfl) ⟨269420, by rfl⟩ : syracuseStep 1436909 = 538841) (by norm_num)
theorem B3075317 : Blo 956588 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B2157821 : Blo 956588 2157821 := bbase (se 3 (by rfl) ⟨404591, by rfl⟩ : syracuseStep 2157821 = 809183) (by norm_num)
theorem B1076485 : Blo 956588 1076485 := bbase (se 4 (by rfl) ⟨100920, by rfl⟩ : syracuseStep 1076485 = 201841) (by norm_num)
theorem B1436933 : Blo 956588 1436933 := bbase (se 4 (by rfl) ⟨134712, by rfl⟩ : syracuseStep 1436933 = 269425) (by norm_num)
theorem B3239189 : Blo 956588 3239189 := bbase (se 6 (by rfl) ⟨75918, by rfl⟩ : syracuseStep 3239189 = 151837) (by norm_num)
theorem B1436957 : Blo 956588 1436957 := bbase (se 3 (by rfl) ⟨269429, by rfl⟩ : syracuseStep 1436957 = 538859) (by norm_num)
theorem B1535269 : Blo 956588 1535269 := bbase (se 4 (by rfl) ⟨143931, by rfl⟩ : syracuseStep 1535269 = 287863) (by norm_num)
theorem B1076521 : Blo 956588 1076521 := bbase (se 2 (by rfl) ⟨403695, by rfl⟩ : syracuseStep 1076521 = 807391) (by norm_num)
theorem B1436981 : Blo 956588 1436981 := bbase (se 5 (by rfl) ⟨67358, by rfl⟩ : syracuseStep 1436981 = 134717) (by norm_num)
theorem B2157893 : Blo 956588 2157893 := bbase (se 4 (by rfl) ⟨202302, by rfl⟩ : syracuseStep 2157893 = 404605) (by norm_num)
theorem B1076557 : Blo 956588 1076557 := bbase (se 3 (by rfl) ⟨201854, by rfl⟩ : syracuseStep 1076557 = 403709) (by norm_num)
theorem B1437005 : Blo 956588 1437005 := bbase (se 3 (by rfl) ⟨269438, by rfl⟩ : syracuseStep 1437005 = 538877) (by norm_num)
theorem B3632485 : Blo 956588 3632485 := bbase (se 4 (by rfl) ⟨340545, by rfl⟩ : syracuseStep 3632485 = 681091) (by norm_num)
theorem B1437029 : Blo 956588 1437029 := bbase (se 4 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 1437029 = 269443) (by norm_num)
theorem B1076593 : Blo 956588 1076593 := bbase (se 2 (by rfl) ⟨403722, by rfl⟩ : syracuseStep 1076593 = 807445) (by norm_num)
theorem B1437053 : Blo 956588 1437053 := bbase (se 3 (by rfl) ⟨269447, by rfl⟩ : syracuseStep 1437053 = 538895) (by norm_num)
theorem B4844933 : Blo 956588 4844933 := bbase (se 4 (by rfl) ⟨454212, by rfl⟩ : syracuseStep 4844933 = 908425) (by norm_num)
theorem B2157965 : Blo 956588 2157965 := bbase (se 3 (by rfl) ⟨404618, by rfl⟩ : syracuseStep 2157965 = 809237) (by norm_num)
theorem B1076629 : Blo 956588 1076629 := bbase (se 6 (by rfl) ⟨25233, by rfl⟩ : syracuseStep 1076629 = 50467) (by norm_num)
theorem B1437077 : Blo 956588 1437077 := bbase (se 6 (by rfl) ⟨33681, by rfl⟩ : syracuseStep 1437077 = 67363) (by norm_num)
theorem B1437101 : Blo 956588 1437101 := bbase (se 3 (by rfl) ⟨269456, by rfl⟩ : syracuseStep 1437101 = 538913) (by norm_num)
theorem B1076665 : Blo 956588 1076665 := bbase (se 2 (by rfl) ⟨403749, by rfl⟩ : syracuseStep 1076665 = 807499) (by norm_num)
theorem B1437125 : Blo 956588 1437125 := bbase (se 4 (by rfl) ⟨134730, by rfl⟩ : syracuseStep 1437125 = 269461) (by norm_num)
theorem B2158037 : Blo 956588 2158037 := bbase (se 7 (by rfl) ⟨25289, by rfl⟩ : syracuseStep 2158037 = 50579) (by norm_num)
theorem B1076701 : Blo 956588 1076701 := bbase (se 3 (by rfl) ⟨201881, by rfl⟩ : syracuseStep 1076701 = 403763) (by norm_num)
theorem B1437149 : Blo 956588 1437149 := bbase (se 3 (by rfl) ⟨269465, by rfl⟩ : syracuseStep 1437149 = 538931) (by norm_num)
theorem B1437173 : Blo 956588 1437173 := bbase (se 5 (by rfl) ⟨67367, by rfl⟩ : syracuseStep 1437173 = 134735) (by norm_num)
theorem B1076737 : Blo 956588 1076737 := bbase (se 2 (by rfl) ⟨403776, by rfl⟩ : syracuseStep 1076737 = 807553) (by norm_num)
theorem B1437197 : Blo 956588 1437197 := bbase (se 3 (by rfl) ⟨269474, by rfl⟩ : syracuseStep 1437197 = 538949) (by norm_num)
theorem B2158109 : Blo 956588 2158109 := bbase (se 3 (by rfl) ⟨404645, by rfl⟩ : syracuseStep 2158109 = 809291) (by norm_num)
theorem B1076773 : Blo 956588 1076773 := bbase (se 4 (by rfl) ⟨100947, by rfl⟩ : syracuseStep 1076773 = 201895) (by norm_num)
theorem B1437221 : Blo 956588 1437221 := bbase (se 4 (by rfl) ⟨134739, by rfl⟩ : syracuseStep 1437221 = 269479) (by norm_num)
theorem B1535525 : Blo 956588 1535525 := bbase (se 4 (by rfl) ⟨143955, by rfl⟩ : syracuseStep 1535525 = 287911) (by norm_num)
theorem B1437245 : Blo 956588 1437245 := bbase (se 3 (by rfl) ⟨269483, by rfl⟩ : syracuseStep 1437245 = 538967) (by norm_num)
theorem B1076809 : Blo 956588 1076809 := bbase (se 2 (by rfl) ⟨403803, by rfl⟩ : syracuseStep 1076809 = 807607) (by norm_num)
theorem B1437269 : Blo 956588 1437269 := bbase (se 8 (by rfl) ⟨8421, by rfl⟩ : syracuseStep 1437269 = 16843) (by norm_num)
theorem B1109597 : Blo 956588 1109597 := bbase (se 3 (by rfl) ⟨208049, by rfl⟩ : syracuseStep 1109597 = 416099) (by norm_num)
theorem B2158181 : Blo 956588 2158181 := bbase (se 4 (by rfl) ⟨202329, by rfl⟩ : syracuseStep 2158181 = 404659) (by norm_num)
theorem B1076845 : Blo 956588 1076845 := bbase (se 3 (by rfl) ⟨201908, by rfl⟩ : syracuseStep 1076845 = 403817) (by norm_num)
theorem B1437293 : Blo 956588 1437293 := bbase (se 3 (by rfl) ⟨269492, by rfl⟩ : syracuseStep 1437293 = 538985) (by norm_num)
theorem B1437317 : Blo 956588 1437317 := bbase (se 4 (by rfl) ⟨134748, by rfl⟩ : syracuseStep 1437317 = 269497) (by norm_num)
theorem B1076881 : Blo 956588 1076881 := bbase (se 2 (by rfl) ⟨403830, by rfl⟩ : syracuseStep 1076881 = 807661) (by norm_num)
theorem B3632789 : Blo 956588 3632789 := bbase (se 6 (by rfl) ⟨85143, by rfl⟩ : syracuseStep 3632789 = 170287) (by norm_num)
theorem B1437341 : Blo 956588 1437341 := bbase (se 3 (by rfl) ⟨269501, by rfl⟩ : syracuseStep 1437341 = 539003) (by norm_num)
theorem B2158253 : Blo 956588 2158253 := bbase (se 3 (by rfl) ⟨404672, by rfl⟩ : syracuseStep 2158253 = 809345) (by norm_num)
theorem B1076917 : Blo 956588 1076917 := bbase (se 5 (by rfl) ⟨50480, by rfl⟩ : syracuseStep 1076917 = 100961) (by norm_num)
theorem B1437365 : Blo 956588 1437365 := bbase (se 5 (by rfl) ⟨67376, by rfl⟩ : syracuseStep 1437365 = 134753) (by norm_num)
theorem B3239621 : Blo 956588 3239621 := bbase (se 4 (by rfl) ⟨303714, by rfl⟩ : syracuseStep 3239621 = 607429) (by norm_num)
theorem B1437389 : Blo 956588 1437389 := bbase (se 3 (by rfl) ⟨269510, by rfl⟩ : syracuseStep 1437389 = 539021) (by norm_num)
theorem B1076953 : Blo 956588 1076953 := bbase (se 2 (by rfl) ⟨403857, by rfl⟩ : syracuseStep 1076953 = 807715) (by norm_num)
theorem B1437413 : Blo 956588 1437413 := bbase (se 4 (by rfl) ⟨134757, by rfl⟩ : syracuseStep 1437413 = 269515) (by norm_num)
theorem B2158325 : Blo 956588 2158325 := bbase (se 5 (by rfl) ⟨101171, by rfl⟩ : syracuseStep 2158325 = 202343) (by norm_num)
theorem B1076989 : Blo 956588 1076989 := bbase (se 3 (by rfl) ⟨201935, by rfl⟩ : syracuseStep 1076989 = 403871) (by norm_num)
theorem B1437437 : Blo 956588 1437437 := bbase (se 3 (by rfl) ⟨269519, by rfl⟩ : syracuseStep 1437437 = 539039) (by norm_num)
theorem B1437461 : Blo 956588 1437461 := bbase (se 6 (by rfl) ⟨33690, by rfl⟩ : syracuseStep 1437461 = 67381) (by norm_num)
theorem B1077025 : Blo 956588 1077025 := bbase (se 2 (by rfl) ⟨403884, by rfl⟩ : syracuseStep 1077025 = 807769) (by norm_num)
theorem B4615973 : Blo 956588 4615973 := bbase (se 4 (by rfl) ⟨432747, by rfl⟩ : syracuseStep 4615973 = 865495) (by norm_num)
theorem B1437485 : Blo 956588 1437485 := bbase (se 3 (by rfl) ⟨269528, by rfl⟩ : syracuseStep 1437485 = 539057) (by norm_num)
theorem B2158397 : Blo 956588 2158397 := bbase (se 3 (by rfl) ⟨404699, by rfl⟩ : syracuseStep 2158397 = 809399) (by norm_num)
theorem B1077061 : Blo 956588 1077061 := bbase (se 4 (by rfl) ⟨100974, by rfl⟩ : syracuseStep 1077061 = 201949) (by norm_num)
theorem B1437509 : Blo 956588 1437509 := bbase (se 4 (by rfl) ⟨134766, by rfl⟩ : syracuseStep 1437509 = 269533) (by norm_num)
theorem B1437533 : Blo 956588 1437533 := bbase (se 3 (by rfl) ⟨269537, by rfl⟩ : syracuseStep 1437533 = 539075) (by norm_num)
theorem B1077097 : Blo 956588 1077097 := bbase (se 2 (by rfl) ⟨403911, by rfl⟩ : syracuseStep 1077097 = 807823) (by norm_num)
theorem B1437557 : Blo 956588 1437557 := bbase (se 5 (by rfl) ⟨67385, by rfl⟩ : syracuseStep 1437557 = 134771) (by norm_num)
theorem B2158469 : Blo 956588 2158469 := bbase (se 4 (by rfl) ⟨202356, by rfl⟩ : syracuseStep 2158469 = 404713) (by norm_num)
theorem B1077133 : Blo 956588 1077133 := bbase (se 3 (by rfl) ⟨201962, by rfl⟩ : syracuseStep 1077133 = 403925) (by norm_num)
theorem B1437581 : Blo 956588 1437581 := bbase (se 3 (by rfl) ⟨269546, by rfl⟩ : syracuseStep 1437581 = 539093) (by norm_num)
theorem B1437605 : Blo 956588 1437605 := bbase (se 4 (by rfl) ⟨134775, by rfl⟩ : syracuseStep 1437605 = 269551) (by norm_num)
theorem B1077169 : Blo 956588 1077169 := bbase (se 2 (by rfl) ⟨403938, by rfl⟩ : syracuseStep 1077169 = 807877) (by norm_num)
theorem B1437629 : Blo 956588 1437629 := bbase (se 3 (by rfl) ⟨269555, by rfl⟩ : syracuseStep 1437629 = 539111) (by norm_num)
theorem B2158541 : Blo 956588 2158541 := bbase (se 3 (by rfl) ⟨404726, by rfl⟩ : syracuseStep 2158541 = 809453) (by norm_num)
theorem B1077205 : Blo 956588 1077205 := bbase (se 7 (by rfl) ⟨12623, by rfl⟩ : syracuseStep 1077205 = 25247) (by norm_num)
theorem B1437653 : Blo 956588 1437653 := bbase (se 7 (by rfl) ⟨16847, by rfl⟩ : syracuseStep 1437653 = 33695) (by norm_num)
theorem B1437677 : Blo 956588 1437677 := bbase (se 3 (by rfl) ⟨269564, by rfl⟩ : syracuseStep 1437677 = 539129) (by norm_num)
theorem B1077241 : Blo 956588 1077241 := bbase (se 2 (by rfl) ⟨403965, by rfl⟩ : syracuseStep 1077241 = 807931) (by norm_num)
theorem B1437701 : Blo 956588 1437701 := bbase (se 4 (by rfl) ⟨134784, by rfl⟩ : syracuseStep 1437701 = 269569) (by norm_num)
theorem B2158613 : Blo 956588 2158613 := bbase (se 6 (by rfl) ⟨50592, by rfl⟩ : syracuseStep 2158613 = 101185) (by norm_num)
theorem B1077277 : Blo 956588 1077277 := bbase (se 3 (by rfl) ⟨201989, by rfl⟩ : syracuseStep 1077277 = 403979) (by norm_num)
theorem B1437725 : Blo 956588 1437725 := bbase (se 3 (by rfl) ⟨269573, by rfl⟩ : syracuseStep 1437725 = 539147) (by norm_num)
theorem B1437749 : Blo 956588 1437749 := bbase (se 5 (by rfl) ⟨67394, by rfl⟩ : syracuseStep 1437749 = 134789) (by norm_num)
theorem B5992501 : Blo 956588 5992501 := bbase (se 5 (by rfl) ⟨280898, by rfl⟩ : syracuseStep 5992501 = 561797) (by norm_num)
theorem B1077313 : Blo 956588 1077313 := bbase (se 2 (by rfl) ⟨403992, by rfl⟩ : syracuseStep 1077313 = 807985) (by norm_num)
theorem B1437773 : Blo 956588 1437773 := bbase (se 3 (by rfl) ⟨269582, by rfl⟩ : syracuseStep 1437773 = 539165) (by norm_num)
theorem B2158685 : Blo 956588 2158685 := bbase (se 3 (by rfl) ⟨404753, by rfl⟩ : syracuseStep 2158685 = 809507) (by norm_num)
theorem B1077349 : Blo 956588 1077349 := bbase (se 4 (by rfl) ⟨101001, by rfl⟩ : syracuseStep 1077349 = 202003) (by norm_num)
theorem B1437797 : Blo 956588 1437797 := bbase (se 4 (by rfl) ⟨134793, by rfl⟩ : syracuseStep 1437797 = 269587) (by norm_num)
theorem B3240053 : Blo 956588 3240053 := bbase (se 5 (by rfl) ⟨151877, by rfl⟩ : syracuseStep 3240053 = 303755) (by norm_num)
theorem B3076213 : Blo 956588 3076213 := bbase (se 5 (by rfl) ⟨144197, by rfl⟩ : syracuseStep 3076213 = 288395) (by norm_num)
theorem B1437821 : Blo 956588 1437821 := bbase (se 3 (by rfl) ⟨269591, by rfl⟩ : syracuseStep 1437821 = 539183) (by norm_num)
theorem B1077385 : Blo 956588 1077385 := bbase (se 2 (by rfl) ⟨404019, by rfl⟩ : syracuseStep 1077385 = 808039) (by norm_num)
theorem B1437845 : Blo 956588 1437845 := bbase (se 6 (by rfl) ⟨33699, by rfl⟩ : syracuseStep 1437845 = 67399) (by norm_num)
theorem B2158757 : Blo 956588 2158757 := bbase (se 4 (by rfl) ⟨202383, by rfl⟩ : syracuseStep 2158757 = 404767) (by norm_num)
theorem B1077421 : Blo 956588 1077421 := bbase (se 3 (by rfl) ⟨202016, by rfl⟩ : syracuseStep 1077421 = 404033) (by norm_num)
theorem B1437869 : Blo 956588 1437869 := bbase (se 3 (by rfl) ⟨269600, by rfl⟩ : syracuseStep 1437869 = 539201) (by norm_num)
theorem B1437893 : Blo 956588 1437893 := bbase (se 4 (by rfl) ⟨134802, by rfl⟩ : syracuseStep 1437893 = 269605) (by norm_num)
theorem B1077457 : Blo 956588 1077457 := bbase (se 2 (by rfl) ⟨404046, by rfl⟩ : syracuseStep 1077457 = 808093) (by norm_num)
theorem B1437917 : Blo 956588 1437917 := bbase (se 3 (by rfl) ⟨269609, by rfl⟩ : syracuseStep 1437917 = 539219) (by norm_num)
theorem B2158829 : Blo 956588 2158829 := bbase (se 3 (by rfl) ⟨404780, by rfl⟩ : syracuseStep 2158829 = 809561) (by norm_num)
theorem B1077493 : Blo 956588 1077493 := bbase (se 5 (by rfl) ⟨50507, by rfl⟩ : syracuseStep 1077493 = 101015) (by norm_num)
theorem B1437941 : Blo 956588 1437941 := bbase (se 5 (by rfl) ⟨67403, by rfl⟩ : syracuseStep 1437941 = 134807) (by norm_num)
theorem B1437965 : Blo 956588 1437965 := bbase (se 3 (by rfl) ⟨269618, by rfl⟩ : syracuseStep 1437965 = 539237) (by norm_num)
theorem B1077529 : Blo 956588 1077529 := bbase (se 2 (by rfl) ⟨404073, by rfl⟩ : syracuseStep 1077529 = 808147) (by norm_num)
theorem B1437989 : Blo 956588 1437989 := bbase (se 4 (by rfl) ⟨134811, by rfl⟩ : syracuseStep 1437989 = 269623) (by norm_num)
theorem B2158901 : Blo 956588 2158901 := bbase (se 5 (by rfl) ⟨101198, by rfl⟩ : syracuseStep 2158901 = 202397) (by norm_num)
theorem B1077565 : Blo 956588 1077565 := bbase (se 3 (by rfl) ⟨202043, by rfl⟩ : syracuseStep 1077565 = 404087) (by norm_num)
theorem B1438013 : Blo 956588 1438013 := bbase (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) (by norm_num)
theorem B1438037 : Blo 956588 1438037 := bbase (se 10 (by rfl) ⟨2106, by rfl⟩ : syracuseStep 1438037 = 4213) (by norm_num)
theorem B1077601 : Blo 956588 1077601 := bbase (se 2 (by rfl) ⟨404100, by rfl⟩ : syracuseStep 1077601 = 808201) (by norm_num)
theorem B1438061 : Blo 956588 1438061 := bbase (se 3 (by rfl) ⟨269636, by rfl⟩ : syracuseStep 1438061 = 539273) (by norm_num)
theorem B2158973 : Blo 956588 2158973 := bbase (se 3 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 2158973 = 809615) (by norm_num)
theorem B1077637 : Blo 956588 1077637 := bbase (se 4 (by rfl) ⟨101028, by rfl⟩ : syracuseStep 1077637 = 202057) (by norm_num)
theorem B1438085 : Blo 956588 1438085 := bbase (se 4 (by rfl) ⟨134820, by rfl⟩ : syracuseStep 1438085 = 269641) (by norm_num)
theorem B1438109 : Blo 956588 1438109 := bbase (se 3 (by rfl) ⟨269645, by rfl⟩ : syracuseStep 1438109 = 539291) (by norm_num)
theorem B1077673 : Blo 956588 1077673 := bbase (se 2 (by rfl) ⟨404127, by rfl⟩ : syracuseStep 1077673 = 808255) (by norm_num)
theorem B1438133 : Blo 956588 1438133 := bbase (se 5 (by rfl) ⟨67412, by rfl⟩ : syracuseStep 1438133 = 134825) (by norm_num)
theorem B2159045 : Blo 956588 2159045 := bbase (se 4 (by rfl) ⟨202410, by rfl⟩ : syracuseStep 2159045 = 404821) (by norm_num)
theorem B1077709 : Blo 956588 1077709 := bbase (se 3 (by rfl) ⟨202070, by rfl⟩ : syracuseStep 1077709 = 404141) (by norm_num)
theorem B1438157 : Blo 956588 1438157 := bbase (se 3 (by rfl) ⟨269654, by rfl⟩ : syracuseStep 1438157 = 539309) (by norm_num)
theorem B1438181 : Blo 956588 1438181 := bbase (se 4 (by rfl) ⟨134829, by rfl⟩ : syracuseStep 1438181 = 269659) (by norm_num)
theorem B1077745 : Blo 956588 1077745 := bbase (se 2 (by rfl) ⟨404154, by rfl⟩ : syracuseStep 1077745 = 808309) (by norm_num)
theorem B1438205 : Blo 956588 1438205 := bbase (se 3 (by rfl) ⟨269663, by rfl⟩ : syracuseStep 1438205 = 539327) (by norm_num)
theorem B2159117 : Blo 956588 2159117 := bbase (se 3 (by rfl) ⟨404834, by rfl⟩ : syracuseStep 2159117 = 809669) (by norm_num)
theorem B1077781 : Blo 956588 1077781 := bbase (se 6 (by rfl) ⟨25260, by rfl⟩ : syracuseStep 1077781 = 50521) (by norm_num)
theorem B1438229 : Blo 956588 1438229 := bbase (se 6 (by rfl) ⟨33708, by rfl⟩ : syracuseStep 1438229 = 67417) (by norm_num)
theorem B3240485 : Blo 956588 3240485 := bbase (se 4 (by rfl) ⟨303795, by rfl⟩ : syracuseStep 3240485 = 607591) (by norm_num)
theorem B1438253 : Blo 956588 1438253 := bbase (se 3 (by rfl) ⟨269672, by rfl⟩ : syracuseStep 1438253 = 539345) (by norm_num)
theorem B1077817 : Blo 956588 1077817 := bbase (se 2 (by rfl) ⟨404181, by rfl⟩ : syracuseStep 1077817 = 808363) (by norm_num)
theorem B1438277 : Blo 956588 1438277 := bbase (se 4 (by rfl) ⟨134838, by rfl⟩ : syracuseStep 1438277 = 269677) (by norm_num)
theorem B2159189 : Blo 956588 2159189 := bbase (se 8 (by rfl) ⟨12651, by rfl⟩ : syracuseStep 2159189 = 25303) (by norm_num)
theorem B1077853 : Blo 956588 1077853 := bbase (se 3 (by rfl) ⟨202097, by rfl⟩ : syracuseStep 1077853 = 404195) (by norm_num)
theorem B1438301 : Blo 956588 1438301 := bbase (se 3 (by rfl) ⟨269681, by rfl⟩ : syracuseStep 1438301 = 539363) (by norm_num)
theorem B1438325 : Blo 956588 1438325 := bbase (se 5 (by rfl) ⟨67421, by rfl⟩ : syracuseStep 1438325 = 134843) (by norm_num)
theorem B2421373 : Blo 956588 2421373 := bbase (se 3 (by rfl) ⟨454007, by rfl⟩ : syracuseStep 2421373 = 908015) (by norm_num)
theorem B1077889 : Blo 956588 1077889 := bbase (se 2 (by rfl) ⟨404208, by rfl⟩ : syracuseStep 1077889 = 808417) (by norm_num)
theorem B1438349 : Blo 956588 1438349 := bbase (se 3 (by rfl) ⟨269690, by rfl⟩ : syracuseStep 1438349 = 539381) (by norm_num)
theorem B1536653 : Blo 956588 1536653 := bbase (se 3 (by rfl) ⟨288122, by rfl⟩ : syracuseStep 1536653 = 576245) (by norm_num)
theorem B4846229 : Blo 956588 4846229 := bbase (se 6 (by rfl) ⟨113583, by rfl⟩ : syracuseStep 4846229 = 227167) (by norm_num)
theorem B2159261 : Blo 956588 2159261 := bbase (se 3 (by rfl) ⟨404861, by rfl⟩ : syracuseStep 2159261 = 809723) (by norm_num)
theorem B1077925 : Blo 956588 1077925 := bbase (se 4 (by rfl) ⟨101055, by rfl⟩ : syracuseStep 1077925 = 202111) (by norm_num)
theorem B1438373 : Blo 956588 1438373 := bbase (se 4 (by rfl) ⟨134847, by rfl⟩ : syracuseStep 1438373 = 269695) (by norm_num)
theorem B1438397 : Blo 956588 1438397 := bbase (se 3 (by rfl) ⟨269699, by rfl⟩ : syracuseStep 1438397 = 539399) (by norm_num)
theorem B1077961 : Blo 956588 1077961 := bbase (se 2 (by rfl) ⟨404235, by rfl⟩ : syracuseStep 1077961 = 808471) (by norm_num)
theorem B16380629 : Blo 956588 16380629 := bbase (se 7 (by rfl) ⟨191960, by rfl⟩ : syracuseStep 16380629 = 383921) (by norm_num)
theorem B1438421 : Blo 956588 1438421 := bbase (se 7 (by rfl) ⟨16856, by rfl⟩ : syracuseStep 1438421 = 33713) (by norm_num)
theorem B2159333 : Blo 956588 2159333 := bbase (se 4 (by rfl) ⟨202437, by rfl⟩ : syracuseStep 2159333 = 404875) (by norm_num)
theorem B2421485 : Blo 956588 2421485 := bbase (se 3 (by rfl) ⟨454028, by rfl⟩ : syracuseStep 2421485 = 908057) (by norm_num)
theorem B1077997 : Blo 956588 1077997 := bbase (se 3 (by rfl) ⟨202124, by rfl⟩ : syracuseStep 1077997 = 404249) (by norm_num)
theorem B1438445 : Blo 956588 1438445 := bbase (se 3 (by rfl) ⟨269708, by rfl⟩ : syracuseStep 1438445 = 539417) (by norm_num)
theorem B1438469 : Blo 956588 1438469 := bbase (se 4 (by rfl) ⟨134856, by rfl⟩ : syracuseStep 1438469 = 269713) (by norm_num)
theorem B1078033 : Blo 956588 1078033 := bbase (se 2 (by rfl) ⟨404262, by rfl⟩ : syracuseStep 1078033 = 808525) (by norm_num)
theorem B1438493 : Blo 956588 1438493 := bbase (se 3 (by rfl) ⟨269717, by rfl⟩ : syracuseStep 1438493 = 539435) (by norm_num)
theorem B2159405 : Blo 956588 2159405 := bbase (se 3 (by rfl) ⟨404888, by rfl⟩ : syracuseStep 2159405 = 809777) (by norm_num)
theorem B1078069 : Blo 956588 1078069 := bbase (se 5 (by rfl) ⟨50534, by rfl⟩ : syracuseStep 1078069 = 101069) (by norm_num)
theorem B1438517 : Blo 956588 1438517 := bbase (se 5 (by rfl) ⟨67430, by rfl⟩ : syracuseStep 1438517 = 134861) (by norm_num)
theorem B1438541 : Blo 956588 1438541 := bbase (se 3 (by rfl) ⟨269726, by rfl⟩ : syracuseStep 1438541 = 539453) (by norm_num)
theorem B1078105 : Blo 956588 1078105 := bbase (se 2 (by rfl) ⟨404289, by rfl⟩ : syracuseStep 1078105 = 808579) (by norm_num)
theorem B1438565 : Blo 956588 1438565 := bbase (se 4 (by rfl) ⟨134865, by rfl⟩ : syracuseStep 1438565 = 269731) (by norm_num)
theorem B2159477 : Blo 956588 2159477 := bbase (se 5 (by rfl) ⟨101225, by rfl⟩ : syracuseStep 2159477 = 202451) (by norm_num)
theorem B1078141 : Blo 956588 1078141 := bbase (se 3 (by rfl) ⟨202151, by rfl⟩ : syracuseStep 1078141 = 404303) (by norm_num)
theorem B1438589 : Blo 956588 1438589 := bbase (se 3 (by rfl) ⟨269735, by rfl⟩ : syracuseStep 1438589 = 539471) (by norm_num)
theorem B1438613 : Blo 956588 1438613 := bbase (se 6 (by rfl) ⟨33717, by rfl⟩ : syracuseStep 1438613 = 67435) (by norm_num)
theorem B1078177 : Blo 956588 1078177 := bbase (se 2 (by rfl) ⟨404316, by rfl⟩ : syracuseStep 1078177 = 808633) (by norm_num)
theorem B2421677 : Blo 956588 2421677 := bbase (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) (by norm_num)
theorem B1438637 : Blo 956588 1438637 := bbase (se 3 (by rfl) ⟨269744, by rfl⟩ : syracuseStep 1438637 = 539489) (by norm_num)
theorem B2159549 : Blo 956588 2159549 := bbase (se 3 (by rfl) ⟨404915, by rfl⟩ : syracuseStep 2159549 = 809831) (by norm_num)
theorem B4092869 : Blo 956588 4092869 := bbase (se 4 (by rfl) ⟨383706, by rfl⟩ : syracuseStep 4092869 = 767413) (by norm_num)
theorem B1078213 : Blo 956588 1078213 := bbase (se 4 (by rfl) ⟨101082, by rfl⟩ : syracuseStep 1078213 = 202165) (by norm_num)
theorem B1438661 : Blo 956588 1438661 := bbase (se 4 (by rfl) ⟨134874, by rfl⟩ : syracuseStep 1438661 = 269749) (by norm_num)
theorem B3240917 : Blo 956588 3240917 := bbase (se 7 (by rfl) ⟨37979, by rfl⟩ : syracuseStep 3240917 = 75959) (by norm_num)
theorem B1438685 : Blo 956588 1438685 := bbase (se 3 (by rfl) ⟨269753, by rfl⟩ : syracuseStep 1438685 = 539507) (by norm_num)
theorem B1078249 : Blo 956588 1078249 := bbase (se 2 (by rfl) ⟨404343, by rfl⟩ : syracuseStep 1078249 = 808687) (by norm_num)
theorem B1438709 : Blo 956588 1438709 := bbase (se 5 (by rfl) ⟨67439, by rfl⟩ : syracuseStep 1438709 = 134879) (by norm_num)
theorem B2159621 : Blo 956588 2159621 := bbase (se 4 (by rfl) ⟨202464, by rfl⟩ : syracuseStep 2159621 = 404929) (by norm_num)
theorem B1078285 : Blo 956588 1078285 := bbase (se 3 (by rfl) ⟨202178, by rfl⟩ : syracuseStep 1078285 = 404357) (by norm_num)
theorem B1438733 : Blo 956588 1438733 := bbase (se 3 (by rfl) ⟨269762, by rfl⟩ : syracuseStep 1438733 = 539525) (by norm_num)
theorem B1438757 : Blo 956588 1438757 := bbase (se 4 (by rfl) ⟨134883, by rfl⟩ : syracuseStep 1438757 = 269767) (by norm_num)
theorem B1078321 : Blo 956588 1078321 := bbase (se 2 (by rfl) ⟨404370, by rfl⟩ : syracuseStep 1078321 = 808741) (by norm_num)
theorem B1438781 : Blo 956588 1438781 := bbase (se 3 (by rfl) ⟨269771, by rfl⟩ : syracuseStep 1438781 = 539543) (by norm_num)
theorem B2159693 : Blo 956588 2159693 := bbase (se 3 (by rfl) ⟨404942, by rfl⟩ : syracuseStep 2159693 = 809885) (by norm_num)
theorem B1078357 : Blo 956588 1078357 := bbase (se 8 (by rfl) ⟨6318, by rfl⟩ : syracuseStep 1078357 = 12637) (by norm_num)
theorem B1438805 : Blo 956588 1438805 := bbase (se 8 (by rfl) ⟨8430, by rfl⟩ : syracuseStep 1438805 = 16861) (by norm_num)
theorem B1438829 : Blo 956588 1438829 := bbase (se 3 (by rfl) ⟨269780, by rfl⟩ : syracuseStep 1438829 = 539561) (by norm_num)
theorem B1078393 : Blo 956588 1078393 := bbase (se 2 (by rfl) ⟨404397, by rfl⟩ : syracuseStep 1078393 = 808795) (by norm_num)
theorem B1438853 : Blo 956588 1438853 := bbase (se 4 (by rfl) ⟨134892, by rfl⟩ : syracuseStep 1438853 = 269785) (by norm_num)
theorem B1537165 : Blo 956588 1537165 := bbase (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) (by norm_num)
theorem B2159765 : Blo 956588 2159765 := bbase (se 6 (by rfl) ⟨50619, by rfl⟩ : syracuseStep 2159765 = 101239) (by norm_num)
theorem B1078429 : Blo 956588 1078429 := bbase (se 3 (by rfl) ⟨202205, by rfl⟩ : syracuseStep 1078429 = 404411) (by norm_num)
theorem B1438877 : Blo 956588 1438877 := bbase (se 3 (by rfl) ⟨269789, by rfl⟩ : syracuseStep 1438877 = 539579) (by norm_num)
theorem B1438901 : Blo 956588 1438901 := bbase (se 5 (by rfl) ⟨67448, by rfl⟩ : syracuseStep 1438901 = 134897) (by norm_num)
theorem B1078465 : Blo 956588 1078465 := bbase (se 2 (by rfl) ⟨404424, by rfl⟩ : syracuseStep 1078465 = 808849) (by norm_num)
theorem B1438925 : Blo 956588 1438925 := bbase (se 3 (by rfl) ⟨269798, by rfl⟩ : syracuseStep 1438925 = 539597) (by norm_num)
theorem B2159837 : Blo 956588 2159837 := bbase (se 3 (by rfl) ⟨404969, by rfl⟩ : syracuseStep 2159837 = 809939) (by norm_num)
theorem B1078501 : Blo 956588 1078501 := bbase (se 4 (by rfl) ⟨101109, by rfl⟩ : syracuseStep 1078501 = 202219) (by norm_num)
theorem B1438949 : Blo 956588 1438949 := bbase (se 4 (by rfl) ⟨134901, by rfl⟩ : syracuseStep 1438949 = 269803) (by norm_num)
theorem B1438973 : Blo 956588 1438973 := bbase (se 3 (by rfl) ⟨269807, by rfl⟩ : syracuseStep 1438973 = 539615) (by norm_num)
theorem B2422021 : Blo 956588 2422021 := bbase (se 4 (by rfl) ⟨227064, by rfl⟩ : syracuseStep 2422021 = 454129) (by norm_num)
theorem B1078537 : Blo 956588 1078537 := bbase (se 2 (by rfl) ⟨404451, by rfl⟩ : syracuseStep 1078537 = 808903) (by norm_num)
theorem B1438997 : Blo 956588 1438997 := bbase (se 6 (by rfl) ⟨33726, by rfl⟩ : syracuseStep 1438997 = 67453) (by norm_num)
theorem B2159909 : Blo 956588 2159909 := bbase (se 4 (by rfl) ⟨202491, by rfl⟩ : syracuseStep 2159909 = 404983) (by norm_num)
theorem B1078573 : Blo 956588 1078573 := bbase (se 3 (by rfl) ⟨202232, by rfl⟩ : syracuseStep 1078573 = 404465) (by norm_num)
theorem B1439021 : Blo 956588 1439021 := bbase (se 3 (by rfl) ⟨269816, by rfl⟩ : syracuseStep 1439021 = 539633) (by norm_num)
theorem B1439045 : Blo 956588 1439045 := bbase (se 4 (by rfl) ⟨134910, by rfl⟩ : syracuseStep 1439045 = 269821) (by norm_num)
theorem B1078609 : Blo 956588 1078609 := bbase (se 2 (by rfl) ⟨404478, by rfl⟩ : syracuseStep 1078609 = 808957) (by norm_num)
theorem B12285269 : Blo 956588 12285269 := bbase (se 13 (by rfl) ⟨2249, by rfl⟩ : syracuseStep 12285269 = 4499) (by norm_num)
theorem B1439069 : Blo 956588 1439069 := bbase (se 3 (by rfl) ⟨269825, by rfl⟩ : syracuseStep 1439069 = 539651) (by norm_num)
theorem B2159981 : Blo 956588 2159981 := bbase (se 3 (by rfl) ⟨404996, by rfl⟩ : syracuseStep 2159981 = 809993) (by norm_num)
theorem B2422133 : Blo 956588 2422133 := bbase (se 5 (by rfl) ⟨113537, by rfl⟩ : syracuseStep 2422133 = 227075) (by norm_num)
theorem B1078645 : Blo 956588 1078645 := bbase (se 5 (by rfl) ⟨50561, by rfl⟩ : syracuseStep 1078645 = 101123) (by norm_num)
theorem B1439093 : Blo 956588 1439093 := bbase (se 5 (by rfl) ⟨67457, by rfl⟩ : syracuseStep 1439093 = 134915) (by norm_num)
theorem B3241349 : Blo 956588 3241349 := bbase (se 4 (by rfl) ⟨303876, by rfl⟩ : syracuseStep 3241349 = 607753) (by norm_num)
theorem B1439117 : Blo 956588 1439117 := bbase (se 3 (by rfl) ⟨269834, by rfl⟩ : syracuseStep 1439117 = 539669) (by norm_num)
theorem B1078681 : Blo 956588 1078681 := bbase (se 2 (by rfl) ⟨404505, by rfl⟩ : syracuseStep 1078681 = 809011) (by norm_num)
theorem B1439141 : Blo 956588 1439141 := bbase (se 4 (by rfl) ⟨134919, by rfl⟩ : syracuseStep 1439141 = 269839) (by norm_num)
theorem B2160053 : Blo 956588 2160053 := bbase (se 5 (by rfl) ⟨101252, by rfl⟩ : syracuseStep 2160053 = 202505) (by norm_num)
theorem B1078717 : Blo 956588 1078717 := bbase (se 3 (by rfl) ⟨202259, by rfl⟩ : syracuseStep 1078717 = 404519) (by norm_num)
theorem B1439165 : Blo 956588 1439165 := bbase (se 3 (by rfl) ⟨269843, by rfl⟩ : syracuseStep 1439165 = 539687) (by norm_num)
theorem B1439189 : Blo 956588 1439189 := bbase (se 7 (by rfl) ⟨16865, by rfl⟩ : syracuseStep 1439189 = 33731) (by norm_num)
theorem B1078753 : Blo 956588 1078753 := bbase (se 2 (by rfl) ⟨404532, by rfl⟩ : syracuseStep 1078753 = 809065) (by norm_num)
theorem B1439213 : Blo 956588 1439213 := bbase (se 3 (by rfl) ⟨269852, by rfl⟩ : syracuseStep 1439213 = 539705) (by norm_num)
theorem B2160125 : Blo 956588 2160125 := bbase (se 3 (by rfl) ⟨405023, by rfl⟩ : syracuseStep 2160125 = 810047) (by norm_num)
theorem B1078789 : Blo 956588 1078789 := bbase (se 4 (by rfl) ⟨101136, by rfl⟩ : syracuseStep 1078789 = 202273) (by norm_num)
theorem B1439237 : Blo 956588 1439237 := bbase (se 4 (by rfl) ⟨134928, by rfl⟩ : syracuseStep 1439237 = 269857) (by norm_num)
theorem B1439261 : Blo 956588 1439261 := bbase (se 3 (by rfl) ⟨269861, by rfl⟩ : syracuseStep 1439261 = 539723) (by norm_num)
theorem B1078825 : Blo 956588 1078825 := bbase (se 2 (by rfl) ⟨404559, by rfl⟩ : syracuseStep 1078825 = 809119) (by norm_num)
theorem B2422325 : Blo 956588 2422325 := bbase (se 5 (by rfl) ⟨113546, by rfl⟩ : syracuseStep 2422325 = 227093) (by norm_num)
theorem B1439285 : Blo 956588 1439285 := bbase (se 5 (by rfl) ⟨67466, by rfl⟩ : syracuseStep 1439285 = 134933) (by norm_num)
theorem B2160197 : Blo 956588 2160197 := bbase (se 4 (by rfl) ⟨202518, by rfl⟩ : syracuseStep 2160197 = 405037) (by norm_num)
theorem B1078861 : Blo 956588 1078861 := bbase (se 3 (by rfl) ⟨202286, by rfl⟩ : syracuseStep 1078861 = 404573) (by norm_num)
theorem B1439309 : Blo 956588 1439309 := bbase (se 3 (by rfl) ⟨269870, by rfl⟩ : syracuseStep 1439309 = 539741) (by norm_num)
theorem B1439333 : Blo 956588 1439333 := bbase (se 4 (by rfl) ⟨134937, by rfl⟩ : syracuseStep 1439333 = 269875) (by norm_num)
theorem B1078897 : Blo 956588 1078897 := bbase (se 2 (by rfl) ⟨404586, by rfl⟩ : syracuseStep 1078897 = 809173) (by norm_num)
theorem B1439357 : Blo 956588 1439357 := bbase (se 3 (by rfl) ⟨269879, by rfl⟩ : syracuseStep 1439357 = 539759) (by norm_num)
theorem B2160269 : Blo 956588 2160269 := bbase (se 3 (by rfl) ⟨405050, by rfl⟩ : syracuseStep 2160269 = 810101) (by norm_num)
theorem B1078933 : Blo 956588 1078933 := bbase (se 6 (by rfl) ⟨25287, by rfl⟩ : syracuseStep 1078933 = 50575) (by norm_num)
theorem B1439381 : Blo 956588 1439381 := bbase (se 6 (by rfl) ⟨33735, by rfl⟩ : syracuseStep 1439381 = 67471) (by norm_num)
theorem B1439405 : Blo 956588 1439405 := bbase (se 3 (by rfl) ⟨269888, by rfl⟩ : syracuseStep 1439405 = 539777) (by norm_num)
theorem B1537709 : Blo 956588 1537709 := bbase (se 3 (by rfl) ⟨288320, by rfl⟩ : syracuseStep 1537709 = 576641) (by norm_num)
theorem B1078969 : Blo 956588 1078969 := bbase (se 2 (by rfl) ⟨404613, by rfl⟩ : syracuseStep 1078969 = 809227) (by norm_num)
theorem B1439429 : Blo 956588 1439429 := bbase (se 4 (by rfl) ⟨134946, by rfl⟩ : syracuseStep 1439429 = 269893) (by norm_num)
theorem B3634901 : Blo 956588 3634901 := bbase (se 7 (by rfl) ⟨42596, by rfl⟩ : syracuseStep 3634901 = 85193) (by norm_num)
theorem B2160341 : Blo 956588 2160341 := bbase (se 7 (by rfl) ⟨25316, by rfl⟩ : syracuseStep 2160341 = 50633) (by norm_num)
theorem B1079005 : Blo 956588 1079005 := bbase (se 3 (by rfl) ⟨202313, by rfl⟩ : syracuseStep 1079005 = 404627) (by norm_num)
theorem B1439453 : Blo 956588 1439453 := bbase (se 3 (by rfl) ⟨269897, by rfl⟩ : syracuseStep 1439453 = 539795) (by norm_num)
theorem B1439477 : Blo 956588 1439477 := bbase (se 5 (by rfl) ⟨67475, by rfl⟩ : syracuseStep 1439477 = 134951) (by norm_num)
theorem B1079041 : Blo 956588 1079041 := bbase (se 2 (by rfl) ⟨404640, by rfl⟩ : syracuseStep 1079041 = 809281) (by norm_num)
theorem B1439501 : Blo 956588 1439501 := bbase (se 3 (by rfl) ⟨269906, by rfl⟩ : syracuseStep 1439501 = 539813) (by norm_num)
theorem B2160413 : Blo 956588 2160413 := bbase (se 3 (by rfl) ⟨405077, by rfl⟩ : syracuseStep 2160413 = 810155) (by norm_num)
theorem B1079077 : Blo 956588 1079077 := bbase (se 4 (by rfl) ⟨101163, by rfl⟩ : syracuseStep 1079077 = 202327) (by norm_num)
theorem B1439525 : Blo 956588 1439525 := bbase (se 4 (by rfl) ⟨134955, by rfl⟩ : syracuseStep 1439525 = 269911) (by norm_num)
theorem B3241781 : Blo 956588 3241781 := bbase (se 5 (by rfl) ⟨151958, by rfl⟩ : syracuseStep 3241781 = 303917) (by norm_num)
theorem B1439549 : Blo 956588 1439549 := bbase (se 3 (by rfl) ⟨269915, by rfl⟩ : syracuseStep 1439549 = 539831) (by norm_num)
theorem B1079113 : Blo 956588 1079113 := bbase (se 2 (by rfl) ⟨404667, by rfl⟩ : syracuseStep 1079113 = 809335) (by norm_num)
theorem B1439573 : Blo 956588 1439573 := bbase (se 9 (by rfl) ⟨4217, by rfl⟩ : syracuseStep 1439573 = 8435) (by norm_num)
theorem B2160485 : Blo 956588 2160485 := bbase (se 4 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 2160485 = 405091) (by norm_num)
theorem B1079149 : Blo 956588 1079149 := bbase (se 3 (by rfl) ⟨202340, by rfl⟩ : syracuseStep 1079149 = 404681) (by norm_num)
theorem B1439597 : Blo 956588 1439597 := bbase (se 3 (by rfl) ⟨269924, by rfl⟩ : syracuseStep 1439597 = 539849) (by norm_num)
theorem B1439621 : Blo 956588 1439621 := bbase (se 4 (by rfl) ⟨134964, by rfl⟩ : syracuseStep 1439621 = 269929) (by norm_num)
theorem B2422669 : Blo 956588 2422669 := bbase (se 3 (by rfl) ⟨454250, by rfl⟩ : syracuseStep 2422669 = 908501) (by norm_num)
theorem B1079185 : Blo 956588 1079185 := bbase (se 2 (by rfl) ⟨404694, by rfl⟩ : syracuseStep 1079185 = 809389) (by norm_num)
theorem B1439645 : Blo 956588 1439645 := bbase (se 3 (by rfl) ⟨269933, by rfl⟩ : syracuseStep 1439645 = 539867) (by norm_num)
theorem B4847525 : Blo 956588 4847525 := bbase (se 4 (by rfl) ⟨454455, by rfl⟩ : syracuseStep 4847525 = 908911) (by norm_num)
theorem B2160557 : Blo 956588 2160557 := bbase (se 3 (by rfl) ⟨405104, by rfl⟩ : syracuseStep 2160557 = 810209) (by norm_num)
theorem B1079221 : Blo 956588 1079221 := bbase (se 5 (by rfl) ⟨50588, by rfl⟩ : syracuseStep 1079221 = 101177) (by norm_num)
theorem B1439669 : Blo 956588 1439669 := bbase (se 5 (by rfl) ⟨67484, by rfl⟩ : syracuseStep 1439669 = 134969) (by norm_num)
theorem B1439693 : Blo 956588 1439693 := bbase (se 3 (by rfl) ⟨269942, by rfl⟩ : syracuseStep 1439693 = 539885) (by norm_num)
theorem B2586581 : Blo 956588 2586581 := bbase (se 7 (by rfl) ⟨30311, by rfl⟩ : syracuseStep 2586581 = 60623) (by norm_num)
theorem B1079257 : Blo 956588 1079257 := bbase (se 2 (by rfl) ⟨404721, by rfl⟩ : syracuseStep 1079257 = 809443) (by norm_num)
theorem B1439717 : Blo 956588 1439717 := bbase (se 4 (by rfl) ⟨134973, by rfl⟩ : syracuseStep 1439717 = 269947) (by norm_num)
theorem B3635189 : Blo 956588 3635189 := bbase (se 5 (by rfl) ⟨170399, by rfl⟩ : syracuseStep 3635189 = 340799) (by norm_num)
theorem B2160629 : Blo 956588 2160629 := bbase (se 5 (by rfl) ⟨101279, by rfl⟩ : syracuseStep 2160629 = 202559) (by norm_num)
theorem B2422781 : Blo 956588 2422781 := bbase (se 3 (by rfl) ⟨454271, by rfl⟩ : syracuseStep 2422781 = 908543) (by norm_num)
theorem B1079293 : Blo 956588 1079293 := bbase (se 3 (by rfl) ⟨202367, by rfl⟩ : syracuseStep 1079293 = 404735) (by norm_num)
theorem B1439741 : Blo 956588 1439741 := bbase (se 3 (by rfl) ⟨269951, by rfl⟩ : syracuseStep 1439741 = 539903) (by norm_num)
theorem B1439765 : Blo 956588 1439765 := bbase (se 6 (by rfl) ⟨33744, by rfl⟩ : syracuseStep 1439765 = 67489) (by norm_num)
theorem B1079329 : Blo 956588 1079329 := bbase (se 2 (by rfl) ⟨404748, by rfl⟩ : syracuseStep 1079329 = 809497) (by norm_num)
theorem B1439789 : Blo 956588 1439789 := bbase (se 3 (by rfl) ⟨269960, by rfl⟩ : syracuseStep 1439789 = 539921) (by norm_num)
theorem B2160701 : Blo 956588 2160701 := bbase (se 3 (by rfl) ⟨405131, by rfl⟩ : syracuseStep 2160701 = 810263) (by norm_num)
theorem B1079365 : Blo 956588 1079365 := bbase (se 4 (by rfl) ⟨101190, by rfl⟩ : syracuseStep 1079365 = 202381) (by norm_num)
theorem B1439813 : Blo 956588 1439813 := bbase (se 4 (by rfl) ⟨134982, by rfl⟩ : syracuseStep 1439813 = 269965) (by norm_num)
theorem B1439837 : Blo 956588 1439837 := bbase (se 3 (by rfl) ⟨269969, by rfl⟩ : syracuseStep 1439837 = 539939) (by norm_num)
theorem B1079401 : Blo 956588 1079401 := bbase (se 2 (by rfl) ⟨404775, by rfl⟩ : syracuseStep 1079401 = 809551) (by norm_num)
theorem B1439861 : Blo 956588 1439861 := bbase (se 5 (by rfl) ⟨67493, by rfl⟩ : syracuseStep 1439861 = 134987) (by norm_num)
theorem B5470325 : Blo 956588 5470325 := bbase (se 5 (by rfl) ⟨256421, by rfl⟩ : syracuseStep 5470325 = 512843) (by norm_num)
theorem B2160773 : Blo 956588 2160773 := bbase (se 4 (by rfl) ⟨202572, by rfl⟩ : syracuseStep 2160773 = 405145) (by norm_num)
theorem B1079437 : Blo 956588 1079437 := bbase (se 3 (by rfl) ⟨202394, by rfl⟩ : syracuseStep 1079437 = 404789) (by norm_num)
theorem B1439885 : Blo 956588 1439885 := bbase (se 3 (by rfl) ⟨269978, by rfl⟩ : syracuseStep 1439885 = 539957) (by norm_num)
theorem B1439909 : Blo 956588 1439909 := bbase (se 4 (by rfl) ⟨134991, by rfl⟩ : syracuseStep 1439909 = 269983) (by norm_num)
theorem B1079473 : Blo 956588 1079473 := bbase (se 2 (by rfl) ⟨404802, by rfl⟩ : syracuseStep 1079473 = 809605) (by norm_num)
theorem B2422973 : Blo 956588 2422973 := bbase (se 3 (by rfl) ⟨454307, by rfl⟩ : syracuseStep 2422973 = 908615) (by norm_num)
theorem B1439933 : Blo 956588 1439933 := bbase (se 3 (by rfl) ⟨269987, by rfl⟩ : syracuseStep 1439933 = 539975) (by norm_num)
theorem B2160845 : Blo 956588 2160845 := bbase (se 3 (by rfl) ⟨405158, by rfl⟩ : syracuseStep 2160845 = 810317) (by norm_num)
theorem B27982037 : Blo 956588 27982037 := bbase (se 7 (by rfl) ⟨327914, by rfl⟩ : syracuseStep 27982037 = 655829) (by norm_num)
theorem B1079509 : Blo 956588 1079509 := bbase (se 7 (by rfl) ⟨12650, by rfl⟩ : syracuseStep 1079509 = 25301) (by norm_num)
theorem B1439957 : Blo 956588 1439957 := bbase (se 7 (by rfl) ⟨16874, by rfl⟩ : syracuseStep 1439957 = 33749) (by norm_num)
theorem B1538261 : Blo 956588 1538261 := bbase (se 7 (by rfl) ⟨18026, by rfl⟩ : syracuseStep 1538261 = 36053) (by norm_num)
theorem B1439981 : Blo 956588 1439981 := bbase (se 3 (by rfl) ⟨269996, by rfl⟩ : syracuseStep 1439981 = 539993) (by norm_num)
theorem B1538293 : Blo 956588 1538293 := bbase (se 5 (by rfl) ⟨72107, by rfl⟩ : syracuseStep 1538293 = 144215) (by norm_num)
theorem B1079545 : Blo 956588 1079545 := bbase (se 2 (by rfl) ⟨404829, by rfl⟩ : syracuseStep 1079545 = 809659) (by norm_num)
theorem B1440005 : Blo 956588 1440005 := bbase (se 4 (by rfl) ⟨135000, by rfl⟩ : syracuseStep 1440005 = 270001) (by norm_num)
theorem B2160917 : Blo 956588 2160917 := bbase (se 6 (by rfl) ⟨50646, by rfl⟩ : syracuseStep 2160917 = 101293) (by norm_num)
theorem B1079581 : Blo 956588 1079581 := bbase (se 3 (by rfl) ⟨202421, by rfl⟩ : syracuseStep 1079581 = 404843) (by norm_num)
theorem B1440029 : Blo 956588 1440029 := bbase (se 3 (by rfl) ⟨270005, by rfl⟩ : syracuseStep 1440029 = 540011) (by norm_num)
theorem B1440053 : Blo 956588 1440053 := bbase (se 5 (by rfl) ⟨67502, by rfl⟩ : syracuseStep 1440053 = 135005) (by norm_num)
theorem B1079617 : Blo 956588 1079617 := bbase (se 2 (by rfl) ⟨404856, by rfl⟩ : syracuseStep 1079617 = 809713) (by norm_num)
theorem B1440077 : Blo 956588 1440077 := bbase (se 3 (by rfl) ⟨270014, by rfl⟩ : syracuseStep 1440077 = 540029) (by norm_num)
theorem B1210717 : Blo 956588 1210717 := bbase (se 3 (by rfl) ⟨227009, by rfl⟩ : syracuseStep 1210717 = 454019) (by norm_num)
theorem B2160989 : Blo 956588 2160989 := bbase (se 3 (by rfl) ⟨405185, by rfl⟩ : syracuseStep 2160989 = 810371) (by norm_num)
theorem B1079653 : Blo 956588 1079653 := bbase (se 4 (by rfl) ⟨101217, by rfl⟩ : syracuseStep 1079653 = 202435) (by norm_num)
theorem B1440101 : Blo 956588 1440101 := bbase (se 4 (by rfl) ⟨135009, by rfl⟩ : syracuseStep 1440101 = 270019) (by norm_num)
theorem B1440125 : Blo 956588 1440125 := bbase (se 3 (by rfl) ⟨270023, by rfl⟩ : syracuseStep 1440125 = 540047) (by norm_num)
theorem B1079689 : Blo 956588 1079689 := bbase (se 2 (by rfl) ⟨404883, by rfl⟩ : syracuseStep 1079689 = 809767) (by norm_num)
theorem B2914709 : Blo 956588 2914709 := bbase (se 6 (by rfl) ⟨68313, by rfl⟩ : syracuseStep 2914709 = 136627) (by norm_num)
theorem B1440149 : Blo 956588 1440149 := bbase (se 6 (by rfl) ⟨33753, by rfl⟩ : syracuseStep 1440149 = 67507) (by norm_num)
theorem B2161061 : Blo 956588 2161061 := bbase (se 4 (by rfl) ⟨202599, by rfl⟩ : syracuseStep 2161061 = 405199) (by norm_num)
theorem B1079725 : Blo 956588 1079725 := bbase (se 3 (by rfl) ⟨202448, by rfl⟩ : syracuseStep 1079725 = 404897) (by norm_num)
theorem B1440173 : Blo 956588 1440173 := bbase (se 3 (by rfl) ⟨270032, by rfl⟩ : syracuseStep 1440173 = 540065) (by norm_num)
theorem B1440197 : Blo 956588 1440197 := bbase (se 4 (by rfl) ⟨135018, by rfl⟩ : syracuseStep 1440197 = 270037) (by norm_num)
theorem B1079761 : Blo 956588 1079761 := bbase (se 2 (by rfl) ⟨404910, by rfl⟩ : syracuseStep 1079761 = 809821) (by norm_num)
theorem B1440221 : Blo 956588 1440221 := bbase (se 3 (by rfl) ⟨270041, by rfl⟩ : syracuseStep 1440221 = 540083) (by norm_num)
theorem B2161133 : Blo 956588 2161133 := bbase (se 3 (by rfl) ⟨405212, by rfl⟩ : syracuseStep 2161133 = 810425) (by norm_num)
theorem B1079797 : Blo 956588 1079797 := bbase (se 5 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 1079797 = 101231) (by norm_num)
theorem B1440245 : Blo 956588 1440245 := bbase (se 5 (by rfl) ⟨67511, by rfl⟩ : syracuseStep 1440245 = 135023) (by norm_num)
theorem B1210889 : Blo 956588 1210889 := bbase (se 2 (by rfl) ⟨454083, by rfl⟩ : syracuseStep 1210889 = 908167) (by norm_num)
theorem B1440269 : Blo 956588 1440269 := bbase (se 3 (by rfl) ⟨270050, by rfl⟩ : syracuseStep 1440269 = 540101) (by norm_num)
theorem B2423317 : Blo 956588 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B1079833 : Blo 956588 1079833 := bbase (se 2 (by rfl) ⟨404937, by rfl⟩ : syracuseStep 1079833 = 809875) (by norm_num)
theorem B1440293 : Blo 956588 1440293 := bbase (se 4 (by rfl) ⟨135027, by rfl⟩ : syracuseStep 1440293 = 270055) (by norm_num)
theorem B2161205 : Blo 956588 2161205 := bbase (se 5 (by rfl) ⟨101306, by rfl⟩ : syracuseStep 2161205 = 202613) (by norm_num)
theorem B1079869 : Blo 956588 1079869 := bbase (se 3 (by rfl) ⟨202475, by rfl⟩ : syracuseStep 1079869 = 404951) (by norm_num)
theorem B1440317 : Blo 956588 1440317 := bbase (se 3 (by rfl) ⟨270059, by rfl⟩ : syracuseStep 1440317 = 540119) (by norm_num)
theorem B1210945 : Blo 956588 1210945 := bbase (se 2 (by rfl) ⟨454104, by rfl⟩ : syracuseStep 1210945 = 908209) (by norm_num)
theorem B1440341 : Blo 956588 1440341 := bbase (se 8 (by rfl) ⟨8439, by rfl⟩ : syracuseStep 1440341 = 16879) (by norm_num)
theorem B1079905 : Blo 956588 1079905 := bbase (se 2 (by rfl) ⟨404964, by rfl⟩ : syracuseStep 1079905 = 809929) (by norm_num)
theorem B1440365 : Blo 956588 1440365 := bbase (se 3 (by rfl) ⟨270068, by rfl⟩ : syracuseStep 1440365 = 540137) (by norm_num)
theorem B2161277 : Blo 956588 2161277 := bbase (se 3 (by rfl) ⟨405239, by rfl⟩ : syracuseStep 2161277 = 810479) (by norm_num)
theorem B2423429 : Blo 956588 2423429 := bbase (se 4 (by rfl) ⟨227196, by rfl⟩ : syracuseStep 2423429 = 454393) (by norm_num)
theorem B1079941 : Blo 956588 1079941 := bbase (se 4 (by rfl) ⟨101244, by rfl⟩ : syracuseStep 1079941 = 202489) (by norm_num)
theorem B1440389 : Blo 956588 1440389 := bbase (se 4 (by rfl) ⟨135036, by rfl⟩ : syracuseStep 1440389 = 270073) (by norm_num)
theorem B1440413 : Blo 956588 1440413 := bbase (se 3 (by rfl) ⟨270077, by rfl⟩ : syracuseStep 1440413 = 540155) (by norm_num)
theorem B1211041 : Blo 956588 1211041 := bbase (se 2 (by rfl) ⟨454140, by rfl⟩ : syracuseStep 1211041 = 908281) (by norm_num)
theorem B1079977 : Blo 956588 1079977 := bbase (se 2 (by rfl) ⟨404991, by rfl⟩ : syracuseStep 1079977 = 809983) (by norm_num)
theorem B1440437 : Blo 956588 1440437 := bbase (se 5 (by rfl) ⟨67520, by rfl⟩ : syracuseStep 1440437 = 135041) (by norm_num)
theorem B1080013 : Blo 956588 1080013 := bbase (se 3 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 1080013 = 405005) (by norm_num)
theorem B1440461 : Blo 956588 1440461 := bbase (se 3 (by rfl) ⟨270086, by rfl⟩ : syracuseStep 1440461 = 540173) (by norm_num)
theorem B1440485 : Blo 956588 1440485 := bbase (se 4 (by rfl) ⟨135045, by rfl⟩ : syracuseStep 1440485 = 270091) (by norm_num)
theorem B1080049 : Blo 956588 1080049 := bbase (se 2 (by rfl) ⟨405018, by rfl⟩ : syracuseStep 1080049 = 810037) (by norm_num)
theorem B1440509 : Blo 956588 1440509 := bbase (se 3 (by rfl) ⟨270095, by rfl⟩ : syracuseStep 1440509 = 540191) (by norm_num)
theorem B1080085 : Blo 956588 1080085 := bbase (se 6 (by rfl) ⟨25314, by rfl⟩ : syracuseStep 1080085 = 50629) (by norm_num)
theorem B1440533 : Blo 956588 1440533 := bbase (se 6 (by rfl) ⟨33762, by rfl⟩ : syracuseStep 1440533 = 67525) (by norm_num)
theorem B1440557 : Blo 956588 1440557 := bbase (se 3 (by rfl) ⟨270104, by rfl⟩ : syracuseStep 1440557 = 540209) (by norm_num)
theorem B1080121 : Blo 956588 1080121 := bbase (se 2 (by rfl) ⟨405045, by rfl⟩ : syracuseStep 1080121 = 810091) (by norm_num)
theorem B2423621 : Blo 956588 2423621 := bbase (se 4 (by rfl) ⟨227214, by rfl⟩ : syracuseStep 2423621 = 454429) (by norm_num)
theorem B1440581 : Blo 956588 1440581 := bbase (se 4 (by rfl) ⟨135054, by rfl⟩ : syracuseStep 1440581 = 270109) (by norm_num)
theorem B1211213 : Blo 956588 1211213 := bbase (se 3 (by rfl) ⟨227102, by rfl⟩ : syracuseStep 1211213 = 454205) (by norm_num)
theorem B1080157 : Blo 956588 1080157 := bbase (se 3 (by rfl) ⟨202529, by rfl⟩ : syracuseStep 1080157 = 405059) (by norm_num)
theorem B1440605 : Blo 956588 1440605 := bbase (se 3 (by rfl) ⟨270113, by rfl⟩ : syracuseStep 1440605 = 540227) (by norm_num)
theorem B1440629 : Blo 956588 1440629 := bbase (se 5 (by rfl) ⟨67529, by rfl⟩ : syracuseStep 1440629 = 135059) (by norm_num)
theorem B1080193 : Blo 956588 1080193 := bbase (se 2 (by rfl) ⟨405072, by rfl⟩ : syracuseStep 1080193 = 810145) (by norm_num)
theorem B1211269 : Blo 956588 1211269 := bbase (se 4 (by rfl) ⟨113556, by rfl⟩ : syracuseStep 1211269 = 227113) (by norm_num)
theorem B1440653 : Blo 956588 1440653 := bbase (se 3 (by rfl) ⟨270122, by rfl⟩ : syracuseStep 1440653 = 540245) (by norm_num)
theorem B1080229 : Blo 956588 1080229 := bbase (se 4 (by rfl) ⟨101271, by rfl⟩ : syracuseStep 1080229 = 202543) (by norm_num)
theorem B1440677 : Blo 956588 1440677 := bbase (se 4 (by rfl) ⟨135063, by rfl⟩ : syracuseStep 1440677 = 270127) (by norm_num)
theorem B1440701 : Blo 956588 1440701 := bbase (se 3 (by rfl) ⟨270131, by rfl⟩ : syracuseStep 1440701 = 540263) (by norm_num)
theorem B1080265 : Blo 956588 1080265 := bbase (se 2 (by rfl) ⟨405099, by rfl⟩ : syracuseStep 1080265 = 810199) (by norm_num)
theorem B1440725 : Blo 956588 1440725 := bbase (se 7 (by rfl) ⟨16883, by rfl⟩ : syracuseStep 1440725 = 33767) (by norm_num)
theorem B1211365 : Blo 956588 1211365 := bbase (se 4 (by rfl) ⟨113565, by rfl⟩ : syracuseStep 1211365 = 227131) (by norm_num)
theorem B1080301 : Blo 956588 1080301 := bbase (se 3 (by rfl) ⟨202556, by rfl⟩ : syracuseStep 1080301 = 405113) (by norm_num)
theorem B1440749 : Blo 956588 1440749 := bbase (se 3 (by rfl) ⟨270140, by rfl⟩ : syracuseStep 1440749 = 540281) (by norm_num)
theorem B1440773 : Blo 956588 1440773 := bbase (se 4 (by rfl) ⟨135072, by rfl⟩ : syracuseStep 1440773 = 270145) (by norm_num)
theorem B1080337 : Blo 956588 1080337 := bbase (se 2 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 1080337 = 810253) (by norm_num)
theorem B1440797 : Blo 956588 1440797 := bbase (se 3 (by rfl) ⟨270149, by rfl⟩ : syracuseStep 1440797 = 540299) (by norm_num)
theorem B1080373 : Blo 956588 1080373 := bbase (se 5 (by rfl) ⟨50642, by rfl⟩ : syracuseStep 1080373 = 101285) (by norm_num)
theorem B1440821 : Blo 956588 1440821 := bbase (se 5 (by rfl) ⟨67538, by rfl⟩ : syracuseStep 1440821 = 135077) (by norm_num)
theorem B1440845 : Blo 956588 1440845 := bbase (se 3 (by rfl) ⟨270158, by rfl⟩ : syracuseStep 1440845 = 540317) (by norm_num)
theorem B1080409 : Blo 956588 1080409 := bbase (se 2 (by rfl) ⟨405153, by rfl⟩ : syracuseStep 1080409 = 810307) (by norm_num)
theorem B1440869 : Blo 956588 1440869 := bbase (se 4 (by rfl) ⟨135081, by rfl⟩ : syracuseStep 1440869 = 270163) (by norm_num)
theorem B1080445 : Blo 956588 1080445 := bbase (se 3 (by rfl) ⟨202583, by rfl⟩ : syracuseStep 1080445 = 405167) (by norm_num)
theorem B1211537 : Blo 956588 1211537 := bbase (se 2 (by rfl) ⟨454326, by rfl⟩ : syracuseStep 1211537 = 908653) (by norm_num)
theorem B3636373 : Blo 956588 3636373 := bbase (se 6 (by rfl) ⟨85227, by rfl⟩ : syracuseStep 3636373 = 170455) (by norm_num)
theorem B2423965 : Blo 956588 2423965 := bbase (se 3 (by rfl) ⟨454493, by rfl⟩ : syracuseStep 2423965 = 908987) (by norm_num)
theorem B1080481 : Blo 956588 1080481 := bbase (se 2 (by rfl) ⟨405180, by rfl⟩ : syracuseStep 1080481 = 810361) (by norm_num)
theorem B4848821 : Blo 956588 4848821 := bbase (se 5 (by rfl) ⟨227288, by rfl⟩ : syracuseStep 4848821 = 454577) (by norm_num)
theorem B1080517 : Blo 956588 1080517 := bbase (se 4 (by rfl) ⟨101298, by rfl⟩ : syracuseStep 1080517 = 202597) (by norm_num)
theorem B1211593 : Blo 956588 1211593 := bbase (se 2 (by rfl) ⟨454347, by rfl⟩ : syracuseStep 1211593 = 908695) (by norm_num)
theorem B1080553 : Blo 956588 1080553 := bbase (se 2 (by rfl) ⟨405207, by rfl⟩ : syracuseStep 1080553 = 810415) (by norm_num)
theorem B2424077 : Blo 956588 2424077 := bbase (se 3 (by rfl) ⟨454514, by rfl⟩ : syracuseStep 2424077 = 909029) (by norm_num)
theorem B1080589 : Blo 956588 1080589 := bbase (se 3 (by rfl) ⟨202610, by rfl⟩ : syracuseStep 1080589 = 405221) (by norm_num)
theorem B1211689 : Blo 956588 1211689 := bbase (se 2 (by rfl) ⟨454383, by rfl⟩ : syracuseStep 1211689 = 908767) (by norm_num)
theorem B1080625 : Blo 956588 1080625 := bbase (se 2 (by rfl) ⟨405234, by rfl⟩ : syracuseStep 1080625 = 810469) (by norm_num)
theorem B4914485 : Blo 956588 4914485 := bbase (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) (by norm_num)
theorem B1080661 : Blo 956588 1080661 := bbase (se 11 (by rfl) ⟨791, by rfl⟩ : syracuseStep 1080661 = 1583) (by norm_num)
theorem B3636677 : Blo 956588 3636677 := bbase (se 4 (by rfl) ⟨340938, by rfl⟩ : syracuseStep 3636677 = 681877) (by norm_num)
theorem B2424269 : Blo 956588 2424269 := bbase (se 3 (by rfl) ⟨454550, by rfl⟩ : syracuseStep 2424269 = 909101) (by norm_num)
theorem B1211861 : Blo 956588 1211861 := bbase (se 7 (by rfl) ⟨14201, by rfl⟩ : syracuseStep 1211861 = 28403) (by norm_num)
theorem B1211917 : Blo 956588 1211917 := bbase (se 3 (by rfl) ⟨227234, by rfl⟩ : syracuseStep 1211917 = 454469) (by norm_num)
theorem B1212013 : Blo 956588 1212013 := bbase (se 3 (by rfl) ⟨227252, by rfl⟩ : syracuseStep 1212013 = 454505) (by norm_num)
theorem B2457317 : Blo 956588 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B1212185 : Blo 956588 1212185 := bbase (se 2 (by rfl) ⟨454569, by rfl⟩ : syracuseStep 1212185 = 909139) (by norm_num)
theorem B2424613 : Blo 956588 2424613 := bbase (se 4 (by rfl) ⟨227307, by rfl⟩ : syracuseStep 2424613 = 454615) (by norm_num)
theorem B1212241 : Blo 956588 1212241 := bbase (se 2 (by rfl) ⟨454590, by rfl⟩ : syracuseStep 1212241 = 909181) (by norm_num)
theorem B2424725 : Blo 956588 2424725 := bbase (se 6 (by rfl) ⟨56829, by rfl⟩ : syracuseStep 2424725 = 113659) (by norm_num)
theorem B1212337 : Blo 956588 1212337 := bbase (se 2 (by rfl) ⟨454626, by rfl⟩ : syracuseStep 1212337 = 909253) (by norm_num)
theorem B1212499 : Blo 956588 1212499 := bstep (se 1 (by rfl) ⟨909374, by rfl⟩ : syracuseStep 1212499 = 1818749) B1818749
theorem B4849955 : Blo 956588 4849955 := bstep (se 1 (by rfl) ⟨3637466, by rfl⟩ : syracuseStep 4849955 = 7274933) B7274933
theorem B3277297 : Blo 956588 3277297 := bstep (se 2 (by rfl) ⟨1228986, by rfl⟩ : syracuseStep 3277297 = 2457973) B2457973
theorem B1638929 : Blo 956588 1638929 := bstep (se 2 (by rfl) ⟨614598, by rfl⟩ : syracuseStep 1638929 = 1229197) B1229197
theorem B1212995 : Blo 956588 1212995 := bstep (se 1 (by rfl) ⟨909746, by rfl⟩ : syracuseStep 1212995 = 1819493) B1819493
theorem B2425585 : Blo 956588 2425585 := bstep (se 2 (by rfl) ⟨909594, by rfl⟩ : syracuseStep 2425585 = 1819189) B1819189
theorem B3113795 : Blo 956588 3113795 := bstep (se 1 (by rfl) ⟨2335346, by rfl⟩ : syracuseStep 3113795 = 4670693) B4670693
theorem B2425859 : Blo 956588 2425859 := bstep (se 1 (by rfl) ⟨1819394, by rfl⟩ : syracuseStep 2425859 = 3638789) B3638789
theorem B4850765 : Blo 956588 4850765 := bstep (se 3 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 4850765 = 1819037) B1819037
theorem B5604515 : Blo 956588 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B1311923 : Blo 956588 1311923 := bstep (se 1 (by rfl) ⟨983942, by rfl⟩ : syracuseStep 1311923 = 1967885) B1967885
theorem B2426051 : Blo 956588 2426051 := bstep (se 1 (by rfl) ⟨1819538, by rfl⟩ : syracuseStep 2426051 = 3639077) B3639077
theorem B1213699 : Blo 956588 1213699 := bstep (se 1 (by rfl) ⟨910274, by rfl⟩ : syracuseStep 1213699 = 1820549) B1820549
theorem B1213795 : Blo 956588 1213795 := bstep (se 1 (by rfl) ⟨910346, by rfl⟩ : syracuseStep 1213795 = 1820693) B1820693
theorem B1214291 : Blo 956588 1214291 := bstep (se 1 (by rfl) ⟨910718, by rfl⟩ : syracuseStep 1214291 = 1821437) B1821437
theorem B4097891 : Blo 956588 4097891 := bstep (se 1 (by rfl) ⟨3073418, by rfl⟩ : syracuseStep 4097891 = 6146837) B6146837
theorem B2426993 : Blo 956588 2426993 := bstep (se 2 (by rfl) ⟨910122, by rfl⟩ : syracuseStep 2426993 = 1820245) B1820245
theorem B2427043 : Blo 956588 2427043 := bstep (se 1 (by rfl) ⟨1820282, by rfl⟩ : syracuseStep 2427043 = 3640565) B3640565
theorem B2427185 : Blo 956588 2427185 := bstep (se 2 (by rfl) ⟨910194, by rfl⟩ : syracuseStep 2427185 = 1820389) B1820389
theorem B3279203 : Blo 956588 3279203 := bstep (se 1 (by rfl) ⟨2459402, by rfl⟩ : syracuseStep 3279203 = 4918805) B4918805
theorem B1214995 : Blo 956588 1214995 := bstep (se 1 (by rfl) ⟨911246, by rfl⟩ : syracuseStep 1214995 = 1822493) B1822493
theorem B1149491 : Blo 956588 1149491 := bstep (se 1 (by rfl) ⟨862118, by rfl⟩ : syracuseStep 1149491 = 1724237) B1724237
theorem B1215091 : Blo 956588 1215091 := bstep (se 1 (by rfl) ⟨911318, by rfl⟩ : syracuseStep 1215091 = 1822637) B1822637
theorem B3640049 : Blo 956588 3640049 := bstep (se 2 (by rfl) ⟨1365018, by rfl⟩ : syracuseStep 3640049 = 2730037) B2730037
theorem B1477441 : Blo 956588 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B1215587 : Blo 956588 1215587 := bstep (se 1 (by rfl) ⟨911690, by rfl⟩ : syracuseStep 1215587 = 1823381) B1823381
theorem B2428177 : Blo 956588 2428177 := bstep (se 2 (by rfl) ⟨910566, by rfl⟩ : syracuseStep 2428177 = 1821133) B1821133
theorem B1248547 : Blo 956588 1248547 := bstep (se 1 (by rfl) ⟨936410, by rfl⟩ : syracuseStep 1248547 = 1872821) B1872821
theorem B8752625 : Blo 956588 8752625 := bstep (se 2 (by rfl) ⟨3282234, by rfl⟩ : syracuseStep 8752625 = 6564469) B6564469
theorem B2428451 : Blo 956588 2428451 := bstep (se 1 (by rfl) ⟨1821338, by rfl⟩ : syracuseStep 2428451 = 3642677) B3642677
theorem B85298741 : Blo 956588 85298741 := bstep (se 5 (by rfl) ⟨3998378, by rfl⟩ : syracuseStep 85298741 = 7996757) B7996757
theorem B1642049 : Blo 956588 1642049 := bstep (se 2 (by rfl) ⟨615768, by rfl⟩ : syracuseStep 1642049 = 1231537) B1231537
theorem B3280483 : Blo 956588 3280483 := bstep (se 1 (by rfl) ⟨2460362, by rfl⟩ : syracuseStep 3280483 = 4920725) B4920725
theorem B2428643 : Blo 956588 2428643 := bstep (se 1 (by rfl) ⟨1821482, by rfl⟩ : syracuseStep 2428643 = 3642965) B3642965
theorem B2330435 : Blo 956588 2330435 := bstep (se 1 (by rfl) ⟨1747826, by rfl⟩ : syracuseStep 2330435 = 3495653) B3495653
theorem B2592593 : Blo 956588 2592593 := bstep (se 2 (by rfl) ⟨972222, by rfl⟩ : syracuseStep 2592593 = 1944445) B1944445
theorem B4853681 : Blo 956588 4853681 := bstep (se 2 (by rfl) ⟨1820130, by rfl⟩ : syracuseStep 4853681 = 3640261) B3640261
theorem B3411953 : Blo 956588 3411953 := bstep (se 2 (by rfl) ⟨1279482, by rfl⟩ : syracuseStep 3411953 = 2558965) B2558965
theorem B2461841 : Blo 956588 2461841 := bstep (se 2 (by rfl) ⟨923190, by rfl⟩ : syracuseStep 2461841 = 1846381) B1846381
theorem B3641507 : Blo 956588 3641507 := bstep (se 1 (by rfl) ⟨2731130, by rfl⟩ : syracuseStep 3641507 = 5462261) B5462261
theorem B2724205 : Blo 956588 2724205 := bstep (se 3 (by rfl) ⟨510788, by rfl⟩ : syracuseStep 2724205 = 1021577) B1021577
theorem B10523077 : Blo 956588 10523077 := bstep (se 4 (by rfl) ⟨986538, by rfl⟩ : syracuseStep 10523077 = 1973077) B1973077
theorem B4100557 : Blo 956588 4100557 := bstep (se 3 (by rfl) ⟨768854, by rfl⟩ : syracuseStep 4100557 = 1537709) B1537709
theorem B5182051 : Blo 956588 5182051 := bstep (se 1 (by rfl) ⟨3886538, by rfl⟩ : syracuseStep 5182051 = 7773077) B7773077
theorem B2429585 : Blo 956588 2429585 := bstep (se 2 (by rfl) ⟨911094, by rfl⟩ : syracuseStep 2429585 = 1822189) B1822189
theorem B2429635 : Blo 956588 2429635 := bstep (se 1 (by rfl) ⟨1822226, by rfl⟩ : syracuseStep 2429635 = 3644453) B3644453
theorem B5182157 : Blo 956588 5182157 := bstep (se 3 (by rfl) ⟨971654, by rfl⟩ : syracuseStep 5182157 = 1943309) B1943309
theorem B6132485 : Blo 956588 6132485 := bstep (se 4 (by rfl) ⟨574920, by rfl⟩ : syracuseStep 6132485 = 1149841) B1149841
theorem B2429777 : Blo 956588 2429777 := bstep (se 2 (by rfl) ⟨911166, by rfl⟩ : syracuseStep 2429777 = 1822333) B1822333
theorem B2593741 : Blo 956588 2593741 := bstep (se 3 (by rfl) ⟨486326, by rfl⟩ : syracuseStep 2593741 = 972653) B972653
theorem B3642509 : Blo 956588 3642509 := bstep (se 3 (by rfl) ⟨682970, by rfl⟩ : syracuseStep 3642509 = 1365941) B1365941
theorem B4855139 : Blo 956588 4855139 := bstep (se 1 (by rfl) ⟨3641354, by rfl⟩ : syracuseStep 4855139 = 7282709) B7282709
theorem B2725265 : Blo 956588 2725265 := bstep (se 2 (by rfl) ⟨1021974, by rfl⟩ : syracuseStep 2725265 = 2043949) B2043949
theorem B3282403 : Blo 956588 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B4101617 : Blo 956588 4101617 := bstep (se 2 (by rfl) ⟨1538106, by rfl⟩ : syracuseStep 4101617 = 3076213) B3076213
theorem B7870193 : Blo 956588 7870193 := bstep (se 2 (by rfl) ⟨2951322, by rfl⟩ : syracuseStep 7870193 = 5902645) B5902645
theorem B5183281 : Blo 956588 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B2430769 : Blo 956588 2430769 := bstep (se 2 (by rfl) ⟨911538, by rfl⟩ : syracuseStep 2430769 = 1823077) B1823077
theorem B74618765 : Blo 956588 74618765 := bstep (se 3 (by rfl) ⟨13991018, by rfl⟩ : syracuseStep 74618765 = 27982037) B27982037
theorem B3282893 : Blo 956588 3282893 := bstep (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) B1231085
theorem B1021987 : Blo 956588 1021987 := bstep (se 1 (by rfl) ⟨766490, by rfl⟩ : syracuseStep 1021987 = 1532981) B1532981
theorem B2725937 : Blo 956588 2725937 := bstep (se 2 (by rfl) ⟨1022226, by rfl⟩ : syracuseStep 2725937 = 2044453) B2044453
theorem B2431043 : Blo 956588 2431043 := bstep (se 1 (by rfl) ⟨1823282, by rfl⟩ : syracuseStep 2431043 = 3646565) B3646565
theorem B8198243 : Blo 956588 8198243 := bstep (se 1 (by rfl) ⟨6148682, by rfl⟩ : syracuseStep 8198243 = 12297365) B12297365
theorem B4855949 : Blo 956588 4855949 := bstep (se 3 (by rfl) ⟨910490, by rfl⟩ : syracuseStep 4855949 = 1820981) B1820981
theorem B956595 : Blo 956588 956595 := bstep (se 1 (by rfl) ⟨717446, by rfl⟩ : syracuseStep 956595 = 1434893) B1434893
theorem B956611 : Blo 956588 956611 := bstep (se 1 (by rfl) ⟨717458, by rfl⟩ : syracuseStep 956611 = 1434917) B1434917
theorem B956627 : Blo 956588 956627 := bstep (se 1 (by rfl) ⟨717470, by rfl⟩ : syracuseStep 956627 = 1434941) B1434941
theorem B956643 : Blo 956588 956643 := bstep (se 1 (by rfl) ⟨717482, by rfl⟩ : syracuseStep 956643 = 1434965) B1434965
theorem B956659 : Blo 956588 956659 := bstep (se 1 (by rfl) ⟨717494, by rfl⟩ : syracuseStep 956659 = 1434989) B1434989
theorem B956675 : Blo 956588 956675 := bstep (se 1 (by rfl) ⟨717506, by rfl⟩ : syracuseStep 956675 = 1435013) B1435013
theorem B2431235 : Blo 956588 2431235 := bstep (se 1 (by rfl) ⟨1823426, by rfl⟩ : syracuseStep 2431235 = 3646853) B3646853
theorem B956691 : Blo 956588 956691 := bstep (se 1 (by rfl) ⟨717518, by rfl⟩ : syracuseStep 956691 = 1435037) B1435037
theorem B956707 : Blo 956588 956707 := bstep (se 1 (by rfl) ⟨717530, by rfl⟩ : syracuseStep 956707 = 1435061) B1435061
theorem B956723 : Blo 956588 956723 := bstep (se 1 (by rfl) ⟨717542, by rfl⟩ : syracuseStep 956723 = 1435085) B1435085
theorem B956739 : Blo 956588 956739 := bstep (se 1 (by rfl) ⟨717554, by rfl⟩ : syracuseStep 956739 = 1435109) B1435109
theorem B956755 : Blo 956588 956755 := bstep (se 1 (by rfl) ⟨717566, by rfl⟩ : syracuseStep 956755 = 1435133) B1435133
theorem B956771 : Blo 956588 956771 := bstep (se 1 (by rfl) ⟨717578, by rfl⟩ : syracuseStep 956771 = 1435157) B1435157
theorem B956787 : Blo 956588 956787 := bstep (se 1 (by rfl) ⟨717590, by rfl⟩ : syracuseStep 956787 = 1435181) B1435181
theorem B956803 : Blo 956588 956803 := bstep (se 1 (by rfl) ⟨717602, by rfl⟩ : syracuseStep 956803 = 1435205) B1435205
theorem B7772557 : Blo 956588 7772557 := bstep (se 3 (by rfl) ⟨1457354, by rfl⟩ : syracuseStep 7772557 = 2914709) B2914709
theorem B956819 : Blo 956588 956819 := bstep (se 1 (by rfl) ⟨717614, by rfl⟩ : syracuseStep 956819 = 1435229) B1435229
theorem B956835 : Blo 956588 956835 := bstep (se 1 (by rfl) ⟨717626, by rfl⟩ : syracuseStep 956835 = 1435253) B1435253
theorem B956851 : Blo 956588 956851 := bstep (se 1 (by rfl) ⟨717638, by rfl⟩ : syracuseStep 956851 = 1435277) B1435277
theorem B956867 : Blo 956588 956867 := bstep (se 1 (by rfl) ⟨717650, by rfl⟩ : syracuseStep 956867 = 1435301) B1435301
theorem B956883 : Blo 956588 956883 := bstep (se 1 (by rfl) ⟨717662, by rfl⟩ : syracuseStep 956883 = 1435325) B1435325
theorem B1022419 : Blo 956588 1022419 := bstep (se 1 (by rfl) ⟨766814, by rfl⟩ : syracuseStep 1022419 = 1533629) B1533629
theorem B956899 : Blo 956588 956899 := bstep (se 1 (by rfl) ⟨717674, by rfl⟩ : syracuseStep 956899 = 1435349) B1435349
theorem B956915 : Blo 956588 956915 := bstep (se 1 (by rfl) ⟨717686, by rfl⟩ : syracuseStep 956915 = 1435373) B1435373
theorem B956931 : Blo 956588 956931 := bstep (se 1 (by rfl) ⟨717698, by rfl⟩ : syracuseStep 956931 = 1435397) B1435397
theorem B956947 : Blo 956588 956947 := bstep (se 1 (by rfl) ⟨717710, by rfl⟩ : syracuseStep 956947 = 1435421) B1435421
theorem B956963 : Blo 956588 956963 := bstep (se 1 (by rfl) ⟨717722, by rfl⟩ : syracuseStep 956963 = 1435445) B1435445
theorem B956979 : Blo 956588 956979 := bstep (se 1 (by rfl) ⟨717734, by rfl⟩ : syracuseStep 956979 = 1435469) B1435469
theorem B956995 : Blo 956588 956995 := bstep (se 1 (by rfl) ⟨717746, by rfl⟩ : syracuseStep 956995 = 1435493) B1435493
theorem B957011 : Blo 956588 957011 := bstep (se 1 (by rfl) ⟨717758, by rfl⟩ : syracuseStep 957011 = 1435517) B1435517
theorem B957027 : Blo 956588 957027 := bstep (se 1 (by rfl) ⟨717770, by rfl⟩ : syracuseStep 957027 = 1435541) B1435541
theorem B7281251 : Blo 956588 7281251 := bstep (se 1 (by rfl) ⟨5460938, by rfl⟩ : syracuseStep 7281251 = 10921877) B10921877
theorem B957043 : Blo 956588 957043 := bstep (se 1 (by rfl) ⟨717782, by rfl⟩ : syracuseStep 957043 = 1435565) B1435565
theorem B957059 : Blo 956588 957059 := bstep (se 1 (by rfl) ⟨717794, by rfl⟩ : syracuseStep 957059 = 1435589) B1435589
theorem B957075 : Blo 956588 957075 := bstep (se 1 (by rfl) ⟨717806, by rfl⟩ : syracuseStep 957075 = 1435613) B1435613
theorem B957091 : Blo 956588 957091 := bstep (se 1 (by rfl) ⟨717818, by rfl⟩ : syracuseStep 957091 = 1435637) B1435637
theorem B2595491 : Blo 956588 2595491 := bstep (se 1 (by rfl) ⟨1946618, by rfl⟩ : syracuseStep 2595491 = 3893237) B3893237
theorem B957107 : Blo 956588 957107 := bstep (se 1 (by rfl) ⟨717830, by rfl⟩ : syracuseStep 957107 = 1435661) B1435661
theorem B957123 : Blo 956588 957123 := bstep (se 1 (by rfl) ⟨717842, by rfl⟩ : syracuseStep 957123 = 1435685) B1435685
theorem B957139 : Blo 956588 957139 := bstep (se 1 (by rfl) ⟨717854, by rfl⟩ : syracuseStep 957139 = 1435709) B1435709
theorem B957155 : Blo 956588 957155 := bstep (se 1 (by rfl) ⟨717866, by rfl⟩ : syracuseStep 957155 = 1435733) B1435733
theorem B957171 : Blo 956588 957171 := bstep (se 1 (by rfl) ⟨717878, by rfl⟩ : syracuseStep 957171 = 1435757) B1435757
theorem B957187 : Blo 956588 957187 := bstep (se 1 (by rfl) ⟨717890, by rfl⟩ : syracuseStep 957187 = 1435781) B1435781
theorem B957203 : Blo 956588 957203 := bstep (se 1 (by rfl) ⟨717902, by rfl⟩ : syracuseStep 957203 = 1435805) B1435805
theorem B1153811 : Blo 956588 1153811 := bstep (se 1 (by rfl) ⟨865358, by rfl⟩ : syracuseStep 1153811 = 1730717) B1730717
theorem B957219 : Blo 956588 957219 := bstep (se 1 (by rfl) ⟨717914, by rfl⟩ : syracuseStep 957219 = 1435829) B1435829
theorem B2595619 : Blo 956588 2595619 := bstep (se 1 (by rfl) ⟨1946714, by rfl⟩ : syracuseStep 2595619 = 3893429) B3893429
theorem B957235 : Blo 956588 957235 := bstep (se 1 (by rfl) ⟨717926, by rfl⟩ : syracuseStep 957235 = 1435853) B1435853
theorem B957251 : Blo 956588 957251 := bstep (se 1 (by rfl) ⟨717938, by rfl⟩ : syracuseStep 957251 = 1435877) B1435877
theorem B2726723 : Blo 956588 2726723 := bstep (se 1 (by rfl) ⟨2045042, by rfl⟩ : syracuseStep 2726723 = 4090085) B4090085
theorem B957267 : Blo 956588 957267 := bstep (se 1 (by rfl) ⟨717950, by rfl⟩ : syracuseStep 957267 = 1435901) B1435901
theorem B957283 : Blo 956588 957283 := bstep (se 1 (by rfl) ⟨717962, by rfl⟩ : syracuseStep 957283 = 1435925) B1435925
theorem B957299 : Blo 956588 957299 := bstep (se 1 (by rfl) ⟨717974, by rfl⟩ : syracuseStep 957299 = 1435949) B1435949
theorem B957315 : Blo 956588 957315 := bstep (se 1 (by rfl) ⟨717986, by rfl⟩ : syracuseStep 957315 = 1435973) B1435973
theorem B957331 : Blo 956588 957331 := bstep (se 1 (by rfl) ⟨717998, by rfl⟩ : syracuseStep 957331 = 1435997) B1435997
theorem B957347 : Blo 956588 957347 := bstep (se 1 (by rfl) ⟨718010, by rfl⟩ : syracuseStep 957347 = 1436021) B1436021
theorem B957363 : Blo 956588 957363 := bstep (se 1 (by rfl) ⟨718022, by rfl⟩ : syracuseStep 957363 = 1436045) B1436045
theorem B957379 : Blo 956588 957379 := bstep (se 1 (by rfl) ⟨718034, by rfl⟩ : syracuseStep 957379 = 1436069) B1436069
theorem B957395 : Blo 956588 957395 := bstep (se 1 (by rfl) ⟨718046, by rfl⟩ : syracuseStep 957395 = 1436093) B1436093
theorem B957411 : Blo 956588 957411 := bstep (se 1 (by rfl) ⟨718058, by rfl⟩ : syracuseStep 957411 = 1436117) B1436117
theorem B957427 : Blo 956588 957427 := bstep (se 1 (by rfl) ⟨718070, by rfl⟩ : syracuseStep 957427 = 1436141) B1436141
theorem B957443 : Blo 956588 957443 := bstep (se 1 (by rfl) ⟨718082, by rfl⟩ : syracuseStep 957443 = 1436165) B1436165
theorem B957459 : Blo 956588 957459 := bstep (se 1 (by rfl) ⟨718094, by rfl⟩ : syracuseStep 957459 = 1436189) B1436189
theorem B957475 : Blo 956588 957475 := bstep (se 1 (by rfl) ⟨718106, by rfl⟩ : syracuseStep 957475 = 1436213) B1436213
theorem B957491 : Blo 956588 957491 := bstep (se 1 (by rfl) ⟨718118, by rfl⟩ : syracuseStep 957491 = 1436237) B1436237
theorem B957507 : Blo 956588 957507 := bstep (se 1 (by rfl) ⟨718130, by rfl⟩ : syracuseStep 957507 = 1436261) B1436261
theorem B5545037 : Blo 956588 5545037 := bstep (se 3 (by rfl) ⟨1039694, by rfl⟩ : syracuseStep 5545037 = 2079389) B2079389
theorem B957523 : Blo 956588 957523 := bstep (se 1 (by rfl) ⟨718142, by rfl⟩ : syracuseStep 957523 = 1436285) B1436285
theorem B957539 : Blo 956588 957539 := bstep (se 1 (by rfl) ⟨718154, by rfl⟩ : syracuseStep 957539 = 1436309) B1436309
theorem B957555 : Blo 956588 957555 := bstep (se 1 (by rfl) ⟨718166, by rfl⟩ : syracuseStep 957555 = 1436333) B1436333
theorem B957571 : Blo 956588 957571 := bstep (se 1 (by rfl) ⟨718178, by rfl⟩ : syracuseStep 957571 = 1436357) B1436357
theorem B2727053 : Blo 956588 2727053 := bstep (se 3 (by rfl) ⟨511322, by rfl⟩ : syracuseStep 2727053 = 1022645) B1022645
theorem B957587 : Blo 956588 957587 := bstep (se 1 (by rfl) ⟨718190, by rfl⟩ : syracuseStep 957587 = 1436381) B1436381
theorem B957603 : Blo 956588 957603 := bstep (se 1 (by rfl) ⟨718202, by rfl⟩ : syracuseStep 957603 = 1436405) B1436405
theorem B957619 : Blo 956588 957619 := bstep (se 1 (by rfl) ⟨718214, by rfl⟩ : syracuseStep 957619 = 1436429) B1436429
theorem B957635 : Blo 956588 957635 := bstep (se 1 (by rfl) ⟨718226, by rfl⟩ : syracuseStep 957635 = 1436453) B1436453
theorem B3644621 : Blo 956588 3644621 := bstep (se 3 (by rfl) ⟨683366, by rfl⟩ : syracuseStep 3644621 = 1366733) B1366733
theorem B2727121 : Blo 956588 2727121 := bstep (se 2 (by rfl) ⟨1022670, by rfl⟩ : syracuseStep 2727121 = 2045341) B2045341
theorem B957651 : Blo 956588 957651 := bstep (se 1 (by rfl) ⟨718238, by rfl⟩ : syracuseStep 957651 = 1436477) B1436477
theorem B957667 : Blo 956588 957667 := bstep (se 1 (by rfl) ⟨718250, by rfl⟩ : syracuseStep 957667 = 1436501) B1436501
theorem B1973489 : Blo 956588 1973489 := bstep (se 2 (by rfl) ⟨740058, by rfl⟩ : syracuseStep 1973489 = 1480117) B1480117
theorem B957683 : Blo 956588 957683 := bstep (se 1 (by rfl) ⟨718262, by rfl⟩ : syracuseStep 957683 = 1436525) B1436525
theorem B957699 : Blo 956588 957699 := bstep (se 1 (by rfl) ⟨718274, by rfl⟩ : syracuseStep 957699 = 1436549) B1436549
theorem B957715 : Blo 956588 957715 := bstep (se 1 (by rfl) ⟨718286, by rfl⟩ : syracuseStep 957715 = 1436573) B1436573
theorem B957731 : Blo 956588 957731 := bstep (se 1 (by rfl) ⟨718298, by rfl⟩ : syracuseStep 957731 = 1436597) B1436597
theorem B957747 : Blo 956588 957747 := bstep (se 1 (by rfl) ⟨718310, by rfl⟩ : syracuseStep 957747 = 1436621) B1436621
theorem B957763 : Blo 956588 957763 := bstep (se 1 (by rfl) ⟨718322, by rfl⟩ : syracuseStep 957763 = 1436645) B1436645
theorem B957779 : Blo 956588 957779 := bstep (se 1 (by rfl) ⟨718334, by rfl⟩ : syracuseStep 957779 = 1436669) B1436669
theorem B957795 : Blo 956588 957795 := bstep (se 1 (by rfl) ⟨718346, by rfl⟩ : syracuseStep 957795 = 1436693) B1436693
theorem B957811 : Blo 956588 957811 := bstep (se 1 (by rfl) ⟨718358, by rfl⟩ : syracuseStep 957811 = 1436717) B1436717
theorem B957827 : Blo 956588 957827 := bstep (se 1 (by rfl) ⟨718370, by rfl⟩ : syracuseStep 957827 = 1436741) B1436741
theorem B957843 : Blo 956588 957843 := bstep (se 1 (by rfl) ⟨718382, by rfl⟩ : syracuseStep 957843 = 1436765) B1436765
theorem B6135203 : Blo 956588 6135203 := bstep (se 1 (by rfl) ⟨4601402, by rfl⟩ : syracuseStep 6135203 = 9202805) B9202805
theorem B957859 : Blo 956588 957859 := bstep (se 1 (by rfl) ⟨718394, by rfl⟩ : syracuseStep 957859 = 1436789) B1436789
theorem B957875 : Blo 956588 957875 := bstep (se 1 (by rfl) ⟨718406, by rfl⟩ : syracuseStep 957875 = 1436813) B1436813
theorem B957891 : Blo 956588 957891 := bstep (se 1 (by rfl) ⟨718418, by rfl⟩ : syracuseStep 957891 = 1436837) B1436837
theorem B957907 : Blo 956588 957907 := bstep (se 1 (by rfl) ⟨718430, by rfl⟩ : syracuseStep 957907 = 1436861) B1436861
theorem B2727395 : Blo 956588 2727395 := bstep (se 1 (by rfl) ⟨2045546, by rfl⟩ : syracuseStep 2727395 = 4091093) B4091093
theorem B957923 : Blo 956588 957923 := bstep (se 1 (by rfl) ⟨718442, by rfl⟩ : syracuseStep 957923 = 1436885) B1436885
theorem B957939 : Blo 956588 957939 := bstep (se 1 (by rfl) ⟨718454, by rfl⟩ : syracuseStep 957939 = 1436909) B1436909
theorem B2301443 : Blo 956588 2301443 := bstep (se 1 (by rfl) ⟨1726082, by rfl⟩ : syracuseStep 2301443 = 3452165) B3452165
theorem B957955 : Blo 956588 957955 := bstep (se 1 (by rfl) ⟨718466, by rfl⟩ : syracuseStep 957955 = 1436933) B1436933
theorem B957971 : Blo 956588 957971 := bstep (se 1 (by rfl) ⟨718478, by rfl⟩ : syracuseStep 957971 = 1436957) B1436957
theorem B957987 : Blo 956588 957987 := bstep (se 1 (by rfl) ⟨718490, by rfl⟩ : syracuseStep 957987 = 1436981) B1436981
theorem B3284525 : Blo 956588 3284525 := bstep (se 3 (by rfl) ⟨615848, by rfl⟩ : syracuseStep 3284525 = 1231697) B1231697
theorem B958003 : Blo 956588 958003 := bstep (se 1 (by rfl) ⟨718502, by rfl⟩ : syracuseStep 958003 = 1437005) B1437005
theorem B958019 : Blo 956588 958019 := bstep (se 1 (by rfl) ⟨718514, by rfl⟩ : syracuseStep 958019 = 1437029) B1437029
theorem B958035 : Blo 956588 958035 := bstep (se 1 (by rfl) ⟨718526, by rfl⟩ : syracuseStep 958035 = 1437053) B1437053
theorem B958051 : Blo 956588 958051 := bstep (se 1 (by rfl) ⟨718538, by rfl⟩ : syracuseStep 958051 = 1437077) B1437077
theorem B11214449 : Blo 956588 11214449 := bstep (se 2 (by rfl) ⟨4205418, by rfl⟩ : syracuseStep 11214449 = 8410837) B8410837
theorem B958067 : Blo 956588 958067 := bstep (se 1 (by rfl) ⟨718550, by rfl⟩ : syracuseStep 958067 = 1437101) B1437101
theorem B958083 : Blo 956588 958083 := bstep (se 1 (by rfl) ⟨718562, by rfl⟩ : syracuseStep 958083 = 1437125) B1437125
theorem B958099 : Blo 956588 958099 := bstep (se 1 (by rfl) ⟨718574, by rfl⟩ : syracuseStep 958099 = 1437149) B1437149
theorem B958115 : Blo 956588 958115 := bstep (se 1 (by rfl) ⟨718586, by rfl⟩ : syracuseStep 958115 = 1437173) B1437173
theorem B958131 : Blo 956588 958131 := bstep (se 1 (by rfl) ⟨718598, by rfl⟩ : syracuseStep 958131 = 1437197) B1437197
theorem B958147 : Blo 956588 958147 := bstep (se 1 (by rfl) ⟨718610, by rfl⟩ : syracuseStep 958147 = 1437221) B1437221
theorem B1023683 : Blo 956588 1023683 := bstep (se 1 (by rfl) ⟨767762, by rfl⟩ : syracuseStep 1023683 = 1535525) B1535525
theorem B958163 : Blo 956588 958163 := bstep (se 1 (by rfl) ⟨718622, by rfl⟩ : syracuseStep 958163 = 1437245) B1437245
theorem B958179 : Blo 956588 958179 := bstep (se 1 (by rfl) ⟨718634, by rfl⟩ : syracuseStep 958179 = 1437269) B1437269
theorem B958195 : Blo 956588 958195 := bstep (se 1 (by rfl) ⟨718646, by rfl⟩ : syracuseStep 958195 = 1437293) B1437293
theorem B958211 : Blo 956588 958211 := bstep (se 1 (by rfl) ⟨718658, by rfl⟩ : syracuseStep 958211 = 1437317) B1437317
theorem B1941265 : Blo 956588 1941265 := bstep (se 2 (by rfl) ⟨727974, by rfl⟩ : syracuseStep 1941265 = 1455949) B1455949
theorem B958227 : Blo 956588 958227 := bstep (se 1 (by rfl) ⟨718670, by rfl⟩ : syracuseStep 958227 = 1437341) B1437341
theorem B958243 : Blo 956588 958243 := bstep (se 1 (by rfl) ⟨718682, by rfl⟩ : syracuseStep 958243 = 1437365) B1437365
theorem B958259 : Blo 956588 958259 := bstep (se 1 (by rfl) ⟨718694, by rfl⟩ : syracuseStep 958259 = 1437389) B1437389
theorem B958275 : Blo 956588 958275 := bstep (se 1 (by rfl) ⟨718706, by rfl⟩ : syracuseStep 958275 = 1437413) B1437413
theorem B958291 : Blo 956588 958291 := bstep (se 1 (by rfl) ⟨718718, by rfl⟩ : syracuseStep 958291 = 1437437) B1437437
theorem B958307 : Blo 956588 958307 := bstep (se 1 (by rfl) ⟨718730, by rfl⟩ : syracuseStep 958307 = 1437461) B1437461
theorem B958323 : Blo 956588 958323 := bstep (se 1 (by rfl) ⟨718742, by rfl⟩ : syracuseStep 958323 = 1437485) B1437485
theorem B958339 : Blo 956588 958339 := bstep (se 1 (by rfl) ⟨718754, by rfl⟩ : syracuseStep 958339 = 1437509) B1437509
theorem B958355 : Blo 956588 958355 := bstep (se 1 (by rfl) ⟨718766, by rfl⟩ : syracuseStep 958355 = 1437533) B1437533
theorem B958371 : Blo 956588 958371 := bstep (se 1 (by rfl) ⟨718778, by rfl⟩ : syracuseStep 958371 = 1437557) B1437557
theorem B958387 : Blo 956588 958387 := bstep (se 1 (by rfl) ⟨718790, by rfl⟩ : syracuseStep 958387 = 1437581) B1437581
theorem B958403 : Blo 956588 958403 := bstep (se 1 (by rfl) ⟨718802, by rfl⟩ : syracuseStep 958403 = 1437605) B1437605
theorem B958419 : Blo 956588 958419 := bstep (se 1 (by rfl) ⟨718814, by rfl⟩ : syracuseStep 958419 = 1437629) B1437629
theorem B958435 : Blo 956588 958435 := bstep (se 1 (by rfl) ⟨718826, by rfl⟩ : syracuseStep 958435 = 1437653) B1437653
theorem B3645425 : Blo 956588 3645425 := bstep (se 2 (by rfl) ⟨1367034, by rfl⟩ : syracuseStep 3645425 = 2734069) B2734069
theorem B958451 : Blo 956588 958451 := bstep (se 1 (by rfl) ⟨718838, by rfl⟩ : syracuseStep 958451 = 1437677) B1437677
theorem B958467 : Blo 956588 958467 := bstep (se 1 (by rfl) ⟨718850, by rfl⟩ : syracuseStep 958467 = 1437701) B1437701
theorem B958483 : Blo 956588 958483 := bstep (se 1 (by rfl) ⟨718862, by rfl⟩ : syracuseStep 958483 = 1437725) B1437725
theorem B958499 : Blo 956588 958499 := bstep (se 1 (by rfl) ⟨718874, by rfl⟩ : syracuseStep 958499 = 1437749) B1437749
theorem B958515 : Blo 956588 958515 := bstep (se 1 (by rfl) ⟨718886, by rfl⟩ : syracuseStep 958515 = 1437773) B1437773
theorem B958531 : Blo 956588 958531 := bstep (se 1 (by rfl) ⟨718898, by rfl⟩ : syracuseStep 958531 = 1437797) B1437797
theorem B958547 : Blo 956588 958547 := bstep (se 1 (by rfl) ⟨718910, by rfl⟩ : syracuseStep 958547 = 1437821) B1437821
theorem B958563 : Blo 956588 958563 := bstep (se 1 (by rfl) ⟨718922, by rfl⟩ : syracuseStep 958563 = 1437845) B1437845
theorem B958579 : Blo 956588 958579 := bstep (se 1 (by rfl) ⟨718934, by rfl⟩ : syracuseStep 958579 = 1437869) B1437869
theorem B958595 : Blo 956588 958595 := bstep (se 1 (by rfl) ⟨718946, by rfl⟩ : syracuseStep 958595 = 1437893) B1437893
theorem B958611 : Blo 956588 958611 := bstep (se 1 (by rfl) ⟨718958, by rfl⟩ : syracuseStep 958611 = 1437917) B1437917
theorem B958627 : Blo 956588 958627 := bstep (se 1 (by rfl) ⟨718970, by rfl⟩ : syracuseStep 958627 = 1437941) B1437941
theorem B958643 : Blo 956588 958643 := bstep (se 1 (by rfl) ⟨718982, by rfl⟩ : syracuseStep 958643 = 1437965) B1437965
theorem B958659 : Blo 956588 958659 := bstep (se 1 (by rfl) ⟨718994, by rfl⟩ : syracuseStep 958659 = 1437989) B1437989
theorem B958675 : Blo 956588 958675 := bstep (se 1 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 958675 = 1438013) B1438013
theorem B958691 : Blo 956588 958691 := bstep (se 1 (by rfl) ⟨719018, by rfl⟩ : syracuseStep 958691 = 1438037) B1438037
theorem B958707 : Blo 956588 958707 := bstep (se 1 (by rfl) ⟨719030, by rfl⟩ : syracuseStep 958707 = 1438061) B1438061
theorem B958723 : Blo 956588 958723 := bstep (se 1 (by rfl) ⟨719042, by rfl⟩ : syracuseStep 958723 = 1438085) B1438085
theorem B958739 : Blo 956588 958739 := bstep (se 1 (by rfl) ⟨719054, by rfl⟩ : syracuseStep 958739 = 1438109) B1438109
theorem B958755 : Blo 956588 958755 := bstep (se 1 (by rfl) ⟨719066, by rfl⟩ : syracuseStep 958755 = 1438133) B1438133
theorem B2728237 : Blo 956588 2728237 := bstep (se 3 (by rfl) ⟨511544, by rfl⟩ : syracuseStep 2728237 = 1023089) B1023089
theorem B958771 : Blo 956588 958771 := bstep (se 1 (by rfl) ⟨719078, by rfl⟩ : syracuseStep 958771 = 1438157) B1438157
theorem B958787 : Blo 956588 958787 := bstep (se 1 (by rfl) ⟨719090, by rfl⟩ : syracuseStep 958787 = 1438181) B1438181
theorem B2302289 : Blo 956588 2302289 := bstep (se 2 (by rfl) ⟨863358, by rfl⟩ : syracuseStep 2302289 = 1726717) B1726717
theorem B958803 : Blo 956588 958803 := bstep (se 1 (by rfl) ⟨719102, by rfl⟩ : syracuseStep 958803 = 1438205) B1438205
theorem B958819 : Blo 956588 958819 := bstep (se 1 (by rfl) ⟨719114, by rfl⟩ : syracuseStep 958819 = 1438229) B1438229
theorem B958835 : Blo 956588 958835 := bstep (se 1 (by rfl) ⟨719126, by rfl⟩ : syracuseStep 958835 = 1438253) B1438253
theorem B958851 : Blo 956588 958851 := bstep (se 1 (by rfl) ⟨719138, by rfl⟩ : syracuseStep 958851 = 1438277) B1438277
theorem B958867 : Blo 956588 958867 := bstep (se 1 (by rfl) ⟨719150, by rfl⟩ : syracuseStep 958867 = 1438301) B1438301
theorem B958883 : Blo 956588 958883 := bstep (se 1 (by rfl) ⟨719162, by rfl⟩ : syracuseStep 958883 = 1438325) B1438325
theorem B958899 : Blo 956588 958899 := bstep (se 1 (by rfl) ⟨719174, by rfl⟩ : syracuseStep 958899 = 1438349) B1438349
theorem B1024435 : Blo 956588 1024435 := bstep (se 1 (by rfl) ⟨768326, by rfl⟩ : syracuseStep 1024435 = 1536653) B1536653
theorem B958915 : Blo 956588 958915 := bstep (se 1 (by rfl) ⟨719186, by rfl⟩ : syracuseStep 958915 = 1438373) B1438373
theorem B2728397 : Blo 956588 2728397 := bstep (se 3 (by rfl) ⟨511574, by rfl⟩ : syracuseStep 2728397 = 1023149) B1023149
theorem B1614289 : Blo 956588 1614289 := bstep (se 2 (by rfl) ⟨605358, by rfl⟩ : syracuseStep 1614289 = 1210717) B1210717
theorem B958931 : Blo 956588 958931 := bstep (se 1 (by rfl) ⟨719198, by rfl⟩ : syracuseStep 958931 = 1438397) B1438397
theorem B10920419 : Blo 956588 10920419 := bstep (se 1 (by rfl) ⟨8190314, by rfl⟩ : syracuseStep 10920419 = 16380629) B16380629
theorem B958947 : Blo 956588 958947 := bstep (se 1 (by rfl) ⟨719210, by rfl⟩ : syracuseStep 958947 = 1438421) B1438421
theorem B1614323 : Blo 956588 1614323 := bstep (se 1 (by rfl) ⟨1210742, by rfl⟩ : syracuseStep 1614323 = 2421485) B2421485
theorem B958963 : Blo 956588 958963 := bstep (se 1 (by rfl) ⟨719222, by rfl⟩ : syracuseStep 958963 = 1438445) B1438445
theorem B958979 : Blo 956588 958979 := bstep (se 1 (by rfl) ⟨719234, by rfl⟩ : syracuseStep 958979 = 1438469) B1438469
theorem B958995 : Blo 956588 958995 := bstep (se 1 (by rfl) ⟨719246, by rfl⟩ : syracuseStep 958995 = 1438493) B1438493
theorem B959011 : Blo 956588 959011 := bstep (se 1 (by rfl) ⟨719258, by rfl⟩ : syracuseStep 959011 = 1438517) B1438517
theorem B959027 : Blo 956588 959027 := bstep (se 1 (by rfl) ⟨719270, by rfl⟩ : syracuseStep 959027 = 1438541) B1438541
theorem B959043 : Blo 956588 959043 := bstep (se 1 (by rfl) ⟨719282, by rfl⟩ : syracuseStep 959043 = 1438565) B1438565
theorem B959059 : Blo 956588 959059 := bstep (se 1 (by rfl) ⟨719294, by rfl⟩ : syracuseStep 959059 = 1438589) B1438589
theorem B959075 : Blo 956588 959075 := bstep (se 1 (by rfl) ⟨719306, by rfl⟩ : syracuseStep 959075 = 1438613) B1438613
theorem B1614451 : Blo 956588 1614451 := bstep (se 1 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 1614451 = 2421677) B2421677
theorem B959091 : Blo 956588 959091 := bstep (se 1 (by rfl) ⟨719318, by rfl⟩ : syracuseStep 959091 = 1438637) B1438637
theorem B2728579 : Blo 956588 2728579 := bstep (se 1 (by rfl) ⟨2046434, by rfl⟩ : syracuseStep 2728579 = 4092869) B4092869
theorem B959107 : Blo 956588 959107 := bstep (se 1 (by rfl) ⟨719330, by rfl⟩ : syracuseStep 959107 = 1438661) B1438661
theorem B3646093 : Blo 956588 3646093 := bstep (se 3 (by rfl) ⟨683642, by rfl⟩ : syracuseStep 3646093 = 1367285) B1367285
theorem B959123 : Blo 956588 959123 := bstep (se 1 (by rfl) ⟨719342, by rfl⟩ : syracuseStep 959123 = 1438685) B1438685
theorem B959139 : Blo 956588 959139 := bstep (se 1 (by rfl) ⟨719354, by rfl⟩ : syracuseStep 959139 = 1438709) B1438709
theorem B959155 : Blo 956588 959155 := bstep (se 1 (by rfl) ⟨719366, by rfl⟩ : syracuseStep 959155 = 1438733) B1438733
theorem B959171 : Blo 956588 959171 := bstep (se 1 (by rfl) ⟨719378, by rfl⟩ : syracuseStep 959171 = 1438757) B1438757
theorem B959187 : Blo 956588 959187 := bstep (se 1 (by rfl) ⟨719390, by rfl⟩ : syracuseStep 959187 = 1438781) B1438781
theorem B959203 : Blo 956588 959203 := bstep (se 1 (by rfl) ⟨719402, by rfl⟩ : syracuseStep 959203 = 1438805) B1438805
theorem B959219 : Blo 956588 959219 := bstep (se 1 (by rfl) ⟨719414, by rfl⟩ : syracuseStep 959219 = 1438829) B1438829
theorem B1614593 : Blo 956588 1614593 := bstep (se 2 (by rfl) ⟨605472, by rfl⟩ : syracuseStep 1614593 = 1210945) B1210945
theorem B959235 : Blo 956588 959235 := bstep (se 1 (by rfl) ⟨719426, by rfl⟩ : syracuseStep 959235 = 1438853) B1438853
theorem B959251 : Blo 956588 959251 := bstep (se 1 (by rfl) ⟨719438, by rfl⟩ : syracuseStep 959251 = 1438877) B1438877
theorem B959267 : Blo 956588 959267 := bstep (se 1 (by rfl) ⟨719450, by rfl⟩ : syracuseStep 959267 = 1438901) B1438901
theorem B959283 : Blo 956588 959283 := bstep (se 1 (by rfl) ⟨719462, by rfl⟩ : syracuseStep 959283 = 1438925) B1438925
theorem B959299 : Blo 956588 959299 := bstep (se 1 (by rfl) ⟨719474, by rfl⟩ : syracuseStep 959299 = 1438949) B1438949
theorem B959315 : Blo 956588 959315 := bstep (se 1 (by rfl) ⟨719486, by rfl⟩ : syracuseStep 959315 = 1438973) B1438973
theorem B959331 : Blo 956588 959331 := bstep (se 1 (by rfl) ⟨719498, by rfl⟩ : syracuseStep 959331 = 1438997) B1438997
theorem B959347 : Blo 956588 959347 := bstep (se 1 (by rfl) ⟨719510, by rfl⟩ : syracuseStep 959347 = 1439021) B1439021
theorem B1614721 : Blo 956588 1614721 := bstep (se 2 (by rfl) ⟨605520, by rfl⟩ : syracuseStep 1614721 = 1211041) B1211041
theorem B959363 : Blo 956588 959363 := bstep (se 1 (by rfl) ⟨719522, by rfl⟩ : syracuseStep 959363 = 1439045) B1439045
theorem B1778563 : Blo 956588 1778563 := bstep (se 1 (by rfl) ⟨1333922, by rfl⟩ : syracuseStep 1778563 = 2667845) B2667845
theorem B959379 : Blo 956588 959379 := bstep (se 1 (by rfl) ⟨719534, by rfl⟩ : syracuseStep 959379 = 1439069) B1439069
theorem B1614755 : Blo 956588 1614755 := bstep (se 1 (by rfl) ⟨1211066, by rfl⟩ : syracuseStep 1614755 = 2422133) B2422133
theorem B959395 : Blo 956588 959395 := bstep (se 1 (by rfl) ⟨719546, by rfl⟩ : syracuseStep 959395 = 1439093) B1439093
theorem B959411 : Blo 956588 959411 := bstep (se 1 (by rfl) ⟨719558, by rfl⟩ : syracuseStep 959411 = 1439117) B1439117
theorem B959427 : Blo 956588 959427 := bstep (se 1 (by rfl) ⟨719570, by rfl⟩ : syracuseStep 959427 = 1439141) B1439141
theorem B959443 : Blo 956588 959443 := bstep (se 1 (by rfl) ⟨719582, by rfl⟩ : syracuseStep 959443 = 1439165) B1439165
theorem B959459 : Blo 956588 959459 := bstep (se 1 (by rfl) ⟨719594, by rfl⟩ : syracuseStep 959459 = 1439189) B1439189
theorem B4858865 : Blo 956588 4858865 := bstep (se 2 (by rfl) ⟨1822074, by rfl⟩ : syracuseStep 4858865 = 3644149) B3644149
theorem B959475 : Blo 956588 959475 := bstep (se 1 (by rfl) ⟨719606, by rfl⟩ : syracuseStep 959475 = 1439213) B1439213
theorem B959491 : Blo 956588 959491 := bstep (se 1 (by rfl) ⟨719618, by rfl⟩ : syracuseStep 959491 = 1439237) B1439237
theorem B959507 : Blo 956588 959507 := bstep (se 1 (by rfl) ⟨719630, by rfl⟩ : syracuseStep 959507 = 1439261) B1439261
theorem B1614883 : Blo 956588 1614883 := bstep (se 1 (by rfl) ⟨1211162, by rfl⟩ : syracuseStep 1614883 = 2422325) B2422325
theorem B959523 : Blo 956588 959523 := bstep (se 1 (by rfl) ⟨719642, by rfl⟩ : syracuseStep 959523 = 1439285) B1439285
theorem B959539 : Blo 956588 959539 := bstep (se 1 (by rfl) ⟨719654, by rfl⟩ : syracuseStep 959539 = 1439309) B1439309
theorem B959555 : Blo 956588 959555 := bstep (se 1 (by rfl) ⟨719666, by rfl⟩ : syracuseStep 959555 = 1439333) B1439333
theorem B959571 : Blo 956588 959571 := bstep (se 1 (by rfl) ⟨719678, by rfl⟩ : syracuseStep 959571 = 1439357) B1439357
theorem B959587 : Blo 956588 959587 := bstep (se 1 (by rfl) ⟨719690, by rfl⟩ : syracuseStep 959587 = 1439381) B1439381
theorem B959603 : Blo 956588 959603 := bstep (se 1 (by rfl) ⟨719702, by rfl⟩ : syracuseStep 959603 = 1439405) B1439405
theorem B959619 : Blo 956588 959619 := bstep (se 1 (by rfl) ⟨719714, by rfl⟩ : syracuseStep 959619 = 1439429) B1439429
theorem B959635 : Blo 956588 959635 := bstep (se 1 (by rfl) ⟨719726, by rfl⟩ : syracuseStep 959635 = 1439453) B1439453
theorem B959651 : Blo 956588 959651 := bstep (se 1 (by rfl) ⟨719738, by rfl⟩ : syracuseStep 959651 = 1439477) B1439477
theorem B1615025 : Blo 956588 1615025 := bstep (se 2 (by rfl) ⟨605634, by rfl⟩ : syracuseStep 1615025 = 1211269) B1211269
theorem B959667 : Blo 956588 959667 := bstep (se 1 (by rfl) ⟨719750, by rfl⟩ : syracuseStep 959667 = 1439501) B1439501
theorem B959683 : Blo 956588 959683 := bstep (se 1 (by rfl) ⟨719762, by rfl⟩ : syracuseStep 959683 = 1439525) B1439525
theorem B959699 : Blo 956588 959699 := bstep (se 1 (by rfl) ⟨719774, by rfl⟩ : syracuseStep 959699 = 1439549) B1439549
theorem B959715 : Blo 956588 959715 := bstep (se 1 (by rfl) ⟨719786, by rfl⟩ : syracuseStep 959715 = 1439573) B1439573
theorem B959731 : Blo 956588 959731 := bstep (se 1 (by rfl) ⟨719798, by rfl⟩ : syracuseStep 959731 = 1439597) B1439597
theorem B959747 : Blo 956588 959747 := bstep (se 1 (by rfl) ⟨719810, by rfl⟩ : syracuseStep 959747 = 1439621) B1439621
theorem B959763 : Blo 956588 959763 := bstep (se 1 (by rfl) ⟨719822, by rfl⟩ : syracuseStep 959763 = 1439645) B1439645
theorem B959779 : Blo 956588 959779 := bstep (se 1 (by rfl) ⟨719834, by rfl⟩ : syracuseStep 959779 = 1439669) B1439669
theorem B1615153 : Blo 956588 1615153 := bstep (se 2 (by rfl) ⟨605682, by rfl⟩ : syracuseStep 1615153 = 1211365) B1211365
theorem B959795 : Blo 956588 959795 := bstep (se 1 (by rfl) ⟨719846, by rfl⟩ : syracuseStep 959795 = 1439693) B1439693
theorem B959811 : Blo 956588 959811 := bstep (se 1 (by rfl) ⟨719858, by rfl⟩ : syracuseStep 959811 = 1439717) B1439717
theorem B1615187 : Blo 956588 1615187 := bstep (se 1 (by rfl) ⟨1211390, by rfl⟩ : syracuseStep 1615187 = 2422781) B2422781
theorem B959827 : Blo 956588 959827 := bstep (se 1 (by rfl) ⟨719870, by rfl⟩ : syracuseStep 959827 = 1439741) B1439741
theorem B959843 : Blo 956588 959843 := bstep (se 1 (by rfl) ⟨719882, by rfl⟩ : syracuseStep 959843 = 1439765) B1439765
theorem B6137201 : Blo 956588 6137201 := bstep (se 2 (by rfl) ⟨2301450, by rfl⟩ : syracuseStep 6137201 = 4602901) B4602901
theorem B959859 : Blo 956588 959859 := bstep (se 1 (by rfl) ⟨719894, by rfl⟩ : syracuseStep 959859 = 1439789) B1439789
theorem B959875 : Blo 956588 959875 := bstep (se 1 (by rfl) ⟨719906, by rfl⟩ : syracuseStep 959875 = 1439813) B1439813
theorem B12166541 : Blo 956588 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B959891 : Blo 956588 959891 := bstep (se 1 (by rfl) ⟨719918, by rfl⟩ : syracuseStep 959891 = 1439837) B1439837
theorem B959907 : Blo 956588 959907 := bstep (se 1 (by rfl) ⟨719930, by rfl⟩ : syracuseStep 959907 = 1439861) B1439861
theorem B3646883 : Blo 956588 3646883 := bstep (se 1 (by rfl) ⟨2735162, by rfl⟩ : syracuseStep 3646883 = 5470325) B5470325
theorem B959923 : Blo 956588 959923 := bstep (se 1 (by rfl) ⟨719942, by rfl⟩ : syracuseStep 959923 = 1439885) B1439885
theorem B959939 : Blo 956588 959939 := bstep (se 1 (by rfl) ⟨719954, by rfl⟩ : syracuseStep 959939 = 1439909) B1439909
theorem B1615315 : Blo 956588 1615315 := bstep (se 1 (by rfl) ⟨1211486, by rfl⟩ : syracuseStep 1615315 = 2422973) B2422973
theorem B959955 : Blo 956588 959955 := bstep (se 1 (by rfl) ⟨719966, by rfl⟩ : syracuseStep 959955 = 1439933) B1439933
theorem B959971 : Blo 956588 959971 := bstep (se 1 (by rfl) ⟨719978, by rfl⟩ : syracuseStep 959971 = 1439957) B1439957
theorem B1025507 : Blo 956588 1025507 := bstep (se 1 (by rfl) ⟨769130, by rfl⟩ : syracuseStep 1025507 = 1538261) B1538261
theorem B959987 : Blo 956588 959987 := bstep (se 1 (by rfl) ⟨719990, by rfl⟩ : syracuseStep 959987 = 1439981) B1439981
theorem B960003 : Blo 956588 960003 := bstep (se 1 (by rfl) ⟨720002, by rfl⟩ : syracuseStep 960003 = 1440005) B1440005
theorem B960019 : Blo 956588 960019 := bstep (se 1 (by rfl) ⟨720014, by rfl⟩ : syracuseStep 960019 = 1440029) B1440029
theorem B960035 : Blo 956588 960035 := bstep (se 1 (by rfl) ⟨720026, by rfl⟩ : syracuseStep 960035 = 1440053) B1440053
theorem B960051 : Blo 956588 960051 := bstep (se 1 (by rfl) ⟨720038, by rfl⟩ : syracuseStep 960051 = 1440077) B1440077
theorem B960067 : Blo 956588 960067 := bstep (se 1 (by rfl) ⟨720050, by rfl⟩ : syracuseStep 960067 = 1440101) B1440101
theorem B2958925 : Blo 956588 2958925 := bstep (se 3 (by rfl) ⟨554798, by rfl⟩ : syracuseStep 2958925 = 1109597) B1109597
theorem B960083 : Blo 956588 960083 := bstep (se 1 (by rfl) ⟨720062, by rfl⟩ : syracuseStep 960083 = 1440125) B1440125
theorem B1615457 : Blo 956588 1615457 := bstep (se 2 (by rfl) ⟨605796, by rfl⟩ : syracuseStep 1615457 = 1211593) B1211593
theorem B960099 : Blo 956588 960099 := bstep (se 1 (by rfl) ⟨720074, by rfl⟩ : syracuseStep 960099 = 1440149) B1440149
theorem B960115 : Blo 956588 960115 := bstep (se 1 (by rfl) ⟨720086, by rfl⟩ : syracuseStep 960115 = 1440173) B1440173
theorem B960131 : Blo 956588 960131 := bstep (se 1 (by rfl) ⟨720098, by rfl⟩ : syracuseStep 960131 = 1440197) B1440197
theorem B960147 : Blo 956588 960147 := bstep (se 1 (by rfl) ⟨720110, by rfl⟩ : syracuseStep 960147 = 1440221) B1440221
theorem B960163 : Blo 956588 960163 := bstep (se 1 (by rfl) ⟨720122, by rfl⟩ : syracuseStep 960163 = 1440245) B1440245
theorem B960179 : Blo 956588 960179 := bstep (se 1 (by rfl) ⟨720134, by rfl⟩ : syracuseStep 960179 = 1440269) B1440269
theorem B960195 : Blo 956588 960195 := bstep (se 1 (by rfl) ⟨720146, by rfl⟩ : syracuseStep 960195 = 1440293) B1440293
theorem B960211 : Blo 956588 960211 := bstep (se 1 (by rfl) ⟨720158, by rfl⟩ : syracuseStep 960211 = 1440317) B1440317
theorem B1615585 : Blo 956588 1615585 := bstep (se 2 (by rfl) ⟨605844, by rfl⟩ : syracuseStep 1615585 = 1211689) B1211689
theorem B960227 : Blo 956588 960227 := bstep (se 1 (by rfl) ⟨720170, by rfl⟩ : syracuseStep 960227 = 1440341) B1440341
theorem B5449457 : Blo 956588 5449457 := bstep (se 2 (by rfl) ⟨2043546, by rfl⟩ : syracuseStep 5449457 = 4087093) B4087093
theorem B960243 : Blo 956588 960243 := bstep (se 1 (by rfl) ⟨720182, by rfl⟩ : syracuseStep 960243 = 1440365) B1440365
theorem B1615619 : Blo 956588 1615619 := bstep (se 1 (by rfl) ⟨1211714, by rfl⟩ : syracuseStep 1615619 = 2423429) B2423429
theorem B960259 : Blo 956588 960259 := bstep (se 1 (by rfl) ⟨720194, by rfl⟩ : syracuseStep 960259 = 1440389) B1440389
theorem B960275 : Blo 956588 960275 := bstep (se 1 (by rfl) ⟨720206, by rfl⟩ : syracuseStep 960275 = 1440413) B1440413
theorem B960291 : Blo 956588 960291 := bstep (se 1 (by rfl) ⟨720218, by rfl⟩ : syracuseStep 960291 = 1440437) B1440437
theorem B960307 : Blo 956588 960307 := bstep (se 1 (by rfl) ⟨720230, by rfl⟩ : syracuseStep 960307 = 1440461) B1440461
theorem B960323 : Blo 956588 960323 := bstep (se 1 (by rfl) ⟨720242, by rfl⟩ : syracuseStep 960323 = 1440485) B1440485
theorem B960339 : Blo 956588 960339 := bstep (se 1 (by rfl) ⟨720254, by rfl⟩ : syracuseStep 960339 = 1440509) B1440509
theorem B960355 : Blo 956588 960355 := bstep (se 1 (by rfl) ⟨720266, by rfl⟩ : syracuseStep 960355 = 1440533) B1440533
theorem B960371 : Blo 956588 960371 := bstep (se 1 (by rfl) ⟨720278, by rfl⟩ : syracuseStep 960371 = 1440557) B1440557
theorem B1615747 : Blo 956588 1615747 := bstep (se 1 (by rfl) ⟨1211810, by rfl⟩ : syracuseStep 1615747 = 2423621) B2423621
theorem B960387 : Blo 956588 960387 := bstep (se 1 (by rfl) ⟨720290, by rfl⟩ : syracuseStep 960387 = 1440581) B1440581
theorem B960403 : Blo 956588 960403 := bstep (se 1 (by rfl) ⟨720302, by rfl⟩ : syracuseStep 960403 = 1440605) B1440605
theorem B960419 : Blo 956588 960419 := bstep (se 1 (by rfl) ⟨720314, by rfl⟩ : syracuseStep 960419 = 1440629) B1440629
theorem B2762669 : Blo 956588 2762669 := bstep (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) B1036001
theorem B960435 : Blo 956588 960435 := bstep (se 1 (by rfl) ⟨720326, by rfl⟩ : syracuseStep 960435 = 1440653) B1440653
theorem B960451 : Blo 956588 960451 := bstep (se 1 (by rfl) ⟨720338, by rfl⟩ : syracuseStep 960451 = 1440677) B1440677
theorem B960467 : Blo 956588 960467 := bstep (se 1 (by rfl) ⟨720350, by rfl⟩ : syracuseStep 960467 = 1440701) B1440701
theorem B960483 : Blo 956588 960483 := bstep (se 1 (by rfl) ⟨720362, by rfl⟩ : syracuseStep 960483 = 1440725) B1440725
theorem B2074609 : Blo 956588 2074609 := bstep (se 2 (by rfl) ⟨777978, by rfl⟩ : syracuseStep 2074609 = 1555957) B1555957
theorem B2729969 : Blo 956588 2729969 := bstep (se 2 (by rfl) ⟨1023738, by rfl⟩ : syracuseStep 2729969 = 2047477) B2047477
theorem B960499 : Blo 956588 960499 := bstep (se 1 (by rfl) ⟨720374, by rfl⟩ : syracuseStep 960499 = 1440749) B1440749
theorem B960515 : Blo 956588 960515 := bstep (se 1 (by rfl) ⟨720386, by rfl⟩ : syracuseStep 960515 = 1440773) B1440773
theorem B1615889 : Blo 956588 1615889 := bstep (se 2 (by rfl) ⟨605958, by rfl⟩ : syracuseStep 1615889 = 1211917) B1211917
theorem B960531 : Blo 956588 960531 := bstep (se 1 (by rfl) ⟨720398, by rfl⟩ : syracuseStep 960531 = 1440797) B1440797
theorem B20719637 : Blo 956588 20719637 := bstep (se 6 (by rfl) ⟨485616, by rfl⟩ : syracuseStep 20719637 = 971233) B971233
theorem B960547 : Blo 956588 960547 := bstep (se 1 (by rfl) ⟨720410, by rfl⟩ : syracuseStep 960547 = 1440821) B1440821
theorem B5253169 : Blo 956588 5253169 := bstep (se 2 (by rfl) ⟨1969938, by rfl⟩ : syracuseStep 5253169 = 3939877) B3939877
theorem B960563 : Blo 956588 960563 := bstep (se 1 (by rfl) ⟨720422, by rfl⟩ : syracuseStep 960563 = 1440845) B1440845
theorem B960579 : Blo 956588 960579 := bstep (se 1 (by rfl) ⟨720434, by rfl⟩ : syracuseStep 960579 = 1440869) B1440869
theorem B1616017 : Blo 956588 1616017 := bstep (se 2 (by rfl) ⟨606006, by rfl⟩ : syracuseStep 1616017 = 1212013) B1212013
theorem B1616051 : Blo 956588 1616051 := bstep (se 1 (by rfl) ⟨1212038, by rfl⟩ : syracuseStep 1616051 = 2424077) B2424077
theorem B6138125 : Blo 956588 6138125 := bstep (se 3 (by rfl) ⟨1150898, by rfl⟩ : syracuseStep 6138125 = 2301797) B2301797
theorem B1616179 : Blo 956588 1616179 := bstep (se 1 (by rfl) ⟨1212134, by rfl⟩ : syracuseStep 1616179 = 2424269) B2424269
theorem B4860323 : Blo 956588 4860323 := bstep (se 1 (by rfl) ⟨3645242, by rfl⟩ : syracuseStep 4860323 = 7290485) B7290485
theorem B1616321 : Blo 956588 1616321 := bstep (se 2 (by rfl) ⟨606120, by rfl⟩ : syracuseStep 1616321 = 1212241) B1212241
theorem B1616449 : Blo 956588 1616449 := bstep (se 2 (by rfl) ⟨606168, by rfl⟩ : syracuseStep 1616449 = 1212337) B1212337
theorem B1616483 : Blo 956588 1616483 := bstep (se 1 (by rfl) ⟨1212362, by rfl⟩ : syracuseStep 1616483 = 2424725) B2424725
theorem B2960003 : Blo 956588 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B1616611 : Blo 956588 1616611 := bstep (se 1 (by rfl) ⟨1212458, by rfl⟩ : syracuseStep 1616611 = 2424917) B2424917
theorem B1616753 : Blo 956588 1616753 := bstep (se 2 (by rfl) ⟨606282, by rfl⟩ : syracuseStep 1616753 = 1212565) B1212565
theorem B2304931 : Blo 956588 2304931 := bstep (se 1 (by rfl) ⟨1728698, by rfl⟩ : syracuseStep 2304931 = 3457397) B3457397
theorem B2730925 : Blo 956588 2730925 := bstep (se 3 (by rfl) ⟨512048, by rfl⟩ : syracuseStep 2730925 = 1024097) B1024097
theorem B1616881 : Blo 956588 1616881 := bstep (se 2 (by rfl) ⟨606330, by rfl⟩ : syracuseStep 1616881 = 1212661) B1212661
theorem B1616915 : Blo 956588 1616915 := bstep (se 1 (by rfl) ⟨1212686, by rfl⟩ : syracuseStep 1616915 = 2425373) B2425373
theorem B6237253 : Blo 956588 6237253 := bstep (se 4 (by rfl) ⟨584742, by rfl⟩ : syracuseStep 6237253 = 1169485) B1169485
theorem B2731153 : Blo 956588 2731153 := bstep (se 2 (by rfl) ⟨1024182, by rfl⟩ : syracuseStep 2731153 = 2048365) B2048365
theorem B1617043 : Blo 956588 1617043 := bstep (se 1 (by rfl) ⟨1212782, by rfl⟩ : syracuseStep 1617043 = 2425565) B2425565
theorem B5450915 : Blo 956588 5450915 := bstep (se 1 (by rfl) ⟨4088186, by rfl⟩ : syracuseStep 5450915 = 8176373) B8176373
theorem B4861133 : Blo 956588 4861133 := bstep (se 3 (by rfl) ⟨911462, by rfl⟩ : syracuseStep 4861133 = 1822925) B1822925
theorem B1617185 : Blo 956588 1617185 := bstep (se 2 (by rfl) ⟨606444, by rfl⟩ : syracuseStep 1617185 = 1212889) B1212889
theorem B2731313 : Blo 956588 2731313 := bstep (se 2 (by rfl) ⟨1024242, by rfl⟩ : syracuseStep 2731313 = 2048485) B2048485
theorem B1617313 : Blo 956588 1617313 := bstep (se 2 (by rfl) ⟨606492, by rfl⟩ : syracuseStep 1617313 = 1212985) B1212985
theorem B2731427 : Blo 956588 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B1617347 : Blo 956588 1617347 := bstep (se 1 (by rfl) ⟨1213010, by rfl⟩ : syracuseStep 1617347 = 2426021) B2426021
theorem B3452465 : Blo 956588 3452465 := bstep (se 2 (by rfl) ⟨1294674, by rfl⟩ : syracuseStep 3452465 = 2589349) B2589349
theorem B1617475 : Blo 956588 1617475 := bstep (se 1 (by rfl) ⟨1213106, by rfl⟩ : syracuseStep 1617475 = 2426213) B2426213
theorem B1617617 : Blo 956588 1617617 := bstep (se 2 (by rfl) ⟨606606, by rfl⟩ : syracuseStep 1617617 = 1213213) B1213213
theorem B3878705 : Blo 956588 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B7286597 : Blo 956588 7286597 := bstep (se 4 (by rfl) ⟨683118, by rfl⟩ : syracuseStep 7286597 = 1366237) B1366237
theorem B1617745 : Blo 956588 1617745 := bstep (se 2 (by rfl) ⟨606654, by rfl⟩ : syracuseStep 1617745 = 1213309) B1213309
theorem B1617779 : Blo 956588 1617779 := bstep (se 1 (by rfl) ⟨1213334, by rfl⟩ : syracuseStep 1617779 = 2426669) B2426669
theorem B3878833 : Blo 956588 3878833 := bstep (se 2 (by rfl) ⟨1454562, by rfl⟩ : syracuseStep 3878833 = 2909125) B2909125
theorem B2076625 : Blo 956588 2076625 := bstep (se 2 (by rfl) ⟨778734, by rfl⟩ : syracuseStep 2076625 = 1557469) B1557469
theorem B1617907 : Blo 956588 1617907 := bstep (se 1 (by rfl) ⟨1213430, by rfl⟩ : syracuseStep 1617907 = 2426861) B2426861
theorem B29503541 : Blo 956588 29503541 := bstep (se 5 (by rfl) ⟨1382978, by rfl⟩ : syracuseStep 29503541 = 2765957) B2765957
theorem B2306161 : Blo 956588 2306161 := bstep (se 2 (by rfl) ⟨864810, by rfl⟩ : syracuseStep 2306161 = 1729621) B1729621
theorem B1618049 : Blo 956588 1618049 := bstep (se 2 (by rfl) ⟨606768, by rfl⟩ : syracuseStep 1618049 = 1213537) B1213537
theorem B4206755 : Blo 956588 4206755 := bstep (se 1 (by rfl) ⟨3155066, by rfl⟩ : syracuseStep 4206755 = 6310133) B6310133
theorem B1618177 : Blo 956588 1618177 := bstep (se 2 (by rfl) ⟨606816, by rfl⟩ : syracuseStep 1618177 = 1213633) B1213633
theorem B1618211 : Blo 956588 1618211 := bstep (se 1 (by rfl) ⟨1213658, by rfl⟩ : syracuseStep 1618211 = 2427317) B2427317
theorem B1945937 : Blo 956588 1945937 := bstep (se 2 (by rfl) ⟨729726, by rfl⟩ : syracuseStep 1945937 = 1459453) B1459453
theorem B2044291 : Blo 956588 2044291 := bstep (se 1 (by rfl) ⟨1533218, by rfl⟩ : syracuseStep 2044291 = 3066437) B3066437
theorem B2732429 : Blo 956588 2732429 := bstep (se 3 (by rfl) ⟨512330, by rfl⟩ : syracuseStep 2732429 = 1024661) B1024661
theorem B1618339 : Blo 956588 1618339 := bstep (se 1 (by rfl) ⟨1213754, by rfl⟩ : syracuseStep 1618339 = 2427509) B2427509
theorem B1618481 : Blo 956588 1618481 := bstep (se 2 (by rfl) ⟨606930, by rfl⟩ : syracuseStep 1618481 = 1213861) B1213861
theorem B2732611 : Blo 956588 2732611 := bstep (se 1 (by rfl) ⟨2049458, by rfl⟩ : syracuseStep 2732611 = 4098917) B4098917
theorem B1618609 : Blo 956588 1618609 := bstep (se 2 (by rfl) ⟨606978, by rfl⟩ : syracuseStep 1618609 = 1213957) B1213957
theorem B2765507 : Blo 956588 2765507 := bstep (se 1 (by rfl) ⟨2074130, by rfl⟩ : syracuseStep 2765507 = 4148261) B4148261
theorem B1618643 : Blo 956588 1618643 := bstep (se 1 (by rfl) ⟨1213982, by rfl⟩ : syracuseStep 1618643 = 2427965) B2427965
theorem B2732771 : Blo 956588 2732771 := bstep (se 1 (by rfl) ⟨2049578, by rfl⟩ : syracuseStep 2732771 = 4099157) B4099157
theorem B1618771 : Blo 956588 1618771 := bstep (se 1 (by rfl) ⟨1214078, by rfl⟩ : syracuseStep 1618771 = 2428157) B2428157
theorem B1618913 : Blo 956588 1618913 := bstep (se 2 (by rfl) ⟨607092, by rfl⟩ : syracuseStep 1618913 = 1214185) B1214185
theorem B1619041 : Blo 956588 1619041 := bstep (se 2 (by rfl) ⟨607140, by rfl⟩ : syracuseStep 1619041 = 1214281) B1214281
theorem B1619075 : Blo 956588 1619075 := bstep (se 1 (by rfl) ⟨1214306, by rfl⟩ : syracuseStep 1619075 = 2428613) B2428613
theorem B1455329 : Blo 956588 1455329 := bstep (se 2 (by rfl) ⟨545748, by rfl⟩ : syracuseStep 1455329 = 1091497) B1091497
theorem B1619203 : Blo 956588 1619203 := bstep (se 1 (by rfl) ⟨1214402, by rfl⟩ : syracuseStep 1619203 = 2428805) B2428805
theorem B4142477 : Blo 956588 4142477 := bstep (se 3 (by rfl) ⟨776714, by rfl⟩ : syracuseStep 4142477 = 1553429) B1553429
theorem B1619345 : Blo 956588 1619345 := bstep (se 2 (by rfl) ⟨607254, by rfl⟩ : syracuseStep 1619345 = 1214509) B1214509
theorem B1619473 : Blo 956588 1619473 := bstep (se 2 (by rfl) ⟨607302, by rfl⟩ : syracuseStep 1619473 = 1214605) B1214605
theorem B1619507 : Blo 956588 1619507 := bstep (se 1 (by rfl) ⟨1214630, by rfl⟩ : syracuseStep 1619507 = 2429261) B2429261
theorem B1619635 : Blo 956588 1619635 := bstep (se 1 (by rfl) ⟨1214726, by rfl⟩ : syracuseStep 1619635 = 2429453) B2429453
theorem B1816273 : Blo 956588 1816273 := bstep (se 2 (by rfl) ⟨681102, by rfl⟩ : syracuseStep 1816273 = 1362205) B1362205
theorem B2733841 : Blo 956588 2733841 := bstep (se 2 (by rfl) ⟨1025190, by rfl⟩ : syracuseStep 2733841 = 2050381) B2050381
theorem B27997973 : Blo 956588 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B1619777 : Blo 956588 1619777 := bstep (se 2 (by rfl) ⟨607416, by rfl⟩ : syracuseStep 1619777 = 1214833) B1214833
theorem B3880781 : Blo 956588 3880781 := bstep (se 3 (by rfl) ⟨727646, by rfl⟩ : syracuseStep 3880781 = 1455293) B1455293
theorem B3192721 : Blo 956588 3192721 := bstep (se 2 (by rfl) ⟨1197270, by rfl⟩ : syracuseStep 3192721 = 2394541) B2394541
theorem B1619905 : Blo 956588 1619905 := bstep (se 2 (by rfl) ⟨607464, by rfl⟩ : syracuseStep 1619905 = 1214929) B1214929
theorem B3880909 : Blo 956588 3880909 := bstep (se 3 (by rfl) ⟨727670, by rfl⟩ : syracuseStep 3880909 = 1455341) B1455341
theorem B1619939 : Blo 956588 1619939 := bstep (se 1 (by rfl) ⟨1214954, by rfl⟩ : syracuseStep 1619939 = 2429909) B2429909
theorem B3880973 : Blo 956588 3880973 := bstep (se 3 (by rfl) ⟨727682, by rfl⟩ : syracuseStep 3880973 = 1455365) B1455365
theorem B1620067 : Blo 956588 1620067 := bstep (se 1 (by rfl) ⟨1215050, by rfl⟩ : syracuseStep 1620067 = 2430101) B2430101
theorem B8173709 : Blo 956588 8173709 := bstep (se 3 (by rfl) ⟨1532570, by rfl⟩ : syracuseStep 8173709 = 3065141) B3065141
theorem B2046161 : Blo 956588 2046161 := bstep (se 2 (by rfl) ⟨767310, by rfl⟩ : syracuseStep 2046161 = 1534621) B1534621
theorem B1620209 : Blo 956588 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B1620337 : Blo 956588 1620337 := bstep (se 2 (by rfl) ⟨607626, by rfl⟩ : syracuseStep 1620337 = 1215253) B1215253
theorem B1620371 : Blo 956588 1620371 := bstep (se 1 (by rfl) ⟨1215278, by rfl⟩ : syracuseStep 1620371 = 2430557) B2430557
theorem B2243089 : Blo 956588 2243089 := bstep (se 2 (by rfl) ⟨841158, by rfl⟩ : syracuseStep 2243089 = 1682317) B1682317
theorem B1620499 : Blo 956588 1620499 := bstep (se 1 (by rfl) ⟨1215374, by rfl⟩ : syracuseStep 1620499 = 2430749) B2430749
theorem B1620641 : Blo 956588 1620641 := bstep (se 2 (by rfl) ⟨607740, by rfl⟩ : syracuseStep 1620641 = 1215481) B1215481
theorem B1817329 : Blo 956588 1817329 := bstep (se 2 (by rfl) ⟨681498, by rfl⟩ : syracuseStep 1817329 = 1362997) B1362997
theorem B1620769 : Blo 956588 1620769 := bstep (se 2 (by rfl) ⟨607788, by rfl⟩ : syracuseStep 1620769 = 1215577) B1215577
theorem B1620803 : Blo 956588 1620803 := bstep (se 1 (by rfl) ⟨1215602, by rfl⟩ : syracuseStep 1620803 = 2431205) B2431205
theorem B1620931 : Blo 956588 1620931 := bstep (se 1 (by rfl) ⟨1215698, by rfl⟩ : syracuseStep 1620931 = 2431397) B2431397
theorem B1752035 : Blo 956588 1752035 := bstep (se 1 (by rfl) ⟨1314026, by rfl⟩ : syracuseStep 1752035 = 2628053) B2628053
theorem B2735117 : Blo 956588 2735117 := bstep (se 3 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 2735117 = 1025669) B1025669
theorem B2047025 : Blo 956588 2047025 := bstep (se 2 (by rfl) ⟨767634, by rfl⟩ : syracuseStep 2047025 = 1535269) B1535269
theorem B1817731 : Blo 956588 1817731 := bstep (se 1 (by rfl) ⟨1363298, by rfl⟩ : syracuseStep 1817731 = 2726597) B2726597
theorem B1817777 : Blo 956588 1817777 := bstep (se 2 (by rfl) ⟨681666, by rfl⟩ : syracuseStep 1817777 = 1363333) B1363333
theorem B2735299 : Blo 956588 2735299 := bstep (se 1 (by rfl) ⟨2051474, by rfl⟩ : syracuseStep 2735299 = 4102949) B4102949
theorem B2735345 : Blo 956588 2735345 := bstep (se 2 (by rfl) ⟨1025754, by rfl⟩ : syracuseStep 2735345 = 2051509) B2051509
theorem B3882275 : Blo 956588 3882275 := bstep (se 1 (by rfl) ⟨2911706, by rfl⟩ : syracuseStep 3882275 = 5823413) B5823413
theorem B1457507 : Blo 956588 1457507 := bstep (se 1 (by rfl) ⟨1093130, by rfl⟩ : syracuseStep 1457507 = 2186261) B2186261
theorem B1293745 : Blo 956588 1293745 := bstep (se 2 (by rfl) ⟨485154, by rfl⟩ : syracuseStep 1293745 = 970309) B970309
theorem B1818065 : Blo 956588 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B3882467 : Blo 956588 3882467 := bstep (se 1 (by rfl) ⟨2911850, by rfl⟩ : syracuseStep 3882467 = 5823701) B5823701
theorem B1556275 : Blo 956588 1556275 := bstep (se 1 (by rfl) ⟨1167206, by rfl⟩ : syracuseStep 1556275 = 2334413) B2334413
theorem B1818787 : Blo 956588 1818787 := bstep (se 1 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 1818787 = 2728181) B2728181
theorem B4145357 : Blo 956588 4145357 := bstep (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) B1554509
theorem B4604131 : Blo 956588 4604131 := bstep (se 1 (by rfl) ⟨3453098, by rfl⟩ : syracuseStep 4604131 = 6906197) B6906197
theorem B2048323 : Blo 956588 2048323 := bstep (se 1 (by rfl) ⟨1536242, by rfl⟩ : syracuseStep 2048323 = 3072485) B3072485
theorem B1458577 : Blo 956588 1458577 := bstep (se 2 (by rfl) ⟨546966, by rfl⟩ : syracuseStep 1458577 = 1093933) B1093933
theorem B8176099 : Blo 956588 8176099 := bstep (se 1 (by rfl) ⟨6132074, by rfl⟩ : syracuseStep 8176099 = 12264149) B12264149
theorem B1819235 : Blo 956588 1819235 := bstep (se 1 (by rfl) ⟨1364426, by rfl⟩ : syracuseStep 1819235 = 2728853) B2728853
theorem B3228497 : Blo 956588 3228497 := bstep (se 2 (by rfl) ⟨1210686, by rfl⟩ : syracuseStep 3228497 = 2421373) B2421373
theorem B1819523 : Blo 956588 1819523 := bstep (se 1 (by rfl) ⟨1364642, by rfl⟩ : syracuseStep 1819523 = 2729285) B2729285
theorem B9225485 : Blo 956588 9225485 := bstep (se 3 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 9225485 = 3459557) B3459557
theorem B11060549 : Blo 956588 11060549 := bstep (se 4 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 11060549 = 2073853) B2073853
theorem B6145379 : Blo 956588 6145379 := bstep (se 1 (by rfl) ⟨4609034, by rfl⟩ : syracuseStep 6145379 = 9218069) B9218069
theorem B3229037 : Blo 956588 3229037 := bstep (se 3 (by rfl) ⟨605444, by rfl⟩ : syracuseStep 3229037 = 1210889) B1210889
theorem B3229091 : Blo 956588 3229091 := bstep (se 1 (by rfl) ⟨2421818, by rfl⟩ : syracuseStep 3229091 = 4843637) B4843637
theorem B1295875 : Blo 956588 1295875 := bstep (se 1 (by rfl) ⟨971906, by rfl⟩ : syracuseStep 1295875 = 1943813) B1943813
theorem B7292429 : Blo 956588 7292429 := bstep (se 3 (by rfl) ⟨1367330, by rfl⟩ : syracuseStep 7292429 = 2734661) B2734661
theorem B2049553 : Blo 956588 2049553 := bstep (se 2 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 2049553 = 1537165) B1537165
theorem B3229361 : Blo 956588 3229361 := bstep (se 2 (by rfl) ⟨1211010, by rfl⟩ : syracuseStep 3229361 = 2422021) B2422021
theorem B1296145 : Blo 956588 1296145 := bstep (se 2 (by rfl) ⟨486054, by rfl⟩ : syracuseStep 1296145 = 972109) B972109
theorem B1820465 : Blo 956588 1820465 := bstep (se 2 (by rfl) ⟨682674, by rfl⟩ : syracuseStep 1820465 = 1365349) B1365349
theorem B20760461 : Blo 956588 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B3065987 : Blo 956588 3065987 := bstep (se 1 (by rfl) ⟨2299490, by rfl⟩ : syracuseStep 3065987 = 4598981) B4598981
theorem B2050211 : Blo 956588 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B4376753 : Blo 956588 4376753 := bstep (se 2 (by rfl) ⟨1641282, by rfl⟩ : syracuseStep 4376753 = 3282565) B3282565
theorem B3229901 : Blo 956588 3229901 := bstep (se 3 (by rfl) ⟨605606, by rfl⟩ : syracuseStep 3229901 = 1211213) B1211213
theorem B3229955 : Blo 956588 3229955 := bstep (se 1 (by rfl) ⟨2422466, by rfl⟩ : syracuseStep 3229955 = 4844933) B4844933
theorem B1296643 : Blo 956588 1296643 := bstep (se 1 (by rfl) ⟨972482, by rfl⟩ : syracuseStep 1296643 = 1944965) B1944965
theorem B1165763 : Blo 956588 1165763 := bstep (se 1 (by rfl) ⟨874322, by rfl⟩ : syracuseStep 1165763 = 1748645) B1748645
theorem B1362433 : Blo 956588 1362433 := bstep (se 2 (by rfl) ⟨510912, by rfl⟩ : syracuseStep 1362433 = 1021825) B1021825
theorem B3230225 : Blo 956588 3230225 := bstep (se 2 (by rfl) ⟨1211334, by rfl⟩ : syracuseStep 3230225 = 2422669) B2422669
theorem B1296913 : Blo 956588 1296913 := bstep (se 2 (by rfl) ⟨486342, by rfl⟩ : syracuseStep 1296913 = 972685) B972685
theorem B1362467 : Blo 956588 1362467 := bstep (se 1 (by rfl) ⟨1021850, by rfl⟩ : syracuseStep 1362467 = 2043701) B2043701
theorem B1821361 : Blo 956588 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B1821521 : Blo 956588 1821521 := bstep (se 2 (by rfl) ⟨683070, by rfl⟩ : syracuseStep 1821521 = 1366141) B1366141
theorem B2051057 : Blo 956588 2051057 := bstep (se 2 (by rfl) ⟨769146, by rfl⟩ : syracuseStep 2051057 = 1538293) B1538293
theorem B3230765 : Blo 956588 3230765 := bstep (se 3 (by rfl) ⟨605768, by rfl⟩ : syracuseStep 3230765 = 1211537) B1211537
theorem B1363025 : Blo 956588 1363025 := bstep (se 2 (by rfl) ⟨511134, by rfl⟩ : syracuseStep 1363025 = 1022269) B1022269
theorem B3230819 : Blo 956588 3230819 := bstep (se 1 (by rfl) ⟨2423114, by rfl⟩ : syracuseStep 3230819 = 4846229) B4846229
theorem B23645297 : Blo 956588 23645297 := bstep (se 2 (by rfl) ⟨8866986, by rfl⟩ : syracuseStep 23645297 = 17733973) B17733973
theorem B1363105 : Blo 956588 1363105 := bstep (se 2 (by rfl) ⟨511164, by rfl⟩ : syracuseStep 1363105 = 1022329) B1022329
theorem B1821923 : Blo 956588 1821923 := bstep (se 1 (by rfl) ⟨1366442, by rfl⟩ : syracuseStep 1821923 = 2732885) B2732885
theorem B3067217 : Blo 956588 3067217 := bstep (se 2 (by rfl) ⟨1150206, by rfl⟩ : syracuseStep 3067217 = 2300413) B2300413
theorem B2805101 : Blo 956588 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B3231089 : Blo 956588 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B5459845 : Blo 956588 5459845 := bstep (se 4 (by rfl) ⟨511860, by rfl⟩ : syracuseStep 5459845 = 1023721) B1023721
theorem B3231629 : Blo 956588 3231629 := bstep (se 3 (by rfl) ⟨605930, by rfl⟩ : syracuseStep 3231629 = 1211861) B1211861
theorem B1363891 : Blo 956588 1363891 := bstep (se 1 (by rfl) ⟨1022918, by rfl⟩ : syracuseStep 1363891 = 2045837) B2045837
theorem B3231683 : Blo 956588 3231683 := bstep (se 1 (by rfl) ⟨2423762, by rfl⟩ : syracuseStep 3231683 = 4847525) B4847525
theorem B1724387 : Blo 956588 1724387 := bstep (se 1 (by rfl) ⟨1293290, by rfl⟩ : syracuseStep 1724387 = 2586581) B2586581
theorem B1822819 : Blo 956588 1822819 := bstep (se 1 (by rfl) ⟨1367114, by rfl⟩ : syracuseStep 1822819 = 2734229) B2734229
theorem B3068077 : Blo 956588 3068077 := bstep (se 3 (by rfl) ⟨575264, by rfl⟩ : syracuseStep 3068077 = 1150529) B1150529
theorem B3231953 : Blo 956588 3231953 := bstep (se 2 (by rfl) ⟨1211982, by rfl⟩ : syracuseStep 3231953 = 2423965) B2423965
theorem B1822979 : Blo 956588 1822979 := bstep (se 1 (by rfl) ⟨1367234, by rfl⟩ : syracuseStep 1822979 = 2734469) B2734469
theorem B1364369 : Blo 956588 1364369 := bstep (se 2 (by rfl) ⟨511638, by rfl⟩ : syracuseStep 1364369 = 1023277) B1023277
theorem B1364483 : Blo 956588 1364483 := bstep (se 1 (by rfl) ⟨1023362, by rfl⟩ : syracuseStep 1364483 = 2046725) B2046725
theorem B971347 : Blo 956588 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B1364563 : Blo 956588 1364563 := bstep (se 1 (by rfl) ⟨1023422, by rfl⟩ : syracuseStep 1364563 = 2046845) B2046845
theorem B1495651 : Blo 956588 1495651 := bstep (se 1 (by rfl) ⟨1121738, by rfl⟩ : syracuseStep 1495651 = 2243477) B2243477
theorem B3232493 : Blo 956588 3232493 := bstep (se 3 (by rfl) ⟨606092, by rfl⟩ : syracuseStep 3232493 = 1212185) B1212185
theorem B3232547 : Blo 956588 3232547 := bstep (se 1 (by rfl) ⟨2424410, by rfl⟩ : syracuseStep 3232547 = 4848821) B4848821
theorem B3232817 : Blo 956588 3232817 := bstep (se 2 (by rfl) ⟨1212306, by rfl⟩ : syracuseStep 3232817 = 2424613) B2424613
theorem B1365121 : Blo 956588 1365121 := bstep (se 2 (by rfl) ⟨511920, by rfl⟩ : syracuseStep 1365121 = 1023841) B1023841
theorem B6149297 : Blo 956588 6149297 := bstep (se 2 (by rfl) ⟨2305986, by rfl⟩ : syracuseStep 6149297 = 4611973) B4611973
theorem B3233357 : Blo 956588 3233357 := bstep (se 3 (by rfl) ⟨606254, by rfl⟩ : syracuseStep 3233357 = 1212509) B1212509
theorem B4609649 : Blo 956588 4609649 := bstep (se 2 (by rfl) ⟨1728618, by rfl⟩ : syracuseStep 4609649 = 3457237) B3457237
theorem B3233411 : Blo 956588 3233411 := bstep (se 1 (by rfl) ⟨2425058, by rfl⟩ : syracuseStep 3233411 = 4850117) B4850117
theorem B1038035 : Blo 956588 1038035 := bstep (se 1 (by rfl) ⟨778526, by rfl⟩ : syracuseStep 1038035 = 1557053) B1557053
theorem B3069677 : Blo 956588 3069677 := bstep (se 3 (by rfl) ⟨575564, by rfl⟩ : syracuseStep 3069677 = 1151129) B1151129
theorem B1365827 : Blo 956588 1365827 := bstep (se 1 (by rfl) ⟨1024370, by rfl⟩ : syracuseStep 1365827 = 2048741) B2048741
theorem B5461829 : Blo 956588 5461829 := bstep (se 4 (by rfl) ⟨512046, by rfl⟩ : syracuseStep 5461829 = 1024093) B1024093
theorem B6149965 : Blo 956588 6149965 := bstep (se 3 (by rfl) ⟨1153118, by rfl⟩ : syracuseStep 6149965 = 2306237) B2306237
theorem B3233681 : Blo 956588 3233681 := bstep (se 2 (by rfl) ⟨1212630, by rfl⟩ : syracuseStep 3233681 = 2425261) B2425261
theorem B10344419 : Blo 956588 10344419 := bstep (se 1 (by rfl) ⟨7758314, by rfl⟩ : syracuseStep 10344419 = 15516629) B15516629
theorem B7264241 : Blo 956588 7264241 := bstep (se 2 (by rfl) ⟨2724090, by rfl⟩ : syracuseStep 7264241 = 5448181) B5448181
theorem B2152529 : Blo 956588 2152529 := bstep (se 2 (by rfl) ⟨807198, by rfl⟩ : syracuseStep 2152529 = 1614397) B1614397
theorem B2152547 : Blo 956588 2152547 := bstep (se 1 (by rfl) ⟨1614410, by rfl⟩ : syracuseStep 2152547 = 3228821) B3228821
theorem B6903949 : Blo 956588 6903949 := bstep (se 3 (by rfl) ⟨1294490, by rfl⟩ : syracuseStep 6903949 = 2588981) B2588981
theorem B2152817 : Blo 956588 2152817 := bstep (se 2 (by rfl) ⟨807306, by rfl⟩ : syracuseStep 2152817 = 1614613) B1614613
theorem B2152835 : Blo 956588 2152835 := bstep (se 1 (by rfl) ⟨1614626, by rfl⟩ : syracuseStep 2152835 = 3229253) B3229253
theorem B3234221 : Blo 956588 3234221 := bstep (se 3 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 3234221 = 1212833) B1212833
theorem B1366465 : Blo 956588 1366465 := bstep (se 2 (by rfl) ⟨512424, by rfl⟩ : syracuseStep 1366465 = 1024849) B1024849
theorem B3234275 : Blo 956588 3234275 := bstep (se 1 (by rfl) ⟨2425706, by rfl⟩ : syracuseStep 3234275 = 4851413) B4851413
theorem B1727011 : Blo 956588 1727011 := bstep (se 1 (by rfl) ⟨1295258, by rfl⟩ : syracuseStep 1727011 = 2590517) B2590517
theorem B1366579 : Blo 956588 1366579 := bstep (se 1 (by rfl) ⟨1024934, by rfl⟩ : syracuseStep 1366579 = 2049869) B2049869
theorem B2153105 : Blo 956588 2153105 := bstep (se 2 (by rfl) ⟨807414, by rfl⟩ : syracuseStep 2153105 = 1614829) B1614829
theorem B2153123 : Blo 956588 2153123 := bstep (se 1 (by rfl) ⟨1614842, by rfl⟩ : syracuseStep 2153123 = 3229685) B3229685
theorem B3234545 : Blo 956588 3234545 := bstep (se 2 (by rfl) ⟨1212954, by rfl⟩ : syracuseStep 3234545 = 2425909) B2425909
theorem B2153393 : Blo 956588 2153393 := bstep (se 2 (by rfl) ⟨807522, by rfl⟩ : syracuseStep 2153393 = 1615045) B1615045
theorem B2153411 : Blo 956588 2153411 := bstep (se 1 (by rfl) ⟨1615058, by rfl⟩ : syracuseStep 2153411 = 3230117) B3230117
theorem B2153681 : Blo 956588 2153681 := bstep (se 2 (by rfl) ⟨807630, by rfl⟩ : syracuseStep 2153681 = 1615261) B1615261
theorem B2153699 : Blo 956588 2153699 := bstep (se 1 (by rfl) ⟨1615274, by rfl⟩ : syracuseStep 2153699 = 3230549) B3230549
theorem B3235085 : Blo 956588 3235085 := bstep (se 3 (by rfl) ⟨606578, by rfl⟩ : syracuseStep 3235085 = 1213157) B1213157
theorem B3071267 : Blo 956588 3071267 := bstep (se 1 (by rfl) ⟨2303450, by rfl⟩ : syracuseStep 3071267 = 4606901) B4606901
theorem B3235139 : Blo 956588 3235139 := bstep (se 1 (by rfl) ⟨2426354, by rfl⟩ : syracuseStep 3235139 = 4852709) B4852709
theorem B2219345 : Blo 956588 2219345 := bstep (se 2 (by rfl) ⟨832254, by rfl⟩ : syracuseStep 2219345 = 1664509) B1664509
theorem B3071459 : Blo 956588 3071459 := bstep (se 1 (by rfl) ⟨2303594, by rfl⟩ : syracuseStep 3071459 = 4607189) B4607189
theorem B5823971 : Blo 956588 5823971 := bstep (se 1 (by rfl) ⟨4367978, by rfl⟩ : syracuseStep 5823971 = 8735957) B8735957
theorem B2153969 : Blo 956588 2153969 := bstep (se 2 (by rfl) ⟨807738, by rfl⟩ : syracuseStep 2153969 = 1615477) B1615477
theorem B2153987 : Blo 956588 2153987 := bstep (se 1 (by rfl) ⟨1615490, by rfl⟩ : syracuseStep 2153987 = 3230981) B3230981
theorem B1728049 : Blo 956588 1728049 := bstep (se 2 (by rfl) ⟨648018, by rfl⟩ : syracuseStep 1728049 = 1296037) B1296037
theorem B3235409 : Blo 956588 3235409 := bstep (se 2 (by rfl) ⟨1213278, by rfl⟩ : syracuseStep 3235409 = 2426557) B2426557
theorem B2154257 : Blo 956588 2154257 := bstep (se 2 (by rfl) ⟨807846, by rfl⟩ : syracuseStep 2154257 = 1615693) B1615693
theorem B2154275 : Blo 956588 2154275 := bstep (se 1 (by rfl) ⟨1615706, by rfl⟩ : syracuseStep 2154275 = 3231413) B3231413
theorem B7757795 : Blo 956588 7757795 := bstep (se 1 (by rfl) ⟨5818346, by rfl⟩ : syracuseStep 7757795 = 11636693) B11636693
theorem B2154545 : Blo 956588 2154545 := bstep (se 2 (by rfl) ⟨807954, by rfl⟩ : syracuseStep 2154545 = 1615909) B1615909
theorem B2154563 : Blo 956588 2154563 := bstep (se 1 (by rfl) ⟨1615922, by rfl⟩ : syracuseStep 2154563 = 3231845) B3231845
theorem B3235949 : Blo 956588 3235949 := bstep (se 3 (by rfl) ⟨606740, by rfl⟩ : syracuseStep 3235949 = 1213481) B1213481
theorem B3072113 : Blo 956588 3072113 := bstep (se 2 (by rfl) ⟨1152042, by rfl⟩ : syracuseStep 3072113 = 2304085) B2304085
theorem B3891341 : Blo 956588 3891341 := bstep (se 3 (by rfl) ⟨729626, by rfl⟩ : syracuseStep 3891341 = 1459253) B1459253
theorem B3236003 : Blo 956588 3236003 := bstep (se 1 (by rfl) ⟨2427002, by rfl⟩ : syracuseStep 3236003 = 4854005) B4854005
theorem B2187427 : Blo 956588 2187427 := bstep (se 1 (by rfl) ⟨1640570, by rfl⟩ : syracuseStep 2187427 = 3281141) B3281141
theorem B2154833 : Blo 956588 2154833 := bstep (se 2 (by rfl) ⟨808062, by rfl⟩ : syracuseStep 2154833 = 1616125) B1616125
theorem B2154851 : Blo 956588 2154851 := bstep (se 1 (by rfl) ⟨1616138, by rfl⟩ : syracuseStep 2154851 = 3232277) B3232277
theorem B2187665 : Blo 956588 2187665 := bstep (se 2 (by rfl) ⟨820374, by rfl⟩ : syracuseStep 2187665 = 1640749) B1640749
theorem B3236273 : Blo 956588 3236273 := bstep (se 2 (by rfl) ⟨1213602, by rfl⟩ : syracuseStep 3236273 = 2427205) B2427205
theorem B1532353 : Blo 956588 1532353 := bstep (se 2 (by rfl) ⟨574632, by rfl⟩ : syracuseStep 1532353 = 1149265) B1149265
theorem B1532449 : Blo 956588 1532449 := bstep (se 2 (by rfl) ⟨574668, by rfl⟩ : syracuseStep 1532449 = 1149337) B1149337
theorem B2155121 : Blo 956588 2155121 := bstep (se 2 (by rfl) ⟨808170, by rfl⟩ : syracuseStep 2155121 = 1616341) B1616341
theorem B2155139 : Blo 956588 2155139 := bstep (se 1 (by rfl) ⟨1616354, by rfl⟩ : syracuseStep 2155139 = 3232709) B3232709
theorem B1532609 : Blo 956588 1532609 := bstep (se 2 (by rfl) ⟨574728, by rfl⟩ : syracuseStep 1532609 = 1149457) B1149457
theorem B44360405 : Blo 956588 44360405 := bstep (se 7 (by rfl) ⟨519848, by rfl⟩ : syracuseStep 44360405 = 1039697) B1039697
theorem B5825357 : Blo 956588 5825357 := bstep (se 3 (by rfl) ⟨1092254, by rfl⟩ : syracuseStep 5825357 = 2184509) B2184509
theorem B2155409 : Blo 956588 2155409 := bstep (se 2 (by rfl) ⟨808278, by rfl⟩ : syracuseStep 2155409 = 1616557) B1616557
theorem B2155427 : Blo 956588 2155427 := bstep (se 1 (by rfl) ⟨1616570, by rfl⟩ : syracuseStep 2155427 = 3233141) B3233141
theorem B3236813 : Blo 956588 3236813 := bstep (se 3 (by rfl) ⟨606902, by rfl⟩ : syracuseStep 3236813 = 1213805) B1213805
theorem B1369043 : Blo 956588 1369043 := bstep (se 1 (by rfl) ⟨1026782, by rfl⟩ : syracuseStep 1369043 = 2053565) B2053565
theorem B3236867 : Blo 956588 3236867 := bstep (se 1 (by rfl) ⟨2427650, by rfl⟩ : syracuseStep 3236867 = 4855301) B4855301
theorem B2155697 : Blo 956588 2155697 := bstep (se 2 (by rfl) ⟨808386, by rfl⟩ : syracuseStep 2155697 = 1616773) B1616773
theorem B2155715 : Blo 956588 2155715 := bstep (se 1 (by rfl) ⟨1616786, by rfl⟩ : syracuseStep 2155715 = 3233573) B3233573
theorem B5825741 : Blo 956588 5825741 := bstep (se 3 (by rfl) ⟨1092326, by rfl⟩ : syracuseStep 5825741 = 2184653) B2184653
theorem B3237137 : Blo 956588 3237137 := bstep (se 2 (by rfl) ⟨1213926, by rfl⟩ : syracuseStep 3237137 = 2427853) B2427853
theorem B1434899 : Blo 956588 1434899 := bstep (se 1 (by rfl) ⟨1076174, by rfl⟩ : syracuseStep 1434899 = 2152349) B2152349
theorem B1434929 : Blo 956588 1434929 := bstep (se 2 (by rfl) ⟨538098, by rfl⟩ : syracuseStep 1434929 = 1076197) B1076197
theorem B1434947 : Blo 956588 1434947 := bstep (se 1 (by rfl) ⟨1076210, by rfl⟩ : syracuseStep 1434947 = 2152421) B2152421
theorem B1434977 : Blo 956588 1434977 := bstep (se 2 (by rfl) ⟨538116, by rfl⟩ : syracuseStep 1434977 = 1076233) B1076233
theorem B1434995 : Blo 956588 1434995 := bstep (se 1 (by rfl) ⟨1076246, by rfl⟩ : syracuseStep 1434995 = 2152493) B2152493
theorem B1435025 : Blo 956588 1435025 := bstep (se 2 (by rfl) ⟨538134, by rfl⟩ : syracuseStep 1435025 = 1076269) B1076269
theorem B1435043 : Blo 956588 1435043 := bstep (se 1 (by rfl) ⟨1076282, by rfl⟩ : syracuseStep 1435043 = 2152565) B2152565
theorem B1435073 : Blo 956588 1435073 := bstep (se 2 (by rfl) ⟨538152, by rfl⟩ : syracuseStep 1435073 = 1076305) B1076305
theorem B2155985 : Blo 956588 2155985 := bstep (se 2 (by rfl) ⟨808494, by rfl⟩ : syracuseStep 2155985 = 1616989) B1616989
theorem B1435091 : Blo 956588 1435091 := bstep (se 1 (by rfl) ⟨1076318, by rfl⟩ : syracuseStep 1435091 = 2152637) B2152637
theorem B2156003 : Blo 956588 2156003 := bstep (se 1 (by rfl) ⟨1617002, by rfl⟩ : syracuseStep 2156003 = 3234005) B3234005
theorem B1435121 : Blo 956588 1435121 := bstep (se 2 (by rfl) ⟨538170, by rfl⟩ : syracuseStep 1435121 = 1076341) B1076341
theorem B1435139 : Blo 956588 1435139 := bstep (se 1 (by rfl) ⟨1076354, by rfl⟩ : syracuseStep 1435139 = 2152709) B2152709
theorem B1435169 : Blo 956588 1435169 := bstep (se 2 (by rfl) ⟨538188, by rfl⟩ : syracuseStep 1435169 = 1076377) B1076377
theorem B1435187 : Blo 956588 1435187 := bstep (se 1 (by rfl) ⟨1076390, by rfl⟩ : syracuseStep 1435187 = 2152781) B2152781
theorem B5465677 : Blo 956588 5465677 := bstep (se 3 (by rfl) ⟨1024814, by rfl⟩ : syracuseStep 5465677 = 2049629) B2049629
theorem B1435217 : Blo 956588 1435217 := bstep (se 2 (by rfl) ⟨538206, by rfl⟩ : syracuseStep 1435217 = 1076413) B1076413
theorem B1435235 : Blo 956588 1435235 := bstep (se 1 (by rfl) ⟨1076426, by rfl⟩ : syracuseStep 1435235 = 2152853) B2152853
theorem B1435265 : Blo 956588 1435265 := bstep (se 2 (by rfl) ⟨538224, by rfl⟩ : syracuseStep 1435265 = 1076449) B1076449
theorem B1435283 : Blo 956588 1435283 := bstep (se 1 (by rfl) ⟨1076462, by rfl⟩ : syracuseStep 1435283 = 2152925) B2152925
theorem B1435313 : Blo 956588 1435313 := bstep (se 2 (by rfl) ⟨538242, by rfl⟩ : syracuseStep 1435313 = 1076485) B1076485
theorem B1435331 : Blo 956588 1435331 := bstep (se 1 (by rfl) ⟨1076498, by rfl⟩ : syracuseStep 1435331 = 2152997) B2152997
theorem B1435361 : Blo 956588 1435361 := bstep (se 2 (by rfl) ⟨538260, by rfl⟩ : syracuseStep 1435361 = 1076521) B1076521
theorem B2156273 : Blo 956588 2156273 := bstep (se 2 (by rfl) ⟨808602, by rfl⟩ : syracuseStep 2156273 = 1617205) B1617205
theorem B1435379 : Blo 956588 1435379 := bstep (se 1 (by rfl) ⟨1076534, by rfl⟩ : syracuseStep 1435379 = 2153069) B2153069
theorem B2156291 : Blo 956588 2156291 := bstep (se 1 (by rfl) ⟨1617218, by rfl⟩ : syracuseStep 2156291 = 3234437) B3234437
theorem B1435409 : Blo 956588 1435409 := bstep (se 2 (by rfl) ⟨538278, by rfl⟩ : syracuseStep 1435409 = 1076557) B1076557
theorem B1435427 : Blo 956588 1435427 := bstep (se 1 (by rfl) ⟨1076570, by rfl⟩ : syracuseStep 1435427 = 2153141) B2153141
theorem B3237677 : Blo 956588 3237677 := bstep (se 3 (by rfl) ⟨607064, by rfl⟩ : syracuseStep 3237677 = 1214129) B1214129
theorem B4843313 : Blo 956588 4843313 := bstep (se 2 (by rfl) ⟨1816242, by rfl⟩ : syracuseStep 4843313 = 3632485) B3632485
theorem B1435457 : Blo 956588 1435457 := bstep (se 2 (by rfl) ⟨538296, by rfl⟩ : syracuseStep 1435457 = 1076593) B1076593
theorem B1435475 : Blo 956588 1435475 := bstep (se 1 (by rfl) ⟨1076606, by rfl⟩ : syracuseStep 1435475 = 2153213) B2153213
theorem B3237731 : Blo 956588 3237731 := bstep (se 1 (by rfl) ⟨2428298, by rfl⟩ : syracuseStep 3237731 = 4856597) B4856597
theorem B1435505 : Blo 956588 1435505 := bstep (se 2 (by rfl) ⟨538314, by rfl⟩ : syracuseStep 1435505 = 1076629) B1076629
theorem B1435523 : Blo 956588 1435523 := bstep (se 1 (by rfl) ⟨1076642, by rfl⟩ : syracuseStep 1435523 = 2153285) B2153285
theorem B1435553 : Blo 956588 1435553 := bstep (se 2 (by rfl) ⟨538332, by rfl⟩ : syracuseStep 1435553 = 1076665) B1076665
theorem B1435571 : Blo 956588 1435571 := bstep (se 1 (by rfl) ⟨1076678, by rfl⟩ : syracuseStep 1435571 = 2153357) B2153357
theorem B1435601 : Blo 956588 1435601 := bstep (se 2 (by rfl) ⟨538350, by rfl⟩ : syracuseStep 1435601 = 1076701) B1076701
theorem B1435619 : Blo 956588 1435619 := bstep (se 1 (by rfl) ⟨1076714, by rfl⟩ : syracuseStep 1435619 = 2153429) B2153429
theorem B4089827 : Blo 956588 4089827 := bstep (se 1 (by rfl) ⟨3067370, by rfl⟩ : syracuseStep 4089827 = 6134741) B6134741
theorem B1435649 : Blo 956588 1435649 := bstep (se 2 (by rfl) ⟨538368, by rfl⟩ : syracuseStep 1435649 = 1076737) B1076737
theorem B2156561 : Blo 956588 2156561 := bstep (se 2 (by rfl) ⟨808710, by rfl⟩ : syracuseStep 2156561 = 1617421) B1617421
theorem B1435667 : Blo 956588 1435667 := bstep (se 1 (by rfl) ⟨1076750, by rfl⟩ : syracuseStep 1435667 = 2153501) B2153501
theorem B2156579 : Blo 956588 2156579 := bstep (se 1 (by rfl) ⟨1617434, by rfl⟩ : syracuseStep 2156579 = 3234869) B3234869
theorem B1435697 : Blo 956588 1435697 := bstep (se 2 (by rfl) ⟨538386, by rfl⟩ : syracuseStep 1435697 = 1076773) B1076773
theorem B1435715 : Blo 956588 1435715 := bstep (se 1 (by rfl) ⟨1076786, by rfl⟩ : syracuseStep 1435715 = 2153573) B2153573
theorem B3074125 : Blo 956588 3074125 := bstep (se 3 (by rfl) ⟨576398, by rfl⟩ : syracuseStep 3074125 = 1152797) B1152797
theorem B1435745 : Blo 956588 1435745 := bstep (se 2 (by rfl) ⟨538404, by rfl⟩ : syracuseStep 1435745 = 1076809) B1076809
theorem B3238001 : Blo 956588 3238001 := bstep (se 2 (by rfl) ⟨1214250, by rfl⟩ : syracuseStep 3238001 = 2428501) B2428501
theorem B1435763 : Blo 956588 1435763 := bstep (se 1 (by rfl) ⟨1076822, by rfl⟩ : syracuseStep 1435763 = 2153645) B2153645
theorem B15558797 : Blo 956588 15558797 := bstep (se 3 (by rfl) ⟨2917274, by rfl⟩ : syracuseStep 15558797 = 5834549) B5834549
theorem B1435793 : Blo 956588 1435793 := bstep (se 2 (by rfl) ⟨538422, by rfl⟩ : syracuseStep 1435793 = 1076845) B1076845
theorem B1435811 : Blo 956588 1435811 := bstep (se 1 (by rfl) ⟨1076858, by rfl⟩ : syracuseStep 1435811 = 2153717) B2153717
theorem B1435841 : Blo 956588 1435841 := bstep (se 2 (by rfl) ⟨538440, by rfl⟩ : syracuseStep 1435841 = 1076881) B1076881
theorem B1435859 : Blo 956588 1435859 := bstep (se 1 (by rfl) ⟨1076894, by rfl⟩ : syracuseStep 1435859 = 2153789) B2153789
theorem B1435889 : Blo 956588 1435889 := bstep (se 2 (by rfl) ⟨538458, by rfl⟩ : syracuseStep 1435889 = 1076917) B1076917
theorem B1435907 : Blo 956588 1435907 := bstep (se 1 (by rfl) ⟨1076930, by rfl⟩ : syracuseStep 1435907 = 2153861) B2153861
theorem B1435937 : Blo 956588 1435937 := bstep (se 2 (by rfl) ⟨538476, by rfl⟩ : syracuseStep 1435937 = 1076953) B1076953
theorem B2156849 : Blo 956588 2156849 := bstep (se 2 (by rfl) ⟨808818, by rfl⟩ : syracuseStep 2156849 = 1617637) B1617637
theorem B1435955 : Blo 956588 1435955 := bstep (se 1 (by rfl) ⟨1076966, by rfl⟩ : syracuseStep 1435955 = 2153933) B2153933
theorem B2156867 : Blo 956588 2156867 := bstep (se 1 (by rfl) ⟨1617650, by rfl⟩ : syracuseStep 2156867 = 3235301) B3235301
theorem B1435985 : Blo 956588 1435985 := bstep (se 2 (by rfl) ⟨538494, by rfl⟩ : syracuseStep 1435985 = 1076989) B1076989
theorem B1436003 : Blo 956588 1436003 := bstep (se 1 (by rfl) ⟨1077002, by rfl⟩ : syracuseStep 1436003 = 2154005) B2154005
theorem B6908273 : Blo 956588 6908273 := bstep (se 2 (by rfl) ⟨2590602, by rfl⟩ : syracuseStep 6908273 = 5181205) B5181205
theorem B1436033 : Blo 956588 1436033 := bstep (se 2 (by rfl) ⟨538512, by rfl⟩ : syracuseStep 1436033 = 1077025) B1077025
theorem B1403281 : Blo 956588 1403281 := bstep (se 2 (by rfl) ⟨526230, by rfl⟩ : syracuseStep 1403281 = 1052461) B1052461
theorem B1436051 : Blo 956588 1436051 := bstep (se 1 (by rfl) ⟨1077038, by rfl⟩ : syracuseStep 1436051 = 2154077) B2154077
theorem B1436081 : Blo 956588 1436081 := bstep (se 2 (by rfl) ⟨538530, by rfl⟩ : syracuseStep 1436081 = 1077061) B1077061
theorem B1436099 : Blo 956588 1436099 := bstep (se 1 (by rfl) ⟨1077074, by rfl⟩ : syracuseStep 1436099 = 2154149) B2154149
theorem B1534403 : Blo 956588 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B1436129 : Blo 956588 1436129 := bstep (se 2 (by rfl) ⟨538548, by rfl⟩ : syracuseStep 1436129 = 1077097) B1077097
theorem B1436147 : Blo 956588 1436147 := bstep (se 1 (by rfl) ⟨1077110, by rfl⟩ : syracuseStep 1436147 = 2154221) B2154221
theorem B5827085 : Blo 956588 5827085 := bstep (se 3 (by rfl) ⟨1092578, by rfl⟩ : syracuseStep 5827085 = 2185157) B2185157
theorem B3074573 : Blo 956588 3074573 := bstep (se 3 (by rfl) ⟨576482, by rfl⟩ : syracuseStep 3074573 = 1152965) B1152965
theorem B1436177 : Blo 956588 1436177 := bstep (se 2 (by rfl) ⟨538566, by rfl⟩ : syracuseStep 1436177 = 1077133) B1077133
theorem B1436195 : Blo 956588 1436195 := bstep (se 1 (by rfl) ⟨1077146, by rfl⟩ : syracuseStep 1436195 = 2154293) B2154293
theorem B1436225 : Blo 956588 1436225 := bstep (se 2 (by rfl) ⟨538584, by rfl⟩ : syracuseStep 1436225 = 1077169) B1077169
theorem B2157137 : Blo 956588 2157137 := bstep (se 2 (by rfl) ⟨808926, by rfl⟩ : syracuseStep 2157137 = 1617853) B1617853
theorem B1436243 : Blo 956588 1436243 := bstep (se 1 (by rfl) ⟨1077182, by rfl⟩ : syracuseStep 1436243 = 2154365) B2154365
theorem B2157155 : Blo 956588 2157155 := bstep (se 1 (by rfl) ⟨1617866, by rfl⟩ : syracuseStep 2157155 = 3235733) B3235733
theorem B2910829 : Blo 956588 2910829 := bstep (se 3 (by rfl) ⟨545780, by rfl⟩ : syracuseStep 2910829 = 1091561) B1091561
theorem B1436273 : Blo 956588 1436273 := bstep (se 2 (by rfl) ⟨538602, by rfl⟩ : syracuseStep 1436273 = 1077205) B1077205
theorem B1436291 : Blo 956588 1436291 := bstep (se 1 (by rfl) ⟨1077218, by rfl⟩ : syracuseStep 1436291 = 2154437) B2154437
theorem B5171845 : Blo 956588 5171845 := bstep (se 4 (by rfl) ⟨484860, by rfl⟩ : syracuseStep 5171845 = 969721) B969721
theorem B3238541 : Blo 956588 3238541 := bstep (se 3 (by rfl) ⟨607226, by rfl⟩ : syracuseStep 3238541 = 1214453) B1214453
theorem B1436321 : Blo 956588 1436321 := bstep (se 2 (by rfl) ⟨538620, by rfl⟩ : syracuseStep 1436321 = 1077241) B1077241
theorem B1436339 : Blo 956588 1436339 := bstep (se 1 (by rfl) ⟨1077254, by rfl⟩ : syracuseStep 1436339 = 2154509) B2154509
theorem B3238595 : Blo 956588 3238595 := bstep (se 1 (by rfl) ⟨2428946, by rfl⟩ : syracuseStep 3238595 = 4857893) B4857893
theorem B2190019 : Blo 956588 2190019 := bstep (se 1 (by rfl) ⟨1642514, by rfl⟩ : syracuseStep 2190019 = 3285029) B3285029
theorem B1436369 : Blo 956588 1436369 := bstep (se 2 (by rfl) ⟨538638, by rfl⟩ : syracuseStep 1436369 = 1077277) B1077277
theorem B1436387 : Blo 956588 1436387 := bstep (se 1 (by rfl) ⟨1077290, by rfl⟩ : syracuseStep 1436387 = 2154581) B2154581
theorem B7990001 : Blo 956588 7990001 := bstep (se 2 (by rfl) ⟨2996250, by rfl⟩ : syracuseStep 7990001 = 5992501) B5992501
theorem B1436417 : Blo 956588 1436417 := bstep (se 2 (by rfl) ⟨538656, by rfl⟩ : syracuseStep 1436417 = 1077313) B1077313
theorem B1436435 : Blo 956588 1436435 := bstep (se 1 (by rfl) ⟨1077326, by rfl⟩ : syracuseStep 1436435 = 2154653) B2154653
theorem B1436465 : Blo 956588 1436465 := bstep (se 2 (by rfl) ⟨538674, by rfl⟩ : syracuseStep 1436465 = 1077349) B1077349
theorem B1436483 : Blo 956588 1436483 := bstep (se 1 (by rfl) ⟨1077362, by rfl⟩ : syracuseStep 1436483 = 2154725) B2154725
theorem B1436513 : Blo 956588 1436513 := bstep (se 2 (by rfl) ⟨538692, by rfl⟩ : syracuseStep 1436513 = 1077385) B1077385
theorem B2157425 : Blo 956588 2157425 := bstep (se 2 (by rfl) ⟨809034, by rfl⟩ : syracuseStep 2157425 = 1618069) B1618069
theorem B1436531 : Blo 956588 1436531 := bstep (se 1 (by rfl) ⟨1077398, by rfl⟩ : syracuseStep 1436531 = 2154797) B2154797
theorem B2157443 : Blo 956588 2157443 := bstep (se 1 (by rfl) ⟨1618082, by rfl⟩ : syracuseStep 2157443 = 3236165) B3236165
theorem B1436561 : Blo 956588 1436561 := bstep (se 2 (by rfl) ⟨538710, by rfl⟩ : syracuseStep 1436561 = 1077421) B1077421
theorem B1436579 : Blo 956588 1436579 := bstep (se 1 (by rfl) ⟨1077434, by rfl⟩ : syracuseStep 1436579 = 2154869) B2154869
theorem B1436609 : Blo 956588 1436609 := bstep (se 2 (by rfl) ⟨538728, by rfl⟩ : syracuseStep 1436609 = 1077457) B1077457
theorem B3238865 : Blo 956588 3238865 := bstep (se 2 (by rfl) ⟨1214574, by rfl⟩ : syracuseStep 3238865 = 2429149) B2429149
theorem B1076179 : Blo 956588 1076179 := bstep (se 1 (by rfl) ⟨807134, by rfl⟩ : syracuseStep 1076179 = 1614269) B1614269
theorem B1436627 : Blo 956588 1436627 := bstep (se 1 (by rfl) ⟨1077470, by rfl⟩ : syracuseStep 1436627 = 2154941) B2154941
theorem B1436657 : Blo 956588 1436657 := bstep (se 2 (by rfl) ⟨538746, by rfl⟩ : syracuseStep 1436657 = 1077493) B1077493
theorem B1436675 : Blo 956588 1436675 := bstep (se 1 (by rfl) ⟨1077506, by rfl⟩ : syracuseStep 1436675 = 2155013) B2155013
theorem B1436705 : Blo 956588 1436705 := bstep (se 2 (by rfl) ⟨538764, by rfl⟩ : syracuseStep 1436705 = 1077529) B1077529
theorem B1436723 : Blo 956588 1436723 := bstep (se 1 (by rfl) ⟨1077542, by rfl⟩ : syracuseStep 1436723 = 2155085) B2155085
theorem B1436753 : Blo 956588 1436753 := bstep (se 2 (by rfl) ⟨538782, by rfl⟩ : syracuseStep 1436753 = 1077565) B1077565
theorem B1076323 : Blo 956588 1076323 := bstep (se 1 (by rfl) ⟨807242, by rfl⟩ : syracuseStep 1076323 = 1614485) B1614485
theorem B1436771 : Blo 956588 1436771 := bstep (se 1 (by rfl) ⟨1077578, by rfl⟩ : syracuseStep 1436771 = 2155157) B2155157
theorem B1436801 : Blo 956588 1436801 := bstep (se 2 (by rfl) ⟨538800, by rfl⟩ : syracuseStep 1436801 = 1077601) B1077601
theorem B2157713 : Blo 956588 2157713 := bstep (se 2 (by rfl) ⟨809142, by rfl⟩ : syracuseStep 2157713 = 1618285) B1618285
theorem B1436819 : Blo 956588 1436819 := bstep (se 1 (by rfl) ⟨1077614, by rfl⟩ : syracuseStep 1436819 = 2155229) B2155229
theorem B2157731 : Blo 956588 2157731 := bstep (se 1 (by rfl) ⟨1618298, by rfl⟩ : syracuseStep 2157731 = 3236597) B3236597
theorem B4091057 : Blo 956588 4091057 := bstep (se 2 (by rfl) ⟨1534146, by rfl⟩ : syracuseStep 4091057 = 3068293) B3068293
theorem B1436849 : Blo 956588 1436849 := bstep (se 2 (by rfl) ⟨538818, by rfl⟩ : syracuseStep 1436849 = 1077637) B1077637
theorem B1436867 : Blo 956588 1436867 := bstep (se 1 (by rfl) ⟨1077650, by rfl⟩ : syracuseStep 1436867 = 2155301) B2155301
theorem B1436897 : Blo 956588 1436897 := bstep (se 2 (by rfl) ⟨538836, by rfl⟩ : syracuseStep 1436897 = 1077673) B1077673
theorem B4844771 : Blo 956588 4844771 := bstep (se 1 (by rfl) ⟨3633578, by rfl⟩ : syracuseStep 4844771 = 7267157) B7267157
theorem B1076467 : Blo 956588 1076467 := bstep (se 1 (by rfl) ⟨807350, by rfl⟩ : syracuseStep 1076467 = 1614701) B1614701
theorem B1436915 : Blo 956588 1436915 := bstep (se 1 (by rfl) ⟨1077686, by rfl⟩ : syracuseStep 1436915 = 2155373) B2155373
theorem B1436945 : Blo 956588 1436945 := bstep (se 2 (by rfl) ⟨538854, by rfl⟩ : syracuseStep 1436945 = 1077709) B1077709
theorem B1535249 : Blo 956588 1535249 := bstep (se 2 (by rfl) ⟨575718, by rfl⟩ : syracuseStep 1535249 = 1151437) B1151437
theorem B1436963 : Blo 956588 1436963 := bstep (se 1 (by rfl) ⟨1077722, by rfl⟩ : syracuseStep 1436963 = 2155445) B2155445
theorem B1436993 : Blo 956588 1436993 := bstep (se 2 (by rfl) ⟨538872, by rfl⟩ : syracuseStep 1436993 = 1077745) B1077745
theorem B1437011 : Blo 956588 1437011 := bstep (se 1 (by rfl) ⟨1077758, by rfl⟩ : syracuseStep 1437011 = 2155517) B2155517
theorem B1437041 : Blo 956588 1437041 := bstep (se 2 (by rfl) ⟨538890, by rfl⟩ : syracuseStep 1437041 = 1077781) B1077781
theorem B1076611 : Blo 956588 1076611 := bstep (se 1 (by rfl) ⟨807458, by rfl⟩ : syracuseStep 1076611 = 1614917) B1614917
theorem B1437059 : Blo 956588 1437059 := bstep (se 1 (by rfl) ⟨1077794, by rfl⟩ : syracuseStep 1437059 = 2155589) B2155589
theorem B1535377 : Blo 956588 1535377 := bstep (se 2 (by rfl) ⟨575766, by rfl⟩ : syracuseStep 1535377 = 1151533) B1151533
theorem B1437089 : Blo 956588 1437089 := bstep (se 2 (by rfl) ⟨538908, by rfl⟩ : syracuseStep 1437089 = 1077817) B1077817
theorem B2158001 : Blo 956588 2158001 := bstep (se 2 (by rfl) ⟨809250, by rfl⟩ : syracuseStep 2158001 = 1618501) B1618501
theorem B1437107 : Blo 956588 1437107 := bstep (se 1 (by rfl) ⟨1077830, by rfl⟩ : syracuseStep 1437107 = 2155661) B2155661
theorem B2158019 : Blo 956588 2158019 := bstep (se 1 (by rfl) ⟨1618514, by rfl⟩ : syracuseStep 2158019 = 3237029) B3237029
theorem B1437137 : Blo 956588 1437137 := bstep (se 2 (by rfl) ⟨538926, by rfl⟩ : syracuseStep 1437137 = 1077853) B1077853
theorem B1535441 : Blo 956588 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B1437155 : Blo 956588 1437155 := bstep (se 1 (by rfl) ⟨1077866, by rfl⟩ : syracuseStep 1437155 = 2155733) B2155733
theorem B3239405 : Blo 956588 3239405 := bstep (se 3 (by rfl) ⟨607388, by rfl⟩ : syracuseStep 3239405 = 1214777) B1214777
theorem B1437185 : Blo 956588 1437185 := bstep (se 2 (by rfl) ⟨538944, by rfl⟩ : syracuseStep 1437185 = 1077889) B1077889
theorem B5467661 : Blo 956588 5467661 := bstep (se 3 (by rfl) ⟨1025186, by rfl⟩ : syracuseStep 5467661 = 2050373) B2050373
theorem B1076755 : Blo 956588 1076755 := bstep (se 1 (by rfl) ⟨807566, by rfl⟩ : syracuseStep 1076755 = 1615133) B1615133
theorem B1437203 : Blo 956588 1437203 := bstep (se 1 (by rfl) ⟨1077902, by rfl⟩ : syracuseStep 1437203 = 2155805) B2155805
theorem B3239459 : Blo 956588 3239459 := bstep (se 1 (by rfl) ⟨2429594, by rfl⟩ : syracuseStep 3239459 = 4859189) B4859189
theorem B1437233 : Blo 956588 1437233 := bstep (se 2 (by rfl) ⟨538962, by rfl⟩ : syracuseStep 1437233 = 1077925) B1077925
theorem B1437251 : Blo 956588 1437251 := bstep (se 1 (by rfl) ⟨1077938, by rfl⟩ : syracuseStep 1437251 = 2155877) B2155877
theorem B1437281 : Blo 956588 1437281 := bstep (se 2 (by rfl) ⟨538980, by rfl⟩ : syracuseStep 1437281 = 1077961) B1077961
theorem B4157027 : Blo 956588 4157027 := bstep (se 1 (by rfl) ⟨3117770, by rfl⟩ : syracuseStep 4157027 = 6235541) B6235541
theorem B1437299 : Blo 956588 1437299 := bstep (se 1 (by rfl) ⟨1077974, by rfl⟩ : syracuseStep 1437299 = 2155949) B2155949
theorem B9203341 : Blo 956588 9203341 := bstep (se 3 (by rfl) ⟨1725626, by rfl⟩ : syracuseStep 9203341 = 3451253) B3451253
theorem B1437329 : Blo 956588 1437329 := bstep (se 2 (by rfl) ⟨538998, by rfl⟩ : syracuseStep 1437329 = 1077997) B1077997
theorem B1076899 : Blo 956588 1076899 := bstep (se 1 (by rfl) ⟨807674, by rfl⟩ : syracuseStep 1076899 = 1615349) B1615349
theorem B1437347 : Blo 956588 1437347 := bstep (se 1 (by rfl) ⟨1078010, by rfl⟩ : syracuseStep 1437347 = 2156021) B2156021
theorem B1437377 : Blo 956588 1437377 := bstep (se 2 (by rfl) ⟨539016, by rfl⟩ : syracuseStep 1437377 = 1078033) B1078033
theorem B2158289 : Blo 956588 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B1437395 : Blo 956588 1437395 := bstep (se 1 (by rfl) ⟨1078046, by rfl⟩ : syracuseStep 1437395 = 2156093) B2156093
theorem B17493731 : Blo 956588 17493731 := bstep (se 1 (by rfl) ⟨13120298, by rfl⟩ : syracuseStep 17493731 = 26240597) B26240597
theorem B2158307 : Blo 956588 2158307 := bstep (se 1 (by rfl) ⟨1618730, by rfl⟩ : syracuseStep 2158307 = 3237461) B3237461
theorem B1437425 : Blo 956588 1437425 := bstep (se 2 (by rfl) ⟨539034, by rfl⟩ : syracuseStep 1437425 = 1078069) B1078069
theorem B1437443 : Blo 956588 1437443 := bstep (se 1 (by rfl) ⟨1078082, by rfl⟩ : syracuseStep 1437443 = 2156165) B2156165
theorem B1437473 : Blo 956588 1437473 := bstep (se 2 (by rfl) ⟨539052, by rfl⟩ : syracuseStep 1437473 = 1078105) B1078105
theorem B3239729 : Blo 956588 3239729 := bstep (se 2 (by rfl) ⟨1214898, by rfl⟩ : syracuseStep 3239729 = 2429797) B2429797
theorem B1077043 : Blo 956588 1077043 := bstep (se 1 (by rfl) ⟨807782, by rfl⟩ : syracuseStep 1077043 = 1615565) B1615565
theorem B1437491 : Blo 956588 1437491 := bstep (se 1 (by rfl) ⟨1078118, by rfl⟩ : syracuseStep 1437491 = 2156237) B2156237
theorem B1437521 : Blo 956588 1437521 := bstep (se 2 (by rfl) ⟨539070, by rfl⟩ : syracuseStep 1437521 = 1078141) B1078141
theorem B1437539 : Blo 956588 1437539 := bstep (se 1 (by rfl) ⟨1078154, by rfl⟩ : syracuseStep 1437539 = 2156309) B2156309
theorem B1437569 : Blo 956588 1437569 := bstep (se 2 (by rfl) ⟨539088, by rfl⟩ : syracuseStep 1437569 = 1078177) B1078177
theorem B1437587 : Blo 956588 1437587 := bstep (se 1 (by rfl) ⟨1078190, by rfl⟩ : syracuseStep 1437587 = 2156381) B2156381
theorem B1437617 : Blo 956588 1437617 := bstep (se 2 (by rfl) ⟨539106, by rfl⟩ : syracuseStep 1437617 = 1078213) B1078213
theorem B1077187 : Blo 956588 1077187 := bstep (se 1 (by rfl) ⟨807890, by rfl⟩ : syracuseStep 1077187 = 1615781) B1615781
theorem B1437635 : Blo 956588 1437635 := bstep (se 1 (by rfl) ⟨1078226, by rfl⟩ : syracuseStep 1437635 = 2156453) B2156453
theorem B1437665 : Blo 956588 1437665 := bstep (se 2 (by rfl) ⟨539124, by rfl⟩ : syracuseStep 1437665 = 1078249) B1078249
theorem B2158577 : Blo 956588 2158577 := bstep (se 2 (by rfl) ⟨809466, by rfl⟩ : syracuseStep 2158577 = 1618933) B1618933
theorem B1437683 : Blo 956588 1437683 := bstep (se 1 (by rfl) ⟨1078262, by rfl⟩ : syracuseStep 1437683 = 2156525) B2156525
theorem B2158595 : Blo 956588 2158595 := bstep (se 1 (by rfl) ⟨1618946, by rfl⟩ : syracuseStep 2158595 = 3237893) B3237893
theorem B4845581 : Blo 956588 4845581 := bstep (se 3 (by rfl) ⟨908546, by rfl⟩ : syracuseStep 4845581 = 1817093) B1817093
theorem B1437713 : Blo 956588 1437713 := bstep (se 2 (by rfl) ⟨539142, by rfl⟩ : syracuseStep 1437713 = 1078285) B1078285
theorem B1437731 : Blo 956588 1437731 := bstep (se 1 (by rfl) ⟨1078298, by rfl⟩ : syracuseStep 1437731 = 2156597) B2156597
theorem B1437761 : Blo 956588 1437761 := bstep (se 2 (by rfl) ⟨539160, by rfl⟩ : syracuseStep 1437761 = 1078321) B1078321
theorem B1077331 : Blo 956588 1077331 := bstep (se 1 (by rfl) ⟨807998, by rfl⟩ : syracuseStep 1077331 = 1615997) B1615997
theorem B1437779 : Blo 956588 1437779 := bstep (se 1 (by rfl) ⟨1078334, by rfl⟩ : syracuseStep 1437779 = 2156669) B2156669
theorem B1437809 : Blo 956588 1437809 := bstep (se 2 (by rfl) ⟨539178, by rfl⟩ : syracuseStep 1437809 = 1078357) B1078357
theorem B1437827 : Blo 956588 1437827 := bstep (se 1 (by rfl) ⟨1078370, by rfl⟩ : syracuseStep 1437827 = 2156741) B2156741
theorem B1437857 : Blo 956588 1437857 := bstep (se 2 (by rfl) ⟨539196, by rfl⟩ : syracuseStep 1437857 = 1078393) B1078393
theorem B1437875 : Blo 956588 1437875 := bstep (se 1 (by rfl) ⟨1078406, by rfl⟩ : syracuseStep 1437875 = 2156813) B2156813
theorem B1437905 : Blo 956588 1437905 := bstep (se 2 (by rfl) ⟨539214, by rfl⟩ : syracuseStep 1437905 = 1078429) B1078429
theorem B1077475 : Blo 956588 1077475 := bstep (se 1 (by rfl) ⟨808106, by rfl⟩ : syracuseStep 1077475 = 1616213) B1616213
theorem B1437923 : Blo 956588 1437923 := bstep (se 1 (by rfl) ⟨1078442, by rfl⟩ : syracuseStep 1437923 = 2156885) B2156885
theorem B1437953 : Blo 956588 1437953 := bstep (se 2 (by rfl) ⟨539232, by rfl⟩ : syracuseStep 1437953 = 1078465) B1078465
theorem B2158865 : Blo 956588 2158865 := bstep (se 2 (by rfl) ⟨809574, by rfl⟩ : syracuseStep 2158865 = 1619149) B1619149
theorem B1437971 : Blo 956588 1437971 := bstep (se 1 (by rfl) ⟨1078478, by rfl⟩ : syracuseStep 1437971 = 2156957) B2156957
theorem B3633443 : Blo 956588 3633443 := bstep (se 1 (by rfl) ⟨2725082, by rfl⟩ : syracuseStep 3633443 = 5450165) B5450165
theorem B2158883 : Blo 956588 2158883 := bstep (se 1 (by rfl) ⟨1619162, by rfl⟩ : syracuseStep 2158883 = 3238325) B3238325
theorem B3633457 : Blo 956588 3633457 := bstep (se 2 (by rfl) ⟨1362546, by rfl⟩ : syracuseStep 3633457 = 2725093) B2725093
theorem B1438001 : Blo 956588 1438001 := bstep (se 2 (by rfl) ⟨539250, by rfl⟩ : syracuseStep 1438001 = 1078501) B1078501
theorem B1438019 : Blo 956588 1438019 := bstep (se 1 (by rfl) ⟨1078514, by rfl⟩ : syracuseStep 1438019 = 2157029) B2157029
theorem B3240269 : Blo 956588 3240269 := bstep (se 3 (by rfl) ⟨607550, by rfl⟩ : syracuseStep 3240269 = 1215101) B1215101
theorem B1438049 : Blo 956588 1438049 := bstep (se 2 (by rfl) ⟨539268, by rfl⟩ : syracuseStep 1438049 = 1078537) B1078537
theorem B1077619 : Blo 956588 1077619 := bstep (se 1 (by rfl) ⟨808214, by rfl⟩ : syracuseStep 1077619 = 1616429) B1616429
theorem B1438067 : Blo 956588 1438067 := bstep (se 1 (by rfl) ⟨1078550, by rfl⟩ : syracuseStep 1438067 = 2157101) B2157101
theorem B3240323 : Blo 956588 3240323 := bstep (se 1 (by rfl) ⟨2430242, by rfl⟩ : syracuseStep 3240323 = 4860485) B4860485
theorem B1438097 : Blo 956588 1438097 := bstep (se 2 (by rfl) ⟨539286, by rfl⟩ : syracuseStep 1438097 = 1078573) B1078573
theorem B1438115 : Blo 956588 1438115 := bstep (se 1 (by rfl) ⟨1078586, by rfl⟩ : syracuseStep 1438115 = 2157173) B2157173
theorem B5468593 : Blo 956588 5468593 := bstep (se 2 (by rfl) ⟨2050722, by rfl⟩ : syracuseStep 5468593 = 4101445) B4101445
theorem B1438145 : Blo 956588 1438145 := bstep (se 2 (by rfl) ⟨539304, by rfl⟩ : syracuseStep 1438145 = 1078609) B1078609
theorem B1438163 : Blo 956588 1438163 := bstep (se 1 (by rfl) ⟨1078622, by rfl⟩ : syracuseStep 1438163 = 2157245) B2157245
theorem B1438193 : Blo 956588 1438193 := bstep (se 2 (by rfl) ⟨539322, by rfl⟩ : syracuseStep 1438193 = 1078645) B1078645
theorem B1536499 : Blo 956588 1536499 := bstep (se 1 (by rfl) ⟨1152374, by rfl⟩ : syracuseStep 1536499 = 2304749) B2304749
theorem B1077763 : Blo 956588 1077763 := bstep (se 1 (by rfl) ⟨808322, by rfl⟩ : syracuseStep 1077763 = 1616645) B1616645
theorem B1438211 : Blo 956588 1438211 := bstep (se 1 (by rfl) ⟨1078658, by rfl⟩ : syracuseStep 1438211 = 2157317) B2157317
theorem B1438241 : Blo 956588 1438241 := bstep (se 2 (by rfl) ⟨539340, by rfl⟩ : syracuseStep 1438241 = 1078681) B1078681
theorem B2159153 : Blo 956588 2159153 := bstep (se 2 (by rfl) ⟨809682, by rfl⟩ : syracuseStep 2159153 = 1619365) B1619365
theorem B1438259 : Blo 956588 1438259 := bstep (se 1 (by rfl) ⟨1078694, by rfl⟩ : syracuseStep 1438259 = 2157389) B2157389
theorem B2159171 : Blo 956588 2159171 := bstep (se 1 (by rfl) ⟨1619378, by rfl⟩ : syracuseStep 2159171 = 3238757) B3238757
theorem B1438289 : Blo 956588 1438289 := bstep (se 2 (by rfl) ⟨539358, by rfl⟩ : syracuseStep 1438289 = 1078717) B1078717
theorem B1438307 : Blo 956588 1438307 := bstep (se 1 (by rfl) ⟨1078730, by rfl⟩ : syracuseStep 1438307 = 2157461) B2157461
theorem B1438337 : Blo 956588 1438337 := bstep (se 2 (by rfl) ⟨539376, by rfl⟩ : syracuseStep 1438337 = 1078753) B1078753
theorem B3240593 : Blo 956588 3240593 := bstep (se 2 (by rfl) ⟨1215222, by rfl⟩ : syracuseStep 3240593 = 2430445) B2430445
theorem B1077907 : Blo 956588 1077907 := bstep (se 1 (by rfl) ⟨808430, by rfl⟩ : syracuseStep 1077907 = 1616861) B1616861
theorem B1438355 : Blo 956588 1438355 := bstep (se 1 (by rfl) ⟨1078766, by rfl⟩ : syracuseStep 1438355 = 2157533) B2157533
theorem B1438385 : Blo 956588 1438385 := bstep (se 2 (by rfl) ⟨539394, by rfl⟩ : syracuseStep 1438385 = 1078789) B1078789
theorem B1438403 : Blo 956588 1438403 := bstep (se 1 (by rfl) ⟨1078802, by rfl⟩ : syracuseStep 1438403 = 2157605) B2157605
theorem B1438433 : Blo 956588 1438433 := bstep (se 2 (by rfl) ⟨539412, by rfl⟩ : syracuseStep 1438433 = 1078825) B1078825
theorem B1438451 : Blo 956588 1438451 := bstep (se 1 (by rfl) ⟨1078838, by rfl⟩ : syracuseStep 1438451 = 2157677) B2157677
theorem B1438481 : Blo 956588 1438481 := bstep (se 2 (by rfl) ⟨539430, by rfl⟩ : syracuseStep 1438481 = 1078861) B1078861
theorem B1078051 : Blo 956588 1078051 := bstep (se 1 (by rfl) ⟨808538, by rfl⟩ : syracuseStep 1078051 = 1617077) B1617077
theorem B1438499 : Blo 956588 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B1438529 : Blo 956588 1438529 := bstep (se 2 (by rfl) ⟨539448, by rfl⟩ : syracuseStep 1438529 = 1078897) B1078897
theorem B5174093 : Blo 956588 5174093 := bstep (se 3 (by rfl) ⟨970142, by rfl⟩ : syracuseStep 5174093 = 1940285) B1940285
theorem B2159441 : Blo 956588 2159441 := bstep (se 2 (by rfl) ⟨809790, by rfl⟩ : syracuseStep 2159441 = 1619581) B1619581
theorem B1438547 : Blo 956588 1438547 := bstep (se 1 (by rfl) ⟨1078910, by rfl⟩ : syracuseStep 1438547 = 2157821) B2157821
theorem B2159459 : Blo 956588 2159459 := bstep (se 1 (by rfl) ⟨1619594, by rfl⟩ : syracuseStep 2159459 = 3239189) B3239189
theorem B1438577 : Blo 956588 1438577 := bstep (se 2 (by rfl) ⟨539466, by rfl⟩ : syracuseStep 1438577 = 1078933) B1078933
theorem B1438595 : Blo 956588 1438595 := bstep (se 1 (by rfl) ⟨1078946, by rfl⟩ : syracuseStep 1438595 = 2157893) B2157893
theorem B1438625 : Blo 956588 1438625 := bstep (se 2 (by rfl) ⟨539484, by rfl⟩ : syracuseStep 1438625 = 1078969) B1078969
theorem B1078195 : Blo 956588 1078195 := bstep (se 1 (by rfl) ⟨808646, by rfl⟩ : syracuseStep 1078195 = 1617293) B1617293
theorem B1438643 : Blo 956588 1438643 := bstep (se 1 (by rfl) ⟨1078982, by rfl⟩ : syracuseStep 1438643 = 2157965) B2157965
theorem B1438673 : Blo 956588 1438673 := bstep (se 2 (by rfl) ⟨539502, by rfl⟩ : syracuseStep 1438673 = 1079005) B1079005
theorem B1438691 : Blo 956588 1438691 := bstep (se 1 (by rfl) ⟨1079018, by rfl⟩ : syracuseStep 1438691 = 2158037) B2158037
theorem B1438721 : Blo 956588 1438721 := bstep (se 2 (by rfl) ⟨539520, by rfl⟩ : syracuseStep 1438721 = 1079041) B1079041
theorem B1438739 : Blo 956588 1438739 := bstep (se 1 (by rfl) ⟨1079054, by rfl⟩ : syracuseStep 1438739 = 2158109) B2158109
theorem B2421809 : Blo 956588 2421809 := bstep (se 2 (by rfl) ⟨908178, by rfl⟩ : syracuseStep 2421809 = 1816357) B1816357
theorem B1438769 : Blo 956588 1438769 := bstep (se 2 (by rfl) ⟨539538, by rfl⟩ : syracuseStep 1438769 = 1079077) B1079077
theorem B1078339 : Blo 956588 1078339 := bstep (se 1 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 1078339 = 1617509) B1617509
theorem B1438787 : Blo 956588 1438787 := bstep (se 1 (by rfl) ⟨1079090, by rfl⟩ : syracuseStep 1438787 = 2158181) B2158181
theorem B1438817 : Blo 956588 1438817 := bstep (se 2 (by rfl) ⟨539556, by rfl⟩ : syracuseStep 1438817 = 1079113) B1079113
theorem B2421859 : Blo 956588 2421859 := bstep (se 1 (by rfl) ⟨1816394, by rfl⟩ : syracuseStep 2421859 = 3632789) B3632789
theorem B2159729 : Blo 956588 2159729 := bstep (se 2 (by rfl) ⟨809898, by rfl⟩ : syracuseStep 2159729 = 1619797) B1619797
theorem B1438835 : Blo 956588 1438835 := bstep (se 1 (by rfl) ⟨1079126, by rfl⟩ : syracuseStep 1438835 = 2158253) B2158253
theorem B2159747 : Blo 956588 2159747 := bstep (se 1 (by rfl) ⟨1619810, by rfl⟩ : syracuseStep 2159747 = 3239621) B3239621
theorem B1438865 : Blo 956588 1438865 := bstep (se 2 (by rfl) ⟨539574, by rfl⟩ : syracuseStep 1438865 = 1079149) B1079149
theorem B1438883 : Blo 956588 1438883 := bstep (se 1 (by rfl) ⟨1079162, by rfl⟩ : syracuseStep 1438883 = 2158325) B2158325
theorem B3241133 : Blo 956588 3241133 := bstep (se 3 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 3241133 = 1215425) B1215425
theorem B1438913 : Blo 956588 1438913 := bstep (se 2 (by rfl) ⟨539592, by rfl⟩ : syracuseStep 1438913 = 1079185) B1079185
theorem B3077315 : Blo 956588 3077315 := bstep (se 1 (by rfl) ⟨2307986, by rfl⟩ : syracuseStep 3077315 = 4615973) B4615973
theorem B1078483 : Blo 956588 1078483 := bstep (se 1 (by rfl) ⟨808862, by rfl⟩ : syracuseStep 1078483 = 1617725) B1617725
theorem B1438931 : Blo 956588 1438931 := bstep (se 1 (by rfl) ⟨1079198, by rfl⟩ : syracuseStep 1438931 = 2158397) B2158397
theorem B3241187 : Blo 956588 3241187 := bstep (se 1 (by rfl) ⟨2430890, by rfl⟩ : syracuseStep 3241187 = 4861781) B4861781
theorem B2422001 : Blo 956588 2422001 := bstep (se 2 (by rfl) ⟨908250, by rfl⟩ : syracuseStep 2422001 = 1816501) B1816501
theorem B1438961 : Blo 956588 1438961 := bstep (se 2 (by rfl) ⟨539610, by rfl⟩ : syracuseStep 1438961 = 1079221) B1079221
theorem B1438979 : Blo 956588 1438979 := bstep (se 1 (by rfl) ⟨1079234, by rfl⟩ : syracuseStep 1438979 = 2158469) B2158469
theorem B4912397 : Blo 956588 4912397 := bstep (se 3 (by rfl) ⟨921074, by rfl⟩ : syracuseStep 4912397 = 1842149) B1842149
theorem B1439009 : Blo 956588 1439009 := bstep (se 2 (by rfl) ⟨539628, by rfl⟩ : syracuseStep 1439009 = 1079257) B1079257
theorem B1439027 : Blo 956588 1439027 := bstep (se 1 (by rfl) ⟨1079270, by rfl⟩ : syracuseStep 1439027 = 2158541) B2158541
theorem B1439057 : Blo 956588 1439057 := bstep (se 2 (by rfl) ⟨539646, by rfl⟩ : syracuseStep 1439057 = 1079293) B1079293
theorem B1078627 : Blo 956588 1078627 := bstep (se 1 (by rfl) ⟨808970, by rfl⟩ : syracuseStep 1078627 = 1617941) B1617941
theorem B1439075 : Blo 956588 1439075 := bstep (se 1 (by rfl) ⟨1079306, by rfl⟩ : syracuseStep 1439075 = 2158613) B2158613
theorem B1439105 : Blo 956588 1439105 := bstep (se 2 (by rfl) ⟨539664, by rfl⟩ : syracuseStep 1439105 = 1079329) B1079329
theorem B2160017 : Blo 956588 2160017 := bstep (se 2 (by rfl) ⟨810006, by rfl⟩ : syracuseStep 2160017 = 1620013) B1620013
theorem B1439123 : Blo 956588 1439123 := bstep (se 1 (by rfl) ⟨1079342, by rfl⟩ : syracuseStep 1439123 = 2158685) B2158685
theorem B1537427 : Blo 956588 1537427 := bstep (se 1 (by rfl) ⟨1153070, by rfl⟩ : syracuseStep 1537427 = 2306141) B2306141
theorem B2160035 : Blo 956588 2160035 := bstep (se 1 (by rfl) ⟨1620026, by rfl⟩ : syracuseStep 2160035 = 3240053) B3240053
theorem B1439153 : Blo 956588 1439153 := bstep (se 2 (by rfl) ⟨539682, by rfl⟩ : syracuseStep 1439153 = 1079365) B1079365
theorem B1439171 : Blo 956588 1439171 := bstep (se 1 (by rfl) ⟨1079378, by rfl⟩ : syracuseStep 1439171 = 2158757) B2158757
theorem B1439201 : Blo 956588 1439201 := bstep (se 2 (by rfl) ⟨539700, by rfl⟩ : syracuseStep 1439201 = 1079401) B1079401
theorem B3241457 : Blo 956588 3241457 := bstep (se 2 (by rfl) ⟨1215546, by rfl⟩ : syracuseStep 3241457 = 2431093) B2431093
theorem B1078771 : Blo 956588 1078771 := bstep (se 1 (by rfl) ⟨809078, by rfl⟩ : syracuseStep 1078771 = 1618157) B1618157
theorem B1439219 : Blo 956588 1439219 := bstep (se 1 (by rfl) ⟨1079414, by rfl⟩ : syracuseStep 1439219 = 2158829) B2158829
theorem B1439249 : Blo 956588 1439249 := bstep (se 2 (by rfl) ⟨539718, by rfl⟩ : syracuseStep 1439249 = 1079437) B1079437
theorem B1439267 : Blo 956588 1439267 := bstep (se 1 (by rfl) ⟨1079450, by rfl⟩ : syracuseStep 1439267 = 2158901) B2158901
theorem B1439297 : Blo 956588 1439297 := bstep (se 2 (by rfl) ⟨539736, by rfl⟩ : syracuseStep 1439297 = 1079473) B1079473
theorem B4093517 : Blo 956588 4093517 := bstep (se 3 (by rfl) ⟨767534, by rfl⟩ : syracuseStep 4093517 = 1535069) B1535069
theorem B1439315 : Blo 956588 1439315 := bstep (se 1 (by rfl) ⟨1079486, by rfl⟩ : syracuseStep 1439315 = 2158973) B2158973
theorem B1439345 : Blo 956588 1439345 := bstep (se 2 (by rfl) ⟨539754, by rfl⟩ : syracuseStep 1439345 = 1079509) B1079509
theorem B1078915 : Blo 956588 1078915 := bstep (se 1 (by rfl) ⟨809186, by rfl⟩ : syracuseStep 1078915 = 1618373) B1618373
theorem B1439363 : Blo 956588 1439363 := bstep (se 1 (by rfl) ⟨1079522, by rfl⟩ : syracuseStep 1439363 = 2159045) B2159045
theorem B1439393 : Blo 956588 1439393 := bstep (se 2 (by rfl) ⟨539772, by rfl⟩ : syracuseStep 1439393 = 1079545) B1079545
theorem B1537697 : Blo 956588 1537697 := bstep (se 2 (by rfl) ⟨576636, by rfl⟩ : syracuseStep 1537697 = 1153273) B1153273
theorem B2160305 : Blo 956588 2160305 := bstep (se 2 (by rfl) ⟨810114, by rfl⟩ : syracuseStep 2160305 = 1620229) B1620229
theorem B1439411 : Blo 956588 1439411 := bstep (se 1 (by rfl) ⟨1079558, by rfl⟩ : syracuseStep 1439411 = 2159117) B2159117
theorem B2160323 : Blo 956588 2160323 := bstep (se 1 (by rfl) ⟨1620242, by rfl⟩ : syracuseStep 2160323 = 3240485) B3240485
theorem B1439441 : Blo 956588 1439441 := bstep (se 2 (by rfl) ⟨539790, by rfl⟩ : syracuseStep 1439441 = 1079581) B1079581
theorem B3634915 : Blo 956588 3634915 := bstep (se 1 (by rfl) ⟨2726186, by rfl⟩ : syracuseStep 3634915 = 5452373) B5452373
theorem B1439459 : Blo 956588 1439459 := bstep (se 1 (by rfl) ⟨1079594, by rfl⟩ : syracuseStep 1439459 = 2159189) B2159189
theorem B1439489 : Blo 956588 1439489 := bstep (se 2 (by rfl) ⟨539808, by rfl⟩ : syracuseStep 1439489 = 1079617) B1079617
theorem B1079059 : Blo 956588 1079059 := bstep (se 1 (by rfl) ⟨809294, by rfl⟩ : syracuseStep 1079059 = 1618589) B1618589
theorem B1439507 : Blo 956588 1439507 := bstep (se 1 (by rfl) ⟨1079630, by rfl⟩ : syracuseStep 1439507 = 2159261) B2159261
theorem B1439537 : Blo 956588 1439537 := bstep (se 2 (by rfl) ⟨539826, by rfl⟩ : syracuseStep 1439537 = 1079653) B1079653
theorem B1439555 : Blo 956588 1439555 := bstep (se 1 (by rfl) ⟨1079666, by rfl⟩ : syracuseStep 1439555 = 2159333) B2159333
theorem B1439585 : Blo 956588 1439585 := bstep (se 2 (by rfl) ⟨539844, by rfl⟩ : syracuseStep 1439585 = 1079689) B1079689
theorem B5470051 : Blo 956588 5470051 := bstep (se 1 (by rfl) ⟨4102538, by rfl⟩ : syracuseStep 5470051 = 8205077) B8205077
theorem B1439603 : Blo 956588 1439603 := bstep (se 1 (by rfl) ⟨1079702, by rfl⟩ : syracuseStep 1439603 = 2159405) B2159405
theorem B1439633 : Blo 956588 1439633 := bstep (se 2 (by rfl) ⟨539862, by rfl⟩ : syracuseStep 1439633 = 1079725) B1079725
theorem B1079203 : Blo 956588 1079203 := bstep (se 1 (by rfl) ⟨809402, by rfl⟩ : syracuseStep 1079203 = 1618805) B1618805
theorem B1439651 : Blo 956588 1439651 := bstep (se 1 (by rfl) ⟨1079738, by rfl⟩ : syracuseStep 1439651 = 2159477) B2159477
theorem B1439681 : Blo 956588 1439681 := bstep (se 2 (by rfl) ⟨539880, by rfl⟩ : syracuseStep 1439681 = 1079761) B1079761
theorem B1537985 : Blo 956588 1537985 := bstep (se 2 (by rfl) ⟨576744, by rfl⟩ : syracuseStep 1537985 = 1153489) B1153489
theorem B2160593 : Blo 956588 2160593 := bstep (se 2 (by rfl) ⟨810222, by rfl⟩ : syracuseStep 2160593 = 1620445) B1620445
theorem B1439699 : Blo 956588 1439699 := bstep (se 1 (by rfl) ⟨1079774, by rfl⟩ : syracuseStep 1439699 = 2159549) B2159549
theorem B2160611 : Blo 956588 2160611 := bstep (se 1 (by rfl) ⟨1620458, by rfl⟩ : syracuseStep 2160611 = 3240917) B3240917
theorem B1439729 : Blo 956588 1439729 := bstep (se 2 (by rfl) ⟨539898, by rfl⟩ : syracuseStep 1439729 = 1079797) B1079797
theorem B1439747 : Blo 956588 1439747 := bstep (se 1 (by rfl) ⟨1079810, by rfl⟩ : syracuseStep 1439747 = 2159621) B2159621
theorem B1439777 : Blo 956588 1439777 := bstep (se 2 (by rfl) ⟨539916, by rfl⟩ : syracuseStep 1439777 = 1079833) B1079833
theorem B1079347 : Blo 956588 1079347 := bstep (se 1 (by rfl) ⟨809510, by rfl⟩ : syracuseStep 1079347 = 1619021) B1619021
theorem B1439795 : Blo 956588 1439795 := bstep (se 1 (by rfl) ⟨1079846, by rfl⟩ : syracuseStep 1439795 = 2159693) B2159693
theorem B1439825 : Blo 956588 1439825 := bstep (se 2 (by rfl) ⟨539934, by rfl⟩ : syracuseStep 1439825 = 1079869) B1079869
theorem B1439843 : Blo 956588 1439843 := bstep (se 1 (by rfl) ⟨1079882, by rfl⟩ : syracuseStep 1439843 = 2159765) B2159765
theorem B1439873 : Blo 956588 1439873 := bstep (se 2 (by rfl) ⟨539952, by rfl⟩ : syracuseStep 1439873 = 1079905) B1079905
theorem B2586755 : Blo 956588 2586755 := bstep (se 1 (by rfl) ⟨1940066, by rfl⟩ : syracuseStep 2586755 = 3880133) B3880133
theorem B1439891 : Blo 956588 1439891 := bstep (se 1 (by rfl) ⟨1079918, by rfl⟩ : syracuseStep 1439891 = 2159837) B2159837
theorem B1439921 : Blo 956588 1439921 := bstep (se 2 (by rfl) ⟨539970, by rfl⟩ : syracuseStep 1439921 = 1079941) B1079941
theorem B1079491 : Blo 956588 1079491 := bstep (se 1 (by rfl) ⟨809618, by rfl⟩ : syracuseStep 1079491 = 1619237) B1619237
theorem B1439939 : Blo 956588 1439939 := bstep (se 1 (by rfl) ⟨1079954, by rfl⟩ : syracuseStep 1439939 = 2159909) B2159909
theorem B2422993 : Blo 956588 2422993 := bstep (se 2 (by rfl) ⟨908622, by rfl⟩ : syracuseStep 2422993 = 1817245) B1817245
theorem B1439969 : Blo 956588 1439969 := bstep (se 2 (by rfl) ⟨539988, by rfl⟩ : syracuseStep 1439969 = 1079977) B1079977
theorem B8190179 : Blo 956588 8190179 := bstep (se 1 (by rfl) ⟨6142634, by rfl⟩ : syracuseStep 8190179 = 12285269) B12285269
theorem B2160881 : Blo 956588 2160881 := bstep (se 2 (by rfl) ⟨810330, by rfl⟩ : syracuseStep 2160881 = 1620661) B1620661
theorem B1439987 : Blo 956588 1439987 := bstep (se 1 (by rfl) ⟨1079990, by rfl⟩ : syracuseStep 1439987 = 2159981) B2159981
theorem B2160899 : Blo 956588 2160899 := bstep (se 1 (by rfl) ⟨1620674, by rfl⟩ : syracuseStep 2160899 = 3241349) B3241349
theorem B1440017 : Blo 956588 1440017 := bstep (se 2 (by rfl) ⟨540006, by rfl⟩ : syracuseStep 1440017 = 1080013) B1080013
theorem B1440035 : Blo 956588 1440035 := bstep (se 1 (by rfl) ⟨1080026, by rfl⟩ : syracuseStep 1440035 = 2160053) B2160053
theorem B1440065 : Blo 956588 1440065 := bstep (se 2 (by rfl) ⟨540024, by rfl⟩ : syracuseStep 1440065 = 1080049) B1080049
theorem B1079635 : Blo 956588 1079635 := bstep (se 1 (by rfl) ⟨809726, by rfl⟩ : syracuseStep 1079635 = 1619453) B1619453
theorem B1440083 : Blo 956588 1440083 := bstep (se 1 (by rfl) ⟨1080062, by rfl⟩ : syracuseStep 1440083 = 2160125) B2160125
theorem B1538401 : Blo 956588 1538401 := bstep (se 2 (by rfl) ⟨576900, by rfl⟩ : syracuseStep 1538401 = 1153801) B1153801
theorem B1440113 : Blo 956588 1440113 := bstep (se 2 (by rfl) ⟨540042, by rfl⟩ : syracuseStep 1440113 = 1080085) B1080085
theorem B5470577 : Blo 956588 5470577 := bstep (se 2 (by rfl) ⟨2051466, by rfl⟩ : syracuseStep 5470577 = 4102933) B4102933
theorem B1440131 : Blo 956588 1440131 := bstep (se 1 (by rfl) ⟨1080098, by rfl⟩ : syracuseStep 1440131 = 2160197) B2160197
theorem B1440161 : Blo 956588 1440161 := bstep (se 2 (by rfl) ⟨540060, by rfl⟩ : syracuseStep 1440161 = 1080121) B1080121
theorem B1440179 : Blo 956588 1440179 := bstep (se 1 (by rfl) ⟨1080134, by rfl⟩ : syracuseStep 1440179 = 2160269) B2160269
theorem B1440209 : Blo 956588 1440209 := bstep (se 2 (by rfl) ⟨540078, by rfl⟩ : syracuseStep 1440209 = 1080157) B1080157
theorem B2423267 : Blo 956588 2423267 := bstep (se 1 (by rfl) ⟨1817450, by rfl⟩ : syracuseStep 2423267 = 3634901) B3634901
theorem B1079779 : Blo 956588 1079779 := bstep (se 1 (by rfl) ⟨809834, by rfl⟩ : syracuseStep 1079779 = 1619669) B1619669
theorem B1440227 : Blo 956588 1440227 := bstep (se 1 (by rfl) ⟨1080170, by rfl⟩ : syracuseStep 1440227 = 2160341) B2160341
theorem B1440257 : Blo 956588 1440257 := bstep (se 2 (by rfl) ⟨540096, by rfl⟩ : syracuseStep 1440257 = 1080193) B1080193
theorem B2161169 : Blo 956588 2161169 := bstep (se 2 (by rfl) ⟨810438, by rfl⟩ : syracuseStep 2161169 = 1620877) B1620877
theorem B1440275 : Blo 956588 1440275 := bstep (se 1 (by rfl) ⟨1080206, by rfl⟩ : syracuseStep 1440275 = 2160413) B2160413
theorem B2161187 : Blo 956588 2161187 := bstep (se 1 (by rfl) ⟨1620890, by rfl⟩ : syracuseStep 2161187 = 3241781) B3241781
theorem B1440305 : Blo 956588 1440305 := bstep (se 2 (by rfl) ⟨540114, by rfl⟩ : syracuseStep 1440305 = 1080229) B1080229
theorem B1440323 : Blo 956588 1440323 := bstep (se 1 (by rfl) ⟨1080242, by rfl⟩ : syracuseStep 1440323 = 2160485) B2160485
theorem B1440353 : Blo 956588 1440353 := bstep (se 2 (by rfl) ⟨540132, by rfl⟩ : syracuseStep 1440353 = 1080265) B1080265
theorem B1079923 : Blo 956588 1079923 := bstep (se 1 (by rfl) ⟨809942, by rfl⟩ : syracuseStep 1079923 = 1619885) B1619885
theorem B1440371 : Blo 956588 1440371 := bstep (se 1 (by rfl) ⟨1080278, by rfl⟩ : syracuseStep 1440371 = 2160557) B2160557
theorem B1440401 : Blo 956588 1440401 := bstep (se 2 (by rfl) ⟨540150, by rfl⟩ : syracuseStep 1440401 = 1080301) B1080301
theorem B2423459 : Blo 956588 2423459 := bstep (se 1 (by rfl) ⟨1817594, by rfl⟩ : syracuseStep 2423459 = 3635189) B3635189
theorem B1440419 : Blo 956588 1440419 := bstep (se 1 (by rfl) ⟨1080314, by rfl⟩ : syracuseStep 1440419 = 2160629) B2160629
theorem B1440449 : Blo 956588 1440449 := bstep (se 2 (by rfl) ⟨540168, by rfl⟩ : syracuseStep 1440449 = 1080337) B1080337
theorem B1440467 : Blo 956588 1440467 := bstep (se 1 (by rfl) ⟨1080350, by rfl⟩ : syracuseStep 1440467 = 2160701) B2160701
theorem B1211107 : Blo 956588 1211107 := bstep (se 1 (by rfl) ⟨908330, by rfl⟩ : syracuseStep 1211107 = 1816661) B1816661
theorem B1440497 : Blo 956588 1440497 := bstep (se 2 (by rfl) ⟨540186, by rfl⟩ : syracuseStep 1440497 = 1080373) B1080373
theorem B1080067 : Blo 956588 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B1440515 : Blo 956588 1440515 := bstep (se 1 (by rfl) ⟨1080386, by rfl⟩ : syracuseStep 1440515 = 2160773) B2160773
theorem B1440545 : Blo 956588 1440545 := bstep (se 2 (by rfl) ⟨540204, by rfl⟩ : syracuseStep 1440545 = 1080409) B1080409
theorem B1440563 : Blo 956588 1440563 := bstep (se 1 (by rfl) ⟨1080422, by rfl⟩ : syracuseStep 1440563 = 2160845) B2160845
theorem B1211203 : Blo 956588 1211203 := bstep (se 1 (by rfl) ⟨908402, by rfl⟩ : syracuseStep 1211203 = 1816805) B1816805
theorem B1440593 : Blo 956588 1440593 := bstep (se 2 (by rfl) ⟨540222, by rfl⟩ : syracuseStep 1440593 = 1080445) B1080445
theorem B1440611 : Blo 956588 1440611 := bstep (se 1 (by rfl) ⟨1080458, by rfl⟩ : syracuseStep 1440611 = 2160917) B2160917
theorem B4848497 : Blo 956588 4848497 := bstep (se 2 (by rfl) ⟨1818186, by rfl⟩ : syracuseStep 4848497 = 3636373) B3636373
theorem B1440641 : Blo 956588 1440641 := bstep (se 2 (by rfl) ⟨540240, by rfl⟩ : syracuseStep 1440641 = 1080481) B1080481
theorem B1080211 : Blo 956588 1080211 := bstep (se 1 (by rfl) ⟨810158, by rfl⟩ : syracuseStep 1080211 = 1620317) B1620317
theorem B1440659 : Blo 956588 1440659 := bstep (se 1 (by rfl) ⟨1080494, by rfl⟩ : syracuseStep 1440659 = 2160989) B2160989
theorem B1440689 : Blo 956588 1440689 := bstep (se 2 (by rfl) ⟨540258, by rfl⟩ : syracuseStep 1440689 = 1080517) B1080517
theorem B1440707 : Blo 956588 1440707 := bstep (se 1 (by rfl) ⟨1080530, by rfl⟩ : syracuseStep 1440707 = 2161061) B2161061
theorem B1440737 : Blo 956588 1440737 := bstep (se 2 (by rfl) ⟨540276, by rfl⟩ : syracuseStep 1440737 = 1080553) B1080553
theorem B3505123 : Blo 956588 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B6224881 : Blo 956588 6224881 := bstep (se 2 (by rfl) ⟨2334330, by rfl⟩ : syracuseStep 6224881 = 4668661) B4668661
theorem B1440755 : Blo 956588 1440755 := bstep (se 1 (by rfl) ⟨1080566, by rfl⟩ : syracuseStep 1440755 = 2161133) B2161133
theorem B3111949 : Blo 956588 3111949 := bstep (se 3 (by rfl) ⟨583490, by rfl⟩ : syracuseStep 3111949 = 1166981) B1166981
theorem B1440785 : Blo 956588 1440785 := bstep (se 2 (by rfl) ⟨540294, by rfl⟩ : syracuseStep 1440785 = 1080589) B1080589
theorem B1080355 : Blo 956588 1080355 := bstep (se 1 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 1080355 = 1620533) B1620533
theorem B1440803 : Blo 956588 1440803 := bstep (se 1 (by rfl) ⟨1080602, by rfl⟩ : syracuseStep 1440803 = 2161205) B2161205
theorem B1440833 : Blo 956588 1440833 := bstep (se 2 (by rfl) ⟨540312, by rfl⟩ : syracuseStep 1440833 = 1080625) B1080625
theorem B1440851 : Blo 956588 1440851 := bstep (se 1 (by rfl) ⟨1080638, by rfl⟩ : syracuseStep 1440851 = 2161277) B2161277
theorem B1440881 : Blo 956588 1440881 := bstep (se 2 (by rfl) ⟨540330, by rfl⟩ : syracuseStep 1440881 = 1080661) B1080661
theorem B1080499 : Blo 956588 1080499 := bstep (se 1 (by rfl) ⟨810374, by rfl⟩ : syracuseStep 1080499 = 1620749) B1620749
theorem B55934165 : Blo 956588 55934165 := bstep (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) B1310957
theorem B18447587 : Blo 956588 18447587 := bstep (se 1 (by rfl) ⟨13835690, by rfl⟩ : syracuseStep 18447587 = 27671381) B27671381
theorem B6552845 : Blo 956588 6552845 := bstep (se 3 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 6552845 = 2457317) B2457317
theorem B1211699 : Blo 956588 1211699 := bstep (se 1 (by rfl) ⟨908774, by rfl⟩ : syracuseStep 1211699 = 1817549) B1817549
theorem B1080643 : Blo 956588 1080643 := bstep (se 1 (by rfl) ⟨810482, by rfl⟩ : syracuseStep 1080643 = 1620965) B1620965
theorem B3276269 : Blo 956588 3276269 := bstep (se 3 (by rfl) ⟨614300, by rfl⟩ : syracuseStep 3276269 = 1228601) B1228601
theorem B3276323 : Blo 956588 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B2424401 : Blo 956588 2424401 := bstep (se 2 (by rfl) ⟨909150, by rfl⟩ : syracuseStep 2424401 = 1818301) B1818301
theorem B2424451 : Blo 956588 2424451 := bstep (se 1 (by rfl) ⟨1818338, by rfl⟩ : syracuseStep 2424451 = 3636677) B3636677
theorem B2424593 : Blo 956588 2424593 := bstep (se 2 (by rfl) ⟨909222, by rfl⟩ : syracuseStep 2424593 = 1818445) B1818445
theorem B3637133 : Blo 956588 3637133 := bstep (se 3 (by rfl) ⟨681962, by rfl⟩ : syracuseStep 3637133 = 1363925) B1363925
theorem B1212403 : Blo 956588 1212403 := bstep (se 1 (by rfl) ⟨909302, by rfl⟩ : syracuseStep 1212403 = 1818605) B1818605
theorem B78676109 : Blo 956588 78676109 := bstep (se 3 (by rfl) ⟨14751770, by rfl⟩ : syracuseStep 78676109 = 29503541) B29503541
theorem B2425049 : Blo 956588 2425049 := bstep (se 2 (by rfl) ⟨909393, by rfl⟩ : syracuseStep 2425049 = 1818787) B1818787
theorem B2916569 : Blo 956588 2916569 := bstep (se 2 (by rfl) ⟨1093713, by rfl⟩ : syracuseStep 2916569 = 2187427) B2187427
theorem B3637649 : Blo 956588 3637649 := bstep (se 2 (by rfl) ⟨1364118, by rfl⟩ : syracuseStep 3637649 = 2728237) B2728237
theorem B1212823 : Blo 956588 1212823 := bstep (se 1 (by rfl) ⟨909617, by rfl⟩ : syracuseStep 1212823 = 1819235) B1819235
theorem B3736343 : Blo 956588 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B3638105 : Blo 956588 3638105 := bstep (se 2 (by rfl) ⟨1364289, by rfl⟩ : syracuseStep 3638105 = 2728579) B2728579
theorem B7373699 : Blo 956588 7373699 := bstep (se 1 (by rfl) ⟨5530274, by rfl⟩ : syracuseStep 7373699 = 11060549) B11060549
theorem B4096919 : Blo 956588 4096919 := bstep (se 1 (by rfl) ⟨3072689, by rfl⟩ : syracuseStep 4096919 = 6145379) B6145379
theorem B3638317 : Blo 956588 3638317 := bstep (se 3 (by rfl) ⟨682184, by rfl⟩ : syracuseStep 3638317 = 1364369) B1364369
theorem B1213643 : Blo 956588 1213643 := bstep (se 1 (by rfl) ⟨910232, by rfl⟩ : syracuseStep 1213643 = 1820465) B1820465
theorem B3638621 : Blo 956588 3638621 := bstep (se 3 (by rfl) ⟨682241, by rfl⟩ : syracuseStep 3638621 = 1364483) B1364483
theorem B2917835 : Blo 956588 2917835 := bstep (se 1 (by rfl) ⟨2188376, by rfl⟩ : syracuseStep 2917835 = 4376753) B4376753
theorem B2426699 : Blo 956588 2426699 := bstep (se 1 (by rfl) ⟨1820024, by rfl⟩ : syracuseStep 2426699 = 3640049) B3640049
theorem B7374685 : Blo 956588 7374685 := bstep (se 3 (by rfl) ⟨1382753, by rfl⟩ : syracuseStep 7374685 = 2765507) B2765507
theorem B1214347 : Blo 956588 1214347 := bstep (se 1 (by rfl) ⟨910760, by rfl⟩ : syracuseStep 1214347 = 1821521) B1821521
theorem B15763531 : Blo 956588 15763531 := bstep (se 1 (by rfl) ⟨11822648, by rfl⟩ : syracuseStep 15763531 = 23645297) B23645297
theorem B1214615 : Blo 956588 1214615 := bstep (se 1 (by rfl) ⟨910961, by rfl⟩ : syracuseStep 1214615 = 1821923) B1821923
theorem B1870067 : Blo 956588 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B5835083 : Blo 956588 5835083 := bstep (se 1 (by rfl) ⟨4376312, by rfl⟩ : syracuseStep 5835083 = 8752625) B8752625
theorem B4852061 : Blo 956588 4852061 := bstep (se 3 (by rfl) ⟨909761, by rfl⟩ : syracuseStep 4852061 = 1819523) B1819523
theorem B1641227 : Blo 956588 1641227 := bstep (se 1 (by rfl) ⟨1230920, by rfl⟩ : syracuseStep 1641227 = 2461841) B2461841
theorem B4098833 : Blo 956588 4098833 := bstep (se 2 (by rfl) ⟨1537062, by rfl⟩ : syracuseStep 4098833 = 3074125) B3074125
theorem B2427671 : Blo 956588 2427671 := bstep (se 1 (by rfl) ⟨1820753, by rfl⟩ : syracuseStep 2427671 = 3641507) B3641507
theorem B1215319 : Blo 956588 1215319 := bstep (se 1 (by rfl) ⟨911489, by rfl⟩ : syracuseStep 1215319 = 1822979) B1822979
theorem B15535309 : Blo 956588 15535309 := bstep (se 3 (by rfl) ⟨2912870, by rfl⟩ : syracuseStep 15535309 = 5825741) B5825741
theorem B2428339 : Blo 956588 2428339 := bstep (se 1 (by rfl) ⟨1821254, by rfl⟩ : syracuseStep 2428339 = 3642509) B3642509
theorem B2428481 : Blo 956588 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B2920025 : Blo 956588 2920025 := bstep (se 2 (by rfl) ⟨1095009, by rfl⟩ : syracuseStep 2920025 = 2190019) B2190019
theorem B4099805 : Blo 956588 4099805 := bstep (se 3 (by rfl) ⟨768713, by rfl⟩ : syracuseStep 4099805 = 1537427) B1537427
theorem B1969921 : Blo 956588 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B5246795 : Blo 956588 5246795 := bstep (se 1 (by rfl) ⟨3935096, by rfl⟩ : syracuseStep 5246795 = 7870193) B7870193
theorem B3641219 : Blo 956588 3641219 := bstep (se 1 (by rfl) ⟨2730914, by rfl⟩ : syracuseStep 3641219 = 5461829) B5461829
theorem B3641233 : Blo 956588 3641233 := bstep (se 2 (by rfl) ⟨1365462, by rfl⟩ : syracuseStep 3641233 = 2730925) B2730925
theorem B49745843 : Blo 956588 49745843 := bstep (se 1 (by rfl) ⟨37309382, by rfl⟩ : syracuseStep 49745843 = 74618765) B74618765
theorem B3641537 : Blo 956588 3641537 := bstep (se 2 (by rfl) ⟨1365576, by rfl⟩ : syracuseStep 3641537 = 2731153) B2731153
theorem B10916045 : Blo 956588 10916045 := bstep (se 3 (by rfl) ⟨2046758, by rfl⟩ : syracuseStep 10916045 = 4093517) B4093517
theorem B12292397 : Blo 956588 12292397 := bstep (se 3 (by rfl) ⟨2304824, by rfl⟩ : syracuseStep 12292397 = 4609649) B4609649
theorem B4854167 : Blo 956588 4854167 := bstep (se 1 (by rfl) ⟨3640625, by rfl⟩ : syracuseStep 4854167 = 7281251) B7281251
theorem B2429747 : Blo 956588 2429747 := bstep (se 1 (by rfl) ⟨1822310, by rfl⟩ : syracuseStep 2429747 = 3644621) B3644621
theorem B3642205 : Blo 956588 3642205 := bstep (se 3 (by rfl) ⟨682913, by rfl⟩ : syracuseStep 3642205 = 1365827) B1365827
theorem B1479563 : Blo 956588 1479563 := bstep (se 1 (by rfl) ⟨1109672, by rfl⟩ : syracuseStep 1479563 = 2219345) B2219345
theorem B7476299 : Blo 956588 7476299 := bstep (se 1 (by rfl) ⟨5607224, by rfl⟩ : syracuseStep 7476299 = 11214449) B11214449
theorem B4101293 : Blo 956588 4101293 := bstep (se 3 (by rfl) ⟨768992, by rfl⟩ : syracuseStep 4101293 = 1537985) B1537985
theorem B7279793 : Blo 956588 7279793 := bstep (se 2 (by rfl) ⟨2729922, by rfl⟩ : syracuseStep 7279793 = 5459845) B5459845
theorem B2430283 : Blo 956588 2430283 := bstep (se 1 (by rfl) ⟨1822712, by rfl⟩ : syracuseStep 2430283 = 3645425) B3645425
theorem B2594227 : Blo 956588 2594227 := bstep (se 1 (by rfl) ⟨1945670, by rfl⟩ : syracuseStep 2594227 = 3891341) B3891341
theorem B2430425 : Blo 956588 2430425 := bstep (se 2 (by rfl) ⟨911409, by rfl⟩ : syracuseStep 2430425 = 1822819) B1822819
theorem B7280279 : Blo 956588 7280279 := bstep (se 1 (by rfl) ⟨5460209, by rfl⟩ : syracuseStep 7280279 = 10920419) B10920419
theorem B33265349 : Blo 956588 33265349 := bstep (se 4 (by rfl) ⟨3118626, by rfl⟩ : syracuseStep 33265349 = 6237253) B6237253
theorem B1021739 : Blo 956588 1021739 := bstep (se 1 (by rfl) ⟨766304, by rfl⟩ : syracuseStep 1021739 = 1532609) B1532609
theorem B2725721 : Blo 956588 2725721 := bstep (se 2 (by rfl) ⟨1022145, by rfl⟩ : syracuseStep 2725721 = 2044291) B2044291
theorem B3643481 : Blo 956588 3643481 := bstep (se 2 (by rfl) ⟨1366305, by rfl⟩ : syracuseStep 3643481 = 2732611) B2732611
theorem B956599 : Blo 956588 956599 := bstep (se 1 (by rfl) ⟨717449, by rfl⟩ : syracuseStep 956599 = 1434899) B1434899
theorem B956619 : Blo 956588 956619 := bstep (se 1 (by rfl) ⟨717464, by rfl⟩ : syracuseStep 956619 = 1434929) B1434929
theorem B956631 : Blo 956588 956631 := bstep (se 1 (by rfl) ⟨717473, by rfl⟩ : syracuseStep 956631 = 1434947) B1434947
theorem B956651 : Blo 956588 956651 := bstep (se 1 (by rfl) ⟨717488, by rfl⟩ : syracuseStep 956651 = 1434977) B1434977
theorem B956663 : Blo 956588 956663 := bstep (se 1 (by rfl) ⟨717497, by rfl⟩ : syracuseStep 956663 = 1434995) B1434995
theorem B956683 : Blo 956588 956683 := bstep (se 1 (by rfl) ⟨717512, by rfl⟩ : syracuseStep 956683 = 1435025) B1435025
theorem B956695 : Blo 956588 956695 := bstep (se 1 (by rfl) ⟨717521, by rfl⟩ : syracuseStep 956695 = 1435043) B1435043
theorem B2431255 : Blo 956588 2431255 := bstep (se 1 (by rfl) ⟨1823441, by rfl⟩ : syracuseStep 2431255 = 3646883) B3646883
theorem B956715 : Blo 956588 956715 := bstep (se 1 (by rfl) ⟨717536, by rfl⟩ : syracuseStep 956715 = 1435073) B1435073
theorem B956727 : Blo 956588 956727 := bstep (se 1 (by rfl) ⟨717545, by rfl⟩ : syracuseStep 956727 = 1435091) B1435091
theorem B956747 : Blo 956588 956747 := bstep (se 1 (by rfl) ⟨717560, by rfl⟩ : syracuseStep 956747 = 1435121) B1435121
theorem B956759 : Blo 956588 956759 := bstep (se 1 (by rfl) ⟨717569, by rfl⟩ : syracuseStep 956759 = 1435139) B1435139
theorem B956779 : Blo 956588 956779 := bstep (se 1 (by rfl) ⟨717584, by rfl⟩ : syracuseStep 956779 = 1435169) B1435169
theorem B956791 : Blo 956588 956791 := bstep (se 1 (by rfl) ⟨717593, by rfl⟩ : syracuseStep 956791 = 1435187) B1435187
theorem B956811 : Blo 956588 956811 := bstep (se 1 (by rfl) ⟨717608, by rfl⟩ : syracuseStep 956811 = 1435217) B1435217
theorem B956823 : Blo 956588 956823 := bstep (se 1 (by rfl) ⟨717617, by rfl⟩ : syracuseStep 956823 = 1435235) B1435235
theorem B956843 : Blo 956588 956843 := bstep (se 1 (by rfl) ⟨717632, by rfl⟩ : syracuseStep 956843 = 1435265) B1435265
theorem B956855 : Blo 956588 956855 := bstep (se 1 (by rfl) ⟨717641, by rfl⟩ : syracuseStep 956855 = 1435283) B1435283
theorem B956875 : Blo 956588 956875 := bstep (se 1 (by rfl) ⟨717656, by rfl⟩ : syracuseStep 956875 = 1435313) B1435313
theorem B956887 : Blo 956588 956887 := bstep (se 1 (by rfl) ⟨717665, by rfl⟩ : syracuseStep 956887 = 1435331) B1435331
theorem B956907 : Blo 956588 956907 := bstep (se 1 (by rfl) ⟨717680, by rfl⟩ : syracuseStep 956907 = 1435361) B1435361
theorem B956919 : Blo 956588 956919 := bstep (se 1 (by rfl) ⟨717689, by rfl⟩ : syracuseStep 956919 = 1435379) B1435379
theorem B956939 : Blo 956588 956939 := bstep (se 1 (by rfl) ⟨717704, by rfl⟩ : syracuseStep 956939 = 1435409) B1435409
theorem B956951 : Blo 956588 956951 := bstep (se 1 (by rfl) ⟨717713, by rfl⟩ : syracuseStep 956951 = 1435427) B1435427
theorem B956971 : Blo 956588 956971 := bstep (se 1 (by rfl) ⟨717728, by rfl⟩ : syracuseStep 956971 = 1435457) B1435457
theorem B956983 : Blo 956588 956983 := bstep (se 1 (by rfl) ⟨717737, by rfl⟩ : syracuseStep 956983 = 1435475) B1435475
theorem B957003 : Blo 956588 957003 := bstep (se 1 (by rfl) ⟨717752, by rfl⟩ : syracuseStep 957003 = 1435505) B1435505
theorem B957015 : Blo 956588 957015 := bstep (se 1 (by rfl) ⟨717761, by rfl⟩ : syracuseStep 957015 = 1435523) B1435523
theorem B957035 : Blo 956588 957035 := bstep (se 1 (by rfl) ⟨717776, by rfl⟩ : syracuseStep 957035 = 1435553) B1435553
theorem B1841779 : Blo 956588 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B957047 : Blo 956588 957047 := bstep (se 1 (by rfl) ⟨717785, by rfl⟩ : syracuseStep 957047 = 1435571) B1435571
theorem B957067 : Blo 956588 957067 := bstep (se 1 (by rfl) ⟨717800, by rfl⟩ : syracuseStep 957067 = 1435601) B1435601
theorem B957079 : Blo 956588 957079 := bstep (se 1 (by rfl) ⟨717809, by rfl⟩ : syracuseStep 957079 = 1435619) B1435619
theorem B2726551 : Blo 956588 2726551 := bstep (se 1 (by rfl) ⟨2044913, by rfl⟩ : syracuseStep 2726551 = 4089827) B4089827
theorem B957099 : Blo 956588 957099 := bstep (se 1 (by rfl) ⟨717824, by rfl⟩ : syracuseStep 957099 = 1435649) B1435649
theorem B957111 : Blo 956588 957111 := bstep (se 1 (by rfl) ⟨717833, by rfl⟩ : syracuseStep 957111 = 1435667) B1435667
theorem B957131 : Blo 956588 957131 := bstep (se 1 (by rfl) ⟨717848, by rfl⟩ : syracuseStep 957131 = 1435697) B1435697
theorem B957143 : Blo 956588 957143 := bstep (se 1 (by rfl) ⟨717857, by rfl⟩ : syracuseStep 957143 = 1435715) B1435715
theorem B957163 : Blo 956588 957163 := bstep (se 1 (by rfl) ⟨717872, by rfl⟩ : syracuseStep 957163 = 1435745) B1435745
theorem B957175 : Blo 956588 957175 := bstep (se 1 (by rfl) ⟨717881, by rfl⟩ : syracuseStep 957175 = 1435763) B1435763
theorem B957195 : Blo 956588 957195 := bstep (se 1 (by rfl) ⟨717896, by rfl⟩ : syracuseStep 957195 = 1435793) B1435793
theorem B957207 : Blo 956588 957207 := bstep (se 1 (by rfl) ⟨717905, by rfl⟩ : syracuseStep 957207 = 1435811) B1435811
theorem B957227 : Blo 956588 957227 := bstep (se 1 (by rfl) ⟨717920, by rfl⟩ : syracuseStep 957227 = 1435841) B1435841
theorem B957239 : Blo 956588 957239 := bstep (se 1 (by rfl) ⟨717929, by rfl⟩ : syracuseStep 957239 = 1435859) B1435859
theorem B957259 : Blo 956588 957259 := bstep (se 1 (by rfl) ⟨717944, by rfl⟩ : syracuseStep 957259 = 1435889) B1435889
theorem B957271 : Blo 956588 957271 := bstep (se 1 (by rfl) ⟨717953, by rfl⟩ : syracuseStep 957271 = 1435907) B1435907
theorem B957291 : Blo 956588 957291 := bstep (se 1 (by rfl) ⟨717968, by rfl⟩ : syracuseStep 957291 = 1435937) B1435937
theorem B957303 : Blo 956588 957303 := bstep (se 1 (by rfl) ⟨717977, by rfl⟩ : syracuseStep 957303 = 1435955) B1435955
theorem B957323 : Blo 956588 957323 := bstep (se 1 (by rfl) ⟨717992, by rfl⟩ : syracuseStep 957323 = 1435985) B1435985
theorem B957335 : Blo 956588 957335 := bstep (se 1 (by rfl) ⟨718001, by rfl⟩ : syracuseStep 957335 = 1436003) B1436003
theorem B957355 : Blo 956588 957355 := bstep (se 1 (by rfl) ⟨718016, by rfl⟩ : syracuseStep 957355 = 1436033) B1436033
theorem B957367 : Blo 956588 957367 := bstep (se 1 (by rfl) ⟨718025, by rfl⟩ : syracuseStep 957367 = 1436051) B1436051
theorem B957387 : Blo 956588 957387 := bstep (se 1 (by rfl) ⟨718040, by rfl⟩ : syracuseStep 957387 = 1436081) B1436081
theorem B957399 : Blo 956588 957399 := bstep (se 1 (by rfl) ⟨718049, by rfl⟩ : syracuseStep 957399 = 1436099) B1436099
theorem B957419 : Blo 956588 957419 := bstep (se 1 (by rfl) ⟨718064, by rfl⟩ : syracuseStep 957419 = 1436129) B1436129
theorem B957431 : Blo 956588 957431 := bstep (se 1 (by rfl) ⟨718073, by rfl⟩ : syracuseStep 957431 = 1436147) B1436147
theorem B957451 : Blo 956588 957451 := bstep (se 1 (by rfl) ⟨718088, by rfl⟩ : syracuseStep 957451 = 1436177) B1436177
theorem B957463 : Blo 956588 957463 := bstep (se 1 (by rfl) ⟨718097, by rfl⟩ : syracuseStep 957463 = 1436195) B1436195
theorem B957483 : Blo 956588 957483 := bstep (se 1 (by rfl) ⟨718112, by rfl⟩ : syracuseStep 957483 = 1436225) B1436225
theorem B957495 : Blo 956588 957495 := bstep (se 1 (by rfl) ⟨718121, by rfl⟩ : syracuseStep 957495 = 1436243) B1436243
theorem B957515 : Blo 956588 957515 := bstep (se 1 (by rfl) ⟨718136, by rfl⟩ : syracuseStep 957515 = 1436273) B1436273
theorem B957527 : Blo 956588 957527 := bstep (se 1 (by rfl) ⟨718145, by rfl⟩ : syracuseStep 957527 = 1436291) B1436291
theorem B1973335 : Blo 956588 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B957547 : Blo 956588 957547 := bstep (se 1 (by rfl) ⟨718160, by rfl⟩ : syracuseStep 957547 = 1436321) B1436321
theorem B957559 : Blo 956588 957559 := bstep (se 1 (by rfl) ⟨718169, by rfl⟩ : syracuseStep 957559 = 1436339) B1436339
theorem B957579 : Blo 956588 957579 := bstep (se 1 (by rfl) ⟨718184, by rfl⟩ : syracuseStep 957579 = 1436369) B1436369
theorem B957591 : Blo 956588 957591 := bstep (se 1 (by rfl) ⟨718193, by rfl⟩ : syracuseStep 957591 = 1436387) B1436387
theorem B957611 : Blo 956588 957611 := bstep (se 1 (by rfl) ⟨718208, by rfl⟩ : syracuseStep 957611 = 1436417) B1436417
theorem B957623 : Blo 956588 957623 := bstep (se 1 (by rfl) ⟨718217, by rfl⟩ : syracuseStep 957623 = 1436435) B1436435
theorem B957643 : Blo 956588 957643 := bstep (se 1 (by rfl) ⟨718232, by rfl⟩ : syracuseStep 957643 = 1436465) B1436465
theorem B957655 : Blo 956588 957655 := bstep (se 1 (by rfl) ⟨718241, by rfl⟩ : syracuseStep 957655 = 1436483) B1436483
theorem B957675 : Blo 956588 957675 := bstep (se 1 (by rfl) ⟨718256, by rfl⟩ : syracuseStep 957675 = 1436513) B1436513
theorem B957687 : Blo 956588 957687 := bstep (se 1 (by rfl) ⟨718265, by rfl⟩ : syracuseStep 957687 = 1436531) B1436531
theorem B957707 : Blo 956588 957707 := bstep (se 1 (by rfl) ⟨718280, by rfl⟩ : syracuseStep 957707 = 1436561) B1436561
theorem B957719 : Blo 956588 957719 := bstep (se 1 (by rfl) ⟨718289, by rfl⟩ : syracuseStep 957719 = 1436579) B1436579
theorem B957739 : Blo 956588 957739 := bstep (se 1 (by rfl) ⟨718304, by rfl⟩ : syracuseStep 957739 = 1436609) B1436609
theorem B957751 : Blo 956588 957751 := bstep (se 1 (by rfl) ⟨718313, by rfl⟩ : syracuseStep 957751 = 1436627) B1436627
theorem B957771 : Blo 956588 957771 := bstep (se 1 (by rfl) ⟨718328, by rfl⟩ : syracuseStep 957771 = 1436657) B1436657
theorem B957783 : Blo 956588 957783 := bstep (se 1 (by rfl) ⟨718337, by rfl⟩ : syracuseStep 957783 = 1436675) B1436675
theorem B957803 : Blo 956588 957803 := bstep (se 1 (by rfl) ⟨718352, by rfl⟩ : syracuseStep 957803 = 1436705) B1436705
theorem B957815 : Blo 956588 957815 := bstep (se 1 (by rfl) ⟨718361, by rfl⟩ : syracuseStep 957815 = 1436723) B1436723
theorem B957835 : Blo 956588 957835 := bstep (se 1 (by rfl) ⟨718376, by rfl⟩ : syracuseStep 957835 = 1436753) B1436753
theorem B957847 : Blo 956588 957847 := bstep (se 1 (by rfl) ⟨718385, by rfl⟩ : syracuseStep 957847 = 1436771) B1436771
theorem B957867 : Blo 956588 957867 := bstep (se 1 (by rfl) ⟨718400, by rfl⟩ : syracuseStep 957867 = 1436801) B1436801
theorem B957879 : Blo 956588 957879 := bstep (se 1 (by rfl) ⟨718409, by rfl⟩ : syracuseStep 957879 = 1436819) B1436819
theorem B2727371 : Blo 956588 2727371 := bstep (se 1 (by rfl) ⟨2045528, by rfl⟩ : syracuseStep 2727371 = 4091057) B4091057
theorem B957899 : Blo 956588 957899 := bstep (se 1 (by rfl) ⟨718424, by rfl⟩ : syracuseStep 957899 = 1436849) B1436849
theorem B957911 : Blo 956588 957911 := bstep (se 1 (by rfl) ⟨718433, by rfl⟩ : syracuseStep 957911 = 1436867) B1436867
theorem B957931 : Blo 956588 957931 := bstep (se 1 (by rfl) ⟨718448, by rfl⟩ : syracuseStep 957931 = 1436897) B1436897
theorem B957943 : Blo 956588 957943 := bstep (se 1 (by rfl) ⟨718457, by rfl⟩ : syracuseStep 957943 = 1436915) B1436915
theorem B957963 : Blo 956588 957963 := bstep (se 1 (by rfl) ⟨718472, by rfl⟩ : syracuseStep 957963 = 1436945) B1436945
theorem B1023499 : Blo 956588 1023499 := bstep (se 1 (by rfl) ⟨767624, by rfl⟩ : syracuseStep 1023499 = 1535249) B1535249
theorem B957975 : Blo 956588 957975 := bstep (se 1 (by rfl) ⟨718481, by rfl⟩ : syracuseStep 957975 = 1436963) B1436963
theorem B957995 : Blo 956588 957995 := bstep (se 1 (by rfl) ⟨718496, by rfl⟩ : syracuseStep 957995 = 1436993) B1436993
theorem B958007 : Blo 956588 958007 := bstep (se 1 (by rfl) ⟨718505, by rfl⟩ : syracuseStep 958007 = 1437011) B1437011
theorem B958027 : Blo 956588 958027 := bstep (se 1 (by rfl) ⟨718520, by rfl⟩ : syracuseStep 958027 = 1437041) B1437041
theorem B958039 : Blo 956588 958039 := bstep (se 1 (by rfl) ⟨718529, by rfl⟩ : syracuseStep 958039 = 1437059) B1437059
theorem B958059 : Blo 956588 958059 := bstep (se 1 (by rfl) ⟨718544, by rfl⟩ : syracuseStep 958059 = 1437089) B1437089
theorem B958071 : Blo 956588 958071 := bstep (se 1 (by rfl) ⟨718553, by rfl⟩ : syracuseStep 958071 = 1437107) B1437107
theorem B958091 : Blo 956588 958091 := bstep (se 1 (by rfl) ⟨718568, by rfl⟩ : syracuseStep 958091 = 1437137) B1437137
theorem B958103 : Blo 956588 958103 := bstep (se 1 (by rfl) ⟨718577, by rfl⟩ : syracuseStep 958103 = 1437155) B1437155
theorem B958123 : Blo 956588 958123 := bstep (se 1 (by rfl) ⟨718592, by rfl⟩ : syracuseStep 958123 = 1437185) B1437185
theorem B3645107 : Blo 956588 3645107 := bstep (se 1 (by rfl) ⟨2733830, by rfl⟩ : syracuseStep 3645107 = 5467661) B5467661
theorem B958135 : Blo 956588 958135 := bstep (se 1 (by rfl) ⟨718601, by rfl⟩ : syracuseStep 958135 = 1437203) B1437203
theorem B3645121 : Blo 956588 3645121 := bstep (se 2 (by rfl) ⟨1366920, by rfl⟩ : syracuseStep 3645121 = 2733841) B2733841
theorem B2301643 : Blo 956588 2301643 := bstep (se 1 (by rfl) ⟨1726232, by rfl⟩ : syracuseStep 2301643 = 3452465) B3452465
theorem B958155 : Blo 956588 958155 := bstep (se 1 (by rfl) ⟨718616, by rfl⟩ : syracuseStep 958155 = 1437233) B1437233
theorem B958167 : Blo 956588 958167 := bstep (se 1 (by rfl) ⟨718625, by rfl⟩ : syracuseStep 958167 = 1437251) B1437251
theorem B958187 : Blo 956588 958187 := bstep (se 1 (by rfl) ⟨718640, by rfl⟩ : syracuseStep 958187 = 1437281) B1437281
theorem B958199 : Blo 956588 958199 := bstep (se 1 (by rfl) ⟨718649, by rfl⟩ : syracuseStep 958199 = 1437299) B1437299
theorem B958219 : Blo 956588 958219 := bstep (se 1 (by rfl) ⟨718664, by rfl⟩ : syracuseStep 958219 = 1437329) B1437329
theorem B8199953 : Blo 956588 8199953 := bstep (se 2 (by rfl) ⟨3074982, by rfl⟩ : syracuseStep 8199953 = 6149965) B6149965
theorem B958231 : Blo 956588 958231 := bstep (se 1 (by rfl) ⟨718673, by rfl⟩ : syracuseStep 958231 = 1437347) B1437347
theorem B958251 : Blo 956588 958251 := bstep (se 1 (by rfl) ⟨718688, by rfl⟩ : syracuseStep 958251 = 1437377) B1437377
theorem B958263 : Blo 956588 958263 := bstep (se 1 (by rfl) ⟨718697, by rfl⟩ : syracuseStep 958263 = 1437395) B1437395
theorem B958283 : Blo 956588 958283 := bstep (se 1 (by rfl) ⟨718712, by rfl⟩ : syracuseStep 958283 = 1437425) B1437425
theorem B958295 : Blo 956588 958295 := bstep (se 1 (by rfl) ⟨718721, by rfl⟩ : syracuseStep 958295 = 1437443) B1437443
theorem B958315 : Blo 956588 958315 := bstep (se 1 (by rfl) ⟨718736, by rfl⟩ : syracuseStep 958315 = 1437473) B1437473
theorem B958327 : Blo 956588 958327 := bstep (se 1 (by rfl) ⟨718745, by rfl⟩ : syracuseStep 958327 = 1437491) B1437491
theorem B4857731 : Blo 956588 4857731 := bstep (se 1 (by rfl) ⟨3643298, by rfl⟩ : syracuseStep 4857731 = 7286597) B7286597
theorem B958347 : Blo 956588 958347 := bstep (se 1 (by rfl) ⟨718760, by rfl⟩ : syracuseStep 958347 = 1437521) B1437521
theorem B958359 : Blo 956588 958359 := bstep (se 1 (by rfl) ⟨718769, by rfl⟩ : syracuseStep 958359 = 1437539) B1437539
theorem B958379 : Blo 956588 958379 := bstep (se 1 (by rfl) ⟨718784, by rfl⟩ : syracuseStep 958379 = 1437569) B1437569
theorem B958391 : Blo 956588 958391 := bstep (se 1 (by rfl) ⟨718793, by rfl⟩ : syracuseStep 958391 = 1437587) B1437587
theorem B958411 : Blo 956588 958411 := bstep (se 1 (by rfl) ⟨718808, by rfl⟩ : syracuseStep 958411 = 1437617) B1437617
theorem B958423 : Blo 956588 958423 := bstep (se 1 (by rfl) ⟨718817, by rfl⟩ : syracuseStep 958423 = 1437635) B1437635
theorem B958443 : Blo 956588 958443 := bstep (se 1 (by rfl) ⟨718832, by rfl⟩ : syracuseStep 958443 = 1437665) B1437665
theorem B958455 : Blo 956588 958455 := bstep (se 1 (by rfl) ⟨718841, by rfl⟩ : syracuseStep 958455 = 1437683) B1437683
theorem B958475 : Blo 956588 958475 := bstep (se 1 (by rfl) ⟨718856, by rfl⟩ : syracuseStep 958475 = 1437713) B1437713
theorem B958487 : Blo 956588 958487 := bstep (se 1 (by rfl) ⟨718865, by rfl⟩ : syracuseStep 958487 = 1437731) B1437731
theorem B958507 : Blo 956588 958507 := bstep (se 1 (by rfl) ⟨718880, by rfl⟩ : syracuseStep 958507 = 1437761) B1437761
theorem B958519 : Blo 956588 958519 := bstep (se 1 (by rfl) ⟨718889, by rfl⟩ : syracuseStep 958519 = 1437779) B1437779
theorem B958539 : Blo 956588 958539 := bstep (se 1 (by rfl) ⟨718904, by rfl⟩ : syracuseStep 958539 = 1437809) B1437809
theorem B958551 : Blo 956588 958551 := bstep (se 1 (by rfl) ⟨718913, by rfl⟩ : syracuseStep 958551 = 1437827) B1437827
theorem B958571 : Blo 956588 958571 := bstep (se 1 (by rfl) ⟨718928, by rfl⟩ : syracuseStep 958571 = 1437857) B1437857
theorem B958583 : Blo 956588 958583 := bstep (se 1 (by rfl) ⟨718937, by rfl⟩ : syracuseStep 958583 = 1437875) B1437875
theorem B958603 : Blo 956588 958603 := bstep (se 1 (by rfl) ⟨718952, by rfl⟩ : syracuseStep 958603 = 1437905) B1437905
theorem B958615 : Blo 956588 958615 := bstep (se 1 (by rfl) ⟨718961, by rfl⟩ : syracuseStep 958615 = 1437923) B1437923
theorem B958635 : Blo 956588 958635 := bstep (se 1 (by rfl) ⟨718976, by rfl⟩ : syracuseStep 958635 = 1437953) B1437953
theorem B958647 : Blo 956588 958647 := bstep (se 1 (by rfl) ⟨718985, by rfl⟩ : syracuseStep 958647 = 1437971) B1437971
theorem B958667 : Blo 956588 958667 := bstep (se 1 (by rfl) ⟨719000, by rfl⟩ : syracuseStep 958667 = 1438001) B1438001
theorem B958679 : Blo 956588 958679 := bstep (se 1 (by rfl) ⟨719009, by rfl⟩ : syracuseStep 958679 = 1438019) B1438019
theorem B958699 : Blo 956588 958699 := bstep (se 1 (by rfl) ⟨719024, by rfl⟩ : syracuseStep 958699 = 1438049) B1438049
theorem B958711 : Blo 956588 958711 := bstep (se 1 (by rfl) ⟨719033, by rfl⟩ : syracuseStep 958711 = 1438067) B1438067
theorem B958731 : Blo 956588 958731 := bstep (se 1 (by rfl) ⟨719048, by rfl⟩ : syracuseStep 958731 = 1438097) B1438097
theorem B958743 : Blo 956588 958743 := bstep (se 1 (by rfl) ⟨719057, by rfl⟩ : syracuseStep 958743 = 1438115) B1438115
theorem B958763 : Blo 956588 958763 := bstep (se 1 (by rfl) ⟨719072, by rfl⟩ : syracuseStep 958763 = 1438145) B1438145
theorem B958775 : Blo 956588 958775 := bstep (se 1 (by rfl) ⟨719081, by rfl⟩ : syracuseStep 958775 = 1438163) B1438163
theorem B958795 : Blo 956588 958795 := bstep (se 1 (by rfl) ⟨719096, by rfl⟩ : syracuseStep 958795 = 1438193) B1438193
theorem B958807 : Blo 956588 958807 := bstep (se 1 (by rfl) ⟨719105, by rfl⟩ : syracuseStep 958807 = 1438211) B1438211
theorem B958827 : Blo 956588 958827 := bstep (se 1 (by rfl) ⟨719120, by rfl⟩ : syracuseStep 958827 = 1438241) B1438241
theorem B958839 : Blo 956588 958839 := bstep (se 1 (by rfl) ⟨719129, by rfl⟩ : syracuseStep 958839 = 1438259) B1438259
theorem B958859 : Blo 956588 958859 := bstep (se 1 (by rfl) ⟨719144, by rfl⟩ : syracuseStep 958859 = 1438289) B1438289
theorem B958871 : Blo 956588 958871 := bstep (se 1 (by rfl) ⟨719153, by rfl⟩ : syracuseStep 958871 = 1438307) B1438307
theorem B958891 : Blo 956588 958891 := bstep (se 1 (by rfl) ⟨719168, by rfl⟩ : syracuseStep 958891 = 1438337) B1438337
theorem B958903 : Blo 956588 958903 := bstep (se 1 (by rfl) ⟨719177, by rfl⟩ : syracuseStep 958903 = 1438355) B1438355
theorem B958923 : Blo 956588 958923 := bstep (se 1 (by rfl) ⟨719192, by rfl⟩ : syracuseStep 958923 = 1438385) B1438385
theorem B958935 : Blo 956588 958935 := bstep (se 1 (by rfl) ⟨719201, by rfl⟩ : syracuseStep 958935 = 1438403) B1438403
theorem B958955 : Blo 956588 958955 := bstep (se 1 (by rfl) ⟨719216, by rfl⟩ : syracuseStep 958955 = 1438433) B1438433
theorem B958967 : Blo 956588 958967 := bstep (se 1 (by rfl) ⟨719225, by rfl⟩ : syracuseStep 958967 = 1438451) B1438451
theorem B958987 : Blo 956588 958987 := bstep (se 1 (by rfl) ⟨719240, by rfl⟩ : syracuseStep 958987 = 1438481) B1438481
theorem B10363409 : Blo 956588 10363409 := bstep (se 2 (by rfl) ⟨3886278, by rfl⟩ : syracuseStep 10363409 = 7772557) B7772557
theorem B958999 : Blo 956588 958999 := bstep (se 1 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 958999 = 1438499) B1438499
theorem B959019 : Blo 956588 959019 := bstep (se 1 (by rfl) ⟨719264, by rfl⟩ : syracuseStep 959019 = 1438529) B1438529
theorem B3449395 : Blo 956588 3449395 := bstep (se 1 (by rfl) ⟨2587046, by rfl⟩ : syracuseStep 3449395 = 5174093) B5174093
theorem B959031 : Blo 956588 959031 := bstep (se 1 (by rfl) ⟨719273, by rfl⟩ : syracuseStep 959031 = 1438547) B1438547
theorem B959051 : Blo 956588 959051 := bstep (se 1 (by rfl) ⟨719288, by rfl⟩ : syracuseStep 959051 = 1438577) B1438577
theorem B959063 : Blo 956588 959063 := bstep (se 1 (by rfl) ⟨719297, by rfl⟩ : syracuseStep 959063 = 1438595) B1438595
theorem B959083 : Blo 956588 959083 := bstep (se 1 (by rfl) ⟨719312, by rfl⟩ : syracuseStep 959083 = 1438625) B1438625
theorem B959095 : Blo 956588 959095 := bstep (se 1 (by rfl) ⟨719321, by rfl⟩ : syracuseStep 959095 = 1438643) B1438643
theorem B959115 : Blo 956588 959115 := bstep (se 1 (by rfl) ⟨719336, by rfl⟩ : syracuseStep 959115 = 1438673) B1438673
theorem B959127 : Blo 956588 959127 := bstep (se 1 (by rfl) ⟨719345, by rfl⟩ : syracuseStep 959127 = 1438691) B1438691
theorem B959147 : Blo 956588 959147 := bstep (se 1 (by rfl) ⟨719360, by rfl⟩ : syracuseStep 959147 = 1438721) B1438721
theorem B959159 : Blo 956588 959159 := bstep (se 1 (by rfl) ⟨719369, by rfl⟩ : syracuseStep 959159 = 1438739) B1438739
theorem B2990785 : Blo 956588 2990785 := bstep (se 2 (by rfl) ⟨1121544, by rfl⟩ : syracuseStep 2990785 = 2243089) B2243089
theorem B1614539 : Blo 956588 1614539 := bstep (se 1 (by rfl) ⟨1210904, by rfl⟩ : syracuseStep 1614539 = 2421809) B2421809
theorem B959179 : Blo 956588 959179 := bstep (se 1 (by rfl) ⟨719384, by rfl⟩ : syracuseStep 959179 = 1438769) B1438769
theorem B959191 : Blo 956588 959191 := bstep (se 1 (by rfl) ⟨719393, by rfl⟩ : syracuseStep 959191 = 1438787) B1438787
theorem B2302681 : Blo 956588 2302681 := bstep (se 2 (by rfl) ⟨863505, by rfl⟩ : syracuseStep 2302681 = 1727011) B1727011
theorem B959211 : Blo 956588 959211 := bstep (se 1 (by rfl) ⟨719408, by rfl⟩ : syracuseStep 959211 = 1438817) B1438817
theorem B959223 : Blo 956588 959223 := bstep (se 1 (by rfl) ⟨719417, by rfl⟩ : syracuseStep 959223 = 1438835) B1438835
theorem B959243 : Blo 956588 959243 := bstep (se 1 (by rfl) ⟨719432, by rfl⟩ : syracuseStep 959243 = 1438865) B1438865
theorem B959255 : Blo 956588 959255 := bstep (se 1 (by rfl) ⟨719441, by rfl⟩ : syracuseStep 959255 = 1438883) B1438883
theorem B959275 : Blo 956588 959275 := bstep (se 1 (by rfl) ⟨719456, by rfl⟩ : syracuseStep 959275 = 1438913) B1438913
theorem B959287 : Blo 956588 959287 := bstep (se 1 (by rfl) ⟨719465, by rfl⟩ : syracuseStep 959287 = 1438931) B1438931
theorem B1614667 : Blo 956588 1614667 := bstep (se 1 (by rfl) ⟨1211000, by rfl⟩ : syracuseStep 1614667 = 2422001) B2422001
theorem B959307 : Blo 956588 959307 := bstep (se 1 (by rfl) ⟨719480, by rfl⟩ : syracuseStep 959307 = 1438961) B1438961
theorem B959319 : Blo 956588 959319 := bstep (se 1 (by rfl) ⟨719489, by rfl⟩ : syracuseStep 959319 = 1438979) B1438979
theorem B959339 : Blo 956588 959339 := bstep (se 1 (by rfl) ⟨719504, by rfl⟩ : syracuseStep 959339 = 1439009) B1439009
theorem B959351 : Blo 956588 959351 := bstep (se 1 (by rfl) ⟨719513, by rfl⟩ : syracuseStep 959351 = 1439027) B1439027
theorem B959371 : Blo 956588 959371 := bstep (se 1 (by rfl) ⟨719528, by rfl⟩ : syracuseStep 959371 = 1439057) B1439057
theorem B959383 : Blo 956588 959383 := bstep (se 1 (by rfl) ⟨719537, by rfl⟩ : syracuseStep 959383 = 1439075) B1439075
theorem B959403 : Blo 956588 959403 := bstep (se 1 (by rfl) ⟨719552, by rfl⟩ : syracuseStep 959403 = 1439105) B1439105
theorem B2761651 : Blo 956588 2761651 := bstep (se 1 (by rfl) ⟨2071238, by rfl⟩ : syracuseStep 2761651 = 4142477) B4142477
theorem B959415 : Blo 956588 959415 := bstep (se 1 (by rfl) ⟨719561, by rfl⟩ : syracuseStep 959415 = 1439123) B1439123
theorem B959435 : Blo 956588 959435 := bstep (se 1 (by rfl) ⟨719576, by rfl⟩ : syracuseStep 959435 = 1439153) B1439153
theorem B959447 : Blo 956588 959447 := bstep (se 1 (by rfl) ⟨719585, by rfl⟩ : syracuseStep 959447 = 1439171) B1439171
theorem B1614809 : Blo 956588 1614809 := bstep (se 2 (by rfl) ⟨605553, by rfl⟩ : syracuseStep 1614809 = 1211107) B1211107
theorem B959467 : Blo 956588 959467 := bstep (se 1 (by rfl) ⟨719600, by rfl⟩ : syracuseStep 959467 = 1439201) B1439201
theorem B959479 : Blo 956588 959479 := bstep (se 1 (by rfl) ⟨719609, by rfl⟩ : syracuseStep 959479 = 1439219) B1439219
theorem B959499 : Blo 956588 959499 := bstep (se 1 (by rfl) ⟨719624, by rfl⟩ : syracuseStep 959499 = 1439249) B1439249
theorem B959511 : Blo 956588 959511 := bstep (se 1 (by rfl) ⟨719633, by rfl⟩ : syracuseStep 959511 = 1439267) B1439267
theorem B959531 : Blo 956588 959531 := bstep (se 1 (by rfl) ⟨719648, by rfl⟩ : syracuseStep 959531 = 1439297) B1439297
theorem B959543 : Blo 956588 959543 := bstep (se 1 (by rfl) ⟨719657, by rfl⟩ : syracuseStep 959543 = 1439315) B1439315
theorem B959563 : Blo 956588 959563 := bstep (se 1 (by rfl) ⟨719672, by rfl⟩ : syracuseStep 959563 = 1439345) B1439345
theorem B959575 : Blo 956588 959575 := bstep (se 1 (by rfl) ⟨719681, by rfl⟩ : syracuseStep 959575 = 1439363) B1439363
theorem B1614937 : Blo 956588 1614937 := bstep (se 2 (by rfl) ⟨605601, by rfl⟩ : syracuseStep 1614937 = 1211203) B1211203
theorem B959595 : Blo 956588 959595 := bstep (se 1 (by rfl) ⟨719696, by rfl⟩ : syracuseStep 959595 = 1439393) B1439393
theorem B1025131 : Blo 956588 1025131 := bstep (se 1 (by rfl) ⟨768848, by rfl⟩ : syracuseStep 1025131 = 1537697) B1537697
theorem B959607 : Blo 956588 959607 := bstep (se 1 (by rfl) ⟨719705, by rfl⟩ : syracuseStep 959607 = 1439411) B1439411
theorem B959627 : Blo 956588 959627 := bstep (se 1 (by rfl) ⟨719720, by rfl⟩ : syracuseStep 959627 = 1439441) B1439441
theorem B959639 : Blo 956588 959639 := bstep (se 1 (by rfl) ⟨719729, by rfl⟩ : syracuseStep 959639 = 1439459) B1439459
theorem B959659 : Blo 956588 959659 := bstep (se 1 (by rfl) ⟨719744, by rfl⟩ : syracuseStep 959659 = 1439489) B1439489
theorem B959671 : Blo 956588 959671 := bstep (se 1 (by rfl) ⟨719753, by rfl⟩ : syracuseStep 959671 = 1439507) B1439507
theorem B959691 : Blo 956588 959691 := bstep (se 1 (by rfl) ⟨719768, by rfl⟩ : syracuseStep 959691 = 1439537) B1439537
theorem B959703 : Blo 956588 959703 := bstep (se 1 (by rfl) ⟨719777, by rfl⟩ : syracuseStep 959703 = 1439555) B1439555
theorem B959723 : Blo 956588 959723 := bstep (se 1 (by rfl) ⟨719792, by rfl⟩ : syracuseStep 959723 = 1439585) B1439585
theorem B959735 : Blo 956588 959735 := bstep (se 1 (by rfl) ⟨719801, by rfl⟩ : syracuseStep 959735 = 1439603) B1439603
theorem B959755 : Blo 956588 959755 := bstep (se 1 (by rfl) ⟨719816, by rfl⟩ : syracuseStep 959755 = 1439633) B1439633
theorem B959767 : Blo 956588 959767 := bstep (se 1 (by rfl) ⟨719825, by rfl⟩ : syracuseStep 959767 = 1439651) B1439651
theorem B959787 : Blo 956588 959787 := bstep (se 1 (by rfl) ⟨719840, by rfl⟩ : syracuseStep 959787 = 1439681) B1439681
theorem B959799 : Blo 956588 959799 := bstep (se 1 (by rfl) ⟨719849, by rfl⟩ : syracuseStep 959799 = 1439699) B1439699
theorem B8299841 : Blo 956588 8299841 := bstep (se 2 (by rfl) ⟨3112440, by rfl⟩ : syracuseStep 8299841 = 6224881) B6224881
theorem B959819 : Blo 956588 959819 := bstep (se 1 (by rfl) ⟨719864, by rfl⟩ : syracuseStep 959819 = 1439729) B1439729
theorem B959831 : Blo 956588 959831 := bstep (se 1 (by rfl) ⟨719873, by rfl⟩ : syracuseStep 959831 = 1439747) B1439747
theorem B959851 : Blo 956588 959851 := bstep (se 1 (by rfl) ⟨719888, by rfl⟩ : syracuseStep 959851 = 1439777) B1439777
theorem B959863 : Blo 956588 959863 := bstep (se 1 (by rfl) ⟨719897, by rfl⟩ : syracuseStep 959863 = 1439795) B1439795
theorem B959883 : Blo 956588 959883 := bstep (se 1 (by rfl) ⟨719912, by rfl⟩ : syracuseStep 959883 = 1439825) B1439825
theorem B959895 : Blo 956588 959895 := bstep (se 1 (by rfl) ⟨719921, by rfl⟩ : syracuseStep 959895 = 1439843) B1439843
theorem B959915 : Blo 956588 959915 := bstep (se 1 (by rfl) ⟨719936, by rfl⟩ : syracuseStep 959915 = 1439873) B1439873
theorem B5449139 : Blo 956588 5449139 := bstep (se 1 (by rfl) ⟨4086854, by rfl⟩ : syracuseStep 5449139 = 8173709) B8173709
theorem B959927 : Blo 956588 959927 := bstep (se 1 (by rfl) ⟨719945, by rfl⟩ : syracuseStep 959927 = 1439891) B1439891
theorem B959947 : Blo 956588 959947 := bstep (se 1 (by rfl) ⟨719960, by rfl⟩ : syracuseStep 959947 = 1439921) B1439921
theorem B959959 : Blo 956588 959959 := bstep (se 1 (by rfl) ⟨719969, by rfl⟩ : syracuseStep 959959 = 1439939) B1439939
theorem B959979 : Blo 956588 959979 := bstep (se 1 (by rfl) ⟨719984, by rfl⟩ : syracuseStep 959979 = 1439969) B1439969
theorem B959991 : Blo 956588 959991 := bstep (se 1 (by rfl) ⟨719993, by rfl⟩ : syracuseStep 959991 = 1439987) B1439987
theorem B960011 : Blo 956588 960011 := bstep (se 1 (by rfl) ⟨720008, by rfl⟩ : syracuseStep 960011 = 1440017) B1440017
theorem B960023 : Blo 956588 960023 := bstep (se 1 (by rfl) ⟨720017, by rfl⟩ : syracuseStep 960023 = 1440035) B1440035
theorem B960043 : Blo 956588 960043 := bstep (se 1 (by rfl) ⟨720032, by rfl⟩ : syracuseStep 960043 = 1440065) B1440065
theorem B960055 : Blo 956588 960055 := bstep (se 1 (by rfl) ⟨720041, by rfl⟩ : syracuseStep 960055 = 1440083) B1440083
theorem B960075 : Blo 956588 960075 := bstep (se 1 (by rfl) ⟨720056, by rfl⟩ : syracuseStep 960075 = 1440113) B1440113
theorem B3647051 : Blo 956588 3647051 := bstep (se 1 (by rfl) ⟨2735288, by rfl⟩ : syracuseStep 3647051 = 5470577) B5470577
theorem B960087 : Blo 956588 960087 := bstep (se 1 (by rfl) ⟨720065, by rfl⟩ : syracuseStep 960087 = 1440131) B1440131
theorem B3647065 : Blo 956588 3647065 := bstep (se 2 (by rfl) ⟨1367649, by rfl⟩ : syracuseStep 3647065 = 2735299) B2735299
theorem B960107 : Blo 956588 960107 := bstep (se 1 (by rfl) ⟨720080, by rfl⟩ : syracuseStep 960107 = 1440161) B1440161
theorem B960119 : Blo 956588 960119 := bstep (se 1 (by rfl) ⟨720089, by rfl⟩ : syracuseStep 960119 = 1440179) B1440179
theorem B960139 : Blo 956588 960139 := bstep (se 1 (by rfl) ⟨720104, by rfl⟩ : syracuseStep 960139 = 1440209) B1440209
theorem B1615511 : Blo 956588 1615511 := bstep (se 1 (by rfl) ⟨1211633, by rfl⟩ : syracuseStep 1615511 = 2423267) B2423267
theorem B960151 : Blo 956588 960151 := bstep (se 1 (by rfl) ⟨720113, by rfl⟩ : syracuseStep 960151 = 1440227) B1440227
theorem B960171 : Blo 956588 960171 := bstep (se 1 (by rfl) ⟨720128, by rfl⟩ : syracuseStep 960171 = 1440257) B1440257
theorem B960183 : Blo 956588 960183 := bstep (se 1 (by rfl) ⟨720137, by rfl⟩ : syracuseStep 960183 = 1440275) B1440275
theorem B960203 : Blo 956588 960203 := bstep (se 1 (by rfl) ⟨720152, by rfl⟩ : syracuseStep 960203 = 1440305) B1440305
theorem B960215 : Blo 956588 960215 := bstep (se 1 (by rfl) ⟨720161, by rfl⟩ : syracuseStep 960215 = 1440323) B1440323
theorem B960235 : Blo 956588 960235 := bstep (se 1 (by rfl) ⟨720176, by rfl⟩ : syracuseStep 960235 = 1440353) B1440353
theorem B960247 : Blo 956588 960247 := bstep (se 1 (by rfl) ⟨720185, by rfl⟩ : syracuseStep 960247 = 1440371) B1440371
theorem B960267 : Blo 956588 960267 := bstep (se 1 (by rfl) ⟨720200, by rfl⟩ : syracuseStep 960267 = 1440401) B1440401
theorem B1615639 : Blo 956588 1615639 := bstep (se 1 (by rfl) ⟨1211729, by rfl⟩ : syracuseStep 1615639 = 2423459) B2423459
theorem B960279 : Blo 956588 960279 := bstep (se 1 (by rfl) ⟨720209, by rfl⟩ : syracuseStep 960279 = 1440419) B1440419
theorem B960299 : Blo 956588 960299 := bstep (se 1 (by rfl) ⟨720224, by rfl⟩ : syracuseStep 960299 = 1440449) B1440449
theorem B960311 : Blo 956588 960311 := bstep (se 1 (by rfl) ⟨720233, by rfl⟩ : syracuseStep 960311 = 1440467) B1440467
theorem B960331 : Blo 956588 960331 := bstep (se 1 (by rfl) ⟨720248, by rfl⟩ : syracuseStep 960331 = 1440497) B1440497
theorem B960343 : Blo 956588 960343 := bstep (se 1 (by rfl) ⟨720257, by rfl⟩ : syracuseStep 960343 = 1440515) B1440515
theorem B2729821 : Blo 956588 2729821 := bstep (se 3 (by rfl) ⟨511841, by rfl⟩ : syracuseStep 2729821 = 1023683) B1023683
theorem B960363 : Blo 956588 960363 := bstep (se 1 (by rfl) ⟨720272, by rfl⟩ : syracuseStep 960363 = 1440545) B1440545
theorem B960375 : Blo 956588 960375 := bstep (se 1 (by rfl) ⟨720281, by rfl⟩ : syracuseStep 960375 = 1440563) B1440563
theorem B960395 : Blo 956588 960395 := bstep (se 1 (by rfl) ⟨720296, by rfl⟩ : syracuseStep 960395 = 1440593) B1440593
theorem B960407 : Blo 956588 960407 := bstep (se 1 (by rfl) ⟨720305, by rfl⟩ : syracuseStep 960407 = 1440611) B1440611
theorem B960427 : Blo 956588 960427 := bstep (se 1 (by rfl) ⟨720320, by rfl⟩ : syracuseStep 960427 = 1440641) B1440641
theorem B960439 : Blo 956588 960439 := bstep (se 1 (by rfl) ⟨720329, by rfl⟩ : syracuseStep 960439 = 1440659) B1440659
theorem B960459 : Blo 956588 960459 := bstep (se 1 (by rfl) ⟨720344, by rfl⟩ : syracuseStep 960459 = 1440689) B1440689
theorem B960471 : Blo 956588 960471 := bstep (se 1 (by rfl) ⟨720353, by rfl⟩ : syracuseStep 960471 = 1440707) B1440707
theorem B960491 : Blo 956588 960491 := bstep (se 1 (by rfl) ⟨720368, by rfl⟩ : syracuseStep 960491 = 1440737) B1440737
theorem B960503 : Blo 956588 960503 := bstep (se 1 (by rfl) ⟨720377, by rfl⟩ : syracuseStep 960503 = 1440755) B1440755
theorem B960523 : Blo 956588 960523 := bstep (se 1 (by rfl) ⟨720392, by rfl⟩ : syracuseStep 960523 = 1440785) B1440785
theorem B960535 : Blo 956588 960535 := bstep (se 1 (by rfl) ⟨720401, by rfl⟩ : syracuseStep 960535 = 1440803) B1440803
theorem B960555 : Blo 956588 960555 := bstep (se 1 (by rfl) ⟨720416, by rfl⟩ : syracuseStep 960555 = 1440833) B1440833
theorem B960567 : Blo 956588 960567 := bstep (se 1 (by rfl) ⟨720425, by rfl⟩ : syracuseStep 960567 = 1440851) B1440851
theorem B2304065 : Blo 956588 2304065 := bstep (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) B1728049
theorem B960587 : Blo 956588 960587 := bstep (se 1 (by rfl) ⟨720440, by rfl⟩ : syracuseStep 960587 = 1440881) B1440881
theorem B12298391 : Blo 956588 12298391 := bstep (se 1 (by rfl) ⟨9223793, by rfl⟩ : syracuseStep 12298391 = 18447587) B18447587
theorem B4368563 : Blo 956588 4368563 := bstep (se 1 (by rfl) ⟨3276422, by rfl⟩ : syracuseStep 4368563 = 6552845) B6552845
theorem B1616267 : Blo 956588 1616267 := bstep (se 1 (by rfl) ⟨1212200, by rfl⟩ : syracuseStep 1616267 = 2424401) B2424401
theorem B2075033 : Blo 956588 2075033 := bstep (se 2 (by rfl) ⟨778137, by rfl⟩ : syracuseStep 2075033 = 1556275) B1556275
theorem B1616395 : Blo 956588 1616395 := bstep (se 1 (by rfl) ⟨1212296, by rfl⟩ : syracuseStep 1616395 = 2424593) B2424593
theorem B4598365 : Blo 956588 4598365 := bstep (se 3 (by rfl) ⟨862193, by rfl⟩ : syracuseStep 4598365 = 1724387) B1724387
theorem B1616537 : Blo 956588 1616537 := bstep (se 2 (by rfl) ⟨606201, by rfl⟩ : syracuseStep 1616537 = 1212403) B1212403
theorem B1616665 : Blo 956588 1616665 := bstep (se 2 (by rfl) ⟨606249, by rfl⟩ : syracuseStep 1616665 = 1212499) B1212499
theorem B2763571 : Blo 956588 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B5450597 : Blo 956588 5450597 := bstep (se 4 (by rfl) ⟨510993, by rfl⟩ : syracuseStep 5450597 = 1021987) B1021987
theorem B6138841 : Blo 956588 6138841 := bstep (se 2 (by rfl) ⟨2302065, by rfl⟩ : syracuseStep 6138841 = 4604131) B4604131
theorem B1092619 : Blo 956588 1092619 := bstep (se 1 (by rfl) ⟨819464, by rfl⟩ : syracuseStep 1092619 = 1638929) B1638929
theorem B2731097 : Blo 956588 2731097 := bstep (se 2 (by rfl) ⟨1024161, by rfl⟩ : syracuseStep 2731097 = 2048323) B2048323
theorem B2075863 : Blo 956588 2075863 := bstep (se 1 (by rfl) ⟨1556897, by rfl⟩ : syracuseStep 2075863 = 3113795) B3113795
theorem B2043137 : Blo 956588 2043137 := bstep (se 2 (by rfl) ⟨766176, by rfl⟩ : syracuseStep 2043137 = 1532353) B1532353
theorem B4369729 : Blo 956588 4369729 := bstep (se 2 (by rfl) ⟨1638648, by rfl⟩ : syracuseStep 4369729 = 3277297) B3277297
theorem B1617239 : Blo 956588 1617239 := bstep (se 1 (by rfl) ⟨1212929, by rfl⟩ : syracuseStep 1617239 = 2425859) B2425859
theorem B1617367 : Blo 956588 1617367 := bstep (se 1 (by rfl) ⟨1213025, by rfl⟩ : syracuseStep 1617367 = 2426051) B2426051
theorem B4861457 : Blo 956588 4861457 := bstep (se 2 (by rfl) ⟨1823046, by rfl⟩ : syracuseStep 4861457 = 3646093) B3646093
theorem B4861619 : Blo 956588 4861619 := bstep (se 1 (by rfl) ⟨3646214, by rfl⟩ : syracuseStep 4861619 = 7292429) B7292429
theorem B13840307 : Blo 956588 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B1617995 : Blo 956588 1617995 := bstep (se 1 (by rfl) ⟨1213496, by rfl⟩ : syracuseStep 1617995 = 2426993) B2426993
theorem B2043991 : Blo 956588 2043991 := bstep (se 1 (by rfl) ⟨1532993, by rfl⟩ : syracuseStep 2043991 = 3065987) B3065987
theorem B1618123 : Blo 956588 1618123 := bstep (se 1 (by rfl) ⟨1213592, by rfl⟩ : syracuseStep 1618123 = 2427185) B2427185
theorem B1618265 : Blo 956588 1618265 := bstep (se 2 (by rfl) ⟨606849, by rfl⟩ : syracuseStep 1618265 = 1213699) B1213699
theorem B1618393 : Blo 956588 1618393 := bstep (se 2 (by rfl) ⟨606897, by rfl⟩ : syracuseStep 1618393 = 1213795) B1213795
theorem B2732737 : Blo 956588 2732737 := bstep (se 2 (by rfl) ⟨1024776, by rfl⟩ : syracuseStep 2732737 = 2049553) B2049553
theorem B7484165 : Blo 956588 7484165 := bstep (se 4 (by rfl) ⟨701640, by rfl⟩ : syracuseStep 7484165 = 1403281) B1403281
theorem B7779077 : Blo 956588 7779077 := bstep (se 4 (by rfl) ⟨729288, by rfl⟩ : syracuseStep 7779077 = 1458577) B1458577
theorem B7287569 : Blo 956588 7287569 := bstep (se 2 (by rfl) ⟨2732838, by rfl⟩ : syracuseStep 7287569 = 5465677) B5465677
theorem B3945233 : Blo 956588 3945233 := bstep (se 2 (by rfl) ⟨1479462, by rfl⟩ : syracuseStep 3945233 = 2958925) B2958925
theorem B2044811 : Blo 956588 2044811 := bstep (se 1 (by rfl) ⟨1533608, by rfl⟩ : syracuseStep 2044811 = 3067217) B3067217
theorem B1618967 : Blo 956588 1618967 := bstep (se 1 (by rfl) ⟨1214225, by rfl⟩ : syracuseStep 1618967 = 2428451) B2428451
theorem B56865827 : Blo 956588 56865827 := bstep (se 1 (by rfl) ⟨42649370, by rfl⟩ : syracuseStep 56865827 = 85298741) B85298741
theorem B1094699 : Blo 956588 1094699 := bstep (se 1 (by rfl) ⟨821024, by rfl⟩ : syracuseStep 1094699 = 1642049) B1642049
theorem B1619095 : Blo 956588 1619095 := bstep (se 1 (by rfl) ⟨1214321, by rfl⟩ : syracuseStep 1619095 = 2428643) B2428643
theorem B21050549 : Blo 956588 21050549 := bstep (se 5 (by rfl) ⟨986744, by rfl⟩ : syracuseStep 21050549 = 1973489) B1973489
theorem B1553623 : Blo 956588 1553623 := bstep (se 1 (by rfl) ⟨1165217, by rfl⟩ : syracuseStep 1553623 = 2330435) B2330435
theorem B2766145 : Blo 956588 2766145 := bstep (se 2 (by rfl) ⟨1037304, by rfl⟩ : syracuseStep 2766145 = 2074609) B2074609
theorem B2274635 : Blo 956588 2274635 := bstep (se 1 (by rfl) ⟨1705976, by rfl⟩ : syracuseStep 2274635 = 3411953) B3411953
theorem B8173061 : Blo 956588 8173061 := bstep (se 4 (by rfl) ⟨766224, by rfl⟩ : syracuseStep 8173061 = 1532449) B1532449
theorem B1619723 : Blo 956588 1619723 := bstep (se 1 (by rfl) ⟨1214792, by rfl⟩ : syracuseStep 1619723 = 2429585) B2429585
theorem B16398125 : Blo 956588 16398125 := bstep (se 3 (by rfl) ⟨3074648, by rfl⟩ : syracuseStep 16398125 = 6149297) B6149297
theorem B1619851 : Blo 956588 1619851 := bstep (se 1 (by rfl) ⟨1214888, by rfl⟩ : syracuseStep 1619851 = 2429777) B2429777
theorem B3880877 : Blo 956588 3880877 := bstep (se 3 (by rfl) ⟨727664, by rfl⟩ : syracuseStep 3880877 = 1455329) B1455329
theorem B1816577 : Blo 956588 1816577 := bstep (se 2 (by rfl) ⟨681216, by rfl⟩ : syracuseStep 1816577 = 1362433) B1362433
theorem B1619993 : Blo 956588 1619993 := bstep (se 2 (by rfl) ⟨607497, by rfl⟩ : syracuseStep 1619993 = 1214995) B1214995
theorem B3881105 : Blo 956588 3881105 := bstep (se 2 (by rfl) ⟨1455414, by rfl⟩ : syracuseStep 3881105 = 2910829) B2910829
theorem B1620121 : Blo 956588 1620121 := bstep (se 2 (by rfl) ⟨607545, by rfl⟩ : syracuseStep 1620121 = 1215091) B1215091
theorem B6895793 : Blo 956588 6895793 := bstep (se 2 (by rfl) ⟨2585922, by rfl⟩ : syracuseStep 6895793 = 5171845) B5171845
theorem B1816843 : Blo 956588 1816843 := bstep (se 1 (by rfl) ⟨1362632, by rfl⟩ : syracuseStep 1816843 = 2725265) B2725265
theorem B2734411 : Blo 956588 2734411 := bstep (se 1 (by rfl) ⟨2050808, by rfl⟩ : syracuseStep 2734411 = 4101617) B4101617
theorem B2734685 : Blo 956588 2734685 := bstep (se 3 (by rfl) ⟨512753, by rfl⟩ : syracuseStep 2734685 = 1025507) B1025507
theorem B6896279 : Blo 956588 6896279 := bstep (se 1 (by rfl) ⟨5172209, by rfl⟩ : syracuseStep 6896279 = 10344419) B10344419
theorem B1817291 : Blo 956588 1817291 := bstep (se 1 (by rfl) ⟨1362968, by rfl⟩ : syracuseStep 1817291 = 2725937) B2725937
theorem B1620695 : Blo 956588 1620695 := bstep (se 1 (by rfl) ⟨1215521, by rfl⟩ : syracuseStep 1620695 = 2431043) B2431043
theorem B1620823 : Blo 956588 1620823 := bstep (se 1 (by rfl) ⟨1215617, by rfl⟩ : syracuseStep 1620823 = 2431235) B2431235
theorem B1817473 : Blo 956588 1817473 := bstep (se 2 (by rfl) ⟨681552, by rfl⟩ : syracuseStep 1817473 = 1363105) B1363105
theorem B2047169 : Blo 956588 2047169 := bstep (se 2 (by rfl) ⟨767688, by rfl⟩ : syracuseStep 2047169 = 1535377) B1535377
theorem B1817815 : Blo 956588 1817815 := bstep (se 1 (by rfl) ⟨1363361, by rfl⟩ : syracuseStep 1817815 = 2726723) B2726723
theorem B2768093 : Blo 956588 2768093 := bstep (se 3 (by rfl) ⟨519017, by rfl⟩ : syracuseStep 2768093 = 1038035) B1038035
theorem B9485669 : Blo 956588 9485669 := bstep (se 4 (by rfl) ⟨889281, by rfl⟩ : syracuseStep 9485669 = 1778563) B1778563
theorem B1818035 : Blo 956588 1818035 := bstep (se 1 (by rfl) ⟨1363526, by rfl⟩ : syracuseStep 1818035 = 2727053) B2727053
theorem B12271121 : Blo 956588 12271121 := bstep (se 2 (by rfl) ⟨4601670, by rfl⟩ : syracuseStep 12271121 = 9203341) B9203341
theorem B2047511 : Blo 956588 2047511 := bstep (se 1 (by rfl) ⟨1535633, by rfl⟩ : syracuseStep 2047511 = 3071267) B3071267
theorem B10927709 : Blo 956588 10927709 := bstep (se 3 (by rfl) ⟨2048945, by rfl⟩ : syracuseStep 10927709 = 4097891) B4097891
theorem B3882647 : Blo 956588 3882647 := bstep (se 1 (by rfl) ⟨2911985, by rfl⟩ : syracuseStep 3882647 = 5823971) B5823971
theorem B1818263 : Blo 956588 1818263 := bstep (se 1 (by rfl) ⟨1363697, by rfl⟩ : syracuseStep 1818263 = 2727395) B2727395
theorem B18693989 : Blo 956588 18693989 := bstep (se 4 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 18693989 = 3505123) B3505123
theorem B1818521 : Blo 956588 1818521 := bstep (se 2 (by rfl) ⟨681945, by rfl⟩ : syracuseStep 1818521 = 1363891) B1363891
theorem B2768833 : Blo 956588 2768833 := bstep (se 2 (by rfl) ⟨1038312, by rfl⟩ : syracuseStep 2768833 = 2076625) B2076625
theorem B16597061 : Blo 956588 16597061 := bstep (se 4 (by rfl) ⟨1555974, by rfl⟩ : syracuseStep 16597061 = 3111949) B3111949
theorem B2048075 : Blo 956588 2048075 := bstep (se 1 (by rfl) ⟨1536056, by rfl⟩ : syracuseStep 2048075 = 3072113) B3072113
theorem B1458443 : Blo 956588 1458443 := bstep (se 1 (by rfl) ⟨1093832, by rfl⟩ : syracuseStep 1458443 = 2187665) B2187665
theorem B1818931 : Blo 956588 1818931 := bstep (se 1 (by rfl) ⟨1364198, by rfl⟩ : syracuseStep 1818931 = 2728397) B2728397
theorem B29573603 : Blo 956588 29573603 := bstep (se 1 (by rfl) ⟨22180202, by rfl⟩ : syracuseStep 29573603 = 44360405) B44360405
theorem B5456429 : Blo 956588 5456429 := bstep (se 3 (by rfl) ⟨1023080, by rfl⟩ : syracuseStep 5456429 = 2046161) B2046161
theorem B3883571 : Blo 956588 3883571 := bstep (se 1 (by rfl) ⟨2912678, by rfl⟩ : syracuseStep 3883571 = 5825357) B5825357
theorem B7291457 : Blo 956588 7291457 := bstep (se 2 (by rfl) ⟨2734296, by rfl⟩ : syracuseStep 7291457 = 5468593) B5468593
theorem B2048665 : Blo 956588 2048665 := bstep (se 2 (by rfl) ⟨768249, by rfl⟩ : syracuseStep 2048665 = 1536499) B1536499
theorem B1295129 : Blo 956588 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B1819417 : Blo 956588 1819417 := bstep (se 2 (by rfl) ⟨682281, by rfl⟩ : syracuseStep 1819417 = 1364563) B1364563
theorem B8111027 : Blo 956588 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B3228875 : Blo 956588 3228875 := bstep (se 1 (by rfl) ⟨2421656, by rfl⟩ : syracuseStep 3228875 = 4843313) B4843313
theorem B3458321 : Blo 956588 3458321 := bstep (se 2 (by rfl) ⟨1296870, by rfl⟩ : syracuseStep 3458321 = 2593741) B2593741
theorem B1819979 : Blo 956588 1819979 := bstep (se 1 (by rfl) ⟨1364984, by rfl⟩ : syracuseStep 1819979 = 2729969) B2729969
theorem B13813091 : Blo 956588 13813091 := bstep (se 1 (by rfl) ⟨10359818, by rfl⟩ : syracuseStep 13813091 = 20719637) B20719637
theorem B10372531 : Blo 956588 10372531 := bstep (se 1 (by rfl) ⟨7779398, by rfl⟩ : syracuseStep 10372531 = 15558797) B15558797
theorem B3229145 : Blo 956588 3229145 := bstep (se 2 (by rfl) ⟨1210929, by rfl⟩ : syracuseStep 3229145 = 2421859) B2421859
theorem B3065309 : Blo 956588 3065309 := bstep (se 3 (by rfl) ⟨574745, by rfl⟩ : syracuseStep 3065309 = 1149491) B1149491
theorem B1820161 : Blo 956588 1820161 := bstep (se 2 (by rfl) ⟨682560, by rfl⟩ : syracuseStep 1820161 = 1365121) B1365121
theorem B4605515 : Blo 956588 4605515 := bstep (se 1 (by rfl) ⟨3454136, by rfl⟩ : syracuseStep 4605515 = 6908273) B6908273
theorem B3884723 : Blo 956588 3884723 := bstep (se 1 (by rfl) ⟨2913542, by rfl⟩ : syracuseStep 3884723 = 5827085) B5827085
theorem B2049715 : Blo 956588 2049715 := bstep (se 1 (by rfl) ⟨1537286, by rfl⟩ : syracuseStep 2049715 = 3074573) B3074573
theorem B5326667 : Blo 956588 5326667 := bstep (se 1 (by rfl) ⟨3995000, by rfl⟩ : syracuseStep 5326667 = 7990001) B7990001
theorem B4376537 : Blo 956588 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B3229847 : Blo 956588 3229847 := bstep (se 1 (by rfl) ⟨2422385, by rfl⟩ : syracuseStep 3229847 = 4844771) B4844771
theorem B1820875 : Blo 956588 1820875 := bstep (se 1 (by rfl) ⟨1365656, by rfl⟩ : syracuseStep 1820875 = 2731313) B2731313
theorem B1820951 : Blo 956588 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B2771351 : Blo 956588 2771351 := bstep (se 1 (by rfl) ⟨2078513, by rfl⟩ : syracuseStep 2771351 = 4157027) B4157027
theorem B7293401 : Blo 956588 7293401 := bstep (se 2 (by rfl) ⟨2735025, by rfl⟩ : syracuseStep 7293401 = 5470051) B5470051
theorem B4672093 : Blo 956588 4672093 := bstep (se 3 (by rfl) ⟨876017, by rfl⟩ : syracuseStep 4672093 = 1752035) B1752035
theorem B3230387 : Blo 956588 3230387 := bstep (se 1 (by rfl) ⟨2422790, by rfl⟩ : syracuseStep 3230387 = 4845581) B4845581
theorem B2804503 : Blo 956588 2804503 := bstep (se 1 (by rfl) ⟨2103377, by rfl⟩ : syracuseStep 2804503 = 4206755) B4206755
theorem B1297291 : Blo 956588 1297291 := bstep (se 1 (by rfl) ⟨972968, by rfl⟩ : syracuseStep 1297291 = 1945937) B1945937
theorem B1821619 : Blo 956588 1821619 := bstep (se 1 (by rfl) ⟨1366214, by rfl⟩ : syracuseStep 1821619 = 2732429) B2732429
theorem B3230657 : Blo 956588 3230657 := bstep (se 2 (by rfl) ⟨1211496, by rfl⟩ : syracuseStep 3230657 = 2422993) B2422993
theorem B68111381 : Blo 956588 68111381 := bstep (se 6 (by rfl) ⟨1596360, by rfl⟩ : syracuseStep 68111381 = 3192721) B3192721
theorem B2051201 : Blo 956588 2051201 := bstep (se 2 (by rfl) ⟨769200, by rfl⟩ : syracuseStep 2051201 = 1538401) B1538401
theorem B1821847 : Blo 956588 1821847 := bstep (se 1 (by rfl) ⟨1366385, by rfl⟩ : syracuseStep 1821847 = 2732771) B2732771
theorem B1821953 : Blo 956588 1821953 := bstep (se 2 (by rfl) ⟨683232, by rfl⟩ : syracuseStep 1821953 = 1366465) B1366465
theorem B1363225 : Blo 956588 1363225 := bstep (se 2 (by rfl) ⟨511209, by rfl⟩ : syracuseStep 1363225 = 1022419) B1022419
theorem B1822105 : Blo 956588 1822105 := bstep (se 2 (by rfl) ⟨683289, by rfl⟩ : syracuseStep 1822105 = 1366579) B1366579
theorem B2051543 : Blo 956588 2051543 := bstep (se 1 (by rfl) ⟨1538657, by rfl⟩ : syracuseStep 2051543 = 3077315) B3077315
theorem B3231197 : Blo 956588 3231197 := bstep (se 3 (by rfl) ⟨605849, by rfl⟩ : syracuseStep 3231197 = 1211699) B1211699
theorem B3460825 : Blo 956588 3460825 := bstep (se 2 (by rfl) ⟨1297809, by rfl⟩ : syracuseStep 3460825 = 2595619) B2595619
theorem B18665315 : Blo 956588 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B1724503 : Blo 956588 1724503 := bstep (se 1 (by rfl) ⟨1293377, by rfl⟩ : syracuseStep 1724503 = 2586755) B2586755
theorem B5460119 : Blo 956588 5460119 := bstep (se 1 (by rfl) ⟨4095089, by rfl⟩ : syracuseStep 5460119 = 8190179) B8190179
theorem B1724993 : Blo 956588 1724993 := bstep (se 2 (by rfl) ⟨646872, by rfl⟩ : syracuseStep 1724993 = 1293745) B1293745
theorem B3232331 : Blo 956588 3232331 := bstep (se 1 (by rfl) ⟨2424248, by rfl⟩ : syracuseStep 3232331 = 4848497) B4848497
theorem B1823411 : Blo 956588 1823411 := bstep (se 1 (by rfl) ⟨1367558, by rfl⟩ : syracuseStep 1823411 = 2735117) B2735117
theorem B1364683 : Blo 956588 1364683 := bstep (se 1 (by rfl) ⟨1023512, by rfl⟩ : syracuseStep 1364683 = 2047025) B2047025
theorem B10343213 : Blo 956588 10343213 := bstep (se 3 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 10343213 = 3878705) B3878705
theorem B1823563 : Blo 956588 1823563 := bstep (se 1 (by rfl) ⟨1367672, by rfl⟩ : syracuseStep 1823563 = 2735345) B2735345
theorem B3232601 : Blo 956588 3232601 := bstep (se 2 (by rfl) ⟨1212225, by rfl⟩ : syracuseStep 3232601 = 2424451) B2424451
theorem B14603125 : Blo 956588 14603125 := bstep (se 5 (by rfl) ⟨684521, by rfl⟩ : syracuseStep 14603125 = 1369043) B1369043
theorem B971671 : Blo 956588 971671 := bstep (se 1 (by rfl) ⟨728753, by rfl⟩ : syracuseStep 971671 = 1457507) B1457507
theorem B2184179 : Blo 956588 2184179 := bstep (se 1 (by rfl) ⟨1638134, by rfl⟩ : syracuseStep 2184179 = 3276269) B3276269
theorem B2184215 : Blo 956588 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B3233303 : Blo 956588 3233303 := bstep (se 1 (by rfl) ⟨2424977, by rfl⟩ : syracuseStep 3233303 = 4849955) B4849955
theorem B2152331 : Blo 956588 2152331 := bstep (se 1 (by rfl) ⟨1614248, by rfl⟩ : syracuseStep 2152331 = 3228497) B3228497
theorem B1365913 : Blo 956588 1365913 := bstep (se 2 (by rfl) ⟨512217, by rfl⟩ : syracuseStep 1365913 = 1024435) B1024435
theorem B2152385 : Blo 956588 2152385 := bstep (se 2 (by rfl) ⟨807144, by rfl⟩ : syracuseStep 2152385 = 1614289) B1614289
theorem B10901465 : Blo 956588 10901465 := bstep (se 2 (by rfl) ⟨4088049, by rfl⟩ : syracuseStep 10901465 = 8176099) B8176099
theorem B3233843 : Blo 956588 3233843 := bstep (se 1 (by rfl) ⟨2425382, by rfl⟩ : syracuseStep 3233843 = 4850765) B4850765
theorem B2152601 : Blo 956588 2152601 := bstep (se 2 (by rfl) ⟨807225, by rfl⟩ : syracuseStep 2152601 = 1614451) B1614451
theorem B6150323 : Blo 956588 6150323 := bstep (se 1 (by rfl) ⟨4612742, by rfl⟩ : syracuseStep 6150323 = 9225485) B9225485
theorem B2152691 : Blo 956588 2152691 := bstep (se 1 (by rfl) ⟨1614518, by rfl⟩ : syracuseStep 2152691 = 3229037) B3229037
theorem B2152727 : Blo 956588 2152727 := bstep (se 1 (by rfl) ⟨1614545, by rfl⟩ : syracuseStep 2152727 = 3229091) B3229091
theorem B3234113 : Blo 956588 3234113 := bstep (se 2 (by rfl) ⟨1212792, by rfl⟩ : syracuseStep 3234113 = 2425585) B2425585
theorem B2152907 : Blo 956588 2152907 := bstep (se 1 (by rfl) ⟨1614680, by rfl⟩ : syracuseStep 2152907 = 3229361) B3229361
theorem B2152961 : Blo 956588 2152961 := bstep (se 2 (by rfl) ⟨807360, by rfl⟩ : syracuseStep 2152961 = 1614721) B1614721
theorem B2153177 : Blo 956588 2153177 := bstep (se 2 (by rfl) ⟨807441, by rfl⟩ : syracuseStep 2153177 = 1614883) B1614883
theorem B1366807 : Blo 956588 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B2153267 : Blo 956588 2153267 := bstep (se 1 (by rfl) ⟨1614950, by rfl⟩ : syracuseStep 2153267 = 3229901) B3229901
theorem B2153303 : Blo 956588 2153303 := bstep (se 1 (by rfl) ⟨1614977, by rfl⟩ : syracuseStep 2153303 = 3229955) B3229955
theorem B3234653 : Blo 956588 3234653 := bstep (se 3 (by rfl) ⟨606497, by rfl⟩ : syracuseStep 3234653 = 1212995) B1212995
theorem B2186135 : Blo 956588 2186135 := bstep (se 1 (by rfl) ⟨1639601, by rfl⟩ : syracuseStep 2186135 = 3279203) B3279203
theorem B2153483 : Blo 956588 2153483 := bstep (se 1 (by rfl) ⟨1615112, by rfl⟩ : syracuseStep 2153483 = 3230225) B3230225
theorem B2153537 : Blo 956588 2153537 := bstep (se 2 (by rfl) ⟨807576, by rfl⟩ : syracuseStep 2153537 = 1615153) B1615153
theorem B13819085 : Blo 956588 13819085 := bstep (se 3 (by rfl) ⟨2591078, by rfl⟩ : syracuseStep 13819085 = 5182157) B5182157
theorem B2153753 : Blo 956588 2153753 := bstep (se 2 (by rfl) ⟨807657, by rfl⟩ : syracuseStep 2153753 = 1615315) B1615315
theorem B1367371 : Blo 956588 1367371 := bstep (se 1 (by rfl) ⟨1025528, by rfl⟩ : syracuseStep 1367371 = 2051057) B2051057
theorem B1727833 : Blo 956588 1727833 := bstep (se 2 (by rfl) ⟨647937, by rfl⟩ : syracuseStep 1727833 = 1295875) B1295875
theorem B2153843 : Blo 956588 2153843 := bstep (se 1 (by rfl) ⟨1615382, by rfl⟩ : syracuseStep 2153843 = 3230765) B3230765
theorem B2153879 : Blo 956588 2153879 := bstep (se 1 (by rfl) ⟨1615409, by rfl⟩ : syracuseStep 2153879 = 3230819) B3230819
theorem B2154059 : Blo 956588 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B2154113 : Blo 956588 2154113 := bstep (se 2 (by rfl) ⟨807792, by rfl⟩ : syracuseStep 2154113 = 1615585) B1615585
theorem B56123077 : Blo 956588 56123077 := bstep (se 4 (by rfl) ⟨5261538, by rfl⟩ : syracuseStep 56123077 = 10523077) B10523077
theorem B2154329 : Blo 956588 2154329 := bstep (se 2 (by rfl) ⟨807873, by rfl⟩ : syracuseStep 2154329 = 1615747) B1615747
theorem B1728395 : Blo 956588 1728395 := bstep (se 1 (by rfl) ⟨1296296, by rfl⟩ : syracuseStep 1728395 = 2592593) B2592593
theorem B2154419 : Blo 956588 2154419 := bstep (se 1 (by rfl) ⟨1615814, by rfl⟩ : syracuseStep 2154419 = 3231629) B3231629
theorem B3235787 : Blo 956588 3235787 := bstep (se 1 (by rfl) ⟨2426840, by rfl⟩ : syracuseStep 3235787 = 4853681) B4853681
theorem B2154455 : Blo 956588 2154455 := bstep (se 1 (by rfl) ⟨1615841, by rfl⟩ : syracuseStep 2154455 = 3231683) B3231683
theorem B7004225 : Blo 956588 7004225 := bstep (se 2 (by rfl) ⟨2626584, by rfl⟩ : syracuseStep 7004225 = 5253169) B5253169
theorem B2154635 : Blo 956588 2154635 := bstep (se 1 (by rfl) ⟨1615976, by rfl⟩ : syracuseStep 2154635 = 3231953) B3231953
theorem B2154689 : Blo 956588 2154689 := bstep (se 2 (by rfl) ⟨808008, by rfl⟩ : syracuseStep 2154689 = 1616017) B1616017
theorem B3236057 : Blo 956588 3236057 := bstep (se 2 (by rfl) ⟨1213521, by rfl⟩ : syracuseStep 3236057 = 2427043) B2427043
theorem B1728857 : Blo 956588 1728857 := bstep (se 2 (by rfl) ⟨648321, by rfl⟩ : syracuseStep 1728857 = 1296643) B1296643
theorem B2154905 : Blo 956588 2154905 := bstep (se 2 (by rfl) ⟨808089, by rfl⟩ : syracuseStep 2154905 = 1616179) B1616179
theorem B3498461 : Blo 956588 3498461 := bstep (se 3 (by rfl) ⟨655961, by rfl⟩ : syracuseStep 3498461 = 1311923) B1311923
theorem B2154995 : Blo 956588 2154995 := bstep (se 1 (by rfl) ⟨1616246, by rfl⟩ : syracuseStep 2154995 = 3232493) B3232493
theorem B4088323 : Blo 956588 4088323 := bstep (se 1 (by rfl) ⟨3066242, by rfl⟩ : syracuseStep 4088323 = 6132485) B6132485
theorem B2155031 : Blo 956588 2155031 := bstep (se 1 (by rfl) ⟨1616273, by rfl⟩ : syracuseStep 2155031 = 3232547) B3232547
theorem B1729217 : Blo 956588 1729217 := bstep (se 2 (by rfl) ⟨648456, by rfl⟩ : syracuseStep 1729217 = 1296913) B1296913
theorem B2155211 : Blo 956588 2155211 := bstep (se 1 (by rfl) ⟨1616408, by rfl⟩ : syracuseStep 2155211 = 3232817) B3232817
theorem B2155265 : Blo 956588 2155265 := bstep (se 2 (by rfl) ⟨808224, by rfl⟩ : syracuseStep 2155265 = 1616449) B1616449
theorem B3236759 : Blo 956588 3236759 := bstep (se 1 (by rfl) ⟨2427569, by rfl⟩ : syracuseStep 3236759 = 4855139) B4855139
theorem B2155481 : Blo 956588 2155481 := bstep (se 2 (by rfl) ⟨808305, by rfl⟩ : syracuseStep 2155481 = 1616611) B1616611
theorem B2155571 : Blo 956588 2155571 := bstep (se 1 (by rfl) ⟨1616678, by rfl⟩ : syracuseStep 2155571 = 3233357) B3233357
theorem B2155607 : Blo 956588 2155607 := bstep (se 1 (by rfl) ⟨1616705, by rfl⟩ : syracuseStep 2155607 = 3233411) B3233411
theorem B3073241 : Blo 956588 3073241 := bstep (se 2 (by rfl) ⟨1152465, by rfl⟩ : syracuseStep 3073241 = 2304931) B2304931
theorem B2155787 : Blo 956588 2155787 := bstep (se 1 (by rfl) ⟨1616840, by rfl⟩ : syracuseStep 2155787 = 3233681) B3233681
theorem B1434905 : Blo 956588 1434905 := bstep (se 2 (by rfl) ⟨538089, by rfl⟩ : syracuseStep 1434905 = 1076179) B1076179
theorem B2188595 : Blo 956588 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B2155841 : Blo 956588 2155841 := bstep (se 2 (by rfl) ⟨808440, by rfl⟩ : syracuseStep 2155841 = 1616881) B1616881
theorem B4842827 : Blo 956588 4842827 := bstep (se 1 (by rfl) ⟨3632120, by rfl⟩ : syracuseStep 4842827 = 7264241) B7264241
theorem B1435019 : Blo 956588 1435019 := bstep (se 1 (by rfl) ⟨1076264, by rfl⟩ : syracuseStep 1435019 = 2152529) B2152529
theorem B1435031 : Blo 956588 1435031 := bstep (se 1 (by rfl) ⟨1076273, by rfl⟩ : syracuseStep 1435031 = 2152547) B2152547
theorem B5465495 : Blo 956588 5465495 := bstep (se 1 (by rfl) ⟨4099121, by rfl⟩ : syracuseStep 5465495 = 8198243) B8198243
theorem B3237299 : Blo 956588 3237299 := bstep (se 1 (by rfl) ⟨2427974, by rfl⟩ : syracuseStep 3237299 = 4855949) B4855949
theorem B1435097 : Blo 956588 1435097 := bstep (se 2 (by rfl) ⟨538161, by rfl⟩ : syracuseStep 1435097 = 1076323) B1076323
theorem B2156057 : Blo 956588 2156057 := bstep (se 2 (by rfl) ⟨808521, by rfl⟩ : syracuseStep 2156057 = 1617043) B1617043
theorem B1435211 : Blo 956588 1435211 := bstep (se 1 (by rfl) ⟨1076408, by rfl⟩ : syracuseStep 1435211 = 2152817) B2152817
theorem B1435223 : Blo 956588 1435223 := bstep (se 1 (by rfl) ⟨1076417, by rfl⟩ : syracuseStep 1435223 = 2152835) B2152835
theorem B2156147 : Blo 956588 2156147 := bstep (se 1 (by rfl) ⟨1617110, by rfl⟩ : syracuseStep 2156147 = 3234221) B3234221
theorem B2156183 : Blo 956588 2156183 := bstep (se 1 (by rfl) ⟨1617137, by rfl⟩ : syracuseStep 2156183 = 3234275) B3234275
theorem B1435289 : Blo 956588 1435289 := bstep (se 2 (by rfl) ⟨538233, by rfl⟩ : syracuseStep 1435289 = 1076467) B1076467
theorem B3237569 : Blo 956588 3237569 := bstep (se 2 (by rfl) ⟨1214088, by rfl⟩ : syracuseStep 3237569 = 2428177) B2428177
theorem B1664729 : Blo 956588 1664729 := bstep (se 2 (by rfl) ⟨624273, by rfl⟩ : syracuseStep 1664729 = 1248547) B1248547
theorem B1435403 : Blo 956588 1435403 := bstep (se 1 (by rfl) ⟨1076552, by rfl⟩ : syracuseStep 1435403 = 2153105) B2153105
theorem B1435415 : Blo 956588 1435415 := bstep (se 1 (by rfl) ⟨1076561, by rfl⟩ : syracuseStep 1435415 = 2153123) B2153123
theorem B1730327 : Blo 956588 1730327 := bstep (se 1 (by rfl) ⟨1297745, by rfl⟩ : syracuseStep 1730327 = 2595491) B2595491
theorem B2156363 : Blo 956588 2156363 := bstep (se 1 (by rfl) ⟨1617272, by rfl⟩ : syracuseStep 2156363 = 3234545) B3234545
theorem B1435481 : Blo 956588 1435481 := bstep (se 2 (by rfl) ⟨538305, by rfl⟩ : syracuseStep 1435481 = 1076611) B1076611
theorem B2156417 : Blo 956588 2156417 := bstep (se 2 (by rfl) ⟨808656, by rfl⟩ : syracuseStep 2156417 = 1617313) B1617313
theorem B1435595 : Blo 956588 1435595 := bstep (se 1 (by rfl) ⟨1076696, by rfl⟩ : syracuseStep 1435595 = 2153393) B2153393
theorem B8185805 : Blo 956588 8185805 := bstep (se 3 (by rfl) ⟨1534838, by rfl⟩ : syracuseStep 8185805 = 3069677) B3069677
theorem B1435607 : Blo 956588 1435607 := bstep (se 1 (by rfl) ⟨1076705, by rfl⟩ : syracuseStep 1435607 = 2153411) B2153411
theorem B1435673 : Blo 956588 1435673 := bstep (se 2 (by rfl) ⟨538377, by rfl⟩ : syracuseStep 1435673 = 1076755) B1076755
theorem B3696691 : Blo 956588 3696691 := bstep (se 1 (by rfl) ⟨2772518, by rfl⟩ : syracuseStep 3696691 = 5545037) B5545037
theorem B2156633 : Blo 956588 2156633 := bstep (se 2 (by rfl) ⟨808737, by rfl⟩ : syracuseStep 2156633 = 1617475) B1617475
theorem B1435787 : Blo 956588 1435787 := bstep (se 1 (by rfl) ⟨1076840, by rfl⟩ : syracuseStep 1435787 = 2153681) B2153681
theorem B1435799 : Blo 956588 1435799 := bstep (se 1 (by rfl) ⟨1076849, by rfl⟩ : syracuseStep 1435799 = 2153699) B2153699
theorem B2156723 : Blo 956588 2156723 := bstep (se 1 (by rfl) ⟨1617542, by rfl⟩ : syracuseStep 2156723 = 3235085) B3235085
theorem B2156759 : Blo 956588 2156759 := bstep (se 1 (by rfl) ⟨1617569, by rfl⟩ : syracuseStep 2156759 = 3235139) B3235139
theorem B1435865 : Blo 956588 1435865 := bstep (se 2 (by rfl) ⟨538449, by rfl⟩ : syracuseStep 1435865 = 1076899) B1076899
theorem B3238109 : Blo 956588 3238109 := bstep (se 3 (by rfl) ⟨607145, by rfl⟩ : syracuseStep 3238109 = 1214291) B1214291
theorem B4090135 : Blo 956588 4090135 := bstep (se 1 (by rfl) ⟨3067601, by rfl⟩ : syracuseStep 4090135 = 6135203) B6135203
theorem B1435979 : Blo 956588 1435979 := bstep (se 1 (by rfl) ⟨1076984, by rfl⟩ : syracuseStep 1435979 = 2153969) B2153969
theorem B1435991 : Blo 956588 1435991 := bstep (se 1 (by rfl) ⟨1076993, by rfl⟩ : syracuseStep 1435991 = 2153987) B2153987
theorem B1534295 : Blo 956588 1534295 := bstep (se 1 (by rfl) ⟨1150721, by rfl⟩ : syracuseStep 1534295 = 2301443) B2301443
theorem B2189683 : Blo 956588 2189683 := bstep (se 1 (by rfl) ⟨1642262, by rfl⟩ : syracuseStep 2189683 = 3284525) B3284525
theorem B2156939 : Blo 956588 2156939 := bstep (se 1 (by rfl) ⟨1617704, by rfl⟩ : syracuseStep 2156939 = 3235409) B3235409
theorem B1436057 : Blo 956588 1436057 := bstep (se 2 (by rfl) ⟨538521, by rfl⟩ : syracuseStep 1436057 = 1077043) B1077043
theorem B2156993 : Blo 956588 2156993 := bstep (se 2 (by rfl) ⟨808872, by rfl⟩ : syracuseStep 2156993 = 1617745) B1617745
theorem B1436171 : Blo 956588 1436171 := bstep (se 1 (by rfl) ⟨1077128, by rfl⟩ : syracuseStep 1436171 = 2154257) B2154257
theorem B1436183 : Blo 956588 1436183 := bstep (se 1 (by rfl) ⟨1077137, by rfl⟩ : syracuseStep 1436183 = 2154275) B2154275
theorem B5171777 : Blo 956588 5171777 := bstep (se 2 (by rfl) ⟨1939416, by rfl⟩ : syracuseStep 5171777 = 3878833) B3878833
theorem B1436249 : Blo 956588 1436249 := bstep (se 2 (by rfl) ⟨538593, by rfl⟩ : syracuseStep 1436249 = 1077187) B1077187
theorem B5171863 : Blo 956588 5171863 := bstep (se 1 (by rfl) ⟨3878897, by rfl⟩ : syracuseStep 5171863 = 7757795) B7757795
theorem B2157209 : Blo 956588 2157209 := bstep (se 2 (by rfl) ⟨808953, by rfl⟩ : syracuseStep 2157209 = 1617907) B1617907
theorem B1436363 : Blo 956588 1436363 := bstep (se 1 (by rfl) ⟨1077272, by rfl⟩ : syracuseStep 1436363 = 2154545) B2154545
theorem B10349261 : Blo 956588 10349261 := bstep (se 3 (by rfl) ⟨1940486, by rfl⟩ : syracuseStep 10349261 = 3880973) B3880973
theorem B1436375 : Blo 956588 1436375 := bstep (se 1 (by rfl) ⟨1077281, by rfl⟩ : syracuseStep 1436375 = 2154563) B2154563
theorem B2157299 : Blo 956588 2157299 := bstep (se 1 (by rfl) ⟨1617974, by rfl⟩ : syracuseStep 2157299 = 3235949) B3235949
theorem B2157335 : Blo 956588 2157335 := bstep (se 1 (by rfl) ⟨1618001, by rfl⟩ : syracuseStep 2157335 = 3236003) B3236003
theorem B1436441 : Blo 956588 1436441 := bstep (se 2 (by rfl) ⟨538665, by rfl⟩ : syracuseStep 1436441 = 1077331) B1077331
theorem B3074881 : Blo 956588 3074881 := bstep (se 2 (by rfl) ⟨1153080, by rfl⟩ : syracuseStep 3074881 = 2306161) B2306161
theorem B1436555 : Blo 956588 1436555 := bstep (se 1 (by rfl) ⟨1077416, by rfl⟩ : syracuseStep 1436555 = 2154833) B2154833
theorem B1534859 : Blo 956588 1534859 := bstep (se 1 (by rfl) ⟨1151144, by rfl⟩ : syracuseStep 1534859 = 2302289) B2302289
theorem B4090769 : Blo 956588 4090769 := bstep (se 2 (by rfl) ⟨1534038, by rfl⟩ : syracuseStep 4090769 = 3068077) B3068077
theorem B1436567 : Blo 956588 1436567 := bstep (se 1 (by rfl) ⟨1077425, by rfl⟩ : syracuseStep 1436567 = 2154851) B2154851
theorem B2157515 : Blo 956588 2157515 := bstep (se 1 (by rfl) ⟨1618136, by rfl⟩ : syracuseStep 2157515 = 3236273) B3236273
theorem B1436633 : Blo 956588 1436633 := bstep (se 2 (by rfl) ⟨538737, by rfl⟩ : syracuseStep 1436633 = 1077475) B1077475
theorem B1076215 : Blo 956588 1076215 := bstep (se 1 (by rfl) ⟨807161, by rfl⟩ : syracuseStep 1076215 = 1614323) B1614323
theorem B2157569 : Blo 956588 2157569 := bstep (se 2 (by rfl) ⟨809088, by rfl⟩ : syracuseStep 2157569 = 1618177) B1618177
theorem B4844609 : Blo 956588 4844609 := bstep (se 2 (by rfl) ⟨1816728, by rfl⟩ : syracuseStep 4844609 = 3633457) B3633457
theorem B1436747 : Blo 956588 1436747 := bstep (se 1 (by rfl) ⟨1077560, by rfl⟩ : syracuseStep 1436747 = 2155121) B2155121
theorem B1436759 : Blo 956588 1436759 := bstep (se 1 (by rfl) ⟨1077569, by rfl⟩ : syracuseStep 1436759 = 2155139) B2155139
theorem B3632273 : Blo 956588 3632273 := bstep (se 2 (by rfl) ⟨1362102, by rfl⟩ : syracuseStep 3632273 = 2724205) B2724205
theorem B1436825 : Blo 956588 1436825 := bstep (se 2 (by rfl) ⟨538809, by rfl⟩ : syracuseStep 1436825 = 1077619) B1077619
theorem B1076395 : Blo 956588 1076395 := bstep (se 1 (by rfl) ⟨807296, by rfl⟩ : syracuseStep 1076395 = 1614593) B1614593
theorem B2157785 : Blo 956588 2157785 := bstep (se 2 (by rfl) ⟨809169, by rfl⟩ : syracuseStep 2157785 = 1618339) B1618339
theorem B1436939 : Blo 956588 1436939 := bstep (se 1 (by rfl) ⟨1077704, by rfl⟩ : syracuseStep 1436939 = 2155409) B2155409
theorem B5467409 : Blo 956588 5467409 := bstep (se 2 (by rfl) ⟨2050278, by rfl⟩ : syracuseStep 5467409 = 4100557) B4100557
theorem B1076503 : Blo 956588 1076503 := bstep (se 1 (by rfl) ⟨807377, by rfl⟩ : syracuseStep 1076503 = 1614755) B1614755
theorem B1436951 : Blo 956588 1436951 := bstep (se 1 (by rfl) ⟨1077713, by rfl⟩ : syracuseStep 1436951 = 2155427) B2155427
theorem B2157875 : Blo 956588 2157875 := bstep (se 1 (by rfl) ⟨1618406, by rfl⟩ : syracuseStep 2157875 = 3236813) B3236813
theorem B3239243 : Blo 956588 3239243 := bstep (se 1 (by rfl) ⟨2429432, by rfl⟩ : syracuseStep 3239243 = 4858865) B4858865
theorem B2157911 : Blo 956588 2157911 := bstep (se 1 (by rfl) ⟨1618433, by rfl⟩ : syracuseStep 2157911 = 3236867) B3236867
theorem B1437017 : Blo 956588 1437017 := bstep (se 2 (by rfl) ⟨538881, by rfl⟩ : syracuseStep 1437017 = 1077763) B1077763
theorem B1076683 : Blo 956588 1076683 := bstep (se 1 (by rfl) ⟨807512, by rfl⟩ : syracuseStep 1076683 = 1615025) B1615025
theorem B1437131 : Blo 956588 1437131 := bstep (se 1 (by rfl) ⟨1077848, by rfl⟩ : syracuseStep 1437131 = 2155697) B2155697
theorem B1437143 : Blo 956588 1437143 := bstep (se 1 (by rfl) ⟨1077857, by rfl⟩ : syracuseStep 1437143 = 2155715) B2155715
theorem B1994201 : Blo 956588 1994201 := bstep (se 2 (by rfl) ⟨747825, by rfl⟩ : syracuseStep 1994201 = 1495651) B1495651
theorem B6909401 : Blo 956588 6909401 := bstep (se 2 (by rfl) ⟨2591025, by rfl⟩ : syracuseStep 6909401 = 5182051) B5182051
theorem B2158091 : Blo 956588 2158091 := bstep (se 1 (by rfl) ⟨1618568, by rfl⟩ : syracuseStep 2158091 = 3237137) B3237137
theorem B1437209 : Blo 956588 1437209 := bstep (se 2 (by rfl) ⟨538953, by rfl⟩ : syracuseStep 1437209 = 1077907) B1077907
theorem B1076791 : Blo 956588 1076791 := bstep (se 1 (by rfl) ⟨807593, by rfl⟩ : syracuseStep 1076791 = 1615187) B1615187
theorem B2158145 : Blo 956588 2158145 := bstep (se 2 (by rfl) ⟨809304, by rfl⟩ : syracuseStep 2158145 = 1618609) B1618609
theorem B4091467 : Blo 956588 4091467 := bstep (se 1 (by rfl) ⟨3068600, by rfl⟩ : syracuseStep 4091467 = 6137201) B6137201
theorem B3239513 : Blo 956588 3239513 := bstep (se 2 (by rfl) ⟨1214817, by rfl⟩ : syracuseStep 3239513 = 2429635) B2429635
theorem B1437323 : Blo 956588 1437323 := bstep (se 1 (by rfl) ⟨1077992, by rfl⟩ : syracuseStep 1437323 = 2155985) B2155985
theorem B1437335 : Blo 956588 1437335 := bstep (se 1 (by rfl) ⟨1078001, by rfl⟩ : syracuseStep 1437335 = 2156003) B2156003
theorem B1437401 : Blo 956588 1437401 := bstep (se 2 (by rfl) ⟨539025, by rfl⟩ : syracuseStep 1437401 = 1078051) B1078051
theorem B1076971 : Blo 956588 1076971 := bstep (se 1 (by rfl) ⟨807728, by rfl⟩ : syracuseStep 1076971 = 1615457) B1615457
theorem B2158361 : Blo 956588 2158361 := bstep (se 2 (by rfl) ⟨809385, by rfl⟩ : syracuseStep 2158361 = 1618771) B1618771
theorem B3632971 : Blo 956588 3632971 := bstep (se 1 (by rfl) ⟨2724728, by rfl⟩ : syracuseStep 3632971 = 5449457) B5449457
theorem B1437515 : Blo 956588 1437515 := bstep (se 1 (by rfl) ⟨1078136, by rfl⟩ : syracuseStep 1437515 = 2156273) B2156273
theorem B1077079 : Blo 956588 1077079 := bstep (se 1 (by rfl) ⟨807809, by rfl⟩ : syracuseStep 1077079 = 1615619) B1615619
theorem B1437527 : Blo 956588 1437527 := bstep (se 1 (by rfl) ⟨1078145, by rfl⟩ : syracuseStep 1437527 = 2156291) B2156291
theorem B3108701 : Blo 956588 3108701 := bstep (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) B1165763
theorem B4091741 : Blo 956588 4091741 := bstep (se 3 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 4091741 = 1534403) B1534403
theorem B2158451 : Blo 956588 2158451 := bstep (se 1 (by rfl) ⟨1618838, by rfl⟩ : syracuseStep 2158451 = 3237677) B3237677
theorem B2158487 : Blo 956588 2158487 := bstep (se 1 (by rfl) ⟨1618865, by rfl⟩ : syracuseStep 2158487 = 3237731) B3237731
theorem B1437593 : Blo 956588 1437593 := bstep (se 2 (by rfl) ⟨539097, by rfl⟩ : syracuseStep 1437593 = 1078195) B1078195
theorem B1077259 : Blo 956588 1077259 := bstep (se 1 (by rfl) ⟨807944, by rfl⟩ : syracuseStep 1077259 = 1615889) B1615889
theorem B1437707 : Blo 956588 1437707 := bstep (se 1 (by rfl) ⟨1078280, by rfl⟩ : syracuseStep 1437707 = 2156561) B2156561
theorem B1437719 : Blo 956588 1437719 := bstep (se 1 (by rfl) ⟨1078289, by rfl⟩ : syracuseStep 1437719 = 2156579) B2156579
theorem B2158667 : Blo 956588 2158667 := bstep (se 1 (by rfl) ⟨1619000, by rfl⟩ : syracuseStep 2158667 = 3238001) B3238001
theorem B1437785 : Blo 956588 1437785 := bstep (se 2 (by rfl) ⟨539169, by rfl⟩ : syracuseStep 1437785 = 1078339) B1078339
theorem B3633245 : Blo 956588 3633245 := bstep (se 3 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 3633245 = 1362467) B1362467
theorem B1077367 : Blo 956588 1077367 := bstep (se 1 (by rfl) ⟨808025, by rfl⟩ : syracuseStep 1077367 = 1616051) B1616051
theorem B2158721 : Blo 956588 2158721 := bstep (se 2 (by rfl) ⟨809520, by rfl⟩ : syracuseStep 2158721 = 1619041) B1619041
theorem B4092083 : Blo 956588 4092083 := bstep (se 1 (by rfl) ⟨3069062, by rfl⟩ : syracuseStep 4092083 = 6138125) B6138125
theorem B1437899 : Blo 956588 1437899 := bstep (se 1 (by rfl) ⟨1078424, by rfl⟩ : syracuseStep 1437899 = 2156849) B2156849
theorem B1437911 : Blo 956588 1437911 := bstep (se 1 (by rfl) ⟨1078433, by rfl⟩ : syracuseStep 1437911 = 2156867) B2156867
theorem B3240215 : Blo 956588 3240215 := bstep (se 1 (by rfl) ⟨2430161, by rfl⟩ : syracuseStep 3240215 = 4860323) B4860323
theorem B1437977 : Blo 956588 1437977 := bstep (se 2 (by rfl) ⟨539241, by rfl⟩ : syracuseStep 1437977 = 1078483) B1078483
theorem B1077547 : Blo 956588 1077547 := bstep (se 1 (by rfl) ⟨808160, by rfl⟩ : syracuseStep 1077547 = 1616321) B1616321
theorem B2158937 : Blo 956588 2158937 := bstep (se 2 (by rfl) ⟨809601, by rfl⟩ : syracuseStep 2158937 = 1619203) B1619203
theorem B1438091 : Blo 956588 1438091 := bstep (se 1 (by rfl) ⟨1078568, by rfl⟩ : syracuseStep 1438091 = 2157137) B2157137
theorem B1077655 : Blo 956588 1077655 := bstep (se 1 (by rfl) ⟨808241, by rfl⟩ : syracuseStep 1077655 = 1616483) B1616483
theorem B1438103 : Blo 956588 1438103 := bstep (se 1 (by rfl) ⟨1078577, by rfl⟩ : syracuseStep 1438103 = 2157155) B2157155
theorem B2159027 : Blo 956588 2159027 := bstep (se 1 (by rfl) ⟨1619270, by rfl⟩ : syracuseStep 2159027 = 3238541) B3238541
theorem B2159063 : Blo 956588 2159063 := bstep (se 1 (by rfl) ⟨1619297, by rfl⟩ : syracuseStep 2159063 = 3238595) B3238595
theorem B1438169 : Blo 956588 1438169 := bstep (se 2 (by rfl) ⟨539313, by rfl⟩ : syracuseStep 1438169 = 1078627) B1078627
theorem B1077835 : Blo 956588 1077835 := bstep (se 1 (by rfl) ⟨808376, by rfl⟩ : syracuseStep 1077835 = 1616753) B1616753
theorem B1438283 : Blo 956588 1438283 := bstep (se 1 (by rfl) ⟨1078712, by rfl⟩ : syracuseStep 1438283 = 2157425) B2157425
theorem B1438295 : Blo 956588 1438295 := bstep (se 1 (by rfl) ⟨1078721, by rfl⟩ : syracuseStep 1438295 = 2157443) B2157443
theorem B2159243 : Blo 956588 2159243 := bstep (se 1 (by rfl) ⟨1619432, by rfl⟩ : syracuseStep 2159243 = 3238865) B3238865
theorem B1438361 : Blo 956588 1438361 := bstep (se 2 (by rfl) ⟨539385, by rfl⟩ : syracuseStep 1438361 = 1078771) B1078771
theorem B1077943 : Blo 956588 1077943 := bstep (se 1 (by rfl) ⟨808457, by rfl⟩ : syracuseStep 1077943 = 1616915) B1616915
theorem B2159297 : Blo 956588 2159297 := bstep (se 2 (by rfl) ⟨809736, by rfl⟩ : syracuseStep 2159297 = 1619473) B1619473
theorem B3076829 : Blo 956588 3076829 := bstep (se 3 (by rfl) ⟨576905, by rfl⟩ : syracuseStep 3076829 = 1153811) B1153811
theorem B1438475 : Blo 956588 1438475 := bstep (se 1 (by rfl) ⟨1078856, by rfl⟩ : syracuseStep 1438475 = 2157713) B2157713
theorem B3633943 : Blo 956588 3633943 := bstep (se 1 (by rfl) ⟨2725457, by rfl⟩ : syracuseStep 3633943 = 5450915) B5450915
theorem B1438487 : Blo 956588 1438487 := bstep (se 1 (by rfl) ⟨1078865, by rfl⟩ : syracuseStep 1438487 = 2157731) B2157731
theorem B3240755 : Blo 956588 3240755 := bstep (se 1 (by rfl) ⟨2430566, by rfl⟩ : syracuseStep 3240755 = 4861133) B4861133
theorem B1438553 : Blo 956588 1438553 := bstep (se 2 (by rfl) ⟨539457, by rfl⟩ : syracuseStep 1438553 = 1078915) B1078915
theorem B1078123 : Blo 956588 1078123 := bstep (se 1 (by rfl) ⟨808592, by rfl⟩ : syracuseStep 1078123 = 1617185) B1617185
theorem B2159513 : Blo 956588 2159513 := bstep (se 2 (by rfl) ⟨809817, by rfl⟩ : syracuseStep 2159513 = 1619635) B1619635
theorem B2421697 : Blo 956588 2421697 := bstep (se 2 (by rfl) ⟨908136, by rfl⟩ : syracuseStep 2421697 = 1816273) B1816273
theorem B1438667 : Blo 956588 1438667 := bstep (se 1 (by rfl) ⟨1079000, by rfl⟩ : syracuseStep 1438667 = 2158001) B2158001
theorem B1078231 : Blo 956588 1078231 := bstep (se 1 (by rfl) ⟨808673, by rfl⟩ : syracuseStep 1078231 = 1617347) B1617347
theorem B1438679 : Blo 956588 1438679 := bstep (se 1 (by rfl) ⟨1079009, by rfl⟩ : syracuseStep 1438679 = 2158019) B2158019
theorem B4846553 : Blo 956588 4846553 := bstep (se 2 (by rfl) ⟨1817457, by rfl⟩ : syracuseStep 4846553 = 3634915) B3634915
theorem B2159603 : Blo 956588 2159603 := bstep (se 1 (by rfl) ⟨1619702, by rfl⟩ : syracuseStep 2159603 = 3239405) B3239405
theorem B2159639 : Blo 956588 2159639 := bstep (se 1 (by rfl) ⟨1619729, by rfl⟩ : syracuseStep 2159639 = 3239459) B3239459
theorem B1438745 : Blo 956588 1438745 := bstep (se 2 (by rfl) ⟨539529, by rfl⟩ : syracuseStep 1438745 = 1079059) B1079059
theorem B6911041 : Blo 956588 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B3241025 : Blo 956588 3241025 := bstep (se 2 (by rfl) ⟨1215384, by rfl⟩ : syracuseStep 3241025 = 2430769) B2430769
theorem B1078411 : Blo 956588 1078411 := bstep (se 1 (by rfl) ⟨808808, by rfl⟩ : syracuseStep 1078411 = 1617617) B1617617
theorem B1438859 : Blo 956588 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B11662487 : Blo 956588 11662487 := bstep (se 1 (by rfl) ⟨8746865, by rfl⟩ : syracuseStep 11662487 = 17493731) B17493731
theorem B1438871 : Blo 956588 1438871 := bstep (se 1 (by rfl) ⟨1079153, by rfl⟩ : syracuseStep 1438871 = 2158307) B2158307
theorem B2159819 : Blo 956588 2159819 := bstep (se 1 (by rfl) ⟨1619864, by rfl⟩ : syracuseStep 2159819 = 3239729) B3239729
theorem B1438937 : Blo 956588 1438937 := bstep (se 2 (by rfl) ⟨539601, by rfl⟩ : syracuseStep 1438937 = 1079203) B1079203
theorem B1078519 : Blo 956588 1078519 := bstep (se 1 (by rfl) ⟨808889, by rfl⟩ : syracuseStep 1078519 = 1617779) B1617779
theorem B2159873 : Blo 956588 2159873 := bstep (se 2 (by rfl) ⟨809952, by rfl⟩ : syracuseStep 2159873 = 1619905) B1619905
theorem B5174545 : Blo 956588 5174545 := bstep (se 2 (by rfl) ⟨1940454, by rfl⟩ : syracuseStep 5174545 = 3880909) B3880909
theorem B1439051 : Blo 956588 1439051 := bstep (se 1 (by rfl) ⟨1079288, by rfl⟩ : syracuseStep 1439051 = 2158577) B2158577
theorem B1439063 : Blo 956588 1439063 := bstep (se 1 (by rfl) ⟨1079297, by rfl⟩ : syracuseStep 1439063 = 2158595) B2158595
theorem B1439129 : Blo 956588 1439129 := bstep (se 2 (by rfl) ⟨539673, by rfl⟩ : syracuseStep 1439129 = 1079347) B1079347
theorem B1078699 : Blo 956588 1078699 := bstep (se 1 (by rfl) ⟨809024, by rfl⟩ : syracuseStep 1078699 = 1618049) B1618049
theorem B2160089 : Blo 956588 2160089 := bstep (se 2 (by rfl) ⟨810033, by rfl⟩ : syracuseStep 2160089 = 1620067) B1620067
theorem B1439243 : Blo 956588 1439243 := bstep (se 1 (by rfl) ⟨1079432, by rfl⟩ : syracuseStep 1439243 = 2158865) B2158865
theorem B9205265 : Blo 956588 9205265 := bstep (se 2 (by rfl) ⟨3451974, by rfl⟩ : syracuseStep 9205265 = 6903949) B6903949
theorem B2422295 : Blo 956588 2422295 := bstep (se 1 (by rfl) ⟨1816721, by rfl⟩ : syracuseStep 2422295 = 3633443) B3633443
theorem B1078807 : Blo 956588 1078807 := bstep (se 1 (by rfl) ⟨809105, by rfl⟩ : syracuseStep 1078807 = 1618211) B1618211
theorem B1439255 : Blo 956588 1439255 := bstep (se 1 (by rfl) ⟨1079441, by rfl⟩ : syracuseStep 1439255 = 2158883) B2158883
theorem B3634733 : Blo 956588 3634733 := bstep (se 3 (by rfl) ⟨681512, by rfl⟩ : syracuseStep 3634733 = 1363025) B1363025
theorem B2160179 : Blo 956588 2160179 := bstep (se 1 (by rfl) ⟨1620134, by rfl⟩ : syracuseStep 2160179 = 3240269) B3240269
theorem B2160215 : Blo 956588 2160215 := bstep (se 1 (by rfl) ⟨1620161, by rfl⟩ : syracuseStep 2160215 = 3240323) B3240323
theorem B1439321 : Blo 956588 1439321 := bstep (se 2 (by rfl) ⟨539745, by rfl⟩ : syracuseStep 1439321 = 1079491) B1079491
theorem B3241565 : Blo 956588 3241565 := bstep (se 3 (by rfl) ⟨607793, by rfl⟩ : syracuseStep 3241565 = 1215587) B1215587
theorem B1078987 : Blo 956588 1078987 := bstep (se 1 (by rfl) ⟨809240, by rfl⟩ : syracuseStep 1078987 = 1618481) B1618481
theorem B1439435 : Blo 956588 1439435 := bstep (se 1 (by rfl) ⟨1079576, by rfl⟩ : syracuseStep 1439435 = 2159153) B2159153
theorem B1439447 : Blo 956588 1439447 := bstep (se 1 (by rfl) ⟨1079585, by rfl⟩ : syracuseStep 1439447 = 2159171) B2159171
theorem B2160395 : Blo 956588 2160395 := bstep (se 1 (by rfl) ⟨1620296, by rfl⟩ : syracuseStep 2160395 = 3240593) B3240593
theorem B1439513 : Blo 956588 1439513 := bstep (se 2 (by rfl) ⟨539817, by rfl⟩ : syracuseStep 1439513 = 1079635) B1079635
theorem B1079095 : Blo 956588 1079095 := bstep (se 1 (by rfl) ⟨809321, by rfl⟩ : syracuseStep 1079095 = 1618643) B1618643
theorem B2160449 : Blo 956588 2160449 := bstep (se 2 (by rfl) ⟨810168, by rfl⟩ : syracuseStep 2160449 = 1620337) B1620337
theorem B17495909 : Blo 956588 17495909 := bstep (se 4 (by rfl) ⟨1640241, by rfl⟩ : syracuseStep 17495909 = 3280483) B3280483
theorem B1439627 : Blo 956588 1439627 := bstep (se 1 (by rfl) ⟨1079720, by rfl⟩ : syracuseStep 1439627 = 2159441) B2159441
theorem B149157773 : Blo 956588 149157773 := bstep (se 3 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 149157773 = 55934165) B55934165
theorem B1439639 : Blo 956588 1439639 := bstep (se 1 (by rfl) ⟨1079729, by rfl⟩ : syracuseStep 1439639 = 2159459) B2159459
theorem B1439705 : Blo 956588 1439705 := bstep (se 2 (by rfl) ⟨539889, by rfl⟩ : syracuseStep 1439705 = 1079779) B1079779
theorem B1079275 : Blo 956588 1079275 := bstep (se 1 (by rfl) ⟨809456, by rfl⟩ : syracuseStep 1079275 = 1618913) B1618913
theorem B2160665 : Blo 956588 2160665 := bstep (se 2 (by rfl) ⟨810249, by rfl⟩ : syracuseStep 2160665 = 1620499) B1620499
theorem B1439819 : Blo 956588 1439819 := bstep (se 1 (by rfl) ⟨1079864, by rfl⟩ : syracuseStep 1439819 = 2159729) B2159729
theorem B1079383 : Blo 956588 1079383 := bstep (se 1 (by rfl) ⟨809537, by rfl⟩ : syracuseStep 1079383 = 1619075) B1619075
theorem B1439831 : Blo 956588 1439831 := bstep (se 1 (by rfl) ⟨1079873, by rfl⟩ : syracuseStep 1439831 = 2159747) B2159747
theorem B2160755 : Blo 956588 2160755 := bstep (se 1 (by rfl) ⟨1620566, by rfl⟩ : syracuseStep 2160755 = 3241133) B3241133
theorem B2160791 : Blo 956588 2160791 := bstep (se 1 (by rfl) ⟨1620593, by rfl⟩ : syracuseStep 2160791 = 3241187) B3241187
theorem B1439897 : Blo 956588 1439897 := bstep (se 2 (by rfl) ⟨539961, by rfl⟩ : syracuseStep 1439897 = 1079923) B1079923
theorem B3274931 : Blo 956588 3274931 := bstep (se 1 (by rfl) ⟨2456198, by rfl⟩ : syracuseStep 3274931 = 4912397) B4912397
theorem B1079563 : Blo 956588 1079563 := bstep (se 1 (by rfl) ⟨809672, by rfl⟩ : syracuseStep 1079563 = 1619345) B1619345
theorem B1440011 : Blo 956588 1440011 := bstep (se 1 (by rfl) ⟨1080008, by rfl⟩ : syracuseStep 1440011 = 2160017) B2160017
theorem B1440023 : Blo 956588 1440023 := bstep (se 1 (by rfl) ⟨1080017, by rfl⟩ : syracuseStep 1440023 = 2160035) B2160035
theorem B2423105 : Blo 956588 2423105 := bstep (se 2 (by rfl) ⟨908664, by rfl⟩ : syracuseStep 2423105 = 1817329) B1817329
theorem B2160971 : Blo 956588 2160971 := bstep (se 1 (by rfl) ⟨1620728, by rfl⟩ : syracuseStep 2160971 = 3241457) B3241457
theorem B1440089 : Blo 956588 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B1079671 : Blo 956588 1079671 := bstep (se 1 (by rfl) ⟨809753, by rfl⟩ : syracuseStep 1079671 = 1619507) B1619507
theorem B2161025 : Blo 956588 2161025 := bstep (se 2 (by rfl) ⟨810384, by rfl⟩ : syracuseStep 2161025 = 1620769) B1620769
theorem B1440203 : Blo 956588 1440203 := bstep (se 1 (by rfl) ⟨1080152, by rfl⟩ : syracuseStep 1440203 = 2160305) B2160305
theorem B1440215 : Blo 956588 1440215 := bstep (se 1 (by rfl) ⟨1080161, by rfl⟩ : syracuseStep 1440215 = 2160323) B2160323
theorem B1440281 : Blo 956588 1440281 := bstep (se 2 (by rfl) ⟨540105, by rfl⟩ : syracuseStep 1440281 = 1080211) B1080211
theorem B1079851 : Blo 956588 1079851 := bstep (se 1 (by rfl) ⟨809888, by rfl⟩ : syracuseStep 1079851 = 1619777) B1619777
theorem B4848173 : Blo 956588 4848173 := bstep (se 3 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 4848173 = 1818065) B1818065
theorem B4094509 : Blo 956588 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B2587187 : Blo 956588 2587187 := bstep (se 1 (by rfl) ⟨1940390, by rfl⟩ : syracuseStep 2587187 = 3880781) B3880781
theorem B2161241 : Blo 956588 2161241 := bstep (se 2 (by rfl) ⟨810465, by rfl⟩ : syracuseStep 2161241 = 1620931) B1620931
theorem B8190557 : Blo 956588 8190557 := bstep (se 3 (by rfl) ⟨1535729, by rfl⟩ : syracuseStep 8190557 = 3071459) B3071459
theorem B1440395 : Blo 956588 1440395 := bstep (se 1 (by rfl) ⟨1080296, by rfl⟩ : syracuseStep 1440395 = 2160593) B2160593
theorem B1079959 : Blo 956588 1079959 := bstep (se 1 (by rfl) ⟨809969, by rfl⟩ : syracuseStep 1079959 = 1619939) B1619939
theorem B1440407 : Blo 956588 1440407 := bstep (se 1 (by rfl) ⟨1080305, by rfl⟩ : syracuseStep 1440407 = 2160611) B2160611
theorem B1440473 : Blo 956588 1440473 := bstep (se 2 (by rfl) ⟨540177, by rfl⟩ : syracuseStep 1440473 = 1080355) B1080355
theorem B10353413 : Blo 956588 10353413 := bstep (se 4 (by rfl) ⟨970632, by rfl⟩ : syracuseStep 10353413 = 1941265) B1941265
theorem B6912773 : Blo 956588 6912773 := bstep (se 4 (by rfl) ⟨648072, by rfl⟩ : syracuseStep 6912773 = 1296145) B1296145
theorem B1080139 : Blo 956588 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B1440587 : Blo 956588 1440587 := bstep (se 1 (by rfl) ⟨1080440, by rfl⟩ : syracuseStep 1440587 = 2160881) B2160881
theorem B1440599 : Blo 956588 1440599 := bstep (se 1 (by rfl) ⟨1080449, by rfl⟩ : syracuseStep 1440599 = 2160899) B2160899
theorem B2423641 : Blo 956588 2423641 := bstep (se 2 (by rfl) ⟨908865, by rfl⟩ : syracuseStep 2423641 = 1817731) B1817731
theorem B1440665 : Blo 956588 1440665 := bstep (se 2 (by rfl) ⟨540249, by rfl⟩ : syracuseStep 1440665 = 1080499) B1080499
theorem B1080247 : Blo 956588 1080247 := bstep (se 1 (by rfl) ⟨810185, by rfl⟩ : syracuseStep 1080247 = 1620371) B1620371
theorem B3636161 : Blo 956588 3636161 := bstep (se 2 (by rfl) ⟨1363560, by rfl⟩ : syracuseStep 3636161 = 2727121) B2727121
theorem B1440779 : Blo 956588 1440779 := bstep (se 1 (by rfl) ⟨1080584, by rfl⟩ : syracuseStep 1440779 = 2161169) B2161169
theorem B1440791 : Blo 956588 1440791 := bstep (se 1 (by rfl) ⟨1080593, by rfl⟩ : syracuseStep 1440791 = 2161187) B2161187
theorem B1440857 : Blo 956588 1440857 := bstep (se 2 (by rfl) ⟨540321, by rfl⟩ : syracuseStep 1440857 = 1080643) B1080643
theorem B1080427 : Blo 956588 1080427 := bstep (se 1 (by rfl) ⟨810320, by rfl⟩ : syracuseStep 1080427 = 1620641) B1620641
theorem B1080535 : Blo 956588 1080535 := bstep (se 1 (by rfl) ⟨810401, by rfl⟩ : syracuseStep 1080535 = 1620803) B1620803
theorem B1211851 : Blo 956588 1211851 := bstep (se 1 (by rfl) ⟨908888, by rfl⟩ : syracuseStep 1211851 = 1817777) B1817777
theorem B2588183 : Blo 956588 2588183 := bstep (se 1 (by rfl) ⟨1941137, by rfl⟩ : syracuseStep 2588183 = 3882275) B3882275
theorem B2588311 : Blo 956588 2588311 := bstep (se 1 (by rfl) ⟨1941233, by rfl⟩ : syracuseStep 2588311 = 3882467) B3882467
theorem B2424755 : Blo 956588 2424755 := bstep (se 1 (by rfl) ⟨1818566, by rfl⟩ : syracuseStep 2424755 = 3637133) B3637133
theorem B23298293 : Blo 956588 23298293 := bstep (se 5 (by rfl) ⟨1092107, by rfl⟩ : syracuseStep 23298293 = 2184215) B2184215
theorem B2425099 : Blo 956588 2425099 := bstep (se 1 (by rfl) ⟨1818824, by rfl⟩ : syracuseStep 2425099 = 3637649) B3637649
theorem B3637619 : Blo 956588 3637619 := bstep (se 1 (by rfl) ⟨2728214, by rfl⟩ : syracuseStep 3637619 = 5456429) B5456429
theorem B2589047 : Blo 956588 2589047 := bstep (se 1 (by rfl) ⟨1941785, by rfl⟩ : syracuseStep 2589047 = 3883571) B3883571
theorem B2425241 : Blo 956588 2425241 := bstep (se 2 (by rfl) ⟨909465, by rfl⟩ : syracuseStep 2425241 = 1818931) B1818931
theorem B2490895 : Blo 956588 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B2425403 : Blo 956588 2425403 := bstep (se 1 (by rfl) ⟨1819052, by rfl⟩ : syracuseStep 2425403 = 3638105) B3638105
theorem B4915799 : Blo 956588 4915799 := bstep (se 1 (by rfl) ⟨3686849, by rfl⟩ : syracuseStep 4915799 = 7373699) B7373699
theorem B1213319 : Blo 956588 1213319 := bstep (se 1 (by rfl) ⟨909989, by rfl⟩ : syracuseStep 1213319 = 1819979) B1819979
theorem B2425747 : Blo 956588 2425747 := bstep (se 1 (by rfl) ⟨1819310, by rfl⟩ : syracuseStep 2425747 = 3638621) B3638621
theorem B9208727 : Blo 956588 9208727 := bstep (se 1 (by rfl) ⟨6906545, by rfl⟩ : syracuseStep 9208727 = 13813091) B13813091
theorem B2425889 : Blo 956588 2425889 := bstep (se 2 (by rfl) ⟨909708, by rfl⟩ : syracuseStep 2425889 = 1819417) B1819417
theorem B2589815 : Blo 956588 2589815 := bstep (se 1 (by rfl) ⟨1942361, by rfl⟩ : syracuseStep 2589815 = 3884723) B3884723
theorem B2917691 : Blo 956588 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B4851089 : Blo 956588 4851089 := bstep (se 2 (by rfl) ⟨1819158, by rfl⟩ : syracuseStep 4851089 = 3638317) B3638317
theorem B1213967 : Blo 956588 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B13830041 : Blo 956588 13830041 := bstep (se 2 (by rfl) ⟨5186265, by rfl⟩ : syracuseStep 13830041 = 10372531) B10372531
theorem B2426881 : Blo 956588 2426881 := bstep (se 2 (by rfl) ⟨910080, by rfl⟩ : syracuseStep 2426881 = 1820161) B1820161
theorem B10520621 : Blo 956588 10520621 := bstep (se 3 (by rfl) ⟨1972616, by rfl⟩ : syracuseStep 10520621 = 3945233) B3945233
theorem B9832913 : Blo 956588 9832913 := bstep (se 2 (by rfl) ⟨3687342, by rfl⟩ : syracuseStep 9832913 = 7374685) B7374685
theorem B3639761 : Blo 956588 3639761 := bstep (se 2 (by rfl) ⟨1364910, by rfl⟩ : syracuseStep 3639761 = 2729821) B2729821
theorem B21629405 : Blo 956588 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B2427479 : Blo 956588 2427479 := bstep (se 1 (by rfl) ⟨1820609, by rfl⟩ : syracuseStep 2427479 = 3641219) B3641219
theorem B33163895 : Blo 956588 33163895 := bstep (se 1 (by rfl) ⟨24872921, by rfl⟩ : syracuseStep 33163895 = 49745843) B49745843
theorem B3640079 : Blo 956588 3640079 := bstep (se 1 (by rfl) ⟨2730059, by rfl⟩ : syracuseStep 3640079 = 5460119) B5460119
theorem B2919197 : Blo 956588 2919197 := bstep (se 3 (by rfl) ⟨547349, by rfl⟩ : syracuseStep 2919197 = 1094699) B1094699
theorem B2427691 : Blo 956588 2427691 := bstep (se 1 (by rfl) ⟨1820768, by rfl⟩ : syracuseStep 2427691 = 3641537) B3641537
theorem B7277363 : Blo 956588 7277363 := bstep (se 1 (by rfl) ⟨5458022, by rfl⟩ : syracuseStep 7277363 = 10916045) B10916045
theorem B8194931 : Blo 956588 8194931 := bstep (se 1 (by rfl) ⟨6146198, by rfl⟩ : syracuseStep 8194931 = 12292397) B12292397
theorem B2427833 : Blo 956588 2427833 := bstep (se 2 (by rfl) ⟨910437, by rfl⟩ : syracuseStep 2427833 = 1820875) B1820875
theorem B1149995 : Blo 956588 1149995 := bstep (se 1 (by rfl) ⟨862496, by rfl⟩ : syracuseStep 1149995 = 1724993) B1724993
theorem B2919577 : Blo 956588 2919577 := bstep (se 2 (by rfl) ⟨1094841, by rfl⟩ : syracuseStep 2919577 = 2189683) B2189683
theorem B986375 : Blo 956588 986375 := bstep (se 1 (by rfl) ⟨739781, by rfl⟩ : syracuseStep 986375 = 1479563) B1479563
theorem B4984199 : Blo 956588 4984199 := bstep (se 1 (by rfl) ⟨3738149, by rfl⟩ : syracuseStep 4984199 = 7476299) B7476299
theorem B4853195 : Blo 956588 4853195 := bstep (se 1 (by rfl) ⟨3639896, by rfl⟩ : syracuseStep 4853195 = 7279793) B7279793
theorem B6131153 : Blo 956588 6131153 := bstep (se 2 (by rfl) ⟨2299182, by rfl⟩ : syracuseStep 6131153 = 4598365) B4598365
theorem B6229457 : Blo 956588 6229457 := bstep (se 2 (by rfl) ⟨2336046, by rfl⟩ : syracuseStep 6229457 = 4672093) B4672093
theorem B3739337 : Blo 956588 3739337 := bstep (se 2 (by rfl) ⟨1402251, by rfl⟩ : syracuseStep 3739337 = 2804503) B2804503
theorem B4099841 : Blo 956588 4099841 := bstep (se 2 (by rfl) ⟨1537440, by rfl⟩ : syracuseStep 4099841 = 3074881) B3074881
theorem B4853519 : Blo 956588 4853519 := bstep (se 1 (by rfl) ⟨3640139, by rfl⟩ : syracuseStep 4853519 = 7280279) B7280279
theorem B2428825 : Blo 956588 2428825 := bstep (se 2 (by rfl) ⟨910809, by rfl⟩ : syracuseStep 2428825 = 1821619) B1821619
theorem B2428987 : Blo 956588 2428987 := bstep (se 1 (by rfl) ⟨1821740, by rfl⟩ : syracuseStep 2428987 = 3643481) B3643481
theorem B4100215 : Blo 956588 4100215 := bstep (se 1 (by rfl) ⟨3075161, by rfl⟩ : syracuseStep 4100215 = 6150323) B6150323
theorem B2429129 : Blo 956588 2429129 := bstep (se 2 (by rfl) ⟨910923, by rfl⟩ : syracuseStep 2429129 = 1821847) B1821847
theorem B20713745 : Blo 956588 20713745 := bstep (se 2 (by rfl) ⟨7767654, by rfl⟩ : syracuseStep 20713745 = 15535309) B15535309
theorem B2429473 : Blo 956588 2429473 := bstep (se 2 (by rfl) ⟨911052, by rfl⟩ : syracuseStep 2429473 = 1822105) B1822105
theorem B9212723 : Blo 956588 9212723 := bstep (se 1 (by rfl) ⟨6909542, by rfl⟩ : syracuseStep 9212723 = 13819085) B13819085
theorem B2626561 : Blo 956588 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B2430071 : Blo 956588 2430071 := bstep (se 1 (by rfl) ⟨1822553, by rfl⟩ : syracuseStep 2430071 = 3645107) B3645107
theorem B4854977 : Blo 956588 4854977 := bstep (se 2 (by rfl) ⟨1820616, by rfl⟩ : syracuseStep 4854977 = 3641233) B3641233
theorem B1152263 : Blo 956588 1152263 := bstep (se 1 (by rfl) ⟨864197, by rfl⟩ : syracuseStep 1152263 = 1728395) B1728395
theorem B2299337 : Blo 956588 2299337 := bstep (se 2 (by rfl) ⟨862251, by rfl⟩ : syracuseStep 2299337 = 1724503) B1724503
theorem B2725321 : Blo 956588 2725321 := bstep (se 2 (by rfl) ⟨1021995, by rfl⟩ : syracuseStep 2725321 = 2043991) B2043991
theorem B1152571 : Blo 956588 1152571 := bstep (se 1 (by rfl) ⟨864428, by rfl⟩ : syracuseStep 1152571 = 1728857) B1728857
theorem B2332307 : Blo 956588 2332307 := bstep (se 1 (by rfl) ⟨1749230, by rfl⟩ : syracuseStep 2332307 = 3498461) B3498461
theorem B1152811 : Blo 956588 1152811 := bstep (se 1 (by rfl) ⟨864608, by rfl⟩ : syracuseStep 1152811 = 1729217) B1729217
theorem B4986845 : Blo 956588 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B956603 : Blo 956588 956603 := bstep (se 1 (by rfl) ⟨717452, by rfl⟩ : syracuseStep 956603 = 1434905) B1434905
theorem B3643649 : Blo 956588 3643649 := bstep (se 2 (by rfl) ⟨1366368, by rfl⟩ : syracuseStep 3643649 = 2732737) B2732737
theorem B956679 : Blo 956588 956679 := bstep (se 1 (by rfl) ⟨717509, by rfl⟩ : syracuseStep 956679 = 1435019) B1435019
theorem B956687 : Blo 956588 956687 := bstep (se 1 (by rfl) ⟨717515, by rfl⟩ : syracuseStep 956687 = 1435031) B1435031
theorem B3643663 : Blo 956588 3643663 := bstep (se 1 (by rfl) ⟨2732747, by rfl⟩ : syracuseStep 3643663 = 5465495) B5465495
theorem B956731 : Blo 956588 956731 := bstep (se 1 (by rfl) ⟨717548, by rfl⟩ : syracuseStep 956731 = 1435097) B1435097
theorem B956807 : Blo 956588 956807 := bstep (se 1 (by rfl) ⟨717605, by rfl⟩ : syracuseStep 956807 = 1435211) B1435211
theorem B2431367 : Blo 956588 2431367 := bstep (se 1 (by rfl) ⟨1823525, by rfl⟩ : syracuseStep 2431367 = 3647051) B3647051
theorem B956815 : Blo 956588 956815 := bstep (se 1 (by rfl) ⟨717611, by rfl⟩ : syracuseStep 956815 = 1435223) B1435223
theorem B2431417 : Blo 956588 2431417 := bstep (se 2 (by rfl) ⟨911781, by rfl⟩ : syracuseStep 2431417 = 1823563) B1823563
theorem B956859 : Blo 956588 956859 := bstep (se 1 (by rfl) ⟨717644, by rfl⟩ : syracuseStep 956859 = 1435289) B1435289
theorem B4856273 : Blo 956588 4856273 := bstep (se 2 (by rfl) ⟨1821102, by rfl⟩ : syracuseStep 4856273 = 3642205) B3642205
theorem B19470833 : Blo 956588 19470833 := bstep (se 2 (by rfl) ⟨7301562, by rfl⟩ : syracuseStep 19470833 = 14603125) B14603125
theorem B956935 : Blo 956588 956935 := bstep (se 1 (by rfl) ⟨717701, by rfl⟩ : syracuseStep 956935 = 1435403) B1435403
theorem B956943 : Blo 956588 956943 := bstep (se 1 (by rfl) ⟨717707, by rfl⟩ : syracuseStep 956943 = 1435415) B1435415
theorem B956987 : Blo 956588 956987 := bstep (se 1 (by rfl) ⟨717740, by rfl⟩ : syracuseStep 956987 = 1435481) B1435481
theorem B957063 : Blo 956588 957063 := bstep (se 1 (by rfl) ⟨717797, by rfl⟩ : syracuseStep 957063 = 1435595) B1435595
theorem B957071 : Blo 956588 957071 := bstep (se 1 (by rfl) ⟨717803, by rfl⟩ : syracuseStep 957071 = 1435607) B1435607
theorem B957115 : Blo 956588 957115 := bstep (se 1 (by rfl) ⟨717836, by rfl⟩ : syracuseStep 957115 = 1435673) B1435673
theorem B9214721 : Blo 956588 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B957191 : Blo 956588 957191 := bstep (se 1 (by rfl) ⟨717893, by rfl⟩ : syracuseStep 957191 = 1435787) B1435787
theorem B957199 : Blo 956588 957199 := bstep (se 1 (by rfl) ⟨717899, by rfl⟩ : syracuseStep 957199 = 1435799) B1435799
theorem B8198927 : Blo 956588 8198927 := bstep (se 1 (by rfl) ⟨6149195, by rfl⟩ : syracuseStep 8198927 = 12298391) B12298391
theorem B957243 : Blo 956588 957243 := bstep (se 1 (by rfl) ⟨717932, by rfl⟩ : syracuseStep 957243 = 1435865) B1435865
theorem B957319 : Blo 956588 957319 := bstep (se 1 (by rfl) ⟨717989, by rfl⟩ : syracuseStep 957319 = 1435979) B1435979
theorem B957327 : Blo 956588 957327 := bstep (se 1 (by rfl) ⟨717995, by rfl⟩ : syracuseStep 957327 = 1435991) B1435991
theorem B1022863 : Blo 956588 1022863 := bstep (se 1 (by rfl) ⟨767147, by rfl⟩ : syracuseStep 1022863 = 1534295) B1534295
theorem B957371 : Blo 956588 957371 := bstep (se 1 (by rfl) ⟨718028, by rfl⟩ : syracuseStep 957371 = 1436057) B1436057
theorem B1383355 : Blo 956588 1383355 := bstep (se 1 (by rfl) ⟨1037516, by rfl⟩ : syracuseStep 1383355 = 2075033) B2075033
theorem B957447 : Blo 956588 957447 := bstep (se 1 (by rfl) ⟨718085, by rfl⟩ : syracuseStep 957447 = 1436171) B1436171
theorem B957455 : Blo 956588 957455 := bstep (se 1 (by rfl) ⟨718091, by rfl⟩ : syracuseStep 957455 = 1436183) B1436183
theorem B3447851 : Blo 956588 3447851 := bstep (se 1 (by rfl) ⟨2585888, by rfl⟩ : syracuseStep 3447851 = 5171777) B5171777
theorem B957499 : Blo 956588 957499 := bstep (se 1 (by rfl) ⟨718124, by rfl⟩ : syracuseStep 957499 = 1436249) B1436249
theorem B957575 : Blo 956588 957575 := bstep (se 1 (by rfl) ⟨718181, by rfl⟩ : syracuseStep 957575 = 1436363) B1436363
theorem B957583 : Blo 956588 957583 := bstep (se 1 (by rfl) ⟨718187, by rfl⟩ : syracuseStep 957583 = 1436375) B1436375
theorem B957627 : Blo 956588 957627 := bstep (se 1 (by rfl) ⟨718220, by rfl⟩ : syracuseStep 957627 = 1436441) B1436441
theorem B957703 : Blo 956588 957703 := bstep (se 1 (by rfl) ⟨718277, by rfl⟩ : syracuseStep 957703 = 1436555) B1436555
theorem B1023239 : Blo 956588 1023239 := bstep (se 1 (by rfl) ⟨767429, by rfl⟩ : syracuseStep 1023239 = 1534859) B1534859
theorem B2727179 : Blo 956588 2727179 := bstep (se 1 (by rfl) ⟨2045384, by rfl⟩ : syracuseStep 2727179 = 4090769) B4090769
theorem B957711 : Blo 956588 957711 := bstep (se 1 (by rfl) ⟨718283, by rfl⟩ : syracuseStep 957711 = 1436567) B1436567
theorem B957755 : Blo 956588 957755 := bstep (se 1 (by rfl) ⟨718316, by rfl⟩ : syracuseStep 957755 = 1436633) B1436633
theorem B957831 : Blo 956588 957831 := bstep (se 1 (by rfl) ⟨718373, by rfl⟩ : syracuseStep 957831 = 1436747) B1436747
theorem B957839 : Blo 956588 957839 := bstep (se 1 (by rfl) ⟨718379, by rfl⟩ : syracuseStep 957839 = 1436759) B1436759
theorem B957883 : Blo 956588 957883 := bstep (se 1 (by rfl) ⟨718412, by rfl⟩ : syracuseStep 957883 = 1436825) B1436825
theorem B957959 : Blo 956588 957959 := bstep (se 1 (by rfl) ⟨718469, by rfl⟩ : syracuseStep 957959 = 1436939) B1436939
theorem B3644939 : Blo 956588 3644939 := bstep (se 1 (by rfl) ⟨2733704, by rfl⟩ : syracuseStep 3644939 = 5467409) B5467409
theorem B957967 : Blo 956588 957967 := bstep (se 1 (by rfl) ⟨718475, by rfl⟩ : syracuseStep 957967 = 1436951) B1436951
theorem B958011 : Blo 956588 958011 := bstep (se 1 (by rfl) ⟨718508, by rfl⟩ : syracuseStep 958011 = 1437017) B1437017
theorem B958087 : Blo 956588 958087 := bstep (se 1 (by rfl) ⟨718565, by rfl⟩ : syracuseStep 958087 = 1437131) B1437131
theorem B958095 : Blo 956588 958095 := bstep (se 1 (by rfl) ⟨718571, by rfl⟩ : syracuseStep 958095 = 1437143) B1437143
theorem B958139 : Blo 956588 958139 := bstep (se 1 (by rfl) ⟨718604, by rfl⟩ : syracuseStep 958139 = 1437209) B1437209
theorem B958215 : Blo 956588 958215 := bstep (se 1 (by rfl) ⟨718661, by rfl⟩ : syracuseStep 958215 = 1437323) B1437323
theorem B958223 : Blo 956588 958223 := bstep (se 1 (by rfl) ⟨718667, by rfl⟩ : syracuseStep 958223 = 1437335) B1437335
theorem B958267 : Blo 956588 958267 := bstep (se 1 (by rfl) ⟨718700, by rfl⟩ : syracuseStep 958267 = 1437401) B1437401
theorem B958343 : Blo 956588 958343 := bstep (se 1 (by rfl) ⟨718757, by rfl⟩ : syracuseStep 958343 = 1437515) B1437515
theorem B958351 : Blo 956588 958351 := bstep (se 1 (by rfl) ⟨718763, by rfl⟩ : syracuseStep 958351 = 1437527) B1437527
theorem B2727827 : Blo 956588 2727827 := bstep (se 1 (by rfl) ⟨2045870, by rfl⟩ : syracuseStep 2727827 = 4091741) B4091741
theorem B958395 : Blo 956588 958395 := bstep (se 1 (by rfl) ⟨718796, by rfl⟩ : syracuseStep 958395 = 1437593) B1437593
theorem B958471 : Blo 956588 958471 := bstep (se 1 (by rfl) ⟨718853, by rfl⟩ : syracuseStep 958471 = 1437707) B1437707
theorem B958479 : Blo 956588 958479 := bstep (se 1 (by rfl) ⟨718859, by rfl⟩ : syracuseStep 958479 = 1437719) B1437719
theorem B958523 : Blo 956588 958523 := bstep (se 1 (by rfl) ⟨718892, by rfl⟩ : syracuseStep 958523 = 1437785) B1437785
theorem B2728055 : Blo 956588 2728055 := bstep (se 1 (by rfl) ⟨2046041, by rfl⟩ : syracuseStep 2728055 = 4092083) B4092083
theorem B958599 : Blo 956588 958599 := bstep (se 1 (by rfl) ⟨718949, by rfl⟩ : syracuseStep 958599 = 1437899) B1437899
theorem B958607 : Blo 956588 958607 := bstep (se 1 (by rfl) ⟨718955, by rfl⟩ : syracuseStep 958607 = 1437911) B1437911
theorem B958651 : Blo 956588 958651 := bstep (se 1 (by rfl) ⟨718988, by rfl⟩ : syracuseStep 958651 = 1437977) B1437977
theorem B958727 : Blo 956588 958727 := bstep (se 1 (by rfl) ⟨719045, by rfl⟩ : syracuseStep 958727 = 1438091) B1438091
theorem B958735 : Blo 956588 958735 := bstep (se 1 (by rfl) ⟨719051, by rfl⟩ : syracuseStep 958735 = 1438103) B1438103
theorem B958779 : Blo 956588 958779 := bstep (se 1 (by rfl) ⟨719084, by rfl⟩ : syracuseStep 958779 = 1438169) B1438169
theorem B958855 : Blo 956588 958855 := bstep (se 1 (by rfl) ⟨719141, by rfl⟩ : syracuseStep 958855 = 1438283) B1438283
theorem B958863 : Blo 956588 958863 := bstep (se 1 (by rfl) ⟨719147, by rfl⟩ : syracuseStep 958863 = 1438295) B1438295
theorem B3645881 : Blo 956588 3645881 := bstep (se 2 (by rfl) ⟨1367205, by rfl⟩ : syracuseStep 3645881 = 2734411) B2734411
theorem B958907 : Blo 956588 958907 := bstep (se 1 (by rfl) ⟨719180, by rfl⟩ : syracuseStep 958907 = 1438361) B1438361
theorem B4989443 : Blo 956588 4989443 := bstep (se 1 (by rfl) ⟨3742082, by rfl⟩ : syracuseStep 4989443 = 7484165) B7484165
theorem B5186051 : Blo 956588 5186051 := bstep (se 1 (by rfl) ⟨3889538, by rfl⟩ : syracuseStep 5186051 = 7779077) B7779077
theorem B958983 : Blo 956588 958983 := bstep (se 1 (by rfl) ⟨719237, by rfl⟩ : syracuseStep 958983 = 1438475) B1438475
theorem B4858379 : Blo 956588 4858379 := bstep (se 1 (by rfl) ⟨3643784, by rfl⟩ : syracuseStep 4858379 = 7287569) B7287569
theorem B958991 : Blo 956588 958991 := bstep (se 1 (by rfl) ⟨719243, by rfl⟩ : syracuseStep 958991 = 1438487) B1438487
theorem B959035 : Blo 956588 959035 := bstep (se 1 (by rfl) ⟨719276, by rfl⟩ : syracuseStep 959035 = 1438553) B1438553
theorem B959111 : Blo 956588 959111 := bstep (se 1 (by rfl) ⟨719333, by rfl⟩ : syracuseStep 959111 = 1438667) B1438667
theorem B959119 : Blo 956588 959119 := bstep (se 1 (by rfl) ⟨719339, by rfl⟩ : syracuseStep 959119 = 1438679) B1438679
theorem B4858541 : Blo 956588 4858541 := bstep (se 3 (by rfl) ⟨910976, by rfl⟩ : syracuseStep 4858541 = 1821953) B1821953
theorem B959163 : Blo 956588 959163 := bstep (se 1 (by rfl) ⟨719372, by rfl⟩ : syracuseStep 959163 = 1438745) B1438745
theorem B959239 : Blo 956588 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B7774991 : Blo 956588 7774991 := bstep (se 1 (by rfl) ⟨5831243, by rfl⟩ : syracuseStep 7774991 = 11662487) B11662487
theorem B959247 : Blo 956588 959247 := bstep (se 1 (by rfl) ⟨719435, by rfl⟩ : syracuseStep 959247 = 1438871) B1438871
theorem B14033699 : Blo 956588 14033699 := bstep (se 1 (by rfl) ⟨10525274, by rfl⟩ : syracuseStep 14033699 = 21050549) B21050549
theorem B959291 : Blo 956588 959291 := bstep (se 1 (by rfl) ⟨719468, by rfl⟩ : syracuseStep 959291 = 1438937) B1438937
theorem B1516423 : Blo 956588 1516423 := bstep (se 1 (by rfl) ⟨1137317, by rfl⟩ : syracuseStep 1516423 = 2274635) B2274635
theorem B959367 : Blo 956588 959367 := bstep (se 1 (by rfl) ⟨719525, by rfl⟩ : syracuseStep 959367 = 1439051) B1439051
theorem B959375 : Blo 956588 959375 := bstep (se 1 (by rfl) ⟨719531, by rfl⟩ : syracuseStep 959375 = 1439063) B1439063
theorem B959419 : Blo 956588 959419 := bstep (se 1 (by rfl) ⟨719564, by rfl⟩ : syracuseStep 959419 = 1439129) B1439129
theorem B5448707 : Blo 956588 5448707 := bstep (se 1 (by rfl) ⟨4086530, by rfl⟩ : syracuseStep 5448707 = 8173061) B8173061
theorem B959495 : Blo 956588 959495 := bstep (se 1 (by rfl) ⟨719621, by rfl⟩ : syracuseStep 959495 = 1439243) B1439243
theorem B6136843 : Blo 956588 6136843 := bstep (se 1 (by rfl) ⟨4602632, by rfl⟩ : syracuseStep 6136843 = 9205265) B9205265
theorem B1614863 : Blo 956588 1614863 := bstep (se 1 (by rfl) ⟨1211147, by rfl⟩ : syracuseStep 1614863 = 2422295) B2422295
theorem B959503 : Blo 956588 959503 := bstep (se 1 (by rfl) ⟨719627, by rfl⟩ : syracuseStep 959503 = 1439255) B1439255
theorem B959547 : Blo 956588 959547 := bstep (se 1 (by rfl) ⟨719660, by rfl⟩ : syracuseStep 959547 = 1439321) B1439321
theorem B18457733 : Blo 956588 18457733 := bstep (se 4 (by rfl) ⟨1730412, by rfl⟩ : syracuseStep 18457733 = 3460825) B3460825
theorem B959623 : Blo 956588 959623 := bstep (se 1 (by rfl) ⟨719717, by rfl⟩ : syracuseStep 959623 = 1439435) B1439435
theorem B959631 : Blo 956588 959631 := bstep (se 1 (by rfl) ⟨719723, by rfl⟩ : syracuseStep 959631 = 1439447) B1439447
theorem B959675 : Blo 956588 959675 := bstep (se 1 (by rfl) ⟨719756, by rfl⟩ : syracuseStep 959675 = 1439513) B1439513
theorem B959751 : Blo 956588 959751 := bstep (se 1 (by rfl) ⟨719813, by rfl⟩ : syracuseStep 959751 = 1439627) B1439627
theorem B959759 : Blo 956588 959759 := bstep (se 1 (by rfl) ⟨719819, by rfl⟩ : syracuseStep 959759 = 1439639) B1439639
theorem B959803 : Blo 956588 959803 := bstep (se 1 (by rfl) ⟨719852, by rfl⟩ : syracuseStep 959803 = 1439705) B1439705
theorem B959879 : Blo 956588 959879 := bstep (se 1 (by rfl) ⟨719909, by rfl⟩ : syracuseStep 959879 = 1439819) B1439819
theorem B959887 : Blo 956588 959887 := bstep (se 1 (by rfl) ⟨719915, by rfl⟩ : syracuseStep 959887 = 1439831) B1439831
theorem B959931 : Blo 956588 959931 := bstep (se 1 (by rfl) ⟨719948, by rfl⟩ : syracuseStep 959931 = 1439897) B1439897
theorem B2631113 : Blo 956588 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B4597195 : Blo 956588 4597195 := bstep (se 1 (by rfl) ⟨3447896, by rfl⟩ : syracuseStep 4597195 = 6895793) B6895793
theorem B960007 : Blo 956588 960007 := bstep (se 1 (by rfl) ⟨720005, by rfl⟩ : syracuseStep 960007 = 1440011) B1440011
theorem B960015 : Blo 956588 960015 := bstep (se 1 (by rfl) ⟨720011, by rfl⟩ : syracuseStep 960015 = 1440023) B1440023
theorem B1615403 : Blo 956588 1615403 := bstep (se 1 (by rfl) ⟨1211552, by rfl⟩ : syracuseStep 1615403 = 2423105) B2423105
theorem B960059 : Blo 956588 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B960135 : Blo 956588 960135 := bstep (se 1 (by rfl) ⟨720101, by rfl⟩ : syracuseStep 960135 = 1440203) B1440203
theorem B960143 : Blo 956588 960143 := bstep (se 1 (by rfl) ⟨720107, by rfl⟩ : syracuseStep 960143 = 1440215) B1440215
theorem B960187 : Blo 956588 960187 := bstep (se 1 (by rfl) ⟨720140, by rfl⟩ : syracuseStep 960187 = 1440281) B1440281
theorem B960263 : Blo 956588 960263 := bstep (se 1 (by rfl) ⟨720197, by rfl⟩ : syracuseStep 960263 = 1440395) B1440395
theorem B4597519 : Blo 956588 4597519 := bstep (se 1 (by rfl) ⟨3448139, by rfl⟩ : syracuseStep 4597519 = 6896279) B6896279
theorem B960271 : Blo 956588 960271 := bstep (se 1 (by rfl) ⟨720203, by rfl⟩ : syracuseStep 960271 = 1440407) B1440407
theorem B2303777 : Blo 956588 2303777 := bstep (se 2 (by rfl) ⟨863916, by rfl⟩ : syracuseStep 2303777 = 1727833) B1727833
theorem B960315 : Blo 956588 960315 := bstep (se 1 (by rfl) ⟨720236, by rfl⟩ : syracuseStep 960315 = 1440473) B1440473
theorem B960391 : Blo 956588 960391 := bstep (se 1 (by rfl) ⟨720293, by rfl⟩ : syracuseStep 960391 = 1440587) B1440587
theorem B960399 : Blo 956588 960399 := bstep (se 1 (by rfl) ⟨720299, by rfl⟩ : syracuseStep 960399 = 1440599) B1440599
theorem B1615801 : Blo 956588 1615801 := bstep (se 2 (by rfl) ⟨605925, by rfl⟩ : syracuseStep 1615801 = 1211851) B1211851
theorem B960443 : Blo 956588 960443 := bstep (se 1 (by rfl) ⟨720332, by rfl⟩ : syracuseStep 960443 = 1440665) B1440665
theorem B960519 : Blo 956588 960519 := bstep (se 1 (by rfl) ⟨720389, by rfl⟩ : syracuseStep 960519 = 1440779) B1440779
theorem B960527 : Blo 956588 960527 := bstep (se 1 (by rfl) ⟨720395, by rfl⟩ : syracuseStep 960527 = 1440791) B1440791
theorem B960571 : Blo 956588 960571 := bstep (se 1 (by rfl) ⟨720428, by rfl⟩ : syracuseStep 960571 = 1440857) B1440857
theorem B1845395 : Blo 956588 1845395 := bstep (se 1 (by rfl) ⟨1384046, by rfl⟩ : syracuseStep 1845395 = 2768093) B2768093
theorem B3451081 : Blo 956588 3451081 := bstep (se 2 (by rfl) ⟨1294155, by rfl⟩ : syracuseStep 3451081 = 2588311) B2588311
theorem B4860161 : Blo 956588 4860161 := bstep (se 2 (by rfl) ⟨1822560, by rfl⟩ : syracuseStep 4860161 = 3645121) B3645121
theorem B7285139 : Blo 956588 7285139 := bstep (se 1 (by rfl) ⟨5463854, by rfl⟩ : syracuseStep 7285139 = 10927709) B10927709
theorem B12462659 : Blo 956588 12462659 := bstep (se 1 (by rfl) ⟨9346994, by rfl⟩ : syracuseStep 12462659 = 18693989) B18693989
theorem B1616503 : Blo 956588 1616503 := bstep (se 1 (by rfl) ⟨1212377, by rfl⟩ : syracuseStep 1616503 = 2424755) B2424755
theorem B1616699 : Blo 956588 1616699 := bstep (se 1 (by rfl) ⟨1212524, by rfl⟩ : syracuseStep 1616699 = 2425049) B2425049
theorem B1944379 : Blo 956588 1944379 := bstep (se 1 (by rfl) ⟨1458284, by rfl⟩ : syracuseStep 1944379 = 2916569) B2916569
theorem B4860971 : Blo 956588 4860971 := bstep (se 1 (by rfl) ⟨3645728, by rfl⟩ : syracuseStep 4860971 = 7291457) B7291457
theorem B1617097 : Blo 956588 1617097 := bstep (se 2 (by rfl) ⟨606411, by rfl⟩ : syracuseStep 1617097 = 1212823) B1212823
theorem B2731279 : Blo 956588 2731279 := bstep (se 1 (by rfl) ⟨2048459, by rfl⟩ : syracuseStep 2731279 = 4096919) B4096919
theorem B5451097 : Blo 956588 5451097 := bstep (se 2 (by rfl) ⟨2044161, by rfl⟩ : syracuseStep 5451097 = 4088323) B4088323
theorem B4599193 : Blo 956588 4599193 := bstep (se 2 (by rfl) ⟨1724697, by rfl⟩ : syracuseStep 4599193 = 3449395) B3449395
theorem B2305547 : Blo 956588 2305547 := bstep (se 1 (by rfl) ⟨1729160, by rfl⟩ : syracuseStep 2305547 = 3458321) B3458321
theorem B2731553 : Blo 956588 2731553 := bstep (se 2 (by rfl) ⟨1024332, by rfl⟩ : syracuseStep 2731553 = 2048665) B2048665
theorem B1945223 : Blo 956588 1945223 := bstep (se 1 (by rfl) ⟨1458917, by rfl⟩ : syracuseStep 1945223 = 2917835) B2917835
theorem B2043539 : Blo 956588 2043539 := bstep (se 1 (by rfl) ⟨1532654, by rfl⟩ : syracuseStep 2043539 = 3065309) B3065309
theorem B1617799 : Blo 956588 1617799 := bstep (se 1 (by rfl) ⟨1213349, by rfl⟩ : syracuseStep 1617799 = 2426699) B2426699
theorem B3551111 : Blo 956588 3551111 := bstep (se 1 (by rfl) ⟨2663333, by rfl⟩ : syracuseStep 3551111 = 5326667) B5326667
theorem B1847567 : Blo 956588 1847567 := bstep (se 1 (by rfl) ⟨1385675, by rfl⟩ : syracuseStep 1847567 = 2771351) B2771351
theorem B4862267 : Blo 956588 4862267 := bstep (se 1 (by rfl) ⟨3646700, by rfl⟩ : syracuseStep 4862267 = 7293401) B7293401
theorem B4862429 : Blo 956588 4862429 := bstep (se 3 (by rfl) ⟨911705, by rfl⟩ : syracuseStep 4862429 = 1823411) B1823411
theorem B2732555 : Blo 956588 2732555 := bstep (se 1 (by rfl) ⟨2049416, by rfl⟩ : syracuseStep 2732555 = 4098833) B4098833
theorem B1618447 : Blo 956588 1618447 := bstep (se 1 (by rfl) ⟨1213835, by rfl⟩ : syracuseStep 1618447 = 2427671) B2427671
theorem B3453677 : Blo 956588 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B4862753 : Blo 956588 4862753 := bstep (se 2 (by rfl) ⟨1823532, by rfl⟩ : syracuseStep 4862753 = 3647065) B3647065
theorem B2732953 : Blo 956588 2732953 := bstep (se 2 (by rfl) ⟨1024857, by rfl⟩ : syracuseStep 2732953 = 2049715) B2049715
theorem B5452829 : Blo 956588 5452829 := bstep (se 3 (by rfl) ⟨1022405, by rfl⟩ : syracuseStep 5452829 = 2044811) B2044811
theorem B1618987 : Blo 956588 1618987 := bstep (se 1 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 1618987 = 2428481) B2428481
theorem B1946683 : Blo 956588 1946683 := bstep (se 1 (by rfl) ⟨1460012, by rfl⟩ : syracuseStep 1946683 = 2920025) B2920025
theorem B2733203 : Blo 956588 2733203 := bstep (se 1 (by rfl) ⟨2049902, by rfl⟩ : syracuseStep 2733203 = 4099805) B4099805
theorem B1619129 : Blo 956588 1619129 := bstep (se 2 (by rfl) ⟨607173, by rfl⟩ : syracuseStep 1619129 = 1214347) B1214347
theorem B4928921 : Blo 956588 4928921 := bstep (se 2 (by rfl) ⟨1848345, by rfl⟩ : syracuseStep 4928921 = 3696691) B3696691
theorem B21018041 : Blo 956588 21018041 := bstep (se 2 (by rfl) ⟨7881765, by rfl⟩ : syracuseStep 21018041 = 15763531) B15763531
theorem B5453513 : Blo 956588 5453513 := bstep (se 2 (by rfl) ⟨2045067, by rfl⟩ : syracuseStep 5453513 = 4090135) B4090135
theorem B6895475 : Blo 956588 6895475 := bstep (se 1 (by rfl) ⟨5171606, by rfl⟩ : syracuseStep 6895475 = 10343213) B10343213
theorem B1619831 : Blo 956588 1619831 := bstep (se 1 (by rfl) ⟨1214873, by rfl⟩ : syracuseStep 1619831 = 2429747) B2429747
theorem B2734195 : Blo 956588 2734195 := bstep (se 1 (by rfl) ⟨2050646, by rfl⟩ : syracuseStep 2734195 = 4101293) B4101293
theorem B22132909 : Blo 956588 22132909 := bstep (se 3 (by rfl) ⟨4149920, by rfl⟩ : syracuseStep 22132909 = 8299841) B8299841
theorem B6895817 : Blo 956588 6895817 := bstep (se 2 (by rfl) ⟨2585931, by rfl⟩ : syracuseStep 6895817 = 5171863) B5171863
theorem B1620283 : Blo 956588 1620283 := bstep (se 1 (by rfl) ⟨1215212, by rfl⟩ : syracuseStep 1620283 = 2430425) B2430425
theorem B3684761 : Blo 956588 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B1620425 : Blo 956588 1620425 := bstep (se 2 (by rfl) ⟨607659, by rfl⟩ : syracuseStep 1620425 = 1215319) B1215319
theorem B1817147 : Blo 956588 1817147 := bstep (se 1 (by rfl) ⟨1362860, by rfl⟩ : syracuseStep 1817147 = 2725721) B2725721
theorem B2767817 : Blo 956588 2767817 := bstep (se 2 (by rfl) ⟨1037931, by rfl⟩ : syracuseStep 2767817 = 2075863) B2075863
theorem B1817633 : Blo 956588 1817633 := bstep (se 2 (by rfl) ⟨681612, by rfl⟩ : syracuseStep 1817633 = 1363225) B1363225
theorem B1457423 : Blo 956588 1457423 := bstep (se 1 (by rfl) ⟨1093067, by rfl⟩ : syracuseStep 1457423 = 2186135) B2186135
theorem B5455289 : Blo 956588 5455289 := bstep (se 2 (by rfl) ⟨2045733, by rfl⟩ : syracuseStep 5455289 = 4091467) B4091467
theorem B14728805 : Blo 956588 14728805 := bstep (se 4 (by rfl) ⟨1380825, by rfl⟩ : syracuseStep 14728805 = 2761651) B2761651
theorem B4669483 : Blo 956588 4669483 := bstep (se 1 (by rfl) ⟨3502112, by rfl⟩ : syracuseStep 4669483 = 7004225) B7004225
theorem B6144173 : Blo 956588 6144173 := bstep (se 3 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 6144173 = 2304065) B2304065
theorem B2048827 : Blo 956588 2048827 := bstep (se 1 (by rfl) ⟨1536620, by rfl⟩ : syracuseStep 2048827 = 3073241) B3073241
theorem B1459063 : Blo 956588 1459063 := bstep (se 1 (by rfl) ⟨1094297, by rfl⟩ : syracuseStep 1459063 = 2188595) B2188595
theorem B3228551 : Blo 956588 3228551 := bstep (se 1 (by rfl) ⟨2421413, by rfl⟩ : syracuseStep 3228551 = 4842827) B4842827
theorem B1819577 : Blo 956588 1819577 := bstep (se 2 (by rfl) ⟨682341, by rfl⟩ : syracuseStep 1819577 = 1364683) B1364683
theorem B1295561 : Blo 956588 1295561 := bstep (se 2 (by rfl) ⟨485835, by rfl⟩ : syracuseStep 1295561 = 971671) B971671
theorem B3228929 : Blo 956588 3228929 := bstep (se 2 (by rfl) ⟨1210848, by rfl⟩ : syracuseStep 3228929 = 2421697) B2421697
theorem B5457203 : Blo 956588 5457203 := bstep (se 1 (by rfl) ⟨4092902, by rfl⟩ : syracuseStep 5457203 = 8185805) B8185805
theorem B6899165 : Blo 956588 6899165 := bstep (se 3 (by rfl) ⟨1293593, by rfl⟩ : syracuseStep 6899165 = 2587187) B2587187
theorem B6899393 : Blo 956588 6899393 := bstep (se 2 (by rfl) ⟨2587272, by rfl⟩ : syracuseStep 6899393 = 5174545) B5174545
theorem B3688193 : Blo 956588 3688193 := bstep (se 2 (by rfl) ⟨1383072, by rfl⟩ : syracuseStep 3688193 = 2766145) B2766145
theorem B6899507 : Blo 956588 6899507 := bstep (se 1 (by rfl) ⟨5174630, by rfl⟩ : syracuseStep 6899507 = 10349261) B10349261
theorem B3458969 : Blo 956588 3458969 := bstep (se 2 (by rfl) ⟨1297113, by rfl⟩ : syracuseStep 3458969 = 2594227) B2594227
theorem B4376605 : Blo 956588 4376605 := bstep (se 3 (by rfl) ⟨820613, by rfl⟩ : syracuseStep 4376605 = 1641227) B1641227
theorem B3229739 : Blo 956588 3229739 := bstep (se 1 (by rfl) ⟨2422304, by rfl⟩ : syracuseStep 3229739 = 4844609) B4844609
theorem B1820731 : Blo 956588 1820731 := bstep (se 1 (by rfl) ⟨1365548, by rfl⟩ : syracuseStep 1820731 = 2731097) B2731097
theorem B1362091 : Blo 956588 1362091 := bstep (se 1 (by rfl) ⟨1021568, by rfl⟩ : syracuseStep 1362091 = 2043137) B2043137
theorem B1329467 : Blo 956588 1329467 := bstep (se 1 (by rfl) ⟨997100, by rfl⟩ : syracuseStep 1329467 = 1994201) B1994201
theorem B4606267 : Blo 956588 4606267 := bstep (se 1 (by rfl) ⟨3454700, by rfl⟩ : syracuseStep 4606267 = 6909401) B6909401
theorem B1821217 : Blo 956588 1821217 := bstep (se 2 (by rfl) ⟨682956, by rfl⟩ : syracuseStep 1821217 = 1365913) B1365913
theorem B9226871 : Blo 956588 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B5458661 : Blo 956588 5458661 := bstep (se 4 (by rfl) ⟨511749, by rfl⟩ : syracuseStep 5458661 = 1023499) B1023499
theorem B10898549 : Blo 956588 10898549 := bstep (se 5 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 10898549 = 1021739) B1021739
theorem B2051219 : Blo 956588 2051219 := bstep (se 1 (by rfl) ⟨1538414, by rfl⟩ : syracuseStep 2051219 = 3076829) B3076829
theorem B3231035 : Blo 956588 3231035 := bstep (se 1 (by rfl) ⟨2423276, by rfl⟩ : syracuseStep 3231035 = 4846553) B4846553
theorem B5459345 : Blo 956588 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B1822409 : Blo 956588 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B3231521 : Blo 956588 3231521 := bstep (se 2 (by rfl) ⟨1211820, by rfl⟩ : syracuseStep 3231521 = 2423641) B2423641
theorem B10932083 : Blo 956588 10932083 := bstep (se 1 (by rfl) ⟨8199062, by rfl⟩ : syracuseStep 10932083 = 16398125) B16398125
theorem B99438515 : Blo 956588 99438515 := bstep (se 1 (by rfl) ⟨74578886, by rfl⟩ : syracuseStep 99438515 = 149157773) B149157773
theorem B2183287 : Blo 956588 2183287 := bstep (se 1 (by rfl) ⟨1637465, by rfl⟩ : syracuseStep 2183287 = 3274931) B3274931
theorem B3232115 : Blo 956588 3232115 := bstep (se 1 (by rfl) ⟨2424086, by rfl⟩ : syracuseStep 3232115 = 4848173) B4848173
theorem B5460371 : Blo 956588 5460371 := bstep (se 1 (by rfl) ⟨4095278, by rfl⟩ : syracuseStep 5460371 = 8190557) B8190557
theorem B1823123 : Blo 956588 1823123 := bstep (se 1 (by rfl) ⟨1367342, by rfl⟩ : syracuseStep 1823123 = 2734685) B2734685
theorem B1823161 : Blo 956588 1823161 := bstep (se 2 (by rfl) ⟨683685, by rfl⟩ : syracuseStep 1823161 = 1367371) B1367371
theorem B6902275 : Blo 956588 6902275 := bstep (se 1 (by rfl) ⟨5176706, by rfl⟩ : syracuseStep 6902275 = 10353413) B10353413
theorem B4608515 : Blo 956588 4608515 := bstep (se 1 (by rfl) ⟨3456386, by rfl⟩ : syracuseStep 4608515 = 6912773) B6912773
theorem B1364779 : Blo 956588 1364779 := bstep (se 1 (by rfl) ⟨1023584, by rfl⟩ : syracuseStep 1364779 = 2047169) B2047169
theorem B74830769 : Blo 956588 74830769 := bstep (se 2 (by rfl) ⟨28061538, by rfl⟩ : syracuseStep 74830769 = 56123077) B56123077
theorem B3068857 : Blo 956588 3068857 := bstep (se 2 (by rfl) ⟨1150821, by rfl⟩ : syracuseStep 3068857 = 2301643) B2301643
theorem B8180747 : Blo 956588 8180747 := bstep (se 1 (by rfl) ⟨6135560, by rfl⟩ : syracuseStep 8180747 = 12271121) B12271121
theorem B1725455 : Blo 956588 1725455 := bstep (se 1 (by rfl) ⟨1294091, by rfl⟩ : syracuseStep 1725455 = 2588183) B2588183
theorem B1365007 : Blo 956588 1365007 := bstep (se 1 (by rfl) ⟨1023755, by rfl⟩ : syracuseStep 1365007 = 2047511) B2047511
theorem B3691777 : Blo 956588 3691777 := bstep (se 2 (by rfl) ⟨1384416, by rfl⟩ : syracuseStep 3691777 = 2768833) B2768833
theorem B11064707 : Blo 956588 11064707 := bstep (se 1 (by rfl) ⟨8298530, by rfl⟩ : syracuseStep 11064707 = 16597061) B16597061
theorem B1365383 : Blo 956588 1365383 := bstep (se 1 (by rfl) ⟨1024037, by rfl⟩ : syracuseStep 1365383 = 2048075) B2048075
theorem B52450739 : Blo 956588 52450739 := bstep (se 1 (by rfl) ⟨39338054, by rfl⟩ : syracuseStep 52450739 = 78676109) B78676109
theorem B19715735 : Blo 956588 19715735 := bstep (se 1 (by rfl) ⟨14786801, by rfl⟩ : syracuseStep 19715735 = 29573603) B29573603
theorem B3889181 : Blo 956588 3889181 := bstep (se 3 (by rfl) ⟨729221, by rfl⟩ : syracuseStep 3889181 = 1458443) B1458443
theorem B2152583 : Blo 956588 2152583 := bstep (se 1 (by rfl) ⟨1614437, by rfl⟩ : syracuseStep 2152583 = 3228875) B3228875
theorem B3987713 : Blo 956588 3987713 := bstep (se 2 (by rfl) ⟨1495392, by rfl⟩ : syracuseStep 3987713 = 2990785) B2990785
theorem B3070241 : Blo 956588 3070241 := bstep (se 2 (by rfl) ⟨1151340, by rfl⟩ : syracuseStep 3070241 = 2302681) B2302681
theorem B2152763 : Blo 956588 2152763 := bstep (se 1 (by rfl) ⟨1614572, by rfl⟩ : syracuseStep 2152763 = 3229145) B3229145
theorem B3070343 : Blo 956588 3070343 := bstep (se 1 (by rfl) ⟨2302757, by rfl⟩ : syracuseStep 3070343 = 4605515) B4605515
theorem B2152889 : Blo 956588 2152889 := bstep (se 2 (by rfl) ⟨807333, by rfl⟩ : syracuseStep 2152889 = 1614667) B1614667
theorem B2153231 : Blo 956588 2153231 := bstep (se 1 (by rfl) ⟨1614923, by rfl⟩ : syracuseStep 2153231 = 3229847) B3229847
theorem B2153249 : Blo 956588 2153249 := bstep (se 2 (by rfl) ⟨807468, by rfl⟩ : syracuseStep 2153249 = 1614937) B1614937
theorem B1366841 : Blo 956588 1366841 := bstep (se 2 (by rfl) ⟨512565, by rfl⟩ : syracuseStep 1366841 = 1025131) B1025131
theorem B3234707 : Blo 956588 3234707 := bstep (se 1 (by rfl) ⟨2426030, by rfl⟩ : syracuseStep 3234707 = 4852061) B4852061
theorem B2153591 : Blo 956588 2153591 := bstep (se 1 (by rfl) ⟨1615193, by rfl⟩ : syracuseStep 2153591 = 3230387) B3230387
theorem B2153771 : Blo 956588 2153771 := bstep (se 1 (by rfl) ⟨1615328, by rfl⟩ : syracuseStep 2153771 = 3230657) B3230657
theorem B1367695 : Blo 956588 1367695 := bstep (se 1 (by rfl) ⟨1025771, by rfl⟩ : syracuseStep 1367695 = 2051543) B2051543
theorem B2154131 : Blo 956588 2154131 := bstep (se 1 (by rfl) ⟨1615598, by rfl⟩ : syracuseStep 2154131 = 3231197) B3231197
theorem B2154185 : Blo 956588 2154185 := bstep (se 2 (by rfl) ⟨807819, by rfl⟩ : syracuseStep 2154185 = 1615639) B1615639
theorem B3497863 : Blo 956588 3497863 := bstep (se 1 (by rfl) ⟨2623397, by rfl⟩ : syracuseStep 3497863 = 5246795) B5246795
theorem B12443543 : Blo 956588 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B5824477 : Blo 956588 5824477 := bstep (se 3 (by rfl) ⟨1092089, by rfl⟩ : syracuseStep 5824477 = 2184179) B2184179
theorem B3236111 : Blo 956588 3236111 := bstep (se 1 (by rfl) ⟨2427083, by rfl⟩ : syracuseStep 3236111 = 4854167) B4854167
theorem B2154887 : Blo 956588 2154887 := bstep (se 1 (by rfl) ⟨1616165, by rfl⟩ : syracuseStep 2154887 = 3232331) B3232331
theorem B3236381 : Blo 956588 3236381 := bstep (se 3 (by rfl) ⟨606821, by rfl⟩ : syracuseStep 3236381 = 1213643) B1213643
theorem B2155067 : Blo 956588 2155067 := bstep (se 1 (by rfl) ⟨1616300, by rfl⟩ : syracuseStep 2155067 = 3232601) B3232601
theorem B2155193 : Blo 956588 2155193 := bstep (se 2 (by rfl) ⟨808197, by rfl⟩ : syracuseStep 2155193 = 1616395) B1616395
theorem B2155535 : Blo 956588 2155535 := bstep (se 1 (by rfl) ⟨1616651, by rfl⟩ : syracuseStep 2155535 = 3233303) B3233303
theorem B2155553 : Blo 956588 2155553 := bstep (se 2 (by rfl) ⟨808332, by rfl⟩ : syracuseStep 2155553 = 1616665) B1616665
theorem B22176899 : Blo 956588 22176899 := bstep (se 1 (by rfl) ⟨16632674, by rfl⟩ : syracuseStep 22176899 = 33265349) B33265349
theorem B1729721 : Blo 956588 1729721 := bstep (se 2 (by rfl) ⟨648645, by rfl⟩ : syracuseStep 1729721 = 1297291) B1297291
theorem B1434887 : Blo 956588 1434887 := bstep (se 1 (by rfl) ⟨1076165, by rfl⟩ : syracuseStep 1434887 = 2152331) B2152331
theorem B8185121 : Blo 956588 8185121 := bstep (se 2 (by rfl) ⟨3069420, by rfl⟩ : syracuseStep 8185121 = 6138841) B6138841
theorem B1434923 : Blo 956588 1434923 := bstep (se 1 (by rfl) ⟨1076192, by rfl⟩ : syracuseStep 1434923 = 2152385) B2152385
theorem B7267643 : Blo 956588 7267643 := bstep (se 1 (by rfl) ⟨5450732, by rfl⟩ : syracuseStep 7267643 = 10901465) B10901465
theorem B1434953 : Blo 956588 1434953 := bstep (se 2 (by rfl) ⟨538107, by rfl⟩ : syracuseStep 1434953 = 1076215) B1076215
theorem B2155895 : Blo 956588 2155895 := bstep (se 1 (by rfl) ⟨1616921, by rfl⟩ : syracuseStep 2155895 = 3233843) B3233843
theorem B1435067 : Blo 956588 1435067 := bstep (se 1 (by rfl) ⟨1076300, by rfl⟩ : syracuseStep 1435067 = 2152601) B2152601
theorem B1435127 : Blo 956588 1435127 := bstep (se 1 (by rfl) ⟨1076345, by rfl⟩ : syracuseStep 1435127 = 2152691) B2152691
theorem B1435151 : Blo 956588 1435151 := bstep (se 1 (by rfl) ⟨1076363, by rfl⟩ : syracuseStep 1435151 = 2152727) B2152727
theorem B2156075 : Blo 956588 2156075 := bstep (se 1 (by rfl) ⟨1617056, by rfl⟩ : syracuseStep 2156075 = 3234113) B3234113
theorem B1435193 : Blo 956588 1435193 := bstep (se 2 (by rfl) ⟨538197, by rfl⟩ : syracuseStep 1435193 = 1076395) B1076395
theorem B1435271 : Blo 956588 1435271 := bstep (se 1 (by rfl) ⟨1076453, by rfl⟩ : syracuseStep 1435271 = 2152907) B2152907
theorem B1435307 : Blo 956588 1435307 := bstep (se 1 (by rfl) ⟨1076480, by rfl⟩ : syracuseStep 1435307 = 2152961) B2152961
theorem B1435337 : Blo 956588 1435337 := bstep (se 2 (by rfl) ⟨538251, by rfl⟩ : syracuseStep 1435337 = 1076503) B1076503
theorem B5826305 : Blo 956588 5826305 := bstep (se 2 (by rfl) ⟨2184864, by rfl⟩ : syracuseStep 5826305 = 4369729) B4369729
theorem B1435451 : Blo 956588 1435451 := bstep (se 1 (by rfl) ⟨1076588, by rfl⟩ : syracuseStep 1435451 = 2153177) B2153177
theorem B1435511 : Blo 956588 1435511 := bstep (se 1 (by rfl) ⟨1076633, by rfl⟩ : syracuseStep 1435511 = 2153267) B2153267
theorem B1435535 : Blo 956588 1435535 := bstep (se 1 (by rfl) ⟨1076651, by rfl⟩ : syracuseStep 1435535 = 2153303) B2153303
theorem B2156435 : Blo 956588 2156435 := bstep (se 1 (by rfl) ⟨1617326, by rfl⟩ : syracuseStep 2156435 = 3234653) B3234653
theorem B3237785 : Blo 956588 3237785 := bstep (se 2 (by rfl) ⟨1214169, by rfl⟩ : syracuseStep 3237785 = 2428339) B2428339
theorem B1435577 : Blo 956588 1435577 := bstep (se 2 (by rfl) ⟨538341, by rfl⟩ : syracuseStep 1435577 = 1076683) B1076683
theorem B2156489 : Blo 956588 2156489 := bstep (se 2 (by rfl) ⟨808683, by rfl⟩ : syracuseStep 2156489 = 1617367) B1617367
theorem B1435655 : Blo 956588 1435655 := bstep (se 1 (by rfl) ⟨1076741, by rfl⟩ : syracuseStep 1435655 = 2153483) B2153483
theorem B1435691 : Blo 956588 1435691 := bstep (se 1 (by rfl) ⟨1076768, by rfl⟩ : syracuseStep 1435691 = 2153537) B2153537
theorem B4614205 : Blo 956588 4614205 := bstep (se 3 (by rfl) ⟨865163, by rfl⟩ : syracuseStep 4614205 = 1730327) B1730327
theorem B1435721 : Blo 956588 1435721 := bstep (se 2 (by rfl) ⟨538395, by rfl⟩ : syracuseStep 1435721 = 1076791) B1076791
theorem B1435835 : Blo 956588 1435835 := bstep (se 1 (by rfl) ⟨1076876, by rfl⟩ : syracuseStep 1435835 = 2153753) B2153753
theorem B1435895 : Blo 956588 1435895 := bstep (se 1 (by rfl) ⟨1076921, by rfl⟩ : syracuseStep 1435895 = 2153843) B2153843
theorem B1435919 : Blo 956588 1435919 := bstep (se 1 (by rfl) ⟨1076939, by rfl⟩ : syracuseStep 1435919 = 2153879) B2153879
theorem B1435961 : Blo 956588 1435961 := bstep (se 2 (by rfl) ⟨538485, by rfl⟩ : syracuseStep 1435961 = 1076971) B1076971
theorem B1436039 : Blo 956588 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B1436075 : Blo 956588 1436075 := bstep (se 1 (by rfl) ⟨1077056, by rfl⟩ : syracuseStep 1436075 = 2154113) B2154113
theorem B4843961 : Blo 956588 4843961 := bstep (se 2 (by rfl) ⟨1816485, by rfl⟩ : syracuseStep 4843961 = 3632971) B3632971
theorem B1436105 : Blo 956588 1436105 := bstep (se 2 (by rfl) ⟨538539, by rfl⟩ : syracuseStep 1436105 = 1077079) B1077079
theorem B10349005 : Blo 956588 10349005 := bstep (se 3 (by rfl) ⟨1940438, by rfl⟩ : syracuseStep 10349005 = 3880877) B3880877
theorem B5466635 : Blo 956588 5466635 := bstep (se 1 (by rfl) ⟨4099976, by rfl⟩ : syracuseStep 5466635 = 8199953) B8199953
theorem B1436219 : Blo 956588 1436219 := bstep (se 1 (by rfl) ⟨1077164, by rfl⟩ : syracuseStep 1436219 = 2154329) B2154329
theorem B3238487 : Blo 956588 3238487 := bstep (se 1 (by rfl) ⟨2428865, by rfl⟩ : syracuseStep 3238487 = 4857731) B4857731
theorem B1436279 : Blo 956588 1436279 := bstep (se 1 (by rfl) ⟨1077209, by rfl⟩ : syracuseStep 1436279 = 2154419) B2154419
theorem B2157191 : Blo 956588 2157191 := bstep (se 1 (by rfl) ⟨1617893, by rfl⟩ : syracuseStep 2157191 = 3235787) B3235787
theorem B1436303 : Blo 956588 1436303 := bstep (se 1 (by rfl) ⟨1077227, by rfl⟩ : syracuseStep 1436303 = 2154455) B2154455
theorem B1436345 : Blo 956588 1436345 := bstep (se 2 (by rfl) ⟨538629, by rfl⟩ : syracuseStep 1436345 = 1077259) B1077259
theorem B5827301 : Blo 956588 5827301 := bstep (se 4 (by rfl) ⟨546309, by rfl⟩ : syracuseStep 5827301 = 1092619) B1092619
theorem B1436423 : Blo 956588 1436423 := bstep (se 1 (by rfl) ⟨1077317, by rfl⟩ : syracuseStep 1436423 = 2154635) B2154635
theorem B1436459 : Blo 956588 1436459 := bstep (se 1 (by rfl) ⟨1077344, by rfl⟩ : syracuseStep 1436459 = 2154689) B2154689
theorem B2157371 : Blo 956588 2157371 := bstep (se 1 (by rfl) ⟨1618028, by rfl⟩ : syracuseStep 2157371 = 3236057) B3236057
theorem B1436489 : Blo 956588 1436489 := bstep (se 2 (by rfl) ⟨538683, by rfl⟩ : syracuseStep 1436489 = 1077367) B1077367
theorem B2157497 : Blo 956588 2157497 := bstep (se 2 (by rfl) ⟨809061, by rfl⟩ : syracuseStep 2157497 = 1618123) B1618123
theorem B1436603 : Blo 956588 1436603 := bstep (se 1 (by rfl) ⟨1077452, by rfl⟩ : syracuseStep 1436603 = 2154905) B2154905
theorem B1436663 : Blo 956588 1436663 := bstep (se 1 (by rfl) ⟨1077497, by rfl⟩ : syracuseStep 1436663 = 2154995) B2154995
theorem B6908939 : Blo 956588 6908939 := bstep (se 1 (by rfl) ⟨5181704, by rfl⟩ : syracuseStep 6908939 = 10363409) B10363409
theorem B1436687 : Blo 956588 1436687 := bstep (se 1 (by rfl) ⟨1077515, by rfl⟩ : syracuseStep 1436687 = 2155031) B2155031
theorem B1436729 : Blo 956588 1436729 := bstep (se 2 (by rfl) ⟨538773, by rfl⟩ : syracuseStep 1436729 = 1077547) B1077547
theorem B3238973 : Blo 956588 3238973 := bstep (se 3 (by rfl) ⟨607307, by rfl⟩ : syracuseStep 3238973 = 1214615) B1214615
theorem B1076359 : Blo 956588 1076359 := bstep (se 1 (by rfl) ⟨807269, by rfl⟩ : syracuseStep 1076359 = 1614539) B1614539
theorem B1436807 : Blo 956588 1436807 := bstep (se 1 (by rfl) ⟨1077605, by rfl⟩ : syracuseStep 1436807 = 2155211) B2155211
theorem B1436843 : Blo 956588 1436843 := bstep (se 1 (by rfl) ⟨1077632, by rfl⟩ : syracuseStep 1436843 = 2155265) B2155265
theorem B1436873 : Blo 956588 1436873 := bstep (se 2 (by rfl) ⟨538827, by rfl⟩ : syracuseStep 1436873 = 1077655) B1077655
theorem B2157839 : Blo 956588 2157839 := bstep (se 1 (by rfl) ⟨1618379, by rfl⟩ : syracuseStep 2157839 = 3236759) B3236759
theorem B2157857 : Blo 956588 2157857 := bstep (se 2 (by rfl) ⟨809196, by rfl⟩ : syracuseStep 2157857 = 1618393) B1618393
theorem B1076539 : Blo 956588 1076539 := bstep (se 1 (by rfl) ⟨807404, by rfl⟩ : syracuseStep 1076539 = 1614809) B1614809
theorem B1436987 : Blo 956588 1436987 := bstep (se 1 (by rfl) ⟨1077740, by rfl⟩ : syracuseStep 1436987 = 2155481) B2155481
theorem B1437047 : Blo 956588 1437047 := bstep (se 1 (by rfl) ⟨1077785, by rfl⟩ : syracuseStep 1437047 = 2155571) B2155571
theorem B1437071 : Blo 956588 1437071 := bstep (se 1 (by rfl) ⟨1077803, by rfl⟩ : syracuseStep 1437071 = 2155607) B2155607
theorem B1437113 : Blo 956588 1437113 := bstep (se 2 (by rfl) ⟨538917, by rfl⟩ : syracuseStep 1437113 = 1077835) B1077835
theorem B1437191 : Blo 956588 1437191 := bstep (se 1 (by rfl) ⟨1077893, by rfl⟩ : syracuseStep 1437191 = 2155787) B2155787
theorem B15560221 : Blo 956588 15560221 := bstep (se 3 (by rfl) ⟨2917541, by rfl⟩ : syracuseStep 15560221 = 5835083) B5835083
theorem B1437227 : Blo 956588 1437227 := bstep (se 1 (by rfl) ⟨1077920, by rfl⟩ : syracuseStep 1437227 = 2155841) B2155841
theorem B1437257 : Blo 956588 1437257 := bstep (se 2 (by rfl) ⟨538971, by rfl⟩ : syracuseStep 1437257 = 1077943) B1077943
theorem B3632759 : Blo 956588 3632759 := bstep (se 1 (by rfl) ⟨2724569, by rfl⟩ : syracuseStep 3632759 = 5449139) B5449139
theorem B2158199 : Blo 956588 2158199 := bstep (se 1 (by rfl) ⟨1618649, by rfl⟩ : syracuseStep 2158199 = 3237299) B3237299
theorem B1437371 : Blo 956588 1437371 := bstep (se 1 (by rfl) ⟨1078028, by rfl⟩ : syracuseStep 1437371 = 2156057) B2156057
theorem B4845257 : Blo 956588 4845257 := bstep (se 2 (by rfl) ⟨1816971, by rfl⟩ : syracuseStep 4845257 = 3633943) B3633943
theorem B1437431 : Blo 956588 1437431 := bstep (se 1 (by rfl) ⟨1078073, by rfl⟩ : syracuseStep 1437431 = 2156147) B2156147
theorem B1077007 : Blo 956588 1077007 := bstep (se 1 (by rfl) ⟨807755, by rfl⟩ : syracuseStep 1077007 = 1615511) B1615511
theorem B1437455 : Blo 956588 1437455 := bstep (se 1 (by rfl) ⟨1078091, by rfl⟩ : syracuseStep 1437455 = 2156183) B2156183
theorem B8285989 : Blo 956588 8285989 := bstep (se 4 (by rfl) ⟨776811, by rfl⟩ : syracuseStep 8285989 = 1553623) B1553623
theorem B2158379 : Blo 956588 2158379 := bstep (se 1 (by rfl) ⟨1618784, by rfl⟩ : syracuseStep 2158379 = 3237569) B3237569
theorem B1437497 : Blo 956588 1437497 := bstep (se 2 (by rfl) ⟨539061, by rfl⟩ : syracuseStep 1437497 = 1078123) B1078123
theorem B1109819 : Blo 956588 1109819 := bstep (se 1 (by rfl) ⟨832364, by rfl⟩ : syracuseStep 1109819 = 1664729) B1664729
theorem B1437575 : Blo 956588 1437575 := bstep (se 1 (by rfl) ⟨1078181, by rfl⟩ : syracuseStep 1437575 = 2156363) B2156363
theorem B1437611 : Blo 956588 1437611 := bstep (se 1 (by rfl) ⟨1078208, by rfl⟩ : syracuseStep 1437611 = 2156417) B2156417
theorem B1437641 : Blo 956588 1437641 := bstep (se 2 (by rfl) ⟨539115, by rfl⟩ : syracuseStep 1437641 = 1078231) B1078231
theorem B1437755 : Blo 956588 1437755 := bstep (se 1 (by rfl) ⟨1078316, by rfl⟩ : syracuseStep 1437755 = 2156633) B2156633
theorem B2912375 : Blo 956588 2912375 := bstep (se 1 (by rfl) ⟨2184281, by rfl⟩ : syracuseStep 2912375 = 4368563) B4368563
theorem B1437815 : Blo 956588 1437815 := bstep (se 1 (by rfl) ⟨1078361, by rfl⟩ : syracuseStep 1437815 = 2156723) B2156723
theorem B1437839 : Blo 956588 1437839 := bstep (se 1 (by rfl) ⟨1078379, by rfl⟩ : syracuseStep 1437839 = 2156759) B2156759
theorem B2158739 : Blo 956588 2158739 := bstep (se 1 (by rfl) ⟨1619054, by rfl⟩ : syracuseStep 2158739 = 3238109) B3238109
theorem B1437881 : Blo 956588 1437881 := bstep (se 2 (by rfl) ⟨539205, by rfl⟩ : syracuseStep 1437881 = 1078411) B1078411
theorem B2158793 : Blo 956588 2158793 := bstep (se 2 (by rfl) ⟨809547, by rfl⟩ : syracuseStep 2158793 = 1619095) B1619095
theorem B1077511 : Blo 956588 1077511 := bstep (se 1 (by rfl) ⟨808133, by rfl⟩ : syracuseStep 1077511 = 1616267) B1616267
theorem B1437959 : Blo 956588 1437959 := bstep (se 1 (by rfl) ⟨1078469, by rfl⟩ : syracuseStep 1437959 = 2156939) B2156939
theorem B1437995 : Blo 956588 1437995 := bstep (se 1 (by rfl) ⟨1078496, by rfl⟩ : syracuseStep 1437995 = 2156993) B2156993
theorem B1438025 : Blo 956588 1438025 := bstep (se 2 (by rfl) ⟨539259, by rfl⟩ : syracuseStep 1438025 = 1078519) B1078519
theorem B3240377 : Blo 956588 3240377 := bstep (se 2 (by rfl) ⟨1215141, by rfl⟩ : syracuseStep 3240377 = 2430283) B2430283
theorem B1077691 : Blo 956588 1077691 := bstep (se 1 (by rfl) ⟨808268, by rfl⟩ : syracuseStep 1077691 = 1616537) B1616537
theorem B1438139 : Blo 956588 1438139 := bstep (se 1 (by rfl) ⟨1078604, by rfl⟩ : syracuseStep 1438139 = 2157209) B2157209
theorem B1438199 : Blo 956588 1438199 := bstep (se 1 (by rfl) ⟨1078649, by rfl⟩ : syracuseStep 1438199 = 2157299) B2157299
theorem B1438223 : Blo 956588 1438223 := bstep (se 1 (by rfl) ⟨1078667, by rfl⟩ : syracuseStep 1438223 = 2157335) B2157335
theorem B1438265 : Blo 956588 1438265 := bstep (se 2 (by rfl) ⟨539349, by rfl⟩ : syracuseStep 1438265 = 1078699) B1078699
theorem B3633731 : Blo 956588 3633731 := bstep (se 1 (by rfl) ⟨2725298, by rfl⟩ : syracuseStep 3633731 = 5450597) B5450597
theorem B1438343 : Blo 956588 1438343 := bstep (se 1 (by rfl) ⟨1078757, by rfl⟩ : syracuseStep 1438343 = 2157515) B2157515
theorem B1438379 : Blo 956588 1438379 := bstep (se 1 (by rfl) ⟨1078784, by rfl⟩ : syracuseStep 1438379 = 2157569) B2157569
theorem B1438409 : Blo 956588 1438409 := bstep (se 2 (by rfl) ⟨539403, by rfl⟩ : syracuseStep 1438409 = 1078807) B1078807
theorem B2421515 : Blo 956588 2421515 := bstep (se 1 (by rfl) ⟨1816136, by rfl⟩ : syracuseStep 2421515 = 3632273) B3632273
theorem B1438523 : Blo 956588 1438523 := bstep (se 1 (by rfl) ⟨1078892, by rfl⟩ : syracuseStep 1438523 = 2157785) B2157785
theorem B1438583 : Blo 956588 1438583 := bstep (se 1 (by rfl) ⟨1078937, by rfl⟩ : syracuseStep 1438583 = 2157875) B2157875
theorem B2159495 : Blo 956588 2159495 := bstep (se 1 (by rfl) ⟨1619621, by rfl⟩ : syracuseStep 2159495 = 3239243) B3239243
theorem B1078159 : Blo 956588 1078159 := bstep (se 1 (by rfl) ⟨808619, by rfl⟩ : syracuseStep 1078159 = 1617239) B1617239
theorem B1438607 : Blo 956588 1438607 := bstep (se 1 (by rfl) ⟨1078955, by rfl⟩ : syracuseStep 1438607 = 2157911) B2157911
theorem B1438649 : Blo 956588 1438649 := bstep (se 2 (by rfl) ⟨539493, by rfl⟩ : syracuseStep 1438649 = 1078987) B1078987
theorem B1438727 : Blo 956588 1438727 := bstep (se 1 (by rfl) ⟨1079045, by rfl⟩ : syracuseStep 1438727 = 2158091) B2158091
theorem B3240971 : Blo 956588 3240971 := bstep (se 1 (by rfl) ⟨2430728, by rfl⟩ : syracuseStep 3240971 = 4861457) B4861457
theorem B1438763 : Blo 956588 1438763 := bstep (se 1 (by rfl) ⟨1079072, by rfl⟩ : syracuseStep 1438763 = 2158145) B2158145
theorem B2159675 : Blo 956588 2159675 := bstep (se 1 (by rfl) ⟨1619756, by rfl⟩ : syracuseStep 2159675 = 3239513) B3239513
theorem B1438793 : Blo 956588 1438793 := bstep (se 2 (by rfl) ⟨539547, by rfl⟩ : syracuseStep 1438793 = 1079095) B1079095
theorem B3241079 : Blo 956588 3241079 := bstep (se 1 (by rfl) ⟨2430809, by rfl⟩ : syracuseStep 3241079 = 4861619) B4861619
theorem B2159801 : Blo 956588 2159801 := bstep (se 2 (by rfl) ⟨809925, by rfl⟩ : syracuseStep 2159801 = 1619851) B1619851
theorem B1438907 : Blo 956588 1438907 := bstep (se 1 (by rfl) ⟨1079180, by rfl⟩ : syracuseStep 1438907 = 2158361) B2158361
theorem B1438967 : Blo 956588 1438967 := bstep (se 1 (by rfl) ⟨1079225, by rfl⟩ : syracuseStep 1438967 = 2158451) B2158451
theorem B1438991 : Blo 956588 1438991 := bstep (se 1 (by rfl) ⟨1079243, by rfl⟩ : syracuseStep 1438991 = 2158487) B2158487
theorem B1439033 : Blo 956588 1439033 := bstep (se 2 (by rfl) ⟨539637, by rfl⟩ : syracuseStep 1439033 = 1079275) B1079275
theorem B1078663 : Blo 956588 1078663 := bstep (se 1 (by rfl) ⟨808997, by rfl⟩ : syracuseStep 1078663 = 1617995) B1617995
theorem B1439111 : Blo 956588 1439111 := bstep (se 1 (by rfl) ⟨1079333, by rfl⟩ : syracuseStep 1439111 = 2158667) B2158667
theorem B181630349 : Blo 956588 181630349 := bstep (se 3 (by rfl) ⟨34055690, by rfl⟩ : syracuseStep 181630349 = 68111381) B68111381
theorem B2422163 : Blo 956588 2422163 := bstep (se 1 (by rfl) ⟨1816622, by rfl⟩ : syracuseStep 2422163 = 3633245) B3633245
theorem B1439147 : Blo 956588 1439147 := bstep (se 1 (by rfl) ⟨1079360, by rfl⟩ : syracuseStep 1439147 = 2158721) B2158721
theorem B1439177 : Blo 956588 1439177 := bstep (se 2 (by rfl) ⟨539691, by rfl⟩ : syracuseStep 1439177 = 1079383) B1079383
theorem B2160143 : Blo 956588 2160143 := bstep (se 1 (by rfl) ⟨1620107, by rfl⟩ : syracuseStep 2160143 = 3240215) B3240215
theorem B2160161 : Blo 956588 2160161 := bstep (se 2 (by rfl) ⟨810060, by rfl⟩ : syracuseStep 2160161 = 1620121) B1620121
theorem B1078843 : Blo 956588 1078843 := bstep (se 1 (by rfl) ⟨809132, by rfl⟩ : syracuseStep 1078843 = 1618265) B1618265
theorem B1439291 : Blo 956588 1439291 := bstep (se 1 (by rfl) ⟨1079468, by rfl⟩ : syracuseStep 1439291 = 2158937) B2158937
theorem B1439351 : Blo 956588 1439351 := bstep (se 1 (by rfl) ⟨1079513, by rfl⟩ : syracuseStep 1439351 = 2159027) B2159027
theorem B1439375 : Blo 956588 1439375 := bstep (se 1 (by rfl) ⟨1079531, by rfl⟩ : syracuseStep 1439375 = 2159063) B2159063
theorem B5469869 : Blo 956588 5469869 := bstep (se 3 (by rfl) ⟨1025600, by rfl⟩ : syracuseStep 5469869 = 2051201) B2051201
theorem B2422457 : Blo 956588 2422457 := bstep (se 2 (by rfl) ⟨908421, by rfl⟩ : syracuseStep 2422457 = 1816843) B1816843
theorem B1439417 : Blo 956588 1439417 := bstep (se 2 (by rfl) ⟨539781, by rfl⟩ : syracuseStep 1439417 = 1079563) B1079563
theorem B3241673 : Blo 956588 3241673 := bstep (se 2 (by rfl) ⟨1215627, by rfl⟩ : syracuseStep 3241673 = 2431255) B2431255
theorem B1439495 : Blo 956588 1439495 := bstep (se 1 (by rfl) ⟨1079621, by rfl⟩ : syracuseStep 1439495 = 2159243) B2159243
theorem B1439531 : Blo 956588 1439531 := bstep (se 1 (by rfl) ⟨1079648, by rfl⟩ : syracuseStep 1439531 = 2159297) B2159297
theorem B1439561 : Blo 956588 1439561 := bstep (se 2 (by rfl) ⟨539835, by rfl⟩ : syracuseStep 1439561 = 1079671) B1079671
theorem B2160503 : Blo 956588 2160503 := bstep (se 1 (by rfl) ⟨1620377, by rfl⟩ : syracuseStep 2160503 = 3240755) B3240755
theorem B1439675 : Blo 956588 1439675 := bstep (se 1 (by rfl) ⟨1079756, by rfl⟩ : syracuseStep 1439675 = 2159513) B2159513
theorem B1439735 : Blo 956588 1439735 := bstep (se 1 (by rfl) ⟨1079801, by rfl⟩ : syracuseStep 1439735 = 2159603) B2159603
theorem B1079311 : Blo 956588 1079311 := bstep (se 1 (by rfl) ⟨809483, by rfl⟩ : syracuseStep 1079311 = 1618967) B1618967
theorem B1439759 : Blo 956588 1439759 := bstep (se 1 (by rfl) ⟨1079819, by rfl⟩ : syracuseStep 1439759 = 2159639) B2159639
theorem B37910551 : Blo 956588 37910551 := bstep (se 1 (by rfl) ⟨28432913, by rfl⟩ : syracuseStep 37910551 = 56865827) B56865827
theorem B2160683 : Blo 956588 2160683 := bstep (se 1 (by rfl) ⟨1620512, by rfl⟩ : syracuseStep 2160683 = 3241025) B3241025
theorem B1439801 : Blo 956588 1439801 := bstep (se 2 (by rfl) ⟨539925, by rfl⟩ : syracuseStep 1439801 = 1079851) B1079851
theorem B1439879 : Blo 956588 1439879 := bstep (se 1 (by rfl) ⟨1079909, by rfl⟩ : syracuseStep 1439879 = 2159819) B2159819
theorem B2455705 : Blo 956588 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B1439915 : Blo 956588 1439915 := bstep (se 1 (by rfl) ⟨1079936, by rfl⟩ : syracuseStep 1439915 = 2159873) B2159873
theorem B3635401 : Blo 956588 3635401 := bstep (se 2 (by rfl) ⟨1363275, by rfl⟩ : syracuseStep 3635401 = 2726551) B2726551
theorem B1439945 : Blo 956588 1439945 := bstep (se 2 (by rfl) ⟨539979, by rfl⟩ : syracuseStep 1439945 = 1079959) B1079959
theorem B1440059 : Blo 956588 1440059 := bstep (se 1 (by rfl) ⟨1080044, by rfl⟩ : syracuseStep 1440059 = 2160089) B2160089
theorem B2423155 : Blo 956588 2423155 := bstep (se 1 (by rfl) ⟨1817366, by rfl⟩ : syracuseStep 2423155 = 3634733) B3634733
theorem B1440119 : Blo 956588 1440119 := bstep (se 1 (by rfl) ⟨1080089, by rfl⟩ : syracuseStep 1440119 = 2160179) B2160179
theorem B1440143 : Blo 956588 1440143 := bstep (se 1 (by rfl) ⟨1080107, by rfl⟩ : syracuseStep 1440143 = 2160215) B2160215
theorem B2161043 : Blo 956588 2161043 := bstep (se 1 (by rfl) ⟨1620782, by rfl⟩ : syracuseStep 2161043 = 3241565) B3241565
theorem B1440185 : Blo 956588 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B2161097 : Blo 956588 2161097 := bstep (se 2 (by rfl) ⟨810411, by rfl⟩ : syracuseStep 2161097 = 1620823) B1620823
theorem B2423297 : Blo 956588 2423297 := bstep (se 2 (by rfl) ⟨908736, by rfl⟩ : syracuseStep 2423297 = 1817473) B1817473
theorem B1079815 : Blo 956588 1079815 := bstep (se 1 (by rfl) ⟨809861, by rfl⟩ : syracuseStep 1079815 = 1619723) B1619723
theorem B1440263 : Blo 956588 1440263 := bstep (se 1 (by rfl) ⟨1080197, by rfl⟩ : syracuseStep 1440263 = 2160395) B2160395
theorem B7272989 : Blo 956588 7272989 := bstep (se 3 (by rfl) ⟨1363685, by rfl⟩ : syracuseStep 7272989 = 2727371) B2727371
theorem B1440299 : Blo 956588 1440299 := bstep (se 1 (by rfl) ⟨1080224, by rfl⟩ : syracuseStep 1440299 = 2160449) B2160449
theorem B11663939 : Blo 956588 11663939 := bstep (se 1 (by rfl) ⟨8747954, by rfl⟩ : syracuseStep 11663939 = 17495909) B17495909
theorem B1440329 : Blo 956588 1440329 := bstep (se 2 (by rfl) ⟨540123, by rfl⟩ : syracuseStep 1440329 = 1080247) B1080247
theorem B1211051 : Blo 956588 1211051 := bstep (se 1 (by rfl) ⟨908288, by rfl⟩ : syracuseStep 1211051 = 1816577) B1816577
theorem B1079995 : Blo 956588 1079995 := bstep (se 1 (by rfl) ⟨809996, by rfl⟩ : syracuseStep 1079995 = 1619993) B1619993
theorem B1440443 : Blo 956588 1440443 := bstep (se 1 (by rfl) ⟨1080332, by rfl⟩ : syracuseStep 1440443 = 2160665) B2160665
theorem B1440503 : Blo 956588 1440503 := bstep (se 1 (by rfl) ⟨1080377, by rfl⟩ : syracuseStep 1440503 = 2160755) B2160755
theorem B2587403 : Blo 956588 2587403 := bstep (se 1 (by rfl) ⟨1940552, by rfl⟩ : syracuseStep 2587403 = 3881105) B3881105
theorem B1440527 : Blo 956588 1440527 := bstep (se 1 (by rfl) ⟨1080395, by rfl⟩ : syracuseStep 1440527 = 2160791) B2160791
theorem B1440569 : Blo 956588 1440569 := bstep (se 2 (by rfl) ⟨540213, by rfl⟩ : syracuseStep 1440569 = 1080427) B1080427
theorem B1440647 : Blo 956588 1440647 := bstep (se 1 (by rfl) ⟨1080485, by rfl⟩ : syracuseStep 1440647 = 2160971) B2160971
theorem B1440683 : Blo 956588 1440683 := bstep (se 1 (by rfl) ⟨1080512, by rfl⟩ : syracuseStep 1440683 = 2161025) B2161025
theorem B2423753 : Blo 956588 2423753 := bstep (se 2 (by rfl) ⟨908907, by rfl⟩ : syracuseStep 2423753 = 1817815) B1817815
theorem B1440713 : Blo 956588 1440713 := bstep (se 2 (by rfl) ⟨540267, by rfl⟩ : syracuseStep 1440713 = 1080535) B1080535
theorem B1440827 : Blo 956588 1440827 := bstep (se 1 (by rfl) ⟨1080620, by rfl⟩ : syracuseStep 1440827 = 2161241) B2161241
theorem B1211527 : Blo 956588 1211527 := bstep (se 1 (by rfl) ⟨908645, by rfl⟩ : syracuseStep 1211527 = 1817291) B1817291
theorem B1080463 : Blo 956588 1080463 := bstep (se 1 (by rfl) ⟨810347, by rfl⟩ : syracuseStep 1080463 = 1620695) B1620695
theorem B2424107 : Blo 956588 2424107 := bstep (se 1 (by rfl) ⟨1818080, by rfl⟩ : syracuseStep 2424107 = 3636161) B3636161
theorem B6323779 : Blo 956588 6323779 := bstep (se 1 (by rfl) ⟨4742834, by rfl⟩ : syracuseStep 6323779 = 9485669) B9485669
theorem B8289869 : Blo 956588 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B1212023 : Blo 956588 1212023 := bstep (se 1 (by rfl) ⟨909017, by rfl⟩ : syracuseStep 1212023 = 1818035) B1818035
theorem B2588431 : Blo 956588 2588431 := bstep (se 1 (by rfl) ⟨1941323, by rfl⟩ : syracuseStep 2588431 = 3882647) B3882647
theorem B1212175 : Blo 956588 1212175 := bstep (se 1 (by rfl) ⟨909131, by rfl⟩ : syracuseStep 1212175 = 1818263) B1818263
theorem B1212347 : Blo 956588 1212347 := bstep (se 1 (by rfl) ⟨909260, by rfl⟩ : syracuseStep 1212347 = 1818521) B1818521
theorem B6225977 : Blo 956588 6225977 := bstep (se 2 (by rfl) ⟨2334741, by rfl⟩ : syracuseStep 6225977 = 4669483) B4669483
theorem B4096115 : Blo 956588 4096115 := bstep (se 1 (by rfl) ⟨3072086, by rfl⟩ : syracuseStep 4096115 = 6144173) B6144173
theorem B15532195 : Blo 956588 15532195 := bstep (se 1 (by rfl) ⟨11649146, by rfl⟩ : syracuseStep 15532195 = 23298293) B23298293
theorem B2425079 : Blo 956588 2425079 := bstep (se 1 (by rfl) ⟨1818809, by rfl⟩ : syracuseStep 2425079 = 3637619) B3637619
theorem B3277199 : Blo 956588 3277199 := bstep (se 1 (by rfl) ⟨2457899, by rfl⟩ : syracuseStep 3277199 = 4915799) B4915799
theorem B1213051 : Blo 956588 1213051 := bstep (se 1 (by rfl) ⟨909788, by rfl⟩ : syracuseStep 1213051 = 1819577) B1819577
theorem B3638135 : Blo 956588 3638135 := bstep (se 1 (by rfl) ⟨2728601, by rfl⟩ : syracuseStep 3638135 = 5457203) B5457203
theorem B13305181 : Blo 956588 13305181 := bstep (se 3 (by rfl) ⟨2494721, by rfl⟩ : syracuseStep 13305181 = 4989443) B4989443
theorem B7013747 : Blo 956588 7013747 := bstep (se 1 (by rfl) ⟨5260310, by rfl⟩ : syracuseStep 7013747 = 10520621) B10520621
theorem B6555275 : Blo 956588 6555275 := bstep (se 1 (by rfl) ⟨4916456, by rfl⟩ : syracuseStep 6555275 = 9832913) B9832913
theorem B2426507 : Blo 956588 2426507 := bstep (se 1 (by rfl) ⟨1819880, by rfl⟩ : syracuseStep 2426507 = 3639761) B3639761
theorem B14419603 : Blo 956588 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B3639107 : Blo 956588 3639107 := bstep (se 1 (by rfl) ⟨2729330, by rfl⟩ : syracuseStep 3639107 = 5458661) B5458661
theorem B2426719 : Blo 956588 2426719 := bstep (se 1 (by rfl) ⟨1820039, by rfl⟩ : syracuseStep 2426719 = 3640079) B3640079
theorem B4851575 : Blo 956588 4851575 := bstep (se 1 (by rfl) ⟨3638681, by rfl⟩ : syracuseStep 4851575 = 7277363) B7277363
theorem B6129593 : Blo 956588 6129593 := bstep (se 2 (by rfl) ⟨2298597, by rfl⟩ : syracuseStep 6129593 = 4597195) B4597195
theorem B3639563 : Blo 956588 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B6130025 : Blo 956588 6130025 := bstep (se 2 (by rfl) ⟨2298759, by rfl⟩ : syracuseStep 6130025 = 4597519) B4597519
theorem B2492891 : Blo 956588 2492891 := bstep (se 1 (by rfl) ⟨1869668, by rfl⟩ : syracuseStep 2492891 = 3739337) B3739337
theorem B1214939 : Blo 956588 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B66292343 : Blo 956588 66292343 := bstep (se 1 (by rfl) ⟨49719257, by rfl⟩ : syracuseStep 66292343 = 99438515) B99438515
theorem B5835473 : Blo 956588 5835473 := bstep (se 2 (by rfl) ⟨2188302, by rfl⟩ : syracuseStep 5835473 = 4376605) B4376605
theorem B2427641 : Blo 956588 2427641 := bstep (se 2 (by rfl) ⟨910365, by rfl⟩ : syracuseStep 2427641 = 1820731) B1820731
theorem B3640247 : Blo 956588 3640247 := bstep (se 1 (by rfl) ⟨2730185, by rfl⟩ : syracuseStep 3640247 = 5460371) B5460371
theorem B1215415 : Blo 956588 1215415 := bstep (se 1 (by rfl) ⟨911561, by rfl⟩ : syracuseStep 1215415 = 1823123) B1823123
theorem B13798673 : Blo 956588 13798673 := bstep (se 2 (by rfl) ⟨5174502, by rfl⟩ : syracuseStep 13798673 = 10349005) B10349005
theorem B1150303 : Blo 956588 1150303 := bstep (se 1 (by rfl) ⟨862727, by rfl⟩ : syracuseStep 1150303 = 1725455) B1725455
theorem B2428289 : Blo 956588 2428289 := bstep (se 2 (by rfl) ⟨910608, by rfl⟩ : syracuseStep 2428289 = 1821217) B1821217
theorem B7376471 : Blo 956588 7376471 := bstep (se 1 (by rfl) ⟨5532353, by rfl⟩ : syracuseStep 7376471 = 11064707) B11064707
theorem B34967159 : Blo 956588 34967159 := bstep (se 1 (by rfl) ⟨26225369, by rfl⟩ : syracuseStep 34967159 = 52450739) B52450739
theorem B3641021 : Blo 956588 3641021 := bstep (se 3 (by rfl) ⟨682691, by rfl⟩ : syracuseStep 3641021 = 1365383) B1365383
theorem B2592505 : Blo 956588 2592505 := bstep (se 2 (by rfl) ⟨972189, by rfl⟩ : syracuseStep 2592505 = 1944379) B1944379
theorem B2658475 : Blo 956588 2658475 := bstep (se 1 (by rfl) ⟨1993856, by rfl⟩ : syracuseStep 2658475 = 3987713) B3987713
theorem B2429099 : Blo 956588 2429099 := bstep (se 1 (by rfl) ⟨1821824, by rfl⟩ : syracuseStep 2429099 = 3643649) B3643649
theorem B7278821 : Blo 956588 7278821 := bstep (se 4 (by rfl) ⟨682389, by rfl⟩ : syracuseStep 7278821 = 1364779) B1364779
theorem B12980555 : Blo 956588 12980555 := bstep (se 1 (by rfl) ⟨9735416, by rfl⟩ : syracuseStep 12980555 = 19470833) B19470833
theorem B3641705 : Blo 956588 3641705 := bstep (se 2 (by rfl) ⟨1365639, by rfl⟩ : syracuseStep 3641705 = 2731279) B2731279
theorem B6132257 : Blo 956588 6132257 := bstep (se 2 (by rfl) ⟨2299596, by rfl⟩ : syracuseStep 6132257 = 4599193) B4599193
theorem B9835181 : Blo 956588 9835181 := bstep (se 3 (by rfl) ⟨1844096, by rfl⟩ : syracuseStep 9835181 = 3688193) B3688193
theorem B20746961 : Blo 956588 20746961 := bstep (se 2 (by rfl) ⟨7780110, by rfl⟩ : syracuseStep 20746961 = 15560221) B15560221
theorem B2429959 : Blo 956588 2429959 := bstep (se 1 (by rfl) ⟨1822469, by rfl⟩ : syracuseStep 2429959 = 3644939) B3644939
theorem B11047985 : Blo 956588 11047985 := bstep (se 2 (by rfl) ⟨4142994, by rfl⟩ : syracuseStep 11047985 = 8285989) B8285989
theorem B8295695 : Blo 956588 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B2430587 : Blo 956588 2430587 := bstep (se 1 (by rfl) ⟨1822940, by rfl⟩ : syracuseStep 2430587 = 3645881) B3645881
theorem B5183327 : Blo 956588 5183327 := bstep (se 1 (by rfl) ⟨3887495, by rfl⟩ : syracuseStep 5183327 = 7774991) B7774991
theorem B2430881 : Blo 956588 2430881 := bstep (se 2 (by rfl) ⟨911580, by rfl⟩ : syracuseStep 2430881 = 1823161) B1823161
theorem B14784599 : Blo 956588 14784599 := bstep (se 1 (by rfl) ⟨11088449, by rfl⟩ : syracuseStep 14784599 = 22176899) B22176899
theorem B3545245 : Blo 956588 3545245 := bstep (se 3 (by rfl) ⟨664733, by rfl⟩ : syracuseStep 3545245 = 1329467) B1329467
theorem B956591 : Blo 956588 956591 := bstep (se 1 (by rfl) ⟨717443, by rfl⟩ : syracuseStep 956591 = 1434887) B1434887
theorem B956615 : Blo 956588 956615 := bstep (se 1 (by rfl) ⟨717461, by rfl⟩ : syracuseStep 956615 = 1434923) B1434923
theorem B956635 : Blo 956588 956635 := bstep (se 1 (by rfl) ⟨717476, by rfl⟩ : syracuseStep 956635 = 1434953) B1434953
theorem B956711 : Blo 956588 956711 := bstep (se 1 (by rfl) ⟨717533, by rfl⟩ : syracuseStep 956711 = 1435067) B1435067
theorem B956751 : Blo 956588 956751 := bstep (se 1 (by rfl) ⟨717563, by rfl⟩ : syracuseStep 956751 = 1435127) B1435127
theorem B956767 : Blo 956588 956767 := bstep (se 1 (by rfl) ⟨717575, by rfl⟩ : syracuseStep 956767 = 1435151) B1435151
theorem B956795 : Blo 956588 956795 := bstep (se 1 (by rfl) ⟨717596, by rfl⟩ : syracuseStep 956795 = 1435193) B1435193
theorem B956847 : Blo 956588 956847 := bstep (se 1 (by rfl) ⟨717635, by rfl⟩ : syracuseStep 956847 = 1435271) B1435271
theorem B956871 : Blo 956588 956871 := bstep (se 1 (by rfl) ⟨717653, by rfl⟩ : syracuseStep 956871 = 1435307) B1435307
theorem B956891 : Blo 956588 956891 := bstep (se 1 (by rfl) ⟨717668, by rfl⟩ : syracuseStep 956891 = 1435337) B1435337
theorem B3643937 : Blo 956588 3643937 := bstep (se 2 (by rfl) ⟨1366476, by rfl⟩ : syracuseStep 3643937 = 2732953) B2732953
theorem B956967 : Blo 956588 956967 := bstep (se 1 (by rfl) ⟨717725, by rfl⟩ : syracuseStep 956967 = 1435451) B1435451
theorem B957007 : Blo 956588 957007 := bstep (se 1 (by rfl) ⟨717755, by rfl⟩ : syracuseStep 957007 = 1435511) B1435511
theorem B957023 : Blo 956588 957023 := bstep (se 1 (by rfl) ⟨717767, by rfl⟩ : syracuseStep 957023 = 1435535) B1435535
theorem B957051 : Blo 956588 957051 := bstep (se 1 (by rfl) ⟨717788, by rfl⟩ : syracuseStep 957051 = 1435577) B1435577
theorem B957103 : Blo 956588 957103 := bstep (se 1 (by rfl) ⟨717827, by rfl⟩ : syracuseStep 957103 = 1435655) B1435655
theorem B957127 : Blo 956588 957127 := bstep (se 1 (by rfl) ⟨717845, by rfl⟩ : syracuseStep 957127 = 1435691) B1435691
theorem B957147 : Blo 956588 957147 := bstep (se 1 (by rfl) ⟨717860, by rfl⟩ : syracuseStep 957147 = 1435721) B1435721
theorem B2595577 : Blo 956588 2595577 := bstep (se 2 (by rfl) ⟨973341, by rfl⟩ : syracuseStep 2595577 = 1946683) B1946683
theorem B957223 : Blo 956588 957223 := bstep (se 1 (by rfl) ⟨717917, by rfl⟩ : syracuseStep 957223 = 1435835) B1435835
theorem B957263 : Blo 956588 957263 := bstep (se 1 (by rfl) ⟨717947, by rfl⟩ : syracuseStep 957263 = 1435895) B1435895
theorem B957279 : Blo 956588 957279 := bstep (se 1 (by rfl) ⟨717959, by rfl⟩ : syracuseStep 957279 = 1435919) B1435919
theorem B957307 : Blo 956588 957307 := bstep (se 1 (by rfl) ⟨717980, by rfl⟩ : syracuseStep 957307 = 1435961) B1435961
theorem B957359 : Blo 956588 957359 := bstep (se 1 (by rfl) ⟨718019, by rfl⟩ : syracuseStep 957359 = 1436039) B1436039
theorem B4856759 : Blo 956588 4856759 := bstep (se 1 (by rfl) ⟨3642569, by rfl⟩ : syracuseStep 4856759 = 7285139) B7285139
theorem B957383 : Blo 956588 957383 := bstep (se 1 (by rfl) ⟨718037, by rfl⟩ : syracuseStep 957383 = 1436075) B1436075
theorem B957403 : Blo 956588 957403 := bstep (se 1 (by rfl) ⟨718052, by rfl⟩ : syracuseStep 957403 = 1436105) B1436105
theorem B4922369 : Blo 956588 4922369 := bstep (se 2 (by rfl) ⟨1845888, by rfl⟩ : syracuseStep 4922369 = 3691777) B3691777
theorem B3644423 : Blo 956588 3644423 := bstep (se 1 (by rfl) ⟨2733317, by rfl⟩ : syracuseStep 3644423 = 5466635) B5466635
theorem B957479 : Blo 956588 957479 := bstep (se 1 (by rfl) ⟨718109, by rfl⟩ : syracuseStep 957479 = 1436219) B1436219
theorem B957519 : Blo 956588 957519 := bstep (se 1 (by rfl) ⟨718139, by rfl⟩ : syracuseStep 957519 = 1436279) B1436279
theorem B957535 : Blo 956588 957535 := bstep (se 1 (by rfl) ⟨718151, by rfl⟩ : syracuseStep 957535 = 1436303) B1436303
theorem B957563 : Blo 956588 957563 := bstep (se 1 (by rfl) ⟨718172, by rfl⟩ : syracuseStep 957563 = 1436345) B1436345
theorem B957615 : Blo 956588 957615 := bstep (se 1 (by rfl) ⟨718211, by rfl⟩ : syracuseStep 957615 = 1436423) B1436423
theorem B957639 : Blo 956588 957639 := bstep (se 1 (by rfl) ⟨718229, by rfl⟩ : syracuseStep 957639 = 1436459) B1436459
theorem B957659 : Blo 956588 957659 := bstep (se 1 (by rfl) ⟨718244, by rfl⟩ : syracuseStep 957659 = 1436489) B1436489
theorem B957735 : Blo 956588 957735 := bstep (se 1 (by rfl) ⟨718301, by rfl⟩ : syracuseStep 957735 = 1436603) B1436603
theorem B957775 : Blo 956588 957775 := bstep (se 1 (by rfl) ⟨718331, by rfl⟩ : syracuseStep 957775 = 1436663) B1436663
theorem B957791 : Blo 956588 957791 := bstep (se 1 (by rfl) ⟨718343, by rfl⟩ : syracuseStep 957791 = 1436687) B1436687
theorem B957819 : Blo 956588 957819 := bstep (se 1 (by rfl) ⟨718364, by rfl⟩ : syracuseStep 957819 = 1436729) B1436729
theorem B957871 : Blo 956588 957871 := bstep (se 1 (by rfl) ⟨718403, by rfl⟩ : syracuseStep 957871 = 1436807) B1436807
theorem B957895 : Blo 956588 957895 := bstep (se 1 (by rfl) ⟨718421, by rfl⟩ : syracuseStep 957895 = 1436843) B1436843
theorem B957915 : Blo 956588 957915 := bstep (se 1 (by rfl) ⟨718436, by rfl⟩ : syracuseStep 957915 = 1436873) B1436873
theorem B3644909 : Blo 956588 3644909 := bstep (se 3 (by rfl) ⟨683420, by rfl⟩ : syracuseStep 3644909 = 1366841) B1366841
theorem B957991 : Blo 956588 957991 := bstep (se 1 (by rfl) ⟨718493, by rfl⟩ : syracuseStep 957991 = 1436987) B1436987
theorem B958031 : Blo 956588 958031 := bstep (se 1 (by rfl) ⟨718523, by rfl⟩ : syracuseStep 958031 = 1437047) B1437047
theorem B958047 : Blo 956588 958047 := bstep (se 1 (by rfl) ⟨718535, by rfl⟩ : syracuseStep 958047 = 1437071) B1437071
theorem B958075 : Blo 956588 958075 := bstep (se 1 (by rfl) ⟨718556, by rfl⟩ : syracuseStep 958075 = 1437113) B1437113
theorem B958127 : Blo 956588 958127 := bstep (se 1 (by rfl) ⟨718595, by rfl⟩ : syracuseStep 958127 = 1437191) B1437191
theorem B958151 : Blo 956588 958151 := bstep (se 1 (by rfl) ⟨718613, by rfl⟩ : syracuseStep 958151 = 1437227) B1437227
theorem B958171 : Blo 956588 958171 := bstep (se 1 (by rfl) ⟨718628, by rfl⟩ : syracuseStep 958171 = 1437257) B1437257
theorem B958247 : Blo 956588 958247 := bstep (se 1 (by rfl) ⟨718685, by rfl⟩ : syracuseStep 958247 = 1437371) B1437371
theorem B958287 : Blo 956588 958287 := bstep (se 1 (by rfl) ⟨718715, by rfl⟩ : syracuseStep 958287 = 1437431) B1437431
theorem B958303 : Blo 956588 958303 := bstep (se 1 (by rfl) ⟨718727, by rfl⟩ : syracuseStep 958303 = 1437455) B1437455
theorem B7380845 : Blo 956588 7380845 := bstep (se 3 (by rfl) ⟨1383908, by rfl⟩ : syracuseStep 7380845 = 2767817) B2767817
theorem B958331 : Blo 956588 958331 := bstep (se 1 (by rfl) ⟨718748, by rfl⟩ : syracuseStep 958331 = 1437497) B1437497
theorem B958383 : Blo 956588 958383 := bstep (se 1 (by rfl) ⟨718787, by rfl⟩ : syracuseStep 958383 = 1437575) B1437575
theorem B2367407 : Blo 956588 2367407 := bstep (se 1 (by rfl) ⟨1775555, by rfl⟩ : syracuseStep 2367407 = 3551111) B3551111
theorem B958407 : Blo 956588 958407 := bstep (se 1 (by rfl) ⟨718805, by rfl⟩ : syracuseStep 958407 = 1437611) B1437611
theorem B958427 : Blo 956588 958427 := bstep (se 1 (by rfl) ⟨718820, by rfl⟩ : syracuseStep 958427 = 1437641) B1437641
theorem B958503 : Blo 956588 958503 := bstep (se 1 (by rfl) ⟨718877, by rfl⟩ : syracuseStep 958503 = 1437755) B1437755
theorem B1941583 : Blo 956588 1941583 := bstep (se 1 (by rfl) ⟨1456187, by rfl⟩ : syracuseStep 1941583 = 2912375) B2912375
theorem B958543 : Blo 956588 958543 := bstep (se 1 (by rfl) ⟨718907, by rfl⟩ : syracuseStep 958543 = 1437815) B1437815
theorem B958559 : Blo 956588 958559 := bstep (se 1 (by rfl) ⟨718919, by rfl⟩ : syracuseStep 958559 = 1437839) B1437839
theorem B958587 : Blo 956588 958587 := bstep (se 1 (by rfl) ⟨718940, by rfl⟩ : syracuseStep 958587 = 1437881) B1437881
theorem B3645593 : Blo 956588 3645593 := bstep (se 2 (by rfl) ⟨1367097, by rfl⟩ : syracuseStep 3645593 = 2734195) B2734195
theorem B958639 : Blo 956588 958639 := bstep (se 1 (by rfl) ⟨718979, by rfl⟩ : syracuseStep 958639 = 1437959) B1437959
theorem B958663 : Blo 956588 958663 := bstep (se 1 (by rfl) ⟨718997, by rfl⟩ : syracuseStep 958663 = 1437995) B1437995
theorem B958683 : Blo 956588 958683 := bstep (se 1 (by rfl) ⟨719012, by rfl⟩ : syracuseStep 958683 = 1438025) B1438025
theorem B958759 : Blo 956588 958759 := bstep (se 1 (by rfl) ⟨719069, by rfl⟩ : syracuseStep 958759 = 1438139) B1438139
theorem B958799 : Blo 956588 958799 := bstep (se 1 (by rfl) ⟨719099, by rfl⟩ : syracuseStep 958799 = 1438199) B1438199
theorem B958815 : Blo 956588 958815 := bstep (se 1 (by rfl) ⟨719111, by rfl⟩ : syracuseStep 958815 = 1438223) B1438223
theorem B4858217 : Blo 956588 4858217 := bstep (se 2 (by rfl) ⟨1821831, by rfl⟩ : syracuseStep 4858217 = 3643663) B3643663
theorem B958843 : Blo 956588 958843 := bstep (se 1 (by rfl) ⟨719132, by rfl⟩ : syracuseStep 958843 = 1438265) B1438265
theorem B958895 : Blo 956588 958895 := bstep (se 1 (by rfl) ⟨719171, by rfl⟩ : syracuseStep 958895 = 1438343) B1438343
theorem B958919 : Blo 956588 958919 := bstep (se 1 (by rfl) ⟨719189, by rfl⟩ : syracuseStep 958919 = 1438379) B1438379
theorem B958939 : Blo 956588 958939 := bstep (se 1 (by rfl) ⟨719204, by rfl⟩ : syracuseStep 958939 = 1438409) B1438409
theorem B2302451 : Blo 956588 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B1614343 : Blo 956588 1614343 := bstep (se 1 (by rfl) ⟨1210757, by rfl⟩ : syracuseStep 1614343 = 2421515) B2421515
theorem B959015 : Blo 956588 959015 := bstep (se 1 (by rfl) ⟨719261, by rfl⟩ : syracuseStep 959015 = 1438523) B1438523
theorem B959055 : Blo 956588 959055 := bstep (se 1 (by rfl) ⟨719291, by rfl⟩ : syracuseStep 959055 = 1438583) B1438583
theorem B959071 : Blo 956588 959071 := bstep (se 1 (by rfl) ⟨719303, by rfl⟩ : syracuseStep 959071 = 1438607) B1438607
theorem B959099 : Blo 956588 959099 := bstep (se 1 (by rfl) ⟨719324, by rfl⟩ : syracuseStep 959099 = 1438649) B1438649
theorem B959151 : Blo 956588 959151 := bstep (se 1 (by rfl) ⟨719363, by rfl⟩ : syracuseStep 959151 = 1438727) B1438727
theorem B2728637 : Blo 956588 2728637 := bstep (se 3 (by rfl) ⟨511619, by rfl⟩ : syracuseStep 2728637 = 1023239) B1023239
theorem B2630333 : Blo 956588 2630333 := bstep (se 3 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 2630333 = 986375) B986375
theorem B959175 : Blo 956588 959175 := bstep (se 1 (by rfl) ⟨719381, by rfl⟩ : syracuseStep 959175 = 1438763) B1438763
theorem B959195 : Blo 956588 959195 := bstep (se 1 (by rfl) ⟨719396, by rfl⟩ : syracuseStep 959195 = 1438793) B1438793
theorem B959271 : Blo 956588 959271 := bstep (se 1 (by rfl) ⟨719453, by rfl⟩ : syracuseStep 959271 = 1438907) B1438907
theorem B959311 : Blo 956588 959311 := bstep (se 1 (by rfl) ⟨719483, by rfl⟩ : syracuseStep 959311 = 1438967) B1438967
theorem B959327 : Blo 956588 959327 := bstep (se 1 (by rfl) ⟨719495, by rfl⟩ : syracuseStep 959327 = 1438991) B1438991
theorem B959355 : Blo 956588 959355 := bstep (se 1 (by rfl) ⟨719516, by rfl⟩ : syracuseStep 959355 = 1439033) B1439033
theorem B959407 : Blo 956588 959407 := bstep (se 1 (by rfl) ⟨719555, by rfl⟩ : syracuseStep 959407 = 1439111) B1439111
theorem B121086899 : Blo 956588 121086899 := bstep (se 1 (by rfl) ⟨90815174, by rfl⟩ : syracuseStep 121086899 = 181630349) B181630349
theorem B1614775 : Blo 956588 1614775 := bstep (se 1 (by rfl) ⟨1211081, by rfl⟩ : syracuseStep 1614775 = 2422163) B2422163
theorem B3285947 : Blo 956588 3285947 := bstep (se 1 (by rfl) ⟨2464460, by rfl⟩ : syracuseStep 3285947 = 4928921) B4928921
theorem B959431 : Blo 956588 959431 := bstep (se 1 (by rfl) ⟨719573, by rfl⟩ : syracuseStep 959431 = 1439147) B1439147
theorem B959451 : Blo 956588 959451 := bstep (se 1 (by rfl) ⟨719588, by rfl⟩ : syracuseStep 959451 = 1439177) B1439177
theorem B959527 : Blo 956588 959527 := bstep (se 1 (by rfl) ⟨719645, by rfl⟩ : syracuseStep 959527 = 1439291) B1439291
theorem B959567 : Blo 956588 959567 := bstep (se 1 (by rfl) ⟨719675, by rfl⟩ : syracuseStep 959567 = 1439351) B1439351
theorem B959583 : Blo 956588 959583 := bstep (se 1 (by rfl) ⟨719687, by rfl⟩ : syracuseStep 959583 = 1439375) B1439375
theorem B3646579 : Blo 956588 3646579 := bstep (se 1 (by rfl) ⟨2734934, by rfl⟩ : syracuseStep 3646579 = 5469869) B5469869
theorem B1614971 : Blo 956588 1614971 := bstep (se 1 (by rfl) ⟨1211228, by rfl⟩ : syracuseStep 1614971 = 2422457) B2422457
theorem B959611 : Blo 956588 959611 := bstep (se 1 (by rfl) ⟨719708, by rfl⟩ : syracuseStep 959611 = 1439417) B1439417
theorem B959663 : Blo 956588 959663 := bstep (se 1 (by rfl) ⟨719747, by rfl⟩ : syracuseStep 959663 = 1439495) B1439495
theorem B959687 : Blo 956588 959687 := bstep (se 1 (by rfl) ⟨719765, by rfl⟩ : syracuseStep 959687 = 1439531) B1439531
theorem B959707 : Blo 956588 959707 := bstep (se 1 (by rfl) ⟨719780, by rfl⟩ : syracuseStep 959707 = 1439561) B1439561
theorem B4596983 : Blo 956588 4596983 := bstep (se 1 (by rfl) ⟨3447737, by rfl⟩ : syracuseStep 4596983 = 6895475) B6895475
theorem B1844473 : Blo 956588 1844473 := bstep (se 2 (by rfl) ⟨691677, by rfl⟩ : syracuseStep 1844473 = 1383355) B1383355
theorem B959783 : Blo 956588 959783 := bstep (se 1 (by rfl) ⟨719837, by rfl⟩ : syracuseStep 959783 = 1439675) B1439675
theorem B959823 : Blo 956588 959823 := bstep (se 1 (by rfl) ⟨719867, by rfl⟩ : syracuseStep 959823 = 1439735) B1439735
theorem B959839 : Blo 956588 959839 := bstep (se 1 (by rfl) ⟨719879, by rfl⟩ : syracuseStep 959839 = 1439759) B1439759
theorem B959867 : Blo 956588 959867 := bstep (se 1 (by rfl) ⟨719900, by rfl⟩ : syracuseStep 959867 = 1439801) B1439801
theorem B959919 : Blo 956588 959919 := bstep (se 1 (by rfl) ⟨719939, by rfl⟩ : syracuseStep 959919 = 1439879) B1439879
theorem B959943 : Blo 956588 959943 := bstep (se 1 (by rfl) ⟨719957, by rfl⟩ : syracuseStep 959943 = 1439915) B1439915
theorem B4597211 : Blo 956588 4597211 := bstep (se 1 (by rfl) ⟨3447908, by rfl⟩ : syracuseStep 4597211 = 6895817) B6895817
theorem B959963 : Blo 956588 959963 := bstep (se 1 (by rfl) ⟨719972, by rfl⟩ : syracuseStep 959963 = 1439945) B1439945
theorem B1615369 : Blo 956588 1615369 := bstep (se 2 (by rfl) ⟨605763, by rfl⟩ : syracuseStep 1615369 = 1211527) B1211527
theorem B960039 : Blo 956588 960039 := bstep (se 1 (by rfl) ⟨720029, by rfl⟩ : syracuseStep 960039 = 1440059) B1440059
theorem B960079 : Blo 956588 960079 := bstep (se 1 (by rfl) ⟨720059, by rfl⟩ : syracuseStep 960079 = 1440119) B1440119
theorem B960095 : Blo 956588 960095 := bstep (se 1 (by rfl) ⟨720071, by rfl⟩ : syracuseStep 960095 = 1440143) B1440143
theorem B960123 : Blo 956588 960123 := bstep (se 1 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 960123 = 1440185) B1440185
theorem B1615531 : Blo 956588 1615531 := bstep (se 1 (by rfl) ⟨1211648, by rfl⟩ : syracuseStep 1615531 = 2423297) B2423297
theorem B960175 : Blo 956588 960175 := bstep (se 1 (by rfl) ⟨720131, by rfl⟩ : syracuseStep 960175 = 1440263) B1440263
theorem B960199 : Blo 956588 960199 := bstep (se 1 (by rfl) ⟨720149, by rfl⟩ : syracuseStep 960199 = 1440299) B1440299
theorem B7775959 : Blo 956588 7775959 := bstep (se 1 (by rfl) ⟨5831969, by rfl⟩ : syracuseStep 7775959 = 11663939) B11663939
theorem B960219 : Blo 956588 960219 := bstep (se 1 (by rfl) ⟨720164, by rfl⟩ : syracuseStep 960219 = 1440329) B1440329
theorem B960295 : Blo 956588 960295 := bstep (se 1 (by rfl) ⟨720221, by rfl⟩ : syracuseStep 960295 = 1440443) B1440443
theorem B960335 : Blo 956588 960335 := bstep (se 1 (by rfl) ⟨720251, by rfl⟩ : syracuseStep 960335 = 1440503) B1440503
theorem B960351 : Blo 956588 960351 := bstep (se 1 (by rfl) ⟨720263, by rfl⟩ : syracuseStep 960351 = 1440527) B1440527
theorem B960379 : Blo 956588 960379 := bstep (se 1 (by rfl) ⟨720284, by rfl⟩ : syracuseStep 960379 = 1440569) B1440569
theorem B960431 : Blo 956588 960431 := bstep (se 1 (by rfl) ⟨720323, by rfl⟩ : syracuseStep 960431 = 1440647) B1440647
theorem B960455 : Blo 956588 960455 := bstep (se 1 (by rfl) ⟨720341, by rfl⟩ : syracuseStep 960455 = 1440683) B1440683
theorem B1615835 : Blo 956588 1615835 := bstep (se 1 (by rfl) ⟨1211876, by rfl⟩ : syracuseStep 1615835 = 2423753) B2423753
theorem B960475 : Blo 956588 960475 := bstep (se 1 (by rfl) ⟨720356, by rfl⟩ : syracuseStep 960475 = 1440713) B1440713
theorem B960551 : Blo 956588 960551 := bstep (se 1 (by rfl) ⟨720413, by rfl⟩ : syracuseStep 960551 = 1440827) B1440827
theorem B8431705 : Blo 956588 8431705 := bstep (se 2 (by rfl) ⟨3161889, by rfl⟩ : syracuseStep 8431705 = 6323779) B6323779
theorem B2959517 : Blo 956588 2959517 := bstep (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) B1109819
theorem B1616071 : Blo 956588 1616071 := bstep (se 1 (by rfl) ⟨1212053, by rfl⟩ : syracuseStep 1616071 = 2424107) B2424107
theorem B3451241 : Blo 956588 3451241 := bstep (se 2 (by rfl) ⟨1294215, by rfl⟩ : syracuseStep 3451241 = 2588431) B2588431
theorem B1616233 : Blo 956588 1616233 := bstep (se 2 (by rfl) ⟨606087, by rfl⟩ : syracuseStep 1616233 = 1212175) B1212175
theorem B4663817 : Blo 956588 4663817 := bstep (se 2 (by rfl) ⟨1748931, by rfl⟩ : syracuseStep 4663817 = 3497863) B3497863
theorem B1616827 : Blo 956588 1616827 := bstep (se 1 (by rfl) ⟨1212620, by rfl⟩ : syracuseStep 1616827 = 2425241) B2425241
theorem B1616935 : Blo 956588 1616935 := bstep (se 1 (by rfl) ⟨1212701, by rfl⟩ : syracuseStep 1616935 = 2425403) B2425403
theorem B6139151 : Blo 956588 6139151 := bstep (se 1 (by rfl) ⟨4604363, by rfl⟩ : syracuseStep 6139151 = 9208727) B9208727
theorem B1617259 : Blo 956588 1617259 := bstep (se 1 (by rfl) ⟨1212944, by rfl⟩ : syracuseStep 1617259 = 2425889) B2425889
theorem B4926845 : Blo 956588 4926845 := bstep (se 3 (by rfl) ⟨923783, by rfl⟩ : syracuseStep 4926845 = 1847567) B1847567
theorem B1945127 : Blo 956588 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B118042181 : Blo 956588 118042181 := bstep (se 4 (by rfl) ⟨11066454, by rfl⟩ : syracuseStep 118042181 = 22132909) B22132909
theorem B4599443 : Blo 956588 4599443 := bstep (se 1 (by rfl) ⟨3449582, by rfl⟩ : syracuseStep 4599443 = 6899165) B6899165
theorem B2731769 : Blo 956588 2731769 := bstep (se 2 (by rfl) ⟨1024413, by rfl⟩ : syracuseStep 2731769 = 2048827) B2048827
theorem B4599595 : Blo 956588 4599595 := bstep (se 1 (by rfl) ⟨3449696, by rfl⟩ : syracuseStep 4599595 = 6899393) B6899393
theorem B4599671 : Blo 956588 4599671 := bstep (se 1 (by rfl) ⟨3449753, by rfl⟩ : syracuseStep 4599671 = 6899507) B6899507
theorem B9220027 : Blo 956588 9220027 := bstep (se 1 (by rfl) ⟨6915020, by rfl⟩ : syracuseStep 9220027 = 13830041) B13830041
theorem B2305979 : Blo 956588 2305979 := bstep (se 1 (by rfl) ⟨1729484, by rfl⟩ : syracuseStep 2305979 = 3458969) B3458969
theorem B1618319 : Blo 956588 1618319 := bstep (se 1 (by rfl) ⟨1213739, by rfl⟩ : syracuseStep 1618319 = 2427479) B2427479
theorem B1618555 : Blo 956588 1618555 := bstep (se 1 (by rfl) ⟨1213916, by rfl⟩ : syracuseStep 1618555 = 2427833) B2427833
theorem B3322799 : Blo 956588 3322799 := bstep (se 1 (by rfl) ⟨2492099, by rfl⟩ : syracuseStep 3322799 = 4984199) B4984199
theorem B2733227 : Blo 956588 2733227 := bstep (se 1 (by rfl) ⟨2049920, by rfl⟩ : syracuseStep 2733227 = 4099841) B4099841
theorem B7288055 : Blo 956588 7288055 := bstep (se 1 (by rfl) ⟨5466041, by rfl⟩ : syracuseStep 7288055 = 10932083) B10932083
theorem B13284773 : Blo 956588 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B1619419 : Blo 956588 1619419 := bstep (se 1 (by rfl) ⟨1214564, by rfl⟩ : syracuseStep 1619419 = 2429129) B2429129
theorem B13809163 : Blo 956588 13809163 := bstep (se 1 (by rfl) ⟨10356872, by rfl⟩ : syracuseStep 13809163 = 20713745) B20713745
theorem B1816121 : Blo 956588 1816121 := bstep (se 2 (by rfl) ⟨681045, by rfl⟩ : syracuseStep 1816121 = 1362091) B1362091
theorem B4601441 : Blo 956588 4601441 := bstep (se 2 (by rfl) ⟨1725540, by rfl⟩ : syracuseStep 4601441 = 3451081) B3451081
theorem B7288541 : Blo 956588 7288541 := bstep (se 3 (by rfl) ⟨1366601, by rfl⟩ : syracuseStep 7288541 = 2733203) B2733203
theorem B6141689 : Blo 956588 6141689 := bstep (se 2 (by rfl) ⟨2303133, by rfl⟩ : syracuseStep 6141689 = 4606267) B4606267
theorem B3454829 : Blo 956588 3454829 := bstep (se 3 (by rfl) ⟨647780, by rfl⟩ : syracuseStep 3454829 = 1295561) B1295561
theorem B6141815 : Blo 956588 6141815 := bstep (se 1 (by rfl) ⟨4606361, by rfl⟩ : syracuseStep 6141815 = 9212723) B9212723
theorem B49887179 : Blo 956588 49887179 := bstep (se 1 (by rfl) ⟨37415384, by rfl⟩ : syracuseStep 49887179 = 74830769) B74830769
theorem B5453831 : Blo 956588 5453831 := bstep (se 1 (by rfl) ⟨4090373, by rfl⟩ : syracuseStep 5453831 = 8180747) B8180747
theorem B1620047 : Blo 956588 1620047 := bstep (se 1 (by rfl) ⟨1215035, by rfl⟩ : syracuseStep 1620047 = 2430071) B2430071
theorem B1554871 : Blo 956588 1554871 := bstep (se 1 (by rfl) ⟨1166153, by rfl⟩ : syracuseStep 1554871 = 2332307) B2332307
theorem B3324563 : Blo 956588 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B2046827 : Blo 956588 2046827 := bstep (se 1 (by rfl) ⟨1535120, by rfl⟩ : syracuseStep 2046827 = 3070241) B3070241
theorem B1620911 : Blo 956588 1620911 := bstep (se 1 (by rfl) ⟨1215683, by rfl⟩ : syracuseStep 1620911 = 2431367) B2431367
theorem B52575293 : Blo 956588 52575293 := bstep (se 3 (by rfl) ⟨9857867, by rfl⟩ : syracuseStep 52575293 = 19715735) B19715735
theorem B6143147 : Blo 956588 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B7781669 : Blo 956588 7781669 := bstep (se 4 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 7781669 = 1459063) B1459063
theorem B1818119 : Blo 956588 1818119 := bstep (se 1 (by rfl) ⟨1363589, by rfl⟩ : syracuseStep 1818119 = 2727179) B2727179
theorem B1818551 : Blo 956588 1818551 := bstep (se 1 (by rfl) ⟨1363913, by rfl⟩ : syracuseStep 1818551 = 2727827) B2727827
theorem B10371149 : Blo 956588 10371149 := bstep (se 3 (by rfl) ⟨1944590, by rfl⟩ : syracuseStep 10371149 = 3889181) B3889181
theorem B1818703 : Blo 956588 1818703 := bstep (se 1 (by rfl) ⟨1364027, by rfl⟩ : syracuseStep 1818703 = 2728055) B2728055
theorem B3457367 : Blo 956588 3457367 := bstep (se 1 (by rfl) ⟨2593025, by rfl⟩ : syracuseStep 3457367 = 5186051) B5186051
theorem B9355799 : Blo 956588 9355799 := bstep (se 1 (by rfl) ⟨7016849, by rfl⟩ : syracuseStep 9355799 = 14033699) B14033699
theorem B12305155 : Blo 956588 12305155 := bstep (se 1 (by rfl) ⟨9228866, by rfl⟩ : syracuseStep 12305155 = 18457733) B18457733
theorem B5456747 : Blo 956588 5456747 := bstep (se 1 (by rfl) ⟨4092560, by rfl⟩ : syracuseStep 5456747 = 8185121) B8185121
theorem B1754075 : Blo 956588 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B3884203 : Blo 956588 3884203 := bstep (se 1 (by rfl) ⟨2913152, by rfl⟩ : syracuseStep 3884203 = 5826305) B5826305
theorem B1820009 : Blo 956588 1820009 := bstep (se 2 (by rfl) ⟨682503, by rfl⟩ : syracuseStep 1820009 = 1365007) B1365007
theorem B1230263 : Blo 956588 1230263 := bstep (se 1 (by rfl) ⟨922697, by rfl⟩ : syracuseStep 1230263 = 1845395) B1845395
theorem B3229307 : Blo 956588 3229307 := bstep (se 1 (by rfl) ⟨2421980, by rfl⟩ : syracuseStep 3229307 = 4843961) B4843961
theorem B8308439 : Blo 956588 8308439 := bstep (se 1 (by rfl) ⟨6231329, by rfl⟩ : syracuseStep 8308439 = 12462659) B12462659
theorem B3229469 : Blo 956588 3229469 := bstep (se 3 (by rfl) ⟨605525, by rfl⟩ : syracuseStep 3229469 = 1211051) B1211051
theorem B3884867 : Blo 956588 3884867 := bstep (se 1 (by rfl) ⟨2913650, by rfl⟩ : syracuseStep 3884867 = 5827301) B5827301
theorem B4605959 : Blo 956588 4605959 := bstep (se 1 (by rfl) ⟨3454469, by rfl⟩ : syracuseStep 4605959 = 6908939) B6908939
theorem B6899741 : Blo 956588 6899741 := bstep (se 3 (by rfl) ⟨1293701, by rfl⟩ : syracuseStep 6899741 = 2587403) B2587403
theorem B7784525 : Blo 956588 7784525 := bstep (se 3 (by rfl) ⟨1459598, by rfl⟩ : syracuseStep 7784525 = 2919197) B2919197
theorem B1821035 : Blo 956588 1821035 := bstep (se 1 (by rfl) ⟨1365776, by rfl⟩ : syracuseStep 1821035 = 2731553) B2731553
theorem B1296815 : Blo 956588 1296815 := bstep (se 1 (by rfl) ⟨972611, by rfl⟩ : syracuseStep 1296815 = 1945223) B1945223
theorem B1362359 : Blo 956588 1362359 := bstep (se 1 (by rfl) ⟨1021769, by rfl⟩ : syracuseStep 1362359 = 2043539) B2043539
theorem B3230171 : Blo 956588 3230171 := bstep (se 1 (by rfl) ⟨2422628, by rfl⟩ : syracuseStep 3230171 = 4845257) B4845257
theorem B50547401 : Blo 956588 50547401 := bstep (se 2 (by rfl) ⟨18955275, by rfl⟩ : syracuseStep 50547401 = 37910551) B37910551
theorem B9194269 : Blo 956588 9194269 := bstep (se 3 (by rfl) ⟨1723925, by rfl⟩ : syracuseStep 9194269 = 3447851) B3447851
theorem B3066653 : Blo 956588 3066653 := bstep (se 3 (by rfl) ⟨574997, by rfl⟩ : syracuseStep 3066653 = 1149995) B1149995
theorem B1821703 : Blo 956588 1821703 := bstep (se 1 (by rfl) ⟨1366277, by rfl⟩ : syracuseStep 1821703 = 2732555) B2732555
theorem B3230873 : Blo 956588 3230873 := bstep (se 2 (by rfl) ⟨1211577, by rfl⟩ : syracuseStep 3230873 = 2423155) B2423155
theorem B7294373 : Blo 956588 7294373 := bstep (se 4 (by rfl) ⟨683847, by rfl⟩ : syracuseStep 7294373 = 1367695) B1367695
theorem B14012027 : Blo 956588 14012027 := bstep (se 1 (by rfl) ⟨10509020, by rfl⟩ : syracuseStep 14012027 = 21018041) B21018041
theorem B1363817 : Blo 956588 1363817 := bstep (se 2 (by rfl) ⟨511431, by rfl⟩ : syracuseStep 1363817 = 1022863) B1022863
theorem B22106317 : Blo 956588 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B6148325 : Blo 956588 6148325 := bstep (se 4 (by rfl) ⟨576405, by rfl⟩ : syracuseStep 6148325 = 1152811) B1152811
theorem B3232061 : Blo 956588 3232061 := bstep (se 3 (by rfl) ⟨606011, by rfl⟩ : syracuseStep 3232061 = 1212023) B1212023
theorem B971615 : Blo 956588 971615 := bstep (se 1 (by rfl) ⟨728711, by rfl⟩ : syracuseStep 971615 = 1457423) B1457423
theorem B9819203 : Blo 956588 9819203 := bstep (se 1 (by rfl) ⟨7364402, by rfl⟩ : syracuseStep 9819203 = 14728805) B14728805
theorem B3232925 : Blo 956588 3232925 := bstep (se 3 (by rfl) ⟨606173, by rfl⟩ : syracuseStep 3232925 = 1212347) B1212347
theorem B1726031 : Blo 956588 1726031 := bstep (se 1 (by rfl) ⟨1294523, by rfl⟩ : syracuseStep 1726031 = 2589047) B2589047
theorem B3233465 : Blo 956588 3233465 := bstep (se 2 (by rfl) ⟨1212549, by rfl⟩ : syracuseStep 3233465 = 2425099) B2425099
theorem B2152367 : Blo 956588 2152367 := bstep (se 1 (by rfl) ⟨1614275, by rfl⟩ : syracuseStep 2152367 = 3228551) B3228551
theorem B1726543 : Blo 956588 1726543 := bstep (se 1 (by rfl) ⟨1294907, by rfl⟩ : syracuseStep 1726543 = 2589815) B2589815
theorem B2152619 : Blo 956588 2152619 := bstep (se 1 (by rfl) ⟨1614464, by rfl⟩ : syracuseStep 2152619 = 3228929) B3228929
theorem B3234059 : Blo 956588 3234059 := bstep (se 1 (by rfl) ⟨2425544, by rfl⟩ : syracuseStep 3234059 = 4851089) B4851089
theorem B2021897 : Blo 956588 2021897 := bstep (se 2 (by rfl) ⟨758211, by rfl⟩ : syracuseStep 2021897 = 1516423) B1516423
theorem B3234329 : Blo 956588 3234329 := bstep (se 2 (by rfl) ⟨1212873, by rfl⟩ : syracuseStep 3234329 = 2425747) B2425747
theorem B8182457 : Blo 956588 8182457 := bstep (se 2 (by rfl) ⟨3068421, by rfl⟩ : syracuseStep 8182457 = 6136843) B6136843
theorem B2153159 : Blo 956588 2153159 := bstep (se 1 (by rfl) ⟨1614869, by rfl⟩ : syracuseStep 2153159 = 3229739) B3229739
theorem B22109263 : Blo 956588 22109263 := bstep (se 1 (by rfl) ⟨16581947, by rfl⟩ : syracuseStep 22109263 = 33163895) B33163895
theorem B6151247 : Blo 956588 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B5463287 : Blo 956588 5463287 := bstep (se 1 (by rfl) ⟨4097465, by rfl⟩ : syracuseStep 5463287 = 8194931) B8194931
theorem B7265699 : Blo 956588 7265699 := bstep (se 1 (by rfl) ⟨5449274, by rfl⟩ : syracuseStep 7265699 = 10898549) B10898549
theorem B1367479 : Blo 956588 1367479 := bstep (se 1 (by rfl) ⟨1025609, by rfl⟩ : syracuseStep 1367479 = 2051219) B2051219
theorem B2154023 : Blo 956588 2154023 := bstep (se 1 (by rfl) ⟨1615517, by rfl⟩ : syracuseStep 2154023 = 3231035) B3231035
theorem B3235463 : Blo 956588 3235463 := bstep (se 1 (by rfl) ⟨2426597, by rfl⟩ : syracuseStep 3235463 = 4853195) B4853195
theorem B4087435 : Blo 956588 4087435 := bstep (se 1 (by rfl) ⟨3065576, by rfl⟩ : syracuseStep 4087435 = 6131153) B6131153
theorem B4152971 : Blo 956588 4152971 := bstep (se 1 (by rfl) ⟨3114728, by rfl⟩ : syracuseStep 4152971 = 6229457) B6229457
theorem B3235517 : Blo 956588 3235517 := bstep (se 3 (by rfl) ⟨606659, by rfl⟩ : syracuseStep 3235517 = 1213319) B1213319
theorem B3235679 : Blo 956588 3235679 := bstep (se 1 (by rfl) ⟨2426759, by rfl⟩ : syracuseStep 3235679 = 4853519) B4853519
theorem B2154347 : Blo 956588 2154347 := bstep (se 1 (by rfl) ⟨1615760, by rfl⟩ : syracuseStep 2154347 = 3231521) B3231521
theorem B2154401 : Blo 956588 2154401 := bstep (se 2 (by rfl) ⟨807900, by rfl⟩ : syracuseStep 2154401 = 1615801) B1615801
theorem B3235841 : Blo 956588 3235841 := bstep (se 2 (by rfl) ⟨1213440, by rfl⟩ : syracuseStep 3235841 = 2426881) B2426881
theorem B6152273 : Blo 956588 6152273 := bstep (se 2 (by rfl) ⟨2307102, by rfl⟩ : syracuseStep 6152273 = 4614205) B4614205
theorem B2154743 : Blo 956588 2154743 := bstep (se 1 (by rfl) ⟨1616057, by rfl⟩ : syracuseStep 2154743 = 3232115) B3232115
theorem B3072343 : Blo 956588 3072343 := bstep (se 1 (by rfl) ⟨2304257, by rfl⟩ : syracuseStep 3072343 = 4608515) B4608515
theorem B4612589 : Blo 956588 4612589 := bstep (se 3 (by rfl) ⟨864860, by rfl⟩ : syracuseStep 4612589 = 1729721) B1729721
theorem B3072701 : Blo 956588 3072701 := bstep (se 3 (by rfl) ⟨576131, by rfl⟩ : syracuseStep 3072701 = 1152263) B1152263
theorem B3236651 : Blo 956588 3236651 := bstep (se 1 (by rfl) ⟨2427488, by rfl⟩ : syracuseStep 3236651 = 4854977) B4854977
theorem B2155337 : Blo 956588 2155337 := bstep (se 2 (by rfl) ⟨808251, by rfl⟩ : syracuseStep 2155337 = 1616503) B1616503
theorem B1532891 : Blo 956588 1532891 := bstep (se 1 (by rfl) ⟨1149668, by rfl⟩ : syracuseStep 1532891 = 2299337) B2299337
theorem B3236921 : Blo 956588 3236921 := bstep (se 2 (by rfl) ⟨1213845, by rfl⟩ : syracuseStep 3236921 = 2427691) B2427691
theorem B3237245 : Blo 956588 3237245 := bstep (se 3 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 3237245 = 1213967) B1213967
theorem B1435055 : Blo 956588 1435055 := bstep (se 1 (by rfl) ⟨1076291, by rfl⟩ : syracuseStep 1435055 = 2152583) B2152583
theorem B1435145 : Blo 956588 1435145 := bstep (se 2 (by rfl) ⟨538179, by rfl⟩ : syracuseStep 1435145 = 1076359) B1076359
theorem B3892769 : Blo 956588 3892769 := bstep (se 2 (by rfl) ⟨1459788, by rfl⟩ : syracuseStep 3892769 = 2919577) B2919577
theorem B1435175 : Blo 956588 1435175 := bstep (se 1 (by rfl) ⟨1076381, by rfl⟩ : syracuseStep 1435175 = 2152763) B2152763
theorem B2156129 : Blo 956588 2156129 := bstep (se 2 (by rfl) ⟨808548, by rfl⟩ : syracuseStep 2156129 = 1617097) B1617097
theorem B1435259 : Blo 956588 1435259 := bstep (se 1 (by rfl) ⟨1076444, by rfl⟩ : syracuseStep 1435259 = 2152889) B2152889
theorem B3237515 : Blo 956588 3237515 := bstep (se 1 (by rfl) ⟨2428136, by rfl⟩ : syracuseStep 3237515 = 4856273) B4856273
theorem B1435385 : Blo 956588 1435385 := bstep (se 2 (by rfl) ⟨538269, by rfl⟩ : syracuseStep 1435385 = 1076539) B1076539
theorem B7268129 : Blo 956588 7268129 := bstep (se 2 (by rfl) ⟨2725548, by rfl⟩ : syracuseStep 7268129 = 5451097) B5451097
theorem B1435487 : Blo 956588 1435487 := bstep (se 1 (by rfl) ⟨1076615, by rfl⟩ : syracuseStep 1435487 = 2153231) B2153231
theorem B5465951 : Blo 956588 5465951 := bstep (se 1 (by rfl) ⟨4099463, by rfl⟩ : syracuseStep 5465951 = 8198927) B8198927
theorem B1435499 : Blo 956588 1435499 := bstep (se 1 (by rfl) ⟨1076624, by rfl⟩ : syracuseStep 1435499 = 2153249) B2153249
theorem B2156471 : Blo 956588 2156471 := bstep (se 1 (by rfl) ⟨1617353, by rfl⟩ : syracuseStep 2156471 = 3234707) B3234707
theorem B1435727 : Blo 956588 1435727 := bstep (se 1 (by rfl) ⟨1076795, by rfl⟩ : syracuseStep 1435727 = 2153591) B2153591
theorem B1435847 : Blo 956588 1435847 := bstep (se 1 (by rfl) ⟨1076885, by rfl⟩ : syracuseStep 1435847 = 2153771) B2153771
theorem B1436009 : Blo 956588 1436009 := bstep (se 2 (by rfl) ⟨538503, by rfl⟩ : syracuseStep 1436009 = 1077007) B1077007
theorem B1436087 : Blo 956588 1436087 := bstep (se 1 (by rfl) ⟨1077065, by rfl⟩ : syracuseStep 1436087 = 2154131) B2154131
theorem B1436123 : Blo 956588 1436123 := bstep (se 1 (by rfl) ⟨1077092, by rfl⟩ : syracuseStep 1436123 = 2154185) B2154185
theorem B2157065 : Blo 956588 2157065 := bstep (se 2 (by rfl) ⟨808899, by rfl⟩ : syracuseStep 2157065 = 1617799) B1617799
theorem B3238433 : Blo 956588 3238433 := bstep (se 2 (by rfl) ⟨1214412, by rfl⟩ : syracuseStep 3238433 = 2428825) B2428825
theorem B3238649 : Blo 956588 3238649 := bstep (se 2 (by rfl) ⟨1214493, by rfl⟩ : syracuseStep 3238649 = 2428987) B2428987
theorem B2911049 : Blo 956588 2911049 := bstep (se 2 (by rfl) ⟨1091643, by rfl⟩ : syracuseStep 2911049 = 2183287) B2183287
theorem B5466953 : Blo 956588 5466953 := bstep (se 2 (by rfl) ⟨2050107, by rfl⟩ : syracuseStep 5466953 = 4100215) B4100215
theorem B2157407 : Blo 956588 2157407 := bstep (se 1 (by rfl) ⟨1618055, by rfl⟩ : syracuseStep 2157407 = 3236111) B3236111
theorem B1436591 : Blo 956588 1436591 := bstep (se 1 (by rfl) ⟨1077443, by rfl⟩ : syracuseStep 1436591 = 2154887) B2154887
theorem B3238919 : Blo 956588 3238919 := bstep (se 1 (by rfl) ⟨2429189, by rfl⟩ : syracuseStep 3238919 = 4858379) B4858379
theorem B1436681 : Blo 956588 1436681 := bstep (se 2 (by rfl) ⟨538755, by rfl⟩ : syracuseStep 1436681 = 1077511) B1077511
theorem B2157587 : Blo 956588 2157587 := bstep (se 1 (by rfl) ⟨1618190, by rfl⟩ : syracuseStep 2157587 = 3236381) B3236381
theorem B1436711 : Blo 956588 1436711 := bstep (se 1 (by rfl) ⟨1077533, by rfl⟩ : syracuseStep 1436711 = 2155067) B2155067
theorem B3239027 : Blo 956588 3239027 := bstep (se 1 (by rfl) ⟨2429270, by rfl⟩ : syracuseStep 3239027 = 4858541) B4858541
theorem B1436795 : Blo 956588 1436795 := bstep (se 1 (by rfl) ⟨1077596, by rfl⟩ : syracuseStep 1436795 = 2155193) B2155193
theorem B1436921 : Blo 956588 1436921 := bstep (se 2 (by rfl) ⟨538845, by rfl⟩ : syracuseStep 1436921 = 1077691) B1077691
theorem B3632471 : Blo 956588 3632471 := bstep (se 1 (by rfl) ⟨2724353, by rfl⟩ : syracuseStep 3632471 = 5448707) B5448707
theorem B9203033 : Blo 956588 9203033 := bstep (se 2 (by rfl) ⟨3451137, by rfl⟩ : syracuseStep 9203033 = 6902275) B6902275
theorem B1076575 : Blo 956588 1076575 := bstep (se 1 (by rfl) ⟨807431, by rfl⟩ : syracuseStep 1076575 = 1614863) B1614863
theorem B1437023 : Blo 956588 1437023 := bstep (se 1 (by rfl) ⟨1077767, by rfl⟩ : syracuseStep 1437023 = 2155535) B2155535
theorem B2157929 : Blo 956588 2157929 := bstep (se 2 (by rfl) ⟨809223, by rfl⟩ : syracuseStep 2157929 = 1618447) B1618447
theorem B1437035 : Blo 956588 1437035 := bstep (se 1 (by rfl) ⟨1077776, by rfl⟩ : syracuseStep 1437035 = 2155553) B2155553
theorem B3239297 : Blo 956588 3239297 := bstep (se 2 (by rfl) ⟨1214736, by rfl⟩ : syracuseStep 3239297 = 2429473) B2429473
theorem B4845095 : Blo 956588 4845095 := bstep (se 1 (by rfl) ⟨3633821, by rfl⟩ : syracuseStep 4845095 = 7267643) B7267643
theorem B1437263 : Blo 956588 1437263 := bstep (se 1 (by rfl) ⟨1077947, by rfl⟩ : syracuseStep 1437263 = 2155895) B2155895
theorem B8187581 : Blo 956588 8187581 := bstep (se 3 (by rfl) ⟨1535171, by rfl⟩ : syracuseStep 8187581 = 3070343) B3070343
theorem B1076935 : Blo 956588 1076935 := bstep (se 1 (by rfl) ⟨807701, by rfl⟩ : syracuseStep 1076935 = 1615403) B1615403
theorem B1437383 : Blo 956588 1437383 := bstep (se 1 (by rfl) ⟨1078037, by rfl⟩ : syracuseStep 1437383 = 2156075) B2156075
theorem B1437545 : Blo 956588 1437545 := bstep (se 2 (by rfl) ⟨539079, by rfl⟩ : syracuseStep 1437545 = 1078159) B1078159
theorem B1535851 : Blo 956588 1535851 := bstep (se 1 (by rfl) ⟨1151888, by rfl⟩ : syracuseStep 1535851 = 2303777) B2303777
theorem B4091809 : Blo 956588 4091809 := bstep (se 2 (by rfl) ⟨1534428, by rfl⟩ : syracuseStep 4091809 = 3068857) B3068857
theorem B1437623 : Blo 956588 1437623 := bstep (se 1 (by rfl) ⟨1078217, by rfl⟩ : syracuseStep 1437623 = 2156435) B2156435
theorem B2158523 : Blo 956588 2158523 := bstep (se 1 (by rfl) ⟨1618892, by rfl⟩ : syracuseStep 2158523 = 3237785) B3237785
theorem B1437659 : Blo 956588 1437659 := bstep (se 1 (by rfl) ⟨1078244, by rfl⟩ : syracuseStep 1437659 = 2156489) B2156489
theorem B3502081 : Blo 956588 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B2158649 : Blo 956588 2158649 := bstep (se 2 (by rfl) ⟨809493, by rfl⟩ : syracuseStep 2158649 = 1618987) B1618987
theorem B3240107 : Blo 956588 3240107 := bstep (se 1 (by rfl) ⟨2430080, by rfl⟩ : syracuseStep 3240107 = 4860161) B4860161
theorem B2158991 : Blo 956588 2158991 := bstep (se 1 (by rfl) ⟨1619243, by rfl⟩ : syracuseStep 2158991 = 3238487) B3238487
theorem B1438127 : Blo 956588 1438127 := bstep (se 1 (by rfl) ⟨1078595, by rfl⟩ : syracuseStep 1438127 = 2157191) B2157191
theorem B1438217 : Blo 956588 1438217 := bstep (se 2 (by rfl) ⟨539331, by rfl⟩ : syracuseStep 1438217 = 1078663) B1078663
theorem B1077799 : Blo 956588 1077799 := bstep (se 1 (by rfl) ⟨808349, by rfl⟩ : syracuseStep 1077799 = 1616699) B1616699
theorem B1438247 : Blo 956588 1438247 := bstep (se 1 (by rfl) ⟨1078685, by rfl⟩ : syracuseStep 1438247 = 2157371) B2157371
theorem B3633761 : Blo 956588 3633761 := bstep (se 2 (by rfl) ⟨1362660, by rfl⟩ : syracuseStep 3633761 = 2725321) B2725321
theorem B1438331 : Blo 956588 1438331 := bstep (se 1 (by rfl) ⟨1078748, by rfl⟩ : syracuseStep 1438331 = 2157497) B2157497
theorem B3240647 : Blo 956588 3240647 := bstep (se 1 (by rfl) ⟨2430485, by rfl⟩ : syracuseStep 3240647 = 4860971) B4860971
theorem B2159315 : Blo 956588 2159315 := bstep (se 1 (by rfl) ⟨1619486, by rfl⟩ : syracuseStep 2159315 = 3238973) B3238973
theorem B1438457 : Blo 956588 1438457 := bstep (se 2 (by rfl) ⟨539421, by rfl⟩ : syracuseStep 1438457 = 1078843) B1078843
theorem B1536761 : Blo 956588 1536761 := bstep (se 2 (by rfl) ⟨576285, by rfl⟩ : syracuseStep 1536761 = 1152571) B1152571
theorem B1438559 : Blo 956588 1438559 := bstep (se 1 (by rfl) ⟨1078919, by rfl⟩ : syracuseStep 1438559 = 2157839) B2157839
theorem B1438571 : Blo 956588 1438571 := bstep (se 1 (by rfl) ⟨1078928, by rfl⟩ : syracuseStep 1438571 = 2157857) B2157857
theorem B1537031 : Blo 956588 1537031 := bstep (se 1 (by rfl) ⟨1152773, by rfl⟩ : syracuseStep 1537031 = 2305547) B2305547
theorem B2421839 : Blo 956588 2421839 := bstep (se 1 (by rfl) ⟨1816379, by rfl⟩ : syracuseStep 2421839 = 3632759) B3632759
theorem B1438799 : Blo 956588 1438799 := bstep (se 1 (by rfl) ⟨1079099, by rfl⟩ : syracuseStep 1438799 = 2158199) B2158199
theorem B1438919 : Blo 956588 1438919 := bstep (se 1 (by rfl) ⟨1079189, by rfl⟩ : syracuseStep 1438919 = 2158379) B2158379
theorem B1439081 : Blo 956588 1439081 := bstep (se 2 (by rfl) ⟨539655, by rfl⟩ : syracuseStep 1439081 = 1079311) B1079311
theorem B1439159 : Blo 956588 1439159 := bstep (se 1 (by rfl) ⟨1079369, by rfl⟩ : syracuseStep 1439159 = 2158739) B2158739
theorem B1439195 : Blo 956588 1439195 := bstep (se 1 (by rfl) ⟨1079396, by rfl⟩ : syracuseStep 1439195 = 2158793) B2158793
theorem B3274273 : Blo 956588 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B3241511 : Blo 956588 3241511 := bstep (se 1 (by rfl) ⟨2431133, by rfl⟩ : syracuseStep 3241511 = 4862267) B4862267
theorem B4847201 : Blo 956588 4847201 := bstep (se 2 (by rfl) ⟨1817700, by rfl⟩ : syracuseStep 4847201 = 3635401) B3635401
theorem B2160251 : Blo 956588 2160251 := bstep (se 1 (by rfl) ⟨1620188, by rfl⟩ : syracuseStep 2160251 = 3240377) B3240377
theorem B3241619 : Blo 956588 3241619 := bstep (se 1 (by rfl) ⟨2431214, by rfl⟩ : syracuseStep 3241619 = 4862429) B4862429
theorem B2422487 : Blo 956588 2422487 := bstep (se 1 (by rfl) ⟨1816865, by rfl⟩ : syracuseStep 2422487 = 3633731) B3633731
theorem B2160377 : Blo 956588 2160377 := bstep (se 2 (by rfl) ⟨810141, by rfl⟩ : syracuseStep 2160377 = 1620283) B1620283
theorem B3241835 : Blo 956588 3241835 := bstep (se 1 (by rfl) ⟨2431376, by rfl⟩ : syracuseStep 3241835 = 4862753) B4862753
theorem B3241889 : Blo 956588 3241889 := bstep (se 2 (by rfl) ⟨1215708, by rfl⟩ : syracuseStep 3241889 = 2431417) B2431417
theorem B1439663 : Blo 956588 1439663 := bstep (se 1 (by rfl) ⟨1079747, by rfl⟩ : syracuseStep 1439663 = 2159495) B2159495
theorem B2160647 : Blo 956588 2160647 := bstep (se 1 (by rfl) ⟨1620485, by rfl⟩ : syracuseStep 2160647 = 3240971) B3240971
theorem B1439753 : Blo 956588 1439753 := bstep (se 2 (by rfl) ⟨539907, by rfl⟩ : syracuseStep 1439753 = 1079815) B1079815
theorem B3635219 : Blo 956588 3635219 := bstep (se 1 (by rfl) ⟨2726414, by rfl⟩ : syracuseStep 3635219 = 5452829) B5452829
theorem B1439783 : Blo 956588 1439783 := bstep (se 1 (by rfl) ⟨1079837, by rfl⟩ : syracuseStep 1439783 = 2159675) B2159675
theorem B2160719 : Blo 956588 2160719 := bstep (se 1 (by rfl) ⟨1620539, by rfl⟩ : syracuseStep 2160719 = 3241079) B3241079
theorem B1079419 : Blo 956588 1079419 := bstep (se 1 (by rfl) ⟨809564, by rfl⟩ : syracuseStep 1079419 = 1619129) B1619129
theorem B1439867 : Blo 956588 1439867 := bstep (se 1 (by rfl) ⟨1079900, by rfl⟩ : syracuseStep 1439867 = 2159801) B2159801
theorem B1439993 : Blo 956588 1439993 := bstep (se 2 (by rfl) ⟨539997, by rfl⟩ : syracuseStep 1439993 = 1079995) B1079995
theorem B1440095 : Blo 956588 1440095 := bstep (se 1 (by rfl) ⟨1080071, by rfl⟩ : syracuseStep 1440095 = 2160143) B2160143
theorem B1440107 : Blo 956588 1440107 := bstep (se 1 (by rfl) ⟨1080080, by rfl⟩ : syracuseStep 1440107 = 2160161) B2160161
theorem B3635675 : Blo 956588 3635675 := bstep (se 1 (by rfl) ⟨2726756, by rfl⟩ : syracuseStep 3635675 = 5453513) B5453513
theorem B2161115 : Blo 956588 2161115 := bstep (se 1 (by rfl) ⟨1620836, by rfl⟩ : syracuseStep 2161115 = 3241673) B3241673
theorem B1079887 : Blo 956588 1079887 := bstep (se 1 (by rfl) ⟨809915, by rfl⟩ : syracuseStep 1079887 = 1619831) B1619831
theorem B1440335 : Blo 956588 1440335 := bstep (se 1 (by rfl) ⟨1080251, by rfl⟩ : syracuseStep 1440335 = 2160503) B2160503
theorem B1440455 : Blo 956588 1440455 := bstep (se 1 (by rfl) ⟨1080341, by rfl⟩ : syracuseStep 1440455 = 2160683) B2160683
theorem B1440617 : Blo 956588 1440617 := bstep (se 2 (by rfl) ⟨540231, by rfl⟩ : syracuseStep 1440617 = 1080463) B1080463
theorem B1440695 : Blo 956588 1440695 := bstep (se 1 (by rfl) ⟨1080521, by rfl⟩ : syracuseStep 1440695 = 2161043) B2161043
theorem B2456507 : Blo 956588 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B1080283 : Blo 956588 1080283 := bstep (se 1 (by rfl) ⟨810212, by rfl⟩ : syracuseStep 1080283 = 1620425) B1620425
theorem B1440731 : Blo 956588 1440731 := bstep (se 1 (by rfl) ⟨1080548, by rfl⟩ : syracuseStep 1440731 = 2161097) B2161097
theorem B4848659 : Blo 956588 4848659 := bstep (se 1 (by rfl) ⟨3636494, by rfl⟩ : syracuseStep 4848659 = 7272989) B7272989
theorem B1211431 : Blo 956588 1211431 := bstep (se 1 (by rfl) ⟨908573, by rfl⟩ : syracuseStep 1211431 = 1817147) B1817147
theorem B1211755 : Blo 956588 1211755 := bstep (se 1 (by rfl) ⟨908816, by rfl⟩ : syracuseStep 1211755 = 1817633) B1817633
theorem B3636859 : Blo 956588 3636859 := bstep (se 1 (by rfl) ⟨2727644, by rfl⟩ : syracuseStep 3636859 = 5455289) B5455289
theorem B7765969 : Blo 956588 7765969 := bstep (se 2 (by rfl) ⟨2912238, by rfl⟩ : syracuseStep 7765969 = 5824477) B5824477
theorem B18677765 : Blo 956588 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B6914099 : Blo 956588 6914099 := bstep (se 1 (by rfl) ⟨5185574, by rfl⟩ : syracuseStep 6914099 = 10371149) B10371149
theorem B2588777 : Blo 956588 2588777 := bstep (se 2 (by rfl) ⟨970791, by rfl⟩ : syracuseStep 2588777 = 1941583) B1941583
theorem B2424937 : Blo 956588 2424937 := bstep (se 2 (by rfl) ⟨909351, by rfl⟩ : syracuseStep 2424937 = 1818703) B1818703
theorem B20709593 : Blo 956588 20709593 := bstep (se 2 (by rfl) ⟨7766097, by rfl⟩ : syracuseStep 20709593 = 15532195) B15532195
theorem B4096457 : Blo 956588 4096457 := bstep (se 2 (by rfl) ⟨1536171, by rfl⟩ : syracuseStep 4096457 = 3072343) B3072343
theorem B3637831 : Blo 956588 3637831 := bstep (se 1 (by rfl) ⟨2728373, by rfl⟩ : syracuseStep 3637831 = 5456747) B5456747
theorem B2425423 : Blo 956588 2425423 := bstep (se 1 (by rfl) ⟨1819067, by rfl⟩ : syracuseStep 2425423 = 3638135) B3638135
theorem B5538959 : Blo 956588 5538959 := bstep (se 1 (by rfl) ⟨4154219, by rfl⟩ : syracuseStep 5538959 = 8308439) B8308439
theorem B2589911 : Blo 956588 2589911 := bstep (se 1 (by rfl) ⟨1942433, by rfl⟩ : syracuseStep 2589911 = 3884867) B3884867
theorem B2426071 : Blo 956588 2426071 := bstep (se 1 (by rfl) ⟨1819553, by rfl⟩ : syracuseStep 2426071 = 3639107) B3639107
theorem B2426375 : Blo 956588 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B5178937 : Blo 956588 5178937 := bstep (se 2 (by rfl) ⟨1942101, by rfl⟩ : syracuseStep 5178937 = 3884203) B3884203
theorem B1214023 : Blo 956588 1214023 := bstep (se 1 (by rfl) ⟨910517, by rfl⟩ : syracuseStep 1214023 = 1821035) B1821035
theorem B2459297 : Blo 956588 2459297 := bstep (se 2 (by rfl) ⟨922236, by rfl⟩ : syracuseStep 2459297 = 1844473) B1844473
theorem B8193869 : Blo 956588 8193869 := bstep (se 3 (by rfl) ⟨1536350, by rfl⟩ : syracuseStep 8193869 = 3072701) B3072701
theorem B2426831 : Blo 956588 2426831 := bstep (se 1 (by rfl) ⟨1820123, by rfl⟩ : syracuseStep 2426831 = 3640247) B3640247
theorem B2590973 : Blo 956588 2590973 := bstep (se 3 (by rfl) ⟨485807, by rfl⟩ : syracuseStep 2590973 = 971615) B971615
theorem B4917647 : Blo 956588 4917647 := bstep (se 1 (by rfl) ⟨3688235, by rfl⟩ : syracuseStep 4917647 = 7376471) B7376471
theorem B9341351 : Blo 956588 9341351 := bstep (se 1 (by rfl) ⟨7006013, by rfl⟩ : syracuseStep 9341351 = 14012027) B14012027
theorem B2427347 : Blo 956588 2427347 := bstep (se 1 (by rfl) ⟨1820510, by rfl⟩ : syracuseStep 2427347 = 3641021) B3641021
theorem B4852547 : Blo 956588 4852547 := bstep (se 1 (by rfl) ⟨3639410, by rfl⟩ : syracuseStep 4852547 = 7278821) B7278821
theorem B4098883 : Blo 956588 4098883 := bstep (se 1 (by rfl) ⟨3074162, by rfl⟩ : syracuseStep 4098883 = 6148325) B6148325
theorem B26184541 : Blo 956588 26184541 := bstep (se 3 (by rfl) ⟨4909601, by rfl⟩ : syracuseStep 26184541 = 9819203) B9819203
theorem B2427803 : Blo 956588 2427803 := bstep (se 1 (by rfl) ⟨1820852, by rfl⟩ : syracuseStep 2427803 = 3641705) B3641705
theorem B6556787 : Blo 956588 6556787 := bstep (se 1 (by rfl) ⟨4917590, by rfl⟩ : syracuseStep 6556787 = 9835181) B9835181
theorem B13831307 : Blo 956588 13831307 := bstep (se 1 (by rfl) ⟨10373480, by rfl⟩ : syracuseStep 13831307 = 20746961) B20746961
theorem B4853357 : Blo 956588 4853357 := bstep (se 3 (by rfl) ⟨910004, by rfl⟩ : syracuseStep 4853357 = 1820009) B1820009
theorem B12259025 : Blo 956588 12259025 := bstep (se 2 (by rfl) ⟨4597134, by rfl⟩ : syracuseStep 12259025 = 9194269) B9194269
theorem B1150687 : Blo 956588 1150687 := bstep (se 1 (by rfl) ⟨863015, by rfl⟩ : syracuseStep 1150687 = 1726031) B1726031
theorem B2428937 : Blo 956588 2428937 := bstep (se 2 (by rfl) ⟨910851, by rfl⟩ : syracuseStep 2428937 = 1821703) B1821703
theorem B1347931 : Blo 956588 1347931 := bstep (se 1 (by rfl) ⟨1010948, by rfl⟩ : syracuseStep 1347931 = 2021897) B2021897
theorem B2429291 : Blo 956588 2429291 := bstep (se 1 (by rfl) ⟨1821968, by rfl⟩ : syracuseStep 2429291 = 3643937) B3643937
theorem B13832693 : Blo 956588 13832693 := bstep (se 5 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 13832693 = 1296815) B1296815
theorem B3281579 : Blo 956588 3281579 := bstep (se 1 (by rfl) ⟨2461184, by rfl⟩ : syracuseStep 3281579 = 4922369) B4922369
theorem B2429615 : Blo 956588 2429615 := bstep (se 1 (by rfl) ⟨1822211, by rfl⟩ : syracuseStep 2429615 = 3644423) B3644423
theorem B4100831 : Blo 956588 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B3642191 : Blo 956588 3642191 := bstep (se 1 (by rfl) ⟨2731643, by rfl⟩ : syracuseStep 3642191 = 5463287) B5463287
theorem B2429939 : Blo 956588 2429939 := bstep (se 1 (by rfl) ⟨1822454, by rfl⟩ : syracuseStep 2429939 = 3644909) B3644909
theorem B6132793 : Blo 956588 6132793 := bstep (se 2 (by rfl) ⟨2299797, by rfl⟩ : syracuseStep 6132793 = 4599595) B4599595
theorem B4920563 : Blo 956588 4920563 := bstep (se 1 (by rfl) ⟨3690422, by rfl⟩ : syracuseStep 4920563 = 7380845) B7380845
theorem B12293369 : Blo 956588 12293369 := bstep (se 2 (by rfl) ⟨4610013, by rfl⟩ : syracuseStep 12293369 = 9220027) B9220027
theorem B4101515 : Blo 956588 4101515 := bstep (se 1 (by rfl) ⟨3076136, by rfl⟩ : syracuseStep 4101515 = 6152273) B6152273
theorem B2430395 : Blo 956588 2430395 := bstep (se 1 (by rfl) ⟨1822796, by rfl⟩ : syracuseStep 2430395 = 3645593) B3645593
theorem B3544633 : Blo 956588 3544633 := bstep (se 2 (by rfl) ⟨1329237, by rfl⟩ : syracuseStep 3544633 = 2658475) B2658475
theorem B956703 : Blo 956588 956703 := bstep (se 1 (by rfl) ⟨717527, by rfl⟩ : syracuseStep 956703 = 1435055) B1435055
theorem B956763 : Blo 956588 956763 := bstep (se 1 (by rfl) ⟨717572, by rfl⟩ : syracuseStep 956763 = 1435145) B1435145
theorem B2595179 : Blo 956588 2595179 := bstep (se 1 (by rfl) ⟨1946384, by rfl⟩ : syracuseStep 2595179 = 3892769) B3892769
theorem B956783 : Blo 956588 956783 := bstep (se 1 (by rfl) ⟨717587, by rfl⟩ : syracuseStep 956783 = 1435175) B1435175
theorem B956839 : Blo 956588 956839 := bstep (se 1 (by rfl) ⟨717629, by rfl⟩ : syracuseStep 956839 = 1435259) B1435259
theorem B956923 : Blo 956588 956923 := bstep (se 1 (by rfl) ⟨717692, by rfl⟩ : syracuseStep 956923 = 1435385) B1435385
theorem B956991 : Blo 956588 956991 := bstep (se 1 (by rfl) ⟨717743, by rfl⟩ : syracuseStep 956991 = 1435487) B1435487
theorem B3643967 : Blo 956588 3643967 := bstep (se 1 (by rfl) ⟨2732975, by rfl⟩ : syracuseStep 3643967 = 5465951) B5465951
theorem B956999 : Blo 956588 956999 := bstep (se 1 (by rfl) ⟨717749, by rfl⟩ : syracuseStep 956999 = 1435499) B1435499
theorem B957151 : Blo 956588 957151 := bstep (se 1 (by rfl) ⟨717863, by rfl⟩ : syracuseStep 957151 = 1435727) B1435727
theorem B957231 : Blo 956588 957231 := bstep (se 1 (by rfl) ⟨717923, by rfl⟩ : syracuseStep 957231 = 1435847) B1435847
theorem B957339 : Blo 956588 957339 := bstep (se 1 (by rfl) ⟨718004, by rfl⟩ : syracuseStep 957339 = 1436009) B1436009
theorem B2300827 : Blo 956588 2300827 := bstep (se 1 (by rfl) ⟨1725620, by rfl⟩ : syracuseStep 2300827 = 3451241) B3451241
theorem B957391 : Blo 956588 957391 := bstep (se 1 (by rfl) ⟨718043, by rfl⟩ : syracuseStep 957391 = 1436087) B1436087
theorem B957415 : Blo 956588 957415 := bstep (se 1 (by rfl) ⟨718061, by rfl⟩ : syracuseStep 957415 = 1436123) B1436123
theorem B1940699 : Blo 956588 1940699 := bstep (se 1 (by rfl) ⟨1455524, by rfl⟩ : syracuseStep 1940699 = 2911049) B2911049
theorem B3644635 : Blo 956588 3644635 := bstep (se 1 (by rfl) ⟨2733476, by rfl⟩ : syracuseStep 3644635 = 5466953) B5466953
theorem B957727 : Blo 956588 957727 := bstep (se 1 (by rfl) ⟨718295, by rfl⟩ : syracuseStep 957727 = 1436591) B1436591
theorem B957787 : Blo 956588 957787 := bstep (se 1 (by rfl) ⟨718340, by rfl⟩ : syracuseStep 957787 = 1436681) B1436681
theorem B957807 : Blo 956588 957807 := bstep (se 1 (by rfl) ⟨718355, by rfl⟩ : syracuseStep 957807 = 1436711) B1436711
theorem B4365697 : Blo 956588 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B957863 : Blo 956588 957863 := bstep (se 1 (by rfl) ⟨718397, by rfl⟩ : syracuseStep 957863 = 1436795) B1436795
theorem B957947 : Blo 956588 957947 := bstep (se 1 (by rfl) ⟨718460, by rfl⟩ : syracuseStep 957947 = 1436921) B1436921
theorem B6135355 : Blo 956588 6135355 := bstep (se 1 (by rfl) ⟨4601516, by rfl⟩ : syracuseStep 6135355 = 9203033) B9203033
theorem B958015 : Blo 956588 958015 := bstep (se 1 (by rfl) ⟨718511, by rfl⟩ : syracuseStep 958015 = 1437023) B1437023
theorem B958023 : Blo 956588 958023 := bstep (se 1 (by rfl) ⟨718517, by rfl⟩ : syracuseStep 958023 = 1437035) B1437035
theorem B3284563 : Blo 956588 3284563 := bstep (se 1 (by rfl) ⟨2463422, by rfl⟩ : syracuseStep 3284563 = 4926845) B4926845
theorem B958175 : Blo 956588 958175 := bstep (se 1 (by rfl) ⟨718631, by rfl⟩ : syracuseStep 958175 = 1437263) B1437263
theorem B958255 : Blo 956588 958255 := bstep (se 1 (by rfl) ⟨718691, by rfl⟩ : syracuseStep 958255 = 1437383) B1437383
theorem B958363 : Blo 956588 958363 := bstep (se 1 (by rfl) ⟨718772, by rfl⟩ : syracuseStep 958363 = 1437545) B1437545
theorem B958415 : Blo 956588 958415 := bstep (se 1 (by rfl) ⟨718811, by rfl⟩ : syracuseStep 958415 = 1437623) B1437623
theorem B958439 : Blo 956588 958439 := bstep (se 1 (by rfl) ⟨718829, by rfl⟩ : syracuseStep 958439 = 1437659) B1437659
theorem B2302057 : Blo 956588 2302057 := bstep (se 2 (by rfl) ⟨863271, by rfl⟩ : syracuseStep 2302057 = 1726543) B1726543
theorem B4726993 : Blo 956588 4726993 := bstep (se 2 (by rfl) ⟨1772622, by rfl⟩ : syracuseStep 4726993 = 3545245) B3545245
theorem B958751 : Blo 956588 958751 := bstep (se 1 (by rfl) ⟨719063, by rfl⟩ : syracuseStep 958751 = 1438127) B1438127
theorem B958811 : Blo 956588 958811 := bstep (se 1 (by rfl) ⟨719108, by rfl⟩ : syracuseStep 958811 = 1438217) B1438217
theorem B958831 : Blo 956588 958831 := bstep (se 1 (by rfl) ⟨719123, by rfl⟩ : syracuseStep 958831 = 1438247) B1438247
theorem B958887 : Blo 956588 958887 := bstep (se 1 (by rfl) ⟨719165, by rfl⟩ : syracuseStep 958887 = 1438331) B1438331
theorem B958971 : Blo 956588 958971 := bstep (se 1 (by rfl) ⟨719228, by rfl⟩ : syracuseStep 958971 = 1438457) B1438457
theorem B1024507 : Blo 956588 1024507 := bstep (se 1 (by rfl) ⟨768380, by rfl⟩ : syracuseStep 1024507 = 1536761) B1536761
theorem B959039 : Blo 956588 959039 := bstep (se 1 (by rfl) ⟨719279, by rfl⟩ : syracuseStep 959039 = 1438559) B1438559
theorem B959047 : Blo 956588 959047 := bstep (se 1 (by rfl) ⟨719285, by rfl⟩ : syracuseStep 959047 = 1438571) B1438571
theorem B2073161 : Blo 956588 2073161 := bstep (se 2 (by rfl) ⟨777435, by rfl⟩ : syracuseStep 2073161 = 1554871) B1554871
theorem B1024687 : Blo 956588 1024687 := bstep (se 1 (by rfl) ⟨768515, by rfl⟩ : syracuseStep 1024687 = 1537031) B1537031
theorem B1614559 : Blo 956588 1614559 := bstep (se 1 (by rfl) ⟨1210919, by rfl⟩ : syracuseStep 1614559 = 2421839) B2421839
theorem B959199 : Blo 956588 959199 := bstep (se 1 (by rfl) ⟨719399, by rfl⟩ : syracuseStep 959199 = 1438799) B1438799
theorem B959279 : Blo 956588 959279 := bstep (se 1 (by rfl) ⟨719459, by rfl⟩ : syracuseStep 959279 = 1438919) B1438919
theorem B4858703 : Blo 956588 4858703 := bstep (se 1 (by rfl) ⟨3644027, by rfl⟩ : syracuseStep 4858703 = 7288055) B7288055
theorem B959387 : Blo 956588 959387 := bstep (se 1 (by rfl) ⟨719540, by rfl⟩ : syracuseStep 959387 = 1439081) B1439081
theorem B8856515 : Blo 956588 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B959439 : Blo 956588 959439 := bstep (se 1 (by rfl) ⟨719579, by rfl⟩ : syracuseStep 959439 = 1439159) B1439159
theorem B959463 : Blo 956588 959463 := bstep (se 1 (by rfl) ⟨719597, by rfl⟩ : syracuseStep 959463 = 1439195) B1439195
theorem B1614991 : Blo 956588 1614991 := bstep (se 1 (by rfl) ⟨1211243, by rfl⟩ : syracuseStep 1614991 = 2422487) B2422487
theorem B4859027 : Blo 956588 4859027 := bstep (se 1 (by rfl) ⟨3644270, by rfl⟩ : syracuseStep 4859027 = 7288541) B7288541
theorem B2303219 : Blo 956588 2303219 := bstep (se 1 (by rfl) ⟨1727414, by rfl⟩ : syracuseStep 2303219 = 3454829) B3454829
theorem B959775 : Blo 956588 959775 := bstep (se 1 (by rfl) ⟨719831, by rfl⟩ : syracuseStep 959775 = 1439663) B1439663
theorem B959835 : Blo 956588 959835 := bstep (se 1 (by rfl) ⟨719876, by rfl⟩ : syracuseStep 959835 = 1439753) B1439753
theorem B959855 : Blo 956588 959855 := bstep (se 1 (by rfl) ⟨719891, by rfl⟩ : syracuseStep 959855 = 1439783) B1439783
theorem B1615241 : Blo 956588 1615241 := bstep (se 2 (by rfl) ⟨605715, by rfl⟩ : syracuseStep 1615241 = 1211431) B1211431
theorem B959911 : Blo 956588 959911 := bstep (se 1 (by rfl) ⟨719933, by rfl⟩ : syracuseStep 959911 = 1439867) B1439867
theorem B959995 : Blo 956588 959995 := bstep (se 1 (by rfl) ⟨719996, by rfl⟩ : syracuseStep 959995 = 1439993) B1439993
theorem B960063 : Blo 956588 960063 := bstep (se 1 (by rfl) ⟨720047, by rfl⟩ : syracuseStep 960063 = 1440095) B1440095
theorem B960071 : Blo 956588 960071 := bstep (se 1 (by rfl) ⟨720053, by rfl⟩ : syracuseStep 960071 = 1440107) B1440107
theorem B960223 : Blo 956588 960223 := bstep (se 1 (by rfl) ⟨720167, by rfl⟩ : syracuseStep 960223 = 1440335) B1440335
theorem B960303 : Blo 956588 960303 := bstep (se 1 (by rfl) ⟨720227, by rfl⟩ : syracuseStep 960303 = 1440455) B1440455
theorem B1615673 : Blo 956588 1615673 := bstep (se 2 (by rfl) ⟨605877, by rfl⟩ : syracuseStep 1615673 = 1211755) B1211755
theorem B960411 : Blo 956588 960411 := bstep (se 1 (by rfl) ⟨720308, by rfl⟩ : syracuseStep 960411 = 1440617) B1440617
theorem B960463 : Blo 956588 960463 := bstep (se 1 (by rfl) ⟨720347, by rfl⟩ : syracuseStep 960463 = 1440695) B1440695
theorem B960487 : Blo 956588 960487 := bstep (se 1 (by rfl) ⟨720365, by rfl⟩ : syracuseStep 960487 = 1440731) B1440731
theorem B5449913 : Blo 956588 5449913 := bstep (se 2 (by rfl) ⟨2043717, by rfl⟩ : syracuseStep 5449913 = 4087435) B4087435
theorem B5187779 : Blo 956588 5187779 := bstep (se 1 (by rfl) ⟨3890834, by rfl⟩ : syracuseStep 5187779 = 7781669) B7781669
theorem B12265789 : Blo 956588 12265789 := bstep (se 3 (by rfl) ⟨2299835, by rfl⟩ : syracuseStep 12265789 = 4599671) B4599671
theorem B2730743 : Blo 956588 2730743 := bstep (se 1 (by rfl) ⟨2048057, by rfl⟩ : syracuseStep 2730743 = 4096115) B4096115
theorem B1616719 : Blo 956588 1616719 := bstep (se 1 (by rfl) ⟨1212539, by rfl⟩ : syracuseStep 1616719 = 2425079) B2425079
theorem B2304911 : Blo 956588 2304911 := bstep (se 1 (by rfl) ⟨1728683, by rfl⟩ : syracuseStep 2304911 = 3457367) B3457367
theorem B6237199 : Blo 956588 6237199 := bstep (se 1 (by rfl) ⟨4677899, by rfl⟩ : syracuseStep 6237199 = 9355799) B9355799
theorem B44969093 : Blo 956588 44969093 := bstep (se 4 (by rfl) ⟨4215852, by rfl⟩ : syracuseStep 44969093 = 8431705) B8431705
theorem B1617401 : Blo 956588 1617401 := bstep (se 2 (by rfl) ⟨606525, by rfl⟩ : syracuseStep 1617401 = 1213051) B1213051
theorem B4370183 : Blo 956588 4370183 := bstep (se 1 (by rfl) ⟨3277637, by rfl⟩ : syracuseStep 4370183 = 6555275) B6555275
theorem B1617671 : Blo 956588 1617671 := bstep (se 1 (by rfl) ⟨1213253, by rfl⟩ : syracuseStep 1617671 = 2426507) B2426507
theorem B4599827 : Blo 956588 4599827 := bstep (se 1 (by rfl) ⟨3449870, by rfl⟩ : syracuseStep 4599827 = 6899741) B6899741
theorem B5189683 : Blo 956588 5189683 := bstep (se 1 (by rfl) ⟨3892262, by rfl⟩ : syracuseStep 5189683 = 7784525) B7784525
theorem B4862105 : Blo 956588 4862105 := bstep (se 2 (by rfl) ⟨1823289, by rfl⟩ : syracuseStep 4862105 = 3646579) B3646579
theorem B17740241 : Blo 956588 17740241 := bstep (se 2 (by rfl) ⟨6652590, by rfl⟩ : syracuseStep 17740241 = 13305181) B13305181
theorem B33698267 : Blo 956588 33698267 := bstep (se 1 (by rfl) ⟨25273700, by rfl⟩ : syracuseStep 33698267 = 50547401) B50547401
theorem B1618427 : Blo 956588 1618427 := bstep (se 1 (by rfl) ⟨1213820, by rfl⟩ : syracuseStep 1618427 = 2427641) B2427641
theorem B2044435 : Blo 956588 2044435 := bstep (se 1 (by rfl) ⟨1533326, by rfl⟩ : syracuseStep 2044435 = 3066653) B3066653
theorem B1618859 : Blo 956588 1618859 := bstep (se 1 (by rfl) ⟨1214144, by rfl⟩ : syracuseStep 1618859 = 2428289) B2428289
theorem B4862915 : Blo 956588 4862915 := bstep (se 1 (by rfl) ⟨3647186, by rfl⟩ : syracuseStep 4862915 = 7294373) B7294373
theorem B10367945 : Blo 956588 10367945 := bstep (se 2 (by rfl) ⟨3887979, by rfl⟩ : syracuseStep 10367945 = 7775959) B7775959
theorem B23311439 : Blo 956588 23311439 := bstep (se 1 (by rfl) ⟨17483579, by rfl⟩ : syracuseStep 23311439 = 34967159) B34967159
theorem B8762525 : Blo 956588 8762525 := bstep (se 3 (by rfl) ⟨1642973, by rfl⟩ : syracuseStep 8762525 = 3285947) B3285947
theorem B1619399 : Blo 956588 1619399 := bstep (se 1 (by rfl) ⟨1214549, by rfl⟩ : syracuseStep 1619399 = 2429099) B2429099
theorem B138459253 : Blo 956588 138459253 := bstep (se 5 (by rfl) ⟨6490277, by rfl⟩ : syracuseStep 138459253 = 12980555) B12980555
theorem B1620391 : Blo 956588 1620391 := bstep (se 1 (by rfl) ⟨1215293, by rfl⟩ : syracuseStep 1620391 = 2430587) B2430587
theorem B3455551 : Blo 956588 3455551 := bstep (se 1 (by rfl) ⟨2591663, by rfl⟩ : syracuseStep 3455551 = 5183327) B5183327
theorem B1620553 : Blo 956588 1620553 := bstep (se 2 (by rfl) ⟨607707, by rfl⟩ : syracuseStep 1620553 = 1215415) B1215415
theorem B1620587 : Blo 956588 1620587 := bstep (se 1 (by rfl) ⟨1215440, by rfl⟩ : syracuseStep 1620587 = 2430881) B2430881
theorem B5454971 : Blo 956588 5454971 := bstep (se 1 (by rfl) ⟨4091228, by rfl⟩ : syracuseStep 5454971 = 8182457) B8182457
theorem B13122805 : Blo 956588 13122805 := bstep (se 5 (by rfl) ⟨615131, by rfl⟩ : syracuseStep 13122805 = 1230263) B1230263
theorem B26590837 : Blo 956588 26590837 := bstep (se 5 (by rfl) ⟨1246445, by rfl⟩ : syracuseStep 26590837 = 2492891) B2492891
theorem B5455745 : Blo 956588 5455745 := bstep (se 2 (by rfl) ⟨2045904, by rfl⟩ : syracuseStep 5455745 = 4091809) B4091809
theorem B29475089 : Blo 956588 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B117916069 : Blo 956588 117916069 := bstep (se 4 (by rfl) ⟨11054631, by rfl⟩ : syracuseStep 117916069 = 22109263) B22109263
theorem B1819091 : Blo 956588 1819091 := bstep (se 1 (by rfl) ⟨1364318, by rfl⟩ : syracuseStep 1819091 = 2728637) B2728637
theorem B1753555 : Blo 956588 1753555 := bstep (se 1 (by rfl) ⟨1315166, by rfl⟩ : syracuseStep 1753555 = 2630333) B2630333
theorem B80724599 : Blo 956588 80724599 := bstep (se 1 (by rfl) ⟨60543449, by rfl⟩ : syracuseStep 80724599 = 121086899) B121086899
theorem B3064655 : Blo 956588 3064655 := bstep (se 1 (by rfl) ⟨2298491, by rfl⟩ : syracuseStep 3064655 = 4596983) B4596983
theorem B3064807 : Blo 956588 3064807 := bstep (se 1 (by rfl) ⟨2298605, by rfl⟩ : syracuseStep 3064807 = 4597211) B4597211
theorem B5458205 : Blo 956588 5458205 := bstep (se 3 (by rfl) ⟨1023413, by rfl⟩ : syracuseStep 5458205 = 2046827) B2046827
theorem B3230063 : Blo 956588 3230063 := bstep (se 1 (by rfl) ⟨2422547, by rfl⟩ : syracuseStep 3230063 = 4845095) B4845095
theorem B1296751 : Blo 956588 1296751 := bstep (se 1 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 1296751 = 1945127) B1945127
theorem B78694787 : Blo 956588 78694787 := bstep (se 1 (by rfl) ⟨59021090, by rfl⟩ : syracuseStep 78694787 = 118042181) B118042181
theorem B3066295 : Blo 956588 3066295 := bstep (se 1 (by rfl) ⟨2299721, by rfl⟩ : syracuseStep 3066295 = 4599443) B4599443
theorem B5458387 : Blo 956588 5458387 := bstep (se 1 (by rfl) ⟨4093790, by rfl⟩ : syracuseStep 5458387 = 8187581) B8187581
theorem B1821179 : Blo 956588 1821179 := bstep (se 1 (by rfl) ⟨1365884, by rfl⟩ : syracuseStep 1821179 = 2731769) B2731769
theorem B2215199 : Blo 956588 2215199 := bstep (se 1 (by rfl) ⟨1661399, by rfl⟩ : syracuseStep 2215199 = 3322799) B3322799
theorem B1822151 : Blo 956588 1822151 := bstep (se 1 (by rfl) ⟨1366613, by rfl⟩ : syracuseStep 1822151 = 2733227) B2733227
theorem B3460769 : Blo 956588 3460769 := bstep (se 2 (by rfl) ⟨1297788, by rfl⟩ : syracuseStep 3460769 = 2595577) B2595577
theorem B3231467 : Blo 956588 3231467 := bstep (se 1 (by rfl) ⟨2423600, by rfl⟩ : syracuseStep 3231467 = 4847201) B4847201
theorem B3067627 : Blo 956588 3067627 := bstep (se 1 (by rfl) ⟨2300720, by rfl⟩ : syracuseStep 3067627 = 4601441) B4601441
theorem B2216375 : Blo 956588 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B1823305 : Blo 956588 1823305 := bstep (se 2 (by rfl) ⟨683739, by rfl⟩ : syracuseStep 1823305 = 1367479) B1367479
theorem B3232439 : Blo 956588 3232439 := bstep (se 1 (by rfl) ⟨2424329, by rfl⟩ : syracuseStep 3232439 = 4848659) B4848659
theorem B35050195 : Blo 956588 35050195 := bstep (se 1 (by rfl) ⟨26287646, by rfl⟩ : syracuseStep 35050195 = 52575293) B52575293
theorem B6313085 : Blo 956588 6313085 := bstep (se 3 (by rfl) ⟨1183703, by rfl⟩ : syracuseStep 6313085 = 2367407) B2367407
theorem B4150651 : Blo 956588 4150651 := bstep (se 1 (by rfl) ⟨3112988, by rfl⟩ : syracuseStep 4150651 = 6225977) B6225977
theorem B1169383 : Blo 956588 1169383 := bstep (se 1 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 1169383 = 1754075) B1754075
theorem B2152457 : Blo 956588 2152457 := bstep (se 2 (by rfl) ⟨807171, by rfl⟩ : syracuseStep 2152457 = 1614343) B1614343
theorem B4675831 : Blo 956588 4675831 := bstep (se 1 (by rfl) ⟨3506873, by rfl⟩ : syracuseStep 4675831 = 7013747) B7013747
theorem B16406873 : Blo 956588 16406873 := bstep (se 2 (by rfl) ⟨6152577, by rfl⟩ : syracuseStep 16406873 = 12305155) B12305155
theorem B8739197 : Blo 956588 8739197 := bstep (se 3 (by rfl) ⟨1638599, by rfl⟩ : syracuseStep 8739197 = 3277199) B3277199
theorem B2152871 : Blo 956588 2152871 := bstep (se 1 (by rfl) ⟨1614653, by rfl⟩ : syracuseStep 2152871 = 3229307) B3229307
theorem B2152979 : Blo 956588 2152979 := bstep (se 1 (by rfl) ⟨1614734, by rfl⟩ : syracuseStep 2152979 = 3229469) B3229469
theorem B2153033 : Blo 956588 2153033 := bstep (se 2 (by rfl) ⟨807387, by rfl⟩ : syracuseStep 2153033 = 1614775) B1614775
theorem B3234383 : Blo 956588 3234383 := bstep (se 1 (by rfl) ⟨2425787, by rfl⟩ : syracuseStep 3234383 = 4851575) B4851575
theorem B4086395 : Blo 956588 4086395 := bstep (se 1 (by rfl) ⟨3064796, by rfl⟩ : syracuseStep 4086395 = 6129593) B6129593
theorem B3070639 : Blo 956588 3070639 := bstep (se 1 (by rfl) ⟨2302979, by rfl⟩ : syracuseStep 3070639 = 4605959) B4605959
theorem B4086683 : Blo 956588 4086683 := bstep (se 1 (by rfl) ⟨3065012, by rfl⟩ : syracuseStep 4086683 = 6130025) B6130025
theorem B2153447 : Blo 956588 2153447 := bstep (se 1 (by rfl) ⟨1615085, by rfl⟩ : syracuseStep 2153447 = 3230171) B3230171
theorem B44194895 : Blo 956588 44194895 := bstep (se 1 (by rfl) ⟨33146171, by rfl⟩ : syracuseStep 44194895 = 66292343) B66292343
theorem B3890315 : Blo 956588 3890315 := bstep (se 1 (by rfl) ⟨2917736, by rfl⟩ : syracuseStep 3890315 = 5835473) B5835473
theorem B2153825 : Blo 956588 2153825 := bstep (se 2 (by rfl) ⟨807684, by rfl⟩ : syracuseStep 2153825 = 1615369) B1615369
theorem B2153915 : Blo 956588 2153915 := bstep (se 1 (by rfl) ⟨1615436, by rfl⟩ : syracuseStep 2153915 = 3230873) B3230873
theorem B9199115 : Blo 956588 9199115 := bstep (se 1 (by rfl) ⟨6899336, by rfl⟩ : syracuseStep 9199115 = 13798673) B13798673
theorem B2154041 : Blo 956588 2154041 := bstep (se 2 (by rfl) ⟨807765, by rfl⟩ : syracuseStep 2154041 = 1615531) B1615531
theorem B3235625 : Blo 956588 3235625 := bstep (se 2 (by rfl) ⟨1213359, by rfl⟩ : syracuseStep 3235625 = 2426719) B2426719
theorem B4087709 : Blo 956588 4087709 := bstep (se 3 (by rfl) ⟨766445, by rfl⟩ : syracuseStep 4087709 = 1532891) B1532891
theorem B2154707 : Blo 956588 2154707 := bstep (se 1 (by rfl) ⟨1616030, by rfl⟩ : syracuseStep 2154707 = 3232061) B3232061
theorem B2154761 : Blo 956588 2154761 := bstep (se 2 (by rfl) ⟨808035, by rfl⟩ : syracuseStep 2154761 = 1616071) B1616071
theorem B4088171 : Blo 956588 4088171 := bstep (se 1 (by rfl) ⟨3066128, by rfl⟩ : syracuseStep 4088171 = 6132257) B6132257
theorem B2154977 : Blo 956588 2154977 := bstep (se 2 (by rfl) ⟨808116, by rfl⟩ : syracuseStep 2154977 = 1616233) B1616233
theorem B7365323 : Blo 956588 7365323 := bstep (se 1 (by rfl) ⟨5523992, by rfl⟩ : syracuseStep 7365323 = 11047985) B11047985
theorem B2155283 : Blo 956588 2155283 := bstep (se 1 (by rfl) ⟨1616462, by rfl⟩ : syracuseStep 2155283 = 3232925) B3232925
theorem B5530463 : Blo 956588 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B2155643 : Blo 956588 2155643 := bstep (se 1 (by rfl) ⟨1616732, by rfl⟩ : syracuseStep 2155643 = 3233465) B3233465
theorem B2155769 : Blo 956588 2155769 := bstep (se 2 (by rfl) ⟨808413, by rfl⟩ : syracuseStep 2155769 = 1616827) B1616827
theorem B1434911 : Blo 956588 1434911 := bstep (se 1 (by rfl) ⟨1076183, by rfl⟩ : syracuseStep 1434911 = 2152367) B2152367
theorem B2155913 : Blo 956588 2155913 := bstep (se 2 (by rfl) ⟨808467, by rfl⟩ : syracuseStep 2155913 = 1616935) B1616935
theorem B9856399 : Blo 956588 9856399 := bstep (se 1 (by rfl) ⟨7392299, by rfl⟩ : syracuseStep 9856399 = 14784599) B14784599
theorem B1435079 : Blo 956588 1435079 := bstep (se 1 (by rfl) ⟨1076309, by rfl⟩ : syracuseStep 1435079 = 2152619) B2152619
theorem B4842989 : Blo 956588 4842989 := bstep (se 3 (by rfl) ⟨908060, by rfl⟩ : syracuseStep 4842989 = 1816121) B1816121
theorem B2156039 : Blo 956588 2156039 := bstep (se 1 (by rfl) ⟨1617029, by rfl⟩ : syracuseStep 2156039 = 3234059) B3234059
theorem B2156219 : Blo 956588 2156219 := bstep (se 1 (by rfl) ⟨1617164, by rfl⟩ : syracuseStep 2156219 = 3234329) B3234329
theorem B1435433 : Blo 956588 1435433 := bstep (se 2 (by rfl) ⟨538287, by rfl⟩ : syracuseStep 1435433 = 1076575) B1076575
theorem B1533737 : Blo 956588 1533737 := bstep (se 2 (by rfl) ⟨575151, by rfl⟩ : syracuseStep 1533737 = 1150303) B1150303
theorem B1435439 : Blo 956588 1435439 := bstep (se 1 (by rfl) ⟨1076579, by rfl⟩ : syracuseStep 1435439 = 2153159) B2153159
theorem B2156345 : Blo 956588 2156345 := bstep (se 2 (by rfl) ⟨808629, by rfl⟩ : syracuseStep 2156345 = 1617259) B1617259
theorem B3237839 : Blo 956588 3237839 := bstep (se 1 (by rfl) ⟨2428379, by rfl⟩ : syracuseStep 3237839 = 4856759) B4856759
theorem B1435913 : Blo 956588 1435913 := bstep (se 2 (by rfl) ⟨538467, by rfl⟩ : syracuseStep 1435913 = 1076935) B1076935
theorem B4843799 : Blo 956588 4843799 := bstep (se 1 (by rfl) ⟨3632849, by rfl⟩ : syracuseStep 4843799 = 7265699) B7265699
theorem B1436015 : Blo 956588 1436015 := bstep (se 1 (by rfl) ⟨1077011, by rfl⟩ : syracuseStep 1436015 = 2154023) B2154023
theorem B2156975 : Blo 956588 2156975 := bstep (se 1 (by rfl) ⟨1617731, by rfl⟩ : syracuseStep 2156975 = 3235463) B3235463
theorem B2157011 : Blo 956588 2157011 := bstep (se 1 (by rfl) ⟨1617758, by rfl⟩ : syracuseStep 2157011 = 3235517) B3235517
theorem B2157119 : Blo 956588 2157119 := bstep (se 1 (by rfl) ⟨1617839, by rfl⟩ : syracuseStep 2157119 = 3235679) B3235679
theorem B1436231 : Blo 956588 1436231 := bstep (se 1 (by rfl) ⟨1077173, by rfl⟩ : syracuseStep 1436231 = 2154347) B2154347
theorem B1436267 : Blo 956588 1436267 := bstep (se 1 (by rfl) ⟨1077200, by rfl⟩ : syracuseStep 1436267 = 2154401) B2154401
theorem B2157227 : Blo 956588 2157227 := bstep (se 1 (by rfl) ⟨1617920, by rfl⟩ : syracuseStep 2157227 = 3235841) B3235841
theorem B1436495 : Blo 956588 1436495 := bstep (se 1 (by rfl) ⟨1077371, by rfl⟩ : syracuseStep 1436495 = 2154743) B2154743
theorem B3238811 : Blo 956588 3238811 := bstep (se 1 (by rfl) ⟨2429108, by rfl⟩ : syracuseStep 3238811 = 4858217) B4858217
theorem B3075059 : Blo 956588 3075059 := bstep (se 1 (by rfl) ⟨2306294, by rfl⟩ : syracuseStep 3075059 = 4612589) B4612589
theorem B1534967 : Blo 956588 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B7892045 : Blo 956588 7892045 := bstep (se 3 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 7892045 = 2959517) B2959517
theorem B2157767 : Blo 956588 2157767 := bstep (se 1 (by rfl) ⟨1618325, by rfl⟩ : syracuseStep 2157767 = 3236651) B3236651
theorem B1436891 : Blo 956588 1436891 := bstep (se 1 (by rfl) ⟨1077668, by rfl⟩ : syracuseStep 1436891 = 2155337) B2155337
theorem B2157947 : Blo 956588 2157947 := bstep (se 1 (by rfl) ⟨1618460, by rfl⟩ : syracuseStep 2157947 = 3236921) B3236921
theorem B1437065 : Blo 956588 1437065 := bstep (se 2 (by rfl) ⟨538899, by rfl⟩ : syracuseStep 1437065 = 1077799) B1077799
theorem B1076647 : Blo 956588 1076647 := bstep (se 1 (by rfl) ⟨807485, by rfl⟩ : syracuseStep 1076647 = 1614971) B1614971
theorem B2158073 : Blo 956588 2158073 := bstep (se 2 (by rfl) ⟨809277, by rfl⟩ : syracuseStep 2158073 = 1618555) B1618555
theorem B2158163 : Blo 956588 2158163 := bstep (se 1 (by rfl) ⟨1618622, by rfl⟩ : syracuseStep 2158163 = 3237245) B3237245
theorem B1437419 : Blo 956588 1437419 := bstep (se 1 (by rfl) ⟨1078064, by rfl⟩ : syracuseStep 1437419 = 2156129) B2156129
theorem B2158343 : Blo 956588 2158343 := bstep (se 1 (by rfl) ⟨1618757, by rfl⟩ : syracuseStep 2158343 = 3237515) B3237515
theorem B3632957 : Blo 956588 3632957 := bstep (se 3 (by rfl) ⟨681179, by rfl⟩ : syracuseStep 3632957 = 1362359) B1362359
theorem B4845419 : Blo 956588 4845419 := bstep (se 1 (by rfl) ⟨3634064, by rfl⟩ : syracuseStep 4845419 = 7268129) B7268129
theorem B3239837 : Blo 956588 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B1437647 : Blo 956588 1437647 := bstep (se 1 (by rfl) ⟨1078235, by rfl⟩ : syracuseStep 1437647 = 2156471) B2156471
theorem B1077223 : Blo 956588 1077223 := bstep (se 1 (by rfl) ⟨807917, by rfl⟩ : syracuseStep 1077223 = 1615835) B1615835
theorem B3239945 : Blo 956588 3239945 := bstep (se 2 (by rfl) ⟨1214979, by rfl⟩ : syracuseStep 3239945 = 2429959) B2429959
theorem B3109211 : Blo 956588 3109211 := bstep (se 1 (by rfl) ⟨2331908, by rfl⟩ : syracuseStep 3109211 = 4663817) B4663817
theorem B1438043 : Blo 956588 1438043 := bstep (se 1 (by rfl) ⟨1078532, by rfl⟩ : syracuseStep 1438043 = 2157065) B2157065
theorem B2158955 : Blo 956588 2158955 := bstep (se 1 (by rfl) ⟨1619216, by rfl⟩ : syracuseStep 2158955 = 3238433) B3238433
theorem B2159099 : Blo 956588 2159099 := bstep (se 1 (by rfl) ⟨1619324, by rfl⟩ : syracuseStep 2159099 = 3238649) B3238649
theorem B1438271 : Blo 956588 1438271 := bstep (se 1 (by rfl) ⟨1078703, by rfl⟩ : syracuseStep 1438271 = 2157407) B2157407
theorem B2159225 : Blo 956588 2159225 := bstep (se 2 (by rfl) ⟨809709, by rfl⟩ : syracuseStep 2159225 = 1619419) B1619419
theorem B2159279 : Blo 956588 2159279 := bstep (se 1 (by rfl) ⟨1619459, by rfl⟩ : syracuseStep 2159279 = 3238919) B3238919
theorem B1438391 : Blo 956588 1438391 := bstep (se 1 (by rfl) ⟨1078793, by rfl⟩ : syracuseStep 1438391 = 2157587) B2157587
theorem B18412217 : Blo 956588 18412217 := bstep (se 2 (by rfl) ⟨6904581, by rfl⟩ : syracuseStep 18412217 = 13809163) B13809163
theorem B2159351 : Blo 956588 2159351 := bstep (se 1 (by rfl) ⟨1619513, by rfl⟩ : syracuseStep 2159351 = 3239027) B3239027
theorem B4092767 : Blo 956588 4092767 := bstep (se 1 (by rfl) ⟨3069575, by rfl⟩ : syracuseStep 4092767 = 6139151) B6139151
theorem B2421647 : Blo 956588 2421647 := bstep (se 1 (by rfl) ⟨1816235, by rfl⟩ : syracuseStep 2421647 = 3632471) B3632471
theorem B1438619 : Blo 956588 1438619 := bstep (se 1 (by rfl) ⟨1078964, by rfl⟩ : syracuseStep 1438619 = 2157929) B2157929
theorem B2159531 : Blo 956588 2159531 := bstep (se 1 (by rfl) ⟨1619648, by rfl⟩ : syracuseStep 2159531 = 3239297) B3239297
theorem B1439015 : Blo 956588 1439015 := bstep (se 1 (by rfl) ⟨1079261, by rfl⟩ : syracuseStep 1439015 = 2158523) B2158523
theorem B1537319 : Blo 956588 1537319 := bstep (se 1 (by rfl) ⟨1152989, by rfl⟩ : syracuseStep 1537319 = 2305979) B2305979
theorem B1439099 : Blo 956588 1439099 := bstep (se 1 (by rfl) ⟨1079324, by rfl⟩ : syracuseStep 1439099 = 2158649) B2158649
theorem B2160071 : Blo 956588 2160071 := bstep (se 1 (by rfl) ⟨1620053, by rfl⟩ : syracuseStep 2160071 = 3240107) B3240107
theorem B1439225 : Blo 956588 1439225 := bstep (se 2 (by rfl) ⟨539709, by rfl⟩ : syracuseStep 1439225 = 1079419) B1079419
theorem B1078879 : Blo 956588 1078879 := bstep (se 1 (by rfl) ⟨809159, by rfl⟩ : syracuseStep 1078879 = 1618319) B1618319
theorem B1439327 : Blo 956588 1439327 := bstep (se 1 (by rfl) ⟨1079495, by rfl⟩ : syracuseStep 1439327 = 2158991) B2158991
theorem B2422507 : Blo 956588 2422507 := bstep (se 1 (by rfl) ⟨1816880, by rfl⟩ : syracuseStep 2422507 = 3633761) B3633761
theorem B2160431 : Blo 956588 2160431 := bstep (se 1 (by rfl) ⟨1620323, by rfl⟩ : syracuseStep 2160431 = 3240647) B3240647
theorem B1439543 : Blo 956588 1439543 := bstep (se 1 (by rfl) ⟨1079657, by rfl⟩ : syracuseStep 1439543 = 2159315) B2159315
theorem B76904549 : Blo 956588 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B1439849 : Blo 956588 1439849 := bstep (se 2 (by rfl) ⟨539943, by rfl⟩ : syracuseStep 1439849 = 1079887) B1079887
theorem B2161007 : Blo 956588 2161007 := bstep (se 1 (by rfl) ⟨1620755, by rfl⟩ : syracuseStep 2161007 = 3241511) B3241511
theorem B1440167 : Blo 956588 1440167 := bstep (se 1 (by rfl) ⟨1080125, by rfl⟩ : syracuseStep 1440167 = 2160251) B2160251
theorem B2161079 : Blo 956588 2161079 := bstep (se 1 (by rfl) ⟨1620809, by rfl⟩ : syracuseStep 2161079 = 3241619) B3241619
theorem B4094459 : Blo 956588 4094459 := bstep (se 1 (by rfl) ⟨3070844, by rfl⟩ : syracuseStep 4094459 = 6141689) B6141689
theorem B1440251 : Blo 956588 1440251 := bstep (se 1 (by rfl) ⟨1080188, by rfl⟩ : syracuseStep 1440251 = 2160377) B2160377
theorem B2161223 : Blo 956588 2161223 := bstep (se 1 (by rfl) ⟨1620917, by rfl⟩ : syracuseStep 2161223 = 3241835) B3241835
theorem B4094543 : Blo 956588 4094543 := bstep (se 1 (by rfl) ⟨3070907, by rfl⟩ : syracuseStep 4094543 = 6141815) B6141815
theorem B2161259 : Blo 956588 2161259 := bstep (se 1 (by rfl) ⟨1620944, by rfl⟩ : syracuseStep 2161259 = 3241889) B3241889
theorem B1440377 : Blo 956588 1440377 := bstep (se 2 (by rfl) ⟨540141, by rfl⟩ : syracuseStep 1440377 = 1080283) B1080283
theorem B13826693 : Blo 956588 13826693 := bstep (se 4 (by rfl) ⟨1296252, by rfl⟩ : syracuseStep 13826693 = 2592505) B2592505
theorem B33258119 : Blo 956588 33258119 := bstep (se 1 (by rfl) ⟨24943589, by rfl⟩ : syracuseStep 33258119 = 49887179) B49887179
theorem B3635887 : Blo 956588 3635887 := bstep (se 1 (by rfl) ⟨2726915, by rfl⟩ : syracuseStep 3635887 = 5453831) B5453831
theorem B1440431 : Blo 956588 1440431 := bstep (se 1 (by rfl) ⟨1080323, by rfl⟩ : syracuseStep 1440431 = 2160647) B2160647
theorem B2423479 : Blo 956588 2423479 := bstep (se 1 (by rfl) ⟨1817609, by rfl⟩ : syracuseStep 2423479 = 3635219) B3635219
theorem B1080031 : Blo 956588 1080031 := bstep (se 1 (by rfl) ⟨810023, by rfl⟩ : syracuseStep 1080031 = 1620047) B1620047
theorem B1440479 : Blo 956588 1440479 := bstep (se 1 (by rfl) ⟨1080359, by rfl⟩ : syracuseStep 1440479 = 2160719) B2160719
theorem B2423783 : Blo 956588 2423783 := bstep (se 1 (by rfl) ⟨1817837, by rfl⟩ : syracuseStep 2423783 = 3635675) B3635675
theorem B1440743 : Blo 956588 1440743 := bstep (se 1 (by rfl) ⟨1080557, by rfl⟩ : syracuseStep 1440743 = 2161115) B2161115
theorem B11074589 : Blo 956588 11074589 := bstep (se 3 (by rfl) ⟨2076485, by rfl⟩ : syracuseStep 11074589 = 4152971) B4152971
theorem B8191205 : Blo 956588 8191205 := bstep (se 4 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 8191205 = 1535851) B1535851
theorem B1080607 : Blo 956588 1080607 := bstep (se 1 (by rfl) ⟨810455, by rfl⟩ : syracuseStep 1080607 = 1620911) B1620911
theorem B1637671 : Blo 956588 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B4095431 : Blo 956588 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B4849145 : Blo 956588 4849145 := bstep (se 2 (by rfl) ⟨1818429, by rfl⟩ : syracuseStep 4849145 = 3636859) B3636859
theorem B3636845 : Blo 956588 3636845 := bstep (se 3 (by rfl) ⟨681908, by rfl⟩ : syracuseStep 3636845 = 1363817) B1363817
theorem B1212079 : Blo 956588 1212079 := bstep (se 1 (by rfl) ⟨909059, by rfl⟩ : syracuseStep 1212079 = 1818119) B1818119
theorem B4849469 : Blo 956588 4849469 := bstep (se 3 (by rfl) ⟨909275, by rfl⟩ : syracuseStep 4849469 = 1818551) B1818551
theorem B10354625 : Blo 956588 10354625 := bstep (se 2 (by rfl) ⟨3882984, by rfl⟩ : syracuseStep 10354625 = 7765969) B7765969
theorem B12451843 : Blo 956588 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B1212727 : Blo 956588 1212727 := bstep (se 1 (by rfl) ⟨909545, by rfl⟩ : syracuseStep 1212727 = 1819091) B1819091
theorem B157221425 : Blo 956588 157221425 := bstep (se 2 (by rfl) ⟨58958034, by rfl⟩ : syracuseStep 157221425 = 117916069) B117916069
theorem B4850441 : Blo 956588 4850441 := bstep (se 2 (by rfl) ⟨1818915, by rfl⟩ : syracuseStep 4850441 = 3637831) B3637831
theorem B1639531 : Blo 956588 1639531 := bstep (se 1 (by rfl) ⟨1229648, by rfl⟩ : syracuseStep 1639531 = 2459297) B2459297
theorem B3638803 : Blo 956588 3638803 := bstep (se 1 (by rfl) ⟨2729102, by rfl⟩ : syracuseStep 3638803 = 5458205) B5458205
theorem B3278431 : Blo 956588 3278431 := bstep (se 1 (by rfl) ⟨2458823, by rfl⟩ : syracuseStep 3278431 = 4917647) B4917647
theorem B6227567 : Blo 956588 6227567 := bstep (se 1 (by rfl) ⟨4670675, by rfl⟩ : syracuseStep 6227567 = 9341351) B9341351
theorem B1214119 : Blo 956588 1214119 := bstep (se 1 (by rfl) ⟨910589, by rfl⟩ : syracuseStep 1214119 = 1821179) B1821179
theorem B13141865 : Blo 956588 13141865 := bstep (se 2 (by rfl) ⟨4928199, by rfl⟩ : syracuseStep 13141865 = 9856399) B9856399
theorem B1476799 : Blo 956588 1476799 := bstep (se 1 (by rfl) ⟨1107599, by rfl⟩ : syracuseStep 1476799 = 2215199) B2215199
theorem B1214767 : Blo 956588 1214767 := bstep (se 1 (by rfl) ⟨911075, by rfl⟩ : syracuseStep 1214767 = 1822151) B1822151
theorem B16354385 : Blo 956588 16354385 := bstep (se 2 (by rfl) ⟨6132894, by rfl⟩ : syracuseStep 16354385 = 12265789) B12265789
theorem B2428127 : Blo 956588 2428127 := bstep (se 1 (by rfl) ⟨1821095, by rfl⟩ : syracuseStep 2428127 = 3642191) B3642191
theorem B7277849 : Blo 956588 7277849 := bstep (se 2 (by rfl) ⟨2729193, by rfl⟩ : syracuseStep 7277849 = 5458387) B5458387
theorem B4099517 : Blo 956588 4099517 := bstep (se 3 (by rfl) ⟨768659, by rfl⟩ : syracuseStep 4099517 = 1537319) B1537319
theorem B3280375 : Blo 956588 3280375 := bstep (se 1 (by rfl) ⟨2460281, by rfl⟩ : syracuseStep 3280375 = 4920563) B4920563
theorem B8195579 : Blo 956588 8195579 := bstep (se 1 (by rfl) ⟨6146684, by rfl⟩ : syracuseStep 8195579 = 12293369) B12293369
theorem B2429311 : Blo 956588 2429311 := bstep (se 1 (by rfl) ⟨1821983, by rfl⟩ : syracuseStep 2429311 = 3643967) B3643967
theorem B2724263 : Blo 956588 2724263 := bstep (se 1 (by rfl) ⟨2043197, by rfl⟩ : syracuseStep 2724263 = 4086395) B4086395
theorem B2724455 : Blo 956588 2724455 := bstep (se 1 (by rfl) ⟨2043341, by rfl⟩ : syracuseStep 2724455 = 4086683) B4086683
theorem B29463263 : Blo 956588 29463263 := bstep (se 1 (by rfl) ⟨22097447, by rfl⟩ : syracuseStep 29463263 = 44194895) B44194895
theorem B2593543 : Blo 956588 2593543 := bstep (se 1 (by rfl) ⟨1945157, by rfl⟩ : syracuseStep 2593543 = 3890315) B3890315
theorem B6132743 : Blo 956588 6132743 := bstep (se 1 (by rfl) ⟨4599557, by rfl⟩ : syracuseStep 6132743 = 9199115) B9199115
theorem B99751061 : Blo 956588 99751061 := bstep (se 6 (by rfl) ⟨2337915, by rfl⟩ : syracuseStep 99751061 = 4675831) B4675831
theorem B2725139 : Blo 956588 2725139 := bstep (se 1 (by rfl) ⟨2043854, by rfl⟩ : syracuseStep 2725139 = 4087709) B4087709
theorem B6919577 : Blo 956588 6919577 := bstep (se 2 (by rfl) ⟨2594841, by rfl⟩ : syracuseStep 6919577 = 5189683) B5189683
theorem B2725447 : Blo 956588 2725447 := bstep (se 1 (by rfl) ⟨2044085, by rfl⟩ : syracuseStep 2725447 = 4088171) B4088171
theorem B5904343 : Blo 956588 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B2725913 : Blo 956588 2725913 := bstep (se 2 (by rfl) ⟨1022217, by rfl⟩ : syracuseStep 2725913 = 2044435) B2044435
theorem B2431073 : Blo 956588 2431073 := bstep (se 2 (by rfl) ⟨911652, by rfl⟩ : syracuseStep 2431073 = 1823305) B1823305
theorem B956607 : Blo 956588 956607 := bstep (se 1 (by rfl) ⟨717455, by rfl⟩ : syracuseStep 956607 = 1434911) B1434911
theorem B46733593 : Blo 956588 46733593 := bstep (se 2 (by rfl) ⟨17525097, by rfl⟩ : syracuseStep 46733593 = 35050195) B35050195
theorem B956719 : Blo 956588 956719 := bstep (se 1 (by rfl) ⟨717539, by rfl⟩ : syracuseStep 956719 = 1435079) B1435079
theorem B209852765 : Blo 956588 209852765 := bstep (se 3 (by rfl) ⟨39347393, by rfl⟩ : syracuseStep 209852765 = 78694787) B78694787
theorem B956955 : Blo 956588 956955 := bstep (se 1 (by rfl) ⟨717716, by rfl⟩ : syracuseStep 956955 = 1435433) B1435433
theorem B1022491 : Blo 956588 1022491 := bstep (se 1 (by rfl) ⟨766868, by rfl⟩ : syracuseStep 1022491 = 1533737) B1533737
theorem B956959 : Blo 956588 956959 := bstep (se 1 (by rfl) ⟨717719, by rfl⟩ : syracuseStep 956959 = 1435439) B1435439
theorem B957275 : Blo 956588 957275 := bstep (se 1 (by rfl) ⟨717956, by rfl⟩ : syracuseStep 957275 = 1435913) B1435913
theorem B957343 : Blo 956588 957343 := bstep (se 1 (by rfl) ⟨718007, by rfl⟩ : syracuseStep 957343 = 1436015) B1436015
theorem B957487 : Blo 956588 957487 := bstep (se 1 (by rfl) ⟨718115, by rfl⟩ : syracuseStep 957487 = 1436231) B1436231
theorem B957511 : Blo 956588 957511 := bstep (se 1 (by rfl) ⟨718133, by rfl⟩ : syracuseStep 957511 = 1436267) B1436267
theorem B957663 : Blo 956588 957663 := bstep (se 1 (by rfl) ⟨718247, by rfl⟩ : syracuseStep 957663 = 1436495) B1436495
theorem B1023311 : Blo 956588 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B957927 : Blo 956588 957927 := bstep (se 1 (by rfl) ⟨718445, by rfl⟩ : syracuseStep 957927 = 1436891) B1436891
theorem B958043 : Blo 956588 958043 := bstep (se 1 (by rfl) ⟨718532, by rfl⟩ : syracuseStep 958043 = 1437065) B1437065
theorem B958279 : Blo 956588 958279 := bstep (se 1 (by rfl) ⟨718709, by rfl⟩ : syracuseStep 958279 = 1437419) B1437419
theorem B958431 : Blo 956588 958431 := bstep (se 1 (by rfl) ⟨718823, by rfl⟩ : syracuseStep 958431 = 1437647) B1437647
theorem B2072807 : Blo 956588 2072807 := bstep (se 1 (by rfl) ⟨1554605, by rfl⟩ : syracuseStep 2072807 = 3109211) B3109211
theorem B958695 : Blo 956588 958695 := bstep (se 1 (by rfl) ⟨719021, by rfl⟩ : syracuseStep 958695 = 1438043) B1438043
theorem B958847 : Blo 956588 958847 := bstep (se 1 (by rfl) ⟨719135, by rfl⟩ : syracuseStep 958847 = 1438271) B1438271
theorem B958927 : Blo 956588 958927 := bstep (se 1 (by rfl) ⟨719195, by rfl⟩ : syracuseStep 958927 = 1438391) B1438391
theorem B2728511 : Blo 956588 2728511 := bstep (se 1 (by rfl) ⟨2046383, by rfl⟩ : syracuseStep 2728511 = 4092767) B4092767
theorem B1614431 : Blo 956588 1614431 := bstep (se 1 (by rfl) ⟨1210823, by rfl⟩ : syracuseStep 1614431 = 2421647) B2421647
theorem B959079 : Blo 956588 959079 := bstep (se 1 (by rfl) ⟨719309, by rfl⟩ : syracuseStep 959079 = 1438619) B1438619
theorem B15540959 : Blo 956588 15540959 := bstep (se 1 (by rfl) ⟨11655719, by rfl⟩ : syracuseStep 15540959 = 23311439) B23311439
theorem B5841683 : Blo 956588 5841683 := bstep (se 1 (by rfl) ⟨4381262, by rfl⟩ : syracuseStep 5841683 = 8762525) B8762525
theorem B959343 : Blo 956588 959343 := bstep (se 1 (by rfl) ⟨719507, by rfl⟩ : syracuseStep 959343 = 1439015) B1439015
theorem B959399 : Blo 956588 959399 := bstep (se 1 (by rfl) ⟨719549, by rfl⟩ : syracuseStep 959399 = 1439099) B1439099
theorem B959483 : Blo 956588 959483 := bstep (se 1 (by rfl) ⟨719612, by rfl⟩ : syracuseStep 959483 = 1439225) B1439225
theorem B959551 : Blo 956588 959551 := bstep (se 1 (by rfl) ⟨719663, by rfl⟩ : syracuseStep 959551 = 1439327) B1439327
theorem B959695 : Blo 956588 959695 := bstep (se 1 (by rfl) ⟨719771, by rfl⟩ : syracuseStep 959695 = 1439543) B1439543
theorem B959899 : Blo 956588 959899 := bstep (se 1 (by rfl) ⟨719924, by rfl⟩ : syracuseStep 959899 = 1439849) B1439849
theorem B960111 : Blo 956588 960111 := bstep (se 1 (by rfl) ⟨720083, by rfl⟩ : syracuseStep 960111 = 1440167) B1440167
theorem B4859513 : Blo 956588 4859513 := bstep (se 2 (by rfl) ⟨1822317, by rfl⟩ : syracuseStep 4859513 = 3644635) B3644635
theorem B2729639 : Blo 956588 2729639 := bstep (se 1 (by rfl) ⟨2047229, by rfl⟩ : syracuseStep 2729639 = 4094459) B4094459
theorem B960167 : Blo 956588 960167 := bstep (se 1 (by rfl) ⟨720125, by rfl⟩ : syracuseStep 960167 = 1440251) B1440251
theorem B2729695 : Blo 956588 2729695 := bstep (se 1 (by rfl) ⟨2047271, by rfl⟩ : syracuseStep 2729695 = 4094543) B4094543
theorem B960251 : Blo 956588 960251 := bstep (se 1 (by rfl) ⟨720188, by rfl⟩ : syracuseStep 960251 = 1440377) B1440377
theorem B9217795 : Blo 956588 9217795 := bstep (se 1 (by rfl) ⟨6913346, by rfl⟩ : syracuseStep 9217795 = 13826693) B13826693
theorem B960287 : Blo 956588 960287 := bstep (se 1 (by rfl) ⟨720215, by rfl⟩ : syracuseStep 960287 = 1440431) B1440431
theorem B960319 : Blo 956588 960319 := bstep (se 1 (by rfl) ⟨720239, by rfl⟩ : syracuseStep 960319 = 1440479) B1440479
theorem B1615855 : Blo 956588 1615855 := bstep (se 1 (by rfl) ⟨1211891, by rfl⟩ : syracuseStep 1615855 = 2423783) B2423783
theorem B960495 : Blo 956588 960495 := bstep (se 1 (by rfl) ⟨720371, by rfl⟩ : syracuseStep 960495 = 1440743) B1440743
theorem B7383059 : Blo 956588 7383059 := bstep (se 1 (by rfl) ⟨5537294, by rfl⟩ : syracuseStep 7383059 = 11074589) B11074589
theorem B1616105 : Blo 956588 1616105 := bstep (se 2 (by rfl) ⟨606039, by rfl⟩ : syracuseStep 1616105 = 1212079) B1212079
theorem B2730287 : Blo 956588 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B13806395 : Blo 956588 13806395 := bstep (se 1 (by rfl) ⟨10354796, by rfl⟩ : syracuseStep 13806395 = 20709593) B20709593
theorem B6302657 : Blo 956588 6302657 := bstep (se 2 (by rfl) ⟨2363496, by rfl⟩ : syracuseStep 6302657 = 4726993) B4726993
theorem B2730971 : Blo 956588 2730971 := bstep (se 1 (by rfl) ⟨2048228, by rfl⟩ : syracuseStep 2730971 = 4096457) B4096457
theorem B53816399 : Blo 956588 53816399 := bstep (se 1 (by rfl) ⟨40362299, by rfl⟩ : syracuseStep 53816399 = 80724599) B80724599
theorem B2043103 : Blo 956588 2043103 := bstep (se 1 (by rfl) ⟨1532327, by rfl⟩ : syracuseStep 2043103 = 3064655) B3064655
theorem B2338073 : Blo 956588 2338073 := bstep (se 2 (by rfl) ⟨876777, by rfl⟩ : syracuseStep 2338073 = 1753555) B1753555
theorem B1617583 : Blo 956588 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B1617887 : Blo 956588 1617887 := bstep (se 1 (by rfl) ⟨1213415, by rfl⟩ : syracuseStep 1617887 = 2426831) B2426831
theorem B1618231 : Blo 956588 1618231 := bstep (se 1 (by rfl) ⟨1213673, by rfl⟩ : syracuseStep 1618231 = 2427347) B2427347
theorem B7188965 : Blo 956588 7188965 := bstep (se 4 (by rfl) ⟨673965, by rfl⟩ : syracuseStep 7188965 = 1347931) B1347931
theorem B1618535 : Blo 956588 1618535 := bstep (se 1 (by rfl) ⟨1213901, by rfl⟩ : syracuseStep 1618535 = 2427803) B2427803
theorem B4371191 : Blo 956588 4371191 := bstep (se 1 (by rfl) ⟨3278393, by rfl⟩ : syracuseStep 4371191 = 6556787) B6556787
theorem B9220871 : Blo 956588 9220871 := bstep (se 1 (by rfl) ⟨6915653, by rfl⟩ : syracuseStep 9220871 = 13831307) B13831307
theorem B1618697 : Blo 956588 1618697 := bstep (se 2 (by rfl) ⟨607011, by rfl⟩ : syracuseStep 1618697 = 1214023) B1214023
theorem B2307179 : Blo 956588 2307179 := bstep (se 1 (by rfl) ⟨1730384, by rfl⟩ : syracuseStep 2307179 = 3460769) B3460769
theorem B8172683 : Blo 956588 8172683 := bstep (se 1 (by rfl) ⟨6129512, by rfl⟩ : syracuseStep 8172683 = 12259025) B12259025
theorem B1619291 : Blo 956588 1619291 := bstep (se 1 (by rfl) ⟨1214468, by rfl⟩ : syracuseStep 1619291 = 2428937) B2428937
theorem B1619527 : Blo 956588 1619527 := bstep (se 1 (by rfl) ⟨1214645, by rfl⟩ : syracuseStep 1619527 = 2429291) B2429291
theorem B9221795 : Blo 956588 9221795 := bstep (se 1 (by rfl) ⟨6916346, by rfl⟩ : syracuseStep 9221795 = 13832693) B13832693
theorem B1619743 : Blo 956588 1619743 := bstep (se 1 (by rfl) ⟨1214807, by rfl⟩ : syracuseStep 1619743 = 2429615) B2429615
theorem B2733887 : Blo 956588 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B1619959 : Blo 956588 1619959 := bstep (se 1 (by rfl) ⟨1214969, by rfl⟩ : syracuseStep 1619959 = 2429939) B2429939
theorem B4208723 : Blo 956588 4208723 := bstep (se 1 (by rfl) ⟨3156542, by rfl⟩ : syracuseStep 4208723 = 6313085) B6313085
theorem B2734343 : Blo 956588 2734343 := bstep (se 1 (by rfl) ⟨2050757, by rfl⟩ : syracuseStep 2734343 = 4101515) B4101515
theorem B1620263 : Blo 956588 1620263 := bstep (se 1 (by rfl) ⟨1215197, by rfl⟩ : syracuseStep 1620263 = 2430395) B2430395
theorem B34912721 : Blo 956588 34912721 := bstep (se 2 (by rfl) ⟨13092270, by rfl⟩ : syracuseStep 34912721 = 26184541) B26184541
theorem B1293799 : Blo 956588 1293799 := bstep (se 1 (by rfl) ⟨970349, by rfl⟩ : syracuseStep 1293799 = 1940699) B1940699
theorem B3686975 : Blo 956588 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B3228659 : Blo 956588 3228659 := bstep (se 1 (by rfl) ⟨2421494, by rfl⟩ : syracuseStep 3228659 = 4842989) B4842989
theorem B8177057 : Blo 956588 8177057 := bstep (se 2 (by rfl) ⟨3066396, by rfl⟩ : syracuseStep 8177057 = 6132793) B6132793
theorem B3458519 : Blo 956588 3458519 := bstep (se 1 (by rfl) ⟨2593889, by rfl⟩ : syracuseStep 3458519 = 5187779) B5187779
theorem B3229199 : Blo 956588 3229199 := bstep (se 1 (by rfl) ⟨2421899, by rfl⟩ : syracuseStep 3229199 = 4843799) B4843799
theorem B88688317 : Blo 956588 88688317 := bstep (se 3 (by rfl) ⟨16629059, by rfl⟩ : syracuseStep 88688317 = 33258119) B33258119
theorem B1820495 : Blo 956588 1820495 := bstep (se 1 (by rfl) ⟨1365371, by rfl⟩ : syracuseStep 1820495 = 2730743) B2730743
theorem B2050039 : Blo 956588 2050039 := bstep (se 1 (by rfl) ⟨1537529, by rfl⟩ : syracuseStep 2050039 = 3075059) B3075059
theorem B5261363 : Blo 956588 5261363 := bstep (se 1 (by rfl) ⟨3946022, by rfl⟩ : syracuseStep 5261363 = 7892045) B7892045
theorem B3230009 : Blo 956588 3230009 := bstep (se 2 (by rfl) ⟨1211253, by rfl⟩ : syracuseStep 3230009 = 2422507) B2422507
theorem B3230279 : Blo 956588 3230279 := bstep (se 1 (by rfl) ⟨2422709, by rfl⟩ : syracuseStep 3230279 = 4845419) B4845419
theorem B1559177 : Blo 956588 1559177 := bstep (se 2 (by rfl) ⟨584691, by rfl⟩ : syracuseStep 1559177 = 1169383) B1169383
theorem B3066551 : Blo 956588 3066551 := bstep (se 1 (by rfl) ⟨2299913, by rfl⟩ : syracuseStep 3066551 = 4599827) B4599827
theorem B22465511 : Blo 956588 22465511 := bstep (se 1 (by rfl) ⟨16849133, by rfl⟩ : syracuseStep 22465511 = 33698267) B33698267
theorem B12274811 : Blo 956588 12274811 := bstep (se 1 (by rfl) ⟨9206108, by rfl⟩ : syracuseStep 12274811 = 18412217) B18412217
theorem B4607401 : Blo 956588 4607401 := bstep (se 2 (by rfl) ⟨1727775, by rfl⟩ : syracuseStep 4607401 = 3455551) B3455551
theorem B3231305 : Blo 956588 3231305 := bstep (se 2 (by rfl) ⟨1211739, by rfl⟩ : syracuseStep 3231305 = 2423479) B2423479
theorem B3067769 : Blo 956588 3067769 := bstep (se 2 (by rfl) ⟨1150413, by rfl⟩ : syracuseStep 3067769 = 2300827) B2300827
theorem B51269699 : Blo 956588 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B2183561 : Blo 956588 2183561 := bstep (se 2 (by rfl) ⟨818835, by rfl⟩ : syracuseStep 2183561 = 1637671) B1637671
theorem B5820929 : Blo 956588 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B8180473 : Blo 956588 8180473 := bstep (se 2 (by rfl) ⟨3067677, by rfl⟩ : syracuseStep 8180473 = 6135355) B6135355
theorem B4379417 : Blo 956588 4379417 := bstep (se 2 (by rfl) ⟨1642281, by rfl⟩ : syracuseStep 4379417 = 3284563) B3284563
theorem B5460803 : Blo 956588 5460803 := bstep (se 1 (by rfl) ⟨4095602, by rfl⟩ : syracuseStep 5460803 = 8191205) B8191205
theorem B3232763 : Blo 956588 3232763 := bstep (se 1 (by rfl) ⟨2424572, by rfl⟩ : syracuseStep 3232763 = 4849145) B4849145
theorem B3232979 : Blo 956588 3232979 := bstep (se 1 (by rfl) ⟨2424734, by rfl⟩ : syracuseStep 3232979 = 4849469) B4849469
theorem B6903083 : Blo 956588 6903083 := bstep (se 1 (by rfl) ⟨5177312, by rfl⟩ : syracuseStep 6903083 = 10354625) B10354625
theorem B4609399 : Blo 956588 4609399 := bstep (se 1 (by rfl) ⟨3457049, by rfl⟩ : syracuseStep 4609399 = 6914099) B6914099
theorem B1725851 : Blo 956588 1725851 := bstep (se 1 (by rfl) ⟨1294388, by rfl⟩ : syracuseStep 1725851 = 2588777) B2588777
theorem B3233249 : Blo 956588 3233249 := bstep (se 2 (by rfl) ⟨1212468, by rfl⟩ : syracuseStep 3233249 = 2424937) B2424937
theorem B3069409 : Blo 956588 3069409 := bstep (se 2 (by rfl) ⟨1151028, by rfl⟩ : syracuseStep 3069409 = 2302057) B2302057
theorem B19650059 : Blo 956588 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B3692639 : Blo 956588 3692639 := bstep (se 1 (by rfl) ⟨2769479, by rfl⟩ : syracuseStep 3692639 = 5538959) B5538959
theorem B3233897 : Blo 956588 3233897 := bstep (se 2 (by rfl) ⟨1212711, by rfl⟩ : syracuseStep 3233897 = 2425423) B2425423
theorem B1726607 : Blo 956588 1726607 := bstep (se 1 (by rfl) ⟨1294955, by rfl⟩ : syracuseStep 1726607 = 2589911) B2589911
theorem B1366249 : Blo 956588 1366249 := bstep (se 2 (by rfl) ⟨512343, by rfl⟩ : syracuseStep 1366249 = 1024687) B1024687
theorem B2152745 : Blo 956588 2152745 := bstep (se 2 (by rfl) ⟨807279, by rfl⟩ : syracuseStep 2152745 = 1614559) B1614559
theorem B5462579 : Blo 956588 5462579 := bstep (se 1 (by rfl) ⟨4096934, by rfl⟩ : syracuseStep 5462579 = 8193869) B8193869
theorem B1727315 : Blo 956588 1727315 := bstep (se 1 (by rfl) ⟨1295486, by rfl⟩ : syracuseStep 1727315 = 2590973) B2590973
theorem B2153321 : Blo 956588 2153321 := bstep (se 2 (by rfl) ⟨807495, by rfl⟩ : syracuseStep 2153321 = 1614991) B1614991
theorem B5528429 : Blo 956588 5528429 := bstep (se 3 (by rfl) ⟨1036580, by rfl⟩ : syracuseStep 5528429 = 2073161) B2073161
theorem B2153375 : Blo 956588 2153375 := bstep (se 1 (by rfl) ⟨1615031, by rfl⟩ : syracuseStep 2153375 = 3230063) B3230063
theorem B3234761 : Blo 956588 3234761 := bstep (se 2 (by rfl) ⟨1213035, by rfl⟩ : syracuseStep 3234761 = 2426071) B2426071
theorem B3235031 : Blo 956588 3235031 := bstep (se 1 (by rfl) ⟨2426273, by rfl⟩ : syracuseStep 3235031 = 4852547) B4852547
theorem B6905249 : Blo 956588 6905249 := bstep (se 2 (by rfl) ⟨2589468, by rfl⟩ : syracuseStep 6905249 = 5178937) B5178937
theorem B3235571 : Blo 956588 3235571 := bstep (se 1 (by rfl) ⟨2426678, by rfl⟩ : syracuseStep 3235571 = 4853357) B4853357
theorem B2154311 : Blo 956588 2154311 := bstep (se 1 (by rfl) ⟨1615733, by rfl⟩ : syracuseStep 2154311 = 3231467) B3231467
theorem B5464037 : Blo 956588 5464037 := bstep (se 4 (by rfl) ⟨512253, by rfl⟩ : syracuseStep 5464037 = 1024507) B1024507
theorem B2187719 : Blo 956588 2187719 := bstep (se 1 (by rfl) ⟨1640789, by rfl⟩ : syracuseStep 2187719 = 3281579) B3281579
theorem B2154959 : Blo 956588 2154959 := bstep (se 1 (by rfl) ⟨1616219, by rfl⟩ : syracuseStep 2154959 = 3232439) B3232439
theorem B1729001 : Blo 956588 1729001 := bstep (se 2 (by rfl) ⟨648375, by rfl⟩ : syracuseStep 1729001 = 1296751) B1296751
theorem B4088393 : Blo 956588 4088393 := bstep (se 2 (by rfl) ⟨1533147, by rfl⟩ : syracuseStep 4088393 = 3066295) B3066295
theorem B5465177 : Blo 956588 5465177 := bstep (se 2 (by rfl) ⟨2049441, by rfl⟩ : syracuseStep 5465177 = 4098883) B4098883
theorem B2155625 : Blo 956588 2155625 := bstep (se 2 (by rfl) ⟨808359, by rfl⟩ : syracuseStep 2155625 = 1616719) B1616719
theorem B1434971 : Blo 956588 1434971 := bstep (se 1 (by rfl) ⟨1076228, by rfl⟩ : syracuseStep 1434971 = 2152457) B2152457
theorem B8316265 : Blo 956588 8316265 := bstep (se 2 (by rfl) ⟨3118599, by rfl⟩ : syracuseStep 8316265 = 6237199) B6237199
theorem B10937915 : Blo 956588 10937915 := bstep (se 1 (by rfl) ⟨8203436, by rfl⟩ : syracuseStep 10937915 = 16406873) B16406873
theorem B1730119 : Blo 956588 1730119 := bstep (se 1 (by rfl) ⟨1297589, by rfl⟩ : syracuseStep 1730119 = 2595179) B2595179
theorem B5826131 : Blo 956588 5826131 := bstep (se 1 (by rfl) ⟨4369598, by rfl⟩ : syracuseStep 5826131 = 8739197) B8739197
theorem B1435247 : Blo 956588 1435247 := bstep (se 1 (by rfl) ⟨1076435, by rfl⟩ : syracuseStep 1435247 = 2152871) B2152871
theorem B1435319 : Blo 956588 1435319 := bstep (se 1 (by rfl) ⟨1076489, by rfl⟩ : syracuseStep 1435319 = 2152979) B2152979
theorem B1435355 : Blo 956588 1435355 := bstep (se 1 (by rfl) ⟨1076516, by rfl⟩ : syracuseStep 1435355 = 2153033) B2153033
theorem B2156255 : Blo 956588 2156255 := bstep (se 1 (by rfl) ⟨1617191, by rfl⟩ : syracuseStep 2156255 = 3234383) B3234383
theorem B1435529 : Blo 956588 1435529 := bstep (se 2 (by rfl) ⟨538323, by rfl⟩ : syracuseStep 1435529 = 1076647) B1076647
theorem B1435631 : Blo 956588 1435631 := bstep (se 1 (by rfl) ⟨1076723, by rfl⟩ : syracuseStep 1435631 = 2153447) B2153447
theorem B1435883 : Blo 956588 1435883 := bstep (se 1 (by rfl) ⟨1076912, by rfl⟩ : syracuseStep 1435883 = 2153825) B2153825
theorem B1435943 : Blo 956588 1435943 := bstep (se 1 (by rfl) ⟨1076957, by rfl⟩ : syracuseStep 1435943 = 2153915) B2153915
theorem B1534249 : Blo 956588 1534249 := bstep (se 2 (by rfl) ⟨575343, by rfl⟩ : syracuseStep 1534249 = 1150687) B1150687
theorem B4090169 : Blo 956588 4090169 := bstep (se 2 (by rfl) ⟨1533813, by rfl⟩ : syracuseStep 4090169 = 3067627) B3067627
theorem B1436027 : Blo 956588 1436027 := bstep (se 1 (by rfl) ⟨1077020, by rfl⟩ : syracuseStep 1436027 = 2154041) B2154041
theorem B2157083 : Blo 956588 2157083 := bstep (se 1 (by rfl) ⟨1617812, by rfl⟩ : syracuseStep 2157083 = 3235625) B3235625
theorem B16345637 : Blo 956588 16345637 := bstep (se 4 (by rfl) ⟨1532403, by rfl⟩ : syracuseStep 16345637 = 3064807) B3064807
theorem B1436297 : Blo 956588 1436297 := bstep (se 2 (by rfl) ⟨538611, by rfl⟩ : syracuseStep 1436297 = 1077223) B1077223
theorem B1436471 : Blo 956588 1436471 := bstep (se 1 (by rfl) ⟨1077353, by rfl⟩ : syracuseStep 1436471 = 2154707) B2154707
theorem B1436507 : Blo 956588 1436507 := bstep (se 1 (by rfl) ⟨1077380, by rfl⟩ : syracuseStep 1436507 = 2154761) B2154761
theorem B1436651 : Blo 956588 1436651 := bstep (se 1 (by rfl) ⟨1077488, by rfl⟩ : syracuseStep 1436651 = 2154977) B2154977
theorem B4910215 : Blo 956588 4910215 := bstep (se 1 (by rfl) ⟨3682661, by rfl⟩ : syracuseStep 4910215 = 7365323) B7365323
theorem B1436855 : Blo 956588 1436855 := bstep (se 1 (by rfl) ⟨1077641, by rfl⟩ : syracuseStep 1436855 = 2155283) B2155283
theorem B3239135 : Blo 956588 3239135 := bstep (se 1 (by rfl) ⟨2429351, by rfl⟩ : syracuseStep 3239135 = 4858703) B4858703
theorem B1437095 : Blo 956588 1437095 := bstep (se 1 (by rfl) ⟨1077821, by rfl⟩ : syracuseStep 1437095 = 2155643) B2155643
theorem B3239351 : Blo 956588 3239351 := bstep (se 1 (by rfl) ⟨2429513, by rfl⟩ : syracuseStep 3239351 = 4859027) B4859027
theorem B1535479 : Blo 956588 1535479 := bstep (se 1 (by rfl) ⟨1151609, by rfl⟩ : syracuseStep 1535479 = 2303219) B2303219
theorem B1437179 : Blo 956588 1437179 := bstep (se 1 (by rfl) ⟨1077884, by rfl⟩ : syracuseStep 1437179 = 2155769) B2155769
theorem B1076827 : Blo 956588 1076827 := bstep (se 1 (by rfl) ⟨807620, by rfl⟩ : syracuseStep 1076827 = 1615241) B1615241
theorem B1437275 : Blo 956588 1437275 := bstep (se 1 (by rfl) ⟨1077956, by rfl⟩ : syracuseStep 1437275 = 2155913) B2155913
theorem B1437359 : Blo 956588 1437359 := bstep (se 1 (by rfl) ⟨1078019, by rfl⟩ : syracuseStep 1437359 = 2156039) B2156039
theorem B1437479 : Blo 956588 1437479 := bstep (se 1 (by rfl) ⟨1078109, by rfl⟩ : syracuseStep 1437479 = 2156219) B2156219
theorem B1077115 : Blo 956588 1077115 := bstep (se 1 (by rfl) ⟨807836, by rfl⟩ : syracuseStep 1077115 = 1615673) B1615673
theorem B1437563 : Blo 956588 1437563 := bstep (se 1 (by rfl) ⟨1078172, by rfl⟩ : syracuseStep 1437563 = 2156345) B2156345
theorem B2158559 : Blo 956588 2158559 := bstep (se 1 (by rfl) ⟨1618919, by rfl⟩ : syracuseStep 2158559 = 3237839) B3237839
theorem B3633275 : Blo 956588 3633275 := bstep (se 1 (by rfl) ⟨2724956, by rfl⟩ : syracuseStep 3633275 = 5449913) B5449913
theorem B1437983 : Blo 956588 1437983 := bstep (se 1 (by rfl) ⟨1078487, by rfl⟩ : syracuseStep 1437983 = 2156975) B2156975
theorem B1438007 : Blo 956588 1438007 := bstep (se 1 (by rfl) ⟨1078505, by rfl⟩ : syracuseStep 1438007 = 2157011) B2157011
theorem B1438079 : Blo 956588 1438079 := bstep (se 1 (by rfl) ⟨1078559, by rfl⟩ : syracuseStep 1438079 = 2157119) B2157119
theorem B1438151 : Blo 956588 1438151 := bstep (se 1 (by rfl) ⟨1078613, by rfl⟩ : syracuseStep 1438151 = 2157227) B2157227
theorem B5534201 : Blo 956588 5534201 := bstep (se 2 (by rfl) ⟨2075325, by rfl⟩ : syracuseStep 5534201 = 4150651) B4150651
theorem B1536607 : Blo 956588 1536607 := bstep (se 1 (by rfl) ⟨1152455, by rfl⟩ : syracuseStep 1536607 = 2304911) B2304911
theorem B2159207 : Blo 956588 2159207 := bstep (se 1 (by rfl) ⟨1619405, by rfl⟩ : syracuseStep 2159207 = 3238811) B3238811
theorem B29979395 : Blo 956588 29979395 := bstep (se 1 (by rfl) ⟨22484546, by rfl⟩ : syracuseStep 29979395 = 44969093) B44969093
theorem B1438505 : Blo 956588 1438505 := bstep (se 2 (by rfl) ⟨539439, by rfl⟩ : syracuseStep 1438505 = 1078879) B1078879
theorem B1438511 : Blo 956588 1438511 := bstep (se 1 (by rfl) ⟨1078883, by rfl⟩ : syracuseStep 1438511 = 2157767) B2157767
theorem B1438631 : Blo 956588 1438631 := bstep (se 1 (by rfl) ⟨1078973, by rfl⟩ : syracuseStep 1438631 = 2157947) B2157947
theorem B94565333 : Blo 956588 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B1078267 : Blo 956588 1078267 := bstep (se 1 (by rfl) ⟨808700, by rfl⟩ : syracuseStep 1078267 = 1617401) B1617401
theorem B1438715 : Blo 956588 1438715 := bstep (se 1 (by rfl) ⟨1079036, by rfl⟩ : syracuseStep 1438715 = 2158073) B2158073
theorem B1438775 : Blo 956588 1438775 := bstep (se 1 (by rfl) ⟨1079081, by rfl⟩ : syracuseStep 1438775 = 2158163) B2158163
theorem B2913455 : Blo 956588 2913455 := bstep (se 1 (by rfl) ⟨2185091, by rfl⟩ : syracuseStep 2913455 = 4370183) B4370183
theorem B1078447 : Blo 956588 1078447 := bstep (se 1 (by rfl) ⟨808835, by rfl⟩ : syracuseStep 1078447 = 1617671) B1617671
theorem B1438895 : Blo 956588 1438895 := bstep (se 1 (by rfl) ⟨1079171, by rfl⟩ : syracuseStep 1438895 = 2158343) B2158343
theorem B2421971 : Blo 956588 2421971 := bstep (se 1 (by rfl) ⟨1816478, by rfl⟩ : syracuseStep 2421971 = 3632957) B3632957
theorem B2159891 : Blo 956588 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B2159963 : Blo 956588 2159963 := bstep (se 1 (by rfl) ⟨1619972, by rfl⟩ : syracuseStep 2159963 = 3239945) B3239945
theorem B3241403 : Blo 956588 3241403 := bstep (se 1 (by rfl) ⟨2431052, by rfl⟩ : syracuseStep 3241403 = 4862105) B4862105
theorem B184612337 : Blo 956588 184612337 := bstep (se 2 (by rfl) ⟨69229626, by rfl⟩ : syracuseStep 184612337 = 138459253) B138459253
theorem B1439303 : Blo 956588 1439303 := bstep (se 1 (by rfl) ⟨1079477, by rfl⟩ : syracuseStep 1439303 = 2158955) B2158955
theorem B18904709 : Blo 956588 18904709 := bstep (se 4 (by rfl) ⟨1772316, by rfl⟩ : syracuseStep 18904709 = 3544633) B3544633
theorem B11826827 : Blo 956588 11826827 := bstep (se 1 (by rfl) ⟨8870120, by rfl⟩ : syracuseStep 11826827 = 17740241) B17740241
theorem B1078951 : Blo 956588 1078951 := bstep (se 1 (by rfl) ⟨809213, by rfl⟩ : syracuseStep 1078951 = 1618427) B1618427
theorem B1439399 : Blo 956588 1439399 := bstep (se 1 (by rfl) ⟨1079549, by rfl⟩ : syracuseStep 1439399 = 2159099) B2159099
theorem B1439483 : Blo 956588 1439483 := bstep (se 1 (by rfl) ⟨1079612, by rfl⟩ : syracuseStep 1439483 = 2159225) B2159225
theorem B1439519 : Blo 956588 1439519 := bstep (se 1 (by rfl) ⟨1079639, by rfl⟩ : syracuseStep 1439519 = 2159279) B2159279
theorem B1439567 : Blo 956588 1439567 := bstep (se 1 (by rfl) ⟨1079675, by rfl⟩ : syracuseStep 1439567 = 2159351) B2159351
theorem B2160521 : Blo 956588 2160521 := bstep (se 2 (by rfl) ⟨810195, by rfl⟩ : syracuseStep 2160521 = 1620391) B1620391
theorem B1079239 : Blo 956588 1079239 := bstep (se 1 (by rfl) ⟨809429, by rfl⟩ : syracuseStep 1079239 = 1618859) B1618859
theorem B1439687 : Blo 956588 1439687 := bstep (se 1 (by rfl) ⟨1079765, by rfl⟩ : syracuseStep 1439687 = 2159531) B2159531
theorem B3241943 : Blo 956588 3241943 := bstep (se 1 (by rfl) ⟨2431457, by rfl⟩ : syracuseStep 3241943 = 4862915) B4862915
theorem B6911963 : Blo 956588 6911963 := bstep (se 1 (by rfl) ⟨5183972, by rfl⟩ : syracuseStep 6911963 = 10367945) B10367945
theorem B2160737 : Blo 956588 2160737 := bstep (se 2 (by rfl) ⟨810276, by rfl⟩ : syracuseStep 2160737 = 1620553) B1620553
theorem B4847849 : Blo 956588 4847849 := bstep (se 2 (by rfl) ⟨1817943, by rfl⟩ : syracuseStep 4847849 = 3635887) B3635887
theorem B4094185 : Blo 956588 4094185 := bstep (se 2 (by rfl) ⟨1535319, by rfl⟩ : syracuseStep 4094185 = 3070639) B3070639
theorem B1440041 : Blo 956588 1440041 := bstep (se 2 (by rfl) ⟨540015, by rfl⟩ : syracuseStep 1440041 = 1080031) B1080031
theorem B1079599 : Blo 956588 1079599 := bstep (se 1 (by rfl) ⟨809699, by rfl⟩ : syracuseStep 1079599 = 1619399) B1619399
theorem B1440047 : Blo 956588 1440047 := bstep (se 1 (by rfl) ⟨1080035, by rfl⟩ : syracuseStep 1440047 = 2160071) B2160071
theorem B1440287 : Blo 956588 1440287 := bstep (se 1 (by rfl) ⟨1080215, by rfl⟩ : syracuseStep 1440287 = 2160431) B2160431
theorem B1440671 : Blo 956588 1440671 := bstep (se 1 (by rfl) ⟨1080503, by rfl⟩ : syracuseStep 1440671 = 2161007) B2161007
theorem B1440719 : Blo 956588 1440719 := bstep (se 1 (by rfl) ⟨1080539, by rfl⟩ : syracuseStep 1440719 = 2161079) B2161079
theorem B17497073 : Blo 956588 17497073 := bstep (se 2 (by rfl) ⟨6561402, by rfl⟩ : syracuseStep 17497073 = 13122805) B13122805
theorem B1440809 : Blo 956588 1440809 := bstep (se 2 (by rfl) ⟨540303, by rfl⟩ : syracuseStep 1440809 = 1080607) B1080607
theorem B1440815 : Blo 956588 1440815 := bstep (se 1 (by rfl) ⟨1080611, by rfl⟩ : syracuseStep 1440815 = 2161223) B2161223
theorem B1080391 : Blo 956588 1080391 := bstep (se 1 (by rfl) ⟨810293, by rfl⟩ : syracuseStep 1080391 = 1620587) B1620587
theorem B1440839 : Blo 956588 1440839 := bstep (se 1 (by rfl) ⟨1080629, by rfl⟩ : syracuseStep 1440839 = 2161259) B2161259
theorem B3636647 : Blo 956588 3636647 := bstep (se 1 (by rfl) ⟨2727485, by rfl⟩ : syracuseStep 3636647 = 5454971) B5454971
theorem B35454449 : Blo 956588 35454449 := bstep (se 2 (by rfl) ⟨13295418, by rfl⟩ : syracuseStep 35454449 = 26590837) B26590837
theorem B2424563 : Blo 956588 2424563 := bstep (se 1 (by rfl) ⟨1818422, by rfl⟩ : syracuseStep 2424563 = 3636845) B3636845
theorem B3637163 : Blo 956588 3637163 := bstep (se 1 (by rfl) ⟨2727872, by rfl⟩ : syracuseStep 3637163 = 5455745) B5455745
theorem B2457983 : Blo 956588 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B3507575 : Blo 956588 3507575 := bstep (se 1 (by rfl) ⟨2630681, by rfl⟩ : syracuseStep 3507575 = 5261363) B5261363
theorem B14977007 : Blo 956588 14977007 := bstep (se 1 (by rfl) ⟨11232755, by rfl⟩ : syracuseStep 14977007 = 22465511) B22465511
theorem B4851737 : Blo 956588 4851737 := bstep (se 2 (by rfl) ⟨1819401, by rfl⟩ : syracuseStep 4851737 = 3638803) B3638803
theorem B4851899 : Blo 956588 4851899 := bstep (se 1 (by rfl) ⟨3638924, by rfl⟩ : syracuseStep 4851899 = 7277849) B7277849
theorem B3639593 : Blo 956588 3639593 := bstep (se 2 (by rfl) ⟨1364847, by rfl⟩ : syracuseStep 3639593 = 2729695) B2729695
theorem B12290393 : Blo 956588 12290393 := bstep (se 2 (by rfl) ⟨4608897, by rfl⟩ : syracuseStep 12290393 = 9217795) B9217795
theorem B2919611 : Blo 956588 2919611 := bstep (se 1 (by rfl) ⟨2189708, by rfl⟩ : syracuseStep 2919611 = 4379417) B4379417
theorem B3640535 : Blo 956588 3640535 := bstep (se 1 (by rfl) ⟨2730401, by rfl⟩ : syracuseStep 3640535 = 5460803) B5460803
theorem B1150567 : Blo 956588 1150567 := bstep (se 1 (by rfl) ⟨862925, by rfl⟩ : syracuseStep 1150567 = 1725851) B1725851
theorem B2461759 : Blo 956588 2461759 := bstep (se 1 (by rfl) ⟨1846319, by rfl⟩ : syracuseStep 2461759 = 3692639) B3692639
theorem B2724137 : Blo 956588 2724137 := bstep (se 2 (by rfl) ⟨1021551, by rfl⟩ : syracuseStep 2724137 = 2043103) B2043103
theorem B3641719 : Blo 956588 3641719 := bstep (se 1 (by rfl) ⟨2731289, by rfl⟩ : syracuseStep 3641719 = 5462579) B5462579
theorem B1151543 : Blo 956588 1151543 := bstep (se 1 (by rfl) ⟨863657, by rfl⟩ : syracuseStep 1151543 = 1727315) B1727315
theorem B4854653 : Blo 956588 4854653 := bstep (se 3 (by rfl) ⟨910247, by rfl⟩ : syracuseStep 4854653 = 1820495) B1820495
theorem B3642691 : Blo 956588 3642691 := bstep (se 1 (by rfl) ⟨2732018, by rfl⟩ : syracuseStep 3642691 = 5464037) B5464037
theorem B1381871 : Blo 956588 1381871 := bstep (se 1 (by rfl) ⟨1036403, by rfl⟩ : syracuseStep 1381871 = 2072807) B2072807
theorem B1152667 : Blo 956588 1152667 := bstep (se 1 (by rfl) ⟨864500, by rfl⟩ : syracuseStep 1152667 = 1729001) B1729001
theorem B2725595 : Blo 956588 2725595 := bstep (se 1 (by rfl) ⟨2044196, by rfl⟩ : syracuseStep 2725595 = 4088393) B4088393
theorem B10360639 : Blo 956588 10360639 := bstep (se 1 (by rfl) ⟨7770479, by rfl⟩ : syracuseStep 10360639 = 15540959) B15540959
theorem B3643451 : Blo 956588 3643451 := bstep (se 1 (by rfl) ⟨2732588, by rfl⟩ : syracuseStep 3643451 = 5465177) B5465177
theorem B7280765 : Blo 956588 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B956647 : Blo 956588 956647 := bstep (se 1 (by rfl) ⟨717485, by rfl⟩ : syracuseStep 956647 = 1434971) B1434971
theorem B956831 : Blo 956588 956831 := bstep (se 1 (by rfl) ⟨717623, by rfl⟩ : syracuseStep 956831 = 1435247) B1435247
theorem B956879 : Blo 956588 956879 := bstep (se 1 (by rfl) ⟨717659, by rfl⟩ : syracuseStep 956879 = 1435319) B1435319
theorem B956903 : Blo 956588 956903 := bstep (se 1 (by rfl) ⟨717677, by rfl⟩ : syracuseStep 956903 = 1435355) B1435355
theorem B957019 : Blo 956588 957019 := bstep (se 1 (by rfl) ⟨717764, by rfl⟩ : syracuseStep 957019 = 1435529) B1435529
theorem B957087 : Blo 956588 957087 := bstep (se 1 (by rfl) ⟨717815, by rfl⟩ : syracuseStep 957087 = 1435631) B1435631
theorem B4922039 : Blo 956588 4922039 := bstep (se 1 (by rfl) ⟨3691529, by rfl⟩ : syracuseStep 4922039 = 7383059) B7383059
theorem B957255 : Blo 956588 957255 := bstep (se 1 (by rfl) ⟨717941, by rfl⟩ : syracuseStep 957255 = 1435883) B1435883
theorem B957295 : Blo 956588 957295 := bstep (se 1 (by rfl) ⟨717971, by rfl⟩ : syracuseStep 957295 = 1435943) B1435943
theorem B2726779 : Blo 956588 2726779 := bstep (se 1 (by rfl) ⟨2045084, by rfl⟩ : syracuseStep 2726779 = 4090169) B4090169
theorem B957351 : Blo 956588 957351 := bstep (se 1 (by rfl) ⟨718013, by rfl⟩ : syracuseStep 957351 = 1436027) B1436027
theorem B957531 : Blo 956588 957531 := bstep (se 1 (by rfl) ⟨718148, by rfl⟩ : syracuseStep 957531 = 1436297) B1436297
theorem B957647 : Blo 956588 957647 := bstep (se 1 (by rfl) ⟨718235, by rfl⟩ : syracuseStep 957647 = 1436471) B1436471
theorem B957671 : Blo 956588 957671 := bstep (se 1 (by rfl) ⟨718253, by rfl⟩ : syracuseStep 957671 = 1436507) B1436507
theorem B957767 : Blo 956588 957767 := bstep (se 1 (by rfl) ⟨718325, by rfl⟩ : syracuseStep 957767 = 1436651) B1436651
theorem B957903 : Blo 956588 957903 := bstep (se 1 (by rfl) ⟨718427, by rfl⟩ : syracuseStep 957903 = 1436855) B1436855
theorem B958063 : Blo 956588 958063 := bstep (se 1 (by rfl) ⟨718547, by rfl⟩ : syracuseStep 958063 = 1437095) B1437095
theorem B958119 : Blo 956588 958119 := bstep (se 1 (by rfl) ⟨718589, by rfl⟩ : syracuseStep 958119 = 1437179) B1437179
theorem B958183 : Blo 956588 958183 := bstep (se 1 (by rfl) ⟨718637, by rfl⟩ : syracuseStep 958183 = 1437275) B1437275
theorem B958239 : Blo 956588 958239 := bstep (se 1 (by rfl) ⟨718679, by rfl⟩ : syracuseStep 958239 = 1437359) B1437359
theorem B958319 : Blo 956588 958319 := bstep (se 1 (by rfl) ⟨718739, by rfl⟩ : syracuseStep 958319 = 1437479) B1437479
theorem B958375 : Blo 956588 958375 := bstep (se 1 (by rfl) ⟨718781, by rfl⟩ : syracuseStep 958375 = 1437563) B1437563
theorem B958655 : Blo 956588 958655 := bstep (se 1 (by rfl) ⟨718991, by rfl⟩ : syracuseStep 958655 = 1437983) B1437983
theorem B958671 : Blo 956588 958671 := bstep (se 1 (by rfl) ⟨719003, by rfl⟩ : syracuseStep 958671 = 1438007) B1438007
theorem B958719 : Blo 956588 958719 := bstep (se 1 (by rfl) ⟨719039, by rfl⟩ : syracuseStep 958719 = 1438079) B1438079
theorem B958767 : Blo 956588 958767 := bstep (se 1 (by rfl) ⟨719075, by rfl⟩ : syracuseStep 958767 = 1438151) B1438151
theorem B4792643 : Blo 956588 4792643 := bstep (se 1 (by rfl) ⟨3594482, by rfl⟩ : syracuseStep 4792643 = 7188965) B7188965
theorem B959003 : Blo 956588 959003 := bstep (se 1 (by rfl) ⟨719252, by rfl⟩ : syracuseStep 959003 = 1438505) B1438505
theorem B959007 : Blo 956588 959007 := bstep (se 1 (by rfl) ⟨719255, by rfl⟩ : syracuseStep 959007 = 1438511) B1438511
theorem B959087 : Blo 956588 959087 := bstep (se 1 (by rfl) ⟨719315, by rfl⟩ : syracuseStep 959087 = 1438631) B1438631
theorem B959143 : Blo 956588 959143 := bstep (se 1 (by rfl) ⟨719357, by rfl⟩ : syracuseStep 959143 = 1438715) B1438715
theorem B959183 : Blo 956588 959183 := bstep (se 1 (by rfl) ⟨719387, by rfl⟩ : syracuseStep 959183 = 1438775) B1438775
theorem B5448455 : Blo 956588 5448455 := bstep (se 1 (by rfl) ⟨4086341, by rfl⟩ : syracuseStep 5448455 = 8172683) B8172683
theorem B1942303 : Blo 956588 1942303 := bstep (se 1 (by rfl) ⟨1456727, by rfl⟩ : syracuseStep 1942303 = 2913455) B2913455
theorem B959263 : Blo 956588 959263 := bstep (se 1 (by rfl) ⟨719447, by rfl⟩ : syracuseStep 959263 = 1438895) B1438895
theorem B1614647 : Blo 956588 1614647 := bstep (se 1 (by rfl) ⟨1210985, by rfl⟩ : syracuseStep 1614647 = 2421971) B2421971
theorem B2728829 : Blo 956588 2728829 := bstep (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) B1023311
theorem B959535 : Blo 956588 959535 := bstep (se 1 (by rfl) ⟨719651, by rfl⟩ : syracuseStep 959535 = 1439303) B1439303
theorem B959599 : Blo 956588 959599 := bstep (se 1 (by rfl) ⟨719699, by rfl⟩ : syracuseStep 959599 = 1439399) B1439399
theorem B959655 : Blo 956588 959655 := bstep (se 1 (by rfl) ⟨719741, by rfl⟩ : syracuseStep 959655 = 1439483) B1439483
theorem B959679 : Blo 956588 959679 := bstep (se 1 (by rfl) ⟨719759, by rfl⟩ : syracuseStep 959679 = 1439519) B1439519
theorem B959711 : Blo 956588 959711 := bstep (se 1 (by rfl) ⟨719783, by rfl⟩ : syracuseStep 959711 = 1439567) B1439567
theorem B959791 : Blo 956588 959791 := bstep (se 1 (by rfl) ⟨719843, by rfl⟩ : syracuseStep 959791 = 1439687) B1439687
theorem B960027 : Blo 956588 960027 := bstep (se 1 (by rfl) ⟨720020, by rfl⟩ : syracuseStep 960027 = 1440041) B1440041
theorem B960031 : Blo 956588 960031 := bstep (se 1 (by rfl) ⟨720023, by rfl⟩ : syracuseStep 960031 = 1440047) B1440047
theorem B23275147 : Blo 956588 23275147 := bstep (se 1 (by rfl) ⟨17456360, by rfl⟩ : syracuseStep 23275147 = 34912721) B34912721
theorem B960191 : Blo 956588 960191 := bstep (se 1 (by rfl) ⟨720143, by rfl⟩ : syracuseStep 960191 = 1440287) B1440287
theorem B960447 : Blo 956588 960447 := bstep (se 1 (by rfl) ⟨720335, by rfl⟩ : syracuseStep 960447 = 1440671) B1440671
theorem B960479 : Blo 956588 960479 := bstep (se 1 (by rfl) ⟨720359, by rfl⟩ : syracuseStep 960479 = 1440719) B1440719
theorem B960539 : Blo 956588 960539 := bstep (se 1 (by rfl) ⟨720404, by rfl⟩ : syracuseStep 960539 = 1440809) B1440809
theorem B960543 : Blo 956588 960543 := bstep (se 1 (by rfl) ⟨720407, by rfl⟩ : syracuseStep 960543 = 1440815) B1440815
theorem B960559 : Blo 956588 960559 := bstep (se 1 (by rfl) ⟨720419, by rfl⟩ : syracuseStep 960559 = 1440839) B1440839
theorem B23636299 : Blo 956588 23636299 := bstep (se 1 (by rfl) ⟨17727224, by rfl⟩ : syracuseStep 23636299 = 35454449) B35454449
theorem B1616375 : Blo 956588 1616375 := bstep (se 1 (by rfl) ⟨1212281, by rfl⟩ : syracuseStep 1616375 = 2424563) B2424563
theorem B136719197 : Blo 956588 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B1616969 : Blo 956588 1616969 := bstep (se 2 (by rfl) ⟨606363, by rfl⟩ : syracuseStep 1616969 = 1212727) B1212727
theorem B5451371 : Blo 956588 5451371 := bstep (se 1 (by rfl) ⟨4088528, by rfl⟩ : syracuseStep 5451371 = 8177057) B8177057
theorem B2305679 : Blo 956588 2305679 := bstep (se 1 (by rfl) ⟨1729259, by rfl⟩ : syracuseStep 2305679 = 3458519) B3458519
theorem B7876261 : Blo 956588 7876261 := bstep (se 4 (by rfl) ⟨738399, by rfl⟩ : syracuseStep 7876261 = 1476799) B1476799
theorem B8761243 : Blo 956588 8761243 := bstep (se 1 (by rfl) ⟨6570932, by rfl⟩ : syracuseStep 8761243 = 13141865) B13141865
theorem B14757869 : Blo 956588 14757869 := bstep (se 3 (by rfl) ⟨2767100, by rfl⟩ : syracuseStep 14757869 = 5534201) B5534201
theorem B2044367 : Blo 956588 2044367 := bstep (se 1 (by rfl) ⟨1533275, by rfl⟩ : syracuseStep 2044367 = 3066551) B3066551
theorem B11088353 : Blo 956588 11088353 := bstep (se 2 (by rfl) ⟨4158132, by rfl⟩ : syracuseStep 11088353 = 8316265) B8316265
theorem B2306825 : Blo 956588 2306825 := bstep (se 2 (by rfl) ⟨865059, by rfl⟩ : syracuseStep 2306825 = 1730119) B1730119
theorem B4371241 : Blo 956588 4371241 := bstep (se 2 (by rfl) ⟨1639215, by rfl⟩ : syracuseStep 4371241 = 3278431) B3278431
theorem B1618751 : Blo 956588 1618751 := bstep (se 1 (by rfl) ⟨1214063, by rfl⟩ : syracuseStep 1618751 = 2428127) B2428127
theorem B1618825 : Blo 956588 1618825 := bstep (se 2 (by rfl) ⟨607059, by rfl⟩ : syracuseStep 1618825 = 1214119) B1214119
theorem B2733011 : Blo 956588 2733011 := bstep (se 1 (by rfl) ⟨2049758, by rfl⟩ : syracuseStep 2733011 = 4099517) B4099517
theorem B2045179 : Blo 956588 2045179 := bstep (se 1 (by rfl) ⟨1533884, by rfl⟩ : syracuseStep 2045179 = 3067769) B3067769
theorem B1455707 : Blo 956588 1455707 := bstep (se 1 (by rfl) ⟨1091780, by rfl⟩ : syracuseStep 1455707 = 2183561) B2183561
theorem B1816175 : Blo 956588 1816175 := bstep (se 1 (by rfl) ⟨1362131, by rfl⟩ : syracuseStep 1816175 = 2724263) B2724263
theorem B3880619 : Blo 956588 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B2045665 : Blo 956588 2045665 := bstep (se 2 (by rfl) ⟨767124, by rfl⟩ : syracuseStep 2045665 = 1534249) B1534249
theorem B1619689 : Blo 956588 1619689 := bstep (se 2 (by rfl) ⟨607383, by rfl⟩ : syracuseStep 1619689 = 1214767) B1214767
theorem B19642175 : Blo 956588 19642175 := bstep (se 1 (by rfl) ⟨14731631, by rfl⟩ : syracuseStep 19642175 = 29463263) B29463263
theorem B1816759 : Blo 956588 1816759 := bstep (se 1 (by rfl) ⟨1362569, by rfl⟩ : syracuseStep 1816759 = 2725139) B2725139
theorem B1620715 : Blo 956588 1620715 := bstep (se 1 (by rfl) ⟨1215536, by rfl⟩ : syracuseStep 1620715 = 2431073) B2431073
theorem B139901843 : Blo 956588 139901843 := bstep (se 1 (by rfl) ⟨104926382, by rfl⟩ : syracuseStep 139901843 = 209852765) B209852765
theorem B50412557 : Blo 956588 50412557 := bstep (se 3 (by rfl) ⟨9452354, by rfl⟩ : syracuseStep 50412557 = 18904709) B18904709
theorem B6143201 : Blo 956588 6143201 := bstep (se 2 (by rfl) ⟨2303700, by rfl⟩ : syracuseStep 6143201 = 4607401) B4607401
theorem B3685619 : Blo 956588 3685619 := bstep (se 1 (by rfl) ⟨2764214, by rfl⟩ : syracuseStep 3685619 = 5528429) B5528429
theorem B4373833 : Blo 956588 4373833 := bstep (se 2 (by rfl) ⟨1640187, by rfl⟩ : syracuseStep 4373833 = 3280375) B3280375
theorem B4603499 : Blo 956588 4603499 := bstep (se 1 (by rfl) ⟨3452624, by rfl⟩ : syracuseStep 4603499 = 6905249) B6905249
theorem B1458479 : Blo 956588 1458479 := bstep (se 1 (by rfl) ⟨1093859, by rfl⟩ : syracuseStep 1458479 = 2187719) B2187719
theorem B4604285 : Blo 956588 4604285 := bstep (se 3 (by rfl) ⟨863303, by rfl⟩ : syracuseStep 4604285 = 1726607) B1726607
theorem B1819007 : Blo 956588 1819007 := bstep (se 1 (by rfl) ⟨1364255, by rfl⟩ : syracuseStep 1819007 = 2728511) B2728511
theorem B2048809 : Blo 956588 2048809 := bstep (se 2 (by rfl) ⟨768303, by rfl⟩ : syracuseStep 2048809 = 1536607) B1536607
theorem B3458057 : Blo 956588 3458057 := bstep (se 2 (by rfl) ⟨1296771, by rfl⟩ : syracuseStep 3458057 = 2593543) B2593543
theorem B7291943 : Blo 956588 7291943 := bstep (se 1 (by rfl) ⟨5468957, by rfl⟩ : syracuseStep 7291943 = 10937915) B10937915
theorem B3884087 : Blo 956588 3884087 := bstep (se 1 (by rfl) ⟨2913065, by rfl⟩ : syracuseStep 3884087 = 5826131) B5826131
theorem B1819759 : Blo 956588 1819759 := bstep (se 1 (by rfl) ⟨1364819, by rfl⟩ : syracuseStep 1819759 = 2729639) B2729639
theorem B10897091 : Blo 956588 10897091 := bstep (se 1 (by rfl) ⟨8172818, by rfl⟩ : syracuseStep 10897091 = 16345637) B16345637
theorem B6145865 : Blo 956588 6145865 := bstep (se 2 (by rfl) ⟨2304699, by rfl⟩ : syracuseStep 6145865 = 4609399) B4609399
theorem B1820647 : Blo 956588 1820647 := bstep (se 1 (by rfl) ⟨1365485, by rfl⟩ : syracuseStep 1820647 = 2730971) B2730971
theorem B1558715 : Blo 956588 1558715 := bstep (se 1 (by rfl) ⟨1169036, by rfl⟩ : syracuseStep 1558715 = 2338073) B2338073
theorem B5458913 : Blo 956588 5458913 := bstep (se 2 (by rfl) ⟨2047092, by rfl⟩ : syracuseStep 5458913 = 4094185) B4094185
theorem B1821665 : Blo 956588 1821665 := bstep (se 2 (by rfl) ⟨683124, by rfl⟩ : syracuseStep 1821665 = 1366249) B1366249
theorem B62311457 : Blo 956588 62311457 := bstep (se 2 (by rfl) ⟨23366796, by rfl⟩ : syracuseStep 62311457 = 46733593) B46733593
theorem B6147247 : Blo 956588 6147247 := bstep (se 1 (by rfl) ⟨4610435, by rfl⟩ : syracuseStep 6147247 = 9220871) B9220871
theorem B1363321 : Blo 956588 1363321 := bstep (se 2 (by rfl) ⟨511245, by rfl⟩ : syracuseStep 1363321 = 1022491) B1022491
theorem B7884551 : Blo 956588 7884551 := bstep (se 1 (by rfl) ⟨5913413, by rfl⟩ : syracuseStep 7884551 = 11826827) B11826827
theorem B6147863 : Blo 956588 6147863 := bstep (se 1 (by rfl) ⟨4610897, by rfl⟩ : syracuseStep 6147863 = 9221795) B9221795
theorem B1822591 : Blo 956588 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B4607975 : Blo 956588 4607975 := bstep (se 1 (by rfl) ⟨3455981, by rfl⟩ : syracuseStep 4607975 = 6911963) B6911963
theorem B2805815 : Blo 956588 2805815 := bstep (se 1 (by rfl) ⟨2104361, by rfl⟩ : syracuseStep 2805815 = 4208723) B4208723
theorem B3231899 : Blo 956588 3231899 := bstep (se 1 (by rfl) ⟨2423924, by rfl⟩ : syracuseStep 3231899 = 4847849) B4847849
theorem B1822895 : Blo 956588 1822895 := bstep (se 1 (by rfl) ⟨1367171, by rfl⟩ : syracuseStep 1822895 = 2734343) B2734343
theorem B1725065 : Blo 956588 1725065 := bstep (se 2 (by rfl) ⟨646899, by rfl⟩ : syracuseStep 1725065 = 1293799) B1293799
theorem B10933541 : Blo 956588 10933541 := bstep (se 4 (by rfl) ⟨1025019, by rfl⟩ : syracuseStep 10933541 = 2050039) B2050039
theorem B16602457 : Blo 956588 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B104814283 : Blo 956588 104814283 := bstep (se 1 (by rfl) ⟨78610712, by rfl⟩ : syracuseStep 104814283 = 157221425) B157221425
theorem B3233627 : Blo 956588 3233627 := bstep (se 1 (by rfl) ⟨2425220, by rfl⟩ : syracuseStep 3233627 = 4850441) B4850441
theorem B2152439 : Blo 956588 2152439 := bstep (se 1 (by rfl) ⟨1614329, by rfl⟩ : syracuseStep 2152439 = 3228659) B3228659
theorem B2152799 : Blo 956588 2152799 := bstep (se 1 (by rfl) ⟨1614599, by rfl⟩ : syracuseStep 2152799 = 3229199) B3229199
theorem B4151711 : Blo 956588 4151711 := bstep (se 1 (by rfl) ⟨3113783, by rfl⟩ : syracuseStep 4151711 = 6227567) B6227567
theorem B2186041 : Blo 956588 2186041 := bstep (se 2 (by rfl) ⟨819765, by rfl⟩ : syracuseStep 2186041 = 1639531) B1639531
theorem B2153339 : Blo 956588 2153339 := bstep (se 1 (by rfl) ⟨1615004, by rfl⟩ : syracuseStep 2153339 = 3230009) B3230009
theorem B7265213 : Blo 956588 7265213 := bstep (se 3 (by rfl) ⟨1362227, by rfl⟩ : syracuseStep 7265213 = 2724455) B2724455
theorem B2153519 : Blo 956588 2153519 := bstep (se 1 (by rfl) ⟨1615139, by rfl⟩ : syracuseStep 2153519 = 3230279) B3230279
theorem B1039451 : Blo 956588 1039451 := bstep (se 1 (by rfl) ⟨779588, by rfl⟩ : syracuseStep 1039451 = 1559177) B1559177
theorem B10902923 : Blo 956588 10902923 := bstep (se 1 (by rfl) ⟨8177192, by rfl⟩ : syracuseStep 10902923 = 16354385) B16354385
theorem B8183207 : Blo 956588 8183207 := bstep (se 1 (by rfl) ⟨6137405, by rfl⟩ : syracuseStep 8183207 = 12274811) B12274811
theorem B118251089 : Blo 956588 118251089 := bstep (se 2 (by rfl) ⟨44344158, by rfl⟩ : syracuseStep 118251089 = 88688317) B88688317
theorem B5463719 : Blo 956588 5463719 := bstep (se 1 (by rfl) ⟨4097789, by rfl⟩ : syracuseStep 5463719 = 8195579) B8195579
theorem B2154203 : Blo 956588 2154203 := bstep (se 1 (by rfl) ⟨1615652, by rfl⟩ : syracuseStep 2154203 = 3231305) B3231305
theorem B252174221 : Blo 956588 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B2154473 : Blo 956588 2154473 := bstep (se 2 (by rfl) ⟨807927, by rfl⟩ : syracuseStep 2154473 = 1615855) B1615855
theorem B266002829 : Blo 956588 266002829 := bstep (se 3 (by rfl) ⟨49875530, by rfl⟩ : syracuseStep 266002829 = 99751061) B99751061
theorem B2155175 : Blo 956588 2155175 := bstep (se 1 (by rfl) ⟨1616381, by rfl⟩ : syracuseStep 2155175 = 3232763) B3232763
theorem B4088495 : Blo 956588 4088495 := bstep (se 1 (by rfl) ⟨3066371, by rfl⟩ : syracuseStep 4088495 = 6132743) B6132743
theorem B18408221 : Blo 956588 18408221 := bstep (se 3 (by rfl) ⟨3451541, by rfl⟩ : syracuseStep 18408221 = 6903083) B6903083
theorem B2155319 : Blo 956588 2155319 := bstep (se 1 (by rfl) ⟨1616489, by rfl⟩ : syracuseStep 2155319 = 3232979) B3232979
theorem B4613051 : Blo 956588 4613051 := bstep (se 1 (by rfl) ⟨3459788, by rfl⟩ : syracuseStep 4613051 = 6919577) B6919577
theorem B2155499 : Blo 956588 2155499 := bstep (se 1 (by rfl) ⟨1616624, by rfl⟩ : syracuseStep 2155499 = 3233249) B3233249
theorem B13100039 : Blo 956588 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B2155931 : Blo 956588 2155931 := bstep (se 1 (by rfl) ⟨1616948, by rfl⟩ : syracuseStep 2155931 = 3233897) B3233897
theorem B6546953 : Blo 956588 6546953 := bstep (se 2 (by rfl) ⟨2455107, by rfl⟩ : syracuseStep 6546953 = 4910215) B4910215
theorem B1435163 : Blo 956588 1435163 := bstep (se 1 (by rfl) ⟨1076372, by rfl⟩ : syracuseStep 1435163 = 2152745) B2152745
theorem B1435547 : Blo 956588 1435547 := bstep (se 1 (by rfl) ⟨1076660, by rfl⟩ : syracuseStep 1435547 = 2153321) B2153321
theorem B1435583 : Blo 956588 1435583 := bstep (se 1 (by rfl) ⟨1076687, by rfl⟩ : syracuseStep 1435583 = 2153375) B2153375
theorem B2156507 : Blo 956588 2156507 := bstep (se 1 (by rfl) ⟨1617380, by rfl⟩ : syracuseStep 2156507 = 3234761) B3234761
theorem B1435769 : Blo 956588 1435769 := bstep (se 2 (by rfl) ⟨538413, by rfl⟩ : syracuseStep 1435769 = 1076827) B1076827
theorem B2156687 : Blo 956588 2156687 := bstep (se 1 (by rfl) ⟨1617515, by rfl⟩ : syracuseStep 2156687 = 3235031) B3235031
theorem B2156777 : Blo 956588 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B2157047 : Blo 956588 2157047 := bstep (se 1 (by rfl) ⟨1617785, by rfl⟩ : syracuseStep 2157047 = 3235571) B3235571
theorem B1436153 : Blo 956588 1436153 := bstep (se 2 (by rfl) ⟨538557, by rfl⟩ : syracuseStep 1436153 = 1077115) B1077115
theorem B1436207 : Blo 956588 1436207 := bstep (se 1 (by rfl) ⟨1077155, by rfl⟩ : syracuseStep 1436207 = 2154311) B2154311
theorem B7269101 : Blo 956588 7269101 := bstep (se 3 (by rfl) ⟨1362956, by rfl⟩ : syracuseStep 7269101 = 2725913) B2725913
theorem B1436639 : Blo 956588 1436639 := bstep (se 1 (by rfl) ⟨1077479, by rfl⟩ : syracuseStep 1436639 = 2154959) B2154959
theorem B1076287 : Blo 956588 1076287 := bstep (se 1 (by rfl) ⟨807215, by rfl⟩ : syracuseStep 1076287 = 1614431) B1614431
theorem B2157641 : Blo 956588 2157641 := bstep (se 2 (by rfl) ⟨809115, by rfl⟩ : syracuseStep 2157641 = 1618231) B1618231
theorem B3239081 : Blo 956588 3239081 := bstep (se 2 (by rfl) ⟨1214655, by rfl⟩ : syracuseStep 3239081 = 2429311) B2429311
theorem B3894455 : Blo 956588 3894455 := bstep (se 1 (by rfl) ⟨2920841, by rfl⟩ : syracuseStep 3894455 = 5841683) B5841683
theorem B1437083 : Blo 956588 1437083 := bstep (se 1 (by rfl) ⟨1077812, by rfl⟩ : syracuseStep 1437083 = 2155625) B2155625
theorem B10907297 : Blo 956588 10907297 := bstep (se 2 (by rfl) ⟨4090236, by rfl⟩ : syracuseStep 10907297 = 8180473) B8180473
theorem B3239675 : Blo 956588 3239675 := bstep (se 1 (by rfl) ⟨2429756, by rfl⟩ : syracuseStep 3239675 = 4859513) B4859513
theorem B1437503 : Blo 956588 1437503 := bstep (se 1 (by rfl) ⟨1078127, by rfl⟩ : syracuseStep 1437503 = 2156255) B2156255
theorem B1437689 : Blo 956588 1437689 := bstep (se 2 (by rfl) ⟨539133, by rfl⟩ : syracuseStep 1437689 = 1078267) B1078267
theorem B1077403 : Blo 956588 1077403 := bstep (se 1 (by rfl) ⟨808052, by rfl⟩ : syracuseStep 1077403 = 1616105) B1616105
theorem B1437929 : Blo 956588 1437929 := bstep (se 2 (by rfl) ⟨539223, by rfl⟩ : syracuseStep 1437929 = 1078447) B1078447
theorem B1438055 : Blo 956588 1438055 := bstep (se 1 (by rfl) ⟨1078541, by rfl⟩ : syracuseStep 1438055 = 2157083) B2157083
theorem B9204263 : Blo 956588 9204263 := bstep (se 1 (by rfl) ⟨6903197, by rfl⟩ : syracuseStep 9204263 = 13806395) B13806395
theorem B4092545 : Blo 956588 4092545 := bstep (se 2 (by rfl) ⟨1534704, by rfl⟩ : syracuseStep 4092545 = 3069409) B3069409
theorem B35877599 : Blo 956588 35877599 := bstep (se 1 (by rfl) ⟨26908199, by rfl⟩ : syracuseStep 35877599 = 53816399) B53816399
theorem B2159369 : Blo 956588 2159369 := bstep (se 2 (by rfl) ⟨809763, by rfl⟩ : syracuseStep 2159369 = 1619527) B1619527
theorem B3633929 : Blo 956588 3633929 := bstep (se 2 (by rfl) ⟨1362723, by rfl⟩ : syracuseStep 3633929 = 2725447) B2725447
theorem B2159423 : Blo 956588 2159423 := bstep (se 1 (by rfl) ⟨1619567, by rfl⟩ : syracuseStep 2159423 = 3239135) B3239135
theorem B1438601 : Blo 956588 1438601 := bstep (se 2 (by rfl) ⟨539475, by rfl⟩ : syracuseStep 1438601 = 1078951) B1078951
theorem B2159567 : Blo 956588 2159567 := bstep (se 1 (by rfl) ⟨1619675, by rfl⟩ : syracuseStep 2159567 = 3239351) B3239351
theorem B2159657 : Blo 956588 2159657 := bstep (se 2 (by rfl) ⟨809871, by rfl⟩ : syracuseStep 2159657 = 1619743) B1619743
theorem B16807085 : Blo 956588 16807085 := bstep (se 3 (by rfl) ⟨3151328, by rfl⟩ : syracuseStep 16807085 = 6302657) B6302657
theorem B1438985 : Blo 956588 1438985 := bstep (se 2 (by rfl) ⟨539619, by rfl⟩ : syracuseStep 1438985 = 1079239) B1079239
theorem B8189221 : Blo 956588 8189221 := bstep (se 4 (by rfl) ⟨767739, by rfl⟩ : syracuseStep 8189221 = 1535479) B1535479
theorem B46658861 : Blo 956588 46658861 := bstep (se 3 (by rfl) ⟨8748536, by rfl⟩ : syracuseStep 46658861 = 17497073) B17497073
theorem B1078591 : Blo 956588 1078591 := bstep (se 1 (by rfl) ⟨808943, by rfl⟩ : syracuseStep 1078591 = 1617887) B1617887
theorem B1439039 : Blo 956588 1439039 := bstep (se 1 (by rfl) ⟨1079279, by rfl⟩ : syracuseStep 1439039 = 2158559) B2158559
theorem B2159945 : Blo 956588 2159945 := bstep (se 2 (by rfl) ⟨809979, by rfl⟩ : syracuseStep 2159945 = 1619959) B1619959
theorem B2422183 : Blo 956588 2422183 := bstep (se 1 (by rfl) ⟨1816637, by rfl⟩ : syracuseStep 2422183 = 3633275) B3633275
theorem B1439465 : Blo 956588 1439465 := bstep (se 2 (by rfl) ⟨539799, by rfl⟩ : syracuseStep 1439465 = 1079599) B1079599
theorem B1079023 : Blo 956588 1079023 := bstep (se 1 (by rfl) ⟨809267, by rfl⟩ : syracuseStep 1079023 = 1618535) B1618535
theorem B1439471 : Blo 956588 1439471 := bstep (se 1 (by rfl) ⟨1079603, by rfl⟩ : syracuseStep 1439471 = 2159207) B2159207
theorem B2914127 : Blo 956588 2914127 := bstep (se 1 (by rfl) ⟨2185595, by rfl⟩ : syracuseStep 2914127 = 4371191) B4371191
theorem B19986263 : Blo 956588 19986263 := bstep (se 1 (by rfl) ⟨14989697, by rfl⟩ : syracuseStep 19986263 = 29979395) B29979395
theorem B1079131 : Blo 956588 1079131 := bstep (se 1 (by rfl) ⟨809348, by rfl⟩ : syracuseStep 1079131 = 1618697) B1618697
theorem B1538119 : Blo 956588 1538119 := bstep (se 1 (by rfl) ⟨1153589, by rfl⟩ : syracuseStep 1538119 = 2307179) B2307179
theorem B1439927 : Blo 956588 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B1079527 : Blo 956588 1079527 := bstep (se 1 (by rfl) ⟨809645, by rfl⟩ : syracuseStep 1079527 = 1619291) B1619291
theorem B1439975 : Blo 956588 1439975 := bstep (se 1 (by rfl) ⟨1079981, by rfl⟩ : syracuseStep 1439975 = 2159963) B2159963
theorem B2160935 : Blo 956588 2160935 := bstep (se 1 (by rfl) ⟨1620701, by rfl⟩ : syracuseStep 2160935 = 3241403) B3241403
theorem B123074891 : Blo 956588 123074891 := bstep (se 1 (by rfl) ⟨92306168, by rfl⟩ : syracuseStep 123074891 = 184612337) B184612337
theorem B1440347 : Blo 956588 1440347 := bstep (se 1 (by rfl) ⟨1080260, by rfl⟩ : syracuseStep 1440347 = 2160521) B2160521
theorem B2161295 : Blo 956588 2161295 := bstep (se 1 (by rfl) ⟨1620971, by rfl⟩ : syracuseStep 2161295 = 3241943) B3241943
theorem B1440491 : Blo 956588 1440491 := bstep (se 1 (by rfl) ⟨1080368, by rfl⟩ : syracuseStep 1440491 = 2160737) B2160737
theorem B1440521 : Blo 956588 1440521 := bstep (se 2 (by rfl) ⟨540195, by rfl⟩ : syracuseStep 1440521 = 1080391) B1080391
theorem B1080175 : Blo 956588 1080175 := bstep (se 1 (by rfl) ⟨810131, by rfl⟩ : syracuseStep 1080175 = 1620263) B1620263
theorem B2424431 : Blo 956588 2424431 := bstep (se 1 (by rfl) ⟨1818323, by rfl⟩ : syracuseStep 2424431 = 3636647) B3636647
theorem B31489829 : Blo 956588 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B2424775 : Blo 956588 2424775 := bstep (se 1 (by rfl) ⟨1818581, by rfl⟩ : syracuseStep 2424775 = 3637163) B3637163
theorem B1212671 : Blo 956588 1212671 := bstep (se 1 (by rfl) ⟨909503, by rfl⟩ : syracuseStep 1212671 = 1819007) B1819007
theorem B2589391 : Blo 956588 2589391 := bstep (se 1 (by rfl) ⟨1942043, by rfl⟩ : syracuseStep 2589391 = 3884087) B3884087
theorem B6554621 : Blo 956588 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B2589737 : Blo 956588 2589737 := bstep (se 2 (by rfl) ⟨971151, by rfl⟩ : syracuseStep 2589737 = 1942303) B1942303
theorem B4097243 : Blo 956588 4097243 := bstep (se 1 (by rfl) ⟨3072932, by rfl⟩ : syracuseStep 4097243 = 6145865) B6145865
theorem B2426345 : Blo 956588 2426345 := bstep (se 2 (by rfl) ⟨909879, by rfl⟩ : syracuseStep 2426345 = 1819759) B1819759
theorem B2426395 : Blo 956588 2426395 := bstep (se 1 (by rfl) ⟨1819796, by rfl⟩ : syracuseStep 2426395 = 3639593) B3639593
theorem B8193595 : Blo 956588 8193595 := bstep (se 1 (by rfl) ⟨6145196, by rfl⟩ : syracuseStep 8193595 = 12290393) B12290393
theorem B3639275 : Blo 956588 3639275 := bstep (se 1 (by rfl) ⟨2729456, by rfl⟩ : syracuseStep 3639275 = 5458913) B5458913
theorem B1214443 : Blo 956588 1214443 := bstep (se 1 (by rfl) ⟨910832, by rfl⟩ : syracuseStep 1214443 = 1821665) B1821665
theorem B2427023 : Blo 956588 2427023 := bstep (se 1 (by rfl) ⟨1820267, by rfl⟩ : syracuseStep 2427023 = 3640535) B3640535
theorem B31033529 : Blo 956588 31033529 := bstep (se 2 (by rfl) ⟨11637573, by rfl⟩ : syracuseStep 31033529 = 23275147) B23275147
theorem B7276877 : Blo 956588 7276877 := bstep (se 3 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 7276877 = 2728829) B2728829
theorem B4098575 : Blo 956588 4098575 := bstep (se 1 (by rfl) ⟨3073931, by rfl⟩ : syracuseStep 4098575 = 6147863) B6147863
theorem B2427529 : Blo 956588 2427529 := bstep (se 2 (by rfl) ⟨910323, by rfl⟩ : syracuseStep 2427529 = 1820647) B1820647
theorem B1870543 : Blo 956588 1870543 := bstep (se 1 (by rfl) ⟨1402907, by rfl⟩ : syracuseStep 1870543 = 2805815) B2805815
theorem B1215263 : Blo 956588 1215263 := bstep (se 1 (by rfl) ⟨911447, by rfl⟩ : syracuseStep 1215263 = 1822895) B1822895
theorem B1150043 : Blo 956588 1150043 := bstep (se 1 (by rfl) ⟨862532, by rfl⟩ : syracuseStep 1150043 = 1725065) B1725065
theorem B2428967 : Blo 956588 2428967 := bstep (se 1 (by rfl) ⟨1821725, by rfl⟩ : syracuseStep 2428967 = 3643451) B3643451
theorem B4853843 : Blo 956588 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B8196329 : Blo 956588 8196329 := bstep (se 2 (by rfl) ⟨3073623, by rfl⟩ : syracuseStep 8196329 = 6147247) B6147247
theorem B3281359 : Blo 956588 3281359 := bstep (se 1 (by rfl) ⟨2461019, by rfl⟩ : syracuseStep 3281359 = 4922039) B4922039
theorem B3642479 : Blo 956588 3642479 := bstep (se 1 (by rfl) ⟨2731859, by rfl⟩ : syracuseStep 3642479 = 5463719) B5463719
theorem B2430121 : Blo 956588 2430121 := bstep (se 2 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 2430121 = 1822591) B1822591
theorem B2725663 : Blo 956588 2725663 := bstep (se 1 (by rfl) ⟨2044247, by rfl⟩ : syracuseStep 2725663 = 4088495) B4088495
theorem B4855625 : Blo 956588 4855625 := bstep (se 2 (by rfl) ⟨1820859, by rfl⟩ : syracuseStep 4855625 = 3641719) B3641719
theorem B956775 : Blo 956588 956775 := bstep (se 1 (by rfl) ⟨717581, by rfl⟩ : syracuseStep 956775 = 1435163) B1435163
theorem B957031 : Blo 956588 957031 := bstep (se 1 (by rfl) ⟨717773, by rfl⟩ : syracuseStep 957031 = 1435547) B1435547
theorem B957055 : Blo 956588 957055 := bstep (se 1 (by rfl) ⟨717791, by rfl⟩ : syracuseStep 957055 = 1435583) B1435583
theorem B957179 : Blo 956588 957179 := bstep (se 1 (by rfl) ⟨717884, by rfl⟩ : syracuseStep 957179 = 1435769) B1435769
theorem B2726905 : Blo 956588 2726905 := bstep (se 2 (by rfl) ⟨1022589, by rfl⟩ : syracuseStep 2726905 = 2045179) B2045179
theorem B957435 : Blo 956588 957435 := bstep (se 1 (by rfl) ⟨718076, by rfl⟩ : syracuseStep 957435 = 1436153) B1436153
theorem B957471 : Blo 956588 957471 := bstep (se 1 (by rfl) ⟨718103, by rfl⟩ : syracuseStep 957471 = 1436207) B1436207
theorem B10918961 : Blo 956588 10918961 := bstep (se 2 (by rfl) ⟨4094610, by rfl⟩ : syracuseStep 10918961 = 8189221) B8189221
theorem B4856921 : Blo 956588 4856921 := bstep (se 2 (by rfl) ⟨1821345, by rfl⟩ : syracuseStep 4856921 = 3642691) B3642691
theorem B957759 : Blo 956588 957759 := bstep (se 1 (by rfl) ⟨718319, by rfl⟩ : syracuseStep 957759 = 1436639) B1436639
theorem B2596303 : Blo 956588 2596303 := bstep (se 1 (by rfl) ⟨1947227, by rfl⟩ : syracuseStep 2596303 = 3894455) B3894455
theorem B958055 : Blo 956588 958055 := bstep (se 1 (by rfl) ⟨718541, by rfl⟩ : syracuseStep 958055 = 1437083) B1437083
theorem B958335 : Blo 956588 958335 := bstep (se 1 (by rfl) ⟨718751, by rfl⟩ : syracuseStep 958335 = 1437503) B1437503
theorem B9838579 : Blo 956588 9838579 := bstep (se 1 (by rfl) ⟨7378934, by rfl⟩ : syracuseStep 9838579 = 14757869) B14757869
theorem B958459 : Blo 956588 958459 := bstep (se 1 (by rfl) ⟨718844, by rfl⟩ : syracuseStep 958459 = 1437689) B1437689
theorem B958619 : Blo 956588 958619 := bstep (se 1 (by rfl) ⟨718964, by rfl⟩ : syracuseStep 958619 = 1437929) B1437929
theorem B958703 : Blo 956588 958703 := bstep (se 1 (by rfl) ⟨719027, by rfl⟩ : syracuseStep 958703 = 1438055) B1438055
theorem B6136175 : Blo 956588 6136175 := bstep (se 1 (by rfl) ⟨4602131, by rfl⟩ : syracuseStep 6136175 = 9204263) B9204263
theorem B2728363 : Blo 956588 2728363 := bstep (se 1 (by rfl) ⟨2046272, by rfl⟩ : syracuseStep 2728363 = 4092545) B4092545
theorem B6136357 : Blo 956588 6136357 := bstep (se 4 (by rfl) ⟨575283, by rfl⟩ : syracuseStep 6136357 = 1150567) B1150567
theorem B959067 : Blo 956588 959067 := bstep (se 1 (by rfl) ⟨719300, by rfl⟩ : syracuseStep 959067 = 1438601) B1438601
theorem B959323 : Blo 956588 959323 := bstep (se 1 (by rfl) ⟨719492, by rfl⟩ : syracuseStep 959323 = 1438985) B1438985
theorem B31105907 : Blo 956588 31105907 := bstep (se 1 (by rfl) ⟨23329430, by rfl⟩ : syracuseStep 31105907 = 46658861) B46658861
theorem B959359 : Blo 956588 959359 := bstep (se 1 (by rfl) ⟨719519, by rfl⟩ : syracuseStep 959359 = 1439039) B1439039
theorem B959643 : Blo 956588 959643 := bstep (se 1 (by rfl) ⟨719732, by rfl⟩ : syracuseStep 959643 = 1439465) B1439465
theorem B959647 : Blo 956588 959647 := bstep (se 1 (by rfl) ⟨719735, by rfl⟩ : syracuseStep 959647 = 1439471) B1439471
theorem B1942751 : Blo 956588 1942751 := bstep (se 1 (by rfl) ⟨1457063, by rfl⟩ : syracuseStep 1942751 = 2914127) B2914127
theorem B959951 : Blo 956588 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B959983 : Blo 956588 959983 := bstep (se 1 (by rfl) ⟨719987, by rfl⟩ : syracuseStep 959983 = 1439975) B1439975
theorem B960231 : Blo 956588 960231 := bstep (se 1 (by rfl) ⟨720173, by rfl⟩ : syracuseStep 960231 = 1440347) B1440347
theorem B960327 : Blo 956588 960327 := bstep (se 1 (by rfl) ⟨720245, by rfl⟩ : syracuseStep 960327 = 1440491) B1440491
theorem B960347 : Blo 956588 960347 := bstep (se 1 (by rfl) ⟨720260, by rfl⟩ : syracuseStep 960347 = 1440521) B1440521
theorem B93267895 : Blo 956588 93267895 := bstep (se 1 (by rfl) ⟨69950921, by rfl⟩ : syracuseStep 93267895 = 139901843) B139901843
theorem B1616287 : Blo 956588 1616287 := bstep (se 1 (by rfl) ⟨1212215, by rfl⟩ : syracuseStep 1616287 = 2424431) B2424431
theorem B8203301 : Blo 956588 8203301 := bstep (se 4 (by rfl) ⟨769059, by rfl⟩ : syracuseStep 8203301 = 1538119) B1538119
theorem B4861295 : Blo 956588 4861295 := bstep (se 1 (by rfl) ⟨3645971, by rfl⟩ : syracuseStep 4861295 = 7291943) B7291943
theorem B2731745 : Blo 956588 2731745 := bstep (se 2 (by rfl) ⟨1024404, by rfl⟩ : syracuseStep 2731745 = 2048809) B2048809
theorem B16626293 : Blo 956588 16626293 := bstep (se 5 (by rfl) ⟨779357, by rfl⟩ : syracuseStep 16626293 = 1558715) B1558715
theorem B1816091 : Blo 956588 1816091 := bstep (se 1 (by rfl) ⟨1362068, by rfl⟩ : syracuseStep 1816091 = 2724137) B2724137
theorem B7289027 : Blo 956588 7289027 := bstep (se 1 (by rfl) ⟨5466770, by rfl⟩ : syracuseStep 7289027 = 10933541) B10933541
theorem B1817063 : Blo 956588 1817063 := bstep (se 1 (by rfl) ⟨1362797, by rfl⟩ : syracuseStep 1817063 = 2725595) B2725595
theorem B3684989 : Blo 956588 3684989 := bstep (se 3 (by rfl) ⟨690935, by rfl⟩ : syracuseStep 3684989 = 1381871) B1381871
theorem B2767807 : Blo 956588 2767807 := bstep (se 1 (by rfl) ⟨2075855, by rfl⟩ : syracuseStep 2767807 = 4151711) B4151711
theorem B5455471 : Blo 956588 5455471 := bstep (se 1 (by rfl) ⟨4091603, by rfl⟩ : syracuseStep 5455471 = 8183207) B8183207
theorem B11681657 : Blo 956588 11681657 := bstep (se 2 (by rfl) ⟨4380621, by rfl⟩ : syracuseStep 11681657 = 8761243) B8761243
theorem B168116147 : Blo 956588 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B3195095 : Blo 956588 3195095 := bstep (se 1 (by rfl) ⟨2396321, by rfl⟩ : syracuseStep 3195095 = 4792643) B4792643
theorem B12272147 : Blo 956588 12272147 := bstep (se 1 (by rfl) ⟨9204110, by rfl⟩ : syracuseStep 12272147 = 18408221) B18408221
theorem B8733359 : Blo 956588 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B22136609 : Blo 956588 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B3229577 : Blo 956588 3229577 := bstep (se 2 (by rfl) ⟨1211091, by rfl⟩ : syracuseStep 3229577 = 2422183) B2422183
theorem B91146131 : Blo 956588 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B13814185 : Blo 956588 13814185 := bstep (se 2 (by rfl) ⟨5180319, by rfl⟩ : syracuseStep 13814185 = 10360639) B10360639
theorem B2771869 : Blo 956588 2771869 := bstep (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) B1039451
theorem B1362911 : Blo 956588 1362911 := bstep (se 1 (by rfl) ⟨1022183, by rfl⟩ : syracuseStep 1362911 = 2044367) B2044367
theorem B7392235 : Blo 956588 7392235 := bstep (se 1 (by rfl) ⟨5544176, by rfl⟩ : syracuseStep 7392235 = 11088353) B11088353
theorem B7785629 : Blo 956588 7785629 := bstep (se 3 (by rfl) ⟨1459805, by rfl⟩ : syracuseStep 7785629 = 2919611) B2919611
theorem B1822007 : Blo 956588 1822007 := bstep (se 1 (by rfl) ⟨1366505, by rfl⟩ : syracuseStep 1822007 = 2733011) B2733011
theorem B970471 : Blo 956588 970471 := bstep (se 1 (by rfl) ⟨727853, by rfl⟩ : syracuseStep 970471 = 1455707) B1455707
theorem B13094783 : Blo 956588 13094783 := bstep (se 1 (by rfl) ⟨9821087, by rfl⟩ : syracuseStep 13094783 = 19642175) B19642175
theorem B13324175 : Blo 956588 13324175 := bstep (se 1 (by rfl) ⟨9993131, by rfl⟩ : syracuseStep 13324175 = 19986263) B19986263
theorem B6148477 : Blo 956588 6148477 := bstep (se 3 (by rfl) ⟨1152839, by rfl⟩ : syracuseStep 6148477 = 2305679) B2305679
theorem B33608371 : Blo 956588 33608371 := bstep (se 1 (by rfl) ⟨25206278, by rfl⟩ : syracuseStep 33608371 = 50412557) B50412557
theorem B21025469 : Blo 956588 21025469 := bstep (se 3 (by rfl) ⟨3942275, by rfl⟩ : syracuseStep 21025469 = 7884551) B7884551
theorem B3068999 : Blo 956588 3068999 := bstep (se 1 (by rfl) ⟨2301749, by rfl⟩ : syracuseStep 3068999 = 4603499) B4603499
theorem B20993219 : Blo 956588 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B3233033 : Blo 956588 3233033 := bstep (se 2 (by rfl) ⟨1212387, by rfl⟩ : syracuseStep 3233033 = 2424775) B2424775
theorem B36885941 : Blo 956588 36885941 := bstep (se 5 (by rfl) ⟨1729028, by rfl⟩ : syracuseStep 36885941 = 3458057) B3458057
theorem B3069523 : Blo 956588 3069523 := bstep (se 1 (by rfl) ⟨2302142, by rfl⟩ : syracuseStep 3069523 = 4604285) B4604285
theorem B13129381 : Blo 956588 13129381 := bstep (se 4 (by rfl) ⟨1230879, by rfl⟩ : syracuseStep 13129381 = 2461759) B2461759
theorem B3889277 : Blo 956588 3889277 := bstep (se 3 (by rfl) ⟨729239, by rfl⟩ : syracuseStep 3889277 = 1458479) B1458479
theorem B7264727 : Blo 956588 7264727 := bstep (se 1 (by rfl) ⟨5448545, by rfl⟩ : syracuseStep 7264727 = 10897091) B10897091
theorem B9984671 : Blo 956588 9984671 := bstep (se 1 (by rfl) ⟨7488503, by rfl⟩ : syracuseStep 9984671 = 14977007) B14977007
theorem B3234491 : Blo 956588 3234491 := bstep (se 1 (by rfl) ⟨2425868, by rfl⟩ : syracuseStep 3234491 = 4851737) B4851737
theorem B3234599 : Blo 956588 3234599 := bstep (se 1 (by rfl) ⟨2425949, by rfl⟩ : syracuseStep 3234599 = 4851899) B4851899
theorem B3070781 : Blo 956588 3070781 := bstep (se 3 (by rfl) ⟨575771, by rfl⟩ : syracuseStep 3070781 = 1151543) B1151543
theorem B41540971 : Blo 956588 41540971 := bstep (se 1 (by rfl) ⟨31155728, by rfl⟩ : syracuseStep 41540971 = 62311457) B62311457
theorem B2154599 : Blo 956588 2154599 := bstep (se 1 (by rfl) ⟨1615949, by rfl⟩ : syracuseStep 2154599 = 3231899) B3231899
theorem B31515065 : Blo 956588 31515065 := bstep (se 2 (by rfl) ⟨11818149, by rfl⟩ : syracuseStep 31515065 = 23636299) B23636299
theorem B3236435 : Blo 956588 3236435 := bstep (se 1 (by rfl) ⟨2427326, by rfl⟩ : syracuseStep 3236435 = 4854653) B4854653
theorem B2155751 : Blo 956588 2155751 := bstep (se 1 (by rfl) ⟨1616813, by rfl⟩ : syracuseStep 2155751 = 3233627) B3233627
theorem B37414133 : Blo 956588 37414133 := bstep (se 5 (by rfl) ⟨1753787, by rfl⟩ : syracuseStep 37414133 = 3507575) B3507575
theorem B1434959 : Blo 956588 1434959 := bstep (se 1 (by rfl) ⟨1076219, by rfl⟩ : syracuseStep 1434959 = 2152439) B2152439
theorem B17458541 : Blo 956588 17458541 := bstep (se 3 (by rfl) ⟨3273476, by rfl⟩ : syracuseStep 17458541 = 6546953) B6546953
theorem B1435049 : Blo 956588 1435049 := bstep (se 2 (by rfl) ⟨538143, by rfl⟩ : syracuseStep 1435049 = 1076287) B1076287
theorem B1435199 : Blo 956588 1435199 := bstep (se 1 (by rfl) ⟨1076399, by rfl⟩ : syracuseStep 1435199 = 2152799) B2152799
theorem B1435559 : Blo 956588 1435559 := bstep (se 1 (by rfl) ⟨1076669, by rfl⟩ : syracuseStep 1435559 = 2153339) B2153339
theorem B4843475 : Blo 956588 4843475 := bstep (se 1 (by rfl) ⟨3632606, by rfl⟩ : syracuseStep 4843475 = 7265213) B7265213
theorem B1435679 : Blo 956588 1435679 := bstep (se 1 (by rfl) ⟨1076759, by rfl⟩ : syracuseStep 1435679 = 2153519) B2153519
theorem B7268615 : Blo 956588 7268615 := bstep (se 1 (by rfl) ⟨5451461, by rfl⟩ : syracuseStep 7268615 = 10902923) B10902923
theorem B78834059 : Blo 956588 78834059 := bstep (se 1 (by rfl) ⟨59125544, by rfl⟩ : syracuseStep 78834059 = 118251089) B118251089
theorem B1436135 : Blo 956588 1436135 := bstep (se 1 (by rfl) ⟨1077101, by rfl⟩ : syracuseStep 1436135 = 2154203) B2154203
theorem B1436315 : Blo 956588 1436315 := bstep (se 1 (by rfl) ⟨1077236, by rfl⟩ : syracuseStep 1436315 = 2154473) B2154473
theorem B1436537 : Blo 956588 1436537 := bstep (se 2 (by rfl) ⟨538701, by rfl⟩ : syracuseStep 1436537 = 1077403) B1077403
theorem B177335219 : Blo 956588 177335219 := bstep (se 1 (by rfl) ⟨133001414, by rfl⟩ : syracuseStep 177335219 = 266002829) B266002829
theorem B1436783 : Blo 956588 1436783 := bstep (se 1 (by rfl) ⟨1077587, by rfl⟩ : syracuseStep 1436783 = 2155175) B2155175
theorem B3632303 : Blo 956588 3632303 := bstep (se 1 (by rfl) ⟨2724227, by rfl⟩ : syracuseStep 3632303 = 5448455) B5448455
theorem B1076431 : Blo 956588 1076431 := bstep (se 1 (by rfl) ⟨807323, by rfl⟩ : syracuseStep 1076431 = 1614647) B1614647
theorem B1436879 : Blo 956588 1436879 := bstep (se 1 (by rfl) ⟨1077659, by rfl⟩ : syracuseStep 1436879 = 2155319) B2155319
theorem B3075367 : Blo 956588 3075367 := bstep (se 1 (by rfl) ⟨2306525, by rfl⟩ : syracuseStep 3075367 = 4613051) B4613051
theorem B1436999 : Blo 956588 1436999 := bstep (se 1 (by rfl) ⟨1077749, by rfl⟩ : syracuseStep 1436999 = 2155499) B2155499
theorem B1437287 : Blo 956588 1437287 := bstep (se 1 (by rfl) ⟨1077965, by rfl⟩ : syracuseStep 1437287 = 2155931) B2155931
theorem B5828321 : Blo 956588 5828321 := bstep (se 2 (by rfl) ⟨2185620, by rfl⟩ : syracuseStep 5828321 = 4371241) B4371241
theorem B2158433 : Blo 956588 2158433 := bstep (se 2 (by rfl) ⟨809412, by rfl⟩ : syracuseStep 2158433 = 1618825) B1618825
theorem B1437671 : Blo 956588 1437671 := bstep (se 1 (by rfl) ⟨1078253, by rfl⟩ : syracuseStep 1437671 = 2156507) B2156507
theorem B1437791 : Blo 956588 1437791 := bstep (se 1 (by rfl) ⟨1078343, by rfl⟩ : syracuseStep 1437791 = 2156687) B2156687
theorem B1437851 : Blo 956588 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B1077583 : Blo 956588 1077583 := bstep (se 1 (by rfl) ⟨808187, by rfl⟩ : syracuseStep 1077583 = 1616375) B1616375
theorem B1438031 : Blo 956588 1438031 := bstep (se 1 (by rfl) ⟨1078523, by rfl⟩ : syracuseStep 1438031 = 2157047) B2157047
theorem B1438121 : Blo 956588 1438121 := bstep (se 2 (by rfl) ⟨539295, by rfl⟩ : syracuseStep 1438121 = 1078591) B1078591
theorem B4846067 : Blo 956588 4846067 := bstep (se 1 (by rfl) ⟨3634550, by rfl⟩ : syracuseStep 4846067 = 7269101) B7269101
theorem B7271045 : Blo 956588 7271045 := bstep (se 4 (by rfl) ⟨681660, by rfl⟩ : syracuseStep 7271045 = 1363321) B1363321
theorem B1077979 : Blo 956588 1077979 := bstep (se 1 (by rfl) ⟨808484, by rfl⟩ : syracuseStep 1077979 = 1616969) B1616969
theorem B1438427 : Blo 956588 1438427 := bstep (se 1 (by rfl) ⟨1078820, by rfl⟩ : syracuseStep 1438427 = 2157641) B2157641
theorem B2159387 : Blo 956588 2159387 := bstep (se 1 (by rfl) ⟨1619540, by rfl⟩ : syracuseStep 2159387 = 3239081) B3239081
theorem B1536889 : Blo 956588 1536889 := bstep (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) B1152667
theorem B139752377 : Blo 956588 139752377 := bstep (se 2 (by rfl) ⟨52407141, by rfl⟩ : syracuseStep 139752377 = 104814283) B104814283
theorem B2159585 : Blo 956588 2159585 := bstep (se 2 (by rfl) ⟨809844, by rfl⟩ : syracuseStep 2159585 = 1619689) B1619689
theorem B1438697 : Blo 956588 1438697 := bstep (se 2 (by rfl) ⟨539511, by rfl⟩ : syracuseStep 1438697 = 1079023) B1079023
theorem B3634247 : Blo 956588 3634247 := bstep (se 1 (by rfl) ⟨2725685, by rfl⟩ : syracuseStep 3634247 = 5451371) B5451371
theorem B7271531 : Blo 956588 7271531 := bstep (se 1 (by rfl) ⟨5453648, by rfl⟩ : syracuseStep 7271531 = 10907297) B10907297
theorem B1438841 : Blo 956588 1438841 := bstep (se 2 (by rfl) ⟨539565, by rfl⟩ : syracuseStep 1438841 = 1079131) B1079131
theorem B2159783 : Blo 956588 2159783 := bstep (se 1 (by rfl) ⟨1619837, by rfl⟩ : syracuseStep 2159783 = 3239675) B3239675
theorem B2422345 : Blo 956588 2422345 := bstep (se 2 (by rfl) ⟨908379, by rfl⟩ : syracuseStep 2422345 = 1816759) B1816759
theorem B1439369 : Blo 956588 1439369 := bstep (se 2 (by rfl) ⟨539763, by rfl⟩ : syracuseStep 1439369 = 1079527) B1079527
theorem B23918399 : Blo 956588 23918399 := bstep (se 1 (by rfl) ⟨17938799, by rfl⟩ : syracuseStep 23918399 = 35877599) B35877599
theorem B2422619 : Blo 956588 2422619 := bstep (se 1 (by rfl) ⟨1816964, by rfl⟩ : syracuseStep 2422619 = 3633929) B3633929
theorem B1439579 : Blo 956588 1439579 := bstep (se 1 (by rfl) ⟨1079684, by rfl⟩ : syracuseStep 1439579 = 2159369) B2159369
theorem B1537883 : Blo 956588 1537883 := bstep (se 1 (by rfl) ⟨1153412, by rfl⟩ : syracuseStep 1537883 = 2306825) B2306825
theorem B1079167 : Blo 956588 1079167 := bstep (se 1 (by rfl) ⟨809375, by rfl⟩ : syracuseStep 1079167 = 1618751) B1618751
theorem B1439615 : Blo 956588 1439615 := bstep (se 1 (by rfl) ⟨1079711, by rfl⟩ : syracuseStep 1439615 = 2159423) B2159423
theorem B9828317 : Blo 956588 9828317 := bstep (se 3 (by rfl) ⟨1842809, by rfl⟩ : syracuseStep 9828317 = 3685619) B3685619
theorem B1439711 : Blo 956588 1439711 := bstep (se 1 (by rfl) ⟨1079783, by rfl⟩ : syracuseStep 1439711 = 2159567) B2159567
theorem B1439771 : Blo 956588 1439771 := bstep (se 1 (by rfl) ⟨1079828, by rfl⟩ : syracuseStep 1439771 = 2159657) B2159657
theorem B11204723 : Blo 956588 11204723 := bstep (se 1 (by rfl) ⟨8403542, by rfl⟩ : syracuseStep 11204723 = 16807085) B16807085
theorem B42006725 : Blo 956588 42006725 := bstep (se 4 (by rfl) ⟨3938130, by rfl⟩ : syracuseStep 42006725 = 7876261) B7876261
theorem B1439963 : Blo 956588 1439963 := bstep (se 1 (by rfl) ⟨1079972, by rfl⟩ : syracuseStep 1439963 = 2159945) B2159945
theorem B2160953 : Blo 956588 2160953 := bstep (se 2 (by rfl) ⟨810357, by rfl⟩ : syracuseStep 2160953 = 1620715) B1620715
theorem B1210783 : Blo 956588 1210783 := bstep (se 1 (by rfl) ⟨908087, by rfl⟩ : syracuseStep 1210783 = 1816175) B1816175
theorem B2914721 : Blo 956588 2914721 := bstep (se 2 (by rfl) ⟨1093020, by rfl⟩ : syracuseStep 2914721 = 2186041) B2186041
theorem B2587079 : Blo 956588 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B1440233 : Blo 956588 1440233 := bstep (se 2 (by rfl) ⟨540087, by rfl⟩ : syracuseStep 1440233 = 1080175) B1080175
theorem B3635705 : Blo 956588 3635705 := bstep (se 2 (by rfl) ⟨1363389, by rfl⟩ : syracuseStep 3635705 = 2726779) B2726779
theorem B10910213 : Blo 956588 10910213 := bstep (se 4 (by rfl) ⟨1022832, by rfl⟩ : syracuseStep 10910213 = 2045665) B2045665
theorem B1440623 : Blo 956588 1440623 := bstep (se 1 (by rfl) ⟨1080467, by rfl⟩ : syracuseStep 1440623 = 2160935) B2160935
theorem B82049927 : Blo 956588 82049927 := bstep (se 1 (by rfl) ⟨61537445, by rfl⟩ : syracuseStep 82049927 = 123074891) B123074891
theorem B1440863 : Blo 956588 1440863 := bstep (se 1 (by rfl) ⟨1080647, by rfl⟩ : syracuseStep 1440863 = 2161295) B2161295
theorem B5831777 : Blo 956588 5831777 := bstep (se 2 (by rfl) ⟨2186916, by rfl⟩ : syracuseStep 5831777 = 4373833) B4373833
theorem B4095467 : Blo 956588 4095467 := bstep (se 1 (by rfl) ⟨3071600, by rfl⟩ : syracuseStep 4095467 = 6143201) B6143201
theorem B12287933 : Blo 956588 12287933 := bstep (se 3 (by rfl) ⟨2303987, by rfl⟩ : syracuseStep 12287933 = 4607975) B4607975
theorem B27623861 : Blo 956588 27623861 := bstep (se 5 (by rfl) ⟨1294868, by rfl⟩ : syracuseStep 27623861 = 2589737) B2589737
theorem B3637817 : Blo 956588 3637817 := bstep (se 2 (by rfl) ⟨1364181, by rfl⟩ : syracuseStep 3637817 = 2728363) B2728363
theorem B2426183 : Blo 956588 2426183 := bstep (se 1 (by rfl) ⟨1819637, by rfl⟩ : syracuseStep 2426183 = 3639275) B3639275
theorem B4851251 : Blo 956588 4851251 := bstep (se 1 (by rfl) ⟨3638438, by rfl⟩ : syracuseStep 4851251 = 7276877) B7276877
theorem B1214671 : Blo 956588 1214671 := bstep (se 1 (by rfl) ⟨911003, by rfl⟩ : syracuseStep 1214671 = 1822007) B1822007
theorem B34081013 : Blo 956588 34081013 := bstep (se 5 (by rfl) ⟨1597547, by rfl⟩ : syracuseStep 34081013 = 3195095) B3195095
theorem B124357193 : Blo 956588 124357193 := bstep (se 2 (by rfl) ⟨46633947, by rfl⟩ : syracuseStep 124357193 = 93267895) B93267895
theorem B8882783 : Blo 956588 8882783 := bstep (se 1 (by rfl) ⟨6662087, by rfl⟩ : syracuseStep 8882783 = 13324175) B13324175
theorem B18418913 : Blo 956588 18418913 := bstep (se 2 (by rfl) ⟨6907092, by rfl⟩ : syracuseStep 18418913 = 13814185) B13814185
theorem B5180669 : Blo 956588 5180669 := bstep (se 3 (by rfl) ⟨971375, by rfl⟩ : syracuseStep 5180669 = 1942751) B1942751
theorem B2428319 : Blo 956588 2428319 := bstep (se 1 (by rfl) ⟨1821239, by rfl⟩ : syracuseStep 2428319 = 3642479) B3642479
theorem B13995479 : Blo 956588 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B2592851 : Blo 956588 2592851 := bstep (se 1 (by rfl) ⟨1944638, by rfl⟩ : syracuseStep 2592851 = 3889277) B3889277
theorem B4100489 : Blo 956588 4100489 := bstep (se 2 (by rfl) ⟨1537683, by rfl⟩ : syracuseStep 4100489 = 3075367) B3075367
theorem B6656447 : Blo 956588 6656447 := bstep (se 1 (by rfl) ⟨4992335, by rfl⟩ : syracuseStep 6656447 = 9984671) B9984671
theorem B7279307 : Blo 956588 7279307 := bstep (se 1 (by rfl) ⟨5459480, by rfl⟩ : syracuseStep 7279307 = 10918961) B10918961
theorem B21010043 : Blo 956588 21010043 := bstep (se 1 (by rfl) ⟨15757532, by rfl⟩ : syracuseStep 21010043 = 31515065) B31515065
theorem B8197969 : Blo 956588 8197969 := bstep (se 2 (by rfl) ⟨3074238, by rfl⟩ : syracuseStep 8197969 = 6148477) B6148477
theorem B24942755 : Blo 956588 24942755 := bstep (se 1 (by rfl) ⟨18707066, by rfl⟩ : syracuseStep 24942755 = 37414133) B37414133
theorem B956639 : Blo 956588 956639 := bstep (se 1 (by rfl) ⟨717479, by rfl⟩ : syracuseStep 956639 = 1434959) B1434959
theorem B11639027 : Blo 956588 11639027 := bstep (se 1 (by rfl) ⟨8729270, by rfl⟩ : syracuseStep 11639027 = 17458541) B17458541
theorem B956699 : Blo 956588 956699 := bstep (se 1 (by rfl) ⟨717524, by rfl⟩ : syracuseStep 956699 = 1435049) B1435049
theorem B956799 : Blo 956588 956799 := bstep (se 1 (by rfl) ⟨717599, by rfl⟩ : syracuseStep 956799 = 1435199) B1435199
theorem B957039 : Blo 956588 957039 := bstep (se 1 (by rfl) ⟨717779, by rfl⟩ : syracuseStep 957039 = 1435559) B1435559
theorem B957119 : Blo 956588 957119 := bstep (se 1 (by rfl) ⟨717839, by rfl⟩ : syracuseStep 957119 = 1435679) B1435679
theorem B957423 : Blo 956588 957423 := bstep (se 1 (by rfl) ⟨718067, by rfl⟩ : syracuseStep 957423 = 1436135) B1436135
theorem B957543 : Blo 956588 957543 := bstep (se 1 (by rfl) ⟨718157, by rfl⟩ : syracuseStep 957543 = 1436315) B1436315
theorem B957691 : Blo 956588 957691 := bstep (se 1 (by rfl) ⟨718268, by rfl⟩ : syracuseStep 957691 = 1436537) B1436537
theorem B957855 : Blo 956588 957855 := bstep (se 1 (by rfl) ⟨718391, by rfl⟩ : syracuseStep 957855 = 1436783) B1436783
theorem B957919 : Blo 956588 957919 := bstep (se 1 (by rfl) ⟨718439, by rfl⟩ : syracuseStep 957919 = 1436879) B1436879
theorem B957999 : Blo 956588 957999 := bstep (se 1 (by rfl) ⟨718499, by rfl⟩ : syracuseStep 957999 = 1436999) B1436999
theorem B17505841 : Blo 956588 17505841 := bstep (se 2 (by rfl) ⟨6564690, by rfl⟩ : syracuseStep 17505841 = 13129381) B13129381
theorem B218799805 : Blo 956588 218799805 := bstep (se 3 (by rfl) ⟨41024963, by rfl⟩ : syracuseStep 218799805 = 82049927) B82049927
theorem B958191 : Blo 956588 958191 := bstep (se 1 (by rfl) ⟨718643, by rfl⟩ : syracuseStep 958191 = 1437287) B1437287
theorem B958447 : Blo 956588 958447 := bstep (se 1 (by rfl) ⟨718835, by rfl⟩ : syracuseStep 958447 = 1437671) B1437671
theorem B958527 : Blo 956588 958527 := bstep (se 1 (by rfl) ⟨718895, by rfl⟩ : syracuseStep 958527 = 1437791) B1437791
theorem B958567 : Blo 956588 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B958687 : Blo 956588 958687 := bstep (se 1 (by rfl) ⟨719015, by rfl⟩ : syracuseStep 958687 = 1438031) B1438031
theorem B958747 : Blo 956588 958747 := bstep (se 1 (by rfl) ⟨719060, by rfl⟩ : syracuseStep 958747 = 1438121) B1438121
theorem B11084195 : Blo 956588 11084195 := bstep (se 1 (by rfl) ⟨8313146, by rfl⟩ : syracuseStep 11084195 = 16626293) B16626293
theorem B958951 : Blo 956588 958951 := bstep (se 1 (by rfl) ⟨719213, by rfl⟩ : syracuseStep 958951 = 1438427) B1438427
theorem B1614377 : Blo 956588 1614377 := bstep (se 2 (by rfl) ⟨605391, by rfl⟩ : syracuseStep 1614377 = 1210783) B1210783
theorem B93168251 : Blo 956588 93168251 := bstep (se 1 (by rfl) ⟨69876188, by rfl⟩ : syracuseStep 93168251 = 139752377) B139752377
theorem B959131 : Blo 956588 959131 := bstep (se 1 (by rfl) ⟨719348, by rfl⟩ : syracuseStep 959131 = 1438697) B1438697
theorem B959227 : Blo 956588 959227 := bstep (se 1 (by rfl) ⟨719420, by rfl⟩ : syracuseStep 959227 = 1438841) B1438841
theorem B959579 : Blo 956588 959579 := bstep (se 1 (by rfl) ⟨719684, by rfl⟩ : syracuseStep 959579 = 1439369) B1439369
theorem B1615079 : Blo 956588 1615079 := bstep (se 1 (by rfl) ⟨1211309, by rfl⟩ : syracuseStep 1615079 = 2422619) B2422619
theorem B959719 : Blo 956588 959719 := bstep (se 1 (by rfl) ⟨719789, by rfl⟩ : syracuseStep 959719 = 1439579) B1439579
theorem B1025255 : Blo 956588 1025255 := bstep (se 1 (by rfl) ⟨768941, by rfl⟩ : syracuseStep 1025255 = 1537883) B1537883
theorem B959743 : Blo 956588 959743 := bstep (se 1 (by rfl) ⟨719807, by rfl⟩ : syracuseStep 959743 = 1439615) B1439615
theorem B959807 : Blo 956588 959807 := bstep (se 1 (by rfl) ⟨719855, by rfl⟩ : syracuseStep 959807 = 1439711) B1439711
theorem B959847 : Blo 956588 959847 := bstep (se 1 (by rfl) ⟨719885, by rfl⟩ : syracuseStep 959847 = 1439771) B1439771
theorem B4859351 : Blo 956588 4859351 := bstep (se 1 (by rfl) ⟨3644513, by rfl⟩ : syracuseStep 4859351 = 7289027) B7289027
theorem B959975 : Blo 956588 959975 := bstep (se 1 (by rfl) ⟨719981, by rfl⟩ : syracuseStep 959975 = 1439963) B1439963
theorem B1943147 : Blo 956588 1943147 := bstep (se 1 (by rfl) ⟨1457360, by rfl⟩ : syracuseStep 1943147 = 2914721) B2914721
theorem B960155 : Blo 956588 960155 := bstep (se 1 (by rfl) ⟨720116, by rfl⟩ : syracuseStep 960155 = 1440233) B1440233
theorem B55387961 : Blo 956588 55387961 := bstep (se 2 (by rfl) ⟨20770485, by rfl⟩ : syracuseStep 55387961 = 41540971) B41540971
theorem B960415 : Blo 956588 960415 := bstep (se 1 (by rfl) ⟨720311, by rfl⟩ : syracuseStep 960415 = 1440623) B1440623
theorem B15542189 : Blo 956588 15542189 := bstep (se 3 (by rfl) ⟨2914160, by rfl⟩ : syracuseStep 15542189 = 5828321) B5828321
theorem B7284653 : Blo 956588 7284653 := bstep (se 3 (by rfl) ⟨1365872, by rfl⟩ : syracuseStep 7284653 = 2731745) B2731745
theorem B960575 : Blo 956588 960575 := bstep (se 1 (by rfl) ⟨720431, by rfl⟩ : syracuseStep 960575 = 1440863) B1440863
theorem B2730311 : Blo 956588 2730311 := bstep (se 1 (by rfl) ⟨2047733, by rfl⟩ : syracuseStep 2730311 = 4095467) B4095467
theorem B112077431 : Blo 956588 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B13118105 : Blo 956588 13118105 := bstep (se 2 (by rfl) ⟨4919289, by rfl⟩ : syracuseStep 13118105 = 9838579) B9838579
theorem B4369747 : Blo 956588 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B2731495 : Blo 956588 2731495 := bstep (se 1 (by rfl) ⟨2048621, by rfl⟩ : syracuseStep 2731495 = 4097243) B4097243
theorem B12267125 : Blo 956588 12267125 := bstep (se 5 (by rfl) ⟨575021, by rfl⟩ : syracuseStep 12267125 = 1150043) B1150043
theorem B16363133 : Blo 956588 16363133 := bstep (se 3 (by rfl) ⟨3068087, by rfl⟩ : syracuseStep 16363133 = 6136175) B6136175
theorem B1617563 : Blo 956588 1617563 := bstep (se 1 (by rfl) ⟨1213172, by rfl⟩ : syracuseStep 1617563 = 2426345) B2426345
theorem B60764087 : Blo 956588 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B1618015 : Blo 956588 1618015 := bstep (se 1 (by rfl) ⟨1213511, by rfl⟩ : syracuseStep 1618015 = 2427023) B2427023
theorem B20689019 : Blo 956588 20689019 := bstep (se 1 (by rfl) ⟨15516764, by rfl⟩ : syracuseStep 20689019 = 31033529) B31033529
theorem B2732383 : Blo 956588 2732383 := bstep (se 1 (by rfl) ⟨2049287, by rfl⟩ : syracuseStep 2732383 = 4098575) B4098575
theorem B10924793 : Blo 956588 10924793 := bstep (se 2 (by rfl) ⟨4096797, by rfl⟩ : syracuseStep 10924793 = 8193595) B8193595
theorem B5190419 : Blo 956588 5190419 := bstep (se 1 (by rfl) ⟨3892814, by rfl⟩ : syracuseStep 5190419 = 7785629) B7785629
theorem B8729855 : Blo 956588 8729855 := bstep (se 1 (by rfl) ⟨6547391, by rfl⟩ : syracuseStep 8729855 = 13094783) B13094783
theorem B1619257 : Blo 956588 1619257 := bstep (se 2 (by rfl) ⟨607221, by rfl⟩ : syracuseStep 1619257 = 1214443) B1214443
theorem B1619311 : Blo 956588 1619311 := bstep (se 1 (by rfl) ⟨1214483, by rfl⟩ : syracuseStep 1619311 = 2428967) B2428967
theorem B2045999 : Blo 956588 2045999 := bstep (se 1 (by rfl) ⟨1534499, by rfl⟩ : syracuseStep 2045999 = 3068999) B3068999
theorem B24590627 : Blo 956588 24590627 := bstep (se 1 (by rfl) ⟨18442970, by rfl⟩ : syracuseStep 24590627 = 36885941) B36885941
theorem B13810085 : Blo 956588 13810085 := bstep (se 4 (by rfl) ⟨1294695, by rfl⟩ : syracuseStep 13810085 = 2589391) B2589391
theorem B9976229 : Blo 956588 9976229 := bstep (se 4 (by rfl) ⟨935271, by rfl⟩ : syracuseStep 9976229 = 1870543) B1870543
theorem B2047187 : Blo 956588 2047187 := bstep (se 1 (by rfl) ⟨1535390, by rfl⟩ : syracuseStep 2047187 = 3070781) B3070781
theorem B59030957 : Blo 956588 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B4375145 : Blo 956588 4375145 := bstep (se 2 (by rfl) ⟨1640679, by rfl⟩ : syracuseStep 4375145 = 3281359) B3281359
theorem B44811161 : Blo 956588 44811161 := bstep (se 2 (by rfl) ⟨16804185, by rfl⟩ : syracuseStep 44811161 = 33608371) B33608371
theorem B2049185 : Blo 956588 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B6898877 : Blo 956588 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B3228983 : Blo 956588 3228983 := bstep (se 1 (by rfl) ⟨2421737, by rfl⟩ : syracuseStep 3228983 = 4843475) B4843475
theorem B3229793 : Blo 956588 3229793 := bstep (se 2 (by rfl) ⟨1211172, by rfl⟩ : syracuseStep 3229793 = 2422345) B2422345
theorem B3230711 : Blo 956588 3230711 := bstep (se 1 (by rfl) ⟨2423033, by rfl⟩ : syracuseStep 3230711 = 4846067) B4846067
theorem B15945599 : Blo 956588 15945599 := bstep (se 1 (by rfl) ⟨11959199, by rfl⟩ : syracuseStep 15945599 = 23918399) B23918399
theorem B3690409 : Blo 956588 3690409 := bstep (se 2 (by rfl) ⟨1383903, by rfl⟩ : syracuseStep 3690409 = 2767807) B2767807
theorem B28004483 : Blo 956588 28004483 := bstep (se 1 (by rfl) ⟨21003362, by rfl⟩ : syracuseStep 28004483 = 42006725) B42006725
theorem B3461737 : Blo 956588 3461737 := bstep (se 2 (by rfl) ⟨1298151, by rfl⟩ : syracuseStep 3461737 = 2596303) B2596303
theorem B3887851 : Blo 956588 3887851 := bstep (se 1 (by rfl) ⟨2915888, by rfl⟩ : syracuseStep 3887851 = 5831777) B5831777
theorem B7787771 : Blo 956588 7787771 := bstep (se 1 (by rfl) ⟨5840828, by rfl⟩ : syracuseStep 7787771 = 11681657) B11681657
theorem B8181431 : Blo 956588 8181431 := bstep (se 1 (by rfl) ⟨6136073, by rfl⟩ : syracuseStep 8181431 = 12272147) B12272147
theorem B5822239 : Blo 956588 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B3233789 : Blo 956588 3233789 := bstep (se 3 (by rfl) ⟨606335, by rfl⟩ : syracuseStep 3233789 = 1212671) B1212671
theorem B8181809 : Blo 956588 8181809 := bstep (se 2 (by rfl) ⟨3068178, by rfl⟩ : syracuseStep 8181809 = 6136357) B6136357
theorem B2153051 : Blo 956588 2153051 := bstep (se 1 (by rfl) ⟨1614788, by rfl⟩ : syracuseStep 2153051 = 3229577) B3229577
theorem B3235193 : Blo 956588 3235193 := bstep (se 2 (by rfl) ⟨1213197, by rfl⟩ : syracuseStep 3235193 = 2426395) B2426395
theorem B3235895 : Blo 956588 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B5464219 : Blo 956588 5464219 := bstep (se 1 (by rfl) ⟨4098164, by rfl⟩ : syracuseStep 5464219 = 8196329) B8196329
theorem B14016979 : Blo 956588 14016979 := bstep (se 1 (by rfl) ⟨10512734, by rfl⟩ : syracuseStep 14016979 = 21025469) B21025469
theorem B2155049 : Blo 956588 2155049 := bstep (se 2 (by rfl) ⟨808143, by rfl⟩ : syracuseStep 2155049 = 1616287) B1616287
theorem B2155355 : Blo 956588 2155355 := bstep (se 1 (by rfl) ⟨1616516, by rfl⟩ : syracuseStep 2155355 = 3233033) B3233033
theorem B3236705 : Blo 956588 3236705 := bstep (se 2 (by rfl) ⟨1213764, by rfl⟩ : syracuseStep 3236705 = 2427529) B2427529
theorem B3695825 : Blo 956588 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B3237083 : Blo 956588 3237083 := bstep (se 1 (by rfl) ⟨2427812, by rfl⟩ : syracuseStep 3237083 = 4855625) B4855625
theorem B9856313 : Blo 956588 9856313 := bstep (se 2 (by rfl) ⟨3696117, by rfl⟩ : syracuseStep 9856313 = 7392235) B7392235
theorem B1435241 : Blo 956588 1435241 := bstep (se 2 (by rfl) ⟨538215, by rfl⟩ : syracuseStep 1435241 = 1076431) B1076431
theorem B4843151 : Blo 956588 4843151 := bstep (se 1 (by rfl) ⟨3632363, by rfl⟩ : syracuseStep 4843151 = 7264727) B7264727
theorem B2156327 : Blo 956588 2156327 := bstep (se 1 (by rfl) ⟨1617245, by rfl⟩ : syracuseStep 2156327 = 3234491) B3234491
theorem B2156399 : Blo 956588 2156399 := bstep (se 1 (by rfl) ⟨1617299, by rfl⟩ : syracuseStep 2156399 = 3234599) B3234599
theorem B3237947 : Blo 956588 3237947 := bstep (se 1 (by rfl) ⟨2428460, by rfl⟩ : syracuseStep 3237947 = 4856921) B4856921
theorem B1436399 : Blo 956588 1436399 := bstep (se 1 (by rfl) ⟨1077299, by rfl⟩ : syracuseStep 1436399 = 2154599) B2154599
theorem B2157623 : Blo 956588 2157623 := bstep (se 1 (by rfl) ⟨1618217, by rfl⟩ : syracuseStep 2157623 = 3236435) B3236435
theorem B1436777 : Blo 956588 1436777 := bstep (se 2 (by rfl) ⟨538791, by rfl⟩ : syracuseStep 1436777 = 1077583) B1077583
theorem B20737271 : Blo 956588 20737271 := bstep (se 1 (by rfl) ⟨15552953, by rfl⟩ : syracuseStep 20737271 = 31105907) B31105907
theorem B1437167 : Blo 956588 1437167 := bstep (se 1 (by rfl) ⟨1077875, by rfl⟩ : syracuseStep 1437167 = 2155751) B2155751
theorem B1437305 : Blo 956588 1437305 := bstep (se 2 (by rfl) ⟨538989, by rfl⟩ : syracuseStep 1437305 = 1077979) B1077979
theorem B4845743 : Blo 956588 4845743 := bstep (se 1 (by rfl) ⟨3634307, by rfl⟩ : syracuseStep 4845743 = 7268615) B7268615
theorem B3240161 : Blo 956588 3240161 := bstep (se 2 (by rfl) ⟨1215060, by rfl⟩ : syracuseStep 3240161 = 2430121) B2430121
theorem B52556039 : Blo 956588 52556039 := bstep (se 1 (by rfl) ⟨39417029, by rfl⟩ : syracuseStep 52556039 = 78834059) B78834059
theorem B118223479 : Blo 956588 118223479 := bstep (se 1 (by rfl) ⟨88667609, by rfl⟩ : syracuseStep 118223479 = 177335219) B177335219
theorem B5468867 : Blo 956588 5468867 := bstep (se 1 (by rfl) ⟨4101650, by rfl⟩ : syracuseStep 5468867 = 8203301) B8203301
theorem B3240701 : Blo 956588 3240701 := bstep (se 3 (by rfl) ⟨607631, by rfl⟩ : syracuseStep 3240701 = 1215263) B1215263
theorem B4092697 : Blo 956588 4092697 := bstep (se 2 (by rfl) ⟨1534761, by rfl⟩ : syracuseStep 4092697 = 3069523) B3069523
theorem B2421535 : Blo 956588 2421535 := bstep (se 1 (by rfl) ⟨1816151, by rfl⟩ : syracuseStep 2421535 = 3632303) B3632303
theorem B3240863 : Blo 956588 3240863 := bstep (se 1 (by rfl) ⟨2430647, by rfl⟩ : syracuseStep 3240863 = 4861295) B4861295
theorem B3634217 : Blo 956588 3634217 := bstep (se 2 (by rfl) ⟨1362831, by rfl⟩ : syracuseStep 3634217 = 2725663) B2725663
theorem B1438889 : Blo 956588 1438889 := bstep (se 2 (by rfl) ⟨539583, by rfl⟩ : syracuseStep 1438889 = 1079167) B1079167
theorem B1438955 : Blo 956588 1438955 := bstep (se 1 (by rfl) ⟨1079216, by rfl⟩ : syracuseStep 1438955 = 2158433) B2158433
theorem B3634429 : Blo 956588 3634429 := bstep (se 3 (by rfl) ⟨681455, by rfl⟩ : syracuseStep 3634429 = 1362911) B1362911
theorem B4847363 : Blo 956588 4847363 := bstep (se 1 (by rfl) ⟨3635522, by rfl⟩ : syracuseStep 4847363 = 7271045) B7271045
theorem B1439591 : Blo 956588 1439591 := bstep (se 1 (by rfl) ⟨1079693, by rfl⟩ : syracuseStep 1439591 = 2159387) B2159387
theorem B1439723 : Blo 956588 1439723 := bstep (se 1 (by rfl) ⟨1079792, by rfl⟩ : syracuseStep 1439723 = 2159585) B2159585
theorem B2422831 : Blo 956588 2422831 := bstep (se 1 (by rfl) ⟨1817123, by rfl⟩ : syracuseStep 2422831 = 3634247) B3634247
theorem B4847687 : Blo 956588 4847687 := bstep (se 1 (by rfl) ⟨3635765, by rfl⟩ : syracuseStep 4847687 = 7271531) B7271531
theorem B1439855 : Blo 956588 1439855 := bstep (se 1 (by rfl) ⟨1079891, by rfl⟩ : syracuseStep 1439855 = 2159783) B2159783
theorem B1210727 : Blo 956588 1210727 := bstep (se 1 (by rfl) ⟨908045, by rfl⟩ : syracuseStep 1210727 = 1816091) B1816091
theorem B5175845 : Blo 956588 5175845 := bstep (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) B970471
theorem B6552211 : Blo 956588 6552211 := bstep (se 1 (by rfl) ⟨4914158, by rfl⟩ : syracuseStep 6552211 = 9828317) B9828317
theorem B3635873 : Blo 956588 3635873 := bstep (se 2 (by rfl) ⟨1363452, by rfl⟩ : syracuseStep 3635873 = 2726905) B2726905
theorem B7469815 : Blo 956588 7469815 := bstep (se 1 (by rfl) ⟨5602361, by rfl⟩ : syracuseStep 7469815 = 11204723) B11204723
theorem B1440635 : Blo 956588 1440635 := bstep (se 1 (by rfl) ⟨1080476, by rfl⟩ : syracuseStep 1440635 = 2160953) B2160953
theorem B1211375 : Blo 956588 1211375 := bstep (se 1 (by rfl) ⟨908531, by rfl⟩ : syracuseStep 1211375 = 1817063) B1817063
theorem B2423803 : Blo 956588 2423803 := bstep (se 1 (by rfl) ⟨1817852, by rfl⟩ : syracuseStep 2423803 = 3635705) B3635705
theorem B7273475 : Blo 956588 7273475 := bstep (se 1 (by rfl) ⟨5455106, by rfl⟩ : syracuseStep 7273475 = 10910213) B10910213
theorem B2456659 : Blo 956588 2456659 := bstep (se 1 (by rfl) ⟨1842494, by rfl⟩ : syracuseStep 2456659 = 3684989) B3684989
theorem B7273961 : Blo 956588 7273961 := bstep (se 2 (by rfl) ⟨2727735, by rfl⟩ : syracuseStep 7273961 = 5455471) B5455471
theorem B8191955 : Blo 956588 8191955 := bstep (se 1 (by rfl) ⟨6143966, by rfl⟩ : syracuseStep 8191955 = 12287933) B12287933
theorem B6914269 : Blo 956588 6914269 := bstep (se 3 (by rfl) ⟨1296425, by rfl⟩ : syracuseStep 6914269 = 2592851) B2592851
theorem B18415907 : Blo 956588 18415907 := bstep (se 1 (by rfl) ⟨13811930, by rfl⟩ : syracuseStep 18415907 = 27623861) B27623861
theorem B2425211 : Blo 956588 2425211 := bstep (se 1 (by rfl) ⟨1818908, by rfl⟩ : syracuseStep 2425211 = 3637817) B3637817
theorem B11667053 : Blo 956588 11667053 := bstep (se 3 (by rfl) ⟨2187572, by rfl⟩ : syracuseStep 11667053 = 4375145) B4375145
theorem B82904795 : Blo 956588 82904795 := bstep (se 1 (by rfl) ⟨62178596, by rfl⟩ : syracuseStep 82904795 = 124357193) B124357193
theorem B4852871 : Blo 956588 4852871 := bstep (se 1 (by rfl) ⟨3639653, by rfl⟩ : syracuseStep 4852871 = 7279307) B7279307
theorem B5181725 : Blo 956588 5181725 := bstep (se 3 (by rfl) ⟨971573, by rfl⟩ : syracuseStep 5181725 = 1943147) B1943147
theorem B3641993 : Blo 956588 3641993 := bstep (se 2 (by rfl) ⟨1365747, by rfl⟩ : syracuseStep 3641993 = 2731495) B2731495
theorem B4920545 : Blo 956588 4920545 := bstep (se 2 (by rfl) ⟨1845204, by rfl⟩ : syracuseStep 4920545 = 3690409) B3690409
theorem B3643177 : Blo 956588 3643177 := bstep (se 2 (by rfl) ⟨1366191, by rfl⟩ : syracuseStep 3643177 = 2732383) B2732383
theorem B2463883 : Blo 956588 2463883 := bstep (se 1 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 2463883 = 3695825) B3695825
theorem B5183801 : Blo 956588 5183801 := bstep (se 2 (by rfl) ⟨1943925, by rfl⟩ : syracuseStep 5183801 = 3887851) B3887851
theorem B956827 : Blo 956588 956827 := bstep (se 1 (by rfl) ⟨717620, by rfl⟩ : syracuseStep 956827 = 1435241) B1435241
theorem B10361459 : Blo 956588 10361459 := bstep (se 1 (by rfl) ⟨7771094, by rfl⟩ : syracuseStep 10361459 = 15542189) B15542189
theorem B4856435 : Blo 956588 4856435 := bstep (se 1 (by rfl) ⟨3642326, by rfl⟩ : syracuseStep 4856435 = 7284653) B7284653
theorem B74718287 : Blo 956588 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B957599 : Blo 956588 957599 := bstep (se 1 (by rfl) ⟨718199, by rfl⟩ : syracuseStep 957599 = 1436399) B1436399
theorem B957851 : Blo 956588 957851 := bstep (se 1 (by rfl) ⟨718388, by rfl⟩ : syracuseStep 957851 = 1436777) B1436777
theorem B958111 : Blo 956588 958111 := bstep (se 1 (by rfl) ⟨718583, by rfl⟩ : syracuseStep 958111 = 1437167) B1437167
theorem B958203 : Blo 956588 958203 := bstep (se 1 (by rfl) ⟨718652, by rfl⟩ : syracuseStep 958203 = 1437305) B1437305
theorem B40509391 : Blo 956588 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B35037359 : Blo 956588 35037359 := bstep (se 1 (by rfl) ⟨26278019, by rfl⟩ : syracuseStep 35037359 = 52556039) B52556039
theorem B3645911 : Blo 956588 3645911 := bstep (se 1 (by rfl) ⟨2734433, by rfl⟩ : syracuseStep 3645911 = 5468867) B5468867
theorem B7283195 : Blo 956588 7283195 := bstep (se 1 (by rfl) ⟨5462396, by rfl⟩ : syracuseStep 7283195 = 10924793) B10924793
theorem B959259 : Blo 956588 959259 := bstep (se 1 (by rfl) ⟨719444, by rfl⟩ : syracuseStep 959259 = 1438889) B1438889
theorem B959303 : Blo 956588 959303 := bstep (se 1 (by rfl) ⟨719477, by rfl⟩ : syracuseStep 959303 = 1438955) B1438955
theorem B959727 : Blo 956588 959727 := bstep (se 1 (by rfl) ⟨719795, by rfl⟩ : syracuseStep 959727 = 1439591) B1439591
theorem B959815 : Blo 956588 959815 := bstep (se 1 (by rfl) ⟨719861, by rfl⟩ : syracuseStep 959815 = 1439723) B1439723
theorem B959903 : Blo 956588 959903 := bstep (se 1 (by rfl) ⟨719927, by rfl⟩ : syracuseStep 959903 = 1439855) B1439855
theorem B16393751 : Blo 956588 16393751 := bstep (se 1 (by rfl) ⟨12295313, by rfl⟩ : syracuseStep 16393751 = 24590627) B24590627
theorem B3450563 : Blo 956588 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B960423 : Blo 956588 960423 := bstep (se 1 (by rfl) ⟨720317, by rfl⟩ : syracuseStep 960423 = 1440635) B1440635
theorem B23341121 : Blo 956588 23341121 := bstep (se 2 (by rfl) ⟨8752920, by rfl⟩ : syracuseStep 23341121 = 17505841) B17505841
theorem B7285625 : Blo 956588 7285625 := bstep (se 2 (by rfl) ⟨2732109, by rfl⟩ : syracuseStep 7285625 = 5464219) B5464219
theorem B18689305 : Blo 956588 18689305 := bstep (se 2 (by rfl) ⟨7008489, by rfl⟩ : syracuseStep 18689305 = 14016979) B14016979
theorem B4599251 : Blo 956588 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B1617455 : Blo 956588 1617455 := bstep (se 1 (by rfl) ⟨1213091, by rfl⟩ : syracuseStep 1617455 = 2426183) B2426183
theorem B22720675 : Blo 956588 22720675 := bstep (se 1 (by rfl) ⟨17040506, by rfl⟩ : syracuseStep 22720675 = 34081013) B34081013
theorem B3453779 : Blo 956588 3453779 := bstep (se 1 (by rfl) ⟨2590334, by rfl⟩ : syracuseStep 3453779 = 5180669) B5180669
theorem B1618879 : Blo 956588 1618879 := bstep (se 1 (by rfl) ⟨1214159, by rfl⟩ : syracuseStep 1618879 = 2428319) B2428319
theorem B10630399 : Blo 956588 10630399 := bstep (se 1 (by rfl) ⟨7972799, by rfl⟩ : syracuseStep 10630399 = 15945599) B15945599
theorem B2733659 : Blo 956588 2733659 := bstep (se 1 (by rfl) ⟨2050244, by rfl⟩ : syracuseStep 2733659 = 4100489) B4100489
theorem B1619561 : Blo 956588 1619561 := bstep (se 2 (by rfl) ⟨607335, by rfl⟩ : syracuseStep 1619561 = 1214671) B1214671
theorem B4437631 : Blo 956588 4437631 := bstep (se 1 (by rfl) ⟨3328223, by rfl⟩ : syracuseStep 4437631 = 6656447) B6656447
theorem B2734013 : Blo 956588 2734013 := bstep (se 3 (by rfl) ⟨512627, by rfl⟩ : syracuseStep 2734013 = 1025255) B1025255
theorem B5191847 : Blo 956588 5191847 := bstep (se 1 (by rfl) ⟨3893885, by rfl⟩ : syracuseStep 5191847 = 7787771) B7787771
theorem B14006695 : Blo 956588 14006695 := bstep (se 1 (by rfl) ⟨10505021, by rfl⟩ : syracuseStep 14006695 = 21010043) B21010043
theorem B5454287 : Blo 956588 5454287 := bstep (se 1 (by rfl) ⟨4090715, by rfl⟩ : syracuseStep 5454287 = 8181431) B8181431
theorem B5454539 : Blo 956588 5454539 := bstep (se 1 (by rfl) ⟨4090904, by rfl⟩ : syracuseStep 5454539 = 8181809) B8181809
theorem B16628503 : Blo 956588 16628503 := bstep (se 1 (by rfl) ⟨12471377, by rfl⟩ : syracuseStep 16628503 = 24942755) B24942755
theorem B5455997 : Blo 956588 5455997 := bstep (se 3 (by rfl) ⟨1022999, by rfl⟩ : syracuseStep 5455997 = 2045999) B2045999
theorem B7389463 : Blo 956588 7389463 := bstep (se 1 (by rfl) ⟨5542097, by rfl⟩ : syracuseStep 7389463 = 11084195) B11084195
theorem B62112167 : Blo 956588 62112167 := bstep (se 1 (by rfl) ⟨46584125, by rfl⟩ : syracuseStep 62112167 = 93168251) B93168251
theorem B157631305 : Blo 956588 157631305 := bstep (se 2 (by rfl) ⟨59111739, by rfl⟩ : syracuseStep 157631305 = 118223479) B118223479
theorem B6570875 : Blo 956588 6570875 := bstep (se 1 (by rfl) ⟨4928156, by rfl⟩ : syracuseStep 6570875 = 9856313) B9856313
theorem B3228605 : Blo 956588 3228605 := bstep (se 3 (by rfl) ⟨605363, by rfl⟩ : syracuseStep 3228605 = 1210727) B1210727
theorem B5456929 : Blo 956588 5456929 := bstep (se 2 (by rfl) ⟨2046348, by rfl⟩ : syracuseStep 5456929 = 4092697) B4092697
theorem B3228713 : Blo 956588 3228713 := bstep (se 2 (by rfl) ⟨1210767, by rfl⟩ : syracuseStep 3228713 = 2421535) B2421535
theorem B3228767 : Blo 956588 3228767 := bstep (se 1 (by rfl) ⟨2421575, by rfl⟩ : syracuseStep 3228767 = 4843151) B4843151
theorem B1820207 : Blo 956588 1820207 := bstep (se 1 (by rfl) ⟨1365155, by rfl⟩ : syracuseStep 1820207 = 2730311) B2730311
theorem B8178083 : Blo 956588 8178083 := bstep (se 1 (by rfl) ⟨6133562, by rfl⟩ : syracuseStep 8178083 = 12267125) B12267125
theorem B10930625 : Blo 956588 10930625 := bstep (se 2 (by rfl) ⟨4098984, by rfl⟩ : syracuseStep 10930625 = 8197969) B8197969
theorem B3230333 : Blo 956588 3230333 := bstep (se 3 (by rfl) ⟨605687, by rfl⟩ : syracuseStep 3230333 = 1211375) B1211375
theorem B3230441 : Blo 956588 3230441 := bstep (se 2 (by rfl) ⟨1211415, by rfl⟩ : syracuseStep 3230441 = 2422831) B2422831
theorem B3230495 : Blo 956588 3230495 := bstep (se 1 (by rfl) ⟨2422871, by rfl⟩ : syracuseStep 3230495 = 4845743) B4845743
theorem B3460279 : Blo 956588 3460279 := bstep (se 1 (by rfl) ⟨2595209, by rfl⟩ : syracuseStep 3460279 = 5190419) B5190419
theorem B5819903 : Blo 956588 5819903 := bstep (se 1 (by rfl) ⟨4364927, by rfl⟩ : syracuseStep 5819903 = 8729855) B8729855
theorem B8736281 : Blo 956588 8736281 := bstep (se 2 (by rfl) ⟨3276105, by rfl⟩ : syracuseStep 8736281 = 6552211) B6552211
theorem B3231575 : Blo 956588 3231575 := bstep (se 1 (by rfl) ⟨2423681, by rfl⟩ : syracuseStep 3231575 = 4847363) B4847363
theorem B3231737 : Blo 956588 3231737 := bstep (se 2 (by rfl) ⟨1211901, by rfl⟩ : syracuseStep 3231737 = 2423803) B2423803
theorem B3231791 : Blo 956588 3231791 := bstep (se 1 (by rfl) ⟨2423843, by rfl⟩ : syracuseStep 3231791 = 4847687) B4847687
theorem B1364791 : Blo 956588 1364791 := bstep (se 1 (by rfl) ⟨1023593, by rfl⟩ : syracuseStep 1364791 = 2047187) B2047187
theorem B5461303 : Blo 956588 5461303 := bstep (se 1 (by rfl) ⟨4095977, by rfl⟩ : syracuseStep 5461303 = 8191955) B8191955
theorem B29874107 : Blo 956588 29874107 := bstep (se 1 (by rfl) ⟨22405580, by rfl⟩ : syracuseStep 29874107 = 44811161) B44811161
theorem B2152655 : Blo 956588 2152655 := bstep (se 1 (by rfl) ⟨1614491, by rfl⟩ : syracuseStep 2152655 = 3228983) B3228983
theorem B3234167 : Blo 956588 3234167 := bstep (se 1 (by rfl) ⟨2425625, by rfl⟩ : syracuseStep 3234167 = 4851251) B4851251
theorem B2153195 : Blo 956588 2153195 := bstep (se 1 (by rfl) ⟨1614896, by rfl⟩ : syracuseStep 2153195 = 3229793) B3229793
theorem B5921855 : Blo 956588 5921855 := bstep (se 1 (by rfl) ⟨4441391, by rfl⟩ : syracuseStep 5921855 = 8882783) B8882783
theorem B2153807 : Blo 956588 2153807 := bstep (se 1 (by rfl) ⟨1615355, by rfl⟩ : syracuseStep 2153807 = 3230711) B3230711
theorem B12279275 : Blo 956588 12279275 := bstep (se 1 (by rfl) ⟨9209456, by rfl⟩ : syracuseStep 12279275 = 18418913) B18418913
theorem B9330319 : Blo 956588 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B18669655 : Blo 956588 18669655 := bstep (se 1 (by rfl) ⟨14002241, by rfl⟩ : syracuseStep 18669655 = 28004483) B28004483
theorem B5464493 : Blo 956588 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B2155859 : Blo 956588 2155859 := bstep (se 1 (by rfl) ⟨1616894, by rfl⟩ : syracuseStep 2155859 = 3233789) B3233789
theorem B7759351 : Blo 956588 7759351 := bstep (se 1 (by rfl) ⟨5819513, by rfl⟩ : syracuseStep 7759351 = 11639027) B11639027
theorem B1435367 : Blo 956588 1435367 := bstep (se 1 (by rfl) ⟨1076525, by rfl⟩ : syracuseStep 1435367 = 2153051) B2153051
theorem B5826329 : Blo 956588 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B2156795 : Blo 956588 2156795 := bstep (se 1 (by rfl) ⟨1617596, by rfl⟩ : syracuseStep 2156795 = 3235193) B3235193
theorem B2157263 : Blo 956588 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B2157353 : Blo 956588 2157353 := bstep (se 2 (by rfl) ⟨809007, by rfl⟩ : syracuseStep 2157353 = 1618015) B1618015
theorem B1076251 : Blo 956588 1076251 := bstep (se 1 (by rfl) ⟨807188, by rfl⟩ : syracuseStep 1076251 = 1614377) B1614377
theorem B1436699 : Blo 956588 1436699 := bstep (se 1 (by rfl) ⟨1077524, by rfl⟩ : syracuseStep 1436699 = 2155049) B2155049
theorem B13102181 : Blo 956588 13102181 := bstep (se 4 (by rfl) ⟨1228329, by rfl⟩ : syracuseStep 13102181 = 2456659) B2456659
theorem B1436903 : Blo 956588 1436903 := bstep (se 1 (by rfl) ⟨1077677, by rfl⟩ : syracuseStep 1436903 = 2155355) B2155355
theorem B2157803 : Blo 956588 2157803 := bstep (se 1 (by rfl) ⟨1618352, by rfl⟩ : syracuseStep 2157803 = 3236705) B3236705
theorem B4615649 : Blo 956588 4615649 := bstep (se 2 (by rfl) ⟨1730868, by rfl⟩ : syracuseStep 4615649 = 3461737) B3461737
theorem B2158055 : Blo 956588 2158055 := bstep (se 1 (by rfl) ⟨1618541, by rfl⟩ : syracuseStep 2158055 = 3237083) B3237083
theorem B1076719 : Blo 956588 1076719 := bstep (se 1 (by rfl) ⟨807539, by rfl⟩ : syracuseStep 1076719 = 1615079) B1615079
theorem B3239567 : Blo 956588 3239567 := bstep (se 1 (by rfl) ⟨2429675, by rfl⟩ : syracuseStep 3239567 = 4859351) B4859351
theorem B1437551 : Blo 956588 1437551 := bstep (se 1 (by rfl) ⟨1078163, by rfl⟩ : syracuseStep 1437551 = 2156327) B2156327
theorem B36925307 : Blo 956588 36925307 := bstep (se 1 (by rfl) ⟨27693980, by rfl⟩ : syracuseStep 36925307 = 55387961) B55387961
theorem B1437599 : Blo 956588 1437599 := bstep (se 1 (by rfl) ⟨1078199, by rfl⟩ : syracuseStep 1437599 = 2156399) B2156399
theorem B2158631 : Blo 956588 2158631 := bstep (se 1 (by rfl) ⟨1618973, by rfl⟩ : syracuseStep 2158631 = 3237947) B3237947
theorem B4845905 : Blo 956588 4845905 := bstep (se 2 (by rfl) ⟨1817214, by rfl⟩ : syracuseStep 4845905 = 3634429) B3634429
theorem B2159009 : Blo 956588 2159009 := bstep (se 2 (by rfl) ⟨809628, by rfl⟩ : syracuseStep 2159009 = 1619257) B1619257
theorem B8745403 : Blo 956588 8745403 := bstep (se 1 (by rfl) ⟨6559052, by rfl⟩ : syracuseStep 8745403 = 13118105) B13118105
theorem B2159081 : Blo 956588 2159081 := bstep (se 2 (by rfl) ⟨809655, by rfl⟩ : syracuseStep 2159081 = 1619311) B1619311
theorem B1438415 : Blo 956588 1438415 := bstep (se 1 (by rfl) ⟨1078811, by rfl⟩ : syracuseStep 1438415 = 2157623) B2157623
theorem B13824847 : Blo 956588 13824847 := bstep (se 1 (by rfl) ⟨10368635, by rfl⟩ : syracuseStep 13824847 = 20737271) B20737271
theorem B7762985 : Blo 956588 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B10908755 : Blo 956588 10908755 := bstep (se 1 (by rfl) ⟨8181566, by rfl⟩ : syracuseStep 10908755 = 16363133) B16363133
theorem B1078375 : Blo 956588 1078375 := bstep (se 1 (by rfl) ⟨808781, by rfl⟩ : syracuseStep 1078375 = 1617563) B1617563
theorem B13792679 : Blo 956588 13792679 := bstep (se 1 (by rfl) ⟨10344509, by rfl⟩ : syracuseStep 13792679 = 20689019) B20689019
theorem B2160107 : Blo 956588 2160107 := bstep (se 1 (by rfl) ⟨1620080, by rfl⟩ : syracuseStep 2160107 = 3240161) B3240161
theorem B2160467 : Blo 956588 2160467 := bstep (se 1 (by rfl) ⟨1620350, by rfl⟩ : syracuseStep 2160467 = 3240701) B3240701
theorem B2160575 : Blo 956588 2160575 := bstep (se 1 (by rfl) ⟨1620431, by rfl⟩ : syracuseStep 2160575 = 3240863) B3240863
theorem B2422811 : Blo 956588 2422811 := bstep (se 1 (by rfl) ⟨1817108, by rfl⟩ : syracuseStep 2422811 = 3634217) B3634217
theorem B9959753 : Blo 956588 9959753 := bstep (se 2 (by rfl) ⟨3734907, by rfl⟩ : syracuseStep 9959753 = 7469815) B7469815
theorem B9206723 : Blo 956588 9206723 := bstep (se 1 (by rfl) ⟨6905042, by rfl⟩ : syracuseStep 9206723 = 13810085) B13810085
theorem B6650819 : Blo 956588 6650819 := bstep (se 1 (by rfl) ⟨4988114, by rfl⟩ : syracuseStep 6650819 = 9976229) B9976229
theorem B2423915 : Blo 956588 2423915 := bstep (se 1 (by rfl) ⟨1817936, by rfl⟩ : syracuseStep 2423915 = 3635873) B3635873
theorem B4848983 : Blo 956588 4848983 := bstep (se 1 (by rfl) ⟨3636737, by rfl⟩ : syracuseStep 4848983 = 7273475) B7273475
theorem B291733073 : Blo 956588 291733073 := bstep (se 2 (by rfl) ⟨109399902, by rfl⟩ : syracuseStep 291733073 = 218799805) B218799805
theorem B39353971 : Blo 956588 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B4849307 : Blo 956588 4849307 := bstep (se 1 (by rfl) ⟨3636980, by rfl⟩ : syracuseStep 4849307 = 7273961) B7273961
theorem B3637331 : Blo 956588 3637331 := bstep (se 1 (by rfl) ⟨2727998, by rfl⟩ : syracuseStep 3637331 = 5455997) B5455997
theorem B1213471 : Blo 956588 1213471 := bstep (se 1 (by rfl) ⟨910103, by rfl⟩ : syracuseStep 1213471 = 1820207) B1820207
theorem B210175073 : Blo 956588 210175073 := bstep (se 2 (by rfl) ⟨78815652, by rfl⟩ : syracuseStep 210175073 = 157631305) B157631305
theorem B7275905 : Blo 956588 7275905 := bstep (se 2 (by rfl) ⟨2728464, by rfl⟩ : syracuseStep 7275905 = 5456929) B5456929
theorem B52562837 : Blo 956588 52562837 := bstep (se 6 (by rfl) ⟨1231941, by rfl⟩ : syracuseStep 52562837 = 2463883) B2463883
theorem B2427995 : Blo 956588 2427995 := bstep (se 1 (by rfl) ⟨1820996, by rfl⟩ : syracuseStep 2427995 = 3641993) B3641993
theorem B49812191 : Blo 956588 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B79664285 : Blo 956588 79664285 := bstep (se 3 (by rfl) ⟨14937053, by rfl⟩ : syracuseStep 79664285 = 29874107) B29874107
theorem B3642995 : Blo 956588 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B2430607 : Blo 956588 2430607 := bstep (se 1 (by rfl) ⟨1822955, by rfl⟩ : syracuseStep 2430607 = 3645911) B3645911
theorem B4855463 : Blo 956588 4855463 := bstep (se 1 (by rfl) ⟨3641597, by rfl⟩ : syracuseStep 4855463 = 7283195) B7283195
theorem B2300375 : Blo 956588 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B956911 : Blo 956588 956911 := bstep (se 1 (by rfl) ⟨717683, by rfl⟩ : syracuseStep 956911 = 1435367) B1435367
theorem B27630557 : Blo 956588 27630557 := bstep (se 3 (by rfl) ⟨5180729, by rfl⟩ : syracuseStep 27630557 = 10361459) B10361459
theorem B7281737 : Blo 956588 7281737 := bstep (se 2 (by rfl) ⟨2730651, by rfl⟩ : syracuseStep 7281737 = 5461303) B5461303
theorem B4857083 : Blo 956588 4857083 := bstep (se 1 (by rfl) ⟨3642812, by rfl⟩ : syracuseStep 4857083 = 7285625) B7285625
theorem B957799 : Blo 956588 957799 := bstep (se 1 (by rfl) ⟨718349, by rfl⟩ : syracuseStep 957799 = 1436699) B1436699
theorem B957935 : Blo 956588 957935 := bstep (se 1 (by rfl) ⟨718451, by rfl⟩ : syracuseStep 957935 = 1436903) B1436903
theorem B4857569 : Blo 956588 4857569 := bstep (se 2 (by rfl) ⟨1821588, by rfl⟩ : syracuseStep 4857569 = 3643177) B3643177
theorem B24551261 : Blo 956588 24551261 := bstep (se 3 (by rfl) ⟨4603361, by rfl⟩ : syracuseStep 24551261 = 9206723) B9206723
theorem B958367 : Blo 956588 958367 := bstep (se 1 (by rfl) ⟨718775, by rfl⟩ : syracuseStep 958367 = 1437551) B1437551
theorem B24616871 : Blo 956588 24616871 := bstep (se 1 (by rfl) ⟨18462653, by rfl⟩ : syracuseStep 24616871 = 36925307) B36925307
theorem B958399 : Blo 956588 958399 := bstep (se 1 (by rfl) ⟨718799, by rfl⟩ : syracuseStep 958399 = 1437599) B1437599
theorem B958943 : Blo 956588 958943 := bstep (se 1 (by rfl) ⟨719207, by rfl⟩ : syracuseStep 958943 = 1438415) B1438415
theorem B2302519 : Blo 956588 2302519 := bstep (se 1 (by rfl) ⟨1726889, by rfl⟩ : syracuseStep 2302519 = 3453779) B3453779
theorem B23667365 : Blo 956588 23667365 := bstep (se 4 (by rfl) ⟨2218815, by rfl⟩ : syracuseStep 23667365 = 4437631) B4437631
theorem B1615207 : Blo 956588 1615207 := bstep (se 1 (by rfl) ⟨1211405, by rfl⟩ : syracuseStep 1615207 = 2422811) B2422811
theorem B4433879 : Blo 956588 4433879 := bstep (se 1 (by rfl) ⟨3325409, by rfl⟩ : syracuseStep 4433879 = 6650819) B6650819
theorem B1615943 : Blo 956588 1615943 := bstep (se 1 (by rfl) ⟨1211957, by rfl⟩ : syracuseStep 1615943 = 2423915) B2423915
theorem B52471961 : Blo 956588 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B194488715 : Blo 956588 194488715 := bstep (se 1 (by rfl) ⟨145866536, by rfl⟩ : syracuseStep 194488715 = 291733073) B291733073
theorem B54012521 : Blo 956588 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B1616807 : Blo 956588 1616807 := bstep (se 1 (by rfl) ⟨1212605, by rfl⟩ : syracuseStep 1616807 = 2425211) B2425211
theorem B9219025 : Blo 956588 9219025 := bstep (se 2 (by rfl) ⟨3457134, by rfl⟩ : syracuseStep 9219025 = 6914269) B6914269
theorem B7778035 : Blo 956588 7778035 := bstep (se 1 (by rfl) ⟨5833526, by rfl⟩ : syracuseStep 7778035 = 11667053) B11667053
theorem B5452055 : Blo 956588 5452055 := bstep (se 1 (by rfl) ⟨4089041, by rfl⟩ : syracuseStep 5452055 = 8178083) B8178083
theorem B7287083 : Blo 956588 7287083 := bstep (se 1 (by rfl) ⟨5465312, by rfl⟩ : syracuseStep 7287083 = 10930625) B10930625
theorem B3879935 : Blo 956588 3879935 := bstep (se 1 (by rfl) ⟨2909951, by rfl⟩ : syracuseStep 3879935 = 5819903) B5819903
theorem B3454483 : Blo 956588 3454483 := bstep (se 1 (by rfl) ⟨2590862, by rfl⟩ : syracuseStep 3454483 = 5181725) B5181725
theorem B13121453 : Blo 956588 13121453 := bstep (se 3 (by rfl) ⟨2460272, by rfl⟩ : syracuseStep 13121453 = 4920545) B4920545
theorem B3455867 : Blo 956588 3455867 := bstep (se 1 (by rfl) ⟨2591900, by rfl⟩ : syracuseStep 3455867 = 5183801) B5183801
theorem B24919073 : Blo 956588 24919073 := bstep (se 2 (by rfl) ⟨9344652, by rfl⟩ : syracuseStep 24919073 = 18689305) B18689305
theorem B3947903 : Blo 956588 3947903 := bstep (se 1 (by rfl) ⟨2960927, by rfl⟩ : syracuseStep 3947903 = 5921855) B5921855
theorem B30294233 : Blo 956588 30294233 := bstep (se 2 (by rfl) ⟨11360337, by rfl⟩ : syracuseStep 30294233 = 22720675) B22720675
theorem B10929167 : Blo 956588 10929167 := bstep (se 1 (by rfl) ⟨8196875, by rfl⟩ : syracuseStep 10929167 = 16393751) B16393751
theorem B1819721 : Blo 956588 1819721 := bstep (se 2 (by rfl) ⟨682395, by rfl⟩ : syracuseStep 1819721 = 1364791) B1364791
theorem B18433129 : Blo 956588 18433129 := bstep (se 2 (by rfl) ⟨6912423, by rfl⟩ : syracuseStep 18433129 = 13824847) B13824847
theorem B3884219 : Blo 956588 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B14173865 : Blo 956588 14173865 := bstep (se 2 (by rfl) ⟨5315199, by rfl⟩ : syracuseStep 14173865 = 10630399) B10630399
theorem B8734787 : Blo 956588 8734787 := bstep (se 1 (by rfl) ⟨6551090, by rfl⟩ : syracuseStep 8734787 = 13102181) B13102181
theorem B3066167 : Blo 956588 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B3230603 : Blo 956588 3230603 := bstep (se 1 (by rfl) ⟨2422952, by rfl⟩ : syracuseStep 3230603 = 4845905) B4845905
theorem B49761701 : Blo 956588 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B9195119 : Blo 956588 9195119 := bstep (se 1 (by rfl) ⟨6896339, by rfl⟩ : syracuseStep 9195119 = 13792679) B13792679
theorem B22171337 : Blo 956588 22171337 := bstep (se 2 (by rfl) ⟨8314251, by rfl⟩ : syracuseStep 22171337 = 16628503) B16628503
theorem B1822439 : Blo 956588 1822439 := bstep (se 1 (by rfl) ⟨1366829, by rfl⟩ : syracuseStep 1822439 = 2733659) B2733659
theorem B1822675 : Blo 956588 1822675 := bstep (se 1 (by rfl) ⟨1367006, by rfl⟩ : syracuseStep 1822675 = 2734013) B2734013
theorem B3461231 : Blo 956588 3461231 := bstep (se 1 (by rfl) ⟨2595923, by rfl⟩ : syracuseStep 3461231 = 5191847) B5191847
theorem B6639835 : Blo 956588 6639835 := bstep (se 1 (by rfl) ⟨4979876, by rfl⟩ : syracuseStep 6639835 = 9959753) B9959753
theorem B3232655 : Blo 956588 3232655 := bstep (se 1 (by rfl) ⟨2424491, by rfl⟩ : syracuseStep 3232655 = 4848983) B4848983
theorem B3232871 : Blo 956588 3232871 := bstep (se 1 (by rfl) ⟨2424653, by rfl⟩ : syracuseStep 3232871 = 4849307) B4849307
theorem B12277271 : Blo 956588 12277271 := bstep (se 1 (by rfl) ⟨9207953, by rfl⟩ : syracuseStep 12277271 = 18415907) B18415907
theorem B41408111 : Blo 956588 41408111 := bstep (se 1 (by rfl) ⟨31056083, by rfl⟩ : syracuseStep 41408111 = 62112167) B62112167
theorem B9852617 : Blo 956588 9852617 := bstep (se 2 (by rfl) ⟨3694731, by rfl⟩ : syracuseStep 9852617 = 7389463) B7389463
theorem B99571493 : Blo 956588 99571493 := bstep (se 4 (by rfl) ⟨9334827, by rfl⟩ : syracuseStep 99571493 = 18669655) B18669655
theorem B4380583 : Blo 956588 4380583 := bstep (se 1 (by rfl) ⟨3285437, by rfl⟩ : syracuseStep 4380583 = 6570875) B6570875
theorem B2152403 : Blo 956588 2152403 := bstep (se 1 (by rfl) ⟨1614302, by rfl⟩ : syracuseStep 2152403 = 3228605) B3228605
theorem B2152475 : Blo 956588 2152475 := bstep (se 1 (by rfl) ⟨1614356, by rfl⟩ : syracuseStep 2152475 = 3228713) B3228713
theorem B2152511 : Blo 956588 2152511 := bstep (se 1 (by rfl) ⟨1614383, by rfl⟩ : syracuseStep 2152511 = 3228767) B3228767
theorem B55269863 : Blo 956588 55269863 := bstep (se 1 (by rfl) ⟨41452397, by rfl⟩ : syracuseStep 55269863 = 82904795) B82904795
theorem B2153555 : Blo 956588 2153555 := bstep (se 1 (by rfl) ⟨1615166, by rfl⟩ : syracuseStep 2153555 = 3230333) B3230333
theorem B2153627 : Blo 956588 2153627 := bstep (se 1 (by rfl) ⟨1615220, by rfl⟩ : syracuseStep 2153627 = 3230441) B3230441
theorem B2153663 : Blo 956588 2153663 := bstep (se 1 (by rfl) ⟨1615247, by rfl⟩ : syracuseStep 2153663 = 3230495) B3230495
theorem B10345801 : Blo 956588 10345801 := bstep (se 2 (by rfl) ⟨3879675, by rfl⟩ : syracuseStep 10345801 = 7759351) B7759351
theorem B3235247 : Blo 956588 3235247 := bstep (se 1 (by rfl) ⟨2426435, by rfl⟩ : syracuseStep 3235247 = 4852871) B4852871
theorem B5824187 : Blo 956588 5824187 := bstep (se 1 (by rfl) ⟨4368140, by rfl⟩ : syracuseStep 5824187 = 8736281) B8736281
theorem B2154383 : Blo 956588 2154383 := bstep (se 1 (by rfl) ⟨1615787, by rfl⟩ : syracuseStep 2154383 = 3231575) B3231575
theorem B2154491 : Blo 956588 2154491 := bstep (se 1 (by rfl) ⟨1615868, by rfl⟩ : syracuseStep 2154491 = 3231737) B3231737
theorem B2154527 : Blo 956588 2154527 := bstep (se 1 (by rfl) ⟨1615895, by rfl⟩ : syracuseStep 2154527 = 3231791) B3231791
theorem B1435001 : Blo 956588 1435001 := bstep (se 2 (by rfl) ⟨538125, by rfl⟩ : syracuseStep 1435001 = 1076251) B1076251
theorem B1435103 : Blo 956588 1435103 := bstep (se 1 (by rfl) ⟨1076327, by rfl⟩ : syracuseStep 1435103 = 2152655) B2152655
theorem B4613705 : Blo 956588 4613705 := bstep (se 2 (by rfl) ⟨1730139, by rfl⟩ : syracuseStep 4613705 = 3460279) B3460279
theorem B2156111 : Blo 956588 2156111 := bstep (se 1 (by rfl) ⟨1617083, by rfl⟩ : syracuseStep 2156111 = 3234167) B3234167
theorem B3237623 : Blo 956588 3237623 := bstep (se 1 (by rfl) ⟨2428217, by rfl⟩ : syracuseStep 3237623 = 4856435) B4856435
theorem B1435463 : Blo 956588 1435463 := bstep (se 1 (by rfl) ⟨1076597, by rfl⟩ : syracuseStep 1435463 = 2153195) B2153195
theorem B1435625 : Blo 956588 1435625 := bstep (se 2 (by rfl) ⟨538359, by rfl⟩ : syracuseStep 1435625 = 1076719) B1076719
theorem B1435871 : Blo 956588 1435871 := bstep (se 1 (by rfl) ⟨1076903, by rfl⟩ : syracuseStep 1435871 = 2153807) B2153807
theorem B8186183 : Blo 956588 8186183 := bstep (se 1 (by rfl) ⟨6139637, by rfl⟩ : syracuseStep 8186183 = 12279275) B12279275
theorem B23358239 : Blo 956588 23358239 := bstep (se 1 (by rfl) ⟨17518679, by rfl⟩ : syracuseStep 23358239 = 35037359) B35037359
theorem B11660537 : Blo 956588 11660537 := bstep (se 2 (by rfl) ⟨4372701, by rfl⟩ : syracuseStep 11660537 = 8745403) B8745403
theorem B1437239 : Blo 956588 1437239 := bstep (se 1 (by rfl) ⟨1077929, by rfl⟩ : syracuseStep 1437239 = 2155859) B2155859
theorem B2158505 : Blo 956588 2158505 := bstep (se 2 (by rfl) ⟨809439, by rfl⟩ : syracuseStep 2158505 = 1618879) B1618879
theorem B15560747 : Blo 956588 15560747 := bstep (se 1 (by rfl) ⟨11670560, by rfl⟩ : syracuseStep 15560747 = 23341121) B23341121
theorem B1437833 : Blo 956588 1437833 := bstep (se 2 (by rfl) ⟨539187, by rfl⟩ : syracuseStep 1437833 = 1078375) B1078375
theorem B1437863 : Blo 956588 1437863 := bstep (se 1 (by rfl) ⟨1078397, by rfl⟩ : syracuseStep 1437863 = 2156795) B2156795
theorem B1438175 : Blo 956588 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B1438235 : Blo 956588 1438235 := bstep (se 1 (by rfl) ⟨1078676, by rfl⟩ : syracuseStep 1438235 = 2157353) B2157353
theorem B1438535 : Blo 956588 1438535 := bstep (se 1 (by rfl) ⟨1078901, by rfl⟩ : syracuseStep 1438535 = 2157803) B2157803
theorem B3077099 : Blo 956588 3077099 := bstep (se 1 (by rfl) ⟨2307824, by rfl⟩ : syracuseStep 3077099 = 4615649) B4615649
theorem B1438703 : Blo 956588 1438703 := bstep (se 1 (by rfl) ⟨1079027, by rfl⟩ : syracuseStep 1438703 = 2158055) B2158055
theorem B1078303 : Blo 956588 1078303 := bstep (se 1 (by rfl) ⟨808727, by rfl⟩ : syracuseStep 1078303 = 1617455) B1617455
theorem B2159711 : Blo 956588 2159711 := bstep (se 1 (by rfl) ⟨1619783, by rfl⟩ : syracuseStep 2159711 = 3239567) B3239567
theorem B1439087 : Blo 956588 1439087 := bstep (se 1 (by rfl) ⟨1079315, by rfl⟩ : syracuseStep 1439087 = 2158631) B2158631
theorem B1439339 : Blo 956588 1439339 := bstep (se 1 (by rfl) ⟨1079504, by rfl⟩ : syracuseStep 1439339 = 2159009) B2159009
theorem B1439387 : Blo 956588 1439387 := bstep (se 1 (by rfl) ⟨1079540, by rfl⟩ : syracuseStep 1439387 = 2159081) B2159081
theorem B18675593 : Blo 956588 18675593 := bstep (se 2 (by rfl) ⟨7003347, by rfl⟩ : syracuseStep 18675593 = 14006695) B14006695
theorem B5175323 : Blo 956588 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B7272503 : Blo 956588 7272503 := bstep (se 1 (by rfl) ⟨5454377, by rfl⟩ : syracuseStep 7272503 = 10908755) B10908755
theorem B1440071 : Blo 956588 1440071 := bstep (se 1 (by rfl) ⟨1080053, by rfl⟩ : syracuseStep 1440071 = 2160107) B2160107
theorem B1079707 : Blo 956588 1079707 := bstep (se 1 (by rfl) ⟨809780, by rfl⟩ : syracuseStep 1079707 = 1619561) B1619561
theorem B1440311 : Blo 956588 1440311 := bstep (se 1 (by rfl) ⟨1080233, by rfl⟩ : syracuseStep 1440311 = 2160467) B2160467
theorem B1440383 : Blo 956588 1440383 := bstep (se 1 (by rfl) ⟨1080287, by rfl⟩ : syracuseStep 1440383 = 2160575) B2160575
theorem B3636191 : Blo 956588 3636191 := bstep (se 1 (by rfl) ⟨2727143, by rfl⟩ : syracuseStep 3636191 = 5454287) B5454287
theorem B3636359 : Blo 956588 3636359 := bstep (se 1 (by rfl) ⟨2727269, by rfl⟩ : syracuseStep 3636359 = 5454539) B5454539
theorem B2424887 : Blo 956588 2424887 := bstep (se 1 (by rfl) ⟨1818665, by rfl⟩ : syracuseStep 2424887 = 3637331) B3637331
theorem B1213147 : Blo 956588 1213147 := bstep (se 1 (by rfl) ⟨909860, by rfl⟩ : syracuseStep 1213147 = 1819721) B1819721
theorem B140116715 : Blo 956588 140116715 := bstep (se 1 (by rfl) ⟨105087536, by rfl⟩ : syracuseStep 140116715 = 210175073) B210175073
theorem B2589479 : Blo 956588 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B4850603 : Blo 956588 4850603 := bstep (se 1 (by rfl) ⟨3637952, by rfl⟩ : syracuseStep 4850603 = 7275905) B7275905
theorem B24577505 : Blo 956588 24577505 := bstep (se 2 (by rfl) ⟨9216564, by rfl⟩ : syracuseStep 24577505 = 18433129) B18433129
theorem B6130079 : Blo 956588 6130079 := bstep (se 1 (by rfl) ⟨4597559, by rfl⟩ : syracuseStep 6130079 = 9195119) B9195119
theorem B14780891 : Blo 956588 14780891 := bstep (se 1 (by rfl) ⟨11085668, by rfl⟩ : syracuseStep 14780891 = 22171337) B22171337
theorem B2428663 : Blo 956588 2428663 := bstep (se 1 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 2428663 = 3642995) B3642995
theorem B12292033 : Blo 956588 12292033 := bstep (se 2 (by rfl) ⟨4609512, by rfl⟩ : syracuseStep 12292033 = 9219025) B9219025
theorem B18420371 : Blo 956588 18420371 := bstep (se 1 (by rfl) ⟨13815278, by rfl⟩ : syracuseStep 18420371 = 27630557) B27630557
theorem B4854491 : Blo 956588 4854491 := bstep (se 1 (by rfl) ⟨3640868, by rfl⟩ : syracuseStep 4854491 = 7281737) B7281737
theorem B2430233 : Blo 956588 2430233 := bstep (se 2 (by rfl) ⟨911337, by rfl⟩ : syracuseStep 2430233 = 1822675) B1822675
theorem B8853113 : Blo 956588 8853113 := bstep (se 2 (by rfl) ⟨3319917, by rfl⟩ : syracuseStep 8853113 = 6639835) B6639835
theorem B956667 : Blo 956588 956667 := bstep (se 1 (by rfl) ⟨717500, by rfl⟩ : syracuseStep 956667 = 1435001) B1435001
theorem B956735 : Blo 956588 956735 := bstep (se 1 (by rfl) ⟨717551, by rfl⟩ : syracuseStep 956735 = 1435103) B1435103
theorem B956975 : Blo 956588 956975 := bstep (se 1 (by rfl) ⟨717731, by rfl⟩ : syracuseStep 956975 = 1435463) B1435463
theorem B2955919 : Blo 956588 2955919 := bstep (se 1 (by rfl) ⟨2216939, by rfl⟩ : syracuseStep 2955919 = 4433879) B4433879
theorem B957083 : Blo 956588 957083 := bstep (se 1 (by rfl) ⟨717812, by rfl⟩ : syracuseStep 957083 = 1435625) B1435625
theorem B957247 : Blo 956588 957247 := bstep (se 1 (by rfl) ⟨717935, by rfl⟩ : syracuseStep 957247 = 1435871) B1435871
theorem B15572159 : Blo 956588 15572159 := bstep (se 1 (by rfl) ⟨11679119, by rfl⟩ : syracuseStep 15572159 = 23358239) B23358239
theorem B958159 : Blo 956588 958159 := bstep (se 1 (by rfl) ⟨718619, by rfl⟩ : syracuseStep 958159 = 1437239) B1437239
theorem B5840777 : Blo 956588 5840777 := bstep (se 2 (by rfl) ⟨2190291, by rfl⟩ : syracuseStep 5840777 = 4380583) B4380583
theorem B958555 : Blo 956588 958555 := bstep (se 1 (by rfl) ⟨718916, by rfl⟩ : syracuseStep 958555 = 1437833) B1437833
theorem B958575 : Blo 956588 958575 := bstep (se 1 (by rfl) ⟨718931, by rfl⟩ : syracuseStep 958575 = 1437863) B1437863
theorem B4858055 : Blo 956588 4858055 := bstep (se 1 (by rfl) ⟨3643541, by rfl⟩ : syracuseStep 4858055 = 7287083) B7287083
theorem B958783 : Blo 956588 958783 := bstep (se 1 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 958783 = 1438175) B1438175
theorem B958823 : Blo 956588 958823 := bstep (se 1 (by rfl) ⟨719117, by rfl⟩ : syracuseStep 958823 = 1438235) B1438235
theorem B959023 : Blo 956588 959023 := bstep (se 1 (by rfl) ⟨719267, by rfl⟩ : syracuseStep 959023 = 1438535) B1438535
theorem B959135 : Blo 956588 959135 := bstep (se 1 (by rfl) ⟨719351, by rfl⟩ : syracuseStep 959135 = 1438703) B1438703
theorem B959391 : Blo 956588 959391 := bstep (se 1 (by rfl) ⟨719543, by rfl⟩ : syracuseStep 959391 = 1439087) B1439087
theorem B959559 : Blo 956588 959559 := bstep (se 1 (by rfl) ⟨719669, by rfl⟩ : syracuseStep 959559 = 1439339) B1439339
theorem B959591 : Blo 956588 959591 := bstep (se 1 (by rfl) ⟨719693, by rfl⟩ : syracuseStep 959591 = 1439387) B1439387
theorem B3450215 : Blo 956588 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B960047 : Blo 956588 960047 := bstep (se 1 (by rfl) ⟨720035, by rfl⟩ : syracuseStep 960047 = 1440071) B1440071
theorem B960207 : Blo 956588 960207 := bstep (se 1 (by rfl) ⟨720155, by rfl⟩ : syracuseStep 960207 = 1440311) B1440311
theorem B960255 : Blo 956588 960255 := bstep (se 1 (by rfl) ⟨720191, by rfl⟩ : syracuseStep 960255 = 1440383) B1440383
theorem B2303911 : Blo 956588 2303911 := bstep (se 1 (by rfl) ⟨1727933, by rfl⟩ : syracuseStep 2303911 = 3455867) B3455867
theorem B4859837 : Blo 956588 4859837 := bstep (se 3 (by rfl) ⟨911219, by rfl⟩ : syracuseStep 4859837 = 1822439) B1822439
theorem B2631935 : Blo 956588 2631935 := bstep (se 1 (by rfl) ⟨1973951, by rfl⟩ : syracuseStep 2631935 = 3947903) B3947903
theorem B20196155 : Blo 956588 20196155 := bstep (se 1 (by rfl) ⟨15147116, by rfl⟩ : syracuseStep 20196155 = 30294233) B30294233
theorem B7286111 : Blo 956588 7286111 := bstep (se 1 (by rfl) ⟨5464583, by rfl⟩ : syracuseStep 7286111 = 10929167) B10929167
theorem B9449243 : Blo 956588 9449243 := bstep (se 1 (by rfl) ⟨7086932, by rfl⟩ : syracuseStep 9449243 = 14173865) B14173865
theorem B1617961 : Blo 956588 1617961 := bstep (se 2 (by rfl) ⟨606735, by rfl⟩ : syracuseStep 1617961 = 1213471) B1213471
theorem B2044111 : Blo 956588 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B35041891 : Blo 956588 35041891 := bstep (se 1 (by rfl) ⟨26281418, by rfl⟩ : syracuseStep 35041891 = 52562837) B52562837
theorem B1618663 : Blo 956588 1618663 := bstep (se 1 (by rfl) ⟨1213997, by rfl⟩ : syracuseStep 1618663 = 2427995) B2427995
theorem B33174467 : Blo 956588 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B2307487 : Blo 956588 2307487 := bstep (se 1 (by rfl) ⟨1730615, by rfl⟩ : syracuseStep 2307487 = 3461231) B3461231
theorem B33208127 : Blo 956588 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B27605407 : Blo 956588 27605407 := bstep (se 1 (by rfl) ⟨20704055, by rfl⟩ : syracuseStep 27605407 = 41408111) B41408111
theorem B6568411 : Blo 956588 6568411 := bstep (se 1 (by rfl) ⟨4926308, by rfl⟩ : syracuseStep 6568411 = 9852617) B9852617
theorem B36846575 : Blo 956588 36846575 := bstep (se 1 (by rfl) ⟨27634931, by rfl⟩ : syracuseStep 36846575 = 55269863) B55269863
theorem B10370713 : Blo 956588 10370713 := bstep (se 2 (by rfl) ⟨3889017, by rfl⟩ : syracuseStep 10370713 = 7778035) B7778035
theorem B3882791 : Blo 956588 3882791 := bstep (se 1 (by rfl) ⟨2912093, by rfl⟩ : syracuseStep 3882791 = 5824187) B5824187
theorem B16367507 : Blo 956588 16367507 := bstep (se 1 (by rfl) ⟨12275630, by rfl⟩ : syracuseStep 16367507 = 24551261) B24551261
theorem B15778243 : Blo 956588 15778243 := bstep (se 1 (by rfl) ⟨11833682, by rfl⟩ : syracuseStep 15778243 = 23667365) B23667365
theorem B34981307 : Blo 956588 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B5457455 : Blo 956588 5457455 := bstep (se 1 (by rfl) ⟨4093091, by rfl⟩ : syracuseStep 5457455 = 8186183) B8186183
theorem B4605977 : Blo 956588 4605977 := bstep (se 2 (by rfl) ⟨1727241, by rfl⟩ : syracuseStep 4605977 = 3454483) B3454483
theorem B10373831 : Blo 956588 10373831 := bstep (se 1 (by rfl) ⟨7780373, by rfl⟩ : syracuseStep 10373831 = 15560747) B15560747
theorem B2051399 : Blo 956588 2051399 := bstep (se 1 (by rfl) ⟨1538549, by rfl⟩ : syracuseStep 2051399 = 3077099) B3077099
theorem B3070025 : Blo 956588 3070025 := bstep (se 2 (by rfl) ⟨1151259, by rfl⟩ : syracuseStep 3070025 = 2302519) B2302519
theorem B5823191 : Blo 956588 5823191 := bstep (se 1 (by rfl) ⟨4367393, by rfl⟩ : syracuseStep 5823191 = 8734787) B8734787
theorem B2153609 : Blo 956588 2153609 := bstep (se 2 (by rfl) ⟨807603, by rfl⟩ : syracuseStep 2153609 = 1615207) B1615207
theorem B2153735 : Blo 956588 2153735 := bstep (se 1 (by rfl) ⟨1615301, by rfl⟩ : syracuseStep 2153735 = 3230603) B3230603
theorem B2155103 : Blo 956588 2155103 := bstep (se 1 (by rfl) ⟨1616327, by rfl⟩ : syracuseStep 2155103 = 3232655) B3232655
theorem B2155247 : Blo 956588 2155247 := bstep (se 1 (by rfl) ⟨1616435, by rfl⟩ : syracuseStep 2155247 = 3232871) B3232871
theorem B53109523 : Blo 956588 53109523 := bstep (se 1 (by rfl) ⟨39832142, by rfl⟩ : syracuseStep 53109523 = 79664285) B79664285
theorem B8184847 : Blo 956588 8184847 := bstep (se 1 (by rfl) ⟨6138635, by rfl⟩ : syracuseStep 8184847 = 12277271) B12277271
theorem B3236975 : Blo 956588 3236975 := bstep (se 1 (by rfl) ⟨2427731, by rfl⟩ : syracuseStep 3236975 = 4855463) B4855463
theorem B66380995 : Blo 956588 66380995 := bstep (se 1 (by rfl) ⟨49785746, by rfl⟩ : syracuseStep 66380995 = 99571493) B99571493
theorem B1434935 : Blo 956588 1434935 := bstep (se 1 (by rfl) ⟨1076201, by rfl⟩ : syracuseStep 1434935 = 2152403) B2152403
theorem B1434983 : Blo 956588 1434983 := bstep (se 1 (by rfl) ⟨1076237, by rfl⟩ : syracuseStep 1434983 = 2152475) B2152475
theorem B1435007 : Blo 956588 1435007 := bstep (se 1 (by rfl) ⟨1076255, by rfl⟩ : syracuseStep 1435007 = 2152511) B2152511
theorem B1533583 : Blo 956588 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B1435703 : Blo 956588 1435703 := bstep (se 1 (by rfl) ⟨1076777, by rfl⟩ : syracuseStep 1435703 = 2153555) B2153555
theorem B1435751 : Blo 956588 1435751 := bstep (se 1 (by rfl) ⟨1076813, by rfl⟩ : syracuseStep 1435751 = 2153627) B2153627
theorem B1435775 : Blo 956588 1435775 := bstep (se 1 (by rfl) ⟨1076831, by rfl⟩ : syracuseStep 1435775 = 2153663) B2153663
theorem B3238055 : Blo 956588 3238055 := bstep (se 1 (by rfl) ⟨2428541, by rfl⟩ : syracuseStep 3238055 = 4857083) B4857083
theorem B2156831 : Blo 956588 2156831 := bstep (se 1 (by rfl) ⟨1617623, by rfl⟩ : syracuseStep 2156831 = 3235247) B3235247
theorem B3238379 : Blo 956588 3238379 := bstep (se 1 (by rfl) ⟨2428784, by rfl⟩ : syracuseStep 3238379 = 4857569) B4857569
theorem B1436255 : Blo 956588 1436255 := bstep (se 1 (by rfl) ⟨1077191, by rfl⟩ : syracuseStep 1436255 = 2154383) B2154383
theorem B16411247 : Blo 956588 16411247 := bstep (se 1 (by rfl) ⟨12308435, by rfl⟩ : syracuseStep 16411247 = 24616871) B24616871
theorem B1436327 : Blo 956588 1436327 := bstep (se 1 (by rfl) ⟨1077245, by rfl⟩ : syracuseStep 1436327 = 2154491) B2154491
theorem B1436351 : Blo 956588 1436351 := bstep (se 1 (by rfl) ⟨1077263, by rfl⟩ : syracuseStep 1436351 = 2154527) B2154527
theorem B3075803 : Blo 956588 3075803 := bstep (se 1 (by rfl) ⟨2306852, by rfl⟩ : syracuseStep 3075803 = 4613705) B4613705
theorem B1437407 : Blo 956588 1437407 := bstep (se 1 (by rfl) ⟨1078055, by rfl⟩ : syracuseStep 1437407 = 2156111) B2156111
theorem B2158415 : Blo 956588 2158415 := bstep (se 1 (by rfl) ⟨1618811, by rfl⟩ : syracuseStep 2158415 = 3237623) B3237623
theorem B1437737 : Blo 956588 1437737 := bstep (se 2 (by rfl) ⟨539151, by rfl⟩ : syracuseStep 1437737 = 1078303) B1078303
theorem B1077295 : Blo 956588 1077295 := bstep (se 1 (by rfl) ⟨807971, by rfl⟩ : syracuseStep 1077295 = 1615943) B1615943
theorem B129659143 : Blo 956588 129659143 := bstep (se 1 (by rfl) ⟨97244357, by rfl⟩ : syracuseStep 129659143 = 194488715) B194488715
theorem B36008347 : Blo 956588 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B1077871 : Blo 956588 1077871 := bstep (se 1 (by rfl) ⟨808403, by rfl⟩ : syracuseStep 1077871 = 1616807) B1616807
theorem B3240809 : Blo 956588 3240809 := bstep (se 2 (by rfl) ⟨1215303, by rfl⟩ : syracuseStep 3240809 = 2430607) B2430607
theorem B1439003 : Blo 956588 1439003 := bstep (se 1 (by rfl) ⟨1079252, by rfl⟩ : syracuseStep 1439003 = 2158505) B2158505
theorem B3634703 : Blo 956588 3634703 := bstep (se 1 (by rfl) ⟨2726027, by rfl⟩ : syracuseStep 3634703 = 5452055) B5452055
theorem B1439609 : Blo 956588 1439609 := bstep (se 2 (by rfl) ⟨539853, by rfl⟩ : syracuseStep 1439609 = 1079707) B1079707
theorem B31094765 : Blo 956588 31094765 := bstep (se 3 (by rfl) ⟨5830268, by rfl⟩ : syracuseStep 31094765 = 11660537) B11660537
theorem B2586623 : Blo 956588 2586623 := bstep (se 1 (by rfl) ⟨1939967, by rfl⟩ : syracuseStep 2586623 = 3879935) B3879935
theorem B1439807 : Blo 956588 1439807 := bstep (se 1 (by rfl) ⟨1079855, by rfl⟩ : syracuseStep 1439807 = 2159711) B2159711
theorem B12450395 : Blo 956588 12450395 := bstep (se 1 (by rfl) ⟨9337796, by rfl⟩ : syracuseStep 12450395 = 18675593) B18675593
theorem B8747635 : Blo 956588 8747635 := bstep (se 1 (by rfl) ⟨6560726, by rfl⟩ : syracuseStep 8747635 = 13121453) B13121453
theorem B4848335 : Blo 956588 4848335 := bstep (se 1 (by rfl) ⟨3636251, by rfl⟩ : syracuseStep 4848335 = 7272503) B7272503
theorem B13794401 : Blo 956588 13794401 := bstep (se 2 (by rfl) ⟨5172900, by rfl⟩ : syracuseStep 13794401 = 10345801) B10345801
theorem B2424127 : Blo 956588 2424127 := bstep (se 1 (by rfl) ⟨1818095, by rfl⟩ : syracuseStep 2424127 = 3636191) B3636191
theorem B16612715 : Blo 956588 16612715 := bstep (se 1 (by rfl) ⟨12459536, by rfl⟩ : syracuseStep 16612715 = 24919073) B24919073
theorem B2424239 : Blo 956588 2424239 := bstep (se 1 (by rfl) ⟨1818179, by rfl⟩ : syracuseStep 2424239 = 3636359) B3636359
theorem B21037657 : Blo 956588 21037657 := bstep (se 2 (by rfl) ⟨7889121, by rfl⟩ : syracuseStep 21037657 = 15778243) B15778243
theorem B16385003 : Blo 956588 16385003 := bstep (se 1 (by rfl) ⟨12288752, by rfl⟩ : syracuseStep 16385003 = 24577505) B24577505
theorem B3638303 : Blo 956588 3638303 := bstep (se 1 (by rfl) ⟨2728727, by rfl⟩ : syracuseStep 3638303 = 5457455) B5457455
theorem B10913129 : Blo 956588 10913129 := bstep (se 2 (by rfl) ⟨4092423, by rfl⟩ : syracuseStep 10913129 = 8184847) B8184847
theorem B88507993 : Blo 956588 88507993 := bstep (se 2 (by rfl) ⟨33190497, by rfl⟩ : syracuseStep 88507993 = 66380995) B66380995
theorem B6915887 : Blo 956588 6915887 := bstep (se 1 (by rfl) ⟨5186915, by rfl⟩ : syracuseStep 6915887 = 10373831) B10373831
theorem B5902075 : Blo 956588 5902075 := bstep (se 1 (by rfl) ⟨4426556, by rfl⟩ : syracuseStep 5902075 = 8853113) B8853113
theorem B283250789 : Blo 956588 283250789 := bstep (se 4 (by rfl) ⟨26554761, by rfl⟩ : syracuseStep 283250789 = 53109523) B53109523
theorem B16389377 : Blo 956588 16389377 := bstep (se 2 (by rfl) ⟨6146016, by rfl⟩ : syracuseStep 16389377 = 12292033) B12292033
theorem B2725481 : Blo 956588 2725481 := bstep (se 2 (by rfl) ⟨1022055, by rfl⟩ : syracuseStep 2725481 = 2044111) B2044111
theorem B48011129 : Blo 956588 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B7018493 : Blo 956588 7018493 := bstep (se 3 (by rfl) ⟨1315967, by rfl⟩ : syracuseStep 7018493 = 2631935) B2631935
theorem B956623 : Blo 956588 956623 := bstep (se 1 (by rfl) ⟨717467, by rfl⟩ : syracuseStep 956623 = 1434935) B1434935
theorem B956655 : Blo 956588 956655 := bstep (se 1 (by rfl) ⟨717491, by rfl⟩ : syracuseStep 956655 = 1434983) B1434983
theorem B956671 : Blo 956588 956671 := bstep (se 1 (by rfl) ⟨717503, by rfl⟩ : syracuseStep 956671 = 1435007) B1435007
theorem B957135 : Blo 956588 957135 := bstep (se 1 (by rfl) ⟨717851, by rfl⟩ : syracuseStep 957135 = 1435703) B1435703
theorem B957167 : Blo 956588 957167 := bstep (se 1 (by rfl) ⟨717875, by rfl⟩ : syracuseStep 957167 = 1435751) B1435751
theorem B957183 : Blo 956588 957183 := bstep (se 1 (by rfl) ⟨717887, by rfl⟩ : syracuseStep 957183 = 1435775) B1435775
theorem B33201053 : Blo 956588 33201053 := bstep (se 3 (by rfl) ⟨6225197, by rfl⟩ : syracuseStep 33201053 = 12450395) B12450395
theorem B957503 : Blo 956588 957503 := bstep (se 1 (by rfl) ⟨718127, by rfl⟩ : syracuseStep 957503 = 1436255) B1436255
theorem B957551 : Blo 956588 957551 := bstep (se 1 (by rfl) ⟨718163, by rfl⟩ : syracuseStep 957551 = 1436327) B1436327
theorem B957567 : Blo 956588 957567 := bstep (se 1 (by rfl) ⟨718175, by rfl⟩ : syracuseStep 957567 = 1436351) B1436351
theorem B4857407 : Blo 956588 4857407 := bstep (se 1 (by rfl) ⟨3643055, by rfl⟩ : syracuseStep 4857407 = 7286111) B7286111
theorem B958271 : Blo 956588 958271 := bstep (se 1 (by rfl) ⟨718703, by rfl⟩ : syracuseStep 958271 = 1437407) B1437407
theorem B6299495 : Blo 956588 6299495 := bstep (se 1 (by rfl) ⟨4724621, by rfl⟩ : syracuseStep 6299495 = 9449243) B9449243
theorem B958491 : Blo 956588 958491 := bstep (se 1 (by rfl) ⟨718868, by rfl⟩ : syracuseStep 958491 = 1437737) B1437737
theorem B36807209 : Blo 956588 36807209 := bstep (se 2 (by rfl) ⟨13802703, by rfl⟩ : syracuseStep 36807209 = 27605407) B27605407
theorem B8757881 : Blo 956588 8757881 := bstep (se 2 (by rfl) ⟨3284205, by rfl⟩ : syracuseStep 8757881 = 6568411) B6568411
theorem B959335 : Blo 956588 959335 := bstep (se 1 (by rfl) ⟨719501, by rfl⟩ : syracuseStep 959335 = 1439003) B1439003
theorem B3941225 : Blo 956588 3941225 := bstep (se 2 (by rfl) ⟨1477959, by rfl⟩ : syracuseStep 3941225 = 2955919) B2955919
theorem B959739 : Blo 956588 959739 := bstep (se 1 (by rfl) ⟨719804, by rfl⟩ : syracuseStep 959739 = 1439609) B1439609
theorem B959871 : Blo 956588 959871 := bstep (se 1 (by rfl) ⟨719903, by rfl⟩ : syracuseStep 959871 = 1439807) B1439807
theorem B1616159 : Blo 956588 1616159 := bstep (se 1 (by rfl) ⟨1212119, by rfl⟩ : syracuseStep 1616159 = 2424239) B2424239
theorem B1616591 : Blo 956588 1616591 := bstep (se 1 (by rfl) ⟨1212443, by rfl⟩ : syracuseStep 1616591 = 2424887) B2424887
theorem B1617529 : Blo 956588 1617529 := bstep (se 2 (by rfl) ⟨606573, by rfl⟩ : syracuseStep 1617529 = 1213147) B1213147
theorem B2044777 : Blo 956588 2044777 := bstep (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) B1533583
theorem B1620155 : Blo 956588 1620155 := bstep (se 1 (by rfl) ⟨1215116, by rfl⟩ : syracuseStep 1620155 = 2430233) B2430233
theorem B2046683 : Blo 956588 2046683 := bstep (se 1 (by rfl) ⟨1535012, by rfl⟩ : syracuseStep 2046683 = 3070025) B3070025
theorem B3882127 : Blo 956588 3882127 := bstep (se 1 (by rfl) ⟨2911595, by rfl⟩ : syracuseStep 3882127 = 5823191) B5823191
theorem B2050535 : Blo 956588 2050535 := bstep (se 1 (by rfl) ⟨1537901, by rfl⟩ : syracuseStep 2050535 = 3075803) B3075803
theorem B22138751 : Blo 956588 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B20729843 : Blo 956588 20729843 := bstep (se 1 (by rfl) ⟨15547382, by rfl⟩ : syracuseStep 20729843 = 31094765) B31094765
theorem B3232169 : Blo 956588 3232169 := bstep (se 2 (by rfl) ⟨1212063, by rfl⟩ : syracuseStep 3232169 = 2424127) B2424127
theorem B3232223 : Blo 956588 3232223 := bstep (se 1 (by rfl) ⟨2424167, by rfl⟩ : syracuseStep 3232223 = 4848335) B4848335
theorem B24564383 : Blo 956588 24564383 := bstep (se 1 (by rfl) ⟨18423287, by rfl⟩ : syracuseStep 24564383 = 36846575) B36846575
theorem B9196267 : Blo 956588 9196267 := bstep (se 1 (by rfl) ⟨6897200, by rfl⟩ : syracuseStep 9196267 = 13794401) B13794401
theorem B93411143 : Blo 956588 93411143 := bstep (se 1 (by rfl) ⟨70058357, by rfl⟩ : syracuseStep 93411143 = 140116715) B140116715
theorem B1726319 : Blo 956588 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B3233735 : Blo 956588 3233735 := bstep (se 1 (by rfl) ⟨2425301, by rfl⟩ : syracuseStep 3233735 = 4850603) B4850603
theorem B23320871 : Blo 956588 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B3070651 : Blo 956588 3070651 := bstep (se 1 (by rfl) ⟨2302988, by rfl⟩ : syracuseStep 3070651 = 4605977) B4605977
theorem B4086719 : Blo 956588 4086719 := bstep (se 1 (by rfl) ⟨3065039, by rfl⟩ : syracuseStep 4086719 = 6130079) B6130079
theorem B1367599 : Blo 956588 1367599 := bstep (se 1 (by rfl) ⟨1025699, by rfl⟩ : syracuseStep 1367599 = 2051399) B2051399
theorem B3071881 : Blo 956588 3071881 := bstep (se 2 (by rfl) ⟨1151955, by rfl⟩ : syracuseStep 3071881 = 2303911) B2303911
theorem B12280247 : Blo 956588 12280247 := bstep (se 1 (by rfl) ⟨9210185, by rfl⟩ : syracuseStep 12280247 = 18420371) B18420371
theorem B3236327 : Blo 956588 3236327 := bstep (se 1 (by rfl) ⟨2427245, by rfl⟩ : syracuseStep 3236327 = 4854491) B4854491
theorem B9200573 : Blo 956588 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B1435739 : Blo 956588 1435739 := bstep (se 1 (by rfl) ⟨1076804, by rfl⟩ : syracuseStep 1435739 = 2153609) B2153609
theorem B10381439 : Blo 956588 10381439 := bstep (se 1 (by rfl) ⟨7786079, by rfl⟩ : syracuseStep 10381439 = 15572159) B15572159
theorem B1435823 : Blo 956588 1435823 := bstep (se 1 (by rfl) ⟨1076867, by rfl⟩ : syracuseStep 1435823 = 2153735) B2153735
theorem B3238217 : Blo 956588 3238217 := bstep (se 2 (by rfl) ⟨1214331, by rfl⟩ : syracuseStep 3238217 = 2428663) B2428663
theorem B3893851 : Blo 956588 3893851 := bstep (se 1 (by rfl) ⟨2920388, by rfl⟩ : syracuseStep 3893851 = 5840777) B5840777
theorem B2157281 : Blo 956588 2157281 := bstep (se 2 (by rfl) ⟨808980, by rfl⟩ : syracuseStep 2157281 = 1617961) B1617961
theorem B1436393 : Blo 956588 1436393 := bstep (se 2 (by rfl) ⟨538647, by rfl⟩ : syracuseStep 1436393 = 1077295) B1077295
theorem B3238703 : Blo 956588 3238703 := bstep (se 1 (by rfl) ⟨2429027, by rfl⟩ : syracuseStep 3238703 = 4858055) B4858055
theorem B172878857 : Blo 956588 172878857 := bstep (se 2 (by rfl) ⟨64829571, by rfl⟩ : syracuseStep 172878857 = 129659143) B129659143
theorem B1436735 : Blo 956588 1436735 := bstep (se 1 (by rfl) ⟨1077551, by rfl⟩ : syracuseStep 1436735 = 2155103) B2155103
theorem B1436831 : Blo 956588 1436831 := bstep (se 1 (by rfl) ⟨1077623, by rfl⟩ : syracuseStep 1436831 = 2155247) B2155247
theorem B2157983 : Blo 956588 2157983 := bstep (se 1 (by rfl) ⟨1618487, by rfl⟩ : syracuseStep 2157983 = 3236975) B3236975
theorem B46722521 : Blo 956588 46722521 := bstep (se 2 (by rfl) ⟨17520945, by rfl⟩ : syracuseStep 46722521 = 35041891) B35041891
theorem B1437161 : Blo 956588 1437161 := bstep (se 2 (by rfl) ⟨538935, by rfl⟩ : syracuseStep 1437161 = 1077871) B1077871
theorem B2158217 : Blo 956588 2158217 := bstep (se 2 (by rfl) ⟨809331, by rfl⟩ : syracuseStep 2158217 = 1618663) B1618663
theorem B39415709 : Blo 956588 39415709 := bstep (se 3 (by rfl) ⟨7390445, by rfl⟩ : syracuseStep 39415709 = 14780891) B14780891
theorem B3239891 : Blo 956588 3239891 := bstep (se 1 (by rfl) ⟨2429918, by rfl⟩ : syracuseStep 3239891 = 4859837) B4859837
theorem B2158703 : Blo 956588 2158703 := bstep (se 1 (by rfl) ⟨1619027, by rfl⟩ : syracuseStep 2158703 = 3238055) B3238055
theorem B1437887 : Blo 956588 1437887 := bstep (se 1 (by rfl) ⟨1078415, by rfl⟩ : syracuseStep 1437887 = 2156831) B2156831
theorem B2158919 : Blo 956588 2158919 := bstep (se 1 (by rfl) ⟨1619189, by rfl⟩ : syracuseStep 2158919 = 3238379) B3238379
theorem B10940831 : Blo 956588 10940831 := bstep (se 1 (by rfl) ⟨8205623, by rfl⟩ : syracuseStep 10940831 = 16411247) B16411247
theorem B13464103 : Blo 956588 13464103 := bstep (se 1 (by rfl) ⟨10098077, by rfl⟩ : syracuseStep 13464103 = 20196155) B20196155
theorem B3076649 : Blo 956588 3076649 := bstep (se 2 (by rfl) ⟨1153743, by rfl⟩ : syracuseStep 3076649 = 2307487) B2307487
theorem B1438943 : Blo 956588 1438943 := bstep (se 1 (by rfl) ⟨1079207, by rfl⟩ : syracuseStep 1438943 = 2158415) B2158415
theorem B2160539 : Blo 956588 2160539 := bstep (se 1 (by rfl) ⟨1620404, by rfl⟩ : syracuseStep 2160539 = 3240809) B3240809
theorem B22116311 : Blo 956588 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B11663513 : Blo 956588 11663513 := bstep (se 2 (by rfl) ⟨4373817, by rfl⟩ : syracuseStep 11663513 = 8747635) B8747635
theorem B2423135 : Blo 956588 2423135 := bstep (se 1 (by rfl) ⟨1817351, by rfl⟩ : syracuseStep 2423135 = 3634703) B3634703
theorem B13827617 : Blo 956588 13827617 := bstep (se 2 (by rfl) ⟨5185356, by rfl⟩ : syracuseStep 13827617 = 10370713) B10370713
theorem B11075143 : Blo 956588 11075143 := bstep (se 1 (by rfl) ⟨8306357, by rfl⟩ : syracuseStep 11075143 = 16612715) B16612715
theorem B2588527 : Blo 956588 2588527 := bstep (se 1 (by rfl) ⟨1941395, by rfl⟩ : syracuseStep 2588527 = 3882791) B3882791
theorem B10911671 : Blo 956588 10911671 := bstep (se 1 (by rfl) ⟨8183753, by rfl⟩ : syracuseStep 10911671 = 16367507) B16367507
theorem B27590645 : Blo 956588 27590645 := bstep (se 5 (by rfl) ⟨1293311, by rfl⟩ : syracuseStep 27590645 = 2586623) B2586623
theorem B2425535 : Blo 956588 2425535 := bstep (se 1 (by rfl) ⟨1819151, by rfl⟩ : syracuseStep 2425535 = 3638303) B3638303
theorem B28050209 : Blo 956588 28050209 := bstep (se 2 (by rfl) ⟨10518828, by rfl⟩ : syracuseStep 28050209 = 21037657) B21037657
theorem B7275419 : Blo 956588 7275419 := bstep (se 1 (by rfl) ⟨5456564, by rfl⟩ : syracuseStep 7275419 = 10913129) B10913129
theorem B2724479 : Blo 956588 2724479 := bstep (se 1 (by rfl) ⟨2043359, by rfl⟩ : syracuseStep 2724479 = 4086719) B4086719
theorem B4199663 : Blo 956588 4199663 := bstep (se 1 (by rfl) ⟨3149747, by rfl⟩ : syracuseStep 4199663 = 6299495) B6299495
theorem B18715981 : Blo 956588 18715981 := bstep (se 3 (by rfl) ⟨3509246, by rfl⟩ : syracuseStep 18715981 = 7018493) B7018493
theorem B5838587 : Blo 956588 5838587 := bstep (se 1 (by rfl) ⟨4378940, by rfl⟩ : syracuseStep 5838587 = 8757881) B8757881
theorem B2627483 : Blo 956588 2627483 := bstep (se 1 (by rfl) ⟨1970612, by rfl⟩ : syracuseStep 2627483 = 3941225) B3941225
theorem B6133715 : Blo 956588 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B12261689 : Blo 956588 12261689 := bstep (se 2 (by rfl) ⟨4598133, by rfl⟩ : syracuseStep 12261689 = 9196267) B9196267
theorem B2726369 : Blo 956588 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B957159 : Blo 956588 957159 := bstep (se 1 (by rfl) ⟨717869, by rfl⟩ : syracuseStep 957159 = 1435739) B1435739
theorem B6920959 : Blo 956588 6920959 := bstep (se 1 (by rfl) ⟨5190719, by rfl⟩ : syracuseStep 6920959 = 10381439) B10381439
theorem B957215 : Blo 956588 957215 := bstep (se 1 (by rfl) ⟨717911, by rfl⟩ : syracuseStep 957215 = 1435823) B1435823
theorem B957595 : Blo 956588 957595 := bstep (se 1 (by rfl) ⟨718196, by rfl⟩ : syracuseStep 957595 = 1436393) B1436393
theorem B115252571 : Blo 956588 115252571 := bstep (se 1 (by rfl) ⟨86439428, by rfl⟩ : syracuseStep 115252571 = 172878857) B172878857
theorem B957823 : Blo 956588 957823 := bstep (se 1 (by rfl) ⟨718367, by rfl⟩ : syracuseStep 957823 = 1436735) B1436735
theorem B957887 : Blo 956588 957887 := bstep (se 1 (by rfl) ⟨718415, by rfl⟩ : syracuseStep 957887 = 1436831) B1436831
theorem B958107 : Blo 956588 958107 := bstep (se 1 (by rfl) ⟨718580, by rfl⟩ : syracuseStep 958107 = 1437161) B1437161
theorem B958591 : Blo 956588 958591 := bstep (se 1 (by rfl) ⟨718943, by rfl⟩ : syracuseStep 958591 = 1437887) B1437887
theorem B959295 : Blo 956588 959295 := bstep (se 1 (by rfl) ⟨719471, by rfl⟩ : syracuseStep 959295 = 1438943) B1438943
theorem B7775675 : Blo 956588 7775675 := bstep (se 1 (by rfl) ⟨5831756, by rfl⟩ : syracuseStep 7775675 = 11663513) B11663513
theorem B1615423 : Blo 956588 1615423 := bstep (se 1 (by rfl) ⟨1211567, by rfl⟩ : syracuseStep 1615423 = 2423135) B2423135
theorem B9218411 : Blo 956588 9218411 := bstep (se 1 (by rfl) ⟨6913808, by rfl⟩ : syracuseStep 9218411 = 13827617) B13827617
theorem B3451369 : Blo 956588 3451369 := bstep (se 2 (by rfl) ⟨1294263, by rfl⟩ : syracuseStep 3451369 = 2588527) B2588527
theorem B18393763 : Blo 956588 18393763 := bstep (se 1 (by rfl) ⟨13795322, by rfl⟩ : syracuseStep 18393763 = 27590645) B27590645
theorem B10923335 : Blo 956588 10923335 := bstep (se 1 (by rfl) ⟨8192501, by rfl⟩ : syracuseStep 10923335 = 16385003) B16385003
theorem B118010657 : Blo 956588 118010657 := bstep (se 2 (by rfl) ⟨44253996, by rfl⟩ : syracuseStep 118010657 = 88507993) B88507993
theorem B14759167 : Blo 956588 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B10926251 : Blo 956588 10926251 := bstep (se 1 (by rfl) ⟨8194688, by rfl⟩ : syracuseStep 10926251 = 16389377) B16389377
theorem B1816987 : Blo 956588 1816987 := bstep (se 1 (by rfl) ⟨1362740, by rfl⟩ : syracuseStep 1816987 = 2725481) B2725481
theorem B62274095 : Blo 956588 62274095 := bstep (se 1 (by rfl) ⟨46705571, by rfl⟩ : syracuseStep 62274095 = 93411143) B93411143
theorem B15547247 : Blo 956588 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B22134035 : Blo 956588 22134035 := bstep (se 1 (by rfl) ⟨16600526, by rfl⟩ : syracuseStep 22134035 = 33201053) B33201053
theorem B4603517 : Blo 956588 4603517 := bstep (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) B1726319
theorem B31148347 : Blo 956588 31148347 := bstep (se 1 (by rfl) ⟨23361260, by rfl⟩ : syracuseStep 31148347 = 46722521) B46722521
theorem B7293887 : Blo 956588 7293887 := bstep (se 1 (by rfl) ⟨5470415, by rfl⟩ : syracuseStep 7293887 = 10940831) B10940831
theorem B2051099 : Blo 956588 2051099 := bstep (se 1 (by rfl) ⟨1538324, by rfl⟩ : syracuseStep 2051099 = 3076649) B3076649
theorem B31477733 : Blo 956588 31477733 := bstep (se 4 (by rfl) ⟨2951037, by rfl⟩ : syracuseStep 31477733 = 5902075) B5902075
theorem B1364455 : Blo 956588 1364455 := bstep (se 1 (by rfl) ⟨1023341, by rfl⟩ : syracuseStep 1364455 = 2046683) B2046683
theorem B1823465 : Blo 956588 1823465 := bstep (se 2 (by rfl) ⟨683799, by rfl⟩ : syracuseStep 1823465 = 1367599) B1367599
theorem B14766857 : Blo 956588 14766857 := bstep (se 2 (by rfl) ⟨5537571, by rfl⟩ : syracuseStep 14766857 = 11075143) B11075143
theorem B4610591 : Blo 956588 4610591 := bstep (se 1 (by rfl) ⟨3457943, by rfl⟩ : syracuseStep 4610591 = 6915887) B6915887
theorem B13819895 : Blo 956588 13819895 := bstep (se 1 (by rfl) ⟨10364921, by rfl⟩ : syracuseStep 13819895 = 20729843) B20729843
theorem B188833859 : Blo 956588 188833859 := bstep (se 1 (by rfl) ⟨141625394, by rfl⟩ : syracuseStep 188833859 = 283250789) B283250789
theorem B2154779 : Blo 956588 2154779 := bstep (se 1 (by rfl) ⟨1616084, by rfl⟩ : syracuseStep 2154779 = 3232169) B3232169
theorem B2154815 : Blo 956588 2154815 := bstep (se 1 (by rfl) ⟨1616111, by rfl⟩ : syracuseStep 2154815 = 3232223) B3232223
theorem B16376255 : Blo 956588 16376255 := bstep (se 1 (by rfl) ⟨12282191, by rfl⟩ : syracuseStep 16376255 = 24564383) B24564383
theorem B20767205 : Blo 956588 20767205 := bstep (se 4 (by rfl) ⟨1946925, by rfl⟩ : syracuseStep 20767205 = 3893851) B3893851
theorem B32007419 : Blo 956588 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B2155823 : Blo 956588 2155823 := bstep (se 1 (by rfl) ⟨1616867, by rfl⟩ : syracuseStep 2155823 = 3233735) B3233735
theorem B2156705 : Blo 956588 2156705 := bstep (se 2 (by rfl) ⟨808764, by rfl⟩ : syracuseStep 2156705 = 1617529) B1617529
theorem B3238271 : Blo 956588 3238271 := bstep (se 1 (by rfl) ⟨2428703, by rfl⟩ : syracuseStep 3238271 = 4857407) B4857407
theorem B8186831 : Blo 956588 8186831 := bstep (se 1 (by rfl) ⟨6140123, by rfl⟩ : syracuseStep 8186831 = 12280247) B12280247
theorem B2157551 : Blo 956588 2157551 := bstep (se 1 (by rfl) ⟨1618163, by rfl⟩ : syracuseStep 2157551 = 3236327) B3236327
theorem B24538139 : Blo 956588 24538139 := bstep (se 1 (by rfl) ⟨18403604, by rfl⟩ : syracuseStep 24538139 = 36807209) B36807209
theorem B17952137 : Blo 956588 17952137 := bstep (se 2 (by rfl) ⟨6732051, by rfl⟩ : syracuseStep 17952137 = 13464103) B13464103
theorem B5468093 : Blo 956588 5468093 := bstep (se 3 (by rfl) ⟨1025267, by rfl⟩ : syracuseStep 5468093 = 2050535) B2050535
theorem B1077439 : Blo 956588 1077439 := bstep (se 1 (by rfl) ⟨808079, by rfl⟩ : syracuseStep 1077439 = 1616159) B1616159
theorem B2158811 : Blo 956588 2158811 := bstep (se 1 (by rfl) ⟨1619108, by rfl⟩ : syracuseStep 2158811 = 3238217) B3238217
theorem B1077727 : Blo 956588 1077727 := bstep (se 1 (by rfl) ⟨808295, by rfl⟩ : syracuseStep 1077727 = 1616591) B1616591
theorem B1438187 : Blo 956588 1438187 := bstep (se 1 (by rfl) ⟨1078640, by rfl⟩ : syracuseStep 1438187 = 2157281) B2157281
theorem B2159135 : Blo 956588 2159135 := bstep (se 1 (by rfl) ⟨1619351, by rfl⟩ : syracuseStep 2159135 = 3238703) B3238703
theorem B1438655 : Blo 956588 1438655 := bstep (se 1 (by rfl) ⟨1078991, by rfl⟩ : syracuseStep 1438655 = 2157983) B2157983
theorem B1438811 : Blo 956588 1438811 := bstep (se 1 (by rfl) ⟨1079108, by rfl⟩ : syracuseStep 1438811 = 2158217) B2158217
theorem B26277139 : Blo 956588 26277139 := bstep (se 1 (by rfl) ⟨19707854, by rfl⟩ : syracuseStep 26277139 = 39415709) B39415709
theorem B2159927 : Blo 956588 2159927 := bstep (se 1 (by rfl) ⟨1619945, by rfl⟩ : syracuseStep 2159927 = 3239891) B3239891
theorem B1439135 : Blo 956588 1439135 := bstep (se 1 (by rfl) ⟨1079351, by rfl⟩ : syracuseStep 1439135 = 2158703) B2158703
theorem B1439279 : Blo 956588 1439279 := bstep (se 1 (by rfl) ⟨1079459, by rfl⟩ : syracuseStep 1439279 = 2158919) B2158919
theorem B4094201 : Blo 956588 4094201 := bstep (se 2 (by rfl) ⟨1535325, by rfl⟩ : syracuseStep 4094201 = 3070651) B3070651
theorem B1440359 : Blo 956588 1440359 := bstep (se 1 (by rfl) ⟨1080269, by rfl⟩ : syracuseStep 1440359 = 2160539) B2160539
theorem B14744207 : Blo 956588 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B1080103 : Blo 956588 1080103 := bstep (se 1 (by rfl) ⟨810077, by rfl⟩ : syracuseStep 1080103 = 1620155) B1620155
theorem B5176169 : Blo 956588 5176169 := bstep (se 2 (by rfl) ⟨1941063, by rfl⟩ : syracuseStep 5176169 = 3882127) B3882127
theorem B4095841 : Blo 956588 4095841 := bstep (se 2 (by rfl) ⟨1535940, by rfl⟩ : syracuseStep 4095841 = 3071881) B3071881
theorem B7274447 : Blo 956588 7274447 := bstep (se 1 (by rfl) ⟨5455835, by rfl⟩ : syracuseStep 7274447 = 10911671) B10911671
theorem B4850279 : Blo 956588 4850279 := bstep (se 1 (by rfl) ⟨3637709, by rfl⟩ : syracuseStep 4850279 = 7275419) B7275419
theorem B1215643 : Blo 956588 1215643 := bstep (se 1 (by rfl) ⟨911732, by rfl⟩ : syracuseStep 1215643 = 1823465) B1823465
theorem B9213263 : Blo 956588 9213263 := bstep (se 1 (by rfl) ⟨6909947, by rfl⟩ : syracuseStep 9213263 = 13819895) B13819895
theorem B10917503 : Blo 956588 10917503 := bstep (se 1 (by rfl) ⟨8188127, by rfl⟩ : syracuseStep 10917503 = 16376255) B16376255
theorem B21338279 : Blo 956588 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B5183783 : Blo 956588 5183783 := bstep (se 1 (by rfl) ⟨3887837, by rfl⟩ : syracuseStep 5183783 = 7775675) B7775675
theorem B35036185 : Blo 956588 35036185 := bstep (se 2 (by rfl) ⟨13138569, by rfl⟩ : syracuseStep 35036185 = 26277139) B26277139
theorem B16358759 : Blo 956588 16358759 := bstep (se 1 (by rfl) ⟨12269069, by rfl⟩ : syracuseStep 16358759 = 24538139) B24538139
theorem B7282223 : Blo 956588 7282223 := bstep (se 1 (by rfl) ⟨5461667, by rfl⟩ : syracuseStep 7282223 = 10923335) B10923335
theorem B11968091 : Blo 956588 11968091 := bstep (se 1 (by rfl) ⟨8976068, by rfl⟩ : syracuseStep 11968091 = 17952137) B17952137
theorem B3645395 : Blo 956588 3645395 := bstep (se 1 (by rfl) ⟨2734046, by rfl⟩ : syracuseStep 3645395 = 5468093) B5468093
theorem B958791 : Blo 956588 958791 := bstep (se 1 (by rfl) ⟨719093, by rfl⟩ : syracuseStep 958791 = 1438187) B1438187
theorem B959103 : Blo 956588 959103 := bstep (se 1 (by rfl) ⟨719327, by rfl⟩ : syracuseStep 959103 = 1438655) B1438655
theorem B959207 : Blo 956588 959207 := bstep (se 1 (by rfl) ⟨719405, by rfl⟩ : syracuseStep 959207 = 1438811) B1438811
theorem B307340189 : Blo 956588 307340189 := bstep (se 3 (by rfl) ⟨57626285, by rfl⟩ : syracuseStep 307340189 = 115252571) B115252571
theorem B959423 : Blo 956588 959423 := bstep (se 1 (by rfl) ⟨719567, by rfl⟩ : syracuseStep 959423 = 1439135) B1439135
theorem B959519 : Blo 956588 959519 := bstep (se 1 (by rfl) ⟨719639, by rfl⟩ : syracuseStep 959519 = 1439279) B1439279
theorem B7284167 : Blo 956588 7284167 := bstep (se 1 (by rfl) ⟨5463125, by rfl⟩ : syracuseStep 7284167 = 10926251) B10926251
theorem B2729467 : Blo 956588 2729467 := bstep (se 1 (by rfl) ⟨2047100, by rfl⟩ : syracuseStep 2729467 = 4094201) B4094201
theorem B960239 : Blo 956588 960239 := bstep (se 1 (by rfl) ⟨720179, by rfl⟩ : syracuseStep 960239 = 1440359) B1440359
theorem B3450779 : Blo 956588 3450779 := bstep (se 1 (by rfl) ⟨2588084, by rfl⟩ : syracuseStep 3450779 = 5176169) B5176169
theorem B10364831 : Blo 956588 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B14756023 : Blo 956588 14756023 := bstep (se 1 (by rfl) ⟨11067017, by rfl⟩ : syracuseStep 14756023 = 22134035) B22134035
theorem B1617023 : Blo 956588 1617023 := bstep (se 1 (by rfl) ⟨1212767, by rfl⟩ : syracuseStep 1617023 = 2425535) B2425535
theorem B4862591 : Blo 956588 4862591 := bstep (se 1 (by rfl) ⟨3646943, by rfl⟩ : syracuseStep 4862591 = 7293887) B7293887
theorem B20985155 : Blo 956588 20985155 := bstep (se 1 (by rfl) ⟨15738866, by rfl⟩ : syracuseStep 20985155 = 31477733) B31477733
theorem B41531129 : Blo 956588 41531129 := bstep (se 2 (by rfl) ⟨15574173, by rfl⟩ : syracuseStep 41531129 = 31148347) B31148347
theorem B1816319 : Blo 956588 1816319 := bstep (se 1 (by rfl) ⟨1362239, by rfl⟩ : syracuseStep 1816319 = 2724479) B2724479
theorem B9844571 : Blo 956588 9844571 := bstep (se 1 (by rfl) ⟨7383428, by rfl⟩ : syracuseStep 9844571 = 14766857) B14766857
theorem B4601825 : Blo 956588 4601825 := bstep (se 2 (by rfl) ⟨1725684, by rfl⟩ : syracuseStep 4601825 = 3451369) B3451369
theorem B2799775 : Blo 956588 2799775 := bstep (se 1 (by rfl) ⟨2099831, by rfl⟩ : syracuseStep 2799775 = 4199663) B4199663
theorem B24525017 : Blo 956588 24525017 := bstep (se 2 (by rfl) ⟨9196881, by rfl⟩ : syracuseStep 24525017 = 18393763) B18393763
theorem B8174459 : Blo 956588 8174459 := bstep (se 1 (by rfl) ⟨6130844, by rfl⟩ : syracuseStep 8174459 = 12261689) B12261689
theorem B1817579 : Blo 956588 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B13844803 : Blo 956588 13844803 := bstep (se 1 (by rfl) ⟨10383602, by rfl⟩ : syracuseStep 13844803 = 20767205) B20767205
theorem B1819273 : Blo 956588 1819273 := bstep (se 2 (by rfl) ⟨682227, by rfl⟩ : syracuseStep 1819273 = 1364455) B1364455
theorem B6145607 : Blo 956588 6145607 := bstep (se 1 (by rfl) ⟨4609205, by rfl⟩ : syracuseStep 6145607 = 9218411) B9218411
theorem B19678889 : Blo 956588 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B24954641 : Blo 956588 24954641 := bstep (se 2 (by rfl) ⟨9357990, by rfl⟩ : syracuseStep 24954641 = 18715981) B18715981
theorem B5457887 : Blo 956588 5457887 := bstep (se 1 (by rfl) ⟨4093415, by rfl⟩ : syracuseStep 5457887 = 8186831) B8186831
theorem B9227945 : Blo 956588 9227945 := bstep (se 2 (by rfl) ⟨3460479, by rfl⟩ : syracuseStep 9227945 = 6920959) B6920959
theorem B3069011 : Blo 956588 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B5461121 : Blo 956588 5461121 := bstep (se 2 (by rfl) ⟨2047920, by rfl⟩ : syracuseStep 5461121 = 4095841) B4095841
theorem B18700139 : Blo 956588 18700139 := bstep (se 1 (by rfl) ⟨14025104, by rfl⟩ : syracuseStep 18700139 = 28050209) B28050209
theorem B1367399 : Blo 956588 1367399 := bstep (se 1 (by rfl) ⟨1025549, by rfl⟩ : syracuseStep 1367399 = 2051099) B2051099
theorem B2153897 : Blo 956588 2153897 := bstep (se 2 (by rfl) ⟨807711, by rfl⟩ : syracuseStep 2153897 = 1615423) B1615423
theorem B3892391 : Blo 956588 3892391 := bstep (se 1 (by rfl) ⟨2919293, by rfl⟩ : syracuseStep 3892391 = 5838587) B5838587
theorem B4089143 : Blo 956588 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B3073727 : Blo 956588 3073727 := bstep (se 1 (by rfl) ⟨2305295, by rfl⟩ : syracuseStep 3073727 = 4610591) B4610591
theorem B7006621 : Blo 956588 7006621 := bstep (se 3 (by rfl) ⟨1313741, by rfl⟩ : syracuseStep 7006621 = 2627483) B2627483
theorem B125889239 : Blo 956588 125889239 := bstep (se 1 (by rfl) ⟨94416929, by rfl⟩ : syracuseStep 125889239 = 188833859) B188833859
theorem B1436519 : Blo 956588 1436519 := bstep (se 1 (by rfl) ⟨1077389, by rfl⟩ : syracuseStep 1436519 = 2154779) B2154779
theorem B1436543 : Blo 956588 1436543 := bstep (se 1 (by rfl) ⟨1077407, by rfl⟩ : syracuseStep 1436543 = 2154815) B2154815
theorem B1436585 : Blo 956588 1436585 := bstep (se 2 (by rfl) ⟨538719, by rfl⟩ : syracuseStep 1436585 = 1077439) B1077439
theorem B1436969 : Blo 956588 1436969 := bstep (se 2 (by rfl) ⟨538863, by rfl⟩ : syracuseStep 1436969 = 1077727) B1077727
theorem B1437215 : Blo 956588 1437215 := bstep (se 1 (by rfl) ⟨1077911, by rfl⟩ : syracuseStep 1437215 = 2155823) B2155823
theorem B1437803 : Blo 956588 1437803 := bstep (se 1 (by rfl) ⟨1078352, by rfl⟩ : syracuseStep 1437803 = 2156705) B2156705
theorem B2158847 : Blo 956588 2158847 := bstep (se 1 (by rfl) ⟨1619135, by rfl⟩ : syracuseStep 2158847 = 3238271) B3238271
theorem B1438367 : Blo 956588 1438367 := bstep (se 1 (by rfl) ⟨1078775, by rfl⟩ : syracuseStep 1438367 = 2157551) B2157551
theorem B1439207 : Blo 956588 1439207 := bstep (se 1 (by rfl) ⟨1079405, by rfl⟩ : syracuseStep 1439207 = 2158811) B2158811
theorem B1439423 : Blo 956588 1439423 := bstep (se 1 (by rfl) ⟨1079567, by rfl⟩ : syracuseStep 1439423 = 2159135) B2159135
theorem B78673771 : Blo 956588 78673771 := bstep (se 1 (by rfl) ⟨59005328, by rfl⟩ : syracuseStep 78673771 = 118010657) B118010657
theorem B2422649 : Blo 956588 2422649 := bstep (se 2 (by rfl) ⟨908493, by rfl⟩ : syracuseStep 2422649 = 1816987) B1816987
theorem B1439951 : Blo 956588 1439951 := bstep (se 1 (by rfl) ⟨1079963, by rfl⟩ : syracuseStep 1439951 = 2159927) B2159927
theorem B1440137 : Blo 956588 1440137 := bstep (se 2 (by rfl) ⟨540051, by rfl⟩ : syracuseStep 1440137 = 1080103) B1080103
theorem B41516063 : Blo 956588 41516063 := bstep (se 1 (by rfl) ⟨31137047, by rfl⟩ : syracuseStep 41516063 = 62274095) B62274095
theorem B9829471 : Blo 956588 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B4849631 : Blo 956588 4849631 := bstep (se 1 (by rfl) ⟨3637223, by rfl⟩ : syracuseStep 4849631 = 7274447) B7274447
theorem B2425697 : Blo 956588 2425697 := bstep (se 2 (by rfl) ⟨909636, by rfl⟩ : syracuseStep 2425697 = 1819273) B1819273
theorem B4097071 : Blo 956588 4097071 := bstep (se 1 (by rfl) ⟨3072803, by rfl⟩ : syracuseStep 4097071 = 6145607) B6145607
theorem B3638591 : Blo 956588 3638591 := bstep (se 1 (by rfl) ⟨2728943, by rfl⟩ : syracuseStep 3638591 = 5457887) B5457887
theorem B3639289 : Blo 956588 3639289 := bstep (se 2 (by rfl) ⟨1364733, by rfl⟩ : syracuseStep 3639289 = 2729467) B2729467
theorem B9342161 : Blo 956588 9342161 := bstep (se 2 (by rfl) ⟨3503310, by rfl⟩ : syracuseStep 9342161 = 7006621) B7006621
theorem B3640747 : Blo 956588 3640747 := bstep (se 1 (by rfl) ⟨2730560, by rfl⟩ : syracuseStep 3640747 = 5461121) B5461121
theorem B7278335 : Blo 956588 7278335 := bstep (se 1 (by rfl) ⟨5458751, by rfl⟩ : syracuseStep 7278335 = 10917503) B10917503
theorem B14225519 : Blo 956588 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B4854815 : Blo 956588 4854815 := bstep (se 1 (by rfl) ⟨3641111, by rfl⟩ : syracuseStep 4854815 = 7282223) B7282223
theorem B2430263 : Blo 956588 2430263 := bstep (se 1 (by rfl) ⟨1822697, by rfl⟩ : syracuseStep 2430263 = 3645395) B3645395
theorem B2594927 : Blo 956588 2594927 := bstep (se 1 (by rfl) ⟨1946195, by rfl⟩ : syracuseStep 2594927 = 3892391) B3892391
theorem B4856111 : Blo 956588 4856111 := bstep (se 1 (by rfl) ⟨3642083, by rfl⟩ : syracuseStep 4856111 = 7284167) B7284167
theorem B2300519 : Blo 956588 2300519 := bstep (se 1 (by rfl) ⟨1725389, by rfl⟩ : syracuseStep 2300519 = 3450779) B3450779
theorem B957679 : Blo 956588 957679 := bstep (se 1 (by rfl) ⟨718259, by rfl⟩ : syracuseStep 957679 = 1436519) B1436519
theorem B957695 : Blo 956588 957695 := bstep (se 1 (by rfl) ⟨718271, by rfl⟩ : syracuseStep 957695 = 1436543) B1436543
theorem B957723 : Blo 956588 957723 := bstep (se 1 (by rfl) ⟨718292, by rfl⟩ : syracuseStep 957723 = 1436585) B1436585
theorem B957979 : Blo 956588 957979 := bstep (se 1 (by rfl) ⟨718484, by rfl⟩ : syracuseStep 957979 = 1436969) B1436969
theorem B958143 : Blo 956588 958143 := bstep (se 1 (by rfl) ⟨718607, by rfl⟩ : syracuseStep 958143 = 1437215) B1437215
theorem B104898361 : Blo 956588 104898361 := bstep (se 2 (by rfl) ⟨39336885, by rfl⟩ : syracuseStep 104898361 = 78673771) B78673771
theorem B958535 : Blo 956588 958535 := bstep (se 1 (by rfl) ⟨718901, by rfl⟩ : syracuseStep 958535 = 1437803) B1437803
theorem B958911 : Blo 956588 958911 := bstep (se 1 (by rfl) ⟨719183, by rfl⟩ : syracuseStep 958911 = 1438367) B1438367
theorem B3646397 : Blo 956588 3646397 := bstep (se 3 (by rfl) ⟨683699, by rfl⟩ : syracuseStep 3646397 = 1367399) B1367399
theorem B959471 : Blo 956588 959471 := bstep (se 1 (by rfl) ⟨719603, by rfl⟩ : syracuseStep 959471 = 1439207) B1439207
theorem B959615 : Blo 956588 959615 := bstep (se 1 (by rfl) ⟨719711, by rfl⟩ : syracuseStep 959615 = 1439423) B1439423
theorem B6563047 : Blo 956588 6563047 := bstep (se 1 (by rfl) ⟨4922285, by rfl⟩ : syracuseStep 6563047 = 9844571) B9844571
theorem B1615099 : Blo 956588 1615099 := bstep (se 1 (by rfl) ⟨1211324, by rfl⟩ : syracuseStep 1615099 = 2422649) B2422649
theorem B959967 : Blo 956588 959967 := bstep (se 1 (by rfl) ⟨719975, by rfl⟩ : syracuseStep 959967 = 1439951) B1439951
theorem B960091 : Blo 956588 960091 := bstep (se 1 (by rfl) ⟨720068, by rfl⟩ : syracuseStep 960091 = 1440137) B1440137
theorem B5449639 : Blo 956588 5449639 := bstep (se 1 (by rfl) ⟨4087229, by rfl⟩ : syracuseStep 5449639 = 8174459) B8174459
theorem B18459737 : Blo 956588 18459737 := bstep (se 2 (by rfl) ⟨6922401, by rfl⟩ : syracuseStep 18459737 = 13844803) B13844803
theorem B13119259 : Blo 956588 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B19674697 : Blo 956588 19674697 := bstep (se 2 (by rfl) ⟨7378011, by rfl⟩ : syracuseStep 19674697 = 14756023) B14756023
theorem B2046007 : Blo 956588 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B6142175 : Blo 956588 6142175 := bstep (se 1 (by rfl) ⟨4606631, by rfl⟩ : syracuseStep 6142175 = 9213263) B9213263
theorem B12466759 : Blo 956588 12466759 := bstep (se 1 (by rfl) ⟨9350069, by rfl⟩ : syracuseStep 12466759 = 18700139) B18700139
theorem B3455855 : Blo 956588 3455855 := bstep (se 1 (by rfl) ⟨2591891, by rfl⟩ : syracuseStep 3455855 = 5183783) B5183783
theorem B1620857 : Blo 956588 1620857 := bstep (se 2 (by rfl) ⟨607821, by rfl⟩ : syracuseStep 1620857 = 1215643) B1215643
theorem B7978727 : Blo 956588 7978727 := bstep (se 1 (by rfl) ⟨5984045, by rfl⟩ : syracuseStep 7978727 = 11968091) B11968091
theorem B2049151 : Blo 956588 2049151 := bstep (se 1 (by rfl) ⟨1536863, by rfl⟩ : syracuseStep 2049151 = 3073727) B3073727
theorem B3067883 : Blo 956588 3067883 := bstep (se 1 (by rfl) ⟨2300912, by rfl⟩ : syracuseStep 3067883 = 4601825) B4601825
theorem B46714913 : Blo 956588 46714913 := bstep (se 2 (by rfl) ⟨17518092, by rfl⟩ : syracuseStep 46714913 = 35036185) B35036185
theorem B27677375 : Blo 956588 27677375 := bstep (se 1 (by rfl) ⟨20758031, by rfl⟩ : syracuseStep 27677375 = 41516063) B41516063
theorem B3233087 : Blo 956588 3233087 := bstep (se 1 (by rfl) ⟨2424815, by rfl⟩ : syracuseStep 3233087 = 4849631) B4849631
theorem B3233519 : Blo 956588 3233519 := bstep (se 1 (by rfl) ⟨2425139, by rfl⟩ : syracuseStep 3233519 = 4850279) B4850279
theorem B16636427 : Blo 956588 16636427 := bstep (se 1 (by rfl) ⟨12477320, by rfl⟩ : syracuseStep 16636427 = 24954641) B24954641
theorem B6151963 : Blo 956588 6151963 := bstep (se 1 (by rfl) ⟨4613972, by rfl⟩ : syracuseStep 6151963 = 9227945) B9227945
theorem B10904381 : Blo 956588 10904381 := bstep (se 3 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 10904381 = 4089143) B4089143
theorem B10905839 : Blo 956588 10905839 := bstep (se 1 (by rfl) ⟨8179379, by rfl⟩ : syracuseStep 10905839 = 16358759) B16358759
theorem B1435931 : Blo 956588 1435931 := bstep (se 1 (by rfl) ⟨1076948, by rfl⟩ : syracuseStep 1435931 = 2153897) B2153897
theorem B204893459 : Blo 956588 204893459 := bstep (se 1 (by rfl) ⟨153670094, by rfl⟩ : syracuseStep 204893459 = 307340189) B307340189
theorem B6909887 : Blo 956588 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B335704637 : Blo 956588 335704637 := bstep (se 3 (by rfl) ⟨62944619, by rfl⟩ : syracuseStep 335704637 = 125889239) B125889239
theorem B1078015 : Blo 956588 1078015 := bstep (se 1 (by rfl) ⟨808511, by rfl⟩ : syracuseStep 1078015 = 1617023) B1617023
theorem B4846877 : Blo 956588 4846877 := bstep (se 3 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 4846877 = 1817579) B1817579
theorem B1439231 : Blo 956588 1439231 := bstep (se 1 (by rfl) ⟨1079423, by rfl⟩ : syracuseStep 1439231 = 2158847) B2158847
theorem B3733033 : Blo 956588 3733033 := bstep (se 2 (by rfl) ⟨1399887, by rfl⟩ : syracuseStep 3733033 = 2799775) B2799775
theorem B3241727 : Blo 956588 3241727 := bstep (se 1 (by rfl) ⟨2431295, by rfl⟩ : syracuseStep 3241727 = 4862591) B4862591
theorem B13990103 : Blo 956588 13990103 := bstep (se 1 (by rfl) ⟨10492577, by rfl⟩ : syracuseStep 13990103 = 20985155) B20985155
theorem B27687419 : Blo 956588 27687419 := bstep (se 1 (by rfl) ⟨20765564, by rfl⟩ : syracuseStep 27687419 = 41531129) B41531129
theorem B1210879 : Blo 956588 1210879 := bstep (se 1 (by rfl) ⟨908159, by rfl⟩ : syracuseStep 1210879 = 1816319) B1816319
theorem B13105961 : Blo 956588 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B16350011 : Blo 956588 16350011 := bstep (se 1 (by rfl) ⟨12262508, by rfl⟩ : syracuseStep 16350011 = 24525017) B24525017
theorem B2425727 : Blo 956588 2425727 := bstep (se 1 (by rfl) ⟨1819295, by rfl⟩ : syracuseStep 2425727 = 3638591) B3638591
theorem B8750729 : Blo 956588 8750729 := bstep (se 2 (by rfl) ⟨3281523, by rfl⟩ : syracuseStep 8750729 = 6563047) B6563047
theorem B6228107 : Blo 956588 6228107 := bstep (se 1 (by rfl) ⟨4671080, by rfl⟩ : syracuseStep 6228107 = 9342161) B9342161
theorem B4852223 : Blo 956588 4852223 := bstep (se 1 (by rfl) ⟨3639167, by rfl⟩ : syracuseStep 4852223 = 7278335) B7278335
theorem B4852385 : Blo 956588 4852385 := bstep (se 2 (by rfl) ⟨1819644, by rfl⟩ : syracuseStep 4852385 = 3639289) B3639289
theorem B18451583 : Blo 956588 18451583 := bstep (se 1 (by rfl) ⟨13838687, by rfl⟩ : syracuseStep 18451583 = 27677375) B27677375
theorem B4854329 : Blo 956588 4854329 := bstep (se 2 (by rfl) ⟨1820373, by rfl⟩ : syracuseStep 4854329 = 3640747) B3640747
theorem B6919805 : Blo 956588 6919805 := bstep (se 3 (by rfl) ⟨1297463, by rfl⟩ : syracuseStep 6919805 = 2594927) B2594927
theorem B2430931 : Blo 956588 2430931 := bstep (se 1 (by rfl) ⟨1823198, by rfl⟩ : syracuseStep 2430931 = 3646397) B3646397
theorem B957287 : Blo 956588 957287 := bstep (se 1 (by rfl) ⟨717965, by rfl⟩ : syracuseStep 957287 = 1435931) B1435931
theorem B6134717 : Blo 956588 6134717 := bstep (se 3 (by rfl) ⟨1150259, by rfl⟩ : syracuseStep 6134717 = 2300519) B2300519
theorem B2728009 : Blo 956588 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B1614505 : Blo 956588 1614505 := bstep (se 2 (by rfl) ⟨605439, by rfl⟩ : syracuseStep 1614505 = 1210879) B1210879
theorem B16622345 : Blo 956588 16622345 := bstep (se 2 (by rfl) ⟨6233379, by rfl⟩ : syracuseStep 16622345 = 12466759) B12466759
theorem B959487 : Blo 956588 959487 := bstep (se 1 (by rfl) ⟨719615, by rfl⟩ : syracuseStep 959487 = 1439231) B1439231
theorem B18458279 : Blo 956588 18458279 := bstep (se 1 (by rfl) ⟨13843709, by rfl⟩ : syracuseStep 18458279 = 27687419) B27687419
theorem B2303903 : Blo 956588 2303903 := bstep (se 1 (by rfl) ⟨1727927, by rfl⟩ : syracuseStep 2303903 = 3455855) B3455855
theorem B21276605 : Blo 956588 21276605 := bstep (se 3 (by rfl) ⟨3989363, by rfl⟩ : syracuseStep 21276605 = 7978727) B7978727
theorem B8202617 : Blo 956588 8202617 := bstep (se 2 (by rfl) ⟨3075981, by rfl⟩ : syracuseStep 8202617 = 6151963) B6151963
theorem B139864481 : Blo 956588 139864481 := bstep (se 2 (by rfl) ⟨52449180, by rfl⟩ : syracuseStep 139864481 = 104898361) B104898361
theorem B18426365 : Blo 956588 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B1617131 : Blo 956588 1617131 := bstep (se 1 (by rfl) ⟨1212848, by rfl⟩ : syracuseStep 1617131 = 2425697) B2425697
theorem B2732201 : Blo 956588 2732201 := bstep (se 2 (by rfl) ⟨1024575, by rfl⟩ : syracuseStep 2732201 = 2049151) B2049151
theorem B2045255 : Blo 956588 2045255 := bstep (se 1 (by rfl) ⟨1533941, by rfl⟩ : syracuseStep 2045255 = 3067883) B3067883
theorem B31143275 : Blo 956588 31143275 := bstep (se 1 (by rfl) ⟨23357456, by rfl⟩ : syracuseStep 31143275 = 46714913) B46714913
theorem B9483679 : Blo 956588 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B1620175 : Blo 956588 1620175 := bstep (se 1 (by rfl) ⟨1215131, by rfl⟩ : syracuseStep 1620175 = 2430263) B2430263
theorem B11090951 : Blo 956588 11090951 := bstep (se 1 (by rfl) ⟨8318213, by rfl⟩ : syracuseStep 11090951 = 16636427) B16636427
theorem B12306491 : Blo 956588 12306491 := bstep (se 1 (by rfl) ⟨9229868, by rfl⟩ : syracuseStep 12306491 = 18459737) B18459737
theorem B26232929 : Blo 956588 26232929 := bstep (se 2 (by rfl) ⟨9837348, by rfl⟩ : syracuseStep 26232929 = 19674697) B19674697
theorem B136595639 : Blo 956588 136595639 := bstep (se 1 (by rfl) ⟨102446729, by rfl⟩ : syracuseStep 136595639 = 204893459) B204893459
theorem B3231251 : Blo 956588 3231251 := bstep (se 1 (by rfl) ⟨2423438, by rfl⟩ : syracuseStep 3231251 = 4846877) B4846877
theorem B9326735 : Blo 956588 9326735 := bstep (se 1 (by rfl) ⟨6995051, by rfl⟩ : syracuseStep 9326735 = 13990103) B13990103
theorem B8737307 : Blo 956588 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B10900007 : Blo 956588 10900007 := bstep (se 1 (by rfl) ⟨8175005, by rfl⟩ : syracuseStep 10900007 = 16350011) B16350011
theorem B5462761 : Blo 956588 5462761 := bstep (se 2 (by rfl) ⟨2048535, by rfl⟩ : syracuseStep 5462761 = 4097071) B4097071
theorem B2153465 : Blo 956588 2153465 := bstep (se 2 (by rfl) ⟨807549, by rfl⟩ : syracuseStep 2153465 = 1615099) B1615099
theorem B7266185 : Blo 956588 7266185 := bstep (se 2 (by rfl) ⟨2724819, by rfl⟩ : syracuseStep 7266185 = 5449639) B5449639
theorem B3236543 : Blo 956588 3236543 := bstep (se 1 (by rfl) ⟨2427407, by rfl⟩ : syracuseStep 3236543 = 4854815) B4854815
theorem B2155391 : Blo 956588 2155391 := bstep (se 1 (by rfl) ⟨1616543, by rfl⟩ : syracuseStep 2155391 = 3233087) B3233087
theorem B2155679 : Blo 956588 2155679 := bstep (se 1 (by rfl) ⟨1616759, by rfl⟩ : syracuseStep 2155679 = 3233519) B3233519
theorem B3237407 : Blo 956588 3237407 := bstep (se 1 (by rfl) ⟨2428055, by rfl⟩ : syracuseStep 3237407 = 4856111) B4856111
theorem B17492345 : Blo 956588 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B7269587 : Blo 956588 7269587 := bstep (se 1 (by rfl) ⟨5452190, by rfl⟩ : syracuseStep 7269587 = 10904381) B10904381
theorem B1437353 : Blo 956588 1437353 := bstep (se 2 (by rfl) ⟨539007, by rfl⟩ : syracuseStep 1437353 = 1078015) B1078015
theorem B7270559 : Blo 956588 7270559 := bstep (se 1 (by rfl) ⟨5452919, by rfl⟩ : syracuseStep 7270559 = 10905839) B10905839
theorem B4977377 : Blo 956588 4977377 := bstep (se 2 (by rfl) ⟨1866516, by rfl⟩ : syracuseStep 4977377 = 3733033) B3733033
theorem B223803091 : Blo 956588 223803091 := bstep (se 1 (by rfl) ⟨167852318, by rfl⟩ : syracuseStep 223803091 = 335704637) B335704637
theorem B2161151 : Blo 956588 2161151 := bstep (se 1 (by rfl) ⟨1620863, by rfl⟩ : syracuseStep 2161151 = 3241727) B3241727
theorem B4094783 : Blo 956588 4094783 := bstep (se 1 (by rfl) ⟨3071087, by rfl⟩ : syracuseStep 4094783 = 6142175) B6142175
theorem B1080571 : Blo 956588 1080571 := bstep (se 1 (by rfl) ⟨810428, by rfl⟩ : syracuseStep 1080571 = 1620857) B1620857
theorem B3637345 : Blo 956588 3637345 := bstep (se 2 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 3637345 = 2728009) B2728009
theorem B5833819 : Blo 956588 5833819 := bstep (se 1 (by rfl) ⟨4375364, by rfl⟩ : syracuseStep 5833819 = 8750729) B8750729
theorem B91063759 : Blo 956588 91063759 := bstep (se 1 (by rfl) ⟨68297819, by rfl⟩ : syracuseStep 91063759 = 136595639) B136595639
theorem B958235 : Blo 956588 958235 := bstep (se 1 (by rfl) ⟨718676, by rfl⟩ : syracuseStep 958235 = 1437353) B1437353
theorem B3318251 : Blo 956588 3318251 := bstep (se 1 (by rfl) ⟨2488688, by rfl⟩ : syracuseStep 3318251 = 4977377) B4977377
theorem B7283681 : Blo 956588 7283681 := bstep (se 2 (by rfl) ⟨2731380, by rfl⟩ : syracuseStep 7283681 = 5462761) B5462761
theorem B1193616485 : Blo 956588 1193616485 := bstep (se 4 (by rfl) ⟨111901545, by rfl⟩ : syracuseStep 1193616485 = 223803091) B223803091
theorem B2729855 : Blo 956588 2729855 := bstep (se 1 (by rfl) ⟨2047391, by rfl⟩ : syracuseStep 2729855 = 4094783) B4094783
theorem B1617151 : Blo 956588 1617151 := bstep (se 1 (by rfl) ⟨1212863, by rfl⟩ : syracuseStep 1617151 = 2425727) B2425727
theorem B8204327 : Blo 956588 8204327 := bstep (se 1 (by rfl) ⟨6153245, by rfl⟩ : syracuseStep 8204327 = 12306491) B12306491
theorem B12301055 : Blo 956588 12301055 := bstep (se 1 (by rfl) ⟨9225791, by rfl⟩ : syracuseStep 12301055 = 18451583) B18451583
theorem B5454013 : Blo 956588 5454013 := bstep (se 3 (by rfl) ⟨1022627, by rfl⟩ : syracuseStep 5454013 = 2045255) B2045255
theorem B56737613 : Blo 956588 56737613 := bstep (se 3 (by rfl) ⟨10638302, by rfl⟩ : syracuseStep 56737613 = 21276605) B21276605
theorem B12305519 : Blo 956588 12305519 := bstep (se 1 (by rfl) ⟨9229139, by rfl⟩ : syracuseStep 12305519 = 18458279) B18458279
theorem B93242987 : Blo 956588 93242987 := bstep (se 1 (by rfl) ⟨69932240, by rfl⟩ : syracuseStep 93242987 = 139864481) B139864481
theorem B50579621 : Blo 956588 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B1821467 : Blo 956588 1821467 := bstep (se 1 (by rfl) ⟨1366100, by rfl⟩ : syracuseStep 1821467 = 2732201) B2732201
theorem B20762183 : Blo 956588 20762183 := bstep (se 1 (by rfl) ⟨15571637, by rfl⟩ : syracuseStep 20762183 = 31143275) B31143275
theorem B7393967 : Blo 956588 7393967 := bstep (se 1 (by rfl) ⟨5545475, by rfl⟩ : syracuseStep 7393967 = 11090951) B11090951
theorem B2152673 : Blo 956588 2152673 := bstep (se 2 (by rfl) ⟨807252, by rfl⟩ : syracuseStep 2152673 = 1614505) B1614505
theorem B17488619 : Blo 956588 17488619 := bstep (se 1 (by rfl) ⟨13116464, by rfl⟩ : syracuseStep 17488619 = 26232929) B26232929
theorem B4152071 : Blo 956588 4152071 := bstep (se 1 (by rfl) ⟨3114053, by rfl⟩ : syracuseStep 4152071 = 6228107) B6228107
theorem B3234815 : Blo 956588 3234815 := bstep (se 1 (by rfl) ⟨2426111, by rfl⟩ : syracuseStep 3234815 = 4852223) B4852223
theorem B3234923 : Blo 956588 3234923 := bstep (se 1 (by rfl) ⟨2426192, by rfl⟩ : syracuseStep 3234923 = 4852385) B4852385
theorem B44326253 : Blo 956588 44326253 := bstep (se 3 (by rfl) ⟨8311172, by rfl⟩ : syracuseStep 44326253 = 16622345) B16622345
theorem B2154167 : Blo 956588 2154167 := bstep (se 1 (by rfl) ⟨1615625, by rfl⟩ : syracuseStep 2154167 = 3231251) B3231251
theorem B6217823 : Blo 956588 6217823 := bstep (se 1 (by rfl) ⟨4663367, by rfl⟩ : syracuseStep 6217823 = 9326735) B9326735
theorem B5824871 : Blo 956588 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B7266671 : Blo 956588 7266671 := bstep (se 1 (by rfl) ⟨5450003, by rfl⟩ : syracuseStep 7266671 = 10900007) B10900007
theorem B3236219 : Blo 956588 3236219 := bstep (se 1 (by rfl) ⟨2427164, by rfl⟩ : syracuseStep 3236219 = 4854329) B4854329
theorem B4613203 : Blo 956588 4613203 := bstep (se 1 (by rfl) ⟨3459902, by rfl⟩ : syracuseStep 4613203 = 6919805) B6919805
theorem B4089811 : Blo 956588 4089811 := bstep (se 1 (by rfl) ⟨3067358, by rfl⟩ : syracuseStep 4089811 = 6134717) B6134717
theorem B1435643 : Blo 956588 1435643 := bstep (se 1 (by rfl) ⟨1076732, by rfl⟩ : syracuseStep 1435643 = 2153465) B2153465
theorem B4844123 : Blo 956588 4844123 := bstep (se 1 (by rfl) ⟨3633092, by rfl⟩ : syracuseStep 4844123 = 7266185) B7266185
theorem B2157695 : Blo 956588 2157695 := bstep (se 1 (by rfl) ⟨1618271, by rfl⟩ : syracuseStep 2157695 = 3236543) B3236543
theorem B1436927 : Blo 956588 1436927 := bstep (se 1 (by rfl) ⟨1077695, by rfl⟩ : syracuseStep 1436927 = 2155391) B2155391
theorem B1437119 : Blo 956588 1437119 := bstep (se 1 (by rfl) ⟨1077839, by rfl⟩ : syracuseStep 1437119 = 2155679) B2155679
theorem B2158271 : Blo 956588 2158271 := bstep (se 1 (by rfl) ⟨1618703, by rfl⟩ : syracuseStep 2158271 = 3237407) B3237407
theorem B1535935 : Blo 956588 1535935 := bstep (se 1 (by rfl) ⟨1151951, by rfl⟩ : syracuseStep 1535935 = 2303903) B2303903
theorem B11661563 : Blo 956588 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B5468411 : Blo 956588 5468411 := bstep (se 1 (by rfl) ⟨4101308, by rfl⟩ : syracuseStep 5468411 = 8202617) B8202617
theorem B12284243 : Blo 956588 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B4846391 : Blo 956588 4846391 := bstep (se 1 (by rfl) ⟨3634793, by rfl⟩ : syracuseStep 4846391 = 7269587) B7269587
theorem B1078087 : Blo 956588 1078087 := bstep (se 1 (by rfl) ⟨808565, by rfl⟩ : syracuseStep 1078087 = 1617131) B1617131
theorem B3241241 : Blo 956588 3241241 := bstep (se 2 (by rfl) ⟨1215465, by rfl⟩ : syracuseStep 3241241 = 2430931) B2430931
theorem B4847039 : Blo 956588 4847039 := bstep (se 1 (by rfl) ⟨3635279, by rfl⟩ : syracuseStep 4847039 = 7270559) B7270559
theorem B2160233 : Blo 956588 2160233 := bstep (se 2 (by rfl) ⟨810087, by rfl⟩ : syracuseStep 2160233 = 1620175) B1620175
theorem B1440761 : Blo 956588 1440761 := bstep (se 2 (by rfl) ⟨540285, by rfl⟩ : syracuseStep 1440761 = 1080571) B1080571
theorem B1440767 : Blo 956588 1440767 := bstep (se 1 (by rfl) ⟨1080575, by rfl⟩ : syracuseStep 1440767 = 2161151) B2161151
theorem B4849793 : Blo 956588 4849793 := bstep (se 2 (by rfl) ⟨1818672, by rfl⟩ : syracuseStep 4849793 = 3637345) B3637345
theorem B62161991 : Blo 956588 62161991 := bstep (se 1 (by rfl) ⟨46621493, by rfl⟩ : syracuseStep 62161991 = 93242987) B93242987
theorem B8848669 : Blo 956588 8848669 := bstep (se 3 (by rfl) ⟨1659125, by rfl⟩ : syracuseStep 8848669 = 3318251) B3318251
theorem B33719747 : Blo 956588 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B4855787 : Blo 956588 4855787 := bstep (se 1 (by rfl) ⟨3641840, by rfl⟩ : syracuseStep 4855787 = 7283681) B7283681
theorem B795744323 : Blo 956588 795744323 := bstep (se 1 (by rfl) ⟨596808242, by rfl⟩ : syracuseStep 795744323 = 1193616485) B1193616485
theorem B957095 : Blo 956588 957095 := bstep (se 1 (by rfl) ⟨717821, by rfl⟩ : syracuseStep 957095 = 1435643) B1435643
theorem B4857245 : Blo 956588 4857245 := bstep (se 3 (by rfl) ⟨910733, by rfl⟩ : syracuseStep 4857245 = 1821467) B1821467
theorem B957951 : Blo 956588 957951 := bstep (se 1 (by rfl) ⟨718463, by rfl⟩ : syracuseStep 957951 = 1436927) B1436927
theorem B958079 : Blo 956588 958079 := bstep (se 1 (by rfl) ⟨718559, by rfl⟩ : syracuseStep 958079 = 1437119) B1437119
theorem B7774375 : Blo 956588 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B3645607 : Blo 956588 3645607 := bstep (se 1 (by rfl) ⟨2734205, by rfl⟩ : syracuseStep 3645607 = 5468411) B5468411
theorem B8200703 : Blo 956588 8200703 := bstep (se 1 (by rfl) ⟨6150527, by rfl⟩ : syracuseStep 8200703 = 12301055) B12301055
theorem B960507 : Blo 956588 960507 := bstep (se 1 (by rfl) ⟨720380, by rfl⟩ : syracuseStep 960507 = 1440761) B1440761
theorem B960511 : Blo 956588 960511 := bstep (se 1 (by rfl) ⟨720383, by rfl⟩ : syracuseStep 960511 = 1440767) B1440767
theorem B37825075 : Blo 956588 37825075 := bstep (se 1 (by rfl) ⟨28368806, by rfl⟩ : syracuseStep 37825075 = 56737613) B56737613
theorem B8203679 : Blo 956588 8203679 := bstep (se 1 (by rfl) ⟨6152759, by rfl⟩ : syracuseStep 8203679 = 12305519) B12305519
theorem B7778425 : Blo 956588 7778425 := bstep (se 2 (by rfl) ⟨2916909, by rfl⟩ : syracuseStep 7778425 = 5833819) B5833819
theorem B121418345 : Blo 956588 121418345 := bstep (se 2 (by rfl) ⟨45531879, by rfl⟩ : syracuseStep 121418345 = 91063759) B91063759
theorem B13841455 : Blo 956588 13841455 := bstep (se 1 (by rfl) ⟨10381091, by rfl⟩ : syracuseStep 13841455 = 20762183) B20762183
theorem B5453081 : Blo 956588 5453081 := bstep (se 2 (by rfl) ⟨2044905, by rfl⟩ : syracuseStep 5453081 = 4089811) B4089811
theorem B4929311 : Blo 956588 4929311 := bstep (se 1 (by rfl) ⟨3696983, by rfl⟩ : syracuseStep 4929311 = 7393967) B7393967
theorem B2047913 : Blo 956588 2047913 := bstep (se 2 (by rfl) ⟨767967, by rfl⟩ : syracuseStep 2047913 = 1535935) B1535935
theorem B4145215 : Blo 956588 4145215 := bstep (se 1 (by rfl) ⟨3108911, by rfl⟩ : syracuseStep 4145215 = 6217823) B6217823
theorem B3883247 : Blo 956588 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B1819903 : Blo 956588 1819903 := bstep (se 1 (by rfl) ⟨1364927, by rfl⟩ : syracuseStep 1819903 = 2729855) B2729855
theorem B3229415 : Blo 956588 3229415 := bstep (se 1 (by rfl) ⟨2422061, by rfl⟩ : syracuseStep 3229415 = 4844123) B4844123
theorem B3230927 : Blo 956588 3230927 := bstep (se 1 (by rfl) ⟨2423195, by rfl⟩ : syracuseStep 3230927 = 4846391) B4846391
theorem B3231359 : Blo 956588 3231359 := bstep (se 1 (by rfl) ⟨2423519, by rfl⟩ : syracuseStep 3231359 = 4847039) B4847039
theorem B1435115 : Blo 956588 1435115 := bstep (se 1 (by rfl) ⟨1076336, by rfl⟩ : syracuseStep 1435115 = 2152673) B2152673
theorem B2156201 : Blo 956588 2156201 := bstep (se 2 (by rfl) ⟨808575, by rfl⟩ : syracuseStep 2156201 = 1617151) B1617151
theorem B11659079 : Blo 956588 11659079 := bstep (se 1 (by rfl) ⟨8744309, by rfl⟩ : syracuseStep 11659079 = 17488619) B17488619
theorem B2156543 : Blo 956588 2156543 := bstep (se 1 (by rfl) ⟨1617407, by rfl⟩ : syracuseStep 2156543 = 3234815) B3234815
theorem B2156615 : Blo 956588 2156615 := bstep (se 1 (by rfl) ⟨1617461, by rfl⟩ : syracuseStep 2156615 = 3234923) B3234923
theorem B29550835 : Blo 956588 29550835 := bstep (se 1 (by rfl) ⟨22163126, by rfl⟩ : syracuseStep 29550835 = 44326253) B44326253
theorem B1436111 : Blo 956588 1436111 := bstep (se 1 (by rfl) ⟨1077083, by rfl⟩ : syracuseStep 1436111 = 2154167) B2154167
theorem B4844447 : Blo 956588 4844447 := bstep (se 1 (by rfl) ⟨3633335, by rfl⟩ : syracuseStep 4844447 = 7266671) B7266671
theorem B2157479 : Blo 956588 2157479 := bstep (se 1 (by rfl) ⟨1618109, by rfl⟩ : syracuseStep 2157479 = 3236219) B3236219
theorem B24603749 : Blo 956588 24603749 := bstep (se 4 (by rfl) ⟨2306601, by rfl⟩ : syracuseStep 24603749 = 4613203) B4613203
theorem B1437449 : Blo 956588 1437449 := bstep (se 2 (by rfl) ⟨539043, by rfl⟩ : syracuseStep 1437449 = 1078087) B1078087
theorem B11072189 : Blo 956588 11072189 := bstep (se 3 (by rfl) ⟨2076035, by rfl⟩ : syracuseStep 11072189 = 4152071) B4152071
theorem B1438463 : Blo 956588 1438463 := bstep (se 1 (by rfl) ⟨1078847, by rfl⟩ : syracuseStep 1438463 = 2157695) B2157695
theorem B1438847 : Blo 956588 1438847 := bstep (se 1 (by rfl) ⟨1079135, by rfl⟩ : syracuseStep 1438847 = 2158271) B2158271
theorem B5469551 : Blo 956588 5469551 := bstep (se 1 (by rfl) ⟨4102163, by rfl⟩ : syracuseStep 5469551 = 8204327) B8204327
theorem B8189495 : Blo 956588 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B7272017 : Blo 956588 7272017 := bstep (se 2 (by rfl) ⟨2727006, by rfl⟩ : syracuseStep 7272017 = 5454013) B5454013
theorem B2160827 : Blo 956588 2160827 := bstep (se 1 (by rfl) ⟨1620620, by rfl⟩ : syracuseStep 2160827 = 3241241) B3241241
theorem B1440155 : Blo 956588 1440155 := bstep (se 1 (by rfl) ⟨1080116, by rfl⟩ : syracuseStep 1440155 = 2160233) B2160233
theorem B2588831 : Blo 956588 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B2426537 : Blo 956588 2426537 := bstep (se 2 (by rfl) ⟨909951, by rfl⟩ : syracuseStep 2426537 = 1819903) B1819903
theorem B11798225 : Blo 956588 11798225 := bstep (se 2 (by rfl) ⟨4424334, by rfl⟩ : syracuseStep 11798225 = 8848669) B8848669
theorem B89919325 : Blo 956588 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B956743 : Blo 956588 956743 := bstep (se 1 (by rfl) ⟨717557, by rfl⟩ : syracuseStep 956743 = 1435115) B1435115
theorem B7772719 : Blo 956588 7772719 := bstep (se 1 (by rfl) ⟨5829539, by rfl⟩ : syracuseStep 7772719 = 11659079) B11659079
theorem B18455273 : Blo 956588 18455273 := bstep (se 2 (by rfl) ⟨6920727, by rfl⟩ : syracuseStep 18455273 = 13841455) B13841455
theorem B957407 : Blo 956588 957407 := bstep (se 1 (by rfl) ⟨718055, by rfl⟩ : syracuseStep 957407 = 1436111) B1436111
theorem B958299 : Blo 956588 958299 := bstep (se 1 (by rfl) ⟨718724, by rfl⟩ : syracuseStep 958299 = 1437449) B1437449
theorem B80945563 : Blo 956588 80945563 := bstep (se 1 (by rfl) ⟨60709172, by rfl⟩ : syracuseStep 80945563 = 121418345) B121418345
theorem B7381459 : Blo 956588 7381459 := bstep (se 1 (by rfl) ⟨5536094, by rfl⟩ : syracuseStep 7381459 = 11072189) B11072189
theorem B958975 : Blo 956588 958975 := bstep (se 1 (by rfl) ⟨719231, by rfl⟩ : syracuseStep 958975 = 1438463) B1438463
theorem B959231 : Blo 956588 959231 := bstep (se 1 (by rfl) ⟨719423, by rfl⟩ : syracuseStep 959231 = 1438847) B1438847
theorem B3646367 : Blo 956588 3646367 := bstep (se 1 (by rfl) ⟨2734775, by rfl⟩ : syracuseStep 3646367 = 5469551) B5469551
theorem B3286207 : Blo 956588 3286207 := bstep (se 1 (by rfl) ⟨2464655, by rfl⟩ : syracuseStep 3286207 = 4929311) B4929311
theorem B960103 : Blo 956588 960103 := bstep (se 1 (by rfl) ⟨720077, by rfl⟩ : syracuseStep 960103 = 1440155) B1440155
theorem B10365833 : Blo 956588 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B4860809 : Blo 956588 4860809 := bstep (se 2 (by rfl) ⟨1822803, by rfl⟩ : syracuseStep 4860809 = 3645607) B3645607
theorem B201733733 : Blo 956588 201733733 := bstep (se 4 (by rfl) ⟨18912537, by rfl⟩ : syracuseStep 201733733 = 37825075) B37825075
theorem B39401113 : Blo 956588 39401113 := bstep (se 2 (by rfl) ⟨14775417, by rfl⟩ : syracuseStep 39401113 = 29550835) B29550835
theorem B530496215 : Blo 956588 530496215 := bstep (se 1 (by rfl) ⟨397872161, by rfl⟩ : syracuseStep 530496215 = 795744323) B795744323
theorem B10371233 : Blo 956588 10371233 := bstep (se 2 (by rfl) ⟨3889212, by rfl⟩ : syracuseStep 10371233 = 7778425) B7778425
theorem B3229631 : Blo 956588 3229631 := bstep (se 1 (by rfl) ⟨2422223, by rfl⟩ : syracuseStep 3229631 = 4844447) B4844447
theorem B16402499 : Blo 956588 16402499 := bstep (se 1 (by rfl) ⟨12301874, by rfl⟩ : syracuseStep 16402499 = 24603749) B24603749
theorem B5459663 : Blo 956588 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B1365275 : Blo 956588 1365275 := bstep (se 1 (by rfl) ⟨1023956, by rfl⟩ : syracuseStep 1365275 = 2047913) B2047913
theorem B5526953 : Blo 956588 5526953 := bstep (se 2 (by rfl) ⟨2072607, by rfl⟩ : syracuseStep 5526953 = 4145215) B4145215
theorem B3233195 : Blo 956588 3233195 := bstep (se 1 (by rfl) ⟨2424896, by rfl⟩ : syracuseStep 3233195 = 4849793) B4849793
theorem B41441327 : Blo 956588 41441327 := bstep (se 1 (by rfl) ⟨31080995, by rfl⟩ : syracuseStep 41441327 = 62161991) B62161991
theorem B2152943 : Blo 956588 2152943 := bstep (se 1 (by rfl) ⟨1614707, by rfl⟩ : syracuseStep 2152943 = 3229415) B3229415
theorem B2153951 : Blo 956588 2153951 := bstep (se 1 (by rfl) ⟨1615463, by rfl⟩ : syracuseStep 2153951 = 3230927) B3230927
theorem B2154239 : Blo 956588 2154239 := bstep (se 1 (by rfl) ⟨1615679, by rfl⟩ : syracuseStep 2154239 = 3231359) B3231359
theorem B3237191 : Blo 956588 3237191 := bstep (se 1 (by rfl) ⟨2427893, by rfl⟩ : syracuseStep 3237191 = 4855787) B4855787
theorem B3238163 : Blo 956588 3238163 := bstep (se 1 (by rfl) ⟨2428622, by rfl⟩ : syracuseStep 3238163 = 4857245) B4857245
theorem B5467135 : Blo 956588 5467135 := bstep (se 1 (by rfl) ⟨4100351, by rfl⟩ : syracuseStep 5467135 = 8200703) B8200703
theorem B1437467 : Blo 956588 1437467 := bstep (se 1 (by rfl) ⟨1078100, by rfl⟩ : syracuseStep 1437467 = 2156201) B2156201
theorem B1437695 : Blo 956588 1437695 := bstep (se 1 (by rfl) ⟨1078271, by rfl⟩ : syracuseStep 1437695 = 2156543) B2156543
theorem B1437743 : Blo 956588 1437743 := bstep (se 1 (by rfl) ⟨1078307, by rfl⟩ : syracuseStep 1437743 = 2156615) B2156615
theorem B1438319 : Blo 956588 1438319 := bstep (se 1 (by rfl) ⟨1078739, by rfl⟩ : syracuseStep 1438319 = 2157479) B2157479
theorem B5469119 : Blo 956588 5469119 := bstep (se 1 (by rfl) ⟨4101839, by rfl⟩ : syracuseStep 5469119 = 8203679) B8203679
theorem B3635387 : Blo 956588 3635387 := bstep (se 1 (by rfl) ⟨2726540, by rfl⟩ : syracuseStep 3635387 = 5453081) B5453081
theorem B4848011 : Blo 956588 4848011 := bstep (se 1 (by rfl) ⟨3636008, by rfl⟩ : syracuseStep 4848011 = 7272017) B7272017
theorem B1440551 : Blo 956588 1440551 := bstep (se 1 (by rfl) ⟨1080413, by rfl⟩ : syracuseStep 1440551 = 2160827) B2160827
theorem B6914155 : Blo 956588 6914155 := bstep (se 1 (by rfl) ⟨5185616, by rfl⟩ : syracuseStep 6914155 = 10371233) B10371233
theorem B7865483 : Blo 956588 7865483 := bstep (se 1 (by rfl) ⟨5899112, by rfl⟩ : syracuseStep 7865483 = 11798225) B11798225
theorem B3639775 : Blo 956588 3639775 := bstep (se 1 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 3639775 = 5459663) B5459663
theorem B3640733 : Blo 956588 3640733 := bstep (se 3 (by rfl) ⟨682637, by rfl⟩ : syracuseStep 3640733 = 1365275) B1365275
theorem B27627551 : Blo 956588 27627551 := bstep (se 1 (by rfl) ⟨20720663, by rfl⟩ : syracuseStep 27627551 = 41441327) B41441327
theorem B2430911 : Blo 956588 2430911 := bstep (se 1 (by rfl) ⟨1823183, by rfl⟩ : syracuseStep 2430911 = 3646367) B3646367
theorem B52534817 : Blo 956588 52534817 := bstep (se 2 (by rfl) ⟨19700556, by rfl⟩ : syracuseStep 52534817 = 39401113) B39401113
theorem B958311 : Blo 956588 958311 := bstep (se 1 (by rfl) ⟨718733, by rfl⟩ : syracuseStep 958311 = 1437467) B1437467
theorem B958463 : Blo 956588 958463 := bstep (se 1 (by rfl) ⟨718847, by rfl⟩ : syracuseStep 958463 = 1437695) B1437695
theorem B958495 : Blo 956588 958495 := bstep (se 1 (by rfl) ⟨718871, by rfl⟩ : syracuseStep 958495 = 1437743) B1437743
theorem B958879 : Blo 956588 958879 := bstep (se 1 (by rfl) ⟨719159, by rfl⟩ : syracuseStep 958879 = 1438319) B1438319
theorem B3646079 : Blo 956588 3646079 := bstep (se 1 (by rfl) ⟨2734559, by rfl⟩ : syracuseStep 3646079 = 5469119) B5469119
theorem B10363625 : Blo 956588 10363625 := bstep (se 2 (by rfl) ⟨3886359, by rfl⟩ : syracuseStep 10363625 = 7772719) B7772719
theorem B134489155 : Blo 956588 134489155 := bstep (se 1 (by rfl) ⟨100866866, by rfl⟩ : syracuseStep 134489155 = 201733733) B201733733
theorem B479569733 : Blo 956588 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B960367 : Blo 956588 960367 := bstep (se 1 (by rfl) ⟨720275, by rfl⟩ : syracuseStep 960367 = 1440551) B1440551
theorem B9841945 : Blo 956588 9841945 := bstep (se 2 (by rfl) ⟨3690729, by rfl⟩ : syracuseStep 9841945 = 7381459) B7381459
theorem B1617691 : Blo 956588 1617691 := bstep (se 1 (by rfl) ⟨1213268, by rfl⟩ : syracuseStep 1617691 = 2426537) B2426537
theorem B3684635 : Blo 956588 3684635 := bstep (se 1 (by rfl) ⟨2763476, by rfl⟩ : syracuseStep 3684635 = 5526953) B5526953
theorem B7289513 : Blo 956588 7289513 := bstep (se 2 (by rfl) ⟨2733567, by rfl⟩ : syracuseStep 7289513 = 5467135) B5467135
theorem B12303515 : Blo 956588 12303515 := bstep (se 1 (by rfl) ⟨9227636, by rfl⟩ : syracuseStep 12303515 = 18455273) B18455273
theorem B3232007 : Blo 956588 3232007 := bstep (se 1 (by rfl) ⟨2424005, by rfl⟩ : syracuseStep 3232007 = 4848011) B4848011
theorem B1725887 : Blo 956588 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B107927417 : Blo 956588 107927417 := bstep (se 2 (by rfl) ⟨40472781, by rfl⟩ : syracuseStep 107927417 = 80945563) B80945563
theorem B2153087 : Blo 956588 2153087 := bstep (se 1 (by rfl) ⟨1614815, by rfl⟩ : syracuseStep 2153087 = 3229631) B3229631
theorem B10934999 : Blo 956588 10934999 := bstep (se 1 (by rfl) ⟨8201249, by rfl⟩ : syracuseStep 10934999 = 16402499) B16402499
theorem B4381609 : Blo 956588 4381609 := bstep (se 2 (by rfl) ⟨1643103, by rfl⟩ : syracuseStep 4381609 = 3286207) B3286207
theorem B2155463 : Blo 956588 2155463 := bstep (se 1 (by rfl) ⟨1616597, by rfl⟩ : syracuseStep 2155463 = 3233195) B3233195
theorem B1435295 : Blo 956588 1435295 := bstep (se 1 (by rfl) ⟨1076471, by rfl⟩ : syracuseStep 1435295 = 2152943) B2152943
theorem B1435967 : Blo 956588 1435967 := bstep (se 1 (by rfl) ⟨1076975, by rfl⟩ : syracuseStep 1435967 = 2153951) B2153951
theorem B1436159 : Blo 956588 1436159 := bstep (se 1 (by rfl) ⟨1077119, by rfl⟩ : syracuseStep 1436159 = 2154239) B2154239
theorem B2158127 : Blo 956588 2158127 := bstep (se 1 (by rfl) ⟨1618595, by rfl⟩ : syracuseStep 2158127 = 3237191) B3237191
theorem B2158775 : Blo 956588 2158775 := bstep (se 1 (by rfl) ⟨1619081, by rfl⟩ : syracuseStep 2158775 = 3238163) B3238163
theorem B6910555 : Blo 956588 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B3240539 : Blo 956588 3240539 := bstep (se 1 (by rfl) ⟨2430404, by rfl⟩ : syracuseStep 3240539 = 4860809) B4860809
theorem B2423591 : Blo 956588 2423591 := bstep (se 1 (by rfl) ⟨1817693, by rfl⟩ : syracuseStep 2423591 = 3635387) B3635387
theorem B353664143 : Blo 956588 353664143 := bstep (se 1 (by rfl) ⟨265248107, by rfl⟩ : syracuseStep 353664143 = 530496215) B530496215
theorem B2427155 : Blo 956588 2427155 := bstep (se 1 (by rfl) ⟨1820366, by rfl⟩ : syracuseStep 2427155 = 3640733) B3640733
theorem B18418367 : Blo 956588 18418367 := bstep (se 1 (by rfl) ⟨13813775, by rfl⟩ : syracuseStep 18418367 = 27627551) B27627551
theorem B20974621 : Blo 956588 20974621 := bstep (se 3 (by rfl) ⟨3932741, by rfl⟩ : syracuseStep 20974621 = 7865483) B7865483
theorem B4853033 : Blo 956588 4853033 := bstep (se 2 (by rfl) ⟨1819887, by rfl⟩ : syracuseStep 4853033 = 3639775) B3639775
theorem B287806445 : Blo 956588 287806445 := bstep (se 3 (by rfl) ⟨53963708, by rfl⟩ : syracuseStep 287806445 = 107927417) B107927417
theorem B2430719 : Blo 956588 2430719 := bstep (se 1 (by rfl) ⟨1823039, by rfl⟩ : syracuseStep 2430719 = 3646079) B3646079
theorem B9214073 : Blo 956588 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B956863 : Blo 956588 956863 := bstep (se 1 (by rfl) ⟨717647, by rfl⟩ : syracuseStep 956863 = 1435295) B1435295
theorem B957311 : Blo 956588 957311 := bstep (se 1 (by rfl) ⟨717983, by rfl⟩ : syracuseStep 957311 = 1435967) B1435967
theorem B957439 : Blo 956588 957439 := bstep (se 1 (by rfl) ⟨718079, by rfl⟩ : syracuseStep 957439 = 1436159) B1436159
theorem B5842145 : Blo 956588 5842145 := bstep (se 2 (by rfl) ⟨2190804, by rfl⟩ : syracuseStep 5842145 = 4381609) B4381609
theorem B4859675 : Blo 956588 4859675 := bstep (se 1 (by rfl) ⟨3644756, by rfl⟩ : syracuseStep 4859675 = 7289513) B7289513
theorem B1615727 : Blo 956588 1615727 := bstep (se 1 (by rfl) ⟨1211795, by rfl⟩ : syracuseStep 1615727 = 2423591) B2423591
theorem B235776095 : Blo 956588 235776095 := bstep (se 1 (by rfl) ⟨176832071, by rfl⟩ : syracuseStep 235776095 = 353664143) B353664143
theorem B8202343 : Blo 956588 8202343 := bstep (se 1 (by rfl) ⟨6151757, by rfl⟩ : syracuseStep 8202343 = 12303515) B12303515
theorem B9218873 : Blo 956588 9218873 := bstep (se 2 (by rfl) ⟨3457077, by rfl⟩ : syracuseStep 9218873 = 6914155) B6914155
theorem B179318873 : Blo 956588 179318873 := bstep (se 2 (by rfl) ⟨67244577, by rfl⟩ : syracuseStep 179318873 = 134489155) B134489155
theorem B4602365 : Blo 956588 4602365 := bstep (se 3 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 4602365 = 1725887) B1725887
theorem B1620607 : Blo 956588 1620607 := bstep (se 1 (by rfl) ⟨1215455, by rfl⟩ : syracuseStep 1620607 = 2430911) B2430911
theorem B13122593 : Blo 956588 13122593 := bstep (se 2 (by rfl) ⟨4920972, by rfl⟩ : syracuseStep 13122593 = 9841945) B9841945
theorem B7289999 : Blo 956588 7289999 := bstep (se 1 (by rfl) ⟨5467499, by rfl⟩ : syracuseStep 7289999 = 10934999) B10934999
theorem B2154671 : Blo 956588 2154671 := bstep (se 1 (by rfl) ⟨1616003, by rfl⟩ : syracuseStep 2154671 = 3232007) B3232007
theorem B1435391 : Blo 956588 1435391 := bstep (se 1 (by rfl) ⟨1076543, by rfl⟩ : syracuseStep 1435391 = 2153087) B2153087
theorem B35023211 : Blo 956588 35023211 := bstep (se 1 (by rfl) ⟨26267408, by rfl⟩ : syracuseStep 35023211 = 52534817) B52534817
theorem B2156921 : Blo 956588 2156921 := bstep (se 2 (by rfl) ⟨808845, by rfl⟩ : syracuseStep 2156921 = 1617691) B1617691
theorem B6909083 : Blo 956588 6909083 := bstep (se 1 (by rfl) ⟨5181812, by rfl⟩ : syracuseStep 6909083 = 10363625) B10363625
theorem B1436975 : Blo 956588 1436975 := bstep (se 1 (by rfl) ⟨1077731, by rfl⟩ : syracuseStep 1436975 = 2155463) B2155463
theorem B319713155 : Blo 956588 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B1438751 : Blo 956588 1438751 := bstep (se 1 (by rfl) ⟨1079063, by rfl⟩ : syracuseStep 1438751 = 2158127) B2158127
theorem B1439183 : Blo 956588 1439183 := bstep (se 1 (by rfl) ⟨1079387, by rfl⟩ : syracuseStep 1439183 = 2158775) B2158775
theorem B2160359 : Blo 956588 2160359 := bstep (se 1 (by rfl) ⟨1620269, by rfl⟩ : syracuseStep 2160359 = 3240539) B3240539
theorem B2456423 : Blo 956588 2456423 := bstep (se 1 (by rfl) ⟨1842317, by rfl⟩ : syracuseStep 2456423 = 3684635) B3684635
theorem B956927 : Blo 956588 956927 := bstep (se 1 (by rfl) ⟨717695, by rfl⟩ : syracuseStep 956927 = 1435391) B1435391
theorem B957983 : Blo 956588 957983 := bstep (se 1 (by rfl) ⟨718487, by rfl⟩ : syracuseStep 957983 = 1436975) B1436975
theorem B119545915 : Blo 956588 119545915 := bstep (se 1 (by rfl) ⟨89659436, by rfl⟩ : syracuseStep 119545915 = 179318873) B179318873
theorem B959167 : Blo 956588 959167 := bstep (se 1 (by rfl) ⟨719375, by rfl⟩ : syracuseStep 959167 = 1438751) B1438751
theorem B959455 : Blo 956588 959455 := bstep (se 1 (by rfl) ⟨719591, by rfl⟩ : syracuseStep 959455 = 1439183) B1439183
theorem B4859999 : Blo 956588 4859999 := bstep (se 1 (by rfl) ⟨3644999, by rfl⟩ : syracuseStep 4859999 = 7289999) B7289999
theorem B1618103 : Blo 956588 1618103 := bstep (se 1 (by rfl) ⟨1213577, by rfl⟩ : syracuseStep 1618103 = 2427155) B2427155
theorem B191870963 : Blo 956588 191870963 := bstep (se 1 (by rfl) ⟨143903222, by rfl⟩ : syracuseStep 191870963 = 287806445) B287806445
theorem B1620479 : Blo 956588 1620479 := bstep (se 1 (by rfl) ⟨1215359, by rfl⟩ : syracuseStep 1620479 = 2430719) B2430719
theorem B27966161 : Blo 956588 27966161 := bstep (se 2 (by rfl) ⟨10487310, by rfl⟩ : syracuseStep 27966161 = 20974621) B20974621
theorem B6142715 : Blo 956588 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B23348807 : Blo 956588 23348807 := bstep (se 1 (by rfl) ⟨17511605, by rfl⟩ : syracuseStep 23348807 = 35023211) B35023211
theorem B6145915 : Blo 956588 6145915 := bstep (se 1 (by rfl) ⟨4609436, by rfl⟩ : syracuseStep 6145915 = 9218873) B9218873
theorem B4606055 : Blo 956588 4606055 := bstep (se 1 (by rfl) ⟨3454541, by rfl⟩ : syracuseStep 4606055 = 6909083) B6909083
theorem B213142103 : Blo 956588 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B3068243 : Blo 956588 3068243 := bstep (se 1 (by rfl) ⟨2301182, by rfl⟩ : syracuseStep 3068243 = 4602365) B4602365
theorem B12278911 : Blo 956588 12278911 := bstep (se 1 (by rfl) ⟨9209183, by rfl⟩ : syracuseStep 12278911 = 18418367) B18418367
theorem B3235355 : Blo 956588 3235355 := bstep (se 1 (by rfl) ⟨2426516, by rfl⟩ : syracuseStep 3235355 = 4853033) B4853033
theorem B10936457 : Blo 956588 10936457 := bstep (se 2 (by rfl) ⟨4101171, by rfl⟩ : syracuseStep 10936457 = 8202343) B8202343
theorem B1436447 : Blo 956588 1436447 := bstep (se 1 (by rfl) ⟨1077335, by rfl⟩ : syracuseStep 1436447 = 2154671) B2154671
theorem B3894763 : Blo 956588 3894763 := bstep (se 1 (by rfl) ⟨2921072, by rfl⟩ : syracuseStep 3894763 = 5842145) B5842145
theorem B3239783 : Blo 956588 3239783 := bstep (se 1 (by rfl) ⟨2429837, by rfl⟩ : syracuseStep 3239783 = 4859675) B4859675
theorem B1077151 : Blo 956588 1077151 := bstep (se 1 (by rfl) ⟨807863, by rfl⟩ : syracuseStep 1077151 = 1615727) B1615727
theorem B157184063 : Blo 956588 157184063 := bstep (se 1 (by rfl) ⟨117888047, by rfl⟩ : syracuseStep 157184063 = 235776095) B235776095
theorem B1437947 : Blo 956588 1437947 := bstep (se 1 (by rfl) ⟨1078460, by rfl⟩ : syracuseStep 1437947 = 2156921) B2156921
theorem B2160809 : Blo 956588 2160809 := bstep (se 2 (by rfl) ⟨810303, by rfl⟩ : syracuseStep 2160809 = 1620607) B1620607
theorem B1440239 : Blo 956588 1440239 := bstep (se 1 (by rfl) ⟨1080179, by rfl⟩ : syracuseStep 1440239 = 2160359) B2160359
theorem B1637615 : Blo 956588 1637615 := bstep (se 1 (by rfl) ⟨1228211, by rfl⟩ : syracuseStep 1637615 = 2456423) B2456423
theorem B8748395 : Blo 956588 8748395 := bstep (se 1 (by rfl) ⟨6561296, by rfl⟩ : syracuseStep 8748395 = 13122593) B13122593
theorem B15565871 : Blo 956588 15565871 := bstep (se 1 (by rfl) ⟨11674403, by rfl⟩ : syracuseStep 15565871 = 23348807) B23348807
theorem B8194553 : Blo 956588 8194553 := bstep (se 2 (by rfl) ⟨3072957, by rfl⟩ : syracuseStep 8194553 = 6145915) B6145915
theorem B957631 : Blo 956588 957631 := bstep (se 1 (by rfl) ⟨718223, by rfl⟩ : syracuseStep 957631 = 1436447) B1436447
theorem B958631 : Blo 956588 958631 := bstep (se 1 (by rfl) ⟨718973, by rfl⟩ : syracuseStep 958631 = 1437947) B1437947
theorem B4366973 : Blo 956588 4366973 := bstep (se 3 (by rfl) ⟨818807, by rfl⟩ : syracuseStep 4366973 = 1637615) B1637615
theorem B960159 : Blo 956588 960159 := bstep (se 1 (by rfl) ⟨720119, by rfl⟩ : syracuseStep 960159 = 1440239) B1440239
theorem B159394553 : Blo 956588 159394553 := bstep (se 2 (by rfl) ⟨59772957, by rfl⟩ : syracuseStep 159394553 = 119545915) B119545915
theorem B142094735 : Blo 956588 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B2045495 : Blo 956588 2045495 := bstep (se 1 (by rfl) ⟨1534121, by rfl⟩ : syracuseStep 2045495 = 3068243) B3068243
theorem B5193017 : Blo 956588 5193017 := bstep (se 2 (by rfl) ⟨1947381, by rfl⟩ : syracuseStep 5193017 = 3894763) B3894763
theorem B7290971 : Blo 956588 7290971 := bstep (se 1 (by rfl) ⟨5468228, by rfl⟩ : syracuseStep 7290971 = 10936457) B10936457
theorem B127913975 : Blo 956588 127913975 := bstep (se 1 (by rfl) ⟨95935481, by rfl⟩ : syracuseStep 127913975 = 191870963) B191870963
theorem B16371881 : Blo 956588 16371881 := bstep (se 2 (by rfl) ⟨6139455, by rfl⟩ : syracuseStep 16371881 = 12278911) B12278911
theorem B3070703 : Blo 956588 3070703 := bstep (se 1 (by rfl) ⟨2303027, by rfl⟩ : syracuseStep 3070703 = 4606055) B4606055
theorem B2156903 : Blo 956588 2156903 := bstep (se 1 (by rfl) ⟨1617677, by rfl⟩ : syracuseStep 2156903 = 3235355) B3235355
theorem B1436201 : Blo 956588 1436201 := bstep (se 2 (by rfl) ⟨538575, by rfl⟩ : syracuseStep 1436201 = 1077151) B1077151
theorem B3239999 : Blo 956588 3239999 := bstep (se 1 (by rfl) ⟨2429999, by rfl⟩ : syracuseStep 3239999 = 4859999) B4859999
theorem B2159855 : Blo 956588 2159855 := bstep (se 1 (by rfl) ⟨1619891, by rfl⟩ : syracuseStep 2159855 = 3239783) B3239783
theorem B104789375 : Blo 956588 104789375 := bstep (se 1 (by rfl) ⟨78592031, by rfl⟩ : syracuseStep 104789375 = 157184063) B157184063
theorem B1078735 : Blo 956588 1078735 := bstep (se 1 (by rfl) ⟨809051, by rfl⟩ : syracuseStep 1078735 = 1618103) B1618103
theorem B1440539 : Blo 956588 1440539 := bstep (se 1 (by rfl) ⟨1080404, by rfl⟩ : syracuseStep 1440539 = 2160809) B2160809
theorem B1080319 : Blo 956588 1080319 := bstep (se 1 (by rfl) ⟨810239, by rfl⟩ : syracuseStep 1080319 = 1620479) B1620479
theorem B18644107 : Blo 956588 18644107 := bstep (se 1 (by rfl) ⟨13983080, by rfl⟩ : syracuseStep 18644107 = 27966161) B27966161
theorem B4095143 : Blo 956588 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B5832263 : Blo 956588 5832263 := bstep (se 1 (by rfl) ⟨4374197, by rfl⟩ : syracuseStep 5832263 = 8748395) B8748395
theorem B10914587 : Blo 956588 10914587 := bstep (se 1 (by rfl) ⟨8185940, by rfl⟩ : syracuseStep 10914587 = 16371881) B16371881
theorem B957467 : Blo 956588 957467 := bstep (se 1 (by rfl) ⟨718100, by rfl⟩ : syracuseStep 957467 = 1436201) B1436201
theorem B960359 : Blo 956588 960359 := bstep (se 1 (by rfl) ⟨720269, by rfl⟩ : syracuseStep 960359 = 1440539) B1440539
theorem B2730095 : Blo 956588 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B4860647 : Blo 956588 4860647 := bstep (se 1 (by rfl) ⟨3645485, by rfl⟩ : syracuseStep 4860647 = 7290971) B7290971
theorem B85275983 : Blo 956588 85275983 := bstep (se 1 (by rfl) ⟨63956987, by rfl⟩ : syracuseStep 85275983 = 127913975) B127913975
theorem B2047135 : Blo 956588 2047135 := bstep (se 1 (by rfl) ⟨1535351, by rfl⟩ : syracuseStep 2047135 = 3070703) B3070703
theorem B1363663 : Blo 956588 1363663 := bstep (se 1 (by rfl) ⟨1022747, by rfl⟩ : syracuseStep 1363663 = 2045495) B2045495
theorem B24858809 : Blo 956588 24858809 := bstep (se 2 (by rfl) ⟨9322053, by rfl⟩ : syracuseStep 24858809 = 18644107) B18644107
theorem B3462011 : Blo 956588 3462011 := bstep (se 1 (by rfl) ⟨2596508, by rfl⟩ : syracuseStep 3462011 = 5193017) B5193017
theorem B3888175 : Blo 956588 3888175 := bstep (se 1 (by rfl) ⟨2916131, by rfl⟩ : syracuseStep 3888175 = 5832263) B5832263
theorem B10377247 : Blo 956588 10377247 := bstep (se 1 (by rfl) ⟨7782935, by rfl⟩ : syracuseStep 10377247 = 15565871) B15565871
theorem B5463035 : Blo 956588 5463035 := bstep (se 1 (by rfl) ⟨4097276, by rfl⟩ : syracuseStep 5463035 = 8194553) B8194553
theorem B2911315 : Blo 956588 2911315 := bstep (se 1 (by rfl) ⟨2183486, by rfl⟩ : syracuseStep 2911315 = 4366973) B4366973
theorem B1437935 : Blo 956588 1437935 := bstep (se 1 (by rfl) ⟨1078451, by rfl⟩ : syracuseStep 1437935 = 2156903) B2156903
theorem B106263035 : Blo 956588 106263035 := bstep (se 1 (by rfl) ⟨79697276, by rfl⟩ : syracuseStep 106263035 = 159394553) B159394553
theorem B1438313 : Blo 956588 1438313 := bstep (se 2 (by rfl) ⟨539367, by rfl⟩ : syracuseStep 1438313 = 1078735) B1078735
theorem B2159999 : Blo 956588 2159999 := bstep (se 1 (by rfl) ⟨1619999, by rfl⟩ : syracuseStep 2159999 = 3239999) B3239999
theorem B94729823 : Blo 956588 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B1439903 : Blo 956588 1439903 := bstep (se 1 (by rfl) ⟨1079927, by rfl⟩ : syracuseStep 1439903 = 2159855) B2159855
theorem B69859583 : Blo 956588 69859583 := bstep (se 1 (by rfl) ⟨52394687, by rfl⟩ : syracuseStep 69859583 = 104789375) B104789375
theorem B1440425 : Blo 956588 1440425 := bstep (se 2 (by rfl) ⟨540159, by rfl⟩ : syracuseStep 1440425 = 1080319) B1080319
theorem B7276391 : Blo 956588 7276391 := bstep (se 1 (by rfl) ⟨5457293, by rfl⟩ : syracuseStep 7276391 = 10914587) B10914587
theorem B3642023 : Blo 956588 3642023 := bstep (se 1 (by rfl) ⟨2731517, by rfl⟩ : syracuseStep 3642023 = 5463035) B5463035
theorem B5184233 : Blo 956588 5184233 := bstep (se 2 (by rfl) ⟨1944087, by rfl⟩ : syracuseStep 5184233 = 3888175) B3888175
theorem B13836329 : Blo 956588 13836329 := bstep (se 2 (by rfl) ⟨5188623, by rfl⟩ : syracuseStep 13836329 = 10377247) B10377247
theorem B958623 : Blo 956588 958623 := bstep (se 1 (by rfl) ⟨718967, by rfl⟩ : syracuseStep 958623 = 1437935) B1437935
theorem B958875 : Blo 956588 958875 := bstep (se 1 (by rfl) ⟨719156, by rfl⟩ : syracuseStep 958875 = 1438313) B1438313
theorem B63153215 : Blo 956588 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B959935 : Blo 956588 959935 := bstep (se 1 (by rfl) ⟨719951, by rfl⟩ : syracuseStep 959935 = 1439903) B1439903
theorem B46573055 : Blo 956588 46573055 := bstep (se 1 (by rfl) ⟨34929791, by rfl⟩ : syracuseStep 46573055 = 69859583) B69859583
theorem B2729513 : Blo 956588 2729513 := bstep (se 2 (by rfl) ⟨1023567, by rfl⟩ : syracuseStep 2729513 = 2047135) B2047135
theorem B960283 : Blo 956588 960283 := bstep (se 1 (by rfl) ⟨720212, by rfl⟩ : syracuseStep 960283 = 1440425) B1440425
theorem B2308007 : Blo 956588 2308007 := bstep (se 1 (by rfl) ⟨1731005, by rfl⟩ : syracuseStep 2308007 = 3462011) B3462011
theorem B3881753 : Blo 956588 3881753 := bstep (se 2 (by rfl) ⟨1455657, by rfl⟩ : syracuseStep 3881753 = 2911315) B2911315
theorem B1818217 : Blo 956588 1818217 := bstep (se 2 (by rfl) ⟨681831, by rfl⟩ : syracuseStep 1818217 = 1363663) B1363663
theorem B1820063 : Blo 956588 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B16572539 : Blo 956588 16572539 := bstep (se 1 (by rfl) ⟨12429404, by rfl⟩ : syracuseStep 16572539 = 24858809) B24858809
theorem B3240431 : Blo 956588 3240431 := bstep (se 1 (by rfl) ⟨2430323, by rfl⟩ : syracuseStep 3240431 = 4860647) B4860647
theorem B70842023 : Blo 956588 70842023 := bstep (se 1 (by rfl) ⟨53131517, by rfl⟩ : syracuseStep 70842023 = 106263035) B106263035
theorem B56850655 : Blo 956588 56850655 := bstep (se 1 (by rfl) ⟨42637991, by rfl⟩ : syracuseStep 56850655 = 85275983) B85275983
theorem B1439999 : Blo 956588 1439999 := bstep (se 1 (by rfl) ⟨1079999, by rfl⟩ : syracuseStep 1439999 = 2159999) B2159999
theorem B1213375 : Blo 956588 1213375 := bstep (se 1 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 1213375 = 1820063) B1820063
theorem B4850927 : Blo 956588 4850927 := bstep (se 1 (by rfl) ⟨3638195, by rfl⟩ : syracuseStep 4850927 = 7276391) B7276391
theorem B2428015 : Blo 956588 2428015 := bstep (se 1 (by rfl) ⟨1821011, by rfl⟩ : syracuseStep 2428015 = 3642023) B3642023
theorem B11048359 : Blo 956588 11048359 := bstep (se 1 (by rfl) ⟨8286269, by rfl⟩ : syracuseStep 11048359 = 16572539) B16572539
theorem B75800873 : Blo 956588 75800873 := bstep (se 2 (by rfl) ⟨28425327, by rfl⟩ : syracuseStep 75800873 = 56850655) B56850655
theorem B47228015 : Blo 956588 47228015 := bstep (se 1 (by rfl) ⟨35421011, by rfl⟩ : syracuseStep 47228015 = 70842023) B70842023
theorem B959999 : Blo 956588 959999 := bstep (se 1 (by rfl) ⟨719999, by rfl⟩ : syracuseStep 959999 = 1439999) B1439999
theorem B3456155 : Blo 956588 3456155 := bstep (se 1 (by rfl) ⟨2592116, by rfl⟩ : syracuseStep 3456155 = 5184233) B5184233
theorem B9224219 : Blo 956588 9224219 := bstep (se 1 (by rfl) ⟨6918164, by rfl⟩ : syracuseStep 9224219 = 13836329) B13836329
theorem B31048703 : Blo 956588 31048703 := bstep (se 1 (by rfl) ⟨23286527, by rfl⟩ : syracuseStep 31048703 = 46573055) B46573055
theorem B1819675 : Blo 956588 1819675 := bstep (se 1 (by rfl) ⟨1364756, by rfl⟩ : syracuseStep 1819675 = 2729513) B2729513
theorem B42102143 : Blo 956588 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B2160287 : Blo 956588 2160287 := bstep (se 1 (by rfl) ⟨1620215, by rfl⟩ : syracuseStep 2160287 = 3240431) B3240431
theorem B1538671 : Blo 956588 1538671 := bstep (se 1 (by rfl) ⟨1154003, by rfl⟩ : syracuseStep 1538671 = 2308007) B2308007
theorem B2587835 : Blo 956588 2587835 := bstep (se 1 (by rfl) ⟨1940876, by rfl⟩ : syracuseStep 2587835 = 3881753) B3881753
theorem B2424289 : Blo 956588 2424289 := bstep (se 2 (by rfl) ⟨909108, by rfl⟩ : syracuseStep 2424289 = 1818217) B1818217
theorem B2426233 : Blo 956588 2426233 := bstep (se 2 (by rfl) ⟨909837, by rfl⟩ : syracuseStep 2426233 = 1819675) B1819675
theorem B50533915 : Blo 956588 50533915 := bstep (se 1 (by rfl) ⟨37900436, by rfl⟩ : syracuseStep 50533915 = 75800873) B75800873
theorem B9216413 : Blo 956588 9216413 := bstep (se 3 (by rfl) ⟨1728077, by rfl⟩ : syracuseStep 9216413 = 3456155) B3456155
theorem B1617833 : Blo 956588 1617833 := bstep (se 2 (by rfl) ⟨606687, by rfl⟩ : syracuseStep 1617833 = 1213375) B1213375
theorem B14731145 : Blo 956588 14731145 := bstep (se 2 (by rfl) ⟨5524179, by rfl⟩ : syracuseStep 14731145 = 11048359) B11048359
theorem B28068095 : Blo 956588 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B2051561 : Blo 956588 2051561 := bstep (se 2 (by rfl) ⟨769335, by rfl⟩ : syracuseStep 2051561 = 1538671) B1538671
theorem B3232385 : Blo 956588 3232385 := bstep (se 2 (by rfl) ⟨1212144, by rfl⟩ : syracuseStep 3232385 = 2424289) B2424289
theorem B1725223 : Blo 956588 1725223 := bstep (se 1 (by rfl) ⟨1293917, by rfl⟩ : syracuseStep 1725223 = 2587835) B2587835
theorem B6149479 : Blo 956588 6149479 := bstep (se 1 (by rfl) ⟨4612109, by rfl⟩ : syracuseStep 6149479 = 9224219) B9224219
theorem B20699135 : Blo 956588 20699135 := bstep (se 1 (by rfl) ⟨15524351, by rfl⟩ : syracuseStep 20699135 = 31048703) B31048703
theorem B3233951 : Blo 956588 3233951 := bstep (se 1 (by rfl) ⟨2425463, by rfl⟩ : syracuseStep 3233951 = 4850927) B4850927
theorem B3237353 : Blo 956588 3237353 := bstep (se 2 (by rfl) ⟨1214007, by rfl⟩ : syracuseStep 3237353 = 2428015) B2428015
theorem B31485343 : Blo 956588 31485343 := bstep (se 1 (by rfl) ⟨23614007, by rfl⟩ : syracuseStep 31485343 = 47228015) B47228015
theorem B1440191 : Blo 956588 1440191 := bstep (se 1 (by rfl) ⟨1080143, by rfl⟩ : syracuseStep 1440191 = 2160287) B2160287
theorem B18712063 : Blo 956588 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B13799423 : Blo 956588 13799423 := bstep (se 1 (by rfl) ⟨10349567, by rfl⟩ : syracuseStep 13799423 = 20699135) B20699135
theorem B41980457 : Blo 956588 41980457 := bstep (se 2 (by rfl) ⟨15742671, by rfl⟩ : syracuseStep 41980457 = 31485343) B31485343
theorem B2300297 : Blo 956588 2300297 := bstep (se 2 (by rfl) ⟨862611, by rfl⟩ : syracuseStep 2300297 = 1725223) B1725223
theorem B8199305 : Blo 956588 8199305 := bstep (se 2 (by rfl) ⟨3074739, by rfl⟩ : syracuseStep 8199305 = 6149479) B6149479
theorem B67378553 : Blo 956588 67378553 := bstep (se 2 (by rfl) ⟨25266957, by rfl⟩ : syracuseStep 67378553 = 50533915) B50533915
theorem B960127 : Blo 956588 960127 := bstep (se 1 (by rfl) ⟨720095, by rfl⟩ : syracuseStep 960127 = 1440191) B1440191
theorem B6144275 : Blo 956588 6144275 := bstep (se 1 (by rfl) ⟨4608206, by rfl⟩ : syracuseStep 6144275 = 9216413) B9216413
theorem B9820763 : Blo 956588 9820763 := bstep (se 1 (by rfl) ⟨7365572, by rfl⟩ : syracuseStep 9820763 = 14731145) B14731145
theorem B3234977 : Blo 956588 3234977 := bstep (se 2 (by rfl) ⟨1213116, by rfl⟩ : syracuseStep 3234977 = 2426233) B2426233
theorem B1367707 : Blo 956588 1367707 := bstep (se 1 (by rfl) ⟨1025780, by rfl⟩ : syracuseStep 1367707 = 2051561) B2051561
theorem B2154923 : Blo 956588 2154923 := bstep (se 1 (by rfl) ⟨1616192, by rfl⟩ : syracuseStep 2154923 = 3232385) B3232385
theorem B2155967 : Blo 956588 2155967 := bstep (se 1 (by rfl) ⟨1616975, by rfl⟩ : syracuseStep 2155967 = 3233951) B3233951
theorem B2158235 : Blo 956588 2158235 := bstep (se 1 (by rfl) ⟨1618676, by rfl⟩ : syracuseStep 2158235 = 3237353) B3237353
theorem B1078555 : Blo 956588 1078555 := bstep (se 1 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 1078555 = 1617833) B1617833
theorem B4096183 : Blo 956588 4096183 := bstep (se 1 (by rfl) ⟨3072137, by rfl⟩ : syracuseStep 4096183 = 6144275) B6144275
theorem B27986971 : Blo 956588 27986971 := bstep (se 1 (by rfl) ⟨20990228, by rfl⟩ : syracuseStep 27986971 = 41980457) B41980457
theorem B6134125 : Blo 956588 6134125 := bstep (se 3 (by rfl) ⟨1150148, by rfl⟩ : syracuseStep 6134125 = 2300297) B2300297
theorem B24949417 : Blo 956588 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B1823609 : Blo 956588 1823609 := bstep (se 2 (by rfl) ⟨683853, by rfl⟩ : syracuseStep 1823609 = 1367707) B1367707
theorem B9199615 : Blo 956588 9199615 := bstep (se 1 (by rfl) ⟨6899711, by rfl⟩ : syracuseStep 9199615 = 13799423) B13799423
theorem B6547175 : Blo 956588 6547175 := bstep (se 1 (by rfl) ⟨4910381, by rfl⟩ : syracuseStep 6547175 = 9820763) B9820763
theorem B5466203 : Blo 956588 5466203 := bstep (se 1 (by rfl) ⟨4099652, by rfl⟩ : syracuseStep 5466203 = 8199305) B8199305
theorem B2156651 : Blo 956588 2156651 := bstep (se 1 (by rfl) ⟨1617488, by rfl⟩ : syracuseStep 2156651 = 3234977) B3234977
theorem B44919035 : Blo 956588 44919035 := bstep (se 1 (by rfl) ⟨33689276, by rfl⟩ : syracuseStep 44919035 = 67378553) B67378553
theorem B1436615 : Blo 956588 1436615 := bstep (se 1 (by rfl) ⟨1077461, by rfl⟩ : syracuseStep 1436615 = 2154923) B2154923
theorem B1437311 : Blo 956588 1437311 := bstep (se 1 (by rfl) ⟨1077983, by rfl⟩ : syracuseStep 1437311 = 2155967) B2155967
theorem B1438073 : Blo 956588 1438073 := bstep (se 2 (by rfl) ⟨539277, by rfl⟩ : syracuseStep 1438073 = 1078555) B1078555
theorem B1438823 : Blo 956588 1438823 := bstep (se 1 (by rfl) ⟨1079117, by rfl⟩ : syracuseStep 1438823 = 2158235) B2158235
theorem B1215739 : Blo 956588 1215739 := bstep (se 1 (by rfl) ⟨911804, by rfl⟩ : syracuseStep 1215739 = 1823609) B1823609
theorem B33265889 : Blo 956588 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B4364783 : Blo 956588 4364783 := bstep (se 1 (by rfl) ⟨3273587, by rfl⟩ : syracuseStep 4364783 = 6547175) B6547175
theorem B3644135 : Blo 956588 3644135 := bstep (se 1 (by rfl) ⟨2733101, by rfl⟩ : syracuseStep 3644135 = 5466203) B5466203
theorem B957743 : Blo 956588 957743 := bstep (se 1 (by rfl) ⟨718307, by rfl⟩ : syracuseStep 957743 = 1436615) B1436615
theorem B958207 : Blo 956588 958207 := bstep (se 1 (by rfl) ⟨718655, by rfl⟩ : syracuseStep 958207 = 1437311) B1437311
theorem B958715 : Blo 956588 958715 := bstep (se 1 (by rfl) ⟨719036, by rfl⟩ : syracuseStep 958715 = 1438073) B1438073
theorem B959215 : Blo 956588 959215 := bstep (se 1 (by rfl) ⟨719411, by rfl⟩ : syracuseStep 959215 = 1438823) B1438823
theorem B12266153 : Blo 956588 12266153 := bstep (se 2 (by rfl) ⟨4599807, by rfl⟩ : syracuseStep 12266153 = 9199615) B9199615
theorem B8178833 : Blo 956588 8178833 := bstep (se 2 (by rfl) ⟨3067062, by rfl⟩ : syracuseStep 8178833 = 6134125) B6134125
theorem B5461577 : Blo 956588 5461577 := bstep (se 2 (by rfl) ⟨2048091, by rfl⟩ : syracuseStep 5461577 = 4096183) B4096183
theorem B37315961 : Blo 956588 37315961 := bstep (se 2 (by rfl) ⟨13993485, by rfl⟩ : syracuseStep 37315961 = 27986971) B27986971
theorem B1437767 : Blo 956588 1437767 := bstep (se 1 (by rfl) ⟨1078325, by rfl⟩ : syracuseStep 1437767 = 2156651) B2156651
theorem B29946023 : Blo 956588 29946023 := bstep (se 1 (by rfl) ⟨22459517, by rfl⟩ : syracuseStep 29946023 = 44919035) B44919035
theorem B3641051 : Blo 956588 3641051 := bstep (se 1 (by rfl) ⟨2730788, by rfl⟩ : syracuseStep 3641051 = 5461577) B5461577
theorem B2429423 : Blo 956588 2429423 := bstep (se 1 (by rfl) ⟨1822067, by rfl⟩ : syracuseStep 2429423 = 3644135) B3644135
theorem B24877307 : Blo 956588 24877307 := bstep (se 1 (by rfl) ⟨18657980, by rfl⟩ : syracuseStep 24877307 = 37315961) B37315961
theorem B958511 : Blo 956588 958511 := bstep (se 1 (by rfl) ⟨718883, by rfl⟩ : syracuseStep 958511 = 1437767) B1437767
theorem B19964015 : Blo 956588 19964015 := bstep (se 1 (by rfl) ⟨14973011, by rfl⟩ : syracuseStep 19964015 = 29946023) B29946023
theorem B5452555 : Blo 956588 5452555 := bstep (se 1 (by rfl) ⟨4089416, by rfl⟩ : syracuseStep 5452555 = 8178833) B8178833
theorem B1620985 : Blo 956588 1620985 := bstep (se 2 (by rfl) ⟨607869, by rfl⟩ : syracuseStep 1620985 = 1215739) B1215739
theorem B8177435 : Blo 956588 8177435 := bstep (se 1 (by rfl) ⟨6133076, by rfl⟩ : syracuseStep 8177435 = 12266153) B12266153
theorem B22177259 : Blo 956588 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B2909855 : Blo 956588 2909855 := bstep (se 1 (by rfl) ⟨2182391, by rfl⟩ : syracuseStep 2909855 = 4364783) B4364783
theorem B2427367 : Blo 956588 2427367 := bstep (se 1 (by rfl) ⟨1820525, by rfl⟩ : syracuseStep 2427367 = 3641051) B3641051
theorem B16584871 : Blo 956588 16584871 := bstep (se 1 (by rfl) ⟨12438653, by rfl⟩ : syracuseStep 16584871 = 24877307) B24877307
theorem B13309343 : Blo 956588 13309343 := bstep (se 1 (by rfl) ⟨9982007, by rfl⟩ : syracuseStep 13309343 = 19964015) B19964015
theorem B14784839 : Blo 956588 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B5451623 : Blo 956588 5451623 := bstep (se 1 (by rfl) ⟨4088717, by rfl⟩ : syracuseStep 5451623 = 8177435) B8177435
theorem B1619615 : Blo 956588 1619615 := bstep (se 1 (by rfl) ⟨1214711, by rfl⟩ : syracuseStep 1619615 = 2429423) B2429423
theorem B7759613 : Blo 956588 7759613 := bstep (se 3 (by rfl) ⟨1454927, by rfl⟩ : syracuseStep 7759613 = 2909855) B2909855
theorem B7270073 : Blo 956588 7270073 := bstep (se 2 (by rfl) ⟨2726277, by rfl⟩ : syracuseStep 7270073 = 5452555) B5452555
theorem B2161313 : Blo 956588 2161313 := bstep (se 2 (by rfl) ⟨810492, by rfl⟩ : syracuseStep 2161313 = 1620985) B1620985
theorem B3236489 : Blo 956588 3236489 := bstep (se 2 (by rfl) ⟨1213683, by rfl⟩ : syracuseStep 3236489 = 2427367) B2427367
theorem B8872895 : Blo 956588 8872895 := bstep (se 1 (by rfl) ⟨6654671, by rfl⟩ : syracuseStep 8872895 = 13309343) B13309343
theorem B9856559 : Blo 956588 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B22113161 : Blo 956588 22113161 := bstep (se 2 (by rfl) ⟨8292435, by rfl⟩ : syracuseStep 22113161 = 16584871) B16584871
theorem B5173075 : Blo 956588 5173075 := bstep (se 1 (by rfl) ⟨3879806, by rfl⟩ : syracuseStep 5173075 = 7759613) B7759613
theorem B4846715 : Blo 956588 4846715 := bstep (se 1 (by rfl) ⟨3635036, by rfl⟩ : syracuseStep 4846715 = 7270073) B7270073
theorem B3634415 : Blo 956588 3634415 := bstep (se 1 (by rfl) ⟨2725811, by rfl⟩ : syracuseStep 3634415 = 5451623) B5451623
theorem B1079743 : Blo 956588 1079743 := bstep (se 1 (by rfl) ⟨809807, by rfl⟩ : syracuseStep 1079743 = 1619615) B1619615
theorem B1440875 : Blo 956588 1440875 := bstep (se 1 (by rfl) ⟨1080656, by rfl⟩ : syracuseStep 1440875 = 2161313) B2161313
theorem B960583 : Blo 956588 960583 := bstep (se 1 (by rfl) ⟨720437, by rfl⟩ : syracuseStep 960583 = 1440875) B1440875
theorem B6897433 : Blo 956588 6897433 := bstep (se 2 (by rfl) ⟨2586537, by rfl⟩ : syracuseStep 6897433 = 5173075) B5173075
theorem B5915263 : Blo 956588 5915263 := bstep (se 1 (by rfl) ⟨4436447, by rfl⟩ : syracuseStep 5915263 = 8872895) B8872895
theorem B6571039 : Blo 956588 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B3231143 : Blo 956588 3231143 := bstep (se 1 (by rfl) ⟨2423357, by rfl⟩ : syracuseStep 3231143 = 4846715) B4846715
theorem B2157659 : Blo 956588 2157659 := bstep (se 1 (by rfl) ⟨1618244, by rfl⟩ : syracuseStep 2157659 = 3236489) B3236489
theorem B14742107 : Blo 956588 14742107 := bstep (se 1 (by rfl) ⟨11056580, by rfl⟩ : syracuseStep 14742107 = 22113161) B22113161
theorem B1439657 : Blo 956588 1439657 := bstep (se 2 (by rfl) ⟨539871, by rfl⟩ : syracuseStep 1439657 = 1079743) B1079743
theorem B2422943 : Blo 956588 2422943 := bstep (se 1 (by rfl) ⟨1817207, by rfl⟩ : syracuseStep 2422943 = 3634415) B3634415
theorem B959771 : Blo 956588 959771 := bstep (se 1 (by rfl) ⟨719828, by rfl⟩ : syracuseStep 959771 = 1439657) B1439657
theorem B1615295 : Blo 956588 1615295 := bstep (se 1 (by rfl) ⟨1211471, by rfl⟩ : syracuseStep 1615295 = 2422943) B2422943
theorem B8761385 : Blo 956588 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B9196577 : Blo 956588 9196577 := bstep (se 2 (by rfl) ⟨3448716, by rfl⟩ : syracuseStep 9196577 = 6897433) B6897433
theorem B7887017 : Blo 956588 7887017 := bstep (se 2 (by rfl) ⟨2957631, by rfl⟩ : syracuseStep 7887017 = 5915263) B5915263
theorem B2154095 : Blo 956588 2154095 := bstep (se 1 (by rfl) ⟨1615571, by rfl⟩ : syracuseStep 2154095 = 3231143) B3231143
theorem B1438439 : Blo 956588 1438439 := bstep (se 1 (by rfl) ⟨1078829, by rfl⟩ : syracuseStep 1438439 = 2157659) B2157659
theorem B9828071 : Blo 956588 9828071 := bstep (se 1 (by rfl) ⟨7371053, by rfl⟩ : syracuseStep 9828071 = 14742107) B14742107
theorem B6131051 : Blo 956588 6131051 := bstep (se 1 (by rfl) ⟨4598288, by rfl⟩ : syracuseStep 6131051 = 9196577) B9196577
theorem B5840923 : Blo 956588 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B958959 : Blo 956588 958959 := bstep (se 1 (by rfl) ⟨719219, by rfl⟩ : syracuseStep 958959 = 1438439) B1438439
theorem B1436063 : Blo 956588 1436063 := bstep (se 1 (by rfl) ⟨1077047, by rfl⟩ : syracuseStep 1436063 = 2154095) B2154095
theorem B21032045 : Blo 956588 21032045 := bstep (se 3 (by rfl) ⟨3943508, by rfl⟩ : syracuseStep 21032045 = 7887017) B7887017
theorem B1076863 : Blo 956588 1076863 := bstep (se 1 (by rfl) ⟨807647, by rfl⟩ : syracuseStep 1076863 = 1615295) B1615295
theorem B6552047 : Blo 956588 6552047 := bstep (se 1 (by rfl) ⟨4914035, by rfl⟩ : syracuseStep 6552047 = 9828071) B9828071
theorem B17472125 : Blo 956588 17472125 := bstep (se 3 (by rfl) ⟨3276023, by rfl⟩ : syracuseStep 17472125 = 6552047) B6552047
theorem B957375 : Blo 956588 957375 := bstep (se 1 (by rfl) ⟨718031, by rfl⟩ : syracuseStep 957375 = 1436063) B1436063
theorem B7787897 : Blo 956588 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B4087367 : Blo 956588 4087367 := bstep (se 1 (by rfl) ⟨3065525, by rfl⟩ : syracuseStep 4087367 = 6131051) B6131051
theorem B1435817 : Blo 956588 1435817 := bstep (se 2 (by rfl) ⟨538431, by rfl⟩ : syracuseStep 1435817 = 1076863) B1076863
theorem B14021363 : Blo 956588 14021363 := bstep (se 1 (by rfl) ⟨10516022, by rfl⟩ : syracuseStep 14021363 = 21032045) B21032045
theorem B37390301 : Blo 956588 37390301 := bstep (se 3 (by rfl) ⟨7010681, by rfl⟩ : syracuseStep 37390301 = 14021363) B14021363
theorem B2724911 : Blo 956588 2724911 := bstep (se 1 (by rfl) ⟨2043683, by rfl⟩ : syracuseStep 2724911 = 4087367) B4087367
theorem B957211 : Blo 956588 957211 := bstep (se 1 (by rfl) ⟨717908, by rfl⟩ : syracuseStep 957211 = 1435817) B1435817
theorem B5191931 : Blo 956588 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B11648083 : Blo 956588 11648083 := bstep (se 1 (by rfl) ⟨8736062, by rfl⟩ : syracuseStep 11648083 = 17472125) B17472125
theorem B1816607 : Blo 956588 1816607 := bstep (se 1 (by rfl) ⟨1362455, by rfl⟩ : syracuseStep 1816607 = 2724911) B2724911
theorem B3461287 : Blo 956588 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B24926867 : Blo 956588 24926867 := bstep (se 1 (by rfl) ⟨18695150, by rfl⟩ : syracuseStep 24926867 = 37390301) B37390301
theorem B15530777 : Blo 956588 15530777 := bstep (se 2 (by rfl) ⟨5824041, by rfl⟩ : syracuseStep 15530777 = 11648083) B11648083
theorem B16617911 : Blo 956588 16617911 := bstep (se 1 (by rfl) ⟨12463433, by rfl⟩ : syracuseStep 16617911 = 24926867) B24926867
theorem B4844285 : Blo 956588 4844285 := bstep (se 3 (by rfl) ⟨908303, by rfl⟩ : syracuseStep 4844285 = 1816607) B1816607
theorem B4615049 : Blo 956588 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B10353851 : Blo 956588 10353851 := bstep (se 1 (by rfl) ⟨7765388, by rfl⟩ : syracuseStep 10353851 = 15530777) B15530777
theorem B177257717 : Blo 956588 177257717 := bstep (se 5 (by rfl) ⟨8308955, by rfl⟩ : syracuseStep 177257717 = 16617911) B16617911
theorem B3229523 : Blo 956588 3229523 := bstep (se 1 (by rfl) ⟨2422142, by rfl⟩ : syracuseStep 3229523 = 4844285) B4844285
theorem B6902567 : Blo 956588 6902567 := bstep (se 1 (by rfl) ⟨5176925, by rfl⟩ : syracuseStep 6902567 = 10353851) B10353851
theorem B3076699 : Blo 956588 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B4102265 : Blo 956588 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B118171811 : Blo 956588 118171811 := bstep (se 1 (by rfl) ⟨88628858, by rfl⟩ : syracuseStep 118171811 = 177257717) B177257717
theorem B4601711 : Blo 956588 4601711 := bstep (se 1 (by rfl) ⟨3451283, by rfl⟩ : syracuseStep 4601711 = 6902567) B6902567
theorem B2153015 : Blo 956588 2153015 := bstep (se 1 (by rfl) ⟨1614761, by rfl⟩ : syracuseStep 2153015 = 3229523) B3229523
theorem B78781207 : Blo 956588 78781207 := bstep (se 1 (by rfl) ⟨59085905, by rfl⟩ : syracuseStep 78781207 = 118171811) B118171811
theorem B3067807 : Blo 956588 3067807 := bstep (se 1 (by rfl) ⟨2300855, by rfl⟩ : syracuseStep 3067807 = 4601711) B4601711
theorem B1435343 : Blo 956588 1435343 := bstep (se 1 (by rfl) ⟨1076507, by rfl⟩ : syracuseStep 1435343 = 2153015) B2153015
theorem B10939373 : Blo 956588 10939373 := bstep (se 3 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 10939373 = 4102265) B4102265
theorem B956895 : Blo 956588 956895 := bstep (se 1 (by rfl) ⟨717671, by rfl⟩ : syracuseStep 956895 = 1435343) B1435343
theorem B7292915 : Blo 956588 7292915 := bstep (se 1 (by rfl) ⟨5469686, by rfl⟩ : syracuseStep 7292915 = 10939373) B10939373
theorem B105041609 : Blo 956588 105041609 := bstep (se 2 (by rfl) ⟨39390603, by rfl⟩ : syracuseStep 105041609 = 78781207) B78781207
theorem B4090409 : Blo 956588 4090409 := bstep (se 2 (by rfl) ⟨1533903, by rfl⟩ : syracuseStep 4090409 = 3067807) B3067807
theorem B70027739 : Blo 956588 70027739 := bstep (se 1 (by rfl) ⟨52520804, by rfl⟩ : syracuseStep 70027739 = 105041609) B105041609
theorem B2726939 : Blo 956588 2726939 := bstep (se 1 (by rfl) ⟨2045204, by rfl⟩ : syracuseStep 2726939 = 4090409) B4090409
theorem B4861943 : Blo 956588 4861943 := bstep (se 1 (by rfl) ⟨3646457, by rfl⟩ : syracuseStep 4861943 = 7292915) B7292915
theorem B1817959 : Blo 956588 1817959 := bstep (se 1 (by rfl) ⟨1363469, by rfl⟩ : syracuseStep 1817959 = 2726939) B2726939
theorem B46685159 : Blo 956588 46685159 := bstep (se 1 (by rfl) ⟨35013869, by rfl⟩ : syracuseStep 46685159 = 70027739) B70027739
theorem B3241295 : Blo 956588 3241295 := bstep (se 1 (by rfl) ⟨2430971, by rfl⟩ : syracuseStep 3241295 = 4861943) B4861943
theorem B31123439 : Blo 956588 31123439 := bstep (se 1 (by rfl) ⟨23342579, by rfl⟩ : syracuseStep 31123439 = 46685159) B46685159
theorem B2160863 : Blo 956588 2160863 := bstep (se 1 (by rfl) ⟨1620647, by rfl⟩ : syracuseStep 2160863 = 3241295) B3241295
theorem B2423945 : Blo 956588 2423945 := bstep (se 2 (by rfl) ⟨908979, by rfl⟩ : syracuseStep 2423945 = 1817959) B1817959
theorem B20748959 : Blo 956588 20748959 := bstep (se 1 (by rfl) ⟨15561719, by rfl⟩ : syracuseStep 20748959 = 31123439) B31123439
theorem B1615963 : Blo 956588 1615963 := bstep (se 1 (by rfl) ⟨1211972, by rfl⟩ : syracuseStep 1615963 = 2423945) B2423945
theorem B1440575 : Blo 956588 1440575 := bstep (se 1 (by rfl) ⟨1080431, by rfl⟩ : syracuseStep 1440575 = 2160863) B2160863
theorem B13832639 : Blo 956588 13832639 := bstep (se 1 (by rfl) ⟨10374479, by rfl⟩ : syracuseStep 13832639 = 20748959) B20748959
theorem B960383 : Blo 956588 960383 := bstep (se 1 (by rfl) ⟨720287, by rfl⟩ : syracuseStep 960383 = 1440575) B1440575
theorem B2154617 : Blo 956588 2154617 := bstep (se 2 (by rfl) ⟨807981, by rfl⟩ : syracuseStep 2154617 = 1615963) B1615963
theorem B9221759 : Blo 956588 9221759 := bstep (se 1 (by rfl) ⟨6916319, by rfl⟩ : syracuseStep 9221759 = 13832639) B13832639
theorem B1436411 : Blo 956588 1436411 := bstep (se 1 (by rfl) ⟨1077308, by rfl⟩ : syracuseStep 1436411 = 2154617) B2154617
theorem B957607 : Blo 956588 957607 := bstep (se 1 (by rfl) ⟨718205, by rfl⟩ : syracuseStep 957607 = 1436411) B1436411
theorem B6147839 : Blo 956588 6147839 := bstep (se 1 (by rfl) ⟨4610879, by rfl⟩ : syracuseStep 6147839 = 9221759) B9221759
theorem B4098559 : Blo 956588 4098559 := bstep (se 1 (by rfl) ⟨3073919, by rfl⟩ : syracuseStep 4098559 = 6147839) B6147839
theorem B5464745 : Blo 956588 5464745 := bstep (se 2 (by rfl) ⟨2049279, by rfl⟩ : syracuseStep 5464745 = 4098559) B4098559
theorem B3643163 : Blo 956588 3643163 := bstep (se 1 (by rfl) ⟨2732372, by rfl⟩ : syracuseStep 3643163 = 5464745) B5464745
theorem B2428775 : Blo 956588 2428775 := bstep (se 1 (by rfl) ⟨1821581, by rfl⟩ : syracuseStep 2428775 = 3643163) B3643163
theorem B1619183 : Blo 956588 1619183 := bstep (se 1 (by rfl) ⟨1214387, by rfl⟩ : syracuseStep 1619183 = 2428775) B2428775
theorem B1079455 : Blo 956588 1079455 := bstep (se 1 (by rfl) ⟨809591, by rfl⟩ : syracuseStep 1079455 = 1619183) B1619183
theorem B1439273 : Blo 956588 1439273 := bstep (se 2 (by rfl) ⟨539727, by rfl⟩ : syracuseStep 1439273 = 1079455) B1079455
theorem B959515 : Blo 956588 959515 := bstep (se 1 (by rfl) ⟨719636, by rfl⟩ : syracuseStep 959515 = 1439273) B1439273

theorem C0 (j : ℕ) (h1 : 239147 ≤ j) (h2 : j ≤ 239846) : Blo 956588 (4 * j + 3) := by
  interval_cases j
  · exact B956591
  · exact B956595
  · exact B956599
  · exact B956603
  · exact B956607
  · exact B956611
  · exact B956615
  · exact B956619
  · exact B956623
  · exact B956627
  · exact B956631
  · exact B956635
  · exact B956639
  · exact B956643
  · exact B956647
  · exact B956651
  · exact B956655
  · exact B956659
  · exact B956663
  · exact B956667
  · exact B956671
  · exact B956675
  · exact B956679
  · exact B956683
  · exact B956687
  · exact B956691
  · exact B956695
  · exact B956699
  · exact B956703
  · exact B956707
  · exact B956711
  · exact B956715
  · exact B956719
  · exact B956723
  · exact B956727
  · exact B956731
  · exact B956735
  · exact B956739
  · exact B956743
  · exact B956747
  · exact B956751
  · exact B956755
  · exact B956759
  · exact B956763
  · exact B956767
  · exact B956771
  · exact B956775
  · exact B956779
  · exact B956783
  · exact B956787
  · exact B956791
  · exact B956795
  · exact B956799
  · exact B956803
  · exact B956807
  · exact B956811
  · exact B956815
  · exact B956819
  · exact B956823
  · exact B956827
  · exact B956831
  · exact B956835
  · exact B956839
  · exact B956843
  · exact B956847
  · exact B956851
  · exact B956855
  · exact B956859
  · exact B956863
  · exact B956867
  · exact B956871
  · exact B956875
  · exact B956879
  · exact B956883
  · exact B956887
  · exact B956891
  · exact B956895
  · exact B956899
  · exact B956903
  · exact B956907
  · exact B956911
  · exact B956915
  · exact B956919
  · exact B956923
  · exact B956927
  · exact B956931
  · exact B956935
  · exact B956939
  · exact B956943
  · exact B956947
  · exact B956951
  · exact B956955
  · exact B956959
  · exact B956963
  · exact B956967
  · exact B956971
  · exact B956975
  · exact B956979
  · exact B956983
  · exact B956987
  · exact B956991
  · exact B956995
  · exact B956999
  · exact B957003
  · exact B957007
  · exact B957011
  · exact B957015
  · exact B957019
  · exact B957023
  · exact B957027
  · exact B957031
  · exact B957035
  · exact B957039
  · exact B957043
  · exact B957047
  · exact B957051
  · exact B957055
  · exact B957059
  · exact B957063
  · exact B957067
  · exact B957071
  · exact B957075
  · exact B957079
  · exact B957083
  · exact B957087
  · exact B957091
  · exact B957095
  · exact B957099
  · exact B957103
  · exact B957107
  · exact B957111
  · exact B957115
  · exact B957119
  · exact B957123
  · exact B957127
  · exact B957131
  · exact B957135
  · exact B957139
  · exact B957143
  · exact B957147
  · exact B957151
  · exact B957155
  · exact B957159
  · exact B957163
  · exact B957167
  · exact B957171
  · exact B957175
  · exact B957179
  · exact B957183
  · exact B957187
  · exact B957191
  · exact B957195
  · exact B957199
  · exact B957203
  · exact B957207
  · exact B957211
  · exact B957215
  · exact B957219
  · exact B957223
  · exact B957227
  · exact B957231
  · exact B957235
  · exact B957239
  · exact B957243
  · exact B957247
  · exact B957251
  · exact B957255
  · exact B957259
  · exact B957263
  · exact B957267
  · exact B957271
  · exact B957275
  · exact B957279
  · exact B957283
  · exact B957287
  · exact B957291
  · exact B957295
  · exact B957299
  · exact B957303
  · exact B957307
  · exact B957311
  · exact B957315
  · exact B957319
  · exact B957323
  · exact B957327
  · exact B957331
  · exact B957335
  · exact B957339
  · exact B957343
  · exact B957347
  · exact B957351
  · exact B957355
  · exact B957359
  · exact B957363
  · exact B957367
  · exact B957371
  · exact B957375
  · exact B957379
  · exact B957383
  · exact B957387
  · exact B957391
  · exact B957395
  · exact B957399
  · exact B957403
  · exact B957407
  · exact B957411
  · exact B957415
  · exact B957419
  · exact B957423
  · exact B957427
  · exact B957431
  · exact B957435
  · exact B957439
  · exact B957443
  · exact B957447
  · exact B957451
  · exact B957455
  · exact B957459
  · exact B957463
  · exact B957467
  · exact B957471
  · exact B957475
  · exact B957479
  · exact B957483
  · exact B957487
  · exact B957491
  · exact B957495
  · exact B957499
  · exact B957503
  · exact B957507
  · exact B957511
  · exact B957515
  · exact B957519
  · exact B957523
  · exact B957527
  · exact B957531
  · exact B957535
  · exact B957539
  · exact B957543
  · exact B957547
  · exact B957551
  · exact B957555
  · exact B957559
  · exact B957563
  · exact B957567
  · exact B957571
  · exact B957575
  · exact B957579
  · exact B957583
  · exact B957587
  · exact B957591
  · exact B957595
  · exact B957599
  · exact B957603
  · exact B957607
  · exact B957611
  · exact B957615
  · exact B957619
  · exact B957623
  · exact B957627
  · exact B957631
  · exact B957635
  · exact B957639
  · exact B957643
  · exact B957647
  · exact B957651
  · exact B957655
  · exact B957659
  · exact B957663
  · exact B957667
  · exact B957671
  · exact B957675
  · exact B957679
  · exact B957683
  · exact B957687
  · exact B957691
  · exact B957695
  · exact B957699
  · exact B957703
  · exact B957707
  · exact B957711
  · exact B957715
  · exact B957719
  · exact B957723
  · exact B957727
  · exact B957731
  · exact B957735
  · exact B957739
  · exact B957743
  · exact B957747
  · exact B957751
  · exact B957755
  · exact B957759
  · exact B957763
  · exact B957767
  · exact B957771
  · exact B957775
  · exact B957779
  · exact B957783
  · exact B957787
  · exact B957791
  · exact B957795
  · exact B957799
  · exact B957803
  · exact B957807
  · exact B957811
  · exact B957815
  · exact B957819
  · exact B957823
  · exact B957827
  · exact B957831
  · exact B957835
  · exact B957839
  · exact B957843
  · exact B957847
  · exact B957851
  · exact B957855
  · exact B957859
  · exact B957863
  · exact B957867
  · exact B957871
  · exact B957875
  · exact B957879
  · exact B957883
  · exact B957887
  · exact B957891
  · exact B957895
  · exact B957899
  · exact B957903
  · exact B957907
  · exact B957911
  · exact B957915
  · exact B957919
  · exact B957923
  · exact B957927
  · exact B957931
  · exact B957935
  · exact B957939
  · exact B957943
  · exact B957947
  · exact B957951
  · exact B957955
  · exact B957959
  · exact B957963
  · exact B957967
  · exact B957971
  · exact B957975
  · exact B957979
  · exact B957983
  · exact B957987
  · exact B957991
  · exact B957995
  · exact B957999
  · exact B958003
  · exact B958007
  · exact B958011
  · exact B958015
  · exact B958019
  · exact B958023
  · exact B958027
  · exact B958031
  · exact B958035
  · exact B958039
  · exact B958043
  · exact B958047
  · exact B958051
  · exact B958055
  · exact B958059
  · exact B958063
  · exact B958067
  · exact B958071
  · exact B958075
  · exact B958079
  · exact B958083
  · exact B958087
  · exact B958091
  · exact B958095
  · exact B958099
  · exact B958103
  · exact B958107
  · exact B958111
  · exact B958115
  · exact B958119
  · exact B958123
  · exact B958127
  · exact B958131
  · exact B958135
  · exact B958139
  · exact B958143
  · exact B958147
  · exact B958151
  · exact B958155
  · exact B958159
  · exact B958163
  · exact B958167
  · exact B958171
  · exact B958175
  · exact B958179
  · exact B958183
  · exact B958187
  · exact B958191
  · exact B958195
  · exact B958199
  · exact B958203
  · exact B958207
  · exact B958211
  · exact B958215
  · exact B958219
  · exact B958223
  · exact B958227
  · exact B958231
  · exact B958235
  · exact B958239
  · exact B958243
  · exact B958247
  · exact B958251
  · exact B958255
  · exact B958259
  · exact B958263
  · exact B958267
  · exact B958271
  · exact B958275
  · exact B958279
  · exact B958283
  · exact B958287
  · exact B958291
  · exact B958295
  · exact B958299
  · exact B958303
  · exact B958307
  · exact B958311
  · exact B958315
  · exact B958319
  · exact B958323
  · exact B958327
  · exact B958331
  · exact B958335
  · exact B958339
  · exact B958343
  · exact B958347
  · exact B958351
  · exact B958355
  · exact B958359
  · exact B958363
  · exact B958367
  · exact B958371
  · exact B958375
  · exact B958379
  · exact B958383
  · exact B958387
  · exact B958391
  · exact B958395
  · exact B958399
  · exact B958403
  · exact B958407
  · exact B958411
  · exact B958415
  · exact B958419
  · exact B958423
  · exact B958427
  · exact B958431
  · exact B958435
  · exact B958439
  · exact B958443
  · exact B958447
  · exact B958451
  · exact B958455
  · exact B958459
  · exact B958463
  · exact B958467
  · exact B958471
  · exact B958475
  · exact B958479
  · exact B958483
  · exact B958487
  · exact B958491
  · exact B958495
  · exact B958499
  · exact B958503
  · exact B958507
  · exact B958511
  · exact B958515
  · exact B958519
  · exact B958523
  · exact B958527
  · exact B958531
  · exact B958535
  · exact B958539
  · exact B958543
  · exact B958547
  · exact B958551
  · exact B958555
  · exact B958559
  · exact B958563
  · exact B958567
  · exact B958571
  · exact B958575
  · exact B958579
  · exact B958583
  · exact B958587
  · exact B958591
  · exact B958595
  · exact B958599
  · exact B958603
  · exact B958607
  · exact B958611
  · exact B958615
  · exact B958619
  · exact B958623
  · exact B958627
  · exact B958631
  · exact B958635
  · exact B958639
  · exact B958643
  · exact B958647
  · exact B958651
  · exact B958655
  · exact B958659
  · exact B958663
  · exact B958667
  · exact B958671
  · exact B958675
  · exact B958679
  · exact B958683
  · exact B958687
  · exact B958691
  · exact B958695
  · exact B958699
  · exact B958703
  · exact B958707
  · exact B958711
  · exact B958715
  · exact B958719
  · exact B958723
  · exact B958727
  · exact B958731
  · exact B958735
  · exact B958739
  · exact B958743
  · exact B958747
  · exact B958751
  · exact B958755
  · exact B958759
  · exact B958763
  · exact B958767
  · exact B958771
  · exact B958775
  · exact B958779
  · exact B958783
  · exact B958787
  · exact B958791
  · exact B958795
  · exact B958799
  · exact B958803
  · exact B958807
  · exact B958811
  · exact B958815
  · exact B958819
  · exact B958823
  · exact B958827
  · exact B958831
  · exact B958835
  · exact B958839
  · exact B958843
  · exact B958847
  · exact B958851
  · exact B958855
  · exact B958859
  · exact B958863
  · exact B958867
  · exact B958871
  · exact B958875
  · exact B958879
  · exact B958883
  · exact B958887
  · exact B958891
  · exact B958895
  · exact B958899
  · exact B958903
  · exact B958907
  · exact B958911
  · exact B958915
  · exact B958919
  · exact B958923
  · exact B958927
  · exact B958931
  · exact B958935
  · exact B958939
  · exact B958943
  · exact B958947
  · exact B958951
  · exact B958955
  · exact B958959
  · exact B958963
  · exact B958967
  · exact B958971
  · exact B958975
  · exact B958979
  · exact B958983
  · exact B958987
  · exact B958991
  · exact B958995
  · exact B958999
  · exact B959003
  · exact B959007
  · exact B959011
  · exact B959015
  · exact B959019
  · exact B959023
  · exact B959027
  · exact B959031
  · exact B959035
  · exact B959039
  · exact B959043
  · exact B959047
  · exact B959051
  · exact B959055
  · exact B959059
  · exact B959063
  · exact B959067
  · exact B959071
  · exact B959075
  · exact B959079
  · exact B959083
  · exact B959087
  · exact B959091
  · exact B959095
  · exact B959099
  · exact B959103
  · exact B959107
  · exact B959111
  · exact B959115
  · exact B959119
  · exact B959123
  · exact B959127
  · exact B959131
  · exact B959135
  · exact B959139
  · exact B959143
  · exact B959147
  · exact B959151
  · exact B959155
  · exact B959159
  · exact B959163
  · exact B959167
  · exact B959171
  · exact B959175
  · exact B959179
  · exact B959183
  · exact B959187
  · exact B959191
  · exact B959195
  · exact B959199
  · exact B959203
  · exact B959207
  · exact B959211
  · exact B959215
  · exact B959219
  · exact B959223
  · exact B959227
  · exact B959231
  · exact B959235
  · exact B959239
  · exact B959243
  · exact B959247
  · exact B959251
  · exact B959255
  · exact B959259
  · exact B959263
  · exact B959267
  · exact B959271
  · exact B959275
  · exact B959279
  · exact B959283
  · exact B959287
  · exact B959291
  · exact B959295
  · exact B959299
  · exact B959303
  · exact B959307
  · exact B959311
  · exact B959315
  · exact B959319
  · exact B959323
  · exact B959327
  · exact B959331
  · exact B959335
  · exact B959339
  · exact B959343
  · exact B959347
  · exact B959351
  · exact B959355
  · exact B959359
  · exact B959363
  · exact B959367
  · exact B959371
  · exact B959375
  · exact B959379
  · exact B959383
  · exact B959387

theorem C1 (j : ℕ) (h1 : 239847 ≤ j) (h2 : j ≤ 240146) : Blo 956588 (4 * j + 3) := by
  interval_cases j
  · exact B959391
  · exact B959395
  · exact B959399
  · exact B959403
  · exact B959407
  · exact B959411
  · exact B959415
  · exact B959419
  · exact B959423
  · exact B959427
  · exact B959431
  · exact B959435
  · exact B959439
  · exact B959443
  · exact B959447
  · exact B959451
  · exact B959455
  · exact B959459
  · exact B959463
  · exact B959467
  · exact B959471
  · exact B959475
  · exact B959479
  · exact B959483
  · exact B959487
  · exact B959491
  · exact B959495
  · exact B959499
  · exact B959503
  · exact B959507
  · exact B959511
  · exact B959515
  · exact B959519
  · exact B959523
  · exact B959527
  · exact B959531
  · exact B959535
  · exact B959539
  · exact B959543
  · exact B959547
  · exact B959551
  · exact B959555
  · exact B959559
  · exact B959563
  · exact B959567
  · exact B959571
  · exact B959575
  · exact B959579
  · exact B959583
  · exact B959587
  · exact B959591
  · exact B959595
  · exact B959599
  · exact B959603
  · exact B959607
  · exact B959611
  · exact B959615
  · exact B959619
  · exact B959623
  · exact B959627
  · exact B959631
  · exact B959635
  · exact B959639
  · exact B959643
  · exact B959647
  · exact B959651
  · exact B959655
  · exact B959659
  · exact B959663
  · exact B959667
  · exact B959671
  · exact B959675
  · exact B959679
  · exact B959683
  · exact B959687
  · exact B959691
  · exact B959695
  · exact B959699
  · exact B959703
  · exact B959707
  · exact B959711
  · exact B959715
  · exact B959719
  · exact B959723
  · exact B959727
  · exact B959731
  · exact B959735
  · exact B959739
  · exact B959743
  · exact B959747
  · exact B959751
  · exact B959755
  · exact B959759
  · exact B959763
  · exact B959767
  · exact B959771
  · exact B959775
  · exact B959779
  · exact B959783
  · exact B959787
  · exact B959791
  · exact B959795
  · exact B959799
  · exact B959803
  · exact B959807
  · exact B959811
  · exact B959815
  · exact B959819
  · exact B959823
  · exact B959827
  · exact B959831
  · exact B959835
  · exact B959839
  · exact B959843
  · exact B959847
  · exact B959851
  · exact B959855
  · exact B959859
  · exact B959863
  · exact B959867
  · exact B959871
  · exact B959875
  · exact B959879
  · exact B959883
  · exact B959887
  · exact B959891
  · exact B959895
  · exact B959899
  · exact B959903
  · exact B959907
  · exact B959911
  · exact B959915
  · exact B959919
  · exact B959923
  · exact B959927
  · exact B959931
  · exact B959935
  · exact B959939
  · exact B959943
  · exact B959947
  · exact B959951
  · exact B959955
  · exact B959959
  · exact B959963
  · exact B959967
  · exact B959971
  · exact B959975
  · exact B959979
  · exact B959983
  · exact B959987
  · exact B959991
  · exact B959995
  · exact B959999
  · exact B960003
  · exact B960007
  · exact B960011
  · exact B960015
  · exact B960019
  · exact B960023
  · exact B960027
  · exact B960031
  · exact B960035
  · exact B960039
  · exact B960043
  · exact B960047
  · exact B960051
  · exact B960055
  · exact B960059
  · exact B960063
  · exact B960067
  · exact B960071
  · exact B960075
  · exact B960079
  · exact B960083
  · exact B960087
  · exact B960091
  · exact B960095
  · exact B960099
  · exact B960103
  · exact B960107
  · exact B960111
  · exact B960115
  · exact B960119
  · exact B960123
  · exact B960127
  · exact B960131
  · exact B960135
  · exact B960139
  · exact B960143
  · exact B960147
  · exact B960151
  · exact B960155
  · exact B960159
  · exact B960163
  · exact B960167
  · exact B960171
  · exact B960175
  · exact B960179
  · exact B960183
  · exact B960187
  · exact B960191
  · exact B960195
  · exact B960199
  · exact B960203
  · exact B960207
  · exact B960211
  · exact B960215
  · exact B960219
  · exact B960223
  · exact B960227
  · exact B960231
  · exact B960235
  · exact B960239
  · exact B960243
  · exact B960247
  · exact B960251
  · exact B960255
  · exact B960259
  · exact B960263
  · exact B960267
  · exact B960271
  · exact B960275
  · exact B960279
  · exact B960283
  · exact B960287
  · exact B960291
  · exact B960295
  · exact B960299
  · exact B960303
  · exact B960307
  · exact B960311
  · exact B960315
  · exact B960319
  · exact B960323
  · exact B960327
  · exact B960331
  · exact B960335
  · exact B960339
  · exact B960343
  · exact B960347
  · exact B960351
  · exact B960355
  · exact B960359
  · exact B960363
  · exact B960367
  · exact B960371
  · exact B960375
  · exact B960379
  · exact B960383
  · exact B960387
  · exact B960391
  · exact B960395
  · exact B960399
  · exact B960403
  · exact B960407
  · exact B960411
  · exact B960415
  · exact B960419
  · exact B960423
  · exact B960427
  · exact B960431
  · exact B960435
  · exact B960439
  · exact B960443
  · exact B960447
  · exact B960451
  · exact B960455
  · exact B960459
  · exact B960463
  · exact B960467
  · exact B960471
  · exact B960475
  · exact B960479
  · exact B960483
  · exact B960487
  · exact B960491
  · exact B960495
  · exact B960499
  · exact B960503
  · exact B960507
  · exact B960511
  · exact B960515
  · exact B960519
  · exact B960523
  · exact B960527
  · exact B960531
  · exact B960535
  · exact B960539
  · exact B960543
  · exact B960547
  · exact B960551
  · exact B960555
  · exact B960559
  · exact B960563
  · exact B960567
  · exact B960571
  · exact B960575
  · exact B960579
  · exact B960583
  · exact B960587

theorem solution (m : ℕ) (hlo : 956588 ≤ m) (hhi : m ≤ 960588) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 239147 ≤ j := by omega
    have hj2 : j ≤ 240146 := by omega
    have hb : Blo 956588 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 239847 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
