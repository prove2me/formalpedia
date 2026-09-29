-- Prove2me | solution 1 for syracuse_descends_range_1219427_1220927
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:56.198822+00:00
-- url     : https://prove2.me/submissions/4b5749d5-cb23-4b21-b6af-70c4ace5aef3

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


theorem B2744333 : Blo 1219427 2744333 := bbase (se 3 (by rfl) ⟨514562, by rfl⟩ : syracuseStep 2744333 = 1029125) (by norm_num)
theorem B1302581 : Blo 1219427 1302581 := bbase (se 5 (by rfl) ⟨61058, by rfl⟩ : syracuseStep 1302581 = 122117) (by norm_num)
theorem B2744405 : Blo 1219427 2744405 := bbase (se 8 (by rfl) ⟨16080, by rfl⟩ : syracuseStep 2744405 = 32161) (by norm_num)
theorem B3088469 : Blo 1219427 3088469 := bbase (se 8 (by rfl) ⟨18096, by rfl⟩ : syracuseStep 3088469 = 36193) (by norm_num)
theorem B1736797 : Blo 1219427 1736797 := bbase (se 3 (by rfl) ⟨325649, by rfl⟩ : syracuseStep 1736797 = 651299) (by norm_num)
theorem B1466461 : Blo 1219427 1466461 := bbase (se 3 (by rfl) ⟨274961, by rfl⟩ : syracuseStep 1466461 = 549923) (by norm_num)
theorem B1466509 : Blo 1219427 1466509 := bbase (se 3 (by rfl) ⟨274970, by rfl⟩ : syracuseStep 1466509 = 549941) (by norm_num)
theorem B2744477 : Blo 1219427 2744477 := bbase (se 3 (by rfl) ⟨514589, by rfl⟩ : syracuseStep 2744477 = 1029179) (by norm_num)
theorem B2605213 : Blo 1219427 2605213 := bbase (se 3 (by rfl) ⟨488477, by rfl⟩ : syracuseStep 2605213 = 976955) (by norm_num)
theorem B2744549 : Blo 1219427 2744549 := bbase (se 4 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 2744549 = 514603) (by norm_num)
theorem B2744621 : Blo 1219427 2744621 := bbase (se 3 (by rfl) ⟨514616, by rfl⟩ : syracuseStep 2744621 = 1029233) (by norm_num)
theorem B2744693 : Blo 1219427 2744693 := bbase (se 5 (by rfl) ⟨128657, by rfl⟩ : syracuseStep 2744693 = 257315) (by norm_num)
theorem B3088813 : Blo 1219427 3088813 := bbase (se 3 (by rfl) ⟨579152, by rfl⟩ : syracuseStep 3088813 = 1158305) (by norm_num)
theorem B9265589 : Blo 1219427 9265589 := bbase (se 5 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 9265589 = 868649) (by norm_num)
theorem B2744765 : Blo 1219427 2744765 := bbase (se 3 (by rfl) ⟨514643, by rfl⟩ : syracuseStep 2744765 = 1029287) (by norm_num)
theorem B6177221 : Blo 1219427 6177221 := bbase (se 4 (by rfl) ⟨579114, by rfl⟩ : syracuseStep 6177221 = 1158229) (by norm_num)
theorem B8028629 : Blo 1219427 8028629 := bbase (se 7 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 8028629 = 188171) (by norm_num)
theorem B1737173 : Blo 1219427 1737173 := bbase (se 7 (by rfl) ⟨20357, by rfl⟩ : syracuseStep 1737173 = 40715) (by norm_num)
theorem B1303025 : Blo 1219427 1303025 := bbase (se 2 (by rfl) ⟨488634, by rfl⟩ : syracuseStep 1303025 = 977269) (by norm_num)
theorem B3908101 : Blo 1219427 3908101 := bbase (se 4 (by rfl) ⟨366384, by rfl⟩ : syracuseStep 3908101 = 732769) (by norm_num)
theorem B2744837 : Blo 1219427 2744837 := bbase (se 4 (by rfl) ⟨257328, by rfl⟩ : syracuseStep 2744837 = 514657) (by norm_num)
theorem B3088925 : Blo 1219427 3088925 := bbase (se 3 (by rfl) ⟨579173, by rfl⟩ : syracuseStep 3088925 = 1158347) (by norm_num)
theorem B1303085 : Blo 1219427 1303085 := bbase (se 3 (by rfl) ⟨244328, by rfl⟩ : syracuseStep 1303085 = 488657) (by norm_num)
theorem B2744909 : Blo 1219427 2744909 := bbase (se 3 (by rfl) ⟨514670, by rfl⟩ : syracuseStep 2744909 = 1029341) (by norm_num)
theorem B21144149 : Blo 1219427 21144149 := bbase (se 8 (by rfl) ⟨123891, by rfl⟩ : syracuseStep 21144149 = 247783) (by norm_num)
theorem B6431333 : Blo 1219427 6431333 := bbase (se 4 (by rfl) ⟨602937, by rfl⟩ : syracuseStep 6431333 = 1205875) (by norm_num)
theorem B2605709 : Blo 1219427 2605709 := bbase (se 3 (by rfl) ⟨488570, by rfl⟩ : syracuseStep 2605709 = 977141) (by norm_num)
theorem B2744981 : Blo 1219427 2744981 := bbase (se 6 (by rfl) ⟨64335, by rfl⟩ : syracuseStep 2744981 = 128671) (by norm_num)
theorem B1303213 : Blo 1219427 1303213 := bbase (se 3 (by rfl) ⟨244352, by rfl⟩ : syracuseStep 1303213 = 488705) (by norm_num)
theorem B5210837 : Blo 1219427 5210837 := bbase (se 7 (by rfl) ⟨61064, by rfl⟩ : syracuseStep 5210837 = 122129) (by norm_num)
theorem B2745053 : Blo 1219427 2745053 := bbase (se 3 (by rfl) ⟨514697, by rfl⟩ : syracuseStep 2745053 = 1029395) (by norm_num)
theorem B3089117 : Blo 1219427 3089117 := bbase (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) (by norm_num)
theorem B2745125 : Blo 1219427 2745125 := bbase (se 4 (by rfl) ⟨257355, by rfl⟩ : syracuseStep 2745125 = 514711) (by norm_num)
theorem B2745197 : Blo 1219427 2745197 := bbase (se 3 (by rfl) ⟨514724, by rfl⟩ : syracuseStep 2745197 = 1029449) (by norm_num)
theorem B2745269 : Blo 1219427 2745269 := bbase (se 5 (by rfl) ⟨128684, by rfl⟩ : syracuseStep 2745269 = 257369) (by norm_num)
theorem B10560469 : Blo 1219427 10560469 := bbase (se 7 (by rfl) ⟨123755, by rfl⟩ : syracuseStep 10560469 = 247511) (by norm_num)
theorem B2745341 : Blo 1219427 2745341 := bbase (se 3 (by rfl) ⟨514751, by rfl⟩ : syracuseStep 2745341 = 1029503) (by norm_num)
theorem B3089461 : Blo 1219427 3089461 := bbase (se 5 (by rfl) ⟨144818, by rfl⟩ : syracuseStep 3089461 = 289637) (by norm_num)
theorem B2745413 : Blo 1219427 2745413 := bbase (se 4 (by rfl) ⟨257382, by rfl⟩ : syracuseStep 2745413 = 514765) (by norm_num)
theorem B1303657 : Blo 1219427 1303657 := bbase (se 2 (by rfl) ⟨488871, by rfl⟩ : syracuseStep 1303657 = 977743) (by norm_num)
theorem B5866613 : Blo 1219427 5866613 := bbase (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) (by norm_num)
theorem B2745485 : Blo 1219427 2745485 := bbase (se 3 (by rfl) ⟨514778, by rfl⟩ : syracuseStep 2745485 = 1029557) (by norm_num)
theorem B3089573 : Blo 1219427 3089573 := bbase (se 4 (by rfl) ⟨289647, by rfl⟩ : syracuseStep 3089573 = 579295) (by norm_num)
theorem B2745557 : Blo 1219427 2745557 := bbase (se 7 (by rfl) ⟨32174, by rfl⟩ : syracuseStep 2745557 = 64349) (by norm_num)
theorem B3130589 : Blo 1219427 3130589 := bbase (se 3 (by rfl) ⟨586985, by rfl⟩ : syracuseStep 3130589 = 1173971) (by norm_num)
theorem B1303777 : Blo 1219427 1303777 := bbase (se 2 (by rfl) ⟨488916, by rfl⟩ : syracuseStep 1303777 = 977833) (by norm_num)
theorem B3474677 : Blo 1219427 3474677 := bbase (se 5 (by rfl) ⟨162875, by rfl⟩ : syracuseStep 3474677 = 325751) (by norm_num)
theorem B2745629 : Blo 1219427 2745629 := bbase (se 3 (by rfl) ⟨514805, by rfl⟩ : syracuseStep 2745629 = 1029611) (by norm_num)
theorem B2745701 : Blo 1219427 2745701 := bbase (se 4 (by rfl) ⟨257409, by rfl⟩ : syracuseStep 2745701 = 514819) (by norm_num)
theorem B3089765 : Blo 1219427 3089765 := bbase (se 4 (by rfl) ⟨289665, by rfl⟩ : syracuseStep 3089765 = 579331) (by norm_num)
theorem B23782805 : Blo 1219427 23782805 := bbase (se 6 (by rfl) ⟨557409, by rfl⟩ : syracuseStep 23782805 = 1114819) (by norm_num)
theorem B5866901 : Blo 1219427 5866901 := bbase (se 6 (by rfl) ⟨137505, by rfl⟩ : syracuseStep 5866901 = 275011) (by norm_num)
theorem B2745773 : Blo 1219427 2745773 := bbase (se 3 (by rfl) ⟨514832, by rfl⟩ : syracuseStep 2745773 = 1029665) (by norm_num)
theorem B1648093 : Blo 1219427 1648093 := bbase (se 3 (by rfl) ⟨309017, by rfl⟩ : syracuseStep 1648093 = 618035) (by norm_num)
theorem B2745845 : Blo 1219427 2745845 := bbase (se 5 (by rfl) ⟨128711, by rfl⟩ : syracuseStep 2745845 = 257423) (by norm_num)
theorem B2606597 : Blo 1219427 2606597 := bbase (se 4 (by rfl) ⟨244368, by rfl⟩ : syracuseStep 2606597 = 488737) (by norm_num)
theorem B2745917 : Blo 1219427 2745917 := bbase (se 3 (by rfl) ⟨514859, by rfl⟩ : syracuseStep 2745917 = 1029719) (by norm_num)
theorem B2057845 : Blo 1219427 2057845 := bbase (se 5 (by rfl) ⟨96461, by rfl⟩ : syracuseStep 2057845 = 192923) (by norm_num)
theorem B2606717 : Blo 1219427 2606717 := bbase (se 3 (by rfl) ⟨488759, by rfl⟩ : syracuseStep 2606717 = 977519) (by norm_num)
theorem B2745989 : Blo 1219427 2745989 := bbase (se 4 (by rfl) ⟨257436, by rfl⟩ : syracuseStep 2745989 = 514873) (by norm_num)
theorem B3090109 : Blo 1219427 3090109 := bbase (se 3 (by rfl) ⟨579395, by rfl⟩ : syracuseStep 3090109 = 1158791) (by norm_num)
theorem B2057933 : Blo 1219427 2057933 := bbase (se 3 (by rfl) ⟨385862, by rfl⟩ : syracuseStep 2057933 = 771725) (by norm_num)
theorem B2746061 : Blo 1219427 2746061 := bbase (se 3 (by rfl) ⟨514886, by rfl⟩ : syracuseStep 2746061 = 1029773) (by norm_num)
theorem B4630229 : Blo 1219427 4630229 := bbase (se 7 (by rfl) ⟨54260, by rfl⟩ : syracuseStep 4630229 = 108521) (by norm_num)
theorem B6178517 : Blo 1219427 6178517 := bbase (se 7 (by rfl) ⟨72404, by rfl⟩ : syracuseStep 6178517 = 144809) (by norm_num)
theorem B2746133 : Blo 1219427 2746133 := bbase (se 6 (by rfl) ⟨64362, by rfl⟩ : syracuseStep 2746133 = 128725) (by norm_num)
theorem B3090221 : Blo 1219427 3090221 := bbase (se 3 (by rfl) ⟨579416, by rfl⟩ : syracuseStep 3090221 = 1158833) (by norm_num)
theorem B2058061 : Blo 1219427 2058061 := bbase (se 3 (by rfl) ⟨385886, by rfl⟩ : syracuseStep 2058061 = 771773) (by norm_num)
theorem B2746205 : Blo 1219427 2746205 := bbase (se 3 (by rfl) ⟨514913, by rfl⟩ : syracuseStep 2746205 = 1029827) (by norm_num)
theorem B3475349 : Blo 1219427 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B4515749 : Blo 1219427 4515749 := bbase (se 4 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 4515749 = 846703) (by norm_num)
theorem B2058149 : Blo 1219427 2058149 := bbase (se 4 (by rfl) ⟨192951, by rfl⟩ : syracuseStep 2058149 = 385903) (by norm_num)
theorem B2746277 : Blo 1219427 2746277 := bbase (se 4 (by rfl) ⟨257463, by rfl⟩ : syracuseStep 2746277 = 514927) (by norm_num)
theorem B2746349 : Blo 1219427 2746349 := bbase (se 3 (by rfl) ⟨514940, by rfl⟩ : syracuseStep 2746349 = 1029881) (by norm_num)
theorem B3090413 : Blo 1219427 3090413 := bbase (se 3 (by rfl) ⟨579452, by rfl⟩ : syracuseStep 3090413 = 1158905) (by norm_num)
theorem B4630517 : Blo 1219427 4630517 := bbase (se 5 (by rfl) ⟨217055, by rfl⟩ : syracuseStep 4630517 = 434111) (by norm_num)
theorem B2058277 : Blo 1219427 2058277 := bbase (se 4 (by rfl) ⟨192963, by rfl⟩ : syracuseStep 2058277 = 385927) (by norm_num)
theorem B2746421 : Blo 1219427 2746421 := bbase (se 5 (by rfl) ⟨128738, by rfl⟩ : syracuseStep 2746421 = 257477) (by norm_num)
theorem B2058365 : Blo 1219427 2058365 := bbase (se 3 (by rfl) ⟨385943, by rfl⟩ : syracuseStep 2058365 = 771887) (by norm_num)
theorem B2746493 : Blo 1219427 2746493 := bbase (se 3 (by rfl) ⟨514967, by rfl⟩ : syracuseStep 2746493 = 1029935) (by norm_num)
theorem B2746565 : Blo 1219427 2746565 := bbase (se 4 (by rfl) ⟨257490, by rfl⟩ : syracuseStep 2746565 = 514981) (by norm_num)
theorem B2607349 : Blo 1219427 2607349 := bbase (se 5 (by rfl) ⟨122219, by rfl⟩ : syracuseStep 2607349 = 244439) (by norm_num)
theorem B2058493 : Blo 1219427 2058493 := bbase (se 3 (by rfl) ⟨385967, by rfl⟩ : syracuseStep 2058493 = 771935) (by norm_num)
theorem B2746637 : Blo 1219427 2746637 := bbase (se 3 (by rfl) ⟨514994, by rfl⟩ : syracuseStep 2746637 = 1029989) (by norm_num)
theorem B1829141 : Blo 1219427 1829141 := bbase (se 6 (by rfl) ⟨42870, by rfl⟩ : syracuseStep 1829141 = 85741) (by norm_num)
theorem B1829165 : Blo 1219427 1829165 := bbase (se 3 (by rfl) ⟨342968, by rfl⟩ : syracuseStep 1829165 = 685937) (by norm_num)
theorem B1829189 : Blo 1219427 1829189 := bbase (se 4 (by rfl) ⟨171486, by rfl⟩ : syracuseStep 1829189 = 342973) (by norm_num)
theorem B3475781 : Blo 1219427 3475781 := bbase (se 4 (by rfl) ⟨325854, by rfl⟩ : syracuseStep 3475781 = 651709) (by norm_num)
theorem B2058581 : Blo 1219427 2058581 := bbase (se 10 (by rfl) ⟨3015, by rfl⟩ : syracuseStep 2058581 = 6031) (by norm_num)
theorem B2746709 : Blo 1219427 2746709 := bbase (se 10 (by rfl) ⟨4023, by rfl⟩ : syracuseStep 2746709 = 8047) (by norm_num)
theorem B1829213 : Blo 1219427 1829213 := bbase (se 3 (by rfl) ⟨342977, by rfl⟩ : syracuseStep 1829213 = 685955) (by norm_num)
theorem B1829237 : Blo 1219427 1829237 := bbase (se 5 (by rfl) ⟨85745, by rfl⟩ : syracuseStep 1829237 = 171491) (by norm_num)
theorem B1829261 : Blo 1219427 1829261 := bbase (se 3 (by rfl) ⟨342986, by rfl⟩ : syracuseStep 1829261 = 685973) (by norm_num)
theorem B2746781 : Blo 1219427 2746781 := bbase (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) (by norm_num)
theorem B1829285 : Blo 1219427 1829285 := bbase (se 4 (by rfl) ⟨171495, by rfl⟩ : syracuseStep 1829285 = 342991) (by norm_num)
theorem B1829309 : Blo 1219427 1829309 := bbase (se 3 (by rfl) ⟨342995, by rfl⟩ : syracuseStep 1829309 = 685991) (by norm_num)
theorem B1321409 : Blo 1219427 1321409 := bbase (se 2 (by rfl) ⟨495528, by rfl⟩ : syracuseStep 1321409 = 991057) (by norm_num)
theorem B5212613 : Blo 1219427 5212613 := bbase (se 4 (by rfl) ⟨488682, by rfl⟩ : syracuseStep 5212613 = 977365) (by norm_num)
theorem B1829333 : Blo 1219427 1829333 := bbase (se 7 (by rfl) ⟨21437, by rfl⟩ : syracuseStep 1829333 = 42875) (by norm_num)
theorem B2058709 : Blo 1219427 2058709 := bbase (se 7 (by rfl) ⟨24125, by rfl⟩ : syracuseStep 2058709 = 48251) (by norm_num)
theorem B2746853 : Blo 1219427 2746853 := bbase (se 4 (by rfl) ⟨257517, by rfl⟩ : syracuseStep 2746853 = 515035) (by norm_num)
theorem B1829357 : Blo 1219427 1829357 := bbase (se 3 (by rfl) ⟨343004, by rfl⟩ : syracuseStep 1829357 = 686009) (by norm_num)
theorem B1829381 : Blo 1219427 1829381 := bbase (se 4 (by rfl) ⟨171504, by rfl⟩ : syracuseStep 1829381 = 343009) (by norm_num)
theorem B1829405 : Blo 1219427 1829405 := bbase (se 3 (by rfl) ⟨343013, by rfl⟩ : syracuseStep 1829405 = 686027) (by norm_num)
theorem B2058797 : Blo 1219427 2058797 := bbase (se 3 (by rfl) ⟨386024, by rfl⟩ : syracuseStep 2058797 = 772049) (by norm_num)
theorem B2746925 : Blo 1219427 2746925 := bbase (se 3 (by rfl) ⟨515048, by rfl⟩ : syracuseStep 2746925 = 1030097) (by norm_num)
theorem B1829429 : Blo 1219427 1829429 := bbase (se 5 (by rfl) ⟨85754, by rfl⟩ : syracuseStep 1829429 = 171509) (by norm_num)
theorem B1829453 : Blo 1219427 1829453 := bbase (se 3 (by rfl) ⟨343022, by rfl⟩ : syracuseStep 1829453 = 686045) (by norm_num)
theorem B1829477 : Blo 1219427 1829477 := bbase (se 4 (by rfl) ⟨171513, by rfl⟩ : syracuseStep 1829477 = 343027) (by norm_num)
theorem B2746997 : Blo 1219427 2746997 := bbase (se 5 (by rfl) ⟨128765, by rfl⟩ : syracuseStep 2746997 = 257531) (by norm_num)
theorem B1829501 : Blo 1219427 1829501 := bbase (se 3 (by rfl) ⟨343031, by rfl⟩ : syracuseStep 1829501 = 686063) (by norm_num)
theorem B1829525 : Blo 1219427 1829525 := bbase (se 6 (by rfl) ⟨42879, by rfl⟩ : syracuseStep 1829525 = 85759) (by norm_num)
theorem B1829549 : Blo 1219427 1829549 := bbase (se 3 (by rfl) ⟨343040, by rfl⟩ : syracuseStep 1829549 = 686081) (by norm_num)
theorem B2058925 : Blo 1219427 2058925 := bbase (se 3 (by rfl) ⟨386048, by rfl⟩ : syracuseStep 2058925 = 772097) (by norm_num)
theorem B2747069 : Blo 1219427 2747069 := bbase (se 3 (by rfl) ⟨515075, by rfl⟩ : syracuseStep 2747069 = 1030151) (by norm_num)
theorem B4238021 : Blo 1219427 4238021 := bbase (se 4 (by rfl) ⟨397314, by rfl⟩ : syracuseStep 4238021 = 794629) (by norm_num)
theorem B1829573 : Blo 1219427 1829573 := bbase (se 4 (by rfl) ⟨171522, by rfl⟩ : syracuseStep 1829573 = 343045) (by norm_num)
theorem B20859605 : Blo 1219427 20859605 := bbase (se 7 (by rfl) ⟨244448, by rfl⟩ : syracuseStep 20859605 = 488897) (by norm_num)
theorem B1829597 : Blo 1219427 1829597 := bbase (se 3 (by rfl) ⟨343049, by rfl⟩ : syracuseStep 1829597 = 686099) (by norm_num)
theorem B1829621 : Blo 1219427 1829621 := bbase (se 5 (by rfl) ⟨85763, by rfl⟩ : syracuseStep 1829621 = 171527) (by norm_num)
theorem B2059013 : Blo 1219427 2059013 := bbase (se 4 (by rfl) ⟨193032, by rfl⟩ : syracuseStep 2059013 = 386065) (by norm_num)
theorem B1829645 : Blo 1219427 1829645 := bbase (se 3 (by rfl) ⟨343058, by rfl⟩ : syracuseStep 1829645 = 686117) (by norm_num)
theorem B1829669 : Blo 1219427 1829669 := bbase (se 4 (by rfl) ⟨171531, by rfl⟩ : syracuseStep 1829669 = 343063) (by norm_num)
theorem B1829693 : Blo 1219427 1829693 := bbase (se 3 (by rfl) ⟨343067, by rfl⟩ : syracuseStep 1829693 = 686135) (by norm_num)
theorem B1829717 : Blo 1219427 1829717 := bbase (se 9 (by rfl) ⟨5360, by rfl⟩ : syracuseStep 1829717 = 10721) (by norm_num)
theorem B1829741 : Blo 1219427 1829741 := bbase (se 3 (by rfl) ⟨343076, by rfl⟩ : syracuseStep 1829741 = 686153) (by norm_num)
theorem B1829765 : Blo 1219427 1829765 := bbase (se 4 (by rfl) ⟨171540, by rfl⟩ : syracuseStep 1829765 = 343081) (by norm_num)
theorem B2059141 : Blo 1219427 2059141 := bbase (se 4 (by rfl) ⟨193044, by rfl⟩ : syracuseStep 2059141 = 386089) (by norm_num)
theorem B1829789 : Blo 1219427 1829789 := bbase (se 3 (by rfl) ⟨343085, by rfl⟩ : syracuseStep 1829789 = 686171) (by norm_num)
theorem B1829813 : Blo 1219427 1829813 := bbase (se 5 (by rfl) ⟨85772, by rfl⟩ : syracuseStep 1829813 = 171545) (by norm_num)
theorem B1829837 : Blo 1219427 1829837 := bbase (se 3 (by rfl) ⟨343094, by rfl⟩ : syracuseStep 1829837 = 686189) (by norm_num)
theorem B2059229 : Blo 1219427 2059229 := bbase (se 3 (by rfl) ⟨386105, by rfl⟩ : syracuseStep 2059229 = 772211) (by norm_num)
theorem B1829861 : Blo 1219427 1829861 := bbase (se 4 (by rfl) ⟨171549, by rfl⟩ : syracuseStep 1829861 = 343099) (by norm_num)
theorem B6179813 : Blo 1219427 6179813 := bbase (se 4 (by rfl) ⟨579357, by rfl⟩ : syracuseStep 6179813 = 1158715) (by norm_num)
theorem B2116589 : Blo 1219427 2116589 := bbase (se 3 (by rfl) ⟨396860, by rfl⟩ : syracuseStep 2116589 = 793721) (by norm_num)
theorem B1829885 : Blo 1219427 1829885 := bbase (se 3 (by rfl) ⟨343103, by rfl⟩ : syracuseStep 1829885 = 686207) (by norm_num)
theorem B2640917 : Blo 1219427 2640917 := bbase (se 6 (by rfl) ⟨61896, by rfl⟩ : syracuseStep 2640917 = 123793) (by norm_num)
theorem B1829909 : Blo 1219427 1829909 := bbase (se 6 (by rfl) ⟨42888, by rfl⟩ : syracuseStep 1829909 = 85777) (by norm_num)
theorem B1829933 : Blo 1219427 1829933 := bbase (se 3 (by rfl) ⟨343112, by rfl⟩ : syracuseStep 1829933 = 686225) (by norm_num)
theorem B3476533 : Blo 1219427 3476533 := bbase (se 5 (by rfl) ⟨162962, by rfl⟩ : syracuseStep 3476533 = 325925) (by norm_num)
theorem B1829957 : Blo 1219427 1829957 := bbase (se 4 (by rfl) ⟨171558, by rfl⟩ : syracuseStep 1829957 = 343117) (by norm_num)
theorem B19786837 : Blo 1219427 19786837 := bbase (se 8 (by rfl) ⟨115938, by rfl⟩ : syracuseStep 19786837 = 231877) (by norm_num)
theorem B1829981 : Blo 1219427 1829981 := bbase (se 3 (by rfl) ⟨343121, by rfl⟩ : syracuseStep 1829981 = 686243) (by norm_num)
theorem B2059357 : Blo 1219427 2059357 := bbase (se 3 (by rfl) ⟨386129, by rfl⟩ : syracuseStep 2059357 = 772259) (by norm_num)
theorem B1830005 : Blo 1219427 1830005 := bbase (se 5 (by rfl) ⟨85781, by rfl⟩ : syracuseStep 1830005 = 171563) (by norm_num)
theorem B1830029 : Blo 1219427 1830029 := bbase (se 3 (by rfl) ⟨343130, by rfl⟩ : syracuseStep 1830029 = 686261) (by norm_num)
theorem B4631701 : Blo 1219427 4631701 := bbase (se 6 (by rfl) ⟨108555, by rfl⟩ : syracuseStep 4631701 = 217111) (by norm_num)
theorem B1830053 : Blo 1219427 1830053 := bbase (se 4 (by rfl) ⟨171567, by rfl⟩ : syracuseStep 1830053 = 343135) (by norm_num)
theorem B2059445 : Blo 1219427 2059445 := bbase (se 5 (by rfl) ⟨96536, by rfl⟩ : syracuseStep 2059445 = 193073) (by norm_num)
theorem B1830077 : Blo 1219427 1830077 := bbase (se 3 (by rfl) ⟨343139, by rfl⟩ : syracuseStep 1830077 = 686279) (by norm_num)
theorem B1543369 : Blo 1219427 1543369 := bbase (se 2 (by rfl) ⟨578763, by rfl⟩ : syracuseStep 1543369 = 1157527) (by norm_num)
theorem B1830101 : Blo 1219427 1830101 := bbase (se 7 (by rfl) ⟨21446, by rfl⟩ : syracuseStep 1830101 = 42893) (by norm_num)
theorem B6597845 : Blo 1219427 6597845 := bbase (se 7 (by rfl) ⟨77318, by rfl⟩ : syracuseStep 6597845 = 154637) (by norm_num)
theorem B1830125 : Blo 1219427 1830125 := bbase (se 3 (by rfl) ⟨343148, by rfl⟩ : syracuseStep 1830125 = 686297) (by norm_num)
theorem B4115717 : Blo 1219427 4115717 := bbase (se 4 (by rfl) ⟨385848, by rfl⟩ : syracuseStep 4115717 = 771697) (by norm_num)
theorem B1830149 : Blo 1219427 1830149 := bbase (se 4 (by rfl) ⟨171576, by rfl⟩ : syracuseStep 1830149 = 343153) (by norm_num)
theorem B1830173 : Blo 1219427 1830173 := bbase (se 3 (by rfl) ⟨343157, by rfl⟩ : syracuseStep 1830173 = 686315) (by norm_num)
theorem B1543465 : Blo 1219427 1543465 := bbase (se 2 (by rfl) ⟨578799, by rfl⟩ : syracuseStep 1543465 = 1157599) (by norm_num)
theorem B1830197 : Blo 1219427 1830197 := bbase (se 5 (by rfl) ⟨85790, by rfl⟩ : syracuseStep 1830197 = 171581) (by norm_num)
theorem B2059573 : Blo 1219427 2059573 := bbase (se 5 (by rfl) ⟨96542, by rfl⟩ : syracuseStep 2059573 = 193085) (by norm_num)
theorem B1830221 : Blo 1219427 1830221 := bbase (se 3 (by rfl) ⟨343166, by rfl⟩ : syracuseStep 1830221 = 686333) (by norm_num)
theorem B1830245 : Blo 1219427 1830245 := bbase (se 4 (by rfl) ⟨171585, by rfl⟩ : syracuseStep 1830245 = 343171) (by norm_num)
theorem B1830269 : Blo 1219427 1830269 := bbase (se 3 (by rfl) ⟨343175, by rfl⟩ : syracuseStep 1830269 = 686351) (by norm_num)
theorem B2059661 : Blo 1219427 2059661 := bbase (se 3 (by rfl) ⟨386186, by rfl⟩ : syracuseStep 2059661 = 772373) (by norm_num)
theorem B1830293 : Blo 1219427 1830293 := bbase (se 6 (by rfl) ⟨42897, by rfl⟩ : syracuseStep 1830293 = 85795) (by norm_num)
theorem B1830317 : Blo 1219427 1830317 := bbase (se 3 (by rfl) ⟨343184, by rfl⟩ : syracuseStep 1830317 = 686369) (by norm_num)
theorem B4632005 : Blo 1219427 4632005 := bbase (se 4 (by rfl) ⟨434250, by rfl⟩ : syracuseStep 4632005 = 868501) (by norm_num)
theorem B1830341 : Blo 1219427 1830341 := bbase (se 4 (by rfl) ⟨171594, by rfl⟩ : syracuseStep 1830341 = 343189) (by norm_num)
theorem B1543637 : Blo 1219427 1543637 := bbase (se 7 (by rfl) ⟨18089, by rfl⟩ : syracuseStep 1543637 = 36179) (by norm_num)
theorem B1830365 : Blo 1219427 1830365 := bbase (se 3 (by rfl) ⟨343193, by rfl⟩ : syracuseStep 1830365 = 686387) (by norm_num)
theorem B1830389 : Blo 1219427 1830389 := bbase (se 5 (by rfl) ⟨85799, by rfl⟩ : syracuseStep 1830389 = 171599) (by norm_num)
theorem B1543693 : Blo 1219427 1543693 := bbase (se 3 (by rfl) ⟨289442, by rfl⟩ : syracuseStep 1543693 = 578885) (by norm_num)
theorem B1830413 : Blo 1219427 1830413 := bbase (se 3 (by rfl) ⟨343202, by rfl⟩ : syracuseStep 1830413 = 686405) (by norm_num)
theorem B2059789 : Blo 1219427 2059789 := bbase (se 3 (by rfl) ⟨386210, by rfl⟩ : syracuseStep 2059789 = 772421) (by norm_num)
theorem B1830437 : Blo 1219427 1830437 := bbase (se 4 (by rfl) ⟨171603, by rfl⟩ : syracuseStep 1830437 = 343207) (by norm_num)
theorem B1830461 : Blo 1219427 1830461 := bbase (se 3 (by rfl) ⟨343211, by rfl⟩ : syracuseStep 1830461 = 686423) (by norm_num)
theorem B2199109 : Blo 1219427 2199109 := bbase (se 4 (by rfl) ⟨206166, by rfl⟩ : syracuseStep 2199109 = 412333) (by norm_num)
theorem B1830485 : Blo 1219427 1830485 := bbase (se 8 (by rfl) ⟨10725, by rfl⟩ : syracuseStep 1830485 = 21451) (by norm_num)
theorem B2059877 : Blo 1219427 2059877 := bbase (se 4 (by rfl) ⟨193113, by rfl⟩ : syracuseStep 2059877 = 386227) (by norm_num)
theorem B1543789 : Blo 1219427 1543789 := bbase (se 3 (by rfl) ⟨289460, by rfl⟩ : syracuseStep 1543789 = 578921) (by norm_num)
theorem B1830509 : Blo 1219427 1830509 := bbase (se 3 (by rfl) ⟨343220, by rfl⟩ : syracuseStep 1830509 = 686441) (by norm_num)
theorem B1830533 : Blo 1219427 1830533 := bbase (se 4 (by rfl) ⟨171612, by rfl⟩ : syracuseStep 1830533 = 343225) (by norm_num)
theorem B1830557 : Blo 1219427 1830557 := bbase (se 3 (by rfl) ⟨343229, by rfl⟩ : syracuseStep 1830557 = 686459) (by norm_num)
theorem B4116149 : Blo 1219427 4116149 := bbase (se 5 (by rfl) ⟨192944, by rfl⟩ : syracuseStep 4116149 = 385889) (by norm_num)
theorem B1855157 : Blo 1219427 1855157 := bbase (se 5 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 1855157 = 173921) (by norm_num)
theorem B1830581 : Blo 1219427 1830581 := bbase (se 5 (by rfl) ⟨85808, by rfl⟩ : syracuseStep 1830581 = 171617) (by norm_num)
theorem B1830605 : Blo 1219427 1830605 := bbase (se 3 (by rfl) ⟨343238, by rfl⟩ : syracuseStep 1830605 = 686477) (by norm_num)
theorem B1371865 : Blo 1219427 1371865 := bbase (se 2 (by rfl) ⟨514449, by rfl⟩ : syracuseStep 1371865 = 1028899) (by norm_num)
theorem B1830629 : Blo 1219427 1830629 := bbase (se 4 (by rfl) ⟨171621, by rfl⟩ : syracuseStep 1830629 = 343243) (by norm_num)
theorem B2060005 : Blo 1219427 2060005 := bbase (se 4 (by rfl) ⟨193125, by rfl⟩ : syracuseStep 2060005 = 386251) (by norm_num)
theorem B1371901 : Blo 1219427 1371901 := bbase (se 3 (by rfl) ⟨257231, by rfl⟩ : syracuseStep 1371901 = 514463) (by norm_num)
theorem B1953533 : Blo 1219427 1953533 := bbase (se 3 (by rfl) ⟨366287, by rfl⟩ : syracuseStep 1953533 = 732575) (by norm_num)
theorem B1830653 : Blo 1219427 1830653 := bbase (se 3 (by rfl) ⟨343247, by rfl⟩ : syracuseStep 1830653 = 686495) (by norm_num)
theorem B1568533 : Blo 1219427 1568533 := bbase (se 6 (by rfl) ⟨36762, by rfl⟩ : syracuseStep 1568533 = 73525) (by norm_num)
theorem B1830677 : Blo 1219427 1830677 := bbase (se 6 (by rfl) ⟨42906, by rfl⟩ : syracuseStep 1830677 = 85813) (by norm_num)
theorem B1543961 : Blo 1219427 1543961 := bbase (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) (by norm_num)
theorem B1371937 : Blo 1219427 1371937 := bbase (se 2 (by rfl) ⟨514476, by rfl⟩ : syracuseStep 1371937 = 1028953) (by norm_num)
theorem B1830701 : Blo 1219427 1830701 := bbase (se 3 (by rfl) ⟨343256, by rfl⟩ : syracuseStep 1830701 = 686513) (by norm_num)
theorem B2060093 : Blo 1219427 2060093 := bbase (se 3 (by rfl) ⟨386267, by rfl⟩ : syracuseStep 2060093 = 772535) (by norm_num)
theorem B1371973 : Blo 1219427 1371973 := bbase (se 4 (by rfl) ⟨128622, by rfl⟩ : syracuseStep 1371973 = 257245) (by norm_num)
theorem B1830725 : Blo 1219427 1830725 := bbase (se 4 (by rfl) ⟨171630, by rfl⟩ : syracuseStep 1830725 = 343261) (by norm_num)
theorem B1544017 : Blo 1219427 1544017 := bbase (se 2 (by rfl) ⟨579006, by rfl⟩ : syracuseStep 1544017 = 1158013) (by norm_num)
theorem B1830749 : Blo 1219427 1830749 := bbase (se 3 (by rfl) ⟨343265, by rfl⟩ : syracuseStep 1830749 = 686531) (by norm_num)
theorem B1372009 : Blo 1219427 1372009 := bbase (se 2 (by rfl) ⟨514503, by rfl⟩ : syracuseStep 1372009 = 1029007) (by norm_num)
theorem B1830773 : Blo 1219427 1830773 := bbase (se 5 (by rfl) ⟨85817, by rfl⟩ : syracuseStep 1830773 = 171635) (by norm_num)
theorem B1372045 : Blo 1219427 1372045 := bbase (se 3 (by rfl) ⟨257258, by rfl⟩ : syracuseStep 1372045 = 514517) (by norm_num)
theorem B1830797 : Blo 1219427 1830797 := bbase (se 3 (by rfl) ⟨343274, by rfl⟩ : syracuseStep 1830797 = 686549) (by norm_num)
theorem B9891733 : Blo 1219427 9891733 := bbase (se 6 (by rfl) ⟨231837, by rfl⟩ : syracuseStep 9891733 = 463675) (by norm_num)
theorem B1830821 : Blo 1219427 1830821 := bbase (se 4 (by rfl) ⟨171639, by rfl⟩ : syracuseStep 1830821 = 343279) (by norm_num)
theorem B1372081 : Blo 1219427 1372081 := bbase (se 2 (by rfl) ⟨514530, by rfl⟩ : syracuseStep 1372081 = 1029061) (by norm_num)
theorem B1544113 : Blo 1219427 1544113 := bbase (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) (by norm_num)
theorem B1830845 : Blo 1219427 1830845 := bbase (se 3 (by rfl) ⟨343283, by rfl⟩ : syracuseStep 1830845 = 686567) (by norm_num)
theorem B2060221 : Blo 1219427 2060221 := bbase (se 3 (by rfl) ⟨386291, by rfl⟩ : syracuseStep 2060221 = 772583) (by norm_num)
theorem B1372117 : Blo 1219427 1372117 := bbase (se 7 (by rfl) ⟨16079, by rfl⟩ : syracuseStep 1372117 = 32159) (by norm_num)
theorem B1830869 : Blo 1219427 1830869 := bbase (se 7 (by rfl) ⟨21455, by rfl⟩ : syracuseStep 1830869 = 42911) (by norm_num)
theorem B1830893 : Blo 1219427 1830893 := bbase (se 3 (by rfl) ⟨343292, by rfl⟩ : syracuseStep 1830893 = 686585) (by norm_num)
theorem B1372153 : Blo 1219427 1372153 := bbase (se 2 (by rfl) ⟨514557, by rfl⟩ : syracuseStep 1372153 = 1029115) (by norm_num)
theorem B1830917 : Blo 1219427 1830917 := bbase (se 4 (by rfl) ⟨171648, by rfl⟩ : syracuseStep 1830917 = 343297) (by norm_num)
theorem B2060309 : Blo 1219427 2060309 := bbase (se 6 (by rfl) ⟨48288, by rfl⟩ : syracuseStep 2060309 = 96577) (by norm_num)
theorem B1372189 : Blo 1219427 1372189 := bbase (se 3 (by rfl) ⟨257285, by rfl⟩ : syracuseStep 1372189 = 514571) (by norm_num)
theorem B1830941 : Blo 1219427 1830941 := bbase (se 3 (by rfl) ⟨343301, by rfl⟩ : syracuseStep 1830941 = 686603) (by norm_num)
theorem B1830965 : Blo 1219427 1830965 := bbase (se 5 (by rfl) ⟨85826, by rfl⟩ : syracuseStep 1830965 = 171653) (by norm_num)
theorem B1372225 : Blo 1219427 1372225 := bbase (se 2 (by rfl) ⟨514584, by rfl⟩ : syracuseStep 1372225 = 1029169) (by norm_num)
theorem B1830989 : Blo 1219427 1830989 := bbase (se 3 (by rfl) ⟨343310, by rfl⟩ : syracuseStep 1830989 = 686621) (by norm_num)
theorem B3297365 : Blo 1219427 3297365 := bbase (se 8 (by rfl) ⟨19320, by rfl⟩ : syracuseStep 3297365 = 38641) (by norm_num)
theorem B1544285 : Blo 1219427 1544285 := bbase (se 3 (by rfl) ⟨289553, by rfl⟩ : syracuseStep 1544285 = 579107) (by norm_num)
theorem B4116581 : Blo 1219427 4116581 := bbase (se 4 (by rfl) ⟨385929, by rfl⟩ : syracuseStep 4116581 = 771859) (by norm_num)
theorem B1372261 : Blo 1219427 1372261 := bbase (se 4 (by rfl) ⟨128649, by rfl⟩ : syracuseStep 1372261 = 257299) (by norm_num)
theorem B1831013 : Blo 1219427 1831013 := bbase (se 4 (by rfl) ⟨171657, by rfl⟩ : syracuseStep 1831013 = 343315) (by norm_num)
theorem B1831037 : Blo 1219427 1831037 := bbase (se 3 (by rfl) ⟨343319, by rfl⟩ : syracuseStep 1831037 = 686639) (by norm_num)
theorem B1372297 : Blo 1219427 1372297 := bbase (se 2 (by rfl) ⟨514611, by rfl⟩ : syracuseStep 1372297 = 1029223) (by norm_num)
theorem B1544341 : Blo 1219427 1544341 := bbase (se 6 (by rfl) ⟨36195, by rfl⟩ : syracuseStep 1544341 = 72391) (by norm_num)
theorem B1831061 : Blo 1219427 1831061 := bbase (se 6 (by rfl) ⟨42915, by rfl⟩ : syracuseStep 1831061 = 85831) (by norm_num)
theorem B14094485 : Blo 1219427 14094485 := bbase (se 6 (by rfl) ⟨330339, by rfl⟩ : syracuseStep 14094485 = 660679) (by norm_num)
theorem B1372333 : Blo 1219427 1372333 := bbase (se 3 (by rfl) ⟨257312, by rfl⟩ : syracuseStep 1372333 = 514625) (by norm_num)
theorem B1855661 : Blo 1219427 1855661 := bbase (se 3 (by rfl) ⟨347936, by rfl⟩ : syracuseStep 1855661 = 695873) (by norm_num)
theorem B1831085 : Blo 1219427 1831085 := bbase (se 3 (by rfl) ⟨343328, by rfl⟩ : syracuseStep 1831085 = 686657) (by norm_num)
theorem B1831109 : Blo 1219427 1831109 := bbase (se 4 (by rfl) ⟨171666, by rfl⟩ : syracuseStep 1831109 = 343333) (by norm_num)
theorem B1372369 : Blo 1219427 1372369 := bbase (se 2 (by rfl) ⟨514638, by rfl⟩ : syracuseStep 1372369 = 1029277) (by norm_num)
theorem B1831133 : Blo 1219427 1831133 := bbase (se 3 (by rfl) ⟨343337, by rfl⟩ : syracuseStep 1831133 = 686675) (by norm_num)
theorem B1372405 : Blo 1219427 1372405 := bbase (se 5 (by rfl) ⟨64331, by rfl⟩ : syracuseStep 1372405 = 128663) (by norm_num)
theorem B1544437 : Blo 1219427 1544437 := bbase (se 5 (by rfl) ⟨72395, by rfl⟩ : syracuseStep 1544437 = 144791) (by norm_num)
theorem B6598901 : Blo 1219427 6598901 := bbase (se 5 (by rfl) ⟨309323, by rfl⟩ : syracuseStep 6598901 = 618647) (by norm_num)
theorem B1831157 : Blo 1219427 1831157 := bbase (se 5 (by rfl) ⟨85835, by rfl⟩ : syracuseStep 1831157 = 171671) (by norm_num)
theorem B1831181 : Blo 1219427 1831181 := bbase (se 3 (by rfl) ⟨343346, by rfl⟩ : syracuseStep 1831181 = 686693) (by norm_num)
theorem B1372441 : Blo 1219427 1372441 := bbase (se 2 (by rfl) ⟨514665, by rfl⟩ : syracuseStep 1372441 = 1029331) (by norm_num)
theorem B1831205 : Blo 1219427 1831205 := bbase (se 4 (by rfl) ⟨171675, by rfl⟩ : syracuseStep 1831205 = 343351) (by norm_num)
theorem B1372477 : Blo 1219427 1372477 := bbase (se 3 (by rfl) ⟨257339, by rfl⟩ : syracuseStep 1372477 = 514679) (by norm_num)
theorem B1831229 : Blo 1219427 1831229 := bbase (se 3 (by rfl) ⟨343355, by rfl⟩ : syracuseStep 1831229 = 686711) (by norm_num)
theorem B5566805 : Blo 1219427 5566805 := bbase (se 10 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 5566805 = 16309) (by norm_num)
theorem B1831253 : Blo 1219427 1831253 := bbase (se 10 (by rfl) ⟨2682, by rfl⟩ : syracuseStep 1831253 = 5365) (by norm_num)
theorem B1372513 : Blo 1219427 1372513 := bbase (se 2 (by rfl) ⟨514692, by rfl⟩ : syracuseStep 1372513 = 1029385) (by norm_num)
theorem B1831277 : Blo 1219427 1831277 := bbase (se 3 (by rfl) ⟨343364, by rfl⟩ : syracuseStep 1831277 = 686729) (by norm_num)
theorem B1372549 : Blo 1219427 1372549 := bbase (se 4 (by rfl) ⟨128676, by rfl⟩ : syracuseStep 1372549 = 257353) (by norm_num)
theorem B1831301 : Blo 1219427 1831301 := bbase (se 4 (by rfl) ⟨171684, by rfl⟩ : syracuseStep 1831301 = 343369) (by norm_num)
theorem B1831325 : Blo 1219427 1831325 := bbase (se 3 (by rfl) ⟨343373, by rfl⟩ : syracuseStep 1831325 = 686747) (by norm_num)
theorem B1544609 : Blo 1219427 1544609 := bbase (se 2 (by rfl) ⟨579228, by rfl⟩ : syracuseStep 1544609 = 1158457) (by norm_num)
theorem B1372585 : Blo 1219427 1372585 := bbase (se 2 (by rfl) ⟨514719, by rfl⟩ : syracuseStep 1372585 = 1029439) (by norm_num)
theorem B1831349 : Blo 1219427 1831349 := bbase (se 5 (by rfl) ⟨85844, by rfl⟩ : syracuseStep 1831349 = 171689) (by norm_num)
theorem B1372621 : Blo 1219427 1372621 := bbase (se 3 (by rfl) ⟨257366, by rfl⟩ : syracuseStep 1372621 = 514733) (by norm_num)
theorem B1831373 : Blo 1219427 1831373 := bbase (se 3 (by rfl) ⟨343382, by rfl⟩ : syracuseStep 1831373 = 686765) (by norm_num)
theorem B1544665 : Blo 1219427 1544665 := bbase (se 2 (by rfl) ⟨579249, by rfl⟩ : syracuseStep 1544665 = 1158499) (by norm_num)
theorem B1372657 : Blo 1219427 1372657 := bbase (se 2 (by rfl) ⟨514746, by rfl⟩ : syracuseStep 1372657 = 1029493) (by norm_num)
theorem B4117013 : Blo 1219427 4117013 := bbase (se 6 (by rfl) ⟨96492, by rfl⟩ : syracuseStep 4117013 = 192985) (by norm_num)
theorem B1372693 : Blo 1219427 1372693 := bbase (se 6 (by rfl) ⟨32172, by rfl⟩ : syracuseStep 1372693 = 64345) (by norm_num)
theorem B1372729 : Blo 1219427 1372729 := bbase (se 2 (by rfl) ⟨514773, by rfl⟩ : syracuseStep 1372729 = 1029547) (by norm_num)
theorem B1544761 : Blo 1219427 1544761 := bbase (se 2 (by rfl) ⟨579285, by rfl⟩ : syracuseStep 1544761 = 1158571) (by norm_num)
theorem B1372765 : Blo 1219427 1372765 := bbase (se 3 (by rfl) ⟨257393, by rfl⟩ : syracuseStep 1372765 = 514787) (by norm_num)
theorem B1372801 : Blo 1219427 1372801 := bbase (se 2 (by rfl) ⟨514800, by rfl⟩ : syracuseStep 1372801 = 1029601) (by norm_num)
theorem B1372837 : Blo 1219427 1372837 := bbase (se 4 (by rfl) ⟨128703, by rfl⟩ : syracuseStep 1372837 = 257407) (by norm_num)
theorem B1372873 : Blo 1219427 1372873 := bbase (se 2 (by rfl) ⟨514827, by rfl⟩ : syracuseStep 1372873 = 1029655) (by norm_num)
theorem B1954525 : Blo 1219427 1954525 := bbase (se 3 (by rfl) ⟨366473, by rfl⟩ : syracuseStep 1954525 = 732947) (by norm_num)
theorem B1544933 : Blo 1219427 1544933 := bbase (se 4 (by rfl) ⟨144837, by rfl⟩ : syracuseStep 1544933 = 289675) (by norm_num)
theorem B1372909 : Blo 1219427 1372909 := bbase (se 3 (by rfl) ⟨257420, by rfl⟩ : syracuseStep 1372909 = 514841) (by norm_num)
theorem B1372945 : Blo 1219427 1372945 := bbase (se 2 (by rfl) ⟨514854, by rfl⟩ : syracuseStep 1372945 = 1029709) (by norm_num)
theorem B1544989 : Blo 1219427 1544989 := bbase (se 3 (by rfl) ⟨289685, by rfl⟩ : syracuseStep 1544989 = 579371) (by norm_num)
theorem B1372981 : Blo 1219427 1372981 := bbase (se 5 (by rfl) ⟨64358, by rfl⟩ : syracuseStep 1372981 = 128717) (by norm_num)
theorem B1373017 : Blo 1219427 1373017 := bbase (se 2 (by rfl) ⟨514881, by rfl⟩ : syracuseStep 1373017 = 1029763) (by norm_num)
theorem B1373053 : Blo 1219427 1373053 := bbase (se 3 (by rfl) ⟨257447, by rfl⟩ : syracuseStep 1373053 = 514895) (by norm_num)
theorem B1545085 : Blo 1219427 1545085 := bbase (se 3 (by rfl) ⟨289703, by rfl⟩ : syracuseStep 1545085 = 579407) (by norm_num)
theorem B1373089 : Blo 1219427 1373089 := bbase (se 2 (by rfl) ⟨514908, by rfl⟩ : syracuseStep 1373089 = 1029817) (by norm_num)
theorem B4117445 : Blo 1219427 4117445 := bbase (se 4 (by rfl) ⟨386010, by rfl⟩ : syracuseStep 4117445 = 772021) (by norm_num)
theorem B1373125 : Blo 1219427 1373125 := bbase (se 4 (by rfl) ⟨128730, by rfl⟩ : syracuseStep 1373125 = 257461) (by norm_num)
theorem B2315213 : Blo 1219427 2315213 := bbase (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) (by norm_num)
theorem B1373161 : Blo 1219427 1373161 := bbase (se 2 (by rfl) ⟨514935, by rfl⟩ : syracuseStep 1373161 = 1029871) (by norm_num)
theorem B1586161 : Blo 1219427 1586161 := bbase (se 2 (by rfl) ⟨594810, by rfl⟩ : syracuseStep 1586161 = 1189621) (by norm_num)
theorem B4396037 : Blo 1219427 4396037 := bbase (se 4 (by rfl) ⟨412128, by rfl⟩ : syracuseStep 4396037 = 824257) (by norm_num)
theorem B1373197 : Blo 1219427 1373197 := bbase (se 3 (by rfl) ⟨257474, by rfl⟩ : syracuseStep 1373197 = 514949) (by norm_num)
theorem B3298325 : Blo 1219427 3298325 := bbase (se 6 (by rfl) ⟨77304, by rfl⟩ : syracuseStep 3298325 = 154609) (by norm_num)
theorem B1373233 : Blo 1219427 1373233 := bbase (se 2 (by rfl) ⟨514962, by rfl⟩ : syracuseStep 1373233 = 1029925) (by norm_num)
theorem B1373269 : Blo 1219427 1373269 := bbase (se 8 (by rfl) ⟨8046, by rfl⟩ : syracuseStep 1373269 = 16093) (by norm_num)
theorem B2782325 : Blo 1219427 2782325 := bbase (se 5 (by rfl) ⟨130421, by rfl⟩ : syracuseStep 2782325 = 260843) (by norm_num)
theorem B1373305 : Blo 1219427 1373305 := bbase (se 2 (by rfl) ⟨514989, by rfl⟩ : syracuseStep 1373305 = 1029979) (by norm_num)
theorem B1954973 : Blo 1219427 1954973 := bbase (se 3 (by rfl) ⟨366557, by rfl⟩ : syracuseStep 1954973 = 733115) (by norm_num)
theorem B1373341 : Blo 1219427 1373341 := bbase (se 3 (by rfl) ⟨257501, by rfl⟩ : syracuseStep 1373341 = 515003) (by norm_num)
theorem B1373377 : Blo 1219427 1373377 := bbase (se 2 (by rfl) ⟨515016, by rfl⟩ : syracuseStep 1373377 = 1030033) (by norm_num)
theorem B1742029 : Blo 1219427 1742029 := bbase (se 3 (by rfl) ⟨326630, by rfl⟩ : syracuseStep 1742029 = 653261) (by norm_num)
theorem B5862613 : Blo 1219427 5862613 := bbase (se 7 (by rfl) ⟨68702, by rfl⟩ : syracuseStep 5862613 = 137405) (by norm_num)
theorem B1373413 : Blo 1219427 1373413 := bbase (se 4 (by rfl) ⟨128757, by rfl⟩ : syracuseStep 1373413 = 257515) (by norm_num)
theorem B4945157 : Blo 1219427 4945157 := bbase (se 4 (by rfl) ⟨463608, by rfl⟩ : syracuseStep 4945157 = 927217) (by norm_num)
theorem B1373449 : Blo 1219427 1373449 := bbase (se 2 (by rfl) ⟨515043, by rfl⟩ : syracuseStep 1373449 = 1030087) (by norm_num)
theorem B1373485 : Blo 1219427 1373485 := bbase (se 3 (by rfl) ⟨257528, by rfl⟩ : syracuseStep 1373485 = 515057) (by norm_num)
theorem B1373521 : Blo 1219427 1373521 := bbase (se 2 (by rfl) ⟨515070, by rfl⟩ : syracuseStep 1373521 = 1030141) (by norm_num)
theorem B1955173 : Blo 1219427 1955173 := bbase (se 4 (by rfl) ⟨183297, by rfl⟩ : syracuseStep 1955173 = 366595) (by norm_num)
theorem B4117877 : Blo 1219427 4117877 := bbase (se 5 (by rfl) ⟨193025, by rfl⟩ : syracuseStep 4117877 = 386051) (by norm_num)
theorem B1357249 : Blo 1219427 1357249 := bbase (se 2 (by rfl) ⟨508968, by rfl⟩ : syracuseStep 1357249 = 1017937) (by norm_num)
theorem B4945349 : Blo 1219427 4945349 := bbase (se 4 (by rfl) ⟨463626, by rfl⟩ : syracuseStep 4945349 = 927253) (by norm_num)
theorem B4634117 : Blo 1219427 4634117 := bbase (se 4 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 4634117 = 868897) (by norm_num)
theorem B2930269 : Blo 1219427 2930269 := bbase (se 3 (by rfl) ⟨549425, by rfl⟩ : syracuseStep 2930269 = 1098851) (by norm_num)
theorem B1955429 : Blo 1219427 1955429 := bbase (se 4 (by rfl) ⟨183321, by rfl⟩ : syracuseStep 1955429 = 366643) (by norm_num)
theorem B8795765 : Blo 1219427 8795765 := bbase (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) (by norm_num)
theorem B2315965 : Blo 1219427 2315965 := bbase (se 3 (by rfl) ⟨434243, by rfl⟩ : syracuseStep 2315965 = 868487) (by norm_num)
theorem B4118309 : Blo 1219427 4118309 := bbase (se 4 (by rfl) ⟨386091, by rfl⟩ : syracuseStep 4118309 = 772183) (by norm_num)
theorem B4634405 : Blo 1219427 4634405 := bbase (se 4 (by rfl) ⟨434475, by rfl⟩ : syracuseStep 4634405 = 868951) (by norm_num)
theorem B2316109 : Blo 1219427 2316109 := bbase (se 3 (by rfl) ⟨434270, by rfl⟩ : syracuseStep 2316109 = 868541) (by norm_num)
theorem B3708757 : Blo 1219427 3708757 := bbase (se 9 (by rfl) ⟨10865, by rfl⟩ : syracuseStep 3708757 = 21731) (by norm_num)
theorem B15644501 : Blo 1219427 15644501 := bbase (se 9 (by rfl) ⟨45833, by rfl⟩ : syracuseStep 15644501 = 91667) (by norm_num)
theorem B4396949 : Blo 1219427 4396949 := bbase (se 6 (by rfl) ⟨103053, by rfl⟩ : syracuseStep 4396949 = 206107) (by norm_num)
theorem B2348957 : Blo 1219427 2348957 := bbase (se 3 (by rfl) ⟨440429, by rfl⟩ : syracuseStep 2348957 = 880859) (by norm_num)
theorem B6174629 : Blo 1219427 6174629 := bbase (se 4 (by rfl) ⟨578871, by rfl⟩ : syracuseStep 6174629 = 1157743) (by norm_num)
theorem B2349005 : Blo 1219427 2349005 := bbase (se 3 (by rfl) ⟨440438, by rfl⟩ : syracuseStep 2349005 = 880877) (by norm_num)
theorem B2316269 : Blo 1219427 2316269 := bbase (se 3 (by rfl) ⟨434300, by rfl⟩ : syracuseStep 2316269 = 868601) (by norm_num)
theorem B2316413 : Blo 1219427 2316413 := bbase (se 3 (by rfl) ⟨434327, by rfl⟩ : syracuseStep 2316413 = 868655) (by norm_num)
theorem B4118741 : Blo 1219427 4118741 := bbase (se 7 (by rfl) ⟨48266, by rfl⟩ : syracuseStep 4118741 = 96533) (by norm_num)
theorem B2783621 : Blo 1219427 2783621 := bbase (se 4 (by rfl) ⟨260964, by rfl⟩ : syracuseStep 2783621 = 521929) (by norm_num)
theorem B2316701 : Blo 1219427 2316701 := bbase (se 3 (by rfl) ⟨434381, by rfl⟩ : syracuseStep 2316701 = 868763) (by norm_num)
theorem B2783693 : Blo 1219427 2783693 := bbase (se 3 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 2783693 = 1043885) (by norm_num)
theorem B3086869 : Blo 1219427 3086869 := bbase (se 6 (by rfl) ⟨72348, by rfl⟩ : syracuseStep 3086869 = 144697) (by norm_num)
theorem B4946453 : Blo 1219427 4946453 := bbase (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) (by norm_num)
theorem B2316853 : Blo 1219427 2316853 := bbase (se 5 (by rfl) ⟨108602, by rfl⟩ : syracuseStep 2316853 = 217205) (by norm_num)
theorem B6945365 : Blo 1219427 6945365 := bbase (se 8 (by rfl) ⟨40695, by rfl⟩ : syracuseStep 6945365 = 81391) (by norm_num)
theorem B3086981 : Blo 1219427 3086981 := bbase (se 4 (by rfl) ⟨289404, by rfl⟩ : syracuseStep 3086981 = 578809) (by norm_num)
theorem B4119173 : Blo 1219427 4119173 := bbase (se 4 (by rfl) ⟨386172, by rfl⟩ : syracuseStep 4119173 = 772345) (by norm_num)
theorem B2931461 : Blo 1219427 2931461 := bbase (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) (by norm_num)
theorem B3087173 : Blo 1219427 3087173 := bbase (se 4 (by rfl) ⟨289422, by rfl⟩ : syracuseStep 3087173 = 578845) (by norm_num)
theorem B2317157 : Blo 1219427 2317157 := bbase (se 4 (by rfl) ⟨217233, by rfl⟩ : syracuseStep 2317157 = 434467) (by norm_num)
theorem B2931653 : Blo 1219427 2931653 := bbase (se 4 (by rfl) ⟨274842, by rfl⟩ : syracuseStep 2931653 = 549685) (by norm_num)
theorem B4635589 : Blo 1219427 4635589 := bbase (se 4 (by rfl) ⟨434586, by rfl⟩ : syracuseStep 4635589 = 869173) (by norm_num)
theorem B1391573 : Blo 1219427 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B4119605 : Blo 1219427 4119605 := bbase (se 5 (by rfl) ⟨193106, by rfl⟩ : syracuseStep 4119605 = 386213) (by norm_num)
theorem B2088037 : Blo 1219427 2088037 := bbase (se 4 (by rfl) ⟨195753, by rfl⟩ : syracuseStep 2088037 = 391507) (by norm_num)
theorem B1465457 : Blo 1219427 1465457 := bbase (se 2 (by rfl) ⟨549546, by rfl⟩ : syracuseStep 1465457 = 1099093) (by norm_num)
theorem B3013757 : Blo 1219427 3013757 := bbase (se 3 (by rfl) ⟨565079, by rfl⟩ : syracuseStep 3013757 = 1130159) (by norm_num)
theorem B6347909 : Blo 1219427 6347909 := bbase (se 4 (by rfl) ⟨595116, by rfl⟩ : syracuseStep 6347909 = 1190233) (by norm_num)
theorem B3087517 : Blo 1219427 3087517 := bbase (se 3 (by rfl) ⟨578909, by rfl⟩ : syracuseStep 3087517 = 1157819) (by norm_num)
theorem B6175925 : Blo 1219427 6175925 := bbase (se 5 (by rfl) ⟨289496, by rfl⟩ : syracuseStep 6175925 = 578993) (by norm_num)
theorem B7814357 : Blo 1219427 7814357 := bbase (se 7 (by rfl) ⟨91574, by rfl⟩ : syracuseStep 7814357 = 183149) (by norm_num)
theorem B3087629 : Blo 1219427 3087629 := bbase (se 3 (by rfl) ⟨578930, by rfl⟩ : syracuseStep 3087629 = 1157861) (by norm_num)
theorem B1236353 : Blo 1219427 1236353 := bbase (se 2 (by rfl) ⟨463632, by rfl⟩ : syracuseStep 1236353 = 927265) (by norm_num)
theorem B2743757 : Blo 1219427 2743757 := bbase (se 3 (by rfl) ⟨514454, by rfl⟩ : syracuseStep 2743757 = 1028909) (by norm_num)
theorem B3087821 : Blo 1219427 3087821 := bbase (se 3 (by rfl) ⟨578966, by rfl⟩ : syracuseStep 3087821 = 1157933) (by norm_num)
theorem B4120037 : Blo 1219427 4120037 := bbase (se 4 (by rfl) ⟨386253, by rfl⟩ : syracuseStep 4120037 = 772507) (by norm_num)
theorem B2473453 : Blo 1219427 2473453 := bbase (se 3 (by rfl) ⟨463772, by rfl⟩ : syracuseStep 2473453 = 927545) (by norm_num)
theorem B11722229 : Blo 1219427 11722229 := bbase (se 5 (by rfl) ⟨549479, by rfl⟩ : syracuseStep 11722229 = 1098959) (by norm_num)
theorem B2743829 : Blo 1219427 2743829 := bbase (se 6 (by rfl) ⟨64308, by rfl⟩ : syracuseStep 2743829 = 128617) (by norm_num)
theorem B2743901 : Blo 1219427 2743901 := bbase (se 3 (by rfl) ⟨514481, by rfl⟩ : syracuseStep 2743901 = 1028963) (by norm_num)
theorem B4947605 : Blo 1219427 4947605 := bbase (se 6 (by rfl) ⟨115959, by rfl⟩ : syracuseStep 4947605 = 231919) (by norm_num)
theorem B2743973 : Blo 1219427 2743973 := bbase (se 4 (by rfl) ⟨257247, by rfl⟩ : syracuseStep 2743973 = 514495) (by norm_num)
theorem B3342005 : Blo 1219427 3342005 := bbase (se 5 (by rfl) ⟨156656, by rfl⟩ : syracuseStep 3342005 = 313313) (by norm_num)
theorem B1302205 : Blo 1219427 1302205 := bbase (se 3 (by rfl) ⟨244163, by rfl⟩ : syracuseStep 1302205 = 488327) (by norm_num)
theorem B3473093 : Blo 1219427 3473093 := bbase (se 4 (by rfl) ⟨325602, by rfl⟩ : syracuseStep 3473093 = 651205) (by norm_num)
theorem B1466057 : Blo 1219427 1466057 := bbase (se 2 (by rfl) ⟨549771, by rfl⟩ : syracuseStep 1466057 = 1099543) (by norm_num)
theorem B5209829 : Blo 1219427 5209829 := bbase (se 4 (by rfl) ⟨488421, by rfl⟩ : syracuseStep 5209829 = 976843) (by norm_num)
theorem B2744045 : Blo 1219427 2744045 := bbase (se 3 (by rfl) ⟨514508, by rfl⟩ : syracuseStep 2744045 = 1029017) (by norm_num)
theorem B1302265 : Blo 1219427 1302265 := bbase (se 2 (by rfl) ⟨488349, by rfl⟩ : syracuseStep 1302265 = 976699) (by norm_num)
theorem B2678525 : Blo 1219427 2678525 := bbase (se 3 (by rfl) ⟨502223, by rfl⟩ : syracuseStep 2678525 = 1004447) (by norm_num)
theorem B3088165 : Blo 1219427 3088165 := bbase (se 4 (by rfl) ⟨289515, by rfl⟩ : syracuseStep 3088165 = 579031) (by norm_num)
theorem B4947749 : Blo 1219427 4947749 := bbase (se 4 (by rfl) ⟨463851, by rfl⟩ : syracuseStep 4947749 = 927703) (by norm_num)
theorem B2744117 : Blo 1219427 2744117 := bbase (se 5 (by rfl) ⟨128630, by rfl⟩ : syracuseStep 2744117 = 257261) (by norm_num)
theorem B11280181 : Blo 1219427 11280181 := bbase (se 5 (by rfl) ⟨528758, by rfl⟩ : syracuseStep 11280181 = 1057517) (by norm_num)
theorem B2744189 : Blo 1219427 2744189 := bbase (se 3 (by rfl) ⟨514535, by rfl⟩ : syracuseStep 2744189 = 1029071) (by norm_num)
theorem B1736581 : Blo 1219427 1736581 := bbase (se 4 (by rfl) ⟨162804, by rfl⟩ : syracuseStep 1736581 = 325609) (by norm_num)
theorem B3088277 : Blo 1219427 3088277 := bbase (se 6 (by rfl) ⟨72381, by rfl⟩ : syracuseStep 3088277 = 144763) (by norm_num)
theorem B4120469 : Blo 1219427 4120469 := bbase (se 6 (by rfl) ⟨96573, by rfl⟩ : syracuseStep 4120469 = 193147) (by norm_num)
theorem B2744261 : Blo 1219427 2744261 := bbase (se 4 (by rfl) ⟨257274, by rfl⟩ : syracuseStep 2744261 = 514549) (by norm_num)
theorem B1466365 : Blo 1219427 1466365 := bbase (se 3 (by rfl) ⟨274943, by rfl⟩ : syracuseStep 1466365 = 549887) (by norm_num)
theorem B1220611 : Blo 1219427 1220611 := bstep (se 1 (by rfl) ⟨915458, by rfl⟩ : syracuseStep 1220611 = 1830917) B1830917
theorem B11722765 : Blo 1219427 11722765 := bstep (se 3 (by rfl) ⟨2198018, by rfl⟩ : syracuseStep 11722765 = 4396037) B4396037
theorem B1220627 : Blo 1219427 1220627 := bstep (se 1 (by rfl) ⟨915470, by rfl⟩ : syracuseStep 1220627 = 1830941) B1830941
theorem B1220643 : Blo 1219427 1220643 := bstep (se 1 (by rfl) ⟨915482, by rfl⟩ : syracuseStep 1220643 = 1830965) B1830965
theorem B2744369 : Blo 1219427 2744369 := bstep (se 2 (by rfl) ⟨1029138, by rfl⟩ : syracuseStep 2744369 = 2058277) B2058277
theorem B1220659 : Blo 1219427 1220659 := bstep (se 1 (by rfl) ⟨915494, by rfl⟩ : syracuseStep 1220659 = 1830989) B1830989
theorem B2744387 : Blo 1219427 2744387 := bstep (se 1 (by rfl) ⟨2058290, by rfl⟩ : syracuseStep 2744387 = 4116581) B4116581
theorem B1220675 : Blo 1219427 1220675 := bstep (se 1 (by rfl) ⟨915506, by rfl⟩ : syracuseStep 1220675 = 1831013) B1831013
theorem B1220691 : Blo 1219427 1220691 := bstep (se 1 (by rfl) ⟨915518, by rfl⟩ : syracuseStep 1220691 = 1831037) B1831037
theorem B1220707 : Blo 1219427 1220707 := bstep (se 1 (by rfl) ⟨915530, by rfl⟩ : syracuseStep 1220707 = 1831061) B1831061
theorem B9396323 : Blo 1219427 9396323 := bstep (se 1 (by rfl) ⟨7047242, by rfl⟩ : syracuseStep 9396323 = 14094485) B14094485
theorem B1220723 : Blo 1219427 1220723 := bstep (se 1 (by rfl) ⟨915542, by rfl⟩ : syracuseStep 1220723 = 1831085) B1831085
theorem B1220739 : Blo 1219427 1220739 := bstep (se 1 (by rfl) ⟨915554, by rfl⟩ : syracuseStep 1220739 = 1831109) B1831109
theorem B3473549 : Blo 1219427 3473549 := bstep (se 3 (by rfl) ⟨651290, by rfl⟩ : syracuseStep 3473549 = 1302581) B1302581
theorem B1220755 : Blo 1219427 1220755 := bstep (se 1 (by rfl) ⟨915566, by rfl⟩ : syracuseStep 1220755 = 1831133) B1831133
theorem B4399267 : Blo 1219427 4399267 := bstep (se 1 (by rfl) ⟨3299450, by rfl⟩ : syracuseStep 4399267 = 6598901) B6598901
theorem B1220771 : Blo 1219427 1220771 := bstep (se 1 (by rfl) ⟨915578, by rfl⟩ : syracuseStep 1220771 = 1831157) B1831157
theorem B1220787 : Blo 1219427 1220787 := bstep (se 1 (by rfl) ⟨915590, by rfl⟩ : syracuseStep 1220787 = 1831181) B1831181
theorem B1220803 : Blo 1219427 1220803 := bstep (se 1 (by rfl) ⟨915602, by rfl⟩ : syracuseStep 1220803 = 1831205) B1831205
theorem B3473617 : Blo 1219427 3473617 := bstep (se 2 (by rfl) ⟨1302606, by rfl⟩ : syracuseStep 3473617 = 2605213) B2605213
theorem B1220819 : Blo 1219427 1220819 := bstep (se 1 (by rfl) ⟨915614, by rfl⟩ : syracuseStep 1220819 = 1831229) B1831229
theorem B3711203 : Blo 1219427 3711203 := bstep (se 1 (by rfl) ⟨2783402, by rfl⟩ : syracuseStep 3711203 = 5566805) B5566805
theorem B1220835 : Blo 1219427 1220835 := bstep (se 1 (by rfl) ⟨915626, by rfl⟩ : syracuseStep 1220835 = 1831253) B1831253
theorem B1220851 : Blo 1219427 1220851 := bstep (se 1 (by rfl) ⟨915638, by rfl⟩ : syracuseStep 1220851 = 1831277) B1831277
theorem B1220867 : Blo 1219427 1220867 := bstep (se 1 (by rfl) ⟨915650, by rfl⟩ : syracuseStep 1220867 = 1831301) B1831301
theorem B1220883 : Blo 1219427 1220883 := bstep (se 1 (by rfl) ⟨915662, by rfl⟩ : syracuseStep 1220883 = 1831325) B1831325
theorem B6177059 : Blo 1219427 6177059 := bstep (se 1 (by rfl) ⟨4632794, by rfl⟩ : syracuseStep 6177059 = 9265589) B9265589
theorem B1220899 : Blo 1219427 1220899 := bstep (se 1 (by rfl) ⟨915674, by rfl⟩ : syracuseStep 1220899 = 1831349) B1831349
theorem B3907885 : Blo 1219427 3907885 := bstep (se 3 (by rfl) ⟨732728, by rfl⟩ : syracuseStep 3907885 = 1465457) B1465457
theorem B1220915 : Blo 1219427 1220915 := bstep (se 1 (by rfl) ⟨915686, by rfl⟩ : syracuseStep 1220915 = 1831373) B1831373
theorem B2744657 : Blo 1219427 2744657 := bstep (se 2 (by rfl) ⟨1029246, by rfl⟩ : syracuseStep 2744657 = 2058493) B2058493
theorem B2744675 : Blo 1219427 2744675 := bstep (se 1 (by rfl) ⟨2058506, by rfl⟩ : syracuseStep 2744675 = 4117013) B4117013
theorem B1737139 : Blo 1219427 1737139 := bstep (se 1 (by rfl) ⟨1302854, by rfl⟩ : syracuseStep 1737139 = 2605709) B2605709
theorem B3473891 : Blo 1219427 3473891 := bstep (se 1 (by rfl) ⟨2605418, by rfl⟩ : syracuseStep 3473891 = 5210837) B5210837
theorem B2744945 : Blo 1219427 2744945 := bstep (se 2 (by rfl) ⟨1029354, by rfl⟩ : syracuseStep 2744945 = 2058709) B2058709
theorem B2744963 : Blo 1219427 2744963 := bstep (se 1 (by rfl) ⟨2058722, by rfl⟩ : syracuseStep 2744963 = 4117445) B4117445
theorem B5210801 : Blo 1219427 5210801 := bstep (se 2 (by rfl) ⟨1954050, by rfl⟩ : syracuseStep 5210801 = 3908101) B3908101
theorem B3089137 : Blo 1219427 3089137 := bstep (se 2 (by rfl) ⟨1158426, by rfl⟩ : syracuseStep 3089137 = 2316853) B2316853
theorem B2745233 : Blo 1219427 2745233 := bstep (se 2 (by rfl) ⟨1029462, by rfl⟩ : syracuseStep 2745233 = 2058925) B2058925
theorem B1737617 : Blo 1219427 1737617 := bstep (se 2 (by rfl) ⟨651606, by rfl⟩ : syracuseStep 1737617 = 1303213) B1303213
theorem B2745251 : Blo 1219427 2745251 := bstep (se 1 (by rfl) ⟨2058938, by rfl⟩ : syracuseStep 2745251 = 4117877) B4117877
theorem B2606033 : Blo 1219427 2606033 := bstep (se 2 (by rfl) ⟨977262, by rfl⟩ : syracuseStep 2606033 = 1954525) B1954525
theorem B1737731 : Blo 1219427 1737731 := bstep (se 1 (by rfl) ⟨1303298, by rfl⟩ : syracuseStep 1737731 = 2606597) B2606597
theorem B3089411 : Blo 1219427 3089411 := bstep (se 1 (by rfl) ⟨2317058, by rfl⟩ : syracuseStep 3089411 = 4634117) B4634117
theorem B1303619 : Blo 1219427 1303619 := bstep (se 1 (by rfl) ⟨977714, by rfl⟩ : syracuseStep 1303619 = 1955429) B1955429
theorem B9290821 : Blo 1219427 9290821 := bstep (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) B1742029
theorem B6177869 : Blo 1219427 6177869 := bstep (se 3 (by rfl) ⟨1158350, by rfl⟩ : syracuseStep 6177869 = 2316701) B2316701
theorem B1737811 : Blo 1219427 1737811 := bstep (se 1 (by rfl) ⟨1303358, by rfl⟩ : syracuseStep 1737811 = 2606717) B2606717
theorem B3523757 : Blo 1219427 3523757 := bstep (se 3 (by rfl) ⟨660704, by rfl⟩ : syracuseStep 3523757 = 1321409) B1321409
theorem B2745521 : Blo 1219427 2745521 := bstep (se 2 (by rfl) ⟨1029570, by rfl⟩ : syracuseStep 2745521 = 2059141) B2059141
theorem B2745539 : Blo 1219427 2745539 := bstep (se 1 (by rfl) ⟨2059154, by rfl⟩ : syracuseStep 2745539 = 4118309) B4118309
theorem B3089603 : Blo 1219427 3089603 := bstep (se 1 (by rfl) ⟨2317202, by rfl⟩ : syracuseStep 3089603 = 4634405) B4634405
theorem B10429667 : Blo 1219427 10429667 := bstep (se 1 (by rfl) ⟨7822250, by rfl⟩ : syracuseStep 10429667 = 15644501) B15644501
theorem B3474733 : Blo 1219427 3474733 := bstep (se 3 (by rfl) ⟨651512, by rfl⟩ : syracuseStep 3474733 = 1303025) B1303025
theorem B2114881 : Blo 1219427 2114881 := bstep (se 2 (by rfl) ⟨793080, by rfl⟩ : syracuseStep 2114881 = 1586161) B1586161
theorem B3474893 : Blo 1219427 3474893 := bstep (se 3 (by rfl) ⟨651542, by rfl⟩ : syracuseStep 3474893 = 1303085) B1303085
theorem B2745809 : Blo 1219427 2745809 := bstep (se 2 (by rfl) ⟨1029678, by rfl⟩ : syracuseStep 2745809 = 2059357) B2059357
theorem B2745827 : Blo 1219427 2745827 := bstep (se 1 (by rfl) ⟨2059370, by rfl⟩ : syracuseStep 2745827 = 4118741) B4118741
theorem B2057825 : Blo 1219427 2057825 := bstep (se 2 (by rfl) ⟨771684, by rfl⟩ : syracuseStep 2057825 = 1543369) B1543369
theorem B7816817 : Blo 1219427 7816817 := bstep (se 2 (by rfl) ⟨2931306, by rfl⟩ : syracuseStep 7816817 = 5862613) B5862613
theorem B1738369 : Blo 1219427 1738369 := bstep (se 2 (by rfl) ⟨651888, by rfl⟩ : syracuseStep 1738369 = 1303777) B1303777
theorem B3475075 : Blo 1219427 3475075 := bstep (se 1 (by rfl) ⟨2606306, by rfl⟩ : syracuseStep 3475075 = 5212613) B5212613
theorem B2057953 : Blo 1219427 2057953 := bstep (se 2 (by rfl) ⟨771732, by rfl⟩ : syracuseStep 2057953 = 1543465) B1543465
theorem B4630243 : Blo 1219427 4630243 := bstep (se 1 (by rfl) ⟨3472682, by rfl⟩ : syracuseStep 4630243 = 6945365) B6945365
theorem B2746097 : Blo 1219427 2746097 := bstep (se 2 (by rfl) ⟨1029786, by rfl⟩ : syracuseStep 2746097 = 2059573) B2059573
theorem B2057987 : Blo 1219427 2057987 := bstep (se 1 (by rfl) ⟨1543490, by rfl⟩ : syracuseStep 2057987 = 3086981) B3086981
theorem B2746115 : Blo 1219427 2746115 := bstep (se 1 (by rfl) ⟨2059586, by rfl⟩ : syracuseStep 2746115 = 4119173) B4119173
theorem B2606897 : Blo 1219427 2606897 := bstep (se 2 (by rfl) ⟨977586, by rfl⟩ : syracuseStep 2606897 = 1955173) B1955173
theorem B19793717 : Blo 1219427 19793717 := bstep (se 5 (by rfl) ⟨927830, by rfl⟩ : syracuseStep 19793717 = 1855661) B1855661
theorem B3909485 : Blo 1219427 3909485 := bstep (se 3 (by rfl) ⟨733028, by rfl⟩ : syracuseStep 3909485 = 1466057) B1466057
theorem B2058115 : Blo 1219427 2058115 := bstep (se 1 (by rfl) ⟨1543586, by rfl⟩ : syracuseStep 2058115 = 3087173) B3087173
theorem B2197457 : Blo 1219427 2197457 := bstep (se 2 (by rfl) ⟨824046, by rfl⟩ : syracuseStep 2197457 = 1648093) B1648093
theorem B2058257 : Blo 1219427 2058257 := bstep (se 2 (by rfl) ⟨771846, by rfl⟩ : syracuseStep 2058257 = 1543693) B1543693
theorem B2746385 : Blo 1219427 2746385 := bstep (se 2 (by rfl) ⟨1029894, by rfl⟩ : syracuseStep 2746385 = 2059789) B2059789
theorem B2746403 : Blo 1219427 2746403 := bstep (se 1 (by rfl) ⟨2059802, by rfl⟩ : syracuseStep 2746403 = 4119605) B4119605
theorem B2009171 : Blo 1219427 2009171 := bstep (se 1 (by rfl) ⟨1506878, by rfl⟩ : syracuseStep 2009171 = 3013757) B3013757
theorem B2058385 : Blo 1219427 2058385 := bstep (se 2 (by rfl) ⟨771894, by rfl⟩ : syracuseStep 2058385 = 1543789) B1543789
theorem B2058419 : Blo 1219427 2058419 := bstep (se 1 (by rfl) ⟨1543814, by rfl⟩ : syracuseStep 2058419 = 3087629) B3087629
theorem B1829153 : Blo 1219427 1829153 := bstep (se 2 (by rfl) ⟨685932, by rfl⟩ : syracuseStep 1829153 = 1371865) B1371865
theorem B2746673 : Blo 1219427 2746673 := bstep (se 2 (by rfl) ⟨1030002, by rfl⟩ : syracuseStep 2746673 = 2060005) B2060005
theorem B1829171 : Blo 1219427 1829171 := bstep (se 1 (by rfl) ⟨1371878, by rfl⟩ : syracuseStep 1829171 = 2743757) B2743757
theorem B2058547 : Blo 1219427 2058547 := bstep (se 1 (by rfl) ⟨1543910, by rfl⟩ : syracuseStep 2058547 = 3087821) B3087821
theorem B2746691 : Blo 1219427 2746691 := bstep (se 1 (by rfl) ⟨2060018, by rfl⟩ : syracuseStep 2746691 = 4120037) B4120037
theorem B1829201 : Blo 1219427 1829201 := bstep (se 2 (by rfl) ⟨685950, by rfl⟩ : syracuseStep 1829201 = 1371901) B1371901
theorem B1829219 : Blo 1219427 1829219 := bstep (se 1 (by rfl) ⟨1371914, by rfl⟩ : syracuseStep 1829219 = 2743829) B2743829
theorem B2091377 : Blo 1219427 2091377 := bstep (se 2 (by rfl) ⟨784266, by rfl⟩ : syracuseStep 2091377 = 1568533) B1568533
theorem B1829249 : Blo 1219427 1829249 := bstep (se 2 (by rfl) ⟨685968, by rfl⟩ : syracuseStep 1829249 = 1371937) B1371937
theorem B1829267 : Blo 1219427 1829267 := bstep (se 1 (by rfl) ⟨1371950, by rfl⟩ : syracuseStep 1829267 = 2743901) B2743901
theorem B1829297 : Blo 1219427 1829297 := bstep (se 2 (by rfl) ⟨685986, by rfl⟩ : syracuseStep 1829297 = 1371973) B1371973
theorem B2058689 : Blo 1219427 2058689 := bstep (se 2 (by rfl) ⟨772008, by rfl⟩ : syracuseStep 2058689 = 1544017) B1544017
theorem B1829315 : Blo 1219427 1829315 := bstep (se 1 (by rfl) ⟨1371986, by rfl⟩ : syracuseStep 1829315 = 2743973) B2743973
theorem B1829345 : Blo 1219427 1829345 := bstep (se 2 (by rfl) ⟨686004, by rfl⟩ : syracuseStep 1829345 = 1372009) B1372009
theorem B1829363 : Blo 1219427 1829363 := bstep (se 1 (by rfl) ⟨1372022, by rfl⟩ : syracuseStep 1829363 = 2744045) B2744045
theorem B7817741 : Blo 1219427 7817741 := bstep (se 3 (by rfl) ⟨1465826, by rfl⟩ : syracuseStep 7817741 = 2931653) B2931653
theorem B1829393 : Blo 1219427 1829393 := bstep (se 2 (by rfl) ⟨686022, by rfl⟩ : syracuseStep 1829393 = 1372045) B1372045
theorem B1829411 : Blo 1219427 1829411 := bstep (se 1 (by rfl) ⟨1372058, by rfl⟩ : syracuseStep 1829411 = 2744117) B2744117
theorem B1829441 : Blo 1219427 1829441 := bstep (se 2 (by rfl) ⟨686040, by rfl⟩ : syracuseStep 1829441 = 1372081) B1372081
theorem B2058817 : Blo 1219427 2058817 := bstep (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) B1544113
theorem B2746961 : Blo 1219427 2746961 := bstep (se 2 (by rfl) ⟨1030110, by rfl⟩ : syracuseStep 2746961 = 2060221) B2060221
theorem B1829459 : Blo 1219427 1829459 := bstep (se 1 (by rfl) ⟨1372094, by rfl⟩ : syracuseStep 1829459 = 2744189) B2744189
theorem B2058851 : Blo 1219427 2058851 := bstep (se 1 (by rfl) ⟨1544138, by rfl⟩ : syracuseStep 2058851 = 3088277) B3088277
theorem B2746979 : Blo 1219427 2746979 := bstep (se 1 (by rfl) ⟨2060234, by rfl⟩ : syracuseStep 2746979 = 4120469) B4120469
theorem B1829489 : Blo 1219427 1829489 := bstep (se 2 (by rfl) ⟨686058, by rfl⟩ : syracuseStep 1829489 = 1372117) B1372117
theorem B1829507 : Blo 1219427 1829507 := bstep (se 1 (by rfl) ⟨1372130, by rfl⟩ : syracuseStep 1829507 = 2744261) B2744261
theorem B1829537 : Blo 1219427 1829537 := bstep (se 2 (by rfl) ⟨686076, by rfl⟩ : syracuseStep 1829537 = 1372153) B1372153
theorem B1829555 : Blo 1219427 1829555 := bstep (se 1 (by rfl) ⟨1372166, by rfl⟩ : syracuseStep 1829555 = 2744333) B2744333
theorem B1829585 : Blo 1219427 1829585 := bstep (se 2 (by rfl) ⟨686094, by rfl⟩ : syracuseStep 1829585 = 1372189) B1372189
theorem B1829603 : Blo 1219427 1829603 := bstep (se 1 (by rfl) ⟨1372202, by rfl⟩ : syracuseStep 1829603 = 2744405) B2744405
theorem B2198243 : Blo 1219427 2198243 := bstep (se 1 (by rfl) ⟨1648682, by rfl⟩ : syracuseStep 2198243 = 3297365) B3297365
theorem B2058979 : Blo 1219427 2058979 := bstep (se 1 (by rfl) ⟨1544234, by rfl⟩ : syracuseStep 2058979 = 3088469) B3088469
theorem B1829633 : Blo 1219427 1829633 := bstep (se 2 (by rfl) ⟨686112, by rfl⟩ : syracuseStep 1829633 = 1372225) B1372225
theorem B1829651 : Blo 1219427 1829651 := bstep (se 1 (by rfl) ⟨1372238, by rfl⟩ : syracuseStep 1829651 = 2744477) B2744477
theorem B1829681 : Blo 1219427 1829681 := bstep (se 2 (by rfl) ⟨686130, by rfl⟩ : syracuseStep 1829681 = 1372261) B1372261
theorem B1829699 : Blo 1219427 1829699 := bstep (se 1 (by rfl) ⟨1372274, by rfl⟩ : syracuseStep 1829699 = 2744549) B2744549
theorem B1829729 : Blo 1219427 1829729 := bstep (se 2 (by rfl) ⟨686148, by rfl⟩ : syracuseStep 1829729 = 1372297) B1372297
theorem B2059121 : Blo 1219427 2059121 := bstep (se 2 (by rfl) ⟨772170, by rfl⟩ : syracuseStep 2059121 = 1544341) B1544341
theorem B1829747 : Blo 1219427 1829747 := bstep (se 1 (by rfl) ⟨1372310, by rfl⟩ : syracuseStep 1829747 = 2744621) B2744621
theorem B1829777 : Blo 1219427 1829777 := bstep (se 2 (by rfl) ⟨686166, by rfl⟩ : syracuseStep 1829777 = 1372333) B1372333
theorem B1829795 : Blo 1219427 1829795 := bstep (se 1 (by rfl) ⟨1372346, by rfl⟩ : syracuseStep 1829795 = 2744693) B2744693
theorem B1829825 : Blo 1219427 1829825 := bstep (se 2 (by rfl) ⟨686184, by rfl⟩ : syracuseStep 1829825 = 1372369) B1372369
theorem B1829843 : Blo 1219427 1829843 := bstep (se 1 (by rfl) ⟨1372382, by rfl⟩ : syracuseStep 1829843 = 2744765) B2744765
theorem B5352419 : Blo 1219427 5352419 := bstep (se 1 (by rfl) ⟨4014314, by rfl⟩ : syracuseStep 5352419 = 8028629) B8028629
theorem B1829873 : Blo 1219427 1829873 := bstep (se 2 (by rfl) ⟨686202, by rfl⟩ : syracuseStep 1829873 = 1372405) B1372405
theorem B2059249 : Blo 1219427 2059249 := bstep (se 2 (by rfl) ⟨772218, by rfl⟩ : syracuseStep 2059249 = 1544437) B1544437
theorem B3476465 : Blo 1219427 3476465 := bstep (se 2 (by rfl) ⟨1303674, by rfl⟩ : syracuseStep 3476465 = 2607349) B2607349
theorem B1829891 : Blo 1219427 1829891 := bstep (se 1 (by rfl) ⟨1372418, by rfl⟩ : syracuseStep 1829891 = 2744837) B2744837
theorem B16927757 : Blo 1219427 16927757 := bstep (se 3 (by rfl) ⟨3173954, by rfl⟩ : syracuseStep 16927757 = 6347909) B6347909
theorem B2059283 : Blo 1219427 2059283 := bstep (se 1 (by rfl) ⟨1544462, by rfl⟩ : syracuseStep 2059283 = 3088925) B3088925
theorem B1829921 : Blo 1219427 1829921 := bstep (se 2 (by rfl) ⟨686220, by rfl⟩ : syracuseStep 1829921 = 1372441) B1372441
theorem B1829939 : Blo 1219427 1829939 := bstep (se 1 (by rfl) ⟨1372454, by rfl⟩ : syracuseStep 1829939 = 2744909) B2744909
theorem B5213261 : Blo 1219427 5213261 := bstep (se 3 (by rfl) ⟨977486, by rfl⟩ : syracuseStep 5213261 = 1954973) B1954973
theorem B1829969 : Blo 1219427 1829969 := bstep (se 2 (by rfl) ⟨686238, by rfl⟩ : syracuseStep 1829969 = 1372477) B1372477
theorem B1829987 : Blo 1219427 1829987 := bstep (se 1 (by rfl) ⟨1372490, by rfl⟩ : syracuseStep 1829987 = 2744981) B2744981
theorem B1830017 : Blo 1219427 1830017 := bstep (se 2 (by rfl) ⟨686256, by rfl⟩ : syracuseStep 1830017 = 1372513) B1372513
theorem B1830035 : Blo 1219427 1830035 := bstep (se 1 (by rfl) ⟨1372526, by rfl⟩ : syracuseStep 1830035 = 2745053) B2745053
theorem B2059411 : Blo 1219427 2059411 := bstep (se 1 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 2059411 = 3089117) B3089117
theorem B1830065 : Blo 1219427 1830065 := bstep (se 2 (by rfl) ⟨686274, by rfl⟩ : syracuseStep 1830065 = 1372549) B1372549
theorem B1830083 : Blo 1219427 1830083 := bstep (se 1 (by rfl) ⟨1372562, by rfl⟩ : syracuseStep 1830083 = 2745125) B2745125
theorem B11136197 : Blo 1219427 11136197 := bstep (se 4 (by rfl) ⟨1044018, by rfl⟩ : syracuseStep 11136197 = 2088037) B2088037
theorem B1830113 : Blo 1219427 1830113 := bstep (se 2 (by rfl) ⟨686292, by rfl⟩ : syracuseStep 1830113 = 1372585) B1372585
theorem B1830131 : Blo 1219427 1830131 := bstep (se 1 (by rfl) ⟨1372598, by rfl⟩ : syracuseStep 1830131 = 2745197) B2745197
theorem B1830161 : Blo 1219427 1830161 := bstep (se 2 (by rfl) ⟨686310, by rfl⟩ : syracuseStep 1830161 = 1372621) B1372621
theorem B2059553 : Blo 1219427 2059553 := bstep (se 2 (by rfl) ⟨772332, by rfl⟩ : syracuseStep 2059553 = 1544665) B1544665
theorem B1830179 : Blo 1219427 1830179 := bstep (se 1 (by rfl) ⟨1372634, by rfl⟩ : syracuseStep 1830179 = 2745269) B2745269
theorem B1543475 : Blo 1219427 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B1830209 : Blo 1219427 1830209 := bstep (se 2 (by rfl) ⟨686328, by rfl⟩ : syracuseStep 1830209 = 1372657) B1372657
theorem B1830227 : Blo 1219427 1830227 := bstep (se 1 (by rfl) ⟨1372670, by rfl⟩ : syracuseStep 1830227 = 2745341) B2745341
theorem B4115825 : Blo 1219427 4115825 := bstep (se 2 (by rfl) ⟨1543434, by rfl⟩ : syracuseStep 4115825 = 3086869) B3086869
theorem B1830257 : Blo 1219427 1830257 := bstep (se 2 (by rfl) ⟨686346, by rfl⟩ : syracuseStep 1830257 = 1372693) B1372693
theorem B1830275 : Blo 1219427 1830275 := bstep (se 1 (by rfl) ⟨1372706, by rfl⟩ : syracuseStep 1830275 = 2745413) B2745413
theorem B1830305 : Blo 1219427 1830305 := bstep (se 2 (by rfl) ⟨686364, by rfl⟩ : syracuseStep 1830305 = 1372729) B1372729
theorem B2059681 : Blo 1219427 2059681 := bstep (se 2 (by rfl) ⟨772380, by rfl⟩ : syracuseStep 2059681 = 1544761) B1544761
theorem B1854883 : Blo 1219427 1854883 := bstep (se 1 (by rfl) ⟨1391162, by rfl⟩ : syracuseStep 1854883 = 2782325) B2782325
theorem B3911075 : Blo 1219427 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B1830323 : Blo 1219427 1830323 := bstep (se 1 (by rfl) ⟨1372742, by rfl⟩ : syracuseStep 1830323 = 2745485) B2745485
theorem B2059715 : Blo 1219427 2059715 := bstep (se 1 (by rfl) ⟨1544786, by rfl⟩ : syracuseStep 2059715 = 3089573) B3089573
theorem B1830353 : Blo 1219427 1830353 := bstep (se 2 (by rfl) ⟨686382, by rfl⟩ : syracuseStep 1830353 = 1372765) B1372765
theorem B1830371 : Blo 1219427 1830371 := bstep (se 1 (by rfl) ⟨1372778, by rfl⟩ : syracuseStep 1830371 = 2745557) B2745557
theorem B1830401 : Blo 1219427 1830401 := bstep (se 2 (by rfl) ⟨686400, by rfl⟩ : syracuseStep 1830401 = 1372801) B1372801
theorem B3296771 : Blo 1219427 3296771 := bstep (se 1 (by rfl) ⟨2472578, by rfl⟩ : syracuseStep 3296771 = 4945157) B4945157
theorem B1830419 : Blo 1219427 1830419 := bstep (se 1 (by rfl) ⟨1372814, by rfl⟩ : syracuseStep 1830419 = 2745629) B2745629
theorem B1830449 : Blo 1219427 1830449 := bstep (se 2 (by rfl) ⟨686418, by rfl⟩ : syracuseStep 1830449 = 1372837) B1372837
theorem B1830467 : Blo 1219427 1830467 := bstep (se 1 (by rfl) ⟨1372850, by rfl⟩ : syracuseStep 1830467 = 2745701) B2745701
theorem B2059843 : Blo 1219427 2059843 := bstep (se 1 (by rfl) ⟨1544882, by rfl⟩ : syracuseStep 2059843 = 3089765) B3089765
theorem B1830497 : Blo 1219427 1830497 := bstep (se 2 (by rfl) ⟨686436, by rfl⟩ : syracuseStep 1830497 = 1372873) B1372873
theorem B15855203 : Blo 1219427 15855203 := bstep (se 1 (by rfl) ⟨11891402, by rfl⟩ : syracuseStep 15855203 = 23782805) B23782805
theorem B3911267 : Blo 1219427 3911267 := bstep (se 1 (by rfl) ⟨2933450, by rfl⟩ : syracuseStep 3911267 = 5866901) B5866901
theorem B1830515 : Blo 1219427 1830515 := bstep (se 1 (by rfl) ⟨1372886, by rfl⟩ : syracuseStep 1830515 = 2745773) B2745773
theorem B3296899 : Blo 1219427 3296899 := bstep (se 1 (by rfl) ⟨2472674, by rfl⟩ : syracuseStep 3296899 = 4945349) B4945349
theorem B1830545 : Blo 1219427 1830545 := bstep (se 2 (by rfl) ⟨686454, by rfl⟩ : syracuseStep 1830545 = 1372909) B1372909
theorem B1830563 : Blo 1219427 1830563 := bstep (se 1 (by rfl) ⟨1372922, by rfl⟩ : syracuseStep 1830563 = 2745845) B2745845
theorem B1830593 : Blo 1219427 1830593 := bstep (se 2 (by rfl) ⟨686472, by rfl⟩ : syracuseStep 1830593 = 1372945) B1372945
theorem B2059985 : Blo 1219427 2059985 := bstep (se 2 (by rfl) ⟨772494, by rfl⟩ : syracuseStep 2059985 = 1544989) B1544989
theorem B1830611 : Blo 1219427 1830611 := bstep (se 1 (by rfl) ⟨1372958, by rfl⟩ : syracuseStep 1830611 = 2745917) B2745917
theorem B1830641 : Blo 1219427 1830641 := bstep (se 2 (by rfl) ⟨686490, by rfl⟩ : syracuseStep 1830641 = 1372981) B1372981
theorem B1830659 : Blo 1219427 1830659 := bstep (se 1 (by rfl) ⟨1372994, by rfl⟩ : syracuseStep 1830659 = 2745989) B2745989
theorem B1830689 : Blo 1219427 1830689 := bstep (se 2 (by rfl) ⟨686508, by rfl⟩ : syracuseStep 1830689 = 1373017) B1373017
theorem B1371955 : Blo 1219427 1371955 := bstep (se 1 (by rfl) ⟨1028966, by rfl⟩ : syracuseStep 1371955 = 2057933) B2057933
theorem B1830707 : Blo 1219427 1830707 := bstep (se 1 (by rfl) ⟨1373030, by rfl⟩ : syracuseStep 1830707 = 2746061) B2746061
theorem B1830737 : Blo 1219427 1830737 := bstep (se 2 (by rfl) ⟨686526, by rfl⟩ : syracuseStep 1830737 = 1373053) B1373053
theorem B2060113 : Blo 1219427 2060113 := bstep (se 2 (by rfl) ⟨772542, by rfl⟩ : syracuseStep 2060113 = 1545085) B1545085
theorem B1830755 : Blo 1219427 1830755 := bstep (se 1 (by rfl) ⟨1373066, by rfl⟩ : syracuseStep 1830755 = 2746133) B2746133
theorem B2060147 : Blo 1219427 2060147 := bstep (se 1 (by rfl) ⟨1545110, by rfl⟩ : syracuseStep 2060147 = 3090221) B3090221
theorem B1830785 : Blo 1219427 1830785 := bstep (se 2 (by rfl) ⟨686544, by rfl⟩ : syracuseStep 1830785 = 1373089) B1373089
theorem B4116365 : Blo 1219427 4116365 := bstep (se 3 (by rfl) ⟨771818, by rfl⟩ : syracuseStep 4116365 = 1543637) B1543637
theorem B4632461 : Blo 1219427 4632461 := bstep (se 3 (by rfl) ⟨868586, by rfl⟩ : syracuseStep 4632461 = 1737173) B1737173
theorem B1830803 : Blo 1219427 1830803 := bstep (se 1 (by rfl) ⟨1373102, by rfl⟩ : syracuseStep 1830803 = 2746205) B2746205
theorem B1830833 : Blo 1219427 1830833 := bstep (se 2 (by rfl) ⟨686562, by rfl⟩ : syracuseStep 1830833 = 1373125) B1373125
theorem B6180785 : Blo 1219427 6180785 := bstep (se 2 (by rfl) ⟨2317794, by rfl⟩ : syracuseStep 6180785 = 4635589) B4635589
theorem B3010499 : Blo 1219427 3010499 := bstep (se 1 (by rfl) ⟨2257874, by rfl⟩ : syracuseStep 3010499 = 4515749) B4515749
theorem B1372099 : Blo 1219427 1372099 := bstep (se 1 (by rfl) ⟨1029074, by rfl⟩ : syracuseStep 1372099 = 2058149) B2058149
theorem B4116419 : Blo 1219427 4116419 := bstep (se 1 (by rfl) ⟨3087314, by rfl⟩ : syracuseStep 4116419 = 6174629) B6174629
theorem B1830851 : Blo 1219427 1830851 := bstep (se 1 (by rfl) ⟨1373138, by rfl⟩ : syracuseStep 1830851 = 2746277) B2746277
theorem B1830881 : Blo 1219427 1830881 := bstep (se 2 (by rfl) ⟨686580, by rfl⟩ : syracuseStep 1830881 = 1373161) B1373161
theorem B1544179 : Blo 1219427 1544179 := bstep (se 1 (by rfl) ⟨1158134, by rfl⟩ : syracuseStep 1544179 = 2316269) B2316269
theorem B1830899 : Blo 1219427 1830899 := bstep (se 1 (by rfl) ⟨1373174, by rfl⟩ : syracuseStep 1830899 = 2746349) B2746349
theorem B2060275 : Blo 1219427 2060275 := bstep (se 1 (by rfl) ⟨1545206, by rfl⟩ : syracuseStep 2060275 = 3090413) B3090413
theorem B1830929 : Blo 1219427 1830929 := bstep (se 2 (by rfl) ⟨686598, by rfl⟩ : syracuseStep 1830929 = 1373197) B1373197
theorem B1830947 : Blo 1219427 1830947 := bstep (se 1 (by rfl) ⟨1373210, by rfl⟩ : syracuseStep 1830947 = 2746421) B2746421
theorem B1830977 : Blo 1219427 1830977 := bstep (se 2 (by rfl) ⟨686616, by rfl⟩ : syracuseStep 1830977 = 1373233) B1373233
theorem B1372243 : Blo 1219427 1372243 := bstep (se 1 (by rfl) ⟨1029182, by rfl⟩ : syracuseStep 1372243 = 2058365) B2058365
theorem B1544275 : Blo 1219427 1544275 := bstep (se 1 (by rfl) ⟨1158206, by rfl⟩ : syracuseStep 1544275 = 2316413) B2316413
theorem B1830995 : Blo 1219427 1830995 := bstep (se 1 (by rfl) ⟨1373246, by rfl⟩ : syracuseStep 1830995 = 2746493) B2746493
theorem B26382449 : Blo 1219427 26382449 := bstep (se 2 (by rfl) ⟨9893418, by rfl⟩ : syracuseStep 26382449 = 19786837) B19786837
theorem B1831025 : Blo 1219427 1831025 := bstep (se 2 (by rfl) ⟨686634, by rfl⟩ : syracuseStep 1831025 = 1373269) B1373269
theorem B1831043 : Blo 1219427 1831043 := bstep (se 1 (by rfl) ⟨1373282, by rfl⟩ : syracuseStep 1831043 = 2746565) B2746565
theorem B1831073 : Blo 1219427 1831073 := bstep (se 2 (by rfl) ⟨686652, by rfl⟩ : syracuseStep 1831073 = 1373305) B1373305
theorem B1831091 : Blo 1219427 1831091 := bstep (se 1 (by rfl) ⟨1373318, by rfl⟩ : syracuseStep 1831091 = 2746637) B2746637
theorem B4116689 : Blo 1219427 4116689 := bstep (se 2 (by rfl) ⟨1543758, by rfl⟩ : syracuseStep 4116689 = 3087517) B3087517
theorem B1831121 : Blo 1219427 1831121 := bstep (se 2 (by rfl) ⟨686670, by rfl⟩ : syracuseStep 1831121 = 1373341) B1373341
theorem B1372387 : Blo 1219427 1372387 := bstep (se 1 (by rfl) ⟨1029290, by rfl⟩ : syracuseStep 1372387 = 2058581) B2058581
theorem B1831139 : Blo 1219427 1831139 := bstep (se 1 (by rfl) ⟨1373354, by rfl⟩ : syracuseStep 1831139 = 2746709) B2746709
theorem B1831169 : Blo 1219427 1831169 := bstep (se 2 (by rfl) ⟨686688, by rfl⟩ : syracuseStep 1831169 = 1373377) B1373377
theorem B1855747 : Blo 1219427 1855747 := bstep (se 1 (by rfl) ⟨1391810, by rfl⟩ : syracuseStep 1855747 = 2783621) B2783621
theorem B17150221 : Blo 1219427 17150221 := bstep (se 3 (by rfl) ⟨3215666, by rfl⟩ : syracuseStep 17150221 = 6431333) B6431333
theorem B1831187 : Blo 1219427 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B1831217 : Blo 1219427 1831217 := bstep (se 2 (by rfl) ⟨686706, by rfl⟩ : syracuseStep 1831217 = 1373413) B1373413
theorem B1855795 : Blo 1219427 1855795 := bstep (se 1 (by rfl) ⟨1391846, by rfl⟩ : syracuseStep 1855795 = 2783693) B2783693
theorem B1831235 : Blo 1219427 1831235 := bstep (se 1 (by rfl) ⟨1373426, by rfl⟩ : syracuseStep 1831235 = 2746853) B2746853
theorem B1831265 : Blo 1219427 1831265 := bstep (se 2 (by rfl) ⟨686724, by rfl⟩ : syracuseStep 1831265 = 1373449) B1373449
theorem B3297635 : Blo 1219427 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B1372531 : Blo 1219427 1372531 := bstep (se 1 (by rfl) ⟨1029398, by rfl⟩ : syracuseStep 1372531 = 2058797) B2058797
theorem B1831283 : Blo 1219427 1831283 := bstep (se 1 (by rfl) ⟨1373462, by rfl⟩ : syracuseStep 1831283 = 2746925) B2746925
theorem B1831313 : Blo 1219427 1831313 := bstep (se 2 (by rfl) ⟨686742, by rfl⟩ : syracuseStep 1831313 = 1373485) B1373485
theorem B1831331 : Blo 1219427 1831331 := bstep (se 1 (by rfl) ⟨1373498, by rfl⟩ : syracuseStep 1831331 = 2746997) B2746997
theorem B1831361 : Blo 1219427 1831361 := bstep (se 2 (by rfl) ⟨686760, by rfl⟩ : syracuseStep 1831361 = 1373521) B1373521
theorem B1831379 : Blo 1219427 1831379 := bstep (se 1 (by rfl) ⟨1373534, by rfl⟩ : syracuseStep 1831379 = 2747069) B2747069
theorem B13906403 : Blo 1219427 13906403 := bstep (se 1 (by rfl) ⟨10429802, by rfl⟩ : syracuseStep 13906403 = 20859605) B20859605
theorem B1954307 : Blo 1219427 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B1372675 : Blo 1219427 1372675 := bstep (se 1 (by rfl) ⟨1029506, by rfl⟩ : syracuseStep 1372675 = 2059013) B2059013
theorem B11301389 : Blo 1219427 11301389 := bstep (se 3 (by rfl) ⟨2119010, by rfl⟩ : syracuseStep 11301389 = 4238021) B4238021
theorem B1544771 : Blo 1219427 1544771 := bstep (se 1 (by rfl) ⟨1158578, by rfl⟩ : syracuseStep 1544771 = 2317157) B2317157
theorem B3297937 : Blo 1219427 3297937 := bstep (se 2 (by rfl) ⟨1236726, by rfl⟩ : syracuseStep 3297937 = 2473453) B2473453
theorem B1372819 : Blo 1219427 1372819 := bstep (se 1 (by rfl) ⟨1029614, by rfl⟩ : syracuseStep 1372819 = 2059229) B2059229
theorem B4117229 : Blo 1219427 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B4117283 : Blo 1219427 4117283 := bstep (se 1 (by rfl) ⟨3087962, by rfl⟩ : syracuseStep 4117283 = 6175925) B6175925
theorem B1372963 : Blo 1219427 1372963 := bstep (se 1 (by rfl) ⟨1029722, by rfl⟩ : syracuseStep 1372963 = 2059445) B2059445
theorem B1373107 : Blo 1219427 1373107 := bstep (se 1 (by rfl) ⟨1029830, by rfl⟩ : syracuseStep 1373107 = 2059661) B2059661
theorem B4117553 : Blo 1219427 4117553 := bstep (se 2 (by rfl) ⟨1544082, by rfl⟩ : syracuseStep 4117553 = 3088165) B3088165
theorem B1373251 : Blo 1219427 1373251 := bstep (se 1 (by rfl) ⟨1029938, by rfl⟩ : syracuseStep 1373251 = 2059877) B2059877
theorem B6263885 : Blo 1219427 6263885 := bstep (se 3 (by rfl) ⟨1174478, by rfl⟩ : syracuseStep 6263885 = 2348957) B2348957
theorem B3298403 : Blo 1219427 3298403 := bstep (se 1 (by rfl) ⟨2473802, by rfl⟩ : syracuseStep 3298403 = 4947605) B4947605
theorem B4945009 : Blo 1219427 4945009 := bstep (se 2 (by rfl) ⟨1854378, by rfl⟩ : syracuseStep 4945009 = 3708757) B3708757
theorem B2315395 : Blo 1219427 2315395 := bstep (se 1 (by rfl) ⟨1736546, by rfl⟩ : syracuseStep 2315395 = 3473093) B3473093
theorem B2315441 : Blo 1219427 2315441 := bstep (se 2 (by rfl) ⟨868290, by rfl⟩ : syracuseStep 2315441 = 1736581) B1736581
theorem B3298499 : Blo 1219427 3298499 := bstep (se 1 (by rfl) ⟨2473874, by rfl⟩ : syracuseStep 3298499 = 4947749) B4947749
theorem B6264013 : Blo 1219427 6264013 := bstep (se 3 (by rfl) ⟨1174502, by rfl⟩ : syracuseStep 6264013 = 2349005) B2349005
theorem B1373395 : Blo 1219427 1373395 := bstep (se 1 (by rfl) ⟨1030046, by rfl⟩ : syracuseStep 1373395 = 2060093) B2060093
theorem B1955153 : Blo 1219427 1955153 := bstep (se 2 (by rfl) ⟨733182, by rfl⟩ : syracuseStep 1955153 = 1466365) B1466365
theorem B1373539 : Blo 1219427 1373539 := bstep (se 1 (by rfl) ⟨1030154, by rfl⟩ : syracuseStep 1373539 = 2060309) B2060309
theorem B2315729 : Blo 1219427 2315729 := bstep (se 2 (by rfl) ⟨868398, by rfl⟩ : syracuseStep 2315729 = 1736797) B1736797
theorem B1955281 : Blo 1219427 1955281 := bstep (se 2 (by rfl) ⟨733230, by rfl⟩ : syracuseStep 1955281 = 1466461) B1466461
theorem B1955345 : Blo 1219427 1955345 := bstep (se 2 (by rfl) ⟨733254, by rfl⟩ : syracuseStep 1955345 = 1466509) B1466509
theorem B35182133 : Blo 1219427 35182133 := bstep (se 5 (by rfl) ⟨1649162, by rfl⟩ : syracuseStep 35182133 = 3298325) B3298325
theorem B4118093 : Blo 1219427 4118093 := bstep (se 3 (by rfl) ⟨772142, by rfl⟩ : syracuseStep 4118093 = 1544285) B1544285
theorem B4118147 : Blo 1219427 4118147 := bstep (se 1 (by rfl) ⟨3088610, by rfl⟩ : syracuseStep 4118147 = 6177221) B6177221
theorem B14096099 : Blo 1219427 14096099 := bstep (se 1 (by rfl) ⟨10572074, by rfl⟩ : syracuseStep 14096099 = 21144149) B21144149
theorem B6952837 : Blo 1219427 6952837 := bstep (se 4 (by rfl) ⟨651828, by rfl⟩ : syracuseStep 6952837 = 1303657) B1303657
theorem B4118417 : Blo 1219427 4118417 := bstep (se 2 (by rfl) ⟨1544406, by rfl⟩ : syracuseStep 4118417 = 3088813) B3088813
theorem B2087059 : Blo 1219427 2087059 := bstep (se 1 (by rfl) ⟨1565294, by rfl⟩ : syracuseStep 2087059 = 3130589) B3130589
theorem B2316451 : Blo 1219427 2316451 := bstep (se 1 (by rfl) ⟨1737338, by rfl⟩ : syracuseStep 2316451 = 3474677) B3474677
theorem B5863843 : Blo 1219427 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B4118957 : Blo 1219427 4118957 := bstep (se 3 (by rfl) ⟨772304, by rfl⟩ : syracuseStep 4118957 = 1544609) B1544609
theorem B3086819 : Blo 1219427 3086819 := bstep (se 1 (by rfl) ⟨2315114, by rfl⟩ : syracuseStep 3086819 = 4630229) B4630229
theorem B4119011 : Blo 1219427 4119011 := bstep (se 1 (by rfl) ⟨3089258, by rfl⟩ : syracuseStep 4119011 = 6178517) B6178517
theorem B2931299 : Blo 1219427 2931299 := bstep (se 1 (by rfl) ⟨2198474, by rfl⟩ : syracuseStep 2931299 = 4396949) B4396949
theorem B2316899 : Blo 1219427 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B14080625 : Blo 1219427 14080625 := bstep (se 2 (by rfl) ⟨5280234, by rfl⟩ : syracuseStep 14080625 = 10560469) B10560469
theorem B3087011 : Blo 1219427 3087011 := bstep (se 1 (by rfl) ⟨2315258, by rfl⟩ : syracuseStep 3087011 = 4630517) B4630517
theorem B13187765 : Blo 1219427 13187765 := bstep (se 5 (by rfl) ⟨618176, by rfl⟩ : syracuseStep 13187765 = 1236353) B1236353
theorem B4119281 : Blo 1219427 4119281 := bstep (se 2 (by rfl) ⟨1544730, by rfl⟩ : syracuseStep 4119281 = 3089461) B3089461
theorem B4635377 : Blo 1219427 4635377 := bstep (se 2 (by rfl) ⟨1738266, by rfl⟩ : syracuseStep 4635377 = 3476533) B3476533
theorem B1219427 : Blo 1219427 1219427 := bstep (se 1 (by rfl) ⟨914570, by rfl⟩ : syracuseStep 1219427 = 1829141) B1829141
theorem B6175601 : Blo 1219427 6175601 := bstep (se 2 (by rfl) ⟨2315850, by rfl⟩ : syracuseStep 6175601 = 4631701) B4631701
theorem B1219443 : Blo 1219427 1219443 := bstep (se 1 (by rfl) ⟨914582, by rfl⟩ : syracuseStep 1219443 = 1829165) B1829165
theorem B1219459 : Blo 1219427 1219459 := bstep (se 1 (by rfl) ⟨914594, by rfl⟩ : syracuseStep 1219459 = 1829189) B1829189
theorem B2317187 : Blo 1219427 2317187 := bstep (se 1 (by rfl) ⟨1737890, by rfl⟩ : syracuseStep 2317187 = 3475781) B3475781
theorem B1219475 : Blo 1219427 1219475 := bstep (se 1 (by rfl) ⟨914606, by rfl⟩ : syracuseStep 1219475 = 1829213) B1829213
theorem B1219491 : Blo 1219427 1219491 := bstep (se 1 (by rfl) ⟨914618, by rfl⟩ : syracuseStep 1219491 = 1829237) B1829237
theorem B1219507 : Blo 1219427 1219507 := bstep (se 1 (by rfl) ⟨914630, by rfl⟩ : syracuseStep 1219507 = 1829261) B1829261
theorem B1219523 : Blo 1219427 1219523 := bstep (se 1 (by rfl) ⟨914642, by rfl⟩ : syracuseStep 1219523 = 1829285) B1829285
theorem B1219539 : Blo 1219427 1219539 := bstep (se 1 (by rfl) ⟨914654, by rfl⟩ : syracuseStep 1219539 = 1829309) B1829309
theorem B1219555 : Blo 1219427 1219555 := bstep (se 1 (by rfl) ⟨914666, by rfl⟩ : syracuseStep 1219555 = 1829333) B1829333
theorem B1219571 : Blo 1219427 1219571 := bstep (se 1 (by rfl) ⟨914678, by rfl⟩ : syracuseStep 1219571 = 1829357) B1829357
theorem B1219587 : Blo 1219427 1219587 := bstep (se 1 (by rfl) ⟨914690, by rfl⟩ : syracuseStep 1219587 = 1829381) B1829381
theorem B1219603 : Blo 1219427 1219603 := bstep (se 1 (by rfl) ⟨914702, by rfl⟩ : syracuseStep 1219603 = 1829405) B1829405
theorem B1219619 : Blo 1219427 1219619 := bstep (se 1 (by rfl) ⟨914714, by rfl⟩ : syracuseStep 1219619 = 1829429) B1829429
theorem B1219635 : Blo 1219427 1219635 := bstep (se 1 (by rfl) ⟨914726, by rfl⟩ : syracuseStep 1219635 = 1829453) B1829453
theorem B1219651 : Blo 1219427 1219651 := bstep (se 1 (by rfl) ⟨914738, by rfl⟩ : syracuseStep 1219651 = 1829477) B1829477
theorem B1219667 : Blo 1219427 1219667 := bstep (se 1 (by rfl) ⟨914750, by rfl⟩ : syracuseStep 1219667 = 1829501) B1829501
theorem B1219683 : Blo 1219427 1219683 := bstep (se 1 (by rfl) ⟨914762, by rfl⟩ : syracuseStep 1219683 = 1829525) B1829525
theorem B1219699 : Blo 1219427 1219699 := bstep (se 1 (by rfl) ⟨914774, by rfl⟩ : syracuseStep 1219699 = 1829549) B1829549
theorem B1219715 : Blo 1219427 1219715 := bstep (se 1 (by rfl) ⟨914786, by rfl⟩ : syracuseStep 1219715 = 1829573) B1829573
theorem B4947085 : Blo 1219427 4947085 := bstep (se 3 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 4947085 = 1855157) B1855157
theorem B1219731 : Blo 1219427 1219731 := bstep (se 1 (by rfl) ⟨914798, by rfl⟩ : syracuseStep 1219731 = 1829597) B1829597
theorem B1219747 : Blo 1219427 1219747 := bstep (se 1 (by rfl) ⟨914810, by rfl⟩ : syracuseStep 1219747 = 1829621) B1829621
theorem B1219763 : Blo 1219427 1219763 := bstep (se 1 (by rfl) ⟨914822, by rfl⟩ : syracuseStep 1219763 = 1829645) B1829645
theorem B1219779 : Blo 1219427 1219779 := bstep (se 1 (by rfl) ⟨914834, by rfl⟩ : syracuseStep 1219779 = 1829669) B1829669
theorem B1219795 : Blo 1219427 1219795 := bstep (se 1 (by rfl) ⟨914846, by rfl⟩ : syracuseStep 1219795 = 1829693) B1829693
theorem B1219811 : Blo 1219427 1219811 := bstep (se 1 (by rfl) ⟨914858, by rfl⟩ : syracuseStep 1219811 = 1829717) B1829717
theorem B1219827 : Blo 1219427 1219827 := bstep (se 1 (by rfl) ⟨914870, by rfl⟩ : syracuseStep 1219827 = 1829741) B1829741
theorem B1809665 : Blo 1219427 1809665 := bstep (se 2 (by rfl) ⟨678624, by rfl⟩ : syracuseStep 1809665 = 1357249) B1357249
theorem B1219843 : Blo 1219427 1219843 := bstep (se 1 (by rfl) ⟨914882, by rfl⟩ : syracuseStep 1219843 = 1829765) B1829765
theorem B4119821 : Blo 1219427 4119821 := bstep (se 3 (by rfl) ⟨772466, by rfl⟩ : syracuseStep 4119821 = 1544933) B1544933
theorem B1219859 : Blo 1219427 1219859 := bstep (se 1 (by rfl) ⟨914894, by rfl⟩ : syracuseStep 1219859 = 1829789) B1829789
theorem B1219875 : Blo 1219427 1219875 := bstep (se 1 (by rfl) ⟨914906, by rfl⟩ : syracuseStep 1219875 = 1829813) B1829813
theorem B1219891 : Blo 1219427 1219891 := bstep (se 1 (by rfl) ⟨914918, by rfl⟩ : syracuseStep 1219891 = 1829837) B1829837
theorem B1219907 : Blo 1219427 1219907 := bstep (se 1 (by rfl) ⟨914930, by rfl⟩ : syracuseStep 1219907 = 1829861) B1829861
theorem B4119875 : Blo 1219427 4119875 := bstep (se 1 (by rfl) ⟨3089906, by rfl⟩ : syracuseStep 4119875 = 6179813) B6179813
theorem B1219923 : Blo 1219427 1219923 := bstep (se 1 (by rfl) ⟨914942, by rfl⟩ : syracuseStep 1219923 = 1829885) B1829885
theorem B1760611 : Blo 1219427 1760611 := bstep (se 1 (by rfl) ⟨1320458, by rfl⟩ : syracuseStep 1760611 = 2640917) B2640917
theorem B1219939 : Blo 1219427 1219939 := bstep (se 1 (by rfl) ⟨914954, by rfl⟩ : syracuseStep 1219939 = 1829909) B1829909
theorem B1219955 : Blo 1219427 1219955 := bstep (se 1 (by rfl) ⟨914966, by rfl⟩ : syracuseStep 1219955 = 1829933) B1829933
theorem B1219971 : Blo 1219427 1219971 := bstep (se 1 (by rfl) ⟨914978, by rfl⟩ : syracuseStep 1219971 = 1829957) B1829957
theorem B1219987 : Blo 1219427 1219987 := bstep (se 1 (by rfl) ⟨914990, by rfl⟩ : syracuseStep 1219987 = 1829981) B1829981
theorem B1220003 : Blo 1219427 1220003 := bstep (se 1 (by rfl) ⟨915002, by rfl⟩ : syracuseStep 1220003 = 1830005) B1830005
theorem B2932145 : Blo 1219427 2932145 := bstep (se 2 (by rfl) ⟨1099554, by rfl⟩ : syracuseStep 2932145 = 2199109) B2199109
theorem B1220019 : Blo 1219427 1220019 := bstep (se 1 (by rfl) ⟨915014, by rfl⟩ : syracuseStep 1220019 = 1830029) B1830029
theorem B1220035 : Blo 1219427 1220035 := bstep (se 1 (by rfl) ⟨915026, by rfl⟩ : syracuseStep 1220035 = 1830053) B1830053
theorem B3907025 : Blo 1219427 3907025 := bstep (se 2 (by rfl) ⟨1465134, by rfl⟩ : syracuseStep 3907025 = 2930269) B2930269
theorem B1220051 : Blo 1219427 1220051 := bstep (se 1 (by rfl) ⟨915038, by rfl⟩ : syracuseStep 1220051 = 1830077) B1830077
theorem B5209571 : Blo 1219427 5209571 := bstep (se 1 (by rfl) ⟨3907178, by rfl⟩ : syracuseStep 5209571 = 7814357) B7814357
theorem B1220067 : Blo 1219427 1220067 := bstep (se 1 (by rfl) ⟨915050, by rfl⟩ : syracuseStep 1220067 = 1830101) B1830101
theorem B4398563 : Blo 1219427 4398563 := bstep (se 1 (by rfl) ⟨3298922, by rfl⟩ : syracuseStep 4398563 = 6597845) B6597845
theorem B2743793 : Blo 1219427 2743793 := bstep (se 2 (by rfl) ⟨1028922, by rfl⟩ : syracuseStep 2743793 = 2057845) B2057845
theorem B1220083 : Blo 1219427 1220083 := bstep (se 1 (by rfl) ⟨915062, by rfl⟩ : syracuseStep 1220083 = 1830125) B1830125
theorem B2743811 : Blo 1219427 2743811 := bstep (se 1 (by rfl) ⟨2057858, by rfl⟩ : syracuseStep 2743811 = 4115717) B4115717
theorem B1220099 : Blo 1219427 1220099 := bstep (se 1 (by rfl) ⟨915074, by rfl⟩ : syracuseStep 1220099 = 1830149) B1830149
theorem B1220115 : Blo 1219427 1220115 := bstep (se 1 (by rfl) ⟨915086, by rfl⟩ : syracuseStep 1220115 = 1830173) B1830173
theorem B1220131 : Blo 1219427 1220131 := bstep (se 1 (by rfl) ⟨915098, by rfl⟩ : syracuseStep 1220131 = 1830197) B1830197
theorem B1220147 : Blo 1219427 1220147 := bstep (se 1 (by rfl) ⟨915110, by rfl⟩ : syracuseStep 1220147 = 1830221) B1830221
theorem B1220163 : Blo 1219427 1220163 := bstep (se 1 (by rfl) ⟨915122, by rfl⟩ : syracuseStep 1220163 = 1830245) B1830245
theorem B1736273 : Blo 1219427 1736273 := bstep (se 2 (by rfl) ⟨651102, by rfl⟩ : syracuseStep 1736273 = 1302205) B1302205
theorem B3087953 : Blo 1219427 3087953 := bstep (se 2 (by rfl) ⟨1157982, by rfl⟩ : syracuseStep 3087953 = 2315965) B2315965
theorem B1220179 : Blo 1219427 1220179 := bstep (se 1 (by rfl) ⟨915134, by rfl⟩ : syracuseStep 1220179 = 1830269) B1830269
theorem B4120145 : Blo 1219427 4120145 := bstep (se 2 (by rfl) ⟨1545054, by rfl⟩ : syracuseStep 4120145 = 3090109) B3090109
theorem B1220195 : Blo 1219427 1220195 := bstep (se 1 (by rfl) ⟨915146, by rfl⟩ : syracuseStep 1220195 = 1830293) B1830293
theorem B1220211 : Blo 1219427 1220211 := bstep (se 1 (by rfl) ⟨915158, by rfl⟩ : syracuseStep 1220211 = 1830317) B1830317
theorem B3088003 : Blo 1219427 3088003 := bstep (se 1 (by rfl) ⟨2316002, by rfl⟩ : syracuseStep 3088003 = 4632005) B4632005
theorem B1220227 : Blo 1219427 1220227 := bstep (se 1 (by rfl) ⟨915170, by rfl⟩ : syracuseStep 1220227 = 1830341) B1830341
theorem B1220243 : Blo 1219427 1220243 := bstep (se 1 (by rfl) ⟨915182, by rfl⟩ : syracuseStep 1220243 = 1830365) B1830365
theorem B1736353 : Blo 1219427 1736353 := bstep (se 2 (by rfl) ⟨651132, by rfl⟩ : syracuseStep 1736353 = 1302265) B1302265
theorem B7814819 : Blo 1219427 7814819 := bstep (se 1 (by rfl) ⟨5861114, by rfl⟩ : syracuseStep 7814819 = 11722229) B11722229
theorem B1220259 : Blo 1219427 1220259 := bstep (se 1 (by rfl) ⟨915194, by rfl⟩ : syracuseStep 1220259 = 1830389) B1830389
theorem B1220275 : Blo 1219427 1220275 := bstep (se 1 (by rfl) ⟨915206, by rfl⟩ : syracuseStep 1220275 = 1830413) B1830413
theorem B1220291 : Blo 1219427 1220291 := bstep (se 1 (by rfl) ⟨915218, by rfl⟩ : syracuseStep 1220291 = 1830437) B1830437
theorem B1220307 : Blo 1219427 1220307 := bstep (se 1 (by rfl) ⟨915230, by rfl⟩ : syracuseStep 1220307 = 1830461) B1830461
theorem B1220323 : Blo 1219427 1220323 := bstep (se 1 (by rfl) ⟨915242, by rfl⟩ : syracuseStep 1220323 = 1830485) B1830485
theorem B15040241 : Blo 1219427 15040241 := bstep (se 2 (by rfl) ⟨5640090, by rfl⟩ : syracuseStep 15040241 = 11280181) B11280181
theorem B1220339 : Blo 1219427 1220339 := bstep (se 1 (by rfl) ⟨915254, by rfl⟩ : syracuseStep 1220339 = 1830509) B1830509
theorem B1220355 : Blo 1219427 1220355 := bstep (se 1 (by rfl) ⟨915266, by rfl⟩ : syracuseStep 1220355 = 1830533) B1830533
theorem B2744081 : Blo 1219427 2744081 := bstep (se 2 (by rfl) ⟨1029030, by rfl⟩ : syracuseStep 2744081 = 2058061) B2058061
theorem B3088145 : Blo 1219427 3088145 := bstep (se 2 (by rfl) ⟨1158054, by rfl⟩ : syracuseStep 3088145 = 2316109) B2316109
theorem B1220371 : Blo 1219427 1220371 := bstep (se 1 (by rfl) ⟨915278, by rfl⟩ : syracuseStep 1220371 = 1830557) B1830557
theorem B2744099 : Blo 1219427 2744099 := bstep (se 1 (by rfl) ⟨2058074, by rfl⟩ : syracuseStep 2744099 = 4116149) B4116149
theorem B2228003 : Blo 1219427 2228003 := bstep (se 1 (by rfl) ⟨1671002, by rfl⟩ : syracuseStep 2228003 = 3342005) B3342005
theorem B1220387 : Blo 1219427 1220387 := bstep (se 1 (by rfl) ⟨915290, by rfl⟩ : syracuseStep 1220387 = 1830581) B1830581
theorem B1220403 : Blo 1219427 1220403 := bstep (se 1 (by rfl) ⟨915302, by rfl⟩ : syracuseStep 1220403 = 1830605) B1830605
theorem B3473219 : Blo 1219427 3473219 := bstep (se 1 (by rfl) ⟨2604914, by rfl⟩ : syracuseStep 3473219 = 5209829) B5209829
theorem B1220419 : Blo 1219427 1220419 := bstep (se 1 (by rfl) ⟨915314, by rfl⟩ : syracuseStep 1220419 = 1830629) B1830629
theorem B1302355 : Blo 1219427 1302355 := bstep (se 1 (by rfl) ⟨976766, by rfl⟩ : syracuseStep 1302355 = 1953533) B1953533
theorem B1220435 : Blo 1219427 1220435 := bstep (se 1 (by rfl) ⟨915326, by rfl⟩ : syracuseStep 1220435 = 1830653) B1830653
theorem B1785683 : Blo 1219427 1785683 := bstep (se 1 (by rfl) ⟨1339262, by rfl⟩ : syracuseStep 1785683 = 2678525) B2678525
theorem B1220451 : Blo 1219427 1220451 := bstep (se 1 (by rfl) ⟨915338, by rfl⟩ : syracuseStep 1220451 = 1830677) B1830677
theorem B13188977 : Blo 1219427 13188977 := bstep (se 2 (by rfl) ⟨4945866, by rfl⟩ : syracuseStep 13188977 = 9891733) B9891733
theorem B1220467 : Blo 1219427 1220467 := bstep (se 1 (by rfl) ⟨915350, by rfl⟩ : syracuseStep 1220467 = 1830701) B1830701
theorem B1220483 : Blo 1219427 1220483 := bstep (se 1 (by rfl) ⟨915362, by rfl⟩ : syracuseStep 1220483 = 1830725) B1830725
theorem B3710861 : Blo 1219427 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B1220499 : Blo 1219427 1220499 := bstep (se 1 (by rfl) ⟨915374, by rfl⟩ : syracuseStep 1220499 = 1830749) B1830749
theorem B1220515 : Blo 1219427 1220515 := bstep (se 1 (by rfl) ⟨915386, by rfl⟩ : syracuseStep 1220515 = 1830773) B1830773
theorem B1220531 : Blo 1219427 1220531 := bstep (se 1 (by rfl) ⟨915398, by rfl⟩ : syracuseStep 1220531 = 1830797) B1830797
theorem B1220547 : Blo 1219427 1220547 := bstep (se 1 (by rfl) ⟨915410, by rfl⟩ : syracuseStep 1220547 = 1830821) B1830821
theorem B5644237 : Blo 1219427 5644237 := bstep (se 3 (by rfl) ⟨1058294, by rfl⟩ : syracuseStep 5644237 = 2116589) B2116589
theorem B1220563 : Blo 1219427 1220563 := bstep (se 1 (by rfl) ⟨915422, by rfl⟩ : syracuseStep 1220563 = 1830845) B1830845
theorem B1220579 : Blo 1219427 1220579 := bstep (se 1 (by rfl) ⟨915434, by rfl⟩ : syracuseStep 1220579 = 1830869) B1830869
theorem B1220595 : Blo 1219427 1220595 := bstep (se 1 (by rfl) ⟨915446, by rfl⟩ : syracuseStep 1220595 = 1830893) B1830893
theorem B1220619 : Blo 1219427 1220619 := bstep (se 1 (by rfl) ⟨915464, by rfl⟩ : syracuseStep 1220619 = 1830929) B1830929
theorem B15630353 : Blo 1219427 15630353 := bstep (se 2 (by rfl) ⟨5861382, by rfl⟩ : syracuseStep 15630353 = 11722765) B11722765
theorem B1220631 : Blo 1219427 1220631 := bstep (se 1 (by rfl) ⟨915473, by rfl⟩ : syracuseStep 1220631 = 1830947) B1830947
theorem B1220651 : Blo 1219427 1220651 := bstep (se 1 (by rfl) ⟨915488, by rfl⟩ : syracuseStep 1220651 = 1830977) B1830977
theorem B1220663 : Blo 1219427 1220663 := bstep (se 1 (by rfl) ⟨915497, by rfl⟩ : syracuseStep 1220663 = 1830995) B1830995
theorem B17588299 : Blo 1219427 17588299 := bstep (se 1 (by rfl) ⟨13191224, by rfl⟩ : syracuseStep 17588299 = 26382449) B26382449
theorem B1220683 : Blo 1219427 1220683 := bstep (se 1 (by rfl) ⟨915512, by rfl⟩ : syracuseStep 1220683 = 1831025) B1831025
theorem B1220695 : Blo 1219427 1220695 := bstep (se 1 (by rfl) ⟨915521, by rfl⟩ : syracuseStep 1220695 = 1831043) B1831043
theorem B1220715 : Blo 1219427 1220715 := bstep (se 1 (by rfl) ⟨915536, by rfl⟩ : syracuseStep 1220715 = 1831073) B1831073
theorem B1220727 : Blo 1219427 1220727 := bstep (se 1 (by rfl) ⟨915545, by rfl⟩ : syracuseStep 1220727 = 1831091) B1831091
theorem B2744459 : Blo 1219427 2744459 := bstep (se 1 (by rfl) ⟨2058344, by rfl⟩ : syracuseStep 2744459 = 4116689) B4116689
theorem B1220747 : Blo 1219427 1220747 := bstep (se 1 (by rfl) ⟨915560, by rfl⟩ : syracuseStep 1220747 = 1831121) B1831121
theorem B2474135 : Blo 1219427 2474135 := bstep (se 1 (by rfl) ⟨1855601, by rfl⟩ : syracuseStep 2474135 = 3711203) B3711203
theorem B1220759 : Blo 1219427 1220759 := bstep (se 1 (by rfl) ⟨915569, by rfl⟩ : syracuseStep 1220759 = 1831139) B1831139
theorem B1220779 : Blo 1219427 1220779 := bstep (se 1 (by rfl) ⟨915584, by rfl⟩ : syracuseStep 1220779 = 1831169) B1831169
theorem B1220791 : Blo 1219427 1220791 := bstep (se 1 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 1220791 = 1831187) B1831187
theorem B2744513 : Blo 1219427 2744513 := bstep (se 2 (by rfl) ⟨1029192, by rfl⟩ : syracuseStep 2744513 = 2058385) B2058385
theorem B1220811 : Blo 1219427 1220811 := bstep (se 1 (by rfl) ⟨915608, by rfl⟩ : syracuseStep 1220811 = 1831217) B1831217
theorem B13902029 : Blo 1219427 13902029 := bstep (se 3 (by rfl) ⟨2606630, by rfl⟩ : syracuseStep 13902029 = 5213261) B5213261
theorem B1220823 : Blo 1219427 1220823 := bstep (se 1 (by rfl) ⟨915617, by rfl⟩ : syracuseStep 1220823 = 1831235) B1831235
theorem B3088601 : Blo 1219427 3088601 := bstep (se 2 (by rfl) ⟨1158225, by rfl⟩ : syracuseStep 3088601 = 2316451) B2316451
theorem B5865689 : Blo 1219427 5865689 := bstep (se 2 (by rfl) ⟨2199633, by rfl⟩ : syracuseStep 5865689 = 4399267) B4399267
theorem B5357789 : Blo 1219427 5357789 := bstep (se 3 (by rfl) ⟨1004585, by rfl⟩ : syracuseStep 5357789 = 2009171) B2009171
theorem B1220843 : Blo 1219427 1220843 := bstep (se 1 (by rfl) ⟨915632, by rfl⟩ : syracuseStep 1220843 = 1831265) B1831265
theorem B1220855 : Blo 1219427 1220855 := bstep (se 1 (by rfl) ⟨915641, by rfl⟩ : syracuseStep 1220855 = 1831283) B1831283
theorem B1220875 : Blo 1219427 1220875 := bstep (se 1 (by rfl) ⟨915656, by rfl⟩ : syracuseStep 1220875 = 1831313) B1831313
theorem B1220887 : Blo 1219427 1220887 := bstep (se 1 (by rfl) ⟨915665, by rfl⟩ : syracuseStep 1220887 = 1831331) B1831331
theorem B1220907 : Blo 1219427 1220907 := bstep (se 1 (by rfl) ⟨915680, by rfl⟩ : syracuseStep 1220907 = 1831361) B1831361
theorem B1220919 : Blo 1219427 1220919 := bstep (se 1 (by rfl) ⟨915689, by rfl⟩ : syracuseStep 1220919 = 1831379) B1831379
theorem B2474329 : Blo 1219427 2474329 := bstep (se 2 (by rfl) ⟨927873, by rfl⟩ : syracuseStep 2474329 = 1855747) B1855747
theorem B5210513 : Blo 1219427 5210513 := bstep (se 2 (by rfl) ⟨1953942, by rfl⟩ : syracuseStep 5210513 = 3907885) B3907885
theorem B2744729 : Blo 1219427 2744729 := bstep (se 2 (by rfl) ⟨1029273, by rfl⟩ : syracuseStep 2744729 = 2058547) B2058547
theorem B2474393 : Blo 1219427 2474393 := bstep (se 2 (by rfl) ⟨927897, by rfl⟩ : syracuseStep 2474393 = 1855795) B1855795
theorem B3473867 : Blo 1219427 3473867 := bstep (se 1 (by rfl) ⟨2605400, by rfl⟩ : syracuseStep 3473867 = 5210801) B5210801
theorem B9396685 : Blo 1219427 9396685 := bstep (se 3 (by rfl) ⟨1761878, by rfl⟩ : syracuseStep 9396685 = 3523757) B3523757
theorem B2744819 : Blo 1219427 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B2744855 : Blo 1219427 2744855 := bstep (se 1 (by rfl) ⟨2058641, by rfl⟩ : syracuseStep 2744855 = 4117283) B4117283
theorem B2745035 : Blo 1219427 2745035 := bstep (se 1 (by rfl) ⟨2058776, by rfl⟩ : syracuseStep 2745035 = 4117553) B4117553
theorem B2745089 : Blo 1219427 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B1303435 : Blo 1219427 1303435 := bstep (se 1 (by rfl) ⟨977576, by rfl⟩ : syracuseStep 1303435 = 1955153) B1955153
theorem B2745305 : Blo 1219427 2745305 := bstep (se 2 (by rfl) ⟨1029489, by rfl⟩ : syracuseStep 2745305 = 2058979) B2058979
theorem B23454755 : Blo 1219427 23454755 := bstep (se 1 (by rfl) ⟨17591066, by rfl⟩ : syracuseStep 23454755 = 35182133) B35182133
theorem B2745395 : Blo 1219427 2745395 := bstep (se 1 (by rfl) ⟨2059046, by rfl⟩ : syracuseStep 2745395 = 4118093) B4118093
theorem B5211211 : Blo 1219427 5211211 := bstep (se 1 (by rfl) ⟨3908408, by rfl⟩ : syracuseStep 5211211 = 7816817) B7816817
theorem B2745431 : Blo 1219427 2745431 := bstep (se 1 (by rfl) ⟨2059073, by rfl⟩ : syracuseStep 2745431 = 4118147) B4118147
theorem B9397399 : Blo 1219427 9397399 := bstep (se 1 (by rfl) ⟨7048049, by rfl⟩ : syracuseStep 9397399 = 14096099) B14096099
theorem B1737931 : Blo 1219427 1737931 := bstep (se 1 (by rfl) ⟨1303448, by rfl⟩ : syracuseStep 1737931 = 2606897) B2606897
theorem B2745611 : Blo 1219427 2745611 := bstep (se 1 (by rfl) ⟨2059208, by rfl⟩ : syracuseStep 2745611 = 4118417) B4118417
theorem B2745665 : Blo 1219427 2745665 := bstep (se 2 (by rfl) ⟨1029624, by rfl⟩ : syracuseStep 2745665 = 2059249) B2059249
theorem B5211485 : Blo 1219427 5211485 := bstep (se 3 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 5211485 = 1954307) B1954307
theorem B12387761 : Blo 1219427 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B6596113 : Blo 1219427 6596113 := bstep (se 2 (by rfl) ⟨2473542, by rfl⟩ : syracuseStep 6596113 = 4947085) B4947085
theorem B2745881 : Blo 1219427 2745881 := bstep (se 2 (by rfl) ⟨1029705, by rfl⟩ : syracuseStep 2745881 = 2059411) B2059411
theorem B4630061 : Blo 1219427 4630061 := bstep (se 3 (by rfl) ⟨868136, by rfl⟩ : syracuseStep 4630061 = 1736273) B1736273
theorem B10430045 : Blo 1219427 10430045 := bstep (se 3 (by rfl) ⟨1955633, by rfl⟩ : syracuseStep 10430045 = 3911267) B3911267
theorem B2745971 : Blo 1219427 2745971 := bstep (se 1 (by rfl) ⟨2059478, by rfl⟩ : syracuseStep 2745971 = 4118957) B4118957
theorem B2057879 : Blo 1219427 2057879 := bstep (se 1 (by rfl) ⟨1543409, by rfl⟩ : syracuseStep 2057879 = 3086819) B3086819
theorem B2746007 : Blo 1219427 2746007 := bstep (se 1 (by rfl) ⟨2059505, by rfl⟩ : syracuseStep 2746007 = 4119011) B4119011
theorem B5211827 : Blo 1219427 5211827 := bstep (se 1 (by rfl) ⟨3908870, by rfl⟩ : syracuseStep 5211827 = 7817741) B7817741
theorem B2058007 : Blo 1219427 2058007 := bstep (se 1 (by rfl) ⟨1543505, by rfl⟩ : syracuseStep 2058007 = 3087011) B3087011
theorem B8791843 : Blo 1219427 8791843 := bstep (se 1 (by rfl) ⟨6593882, by rfl⟩ : syracuseStep 8791843 = 13187765) B13187765
theorem B2746187 : Blo 1219427 2746187 := bstep (se 1 (by rfl) ⟨2059640, by rfl⟩ : syracuseStep 2746187 = 4119281) B4119281
theorem B3090251 : Blo 1219427 3090251 := bstep (se 1 (by rfl) ⟨2317688, by rfl⟩ : syracuseStep 3090251 = 4635377) B4635377
theorem B2746241 : Blo 1219427 2746241 := bstep (se 2 (by rfl) ⟨1029840, by rfl⟩ : syracuseStep 2746241 = 2059681) B2059681
theorem B2607041 : Blo 1219427 2607041 := bstep (se 2 (by rfl) ⟨977640, by rfl⟩ : syracuseStep 2607041 = 1955281) B1955281
theorem B2746457 : Blo 1219427 2746457 := bstep (se 2 (by rfl) ⟨1029921, by rfl⟩ : syracuseStep 2746457 = 2059843) B2059843
theorem B7424131 : Blo 1219427 7424131 := bstep (se 1 (by rfl) ⟨5568098, by rfl⟩ : syracuseStep 7424131 = 11136197) B11136197
theorem B2746547 : Blo 1219427 2746547 := bstep (se 1 (by rfl) ⟨2059910, by rfl⟩ : syracuseStep 2746547 = 4119821) B4119821
theorem B2746583 : Blo 1219427 2746583 := bstep (se 1 (by rfl) ⟨2059937, by rfl⟩ : syracuseStep 2746583 = 4119875) B4119875
theorem B4761821 : Blo 1219427 4761821 := bstep (se 3 (by rfl) ⟨892841, by rfl⟩ : syracuseStep 4761821 = 1785683) B1785683
theorem B2607383 : Blo 1219427 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B1829195 : Blo 1219427 1829195 := bstep (se 1 (by rfl) ⟨1371896, by rfl⟩ : syracuseStep 1829195 = 2743793) B2743793
theorem B1829207 : Blo 1219427 1829207 := bstep (se 1 (by rfl) ⟨1371905, by rfl⟩ : syracuseStep 1829207 = 2743811) B2743811
theorem B2197847 : Blo 1219427 2197847 := bstep (se 1 (by rfl) ⟨1648385, by rfl⟩ : syracuseStep 2197847 = 3296771) B3296771
theorem B6179165 : Blo 1219427 6179165 := bstep (se 3 (by rfl) ⟨1158593, by rfl⟩ : syracuseStep 6179165 = 2317187) B2317187
theorem B2058635 : Blo 1219427 2058635 := bstep (se 1 (by rfl) ⟨1543976, by rfl⟩ : syracuseStep 2058635 = 3087953) B3087953
theorem B2746763 : Blo 1219427 2746763 := bstep (se 1 (by rfl) ⟨2060072, by rfl⟩ : syracuseStep 2746763 = 4120145) B4120145
theorem B10570135 : Blo 1219427 10570135 := bstep (se 1 (by rfl) ⟨7927601, by rfl⟩ : syracuseStep 10570135 = 15855203) B15855203
theorem B1829273 : Blo 1219427 1829273 := bstep (se 2 (by rfl) ⟨685977, by rfl⟩ : syracuseStep 1829273 = 1371955) B1371955
theorem B2746817 : Blo 1219427 2746817 := bstep (se 2 (by rfl) ⟨1030056, by rfl⟩ : syracuseStep 2746817 = 2060113) B2060113
theorem B1829387 : Blo 1219427 1829387 := bstep (se 1 (by rfl) ⟨1372040, by rfl⟩ : syracuseStep 1829387 = 2744081) B2744081
theorem B2058763 : Blo 1219427 2058763 := bstep (se 1 (by rfl) ⟨1544072, by rfl⟩ : syracuseStep 2058763 = 3088145) B3088145
theorem B1829399 : Blo 1219427 1829399 := bstep (se 1 (by rfl) ⟨1372049, by rfl⟩ : syracuseStep 1829399 = 2744099) B2744099
theorem B1485335 : Blo 1219427 1485335 := bstep (se 1 (by rfl) ⟨1114001, by rfl⟩ : syracuseStep 1485335 = 2228003) B2228003
theorem B6949421 : Blo 1219427 6949421 := bstep (se 3 (by rfl) ⟨1303016, by rfl⟩ : syracuseStep 6949421 = 2606033) B2606033
theorem B8792651 : Blo 1219427 8792651 := bstep (se 1 (by rfl) ⟨6594488, by rfl⟩ : syracuseStep 8792651 = 13188977) B13188977
theorem B1829465 : Blo 1219427 1829465 := bstep (se 2 (by rfl) ⟨686049, by rfl⟩ : syracuseStep 1829465 = 1372099) B1372099
theorem B2058905 : Blo 1219427 2058905 := bstep (se 2 (by rfl) ⟨772089, by rfl⟩ : syracuseStep 2058905 = 1544179) B1544179
theorem B2747033 : Blo 1219427 2747033 := bstep (se 2 (by rfl) ⟨1030137, by rfl⟩ : syracuseStep 2747033 = 2060275) B2060275
theorem B19303093 : Blo 1219427 19303093 := bstep (se 5 (by rfl) ⟨904832, by rfl⟩ : syracuseStep 19303093 = 1809665) B1809665
theorem B1829579 : Blo 1219427 1829579 := bstep (se 1 (by rfl) ⟨1372184, by rfl⟩ : syracuseStep 1829579 = 2744369) B2744369
theorem B1829591 : Blo 1219427 1829591 := bstep (se 1 (by rfl) ⟨1372193, by rfl⟩ : syracuseStep 1829591 = 2744387) B2744387
theorem B1829657 : Blo 1219427 1829657 := bstep (se 2 (by rfl) ⟨686121, by rfl⟩ : syracuseStep 1829657 = 1372243) B1372243
theorem B2059033 : Blo 1219427 2059033 := bstep (se 2 (by rfl) ⟨772137, by rfl⟩ : syracuseStep 2059033 = 1544275) B1544275
theorem B3476317 : Blo 1219427 3476317 := bstep (se 3 (by rfl) ⟨651809, by rfl⟩ : syracuseStep 3476317 = 1303619) B1303619
theorem B1829771 : Blo 1219427 1829771 := bstep (se 1 (by rfl) ⟨1372328, by rfl⟩ : syracuseStep 1829771 = 2744657) B2744657
theorem B1829783 : Blo 1219427 1829783 := bstep (se 1 (by rfl) ⟨1372337, by rfl⟩ : syracuseStep 1829783 = 2744675) B2744675
theorem B2198423 : Blo 1219427 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B4631489 : Blo 1219427 4631489 := bstep (se 2 (by rfl) ⟨1736808, by rfl⟩ : syracuseStep 4631489 = 3473617) B3473617
theorem B1829849 : Blo 1219427 1829849 := bstep (se 2 (by rfl) ⟨686193, by rfl⟩ : syracuseStep 1829849 = 1372387) B1372387
theorem B22866961 : Blo 1219427 22866961 := bstep (se 2 (by rfl) ⟨8575110, by rfl⟩ : syracuseStep 22866961 = 17150221) B17150221
theorem B1829963 : Blo 1219427 1829963 := bstep (se 1 (by rfl) ⟨1372472, by rfl⟩ : syracuseStep 1829963 = 2744945) B2744945
theorem B1829975 : Blo 1219427 1829975 := bstep (se 1 (by rfl) ⟨1372481, by rfl⟩ : syracuseStep 1829975 = 2744963) B2744963
theorem B1830041 : Blo 1219427 1830041 := bstep (se 2 (by rfl) ⟨686265, by rfl⟩ : syracuseStep 1830041 = 1372531) B1372531
theorem B7818457 : Blo 1219427 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B1830155 : Blo 1219427 1830155 := bstep (se 1 (by rfl) ⟨1372616, by rfl⟩ : syracuseStep 1830155 = 2745233) B2745233
theorem B1830167 : Blo 1219427 1830167 := bstep (se 1 (by rfl) ⟨1372625, by rfl⟩ : syracuseStep 1830167 = 2745251) B2745251
theorem B2059607 : Blo 1219427 2059607 := bstep (se 1 (by rfl) ⟨1544705, by rfl⟩ : syracuseStep 2059607 = 3089411) B3089411
theorem B1830233 : Blo 1219427 1830233 := bstep (se 2 (by rfl) ⟨686337, by rfl⟩ : syracuseStep 1830233 = 1372675) B1372675
theorem B2198935 : Blo 1219427 2198935 := bstep (se 1 (by rfl) ⟨1649201, by rfl⟩ : syracuseStep 2198935 = 3298403) B3298403
theorem B1543627 : Blo 1219427 1543627 := bstep (se 1 (by rfl) ⟨1157720, by rfl⟩ : syracuseStep 1543627 = 2315441) B2315441
theorem B1830347 : Blo 1219427 1830347 := bstep (se 1 (by rfl) ⟨1372760, by rfl⟩ : syracuseStep 1830347 = 2745521) B2745521
theorem B1830359 : Blo 1219427 1830359 := bstep (se 1 (by rfl) ⟨1372769, by rfl⟩ : syracuseStep 1830359 = 2745539) B2745539
theorem B2198999 : Blo 1219427 2198999 := bstep (se 1 (by rfl) ⟨1649249, by rfl⟩ : syracuseStep 2198999 = 3298499) B3298499
theorem B2059735 : Blo 1219427 2059735 := bstep (se 1 (by rfl) ⟨1544801, by rfl⟩ : syracuseStep 2059735 = 3089603) B3089603
theorem B4115933 : Blo 1219427 4115933 := bstep (se 3 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 4115933 = 1543475) B1543475
theorem B1830425 : Blo 1219427 1830425 := bstep (se 2 (by rfl) ⟨686409, by rfl⟩ : syracuseStep 1830425 = 1372819) B1372819
theorem B1830539 : Blo 1219427 1830539 := bstep (se 1 (by rfl) ⟨1372904, by rfl⟩ : syracuseStep 1830539 = 2745809) B2745809
theorem B1830551 : Blo 1219427 1830551 := bstep (se 1 (by rfl) ⟨1372913, by rfl⟩ : syracuseStep 1830551 = 2745827) B2745827
theorem B1830617 : Blo 1219427 1830617 := bstep (se 2 (by rfl) ⟨686481, by rfl⟩ : syracuseStep 1830617 = 1372963) B1372963
theorem B1371883 : Blo 1219427 1371883 := bstep (se 1 (by rfl) ⟨1028912, by rfl⟩ : syracuseStep 1371883 = 2057825) B2057825
theorem B1830731 : Blo 1219427 1830731 := bstep (se 1 (by rfl) ⟨1373048, by rfl⟩ : syracuseStep 1830731 = 2746097) B2746097
theorem B1371991 : Blo 1219427 1371991 := bstep (se 1 (by rfl) ⟨1028993, by rfl⟩ : syracuseStep 1371991 = 2057987) B2057987
theorem B1830743 : Blo 1219427 1830743 := bstep (se 1 (by rfl) ⟨1373057, by rfl⟩ : syracuseStep 1830743 = 2746115) B2746115
theorem B1830809 : Blo 1219427 1830809 := bstep (se 2 (by rfl) ⟨686553, by rfl⟩ : syracuseStep 1830809 = 1373107) B1373107
theorem B1372171 : Blo 1219427 1372171 := bstep (se 1 (by rfl) ⟨1029128, by rfl⟩ : syracuseStep 1372171 = 2058257) B2058257
theorem B1830923 : Blo 1219427 1830923 := bstep (se 1 (by rfl) ⟨1373192, by rfl⟩ : syracuseStep 1830923 = 2746385) B2746385
theorem B45117461 : Blo 1219427 45117461 := bstep (se 6 (by rfl) ⟨1057440, by rfl⟩ : syracuseStep 45117461 = 2114881) B2114881
theorem B1830935 : Blo 1219427 1830935 := bstep (se 1 (by rfl) ⟨1373201, by rfl⟩ : syracuseStep 1830935 = 2746403) B2746403
theorem B5214253 : Blo 1219427 5214253 := bstep (se 3 (by rfl) ⟨977672, by rfl⟩ : syracuseStep 5214253 = 1955345) B1955345
theorem B1831001 : Blo 1219427 1831001 := bstep (se 2 (by rfl) ⟨686625, by rfl⟩ : syracuseStep 1831001 = 1373251) B1373251
theorem B1372279 : Blo 1219427 1372279 := bstep (se 1 (by rfl) ⟨1029209, by rfl⟩ : syracuseStep 1372279 = 2058419) B2058419
theorem B1831115 : Blo 1219427 1831115 := bstep (se 1 (by rfl) ⟨1373336, by rfl⟩ : syracuseStep 1831115 = 2746673) B2746673
theorem B1831127 : Blo 1219427 1831127 := bstep (se 1 (by rfl) ⟨1373345, by rfl⟩ : syracuseStep 1831127 = 2746691) B2746691
theorem B8352017 : Blo 1219427 8352017 := bstep (se 2 (by rfl) ⟨3132006, by rfl⟩ : syracuseStep 8352017 = 6264013) B6264013
theorem B1831193 : Blo 1219427 1831193 := bstep (se 2 (by rfl) ⟨686697, by rfl⟩ : syracuseStep 1831193 = 1373395) B1373395
theorem B1372459 : Blo 1219427 1372459 := bstep (se 1 (by rfl) ⟨1029344, by rfl⟩ : syracuseStep 1372459 = 2058689) B2058689
theorem B1831307 : Blo 1219427 1831307 := bstep (se 1 (by rfl) ⟨1373480, by rfl⟩ : syracuseStep 1831307 = 2746961) B2746961
theorem B4632977 : Blo 1219427 4632977 := bstep (se 2 (by rfl) ⟨1737366, by rfl⟩ : syracuseStep 4632977 = 3474733) B3474733
theorem B1954199 : Blo 1219427 1954199 := bstep (se 1 (by rfl) ⟨1465649, by rfl⟩ : syracuseStep 1954199 = 2931299) B2931299
theorem B1372567 : Blo 1219427 1372567 := bstep (se 1 (by rfl) ⟨1029425, by rfl⟩ : syracuseStep 1372567 = 2058851) B2058851
theorem B1544599 : Blo 1219427 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B1831319 : Blo 1219427 1831319 := bstep (se 1 (by rfl) ⟨1373489, by rfl⟩ : syracuseStep 1831319 = 2746979) B2746979
theorem B2347481 : Blo 1219427 2347481 := bstep (se 2 (by rfl) ⟨880305, by rfl⟩ : syracuseStep 2347481 = 1760611) B1760611
theorem B1831385 : Blo 1219427 1831385 := bstep (se 2 (by rfl) ⟨686769, by rfl⟩ : syracuseStep 1831385 = 1373539) B1373539
theorem B4117067 : Blo 1219427 4117067 := bstep (se 1 (by rfl) ⟨3087800, by rfl⟩ : syracuseStep 4117067 = 6175601) B6175601
theorem B1372747 : Blo 1219427 1372747 := bstep (se 1 (by rfl) ⟨1029560, by rfl⟩ : syracuseStep 1372747 = 2059121) B2059121
theorem B3568279 : Blo 1219427 3568279 := bstep (se 1 (by rfl) ⟨2676209, by rfl⟩ : syracuseStep 3568279 = 5352419) B5352419
theorem B11285171 : Blo 1219427 11285171 := bstep (se 1 (by rfl) ⟨8463878, by rfl⟩ : syracuseStep 11285171 = 16927757) B16927757
theorem B1372855 : Blo 1219427 1372855 := bstep (se 1 (by rfl) ⟨1029641, by rfl⟩ : syracuseStep 1372855 = 2059283) B2059283
theorem B4395865 : Blo 1219427 4395865 := bstep (se 2 (by rfl) ⟨1648449, by rfl⟩ : syracuseStep 4395865 = 3296899) B3296899
theorem B4117337 : Blo 1219427 4117337 := bstep (se 2 (by rfl) ⟨1544001, by rfl⟩ : syracuseStep 4117337 = 3088003) B3088003
theorem B4633433 : Blo 1219427 4633433 := bstep (se 2 (by rfl) ⟨1737537, by rfl⟩ : syracuseStep 4633433 = 3475075) B3475075
theorem B1373035 : Blo 1219427 1373035 := bstep (se 1 (by rfl) ⟨1029776, by rfl⟩ : syracuseStep 1373035 = 2059553) B2059553
theorem B2315137 : Blo 1219427 2315137 := bstep (se 2 (by rfl) ⟨868176, by rfl⟩ : syracuseStep 2315137 = 1736353) B1736353
theorem B1954763 : Blo 1219427 1954763 := bstep (se 1 (by rfl) ⟨1466072, by rfl⟩ : syracuseStep 1954763 = 2932145) B2932145
theorem B10425293 : Blo 1219427 10425293 := bstep (se 3 (by rfl) ⟨1954742, by rfl⟩ : syracuseStep 10425293 = 3909485) B3909485
theorem B1373143 : Blo 1219427 1373143 := bstep (se 1 (by rfl) ⟨1029857, by rfl⟩ : syracuseStep 1373143 = 2059715) B2059715
theorem B6173657 : Blo 1219427 6173657 := bstep (se 2 (by rfl) ⟨2315121, by rfl⟩ : syracuseStep 6173657 = 4630243) B4630243
theorem B4633645 : Blo 1219427 4633645 := bstep (se 3 (by rfl) ⟨868808, by rfl⟩ : syracuseStep 4633645 = 1737617) B1737617
theorem B1373323 : Blo 1219427 1373323 := bstep (se 1 (by rfl) ⟨1029992, by rfl⟩ : syracuseStep 1373323 = 2059985) B2059985
theorem B9270449 : Blo 1219427 9270449 := bstep (se 2 (by rfl) ⟨3476418, by rfl⟩ : syracuseStep 9270449 = 6952837) B6952837
theorem B2315479 : Blo 1219427 2315479 := bstep (se 1 (by rfl) ⟨1736609, by rfl⟩ : syracuseStep 2315479 = 3473219) B3473219
theorem B1373431 : Blo 1219427 1373431 := bstep (se 1 (by rfl) ⟨1030073, by rfl⟩ : syracuseStep 1373431 = 2060147) B2060147
theorem B7525649 : Blo 1219427 7525649 := bstep (se 2 (by rfl) ⟨2822118, by rfl⟩ : syracuseStep 7525649 = 5644237) B5644237
theorem B4633949 : Blo 1219427 4633949 := bstep (se 3 (by rfl) ⟨868865, by rfl⟩ : syracuseStep 4633949 = 1737731) B1737731
theorem B6264215 : Blo 1219427 6264215 := bstep (se 1 (by rfl) ⟨4698161, by rfl⟩ : syracuseStep 6264215 = 9396323) B9396323
theorem B2315699 : Blo 1219427 2315699 := bstep (se 1 (by rfl) ⟨1736774, by rfl⟩ : syracuseStep 2315699 = 3473549) B3473549
theorem B4118039 : Blo 1219427 4118039 := bstep (se 1 (by rfl) ⟨3088529, by rfl⟩ : syracuseStep 4118039 = 6177059) B6177059
theorem B2782745 : Blo 1219427 2782745 := bstep (se 2 (by rfl) ⟨1043529, by rfl⟩ : syracuseStep 2782745 = 2087059) B2087059
theorem B2315927 : Blo 1219427 2315927 := bstep (se 1 (by rfl) ⟨1736945, by rfl⟩ : syracuseStep 2315927 = 3473891) B3473891
theorem B9270935 : Blo 1219427 9270935 := bstep (se 1 (by rfl) ⟨6953201, by rfl⟩ : syracuseStep 9270935 = 13906403) B13906403
theorem B7534259 : Blo 1219427 7534259 := bstep (se 1 (by rfl) ⟨5650694, by rfl⟩ : syracuseStep 7534259 = 11301389) B11301389
theorem B2316185 : Blo 1219427 2316185 := bstep (se 2 (by rfl) ⟨868569, by rfl⟩ : syracuseStep 2316185 = 1737139) B1737139
theorem B4118579 : Blo 1219427 4118579 := bstep (se 1 (by rfl) ⟨3088934, by rfl⟩ : syracuseStep 4118579 = 6177869) B6177869
theorem B4175923 : Blo 1219427 4175923 := bstep (se 1 (by rfl) ⟨3131942, by rfl⟩ : syracuseStep 4175923 = 6263885) B6263885
theorem B6953111 : Blo 1219427 6953111 := bstep (se 1 (by rfl) ⟨5214833, by rfl⟩ : syracuseStep 6953111 = 10429667) B10429667
theorem B4397249 : Blo 1219427 4397249 := bstep (se 2 (by rfl) ⟨1648968, by rfl⟩ : syracuseStep 4397249 = 3297937) B3297937
theorem B5577005 : Blo 1219427 5577005 := bstep (se 3 (by rfl) ⟨1045688, by rfl⟩ : syracuseStep 5577005 = 2091377) B2091377
theorem B2316595 : Blo 1219427 2316595 := bstep (se 1 (by rfl) ⟨1737446, by rfl⟩ : syracuseStep 2316595 = 3474893) B3474893
theorem B4118849 : Blo 1219427 4118849 := bstep (se 2 (by rfl) ⟨1544568, by rfl⟩ : syracuseStep 4118849 = 3089137) B3089137
theorem B13195811 : Blo 1219427 13195811 := bstep (se 1 (by rfl) ⟨9896858, by rfl⟩ : syracuseStep 13195811 = 19793717) B19793717
theorem B6175277 : Blo 1219427 6175277 := bstep (se 3 (by rfl) ⟨1157864, by rfl⟩ : syracuseStep 6175277 = 2315729) B2315729
theorem B1464971 : Blo 1219427 1464971 := bstep (se 1 (by rfl) ⟨1098728, by rfl⟩ : syracuseStep 1464971 = 2197457) B2197457
theorem B2317081 : Blo 1219427 2317081 := bstep (se 2 (by rfl) ⟨868905, by rfl⟩ : syracuseStep 2317081 = 1737811) B1737811
theorem B6593345 : Blo 1219427 6593345 := bstep (se 2 (by rfl) ⟨2472504, by rfl⟩ : syracuseStep 6593345 = 4945009) B4945009
theorem B3087193 : Blo 1219427 3087193 := bstep (se 2 (by rfl) ⟨1157697, by rfl⟩ : syracuseStep 3087193 = 2315395) B2315395
theorem B4119389 : Blo 1219427 4119389 := bstep (se 3 (by rfl) ⟨772385, by rfl⟩ : syracuseStep 4119389 = 1544771) B1544771
theorem B1219435 : Blo 1219427 1219435 := bstep (se 1 (by rfl) ⟨914576, by rfl⟩ : syracuseStep 1219435 = 1829153) B1829153
theorem B1219447 : Blo 1219427 1219447 := bstep (se 1 (by rfl) ⟨914585, by rfl⟩ : syracuseStep 1219447 = 1829171) B1829171
theorem B1219467 : Blo 1219427 1219467 := bstep (se 1 (by rfl) ⟨914600, by rfl⟩ : syracuseStep 1219467 = 1829201) B1829201
theorem B1219479 : Blo 1219427 1219479 := bstep (se 1 (by rfl) ⟨914609, by rfl⟩ : syracuseStep 1219479 = 1829219) B1829219
theorem B1219499 : Blo 1219427 1219499 := bstep (se 1 (by rfl) ⟨914624, by rfl⟩ : syracuseStep 1219499 = 1829249) B1829249
theorem B1219511 : Blo 1219427 1219511 := bstep (se 1 (by rfl) ⟨914633, by rfl⟩ : syracuseStep 1219511 = 1829267) B1829267
theorem B1219531 : Blo 1219427 1219531 := bstep (se 1 (by rfl) ⟨914648, by rfl⟩ : syracuseStep 1219531 = 1829297) B1829297
theorem B1219543 : Blo 1219427 1219543 := bstep (se 1 (by rfl) ⟨914657, by rfl⟩ : syracuseStep 1219543 = 1829315) B1829315
theorem B1219563 : Blo 1219427 1219563 := bstep (se 1 (by rfl) ⟨914672, by rfl⟩ : syracuseStep 1219563 = 1829345) B1829345
theorem B1219575 : Blo 1219427 1219575 := bstep (se 1 (by rfl) ⟨914681, by rfl⟩ : syracuseStep 1219575 = 1829363) B1829363
theorem B1219595 : Blo 1219427 1219595 := bstep (se 1 (by rfl) ⟨914696, by rfl⟩ : syracuseStep 1219595 = 1829393) B1829393
theorem B1219607 : Blo 1219427 1219607 := bstep (se 1 (by rfl) ⟨914705, by rfl⟩ : syracuseStep 1219607 = 1829411) B1829411
theorem B1219627 : Blo 1219427 1219627 := bstep (se 1 (by rfl) ⟨914720, by rfl⟩ : syracuseStep 1219627 = 1829441) B1829441
theorem B1219639 : Blo 1219427 1219639 := bstep (se 1 (by rfl) ⟨914729, by rfl⟩ : syracuseStep 1219639 = 1829459) B1829459
theorem B9387083 : Blo 1219427 9387083 := bstep (se 1 (by rfl) ⟨7040312, by rfl⟩ : syracuseStep 9387083 = 14080625) B14080625
theorem B1219659 : Blo 1219427 1219659 := bstep (se 1 (by rfl) ⟨914744, by rfl⟩ : syracuseStep 1219659 = 1829489) B1829489
theorem B1219671 : Blo 1219427 1219671 := bstep (se 1 (by rfl) ⟨914753, by rfl⟩ : syracuseStep 1219671 = 1829507) B1829507
theorem B1219691 : Blo 1219427 1219691 := bstep (se 1 (by rfl) ⟨914768, by rfl⟩ : syracuseStep 1219691 = 1829537) B1829537
theorem B1219703 : Blo 1219427 1219703 := bstep (se 1 (by rfl) ⟨914777, by rfl⟩ : syracuseStep 1219703 = 1829555) B1829555
theorem B1219723 : Blo 1219427 1219723 := bstep (se 1 (by rfl) ⟨914792, by rfl⟩ : syracuseStep 1219723 = 1829585) B1829585
theorem B1219735 : Blo 1219427 1219735 := bstep (se 1 (by rfl) ⟨914801, by rfl⟩ : syracuseStep 1219735 = 1829603) B1829603
theorem B1465495 : Blo 1219427 1465495 := bstep (se 1 (by rfl) ⟨1099121, by rfl⟩ : syracuseStep 1465495 = 2198243) B2198243
theorem B1219755 : Blo 1219427 1219755 := bstep (se 1 (by rfl) ⟨914816, by rfl⟩ : syracuseStep 1219755 = 1829633) B1829633
theorem B1219767 : Blo 1219427 1219767 := bstep (se 1 (by rfl) ⟨914825, by rfl⟩ : syracuseStep 1219767 = 1829651) B1829651
theorem B1219787 : Blo 1219427 1219787 := bstep (se 1 (by rfl) ⟨914840, by rfl⟩ : syracuseStep 1219787 = 1829681) B1829681
theorem B1219799 : Blo 1219427 1219799 := bstep (se 1 (by rfl) ⟨914849, by rfl⟩ : syracuseStep 1219799 = 1829699) B1829699
theorem B2473177 : Blo 1219427 2473177 := bstep (se 2 (by rfl) ⟨927441, by rfl⟩ : syracuseStep 2473177 = 1854883) B1854883
theorem B1219819 : Blo 1219427 1219819 := bstep (se 1 (by rfl) ⟨914864, by rfl⟩ : syracuseStep 1219819 = 1829729) B1829729
theorem B1219831 : Blo 1219427 1219831 := bstep (se 1 (by rfl) ⟨914873, by rfl⟩ : syracuseStep 1219831 = 1829747) B1829747
theorem B1219851 : Blo 1219427 1219851 := bstep (se 1 (by rfl) ⟨914888, by rfl⟩ : syracuseStep 1219851 = 1829777) B1829777
theorem B1219863 : Blo 1219427 1219863 := bstep (se 1 (by rfl) ⟨914897, by rfl⟩ : syracuseStep 1219863 = 1829795) B1829795
theorem B1219883 : Blo 1219427 1219883 := bstep (se 1 (by rfl) ⟨914912, by rfl⟩ : syracuseStep 1219883 = 1829825) B1829825
theorem B1219895 : Blo 1219427 1219895 := bstep (se 1 (by rfl) ⟨914921, by rfl⟩ : syracuseStep 1219895 = 1829843) B1829843
theorem B1219915 : Blo 1219427 1219915 := bstep (se 1 (by rfl) ⟨914936, by rfl⟩ : syracuseStep 1219915 = 1829873) B1829873
theorem B2317643 : Blo 1219427 2317643 := bstep (se 1 (by rfl) ⟨1738232, by rfl⟩ : syracuseStep 2317643 = 3476465) B3476465
theorem B1219927 : Blo 1219427 1219927 := bstep (se 1 (by rfl) ⟨914945, by rfl⟩ : syracuseStep 1219927 = 1829891) B1829891
theorem B1219947 : Blo 1219427 1219947 := bstep (se 1 (by rfl) ⟨914960, by rfl⟩ : syracuseStep 1219947 = 1829921) B1829921
theorem B1219959 : Blo 1219427 1219959 := bstep (se 1 (by rfl) ⟨914969, by rfl⟩ : syracuseStep 1219959 = 1829939) B1829939
theorem B1219979 : Blo 1219427 1219979 := bstep (se 1 (by rfl) ⟨914984, by rfl⟩ : syracuseStep 1219979 = 1829969) B1829969
theorem B1219991 : Blo 1219427 1219991 := bstep (se 1 (by rfl) ⟨914993, by rfl⟩ : syracuseStep 1219991 = 1829987) B1829987
theorem B1220011 : Blo 1219427 1220011 := bstep (se 1 (by rfl) ⟨915008, by rfl⟩ : syracuseStep 1220011 = 1830017) B1830017
theorem B1220023 : Blo 1219427 1220023 := bstep (se 1 (by rfl) ⟨915017, by rfl⟩ : syracuseStep 1220023 = 1830035) B1830035
theorem B1220043 : Blo 1219427 1220043 := bstep (se 1 (by rfl) ⟨915032, by rfl⟩ : syracuseStep 1220043 = 1830065) B1830065
theorem B1220055 : Blo 1219427 1220055 := bstep (se 1 (by rfl) ⟨915041, by rfl⟩ : syracuseStep 1220055 = 1830083) B1830083
theorem B1220075 : Blo 1219427 1220075 := bstep (se 1 (by rfl) ⟨915056, by rfl⟩ : syracuseStep 1220075 = 1830113) B1830113
theorem B1220087 : Blo 1219427 1220087 := bstep (se 1 (by rfl) ⟨915065, by rfl⟩ : syracuseStep 1220087 = 1830131) B1830131
theorem B2317825 : Blo 1219427 2317825 := bstep (se 2 (by rfl) ⟨869184, by rfl⟩ : syracuseStep 2317825 = 1738369) B1738369
theorem B1220107 : Blo 1219427 1220107 := bstep (se 1 (by rfl) ⟨915080, by rfl⟩ : syracuseStep 1220107 = 1830161) B1830161
theorem B1220119 : Blo 1219427 1220119 := bstep (se 1 (by rfl) ⟨915089, by rfl⟩ : syracuseStep 1220119 = 1830179) B1830179
theorem B1220139 : Blo 1219427 1220139 := bstep (se 1 (by rfl) ⟨915104, by rfl⟩ : syracuseStep 1220139 = 1830209) B1830209
theorem B1220151 : Blo 1219427 1220151 := bstep (se 1 (by rfl) ⟨915113, by rfl⟩ : syracuseStep 1220151 = 1830227) B1830227
theorem B2743883 : Blo 1219427 2743883 := bstep (se 1 (by rfl) ⟨2057912, by rfl⟩ : syracuseStep 2743883 = 4115825) B4115825
theorem B1220171 : Blo 1219427 1220171 := bstep (se 1 (by rfl) ⟨915128, by rfl⟩ : syracuseStep 1220171 = 1830257) B1830257
theorem B1220183 : Blo 1219427 1220183 := bstep (se 1 (by rfl) ⟨915137, by rfl⟩ : syracuseStep 1220183 = 1830275) B1830275
theorem B1220203 : Blo 1219427 1220203 := bstep (se 1 (by rfl) ⟨915152, by rfl⟩ : syracuseStep 1220203 = 1830305) B1830305
theorem B1220215 : Blo 1219427 1220215 := bstep (se 1 (by rfl) ⟨915161, by rfl⟩ : syracuseStep 1220215 = 1830323) B1830323
theorem B2743937 : Blo 1219427 2743937 := bstep (se 2 (by rfl) ⟨1028976, by rfl⟩ : syracuseStep 2743937 = 2057953) B2057953
theorem B2604683 : Blo 1219427 2604683 := bstep (se 1 (by rfl) ⟨1953512, by rfl⟩ : syracuseStep 2604683 = 3907025) B3907025
theorem B1220235 : Blo 1219427 1220235 := bstep (se 1 (by rfl) ⟨915176, by rfl⟩ : syracuseStep 1220235 = 1830353) B1830353
theorem B3473047 : Blo 1219427 3473047 := bstep (se 1 (by rfl) ⟨2604785, by rfl⟩ : syracuseStep 3473047 = 5209571) B5209571
theorem B1220247 : Blo 1219427 1220247 := bstep (se 1 (by rfl) ⟨915185, by rfl⟩ : syracuseStep 1220247 = 1830371) B1830371
theorem B2932375 : Blo 1219427 2932375 := bstep (se 1 (by rfl) ⟨2199281, by rfl⟩ : syracuseStep 2932375 = 4398563) B4398563
theorem B1220267 : Blo 1219427 1220267 := bstep (se 1 (by rfl) ⟨915200, by rfl⟩ : syracuseStep 1220267 = 1830401) B1830401
theorem B1220279 : Blo 1219427 1220279 := bstep (se 1 (by rfl) ⟨915209, by rfl⟩ : syracuseStep 1220279 = 1830419) B1830419
theorem B1220299 : Blo 1219427 1220299 := bstep (se 1 (by rfl) ⟨915224, by rfl⟩ : syracuseStep 1220299 = 1830449) B1830449
theorem B1220311 : Blo 1219427 1220311 := bstep (se 1 (by rfl) ⟨915233, by rfl⟩ : syracuseStep 1220311 = 1830467) B1830467
theorem B1220331 : Blo 1219427 1220331 := bstep (se 1 (by rfl) ⟨915248, by rfl⟩ : syracuseStep 1220331 = 1830497) B1830497
theorem B1220343 : Blo 1219427 1220343 := bstep (se 1 (by rfl) ⟨915257, by rfl⟩ : syracuseStep 1220343 = 1830515) B1830515
theorem B1220363 : Blo 1219427 1220363 := bstep (se 1 (by rfl) ⟨915272, by rfl⟩ : syracuseStep 1220363 = 1830545) B1830545
theorem B5209879 : Blo 1219427 5209879 := bstep (se 1 (by rfl) ⟨3907409, by rfl⟩ : syracuseStep 5209879 = 7814819) B7814819
theorem B1220375 : Blo 1219427 1220375 := bstep (se 1 (by rfl) ⟨915281, by rfl⟩ : syracuseStep 1220375 = 1830563) B1830563
theorem B1736473 : Blo 1219427 1736473 := bstep (se 2 (by rfl) ⟨651177, by rfl⟩ : syracuseStep 1736473 = 1302355) B1302355
theorem B1220395 : Blo 1219427 1220395 := bstep (se 1 (by rfl) ⟨915296, by rfl⟩ : syracuseStep 1220395 = 1830593) B1830593
theorem B1220407 : Blo 1219427 1220407 := bstep (se 1 (by rfl) ⟨915305, by rfl⟩ : syracuseStep 1220407 = 1830611) B1830611
theorem B10026827 : Blo 1219427 10026827 := bstep (se 1 (by rfl) ⟨7520120, by rfl⟩ : syracuseStep 10026827 = 15040241) B15040241
theorem B1220427 : Blo 1219427 1220427 := bstep (se 1 (by rfl) ⟨915320, by rfl⟩ : syracuseStep 1220427 = 1830641) B1830641
theorem B1220439 : Blo 1219427 1220439 := bstep (se 1 (by rfl) ⟨915329, by rfl⟩ : syracuseStep 1220439 = 1830659) B1830659
theorem B2744153 : Blo 1219427 2744153 := bstep (se 2 (by rfl) ⟨1029057, by rfl⟩ : syracuseStep 2744153 = 2058115) B2058115
theorem B1220459 : Blo 1219427 1220459 := bstep (se 1 (by rfl) ⟨915344, by rfl⟩ : syracuseStep 1220459 = 1830689) B1830689
theorem B1220471 : Blo 1219427 1220471 := bstep (se 1 (by rfl) ⟨915353, by rfl⟩ : syracuseStep 1220471 = 1830707) B1830707
theorem B1220491 : Blo 1219427 1220491 := bstep (se 1 (by rfl) ⟨915368, by rfl⟩ : syracuseStep 1220491 = 1830737) B1830737
theorem B1220503 : Blo 1219427 1220503 := bstep (se 1 (by rfl) ⟨915377, by rfl⟩ : syracuseStep 1220503 = 1830755) B1830755
theorem B1220523 : Blo 1219427 1220523 := bstep (se 1 (by rfl) ⟨915392, by rfl⟩ : syracuseStep 1220523 = 1830785) B1830785
theorem B2744243 : Blo 1219427 2744243 := bstep (se 1 (by rfl) ⟨2058182, by rfl⟩ : syracuseStep 2744243 = 4116365) B4116365
theorem B3088307 : Blo 1219427 3088307 := bstep (se 1 (by rfl) ⟨2316230, by rfl⟩ : syracuseStep 3088307 = 4632461) B4632461
theorem B2473907 : Blo 1219427 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B1220535 : Blo 1219427 1220535 := bstep (se 1 (by rfl) ⟨915401, by rfl⟩ : syracuseStep 1220535 = 1830803) B1830803
theorem B1220555 : Blo 1219427 1220555 := bstep (se 1 (by rfl) ⟨915416, by rfl⟩ : syracuseStep 1220555 = 1830833) B1830833
theorem B4120523 : Blo 1219427 4120523 := bstep (se 1 (by rfl) ⟨3090392, by rfl⟩ : syracuseStep 4120523 = 6180785) B6180785
theorem B2006999 : Blo 1219427 2006999 := bstep (se 1 (by rfl) ⟨1505249, by rfl⟩ : syracuseStep 2006999 = 3010499) B3010499
theorem B2744279 : Blo 1219427 2744279 := bstep (se 1 (by rfl) ⟨2058209, by rfl⟩ : syracuseStep 2744279 = 4116419) B4116419
theorem B1220567 : Blo 1219427 1220567 := bstep (se 1 (by rfl) ⟨915425, by rfl⟩ : syracuseStep 1220567 = 1830851) B1830851
theorem B1220587 : Blo 1219427 1220587 := bstep (se 1 (by rfl) ⟨915440, by rfl⟩ : syracuseStep 1220587 = 1830881) B1830881
theorem B1220599 : Blo 1219427 1220599 := bstep (se 1 (by rfl) ⟨915449, by rfl⟩ : syracuseStep 1220599 = 1830899) B1830899
theorem B1220615 : Blo 1219427 1220615 := bstep (se 1 (by rfl) ⟨915461, by rfl⟩ : syracuseStep 1220615 = 1830923) B1830923
theorem B10420235 : Blo 1219427 10420235 := bstep (se 1 (by rfl) ⟨7815176, by rfl⟩ : syracuseStep 10420235 = 15630353) B15630353
theorem B1220623 : Blo 1219427 1220623 := bstep (se 1 (by rfl) ⟨915467, by rfl⟩ : syracuseStep 1220623 = 1830935) B1830935
theorem B1220667 : Blo 1219427 1220667 := bstep (se 1 (by rfl) ⟨915500, by rfl⟩ : syracuseStep 1220667 = 1831001) B1831001
theorem B1220743 : Blo 1219427 1220743 := bstep (se 1 (by rfl) ⟨915557, by rfl⟩ : syracuseStep 1220743 = 1831115) B1831115
theorem B1220751 : Blo 1219427 1220751 := bstep (se 1 (by rfl) ⟨915563, by rfl⟩ : syracuseStep 1220751 = 1831127) B1831127
theorem B3571859 : Blo 1219427 3571859 := bstep (se 1 (by rfl) ⟨2678894, by rfl⟩ : syracuseStep 3571859 = 5357789) B5357789
theorem B1220795 : Blo 1219427 1220795 := bstep (se 1 (by rfl) ⟨915596, by rfl⟩ : syracuseStep 1220795 = 1831193) B1831193
theorem B1220871 : Blo 1219427 1220871 := bstep (se 1 (by rfl) ⟨915653, by rfl⟩ : syracuseStep 1220871 = 1831307) B1831307
theorem B3473675 : Blo 1219427 3473675 := bstep (se 1 (by rfl) ⟨2605256, by rfl⟩ : syracuseStep 3473675 = 5210513) B5210513
theorem B3088651 : Blo 1219427 3088651 := bstep (se 1 (by rfl) ⟨2316488, by rfl⟩ : syracuseStep 3088651 = 4632977) B4632977
theorem B1302799 : Blo 1219427 1302799 := bstep (se 1 (by rfl) ⟨977099, by rfl⟩ : syracuseStep 1302799 = 1954199) B1954199
theorem B1220879 : Blo 1219427 1220879 := bstep (se 1 (by rfl) ⟨915659, by rfl⟩ : syracuseStep 1220879 = 1831319) B1831319
theorem B1564987 : Blo 1219427 1564987 := bstep (se 1 (by rfl) ⟨1173740, by rfl⟩ : syracuseStep 1564987 = 2347481) B2347481
theorem B1220923 : Blo 1219427 1220923 := bstep (se 1 (by rfl) ⟨915692, by rfl⟩ : syracuseStep 1220923 = 1831385) B1831385
theorem B2744711 : Blo 1219427 2744711 := bstep (se 1 (by rfl) ⟨2058533, by rfl⟩ : syracuseStep 2744711 = 4117067) B4117067
theorem B3088793 : Blo 1219427 3088793 := bstep (se 2 (by rfl) ⟨1158297, by rfl⟩ : syracuseStep 3088793 = 2316595) B2316595
theorem B2744891 : Blo 1219427 2744891 := bstep (se 1 (by rfl) ⟨2058668, by rfl⟩ : syracuseStep 2744891 = 4117337) B4117337
theorem B3088955 : Blo 1219427 3088955 := bstep (se 1 (by rfl) ⟨2316716, by rfl⟩ : syracuseStep 3088955 = 4633433) B4633433
theorem B1303175 : Blo 1219427 1303175 := bstep (se 1 (by rfl) ⟨977381, by rfl⟩ : syracuseStep 1303175 = 1954763) B1954763
theorem B2745017 : Blo 1219427 2745017 := bstep (se 2 (by rfl) ⟨1029381, by rfl⟩ : syracuseStep 2745017 = 2058763) B2058763
theorem B7815973 : Blo 1219427 7815973 := bstep (se 4 (by rfl) ⟨732747, by rfl⟩ : syracuseStep 7815973 = 1465495) B1465495
theorem B3474323 : Blo 1219427 3474323 := bstep (se 1 (by rfl) ⟨2605742, by rfl⟩ : syracuseStep 3474323 = 5211485) B5211485
theorem B3089299 : Blo 1219427 3089299 := bstep (se 1 (by rfl) ⟨2316974, by rfl⟩ : syracuseStep 3089299 = 4633949) B4633949
theorem B102949829 : Blo 1219427 102949829 := bstep (se 4 (by rfl) ⟨9651546, by rfl⟩ : syracuseStep 102949829 = 19303093) B19303093
theorem B8258507 : Blo 1219427 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B2745359 : Blo 1219427 2745359 := bstep (se 1 (by rfl) ⟨2059019, by rfl⟩ : syracuseStep 2745359 = 4118039) B4118039
theorem B2745377 : Blo 1219427 2745377 := bstep (se 2 (by rfl) ⟨1029516, by rfl⟩ : syracuseStep 2745377 = 2059033) B2059033
theorem B3089441 : Blo 1219427 3089441 := bstep (se 2 (by rfl) ⟨1158540, by rfl⟩ : syracuseStep 3089441 = 2317081) B2317081
theorem B5022839 : Blo 1219427 5022839 := bstep (se 1 (by rfl) ⟨3767129, by rfl⟩ : syracuseStep 5022839 = 7534259) B7534259
theorem B3474551 : Blo 1219427 3474551 := bstep (se 1 (by rfl) ⟨2605913, by rfl⟩ : syracuseStep 3474551 = 5211827) B5211827
theorem B1738027 : Blo 1219427 1738027 := bstep (se 1 (by rfl) ⟨1303520, by rfl⟩ : syracuseStep 1738027 = 2607041) B2607041
theorem B2745719 : Blo 1219427 2745719 := bstep (se 1 (by rfl) ⟨2059289, by rfl⟩ : syracuseStep 2745719 = 4118579) B4118579
theorem B6178193 : Blo 1219427 6178193 := bstep (se 2 (by rfl) ⟨2316822, by rfl⟩ : syracuseStep 6178193 = 4633645) B4633645
theorem B6948281 : Blo 1219427 6948281 := bstep (se 2 (by rfl) ⟨2605605, by rfl⟩ : syracuseStep 6948281 = 5211211) B5211211
theorem B1738255 : Blo 1219427 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B23447069 : Blo 1219427 23447069 := bstep (se 3 (by rfl) ⟨4396325, by rfl⟩ : syracuseStep 23447069 = 8792651) B8792651
theorem B2745899 : Blo 1219427 2745899 := bstep (se 1 (by rfl) ⟨2059424, by rfl⟩ : syracuseStep 2745899 = 4118849) B4118849
theorem B26388341 : Blo 1219427 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B2746259 : Blo 1219427 2746259 := bstep (se 1 (by rfl) ⟨2059694, by rfl⟩ : syracuseStep 2746259 = 4119389) B4119389
theorem B2058169 : Blo 1219427 2058169 := bstep (se 2 (by rfl) ⟨771813, by rfl⟩ : syracuseStep 2058169 = 1543627) B1543627
theorem B2746313 : Blo 1219427 2746313 := bstep (se 2 (by rfl) ⟨1029867, by rfl⟩ : syracuseStep 2746313 = 2059735) B2059735
theorem B3090433 : Blo 1219427 3090433 := bstep (se 2 (by rfl) ⟨1158912, by rfl⟩ : syracuseStep 3090433 = 2317825) B2317825
theorem B4630729 : Blo 1219427 4630729 := bstep (se 2 (by rfl) ⟨1736523, by rfl⟩ : syracuseStep 4630729 = 3473047) B3473047
theorem B3909833 : Blo 1219427 3909833 := bstep (se 2 (by rfl) ⟨1466187, by rfl⟩ : syracuseStep 3909833 = 2932375) B2932375
theorem B1829177 : Blo 1219427 1829177 := bstep (se 2 (by rfl) ⟨685941, by rfl⟩ : syracuseStep 1829177 = 1371883) B1371883
theorem B1829255 : Blo 1219427 1829255 := bstep (se 1 (by rfl) ⟨1371941, by rfl⟩ : syracuseStep 1829255 = 2743883) B2743883
theorem B1829291 : Blo 1219427 1829291 := bstep (se 1 (by rfl) ⟨1371968, by rfl⟩ : syracuseStep 1829291 = 2743937) B2743937
theorem B1829321 : Blo 1219427 1829321 := bstep (se 2 (by rfl) ⟨685995, by rfl⟩ : syracuseStep 1829321 = 1371991) B1371991
theorem B1829435 : Blo 1219427 1829435 := bstep (se 1 (by rfl) ⟨1372076, by rfl⟩ : syracuseStep 1829435 = 2744153) B2744153
theorem B1829495 : Blo 1219427 1829495 := bstep (se 1 (by rfl) ⟨1372121, by rfl⟩ : syracuseStep 1829495 = 2744243) B2744243
theorem B2058871 : Blo 1219427 2058871 := bstep (se 1 (by rfl) ⟨1544153, by rfl⟩ : syracuseStep 2058871 = 3088307) B3088307
theorem B2747015 : Blo 1219427 2747015 := bstep (se 1 (by rfl) ⟨2060261, by rfl⟩ : syracuseStep 2747015 = 4120523) B4120523
theorem B1337999 : Blo 1219427 1337999 := bstep (se 1 (by rfl) ⟨1003499, by rfl⟩ : syracuseStep 1337999 = 2006999) B2006999
theorem B1829519 : Blo 1219427 1829519 := bstep (se 1 (by rfl) ⟨1372139, by rfl⟩ : syracuseStep 1829519 = 2744279) B2744279
theorem B1829561 : Blo 1219427 1829561 := bstep (se 2 (by rfl) ⟨686085, by rfl⟩ : syracuseStep 1829561 = 1372171) B1372171
theorem B1829639 : Blo 1219427 1829639 := bstep (se 1 (by rfl) ⟨1372229, by rfl⟩ : syracuseStep 1829639 = 2744459) B2744459
theorem B1649423 : Blo 1219427 1649423 := bstep (se 1 (by rfl) ⟨1237067, by rfl⟩ : syracuseStep 1649423 = 2474135) B2474135
theorem B1829675 : Blo 1219427 1829675 := bstep (se 1 (by rfl) ⟨1372256, by rfl⟩ : syracuseStep 1829675 = 2744513) B2744513
theorem B9268019 : Blo 1219427 9268019 := bstep (se 1 (by rfl) ⟨6951014, by rfl⟩ : syracuseStep 9268019 = 13902029) B13902029
theorem B2059067 : Blo 1219427 2059067 := bstep (se 1 (by rfl) ⟨1544300, by rfl⟩ : syracuseStep 2059067 = 3088601) B3088601
theorem B3910459 : Blo 1219427 3910459 := bstep (se 1 (by rfl) ⟨2932844, by rfl⟩ : syracuseStep 3910459 = 5865689) B5865689
theorem B1829705 : Blo 1219427 1829705 := bstep (se 2 (by rfl) ⟨686139, by rfl⟩ : syracuseStep 1829705 = 1372279) B1372279
theorem B9898841 : Blo 1219427 9898841 := bstep (se 2 (by rfl) ⟨3712065, by rfl⟩ : syracuseStep 9898841 = 7424131) B7424131
theorem B1829819 : Blo 1219427 1829819 := bstep (se 1 (by rfl) ⟨1372364, by rfl⟩ : syracuseStep 1829819 = 2744729) B2744729
theorem B1829879 : Blo 1219427 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B1829903 : Blo 1219427 1829903 := bstep (se 1 (by rfl) ⟨1372427, by rfl⟩ : syracuseStep 1829903 = 2744855) B2744855
theorem B1829945 : Blo 1219427 1829945 := bstep (se 2 (by rfl) ⟨686229, by rfl⟩ : syracuseStep 1829945 = 1372459) B1372459
theorem B7523447 : Blo 1219427 7523447 := bstep (se 1 (by rfl) ⟨5642585, by rfl⟩ : syracuseStep 7523447 = 11285171) B11285171
theorem B1830023 : Blo 1219427 1830023 := bstep (se 1 (by rfl) ⟨1372517, by rfl⟩ : syracuseStep 1830023 = 2745035) B2745035
theorem B1830059 : Blo 1219427 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B1830089 : Blo 1219427 1830089 := bstep (se 2 (by rfl) ⟨686283, by rfl⟩ : syracuseStep 1830089 = 1372567) B1372567
theorem B2059465 : Blo 1219427 2059465 := bstep (se 2 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 2059465 = 1544599) B1544599
theorem B14093513 : Blo 1219427 14093513 := bstep (se 2 (by rfl) ⟨5285067, by rfl⟩ : syracuseStep 14093513 = 10570135) B10570135
theorem B12528913 : Blo 1219427 12528913 := bstep (se 2 (by rfl) ⟨4698342, by rfl⟩ : syracuseStep 12528913 = 9396685) B9396685
theorem B6950195 : Blo 1219427 6950195 := bstep (se 1 (by rfl) ⟨5212646, by rfl⟩ : syracuseStep 6950195 = 10425293) B10425293
theorem B4115771 : Blo 1219427 4115771 := bstep (se 1 (by rfl) ⟨3086828, by rfl⟩ : syracuseStep 4115771 = 6173657) B6173657
theorem B1830203 : Blo 1219427 1830203 := bstep (se 1 (by rfl) ⟨1372652, by rfl⟩ : syracuseStep 1830203 = 2745305) B2745305
theorem B1830263 : Blo 1219427 1830263 := bstep (se 1 (by rfl) ⟨1372697, by rfl⟩ : syracuseStep 1830263 = 2745395) B2745395
theorem B1830287 : Blo 1219427 1830287 := bstep (se 1 (by rfl) ⟨1372715, by rfl⟩ : syracuseStep 1830287 = 2745431) B2745431
theorem B1830329 : Blo 1219427 1830329 := bstep (se 2 (by rfl) ⟨686373, by rfl⟩ : syracuseStep 1830329 = 1372747) B1372747
theorem B6180299 : Blo 1219427 6180299 := bstep (se 1 (by rfl) ⟨4635224, by rfl⟩ : syracuseStep 6180299 = 9270449) B9270449
theorem B1830407 : Blo 1219427 1830407 := bstep (se 1 (by rfl) ⟨1372805, by rfl⟩ : syracuseStep 1830407 = 2745611) B2745611
theorem B5017099 : Blo 1219427 5017099 := bstep (se 1 (by rfl) ⟨3762824, by rfl⟩ : syracuseStep 5017099 = 7525649) B7525649
theorem B1830443 : Blo 1219427 1830443 := bstep (se 1 (by rfl) ⟨1372832, by rfl⟩ : syracuseStep 1830443 = 2745665) B2745665
theorem B1830473 : Blo 1219427 1830473 := bstep (se 2 (by rfl) ⟨686427, by rfl⟩ : syracuseStep 1830473 = 1372855) B1372855
theorem B1543799 : Blo 1219427 1543799 := bstep (se 1 (by rfl) ⟨1157849, by rfl⟩ : syracuseStep 1543799 = 2315699) B2315699
theorem B1855163 : Blo 1219427 1855163 := bstep (se 1 (by rfl) ⟨1391372, by rfl⟩ : syracuseStep 1855163 = 2782745) B2782745
theorem B1830587 : Blo 1219427 1830587 := bstep (se 1 (by rfl) ⟨1372940, by rfl⟩ : syracuseStep 1830587 = 2745881) B2745881
theorem B6598381 : Blo 1219427 6598381 := bstep (se 3 (by rfl) ⟨1237196, by rfl⟩ : syracuseStep 6598381 = 2474393) B2474393
theorem B1830647 : Blo 1219427 1830647 := bstep (se 1 (by rfl) ⟨1372985, by rfl⟩ : syracuseStep 1830647 = 2745971) B2745971
theorem B1371919 : Blo 1219427 1371919 := bstep (se 1 (by rfl) ⟨1028939, by rfl⟩ : syracuseStep 1371919 = 2057879) B2057879
theorem B1543951 : Blo 1219427 1543951 := bstep (se 1 (by rfl) ⟨1157963, by rfl⟩ : syracuseStep 1543951 = 2315927) B2315927
theorem B1830671 : Blo 1219427 1830671 := bstep (se 1 (by rfl) ⟨1373003, by rfl⟩ : syracuseStep 1830671 = 2746007) B2746007
theorem B6180623 : Blo 1219427 6180623 := bstep (se 1 (by rfl) ⟨4635467, by rfl⟩ : syracuseStep 6180623 = 9270935) B9270935
theorem B4116257 : Blo 1219427 4116257 := bstep (se 2 (by rfl) ⟨1543596, by rfl⟩ : syracuseStep 4116257 = 3087193) B3087193
theorem B5861153 : Blo 1219427 5861153 := bstep (se 2 (by rfl) ⟨2197932, by rfl⟩ : syracuseStep 5861153 = 4395865) B4395865
theorem B1830713 : Blo 1219427 1830713 := bstep (se 2 (by rfl) ⟨686517, by rfl⟩ : syracuseStep 1830713 = 1373035) B1373035
theorem B1830791 : Blo 1219427 1830791 := bstep (se 1 (by rfl) ⟨1373093, by rfl⟩ : syracuseStep 1830791 = 2746187) B2746187
theorem B2060167 : Blo 1219427 2060167 := bstep (se 1 (by rfl) ⟨1545125, by rfl⟩ : syracuseStep 2060167 = 3090251) B3090251
theorem B1830827 : Blo 1219427 1830827 := bstep (se 1 (by rfl) ⟨1373120, by rfl⟩ : syracuseStep 1830827 = 2746241) B2746241
theorem B1544123 : Blo 1219427 1544123 := bstep (se 1 (by rfl) ⟨1158092, by rfl⟩ : syracuseStep 1544123 = 2316185) B2316185
theorem B1830857 : Blo 1219427 1830857 := bstep (se 2 (by rfl) ⟨686571, by rfl⟩ : syracuseStep 1830857 = 1373143) B1373143
theorem B1830971 : Blo 1219427 1830971 := bstep (se 1 (by rfl) ⟨1373228, by rfl⟩ : syracuseStep 1830971 = 2746457) B2746457
theorem B3960893 : Blo 1219427 3960893 := bstep (se 3 (by rfl) ⟨742667, by rfl⟩ : syracuseStep 3960893 = 1485335) B1485335
theorem B35188829 : Blo 1219427 35188829 := bstep (se 3 (by rfl) ⟨6597905, by rfl⟩ : syracuseStep 35188829 = 13195811) B13195811
theorem B15626357 : Blo 1219427 15626357 := bstep (se 5 (by rfl) ⟨732485, by rfl⟩ : syracuseStep 15626357 = 1464971) B1464971
theorem B1831031 : Blo 1219427 1831031 := bstep (se 1 (by rfl) ⟨1373273, by rfl⟩ : syracuseStep 1831031 = 2746547) B2746547
theorem B1831055 : Blo 1219427 1831055 := bstep (se 1 (by rfl) ⟨1373291, by rfl⟩ : syracuseStep 1831055 = 2746583) B2746583
theorem B3174547 : Blo 1219427 3174547 := bstep (se 1 (by rfl) ⟨2380910, by rfl⟩ : syracuseStep 3174547 = 4761821) B4761821
theorem B1831097 : Blo 1219427 1831097 := bstep (se 2 (by rfl) ⟨686661, by rfl⟩ : syracuseStep 1831097 = 1373323) B1373323
theorem B12529865 : Blo 1219427 12529865 := bstep (se 2 (by rfl) ⟨4698699, by rfl⟩ : syracuseStep 12529865 = 9397399) B9397399
theorem B1372423 : Blo 1219427 1372423 := bstep (se 1 (by rfl) ⟨1029317, by rfl⟩ : syracuseStep 1372423 = 2058635) B2058635
theorem B1831175 : Blo 1219427 1831175 := bstep (se 1 (by rfl) ⟨1373381, by rfl⟩ : syracuseStep 1831175 = 2746763) B2746763
theorem B3297569 : Blo 1219427 3297569 := bstep (se 2 (by rfl) ⟨1236588, by rfl⟩ : syracuseStep 3297569 = 2473177) B2473177
theorem B10424609 : Blo 1219427 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B1831211 : Blo 1219427 1831211 := bstep (se 1 (by rfl) ⟨1373408, by rfl⟩ : syracuseStep 1831211 = 2746817) B2746817
theorem B1831241 : Blo 1219427 1831241 := bstep (se 2 (by rfl) ⟨686715, by rfl⟩ : syracuseStep 1831241 = 1373431) B1373431
theorem B4116851 : Blo 1219427 4116851 := bstep (se 1 (by rfl) ⟨3087638, by rfl⟩ : syracuseStep 4116851 = 6175277) B6175277
theorem B4632947 : Blo 1219427 4632947 := bstep (se 1 (by rfl) ⟨3474710, by rfl⟩ : syracuseStep 4632947 = 6949421) B6949421
theorem B1372603 : Blo 1219427 1372603 := bstep (se 1 (by rfl) ⟨1029452, by rfl⟩ : syracuseStep 1372603 = 2058905) B2058905
theorem B1831355 : Blo 1219427 1831355 := bstep (se 1 (by rfl) ⟨1373516, by rfl⟩ : syracuseStep 1831355 = 2747033) B2747033
theorem B4395563 : Blo 1219427 4395563 := bstep (se 1 (by rfl) ⟨3296672, by rfl⟩ : syracuseStep 4395563 = 6593345) B6593345
theorem B8794817 : Blo 1219427 8794817 := bstep (se 2 (by rfl) ⟨3298056, by rfl⟩ : syracuseStep 8794817 = 6596113) B6596113
theorem B6951653 : Blo 1219427 6951653 := bstep (se 4 (by rfl) ⟨651717, by rfl⟩ : syracuseStep 6951653 = 1303435) B1303435
theorem B1545095 : Blo 1219427 1545095 := bstep (se 1 (by rfl) ⟨1158821, by rfl⟩ : syracuseStep 1545095 = 2317643) B2317643
theorem B1373071 : Blo 1219427 1373071 := bstep (se 1 (by rfl) ⟨1029803, by rfl⟩ : syracuseStep 1373071 = 2059607) B2059607
theorem B2315297 : Blo 1219427 2315297 := bstep (se 2 (by rfl) ⟨868236, by rfl⟩ : syracuseStep 2315297 = 1736473) B1736473
theorem B30078307 : Blo 1219427 30078307 := bstep (se 1 (by rfl) ⟨22558730, by rfl⟩ : syracuseStep 30078307 = 45117461) B45117461
theorem B6952337 : Blo 1219427 6952337 := bstep (se 2 (by rfl) ⟨2607126, by rfl⟩ : syracuseStep 6952337 = 5214253) B5214253
theorem B5567897 : Blo 1219427 5567897 := bstep (se 2 (by rfl) ⟨2087961, by rfl⟩ : syracuseStep 5567897 = 4175923) B4175923
theorem B23451065 : Blo 1219427 23451065 := bstep (se 2 (by rfl) ⟨8794149, by rfl⟩ : syracuseStep 23451065 = 17588299) B17588299
theorem B5568011 : Blo 1219427 5568011 := bstep (se 1 (by rfl) ⟨4176008, by rfl⟩ : syracuseStep 5568011 = 8352017) B8352017
theorem B3299105 : Blo 1219427 3299105 := bstep (se 2 (by rfl) ⟨1237164, by rfl⟩ : syracuseStep 3299105 = 2474329) B2474329
theorem B15636503 : Blo 1219427 15636503 := bstep (se 1 (by rfl) ⟨11727377, by rfl⟩ : syracuseStep 15636503 = 23454755) B23454755
theorem B4757705 : Blo 1219427 4757705 := bstep (se 2 (by rfl) ⟨1784139, by rfl⟩ : syracuseStep 4757705 = 3568279) B3568279
theorem B4176143 : Blo 1219427 4176143 := bstep (se 1 (by rfl) ⟨3132107, by rfl⟩ : syracuseStep 4176143 = 6264215) B6264215
theorem B3086707 : Blo 1219427 3086707 := bstep (se 1 (by rfl) ⟨2315030, by rfl⟩ : syracuseStep 3086707 = 4630061) B4630061
theorem B6953363 : Blo 1219427 6953363 := bstep (se 1 (by rfl) ⟨5215022, by rfl⟩ : syracuseStep 6953363 = 10430045) B10430045
theorem B4635089 : Blo 1219427 4635089 := bstep (se 2 (by rfl) ⟨1738158, by rfl⟩ : syracuseStep 4635089 = 3476317) B3476317
theorem B3086849 : Blo 1219427 3086849 := bstep (se 2 (by rfl) ⟨1157568, by rfl⟩ : syracuseStep 3086849 = 2315137) B2315137
theorem B9263645 : Blo 1219427 9263645 := bstep (se 3 (by rfl) ⟨1736933, by rfl⟩ : syracuseStep 9263645 = 3473867) B3473867
theorem B5863997 : Blo 1219427 5863997 := bstep (se 3 (by rfl) ⟨1099499, by rfl⟩ : syracuseStep 5863997 = 2198999) B2198999
theorem B30489281 : Blo 1219427 30489281 := bstep (se 2 (by rfl) ⟨11433480, by rfl⟩ : syracuseStep 30489281 = 22866961) B22866961
theorem B4635407 : Blo 1219427 4635407 := bstep (se 1 (by rfl) ⟨3476555, by rfl⟩ : syracuseStep 4635407 = 6953111) B6953111
theorem B2931499 : Blo 1219427 2931499 := bstep (se 1 (by rfl) ⟨2198624, by rfl⟩ : syracuseStep 2931499 = 4397249) B4397249
theorem B3718003 : Blo 1219427 3718003 := bstep (se 1 (by rfl) ⟨2788502, by rfl⟩ : syracuseStep 3718003 = 5577005) B5577005
theorem B1219463 : Blo 1219427 1219463 := bstep (se 1 (by rfl) ⟨914597, by rfl⟩ : syracuseStep 1219463 = 1829195) B1829195
theorem B1219471 : Blo 1219427 1219471 := bstep (se 1 (by rfl) ⟨914603, by rfl⟩ : syracuseStep 1219471 = 1829207) B1829207
theorem B1465231 : Blo 1219427 1465231 := bstep (se 1 (by rfl) ⟨1098923, by rfl⟩ : syracuseStep 1465231 = 2197847) B2197847
theorem B4119443 : Blo 1219427 4119443 := bstep (se 1 (by rfl) ⟨3089582, by rfl⟩ : syracuseStep 4119443 = 6179165) B6179165
theorem B2317241 : Blo 1219427 2317241 := bstep (se 2 (by rfl) ⟨868965, by rfl⟩ : syracuseStep 2317241 = 1737931) B1737931
theorem B1219515 : Blo 1219427 1219515 := bstep (se 1 (by rfl) ⟨914636, by rfl⟩ : syracuseStep 1219515 = 1829273) B1829273
theorem B3087305 : Blo 1219427 3087305 := bstep (se 2 (by rfl) ⟨1157739, by rfl⟩ : syracuseStep 3087305 = 2315479) B2315479
theorem B1219591 : Blo 1219427 1219591 := bstep (se 1 (by rfl) ⟨914693, by rfl⟩ : syracuseStep 1219591 = 1829387) B1829387
theorem B1219599 : Blo 1219427 1219599 := bstep (se 1 (by rfl) ⟨914699, by rfl⟩ : syracuseStep 1219599 = 1829399) B1829399
theorem B6945821 : Blo 1219427 6945821 := bstep (se 3 (by rfl) ⟨1302341, by rfl⟩ : syracuseStep 6945821 = 2604683) B2604683
theorem B1219643 : Blo 1219427 1219643 := bstep (se 1 (by rfl) ⟨914732, by rfl⟩ : syracuseStep 1219643 = 1829465) B1829465
theorem B1219719 : Blo 1219427 1219719 := bstep (se 1 (by rfl) ⟨914789, by rfl⟩ : syracuseStep 1219719 = 1829579) B1829579
theorem B1219727 : Blo 1219427 1219727 := bstep (se 1 (by rfl) ⟨914795, by rfl⟩ : syracuseStep 1219727 = 1829591) B1829591
theorem B1219771 : Blo 1219427 1219771 := bstep (se 1 (by rfl) ⟨914828, by rfl⟩ : syracuseStep 1219771 = 1829657) B1829657
theorem B2931913 : Blo 1219427 2931913 := bstep (se 2 (by rfl) ⟨1099467, by rfl⟩ : syracuseStep 2931913 = 2198935) B2198935
theorem B1219847 : Blo 1219427 1219847 := bstep (se 1 (by rfl) ⟨914885, by rfl⟩ : syracuseStep 1219847 = 1829771) B1829771
theorem B1219855 : Blo 1219427 1219855 := bstep (se 1 (by rfl) ⟨914891, by rfl⟩ : syracuseStep 1219855 = 1829783) B1829783
theorem B1465615 : Blo 1219427 1465615 := bstep (se 1 (by rfl) ⟨1099211, by rfl⟩ : syracuseStep 1465615 = 2198423) B2198423
theorem B3087659 : Blo 1219427 3087659 := bstep (se 1 (by rfl) ⟨2315744, by rfl⟩ : syracuseStep 3087659 = 4631489) B4631489
theorem B1219899 : Blo 1219427 1219899 := bstep (se 1 (by rfl) ⟨914924, by rfl⟩ : syracuseStep 1219899 = 1829849) B1829849
theorem B6258055 : Blo 1219427 6258055 := bstep (se 1 (by rfl) ⟨4693541, by rfl⟩ : syracuseStep 6258055 = 9387083) B9387083
theorem B1219975 : Blo 1219427 1219975 := bstep (se 1 (by rfl) ⟨914981, by rfl⟩ : syracuseStep 1219975 = 1829963) B1829963
theorem B1219983 : Blo 1219427 1219983 := bstep (se 1 (by rfl) ⟨914987, by rfl⟩ : syracuseStep 1219983 = 1829975) B1829975
theorem B1220027 : Blo 1219427 1220027 := bstep (se 1 (by rfl) ⟨915020, by rfl⟩ : syracuseStep 1220027 = 1830041) B1830041
theorem B1220103 : Blo 1219427 1220103 := bstep (se 1 (by rfl) ⟨915077, by rfl⟩ : syracuseStep 1220103 = 1830155) B1830155
theorem B1220111 : Blo 1219427 1220111 := bstep (se 1 (by rfl) ⟨915083, by rfl⟩ : syracuseStep 1220111 = 1830167) B1830167
theorem B1220155 : Blo 1219427 1220155 := bstep (se 1 (by rfl) ⟨915116, by rfl⟩ : syracuseStep 1220155 = 1830233) B1830233
theorem B1220231 : Blo 1219427 1220231 := bstep (se 1 (by rfl) ⟨915173, by rfl⟩ : syracuseStep 1220231 = 1830347) B1830347
theorem B1220239 : Blo 1219427 1220239 := bstep (se 1 (by rfl) ⟨915179, by rfl⟩ : syracuseStep 1220239 = 1830359) B1830359
theorem B2743955 : Blo 1219427 2743955 := bstep (se 1 (by rfl) ⟨2057966, by rfl⟩ : syracuseStep 2743955 = 4115933) B4115933
theorem B1220283 : Blo 1219427 1220283 := bstep (se 1 (by rfl) ⟨915212, by rfl⟩ : syracuseStep 1220283 = 1830425) B1830425
theorem B2744009 : Blo 1219427 2744009 := bstep (se 2 (by rfl) ⟨1029003, by rfl⟩ : syracuseStep 2744009 = 2058007) B2058007
theorem B6946505 : Blo 1219427 6946505 := bstep (se 2 (by rfl) ⟨2604939, by rfl⟩ : syracuseStep 6946505 = 5209879) B5209879
theorem B11722457 : Blo 1219427 11722457 := bstep (se 2 (by rfl) ⟨4395921, by rfl⟩ : syracuseStep 11722457 = 8791843) B8791843
theorem B1220359 : Blo 1219427 1220359 := bstep (se 1 (by rfl) ⟨915269, by rfl⟩ : syracuseStep 1220359 = 1830539) B1830539
theorem B1220367 : Blo 1219427 1220367 := bstep (se 1 (by rfl) ⟨915275, by rfl⟩ : syracuseStep 1220367 = 1830551) B1830551
theorem B1220411 : Blo 1219427 1220411 := bstep (se 1 (by rfl) ⟨915308, by rfl⟩ : syracuseStep 1220411 = 1830617) B1830617
theorem B6684551 : Blo 1219427 6684551 := bstep (se 1 (by rfl) ⟨5013413, by rfl⟩ : syracuseStep 6684551 = 10026827) B10026827
theorem B1220487 : Blo 1219427 1220487 := bstep (se 1 (by rfl) ⟨915365, by rfl⟩ : syracuseStep 1220487 = 1830731) B1830731
theorem B1220495 : Blo 1219427 1220495 := bstep (se 1 (by rfl) ⟨915371, by rfl⟩ : syracuseStep 1220495 = 1830743) B1830743
theorem B1220539 : Blo 1219427 1220539 := bstep (se 1 (by rfl) ⟨915404, by rfl⟩ : syracuseStep 1220539 = 1830809) B1830809
theorem B4120577 : Blo 1219427 4120577 := bstep (se 2 (by rfl) ⟨1545216, by rfl⟩ : syracuseStep 4120577 = 3090433) B3090433
theorem B6946823 : Blo 1219427 6946823 := bstep (se 1 (by rfl) ⟨5210117, by rfl⟩ : syracuseStep 6946823 = 10420235) B10420235
theorem B1220647 : Blo 1219427 1220647 := bstep (se 1 (by rfl) ⟨915485, by rfl⟩ : syracuseStep 1220647 = 1830971) B1830971
theorem B1220687 : Blo 1219427 1220687 := bstep (se 1 (by rfl) ⟨915515, by rfl⟩ : syracuseStep 1220687 = 1831031) B1831031
theorem B1220703 : Blo 1219427 1220703 := bstep (se 1 (by rfl) ⟨915527, by rfl⟩ : syracuseStep 1220703 = 1831055) B1831055
theorem B1220731 : Blo 1219427 1220731 := bstep (se 1 (by rfl) ⟨915548, by rfl⟩ : syracuseStep 1220731 = 1831097) B1831097
theorem B1220783 : Blo 1219427 1220783 := bstep (se 1 (by rfl) ⟨915587, by rfl⟩ : syracuseStep 1220783 = 1831175) B1831175
theorem B1220807 : Blo 1219427 1220807 := bstep (se 1 (by rfl) ⟨915605, by rfl⟩ : syracuseStep 1220807 = 1831211) B1831211
theorem B1220827 : Blo 1219427 1220827 := bstep (se 1 (by rfl) ⟨915620, by rfl⟩ : syracuseStep 1220827 = 1831241) B1831241
theorem B2744567 : Blo 1219427 2744567 := bstep (se 1 (by rfl) ⟨2058425, by rfl⟩ : syracuseStep 2744567 = 4116851) B4116851
theorem B3088631 : Blo 1219427 3088631 := bstep (se 1 (by rfl) ⟨2316473, by rfl⟩ : syracuseStep 3088631 = 4632947) B4632947
theorem B1220903 : Blo 1219427 1220903 := bstep (se 1 (by rfl) ⟨915677, by rfl⟩ : syracuseStep 1220903 = 1831355) B1831355
theorem B20062525 : Blo 1219427 20062525 := bstep (se 3 (by rfl) ⟨3761723, by rfl⟩ : syracuseStep 20062525 = 7523447) B7523447
theorem B1737065 : Blo 1219427 1737065 := bstep (se 2 (by rfl) ⟨651399, by rfl⟩ : syracuseStep 1737065 = 1302799) B1302799
theorem B68633219 : Blo 1219427 68633219 := bstep (se 1 (by rfl) ⟨51474914, by rfl⟩ : syracuseStep 68633219 = 102949829) B102949829
theorem B5505671 : Blo 1219427 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B2745161 : Blo 1219427 2745161 := bstep (se 2 (by rfl) ⟨1029435, by rfl⟩ : syracuseStep 2745161 = 2058871) B2058871
theorem B3712007 : Blo 1219427 3712007 := bstep (se 1 (by rfl) ⟨2784005, by rfl⟩ : syracuseStep 3712007 = 5568011) B5568011
theorem B15631379 : Blo 1219427 15631379 := bstep (se 1 (by rfl) ⟨11723534, by rfl⟩ : syracuseStep 15631379 = 23447069) B23447069
theorem B10421297 : Blo 1219427 10421297 := bstep (se 2 (by rfl) ⟨3907986, by rfl⟩ : syracuseStep 10421297 = 7815973) B7815973
theorem B3908665 : Blo 1219427 3908665 := bstep (se 2 (by rfl) ⟨1465749, by rfl⟩ : syracuseStep 3908665 = 2931499) B2931499
theorem B4957337 : Blo 1219427 4957337 := bstep (se 2 (by rfl) ⟨1859001, by rfl⟩ : syracuseStep 4957337 = 3718003) B3718003
theorem B3171803 : Blo 1219427 3171803 := bstep (se 1 (by rfl) ⟨2378852, by rfl⟩ : syracuseStep 3171803 = 4757705) B4757705
theorem B2606555 : Blo 1219427 2606555 := bstep (se 1 (by rfl) ⟨1954916, by rfl⟩ : syracuseStep 2606555 = 3909833) B3909833
theorem B3909217 : Blo 1219427 3909217 := bstep (se 2 (by rfl) ⟨1465956, by rfl⟩ : syracuseStep 3909217 = 2931913) B2931913
theorem B2745953 : Blo 1219427 2745953 := bstep (se 2 (by rfl) ⟨1029732, by rfl⟩ : syracuseStep 2745953 = 2059465) B2059465
theorem B3090059 : Blo 1219427 3090059 := bstep (se 1 (by rfl) ⟨2317544, by rfl⟩ : syracuseStep 3090059 = 4635089) B4635089
theorem B2057899 : Blo 1219427 2057899 := bstep (se 1 (by rfl) ⟨1543424, by rfl⟩ : syracuseStep 2057899 = 3086849) B3086849
theorem B3475133 : Blo 1219427 3475133 := bstep (se 3 (by rfl) ⟨651587, by rfl⟩ : syracuseStep 3475133 = 1303175) B1303175
theorem B16705217 : Blo 1219427 16705217 := bstep (se 2 (by rfl) ⟨6264456, by rfl⟩ : syracuseStep 16705217 = 12528913) B12528913
theorem B3909331 : Blo 1219427 3909331 := bstep (se 1 (by rfl) ⟨2931998, by rfl⟩ : syracuseStep 3909331 = 5863997) B5863997
theorem B20326187 : Blo 1219427 20326187 := bstep (se 1 (by rfl) ⟨15244640, by rfl⟩ : syracuseStep 20326187 = 30489281) B30489281
theorem B3090271 : Blo 1219427 3090271 := bstep (se 1 (by rfl) ⟨2317703, by rfl⟩ : syracuseStep 3090271 = 4635407) B4635407
theorem B6178679 : Blo 1219427 6178679 := bstep (se 1 (by rfl) ⟨4634009, by rfl⟩ : syracuseStep 6178679 = 9268019) B9268019
theorem B2746295 : Blo 1219427 2746295 := bstep (se 1 (by rfl) ⟨2059721, by rfl⟩ : syracuseStep 2746295 = 4119443) B4119443
theorem B2058203 : Blo 1219427 2058203 := bstep (se 1 (by rfl) ⟨1543652, by rfl⟩ : syracuseStep 2058203 = 3087305) B3087305
theorem B4630547 : Blo 1219427 4630547 := bstep (se 1 (by rfl) ⟨3472910, by rfl⟩ : syracuseStep 4630547 = 6945821) B6945821
theorem B2058439 : Blo 1219427 2058439 := bstep (se 1 (by rfl) ⟨1543829, by rfl⟩ : syracuseStep 2058439 = 3087659) B3087659
theorem B1829225 : Blo 1219427 1829225 := bstep (se 2 (by rfl) ⟨685959, by rfl⟩ : syracuseStep 1829225 = 1371919) B1371919
theorem B2058601 : Blo 1219427 2058601 := bstep (se 2 (by rfl) ⟨771975, by rfl⟩ : syracuseStep 2058601 = 1543951) B1543951
theorem B1829303 : Blo 1219427 1829303 := bstep (se 1 (by rfl) ⟨1371977, by rfl⟩ : syracuseStep 1829303 = 2743955) B2743955
theorem B1829339 : Blo 1219427 1829339 := bstep (se 1 (by rfl) ⟨1372004, by rfl⟩ : syracuseStep 1829339 = 2744009) B2744009
theorem B4631003 : Blo 1219427 4631003 := bstep (se 1 (by rfl) ⟨3473252, by rfl⟩ : syracuseStep 4631003 = 6946505) B6946505
theorem B2746889 : Blo 1219427 2746889 := bstep (se 2 (by rfl) ⟨1030083, by rfl⟩ : syracuseStep 2746889 = 2060167) B2060167
theorem B2640595 : Blo 1219427 2640595 := bstep (se 1 (by rfl) ⟨1980446, by rfl⟩ : syracuseStep 2640595 = 3960893) B3960893
theorem B6949739 : Blo 1219427 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B1829807 : Blo 1219427 1829807 := bstep (se 1 (by rfl) ⟨1372355, by rfl⟩ : syracuseStep 1829807 = 2744711) B2744711
theorem B2059195 : Blo 1219427 2059195 := bstep (se 1 (by rfl) ⟨1544396, by rfl⟩ : syracuseStep 2059195 = 3088793) B3088793
theorem B1829897 : Blo 1219427 1829897 := bstep (se 2 (by rfl) ⟨686211, by rfl⟩ : syracuseStep 1829897 = 1372423) B1372423
theorem B1829927 : Blo 1219427 1829927 := bstep (se 1 (by rfl) ⟨1372445, by rfl⟩ : syracuseStep 1829927 = 2744891) B2744891
theorem B2059303 : Blo 1219427 2059303 := bstep (se 1 (by rfl) ⟨1544477, by rfl⟩ : syracuseStep 2059303 = 3088955) B3088955
theorem B1830011 : Blo 1219427 1830011 := bstep (se 1 (by rfl) ⟨1372508, by rfl⟩ : syracuseStep 1830011 = 2745017) B2745017
theorem B4115609 : Blo 1219427 4115609 := bstep (se 2 (by rfl) ⟨1543353, by rfl⟩ : syracuseStep 4115609 = 3086707) B3086707
theorem B1830137 : Blo 1219427 1830137 := bstep (se 2 (by rfl) ⟨686301, by rfl⟩ : syracuseStep 1830137 = 1372603) B1372603
theorem B1830239 : Blo 1219427 1830239 := bstep (se 1 (by rfl) ⟨1372679, by rfl⟩ : syracuseStep 1830239 = 2745359) B2745359
theorem B1543531 : Blo 1219427 1543531 := bstep (se 1 (by rfl) ⟨1157648, by rfl⟩ : syracuseStep 1543531 = 2315297) B2315297
theorem B1830251 : Blo 1219427 1830251 := bstep (se 1 (by rfl) ⟨1372688, by rfl⟩ : syracuseStep 1830251 = 2745377) B2745377
theorem B2059627 : Blo 1219427 2059627 := bstep (se 1 (by rfl) ⟨1544720, by rfl⟩ : syracuseStep 2059627 = 3089441) B3089441
theorem B8793517 : Blo 1219427 8793517 := bstep (se 3 (by rfl) ⟨1648784, by rfl⟩ : syracuseStep 8793517 = 3297569) B3297569
theorem B1830479 : Blo 1219427 1830479 := bstep (se 1 (by rfl) ⟨1372859, by rfl⟩ : syracuseStep 1830479 = 2745719) B2745719
theorem B4632187 : Blo 1219427 4632187 := bstep (se 1 (by rfl) ⟨3474140, by rfl⟩ : syracuseStep 4632187 = 6948281) B6948281
theorem B15634043 : Blo 1219427 15634043 := bstep (se 1 (by rfl) ⟨11725532, by rfl⟩ : syracuseStep 15634043 = 23451065) B23451065
theorem B1830599 : Blo 1219427 1830599 := bstep (se 1 (by rfl) ⟨1372949, by rfl⟩ : syracuseStep 1830599 = 2745899) B2745899
theorem B14847725 : Blo 1219427 14847725 := bstep (se 3 (by rfl) ⟨2783948, by rfl⟩ : syracuseStep 14847725 = 5567897) B5567897
theorem B5213945 : Blo 1219427 5213945 := bstep (se 2 (by rfl) ⟨1955229, by rfl⟩ : syracuseStep 5213945 = 3910459) B3910459
theorem B1953641 : Blo 1219427 1953641 := bstep (se 2 (by rfl) ⟨732615, by rfl⟩ : syracuseStep 1953641 = 1465231) B1465231
theorem B1830761 : Blo 1219427 1830761 := bstep (se 2 (by rfl) ⟨686535, by rfl⟩ : syracuseStep 1830761 = 1373071) B1373071
theorem B2199403 : Blo 1219427 2199403 := bstep (se 1 (by rfl) ⟨1649552, by rfl⟩ : syracuseStep 2199403 = 3299105) B3299105
theorem B17592227 : Blo 1219427 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B1830839 : Blo 1219427 1830839 := bstep (se 1 (by rfl) ⟨1373129, by rfl⟩ : syracuseStep 1830839 = 2746259) B2746259
theorem B1830875 : Blo 1219427 1830875 := bstep (se 1 (by rfl) ⟨1373156, by rfl⟩ : syracuseStep 1830875 = 2746313) B2746313
theorem B10424335 : Blo 1219427 10424335 := bstep (se 1 (by rfl) ⟨7818251, by rfl⟩ : syracuseStep 10424335 = 15636503) B15636503
theorem B9269477 : Blo 1219427 9269477 := bstep (se 4 (by rfl) ⟨869013, by rfl⟩ : syracuseStep 9269477 = 1738027) B1738027
theorem B4116797 : Blo 1219427 4116797 := bstep (se 3 (by rfl) ⟨771899, by rfl⟩ : syracuseStep 4116797 = 1543799) B1543799
theorem B1954153 : Blo 1219427 1954153 := bstep (se 2 (by rfl) ⟨732807, by rfl⟩ : syracuseStep 1954153 = 1465615) B1465615
theorem B3567997 : Blo 1219427 3567997 := bstep (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) B1337999
theorem B1831343 : Blo 1219427 1831343 := bstep (se 1 (by rfl) ⟨1373507, by rfl⟩ : syracuseStep 1831343 = 2747015) B2747015
theorem B40104409 : Blo 1219427 40104409 := bstep (se 2 (by rfl) ⟨15039153, by rfl⟩ : syracuseStep 40104409 = 30078307) B30078307
theorem B8344073 : Blo 1219427 8344073 := bstep (se 2 (by rfl) ⟨3129027, by rfl⟩ : syracuseStep 8344073 = 6258055) B6258055
theorem B1372711 : Blo 1219427 1372711 := bstep (se 1 (by rfl) ⟨1029533, by rfl⟩ : syracuseStep 1372711 = 2059067) B2059067
theorem B6599227 : Blo 1219427 6599227 := bstep (se 1 (by rfl) ⟨4949420, by rfl⟩ : syracuseStep 6599227 = 9898841) B9898841
theorem B1544827 : Blo 1219427 1544827 := bstep (se 1 (by rfl) ⟨1158620, by rfl⟩ : syracuseStep 1544827 = 2317241) B2317241
theorem B6689465 : Blo 1219427 6689465 := bstep (se 2 (by rfl) ⟨2508549, by rfl⟩ : syracuseStep 6689465 = 5017099) B5017099
theorem B4633463 : Blo 1219427 4633463 := bstep (se 1 (by rfl) ⟨3475097, by rfl⟩ : syracuseStep 4633463 = 6950195) B6950195
theorem B4117661 : Blo 1219427 4117661 := bstep (se 3 (by rfl) ⟨772061, by rfl⟩ : syracuseStep 4117661 = 1544123) B1544123
theorem B23459219 : Blo 1219427 23459219 := bstep (se 1 (by rfl) ⟨17594414, by rfl⟩ : syracuseStep 23459219 = 35188829) B35188829
theorem B10417571 : Blo 1219427 10417571 := bstep (se 1 (by rfl) ⟨7813178, by rfl⟩ : syracuseStep 10417571 = 15626357) B15626357
theorem B2381239 : Blo 1219427 2381239 := bstep (se 1 (by rfl) ⟨1785929, by rfl⟩ : syracuseStep 2381239 = 3571859) B3571859
theorem B8353243 : Blo 1219427 8353243 := bstep (se 1 (by rfl) ⟨6264932, by rfl⟩ : syracuseStep 8353243 = 12529865) B12529865
theorem B2315783 : Blo 1219427 2315783 := bstep (se 1 (by rfl) ⟨1736837, by rfl⟩ : syracuseStep 2315783 = 3473675) B3473675
theorem B4232729 : Blo 1219427 4232729 := bstep (se 2 (by rfl) ⟨1587273, by rfl⟩ : syracuseStep 4232729 = 3174547) B3174547
theorem B6174305 : Blo 1219427 6174305 := bstep (se 2 (by rfl) ⟨2315364, by rfl⟩ : syracuseStep 6174305 = 4630729) B4630729
theorem B4118201 : Blo 1219427 4118201 := bstep (se 2 (by rfl) ⟨1544325, by rfl⟩ : syracuseStep 4118201 = 3088651) B3088651
theorem B2930375 : Blo 1219427 2930375 := bstep (se 1 (by rfl) ⟨2197781, by rfl⟩ : syracuseStep 2930375 = 4395563) B4395563
theorem B2086649 : Blo 1219427 2086649 := bstep (se 2 (by rfl) ⟨782493, by rfl⟩ : syracuseStep 2086649 = 1564987) B1564987
theorem B5863211 : Blo 1219427 5863211 := bstep (se 1 (by rfl) ⟨4397408, by rfl⟩ : syracuseStep 5863211 = 8794817) B8794817
theorem B4634435 : Blo 1219427 4634435 := bstep (se 1 (by rfl) ⟨3475826, by rfl⟩ : syracuseStep 4634435 = 6951653) B6951653
theorem B2316215 : Blo 1219427 2316215 := bstep (se 1 (by rfl) ⟨1737161, by rfl⟩ : syracuseStep 2316215 = 3474323) B3474323
theorem B3348559 : Blo 1219427 3348559 := bstep (se 1 (by rfl) ⟨2511419, by rfl⟩ : syracuseStep 3348559 = 5022839) B5022839
theorem B2316367 : Blo 1219427 2316367 := bstep (se 1 (by rfl) ⟨1737275, by rfl⟩ : syracuseStep 2316367 = 3474551) B3474551
theorem B4118795 : Blo 1219427 4118795 := bstep (se 1 (by rfl) ⟨3089096, by rfl⟩ : syracuseStep 4118795 = 6178193) B6178193
theorem B4634891 : Blo 1219427 4634891 := bstep (se 1 (by rfl) ⟨3476168, by rfl⟩ : syracuseStep 4634891 = 6952337) B6952337
theorem B4119065 : Blo 1219427 4119065 := bstep (se 2 (by rfl) ⟨1544649, by rfl⟩ : syracuseStep 4119065 = 3089299) B3089299
theorem B2784095 : Blo 1219427 2784095 := bstep (se 1 (by rfl) ⟨2088071, by rfl⟩ : syracuseStep 2784095 = 4176143) B4176143
theorem B1219451 : Blo 1219427 1219451 := bstep (se 1 (by rfl) ⟨914588, by rfl⟩ : syracuseStep 1219451 = 1829177) B1829177
theorem B1219503 : Blo 1219427 1219503 := bstep (se 1 (by rfl) ⟨914627, by rfl⟩ : syracuseStep 1219503 = 1829255) B1829255
theorem B4635575 : Blo 1219427 4635575 := bstep (se 1 (by rfl) ⟨3476681, by rfl⟩ : syracuseStep 4635575 = 6953363) B6953363
theorem B1219527 : Blo 1219427 1219527 := bstep (se 1 (by rfl) ⟨914645, by rfl⟩ : syracuseStep 1219527 = 1829291) B1829291
theorem B1219547 : Blo 1219427 1219547 := bstep (se 1 (by rfl) ⟨914660, by rfl⟩ : syracuseStep 1219547 = 1829321) B1829321
theorem B6175763 : Blo 1219427 6175763 := bstep (se 1 (by rfl) ⟨4631822, by rfl⟩ : syracuseStep 6175763 = 9263645) B9263645
theorem B1219623 : Blo 1219427 1219623 := bstep (se 1 (by rfl) ⟨914717, by rfl⟩ : syracuseStep 1219623 = 1829435) B1829435
theorem B1219663 : Blo 1219427 1219663 := bstep (se 1 (by rfl) ⟨914747, by rfl⟩ : syracuseStep 1219663 = 1829495) B1829495
theorem B1219679 : Blo 1219427 1219679 := bstep (se 1 (by rfl) ⟨914759, by rfl⟩ : syracuseStep 1219679 = 1829519) B1829519
theorem B1219707 : Blo 1219427 1219707 := bstep (se 1 (by rfl) ⟨914780, by rfl⟩ : syracuseStep 1219707 = 1829561) B1829561
theorem B4947101 : Blo 1219427 4947101 := bstep (se 3 (by rfl) ⟨927581, by rfl⟩ : syracuseStep 4947101 = 1855163) B1855163
theorem B1219759 : Blo 1219427 1219759 := bstep (se 1 (by rfl) ⟨914819, by rfl⟩ : syracuseStep 1219759 = 1829639) B1829639
theorem B1219783 : Blo 1219427 1219783 := bstep (se 1 (by rfl) ⟨914837, by rfl⟩ : syracuseStep 1219783 = 1829675) B1829675
theorem B1219803 : Blo 1219427 1219803 := bstep (se 1 (by rfl) ⟨914852, by rfl⟩ : syracuseStep 1219803 = 1829705) B1829705
theorem B1219879 : Blo 1219427 1219879 := bstep (se 1 (by rfl) ⟨914909, by rfl⟩ : syracuseStep 1219879 = 1829819) B1829819
theorem B1219919 : Blo 1219427 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B1219935 : Blo 1219427 1219935 := bstep (se 1 (by rfl) ⟨914951, by rfl⟩ : syracuseStep 1219935 = 1829903) B1829903
theorem B2317673 : Blo 1219427 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B1219963 : Blo 1219427 1219963 := bstep (se 1 (by rfl) ⟨914972, by rfl⟩ : syracuseStep 1219963 = 1829945) B1829945
theorem B4398461 : Blo 1219427 4398461 := bstep (se 3 (by rfl) ⟨824711, by rfl⟩ : syracuseStep 4398461 = 1649423) B1649423
theorem B1220015 : Blo 1219427 1220015 := bstep (se 1 (by rfl) ⟨915011, by rfl⟩ : syracuseStep 1220015 = 1830023) B1830023
theorem B1220039 : Blo 1219427 1220039 := bstep (se 1 (by rfl) ⟨915029, by rfl⟩ : syracuseStep 1220039 = 1830059) B1830059
theorem B1220059 : Blo 1219427 1220059 := bstep (se 1 (by rfl) ⟨915044, by rfl⟩ : syracuseStep 1220059 = 1830089) B1830089
theorem B9395675 : Blo 1219427 9395675 := bstep (se 1 (by rfl) ⟨7046756, by rfl⟩ : syracuseStep 9395675 = 14093513) B14093513
theorem B2743847 : Blo 1219427 2743847 := bstep (se 1 (by rfl) ⟨2057885, by rfl⟩ : syracuseStep 2743847 = 4115771) B4115771
theorem B1220135 : Blo 1219427 1220135 := bstep (se 1 (by rfl) ⟨915101, by rfl⟩ : syracuseStep 1220135 = 1830203) B1830203
theorem B1220175 : Blo 1219427 1220175 := bstep (se 1 (by rfl) ⟨915131, by rfl⟩ : syracuseStep 1220175 = 1830263) B1830263
theorem B1220191 : Blo 1219427 1220191 := bstep (se 1 (by rfl) ⟨915143, by rfl⟩ : syracuseStep 1220191 = 1830287) B1830287
theorem B1220219 : Blo 1219427 1220219 := bstep (se 1 (by rfl) ⟨915164, by rfl⟩ : syracuseStep 1220219 = 1830329) B1830329
theorem B4120199 : Blo 1219427 4120199 := bstep (se 1 (by rfl) ⟨3090149, by rfl⟩ : syracuseStep 4120199 = 6180299) B6180299
theorem B8797841 : Blo 1219427 8797841 := bstep (se 2 (by rfl) ⟨3299190, by rfl⟩ : syracuseStep 8797841 = 6598381) B6598381
theorem B1220271 : Blo 1219427 1220271 := bstep (se 1 (by rfl) ⟨915203, by rfl⟩ : syracuseStep 1220271 = 1830407) B1830407
theorem B4120253 : Blo 1219427 4120253 := bstep (se 3 (by rfl) ⟨772547, by rfl⟩ : syracuseStep 4120253 = 1545095) B1545095
theorem B1220295 : Blo 1219427 1220295 := bstep (se 1 (by rfl) ⟨915221, by rfl⟩ : syracuseStep 1220295 = 1830443) B1830443
theorem B1220315 : Blo 1219427 1220315 := bstep (se 1 (by rfl) ⟨915236, by rfl⟩ : syracuseStep 1220315 = 1830473) B1830473
theorem B1220391 : Blo 1219427 1220391 := bstep (se 1 (by rfl) ⟨915293, by rfl⟩ : syracuseStep 1220391 = 1830587) B1830587
theorem B7814971 : Blo 1219427 7814971 := bstep (se 1 (by rfl) ⟨5861228, by rfl⟩ : syracuseStep 7814971 = 11722457) B11722457
theorem B1220431 : Blo 1219427 1220431 := bstep (se 1 (by rfl) ⟨915323, by rfl⟩ : syracuseStep 1220431 = 1830647) B1830647
theorem B1220447 : Blo 1219427 1220447 := bstep (se 1 (by rfl) ⟨915335, by rfl⟩ : syracuseStep 1220447 = 1830671) B1830671
theorem B4120415 : Blo 1219427 4120415 := bstep (se 1 (by rfl) ⟨3090311, by rfl⟩ : syracuseStep 4120415 = 6180623) B6180623
theorem B2744171 : Blo 1219427 2744171 := bstep (se 1 (by rfl) ⟨2058128, by rfl⟩ : syracuseStep 2744171 = 4116257) B4116257
theorem B3907435 : Blo 1219427 3907435 := bstep (se 1 (by rfl) ⟨2930576, by rfl⟩ : syracuseStep 3907435 = 5861153) B5861153
theorem B1220475 : Blo 1219427 1220475 := bstep (se 1 (by rfl) ⟨915356, by rfl⟩ : syracuseStep 1220475 = 1830713) B1830713
theorem B2744225 : Blo 1219427 2744225 := bstep (se 2 (by rfl) ⟨1029084, by rfl⟩ : syracuseStep 2744225 = 2058169) B2058169
theorem B4456367 : Blo 1219427 4456367 := bstep (se 1 (by rfl) ⟨3342275, by rfl⟩ : syracuseStep 4456367 = 6684551) B6684551
theorem B1220527 : Blo 1219427 1220527 := bstep (se 1 (by rfl) ⟨915395, by rfl⟩ : syracuseStep 1220527 = 1830791) B1830791
theorem B1220551 : Blo 1219427 1220551 := bstep (se 1 (by rfl) ⟨915413, by rfl⟩ : syracuseStep 1220551 = 1830827) B1830827
theorem B1220571 : Blo 1219427 1220571 := bstep (se 1 (by rfl) ⟨915428, by rfl⟩ : syracuseStep 1220571 = 1830857) B1830857
theorem B3088489 : Blo 1219427 3088489 := bstep (se 2 (by rfl) ⟨1158183, by rfl⟩ : syracuseStep 3088489 = 2316367) B2316367
theorem B2744531 : Blo 1219427 2744531 := bstep (se 1 (by rfl) ⟨2058398, by rfl⟩ : syracuseStep 2744531 = 4116797) B4116797
theorem B2744585 : Blo 1219427 2744585 := bstep (se 2 (by rfl) ⟨1029219, by rfl⟩ : syracuseStep 2744585 = 2058439) B2058439
theorem B1220895 : Blo 1219427 1220895 := bstep (se 1 (by rfl) ⟨915671, by rfl⟩ : syracuseStep 1220895 = 1831343) B1831343
theorem B5562715 : Blo 1219427 5562715 := bstep (se 1 (by rfl) ⟨4172036, by rfl⟩ : syracuseStep 5562715 = 8344073) B8344073
theorem B17858981 : Blo 1219427 17858981 := bstep (se 4 (by rfl) ⟨1674279, by rfl⟩ : syracuseStep 17858981 = 3348559) B3348559
theorem B3670447 : Blo 1219427 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B2744801 : Blo 1219427 2744801 := bstep (se 2 (by rfl) ⟨1029300, by rfl⟩ : syracuseStep 2744801 = 2058601) B2058601
theorem B2605537 : Blo 1219427 2605537 := bstep (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) B1954153
theorem B3088975 : Blo 1219427 3088975 := bstep (se 1 (by rfl) ⟨2316731, by rfl⟩ : syracuseStep 3088975 = 4633463) B4633463
theorem B2474671 : Blo 1219427 2474671 := bstep (se 1 (by rfl) ⟨1856003, by rfl⟩ : syracuseStep 2474671 = 3712007) B3712007
theorem B10420919 : Blo 1219427 10420919 := bstep (se 1 (by rfl) ⟨7815689, by rfl⟩ : syracuseStep 10420919 = 15631379) B15631379
theorem B6947531 : Blo 1219427 6947531 := bstep (se 1 (by rfl) ⟨5210648, by rfl⟩ : syracuseStep 6947531 = 10421297) B10421297
theorem B8798969 : Blo 1219427 8798969 := bstep (se 2 (by rfl) ⟨3299613, by rfl⟩ : syracuseStep 8798969 = 6599227) B6599227
theorem B2745107 : Blo 1219427 2745107 := bstep (se 1 (by rfl) ⟨2058830, by rfl⟩ : syracuseStep 2745107 = 4117661) B4117661
theorem B15639479 : Blo 1219427 15639479 := bstep (se 1 (by rfl) ⟨11729609, by rfl⟩ : syracuseStep 15639479 = 23459219) B23459219
theorem B1737703 : Blo 1219427 1737703 := bstep (se 1 (by rfl) ⟨1303277, by rfl⟩ : syracuseStep 1737703 = 2606555) B2606555
theorem B2745467 : Blo 1219427 2745467 := bstep (se 1 (by rfl) ⟨2059100, by rfl⟩ : syracuseStep 2745467 = 4118201) B4118201
theorem B3908807 : Blo 1219427 3908807 := bstep (se 1 (by rfl) ⟨2931605, by rfl⟩ : syracuseStep 3908807 = 5863211) B5863211
theorem B3089623 : Blo 1219427 3089623 := bstep (se 1 (by rfl) ⟨2317217, by rfl⟩ : syracuseStep 3089623 = 4634435) B4634435
theorem B2745593 : Blo 1219427 2745593 := bstep (se 2 (by rfl) ⟨1029597, by rfl⟩ : syracuseStep 2745593 = 2059195) B2059195
theorem B2745737 : Blo 1219427 2745737 := bstep (se 2 (by rfl) ⟨1029651, by rfl⟩ : syracuseStep 2745737 = 2059303) B2059303
theorem B5211553 : Blo 1219427 5211553 := bstep (se 2 (by rfl) ⟨1954332, by rfl⟩ : syracuseStep 5211553 = 3908665) B3908665
theorem B2745863 : Blo 1219427 2745863 := bstep (se 1 (by rfl) ⟨2059397, by rfl⟩ : syracuseStep 2745863 = 4118795) B4118795
theorem B3089927 : Blo 1219427 3089927 := bstep (se 1 (by rfl) ⟨2317445, by rfl⟩ : syracuseStep 3089927 = 4634891) B4634891
theorem B2746043 : Blo 1219427 2746043 := bstep (se 1 (by rfl) ⟨2059532, by rfl⟩ : syracuseStep 2746043 = 4119065) B4119065
theorem B2058041 : Blo 1219427 2058041 := bstep (se 2 (by rfl) ⟨771765, by rfl⟩ : syracuseStep 2058041 = 1543531) B1543531
theorem B2746169 : Blo 1219427 2746169 := bstep (se 2 (by rfl) ⟨1029813, by rfl⟩ : syracuseStep 2746169 = 2059627) B2059627
theorem B11724689 : Blo 1219427 11724689 := bstep (se 2 (by rfl) ⟨4396758, by rfl⟩ : syracuseStep 11724689 = 8793517) B8793517
theorem B3090383 : Blo 1219427 3090383 := bstep (se 1 (by rfl) ⟨2317787, by rfl⟩ : syracuseStep 3090383 = 4635575) B4635575
theorem B5212289 : Blo 1219427 5212289 := bstep (se 2 (by rfl) ⟨1954608, by rfl⟩ : syracuseStep 5212289 = 3909217) B3909217
theorem B5212441 : Blo 1219427 5212441 := bstep (se 2 (by rfl) ⟨1954665, by rfl⟩ : syracuseStep 5212441 = 3909331) B3909331
theorem B1829231 : Blo 1219427 1829231 := bstep (se 1 (by rfl) ⟨1371923, by rfl⟩ : syracuseStep 1829231 = 2743847) B2743847
theorem B10422695 : Blo 1219427 10422695 := bstep (se 1 (by rfl) ⟨7817021, by rfl⟩ : syracuseStep 10422695 = 15634043) B15634043
theorem B2746799 : Blo 1219427 2746799 := bstep (se 1 (by rfl) ⟨2060099, by rfl⟩ : syracuseStep 2746799 = 4120199) B4120199
theorem B2746835 : Blo 1219427 2746835 := bstep (se 1 (by rfl) ⟨2060126, by rfl⟩ : syracuseStep 2746835 = 4120253) B4120253
theorem B9898483 : Blo 1219427 9898483 := bstep (se 1 (by rfl) ⟨7423862, by rfl⟩ : syracuseStep 9898483 = 14847725) B14847725
theorem B3475963 : Blo 1219427 3475963 := bstep (se 1 (by rfl) ⟨2606972, by rfl⟩ : syracuseStep 3475963 = 5213945) B5213945
theorem B2746943 : Blo 1219427 2746943 := bstep (se 1 (by rfl) ⟨2060207, by rfl⟩ : syracuseStep 2746943 = 4120415) B4120415
theorem B1829447 : Blo 1219427 1829447 := bstep (se 1 (by rfl) ⟨1372085, by rfl⟩ : syracuseStep 1829447 = 2744171) B2744171
theorem B1829483 : Blo 1219427 1829483 := bstep (se 1 (by rfl) ⟨1372112, by rfl⟩ : syracuseStep 1829483 = 2744225) B2744225
theorem B2747051 : Blo 1219427 2747051 := bstep (se 1 (by rfl) ⟨2060288, by rfl⟩ : syracuseStep 2747051 = 4120577) B4120577
theorem B4631215 : Blo 1219427 4631215 := bstep (se 1 (by rfl) ⟨3473411, by rfl⟩ : syracuseStep 4631215 = 6946823) B6946823
theorem B6179651 : Blo 1219427 6179651 := bstep (se 1 (by rfl) ⟨4634738, by rfl⟩ : syracuseStep 6179651 = 9269477) B9269477
theorem B1829711 : Blo 1219427 1829711 := bstep (se 1 (by rfl) ⟨1372283, by rfl⟩ : syracuseStep 1829711 = 2744567) B2744567
theorem B2059087 : Blo 1219427 2059087 := bstep (se 1 (by rfl) ⟨1544315, by rfl⟩ : syracuseStep 2059087 = 3088631) B3088631
theorem B26750033 : Blo 1219427 26750033 := bstep (se 2 (by rfl) ⟨10031262, by rfl⟩ : syracuseStep 26750033 = 20062525) B20062525
theorem B45755479 : Blo 1219427 45755479 := bstep (se 1 (by rfl) ⟨34316609, by rfl⟩ : syracuseStep 45755479 = 68633219) B68633219
theorem B4459643 : Blo 1219427 4459643 := bstep (se 1 (by rfl) ⟨3344732, by rfl⟩ : syracuseStep 4459643 = 6689465) B6689465
theorem B1830107 : Blo 1219427 1830107 := bstep (se 1 (by rfl) ⟨1372580, by rfl⟩ : syracuseStep 1830107 = 2745161) B2745161
theorem B53472545 : Blo 1219427 53472545 := bstep (se 2 (by rfl) ⟨20052204, by rfl⟩ : syracuseStep 53472545 = 40104409) B40104409
theorem B1830281 : Blo 1219427 1830281 := bstep (se 2 (by rfl) ⟨686355, by rfl⟩ : syracuseStep 1830281 = 1372711) B1372711
theorem B3304891 : Blo 1219427 3304891 := bstep (se 1 (by rfl) ⟨2478668, by rfl⟩ : syracuseStep 3304891 = 4957337) B4957337
theorem B2059769 : Blo 1219427 2059769 := bstep (se 2 (by rfl) ⟨772413, by rfl⟩ : syracuseStep 2059769 = 1544827) B1544827
theorem B4632173 : Blo 1219427 4632173 := bstep (se 3 (by rfl) ⟨868532, by rfl⟩ : syracuseStep 4632173 = 1737065) B1737065
theorem B6180461 : Blo 1219427 6180461 := bstep (se 3 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 6180461 = 2317673) B2317673
theorem B1543855 : Blo 1219427 1543855 := bstep (se 1 (by rfl) ⟨1157891, by rfl⟩ : syracuseStep 1543855 = 2315783) B2315783
theorem B2821819 : Blo 1219427 2821819 := bstep (se 1 (by rfl) ⟨2116364, by rfl⟩ : syracuseStep 2821819 = 4232729) B4232729
theorem B4116203 : Blo 1219427 4116203 := bstep (se 1 (by rfl) ⟨3087152, by rfl⟩ : syracuseStep 4116203 = 6174305) B6174305
theorem B1830635 : Blo 1219427 1830635 := bstep (se 1 (by rfl) ⟨1372976, by rfl⟩ : syracuseStep 1830635 = 2745953) B2745953
theorem B2060039 : Blo 1219427 2060039 := bstep (se 1 (by rfl) ⟨1545029, by rfl⟩ : syracuseStep 2060039 = 3090059) B3090059
theorem B8458141 : Blo 1219427 8458141 := bstep (se 3 (by rfl) ⟨1585901, by rfl⟩ : syracuseStep 8458141 = 3171803) B3171803
theorem B1830863 : Blo 1219427 1830863 := bstep (se 1 (by rfl) ⟨1373147, by rfl⟩ : syracuseStep 1830863 = 2746295) B2746295
theorem B1372135 : Blo 1219427 1372135 := bstep (se 1 (by rfl) ⟨1029101, by rfl⟩ : syracuseStep 1372135 = 2058203) B2058203
theorem B1831259 : Blo 1219427 1831259 := bstep (se 1 (by rfl) ⟨1373444, by rfl⟩ : syracuseStep 1831259 = 2746889) B2746889
theorem B1856063 : Blo 1219427 1856063 := bstep (se 1 (by rfl) ⟨1392047, by rfl⟩ : syracuseStep 1856063 = 2784095) B2784095
theorem B4633159 : Blo 1219427 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B3174985 : Blo 1219427 3174985 := bstep (se 2 (by rfl) ⟨1190619, by rfl⟩ : syracuseStep 3174985 = 2381239) B2381239
theorem B11137657 : Blo 1219427 11137657 := bstep (se 2 (by rfl) ⟨4176621, by rfl⟩ : syracuseStep 11137657 = 8353243) B8353243
theorem B4117175 : Blo 1219427 4117175 := bstep (se 1 (by rfl) ⟨3087881, by rfl⟩ : syracuseStep 4117175 = 6175763) B6175763
theorem B3298067 : Blo 1219427 3298067 := bstep (se 1 (by rfl) ⟨2473550, by rfl⟩ : syracuseStep 3298067 = 4947101) B4947101
theorem B54203165 : Blo 1219427 54203165 := bstep (se 3 (by rfl) ⟨10163093, by rfl⟩ : syracuseStep 54203165 = 20326187) B20326187
theorem B6263783 : Blo 1219427 6263783 := bstep (se 1 (by rfl) ⟨4697837, by rfl⟩ : syracuseStep 6263783 = 9395675) B9395675
theorem B11728151 : Blo 1219427 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B2970911 : Blo 1219427 2970911 := bstep (se 1 (by rfl) ⟨2228183, by rfl⟩ : syracuseStep 2970911 = 4456367) B4456367
theorem B13899113 : Blo 1219427 13899113 := bstep (se 2 (by rfl) ⟨5212167, by rfl⟩ : syracuseStep 13899113 = 10424335) B10424335
theorem B4757329 : Blo 1219427 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B6945047 : Blo 1219427 6945047 := bstep (se 1 (by rfl) ⟨5208785, by rfl⟩ : syracuseStep 6945047 = 10417571) B10417571
theorem B3520793 : Blo 1219427 3520793 := bstep (se 2 (by rfl) ⟨1320297, by rfl⟩ : syracuseStep 3520793 = 2640595) B2640595
theorem B2316755 : Blo 1219427 2316755 := bstep (se 1 (by rfl) ⟨1737566, by rfl⟩ : syracuseStep 2316755 = 3475133) B3475133
theorem B1391099 : Blo 1219427 1391099 := bstep (se 1 (by rfl) ⟨1043324, by rfl⟩ : syracuseStep 1391099 = 2086649) B2086649
theorem B4119119 : Blo 1219427 4119119 := bstep (se 1 (by rfl) ⟨3089339, by rfl⟩ : syracuseStep 4119119 = 6178679) B6178679
theorem B3087031 : Blo 1219427 3087031 := bstep (se 1 (by rfl) ⟨2315273, by rfl⟩ : syracuseStep 3087031 = 4630547) B4630547
theorem B1219483 : Blo 1219427 1219483 := bstep (se 1 (by rfl) ⟨914612, by rfl⟩ : syracuseStep 1219483 = 1829225) B1829225
theorem B1219535 : Blo 1219427 1219535 := bstep (se 1 (by rfl) ⟨914651, by rfl⟩ : syracuseStep 1219535 = 1829303) B1829303
theorem B1219559 : Blo 1219427 1219559 := bstep (se 1 (by rfl) ⟨914669, by rfl⟩ : syracuseStep 1219559 = 1829339) B1829339
theorem B3087335 : Blo 1219427 3087335 := bstep (se 1 (by rfl) ⟨2315501, by rfl⟩ : syracuseStep 3087335 = 4631003) B4631003
theorem B44547245 : Blo 1219427 44547245 := bstep (se 3 (by rfl) ⟨8352608, by rfl⟩ : syracuseStep 44547245 = 16705217) B16705217
theorem B7814333 : Blo 1219427 7814333 := bstep (se 3 (by rfl) ⟨1465187, by rfl⟩ : syracuseStep 7814333 = 2930375) B2930375
theorem B1219871 : Blo 1219427 1219871 := bstep (se 1 (by rfl) ⟨914903, by rfl⟩ : syracuseStep 1219871 = 1829807) B1829807
theorem B1219931 : Blo 1219427 1219931 := bstep (se 1 (by rfl) ⟨914948, by rfl⟩ : syracuseStep 1219931 = 1829897) B1829897
theorem B1219951 : Blo 1219427 1219951 := bstep (se 1 (by rfl) ⟨914963, by rfl⟩ : syracuseStep 1219951 = 1829927) B1829927
theorem B1220007 : Blo 1219427 1220007 := bstep (se 1 (by rfl) ⟨915005, by rfl⟩ : syracuseStep 1220007 = 1830011) B1830011
theorem B2743739 : Blo 1219427 2743739 := bstep (se 1 (by rfl) ⟨2057804, by rfl⟩ : syracuseStep 2743739 = 4115609) B4115609
theorem B6176249 : Blo 1219427 6176249 := bstep (se 2 (by rfl) ⟨2316093, by rfl⟩ : syracuseStep 6176249 = 4632187) B4632187
theorem B1220091 : Blo 1219427 1220091 := bstep (se 1 (by rfl) ⟨915068, by rfl⟩ : syracuseStep 1220091 = 1830137) B1830137
theorem B2743865 : Blo 1219427 2743865 := bstep (se 2 (by rfl) ⟨1028949, by rfl⟩ : syracuseStep 2743865 = 2057899) B2057899
theorem B1220159 : Blo 1219427 1220159 := bstep (se 1 (by rfl) ⟨915119, by rfl⟩ : syracuseStep 1220159 = 1830239) B1830239
theorem B1220167 : Blo 1219427 1220167 := bstep (se 1 (by rfl) ⟨915125, by rfl⟩ : syracuseStep 1220167 = 1830251) B1830251
theorem B2932307 : Blo 1219427 2932307 := bstep (se 1 (by rfl) ⟨2199230, by rfl⟩ : syracuseStep 2932307 = 4398461) B4398461
theorem B1220319 : Blo 1219427 1220319 := bstep (se 1 (by rfl) ⟨915239, by rfl⟩ : syracuseStep 1220319 = 1830479) B1830479
theorem B10419961 : Blo 1219427 10419961 := bstep (se 2 (by rfl) ⟨3907485, by rfl⟩ : syracuseStep 10419961 = 7814971) B7814971
theorem B5865227 : Blo 1219427 5865227 := bstep (se 1 (by rfl) ⟨4398920, by rfl⟩ : syracuseStep 5865227 = 8797841) B8797841
theorem B4120361 : Blo 1219427 4120361 := bstep (se 2 (by rfl) ⟨1545135, by rfl⟩ : syracuseStep 4120361 = 3090271) B3090271
theorem B1220399 : Blo 1219427 1220399 := bstep (se 1 (by rfl) ⟨915299, by rfl⟩ : syracuseStep 1220399 = 1830599) B1830599
theorem B5209913 : Blo 1219427 5209913 := bstep (se 2 (by rfl) ⟨1953717, by rfl⟩ : syracuseStep 5209913 = 3907435) B3907435
theorem B2932537 : Blo 1219427 2932537 := bstep (se 2 (by rfl) ⟨1099701, by rfl⟩ : syracuseStep 2932537 = 2199403) B2199403
theorem B6176573 : Blo 1219427 6176573 := bstep (se 3 (by rfl) ⟨1158107, by rfl⟩ : syracuseStep 6176573 = 2316215) B2316215
theorem B1302427 : Blo 1219427 1302427 := bstep (se 1 (by rfl) ⟨976820, by rfl⟩ : syracuseStep 1302427 = 1953641) B1953641
theorem B1220507 : Blo 1219427 1220507 := bstep (se 1 (by rfl) ⟨915380, by rfl⟩ : syracuseStep 1220507 = 1830761) B1830761
theorem B1220559 : Blo 1219427 1220559 := bstep (se 1 (by rfl) ⟨915419, by rfl⟩ : syracuseStep 1220559 = 1830839) B1830839
theorem B1220583 : Blo 1219427 1220583 := bstep (se 1 (by rfl) ⟨915437, by rfl⟩ : syracuseStep 1220583 = 1830875) B1830875
theorem B1220839 : Blo 1219427 1220839 := bstep (se 1 (by rfl) ⟨915629, by rfl⟩ : syracuseStep 1220839 = 1831259) B1831259
theorem B1237375 : Blo 1219427 1237375 := bstep (se 1 (by rfl) ⟨928031, by rfl⟩ : syracuseStep 1237375 = 1856063) B1856063
theorem B6947279 : Blo 1219427 6947279 := bstep (se 1 (by rfl) ⟨5210459, by rfl⟩ : syracuseStep 6947279 = 10420919) B10420919
theorem B2744783 : Blo 1219427 2744783 := bstep (se 1 (by rfl) ⟨2058587, by rfl⟩ : syracuseStep 2744783 = 4117175) B4117175
theorem B5865979 : Blo 1219427 5865979 := bstep (se 1 (by rfl) ⟨4399484, by rfl⟩ : syracuseStep 5865979 = 8798969) B8798969
theorem B36135443 : Blo 1219427 36135443 := bstep (se 1 (by rfl) ⟨27101582, by rfl⟩ : syracuseStep 36135443 = 54203165) B54203165
theorem B13197977 : Blo 1219427 13197977 := bstep (se 2 (by rfl) ⟨4949241, by rfl⟩ : syracuseStep 13197977 = 9898483) B9898483
theorem B9388781 : Blo 1219427 9388781 := bstep (se 3 (by rfl) ⟨1760396, by rfl⟩ : syracuseStep 9388781 = 3520793) B3520793
theorem B6177545 : Blo 1219427 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B2605871 : Blo 1219427 2605871 := bstep (se 1 (by rfl) ⟨1954403, by rfl⟩ : syracuseStep 2605871 = 3908807) B3908807
theorem B9266075 : Blo 1219427 9266075 := bstep (se 1 (by rfl) ⟨6949556, by rfl⟩ : syracuseStep 9266075 = 13899113) B13899113
theorem B2745449 : Blo 1219427 2745449 := bstep (se 2 (by rfl) ⟨1029543, by rfl⟩ : syracuseStep 2745449 = 2059087) B2059087
theorem B7816459 : Blo 1219427 7816459 := bstep (se 1 (by rfl) ⟨5862344, by rfl⟩ : syracuseStep 7816459 = 11724689) B11724689
theorem B3474859 : Blo 1219427 3474859 := bstep (se 1 (by rfl) ⟨2606144, by rfl⟩ : syracuseStep 3474859 = 5212289) B5212289
theorem B61007305 : Blo 1219427 61007305 := bstep (se 2 (by rfl) ⟨22877739, by rfl⟩ : syracuseStep 61007305 = 45755479) B45755479
theorem B4630031 : Blo 1219427 4630031 := bstep (se 1 (by rfl) ⟨3472523, by rfl⟩ : syracuseStep 4630031 = 6945047) B6945047
theorem B6948463 : Blo 1219427 6948463 := bstep (se 1 (by rfl) ⟨5211347, by rfl⟩ : syracuseStep 6948463 = 10422695) B10422695
theorem B2746079 : Blo 1219427 2746079 := bstep (se 1 (by rfl) ⟨2059559, by rfl⟩ : syracuseStep 2746079 = 4119119) B4119119
theorem B6948737 : Blo 1219427 6948737 := bstep (se 2 (by rfl) ⟨2605776, by rfl⟩ : syracuseStep 6948737 = 5211553) B5211553
theorem B2058223 : Blo 1219427 2058223 := bstep (se 1 (by rfl) ⟨1543667, by rfl⟩ : syracuseStep 2058223 = 3087335) B3087335
theorem B29698163 : Blo 1219427 29698163 := bstep (se 1 (by rfl) ⟨22273622, by rfl⟩ : syracuseStep 29698163 = 44547245) B44547245
theorem B2058473 : Blo 1219427 2058473 := bstep (se 2 (by rfl) ⟨771927, by rfl⟩ : syracuseStep 2058473 = 1543855) B1543855
theorem B3762425 : Blo 1219427 3762425 := bstep (se 2 (by rfl) ⟨1410909, by rfl⟩ : syracuseStep 3762425 = 2821819) B2821819
theorem B1829159 : Blo 1219427 1829159 := bstep (se 1 (by rfl) ⟨1371869, by rfl⟩ : syracuseStep 1829159 = 2743739) B2743739
theorem B1829243 : Blo 1219427 1829243 := bstep (se 1 (by rfl) ⟨1371932, by rfl⟩ : syracuseStep 1829243 = 2743865) B2743865
theorem B3910049 : Blo 1219427 3910049 := bstep (se 2 (by rfl) ⟨1466268, by rfl⟩ : syracuseStep 3910049 = 2932537) B2932537
theorem B6343105 : Blo 1219427 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B13896197 : Blo 1219427 13896197 := bstep (se 4 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 13896197 = 2605537) B2605537
theorem B3910151 : Blo 1219427 3910151 := bstep (se 1 (by rfl) ⟨2932613, by rfl⟩ : syracuseStep 3910151 = 5865227) B5865227
theorem B2746907 : Blo 1219427 2746907 := bstep (se 1 (by rfl) ⟨2060180, by rfl⟩ : syracuseStep 2746907 = 4120361) B4120361
theorem B1829513 : Blo 1219427 1829513 := bstep (se 2 (by rfl) ⟨686067, by rfl⟩ : syracuseStep 1829513 = 1372135) B1372135
theorem B1829687 : Blo 1219427 1829687 := bstep (se 1 (by rfl) ⟨1372265, by rfl⟩ : syracuseStep 1829687 = 2744531) B2744531
theorem B1829723 : Blo 1219427 1829723 := bstep (se 1 (by rfl) ⟨1372292, by rfl⟩ : syracuseStep 1829723 = 2744585) B2744585
theorem B11905987 : Blo 1219427 11905987 := bstep (se 1 (by rfl) ⟨8929490, by rfl⟩ : syracuseStep 11905987 = 17858981) B17858981
theorem B1829867 : Blo 1219427 1829867 := bstep (se 1 (by rfl) ⟨1372400, by rfl⟩ : syracuseStep 1829867 = 2744801) B2744801
theorem B6949921 : Blo 1219427 6949921 := bstep (se 2 (by rfl) ⟨2606220, by rfl⟩ : syracuseStep 6949921 = 5212441) B5212441
theorem B7416953 : Blo 1219427 7416953 := bstep (se 2 (by rfl) ⟨2781357, by rfl⟩ : syracuseStep 7416953 = 5562715) B5562715
theorem B4631687 : Blo 1219427 4631687 := bstep (se 1 (by rfl) ⟨3473765, by rfl⟩ : syracuseStep 4631687 = 6947531) B6947531
theorem B1830071 : Blo 1219427 1830071 := bstep (se 1 (by rfl) ⟨1372553, by rfl⟩ : syracuseStep 1830071 = 2745107) B2745107
theorem B2198711 : Blo 1219427 2198711 := bstep (se 1 (by rfl) ⟨1649033, by rfl⟩ : syracuseStep 2198711 = 3298067) B3298067
theorem B4893929 : Blo 1219427 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B1830311 : Blo 1219427 1830311 := bstep (se 1 (by rfl) ⟨1372733, by rfl⟩ : syracuseStep 1830311 = 2745467) B2745467
theorem B1830395 : Blo 1219427 1830395 := bstep (se 1 (by rfl) ⟨1372796, by rfl⟩ : syracuseStep 1830395 = 2745593) B2745593
theorem B7818767 : Blo 1219427 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B4116041 : Blo 1219427 4116041 := bstep (se 2 (by rfl) ⟨1543515, by rfl⟩ : syracuseStep 4116041 = 3087031) B3087031
theorem B1830491 : Blo 1219427 1830491 := bstep (se 1 (by rfl) ⟨1372868, by rfl⟩ : syracuseStep 1830491 = 2745737) B2745737
theorem B1830575 : Blo 1219427 1830575 := bstep (se 1 (by rfl) ⟨1372931, by rfl⟩ : syracuseStep 1830575 = 2745863) B2745863
theorem B2059951 : Blo 1219427 2059951 := bstep (se 1 (by rfl) ⟨1544963, by rfl⟩ : syracuseStep 2059951 = 3089927) B3089927
theorem B1830695 : Blo 1219427 1830695 := bstep (se 1 (by rfl) ⟨1373021, by rfl⟩ : syracuseStep 1830695 = 2746043) B2746043
theorem B1372027 : Blo 1219427 1372027 := bstep (se 1 (by rfl) ⟨1029020, by rfl⟩ : syracuseStep 1372027 = 2058041) B2058041
theorem B1830779 : Blo 1219427 1830779 := bstep (se 1 (by rfl) ⟨1373084, by rfl⟩ : syracuseStep 1830779 = 2746169) B2746169
theorem B2060255 : Blo 1219427 2060255 := bstep (se 1 (by rfl) ⟨1545191, by rfl⟩ : syracuseStep 2060255 = 3090383) B3090383
theorem B1831199 : Blo 1219427 1831199 := bstep (se 1 (by rfl) ⟨1373399, by rfl⟩ : syracuseStep 1831199 = 2746799) B2746799
theorem B1544503 : Blo 1219427 1544503 := bstep (se 1 (by rfl) ⟨1158377, by rfl⟩ : syracuseStep 1544503 = 2316755) B2316755
theorem B1831223 : Blo 1219427 1831223 := bstep (se 1 (by rfl) ⟨1373417, by rfl⟩ : syracuseStep 1831223 = 2746835) B2746835
theorem B1831295 : Blo 1219427 1831295 := bstep (se 1 (by rfl) ⟨1373471, by rfl⟩ : syracuseStep 1831295 = 2746943) B2746943
theorem B1831367 : Blo 1219427 1831367 := bstep (se 1 (by rfl) ⟨1373525, by rfl⟩ : syracuseStep 1831367 = 2747051) B2747051
theorem B35648363 : Blo 1219427 35648363 := bstep (se 1 (by rfl) ⟨26736272, by rfl⟩ : syracuseStep 35648363 = 53472545) B53472545
theorem B4117499 : Blo 1219427 4117499 := bstep (se 1 (by rfl) ⟨3088124, by rfl⟩ : syracuseStep 4117499 = 6176249) B6176249
theorem B1373179 : Blo 1219427 1373179 := bstep (se 1 (by rfl) ⟨1029884, by rfl⟩ : syracuseStep 1373179 = 2059769) B2059769
theorem B1954871 : Blo 1219427 1954871 := bstep (se 1 (by rfl) ⟨1466153, by rfl⟩ : syracuseStep 1954871 = 2932307) B2932307
theorem B1373359 : Blo 1219427 1373359 := bstep (se 1 (by rfl) ⟨1030019, by rfl⟩ : syracuseStep 1373359 = 2060039) B2060039
theorem B11277521 : Blo 1219427 11277521 := bstep (se 2 (by rfl) ⟨4229070, by rfl⟩ : syracuseStep 11277521 = 8458141) B8458141
theorem B4117715 : Blo 1219427 4117715 := bstep (se 1 (by rfl) ⟨3088286, by rfl⟩ : syracuseStep 4117715 = 6176573) B6176573
theorem B4117985 : Blo 1219427 4117985 := bstep (se 2 (by rfl) ⟨1544244, by rfl⟩ : syracuseStep 4117985 = 3088489) B3088489
theorem B10426319 : Blo 1219427 10426319 := bstep (se 1 (by rfl) ⟨7819739, by rfl⟩ : syracuseStep 10426319 = 15639479) B15639479
theorem B4175855 : Blo 1219427 4175855 := bstep (se 1 (by rfl) ⟨3131891, by rfl⟩ : syracuseStep 4175855 = 6263783) B6263783
theorem B4634617 : Blo 1219427 4634617 := bstep (se 2 (by rfl) ⟨1737981, by rfl⟩ : syracuseStep 4634617 = 3475963) B3475963
theorem B4233313 : Blo 1219427 4233313 := bstep (se 2 (by rfl) ⟨1587492, by rfl⟩ : syracuseStep 4233313 = 3174985) B3174985
theorem B4118633 : Blo 1219427 4118633 := bstep (se 2 (by rfl) ⟨1544487, by rfl⟩ : syracuseStep 4118633 = 3088975) B3088975
theorem B14850209 : Blo 1219427 14850209 := bstep (se 2 (by rfl) ⟨5568828, by rfl⟩ : syracuseStep 14850209 = 11137657) B11137657
theorem B1980607 : Blo 1219427 1980607 := bstep (se 1 (by rfl) ⟨1485455, by rfl⟩ : syracuseStep 1980607 = 2970911) B2970911
theorem B6174953 : Blo 1219427 6174953 := bstep (se 2 (by rfl) ⟨2315607, by rfl⟩ : syracuseStep 6174953 = 4631215) B4631215
theorem B3299561 : Blo 1219427 3299561 := bstep (se 2 (by rfl) ⟨1237335, by rfl⟩ : syracuseStep 3299561 = 2474671) B2474671
theorem B2316937 : Blo 1219427 2316937 := bstep (se 2 (by rfl) ⟨868851, by rfl⟩ : syracuseStep 2316937 = 1737703) B1737703
theorem B3709597 : Blo 1219427 3709597 := bstep (se 3 (by rfl) ⟨695549, by rfl⟩ : syracuseStep 3709597 = 1391099) B1391099
theorem B1219487 : Blo 1219427 1219487 := bstep (se 1 (by rfl) ⟨914615, by rfl⟩ : syracuseStep 1219487 = 1829231) B1829231
theorem B4119497 : Blo 1219427 4119497 := bstep (se 2 (by rfl) ⟨1544811, by rfl⟩ : syracuseStep 4119497 = 3089623) B3089623
theorem B1219631 : Blo 1219427 1219631 := bstep (se 1 (by rfl) ⟨914723, by rfl⟩ : syracuseStep 1219631 = 1829447) B1829447
theorem B1219655 : Blo 1219427 1219655 := bstep (se 1 (by rfl) ⟨914741, by rfl⟩ : syracuseStep 1219655 = 1829483) B1829483
theorem B4119767 : Blo 1219427 4119767 := bstep (se 1 (by rfl) ⟨3089825, by rfl⟩ : syracuseStep 4119767 = 6179651) B6179651
theorem B1219807 : Blo 1219427 1219807 := bstep (se 1 (by rfl) ⟨914855, by rfl⟩ : syracuseStep 1219807 = 1829711) B1829711
theorem B4406521 : Blo 1219427 4406521 := bstep (se 2 (by rfl) ⟨1652445, by rfl⟩ : syracuseStep 4406521 = 3304891) B3304891
theorem B17833355 : Blo 1219427 17833355 := bstep (se 1 (by rfl) ⟨13375016, by rfl⟩ : syracuseStep 17833355 = 26750033) B26750033
theorem B2973095 : Blo 1219427 2973095 := bstep (se 1 (by rfl) ⟨2229821, by rfl⟩ : syracuseStep 2973095 = 4459643) B4459643
theorem B5209555 : Blo 1219427 5209555 := bstep (se 1 (by rfl) ⟨3907166, by rfl⟩ : syracuseStep 5209555 = 7814333) B7814333
theorem B1220071 : Blo 1219427 1220071 := bstep (se 1 (by rfl) ⟨915053, by rfl⟩ : syracuseStep 1220071 = 1830107) B1830107
theorem B1220187 : Blo 1219427 1220187 := bstep (se 1 (by rfl) ⟨915140, by rfl⟩ : syracuseStep 1220187 = 1830281) B1830281
theorem B13893281 : Blo 1219427 13893281 := bstep (se 2 (by rfl) ⟨5209980, by rfl⟩ : syracuseStep 13893281 = 10419961) B10419961
theorem B3088115 : Blo 1219427 3088115 := bstep (se 1 (by rfl) ⟨2316086, by rfl⟩ : syracuseStep 3088115 = 4632173) B4632173
theorem B4120307 : Blo 1219427 4120307 := bstep (se 1 (by rfl) ⟨3090230, by rfl⟩ : syracuseStep 4120307 = 6180461) B6180461
theorem B2744135 : Blo 1219427 2744135 := bstep (se 1 (by rfl) ⟨2058101, by rfl⟩ : syracuseStep 2744135 = 4116203) B4116203
theorem B1220423 : Blo 1219427 1220423 := bstep (se 1 (by rfl) ⟨915317, by rfl⟩ : syracuseStep 1220423 = 1830635) B1830635
theorem B1736569 : Blo 1219427 1736569 := bstep (se 2 (by rfl) ⟨651213, by rfl⟩ : syracuseStep 1736569 = 1302427) B1302427
theorem B3473275 : Blo 1219427 3473275 := bstep (se 1 (by rfl) ⟨2604956, by rfl⟩ : syracuseStep 3473275 = 5209913) B5209913
theorem B1220575 : Blo 1219427 1220575 := bstep (se 1 (by rfl) ⟨915431, by rfl⟩ : syracuseStep 1220575 = 1830863) B1830863
theorem B5644417 : Blo 1219427 5644417 := bstep (se 2 (by rfl) ⟨2116656, by rfl⟩ : syracuseStep 5644417 = 4233313) B4233313
theorem B1220799 : Blo 1219427 1220799 := bstep (se 1 (by rfl) ⟨915599, by rfl⟩ : syracuseStep 1220799 = 1831199) B1831199
theorem B1220815 : Blo 1219427 1220815 := bstep (se 1 (by rfl) ⟨915611, by rfl⟩ : syracuseStep 1220815 = 1831223) B1831223
theorem B1220863 : Blo 1219427 1220863 := bstep (se 1 (by rfl) ⟨915647, by rfl⟩ : syracuseStep 1220863 = 1831295) B1831295
theorem B1220911 : Blo 1219427 1220911 := bstep (se 1 (by rfl) ⟨915683, by rfl⟩ : syracuseStep 1220911 = 1831367) B1831367
theorem B8798651 : Blo 1219427 8798651 := bstep (se 1 (by rfl) ⟨6598988, by rfl⟩ : syracuseStep 8798651 = 13197977) B13197977
theorem B6259187 : Blo 1219427 6259187 := bstep (se 1 (by rfl) ⟨4694390, by rfl⟩ : syracuseStep 6259187 = 9388781) B9388781
theorem B23765575 : Blo 1219427 23765575 := bstep (se 1 (by rfl) ⟨17824181, by rfl⟩ : syracuseStep 23765575 = 35648363) B35648363
theorem B6177383 : Blo 1219427 6177383 := bstep (se 1 (by rfl) ⟨4633037, by rfl⟩ : syracuseStep 6177383 = 9266075) B9266075
theorem B2744999 : Blo 1219427 2744999 := bstep (se 1 (by rfl) ⟨2058749, by rfl⟩ : syracuseStep 2744999 = 4117499) B4117499
theorem B1303247 : Blo 1219427 1303247 := bstep (se 1 (by rfl) ⟨977435, by rfl⟩ : syracuseStep 1303247 = 1954871) B1954871
theorem B2745143 : Blo 1219427 2745143 := bstep (se 1 (by rfl) ⟨2058857, by rfl⟩ : syracuseStep 2745143 = 4117715) B4117715
theorem B3089249 : Blo 1219427 3089249 := bstep (se 2 (by rfl) ⟨1158468, by rfl⟩ : syracuseStep 3089249 = 2316937) B2316937
theorem B2745323 : Blo 1219427 2745323 := bstep (se 1 (by rfl) ⟨2058992, by rfl⟩ : syracuseStep 2745323 = 4117985) B4117985
theorem B9266561 : Blo 1219427 9266561 := bstep (se 2 (by rfl) ⟨3474960, by rfl⟩ : syracuseStep 9266561 = 6949921) B6949921
theorem B2745755 : Blo 1219427 2745755 := bstep (se 1 (by rfl) ⟨2059316, by rfl⟩ : syracuseStep 2745755 = 4118633) B4118633
theorem B2508283 : Blo 1219427 2508283 := bstep (se 1 (by rfl) ⟨1881212, by rfl⟩ : syracuseStep 2508283 = 3762425) B3762425
theorem B2606699 : Blo 1219427 2606699 := bstep (se 1 (by rfl) ⟨1955024, by rfl⟩ : syracuseStep 2606699 = 3910049) B3910049
theorem B5875361 : Blo 1219427 5875361 := bstep (se 2 (by rfl) ⟨2203260, by rfl⟩ : syracuseStep 5875361 = 4406521) B4406521
theorem B10421945 : Blo 1219427 10421945 := bstep (se 2 (by rfl) ⟨3908229, by rfl⟩ : syracuseStep 10421945 = 7816459) B7816459
theorem B2746331 : Blo 1219427 2746331 := bstep (se 1 (by rfl) ⟨2059748, by rfl⟩ : syracuseStep 2746331 = 4119497) B4119497
theorem B6948989 : Blo 1219427 6948989 := bstep (se 3 (by rfl) ⟨1302935, by rfl⟩ : syracuseStep 6948989 = 2605871) B2605871
theorem B2746511 : Blo 1219427 2746511 := bstep (se 1 (by rfl) ⟨2059883, by rfl⟩ : syracuseStep 2746511 = 4119767) B4119767
theorem B3262619 : Blo 1219427 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B2746601 : Blo 1219427 2746601 := bstep (se 2 (by rfl) ⟨1029975, by rfl⟩ : syracuseStep 2746601 = 2059951) B2059951
theorem B11888903 : Blo 1219427 11888903 := bstep (se 1 (by rfl) ⟨8916677, by rfl⟩ : syracuseStep 11888903 = 17833355) B17833355
theorem B5212511 : Blo 1219427 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B2058743 : Blo 1219427 2058743 := bstep (se 1 (by rfl) ⟨1544057, by rfl⟩ : syracuseStep 2058743 = 3088115) B3088115
theorem B2746871 : Blo 1219427 2746871 := bstep (se 1 (by rfl) ⟨2060153, by rfl⟩ : syracuseStep 2746871 = 4120307) B4120307
theorem B1829369 : Blo 1219427 1829369 := bstep (se 2 (by rfl) ⟨686013, by rfl⟩ : syracuseStep 1829369 = 1372027) B1372027
theorem B4631033 : Blo 1219427 4631033 := bstep (se 2 (by rfl) ⟨1736637, by rfl⟩ : syracuseStep 4631033 = 3473275) B3473275
theorem B1829423 : Blo 1219427 1829423 := bstep (se 1 (by rfl) ⟨1372067, by rfl⟩ : syracuseStep 1829423 = 2744135) B2744135
theorem B6179489 : Blo 1219427 6179489 := bstep (se 2 (by rfl) ⟨2317308, by rfl⟩ : syracuseStep 6179489 = 4634617) B4634617
theorem B2640809 : Blo 1219427 2640809 := bstep (se 2 (by rfl) ⟨990303, by rfl⟩ : syracuseStep 2640809 = 1980607) B1980607
theorem B4631519 : Blo 1219427 4631519 := bstep (se 1 (by rfl) ⟨3473639, by rfl⟩ : syracuseStep 4631519 = 6947279) B6947279
theorem B1829855 : Blo 1219427 1829855 := bstep (se 1 (by rfl) ⟨1372391, by rfl⟩ : syracuseStep 1829855 = 2744783) B2744783
theorem B2059337 : Blo 1219427 2059337 := bstep (se 2 (by rfl) ⟨772251, by rfl⟩ : syracuseStep 2059337 = 1544503) B1544503
theorem B8457473 : Blo 1219427 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B1830299 : Blo 1219427 1830299 := bstep (se 1 (by rfl) ⟨1372724, by rfl⟩ : syracuseStep 1830299 = 2745449) B2745449
theorem B1830719 : Blo 1219427 1830719 := bstep (se 1 (by rfl) ⟨1373039, by rfl⟩ : syracuseStep 1830719 = 2746079) B2746079
theorem B4632491 : Blo 1219427 4632491 := bstep (se 1 (by rfl) ⟨3474368, by rfl⟩ : syracuseStep 4632491 = 6948737) B6948737
theorem B6950879 : Blo 1219427 6950879 := bstep (se 1 (by rfl) ⟨5213159, by rfl⟩ : syracuseStep 6950879 = 10426319) B10426319
theorem B1830905 : Blo 1219427 1830905 := bstep (se 2 (by rfl) ⟨686589, by rfl⟩ : syracuseStep 1830905 = 1373179) B1373179
theorem B9900139 : Blo 1219427 9900139 := bstep (se 1 (by rfl) ⟨7425104, by rfl⟩ : syracuseStep 9900139 = 14850209) B14850209
theorem B4116635 : Blo 1219427 4116635 := bstep (se 1 (by rfl) ⟨3087476, by rfl⟩ : syracuseStep 4116635 = 6174953) B6174953
theorem B1372315 : Blo 1219427 1372315 := bstep (se 1 (by rfl) ⟨1029236, by rfl⟩ : syracuseStep 1372315 = 2058473) B2058473
theorem B2199707 : Blo 1219427 2199707 := bstep (se 1 (by rfl) ⟨1649780, by rfl⟩ : syracuseStep 2199707 = 3299561) B3299561
theorem B1831145 : Blo 1219427 1831145 := bstep (se 2 (by rfl) ⟨686679, by rfl⟩ : syracuseStep 1831145 = 1373359) B1373359
theorem B1831271 : Blo 1219427 1831271 := bstep (se 1 (by rfl) ⟨1373453, by rfl⟩ : syracuseStep 1831271 = 2746907) B2746907
theorem B4633145 : Blo 1219427 4633145 := bstep (se 2 (by rfl) ⟨1737429, by rfl⟩ : syracuseStep 4633145 = 3474859) B3474859
theorem B81343073 : Blo 1219427 81343073 := bstep (se 2 (by rfl) ⟨30503652, by rfl⟩ : syracuseStep 81343073 = 61007305) B61007305
theorem B9261701 : Blo 1219427 9261701 := bstep (se 4 (by rfl) ⟨868284, by rfl⟩ : syracuseStep 9261701 = 1736569) B1736569
theorem B6599333 : Blo 1219427 6599333 := bstep (se 4 (by rfl) ⟨618687, by rfl⟩ : syracuseStep 6599333 = 1237375) B1237375
theorem B4944635 : Blo 1219427 4944635 := bstep (se 1 (by rfl) ⟨3708476, by rfl⟩ : syracuseStep 4944635 = 7416953) B7416953
theorem B9262187 : Blo 1219427 9262187 := bstep (se 1 (by rfl) ⟨6946640, by rfl⟩ : syracuseStep 9262187 = 13893281) B13893281
theorem B1373503 : Blo 1219427 1373503 := bstep (se 1 (by rfl) ⟨1030127, by rfl⟩ : syracuseStep 1373503 = 2060255) B2060255
theorem B24090295 : Blo 1219427 24090295 := bstep (se 1 (by rfl) ⟨18067721, by rfl⟩ : syracuseStep 24090295 = 36135443) B36135443
theorem B5863229 : Blo 1219427 5863229 := bstep (se 3 (by rfl) ⟨1099355, by rfl⟩ : syracuseStep 5863229 = 2198711) B2198711
theorem B4118363 : Blo 1219427 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B7821305 : Blo 1219427 7821305 := bstep (se 2 (by rfl) ⟨2932989, by rfl⟩ : syracuseStep 7821305 = 5865979) B5865979
theorem B7518347 : Blo 1219427 7518347 := bstep (se 1 (by rfl) ⟨5638760, by rfl⟩ : syracuseStep 7518347 = 11277521) B11277521
theorem B4946129 : Blo 1219427 4946129 := bstep (se 2 (by rfl) ⟨1854798, by rfl⟩ : syracuseStep 4946129 = 3709597) B3709597
theorem B3086687 : Blo 1219427 3086687 := bstep (se 1 (by rfl) ⟨2315015, by rfl⟩ : syracuseStep 3086687 = 4630031) B4630031
theorem B15874649 : Blo 1219427 15874649 := bstep (se 2 (by rfl) ⟨5952993, by rfl⟩ : syracuseStep 15874649 = 11905987) B11905987
theorem B2783903 : Blo 1219427 2783903 := bstep (se 1 (by rfl) ⟨2087927, by rfl⟩ : syracuseStep 2783903 = 4175855) B4175855
theorem B10427069 : Blo 1219427 10427069 := bstep (se 3 (by rfl) ⟨1955075, by rfl⟩ : syracuseStep 10427069 = 3910151) B3910151
theorem B19798775 : Blo 1219427 19798775 := bstep (se 1 (by rfl) ⟨14849081, by rfl⟩ : syracuseStep 19798775 = 29698163) B29698163
theorem B1219439 : Blo 1219427 1219439 := bstep (se 1 (by rfl) ⟨914579, by rfl⟩ : syracuseStep 1219439 = 1829159) B1829159
theorem B1219495 : Blo 1219427 1219495 := bstep (se 1 (by rfl) ⟨914621, by rfl⟩ : syracuseStep 1219495 = 1829243) B1829243
theorem B9264131 : Blo 1219427 9264131 := bstep (se 1 (by rfl) ⟨6948098, by rfl⟩ : syracuseStep 9264131 = 13896197) B13896197
theorem B1219675 : Blo 1219427 1219675 := bstep (se 1 (by rfl) ⟨914756, by rfl⟩ : syracuseStep 1219675 = 1829513) B1829513
theorem B1219791 : Blo 1219427 1219791 := bstep (se 1 (by rfl) ⟨914843, by rfl⟩ : syracuseStep 1219791 = 1829687) B1829687
theorem B1219815 : Blo 1219427 1219815 := bstep (se 1 (by rfl) ⟨914861, by rfl⟩ : syracuseStep 1219815 = 1829723) B1829723
theorem B6946073 : Blo 1219427 6946073 := bstep (se 2 (by rfl) ⟨2604777, by rfl⟩ : syracuseStep 6946073 = 5209555) B5209555
theorem B1219911 : Blo 1219427 1219911 := bstep (se 1 (by rfl) ⟨914933, by rfl⟩ : syracuseStep 1219911 = 1829867) B1829867
theorem B3087791 : Blo 1219427 3087791 := bstep (se 1 (by rfl) ⟨2315843, by rfl⟩ : syracuseStep 3087791 = 4631687) B4631687
theorem B1220047 : Blo 1219427 1220047 := bstep (se 1 (by rfl) ⟨915035, by rfl⟩ : syracuseStep 1220047 = 1830071) B1830071
theorem B9264617 : Blo 1219427 9264617 := bstep (se 2 (by rfl) ⟨3474231, by rfl⟩ : syracuseStep 9264617 = 6948463) B6948463
theorem B1220207 : Blo 1219427 1220207 := bstep (se 1 (by rfl) ⟨915155, by rfl⟩ : syracuseStep 1220207 = 1830311) B1830311
theorem B1982063 : Blo 1219427 1982063 := bstep (se 1 (by rfl) ⟨1486547, by rfl⟩ : syracuseStep 1982063 = 2973095) B2973095
theorem B1220263 : Blo 1219427 1220263 := bstep (se 1 (by rfl) ⟨915197, by rfl⟩ : syracuseStep 1220263 = 1830395) B1830395
theorem B2744027 : Blo 1219427 2744027 := bstep (se 1 (by rfl) ⟨2058020, by rfl⟩ : syracuseStep 2744027 = 4116041) B4116041
theorem B1220327 : Blo 1219427 1220327 := bstep (se 1 (by rfl) ⟨915245, by rfl⟩ : syracuseStep 1220327 = 1830491) B1830491
theorem B1220383 : Blo 1219427 1220383 := bstep (se 1 (by rfl) ⟨915287, by rfl⟩ : syracuseStep 1220383 = 1830575) B1830575
theorem B1220463 : Blo 1219427 1220463 := bstep (se 1 (by rfl) ⟨915347, by rfl⟩ : syracuseStep 1220463 = 1830695) B1830695
theorem B1220519 : Blo 1219427 1220519 := bstep (se 1 (by rfl) ⟨915389, by rfl⟩ : syracuseStep 1220519 = 1830779) B1830779
theorem B2744297 : Blo 1219427 2744297 := bstep (se 2 (by rfl) ⟨1029111, by rfl⟩ : syracuseStep 2744297 = 2058223) B2058223
theorem B2744423 : Blo 1219427 2744423 := bstep (se 1 (by rfl) ⟨2058317, by rfl⟩ : syracuseStep 2744423 = 4116635) B4116635
theorem B1466471 : Blo 1219427 1466471 := bstep (se 1 (by rfl) ⟨1099853, by rfl⟩ : syracuseStep 1466471 = 2199707) B2199707
theorem B1220763 : Blo 1219427 1220763 := bstep (se 1 (by rfl) ⟨915572, by rfl⟩ : syracuseStep 1220763 = 1831145) B1831145
theorem B1220847 : Blo 1219427 1220847 := bstep (se 1 (by rfl) ⟨915635, by rfl⟩ : syracuseStep 1220847 = 1831271) B1831271
theorem B5865767 : Blo 1219427 5865767 := bstep (se 1 (by rfl) ⟨4399325, by rfl⟩ : syracuseStep 5865767 = 8798651) B8798651
theorem B3088763 : Blo 1219427 3088763 := bstep (se 1 (by rfl) ⟨2316572, by rfl⟩ : syracuseStep 3088763 = 4633145) B4633145
theorem B8700317 : Blo 1219427 8700317 := bstep (se 3 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 8700317 = 3262619) B3262619
theorem B22553261 : Blo 1219427 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B31687433 : Blo 1219427 31687433 := bstep (se 2 (by rfl) ⟨11882787, by rfl⟩ : syracuseStep 31687433 = 23765575) B23765575
theorem B6177707 : Blo 1219427 6177707 := bstep (se 1 (by rfl) ⟨4633280, by rfl⟩ : syracuseStep 6177707 = 9266561) B9266561
theorem B3916907 : Blo 1219427 3916907 := bstep (se 1 (by rfl) ⟨2937680, by rfl⟩ : syracuseStep 3916907 = 5875361) B5875361
theorem B6947963 : Blo 1219427 6947963 := bstep (se 1 (by rfl) ⟨5210972, by rfl⟩ : syracuseStep 6947963 = 10421945) B10421945
theorem B3908819 : Blo 1219427 3908819 := bstep (se 1 (by rfl) ⟨2931614, by rfl⟩ : syracuseStep 3908819 = 5863229) B5863229
theorem B2745575 : Blo 1219427 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B2057791 : Blo 1219427 2057791 := bstep (se 1 (by rfl) ⟨1543343, by rfl⟩ : syracuseStep 2057791 = 3086687) B3086687
theorem B3475007 : Blo 1219427 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B5285501 : Blo 1219427 5285501 := bstep (se 3 (by rfl) ⟨991031, by rfl⟩ : syracuseStep 5285501 = 1982063) B1982063
theorem B7423741 : Blo 1219427 7423741 := bstep (se 3 (by rfl) ⟨1391951, by rfl⟩ : syracuseStep 7423741 = 2783903) B2783903
theorem B17598221 : Blo 1219427 17598221 := bstep (se 3 (by rfl) ⟨3299666, by rfl⟩ : syracuseStep 17598221 = 6599333) B6599333
theorem B13199183 : Blo 1219427 13199183 := bstep (se 1 (by rfl) ⟨9899387, by rfl⟩ : syracuseStep 13199183 = 19798775) B19798775
theorem B3475325 : Blo 1219427 3475325 := bstep (se 3 (by rfl) ⟨651623, by rfl⟩ : syracuseStep 3475325 = 1303247) B1303247
theorem B3344377 : Blo 1219427 3344377 := bstep (se 2 (by rfl) ⟨1254141, by rfl⟩ : syracuseStep 3344377 = 2508283) B2508283
theorem B4630715 : Blo 1219427 4630715 := bstep (se 1 (by rfl) ⟨3473036, by rfl⟩ : syracuseStep 4630715 = 6946073) B6946073
theorem B2058527 : Blo 1219427 2058527 := bstep (se 1 (by rfl) ⟨1543895, by rfl⟩ : syracuseStep 2058527 = 3087791) B3087791
theorem B1829351 : Blo 1219427 1829351 := bstep (se 1 (by rfl) ⟨1372013, by rfl⟩ : syracuseStep 1829351 = 2744027) B2744027
theorem B1829531 : Blo 1219427 1829531 := bstep (se 1 (by rfl) ⟨1372148, by rfl⟩ : syracuseStep 1829531 = 2744297) B2744297
theorem B13200185 : Blo 1219427 13200185 := bstep (se 2 (by rfl) ⟨4950069, by rfl⟩ : syracuseStep 13200185 = 9900139) B9900139
theorem B1829753 : Blo 1219427 1829753 := bstep (se 2 (by rfl) ⟨686157, by rfl⟩ : syracuseStep 1829753 = 1372315) B1372315
theorem B4172791 : Blo 1219427 4172791 := bstep (se 1 (by rfl) ⟨3129593, by rfl⟩ : syracuseStep 4172791 = 6259187) B6259187
theorem B1829999 : Blo 1219427 1829999 := bstep (se 1 (by rfl) ⟨1372499, by rfl⟩ : syracuseStep 1829999 = 2744999) B2744999
theorem B3296423 : Blo 1219427 3296423 := bstep (se 1 (by rfl) ⟨2472317, by rfl⟩ : syracuseStep 3296423 = 4944635) B4944635
theorem B1830095 : Blo 1219427 1830095 := bstep (se 1 (by rfl) ⟨1372571, by rfl⟩ : syracuseStep 1830095 = 2745143) B2745143
theorem B2059499 : Blo 1219427 2059499 := bstep (se 1 (by rfl) ⟨1544624, by rfl⟩ : syracuseStep 2059499 = 3089249) B3089249
theorem B1830215 : Blo 1219427 1830215 := bstep (se 1 (by rfl) ⟨1372661, by rfl⟩ : syracuseStep 1830215 = 2745323) B2745323
theorem B1830503 : Blo 1219427 1830503 := bstep (se 1 (by rfl) ⟨1372877, by rfl⟩ : syracuseStep 1830503 = 2745755) B2745755
theorem B1830887 : Blo 1219427 1830887 := bstep (se 1 (by rfl) ⟨1373165, by rfl⟩ : syracuseStep 1830887 = 2746331) B2746331
theorem B5214203 : Blo 1219427 5214203 := bstep (se 1 (by rfl) ⟨3910652, by rfl⟩ : syracuseStep 5214203 = 7821305) B7821305
theorem B4632659 : Blo 1219427 4632659 := bstep (se 1 (by rfl) ⟨3474494, by rfl⟩ : syracuseStep 4632659 = 6948989) B6948989
theorem B1831007 : Blo 1219427 1831007 := bstep (se 1 (by rfl) ⟨1373255, by rfl⟩ : syracuseStep 1831007 = 2746511) B2746511
theorem B3297419 : Blo 1219427 3297419 := bstep (se 1 (by rfl) ⟨2473064, by rfl⟩ : syracuseStep 3297419 = 4946129) B4946129
theorem B1831067 : Blo 1219427 1831067 := bstep (se 1 (by rfl) ⟨1373300, by rfl⟩ : syracuseStep 1831067 = 2746601) B2746601
theorem B7925935 : Blo 1219427 7925935 := bstep (se 1 (by rfl) ⟨5944451, by rfl⟩ : syracuseStep 7925935 = 11888903) B11888903
theorem B6951197 : Blo 1219427 6951197 := bstep (se 3 (by rfl) ⟨1303349, by rfl⟩ : syracuseStep 6951197 = 2606699) B2606699
theorem B1372495 : Blo 1219427 1372495 := bstep (se 1 (by rfl) ⟨1029371, by rfl⟩ : syracuseStep 1372495 = 2058743) B2058743
theorem B1831247 : Blo 1219427 1831247 := bstep (se 1 (by rfl) ⟨1373435, by rfl⟩ : syracuseStep 1831247 = 2746871) B2746871
theorem B1831337 : Blo 1219427 1831337 := bstep (se 2 (by rfl) ⟨686751, by rfl⟩ : syracuseStep 1831337 = 1373503) B1373503
theorem B6951379 : Blo 1219427 6951379 := bstep (se 1 (by rfl) ⟨5213534, by rfl⟩ : syracuseStep 6951379 = 10427069) B10427069
theorem B1372891 : Blo 1219427 1372891 := bstep (se 1 (by rfl) ⟨1029668, by rfl⟩ : syracuseStep 1372891 = 2059337) B2059337
theorem B7042157 : Blo 1219427 7042157 := bstep (se 3 (by rfl) ⟨1320404, by rfl⟩ : syracuseStep 7042157 = 2640809) B2640809
theorem B1220603 : Blo 1219427 1220603 := bstep (se 1 (by rfl) ⟨915452, by rfl⟩ : syracuseStep 1220603 = 1830905) B1830905
theorem B4633919 : Blo 1219427 4633919 := bstep (se 1 (by rfl) ⟨3475439, by rfl⟩ : syracuseStep 4633919 = 6950879) B6950879
theorem B7525889 : Blo 1219427 7525889 := bstep (se 2 (by rfl) ⟨2822208, by rfl⟩ : syracuseStep 7525889 = 5644417) B5644417
theorem B4118255 : Blo 1219427 4118255 := bstep (se 1 (by rfl) ⟨3088691, by rfl⟩ : syracuseStep 4118255 = 6177383) B6177383
theorem B6174467 : Blo 1219427 6174467 := bstep (se 1 (by rfl) ⟨4630850, by rfl⟩ : syracuseStep 6174467 = 9261701) B9261701
theorem B6174791 : Blo 1219427 6174791 := bstep (se 1 (by rfl) ⟨4631093, by rfl⟩ : syracuseStep 6174791 = 9262187) B9262187
theorem B5012231 : Blo 1219427 5012231 := bstep (se 1 (by rfl) ⟨3759173, by rfl⟩ : syracuseStep 5012231 = 7518347) B7518347
theorem B216914861 : Blo 1219427 216914861 := bstep (se 3 (by rfl) ⟨40671536, by rfl⟩ : syracuseStep 216914861 = 81343073) B81343073
theorem B1219579 : Blo 1219427 1219579 := bstep (se 1 (by rfl) ⟨914684, by rfl⟩ : syracuseStep 1219579 = 1829369) B1829369
theorem B3087355 : Blo 1219427 3087355 := bstep (se 1 (by rfl) ⟨2315516, by rfl⟩ : syracuseStep 3087355 = 4631033) B4631033
theorem B1219615 : Blo 1219427 1219615 := bstep (se 1 (by rfl) ⟨914711, by rfl⟩ : syracuseStep 1219615 = 1829423) B1829423
theorem B10583099 : Blo 1219427 10583099 := bstep (se 1 (by rfl) ⟨7937324, by rfl⟩ : syracuseStep 10583099 = 15874649) B15874649
theorem B4119659 : Blo 1219427 4119659 := bstep (se 1 (by rfl) ⟨3089744, by rfl⟩ : syracuseStep 4119659 = 6179489) B6179489
theorem B3087679 : Blo 1219427 3087679 := bstep (se 1 (by rfl) ⟨2315759, by rfl⟩ : syracuseStep 3087679 = 4631519) B4631519
theorem B1219903 : Blo 1219427 1219903 := bstep (se 1 (by rfl) ⟨914927, by rfl⟩ : syracuseStep 1219903 = 1829855) B1829855
theorem B6176087 : Blo 1219427 6176087 := bstep (se 1 (by rfl) ⟨4632065, by rfl⟩ : syracuseStep 6176087 = 9264131) B9264131
theorem B32120393 : Blo 1219427 32120393 := bstep (se 2 (by rfl) ⟨12045147, by rfl⟩ : syracuseStep 32120393 = 24090295) B24090295
theorem B1220199 : Blo 1219427 1220199 := bstep (se 1 (by rfl) ⟨915149, by rfl⟩ : syracuseStep 1220199 = 1830299) B1830299
theorem B6176411 : Blo 1219427 6176411 := bstep (se 1 (by rfl) ⟨4632308, by rfl⟩ : syracuseStep 6176411 = 9264617) B9264617
theorem B1220479 : Blo 1219427 1220479 := bstep (se 1 (by rfl) ⟨915359, by rfl⟩ : syracuseStep 1220479 = 1830719) B1830719
theorem B3088327 : Blo 1219427 3088327 := bstep (se 1 (by rfl) ⟨2316245, by rfl⟩ : syracuseStep 3088327 = 4632491) B4632491
theorem B3088439 : Blo 1219427 3088439 := bstep (se 1 (by rfl) ⟨2316329, by rfl⟩ : syracuseStep 3088439 = 4632659) B4632659
theorem B1220671 : Blo 1219427 1220671 := bstep (se 1 (by rfl) ⟨915503, by rfl⟩ : syracuseStep 1220671 = 1831007) B1831007
theorem B1220711 : Blo 1219427 1220711 := bstep (se 1 (by rfl) ⟨915533, by rfl⟩ : syracuseStep 1220711 = 1831067) B1831067
theorem B1220831 : Blo 1219427 1220831 := bstep (se 1 (by rfl) ⟨915623, by rfl⟩ : syracuseStep 1220831 = 1831247) B1831247
theorem B10567913 : Blo 1219427 10567913 := bstep (se 2 (by rfl) ⟨3962967, by rfl⟩ : syracuseStep 10567913 = 7925935) B7925935
theorem B5800211 : Blo 1219427 5800211 := bstep (se 1 (by rfl) ⟨4350158, by rfl⟩ : syracuseStep 5800211 = 8700317) B8700317
theorem B1220891 : Blo 1219427 1220891 := bstep (se 1 (by rfl) ⟨915668, by rfl⟩ : syracuseStep 1220891 = 1831337) B1831337
theorem B4694771 : Blo 1219427 4694771 := bstep (se 1 (by rfl) ⟨3521078, by rfl⟩ : syracuseStep 4694771 = 7042157) B7042157
theorem B2605879 : Blo 1219427 2605879 := bstep (se 1 (by rfl) ⟨1954409, by rfl⟩ : syracuseStep 2605879 = 3908819) B3908819
theorem B3089279 : Blo 1219427 3089279 := bstep (se 1 (by rfl) ⟨2316959, by rfl⟩ : syracuseStep 3089279 = 4633919) B4633919
theorem B3523667 : Blo 1219427 3523667 := bstep (se 1 (by rfl) ⟨2642750, by rfl⟩ : syracuseStep 3523667 = 5285501) B5285501
theorem B2745503 : Blo 1219427 2745503 := bstep (se 1 (by rfl) ⟨2059127, by rfl⟩ : syracuseStep 2745503 = 4118255) B4118255
theorem B11732147 : Blo 1219427 11732147 := bstep (se 1 (by rfl) ⟨8799110, by rfl⟩ : syracuseStep 11732147 = 17598221) B17598221
theorem B8799455 : Blo 1219427 8799455 := bstep (se 1 (by rfl) ⟨6599591, by rfl⟩ : syracuseStep 8799455 = 13199183) B13199183
theorem B5563721 : Blo 1219427 5563721 := bstep (se 2 (by rfl) ⟨2086395, by rfl⟩ : syracuseStep 5563721 = 4172791) B4172791
theorem B8800123 : Blo 1219427 8800123 := bstep (se 1 (by rfl) ⟨6600092, by rfl⟩ : syracuseStep 8800123 = 13200185) B13200185
theorem B7055399 : Blo 1219427 7055399 := bstep (se 1 (by rfl) ⟨5291549, by rfl⟩ : syracuseStep 7055399 = 10583099) B10583099
theorem B2746439 : Blo 1219427 2746439 := bstep (se 1 (by rfl) ⟨2059829, by rfl⟩ : syracuseStep 2746439 = 4119659) B4119659
theorem B2197615 : Blo 1219427 2197615 := bstep (se 1 (by rfl) ⟨1648211, by rfl⟩ : syracuseStep 2197615 = 3296423) B3296423
theorem B9267533 : Blo 1219427 9267533 := bstep (se 3 (by rfl) ⟨1737662, by rfl⟩ : syracuseStep 9267533 = 3475325) B3475325
theorem B9898321 : Blo 1219427 9898321 := bstep (se 2 (by rfl) ⟨3711870, by rfl⟩ : syracuseStep 9898321 = 7423741) B7423741
theorem B578439629 : Blo 1219427 578439629 := bstep (se 3 (by rfl) ⟨108457430, by rfl⟩ : syracuseStep 578439629 = 216914861) B216914861
theorem B71346709 : Blo 1219427 71346709 := bstep (se 6 (by rfl) ⟨1672188, by rfl⟩ : syracuseStep 71346709 = 3344377) B3344377
theorem B3476135 : Blo 1219427 3476135 := bstep (se 1 (by rfl) ⟨2607101, by rfl⟩ : syracuseStep 3476135 = 5214203) B5214203
theorem B1829615 : Blo 1219427 1829615 := bstep (se 1 (by rfl) ⟨1372211, by rfl⟩ : syracuseStep 1829615 = 2744423) B2744423
theorem B53463797 : Blo 1219427 53463797 := bstep (se 5 (by rfl) ⟨2506115, by rfl⟩ : syracuseStep 53463797 = 5012231) B5012231
theorem B2198279 : Blo 1219427 2198279 := bstep (se 1 (by rfl) ⟨1648709, by rfl⟩ : syracuseStep 2198279 = 3297419) B3297419
theorem B3910511 : Blo 1219427 3910511 := bstep (se 1 (by rfl) ⟨2932883, by rfl⟩ : syracuseStep 3910511 = 5865767) B5865767
theorem B2059175 : Blo 1219427 2059175 := bstep (se 1 (by rfl) ⟨1544381, by rfl⟩ : syracuseStep 2059175 = 3088763) B3088763
theorem B3910589 : Blo 1219427 3910589 := bstep (se 3 (by rfl) ⟨733235, by rfl⟩ : syracuseStep 3910589 = 1466471) B1466471
theorem B1829993 : Blo 1219427 1829993 := bstep (se 2 (by rfl) ⟨686247, by rfl⟩ : syracuseStep 1829993 = 1372495) B1372495
theorem B15035507 : Blo 1219427 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B9268505 : Blo 1219427 9268505 := bstep (se 2 (by rfl) ⟨3475689, by rfl⟩ : syracuseStep 9268505 = 6951379) B6951379
theorem B4631975 : Blo 1219427 4631975 := bstep (se 1 (by rfl) ⟨3473981, by rfl⟩ : syracuseStep 4631975 = 6947963) B6947963
theorem B342617525 : Blo 1219427 342617525 := bstep (se 5 (by rfl) ⟨16060196, by rfl⟩ : syracuseStep 342617525 = 32120393) B32120393
theorem B1830383 : Blo 1219427 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B1830521 : Blo 1219427 1830521 := bstep (se 2 (by rfl) ⟨686445, by rfl⟩ : syracuseStep 1830521 = 1372891) B1372891
theorem B5017259 : Blo 1219427 5017259 := bstep (se 1 (by rfl) ⟨3762944, by rfl⟩ : syracuseStep 5017259 = 7525889) B7525889
theorem B4116311 : Blo 1219427 4116311 := bstep (se 1 (by rfl) ⟨3087233, by rfl⟩ : syracuseStep 4116311 = 6174467) B6174467
theorem B4116473 : Blo 1219427 4116473 := bstep (se 2 (by rfl) ⟨1543677, by rfl⟩ : syracuseStep 4116473 = 3087355) B3087355
theorem B4116527 : Blo 1219427 4116527 := bstep (se 1 (by rfl) ⟨3087395, by rfl⟩ : syracuseStep 4116527 = 6174791) B6174791
theorem B1372351 : Blo 1219427 1372351 := bstep (se 1 (by rfl) ⟨1029263, by rfl⟩ : syracuseStep 1372351 = 2058527) B2058527
theorem B4116905 : Blo 1219427 4116905 := bstep (se 2 (by rfl) ⟨1543839, by rfl⟩ : syracuseStep 4116905 = 3087679) B3087679
theorem B1372999 : Blo 1219427 1372999 := bstep (se 1 (by rfl) ⟨1029749, by rfl⟩ : syracuseStep 1372999 = 2059499) B2059499
theorem B4117391 : Blo 1219427 4117391 := bstep (se 1 (by rfl) ⟨3088043, by rfl⟩ : syracuseStep 4117391 = 6176087) B6176087
theorem B4117607 : Blo 1219427 4117607 := bstep (se 1 (by rfl) ⟨3088205, by rfl⟩ : syracuseStep 4117607 = 6176411) B6176411
theorem B4117769 : Blo 1219427 4117769 := bstep (se 2 (by rfl) ⟨1544163, by rfl⟩ : syracuseStep 4117769 = 3088327) B3088327
theorem B4634131 : Blo 1219427 4634131 := bstep (se 1 (by rfl) ⟨3475598, by rfl⟩ : syracuseStep 4634131 = 6951197) B6951197
theorem B21124955 : Blo 1219427 21124955 := bstep (se 1 (by rfl) ⟨15843716, by rfl⟩ : syracuseStep 21124955 = 31687433) B31687433
theorem B4118471 : Blo 1219427 4118471 := bstep (se 1 (by rfl) ⟨3088853, by rfl⟩ : syracuseStep 4118471 = 6177707) B6177707
theorem B2611271 : Blo 1219427 2611271 := bstep (se 1 (by rfl) ⟨1958453, by rfl⟩ : syracuseStep 2611271 = 3916907) B3916907
theorem B2316671 : Blo 1219427 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B3087143 : Blo 1219427 3087143 := bstep (se 1 (by rfl) ⟨2315357, by rfl⟩ : syracuseStep 3087143 = 4630715) B4630715
theorem B1219567 : Blo 1219427 1219567 := bstep (se 1 (by rfl) ⟨914675, by rfl⟩ : syracuseStep 1219567 = 1829351) B1829351
theorem B1219687 : Blo 1219427 1219687 := bstep (se 1 (by rfl) ⟨914765, by rfl⟩ : syracuseStep 1219687 = 1829531) B1829531
theorem B1219835 : Blo 1219427 1219835 := bstep (se 1 (by rfl) ⟨914876, by rfl⟩ : syracuseStep 1219835 = 1829753) B1829753
theorem B1219999 : Blo 1219427 1219999 := bstep (se 1 (by rfl) ⟨914999, by rfl⟩ : syracuseStep 1219999 = 1829999) B1829999
theorem B2743721 : Blo 1219427 2743721 := bstep (se 2 (by rfl) ⟨1028895, by rfl⟩ : syracuseStep 2743721 = 2057791) B2057791
theorem B1220063 : Blo 1219427 1220063 := bstep (se 1 (by rfl) ⟨915047, by rfl⟩ : syracuseStep 1220063 = 1830095) B1830095
theorem B1220143 : Blo 1219427 1220143 := bstep (se 1 (by rfl) ⟨915107, by rfl⟩ : syracuseStep 1220143 = 1830215) B1830215
theorem B1220335 : Blo 1219427 1220335 := bstep (se 1 (by rfl) ⟨915251, by rfl⟩ : syracuseStep 1220335 = 1830503) B1830503
theorem B1220591 : Blo 1219427 1220591 := bstep (se 1 (by rfl) ⟨915443, by rfl⟩ : syracuseStep 1220591 = 1830887) B1830887
theorem B2744351 : Blo 1219427 2744351 := bstep (se 1 (by rfl) ⟨2058263, by rfl⟩ : syracuseStep 2744351 = 4116527) B4116527
theorem B3866807 : Blo 1219427 3866807 := bstep (se 1 (by rfl) ⟨2900105, by rfl⟩ : syracuseStep 3866807 = 5800211) B5800211
theorem B9396445 : Blo 1219427 9396445 := bstep (se 3 (by rfl) ⟨1761833, by rfl⟩ : syracuseStep 9396445 = 3523667) B3523667
theorem B2744603 : Blo 1219427 2744603 := bstep (se 1 (by rfl) ⟨2058452, by rfl⟩ : syracuseStep 2744603 = 4116905) B4116905
theorem B13197761 : Blo 1219427 13197761 := bstep (se 2 (by rfl) ⟨4949160, by rfl⟩ : syracuseStep 13197761 = 9898321) B9898321
theorem B3129847 : Blo 1219427 3129847 := bstep (se 1 (by rfl) ⟨2347385, by rfl⟩ : syracuseStep 3129847 = 4694771) B4694771
theorem B2744927 : Blo 1219427 2744927 := bstep (se 1 (by rfl) ⟨2058695, by rfl⟩ : syracuseStep 2744927 = 4117391) B4117391
theorem B2745071 : Blo 1219427 2745071 := bstep (se 1 (by rfl) ⟨2058803, by rfl⟩ : syracuseStep 2745071 = 4117607) B4117607
theorem B2745179 : Blo 1219427 2745179 := bstep (se 1 (by rfl) ⟨2058884, by rfl⟩ : syracuseStep 2745179 = 4117769) B4117769
theorem B3474505 : Blo 1219427 3474505 := bstep (se 2 (by rfl) ⟨1302939, by rfl⟩ : syracuseStep 3474505 = 2605879) B2605879
theorem B14083303 : Blo 1219427 14083303 := bstep (se 1 (by rfl) ⟨10562477, by rfl⟩ : syracuseStep 14083303 = 21124955) B21124955
theorem B2745647 : Blo 1219427 2745647 := bstep (se 1 (by rfl) ⟨2059235, by rfl⟩ : syracuseStep 2745647 = 4118471) B4118471
theorem B4703599 : Blo 1219427 4703599 := bstep (se 1 (by rfl) ⟨3527699, by rfl⟩ : syracuseStep 4703599 = 7055399) B7055399
theorem B6178355 : Blo 1219427 6178355 := bstep (se 1 (by rfl) ⟨4633766, by rfl⟩ : syracuseStep 6178355 = 9267533) B9267533
theorem B2058095 : Blo 1219427 2058095 := bstep (se 1 (by rfl) ⟨1543571, by rfl⟩ : syracuseStep 2058095 = 3087143) B3087143
theorem B2607007 : Blo 1219427 2607007 := bstep (se 1 (by rfl) ⟨1955255, by rfl⟩ : syracuseStep 2607007 = 3910511) B3910511
theorem B2607059 : Blo 1219427 2607059 := bstep (se 1 (by rfl) ⟨1955294, by rfl⟩ : syracuseStep 2607059 = 3910589) B3910589
theorem B6178841 : Blo 1219427 6178841 := bstep (se 2 (by rfl) ⟨2317065, by rfl⟩ : syracuseStep 6178841 = 4634131) B4634131
theorem B6179003 : Blo 1219427 6179003 := bstep (se 1 (by rfl) ⟨4634252, by rfl⟩ : syracuseStep 6179003 = 9268505) B9268505
theorem B1829147 : Blo 1219427 1829147 := bstep (se 1 (by rfl) ⟨1371860, by rfl⟩ : syracuseStep 1829147 = 2743721) B2743721
theorem B228411683 : Blo 1219427 228411683 := bstep (se 1 (by rfl) ⟨171308762, by rfl⟩ : syracuseStep 228411683 = 342617525) B342617525
theorem B112724405 : Blo 1219427 112724405 := bstep (se 5 (by rfl) ⟨5283956, by rfl⟩ : syracuseStep 112724405 = 10567913) B10567913
theorem B3344839 : Blo 1219427 3344839 := bstep (se 1 (by rfl) ⟨2508629, by rfl⟩ : syracuseStep 3344839 = 5017259) B5017259
theorem B11733497 : Blo 1219427 11733497 := bstep (se 2 (by rfl) ⟨4400061, by rfl⟩ : syracuseStep 11733497 = 8800123) B8800123
theorem B2058959 : Blo 1219427 2058959 := bstep (se 1 (by rfl) ⟨1544219, by rfl⟩ : syracuseStep 2058959 = 3088439) B3088439
theorem B1829801 : Blo 1219427 1829801 := bstep (se 2 (by rfl) ⟨686175, by rfl⟩ : syracuseStep 1829801 = 1372351) B1372351
theorem B23465213 : Blo 1219427 23465213 := bstep (se 3 (by rfl) ⟨4399727, by rfl⟩ : syracuseStep 23465213 = 8799455) B8799455
theorem B2059519 : Blo 1219427 2059519 := bstep (se 1 (by rfl) ⟨1544639, by rfl⟩ : syracuseStep 2059519 = 3089279) B3089279
theorem B1830335 : Blo 1219427 1830335 := bstep (se 1 (by rfl) ⟨1372751, by rfl⟩ : syracuseStep 1830335 = 2745503) B2745503
theorem B2744315 : Blo 1219427 2744315 := bstep (se 1 (by rfl) ⟨2058236, by rfl⟩ : syracuseStep 2744315 = 4116473) B4116473
theorem B1830665 : Blo 1219427 1830665 := bstep (se 2 (by rfl) ⟨686499, by rfl⟩ : syracuseStep 1830665 = 1372999) B1372999
theorem B1740847 : Blo 1219427 1740847 := bstep (se 1 (by rfl) ⟨1305635, by rfl⟩ : syracuseStep 1740847 = 2611271) B2611271
theorem B1830959 : Blo 1219427 1830959 := bstep (se 1 (by rfl) ⟨1373219, by rfl⟩ : syracuseStep 1830959 = 2746439) B2746439
theorem B1544447 : Blo 1219427 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B385626419 : Blo 1219427 385626419 := bstep (se 1 (by rfl) ⟨289219814, by rfl⟩ : syracuseStep 385626419 = 578439629) B578439629
theorem B1372783 : Blo 1219427 1372783 := bstep (se 1 (by rfl) ⟨1029587, by rfl⟩ : syracuseStep 1372783 = 2059175) B2059175
theorem B5862077 : Blo 1219427 5862077 := bstep (se 3 (by rfl) ⟨1099139, by rfl⟩ : syracuseStep 5862077 = 2198279) B2198279
theorem B10023671 : Blo 1219427 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B380515781 : Blo 1219427 380515781 := bstep (se 4 (by rfl) ⟨35673354, by rfl⟩ : syracuseStep 380515781 = 71346709) B71346709
theorem B2930153 : Blo 1219427 2930153 := bstep (se 2 (by rfl) ⟨1098807, by rfl⟩ : syracuseStep 2930153 = 2197615) B2197615
theorem B7821431 : Blo 1219427 7821431 := bstep (se 1 (by rfl) ⟨5866073, by rfl⟩ : syracuseStep 7821431 = 11732147) B11732147
theorem B3709147 : Blo 1219427 3709147 := bstep (se 1 (by rfl) ⟨2781860, by rfl⟩ : syracuseStep 3709147 = 5563721) B5563721
theorem B2317423 : Blo 1219427 2317423 := bstep (se 1 (by rfl) ⟨1738067, by rfl⟩ : syracuseStep 2317423 = 3476135) B3476135
theorem B1219743 : Blo 1219427 1219743 := bstep (se 1 (by rfl) ⟨914807, by rfl⟩ : syracuseStep 1219743 = 1829615) B1829615
theorem B35642531 : Blo 1219427 35642531 := bstep (se 1 (by rfl) ⟨26731898, by rfl⟩ : syracuseStep 35642531 = 53463797) B53463797
theorem B1219995 : Blo 1219427 1219995 := bstep (se 1 (by rfl) ⟨914996, by rfl⟩ : syracuseStep 1219995 = 1829993) B1829993
theorem B3087983 : Blo 1219427 3087983 := bstep (se 1 (by rfl) ⟨2315987, by rfl⟩ : syracuseStep 3087983 = 4631975) B4631975
theorem B1220255 : Blo 1219427 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B1220347 : Blo 1219427 1220347 := bstep (se 1 (by rfl) ⟨915260, by rfl⟩ : syracuseStep 1220347 = 1830521) B1830521
theorem B2744207 : Blo 1219427 2744207 := bstep (se 1 (by rfl) ⟨2058155, by rfl⟩ : syracuseStep 2744207 = 4116311) B4116311
theorem B1220639 : Blo 1219427 1220639 := bstep (se 1 (by rfl) ⟨915479, by rfl⟩ : syracuseStep 1220639 = 1830959) B1830959
theorem B8798507 : Blo 1219427 8798507 := bstep (se 1 (by rfl) ⟨6598880, by rfl⟩ : syracuseStep 8798507 = 13197761) B13197761
theorem B3908051 : Blo 1219427 3908051 := bstep (se 1 (by rfl) ⟨2931038, by rfl⟩ : syracuseStep 3908051 = 5862077) B5862077
theorem B1738039 : Blo 1219427 1738039 := bstep (se 1 (by rfl) ⟨1303529, by rfl⟩ : syracuseStep 1738039 = 2607059) B2607059
theorem B3089897 : Blo 1219427 3089897 := bstep (se 2 (by rfl) ⟨1158711, by rfl⟩ : syracuseStep 3089897 = 2317423) B2317423
theorem B152274455 : Blo 1219427 152274455 := bstep (se 1 (by rfl) ⟨114205841, by rfl⟩ : syracuseStep 152274455 = 228411683) B228411683
theorem B18777737 : Blo 1219427 18777737 := bstep (se 2 (by rfl) ⟨7041651, by rfl⟩ : syracuseStep 18777737 = 14083303) B14083303
theorem B2746025 : Blo 1219427 2746025 := bstep (se 2 (by rfl) ⟨1029759, by rfl⟩ : syracuseStep 2746025 = 2059519) B2059519
theorem B25085861 : Blo 1219427 25085861 := bstep (se 4 (by rfl) ⟨2351799, by rfl⟩ : syracuseStep 25085861 = 4703599) B4703599
theorem B2058655 : Blo 1219427 2058655 := bstep (se 1 (by rfl) ⟨1543991, by rfl⟩ : syracuseStep 2058655 = 3087983) B3087983
theorem B3476009 : Blo 1219427 3476009 := bstep (se 2 (by rfl) ⟨1303503, by rfl⟩ : syracuseStep 3476009 = 2607007) B2607007
theorem B1829471 : Blo 1219427 1829471 := bstep (se 1 (by rfl) ⟨1372103, by rfl⟩ : syracuseStep 1829471 = 2744207) B2744207
theorem B1829543 : Blo 1219427 1829543 := bstep (se 1 (by rfl) ⟨1372157, by rfl⟩ : syracuseStep 1829543 = 2744315) B2744315
theorem B1829567 : Blo 1219427 1829567 := bstep (se 1 (by rfl) ⟨1372175, by rfl⟩ : syracuseStep 1829567 = 2744351) B2744351
theorem B2321129 : Blo 1219427 2321129 := bstep (se 2 (by rfl) ⟨870423, by rfl⟩ : syracuseStep 2321129 = 1740847) B1740847
theorem B1829735 : Blo 1219427 1829735 := bstep (se 1 (by rfl) ⟨1372301, by rfl⟩ : syracuseStep 1829735 = 2744603) B2744603
theorem B257084279 : Blo 1219427 257084279 := bstep (se 1 (by rfl) ⟨192813209, by rfl⟩ : syracuseStep 257084279 = 385626419) B385626419
theorem B12528593 : Blo 1219427 12528593 := bstep (se 2 (by rfl) ⟨4698222, by rfl⟩ : syracuseStep 12528593 = 9396445) B9396445
theorem B1829951 : Blo 1219427 1829951 := bstep (se 1 (by rfl) ⟨1372463, by rfl⟩ : syracuseStep 1829951 = 2744927) B2744927
theorem B1830047 : Blo 1219427 1830047 := bstep (se 1 (by rfl) ⟨1372535, by rfl⟩ : syracuseStep 1830047 = 2745071) B2745071
theorem B1830119 : Blo 1219427 1830119 := bstep (se 1 (by rfl) ⟨1372589, by rfl⟩ : syracuseStep 1830119 = 2745179) B2745179
theorem B1830377 : Blo 1219427 1830377 := bstep (se 2 (by rfl) ⟨686391, by rfl⟩ : syracuseStep 1830377 = 1372783) B1372783
theorem B1830431 : Blo 1219427 1830431 := bstep (se 1 (by rfl) ⟨1372823, by rfl⟩ : syracuseStep 1830431 = 2745647) B2745647
theorem B253677187 : Blo 1219427 253677187 := bstep (se 1 (by rfl) ⟨190257890, by rfl⟩ : syracuseStep 253677187 = 380515781) B380515781
theorem B1372063 : Blo 1219427 1372063 := bstep (se 1 (by rfl) ⟨1029047, by rfl⟩ : syracuseStep 1372063 = 2058095) B2058095
theorem B5214287 : Blo 1219427 5214287 := bstep (se 1 (by rfl) ⟨3910715, by rfl⟩ : syracuseStep 5214287 = 7821431) B7821431
theorem B4632673 : Blo 1219427 4632673 := bstep (se 2 (by rfl) ⟨1737252, by rfl⟩ : syracuseStep 4632673 = 3474505) B3474505
theorem B71356565 : Blo 1219427 71356565 := bstep (se 6 (by rfl) ⟨1672419, by rfl⟩ : syracuseStep 71356565 = 3344839) B3344839
theorem B75149603 : Blo 1219427 75149603 := bstep (se 1 (by rfl) ⟨56362202, by rfl⟩ : syracuseStep 75149603 = 112724405) B112724405
theorem B1372639 : Blo 1219427 1372639 := bstep (se 1 (by rfl) ⟨1029479, by rfl⟩ : syracuseStep 1372639 = 2058959) B2058959
theorem B23761687 : Blo 1219427 23761687 := bstep (se 1 (by rfl) ⟨17821265, by rfl⟩ : syracuseStep 23761687 = 35642531) B35642531
theorem B15643475 : Blo 1219427 15643475 := bstep (se 1 (by rfl) ⟨11732606, by rfl⟩ : syracuseStep 15643475 = 23465213) B23465213
theorem B16692517 : Blo 1219427 16692517 := bstep (se 4 (by rfl) ⟨1564923, by rfl⟩ : syracuseStep 16692517 = 3129847) B3129847
theorem B2577871 : Blo 1219427 2577871 := bstep (se 1 (by rfl) ⟨1933403, by rfl⟩ : syracuseStep 2577871 = 3866807) B3866807
theorem B4945529 : Blo 1219427 4945529 := bstep (se 2 (by rfl) ⟨1854573, by rfl⟩ : syracuseStep 4945529 = 3709147) B3709147
theorem B6682447 : Blo 1219427 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B4118525 : Blo 1219427 4118525 := bstep (se 3 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 4118525 = 1544447) B1544447
theorem B4118903 : Blo 1219427 4118903 := bstep (se 1 (by rfl) ⟨3089177, by rfl⟩ : syracuseStep 4118903 = 6178355) B6178355
theorem B7813741 : Blo 1219427 7813741 := bstep (se 3 (by rfl) ⟨1465076, by rfl⟩ : syracuseStep 7813741 = 2930153) B2930153
theorem B4119227 : Blo 1219427 4119227 := bstep (se 1 (by rfl) ⟨3089420, by rfl⟩ : syracuseStep 4119227 = 6178841) B6178841
theorem B4119335 : Blo 1219427 4119335 := bstep (se 1 (by rfl) ⟨3089501, by rfl⟩ : syracuseStep 4119335 = 6179003) B6179003
theorem B1219431 : Blo 1219427 1219431 := bstep (se 1 (by rfl) ⟨914573, by rfl⟩ : syracuseStep 1219431 = 1829147) B1829147
theorem B7822331 : Blo 1219427 7822331 := bstep (se 1 (by rfl) ⟨5866748, by rfl⟩ : syracuseStep 7822331 = 11733497) B11733497
theorem B1219867 : Blo 1219427 1219867 := bstep (se 1 (by rfl) ⟨914900, by rfl⟩ : syracuseStep 1219867 = 1829801) B1829801
theorem B1220223 : Blo 1219427 1220223 := bstep (se 1 (by rfl) ⟨915167, by rfl⟩ : syracuseStep 1220223 = 1830335) B1830335
theorem B1220443 : Blo 1219427 1220443 := bstep (se 1 (by rfl) ⟨915332, by rfl⟩ : syracuseStep 1220443 = 1830665) B1830665
theorem B6176897 : Blo 1219427 6176897 := bstep (se 2 (by rfl) ⟨2316336, by rfl⟩ : syracuseStep 6176897 = 4632673) B4632673
theorem B5865671 : Blo 1219427 5865671 := bstep (se 1 (by rfl) ⟨4399253, by rfl⟩ : syracuseStep 5865671 = 8798507) B8798507
theorem B2605367 : Blo 1219427 2605367 := bstep (se 1 (by rfl) ⟨1954025, by rfl⟩ : syracuseStep 2605367 = 3908051) B3908051
theorem B190284173 : Blo 1219427 190284173 := bstep (se 3 (by rfl) ⟨35678282, by rfl⟩ : syracuseStep 190284173 = 71356565) B71356565
theorem B2744873 : Blo 1219427 2744873 := bstep (se 2 (by rfl) ⟨1029327, by rfl⟩ : syracuseStep 2744873 = 2058655) B2058655
theorem B10428983 : Blo 1219427 10428983 := bstep (se 1 (by rfl) ⟨7821737, by rfl⟩ : syracuseStep 10428983 = 15643475) B15643475
theorem B101516303 : Blo 1219427 101516303 := bstep (se 1 (by rfl) ⟨76137227, by rfl⟩ : syracuseStep 101516303 = 152274455) B152274455
theorem B12518491 : Blo 1219427 12518491 := bstep (se 1 (by rfl) ⟨9388868, by rfl⟩ : syracuseStep 12518491 = 18777737) B18777737
theorem B2745683 : Blo 1219427 2745683 := bstep (se 1 (by rfl) ⟨2059262, by rfl⟩ : syracuseStep 2745683 = 4118525) B4118525
theorem B2745935 : Blo 1219427 2745935 := bstep (se 1 (by rfl) ⟨2059451, by rfl⟩ : syracuseStep 2745935 = 4118903) B4118903
theorem B2746151 : Blo 1219427 2746151 := bstep (se 1 (by rfl) ⟨2059613, by rfl⟩ : syracuseStep 2746151 = 4119227) B4119227
theorem B2746223 : Blo 1219427 2746223 := bstep (se 1 (by rfl) ⟨2059667, by rfl⟩ : syracuseStep 2746223 = 4119335) B4119335
theorem B1829417 : Blo 1219427 1829417 := bstep (se 2 (by rfl) ⟨686031, by rfl⟩ : syracuseStep 1829417 = 1372063) B1372063
theorem B3476191 : Blo 1219427 3476191 := bstep (se 1 (by rfl) ⟨2607143, by rfl⟩ : syracuseStep 3476191 = 5214287) B5214287
theorem B1830185 : Blo 1219427 1830185 := bstep (se 2 (by rfl) ⟨686319, by rfl⟩ : syracuseStep 1830185 = 1372639) B1372639
theorem B2059931 : Blo 1219427 2059931 := bstep (se 1 (by rfl) ⟨1544948, by rfl⟩ : syracuseStep 2059931 = 3089897) B3089897
theorem B31682249 : Blo 1219427 31682249 := bstep (se 2 (by rfl) ⟨11880843, by rfl⟩ : syracuseStep 31682249 = 23761687) B23761687
theorem B3297019 : Blo 1219427 3297019 := bstep (se 1 (by rfl) ⟨2472764, by rfl⟩ : syracuseStep 3297019 = 4945529) B4945529
theorem B1830683 : Blo 1219427 1830683 := bstep (se 1 (by rfl) ⟨1373012, by rfl⟩ : syracuseStep 1830683 = 2746025) B2746025
theorem B16723907 : Blo 1219427 16723907 := bstep (se 1 (by rfl) ⟨12542930, by rfl⟩ : syracuseStep 16723907 = 25085861) B25085861
theorem B171389519 : Blo 1219427 171389519 := bstep (se 1 (by rfl) ⟨128542139, by rfl⟩ : syracuseStep 171389519 = 257084279) B257084279
theorem B3437161 : Blo 1219427 3437161 := bstep (se 2 (by rfl) ⟨1288935, by rfl⟩ : syracuseStep 3437161 = 2577871) B2577871
theorem B8352395 : Blo 1219427 8352395 := bstep (se 1 (by rfl) ⟨6264296, by rfl⟩ : syracuseStep 8352395 = 12528593) B12528593
theorem B5214887 : Blo 1219427 5214887 := bstep (se 1 (by rfl) ⟨3911165, by rfl⟩ : syracuseStep 5214887 = 7822331) B7822331
theorem B338236249 : Blo 1219427 338236249 := bstep (se 2 (by rfl) ⟨126838593, by rfl⟩ : syracuseStep 338236249 = 253677187) B253677187
theorem B8909929 : Blo 1219427 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B50099735 : Blo 1219427 50099735 := bstep (se 1 (by rfl) ⟨37574801, by rfl⟩ : syracuseStep 50099735 = 75149603) B75149603
theorem B10418321 : Blo 1219427 10418321 := bstep (se 2 (by rfl) ⟨3906870, by rfl⟩ : syracuseStep 10418321 = 7813741) B7813741
theorem B2317339 : Blo 1219427 2317339 := bstep (se 1 (by rfl) ⟨1738004, by rfl⟩ : syracuseStep 2317339 = 3476009) B3476009
theorem B22256689 : Blo 1219427 22256689 := bstep (se 2 (by rfl) ⟨8346258, by rfl⟩ : syracuseStep 22256689 = 16692517) B16692517
theorem B1219647 : Blo 1219427 1219647 := bstep (se 1 (by rfl) ⟨914735, by rfl⟩ : syracuseStep 1219647 = 1829471) B1829471
theorem B2317385 : Blo 1219427 2317385 := bstep (se 2 (by rfl) ⟨869019, by rfl⟩ : syracuseStep 2317385 = 1738039) B1738039
theorem B1219695 : Blo 1219427 1219695 := bstep (se 1 (by rfl) ⟨914771, by rfl⟩ : syracuseStep 1219695 = 1829543) B1829543
theorem B1219711 : Blo 1219427 1219711 := bstep (se 1 (by rfl) ⟨914783, by rfl⟩ : syracuseStep 1219711 = 1829567) B1829567
theorem B1547419 : Blo 1219427 1547419 := bstep (se 1 (by rfl) ⟨1160564, by rfl⟩ : syracuseStep 1547419 = 2321129) B2321129
theorem B1219823 : Blo 1219427 1219823 := bstep (se 1 (by rfl) ⟨914867, by rfl⟩ : syracuseStep 1219823 = 1829735) B1829735
theorem B1219967 : Blo 1219427 1219967 := bstep (se 1 (by rfl) ⟨914975, by rfl⟩ : syracuseStep 1219967 = 1829951) B1829951
theorem B1220031 : Blo 1219427 1220031 := bstep (se 1 (by rfl) ⟨915023, by rfl⟩ : syracuseStep 1220031 = 1830047) B1830047
theorem B1220079 : Blo 1219427 1220079 := bstep (se 1 (by rfl) ⟨915059, by rfl⟩ : syracuseStep 1220079 = 1830119) B1830119
theorem B1220251 : Blo 1219427 1220251 := bstep (se 1 (by rfl) ⟨915188, by rfl⟩ : syracuseStep 1220251 = 1830377) B1830377
theorem B1220287 : Blo 1219427 1220287 := bstep (se 1 (by rfl) ⟨915215, by rfl⟩ : syracuseStep 1220287 = 1830431) B1830431
theorem B1736911 : Blo 1219427 1736911 := bstep (se 1 (by rfl) ⟨1302683, by rfl⟩ : syracuseStep 1736911 = 2605367) B2605367
theorem B33399823 : Blo 1219427 33399823 := bstep (se 1 (by rfl) ⟨25049867, by rfl⟩ : syracuseStep 33399823 = 50099735) B50099735
theorem B3089785 : Blo 1219427 3089785 := bstep (se 2 (by rfl) ⟨1158669, by rfl⟩ : syracuseStep 3089785 = 2317339) B2317339
theorem B11879905 : Blo 1219427 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B21121499 : Blo 1219427 21121499 := bstep (se 1 (by rfl) ⟨15841124, by rfl⟩ : syracuseStep 21121499 = 31682249) B31682249
theorem B3910447 : Blo 1219427 3910447 := bstep (se 1 (by rfl) ⟨2932835, by rfl⟩ : syracuseStep 3910447 = 5865671) B5865671
theorem B126856115 : Blo 1219427 126856115 := bstep (se 1 (by rfl) ⟨95142086, by rfl⟩ : syracuseStep 126856115 = 190284173) B190284173
theorem B1829915 : Blo 1219427 1829915 := bstep (se 1 (by rfl) ⟨1372436, by rfl⟩ : syracuseStep 1829915 = 2744873) B2744873
theorem B3476591 : Blo 1219427 3476591 := bstep (se 1 (by rfl) ⟨2607443, by rfl⟩ : syracuseStep 3476591 = 5214887) B5214887
theorem B67677535 : Blo 1219427 67677535 := bstep (se 1 (by rfl) ⟨50758151, by rfl⟩ : syracuseStep 67677535 = 101516303) B101516303
theorem B1830455 : Blo 1219427 1830455 := bstep (se 1 (by rfl) ⟨1372841, by rfl⟩ : syracuseStep 1830455 = 2745683) B2745683
theorem B1830623 : Blo 1219427 1830623 := bstep (se 1 (by rfl) ⟨1372967, by rfl⟩ : syracuseStep 1830623 = 2745935) B2745935
theorem B450981665 : Blo 1219427 450981665 := bstep (se 2 (by rfl) ⟨169118124, by rfl⟩ : syracuseStep 450981665 = 338236249) B338236249
theorem B1830767 : Blo 1219427 1830767 := bstep (se 1 (by rfl) ⟨1373075, by rfl⟩ : syracuseStep 1830767 = 2746151) B2746151
theorem B1830815 : Blo 1219427 1830815 := bstep (se 1 (by rfl) ⟨1373111, by rfl⟩ : syracuseStep 1830815 = 2746223) B2746223
theorem B29675585 : Blo 1219427 29675585 := bstep (se 2 (by rfl) ⟨11128344, by rfl⟩ : syracuseStep 29675585 = 22256689) B22256689
theorem B16691321 : Blo 1219427 16691321 := bstep (se 2 (by rfl) ⟨6259245, by rfl⟩ : syracuseStep 16691321 = 12518491) B12518491
theorem B1544923 : Blo 1219427 1544923 := bstep (se 1 (by rfl) ⟨1158692, by rfl⟩ : syracuseStep 1544923 = 2317385) B2317385
theorem B4396025 : Blo 1219427 4396025 := bstep (se 2 (by rfl) ⟨1648509, by rfl⟩ : syracuseStep 4396025 = 3297019) B3297019
theorem B1373287 : Blo 1219427 1373287 := bstep (se 1 (by rfl) ⟨1029965, by rfl⟩ : syracuseStep 1373287 = 2059931) B2059931
theorem B4117931 : Blo 1219427 4117931 := bstep (se 1 (by rfl) ⟨3088448, by rfl⟩ : syracuseStep 4117931 = 6176897) B6176897
theorem B6952655 : Blo 1219427 6952655 := bstep (se 1 (by rfl) ⟨5214491, by rfl⟩ : syracuseStep 6952655 = 10428983) B10428983
theorem B114259679 : Blo 1219427 114259679 := bstep (se 1 (by rfl) ⟨85694759, by rfl⟩ : syracuseStep 114259679 = 171389519) B171389519
theorem B5568263 : Blo 1219427 5568263 := bstep (se 1 (by rfl) ⟨4176197, by rfl⟩ : syracuseStep 5568263 = 8352395) B8352395
theorem B18331525 : Blo 1219427 18331525 := bstep (se 4 (by rfl) ⟨1718580, by rfl⟩ : syracuseStep 18331525 = 3437161) B3437161
theorem B4634921 : Blo 1219427 4634921 := bstep (se 2 (by rfl) ⟨1738095, by rfl⟩ : syracuseStep 4634921 = 3476191) B3476191
theorem B6945547 : Blo 1219427 6945547 := bstep (se 1 (by rfl) ⟨5209160, by rfl⟩ : syracuseStep 6945547 = 10418321) B10418321
theorem B2063225 : Blo 1219427 2063225 := bstep (se 2 (by rfl) ⟨773709, by rfl⟩ : syracuseStep 2063225 = 1547419) B1547419
theorem B1219611 : Blo 1219427 1219611 := bstep (se 1 (by rfl) ⟨914708, by rfl⟩ : syracuseStep 1219611 = 1829417) B1829417
theorem B1220123 : Blo 1219427 1220123 := bstep (se 1 (by rfl) ⟨915092, by rfl⟩ : syracuseStep 1220123 = 1830185) B1830185
theorem B1220455 : Blo 1219427 1220455 := bstep (se 1 (by rfl) ⟨915341, by rfl⟩ : syracuseStep 1220455 = 1830683) B1830683
theorem B11149271 : Blo 1219427 11149271 := bstep (se 1 (by rfl) ⟨8361953, by rfl⟩ : syracuseStep 11149271 = 16723907) B16723907
theorem B19783723 : Blo 1219427 19783723 := bstep (se 1 (by rfl) ⟨14837792, by rfl⟩ : syracuseStep 19783723 = 29675585) B29675585
theorem B2745287 : Blo 1219427 2745287 := bstep (se 1 (by rfl) ⟨2058965, by rfl⟩ : syracuseStep 2745287 = 4117931) B4117931
theorem B3712175 : Blo 1219427 3712175 := bstep (se 1 (by rfl) ⟨2784131, by rfl⟩ : syracuseStep 3712175 = 5568263) B5568263
theorem B44533097 : Blo 1219427 44533097 := bstep (se 2 (by rfl) ⟨16699911, by rfl⟩ : syracuseStep 44533097 = 33399823) B33399823
theorem B3089947 : Blo 1219427 3089947 := bstep (se 1 (by rfl) ⟨2317460, by rfl⟩ : syracuseStep 3089947 = 4634921) B4634921
theorem B90236713 : Blo 1219427 90236713 := bstep (se 2 (by rfl) ⟨33838767, by rfl⟩ : syracuseStep 90236713 = 67677535) B67677535
theorem B7432847 : Blo 1219427 7432847 := bstep (se 1 (by rfl) ⟨5574635, by rfl⟩ : syracuseStep 7432847 = 11149271) B11149271
theorem B11127547 : Blo 1219427 11127547 := bstep (se 1 (by rfl) ⟨8345660, by rfl⟩ : syracuseStep 11127547 = 16691321) B16691321
theorem B2059897 : Blo 1219427 2059897 := bstep (se 2 (by rfl) ⟨772461, by rfl⟩ : syracuseStep 2059897 = 1544923) B1544923
theorem B9260729 : Blo 1219427 9260729 := bstep (se 2 (by rfl) ⟨3472773, by rfl⟩ : syracuseStep 9260729 = 6945547) B6945547
theorem B5213929 : Blo 1219427 5213929 := bstep (se 2 (by rfl) ⟨1955223, by rfl⟩ : syracuseStep 5213929 = 3910447) B3910447
theorem B76173119 : Blo 1219427 76173119 := bstep (se 1 (by rfl) ⟨57129839, by rfl⟩ : syracuseStep 76173119 = 114259679) B114259679
theorem B1831049 : Blo 1219427 1831049 := bstep (se 2 (by rfl) ⟨686643, by rfl⟩ : syracuseStep 1831049 = 1373287) B1373287
theorem B84570743 : Blo 1219427 84570743 := bstep (se 1 (by rfl) ⟨63428057, by rfl⟩ : syracuseStep 84570743 = 126856115) B126856115
theorem B15839873 : Blo 1219427 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B24442033 : Blo 1219427 24442033 := bstep (se 2 (by rfl) ⟨9165762, by rfl⟩ : syracuseStep 24442033 = 18331525) B18331525
theorem B2315881 : Blo 1219427 2315881 := bstep (se 2 (by rfl) ⟨868455, by rfl⟩ : syracuseStep 2315881 = 1736911) B1736911
theorem B2930683 : Blo 1219427 2930683 := bstep (se 1 (by rfl) ⟨2198012, by rfl⟩ : syracuseStep 2930683 = 4396025) B4396025
theorem B4635103 : Blo 1219427 4635103 := bstep (se 1 (by rfl) ⟨3476327, by rfl⟩ : syracuseStep 4635103 = 6952655) B6952655
theorem B14080999 : Blo 1219427 14080999 := bstep (se 1 (by rfl) ⟨10560749, by rfl⟩ : syracuseStep 14080999 = 21121499) B21121499
theorem B4119713 : Blo 1219427 4119713 := bstep (se 2 (by rfl) ⟨1544892, by rfl⟩ : syracuseStep 4119713 = 3089785) B3089785
theorem B1375483 : Blo 1219427 1375483 := bstep (se 1 (by rfl) ⟨1031612, by rfl⟩ : syracuseStep 1375483 = 2063225) B2063225
theorem B1219943 : Blo 1219427 1219943 := bstep (se 1 (by rfl) ⟨914957, by rfl⟩ : syracuseStep 1219943 = 1829915) B1829915
theorem B2317727 : Blo 1219427 2317727 := bstep (se 1 (by rfl) ⟨1738295, by rfl⟩ : syracuseStep 2317727 = 3476591) B3476591
theorem B1220303 : Blo 1219427 1220303 := bstep (se 1 (by rfl) ⟨915227, by rfl⟩ : syracuseStep 1220303 = 1830455) B1830455
theorem B1220415 : Blo 1219427 1220415 := bstep (se 1 (by rfl) ⟨915311, by rfl⟩ : syracuseStep 1220415 = 1830623) B1830623
theorem B300654443 : Blo 1219427 300654443 := bstep (se 1 (by rfl) ⟨225490832, by rfl⟩ : syracuseStep 300654443 = 450981665) B450981665
theorem B1220511 : Blo 1219427 1220511 := bstep (se 1 (by rfl) ⟨915383, by rfl⟩ : syracuseStep 1220511 = 1830767) B1830767
theorem B1220543 : Blo 1219427 1220543 := bstep (se 1 (by rfl) ⟨915407, by rfl⟩ : syracuseStep 1220543 = 1830815) B1830815
theorem B26378297 : Blo 1219427 26378297 := bstep (se 2 (by rfl) ⟨9891861, by rfl⟩ : syracuseStep 26378297 = 19783723) B19783723
theorem B1220699 : Blo 1219427 1220699 := bstep (se 1 (by rfl) ⟨915524, by rfl⟩ : syracuseStep 1220699 = 1831049) B1831049
theorem B10559915 : Blo 1219427 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B2474783 : Blo 1219427 2474783 := bstep (se 1 (by rfl) ⟨1856087, by rfl⟩ : syracuseStep 2474783 = 3712175) B3712175
theorem B29688731 : Blo 1219427 29688731 := bstep (se 1 (by rfl) ⟨22266548, by rfl⟩ : syracuseStep 29688731 = 44533097) B44533097
theorem B14836729 : Blo 1219427 14836729 := bstep (se 2 (by rfl) ⟨5563773, by rfl⟩ : syracuseStep 14836729 = 11127547) B11127547
theorem B32589377 : Blo 1219427 32589377 := bstep (se 2 (by rfl) ⟨12221016, by rfl⟩ : syracuseStep 32589377 = 24442033) B24442033
theorem B2746475 : Blo 1219427 2746475 := bstep (se 1 (by rfl) ⟨2059856, by rfl⟩ : syracuseStep 2746475 = 4119713) B4119713
theorem B2746529 : Blo 1219427 2746529 := bstep (se 2 (by rfl) ⟨1029948, by rfl⟩ : syracuseStep 2746529 = 2059897) B2059897
theorem B200436295 : Blo 1219427 200436295 := bstep (se 1 (by rfl) ⟨150327221, by rfl⟩ : syracuseStep 200436295 = 300654443) B300654443
theorem B56380495 : Blo 1219427 56380495 := bstep (se 1 (by rfl) ⟨42285371, by rfl⟩ : syracuseStep 56380495 = 84570743) B84570743
theorem B6180137 : Blo 1219427 6180137 := bstep (se 2 (by rfl) ⟨2317551, by rfl⟩ : syracuseStep 6180137 = 4635103) B4635103
theorem B1830191 : Blo 1219427 1830191 := bstep (se 1 (by rfl) ⟨1372643, by rfl⟩ : syracuseStep 1830191 = 2745287) B2745287
theorem B1545151 : Blo 1219427 1545151 := bstep (se 1 (by rfl) ⟨1158863, by rfl⟩ : syracuseStep 1545151 = 2317727) B2317727
theorem B6951905 : Blo 1219427 6951905 := bstep (se 2 (by rfl) ⟨2606964, by rfl⟩ : syracuseStep 6951905 = 5213929) B5213929
theorem B6173819 : Blo 1219427 6173819 := bstep (se 1 (by rfl) ⟨4630364, by rfl⟩ : syracuseStep 6173819 = 9260729) B9260729
theorem B18774665 : Blo 1219427 18774665 := bstep (se 2 (by rfl) ⟨7040499, by rfl⟩ : syracuseStep 18774665 = 14080999) B14080999
theorem B1833977 : Blo 1219427 1833977 := bstep (se 2 (by rfl) ⟨687741, by rfl⟩ : syracuseStep 1833977 = 1375483) B1375483
theorem B4955231 : Blo 1219427 4955231 := bstep (se 1 (by rfl) ⟨3716423, by rfl⟩ : syracuseStep 4955231 = 7432847) B7432847
theorem B4119929 : Blo 1219427 4119929 := bstep (se 2 (by rfl) ⟨1544973, by rfl⟩ : syracuseStep 4119929 = 3089947) B3089947
theorem B3087841 : Blo 1219427 3087841 := bstep (se 2 (by rfl) ⟨1157940, by rfl⟩ : syracuseStep 3087841 = 2315881) B2315881
theorem B120315617 : Blo 1219427 120315617 := bstep (se 2 (by rfl) ⟨45118356, by rfl⟩ : syracuseStep 120315617 = 90236713) B90236713
theorem B50782079 : Blo 1219427 50782079 := bstep (se 1 (by rfl) ⟨38086559, by rfl⟩ : syracuseStep 50782079 = 76173119) B76173119
theorem B3907577 : Blo 1219427 3907577 := bstep (se 2 (by rfl) ⟨1465341, by rfl⟩ : syracuseStep 3907577 = 2930683) B2930683
theorem B13213949 : Blo 1219427 13213949 := bstep (se 3 (by rfl) ⟨2477615, by rfl⟩ : syracuseStep 13213949 = 4955231) B4955231
theorem B19792487 : Blo 1219427 19792487 := bstep (se 1 (by rfl) ⟨14844365, by rfl⟩ : syracuseStep 19792487 = 29688731) B29688731
theorem B267248393 : Blo 1219427 267248393 := bstep (se 2 (by rfl) ⟨100218147, by rfl⟩ : syracuseStep 267248393 = 200436295) B200436295
theorem B21726251 : Blo 1219427 21726251 := bstep (se 1 (by rfl) ⟨16294688, by rfl⟩ : syracuseStep 21726251 = 32589377) B32589377
theorem B1222651 : Blo 1219427 1222651 := bstep (se 1 (by rfl) ⟨916988, by rfl⟩ : syracuseStep 1222651 = 1833977) B1833977
theorem B2746619 : Blo 1219427 2746619 := bstep (se 1 (by rfl) ⟨2059964, by rfl⟩ : syracuseStep 2746619 = 4119929) B4119929
theorem B80210411 : Blo 1219427 80210411 := bstep (se 1 (by rfl) ⟨60157808, by rfl⟩ : syracuseStep 80210411 = 120315617) B120315617
theorem B7039943 : Blo 1219427 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B1649855 : Blo 1219427 1649855 := bstep (se 1 (by rfl) ⟨1237391, by rfl⟩ : syracuseStep 1649855 = 2474783) B2474783
theorem B4115879 : Blo 1219427 4115879 := bstep (se 1 (by rfl) ⟨3086909, by rfl⟩ : syracuseStep 4115879 = 6173819) B6173819
theorem B2060201 : Blo 1219427 2060201 := bstep (se 2 (by rfl) ⟨772575, by rfl⟩ : syracuseStep 2060201 = 1545151) B1545151
theorem B1830983 : Blo 1219427 1830983 := bstep (se 1 (by rfl) ⟨1373237, by rfl⟩ : syracuseStep 1830983 = 2746475) B2746475
theorem B75173993 : Blo 1219427 75173993 := bstep (se 2 (by rfl) ⟨28190247, by rfl⟩ : syracuseStep 75173993 = 56380495) B56380495
theorem B1831019 : Blo 1219427 1831019 := bstep (se 1 (by rfl) ⟨1373264, by rfl⟩ : syracuseStep 1831019 = 2746529) B2746529
theorem B4117121 : Blo 1219427 4117121 := bstep (se 2 (by rfl) ⟨1543920, by rfl⟩ : syracuseStep 4117121 = 3087841) B3087841
theorem B33854719 : Blo 1219427 33854719 := bstep (se 1 (by rfl) ⟨25391039, by rfl⟩ : syracuseStep 33854719 = 50782079) B50782079
theorem B17585531 : Blo 1219427 17585531 := bstep (se 1 (by rfl) ⟨13189148, by rfl⟩ : syracuseStep 17585531 = 26378297) B26378297
theorem B4634603 : Blo 1219427 4634603 := bstep (se 1 (by rfl) ⟨3475952, by rfl⟩ : syracuseStep 4634603 = 6951905) B6951905
theorem B19782305 : Blo 1219427 19782305 := bstep (se 2 (by rfl) ⟨7418364, by rfl⟩ : syracuseStep 19782305 = 14836729) B14836729
theorem B12516443 : Blo 1219427 12516443 := bstep (se 1 (by rfl) ⟨9387332, by rfl⟩ : syracuseStep 12516443 = 18774665) B18774665
theorem B4120091 : Blo 1219427 4120091 := bstep (se 1 (by rfl) ⟨3090068, by rfl⟩ : syracuseStep 4120091 = 6180137) B6180137
theorem B1220127 : Blo 1219427 1220127 := bstep (se 1 (by rfl) ⟨915095, by rfl⟩ : syracuseStep 1220127 = 1830191) B1830191
theorem B2605051 : Blo 1219427 2605051 := bstep (se 1 (by rfl) ⟨1953788, by rfl⟩ : syracuseStep 2605051 = 3907577) B3907577
theorem B1220655 : Blo 1219427 1220655 := bstep (se 1 (by rfl) ⟨915491, by rfl⟩ : syracuseStep 1220655 = 1830983) B1830983
theorem B1220679 : Blo 1219427 1220679 := bstep (se 1 (by rfl) ⟨915509, by rfl⟩ : syracuseStep 1220679 = 1831019) B1831019
theorem B2744747 : Blo 1219427 2744747 := bstep (se 1 (by rfl) ⟨2058560, by rfl⟩ : syracuseStep 2744747 = 4117121) B4117121
theorem B4399613 : Blo 1219427 4399613 := bstep (se 3 (by rfl) ⟨824927, by rfl⟩ : syracuseStep 4399613 = 1649855) B1649855
theorem B14484167 : Blo 1219427 14484167 := bstep (se 1 (by rfl) ⟨10863125, by rfl⟩ : syracuseStep 14484167 = 21726251) B21726251
theorem B11723687 : Blo 1219427 11723687 := bstep (se 1 (by rfl) ⟨8792765, by rfl⟩ : syracuseStep 11723687 = 17585531) B17585531
theorem B3089735 : Blo 1219427 3089735 := bstep (se 1 (by rfl) ⟨2317301, by rfl⟩ : syracuseStep 3089735 = 4634603) B4634603
theorem B45139625 : Blo 1219427 45139625 := bstep (se 2 (by rfl) ⟨16927359, by rfl⟩ : syracuseStep 45139625 = 33854719) B33854719
theorem B1630201 : Blo 1219427 1630201 := bstep (se 2 (by rfl) ⟨611325, by rfl⟩ : syracuseStep 1630201 = 1222651) B1222651
theorem B3473401 : Blo 1219427 3473401 := bstep (se 2 (by rfl) ⟨1302525, by rfl⟩ : syracuseStep 3473401 = 2605051) B2605051
theorem B2746727 : Blo 1219427 2746727 := bstep (se 1 (by rfl) ⟨2060045, by rfl⟩ : syracuseStep 2746727 = 4120091) B4120091
theorem B35237197 : Blo 1219427 35237197 := bstep (se 3 (by rfl) ⟨6606974, by rfl⟩ : syracuseStep 35237197 = 13213949) B13213949
theorem B1831079 : Blo 1219427 1831079 := bstep (se 1 (by rfl) ⟨1373309, by rfl⟩ : syracuseStep 1831079 = 2746619) B2746619
theorem B53473607 : Blo 1219427 53473607 := bstep (se 1 (by rfl) ⟨40105205, by rfl⟩ : syracuseStep 53473607 = 80210411) B80210411
theorem B8344295 : Blo 1219427 8344295 := bstep (se 1 (by rfl) ⟨6258221, by rfl⟩ : syracuseStep 8344295 = 12516443) B12516443
theorem B1373467 : Blo 1219427 1373467 := bstep (se 1 (by rfl) ⟨1030100, by rfl⟩ : syracuseStep 1373467 = 2060201) B2060201
theorem B50115995 : Blo 1219427 50115995 := bstep (se 1 (by rfl) ⟨37586996, by rfl⟩ : syracuseStep 50115995 = 75173993) B75173993
theorem B13194991 : Blo 1219427 13194991 := bstep (se 1 (by rfl) ⟨9896243, by rfl⟩ : syracuseStep 13194991 = 19792487) B19792487
theorem B178165595 : Blo 1219427 178165595 := bstep (se 1 (by rfl) ⟨133624196, by rfl⟩ : syracuseStep 178165595 = 267248393) B267248393
theorem B13188203 : Blo 1219427 13188203 := bstep (se 1 (by rfl) ⟨9891152, by rfl⟩ : syracuseStep 13188203 = 19782305) B19782305
theorem B4693295 : Blo 1219427 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B2743919 : Blo 1219427 2743919 := bstep (se 1 (by rfl) ⟨2057939, by rfl⟩ : syracuseStep 2743919 = 4115879) B4115879
theorem B1220719 : Blo 1219427 1220719 := bstep (se 1 (by rfl) ⟨915539, by rfl⟩ : syracuseStep 1220719 = 1831079) B1831079
theorem B2933075 : Blo 1219427 2933075 := bstep (se 1 (by rfl) ⟨2199806, by rfl⟩ : syracuseStep 2933075 = 4399613) B4399613
theorem B5562863 : Blo 1219427 5562863 := bstep (se 1 (by rfl) ⟨4172147, by rfl⟩ : syracuseStep 5562863 = 8344295) B8344295
theorem B7815791 : Blo 1219427 7815791 := bstep (se 1 (by rfl) ⟨5861843, by rfl⟩ : syracuseStep 7815791 = 11723687) B11723687
theorem B118777063 : Blo 1219427 118777063 := bstep (se 1 (by rfl) ⟨89082797, by rfl⟩ : syracuseStep 118777063 = 178165595) B178165595
theorem B46982929 : Blo 1219427 46982929 := bstep (se 2 (by rfl) ⟨17618598, by rfl⟩ : syracuseStep 46982929 = 35237197) B35237197
theorem B8792135 : Blo 1219427 8792135 := bstep (se 1 (by rfl) ⟨6594101, by rfl⟩ : syracuseStep 8792135 = 13188203) B13188203
theorem B1829279 : Blo 1219427 1829279 := bstep (se 1 (by rfl) ⟨1371959, by rfl⟩ : syracuseStep 1829279 = 2743919) B2743919
theorem B4631201 : Blo 1219427 4631201 := bstep (se 2 (by rfl) ⟨1736700, by rfl⟩ : syracuseStep 4631201 = 3473401) B3473401
theorem B2173601 : Blo 1219427 2173601 := bstep (se 2 (by rfl) ⟨815100, by rfl⟩ : syracuseStep 2173601 = 1630201) B1630201
theorem B1829831 : Blo 1219427 1829831 := bstep (se 1 (by rfl) ⟨1372373, by rfl⟩ : syracuseStep 1829831 = 2744747) B2744747
theorem B2059823 : Blo 1219427 2059823 := bstep (se 1 (by rfl) ⟨1544867, by rfl⟩ : syracuseStep 2059823 = 3089735) B3089735
theorem B33410663 : Blo 1219427 33410663 := bstep (se 1 (by rfl) ⟨25057997, by rfl⟩ : syracuseStep 33410663 = 50115995) B50115995
theorem B30093083 : Blo 1219427 30093083 := bstep (se 1 (by rfl) ⟨22569812, by rfl⟩ : syracuseStep 30093083 = 45139625) B45139625
theorem B1831151 : Blo 1219427 1831151 := bstep (se 1 (by rfl) ⟨1373363, by rfl⟩ : syracuseStep 1831151 = 2746727) B2746727
theorem B1831289 : Blo 1219427 1831289 := bstep (se 2 (by rfl) ⟨686733, by rfl⟩ : syracuseStep 1831289 = 1373467) B1373467
theorem B17593321 : Blo 1219427 17593321 := bstep (se 2 (by rfl) ⟨6597495, by rfl⟩ : syracuseStep 17593321 = 13194991) B13194991
theorem B35649071 : Blo 1219427 35649071 := bstep (se 1 (by rfl) ⟨26736803, by rfl⟩ : syracuseStep 35649071 = 53473607) B53473607
theorem B9656111 : Blo 1219427 9656111 := bstep (se 1 (by rfl) ⟨7242083, by rfl⟩ : syracuseStep 9656111 = 14484167) B14484167
theorem B3128863 : Blo 1219427 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B1220767 : Blo 1219427 1220767 := bstep (se 1 (by rfl) ⟨915575, by rfl⟩ : syracuseStep 1220767 = 1831151) B1831151
theorem B1220859 : Blo 1219427 1220859 := bstep (se 1 (by rfl) ⟨915644, by rfl⟩ : syracuseStep 1220859 = 1831289) B1831289
theorem B23766047 : Blo 1219427 23766047 := bstep (se 1 (by rfl) ⟨17824535, by rfl⟩ : syracuseStep 23766047 = 35649071) B35649071
theorem B20842109 : Blo 1219427 20842109 := bstep (se 3 (by rfl) ⟨3907895, by rfl⟩ : syracuseStep 20842109 = 7815791) B7815791
theorem B158369417 : Blo 1219427 158369417 := bstep (se 2 (by rfl) ⟨59388531, by rfl⟩ : syracuseStep 158369417 = 118777063) B118777063
theorem B4171817 : Blo 1219427 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B23457761 : Blo 1219427 23457761 := bstep (se 2 (by rfl) ⟨8796660, by rfl⟩ : syracuseStep 23457761 = 17593321) B17593321
theorem B5861423 : Blo 1219427 5861423 := bstep (se 1 (by rfl) ⟨4396067, by rfl⟩ : syracuseStep 5861423 = 8792135) B8792135
theorem B5796269 : Blo 1219427 5796269 := bstep (se 3 (by rfl) ⟨1086800, by rfl⟩ : syracuseStep 5796269 = 2173601) B2173601
theorem B1373215 : Blo 1219427 1373215 := bstep (se 1 (by rfl) ⟨1029911, by rfl⟩ : syracuseStep 1373215 = 2059823) B2059823
theorem B1955383 : Blo 1219427 1955383 := bstep (se 1 (by rfl) ⟨1466537, by rfl⟩ : syracuseStep 1955383 = 2933075) B2933075
theorem B3708575 : Blo 1219427 3708575 := bstep (se 1 (by rfl) ⟨2781431, by rfl⟩ : syracuseStep 3708575 = 5562863) B5562863
theorem B6437407 : Blo 1219427 6437407 := bstep (se 1 (by rfl) ⟨4828055, by rfl⟩ : syracuseStep 6437407 = 9656111) B9656111
theorem B1219519 : Blo 1219427 1219519 := bstep (se 1 (by rfl) ⟨914639, by rfl⟩ : syracuseStep 1219519 = 1829279) B1829279
theorem B3087467 : Blo 1219427 3087467 := bstep (se 1 (by rfl) ⟨2315600, by rfl⟩ : syracuseStep 3087467 = 4631201) B4631201
theorem B1219887 : Blo 1219427 1219887 := bstep (se 1 (by rfl) ⟨914915, by rfl⟩ : syracuseStep 1219887 = 1829831) B1829831
theorem B62643905 : Blo 1219427 62643905 := bstep (se 2 (by rfl) ⟨23491464, by rfl⟩ : syracuseStep 62643905 = 46982929) B46982929
theorem B22273775 : Blo 1219427 22273775 := bstep (se 1 (by rfl) ⟨16705331, by rfl⟩ : syracuseStep 22273775 = 33410663) B33410663
theorem B20062055 : Blo 1219427 20062055 := bstep (se 1 (by rfl) ⟨15046541, by rfl⟩ : syracuseStep 20062055 = 30093083) B30093083
theorem B3907615 : Blo 1219427 3907615 := bstep (se 1 (by rfl) ⟨2930711, by rfl⟩ : syracuseStep 3907615 = 5861423) B5861423
theorem B10428709 : Blo 1219427 10428709 := bstep (se 4 (by rfl) ⟨977691, by rfl⟩ : syracuseStep 10428709 = 1955383) B1955383
theorem B15844031 : Blo 1219427 15844031 := bstep (se 1 (by rfl) ⟨11883023, by rfl⟩ : syracuseStep 15844031 = 23766047) B23766047
theorem B13894739 : Blo 1219427 13894739 := bstep (se 1 (by rfl) ⟨10421054, by rfl⟩ : syracuseStep 13894739 = 20842109) B20842109
theorem B105579611 : Blo 1219427 105579611 := bstep (se 1 (by rfl) ⟨79184708, by rfl⟩ : syracuseStep 105579611 = 158369417) B158369417
theorem B2058311 : Blo 1219427 2058311 := bstep (se 1 (by rfl) ⟨1543733, by rfl⟩ : syracuseStep 2058311 = 3087467) B3087467
theorem B2781211 : Blo 1219427 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B1830953 : Blo 1219427 1830953 := bstep (se 2 (by rfl) ⟨686607, by rfl⟩ : syracuseStep 1830953 = 1373215) B1373215
theorem B14849183 : Blo 1219427 14849183 := bstep (se 1 (by rfl) ⟨11136887, by rfl⟩ : syracuseStep 14849183 = 22273775) B22273775
theorem B13374703 : Blo 1219427 13374703 := bstep (se 1 (by rfl) ⟨10031027, by rfl⟩ : syracuseStep 13374703 = 20062055) B20062055
theorem B3864179 : Blo 1219427 3864179 := bstep (se 1 (by rfl) ⟨2898134, by rfl⟩ : syracuseStep 3864179 = 5796269) B5796269
theorem B8583209 : Blo 1219427 8583209 := bstep (se 2 (by rfl) ⟨3218703, by rfl⟩ : syracuseStep 8583209 = 6437407) B6437407
theorem B2472383 : Blo 1219427 2472383 := bstep (se 1 (by rfl) ⟨1854287, by rfl⟩ : syracuseStep 2472383 = 3708575) B3708575
theorem B41762603 : Blo 1219427 41762603 := bstep (se 1 (by rfl) ⟨31321952, by rfl⟩ : syracuseStep 41762603 = 62643905) B62643905
theorem B15638507 : Blo 1219427 15638507 := bstep (se 1 (by rfl) ⟨11728880, by rfl⟩ : syracuseStep 15638507 = 23457761) B23457761
theorem B1220635 : Blo 1219427 1220635 := bstep (se 1 (by rfl) ⟨915476, by rfl⟩ : syracuseStep 1220635 = 1830953) B1830953
theorem B5210153 : Blo 1219427 5210153 := bstep (se 2 (by rfl) ⟨1953807, by rfl⟩ : syracuseStep 5210153 = 3907615) B3907615
theorem B70386407 : Blo 1219427 70386407 := bstep (se 1 (by rfl) ⟨52789805, by rfl⟩ : syracuseStep 70386407 = 105579611) B105579611
theorem B13904945 : Blo 1219427 13904945 := bstep (se 2 (by rfl) ⟨5214354, by rfl⟩ : syracuseStep 13904945 = 10428709) B10428709
theorem B10562687 : Blo 1219427 10562687 := bstep (se 1 (by rfl) ⟨7922015, by rfl⟩ : syracuseStep 10562687 = 15844031) B15844031
theorem B2576119 : Blo 1219427 2576119 := bstep (se 1 (by rfl) ⟨1932089, by rfl⟩ : syracuseStep 2576119 = 3864179) B3864179
theorem B71331749 : Blo 1219427 71331749 := bstep (se 4 (by rfl) ⟨6687351, by rfl⟩ : syracuseStep 71331749 = 13374703) B13374703
theorem B5722139 : Blo 1219427 5722139 := bstep (se 1 (by rfl) ⟨4291604, by rfl⟩ : syracuseStep 5722139 = 8583209) B8583209
theorem B1372207 : Blo 1219427 1372207 := bstep (se 1 (by rfl) ⟨1029155, by rfl⟩ : syracuseStep 1372207 = 2058311) B2058311
theorem B27841735 : Blo 1219427 27841735 := bstep (se 1 (by rfl) ⟨20881301, by rfl⟩ : syracuseStep 27841735 = 41762603) B41762603
theorem B10425671 : Blo 1219427 10425671 := bstep (se 1 (by rfl) ⟨7819253, by rfl⟩ : syracuseStep 10425671 = 15638507) B15638507
theorem B3708281 : Blo 1219427 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B39597821 : Blo 1219427 39597821 := bstep (se 3 (by rfl) ⟨7424591, by rfl⟩ : syracuseStep 39597821 = 14849183) B14849183
theorem B9263159 : Blo 1219427 9263159 := bstep (se 1 (by rfl) ⟨6947369, by rfl⟩ : syracuseStep 9263159 = 13894739) B13894739
theorem B6593021 : Blo 1219427 6593021 := bstep (se 3 (by rfl) ⟨1236191, by rfl⟩ : syracuseStep 6593021 = 2472383) B2472383
theorem B3473435 : Blo 1219427 3473435 := bstep (se 1 (by rfl) ⟨2605076, by rfl⟩ : syracuseStep 3473435 = 5210153) B5210153
theorem B46924271 : Blo 1219427 46924271 := bstep (se 1 (by rfl) ⟨35193203, by rfl⟩ : syracuseStep 46924271 = 70386407) B70386407
theorem B9888749 : Blo 1219427 9888749 := bstep (se 3 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 9888749 = 3708281) B3708281
theorem B3434825 : Blo 1219427 3434825 := bstep (se 2 (by rfl) ⟨1288059, by rfl⟩ : syracuseStep 3434825 = 2576119) B2576119
theorem B1829609 : Blo 1219427 1829609 := bstep (se 2 (by rfl) ⟨686103, by rfl⟩ : syracuseStep 1829609 = 1372207) B1372207
theorem B6950447 : Blo 1219427 6950447 := bstep (se 1 (by rfl) ⟨5212835, by rfl⟩ : syracuseStep 6950447 = 10425671) B10425671
theorem B26398547 : Blo 1219427 26398547 := bstep (se 1 (by rfl) ⟨19798910, by rfl⟩ : syracuseStep 26398547 = 39597821) B39597821
theorem B37122313 : Blo 1219427 37122313 := bstep (se 2 (by rfl) ⟨13920867, by rfl⟩ : syracuseStep 37122313 = 27841735) B27841735
theorem B4395347 : Blo 1219427 4395347 := bstep (se 1 (by rfl) ⟨3296510, by rfl⟩ : syracuseStep 4395347 = 6593021) B6593021
theorem B9269963 : Blo 1219427 9269963 := bstep (se 1 (by rfl) ⟨6952472, by rfl⟩ : syracuseStep 9269963 = 13904945) B13904945
theorem B7041791 : Blo 1219427 7041791 := bstep (se 1 (by rfl) ⟨5281343, by rfl⟩ : syracuseStep 7041791 = 10562687) B10562687
theorem B3814759 : Blo 1219427 3814759 := bstep (se 1 (by rfl) ⟨2861069, by rfl⟩ : syracuseStep 3814759 = 5722139) B5722139
theorem B6175439 : Blo 1219427 6175439 := bstep (se 1 (by rfl) ⟨4631579, by rfl⟩ : syracuseStep 6175439 = 9263159) B9263159
theorem B47554499 : Blo 1219427 47554499 := bstep (se 1 (by rfl) ⟨35665874, by rfl⟩ : syracuseStep 47554499 = 71331749) B71331749
theorem B49496417 : Blo 1219427 49496417 := bstep (se 2 (by rfl) ⟨18561156, by rfl⟩ : syracuseStep 49496417 = 37122313) B37122313
theorem B4694527 : Blo 1219427 4694527 := bstep (se 1 (by rfl) ⟨3520895, by rfl⟩ : syracuseStep 4694527 = 7041791) B7041791
theorem B17599031 : Blo 1219427 17599031 := bstep (se 1 (by rfl) ⟨13199273, by rfl⟩ : syracuseStep 17599031 = 26398547) B26398547
theorem B6179975 : Blo 1219427 6179975 := bstep (se 1 (by rfl) ⟨4634981, by rfl⟩ : syracuseStep 6179975 = 9269963) B9269963
theorem B2289883 : Blo 1219427 2289883 := bstep (se 1 (by rfl) ⟨1717412, by rfl⟩ : syracuseStep 2289883 = 3434825) B3434825
theorem B4116959 : Blo 1219427 4116959 := bstep (se 1 (by rfl) ⟨3087719, by rfl⟩ : syracuseStep 4116959 = 6175439) B6175439
theorem B20345381 : Blo 1219427 20345381 := bstep (se 4 (by rfl) ⟨1907379, by rfl⟩ : syracuseStep 20345381 = 3814759) B3814759
theorem B4633631 : Blo 1219427 4633631 := bstep (se 1 (by rfl) ⟨3475223, by rfl⟩ : syracuseStep 4633631 = 6950447) B6950447
theorem B2315623 : Blo 1219427 2315623 := bstep (se 1 (by rfl) ⟨1736717, by rfl⟩ : syracuseStep 2315623 = 3473435) B3473435
theorem B2930231 : Blo 1219427 2930231 := bstep (se 1 (by rfl) ⟨2197673, by rfl⟩ : syracuseStep 2930231 = 4395347) B4395347
theorem B31282847 : Blo 1219427 31282847 := bstep (se 1 (by rfl) ⟨23462135, by rfl⟩ : syracuseStep 31282847 = 46924271) B46924271
theorem B6592499 : Blo 1219427 6592499 := bstep (se 1 (by rfl) ⟨4944374, by rfl⟩ : syracuseStep 6592499 = 9888749) B9888749
theorem B1219739 : Blo 1219427 1219739 := bstep (se 1 (by rfl) ⟨914804, by rfl⟩ : syracuseStep 1219739 = 1829609) B1829609
theorem B31702999 : Blo 1219427 31702999 := bstep (se 1 (by rfl) ⟨23777249, by rfl⟩ : syracuseStep 31702999 = 47554499) B47554499
theorem B32997611 : Blo 1219427 32997611 := bstep (se 1 (by rfl) ⟨24748208, by rfl⟩ : syracuseStep 32997611 = 49496417) B49496417
theorem B2744639 : Blo 1219427 2744639 := bstep (se 1 (by rfl) ⟨2058479, by rfl⟩ : syracuseStep 2744639 = 4116959) B4116959
theorem B6259369 : Blo 1219427 6259369 := bstep (se 2 (by rfl) ⟨2347263, by rfl⟩ : syracuseStep 6259369 = 4694527) B4694527
theorem B3089087 : Blo 1219427 3089087 := bstep (se 1 (by rfl) ⟨2316815, by rfl⟩ : syracuseStep 3089087 = 4633631) B4633631
theorem B11732687 : Blo 1219427 11732687 := bstep (se 1 (by rfl) ⟨8799515, by rfl⟩ : syracuseStep 11732687 = 17599031) B17599031
theorem B1953487 : Blo 1219427 1953487 := bstep (se 1 (by rfl) ⟨1465115, by rfl⟩ : syracuseStep 1953487 = 2930231) B2930231
theorem B4394999 : Blo 1219427 4394999 := bstep (se 1 (by rfl) ⟨3296249, by rfl⟩ : syracuseStep 4394999 = 6592499) B6592499
theorem B3053177 : Blo 1219427 3053177 := bstep (se 2 (by rfl) ⟨1144941, by rfl⟩ : syracuseStep 3053177 = 2289883) B2289883
theorem B13563587 : Blo 1219427 13563587 := bstep (se 1 (by rfl) ⟨10172690, by rfl⟩ : syracuseStep 13563587 = 20345381) B20345381
theorem B20855231 : Blo 1219427 20855231 := bstep (se 1 (by rfl) ⟨15641423, by rfl⟩ : syracuseStep 20855231 = 31282847) B31282847
theorem B3087497 : Blo 1219427 3087497 := bstep (se 2 (by rfl) ⟨1157811, by rfl⟩ : syracuseStep 3087497 = 2315623) B2315623
theorem B4119983 : Blo 1219427 4119983 := bstep (se 1 (by rfl) ⟨3089987, by rfl⟩ : syracuseStep 4119983 = 6179975) B6179975
theorem B42270665 : Blo 1219427 42270665 := bstep (se 2 (by rfl) ⟨15851499, by rfl⟩ : syracuseStep 42270665 = 31702999) B31702999
theorem B13903487 : Blo 1219427 13903487 := bstep (se 1 (by rfl) ⟨10427615, by rfl⟩ : syracuseStep 13903487 = 20855231) B20855231
theorem B2058331 : Blo 1219427 2058331 := bstep (se 1 (by rfl) ⟨1543748, by rfl⟩ : syracuseStep 2058331 = 3087497) B3087497
theorem B2746655 : Blo 1219427 2746655 := bstep (se 1 (by rfl) ⟨2059991, by rfl⟩ : syracuseStep 2746655 = 4119983) B4119983
theorem B21998407 : Blo 1219427 21998407 := bstep (se 1 (by rfl) ⟨16498805, by rfl⟩ : syracuseStep 21998407 = 32997611) B32997611
theorem B1829759 : Blo 1219427 1829759 := bstep (se 1 (by rfl) ⟨1372319, by rfl⟩ : syracuseStep 1829759 = 2744639) B2744639
theorem B2059391 : Blo 1219427 2059391 := bstep (se 1 (by rfl) ⟨1544543, by rfl⟩ : syracuseStep 2059391 = 3089087) B3089087
theorem B2035451 : Blo 1219427 2035451 := bstep (se 1 (by rfl) ⟨1526588, by rfl⟩ : syracuseStep 2035451 = 3053177) B3053177
theorem B11719997 : Blo 1219427 11719997 := bstep (se 3 (by rfl) ⟨2197499, by rfl⟩ : syracuseStep 11719997 = 4394999) B4394999
theorem B8345825 : Blo 1219427 8345825 := bstep (se 2 (by rfl) ⟨3129684, by rfl⟩ : syracuseStep 8345825 = 6259369) B6259369
theorem B9042391 : Blo 1219427 9042391 := bstep (se 1 (by rfl) ⟨6781793, by rfl⟩ : syracuseStep 9042391 = 13563587) B13563587
theorem B7821791 : Blo 1219427 7821791 := bstep (se 1 (by rfl) ⟨5866343, by rfl⟩ : syracuseStep 7821791 = 11732687) B11732687
theorem B450887093 : Blo 1219427 450887093 := bstep (se 5 (by rfl) ⟨21135332, by rfl⟩ : syracuseStep 450887093 = 42270665) B42270665
theorem B2604649 : Blo 1219427 2604649 := bstep (se 2 (by rfl) ⟨976743, by rfl⟩ : syracuseStep 2604649 = 1953487) B1953487
theorem B2744441 : Blo 1219427 2744441 := bstep (se 2 (by rfl) ⟨1029165, by rfl⟩ : syracuseStep 2744441 = 2058331) B2058331
theorem B5563883 : Blo 1219427 5563883 := bstep (se 1 (by rfl) ⟨4172912, by rfl⟩ : syracuseStep 5563883 = 8345825) B8345825
theorem B300591395 : Blo 1219427 300591395 := bstep (se 1 (by rfl) ⟨225443546, by rfl⟩ : syracuseStep 300591395 = 450887093) B450887093
theorem B9268991 : Blo 1219427 9268991 := bstep (se 1 (by rfl) ⟨6951743, by rfl⟩ : syracuseStep 9268991 = 13903487) B13903487
theorem B29331209 : Blo 1219427 29331209 := bstep (se 2 (by rfl) ⟨10999203, by rfl⟩ : syracuseStep 29331209 = 21998407) B21998407
theorem B1831103 : Blo 1219427 1831103 := bstep (se 1 (by rfl) ⟨1373327, by rfl⟩ : syracuseStep 1831103 = 2746655) B2746655
theorem B5214527 : Blo 1219427 5214527 := bstep (se 1 (by rfl) ⟨3910895, by rfl⟩ : syracuseStep 5214527 = 7821791) B7821791
theorem B1372927 : Blo 1219427 1372927 := bstep (se 1 (by rfl) ⟨1029695, by rfl⟩ : syracuseStep 1372927 = 2059391) B2059391
theorem B1356967 : Blo 1219427 1356967 := bstep (se 1 (by rfl) ⟨1017725, by rfl⟩ : syracuseStep 1356967 = 2035451) B2035451
theorem B12056521 : Blo 1219427 12056521 := bstep (se 2 (by rfl) ⟨4521195, by rfl⟩ : syracuseStep 12056521 = 9042391) B9042391
theorem B7813331 : Blo 1219427 7813331 := bstep (se 1 (by rfl) ⟨5859998, by rfl⟩ : syracuseStep 7813331 = 11719997) B11719997
theorem B1219839 : Blo 1219427 1219839 := bstep (se 1 (by rfl) ⟨914879, by rfl⟩ : syracuseStep 1219839 = 1829759) B1829759
theorem B3472865 : Blo 1219427 3472865 := bstep (se 2 (by rfl) ⟨1302324, by rfl⟩ : syracuseStep 3472865 = 2604649) B2604649
theorem B1220735 : Blo 1219427 1220735 := bstep (se 1 (by rfl) ⟨915551, by rfl⟩ : syracuseStep 1220735 = 1831103) B1831103
theorem B200394263 : Blo 1219427 200394263 := bstep (se 1 (by rfl) ⟨150295697, by rfl⟩ : syracuseStep 200394263 = 300591395) B300591395
theorem B6179327 : Blo 1219427 6179327 := bstep (se 1 (by rfl) ⟨4634495, by rfl⟩ : syracuseStep 6179327 = 9268991) B9268991
theorem B16075361 : Blo 1219427 16075361 := bstep (se 2 (by rfl) ⟨6028260, by rfl⟩ : syracuseStep 16075361 = 12056521) B12056521
theorem B1829627 : Blo 1219427 1829627 := bstep (se 1 (by rfl) ⟨1372220, by rfl⟩ : syracuseStep 1829627 = 2744441) B2744441
theorem B3476351 : Blo 1219427 3476351 := bstep (se 1 (by rfl) ⟨2607263, by rfl⟩ : syracuseStep 3476351 = 5214527) B5214527
theorem B1830569 : Blo 1219427 1830569 := bstep (se 2 (by rfl) ⟨686463, by rfl⟩ : syracuseStep 1830569 = 1372927) B1372927
theorem B2315243 : Blo 1219427 2315243 := bstep (se 1 (by rfl) ⟨1736432, by rfl⟩ : syracuseStep 2315243 = 3472865) B3472865
theorem B3709255 : Blo 1219427 3709255 := bstep (se 1 (by rfl) ⟨2781941, by rfl⟩ : syracuseStep 3709255 = 5563883) B5563883
theorem B5208887 : Blo 1219427 5208887 := bstep (se 1 (by rfl) ⟨3906665, by rfl⟩ : syracuseStep 5208887 = 7813331) B7813331
theorem B1809289 : Blo 1219427 1809289 := bstep (se 2 (by rfl) ⟨678483, by rfl⟩ : syracuseStep 1809289 = 1356967) B1356967
theorem B19554139 : Blo 1219427 19554139 := bstep (se 1 (by rfl) ⟨14665604, by rfl⟩ : syracuseStep 19554139 = 29331209) B29331209
theorem B133596175 : Blo 1219427 133596175 := bstep (se 1 (by rfl) ⟨100197131, by rfl⟩ : syracuseStep 133596175 = 200394263) B200394263
theorem B10716907 : Blo 1219427 10716907 := bstep (se 1 (by rfl) ⟨8037680, by rfl⟩ : syracuseStep 10716907 = 16075361) B16075361
theorem B2412385 : Blo 1219427 2412385 := bstep (se 2 (by rfl) ⟨904644, by rfl⟩ : syracuseStep 2412385 = 1809289) B1809289
theorem B104288741 : Blo 1219427 104288741 := bstep (se 4 (by rfl) ⟨9777069, by rfl⟩ : syracuseStep 104288741 = 19554139) B19554139
theorem B13890365 : Blo 1219427 13890365 := bstep (se 3 (by rfl) ⟨2604443, by rfl⟩ : syracuseStep 13890365 = 5208887) B5208887
theorem B6173981 : Blo 1219427 6173981 := bstep (se 3 (by rfl) ⟨1157621, by rfl⟩ : syracuseStep 6173981 = 2315243) B2315243
theorem B4945673 : Blo 1219427 4945673 := bstep (se 2 (by rfl) ⟨1854627, by rfl⟩ : syracuseStep 4945673 = 3709255) B3709255
theorem B4119551 : Blo 1219427 4119551 := bstep (se 1 (by rfl) ⟨3089663, by rfl⟩ : syracuseStep 4119551 = 6179327) B6179327
theorem B1219751 : Blo 1219427 1219751 := bstep (se 1 (by rfl) ⟨914813, by rfl⟩ : syracuseStep 1219751 = 1829627) B1829627
theorem B2317567 : Blo 1219427 2317567 := bstep (se 1 (by rfl) ⟨1738175, by rfl⟩ : syracuseStep 2317567 = 3476351) B3476351
theorem B1220379 : Blo 1219427 1220379 := bstep (se 1 (by rfl) ⟨915284, by rfl⟩ : syracuseStep 1220379 = 1830569) B1830569
theorem B69525827 : Blo 1219427 69525827 := bstep (se 1 (by rfl) ⟨52144370, by rfl⟩ : syracuseStep 69525827 = 104288741) B104288741
theorem B178128233 : Blo 1219427 178128233 := bstep (se 2 (by rfl) ⟨66798087, by rfl⟩ : syracuseStep 178128233 = 133596175) B133596175
theorem B3090089 : Blo 1219427 3090089 := bstep (se 2 (by rfl) ⟨1158783, by rfl⟩ : syracuseStep 3090089 = 2317567) B2317567
theorem B2746367 : Blo 1219427 2746367 := bstep (se 1 (by rfl) ⟨2059775, by rfl⟩ : syracuseStep 2746367 = 4119551) B4119551
theorem B14289209 : Blo 1219427 14289209 := bstep (se 2 (by rfl) ⟨5358453, by rfl⟩ : syracuseStep 14289209 = 10716907) B10716907
theorem B9260243 : Blo 1219427 9260243 := bstep (se 1 (by rfl) ⟨6945182, by rfl⟩ : syracuseStep 9260243 = 13890365) B13890365
theorem B4115987 : Blo 1219427 4115987 := bstep (se 1 (by rfl) ⟨3086990, by rfl⟩ : syracuseStep 4115987 = 6173981) B6173981
theorem B3297115 : Blo 1219427 3297115 := bstep (se 1 (by rfl) ⟨2472836, by rfl⟩ : syracuseStep 3297115 = 4945673) B4945673
theorem B12866053 : Blo 1219427 12866053 := bstep (se 4 (by rfl) ⟨1206192, by rfl⟩ : syracuseStep 12866053 = 2412385) B2412385
theorem B46350551 : Blo 1219427 46350551 := bstep (se 1 (by rfl) ⟨34762913, by rfl⟩ : syracuseStep 46350551 = 69525827) B69525827
theorem B17154737 : Blo 1219427 17154737 := bstep (se 2 (by rfl) ⟨6433026, by rfl⟩ : syracuseStep 17154737 = 12866053) B12866053
theorem B118752155 : Blo 1219427 118752155 := bstep (se 1 (by rfl) ⟨89064116, by rfl⟩ : syracuseStep 118752155 = 178128233) B178128233
theorem B2060059 : Blo 1219427 2060059 := bstep (se 1 (by rfl) ⟨1545044, by rfl⟩ : syracuseStep 2060059 = 3090089) B3090089
theorem B1830911 : Blo 1219427 1830911 := bstep (se 1 (by rfl) ⟨1373183, by rfl⟩ : syracuseStep 1830911 = 2746367) B2746367
theorem B6173495 : Blo 1219427 6173495 := bstep (se 1 (by rfl) ⟨4630121, by rfl⟩ : syracuseStep 6173495 = 9260243) B9260243
theorem B4396153 : Blo 1219427 4396153 := bstep (se 2 (by rfl) ⟨1648557, by rfl⟩ : syracuseStep 4396153 = 3297115) B3297115
theorem B9526139 : Blo 1219427 9526139 := bstep (se 1 (by rfl) ⟨7144604, by rfl⟩ : syracuseStep 9526139 = 14289209) B14289209
theorem B2743991 : Blo 1219427 2743991 := bstep (se 1 (by rfl) ⟨2057993, by rfl⟩ : syracuseStep 2743991 = 4115987) B4115987
theorem B30900367 : Blo 1219427 30900367 := bstep (se 1 (by rfl) ⟨23175275, by rfl⟩ : syracuseStep 30900367 = 46350551) B46350551
theorem B11436491 : Blo 1219427 11436491 := bstep (se 1 (by rfl) ⟨8577368, by rfl⟩ : syracuseStep 11436491 = 17154737) B17154737
theorem B79168103 : Blo 1219427 79168103 := bstep (se 1 (by rfl) ⟨59376077, by rfl⟩ : syracuseStep 79168103 = 118752155) B118752155
theorem B6350759 : Blo 1219427 6350759 := bstep (se 1 (by rfl) ⟨4763069, by rfl⟩ : syracuseStep 6350759 = 9526139) B9526139
theorem B2746745 : Blo 1219427 2746745 := bstep (se 2 (by rfl) ⟨1030029, by rfl⟩ : syracuseStep 2746745 = 2060059) B2060059
theorem B1829327 : Blo 1219427 1829327 := bstep (se 1 (by rfl) ⟨1371995, by rfl⟩ : syracuseStep 1829327 = 2743991) B2743991
theorem B4115663 : Blo 1219427 4115663 := bstep (se 1 (by rfl) ⟨3086747, by rfl⟩ : syracuseStep 4115663 = 6173495) B6173495
theorem B5861537 : Blo 1219427 5861537 := bstep (se 2 (by rfl) ⟨2198076, by rfl⟩ : syracuseStep 5861537 = 4396153) B4396153
theorem B1220607 : Blo 1219427 1220607 := bstep (se 1 (by rfl) ⟨915455, by rfl⟩ : syracuseStep 1220607 = 1830911) B1830911
theorem B3907691 : Blo 1219427 3907691 := bstep (se 1 (by rfl) ⟨2930768, by rfl⟩ : syracuseStep 3907691 = 5861537) B5861537
theorem B67741429 : Blo 1219427 67741429 := bstep (se 5 (by rfl) ⟨3175379, by rfl⟩ : syracuseStep 67741429 = 6350759) B6350759
theorem B41200489 : Blo 1219427 41200489 := bstep (se 2 (by rfl) ⟨15450183, by rfl⟩ : syracuseStep 41200489 = 30900367) B30900367
theorem B1831163 : Blo 1219427 1831163 := bstep (se 1 (by rfl) ⟨1373372, by rfl⟩ : syracuseStep 1831163 = 2746745) B2746745
theorem B7624327 : Blo 1219427 7624327 := bstep (se 1 (by rfl) ⟨5718245, by rfl⟩ : syracuseStep 7624327 = 11436491) B11436491
theorem B52778735 : Blo 1219427 52778735 := bstep (se 1 (by rfl) ⟨39584051, by rfl⟩ : syracuseStep 52778735 = 79168103) B79168103
theorem B1219551 : Blo 1219427 1219551 := bstep (se 1 (by rfl) ⟨914663, by rfl⟩ : syracuseStep 1219551 = 1829327) B1829327
theorem B2743775 : Blo 1219427 2743775 := bstep (se 1 (by rfl) ⟨2057831, by rfl⟩ : syracuseStep 2743775 = 4115663) B4115663
theorem B2605127 : Blo 1219427 2605127 := bstep (se 1 (by rfl) ⟨1953845, by rfl⟩ : syracuseStep 2605127 = 3907691) B3907691
theorem B1220775 : Blo 1219427 1220775 := bstep (se 1 (by rfl) ⟨915581, by rfl⟩ : syracuseStep 1220775 = 1831163) B1831163
theorem B35185823 : Blo 1219427 35185823 := bstep (se 1 (by rfl) ⟨26389367, by rfl⟩ : syracuseStep 35185823 = 52778735) B52778735
theorem B1829183 : Blo 1219427 1829183 := bstep (se 1 (by rfl) ⟨1371887, by rfl⟩ : syracuseStep 1829183 = 2743775) B2743775
theorem B90321905 : Blo 1219427 90321905 := bstep (se 2 (by rfl) ⟨33870714, by rfl⟩ : syracuseStep 90321905 = 67741429) B67741429
theorem B54933985 : Blo 1219427 54933985 := bstep (se 2 (by rfl) ⟨20600244, by rfl⟩ : syracuseStep 54933985 = 41200489) B41200489
theorem B10165769 : Blo 1219427 10165769 := bstep (se 2 (by rfl) ⟨3812163, by rfl⟩ : syracuseStep 10165769 = 7624327) B7624327
theorem B6947005 : Blo 1219427 6947005 := bstep (se 3 (by rfl) ⟨1302563, by rfl⟩ : syracuseStep 6947005 = 2605127) B2605127
theorem B73245313 : Blo 1219427 73245313 := bstep (se 2 (by rfl) ⟨27466992, by rfl⟩ : syracuseStep 73245313 = 54933985) B54933985
theorem B6777179 : Blo 1219427 6777179 := bstep (se 1 (by rfl) ⟨5082884, by rfl⟩ : syracuseStep 6777179 = 10165769) B10165769
theorem B60214603 : Blo 1219427 60214603 := bstep (se 1 (by rfl) ⟨45160952, by rfl⟩ : syracuseStep 60214603 = 90321905) B90321905
theorem B23457215 : Blo 1219427 23457215 := bstep (se 1 (by rfl) ⟨17592911, by rfl⟩ : syracuseStep 23457215 = 35185823) B35185823
theorem B1219455 : Blo 1219427 1219455 := bstep (se 1 (by rfl) ⟨914591, by rfl⟩ : syracuseStep 1219455 = 1829183) B1829183
theorem B97660417 : Blo 1219427 97660417 := bstep (se 2 (by rfl) ⟨36622656, by rfl⟩ : syracuseStep 97660417 = 73245313) B73245313
theorem B4518119 : Blo 1219427 4518119 := bstep (se 1 (by rfl) ⟨3388589, by rfl⟩ : syracuseStep 4518119 = 6777179) B6777179
theorem B80286137 : Blo 1219427 80286137 := bstep (se 2 (by rfl) ⟨30107301, by rfl⟩ : syracuseStep 80286137 = 60214603) B60214603
theorem B9262673 : Blo 1219427 9262673 := bstep (se 2 (by rfl) ⟨3473502, by rfl⟩ : syracuseStep 9262673 = 6947005) B6947005
theorem B15638143 : Blo 1219427 15638143 := bstep (se 1 (by rfl) ⟨11728607, by rfl⟩ : syracuseStep 15638143 = 23457215) B23457215
theorem B130213889 : Blo 1219427 130213889 := bstep (se 2 (by rfl) ⟨48830208, by rfl⟩ : syracuseStep 130213889 = 97660417) B97660417
theorem B20850857 : Blo 1219427 20850857 := bstep (se 2 (by rfl) ⟨7819071, by rfl⟩ : syracuseStep 20850857 = 15638143) B15638143
theorem B3012079 : Blo 1219427 3012079 := bstep (se 1 (by rfl) ⟨2259059, by rfl⟩ : syracuseStep 3012079 = 4518119) B4518119
theorem B53524091 : Blo 1219427 53524091 := bstep (se 1 (by rfl) ⟨40143068, by rfl⟩ : syracuseStep 53524091 = 80286137) B80286137
theorem B6175115 : Blo 1219427 6175115 := bstep (se 1 (by rfl) ⟨4631336, by rfl⟩ : syracuseStep 6175115 = 9262673) B9262673
theorem B4016105 : Blo 1219427 4016105 := bstep (se 2 (by rfl) ⟨1506039, by rfl⟩ : syracuseStep 4016105 = 3012079) B3012079
theorem B4116743 : Blo 1219427 4116743 := bstep (se 1 (by rfl) ⟨3087557, by rfl⟩ : syracuseStep 4116743 = 6175115) B6175115
theorem B35682727 : Blo 1219427 35682727 := bstep (se 1 (by rfl) ⟨26762045, by rfl⟩ : syracuseStep 35682727 = 53524091) B53524091
theorem B86809259 : Blo 1219427 86809259 := bstep (se 1 (by rfl) ⟨65106944, by rfl⟩ : syracuseStep 86809259 = 130213889) B130213889
theorem B13900571 : Blo 1219427 13900571 := bstep (se 1 (by rfl) ⟨10425428, by rfl⟩ : syracuseStep 13900571 = 20850857) B20850857
theorem B2744495 : Blo 1219427 2744495 := bstep (se 1 (by rfl) ⟨2058371, by rfl⟩ : syracuseStep 2744495 = 4116743) B4116743
theorem B9267047 : Blo 1219427 9267047 := bstep (se 1 (by rfl) ⟨6950285, by rfl⟩ : syracuseStep 9267047 = 13900571) B13900571
theorem B57872839 : Blo 1219427 57872839 := bstep (se 1 (by rfl) ⟨43404629, by rfl⟩ : syracuseStep 57872839 = 86809259) B86809259
theorem B47576969 : Blo 1219427 47576969 := bstep (se 2 (by rfl) ⟨17841363, by rfl⟩ : syracuseStep 47576969 = 35682727) B35682727
theorem B2677403 : Blo 1219427 2677403 := bstep (se 1 (by rfl) ⟨2008052, by rfl⟩ : syracuseStep 2677403 = 4016105) B4016105
theorem B6178031 : Blo 1219427 6178031 := bstep (se 1 (by rfl) ⟨4633523, by rfl⟩ : syracuseStep 6178031 = 9267047) B9267047
theorem B1829663 : Blo 1219427 1829663 := bstep (se 1 (by rfl) ⟨1372247, by rfl⟩ : syracuseStep 1829663 = 2744495) B2744495
theorem B77163785 : Blo 1219427 77163785 := bstep (se 2 (by rfl) ⟨28936419, by rfl⟩ : syracuseStep 77163785 = 57872839) B57872839
theorem B31717979 : Blo 1219427 31717979 := bstep (se 1 (by rfl) ⟨23788484, by rfl⟩ : syracuseStep 31717979 = 47576969) B47576969
theorem B1784935 : Blo 1219427 1784935 := bstep (se 1 (by rfl) ⟨1338701, by rfl⟩ : syracuseStep 1784935 = 2677403) B2677403
theorem B9519653 : Blo 1219427 9519653 := bstep (se 4 (by rfl) ⟨892467, by rfl⟩ : syracuseStep 9519653 = 1784935) B1784935
theorem B21145319 : Blo 1219427 21145319 := bstep (se 1 (by rfl) ⟨15858989, by rfl⟩ : syracuseStep 21145319 = 31717979) B31717979
theorem B51442523 : Blo 1219427 51442523 := bstep (se 1 (by rfl) ⟨38581892, by rfl⟩ : syracuseStep 51442523 = 77163785) B77163785
theorem B4118687 : Blo 1219427 4118687 := bstep (se 1 (by rfl) ⟨3089015, by rfl⟩ : syracuseStep 4118687 = 6178031) B6178031
theorem B1219775 : Blo 1219427 1219775 := bstep (se 1 (by rfl) ⟨914831, by rfl⟩ : syracuseStep 1219775 = 1829663) B1829663
theorem B2745791 : Blo 1219427 2745791 := bstep (se 1 (by rfl) ⟨2059343, by rfl⟩ : syracuseStep 2745791 = 4118687) B4118687
theorem B34295015 : Blo 1219427 34295015 := bstep (se 1 (by rfl) ⟨25721261, by rfl⟩ : syracuseStep 34295015 = 51442523) B51442523
theorem B6346435 : Blo 1219427 6346435 := bstep (se 1 (by rfl) ⟨4759826, by rfl⟩ : syracuseStep 6346435 = 9519653) B9519653
theorem B14096879 : Blo 1219427 14096879 := bstep (se 1 (by rfl) ⟨10572659, by rfl⟩ : syracuseStep 14096879 = 21145319) B21145319
theorem B9397919 : Blo 1219427 9397919 := bstep (se 1 (by rfl) ⟨7048439, by rfl⟩ : syracuseStep 9397919 = 14096879) B14096879
theorem B1830527 : Blo 1219427 1830527 := bstep (se 1 (by rfl) ⟨1372895, by rfl⟩ : syracuseStep 1830527 = 2745791) B2745791
theorem B22863343 : Blo 1219427 22863343 := bstep (se 1 (by rfl) ⟨17147507, by rfl⟩ : syracuseStep 22863343 = 34295015) B34295015
theorem B8461913 : Blo 1219427 8461913 := bstep (se 2 (by rfl) ⟨3173217, by rfl⟩ : syracuseStep 8461913 = 6346435) B6346435
theorem B30484457 : Blo 1219427 30484457 := bstep (se 2 (by rfl) ⟨11431671, by rfl⟩ : syracuseStep 30484457 = 22863343) B22863343
theorem B22565101 : Blo 1219427 22565101 := bstep (se 3 (by rfl) ⟨4230956, by rfl⟩ : syracuseStep 22565101 = 8461913) B8461913
theorem B6265279 : Blo 1219427 6265279 := bstep (se 1 (by rfl) ⟨4698959, by rfl⟩ : syracuseStep 6265279 = 9397919) B9397919
theorem B1220351 : Blo 1219427 1220351 := bstep (se 1 (by rfl) ⟨915263, by rfl⟩ : syracuseStep 1220351 = 1830527) B1830527
theorem B30086801 : Blo 1219427 30086801 := bstep (se 2 (by rfl) ⟨11282550, by rfl⟩ : syracuseStep 30086801 = 22565101) B22565101
theorem B8353705 : Blo 1219427 8353705 := bstep (se 2 (by rfl) ⟨3132639, by rfl⟩ : syracuseStep 8353705 = 6265279) B6265279
theorem B20322971 : Blo 1219427 20322971 := bstep (se 1 (by rfl) ⟨15242228, by rfl⟩ : syracuseStep 20322971 = 30484457) B30484457
theorem B20057867 : Blo 1219427 20057867 := bstep (se 1 (by rfl) ⟨15043400, by rfl⟩ : syracuseStep 20057867 = 30086801) B30086801
theorem B11138273 : Blo 1219427 11138273 := bstep (se 2 (by rfl) ⟨4176852, by rfl⟩ : syracuseStep 11138273 = 8353705) B8353705
theorem B13548647 : Blo 1219427 13548647 := bstep (se 1 (by rfl) ⟨10161485, by rfl⟩ : syracuseStep 13548647 = 20322971) B20322971
theorem B13371911 : Blo 1219427 13371911 := bstep (se 1 (by rfl) ⟨10028933, by rfl⟩ : syracuseStep 13371911 = 20057867) B20057867
theorem B36129725 : Blo 1219427 36129725 := bstep (se 3 (by rfl) ⟨6774323, by rfl⟩ : syracuseStep 36129725 = 13548647) B13548647
theorem B7425515 : Blo 1219427 7425515 := bstep (se 1 (by rfl) ⟨5569136, by rfl⟩ : syracuseStep 7425515 = 11138273) B11138273
theorem B8914607 : Blo 1219427 8914607 := bstep (se 1 (by rfl) ⟨6685955, by rfl⟩ : syracuseStep 8914607 = 13371911) B13371911
theorem B24086483 : Blo 1219427 24086483 := bstep (se 1 (by rfl) ⟨18064862, by rfl⟩ : syracuseStep 24086483 = 36129725) B36129725
theorem B4950343 : Blo 1219427 4950343 := bstep (se 1 (by rfl) ⟨3712757, by rfl⟩ : syracuseStep 4950343 = 7425515) B7425515
theorem B16057655 : Blo 1219427 16057655 := bstep (se 1 (by rfl) ⟨12043241, by rfl⟩ : syracuseStep 16057655 = 24086483) B24086483
theorem B5943071 : Blo 1219427 5943071 := bstep (se 1 (by rfl) ⟨4457303, by rfl⟩ : syracuseStep 5943071 = 8914607) B8914607
theorem B6600457 : Blo 1219427 6600457 := bstep (se 2 (by rfl) ⟨2475171, by rfl⟩ : syracuseStep 6600457 = 4950343) B4950343
theorem B8800609 : Blo 1219427 8800609 := bstep (se 2 (by rfl) ⟨3300228, by rfl⟩ : syracuseStep 8800609 = 6600457) B6600457
theorem B3962047 : Blo 1219427 3962047 := bstep (se 1 (by rfl) ⟨2971535, by rfl⟩ : syracuseStep 3962047 = 5943071) B5943071
theorem B10705103 : Blo 1219427 10705103 := bstep (se 1 (by rfl) ⟨8028827, by rfl⟩ : syracuseStep 10705103 = 16057655) B16057655
theorem B11734145 : Blo 1219427 11734145 := bstep (se 2 (by rfl) ⟨4400304, by rfl⟩ : syracuseStep 11734145 = 8800609) B8800609
theorem B5282729 : Blo 1219427 5282729 := bstep (se 2 (by rfl) ⟨1981023, by rfl⟩ : syracuseStep 5282729 = 3962047) B3962047
theorem B114187765 : Blo 1219427 114187765 := bstep (se 5 (by rfl) ⟨5352551, by rfl⟩ : syracuseStep 114187765 = 10705103) B10705103
theorem B152250353 : Blo 1219427 152250353 := bstep (se 2 (by rfl) ⟨57093882, by rfl⟩ : syracuseStep 152250353 = 114187765) B114187765
theorem B3521819 : Blo 1219427 3521819 := bstep (se 1 (by rfl) ⟨2641364, by rfl⟩ : syracuseStep 3521819 = 5282729) B5282729
theorem B7822763 : Blo 1219427 7822763 := bstep (se 1 (by rfl) ⟨5867072, by rfl⟩ : syracuseStep 7822763 = 11734145) B11734145
theorem B101500235 : Blo 1219427 101500235 := bstep (se 1 (by rfl) ⟨76125176, by rfl⟩ : syracuseStep 101500235 = 152250353) B152250353
theorem B2347879 : Blo 1219427 2347879 := bstep (se 1 (by rfl) ⟨1760909, by rfl⟩ : syracuseStep 2347879 = 3521819) B3521819
theorem B5215175 : Blo 1219427 5215175 := bstep (se 1 (by rfl) ⟨3911381, by rfl⟩ : syracuseStep 5215175 = 7822763) B7822763
theorem B67666823 : Blo 1219427 67666823 := bstep (se 1 (by rfl) ⟨50750117, by rfl⟩ : syracuseStep 67666823 = 101500235) B101500235
theorem B3130505 : Blo 1219427 3130505 := bstep (se 2 (by rfl) ⟨1173939, by rfl⟩ : syracuseStep 3130505 = 2347879) B2347879
theorem B3476783 : Blo 1219427 3476783 := bstep (se 1 (by rfl) ⟨2607587, by rfl⟩ : syracuseStep 3476783 = 5215175) B5215175
theorem B45111215 : Blo 1219427 45111215 := bstep (se 1 (by rfl) ⟨33833411, by rfl⟩ : syracuseStep 45111215 = 67666823) B67666823
theorem B2087003 : Blo 1219427 2087003 := bstep (se 1 (by rfl) ⟨1565252, by rfl⟩ : syracuseStep 2087003 = 3130505) B3130505
theorem B9271421 : Blo 1219427 9271421 := bstep (se 3 (by rfl) ⟨1738391, by rfl⟩ : syracuseStep 9271421 = 3476783) B3476783
theorem B5565341 : Blo 1219427 5565341 := bstep (se 3 (by rfl) ⟨1043501, by rfl⟩ : syracuseStep 5565341 = 2087003) B2087003
theorem B6180947 : Blo 1219427 6180947 := bstep (se 1 (by rfl) ⟨4635710, by rfl⟩ : syracuseStep 6180947 = 9271421) B9271421
theorem B120296573 : Blo 1219427 120296573 := bstep (se 3 (by rfl) ⟨22555607, by rfl⟩ : syracuseStep 120296573 = 45111215) B45111215
theorem B4120631 : Blo 1219427 4120631 := bstep (se 1 (by rfl) ⟨3090473, by rfl⟩ : syracuseStep 4120631 = 6180947) B6180947
theorem B80197715 : Blo 1219427 80197715 := bstep (se 1 (by rfl) ⟨60148286, by rfl⟩ : syracuseStep 80197715 = 120296573) B120296573
theorem B3710227 : Blo 1219427 3710227 := bstep (se 1 (by rfl) ⟨2782670, by rfl⟩ : syracuseStep 3710227 = 5565341) B5565341
theorem B2747087 : Blo 1219427 2747087 := bstep (se 1 (by rfl) ⟨2060315, by rfl⟩ : syracuseStep 2747087 = 4120631) B4120631
theorem B53465143 : Blo 1219427 53465143 := bstep (se 1 (by rfl) ⟨40098857, by rfl⟩ : syracuseStep 53465143 = 80197715) B80197715
theorem B4946969 : Blo 1219427 4946969 := bstep (se 2 (by rfl) ⟨1855113, by rfl⟩ : syracuseStep 4946969 = 3710227) B3710227
theorem B71286857 : Blo 1219427 71286857 := bstep (se 2 (by rfl) ⟨26732571, by rfl⟩ : syracuseStep 71286857 = 53465143) B53465143
theorem B1831391 : Blo 1219427 1831391 := bstep (se 1 (by rfl) ⟨1373543, by rfl⟩ : syracuseStep 1831391 = 2747087) B2747087
theorem B3297979 : Blo 1219427 3297979 := bstep (se 1 (by rfl) ⟨2473484, by rfl⟩ : syracuseStep 3297979 = 4946969) B4946969
theorem B1220927 : Blo 1219427 1220927 := bstep (se 1 (by rfl) ⟨915695, by rfl⟩ : syracuseStep 1220927 = 1831391) B1831391
theorem B17589221 : Blo 1219427 17589221 := bstep (se 4 (by rfl) ⟨1648989, by rfl⟩ : syracuseStep 17589221 = 3297979) B3297979
theorem B47524571 : Blo 1219427 47524571 := bstep (se 1 (by rfl) ⟨35643428, by rfl⟩ : syracuseStep 47524571 = 71286857) B71286857
theorem B11726147 : Blo 1219427 11726147 := bstep (se 1 (by rfl) ⟨8794610, by rfl⟩ : syracuseStep 11726147 = 17589221) B17589221
theorem B31683047 : Blo 1219427 31683047 := bstep (se 1 (by rfl) ⟨23762285, by rfl⟩ : syracuseStep 31683047 = 47524571) B47524571
theorem B31269725 : Blo 1219427 31269725 := bstep (se 3 (by rfl) ⟨5863073, by rfl⟩ : syracuseStep 31269725 = 11726147) B11726147
theorem B84488125 : Blo 1219427 84488125 := bstep (se 3 (by rfl) ⟨15841523, by rfl⟩ : syracuseStep 84488125 = 31683047) B31683047
theorem B112650833 : Blo 1219427 112650833 := bstep (se 2 (by rfl) ⟨42244062, by rfl⟩ : syracuseStep 112650833 = 84488125) B84488125
theorem B20846483 : Blo 1219427 20846483 := bstep (se 1 (by rfl) ⟨15634862, by rfl⟩ : syracuseStep 20846483 = 31269725) B31269725
theorem B13897655 : Blo 1219427 13897655 := bstep (se 1 (by rfl) ⟨10423241, by rfl⟩ : syracuseStep 13897655 = 20846483) B20846483
theorem B75100555 : Blo 1219427 75100555 := bstep (se 1 (by rfl) ⟨56325416, by rfl⟩ : syracuseStep 75100555 = 112650833) B112650833
theorem B100134073 : Blo 1219427 100134073 := bstep (se 2 (by rfl) ⟨37550277, by rfl⟩ : syracuseStep 100134073 = 75100555) B75100555
theorem B9265103 : Blo 1219427 9265103 := bstep (se 1 (by rfl) ⟨6948827, by rfl⟩ : syracuseStep 9265103 = 13897655) B13897655
theorem B133512097 : Blo 1219427 133512097 := bstep (se 2 (by rfl) ⟨50067036, by rfl⟩ : syracuseStep 133512097 = 100134073) B100134073
theorem B6176735 : Blo 1219427 6176735 := bstep (se 1 (by rfl) ⟨4632551, by rfl⟩ : syracuseStep 6176735 = 9265103) B9265103
theorem B178016129 : Blo 1219427 178016129 := bstep (se 2 (by rfl) ⟨66756048, by rfl⟩ : syracuseStep 178016129 = 133512097) B133512097
theorem B4117823 : Blo 1219427 4117823 := bstep (se 1 (by rfl) ⟨3088367, by rfl⟩ : syracuseStep 4117823 = 6176735) B6176735
theorem B2745215 : Blo 1219427 2745215 := bstep (se 1 (by rfl) ⟨2058911, by rfl⟩ : syracuseStep 2745215 = 4117823) B4117823
theorem B118677419 : Blo 1219427 118677419 := bstep (se 1 (by rfl) ⟨89008064, by rfl⟩ : syracuseStep 118677419 = 178016129) B178016129
theorem B1830143 : Blo 1219427 1830143 := bstep (se 1 (by rfl) ⟨1372607, by rfl⟩ : syracuseStep 1830143 = 2745215) B2745215
theorem B79118279 : Blo 1219427 79118279 := bstep (se 1 (by rfl) ⟨59338709, by rfl⟩ : syracuseStep 79118279 = 118677419) B118677419
theorem B52745519 : Blo 1219427 52745519 := bstep (se 1 (by rfl) ⟨39559139, by rfl⟩ : syracuseStep 52745519 = 79118279) B79118279
theorem B1220095 : Blo 1219427 1220095 := bstep (se 1 (by rfl) ⟨915071, by rfl⟩ : syracuseStep 1220095 = 1830143) B1830143
theorem B35163679 : Blo 1219427 35163679 := bstep (se 1 (by rfl) ⟨26372759, by rfl⟩ : syracuseStep 35163679 = 52745519) B52745519
theorem B46884905 : Blo 1219427 46884905 := bstep (se 2 (by rfl) ⟨17581839, by rfl⟩ : syracuseStep 46884905 = 35163679) B35163679
theorem B31256603 : Blo 1219427 31256603 := bstep (se 1 (by rfl) ⟨23442452, by rfl⟩ : syracuseStep 31256603 = 46884905) B46884905
theorem B20837735 : Blo 1219427 20837735 := bstep (se 1 (by rfl) ⟨15628301, by rfl⟩ : syracuseStep 20837735 = 31256603) B31256603
theorem B13891823 : Blo 1219427 13891823 := bstep (se 1 (by rfl) ⟨10418867, by rfl⟩ : syracuseStep 13891823 = 20837735) B20837735
theorem B9261215 : Blo 1219427 9261215 := bstep (se 1 (by rfl) ⟨6945911, by rfl⟩ : syracuseStep 9261215 = 13891823) B13891823
theorem B6174143 : Blo 1219427 6174143 := bstep (se 1 (by rfl) ⟨4630607, by rfl⟩ : syracuseStep 6174143 = 9261215) B9261215
theorem B4116095 : Blo 1219427 4116095 := bstep (se 1 (by rfl) ⟨3087071, by rfl⟩ : syracuseStep 4116095 = 6174143) B6174143
theorem B2744063 : Blo 1219427 2744063 := bstep (se 1 (by rfl) ⟨2058047, by rfl⟩ : syracuseStep 2744063 = 4116095) B4116095
theorem B1829375 : Blo 1219427 1829375 := bstep (se 1 (by rfl) ⟨1372031, by rfl⟩ : syracuseStep 1829375 = 2744063) B2744063
theorem B1219583 : Blo 1219427 1219583 := bstep (se 1 (by rfl) ⟨914687, by rfl⟩ : syracuseStep 1219583 = 1829375) B1829375

theorem C0 (j : ℕ) (h1 : 304856 ≤ j) (h2 : j ≤ 305231) : Blo 1219427 (4 * j + 3) := by
  interval_cases j
  · exact B1219427
  · exact B1219431
  · exact B1219435
  · exact B1219439
  · exact B1219443
  · exact B1219447
  · exact B1219451
  · exact B1219455
  · exact B1219459
  · exact B1219463
  · exact B1219467
  · exact B1219471
  · exact B1219475
  · exact B1219479
  · exact B1219483
  · exact B1219487
  · exact B1219491
  · exact B1219495
  · exact B1219499
  · exact B1219503
  · exact B1219507
  · exact B1219511
  · exact B1219515
  · exact B1219519
  · exact B1219523
  · exact B1219527
  · exact B1219531
  · exact B1219535
  · exact B1219539
  · exact B1219543
  · exact B1219547
  · exact B1219551
  · exact B1219555
  · exact B1219559
  · exact B1219563
  · exact B1219567
  · exact B1219571
  · exact B1219575
  · exact B1219579
  · exact B1219583
  · exact B1219587
  · exact B1219591
  · exact B1219595
  · exact B1219599
  · exact B1219603
  · exact B1219607
  · exact B1219611
  · exact B1219615
  · exact B1219619
  · exact B1219623
  · exact B1219627
  · exact B1219631
  · exact B1219635
  · exact B1219639
  · exact B1219643
  · exact B1219647
  · exact B1219651
  · exact B1219655
  · exact B1219659
  · exact B1219663
  · exact B1219667
  · exact B1219671
  · exact B1219675
  · exact B1219679
  · exact B1219683
  · exact B1219687
  · exact B1219691
  · exact B1219695
  · exact B1219699
  · exact B1219703
  · exact B1219707
  · exact B1219711
  · exact B1219715
  · exact B1219719
  · exact B1219723
  · exact B1219727
  · exact B1219731
  · exact B1219735
  · exact B1219739
  · exact B1219743
  · exact B1219747
  · exact B1219751
  · exact B1219755
  · exact B1219759
  · exact B1219763
  · exact B1219767
  · exact B1219771
  · exact B1219775
  · exact B1219779
  · exact B1219783
  · exact B1219787
  · exact B1219791
  · exact B1219795
  · exact B1219799
  · exact B1219803
  · exact B1219807
  · exact B1219811
  · exact B1219815
  · exact B1219819
  · exact B1219823
  · exact B1219827
  · exact B1219831
  · exact B1219835
  · exact B1219839
  · exact B1219843
  · exact B1219847
  · exact B1219851
  · exact B1219855
  · exact B1219859
  · exact B1219863
  · exact B1219867
  · exact B1219871
  · exact B1219875
  · exact B1219879
  · exact B1219883
  · exact B1219887
  · exact B1219891
  · exact B1219895
  · exact B1219899
  · exact B1219903
  · exact B1219907
  · exact B1219911
  · exact B1219915
  · exact B1219919
  · exact B1219923
  · exact B1219927
  · exact B1219931
  · exact B1219935
  · exact B1219939
  · exact B1219943
  · exact B1219947
  · exact B1219951
  · exact B1219955
  · exact B1219959
  · exact B1219963
  · exact B1219967
  · exact B1219971
  · exact B1219975
  · exact B1219979
  · exact B1219983
  · exact B1219987
  · exact B1219991
  · exact B1219995
  · exact B1219999
  · exact B1220003
  · exact B1220007
  · exact B1220011
  · exact B1220015
  · exact B1220019
  · exact B1220023
  · exact B1220027
  · exact B1220031
  · exact B1220035
  · exact B1220039
  · exact B1220043
  · exact B1220047
  · exact B1220051
  · exact B1220055
  · exact B1220059
  · exact B1220063
  · exact B1220067
  · exact B1220071
  · exact B1220075
  · exact B1220079
  · exact B1220083
  · exact B1220087
  · exact B1220091
  · exact B1220095
  · exact B1220099
  · exact B1220103
  · exact B1220107
  · exact B1220111
  · exact B1220115
  · exact B1220119
  · exact B1220123
  · exact B1220127
  · exact B1220131
  · exact B1220135
  · exact B1220139
  · exact B1220143
  · exact B1220147
  · exact B1220151
  · exact B1220155
  · exact B1220159
  · exact B1220163
  · exact B1220167
  · exact B1220171
  · exact B1220175
  · exact B1220179
  · exact B1220183
  · exact B1220187
  · exact B1220191
  · exact B1220195
  · exact B1220199
  · exact B1220203
  · exact B1220207
  · exact B1220211
  · exact B1220215
  · exact B1220219
  · exact B1220223
  · exact B1220227
  · exact B1220231
  · exact B1220235
  · exact B1220239
  · exact B1220243
  · exact B1220247
  · exact B1220251
  · exact B1220255
  · exact B1220259
  · exact B1220263
  · exact B1220267
  · exact B1220271
  · exact B1220275
  · exact B1220279
  · exact B1220283
  · exact B1220287
  · exact B1220291
  · exact B1220295
  · exact B1220299
  · exact B1220303
  · exact B1220307
  · exact B1220311
  · exact B1220315
  · exact B1220319
  · exact B1220323
  · exact B1220327
  · exact B1220331
  · exact B1220335
  · exact B1220339
  · exact B1220343
  · exact B1220347
  · exact B1220351
  · exact B1220355
  · exact B1220359
  · exact B1220363
  · exact B1220367
  · exact B1220371
  · exact B1220375
  · exact B1220379
  · exact B1220383
  · exact B1220387
  · exact B1220391
  · exact B1220395
  · exact B1220399
  · exact B1220403
  · exact B1220407
  · exact B1220411
  · exact B1220415
  · exact B1220419
  · exact B1220423
  · exact B1220427
  · exact B1220431
  · exact B1220435
  · exact B1220439
  · exact B1220443
  · exact B1220447
  · exact B1220451
  · exact B1220455
  · exact B1220459
  · exact B1220463
  · exact B1220467
  · exact B1220471
  · exact B1220475
  · exact B1220479
  · exact B1220483
  · exact B1220487
  · exact B1220491
  · exact B1220495
  · exact B1220499
  · exact B1220503
  · exact B1220507
  · exact B1220511
  · exact B1220515
  · exact B1220519
  · exact B1220523
  · exact B1220527
  · exact B1220531
  · exact B1220535
  · exact B1220539
  · exact B1220543
  · exact B1220547
  · exact B1220551
  · exact B1220555
  · exact B1220559
  · exact B1220563
  · exact B1220567
  · exact B1220571
  · exact B1220575
  · exact B1220579
  · exact B1220583
  · exact B1220587
  · exact B1220591
  · exact B1220595
  · exact B1220599
  · exact B1220603
  · exact B1220607
  · exact B1220611
  · exact B1220615
  · exact B1220619
  · exact B1220623
  · exact B1220627
  · exact B1220631
  · exact B1220635
  · exact B1220639
  · exact B1220643
  · exact B1220647
  · exact B1220651
  · exact B1220655
  · exact B1220659
  · exact B1220663
  · exact B1220667
  · exact B1220671
  · exact B1220675
  · exact B1220679
  · exact B1220683
  · exact B1220687
  · exact B1220691
  · exact B1220695
  · exact B1220699
  · exact B1220703
  · exact B1220707
  · exact B1220711
  · exact B1220715
  · exact B1220719
  · exact B1220723
  · exact B1220727
  · exact B1220731
  · exact B1220735
  · exact B1220739
  · exact B1220743
  · exact B1220747
  · exact B1220751
  · exact B1220755
  · exact B1220759
  · exact B1220763
  · exact B1220767
  · exact B1220771
  · exact B1220775
  · exact B1220779
  · exact B1220783
  · exact B1220787
  · exact B1220791
  · exact B1220795
  · exact B1220799
  · exact B1220803
  · exact B1220807
  · exact B1220811
  · exact B1220815
  · exact B1220819
  · exact B1220823
  · exact B1220827
  · exact B1220831
  · exact B1220835
  · exact B1220839
  · exact B1220843
  · exact B1220847
  · exact B1220851
  · exact B1220855
  · exact B1220859
  · exact B1220863
  · exact B1220867
  · exact B1220871
  · exact B1220875
  · exact B1220879
  · exact B1220883
  · exact B1220887
  · exact B1220891
  · exact B1220895
  · exact B1220899
  · exact B1220903
  · exact B1220907
  · exact B1220911
  · exact B1220915
  · exact B1220919
  · exact B1220923
  · exact B1220927

theorem solution (m : ℕ) (hlo : 1219427 ≤ m) (hhi : m ≤ 1220927) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 304856 ≤ j := by omega
    have hj2 : j ≤ 305231 := by omega
    have hb : Blo 1219427 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
