-- Prove2me | solution 1 for syracuse_descends_range_1372005_1374005
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:12.878246+00:00
-- url     : https://prove2.me/submissions/eae2be45-4fa3-4c9b-967c-4720031e0050

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


theorem B2318341 : Blo 1372005 2318341 := bbase (se 4 (by rfl) ⟨217344, by rfl⟩ : syracuseStep 2318341 = 434689) (by norm_num)
theorem B1736741 : Blo 1372005 1736741 := bbase (se 4 (by rfl) ⟨162819, by rfl⟩ : syracuseStep 1736741 = 325639) (by norm_num)
theorem B3088421 : Blo 1372005 3088421 := bbase (se 4 (by rfl) ⟨289539, by rfl⟩ : syracuseStep 3088421 = 579079) (by norm_num)
theorem B4636709 : Blo 1372005 4636709 := bbase (se 4 (by rfl) ⟨434691, by rfl⟩ : syracuseStep 4636709 = 869383) (by norm_num)
theorem B4948037 : Blo 1372005 4948037 := bbase (se 4 (by rfl) ⟨463878, by rfl⟩ : syracuseStep 4948037 = 927757) (by norm_num)
theorem B1736797 : Blo 1372005 1736797 := bbase (se 3 (by rfl) ⟨325649, by rfl⟩ : syracuseStep 1736797 = 651299) (by norm_num)
theorem B1466461 : Blo 1372005 1466461 := bbase (se 3 (by rfl) ⟨274961, by rfl⟩ : syracuseStep 1466461 = 549923) (by norm_num)
theorem B2318429 : Blo 1372005 2318429 := bbase (se 3 (by rfl) ⟨434705, by rfl⟩ : syracuseStep 2318429 = 869411) (by norm_num)
theorem B3088493 : Blo 1372005 3088493 := bbase (se 3 (by rfl) ⟨579092, by rfl⟩ : syracuseStep 3088493 = 1158185) (by norm_num)
theorem B3088565 : Blo 1372005 3088565 := bbase (se 5 (by rfl) ⟨144776, by rfl⟩ : syracuseStep 3088565 = 289553) (by norm_num)
theorem B1736893 : Blo 1372005 1736893 := bbase (se 3 (by rfl) ⟨325667, by rfl⟩ : syracuseStep 1736893 = 651335) (by norm_num)
theorem B2318557 : Blo 1372005 2318557 := bbase (se 3 (by rfl) ⟨434729, by rfl⟩ : syracuseStep 2318557 = 869459) (by norm_num)
theorem B6947045 : Blo 1372005 6947045 := bbase (se 4 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 6947045 = 1302571) (by norm_num)
theorem B5570789 : Blo 1372005 5570789 := bbase (se 4 (by rfl) ⟨522261, by rfl⟩ : syracuseStep 5570789 = 1044523) (by norm_num)
theorem B3088637 : Blo 1372005 3088637 := bbase (se 3 (by rfl) ⟨579119, by rfl⟩ : syracuseStep 3088637 = 1158239) (by norm_num)
theorem B6521093 : Blo 1372005 6521093 := bbase (se 4 (by rfl) ⟨611352, by rfl⟩ : syracuseStep 6521093 = 1222705) (by norm_num)
theorem B3473725 : Blo 1372005 3473725 := bbase (se 3 (by rfl) ⟨651323, by rfl⟩ : syracuseStep 3473725 = 1302647) (by norm_num)
theorem B3088709 : Blo 1372005 3088709 := bbase (se 4 (by rfl) ⟨289566, by rfl⟩ : syracuseStep 3088709 = 579133) (by norm_num)
theorem B1810765 : Blo 1372005 1810765 := bbase (se 3 (by rfl) ⟨339518, by rfl⟩ : syracuseStep 1810765 = 679037) (by norm_num)
theorem B1737065 : Blo 1372005 1737065 := bbase (se 2 (by rfl) ⟨651399, by rfl⟩ : syracuseStep 1737065 = 1302799) (by norm_num)
theorem B2933101 : Blo 1372005 2933101 := bbase (se 3 (by rfl) ⟨549956, by rfl⟩ : syracuseStep 2933101 = 1099913) (by norm_num)
theorem B3088781 : Blo 1372005 3088781 := bbase (se 3 (by rfl) ⟨579146, by rfl⟩ : syracuseStep 3088781 = 1158293) (by norm_num)
theorem B1737121 : Blo 1372005 1737121 := bbase (se 2 (by rfl) ⟨651420, by rfl⟩ : syracuseStep 1737121 = 1302841) (by norm_num)
theorem B3473837 : Blo 1372005 3473837 := bbase (se 3 (by rfl) ⟨651344, by rfl⟩ : syracuseStep 3473837 = 1302689) (by norm_num)
theorem B4456885 : Blo 1372005 4456885 := bbase (se 5 (by rfl) ⟨208916, by rfl⟩ : syracuseStep 4456885 = 417833) (by norm_num)
theorem B3088853 : Blo 1372005 3088853 := bbase (se 7 (by rfl) ⟨36197, by rfl⟩ : syracuseStep 3088853 = 72395) (by norm_num)
theorem B4637141 : Blo 1372005 4637141 := bbase (se 7 (by rfl) ⟨54341, by rfl⟩ : syracuseStep 4637141 = 108683) (by norm_num)
theorem B1737217 : Blo 1372005 1737217 := bbase (se 2 (by rfl) ⟨651456, by rfl⟩ : syracuseStep 1737217 = 1302913) (by norm_num)
theorem B3908101 : Blo 1372005 3908101 := bbase (se 4 (by rfl) ⟨366384, by rfl⟩ : syracuseStep 3908101 = 732769) (by norm_num)
theorem B1466905 : Blo 1372005 1466905 := bbase (se 2 (by rfl) ⟨550089, by rfl⟩ : syracuseStep 1466905 = 1100179) (by norm_num)
theorem B3088925 : Blo 1372005 3088925 := bbase (se 3 (by rfl) ⟨579173, by rfl⟩ : syracuseStep 3088925 = 1158347) (by norm_num)
theorem B2605621 : Blo 1372005 2605621 := bbase (se 5 (by rfl) ⟨122138, by rfl⟩ : syracuseStep 2605621 = 244277) (by norm_num)
theorem B21144149 : Blo 1372005 21144149 := bbase (se 8 (by rfl) ⟨123891, by rfl⟩ : syracuseStep 21144149 = 247783) (by norm_num)
theorem B3088997 : Blo 1372005 3088997 := bbase (se 4 (by rfl) ⟨289593, by rfl⟩ : syracuseStep 3088997 = 579187) (by norm_num)
theorem B3474029 : Blo 1372005 3474029 := bbase (se 3 (by rfl) ⟨651380, by rfl⟩ : syracuseStep 3474029 = 1302761) (by norm_num)
theorem B11723413 : Blo 1372005 11723413 := bbase (se 6 (by rfl) ⟨274767, by rfl⟩ : syracuseStep 11723413 = 549535) (by norm_num)
theorem B1467029 : Blo 1372005 1467029 := bbase (se 6 (by rfl) ⟨34383, by rfl⟩ : syracuseStep 1467029 = 68767) (by norm_num)
theorem B1737389 : Blo 1372005 1737389 := bbase (se 3 (by rfl) ⟨325760, by rfl⟩ : syracuseStep 1737389 = 651521) (by norm_num)
theorem B3089069 : Blo 1372005 3089069 := bbase (se 3 (by rfl) ⟨579200, by rfl⟩ : syracuseStep 3089069 = 1158401) (by norm_num)
theorem B2605765 : Blo 1372005 2605765 := bbase (se 4 (by rfl) ⟨244290, by rfl⟩ : syracuseStep 2605765 = 488581) (by norm_num)
theorem B1737445 : Blo 1372005 1737445 := bbase (se 4 (by rfl) ⟨162885, by rfl⟩ : syracuseStep 1737445 = 325771) (by norm_num)
theorem B2474725 : Blo 1372005 2474725 := bbase (se 4 (by rfl) ⟨232005, by rfl⟩ : syracuseStep 2474725 = 464011) (by norm_num)
theorem B3089141 : Blo 1372005 3089141 := bbase (se 5 (by rfl) ⟨144803, by rfl⟩ : syracuseStep 3089141 = 289607) (by norm_num)
theorem B6259477 : Blo 1372005 6259477 := bbase (se 6 (by rfl) ⟨146706, by rfl⟩ : syracuseStep 6259477 = 293413) (by norm_num)
theorem B3089213 : Blo 1372005 3089213 := bbase (se 3 (by rfl) ⟨579227, by rfl⟩ : syracuseStep 3089213 = 1158455) (by norm_num)
theorem B1409857 : Blo 1372005 1409857 := bbase (se 2 (by rfl) ⟨528696, by rfl⟩ : syracuseStep 1409857 = 1057393) (by norm_num)
theorem B1737541 : Blo 1372005 1737541 := bbase (se 4 (by rfl) ⟨162894, by rfl⟩ : syracuseStep 1737541 = 325789) (by norm_num)
theorem B2605925 : Blo 1372005 2605925 := bbase (se 4 (by rfl) ⟨244305, by rfl⟩ : syracuseStep 2605925 = 488611) (by norm_num)
theorem B2474869 : Blo 1372005 2474869 := bbase (se 5 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 2474869 = 232019) (by norm_num)
theorem B5211013 : Blo 1372005 5211013 := bbase (se 4 (by rfl) ⟨488532, by rfl⟩ : syracuseStep 5211013 = 977065) (by norm_num)
theorem B3089285 : Blo 1372005 3089285 := bbase (se 4 (by rfl) ⟨289620, by rfl⟩ : syracuseStep 3089285 = 579241) (by norm_num)
theorem B3474373 : Blo 1372005 3474373 := bbase (se 4 (by rfl) ⟨325722, by rfl⟩ : syracuseStep 3474373 = 651445) (by norm_num)
theorem B3089357 : Blo 1372005 3089357 := bbase (se 3 (by rfl) ⟨579254, by rfl⟩ : syracuseStep 3089357 = 1158509) (by norm_num)
theorem B1737713 : Blo 1372005 1737713 := bbase (se 2 (by rfl) ⟨651642, by rfl⟩ : syracuseStep 1737713 = 1303285) (by norm_num)
theorem B2606069 : Blo 1372005 2606069 := bbase (se 5 (by rfl) ⟨122159, by rfl⟩ : syracuseStep 2606069 = 244319) (by norm_num)
theorem B3343357 : Blo 1372005 3343357 := bbase (se 3 (by rfl) ⟨626879, by rfl⟩ : syracuseStep 3343357 = 1253759) (by norm_num)
theorem B2507789 : Blo 1372005 2507789 := bbase (se 3 (by rfl) ⟨470210, by rfl⟩ : syracuseStep 2507789 = 940421) (by norm_num)
theorem B3089429 : Blo 1372005 3089429 := bbase (se 6 (by rfl) ⟨72408, by rfl⟩ : syracuseStep 3089429 = 144817) (by norm_num)
theorem B1737769 : Blo 1372005 1737769 := bbase (se 2 (by rfl) ⟨651663, by rfl⟩ : syracuseStep 1737769 = 1303327) (by norm_num)
theorem B3474485 : Blo 1372005 3474485 := bbase (se 5 (by rfl) ⟨162866, by rfl⟩ : syracuseStep 3474485 = 325733) (by norm_num)
theorem B3343445 : Blo 1372005 3343445 := bbase (se 8 (by rfl) ⟨19590, by rfl⟩ : syracuseStep 3343445 = 39181) (by norm_num)
theorem B3089501 : Blo 1372005 3089501 := bbase (se 3 (by rfl) ⟨579281, by rfl⟩ : syracuseStep 3089501 = 1158563) (by norm_num)
theorem B5866613 : Blo 1372005 5866613 := bbase (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) (by norm_num)
theorem B1737865 : Blo 1372005 1737865 := bbase (se 2 (by rfl) ⟨651699, by rfl⟩ : syracuseStep 1737865 = 1303399) (by norm_num)
theorem B3089573 : Blo 1372005 3089573 := bbase (se 4 (by rfl) ⟨289647, by rfl⟩ : syracuseStep 3089573 = 579295) (by norm_num)
theorem B5211317 : Blo 1372005 5211317 := bbase (se 5 (by rfl) ⟨244280, by rfl⟩ : syracuseStep 5211317 = 488561) (by norm_num)
theorem B3130597 : Blo 1372005 3130597 := bbase (se 4 (by rfl) ⟨293493, by rfl⟩ : syracuseStep 3130597 = 586987) (by norm_num)
theorem B3089645 : Blo 1372005 3089645 := bbase (se 3 (by rfl) ⟨579308, by rfl⟩ : syracuseStep 3089645 = 1158617) (by norm_num)
theorem B3474677 : Blo 1372005 3474677 := bbase (se 5 (by rfl) ⟨162875, by rfl⟩ : syracuseStep 3474677 = 325751) (by norm_num)
theorem B2606357 : Blo 1372005 2606357 := bbase (se 6 (by rfl) ⟨61086, by rfl⟩ : syracuseStep 2606357 = 122173) (by norm_num)
theorem B3089717 : Blo 1372005 3089717 := bbase (se 5 (by rfl) ⟨144830, by rfl⟩ : syracuseStep 3089717 = 289661) (by norm_num)
theorem B1738037 : Blo 1372005 1738037 := bbase (se 5 (by rfl) ⟨81470, by rfl⟩ : syracuseStep 1738037 = 162941) (by norm_num)
theorem B1738093 : Blo 1372005 1738093 := bbase (se 3 (by rfl) ⟨325892, by rfl⟩ : syracuseStep 1738093 = 651785) (by norm_num)
theorem B3089789 : Blo 1372005 3089789 := bbase (se 3 (by rfl) ⟨579335, by rfl⟩ : syracuseStep 3089789 = 1158671) (by norm_num)
theorem B23782805 : Blo 1372005 23782805 := bbase (se 6 (by rfl) ⟨557409, by rfl⟩ : syracuseStep 23782805 = 1114819) (by norm_num)
theorem B5866901 : Blo 1372005 5866901 := bbase (se 6 (by rfl) ⟨137505, by rfl⟩ : syracuseStep 5866901 = 275011) (by norm_num)
theorem B2606509 : Blo 1372005 2606509 := bbase (se 3 (by rfl) ⟨488720, by rfl⟩ : syracuseStep 2606509 = 977441) (by norm_num)
theorem B2475445 : Blo 1372005 2475445 := bbase (se 5 (by rfl) ⟨116036, by rfl⟩ : syracuseStep 2475445 = 232073) (by norm_num)
theorem B3089861 : Blo 1372005 3089861 := bbase (se 4 (by rfl) ⟨289674, by rfl⟩ : syracuseStep 3089861 = 579349) (by norm_num)
theorem B1738189 : Blo 1372005 1738189 := bbase (se 3 (by rfl) ⟨325910, by rfl⟩ : syracuseStep 1738189 = 651821) (by norm_num)
theorem B6948341 : Blo 1372005 6948341 := bbase (se 5 (by rfl) ⟨325703, by rfl⟩ : syracuseStep 6948341 = 651407) (by norm_num)
theorem B3089933 : Blo 1372005 3089933 := bbase (se 3 (by rfl) ⟨579362, by rfl⟩ : syracuseStep 3089933 = 1158725) (by norm_num)
theorem B3475021 : Blo 1372005 3475021 := bbase (se 3 (by rfl) ⟨651566, by rfl⟩ : syracuseStep 3475021 = 1303133) (by norm_num)
theorem B3090005 : Blo 1372005 3090005 := bbase (se 8 (by rfl) ⟨18105, by rfl⟩ : syracuseStep 3090005 = 36211) (by norm_num)
theorem B1738361 : Blo 1372005 1738361 := bbase (se 2 (by rfl) ⟨651885, by rfl⟩ : syracuseStep 1738361 = 1303771) (by norm_num)
theorem B1672849 : Blo 1372005 1672849 := bbase (se 2 (by rfl) ⟨627318, by rfl⟩ : syracuseStep 1672849 = 1254637) (by norm_num)
theorem B3090077 : Blo 1372005 3090077 := bbase (se 3 (by rfl) ⟨579389, by rfl⟩ : syracuseStep 3090077 = 1158779) (by norm_num)
theorem B1738417 : Blo 1372005 1738417 := bbase (se 2 (by rfl) ⟨651906, by rfl⟩ : syracuseStep 1738417 = 1303813) (by norm_num)
theorem B3475133 : Blo 1372005 3475133 := bbase (se 3 (by rfl) ⟨651587, by rfl⟩ : syracuseStep 3475133 = 1303175) (by norm_num)
theorem B3262141 : Blo 1372005 3262141 := bbase (se 3 (by rfl) ⟨611651, by rfl⟩ : syracuseStep 3262141 = 1223303) (by norm_num)
theorem B2606813 : Blo 1372005 2606813 := bbase (se 3 (by rfl) ⟨488777, by rfl⟩ : syracuseStep 2606813 = 977555) (by norm_num)
theorem B3090149 : Blo 1372005 3090149 := bbase (se 4 (by rfl) ⟨289701, by rfl⟩ : syracuseStep 3090149 = 579403) (by norm_num)
theorem B1672969 : Blo 1372005 1672969 := bbase (se 2 (by rfl) ⟨627363, by rfl⟩ : syracuseStep 1672969 = 1254727) (by norm_num)
theorem B1738513 : Blo 1372005 1738513 := bbase (se 2 (by rfl) ⟨651942, by rfl⟩ : syracuseStep 1738513 = 1303885) (by norm_num)
theorem B2058029 : Blo 1372005 2058029 := bbase (se 3 (by rfl) ⟨385880, by rfl⟩ : syracuseStep 2058029 = 771761) (by norm_num)
theorem B3090221 : Blo 1372005 3090221 := bbase (se 3 (by rfl) ⟨579416, by rfl⟩ : syracuseStep 3090221 = 1158833) (by norm_num)
theorem B2475821 : Blo 1372005 2475821 := bbase (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) (by norm_num)
theorem B2058053 : Blo 1372005 2058053 := bbase (se 4 (by rfl) ⟨192942, by rfl⟩ : syracuseStep 2058053 = 385885) (by norm_num)
theorem B2058077 : Blo 1372005 2058077 := bbase (se 3 (by rfl) ⟨385889, by rfl⟩ : syracuseStep 2058077 = 771779) (by norm_num)
theorem B2058101 : Blo 1372005 2058101 := bbase (se 5 (by rfl) ⟨96473, by rfl⟩ : syracuseStep 2058101 = 192947) (by norm_num)
theorem B3090293 : Blo 1372005 3090293 := bbase (se 5 (by rfl) ⟨144857, by rfl⟩ : syracuseStep 3090293 = 289715) (by norm_num)
theorem B3475325 : Blo 1372005 3475325 := bbase (se 3 (by rfl) ⟨651623, by rfl⟩ : syracuseStep 3475325 = 1303247) (by norm_num)
theorem B2058125 : Blo 1372005 2058125 := bbase (se 3 (by rfl) ⟨385898, by rfl⟩ : syracuseStep 2058125 = 771797) (by norm_num)
theorem B2058149 : Blo 1372005 2058149 := bbase (se 4 (by rfl) ⟨192951, by rfl⟩ : syracuseStep 2058149 = 385903) (by norm_num)
theorem B2058173 : Blo 1372005 2058173 := bbase (se 3 (by rfl) ⟨385907, by rfl⟩ : syracuseStep 2058173 = 771815) (by norm_num)
theorem B3090365 : Blo 1372005 3090365 := bbase (se 3 (by rfl) ⟨579443, by rfl⟩ : syracuseStep 3090365 = 1158887) (by norm_num)
theorem B1738685 : Blo 1372005 1738685 := bbase (se 3 (by rfl) ⟨326003, by rfl⟩ : syracuseStep 1738685 = 652007) (by norm_num)
theorem B2058197 : Blo 1372005 2058197 := bbase (se 7 (by rfl) ⟨24119, by rfl⟩ : syracuseStep 2058197 = 48239) (by norm_num)
theorem B4401125 : Blo 1372005 4401125 := bbase (se 4 (by rfl) ⟨412605, by rfl⟩ : syracuseStep 4401125 = 825211) (by norm_num)
theorem B2058221 : Blo 1372005 2058221 := bbase (se 3 (by rfl) ⟨385916, by rfl⟩ : syracuseStep 2058221 = 771833) (by norm_num)
theorem B1738741 : Blo 1372005 1738741 := bbase (se 5 (by rfl) ⟨81503, by rfl⟩ : syracuseStep 1738741 = 163007) (by norm_num)
theorem B2058245 : Blo 1372005 2058245 := bbase (se 4 (by rfl) ⟨192960, by rfl⟩ : syracuseStep 2058245 = 385921) (by norm_num)
theorem B3090437 : Blo 1372005 3090437 := bbase (se 4 (by rfl) ⟨289728, by rfl⟩ : syracuseStep 3090437 = 579457) (by norm_num)
theorem B2058269 : Blo 1372005 2058269 := bbase (se 3 (by rfl) ⟨385925, by rfl⟩ : syracuseStep 2058269 = 771851) (by norm_num)
theorem B2058293 : Blo 1372005 2058293 := bbase (se 5 (by rfl) ⟨96482, by rfl⟩ : syracuseStep 2058293 = 192965) (by norm_num)
theorem B2058317 : Blo 1372005 2058317 := bbase (se 3 (by rfl) ⟨385934, by rfl⟩ : syracuseStep 2058317 = 771869) (by norm_num)
theorem B3090509 : Blo 1372005 3090509 := bbase (se 3 (by rfl) ⟨579470, by rfl⟩ : syracuseStep 3090509 = 1158941) (by norm_num)
theorem B1648721 : Blo 1372005 1648721 := bbase (se 2 (by rfl) ⟨618270, by rfl⟩ : syracuseStep 1648721 = 1236541) (by norm_num)
theorem B1738837 : Blo 1372005 1738837 := bbase (se 8 (by rfl) ⟨10188, by rfl⟩ : syracuseStep 1738837 = 20377) (by norm_num)
theorem B2058341 : Blo 1372005 2058341 := bbase (se 4 (by rfl) ⟨192969, by rfl⟩ : syracuseStep 2058341 = 385939) (by norm_num)
theorem B2058365 : Blo 1372005 2058365 := bbase (se 3 (by rfl) ⟨385943, by rfl⟩ : syracuseStep 2058365 = 771887) (by norm_num)
theorem B4630661 : Blo 1372005 4630661 := bbase (se 4 (by rfl) ⟨434124, by rfl⟩ : syracuseStep 4630661 = 868249) (by norm_num)
theorem B5867653 : Blo 1372005 5867653 := bbase (se 4 (by rfl) ⟨550092, by rfl⟩ : syracuseStep 5867653 = 1100185) (by norm_num)
theorem B2058389 : Blo 1372005 2058389 := bbase (se 6 (by rfl) ⟨48243, by rfl⟩ : syracuseStep 2058389 = 96487) (by norm_num)
theorem B3090581 : Blo 1372005 3090581 := bbase (se 6 (by rfl) ⟨72435, by rfl⟩ : syracuseStep 3090581 = 144871) (by norm_num)
theorem B1648793 : Blo 1372005 1648793 := bbase (se 2 (by rfl) ⟨618297, by rfl⟩ : syracuseStep 1648793 = 1236595) (by norm_num)
theorem B2058413 : Blo 1372005 2058413 := bbase (se 3 (by rfl) ⟨385952, by rfl⟩ : syracuseStep 2058413 = 771905) (by norm_num)
theorem B2058437 : Blo 1372005 2058437 := bbase (se 4 (by rfl) ⟨192978, by rfl⟩ : syracuseStep 2058437 = 385957) (by norm_num)
theorem B3475669 : Blo 1372005 3475669 := bbase (se 7 (by rfl) ⟨40730, by rfl⟩ : syracuseStep 3475669 = 81461) (by norm_num)
theorem B4950229 : Blo 1372005 4950229 := bbase (se 7 (by rfl) ⟨58010, by rfl⟩ : syracuseStep 4950229 = 116021) (by norm_num)
theorem B2058461 : Blo 1372005 2058461 := bbase (se 3 (by rfl) ⟨385961, by rfl⟩ : syracuseStep 2058461 = 771923) (by norm_num)
theorem B3090653 : Blo 1372005 3090653 := bbase (se 3 (by rfl) ⟨579497, by rfl⟩ : syracuseStep 3090653 = 1158995) (by norm_num)
theorem B2058485 : Blo 1372005 2058485 := bbase (se 5 (by rfl) ⟨96491, by rfl⟩ : syracuseStep 2058485 = 192983) (by norm_num)
theorem B2058509 : Blo 1372005 2058509 := bbase (se 3 (by rfl) ⟨385970, by rfl⟩ : syracuseStep 2058509 = 771941) (by norm_num)
theorem B2058533 : Blo 1372005 2058533 := bbase (se 4 (by rfl) ⟨192987, by rfl⟩ : syracuseStep 2058533 = 385975) (by norm_num)
theorem B3090725 : Blo 1372005 3090725 := bbase (se 4 (by rfl) ⟨289755, by rfl⟩ : syracuseStep 3090725 = 579511) (by norm_num)
theorem B2058557 : Blo 1372005 2058557 := bbase (se 3 (by rfl) ⟨385979, by rfl⟩ : syracuseStep 2058557 = 771959) (by norm_num)
theorem B3475781 : Blo 1372005 3475781 := bbase (se 4 (by rfl) ⟨325854, by rfl⟩ : syracuseStep 3475781 = 651709) (by norm_num)
theorem B2058581 : Blo 1372005 2058581 := bbase (se 10 (by rfl) ⟨3015, by rfl⟩ : syracuseStep 2058581 = 6031) (by norm_num)
theorem B2058605 : Blo 1372005 2058605 := bbase (se 3 (by rfl) ⟨385988, by rfl⟩ : syracuseStep 2058605 = 771977) (by norm_num)
theorem B3090797 : Blo 1372005 3090797 := bbase (se 3 (by rfl) ⟨579524, by rfl⟩ : syracuseStep 3090797 = 1159049) (by norm_num)
theorem B2058629 : Blo 1372005 2058629 := bbase (se 4 (by rfl) ⟨192996, by rfl⟩ : syracuseStep 2058629 = 385993) (by norm_num)
theorem B2058653 : Blo 1372005 2058653 := bbase (se 3 (by rfl) ⟨385997, by rfl⟩ : syracuseStep 2058653 = 771995) (by norm_num)
theorem B2058677 : Blo 1372005 2058677 := bbase (se 5 (by rfl) ⟨96500, by rfl⟩ : syracuseStep 2058677 = 193001) (by norm_num)
theorem B3090869 : Blo 1372005 3090869 := bbase (se 5 (by rfl) ⟨144884, by rfl⟩ : syracuseStep 3090869 = 289769) (by norm_num)
theorem B2058701 : Blo 1372005 2058701 := bbase (se 3 (by rfl) ⟨386006, by rfl⟩ : syracuseStep 2058701 = 772013) (by norm_num)
theorem B1649101 : Blo 1372005 1649101 := bbase (se 3 (by rfl) ⟨309206, by rfl⟩ : syracuseStep 1649101 = 618413) (by norm_num)
theorem B2607565 : Blo 1372005 2607565 := bbase (se 3 (by rfl) ⟨488918, by rfl⟩ : syracuseStep 2607565 = 977837) (by norm_num)
theorem B2009549 : Blo 1372005 2009549 := bbase (se 3 (by rfl) ⟨376790, by rfl⟩ : syracuseStep 2009549 = 753581) (by norm_num)
theorem B2058725 : Blo 1372005 2058725 := bbase (se 4 (by rfl) ⟨193005, by rfl⟩ : syracuseStep 2058725 = 386011) (by norm_num)
theorem B2058749 : Blo 1372005 2058749 := bbase (se 3 (by rfl) ⟨386015, by rfl⟩ : syracuseStep 2058749 = 772031) (by norm_num)
theorem B3090941 : Blo 1372005 3090941 := bbase (se 3 (by rfl) ⟨579551, by rfl⟩ : syracuseStep 3090941 = 1159103) (by norm_num)
theorem B3475973 : Blo 1372005 3475973 := bbase (se 4 (by rfl) ⟨325872, by rfl⟩ : syracuseStep 3475973 = 651745) (by norm_num)
theorem B2058773 : Blo 1372005 2058773 := bbase (se 6 (by rfl) ⟨48252, by rfl⟩ : syracuseStep 2058773 = 96505) (by norm_num)
theorem B2058797 : Blo 1372005 2058797 := bbase (se 3 (by rfl) ⟨386024, by rfl⟩ : syracuseStep 2058797 = 772049) (by norm_num)
theorem B1485361 : Blo 1372005 1485361 := bbase (se 2 (by rfl) ⟨557010, by rfl⟩ : syracuseStep 1485361 = 1114021) (by norm_num)
theorem B4631093 : Blo 1372005 4631093 := bbase (se 5 (by rfl) ⟨217082, by rfl⟩ : syracuseStep 4631093 = 434165) (by norm_num)
theorem B2058821 : Blo 1372005 2058821 := bbase (se 4 (by rfl) ⟨193014, by rfl⟩ : syracuseStep 2058821 = 386029) (by norm_num)
theorem B3091013 : Blo 1372005 3091013 := bbase (se 4 (by rfl) ⟨289782, by rfl⟩ : syracuseStep 3091013 = 579565) (by norm_num)
theorem B11725397 : Blo 1372005 11725397 := bbase (se 8 (by rfl) ⟨68703, by rfl⟩ : syracuseStep 11725397 = 137407) (by norm_num)
theorem B3525205 : Blo 1372005 3525205 := bbase (se 8 (by rfl) ⟨20655, by rfl⟩ : syracuseStep 3525205 = 41311) (by norm_num)
theorem B2058845 : Blo 1372005 2058845 := bbase (se 3 (by rfl) ⟨386033, by rfl⟩ : syracuseStep 2058845 = 772067) (by norm_num)
theorem B2607709 : Blo 1372005 2607709 := bbase (se 3 (by rfl) ⟨488945, by rfl⟩ : syracuseStep 2607709 = 977891) (by norm_num)
theorem B2058869 : Blo 1372005 2058869 := bbase (se 5 (by rfl) ⟨96509, by rfl⟩ : syracuseStep 2058869 = 193019) (by norm_num)
theorem B1649269 : Blo 1372005 1649269 := bbase (se 5 (by rfl) ⟨77309, by rfl⟩ : syracuseStep 1649269 = 154619) (by norm_num)
theorem B2058893 : Blo 1372005 2058893 := bbase (se 3 (by rfl) ⟨386042, by rfl⟩ : syracuseStep 2058893 = 772085) (by norm_num)
theorem B3091085 : Blo 1372005 3091085 := bbase (se 3 (by rfl) ⟨579578, by rfl⟩ : syracuseStep 3091085 = 1159157) (by norm_num)
theorem B5638805 : Blo 1372005 5638805 := bbase (se 6 (by rfl) ⟨132159, by rfl⟩ : syracuseStep 5638805 = 264319) (by norm_num)
theorem B2058917 : Blo 1372005 2058917 := bbase (se 4 (by rfl) ⟨193023, by rfl⟩ : syracuseStep 2058917 = 386047) (by norm_num)
theorem B1649317 : Blo 1372005 1649317 := bbase (se 4 (by rfl) ⟨154623, by rfl⟩ : syracuseStep 1649317 = 309247) (by norm_num)
theorem B2058941 : Blo 1372005 2058941 := bbase (se 3 (by rfl) ⟨386051, by rfl⟩ : syracuseStep 2058941 = 772103) (by norm_num)
theorem B2058965 : Blo 1372005 2058965 := bbase (se 7 (by rfl) ⟨24128, by rfl⟩ : syracuseStep 2058965 = 48257) (by norm_num)
theorem B3091157 : Blo 1372005 3091157 := bbase (se 7 (by rfl) ⟨36224, by rfl⟩ : syracuseStep 3091157 = 72449) (by norm_num)
theorem B2058989 : Blo 1372005 2058989 := bbase (se 3 (by rfl) ⟨386060, by rfl⟩ : syracuseStep 2058989 = 772121) (by norm_num)
theorem B2198269 : Blo 1372005 2198269 := bbase (se 3 (by rfl) ⟨412175, by rfl⟩ : syracuseStep 2198269 = 824351) (by norm_num)
theorem B2607869 : Blo 1372005 2607869 := bbase (se 3 (by rfl) ⟨488975, by rfl⟩ : syracuseStep 2607869 = 977951) (by norm_num)
theorem B2059013 : Blo 1372005 2059013 := bbase (se 4 (by rfl) ⟨193032, by rfl⟩ : syracuseStep 2059013 = 386065) (by norm_num)
theorem B6949637 : Blo 1372005 6949637 := bbase (se 4 (by rfl) ⟨651528, by rfl⟩ : syracuseStep 6949637 = 1303057) (by norm_num)
theorem B1649413 : Blo 1372005 1649413 := bbase (se 4 (by rfl) ⟨154632, by rfl⟩ : syracuseStep 1649413 = 309265) (by norm_num)
theorem B2059037 : Blo 1372005 2059037 := bbase (se 3 (by rfl) ⟨386069, by rfl⟩ : syracuseStep 2059037 = 772139) (by norm_num)
theorem B3091229 : Blo 1372005 3091229 := bbase (se 3 (by rfl) ⟨579605, by rfl⟩ : syracuseStep 3091229 = 1159211) (by norm_num)
theorem B2059061 : Blo 1372005 2059061 := bbase (se 5 (by rfl) ⟨96518, by rfl⟩ : syracuseStep 2059061 = 193037) (by norm_num)
theorem B2059085 : Blo 1372005 2059085 := bbase (se 3 (by rfl) ⟨386078, by rfl⟩ : syracuseStep 2059085 = 772157) (by norm_num)
theorem B3476317 : Blo 1372005 3476317 := bbase (se 3 (by rfl) ⟨651809, by rfl⟩ : syracuseStep 3476317 = 1303619) (by norm_num)
theorem B2059109 : Blo 1372005 2059109 := bbase (se 4 (by rfl) ⟨193041, by rfl⟩ : syracuseStep 2059109 = 386083) (by norm_num)
theorem B5868389 : Blo 1372005 5868389 := bbase (se 4 (by rfl) ⟨550161, by rfl⟩ : syracuseStep 5868389 = 1100323) (by norm_num)
theorem B3091301 : Blo 1372005 3091301 := bbase (se 4 (by rfl) ⟨289809, by rfl⟩ : syracuseStep 3091301 = 579619) (by norm_num)
theorem B2059133 : Blo 1372005 2059133 := bbase (se 3 (by rfl) ⟨386087, by rfl⟩ : syracuseStep 2059133 = 772175) (by norm_num)
theorem B2608013 : Blo 1372005 2608013 := bbase (se 3 (by rfl) ⟨489002, by rfl⟩ : syracuseStep 2608013 = 978005) (by norm_num)
theorem B2059157 : Blo 1372005 2059157 := bbase (se 6 (by rfl) ⟨48261, by rfl⟩ : syracuseStep 2059157 = 96523) (by norm_num)
theorem B2059181 : Blo 1372005 2059181 := bbase (se 3 (by rfl) ⟨386096, by rfl⟩ : syracuseStep 2059181 = 772193) (by norm_num)
theorem B3091373 : Blo 1372005 3091373 := bbase (se 3 (by rfl) ⟨579632, by rfl⟩ : syracuseStep 3091373 = 1159265) (by norm_num)
theorem B2059205 : Blo 1372005 2059205 := bbase (se 4 (by rfl) ⟨193050, by rfl⟩ : syracuseStep 2059205 = 386101) (by norm_num)
theorem B3476429 : Blo 1372005 3476429 := bbase (se 3 (by rfl) ⟨651830, by rfl⟩ : syracuseStep 3476429 = 1303661) (by norm_num)
theorem B2059229 : Blo 1372005 2059229 := bbase (se 3 (by rfl) ⟨386105, by rfl⟩ : syracuseStep 2059229 = 772211) (by norm_num)
theorem B4631525 : Blo 1372005 4631525 := bbase (se 4 (by rfl) ⟨434205, by rfl⟩ : syracuseStep 4631525 = 868411) (by norm_num)
theorem B2059253 : Blo 1372005 2059253 := bbase (se 5 (by rfl) ⟨96527, by rfl⟩ : syracuseStep 2059253 = 193055) (by norm_num)
theorem B3091445 : Blo 1372005 3091445 := bbase (se 5 (by rfl) ⟨144911, by rfl⟩ : syracuseStep 3091445 = 289823) (by norm_num)
theorem B2059277 : Blo 1372005 2059277 := bbase (se 3 (by rfl) ⟨386114, by rfl⟩ : syracuseStep 2059277 = 772229) (by norm_num)
theorem B2059301 : Blo 1372005 2059301 := bbase (se 4 (by rfl) ⟨193059, by rfl⟩ : syracuseStep 2059301 = 386119) (by norm_num)
theorem B2059325 : Blo 1372005 2059325 := bbase (se 3 (by rfl) ⟨386123, by rfl⟩ : syracuseStep 2059325 = 772247) (by norm_num)
theorem B2059349 : Blo 1372005 2059349 := bbase (se 8 (by rfl) ⟨12066, by rfl⟩ : syracuseStep 2059349 = 24133) (by norm_num)
theorem B2059373 : Blo 1372005 2059373 := bbase (se 3 (by rfl) ⟨386132, by rfl⟩ : syracuseStep 2059373 = 772265) (by norm_num)
theorem B2059397 : Blo 1372005 2059397 := bbase (se 4 (by rfl) ⟨193068, by rfl⟩ : syracuseStep 2059397 = 386137) (by norm_num)
theorem B3476621 : Blo 1372005 3476621 := bbase (se 3 (by rfl) ⟨651866, by rfl⟩ : syracuseStep 3476621 = 1303733) (by norm_num)
theorem B7818389 : Blo 1372005 7818389 := bbase (se 6 (by rfl) ⟨183243, by rfl⟩ : syracuseStep 7818389 = 366487) (by norm_num)
theorem B2059421 : Blo 1372005 2059421 := bbase (se 3 (by rfl) ⟨386141, by rfl⟩ : syracuseStep 2059421 = 772283) (by norm_num)
theorem B2608301 : Blo 1372005 2608301 := bbase (se 3 (by rfl) ⟨489056, by rfl⟩ : syracuseStep 2608301 = 978113) (by norm_num)
theorem B2059445 : Blo 1372005 2059445 := bbase (se 5 (by rfl) ⟨96536, by rfl⟩ : syracuseStep 2059445 = 193073) (by norm_num)
theorem B2059469 : Blo 1372005 2059469 := bbase (se 3 (by rfl) ⟨386150, by rfl⟩ : syracuseStep 2059469 = 772301) (by norm_num)
theorem B6597845 : Blo 1372005 6597845 := bbase (se 7 (by rfl) ⟨77318, by rfl⟩ : syracuseStep 6597845 = 154637) (by norm_num)
theorem B2059493 : Blo 1372005 2059493 := bbase (se 4 (by rfl) ⟨193077, by rfl⟩ : syracuseStep 2059493 = 386155) (by norm_num)
theorem B5213429 : Blo 1372005 5213429 := bbase (se 5 (by rfl) ⟨244379, by rfl⟩ : syracuseStep 5213429 = 488759) (by norm_num)
theorem B2059517 : Blo 1372005 2059517 := bbase (se 3 (by rfl) ⟨386159, by rfl⟩ : syracuseStep 2059517 = 772319) (by norm_num)
theorem B5860613 : Blo 1372005 5860613 := bbase (se 4 (by rfl) ⟨549432, by rfl⟩ : syracuseStep 5860613 = 1098865) (by norm_num)
theorem B2059541 : Blo 1372005 2059541 := bbase (se 6 (by rfl) ⟨48270, by rfl⟩ : syracuseStep 2059541 = 96541) (by norm_num)
theorem B3910949 : Blo 1372005 3910949 := bbase (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) (by norm_num)
theorem B2059565 : Blo 1372005 2059565 := bbase (se 3 (by rfl) ⟨386168, by rfl⟩ : syracuseStep 2059565 = 772337) (by norm_num)
theorem B2059589 : Blo 1372005 2059589 := bbase (se 4 (by rfl) ⟨193086, by rfl⟩ : syracuseStep 2059589 = 386173) (by norm_num)
theorem B1649989 : Blo 1372005 1649989 := bbase (se 4 (by rfl) ⟨154686, by rfl⟩ : syracuseStep 1649989 = 309373) (by norm_num)
theorem B2608453 : Blo 1372005 2608453 := bbase (se 4 (by rfl) ⟨244542, by rfl⟩ : syracuseStep 2608453 = 489085) (by norm_num)
theorem B1543513 : Blo 1372005 1543513 := bbase (se 2 (by rfl) ⟨578817, by rfl⟩ : syracuseStep 1543513 = 1157635) (by norm_num)
theorem B2059613 : Blo 1372005 2059613 := bbase (se 3 (by rfl) ⟨386177, by rfl⟩ : syracuseStep 2059613 = 772355) (by norm_num)
theorem B5565797 : Blo 1372005 5565797 := bbase (se 4 (by rfl) ⟨521793, by rfl⟩ : syracuseStep 5565797 = 1043587) (by norm_num)
theorem B2542949 : Blo 1372005 2542949 := bbase (se 4 (by rfl) ⟨238401, by rfl⟩ : syracuseStep 2542949 = 476803) (by norm_num)
theorem B2059637 : Blo 1372005 2059637 := bbase (se 5 (by rfl) ⟨96545, by rfl⟩ : syracuseStep 2059637 = 193091) (by norm_num)
theorem B7048565 : Blo 1372005 7048565 := bbase (se 5 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 7048565 = 660803) (by norm_num)
theorem B1543549 : Blo 1372005 1543549 := bbase (se 3 (by rfl) ⟨289415, by rfl⟩ : syracuseStep 1543549 = 578831) (by norm_num)
theorem B2059661 : Blo 1372005 2059661 := bbase (se 3 (by rfl) ⟨386186, by rfl⟩ : syracuseStep 2059661 = 772373) (by norm_num)
theorem B4631957 : Blo 1372005 4631957 := bbase (se 6 (by rfl) ⟨108561, by rfl⟩ : syracuseStep 4631957 = 217123) (by norm_num)
theorem B1543585 : Blo 1372005 1543585 := bbase (se 2 (by rfl) ⟨578844, by rfl⟩ : syracuseStep 1543585 = 1157689) (by norm_num)
theorem B4697509 : Blo 1372005 4697509 := bbase (se 4 (by rfl) ⟨440391, by rfl⟩ : syracuseStep 4697509 = 880783) (by norm_num)
theorem B2059685 : Blo 1372005 2059685 := bbase (se 4 (by rfl) ⟨193095, by rfl⟩ : syracuseStep 2059685 = 386191) (by norm_num)
theorem B3296693 : Blo 1372005 3296693 := bbase (se 5 (by rfl) ⟨154532, by rfl⟩ : syracuseStep 3296693 = 309065) (by norm_num)
theorem B2059709 : Blo 1372005 2059709 := bbase (se 3 (by rfl) ⟨386195, by rfl⟩ : syracuseStep 2059709 = 772391) (by norm_num)
theorem B1543621 : Blo 1372005 1543621 := bbase (se 4 (by rfl) ⟨144714, by rfl⟩ : syracuseStep 1543621 = 289429) (by norm_num)
theorem B2059733 : Blo 1372005 2059733 := bbase (se 7 (by rfl) ⟨24137, by rfl⟩ : syracuseStep 2059733 = 48275) (by norm_num)
theorem B3476965 : Blo 1372005 3476965 := bbase (se 4 (by rfl) ⟨325965, by rfl⟩ : syracuseStep 3476965 = 651931) (by norm_num)
theorem B1543657 : Blo 1372005 1543657 := bbase (se 2 (by rfl) ⟨578871, by rfl⟩ : syracuseStep 1543657 = 1157743) (by norm_num)
theorem B3296749 : Blo 1372005 3296749 := bbase (se 3 (by rfl) ⟨618140, by rfl⟩ : syracuseStep 3296749 = 1236281) (by norm_num)
theorem B2059757 : Blo 1372005 2059757 := bbase (se 3 (by rfl) ⟨386204, by rfl⟩ : syracuseStep 2059757 = 772409) (by norm_num)
theorem B2715125 : Blo 1372005 2715125 := bbase (se 5 (by rfl) ⟨127271, by rfl⟩ : syracuseStep 2715125 = 254543) (by norm_num)
theorem B10431989 : Blo 1372005 10431989 := bbase (se 5 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 10431989 = 977999) (by norm_num)
theorem B2059781 : Blo 1372005 2059781 := bbase (se 4 (by rfl) ⟨193104, by rfl⟩ : syracuseStep 2059781 = 386209) (by norm_num)
theorem B1543693 : Blo 1372005 1543693 := bbase (se 3 (by rfl) ⟨289442, by rfl⟩ : syracuseStep 1543693 = 578885) (by norm_num)
theorem B4697621 : Blo 1372005 4697621 := bbase (se 6 (by rfl) ⟨110100, by rfl⟩ : syracuseStep 4697621 = 220201) (by norm_num)
theorem B5213717 : Blo 1372005 5213717 := bbase (se 6 (by rfl) ⟨122196, by rfl⟩ : syracuseStep 5213717 = 244393) (by norm_num)
theorem B2059805 : Blo 1372005 2059805 := bbase (se 3 (by rfl) ⟨386213, by rfl⟩ : syracuseStep 2059805 = 772427) (by norm_num)
theorem B1543729 : Blo 1372005 1543729 := bbase (se 2 (by rfl) ⟨578898, by rfl⟩ : syracuseStep 1543729 = 1157797) (by norm_num)
theorem B2059829 : Blo 1372005 2059829 := bbase (se 5 (by rfl) ⟨96554, by rfl⟩ : syracuseStep 2059829 = 193109) (by norm_num)
theorem B2059853 : Blo 1372005 2059853 := bbase (se 3 (by rfl) ⟨386222, by rfl⟩ : syracuseStep 2059853 = 772445) (by norm_num)
theorem B1543765 : Blo 1372005 1543765 := bbase (se 8 (by rfl) ⟨9045, by rfl⟩ : syracuseStep 1543765 = 18091) (by norm_num)
theorem B3477077 : Blo 1372005 3477077 := bbase (se 8 (by rfl) ⟨20373, by rfl⟩ : syracuseStep 3477077 = 40747) (by norm_num)
theorem B2059877 : Blo 1372005 2059877 := bbase (se 4 (by rfl) ⟨193113, by rfl⟩ : syracuseStep 2059877 = 386227) (by norm_num)
theorem B1543801 : Blo 1372005 1543801 := bbase (se 2 (by rfl) ⟨578925, by rfl⟩ : syracuseStep 1543801 = 1157851) (by norm_num)
theorem B2059901 : Blo 1372005 2059901 := bbase (se 3 (by rfl) ⟨386231, by rfl⟩ : syracuseStep 2059901 = 772463) (by norm_num)
theorem B2059925 : Blo 1372005 2059925 := bbase (se 6 (by rfl) ⟨48279, by rfl⟩ : syracuseStep 2059925 = 96559) (by norm_num)
theorem B1543837 : Blo 1372005 1543837 := bbase (se 3 (by rfl) ⟨289469, by rfl⟩ : syracuseStep 1543837 = 578939) (by norm_num)
theorem B2059949 : Blo 1372005 2059949 := bbase (se 3 (by rfl) ⟨386240, by rfl⟩ : syracuseStep 2059949 = 772481) (by norm_num)
theorem B1855157 : Blo 1372005 1855157 := bbase (se 5 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 1855157 = 173921) (by norm_num)
theorem B1543873 : Blo 1372005 1543873 := bbase (se 2 (by rfl) ⟨578952, by rfl⟩ : syracuseStep 1543873 = 1157905) (by norm_num)
theorem B2059973 : Blo 1372005 2059973 := bbase (se 4 (by rfl) ⟨193122, by rfl⟩ : syracuseStep 2059973 = 386245) (by norm_num)
theorem B15634133 : Blo 1372005 15634133 := bbase (se 7 (by rfl) ⟨183212, by rfl⟩ : syracuseStep 15634133 = 366425) (by norm_num)
theorem B2059997 : Blo 1372005 2059997 := bbase (se 3 (by rfl) ⟨386249, by rfl⟩ : syracuseStep 2059997 = 772499) (by norm_num)
theorem B1543909 : Blo 1372005 1543909 := bbase (se 4 (by rfl) ⟨144741, by rfl⟩ : syracuseStep 1543909 = 289483) (by norm_num)
theorem B8793845 : Blo 1372005 8793845 := bbase (se 5 (by rfl) ⟨412211, by rfl⟩ : syracuseStep 8793845 = 824423) (by norm_num)
theorem B2060021 : Blo 1372005 2060021 := bbase (se 5 (by rfl) ⟨96563, by rfl⟩ : syracuseStep 2060021 = 193127) (by norm_num)
theorem B9899765 : Blo 1372005 9899765 := bbase (se 5 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 9899765 = 928103) (by norm_num)
theorem B1543945 : Blo 1372005 1543945 := bbase (se 2 (by rfl) ⟨578979, by rfl⟩ : syracuseStep 1543945 = 1157959) (by norm_num)
theorem B2060045 : Blo 1372005 2060045 := bbase (se 3 (by rfl) ⟨386258, by rfl⟩ : syracuseStep 2060045 = 772517) (by norm_num)
theorem B3477269 : Blo 1372005 3477269 := bbase (se 6 (by rfl) ⟨81498, by rfl⟩ : syracuseStep 3477269 = 162997) (by norm_num)
theorem B2060069 : Blo 1372005 2060069 := bbase (se 4 (by rfl) ⟨193131, by rfl⟩ : syracuseStep 2060069 = 386263) (by norm_num)
theorem B1543981 : Blo 1372005 1543981 := bbase (se 3 (by rfl) ⟨289496, by rfl⟩ : syracuseStep 1543981 = 578993) (by norm_num)
theorem B2060093 : Blo 1372005 2060093 := bbase (se 3 (by rfl) ⟨386267, by rfl⟩ : syracuseStep 2060093 = 772535) (by norm_num)
theorem B4632389 : Blo 1372005 4632389 := bbase (se 4 (by rfl) ⟨434286, by rfl⟩ : syracuseStep 4632389 = 868573) (by norm_num)
theorem B1544017 : Blo 1372005 1544017 := bbase (se 2 (by rfl) ⟨579006, by rfl⟩ : syracuseStep 1544017 = 1158013) (by norm_num)
theorem B2060117 : Blo 1372005 2060117 := bbase (se 9 (by rfl) ⟨6035, by rfl⟩ : syracuseStep 2060117 = 12071) (by norm_num)
theorem B3297125 : Blo 1372005 3297125 := bbase (se 4 (by rfl) ⟨309105, by rfl⟩ : syracuseStep 3297125 = 618211) (by norm_num)
theorem B2060141 : Blo 1372005 2060141 := bbase (se 3 (by rfl) ⟨386276, by rfl⟩ : syracuseStep 2060141 = 772553) (by norm_num)
theorem B1544053 : Blo 1372005 1544053 := bbase (se 5 (by rfl) ⟨72377, by rfl⟩ : syracuseStep 1544053 = 144755) (by norm_num)
theorem B2060165 : Blo 1372005 2060165 := bbase (se 4 (by rfl) ⟨193140, by rfl⟩ : syracuseStep 2060165 = 386281) (by norm_num)
theorem B10424213 : Blo 1372005 10424213 := bbase (se 6 (by rfl) ⟨244317, by rfl⟩ : syracuseStep 10424213 = 488635) (by norm_num)
theorem B1544089 : Blo 1372005 1544089 := bbase (se 2 (by rfl) ⟨579033, by rfl⟩ : syracuseStep 1544089 = 1158067) (by norm_num)
theorem B2060189 : Blo 1372005 2060189 := bbase (se 3 (by rfl) ⟨386285, by rfl⟩ : syracuseStep 2060189 = 772571) (by norm_num)
theorem B2060213 : Blo 1372005 2060213 := bbase (se 5 (by rfl) ⟨96572, by rfl⟩ : syracuseStep 2060213 = 193145) (by norm_num)
theorem B1544125 : Blo 1372005 1544125 := bbase (se 3 (by rfl) ⟨289523, by rfl⟩ : syracuseStep 1544125 = 579047) (by norm_num)
theorem B2060237 : Blo 1372005 2060237 := bbase (se 3 (by rfl) ⟨386294, by rfl⟩ : syracuseStep 2060237 = 772589) (by norm_num)
theorem B1544161 : Blo 1372005 1544161 := bbase (se 2 (by rfl) ⟨579060, by rfl⟩ : syracuseStep 1544161 = 1158121) (by norm_num)
theorem B2060261 : Blo 1372005 2060261 := bbase (se 4 (by rfl) ⟨193149, by rfl⟩ : syracuseStep 2060261 = 386299) (by norm_num)
theorem B6688757 : Blo 1372005 6688757 := bbase (se 5 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 6688757 = 627071) (by norm_num)
theorem B1486841 : Blo 1372005 1486841 := bbase (se 2 (by rfl) ⟨557565, by rfl⟩ : syracuseStep 1486841 = 1115131) (by norm_num)
theorem B2060285 : Blo 1372005 2060285 := bbase (se 3 (by rfl) ⟨386303, by rfl⟩ : syracuseStep 2060285 = 772607) (by norm_num)
theorem B1544197 : Blo 1372005 1544197 := bbase (se 4 (by rfl) ⟨144768, by rfl⟩ : syracuseStep 1544197 = 289537) (by norm_num)
theorem B6950933 : Blo 1372005 6950933 := bbase (se 6 (by rfl) ⟨162912, by rfl⟩ : syracuseStep 6950933 = 325825) (by norm_num)
theorem B2060309 : Blo 1372005 2060309 := bbase (se 6 (by rfl) ⟨48288, by rfl⟩ : syracuseStep 2060309 = 96577) (by norm_num)
theorem B1544233 : Blo 1372005 1544233 := bbase (se 2 (by rfl) ⟨579087, by rfl⟩ : syracuseStep 1544233 = 1158175) (by norm_num)
theorem B2060333 : Blo 1372005 2060333 := bbase (se 3 (by rfl) ⟨386312, by rfl⟩ : syracuseStep 2060333 = 772625) (by norm_num)
theorem B2060357 : Blo 1372005 2060357 := bbase (se 4 (by rfl) ⟨193158, by rfl⟩ : syracuseStep 2060357 = 386317) (by norm_num)
theorem B1544269 : Blo 1372005 1544269 := bbase (se 3 (by rfl) ⟨289550, by rfl⟩ : syracuseStep 1544269 = 579101) (by norm_num)
theorem B3297365 : Blo 1372005 3297365 := bbase (se 8 (by rfl) ⟨19320, by rfl⟩ : syracuseStep 3297365 = 38641) (by norm_num)
theorem B2060381 : Blo 1372005 2060381 := bbase (se 3 (by rfl) ⟨386321, by rfl⟩ : syracuseStep 2060381 = 772643) (by norm_num)
theorem B2199653 : Blo 1372005 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B3477613 : Blo 1372005 3477613 := bbase (se 3 (by rfl) ⟨652052, by rfl⟩ : syracuseStep 3477613 = 1304105) (by norm_num)
theorem B1544305 : Blo 1372005 1544305 := bbase (se 2 (by rfl) ⟨579114, by rfl⟩ : syracuseStep 1544305 = 1158229) (by norm_num)
theorem B2060405 : Blo 1372005 2060405 := bbase (se 5 (by rfl) ⟨96581, by rfl⟩ : syracuseStep 2060405 = 193163) (by norm_num)
theorem B3764357 : Blo 1372005 3764357 := bbase (se 4 (by rfl) ⟨352908, by rfl⟩ : syracuseStep 3764357 = 705817) (by norm_num)
theorem B2060429 : Blo 1372005 2060429 := bbase (se 3 (by rfl) ⟨386330, by rfl⟩ : syracuseStep 2060429 = 772661) (by norm_num)
theorem B1544341 : Blo 1372005 1544341 := bbase (se 6 (by rfl) ⟨36195, by rfl⟩ : syracuseStep 1544341 = 72391) (by norm_num)
theorem B2060453 : Blo 1372005 2060453 := bbase (se 4 (by rfl) ⟨193167, by rfl⟩ : syracuseStep 2060453 = 386335) (by norm_num)
theorem B1544377 : Blo 1372005 1544377 := bbase (se 2 (by rfl) ⟨579141, by rfl⟩ : syracuseStep 1544377 = 1158283) (by norm_num)
theorem B2060477 : Blo 1372005 2060477 := bbase (se 3 (by rfl) ⟨386339, by rfl⟩ : syracuseStep 2060477 = 772679) (by norm_num)
theorem B18084053 : Blo 1372005 18084053 := bbase (se 7 (by rfl) ⟨211922, by rfl⟩ : syracuseStep 18084053 = 423845) (by norm_num)
theorem B2060501 : Blo 1372005 2060501 := bbase (se 7 (by rfl) ⟨24146, by rfl⟩ : syracuseStep 2060501 = 48293) (by norm_num)
theorem B1544413 : Blo 1372005 1544413 := bbase (se 3 (by rfl) ⟨289577, by rfl⟩ : syracuseStep 1544413 = 579155) (by norm_num)
theorem B3477725 : Blo 1372005 3477725 := bbase (se 3 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 3477725 = 1304147) (by norm_num)
theorem B5861605 : Blo 1372005 5861605 := bbase (se 4 (by rfl) ⟨549525, by rfl⟩ : syracuseStep 5861605 = 1099051) (by norm_num)
theorem B2060525 : Blo 1372005 2060525 := bbase (se 3 (by rfl) ⟨386348, by rfl⟩ : syracuseStep 2060525 = 772697) (by norm_num)
theorem B4632821 : Blo 1372005 4632821 := bbase (se 5 (by rfl) ⟨217163, by rfl⟩ : syracuseStep 4632821 = 434327) (by norm_num)
theorem B1544449 : Blo 1372005 1544449 := bbase (se 2 (by rfl) ⟨579168, by rfl⟩ : syracuseStep 1544449 = 1158337) (by norm_num)
theorem B2060549 : Blo 1372005 2060549 := bbase (se 4 (by rfl) ⟨193176, by rfl⟩ : syracuseStep 2060549 = 386353) (by norm_num)
theorem B2060573 : Blo 1372005 2060573 := bbase (se 3 (by rfl) ⟨386357, by rfl⟩ : syracuseStep 2060573 = 772715) (by norm_num)
theorem B1544485 : Blo 1372005 1544485 := bbase (se 4 (by rfl) ⟨144795, by rfl⟩ : syracuseStep 1544485 = 289591) (by norm_num)
theorem B2199845 : Blo 1372005 2199845 := bbase (se 4 (by rfl) ⟨206235, by rfl⟩ : syracuseStep 2199845 = 412471) (by norm_num)
theorem B2060597 : Blo 1372005 2060597 := bbase (se 5 (by rfl) ⟨96590, by rfl⟩ : syracuseStep 2060597 = 193181) (by norm_num)
theorem B1544521 : Blo 1372005 1544521 := bbase (se 2 (by rfl) ⟨579195, by rfl⟩ : syracuseStep 1544521 = 1158391) (by norm_num)
theorem B2060621 : Blo 1372005 2060621 := bbase (se 3 (by rfl) ⟨386366, by rfl⟩ : syracuseStep 2060621 = 772733) (by norm_num)
theorem B2060645 : Blo 1372005 2060645 := bbase (se 4 (by rfl) ⟨193185, by rfl⟩ : syracuseStep 2060645 = 386371) (by norm_num)
theorem B1544557 : Blo 1372005 1544557 := bbase (se 3 (by rfl) ⟨289604, by rfl⟩ : syracuseStep 1544557 = 579209) (by norm_num)
theorem B2060669 : Blo 1372005 2060669 := bbase (se 3 (by rfl) ⟨386375, by rfl⟩ : syracuseStep 2060669 = 772751) (by norm_num)
theorem B1544593 : Blo 1372005 1544593 := bbase (se 2 (by rfl) ⟨579222, by rfl⟩ : syracuseStep 1544593 = 1158445) (by norm_num)
theorem B2060693 : Blo 1372005 2060693 := bbase (se 6 (by rfl) ⟨48297, by rfl⟩ : syracuseStep 2060693 = 96595) (by norm_num)
theorem B3477917 : Blo 1372005 3477917 := bbase (se 3 (by rfl) ⟨652109, by rfl⟩ : syracuseStep 3477917 = 1304219) (by norm_num)
theorem B2060717 : Blo 1372005 2060717 := bbase (se 3 (by rfl) ⟨386384, by rfl⟩ : syracuseStep 2060717 = 772769) (by norm_num)
theorem B1544629 : Blo 1372005 1544629 := bbase (se 5 (by rfl) ⟨72404, by rfl⟩ : syracuseStep 1544629 = 144809) (by norm_num)
theorem B3912133 : Blo 1372005 3912133 := bbase (se 4 (by rfl) ⟨366762, by rfl⟩ : syracuseStep 3912133 = 733525) (by norm_num)
theorem B2060741 : Blo 1372005 2060741 := bbase (se 4 (by rfl) ⟨193194, by rfl⟩ : syracuseStep 2060741 = 386389) (by norm_num)
theorem B1544665 : Blo 1372005 1544665 := bbase (se 2 (by rfl) ⟨579249, by rfl⟩ : syracuseStep 1544665 = 1158499) (by norm_num)
theorem B2060765 : Blo 1372005 2060765 := bbase (se 3 (by rfl) ⟨386393, by rfl⟩ : syracuseStep 2060765 = 772787) (by norm_num)
theorem B2060789 : Blo 1372005 2060789 := bbase (se 5 (by rfl) ⟨96599, by rfl⟩ : syracuseStep 2060789 = 193199) (by norm_num)
theorem B1544701 : Blo 1372005 1544701 := bbase (se 3 (by rfl) ⟨289631, by rfl⟩ : syracuseStep 1544701 = 579263) (by norm_num)
theorem B2060813 : Blo 1372005 2060813 := bbase (se 3 (by rfl) ⟨386402, by rfl⟩ : syracuseStep 2060813 = 772805) (by norm_num)
theorem B1544737 : Blo 1372005 1544737 := bbase (se 2 (by rfl) ⟨579276, by rfl⟩ : syracuseStep 1544737 = 1158553) (by norm_num)
theorem B2060837 : Blo 1372005 2060837 := bbase (se 4 (by rfl) ⟨193203, by rfl⟩ : syracuseStep 2060837 = 386407) (by norm_num)
theorem B2060861 : Blo 1372005 2060861 := bbase (se 3 (by rfl) ⟨386411, by rfl⟩ : syracuseStep 2060861 = 772823) (by norm_num)
theorem B1544773 : Blo 1372005 1544773 := bbase (se 4 (by rfl) ⟨144822, by rfl⟩ : syracuseStep 1544773 = 289645) (by norm_num)
theorem B1954381 : Blo 1372005 1954381 := bbase (se 3 (by rfl) ⟨366446, by rfl⟩ : syracuseStep 1954381 = 732893) (by norm_num)
theorem B2060885 : Blo 1372005 2060885 := bbase (se 8 (by rfl) ⟨12075, by rfl⟩ : syracuseStep 2060885 = 24151) (by norm_num)
theorem B3912293 : Blo 1372005 3912293 := bbase (se 4 (by rfl) ⟨366777, by rfl⟩ : syracuseStep 3912293 = 733555) (by norm_num)
theorem B1544809 : Blo 1372005 1544809 := bbase (se 2 (by rfl) ⟨579303, by rfl⟩ : syracuseStep 1544809 = 1158607) (by norm_num)
theorem B2060909 : Blo 1372005 2060909 := bbase (se 3 (by rfl) ⟨386420, by rfl⟩ : syracuseStep 2060909 = 772841) (by norm_num)
theorem B2060933 : Blo 1372005 2060933 := bbase (se 4 (by rfl) ⟨193212, by rfl⟩ : syracuseStep 2060933 = 386425) (by norm_num)
theorem B1544845 : Blo 1372005 1544845 := bbase (se 3 (by rfl) ⟨289658, by rfl⟩ : syracuseStep 1544845 = 579317) (by norm_num)
theorem B2060957 : Blo 1372005 2060957 := bbase (se 3 (by rfl) ⟨386429, by rfl⟩ : syracuseStep 2060957 = 772859) (by norm_num)
theorem B4633253 : Blo 1372005 4633253 := bbase (se 4 (by rfl) ⟨434367, by rfl⟩ : syracuseStep 4633253 = 868735) (by norm_num)
theorem B1544881 : Blo 1372005 1544881 := bbase (se 2 (by rfl) ⟨579330, by rfl⟩ : syracuseStep 1544881 = 1158661) (by norm_num)
theorem B5214901 : Blo 1372005 5214901 := bbase (se 5 (by rfl) ⟨244448, by rfl⟩ : syracuseStep 5214901 = 488897) (by norm_num)
theorem B2060981 : Blo 1372005 2060981 := bbase (se 5 (by rfl) ⟨96608, by rfl⟩ : syracuseStep 2060981 = 193217) (by norm_num)
theorem B2061005 : Blo 1372005 2061005 := bbase (se 3 (by rfl) ⟨386438, by rfl⟩ : syracuseStep 2061005 = 772877) (by norm_num)
theorem B1544917 : Blo 1372005 1544917 := bbase (se 7 (by rfl) ⟨18104, by rfl⟩ : syracuseStep 1544917 = 36209) (by norm_num)
theorem B1544953 : Blo 1372005 1544953 := bbase (se 2 (by rfl) ⟨579357, by rfl⟩ : syracuseStep 1544953 = 1158715) (by norm_num)
theorem B1544989 : Blo 1372005 1544989 := bbase (se 3 (by rfl) ⟨289685, by rfl⟩ : syracuseStep 1544989 = 579371) (by norm_num)
theorem B1545025 : Blo 1372005 1545025 := bbase (se 2 (by rfl) ⟨579384, by rfl⟩ : syracuseStep 1545025 = 1158769) (by norm_num)
theorem B3912533 : Blo 1372005 3912533 := bbase (se 9 (by rfl) ⟨11462, by rfl⟩ : syracuseStep 3912533 = 22925) (by norm_num)
theorem B1545061 : Blo 1372005 1545061 := bbase (se 4 (by rfl) ⟨144849, by rfl⟩ : syracuseStep 1545061 = 289699) (by norm_num)
theorem B1545097 : Blo 1372005 1545097 := bbase (se 2 (by rfl) ⟨579411, by rfl⟩ : syracuseStep 1545097 = 1158823) (by norm_num)
theorem B1545133 : Blo 1372005 1545133 := bbase (se 3 (by rfl) ⟨289712, by rfl⟩ : syracuseStep 1545133 = 579425) (by norm_num)
theorem B4395973 : Blo 1372005 4395973 := bbase (se 4 (by rfl) ⟨412122, by rfl⟩ : syracuseStep 4395973 = 824245) (by norm_num)
theorem B1545169 : Blo 1372005 1545169 := bbase (se 2 (by rfl) ⟨579438, by rfl⟩ : syracuseStep 1545169 = 1158877) (by norm_num)
theorem B5215205 : Blo 1372005 5215205 := bbase (se 4 (by rfl) ⟨488925, by rfl⟩ : syracuseStep 5215205 = 977851) (by norm_num)
theorem B1545205 : Blo 1372005 1545205 := bbase (se 5 (by rfl) ⟨72431, by rfl⟩ : syracuseStep 1545205 = 144863) (by norm_num)
theorem B1545241 : Blo 1372005 1545241 := bbase (se 2 (by rfl) ⟨579465, by rfl⟩ : syracuseStep 1545241 = 1158931) (by norm_num)
theorem B2315317 : Blo 1372005 2315317 := bbase (se 5 (by rfl) ⟨108530, by rfl⟩ : syracuseStep 2315317 = 217061) (by norm_num)
theorem B1545277 : Blo 1372005 1545277 := bbase (se 3 (by rfl) ⟨289739, by rfl⟩ : syracuseStep 1545277 = 579479) (by norm_num)
theorem B4633685 : Blo 1372005 4633685 := bbase (se 8 (by rfl) ⟨27150, by rfl⟩ : syracuseStep 4633685 = 54301) (by norm_num)
theorem B1545313 : Blo 1372005 1545313 := bbase (se 2 (by rfl) ⟨579492, by rfl⟩ : syracuseStep 1545313 = 1158985) (by norm_num)
theorem B1545349 : Blo 1372005 1545349 := bbase (se 4 (by rfl) ⟨144876, by rfl⟩ : syracuseStep 1545349 = 289753) (by norm_num)
theorem B2315405 : Blo 1372005 2315405 := bbase (se 3 (by rfl) ⟨434138, by rfl⟩ : syracuseStep 2315405 = 868277) (by norm_num)
theorem B1954973 : Blo 1372005 1954973 := bbase (se 3 (by rfl) ⟨366557, by rfl⟩ : syracuseStep 1954973 = 733115) (by norm_num)
theorem B1545385 : Blo 1372005 1545385 := bbase (se 2 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 1545385 = 1159039) (by norm_num)
theorem B1742029 : Blo 1372005 1742029 := bbase (se 3 (by rfl) ⟨326630, by rfl⟩ : syracuseStep 1742029 = 653261) (by norm_num)
theorem B1545421 : Blo 1372005 1545421 := bbase (se 3 (by rfl) ⟨289766, by rfl⟩ : syracuseStep 1545421 = 579533) (by norm_num)
theorem B1955053 : Blo 1372005 1955053 := bbase (se 3 (by rfl) ⟨366572, by rfl⟩ : syracuseStep 1955053 = 733145) (by norm_num)
theorem B1545457 : Blo 1372005 1545457 := bbase (se 2 (by rfl) ⟨579546, by rfl⟩ : syracuseStep 1545457 = 1159093) (by norm_num)
theorem B2315533 : Blo 1372005 2315533 := bbase (se 3 (by rfl) ⟨434162, by rfl⟩ : syracuseStep 2315533 = 868325) (by norm_num)
theorem B1545493 : Blo 1372005 1545493 := bbase (se 6 (by rfl) ⟨36222, by rfl⟩ : syracuseStep 1545493 = 72445) (by norm_num)
theorem B6952229 : Blo 1372005 6952229 := bbase (se 4 (by rfl) ⟨651771, by rfl⟩ : syracuseStep 6952229 = 1303543) (by norm_num)
theorem B1545529 : Blo 1372005 1545529 := bbase (se 2 (by rfl) ⟨579573, by rfl⟩ : syracuseStep 1545529 = 1159147) (by norm_num)
theorem B17593685 : Blo 1372005 17593685 := bbase (se 13 (by rfl) ⟨3221, by rfl⟩ : syracuseStep 17593685 = 6443) (by norm_num)
theorem B1545565 : Blo 1372005 1545565 := bbase (se 3 (by rfl) ⟨289793, by rfl⟩ : syracuseStep 1545565 = 579587) (by norm_num)
theorem B2315621 : Blo 1372005 2315621 := bbase (se 4 (by rfl) ⟨217089, by rfl⟩ : syracuseStep 2315621 = 434179) (by norm_num)
theorem B1955173 : Blo 1372005 1955173 := bbase (se 4 (by rfl) ⟨183297, by rfl⟩ : syracuseStep 1955173 = 366595) (by norm_num)
theorem B1545601 : Blo 1372005 1545601 := bbase (se 2 (by rfl) ⟨579600, by rfl⟩ : syracuseStep 1545601 = 1159201) (by norm_num)
theorem B13202837 : Blo 1372005 13202837 := bbase (se 6 (by rfl) ⟨309441, by rfl⟩ : syracuseStep 13202837 = 618883) (by norm_num)
theorem B1545637 : Blo 1372005 1545637 := bbase (se 4 (by rfl) ⟨144903, by rfl⟩ : syracuseStep 1545637 = 289807) (by norm_num)
theorem B1955269 : Blo 1372005 1955269 := bbase (se 4 (by rfl) ⟨183306, by rfl⟩ : syracuseStep 1955269 = 366613) (by norm_num)
theorem B1545673 : Blo 1372005 1545673 := bbase (se 2 (by rfl) ⟨579627, by rfl⟩ : syracuseStep 1545673 = 1159255) (by norm_num)
theorem B2315749 : Blo 1372005 2315749 := bbase (se 4 (by rfl) ⟨217101, by rfl⟩ : syracuseStep 2315749 = 434203) (by norm_num)
theorem B1545709 : Blo 1372005 1545709 := bbase (se 3 (by rfl) ⟨289820, by rfl⟩ : syracuseStep 1545709 = 579641) (by norm_num)
theorem B4634117 : Blo 1372005 4634117 := bbase (se 4 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 4634117 = 868897) (by norm_num)
theorem B1545745 : Blo 1372005 1545745 := bbase (se 2 (by rfl) ⟨579654, by rfl⟩ : syracuseStep 1545745 = 1159309) (by norm_num)
theorem B2315837 : Blo 1372005 2315837 := bbase (se 3 (by rfl) ⟨434219, by rfl⟩ : syracuseStep 2315837 = 868439) (by norm_num)
theorem B3176101 : Blo 1372005 3176101 := bbase (se 4 (by rfl) ⟨297759, by rfl⟩ : syracuseStep 3176101 = 595519) (by norm_num)
theorem B2315965 : Blo 1372005 2315965 := bbase (se 3 (by rfl) ⟨434243, by rfl⟩ : syracuseStep 2315965 = 868487) (by norm_num)
theorem B3708629 : Blo 1372005 3708629 := bbase (se 7 (by rfl) ⟨43460, by rfl⟩ : syracuseStep 3708629 = 86921) (by norm_num)
theorem B2316053 : Blo 1372005 2316053 := bbase (se 6 (by rfl) ⟨54282, by rfl⟩ : syracuseStep 2316053 = 108565) (by norm_num)
theorem B3708757 : Blo 1372005 3708757 := bbase (se 9 (by rfl) ⟨10865, by rfl⟩ : syracuseStep 3708757 = 21731) (by norm_num)
theorem B2930573 : Blo 1372005 2930573 := bbase (se 3 (by rfl) ⟨549482, by rfl⟩ : syracuseStep 2930573 = 1098965) (by norm_num)
theorem B2783117 : Blo 1372005 2783117 := bbase (se 3 (by rfl) ⟨521834, by rfl⟩ : syracuseStep 2783117 = 1043669) (by norm_num)
theorem B2316181 : Blo 1372005 2316181 := bbase (se 6 (by rfl) ⟨54285, by rfl⟩ : syracuseStep 2316181 = 108571) (by norm_num)
theorem B2381717 : Blo 1372005 2381717 := bbase (se 6 (by rfl) ⟨55821, by rfl⟩ : syracuseStep 2381717 = 111643) (by norm_num)
theorem B4634549 : Blo 1372005 4634549 := bbase (se 5 (by rfl) ⟨217244, by rfl⟩ : syracuseStep 4634549 = 434489) (by norm_num)
theorem B1955765 : Blo 1372005 1955765 := bbase (se 5 (by rfl) ⟨91676, by rfl⟩ : syracuseStep 1955765 = 183353) (by norm_num)
theorem B2316269 : Blo 1372005 2316269 := bbase (se 3 (by rfl) ⟨434300, by rfl⟩ : syracuseStep 2316269 = 868601) (by norm_num)
theorem B2930717 : Blo 1372005 2930717 := bbase (se 3 (by rfl) ⟨549509, by rfl⟩ : syracuseStep 2930717 = 1099019) (by norm_num)
theorem B3012637 : Blo 1372005 3012637 := bbase (se 3 (by rfl) ⟨564869, by rfl⟩ : syracuseStep 3012637 = 1129739) (by norm_num)
theorem B2316397 : Blo 1372005 2316397 := bbase (se 3 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 2316397 = 868649) (by norm_num)
theorem B3709093 : Blo 1372005 3709093 := bbase (se 4 (by rfl) ⟨347727, by rfl⟩ : syracuseStep 3709093 = 695455) (by norm_num)
theorem B2316485 : Blo 1372005 2316485 := bbase (se 4 (by rfl) ⟨217170, by rfl⟩ : syracuseStep 2316485 = 434341) (by norm_num)
theorem B2316613 : Blo 1372005 2316613 := bbase (se 4 (by rfl) ⟨217182, by rfl⟩ : syracuseStep 2316613 = 434365) (by norm_num)
theorem B4634981 : Blo 1372005 4634981 := bbase (se 4 (by rfl) ⟨434529, by rfl⟩ : syracuseStep 4634981 = 869059) (by norm_num)
theorem B11737493 : Blo 1372005 11737493 := bbase (se 6 (by rfl) ⟨275097, by rfl⟩ : syracuseStep 11737493 = 550195) (by norm_num)
theorem B2316701 : Blo 1372005 2316701 := bbase (se 3 (by rfl) ⟨434381, by rfl⟩ : syracuseStep 2316701 = 868763) (by norm_num)
theorem B1956317 : Blo 1372005 1956317 := bbase (se 3 (by rfl) ⟨366809, by rfl⟩ : syracuseStep 1956317 = 733619) (by norm_num)
theorem B4946453 : Blo 1372005 4946453 := bbase (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) (by norm_num)
theorem B2316829 : Blo 1372005 2316829 := bbase (se 3 (by rfl) ⟨434405, by rfl⟩ : syracuseStep 2316829 = 868811) (by norm_num)
theorem B1391137 : Blo 1372005 1391137 := bbase (se 2 (by rfl) ⟨521676, by rfl⟩ : syracuseStep 1391137 = 1043353) (by norm_num)
theorem B1391141 : Blo 1372005 1391141 := bbase (se 4 (by rfl) ⟨130419, by rfl⟩ : syracuseStep 1391141 = 260839) (by norm_num)
theorem B6953525 : Blo 1372005 6953525 := bbase (se 5 (by rfl) ⟨325946, by rfl⟩ : syracuseStep 6953525 = 651893) (by norm_num)
theorem B2316917 : Blo 1372005 2316917 := bbase (se 5 (by rfl) ⟨108605, by rfl⟩ : syracuseStep 2316917 = 217211) (by norm_num)
theorem B1694353 : Blo 1372005 1694353 := bbase (se 2 (by rfl) ⟨635382, by rfl⟩ : syracuseStep 1694353 = 1270765) (by norm_num)
theorem B3087053 : Blo 1372005 3087053 := bbase (se 3 (by rfl) ⟨578822, by rfl⟩ : syracuseStep 3087053 = 1157645) (by norm_num)
theorem B2317045 : Blo 1372005 2317045 := bbase (se 5 (by rfl) ⟨108611, by rfl⟩ : syracuseStep 2317045 = 217223) (by norm_num)
theorem B3521285 : Blo 1372005 3521285 := bbase (se 4 (by rfl) ⟨330120, by rfl⟩ : syracuseStep 3521285 = 660241) (by norm_num)
theorem B2931461 : Blo 1372005 2931461 := bbase (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) (by norm_num)
theorem B3087125 : Blo 1372005 3087125 := bbase (se 6 (by rfl) ⟨72354, by rfl⟩ : syracuseStep 3087125 = 144709) (by norm_num)
theorem B4635413 : Blo 1372005 4635413 := bbase (se 6 (by rfl) ⟨108642, by rfl⟩ : syracuseStep 4635413 = 217285) (by norm_num)
theorem B2317133 : Blo 1372005 2317133 := bbase (se 3 (by rfl) ⟨434462, by rfl⟩ : syracuseStep 2317133 = 868925) (by norm_num)
theorem B39615317 : Blo 1372005 39615317 := bbase (se 9 (by rfl) ⟨116060, by rfl⟩ : syracuseStep 39615317 = 232121) (by norm_num)
theorem B3087197 : Blo 1372005 3087197 := bbase (se 3 (by rfl) ⟨578849, by rfl⟩ : syracuseStep 3087197 = 1157699) (by norm_num)
theorem B1809289 : Blo 1372005 1809289 := bbase (se 2 (by rfl) ⟨678483, by rfl⟩ : syracuseStep 1809289 = 1356967) (by norm_num)
theorem B3087269 : Blo 1372005 3087269 := bbase (se 4 (by rfl) ⟨289431, by rfl⟩ : syracuseStep 3087269 = 578863) (by norm_num)
theorem B1465273 : Blo 1372005 1465273 := bbase (se 2 (by rfl) ⟨549477, by rfl⟩ : syracuseStep 1465273 = 1098955) (by norm_num)
theorem B2317261 : Blo 1372005 2317261 := bbase (se 3 (by rfl) ⟨434486, by rfl⟩ : syracuseStep 2317261 = 868973) (by norm_num)
theorem B3087341 : Blo 1372005 3087341 := bbase (se 3 (by rfl) ⟨578876, by rfl⟩ : syracuseStep 3087341 = 1157753) (by norm_num)
theorem B21134357 : Blo 1372005 21134357 := bbase (se 6 (by rfl) ⟨495336, by rfl⟩ : syracuseStep 21134357 = 990673) (by norm_num)
theorem B2317349 : Blo 1372005 2317349 := bbase (se 4 (by rfl) ⟨217251, by rfl⟩ : syracuseStep 2317349 = 434503) (by norm_num)
theorem B3087413 : Blo 1372005 3087413 := bbase (se 5 (by rfl) ⟨144722, by rfl⟩ : syracuseStep 3087413 = 289445) (by norm_num)
theorem B2088037 : Blo 1372005 2088037 := bbase (se 4 (by rfl) ⟨195753, by rfl⟩ : syracuseStep 2088037 = 391507) (by norm_num)
theorem B1465457 : Blo 1372005 1465457 := bbase (se 2 (by rfl) ⟨549546, by rfl⟩ : syracuseStep 1465457 = 1099093) (by norm_num)
theorem B3087485 : Blo 1372005 3087485 := bbase (se 3 (by rfl) ⟨578903, by rfl⟩ : syracuseStep 3087485 = 1157807) (by norm_num)
theorem B6347909 : Blo 1372005 6347909 := bbase (se 4 (by rfl) ⟨595116, by rfl⟩ : syracuseStep 6347909 = 1190233) (by norm_num)
theorem B1391765 : Blo 1372005 1391765 := bbase (se 6 (by rfl) ⟨32619, by rfl⟩ : syracuseStep 1391765 = 65239) (by norm_num)
theorem B2317477 : Blo 1372005 2317477 := bbase (se 4 (by rfl) ⟨217263, by rfl⟩ : syracuseStep 2317477 = 434527) (by norm_num)
theorem B3300517 : Blo 1372005 3300517 := bbase (se 4 (by rfl) ⟨309423, by rfl⟩ : syracuseStep 3300517 = 618847) (by norm_num)
theorem B3087557 : Blo 1372005 3087557 := bbase (se 4 (by rfl) ⟨289458, by rfl⟩ : syracuseStep 3087557 = 578917) (by norm_num)
theorem B4635845 : Blo 1372005 4635845 := bbase (se 4 (by rfl) ⟨434610, by rfl⟩ : syracuseStep 4635845 = 869221) (by norm_num)
theorem B1981669 : Blo 1372005 1981669 := bbase (se 4 (by rfl) ⟨185781, by rfl⟩ : syracuseStep 1981669 = 371563) (by norm_num)
theorem B2317565 : Blo 1372005 2317565 := bbase (se 3 (by rfl) ⟨434543, by rfl⟩ : syracuseStep 2317565 = 869087) (by norm_num)
theorem B3087629 : Blo 1372005 3087629 := bbase (se 3 (by rfl) ⟨578930, by rfl⟩ : syracuseStep 3087629 = 1157861) (by norm_num)
theorem B3087701 : Blo 1372005 3087701 := bbase (se 11 (by rfl) ⟨2261, by rfl⟩ : syracuseStep 3087701 = 4523) (by norm_num)
theorem B25058645 : Blo 1372005 25058645 := bbase (se 11 (by rfl) ⟨18353, by rfl⟩ : syracuseStep 25058645 = 36707) (by norm_num)
theorem B4947317 : Blo 1372005 4947317 := bbase (se 5 (by rfl) ⟨231905, by rfl⟩ : syracuseStep 4947317 = 463811) (by norm_num)
theorem B2317693 : Blo 1372005 2317693 := bbase (se 3 (by rfl) ⟨434567, by rfl⟩ : syracuseStep 2317693 = 869135) (by norm_num)
theorem B1392013 : Blo 1372005 1392013 := bbase (se 3 (by rfl) ⟨261002, by rfl⟩ : syracuseStep 1392013 = 522005) (by norm_num)
theorem B3087773 : Blo 1372005 3087773 := bbase (se 3 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 3087773 = 1157915) (by norm_num)
theorem B1392049 : Blo 1372005 1392049 := bbase (se 2 (by rfl) ⟨522018, by rfl⟩ : syracuseStep 1392049 = 1044037) (by norm_num)
theorem B5209541 : Blo 1372005 5209541 := bbase (se 4 (by rfl) ⟨488394, by rfl⟩ : syracuseStep 5209541 = 976789) (by norm_num)
theorem B2317781 : Blo 1372005 2317781 := bbase (se 7 (by rfl) ⟨27161, by rfl⟩ : syracuseStep 2317781 = 54323) (by norm_num)
theorem B3087845 : Blo 1372005 3087845 := bbase (se 4 (by rfl) ⟨289485, by rfl⟩ : syracuseStep 3087845 = 578971) (by norm_num)
theorem B2932213 : Blo 1372005 2932213 := bbase (se 5 (by rfl) ⟨137447, by rfl⟩ : syracuseStep 2932213 = 274895) (by norm_num)
theorem B3087917 : Blo 1372005 3087917 := bbase (se 3 (by rfl) ⟨578984, by rfl⟩ : syracuseStep 3087917 = 1157969) (by norm_num)
theorem B2317909 : Blo 1372005 2317909 := bbase (se 8 (by rfl) ⟨13581, by rfl⟩ : syracuseStep 2317909 = 27163) (by norm_num)
theorem B1760869 : Blo 1372005 1760869 := bbase (se 4 (by rfl) ⟨165081, by rfl⟩ : syracuseStep 1760869 = 330163) (by norm_num)
theorem B3087989 : Blo 1372005 3087989 := bbase (se 5 (by rfl) ⟨144749, by rfl⟩ : syracuseStep 3087989 = 289499) (by norm_num)
theorem B4636277 : Blo 1372005 4636277 := bbase (se 5 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 4636277 = 434651) (by norm_num)
theorem B2932357 : Blo 1372005 2932357 := bbase (se 4 (by rfl) ⟨274908, by rfl⟩ : syracuseStep 2932357 = 549817) (by norm_num)
theorem B4947605 : Blo 1372005 4947605 := bbase (se 6 (by rfl) ⟨115959, by rfl⟩ : syracuseStep 4947605 = 231919) (by norm_num)
theorem B2317997 : Blo 1372005 2317997 := bbase (se 3 (by rfl) ⟨434624, by rfl⟩ : syracuseStep 2317997 = 869249) (by norm_num)
theorem B3473077 : Blo 1372005 3473077 := bbase (se 5 (by rfl) ⟨162800, by rfl⟩ : syracuseStep 3473077 = 325601) (by norm_num)
theorem B3342005 : Blo 1372005 3342005 := bbase (se 5 (by rfl) ⟨156656, by rfl⟩ : syracuseStep 3342005 = 313313) (by norm_num)
theorem B3088061 : Blo 1372005 3088061 := bbase (se 3 (by rfl) ⟨579011, by rfl⟩ : syracuseStep 3088061 = 1158023) (by norm_num)
theorem B5209829 : Blo 1372005 5209829 := bbase (se 4 (by rfl) ⟨488421, by rfl⟩ : syracuseStep 5209829 = 976843) (by norm_num)
theorem B3088133 : Blo 1372005 3088133 := bbase (se 4 (by rfl) ⟨289512, by rfl⟩ : syracuseStep 3088133 = 579025) (by norm_num)
theorem B3907349 : Blo 1372005 3907349 := bbase (se 6 (by rfl) ⟨91578, by rfl⟩ : syracuseStep 3907349 = 183157) (by norm_num)
theorem B1736473 : Blo 1372005 1736473 := bbase (se 2 (by rfl) ⟨651177, by rfl⟩ : syracuseStep 1736473 = 1302355) (by norm_num)
theorem B3473189 : Blo 1372005 3473189 := bbase (se 4 (by rfl) ⟨325611, by rfl⟩ : syracuseStep 3473189 = 651223) (by norm_num)
theorem B2318125 : Blo 1372005 2318125 := bbase (se 3 (by rfl) ⟨434648, by rfl⟩ : syracuseStep 2318125 = 869297) (by norm_num)
theorem B11280181 : Blo 1372005 11280181 := bbase (se 5 (by rfl) ⟨528758, by rfl⟩ : syracuseStep 11280181 = 1057517) (by norm_num)
theorem B2604869 : Blo 1372005 2604869 := bbase (se 4 (by rfl) ⟨244206, by rfl⟩ : syracuseStep 2604869 = 488413) (by norm_num)
theorem B6954821 : Blo 1372005 6954821 := bbase (se 4 (by rfl) ⟨652014, by rfl⟩ : syracuseStep 6954821 = 1304029) (by norm_num)
theorem B3088205 : Blo 1372005 3088205 := bbase (se 3 (by rfl) ⟨579038, by rfl⟩ : syracuseStep 3088205 = 1158077) (by norm_num)
theorem B1466209 : Blo 1372005 1466209 := bbase (se 2 (by rfl) ⟨549828, by rfl⟩ : syracuseStep 1466209 = 1099657) (by norm_num)
theorem B1736569 : Blo 1372005 1736569 := bbase (se 2 (by rfl) ⟨651213, by rfl⟩ : syracuseStep 1736569 = 1302427) (by norm_num)
theorem B2318213 : Blo 1372005 2318213 := bbase (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) (by norm_num)
theorem B3088277 : Blo 1372005 3088277 := bbase (se 6 (by rfl) ⟨72381, by rfl⟩ : syracuseStep 3088277 = 144763) (by norm_num)
theorem B1466281 : Blo 1372005 1466281 := bbase (se 2 (by rfl) ⟨549855, by rfl⟩ : syracuseStep 1466281 = 1099711) (by norm_num)
theorem B3088349 : Blo 1372005 3088349 := bbase (se 3 (by rfl) ⟨579065, by rfl⟩ : syracuseStep 3088349 = 1158131) (by norm_num)
theorem B3473381 : Blo 1372005 3473381 := bbase (se 4 (by rfl) ⟨325629, by rfl⟩ : syracuseStep 3473381 = 651259) (by norm_num)
theorem B2228197 : Blo 1372005 2228197 := bbase (se 4 (by rfl) ⟨208893, by rfl⟩ : syracuseStep 2228197 = 417787) (by norm_num)
theorem B2932733 : Blo 1372005 2932733 := bbase (se 3 (by rfl) ⟨549887, by rfl⟩ : syracuseStep 2932733 = 1099775) (by norm_num)
theorem B1466435 : Blo 1372005 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B2318449 : Blo 1372005 2318449 := bstep (se 2 (by rfl) ⟨869418, by rfl⟩ : syracuseStep 2318449 = 1738837) B1738837
theorem B3088529 : Blo 1372005 3088529 := bstep (se 2 (by rfl) ⟨1158198, by rfl⟩ : syracuseStep 3088529 = 2316397) B2316397
theorem B4636817 : Blo 1372005 4636817 := bstep (se 2 (by rfl) ⟨1738806, by rfl⟩ : syracuseStep 4636817 = 3477613) B3477613
theorem B2318483 : Blo 1372005 2318483 := bstep (se 1 (by rfl) ⟨1738862, by rfl⟩ : syracuseStep 2318483 = 3477725) B3477725
theorem B3088547 : Blo 1372005 3088547 := bstep (se 1 (by rfl) ⟨2316410, by rfl⟩ : syracuseStep 3088547 = 4632821) B4632821
theorem B7823537 : Blo 1372005 7823537 := bstep (se 2 (by rfl) ⟨2933826, by rfl⟩ : syracuseStep 7823537 = 5867653) B5867653
theorem B7921925 : Blo 1372005 7921925 := bstep (se 4 (by rfl) ⟨742680, by rfl⟩ : syracuseStep 7921925 = 1485361) B1485361
theorem B2318611 : Blo 1372005 2318611 := bstep (se 1 (by rfl) ⟨1738958, by rfl⟩ : syracuseStep 2318611 = 3477917) B3477917
theorem B3907885 : Blo 1372005 3907885 := bstep (se 3 (by rfl) ⟨732728, by rfl⟩ : syracuseStep 3907885 = 1465457) B1465457
theorem B7815473 : Blo 1372005 7815473 := bstep (se 2 (by rfl) ⟨2930802, by rfl⟩ : syracuseStep 7815473 = 5861605) B5861605
theorem B3088817 : Blo 1372005 3088817 := bstep (se 2 (by rfl) ⟨1158306, by rfl⟩ : syracuseStep 3088817 = 2316613) B2316613
theorem B3088835 : Blo 1372005 3088835 := bstep (se 1 (by rfl) ⟨2316626, by rfl⟩ : syracuseStep 3088835 = 4633253) B4633253
theorem B6955469 : Blo 1372005 6955469 := bstep (se 3 (by rfl) ⟨1304150, by rfl⟩ : syracuseStep 6955469 = 2608301) B2608301
theorem B1737283 : Blo 1372005 1737283 := bstep (se 1 (by rfl) ⟨1302962, by rfl⟩ : syracuseStep 1737283 = 2605925) B2605925
theorem B1737379 : Blo 1372005 1737379 := bstep (se 1 (by rfl) ⟨1303034, by rfl⟩ : syracuseStep 1737379 = 2606069) B2606069
theorem B5210801 : Blo 1372005 5210801 := bstep (se 2 (by rfl) ⟨1954050, by rfl⟩ : syracuseStep 5210801 = 3908101) B3908101
theorem B1671859 : Blo 1372005 1671859 := bstep (se 1 (by rfl) ⟨1253894, by rfl⟩ : syracuseStep 1671859 = 2507789) B2507789
theorem B3089105 : Blo 1372005 3089105 := bstep (se 2 (by rfl) ⟨1158414, by rfl⟩ : syracuseStep 3089105 = 2316829) B2316829
theorem B2228963 : Blo 1372005 2228963 := bstep (se 1 (by rfl) ⟨1671722, by rfl⟩ : syracuseStep 2228963 = 3343445) B3343445
theorem B3089123 : Blo 1372005 3089123 := bstep (se 1 (by rfl) ⟨2316842, by rfl⟩ : syracuseStep 3089123 = 4633685) B4633685
theorem B3474161 : Blo 1372005 3474161 := bstep (se 2 (by rfl) ⟨1302810, by rfl⟩ : syracuseStep 3474161 = 2605621) B2605621
theorem B5866253 : Blo 1372005 5866253 := bstep (se 3 (by rfl) ⟨1099922, by rfl⟩ : syracuseStep 5866253 = 2199845) B2199845
theorem B2605841 : Blo 1372005 2605841 := bstep (se 2 (by rfl) ⟨977190, by rfl⟩ : syracuseStep 2605841 = 1954381) B1954381
theorem B3474211 : Blo 1372005 3474211 := bstep (se 1 (by rfl) ⟨2605658, by rfl⟩ : syracuseStep 3474211 = 5211317) B5211317
theorem B15631217 : Blo 1372005 15631217 := bstep (se 2 (by rfl) ⟨5861706, by rfl⟩ : syracuseStep 15631217 = 11723413) B11723413
theorem B3474353 : Blo 1372005 3474353 := bstep (se 2 (by rfl) ⟨1302882, by rfl⟩ : syracuseStep 3474353 = 2605765) B2605765
theorem B3089393 : Blo 1372005 3089393 := bstep (se 2 (by rfl) ⟨1158522, by rfl⟩ : syracuseStep 3089393 = 2317045) B2317045
theorem B3089411 : Blo 1372005 3089411 := bstep (se 1 (by rfl) ⟨2317058, by rfl⟩ : syracuseStep 3089411 = 4634117) B4634117
theorem B27124789 : Blo 1372005 27124789 := bstep (se 5 (by rfl) ⟨1271474, by rfl⟩ : syracuseStep 27124789 = 2542949) B2542949
theorem B9290821 : Blo 1372005 9290821 := bstep (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) B1742029
theorem B1737875 : Blo 1372005 1737875 := bstep (se 1 (by rfl) ⟨1303406, by rfl⟩ : syracuseStep 1737875 = 2606813) B2606813
theorem B6948017 : Blo 1372005 6948017 := bstep (se 2 (by rfl) ⟨2605506, by rfl⟩ : syracuseStep 6948017 = 5211013) B5211013
theorem B5358797 : Blo 1372005 5358797 := bstep (se 3 (by rfl) ⟨1004774, by rfl⟩ : syracuseStep 5358797 = 2009549) B2009549
theorem B3089681 : Blo 1372005 3089681 := bstep (se 2 (by rfl) ⟨1158630, by rfl⟩ : syracuseStep 3089681 = 2317261) B2317261
theorem B3089699 : Blo 1372005 3089699 := bstep (se 1 (by rfl) ⟨2317274, by rfl⟩ : syracuseStep 3089699 = 4634549) B4634549
theorem B2934083 : Blo 1372005 2934083 := bstep (se 1 (by rfl) ⟨2200562, by rfl⟩ : syracuseStep 2934083 = 4401125) B4401125
theorem B4457809 : Blo 1372005 4457809 := bstep (se 2 (by rfl) ⟨1671678, by rfl⟩ : syracuseStep 4457809 = 3343357) B3343357
theorem B3089969 : Blo 1372005 3089969 := bstep (se 2 (by rfl) ⟨1158738, by rfl⟩ : syracuseStep 3089969 = 2317477) B2317477
theorem B4400689 : Blo 1372005 4400689 := bstep (se 2 (by rfl) ⟨1650258, by rfl⟩ : syracuseStep 4400689 = 3300517) B3300517
theorem B14845493 : Blo 1372005 14845493 := bstep (se 5 (by rfl) ⟨695882, by rfl⟩ : syracuseStep 14845493 = 1391765) B1391765
theorem B3089987 : Blo 1372005 3089987 := bstep (se 1 (by rfl) ⟨2317490, by rfl⟩ : syracuseStep 3089987 = 4634981) B4634981
theorem B7824995 : Blo 1372005 7824995 := bstep (se 1 (by rfl) ⟨5868746, by rfl⟩ : syracuseStep 7824995 = 11737493) B11737493
theorem B2606737 : Blo 1372005 2606737 := bstep (se 2 (by rfl) ⟨977526, by rfl⟩ : syracuseStep 2606737 = 1955053) B1955053
theorem B8799941 : Blo 1372005 8799941 := bstep (se 4 (by rfl) ⟨824994, by rfl⟩ : syracuseStep 8799941 = 1649989) B1649989
theorem B7816931 : Blo 1372005 7816931 := bstep (se 1 (by rfl) ⟨5862698, by rfl⟩ : syracuseStep 7816931 = 11725397) B11725397
theorem B2058017 : Blo 1372005 2058017 := bstep (se 2 (by rfl) ⟨771756, by rfl⟩ : syracuseStep 2058017 = 1543513) B1543513
theorem B2606897 : Blo 1372005 2606897 := bstep (se 2 (by rfl) ⟨977586, by rfl⟩ : syracuseStep 2606897 = 1955173) B1955173
theorem B2058035 : Blo 1372005 2058035 := bstep (se 1 (by rfl) ⟨1543526, by rfl⟩ : syracuseStep 2058035 = 3087053) B3087053
theorem B2058065 : Blo 1372005 2058065 := bstep (se 2 (by rfl) ⟨771774, by rfl⟩ : syracuseStep 2058065 = 1543549) B1543549
theorem B3090257 : Blo 1372005 3090257 := bstep (se 2 (by rfl) ⟨1158846, by rfl⟩ : syracuseStep 3090257 = 2317693) B2317693
theorem B1738579 : Blo 1372005 1738579 := bstep (se 1 (by rfl) ⟨1303934, by rfl⟩ : syracuseStep 1738579 = 2607869) B2607869
theorem B2058083 : Blo 1372005 2058083 := bstep (se 1 (by rfl) ⟨1543562, by rfl⟩ : syracuseStep 2058083 = 3087125) B3087125
theorem B3090275 : Blo 1372005 3090275 := bstep (se 1 (by rfl) ⟨2317706, by rfl⟩ : syracuseStep 3090275 = 4635413) B4635413
theorem B2058113 : Blo 1372005 2058113 := bstep (se 2 (by rfl) ⟨771792, by rfl⟩ : syracuseStep 2058113 = 1543585) B1543585
theorem B3475345 : Blo 1372005 3475345 := bstep (se 2 (by rfl) ⟨1303254, by rfl⟩ : syracuseStep 3475345 = 2606509) B2606509
theorem B2058131 : Blo 1372005 2058131 := bstep (se 1 (by rfl) ⟨1543598, by rfl⟩ : syracuseStep 2058131 = 3087197) B3087197
theorem B2058161 : Blo 1372005 2058161 := bstep (se 2 (by rfl) ⟨771810, by rfl⟩ : syracuseStep 2058161 = 1543621) B1543621
theorem B1738675 : Blo 1372005 1738675 := bstep (se 1 (by rfl) ⟨1304006, by rfl⟩ : syracuseStep 1738675 = 2608013) B2608013
theorem B2058179 : Blo 1372005 2058179 := bstep (se 1 (by rfl) ⟨1543634, by rfl⟩ : syracuseStep 2058179 = 3087269) B3087269
theorem B2058209 : Blo 1372005 2058209 := bstep (se 2 (by rfl) ⟨771828, by rfl⟩ : syracuseStep 2058209 = 1543657) B1543657
theorem B3909617 : Blo 1372005 3909617 := bstep (se 2 (by rfl) ⟨1466106, by rfl⟩ : syracuseStep 3909617 = 2932213) B2932213
theorem B2058227 : Blo 1372005 2058227 := bstep (se 1 (by rfl) ⟨1543670, by rfl⟩ : syracuseStep 2058227 = 3087341) B3087341
theorem B2058257 : Blo 1372005 2058257 := bstep (se 2 (by rfl) ⟨771846, by rfl⟩ : syracuseStep 2058257 = 1543693) B1543693
theorem B2058275 : Blo 1372005 2058275 := bstep (se 1 (by rfl) ⟨1543706, by rfl⟩ : syracuseStep 2058275 = 3087413) B3087413
theorem B2058305 : Blo 1372005 2058305 := bstep (se 2 (by rfl) ⟨771864, by rfl⟩ : syracuseStep 2058305 = 1543729) B1543729
theorem B2058323 : Blo 1372005 2058323 := bstep (se 1 (by rfl) ⟨1543742, by rfl⟩ : syracuseStep 2058323 = 3087485) B3087485
theorem B5212259 : Blo 1372005 5212259 := bstep (se 1 (by rfl) ⟨3909194, by rfl⟩ : syracuseStep 5212259 = 7818389) B7818389
theorem B2058353 : Blo 1372005 2058353 := bstep (se 2 (by rfl) ⟨771882, by rfl⟩ : syracuseStep 2058353 = 1543765) B1543765
theorem B3090545 : Blo 1372005 3090545 := bstep (se 2 (by rfl) ⟨1158954, by rfl⟩ : syracuseStep 3090545 = 2317909) B2317909
theorem B2058371 : Blo 1372005 2058371 := bstep (se 1 (by rfl) ⟨1543778, by rfl⟩ : syracuseStep 2058371 = 3087557) B3087557
theorem B3090563 : Blo 1372005 3090563 := bstep (se 1 (by rfl) ⟨2317922, by rfl⟩ : syracuseStep 3090563 = 4635845) B4635845
theorem B2058401 : Blo 1372005 2058401 := bstep (se 2 (by rfl) ⟨771900, by rfl⟩ : syracuseStep 2058401 = 1543801) B1543801
theorem B3475619 : Blo 1372005 3475619 := bstep (se 1 (by rfl) ⟨2606714, by rfl⟩ : syracuseStep 3475619 = 5213429) B5213429
theorem B3909809 : Blo 1372005 3909809 := bstep (se 2 (by rfl) ⟨1466178, by rfl⟩ : syracuseStep 3909809 = 2932357) B2932357
theorem B2058419 : Blo 1372005 2058419 := bstep (se 1 (by rfl) ⟨1543814, by rfl⟩ : syracuseStep 2058419 = 3087629) B3087629
theorem B2230465 : Blo 1372005 2230465 := bstep (se 2 (by rfl) ⟨836424, by rfl⟩ : syracuseStep 2230465 = 1672849) B1672849
theorem B2607299 : Blo 1372005 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B2058449 : Blo 1372005 2058449 := bstep (se 2 (by rfl) ⟨771918, by rfl⟩ : syracuseStep 2058449 = 1543837) B1543837
theorem B2058467 : Blo 1372005 2058467 := bstep (se 1 (by rfl) ⟨1543850, by rfl⟩ : syracuseStep 2058467 = 3087701) B3087701
theorem B16705763 : Blo 1372005 16705763 := bstep (se 1 (by rfl) ⟨12529322, by rfl⟩ : syracuseStep 16705763 = 25058645) B25058645
theorem B4630769 : Blo 1372005 4630769 := bstep (se 2 (by rfl) ⟨1736538, by rfl⟩ : syracuseStep 4630769 = 3473077) B3473077
theorem B2058497 : Blo 1372005 2058497 := bstep (se 2 (by rfl) ⟨771936, by rfl⟩ : syracuseStep 2058497 = 1543873) B1543873
theorem B8792333 : Blo 1372005 8792333 := bstep (se 3 (by rfl) ⟨1648562, by rfl⟩ : syracuseStep 8792333 = 3297125) B3297125
theorem B2058515 : Blo 1372005 2058515 := bstep (se 1 (by rfl) ⟨1543886, by rfl⟩ : syracuseStep 2058515 = 3087773) B3087773
theorem B2197795 : Blo 1372005 2197795 := bstep (se 1 (by rfl) ⟨1648346, by rfl⟩ : syracuseStep 2197795 = 3296693) B3296693
theorem B2058545 : Blo 1372005 2058545 := bstep (se 2 (by rfl) ⟨771954, by rfl⟩ : syracuseStep 2058545 = 1543909) B1543909
theorem B2058563 : Blo 1372005 2058563 := bstep (se 1 (by rfl) ⟨1543922, by rfl⟩ : syracuseStep 2058563 = 3087845) B3087845
theorem B2058593 : Blo 1372005 2058593 := bstep (se 2 (by rfl) ⟨771972, by rfl⟩ : syracuseStep 2058593 = 1543945) B1543945
theorem B3131747 : Blo 1372005 3131747 := bstep (se 1 (by rfl) ⟨2348810, by rfl⟩ : syracuseStep 3131747 = 4697621) B4697621
theorem B3475811 : Blo 1372005 3475811 := bstep (se 1 (by rfl) ⟨2606858, by rfl⟩ : syracuseStep 3475811 = 5213717) B5213717
theorem B2230625 : Blo 1372005 2230625 := bstep (se 2 (by rfl) ⟨836484, by rfl⟩ : syracuseStep 2230625 = 1672969) B1672969
theorem B2058611 : Blo 1372005 2058611 := bstep (se 1 (by rfl) ⟨1543958, by rfl⟩ : syracuseStep 2058611 = 3087917) B3087917
theorem B2058641 : Blo 1372005 2058641 := bstep (se 2 (by rfl) ⟨771990, by rfl⟩ : syracuseStep 2058641 = 1543981) B1543981
theorem B3090833 : Blo 1372005 3090833 := bstep (se 2 (by rfl) ⟨1159062, by rfl⟩ : syracuseStep 3090833 = 2318125) B2318125
theorem B2058659 : Blo 1372005 2058659 := bstep (se 1 (by rfl) ⟨1543994, by rfl⟩ : syracuseStep 2058659 = 3087989) B3087989
theorem B3090851 : Blo 1372005 3090851 := bstep (se 1 (by rfl) ⟨2318138, by rfl⟩ : syracuseStep 3090851 = 4636277) B4636277
theorem B2058689 : Blo 1372005 2058689 := bstep (se 2 (by rfl) ⟨772008, by rfl⟩ : syracuseStep 2058689 = 1544017) B1544017
theorem B2058707 : Blo 1372005 2058707 := bstep (se 1 (by rfl) ⟨1544030, by rfl⟩ : syracuseStep 2058707 = 3088061) B3088061
theorem B10422755 : Blo 1372005 10422755 := bstep (se 1 (by rfl) ⟨7817066, by rfl⟩ : syracuseStep 10422755 = 15634133) B15634133
theorem B2058737 : Blo 1372005 2058737 := bstep (se 2 (by rfl) ⟨772026, by rfl⟩ : syracuseStep 2058737 = 1544053) B1544053
theorem B2058755 : Blo 1372005 2058755 := bstep (se 1 (by rfl) ⟨1544066, by rfl⟩ : syracuseStep 2058755 = 3088133) B3088133
theorem B2058785 : Blo 1372005 2058785 := bstep (se 2 (by rfl) ⟨772044, by rfl⟩ : syracuseStep 2058785 = 1544089) B1544089
theorem B2058803 : Blo 1372005 2058803 := bstep (se 1 (by rfl) ⟨1544102, by rfl⟩ : syracuseStep 2058803 = 3088205) B3088205
theorem B28961333 : Blo 1372005 28961333 := bstep (se 5 (by rfl) ⟨1357562, by rfl⟩ : syracuseStep 28961333 = 2715125) B2715125
theorem B2058833 : Blo 1372005 2058833 := bstep (se 2 (by rfl) ⟨772062, by rfl⟩ : syracuseStep 2058833 = 1544125) B1544125
theorem B2058851 : Blo 1372005 2058851 := bstep (se 1 (by rfl) ⟨1544138, by rfl⟩ : syracuseStep 2058851 = 3088277) B3088277
theorem B6949475 : Blo 1372005 6949475 := bstep (se 1 (by rfl) ⟨5212106, by rfl⟩ : syracuseStep 6949475 = 10424213) B10424213
theorem B2058881 : Blo 1372005 2058881 := bstep (se 2 (by rfl) ⟨772080, by rfl⟩ : syracuseStep 2058881 = 1544161) B1544161
theorem B17836685 : Blo 1372005 17836685 := bstep (se 3 (by rfl) ⟨3344378, by rfl⟩ : syracuseStep 17836685 = 6688757) B6688757
theorem B2058899 : Blo 1372005 2058899 := bstep (se 1 (by rfl) ⟨1544174, by rfl⟩ : syracuseStep 2058899 = 3088349) B3088349
theorem B2058929 : Blo 1372005 2058929 := bstep (se 2 (by rfl) ⟨772098, by rfl⟩ : syracuseStep 2058929 = 1544197) B1544197
theorem B3091121 : Blo 1372005 3091121 := bstep (se 2 (by rfl) ⟨1159170, by rfl⟩ : syracuseStep 3091121 = 2318341) B2318341
theorem B2058947 : Blo 1372005 2058947 := bstep (se 1 (by rfl) ⟨1544210, by rfl⟩ : syracuseStep 2058947 = 3088421) B3088421
theorem B3091139 : Blo 1372005 3091139 := bstep (se 1 (by rfl) ⟨2318354, by rfl⟩ : syracuseStep 3091139 = 4636709) B4636709
theorem B4016849 : Blo 1372005 4016849 := bstep (se 2 (by rfl) ⟨1506318, by rfl⟩ : syracuseStep 4016849 = 3012637) B3012637
theorem B2058977 : Blo 1372005 2058977 := bstep (se 2 (by rfl) ⟨772116, by rfl⟩ : syracuseStep 2058977 = 1544233) B1544233
theorem B2198243 : Blo 1372005 2198243 := bstep (se 1 (by rfl) ⟨1648682, by rfl⟩ : syracuseStep 2198243 = 3297365) B3297365
theorem B2058995 : Blo 1372005 2058995 := bstep (se 1 (by rfl) ⟨1544246, by rfl⟩ : syracuseStep 2058995 = 3088493) B3088493
theorem B2509571 : Blo 1372005 2509571 := bstep (se 1 (by rfl) ⟨1882178, by rfl⟩ : syracuseStep 2509571 = 3764357) B3764357
theorem B4631309 : Blo 1372005 4631309 := bstep (se 3 (by rfl) ⟨868370, by rfl⟩ : syracuseStep 4631309 = 1736741) B1736741
theorem B2059025 : Blo 1372005 2059025 := bstep (se 2 (by rfl) ⟨772134, by rfl⟩ : syracuseStep 2059025 = 1544269) B1544269
theorem B2059043 : Blo 1372005 2059043 := bstep (se 1 (by rfl) ⟨1544282, by rfl⟩ : syracuseStep 2059043 = 3088565) B3088565
theorem B2059073 : Blo 1372005 2059073 := bstep (se 2 (by rfl) ⟨772152, by rfl⟩ : syracuseStep 2059073 = 1544305) B1544305
theorem B4631363 : Blo 1372005 4631363 := bstep (se 1 (by rfl) ⟨3473522, by rfl⟩ : syracuseStep 4631363 = 6947045) B6947045
theorem B2059091 : Blo 1372005 2059091 := bstep (se 1 (by rfl) ⟨1544318, by rfl⟩ : syracuseStep 2059091 = 3088637) B3088637
theorem B2059121 : Blo 1372005 2059121 := bstep (se 2 (by rfl) ⟨772170, by rfl⟩ : syracuseStep 2059121 = 1544341) B1544341
theorem B2059139 : Blo 1372005 2059139 := bstep (se 1 (by rfl) ⟨1544354, by rfl⟩ : syracuseStep 2059139 = 3088709) B3088709
theorem B2059169 : Blo 1372005 2059169 := bstep (se 2 (by rfl) ⟨772188, by rfl⟩ : syracuseStep 2059169 = 1544377) B1544377
theorem B2059187 : Blo 1372005 2059187 := bstep (se 1 (by rfl) ⟨1544390, by rfl⟩ : syracuseStep 2059187 = 3088781) B3088781
theorem B2059217 : Blo 1372005 2059217 := bstep (se 2 (by rfl) ⟨772206, by rfl⟩ : syracuseStep 2059217 = 1544413) B1544413
theorem B3091409 : Blo 1372005 3091409 := bstep (se 2 (by rfl) ⟨1159278, by rfl⟩ : syracuseStep 3091409 = 2318557) B2318557
theorem B2059235 : Blo 1372005 2059235 := bstep (se 1 (by rfl) ⟨1544426, by rfl⟩ : syracuseStep 2059235 = 3088853) B3088853
theorem B3091427 : Blo 1372005 3091427 := bstep (se 1 (by rfl) ⟨2318570, by rfl⟩ : syracuseStep 3091427 = 4637141) B4637141
theorem B2059265 : Blo 1372005 2059265 := bstep (se 2 (by rfl) ⟨772224, by rfl⟩ : syracuseStep 2059265 = 1544449) B1544449
theorem B16927757 : Blo 1372005 16927757 := bstep (se 3 (by rfl) ⟨3173954, by rfl⟩ : syracuseStep 16927757 = 6347909) B6347909
theorem B2059283 : Blo 1372005 2059283 := bstep (se 1 (by rfl) ⟨1544462, by rfl⟩ : syracuseStep 2059283 = 3088925) B3088925
theorem B2059313 : Blo 1372005 2059313 := bstep (se 2 (by rfl) ⟨772242, by rfl⟩ : syracuseStep 2059313 = 1544485) B1544485
theorem B2059331 : Blo 1372005 2059331 := bstep (se 1 (by rfl) ⟨1544498, by rfl⟩ : syracuseStep 2059331 = 3088997) B3088997
theorem B2608195 : Blo 1372005 2608195 := bstep (se 1 (by rfl) ⟨1956146, by rfl⟩ : syracuseStep 2608195 = 3912293) B3912293
theorem B5213261 : Blo 1372005 5213261 := bstep (se 3 (by rfl) ⟨977486, by rfl⟩ : syracuseStep 5213261 = 1954973) B1954973
theorem B4631633 : Blo 1372005 4631633 := bstep (se 2 (by rfl) ⟨1736862, by rfl⟩ : syracuseStep 4631633 = 3473725) B3473725
theorem B2059361 : Blo 1372005 2059361 := bstep (se 2 (by rfl) ⟨772260, by rfl⟩ : syracuseStep 2059361 = 1544521) B1544521
theorem B2059379 : Blo 1372005 2059379 := bstep (se 1 (by rfl) ⟨1544534, by rfl⟩ : syracuseStep 2059379 = 3089069) B3089069
theorem B2059409 : Blo 1372005 2059409 := bstep (se 2 (by rfl) ⟨772278, by rfl⟩ : syracuseStep 2059409 = 1544557) B1544557
theorem B3910801 : Blo 1372005 3910801 := bstep (se 2 (by rfl) ⟨1466550, by rfl⟩ : syracuseStep 3910801 = 2933101) B2933101
theorem B2059427 : Blo 1372005 2059427 := bstep (se 1 (by rfl) ⟨1544570, by rfl⟩ : syracuseStep 2059427 = 3089141) B3089141
theorem B2059457 : Blo 1372005 2059457 := bstep (se 2 (by rfl) ⟨772296, by rfl⟩ : syracuseStep 2059457 = 1544593) B1544593
theorem B11136197 : Blo 1372005 11136197 := bstep (se 4 (by rfl) ⟨1044018, by rfl⟩ : syracuseStep 11136197 = 2088037) B2088037
theorem B2059475 : Blo 1372005 2059475 := bstep (se 1 (by rfl) ⟨1544606, by rfl⟩ : syracuseStep 2059475 = 3089213) B3089213
theorem B2608355 : Blo 1372005 2608355 := bstep (se 1 (by rfl) ⟨1956266, by rfl⟩ : syracuseStep 2608355 = 3912533) B3912533
theorem B5942513 : Blo 1372005 5942513 := bstep (se 2 (by rfl) ⟨2228442, by rfl⟩ : syracuseStep 5942513 = 4456885) B4456885
theorem B2059505 : Blo 1372005 2059505 := bstep (se 2 (by rfl) ⟨772314, by rfl⟩ : syracuseStep 2059505 = 1544629) B1544629
theorem B2059523 : Blo 1372005 2059523 := bstep (se 1 (by rfl) ⟨1544642, by rfl⟩ : syracuseStep 2059523 = 3089285) B3089285
theorem B14855437 : Blo 1372005 14855437 := bstep (se 3 (by rfl) ⟨2785394, by rfl⟩ : syracuseStep 14855437 = 5570789) B5570789
theorem B2198801 : Blo 1372005 2198801 := bstep (se 2 (by rfl) ⟨824550, by rfl⟩ : syracuseStep 2198801 = 1649101) B1649101
theorem B3476753 : Blo 1372005 3476753 := bstep (se 2 (by rfl) ⟨1303782, by rfl⟩ : syracuseStep 3476753 = 2607565) B2607565
theorem B2059553 : Blo 1372005 2059553 := bstep (se 2 (by rfl) ⟨772332, by rfl⟩ : syracuseStep 2059553 = 1544665) B1544665
theorem B2059571 : Blo 1372005 2059571 := bstep (se 1 (by rfl) ⟨1544678, by rfl⟩ : syracuseStep 2059571 = 3089357) B3089357
theorem B3476803 : Blo 1372005 3476803 := bstep (se 1 (by rfl) ⟨2607602, by rfl⟩ : syracuseStep 3476803 = 5215205) B5215205
theorem B2059601 : Blo 1372005 2059601 := bstep (se 2 (by rfl) ⟨772350, by rfl⟩ : syracuseStep 2059601 = 1544701) B1544701
theorem B2059619 : Blo 1372005 2059619 := bstep (se 1 (by rfl) ⟨1544714, by rfl⟩ : syracuseStep 2059619 = 3089429) B3089429
theorem B2059649 : Blo 1372005 2059649 := bstep (se 2 (by rfl) ⟨772368, by rfl⟩ : syracuseStep 2059649 = 1544737) B1544737
theorem B6950285 : Blo 1372005 6950285 := bstep (se 3 (by rfl) ⟨1303178, by rfl⟩ : syracuseStep 6950285 = 2606357) B2606357
theorem B2059667 : Blo 1372005 2059667 := bstep (se 1 (by rfl) ⟨1544750, by rfl⟩ : syracuseStep 2059667 = 3089501) B3089501
theorem B3911075 : Blo 1372005 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B2059697 : Blo 1372005 2059697 := bstep (se 2 (by rfl) ⟨772386, by rfl⟩ : syracuseStep 2059697 = 1544773) B1544773
theorem B1543603 : Blo 1372005 1543603 := bstep (se 1 (by rfl) ⟨1157702, by rfl⟩ : syracuseStep 1543603 = 2315405) B2315405
theorem B2059715 : Blo 1372005 2059715 := bstep (se 1 (by rfl) ⟨1544786, by rfl⟩ : syracuseStep 2059715 = 3089573) B3089573
theorem B3476945 : Blo 1372005 3476945 := bstep (se 2 (by rfl) ⟨1303854, by rfl⟩ : syracuseStep 3476945 = 2607709) B2607709
theorem B2059745 : Blo 1372005 2059745 := bstep (se 2 (by rfl) ⟨772404, by rfl⟩ : syracuseStep 2059745 = 1544809) B1544809
theorem B2199025 : Blo 1372005 2199025 := bstep (se 2 (by rfl) ⟨824634, by rfl⟩ : syracuseStep 2199025 = 1649269) B1649269
theorem B2059763 : Blo 1372005 2059763 := bstep (se 1 (by rfl) ⟨1544822, by rfl⟩ : syracuseStep 2059763 = 3089645) B3089645
theorem B2059793 : Blo 1372005 2059793 := bstep (se 2 (by rfl) ⟨772422, by rfl⟩ : syracuseStep 2059793 = 1544845) B1544845
theorem B2059811 : Blo 1372005 2059811 := bstep (se 1 (by rfl) ⟨1544858, by rfl⟩ : syracuseStep 2059811 = 3089717) B3089717
theorem B2199089 : Blo 1372005 2199089 := bstep (se 2 (by rfl) ⟨824658, by rfl⟩ : syracuseStep 2199089 = 1649317) B1649317
theorem B2059841 : Blo 1372005 2059841 := bstep (se 2 (by rfl) ⟨772440, by rfl⟩ : syracuseStep 2059841 = 1544881) B1544881
theorem B1543747 : Blo 1372005 1543747 := bstep (se 1 (by rfl) ⟨1157810, by rfl⟩ : syracuseStep 1543747 = 2315621) B2315621
theorem B2059859 : Blo 1372005 2059859 := bstep (se 1 (by rfl) ⟨1544894, by rfl⟩ : syracuseStep 2059859 = 3089789) B3089789
theorem B15855203 : Blo 1372005 15855203 := bstep (se 1 (by rfl) ⟨11891402, by rfl⟩ : syracuseStep 15855203 = 23782805) B23782805
theorem B3911267 : Blo 1372005 3911267 := bstep (se 1 (by rfl) ⟨2933450, by rfl⟩ : syracuseStep 3911267 = 5866901) B5866901
theorem B8801891 : Blo 1372005 8801891 := bstep (se 1 (by rfl) ⟨6601418, by rfl⟩ : syracuseStep 8801891 = 13202837) B13202837
theorem B4632173 : Blo 1372005 4632173 := bstep (se 3 (by rfl) ⟨868532, by rfl⟩ : syracuseStep 4632173 = 1737065) B1737065
theorem B2059889 : Blo 1372005 2059889 := bstep (se 2 (by rfl) ⟨772458, by rfl⟩ : syracuseStep 2059889 = 1544917) B1544917
theorem B2059907 : Blo 1372005 2059907 := bstep (se 1 (by rfl) ⟨1544930, by rfl⟩ : syracuseStep 2059907 = 3089861) B3089861
theorem B2059937 : Blo 1372005 2059937 := bstep (se 2 (by rfl) ⟨772476, by rfl⟩ : syracuseStep 2059937 = 1544953) B1544953
theorem B4632227 : Blo 1372005 4632227 := bstep (se 1 (by rfl) ⟨3474170, by rfl⟩ : syracuseStep 4632227 = 6948341) B6948341
theorem B2199217 : Blo 1372005 2199217 := bstep (se 2 (by rfl) ⟨824706, by rfl⟩ : syracuseStep 2199217 = 1649413) B1649413
theorem B2059955 : Blo 1372005 2059955 := bstep (se 1 (by rfl) ⟨1544966, by rfl⟩ : syracuseStep 2059955 = 3089933) B3089933
theorem B2059985 : Blo 1372005 2059985 := bstep (se 2 (by rfl) ⟨772494, by rfl⟩ : syracuseStep 2059985 = 1544989) B1544989
theorem B1543891 : Blo 1372005 1543891 := bstep (se 1 (by rfl) ⟨1157918, by rfl⟩ : syracuseStep 1543891 = 2315837) B2315837
theorem B2060003 : Blo 1372005 2060003 := bstep (se 1 (by rfl) ⟨1545002, by rfl⟩ : syracuseStep 2060003 = 3090005) B3090005
theorem B2060033 : Blo 1372005 2060033 := bstep (se 2 (by rfl) ⟨772512, by rfl⟩ : syracuseStep 2060033 = 1545025) B1545025
theorem B2060051 : Blo 1372005 2060051 := bstep (se 1 (by rfl) ⟨1545038, by rfl⟩ : syracuseStep 2060051 = 3090077) B3090077
theorem B2060081 : Blo 1372005 2060081 := bstep (se 2 (by rfl) ⟨772530, by rfl⟩ : syracuseStep 2060081 = 1545061) B1545061
theorem B2060099 : Blo 1372005 2060099 := bstep (se 1 (by rfl) ⟨1545074, by rfl⟩ : syracuseStep 2060099 = 3090149) B3090149
theorem B2412385 : Blo 1372005 2412385 := bstep (se 2 (by rfl) ⟨904644, by rfl⟩ : syracuseStep 2412385 = 1809289) B1809289
theorem B2060129 : Blo 1372005 2060129 := bstep (se 2 (by rfl) ⟨772548, by rfl⟩ : syracuseStep 2060129 = 1545097) B1545097
theorem B1544035 : Blo 1372005 1544035 := bstep (se 1 (by rfl) ⟨1158026, by rfl⟩ : syracuseStep 1544035 = 2316053) B2316053
theorem B1372019 : Blo 1372005 1372019 := bstep (se 1 (by rfl) ⟨1029014, by rfl⟩ : syracuseStep 1372019 = 2058029) B2058029
theorem B2060147 : Blo 1372005 2060147 := bstep (se 1 (by rfl) ⟨1545110, by rfl⟩ : syracuseStep 2060147 = 3090221) B3090221
theorem B1650547 : Blo 1372005 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B1372035 : Blo 1372005 1372035 := bstep (se 1 (by rfl) ⟨1029026, by rfl⟩ : syracuseStep 1372035 = 2058053) B2058053
theorem B2060177 : Blo 1372005 2060177 := bstep (se 2 (by rfl) ⟨772566, by rfl⟩ : syracuseStep 2060177 = 1545133) B1545133
theorem B1372051 : Blo 1372005 1372051 := bstep (se 1 (by rfl) ⟨1029038, by rfl⟩ : syracuseStep 1372051 = 2058077) B2058077
theorem B1372067 : Blo 1372005 1372067 := bstep (se 1 (by rfl) ⟨1029050, by rfl⟩ : syracuseStep 1372067 = 2058101) B2058101
theorem B2060195 : Blo 1372005 2060195 := bstep (se 1 (by rfl) ⟨1545146, by rfl⟩ : syracuseStep 2060195 = 3090293) B3090293
theorem B5861297 : Blo 1372005 5861297 := bstep (se 2 (by rfl) ⟨2197986, by rfl⟩ : syracuseStep 5861297 = 4395973) B4395973
theorem B4632497 : Blo 1372005 4632497 := bstep (se 2 (by rfl) ⟨1737186, by rfl⟩ : syracuseStep 4632497 = 3474373) B3474373
theorem B1372083 : Blo 1372005 1372083 := bstep (se 1 (by rfl) ⟨1029062, by rfl⟩ : syracuseStep 1372083 = 2058125) B2058125
theorem B1953715 : Blo 1372005 1953715 := bstep (se 1 (by rfl) ⟨1465286, by rfl⟩ : syracuseStep 1953715 = 2930573) B2930573
theorem B2060225 : Blo 1372005 2060225 := bstep (se 2 (by rfl) ⟨772584, by rfl⟩ : syracuseStep 2060225 = 1545169) B1545169
theorem B1372099 : Blo 1372005 1372099 := bstep (se 1 (by rfl) ⟨1029074, by rfl⟩ : syracuseStep 1372099 = 2058149) B2058149
theorem B1372115 : Blo 1372005 1372115 := bstep (se 1 (by rfl) ⟨1029086, by rfl⟩ : syracuseStep 1372115 = 2058173) B2058173
theorem B2060243 : Blo 1372005 2060243 := bstep (se 1 (by rfl) ⟨1545182, by rfl⟩ : syracuseStep 2060243 = 3090365) B3090365
theorem B1372131 : Blo 1372005 1372131 := bstep (se 1 (by rfl) ⟨1029098, by rfl⟩ : syracuseStep 1372131 = 2058197) B2058197
theorem B2060273 : Blo 1372005 2060273 := bstep (se 2 (by rfl) ⟨772602, by rfl⟩ : syracuseStep 2060273 = 1545205) B1545205
theorem B1372147 : Blo 1372005 1372147 := bstep (se 1 (by rfl) ⟨1029110, by rfl⟩ : syracuseStep 1372147 = 2058221) B2058221
theorem B1544179 : Blo 1372005 1544179 := bstep (se 1 (by rfl) ⟨1158134, by rfl⟩ : syracuseStep 1544179 = 2316269) B2316269
theorem B1372163 : Blo 1372005 1372163 := bstep (se 1 (by rfl) ⟨1029122, by rfl⟩ : syracuseStep 1372163 = 2058245) B2058245
theorem B2060291 : Blo 1372005 2060291 := bstep (se 1 (by rfl) ⟨1545218, by rfl⟩ : syracuseStep 2060291 = 3090437) B3090437
theorem B1372179 : Blo 1372005 1372179 := bstep (se 1 (by rfl) ⟨1029134, by rfl⟩ : syracuseStep 1372179 = 2058269) B2058269
theorem B1953811 : Blo 1372005 1953811 := bstep (se 1 (by rfl) ⟨1465358, by rfl⟩ : syracuseStep 1953811 = 2930717) B2930717
theorem B2060321 : Blo 1372005 2060321 := bstep (se 2 (by rfl) ⟨772620, by rfl⟩ : syracuseStep 2060321 = 1545241) B1545241
theorem B1372195 : Blo 1372005 1372195 := bstep (se 1 (by rfl) ⟨1029146, by rfl⟩ : syracuseStep 1372195 = 2058293) B2058293
theorem B1372211 : Blo 1372005 1372211 := bstep (se 1 (by rfl) ⟨1029158, by rfl⟩ : syracuseStep 1372211 = 2058317) B2058317
theorem B2060339 : Blo 1372005 2060339 := bstep (se 1 (by rfl) ⟨1545254, by rfl⟩ : syracuseStep 2060339 = 3090509) B3090509
theorem B1372227 : Blo 1372005 1372227 := bstep (se 1 (by rfl) ⟨1029170, by rfl⟩ : syracuseStep 1372227 = 2058341) B2058341
theorem B2060369 : Blo 1372005 2060369 := bstep (se 2 (by rfl) ⟨772638, by rfl⟩ : syracuseStep 2060369 = 1545277) B1545277
theorem B1372243 : Blo 1372005 1372243 := bstep (se 1 (by rfl) ⟨1029182, by rfl⟩ : syracuseStep 1372243 = 2058365) B2058365
theorem B1372259 : Blo 1372005 1372259 := bstep (se 1 (by rfl) ⟨1029194, by rfl⟩ : syracuseStep 1372259 = 2058389) B2058389
theorem B2060387 : Blo 1372005 2060387 := bstep (se 1 (by rfl) ⟨1545290, by rfl⟩ : syracuseStep 2060387 = 3090581) B3090581
theorem B1372275 : Blo 1372005 1372275 := bstep (se 1 (by rfl) ⟨1029206, by rfl⟩ : syracuseStep 1372275 = 2058413) B2058413
theorem B2060417 : Blo 1372005 2060417 := bstep (se 2 (by rfl) ⟨772656, by rfl⟩ : syracuseStep 2060417 = 1545313) B1545313
theorem B1372291 : Blo 1372005 1372291 := bstep (se 1 (by rfl) ⟨1029218, by rfl⟩ : syracuseStep 1372291 = 2058437) B2058437
theorem B1544323 : Blo 1372005 1544323 := bstep (se 1 (by rfl) ⟨1158242, by rfl⟩ : syracuseStep 1544323 = 2316485) B2316485
theorem B1372307 : Blo 1372005 1372307 := bstep (se 1 (by rfl) ⟨1029230, by rfl⟩ : syracuseStep 1372307 = 2058461) B2058461
theorem B2060435 : Blo 1372005 2060435 := bstep (se 1 (by rfl) ⟨1545326, by rfl⟩ : syracuseStep 2060435 = 3090653) B3090653
theorem B1372323 : Blo 1372005 1372323 := bstep (se 1 (by rfl) ⟨1029242, by rfl⟩ : syracuseStep 1372323 = 2058485) B2058485
theorem B2060465 : Blo 1372005 2060465 := bstep (se 2 (by rfl) ⟨772674, by rfl⟩ : syracuseStep 2060465 = 1545349) B1545349
theorem B1372339 : Blo 1372005 1372339 := bstep (se 1 (by rfl) ⟨1029254, by rfl⟩ : syracuseStep 1372339 = 2058509) B2058509
theorem B1372355 : Blo 1372005 1372355 := bstep (se 1 (by rfl) ⟨1029266, by rfl⟩ : syracuseStep 1372355 = 2058533) B2058533
theorem B2060483 : Blo 1372005 2060483 := bstep (se 1 (by rfl) ⟨1545362, by rfl⟩ : syracuseStep 2060483 = 3090725) B3090725
theorem B1372371 : Blo 1372005 1372371 := bstep (se 1 (by rfl) ⟨1029278, by rfl⟩ : syracuseStep 1372371 = 2058557) B2058557
theorem B2060513 : Blo 1372005 2060513 := bstep (se 2 (by rfl) ⟨772692, by rfl⟩ : syracuseStep 2060513 = 1545385) B1545385
theorem B1372387 : Blo 1372005 1372387 := bstep (se 1 (by rfl) ⟨1029290, by rfl⟩ : syracuseStep 1372387 = 2058581) B2058581
theorem B1372403 : Blo 1372005 1372403 := bstep (se 1 (by rfl) ⟨1029302, by rfl⟩ : syracuseStep 1372403 = 2058605) B2058605
theorem B2060531 : Blo 1372005 2060531 := bstep (se 1 (by rfl) ⟨1545398, by rfl⟩ : syracuseStep 2060531 = 3090797) B3090797
theorem B1372419 : Blo 1372005 1372419 := bstep (se 1 (by rfl) ⟨1029314, by rfl⟩ : syracuseStep 1372419 = 2058629) B2058629
theorem B2060561 : Blo 1372005 2060561 := bstep (se 2 (by rfl) ⟨772710, by rfl⟩ : syracuseStep 2060561 = 1545421) B1545421
theorem B1372435 : Blo 1372005 1372435 := bstep (se 1 (by rfl) ⟨1029326, by rfl⟩ : syracuseStep 1372435 = 2058653) B2058653
theorem B1544467 : Blo 1372005 1544467 := bstep (se 1 (by rfl) ⟨1158350, by rfl⟩ : syracuseStep 1544467 = 2316701) B2316701
theorem B1372451 : Blo 1372005 1372451 := bstep (se 1 (by rfl) ⟨1029338, by rfl⟩ : syracuseStep 1372451 = 2058677) B2058677
theorem B2060579 : Blo 1372005 2060579 := bstep (se 1 (by rfl) ⟨1545434, by rfl⟩ : syracuseStep 2060579 = 3090869) B3090869
theorem B4174129 : Blo 1372005 4174129 := bstep (se 2 (by rfl) ⟨1565298, by rfl⟩ : syracuseStep 4174129 = 3130597) B3130597
theorem B2642225 : Blo 1372005 2642225 := bstep (se 2 (by rfl) ⟨990834, by rfl⟩ : syracuseStep 2642225 = 1981669) B1981669
theorem B1372467 : Blo 1372005 1372467 := bstep (se 1 (by rfl) ⟨1029350, by rfl⟩ : syracuseStep 1372467 = 2058701) B2058701
theorem B2060609 : Blo 1372005 2060609 := bstep (se 2 (by rfl) ⟨772728, by rfl⟩ : syracuseStep 2060609 = 1545457) B1545457
theorem B1372483 : Blo 1372005 1372483 := bstep (se 1 (by rfl) ⟨1029362, by rfl⟩ : syracuseStep 1372483 = 2058725) B2058725
theorem B1372499 : Blo 1372005 1372499 := bstep (se 1 (by rfl) ⟨1029374, by rfl⟩ : syracuseStep 1372499 = 2058749) B2058749
theorem B2060627 : Blo 1372005 2060627 := bstep (se 1 (by rfl) ⟨1545470, by rfl⟩ : syracuseStep 2060627 = 3090941) B3090941
theorem B3297635 : Blo 1372005 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B1372515 : Blo 1372005 1372515 := bstep (se 1 (by rfl) ⟨1029386, by rfl⟩ : syracuseStep 1372515 = 2058773) B2058773
theorem B2060657 : Blo 1372005 2060657 := bstep (se 2 (by rfl) ⟨772746, by rfl⟩ : syracuseStep 2060657 = 1545493) B1545493
theorem B1372531 : Blo 1372005 1372531 := bstep (se 1 (by rfl) ⟨1029398, by rfl⟩ : syracuseStep 1372531 = 2058797) B2058797
theorem B1372547 : Blo 1372005 1372547 := bstep (se 1 (by rfl) ⟨1029410, by rfl⟩ : syracuseStep 1372547 = 2058821) B2058821
theorem B2060675 : Blo 1372005 2060675 := bstep (se 1 (by rfl) ⟨1545506, by rfl⟩ : syracuseStep 2060675 = 3091013) B3091013
theorem B3912077 : Blo 1372005 3912077 := bstep (se 3 (by rfl) ⟨733514, by rfl⟩ : syracuseStep 3912077 = 1467029) B1467029
theorem B1372563 : Blo 1372005 1372563 := bstep (se 1 (by rfl) ⟨1029422, by rfl⟩ : syracuseStep 1372563 = 2058845) B2058845
theorem B2060705 : Blo 1372005 2060705 := bstep (se 2 (by rfl) ⟨772764, by rfl⟩ : syracuseStep 2060705 = 1545529) B1545529
theorem B1372579 : Blo 1372005 1372579 := bstep (se 1 (by rfl) ⟨1029434, by rfl⟩ : syracuseStep 1372579 = 2058869) B2058869
theorem B1544611 : Blo 1372005 1544611 := bstep (se 1 (by rfl) ⟨1158458, by rfl⟩ : syracuseStep 1544611 = 2316917) B2316917
theorem B3477937 : Blo 1372005 3477937 := bstep (se 2 (by rfl) ⟨1304226, by rfl⟩ : syracuseStep 3477937 = 2608453) B2608453
theorem B1372595 : Blo 1372005 1372595 := bstep (se 1 (by rfl) ⟨1029446, by rfl⟩ : syracuseStep 1372595 = 2058893) B2058893
theorem B2060723 : Blo 1372005 2060723 := bstep (se 1 (by rfl) ⟨1545542, by rfl⟩ : syracuseStep 2060723 = 3091085) B3091085
theorem B1372611 : Blo 1372005 1372611 := bstep (se 1 (by rfl) ⟨1029458, by rfl⟩ : syracuseStep 1372611 = 2058917) B2058917
theorem B4633037 : Blo 1372005 4633037 := bstep (se 3 (by rfl) ⟨868694, by rfl⟩ : syracuseStep 4633037 = 1737389) B1737389
theorem B2060753 : Blo 1372005 2060753 := bstep (se 2 (by rfl) ⟨772782, by rfl⟩ : syracuseStep 2060753 = 1545565) B1545565
theorem B1372627 : Blo 1372005 1372627 := bstep (se 1 (by rfl) ⟨1029470, by rfl⟩ : syracuseStep 1372627 = 2058941) B2058941
theorem B1372643 : Blo 1372005 1372643 := bstep (se 1 (by rfl) ⟨1029482, by rfl⟩ : syracuseStep 1372643 = 2058965) B2058965
theorem B2060771 : Blo 1372005 2060771 := bstep (se 1 (by rfl) ⟨1545578, by rfl⟩ : syracuseStep 2060771 = 3091157) B3091157
theorem B1372659 : Blo 1372005 1372659 := bstep (se 1 (by rfl) ⟨1029494, by rfl⟩ : syracuseStep 1372659 = 2058989) B2058989
theorem B1372675 : Blo 1372005 1372675 := bstep (se 1 (by rfl) ⟨1029506, by rfl⟩ : syracuseStep 1372675 = 2059013) B2059013
theorem B2347523 : Blo 1372005 2347523 := bstep (se 1 (by rfl) ⟨1760642, by rfl⟩ : syracuseStep 2347523 = 3521285) B3521285
theorem B1954307 : Blo 1372005 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B4633091 : Blo 1372005 4633091 := bstep (se 1 (by rfl) ⟨3474818, by rfl⟩ : syracuseStep 4633091 = 6949637) B6949637
theorem B2060801 : Blo 1372005 2060801 := bstep (se 2 (by rfl) ⟨772800, by rfl⟩ : syracuseStep 2060801 = 1545601) B1545601
theorem B1856017 : Blo 1372005 1856017 := bstep (se 2 (by rfl) ⟨696006, by rfl⟩ : syracuseStep 1856017 = 1392013) B1392013
theorem B1372691 : Blo 1372005 1372691 := bstep (se 1 (by rfl) ⟨1029518, by rfl⟩ : syracuseStep 1372691 = 2059037) B2059037
theorem B2060819 : Blo 1372005 2060819 := bstep (se 1 (by rfl) ⟨1545614, by rfl⟩ : syracuseStep 2060819 = 3091229) B3091229
theorem B1372707 : Blo 1372005 1372707 := bstep (se 1 (by rfl) ⟨1029530, by rfl⟩ : syracuseStep 1372707 = 2059061) B2059061
theorem B6263345 : Blo 1372005 6263345 := bstep (se 2 (by rfl) ⟨2348754, by rfl⟩ : syracuseStep 6263345 = 4697509) B4697509
theorem B2060849 : Blo 1372005 2060849 := bstep (se 2 (by rfl) ⟨772818, by rfl⟩ : syracuseStep 2060849 = 1545637) B1545637
theorem B1372723 : Blo 1372005 1372723 := bstep (se 1 (by rfl) ⟨1029542, by rfl⟩ : syracuseStep 1372723 = 2059085) B2059085
theorem B1544755 : Blo 1372005 1544755 := bstep (se 1 (by rfl) ⟨1158566, by rfl⟩ : syracuseStep 1544755 = 2317133) B2317133
theorem B1856065 : Blo 1372005 1856065 := bstep (se 2 (by rfl) ⟨696024, by rfl⟩ : syracuseStep 1856065 = 1392049) B1392049
theorem B1372739 : Blo 1372005 1372739 := bstep (se 1 (by rfl) ⟨1029554, by rfl⟩ : syracuseStep 1372739 = 2059109) B2059109
theorem B3912259 : Blo 1372005 3912259 := bstep (se 1 (by rfl) ⟨2934194, by rfl⟩ : syracuseStep 3912259 = 5868389) B5868389
theorem B2060867 : Blo 1372005 2060867 := bstep (se 1 (by rfl) ⟨1545650, by rfl⟩ : syracuseStep 2060867 = 3091301) B3091301
theorem B1372755 : Blo 1372005 1372755 := bstep (se 1 (by rfl) ⟨1029566, by rfl⟩ : syracuseStep 1372755 = 2059133) B2059133
theorem B2060897 : Blo 1372005 2060897 := bstep (se 2 (by rfl) ⟨772836, by rfl⟩ : syracuseStep 2060897 = 1545673) B1545673
theorem B1372771 : Blo 1372005 1372771 := bstep (se 1 (by rfl) ⟨1029578, by rfl⟩ : syracuseStep 1372771 = 2059157) B2059157
theorem B1372787 : Blo 1372005 1372787 := bstep (se 1 (by rfl) ⟨1029590, by rfl⟩ : syracuseStep 1372787 = 2059181) B2059181
theorem B2060915 : Blo 1372005 2060915 := bstep (se 1 (by rfl) ⟨1545686, by rfl⟩ : syracuseStep 2060915 = 3091373) B3091373
theorem B1372803 : Blo 1372005 1372803 := bstep (se 1 (by rfl) ⟨1029602, by rfl⟩ : syracuseStep 1372803 = 2059205) B2059205
theorem B4395665 : Blo 1372005 4395665 := bstep (se 2 (by rfl) ⟨1648374, by rfl⟩ : syracuseStep 4395665 = 3296749) B3296749
theorem B2060945 : Blo 1372005 2060945 := bstep (se 2 (by rfl) ⟨772854, by rfl⟩ : syracuseStep 2060945 = 1545709) B1545709
theorem B1372819 : Blo 1372005 1372819 := bstep (se 1 (by rfl) ⟨1029614, by rfl⟩ : syracuseStep 1372819 = 2059229) B2059229
theorem B1372835 : Blo 1372005 1372835 := bstep (se 1 (by rfl) ⟨1029626, by rfl⟩ : syracuseStep 1372835 = 2059253) B2059253
theorem B2060963 : Blo 1372005 2060963 := bstep (se 1 (by rfl) ⟨1545722, by rfl⟩ : syracuseStep 2060963 = 3091445) B3091445
theorem B1372851 : Blo 1372005 1372851 := bstep (se 1 (by rfl) ⟨1029638, by rfl⟩ : syracuseStep 1372851 = 2059277) B2059277
theorem B2060993 : Blo 1372005 2060993 := bstep (se 2 (by rfl) ⟨772872, by rfl⟩ : syracuseStep 2060993 = 1545745) B1545745
theorem B1372867 : Blo 1372005 1372867 := bstep (se 1 (by rfl) ⟨1029650, by rfl⟩ : syracuseStep 1372867 = 2059301) B2059301
theorem B1544899 : Blo 1372005 1544899 := bstep (se 1 (by rfl) ⟨1158674, by rfl⟩ : syracuseStep 1544899 = 2317349) B2317349
theorem B1372883 : Blo 1372005 1372883 := bstep (se 1 (by rfl) ⟨1029662, by rfl⟩ : syracuseStep 1372883 = 2059325) B2059325
theorem B1372899 : Blo 1372005 1372899 := bstep (se 1 (by rfl) ⟨1029674, by rfl⟩ : syracuseStep 1372899 = 2059349) B2059349
theorem B1372915 : Blo 1372005 1372915 := bstep (se 1 (by rfl) ⟨1029686, by rfl⟩ : syracuseStep 1372915 = 2059373) B2059373
theorem B1372931 : Blo 1372005 1372931 := bstep (se 1 (by rfl) ⟨1029698, by rfl⟩ : syracuseStep 1372931 = 2059397) B2059397
theorem B4633361 : Blo 1372005 4633361 := bstep (se 2 (by rfl) ⟨1737510, by rfl⟩ : syracuseStep 4633361 = 3475021) B3475021
theorem B1372947 : Blo 1372005 1372947 := bstep (se 1 (by rfl) ⟨1029710, by rfl⟩ : syracuseStep 1372947 = 2059421) B2059421
theorem B1372963 : Blo 1372005 1372963 := bstep (se 1 (by rfl) ⟨1029722, by rfl⟩ : syracuseStep 1372963 = 2059445) B2059445
theorem B2347825 : Blo 1372005 2347825 := bstep (se 2 (by rfl) ⟨880434, by rfl⟩ : syracuseStep 2347825 = 1760869) B1760869
theorem B1372979 : Blo 1372005 1372979 := bstep (se 1 (by rfl) ⟨1029734, by rfl⟩ : syracuseStep 1372979 = 2059469) B2059469
theorem B1372995 : Blo 1372005 1372995 := bstep (se 1 (by rfl) ⟨1029746, by rfl⟩ : syracuseStep 1372995 = 2059493) B2059493
theorem B1373011 : Blo 1372005 1373011 := bstep (se 1 (by rfl) ⟨1029758, by rfl⟩ : syracuseStep 1373011 = 2059517) B2059517
theorem B1545043 : Blo 1372005 1545043 := bstep (se 1 (by rfl) ⟨1158782, by rfl⟩ : syracuseStep 1545043 = 2317565) B2317565
theorem B1373027 : Blo 1372005 1373027 := bstep (se 1 (by rfl) ⟨1029770, by rfl⟩ : syracuseStep 1373027 = 2059541) B2059541
theorem B1373043 : Blo 1372005 1373043 := bstep (se 1 (by rfl) ⟨1029782, by rfl⟩ : syracuseStep 1373043 = 2059565) B2059565
theorem B1373059 : Blo 1372005 1373059 := bstep (se 1 (by rfl) ⟨1029794, by rfl⟩ : syracuseStep 1373059 = 2059589) B2059589
theorem B7820165 : Blo 1372005 7820165 := bstep (se 4 (by rfl) ⟨733140, by rfl⟩ : syracuseStep 7820165 = 1466281) B1466281
theorem B1373075 : Blo 1372005 1373075 := bstep (se 1 (by rfl) ⟨1029806, by rfl⟩ : syracuseStep 1373075 = 2059613) B2059613
theorem B3298211 : Blo 1372005 3298211 := bstep (se 1 (by rfl) ⟨2473658, by rfl⟩ : syracuseStep 3298211 = 4947317) B4947317
theorem B1373091 : Blo 1372005 1373091 := bstep (se 1 (by rfl) ⟨1029818, by rfl⟩ : syracuseStep 1373091 = 2059637) B2059637
theorem B4699043 : Blo 1372005 4699043 := bstep (se 1 (by rfl) ⟨3524282, by rfl⟩ : syracuseStep 4699043 = 7048565) B7048565
theorem B1373107 : Blo 1372005 1373107 := bstep (se 1 (by rfl) ⟨1029830, by rfl⟩ : syracuseStep 1373107 = 2059661) B2059661
theorem B1373123 : Blo 1372005 1373123 := bstep (se 1 (by rfl) ⟨1029842, by rfl⟩ : syracuseStep 1373123 = 2059685) B2059685
theorem B1373139 : Blo 1372005 1373139 := bstep (se 1 (by rfl) ⟨1029854, by rfl⟩ : syracuseStep 1373139 = 2059709) B2059709
theorem B1373155 : Blo 1372005 1373155 := bstep (se 1 (by rfl) ⟨1029866, by rfl⟩ : syracuseStep 1373155 = 2059733) B2059733
theorem B1545187 : Blo 1372005 1545187 := bstep (se 1 (by rfl) ⟨1158890, by rfl⟩ : syracuseStep 1545187 = 2317781) B2317781
theorem B1373171 : Blo 1372005 1373171 := bstep (se 1 (by rfl) ⟨1029878, by rfl⟩ : syracuseStep 1373171 = 2059757) B2059757
theorem B1373187 : Blo 1372005 1373187 := bstep (se 1 (by rfl) ⟨1029890, by rfl⟩ : syracuseStep 1373187 = 2059781) B2059781
theorem B1373203 : Blo 1372005 1373203 := bstep (se 1 (by rfl) ⟨1029902, by rfl⟩ : syracuseStep 1373203 = 2059805) B2059805
theorem B2315297 : Blo 1372005 2315297 := bstep (se 2 (by rfl) ⟨868236, by rfl⟩ : syracuseStep 2315297 = 1736473) B1736473
theorem B1373219 : Blo 1372005 1373219 := bstep (se 1 (by rfl) ⟨1029914, by rfl⟩ : syracuseStep 1373219 = 2059829) B2059829
theorem B1373235 : Blo 1372005 1373235 := bstep (se 1 (by rfl) ⟨1029926, by rfl⟩ : syracuseStep 1373235 = 2059853) B2059853
theorem B1373251 : Blo 1372005 1373251 := bstep (se 1 (by rfl) ⟨1029938, by rfl⟩ : syracuseStep 1373251 = 2059877) B2059877
theorem B1373267 : Blo 1372005 1373267 := bstep (se 1 (by rfl) ⟨1029950, by rfl⟩ : syracuseStep 1373267 = 2059901) B2059901
theorem B3298403 : Blo 1372005 3298403 := bstep (se 1 (by rfl) ⟨2473802, by rfl⟩ : syracuseStep 3298403 = 4947605) B4947605
theorem B1373283 : Blo 1372005 1373283 := bstep (se 1 (by rfl) ⟨1029962, by rfl⟩ : syracuseStep 1373283 = 2059925) B2059925
theorem B4945009 : Blo 1372005 4945009 := bstep (se 2 (by rfl) ⟨1854378, by rfl⟩ : syracuseStep 4945009 = 3708757) B3708757
theorem B1373299 : Blo 1372005 1373299 := bstep (se 1 (by rfl) ⟨1029974, by rfl⟩ : syracuseStep 1373299 = 2059949) B2059949
theorem B1545331 : Blo 1372005 1545331 := bstep (se 1 (by rfl) ⟨1158998, by rfl⟩ : syracuseStep 1545331 = 2317997) B2317997
theorem B1954945 : Blo 1372005 1954945 := bstep (se 2 (by rfl) ⟨733104, by rfl⟩ : syracuseStep 1954945 = 1466209) B1466209
theorem B1373315 : Blo 1372005 1373315 := bstep (se 1 (by rfl) ⟨1029986, by rfl⟩ : syracuseStep 1373315 = 2059973) B2059973
theorem B5215373 : Blo 1372005 5215373 := bstep (se 3 (by rfl) ⟨977882, by rfl⟩ : syracuseStep 5215373 = 1955765) B1955765
theorem B1373331 : Blo 1372005 1373331 := bstep (se 1 (by rfl) ⟨1029998, by rfl⟩ : syracuseStep 1373331 = 2059997) B2059997
theorem B2315425 : Blo 1372005 2315425 := bstep (se 2 (by rfl) ⟨868284, by rfl⟩ : syracuseStep 2315425 = 1736569) B1736569
theorem B5862563 : Blo 1372005 5862563 := bstep (se 1 (by rfl) ⟨4396922, by rfl⟩ : syracuseStep 5862563 = 8793845) B8793845
theorem B1373347 : Blo 1372005 1373347 := bstep (se 1 (by rfl) ⟨1030010, by rfl⟩ : syracuseStep 1373347 = 2060021) B2060021
theorem B6599843 : Blo 1372005 6599843 := bstep (se 1 (by rfl) ⟨4949882, by rfl⟩ : syracuseStep 6599843 = 9899765) B9899765
theorem B1373363 : Blo 1372005 1373363 := bstep (se 1 (by rfl) ⟨1030022, by rfl⟩ : syracuseStep 1373363 = 2060045) B2060045
theorem B2315459 : Blo 1372005 2315459 := bstep (se 1 (by rfl) ⟨1736594, by rfl⟩ : syracuseStep 2315459 = 3473189) B3473189
theorem B1373379 : Blo 1372005 1373379 := bstep (se 1 (by rfl) ⟨1030034, by rfl⟩ : syracuseStep 1373379 = 2060069) B2060069
theorem B1373395 : Blo 1372005 1373395 := bstep (se 1 (by rfl) ⟨1030046, by rfl⟩ : syracuseStep 1373395 = 2060093) B2060093
theorem B1373411 : Blo 1372005 1373411 := bstep (se 1 (by rfl) ⟨1030058, by rfl⟩ : syracuseStep 1373411 = 2060117) B2060117
theorem B1373427 : Blo 1372005 1373427 := bstep (se 1 (by rfl) ⟨1030070, by rfl⟩ : syracuseStep 1373427 = 2060141) B2060141
theorem B1373443 : Blo 1372005 1373443 := bstep (se 1 (by rfl) ⟨1030082, by rfl⟩ : syracuseStep 1373443 = 2060165) B2060165
theorem B1545475 : Blo 1372005 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B1373459 : Blo 1372005 1373459 := bstep (se 1 (by rfl) ⟨1030094, by rfl⟩ : syracuseStep 1373459 = 2060189) B2060189
theorem B1373475 : Blo 1372005 1373475 := bstep (se 1 (by rfl) ⟨1030106, by rfl⟩ : syracuseStep 1373475 = 2060213) B2060213
theorem B4633901 : Blo 1372005 4633901 := bstep (se 3 (by rfl) ⟨868856, by rfl⟩ : syracuseStep 4633901 = 1737713) B1737713
theorem B2970929 : Blo 1372005 2970929 := bstep (se 2 (by rfl) ⟨1114098, by rfl⟩ : syracuseStep 2970929 = 2228197) B2228197
theorem B1373491 : Blo 1372005 1373491 := bstep (se 1 (by rfl) ⟨1030118, by rfl⟩ : syracuseStep 1373491 = 2060237) B2060237
theorem B2315587 : Blo 1372005 2315587 := bstep (se 1 (by rfl) ⟨1736690, by rfl⟩ : syracuseStep 2315587 = 3473381) B3473381
theorem B1373507 : Blo 1372005 1373507 := bstep (se 1 (by rfl) ⟨1030130, by rfl⟩ : syracuseStep 1373507 = 2060261) B2060261
theorem B7820621 : Blo 1372005 7820621 := bstep (se 3 (by rfl) ⟨1466366, by rfl⟩ : syracuseStep 7820621 = 2932733) B2932733
theorem B1373523 : Blo 1372005 1373523 := bstep (se 1 (by rfl) ⟨1030142, by rfl⟩ : syracuseStep 1373523 = 2060285) B2060285
theorem B4633955 : Blo 1372005 4633955 := bstep (se 1 (by rfl) ⟨3475466, by rfl⟩ : syracuseStep 4633955 = 6950933) B6950933
theorem B1373539 : Blo 1372005 1373539 := bstep (se 1 (by rfl) ⟨1030154, by rfl⟩ : syracuseStep 1373539 = 2060309) B2060309
theorem B1373555 : Blo 1372005 1373555 := bstep (se 1 (by rfl) ⟨1030166, by rfl⟩ : syracuseStep 1373555 = 2060333) B2060333
theorem B3298691 : Blo 1372005 3298691 := bstep (se 1 (by rfl) ⟨2474018, by rfl⟩ : syracuseStep 3298691 = 4948037) B4948037
theorem B1373571 : Blo 1372005 1373571 := bstep (se 1 (by rfl) ⟨1030178, by rfl⟩ : syracuseStep 1373571 = 2060357) B2060357
theorem B1373587 : Blo 1372005 1373587 := bstep (se 1 (by rfl) ⟨1030190, by rfl⟩ : syracuseStep 1373587 = 2060381) B2060381
theorem B1545619 : Blo 1372005 1545619 := bstep (se 1 (by rfl) ⟨1159214, by rfl⟩ : syracuseStep 1545619 = 2318429) B2318429
theorem B1373603 : Blo 1372005 1373603 := bstep (se 1 (by rfl) ⟨1030202, by rfl⟩ : syracuseStep 1373603 = 2060405) B2060405
theorem B1373619 : Blo 1372005 1373619 := bstep (se 1 (by rfl) ⟨1030214, by rfl⟩ : syracuseStep 1373619 = 2060429) B2060429
theorem B1373635 : Blo 1372005 1373635 := bstep (se 1 (by rfl) ⟨1030226, by rfl⟩ : syracuseStep 1373635 = 2060453) B2060453
theorem B2315729 : Blo 1372005 2315729 := bstep (se 2 (by rfl) ⟨868398, by rfl⟩ : syracuseStep 2315729 = 1736797) B1736797
theorem B1955281 : Blo 1372005 1955281 := bstep (se 2 (by rfl) ⟨733230, by rfl⟩ : syracuseStep 1955281 = 1466461) B1466461
theorem B1373651 : Blo 1372005 1373651 := bstep (se 1 (by rfl) ⟨1030238, by rfl⟩ : syracuseStep 1373651 = 2060477) B2060477
theorem B12056035 : Blo 1372005 12056035 := bstep (se 1 (by rfl) ⟨9042026, by rfl⟩ : syracuseStep 12056035 = 18084053) B18084053
theorem B1373667 : Blo 1372005 1373667 := bstep (se 1 (by rfl) ⟨1030250, by rfl⟩ : syracuseStep 1373667 = 2060501) B2060501
theorem B1373683 : Blo 1372005 1373683 := bstep (se 1 (by rfl) ⟨1030262, by rfl⟩ : syracuseStep 1373683 = 2060525) B2060525
theorem B4347395 : Blo 1372005 4347395 := bstep (se 1 (by rfl) ⟨3260546, by rfl⟩ : syracuseStep 4347395 = 6521093) B6521093
theorem B1373699 : Blo 1372005 1373699 := bstep (se 1 (by rfl) ⟨1030274, by rfl⟩ : syracuseStep 1373699 = 2060549) B2060549
theorem B1373715 : Blo 1372005 1373715 := bstep (se 1 (by rfl) ⟨1030286, by rfl⟩ : syracuseStep 1373715 = 2060573) B2060573
theorem B1373731 : Blo 1372005 1373731 := bstep (se 1 (by rfl) ⟨1030298, by rfl⟩ : syracuseStep 1373731 = 2060597) B2060597
theorem B4396589 : Blo 1372005 4396589 := bstep (se 3 (by rfl) ⟨824360, by rfl⟩ : syracuseStep 4396589 = 1648721) B1648721
theorem B4945457 : Blo 1372005 4945457 := bstep (se 2 (by rfl) ⟨1854546, by rfl⟩ : syracuseStep 4945457 = 3709093) B3709093
theorem B1373747 : Blo 1372005 1373747 := bstep (se 1 (by rfl) ⟨1030310, by rfl⟩ : syracuseStep 1373747 = 2060621) B2060621
theorem B1373763 : Blo 1372005 1373763 := bstep (se 1 (by rfl) ⟨1030322, by rfl⟩ : syracuseStep 1373763 = 2060645) B2060645
theorem B2315857 : Blo 1372005 2315857 := bstep (se 2 (by rfl) ⟨868446, by rfl⟩ : syracuseStep 2315857 = 1736893) B1736893
theorem B1373779 : Blo 1372005 1373779 := bstep (se 1 (by rfl) ⟨1030334, by rfl⟩ : syracuseStep 1373779 = 2060669) B2060669
theorem B1373795 : Blo 1372005 1373795 := bstep (se 1 (by rfl) ⟨1030346, by rfl⟩ : syracuseStep 1373795 = 2060693) B2060693
theorem B4634225 : Blo 1372005 4634225 := bstep (se 2 (by rfl) ⟨1737834, by rfl⟩ : syracuseStep 4634225 = 3475669) B3475669
theorem B6600305 : Blo 1372005 6600305 := bstep (se 2 (by rfl) ⟨2475114, by rfl⟩ : syracuseStep 6600305 = 4950229) B4950229
theorem B2315891 : Blo 1372005 2315891 := bstep (se 1 (by rfl) ⟨1736918, by rfl⟩ : syracuseStep 2315891 = 3473837) B3473837
theorem B1373811 : Blo 1372005 1373811 := bstep (se 1 (by rfl) ⟨1030358, by rfl⟩ : syracuseStep 1373811 = 2060717) B2060717
theorem B1373827 : Blo 1372005 1373827 := bstep (se 1 (by rfl) ⟨1030370, by rfl⟩ : syracuseStep 1373827 = 2060741) B2060741
theorem B1373843 : Blo 1372005 1373843 := bstep (se 1 (by rfl) ⟨1030382, by rfl⟩ : syracuseStep 1373843 = 2060765) B2060765
theorem B1373859 : Blo 1372005 1373859 := bstep (se 1 (by rfl) ⟨1030394, by rfl⟩ : syracuseStep 1373859 = 2060789) B2060789
theorem B1373875 : Blo 1372005 1373875 := bstep (se 1 (by rfl) ⟨1030406, by rfl⟩ : syracuseStep 1373875 = 2060813) B2060813
theorem B1373891 : Blo 1372005 1373891 := bstep (se 1 (by rfl) ⟨1030418, by rfl⟩ : syracuseStep 1373891 = 2060837) B2060837
theorem B1373907 : Blo 1372005 1373907 := bstep (se 1 (by rfl) ⟨1030430, by rfl⟩ : syracuseStep 1373907 = 2060861) B2060861
theorem B14096099 : Blo 1372005 14096099 := bstep (se 1 (by rfl) ⟨10572074, by rfl⟩ : syracuseStep 14096099 = 21144149) B21144149
theorem B1373923 : Blo 1372005 1373923 := bstep (se 1 (by rfl) ⟨1030442, by rfl⟩ : syracuseStep 1373923 = 2060885) B2060885
theorem B4396781 : Blo 1372005 4396781 := bstep (se 3 (by rfl) ⟨824396, by rfl⟩ : syracuseStep 4396781 = 1648793) B1648793
theorem B2316019 : Blo 1372005 2316019 := bstep (se 1 (by rfl) ⟨1737014, by rfl⟩ : syracuseStep 2316019 = 3474029) B3474029
theorem B1373939 : Blo 1372005 1373939 := bstep (se 1 (by rfl) ⟨1030454, by rfl⟩ : syracuseStep 1373939 = 2060909) B2060909
theorem B1373955 : Blo 1372005 1373955 := bstep (se 1 (by rfl) ⟨1030466, by rfl⟩ : syracuseStep 1373955 = 2060933) B2060933
theorem B1373971 : Blo 1372005 1373971 := bstep (se 1 (by rfl) ⟨1030478, by rfl⟩ : syracuseStep 1373971 = 2060957) B2060957
theorem B1373987 : Blo 1372005 1373987 := bstep (se 1 (by rfl) ⟨1030490, by rfl⟩ : syracuseStep 1373987 = 2060981) B2060981
theorem B1374003 : Blo 1372005 1374003 := bstep (se 1 (by rfl) ⟨1030502, by rfl⟩ : syracuseStep 1374003 = 2061005) B2061005
theorem B2316161 : Blo 1372005 2316161 := bstep (se 2 (by rfl) ⟨868560, by rfl⟩ : syracuseStep 2316161 = 1737121) B1737121
theorem B5216177 : Blo 1372005 5216177 := bstep (se 2 (by rfl) ⟨1956066, by rfl⟩ : syracuseStep 5216177 = 3912133) B3912133
theorem B2316289 : Blo 1372005 2316289 := bstep (se 2 (by rfl) ⟨868608, by rfl⟩ : syracuseStep 2316289 = 1737217) B1737217
theorem B15628301 : Blo 1372005 15628301 := bstep (se 3 (by rfl) ⟨2930306, by rfl⟩ : syracuseStep 15628301 = 5860613) B5860613
theorem B29677589 : Blo 1372005 29677589 := bstep (se 6 (by rfl) ⟨695568, by rfl⟩ : syracuseStep 29677589 = 1391137) B1391137
theorem B1955873 : Blo 1372005 1955873 := bstep (se 2 (by rfl) ⟨733452, by rfl⟩ : syracuseStep 1955873 = 1466905) B1466905
theorem B2316323 : Blo 1372005 2316323 := bstep (se 1 (by rfl) ⟨1737242, by rfl⟩ : syracuseStep 2316323 = 3474485) B3474485
theorem B4700273 : Blo 1372005 4700273 := bstep (se 2 (by rfl) ⟨1762602, by rfl⟩ : syracuseStep 4700273 = 3525205) B3525205
theorem B4634765 : Blo 1372005 4634765 := bstep (se 3 (by rfl) ⟨869018, by rfl⟩ : syracuseStep 4634765 = 1738037) B1738037
theorem B2316451 : Blo 1372005 2316451 := bstep (se 1 (by rfl) ⟨1737338, by rfl⟩ : syracuseStep 2316451 = 3474677) B3474677
theorem B2259137 : Blo 1372005 2259137 := bstep (se 2 (by rfl) ⟨847176, by rfl⟩ : syracuseStep 2259137 = 1694353) B1694353
theorem B4634819 : Blo 1372005 4634819 := bstep (se 1 (by rfl) ⟨3476114, by rfl⟩ : syracuseStep 4634819 = 6952229) B6952229
theorem B16939205 : Blo 1372005 16939205 := bstep (se 4 (by rfl) ⟨1588050, by rfl⟩ : syracuseStep 16939205 = 3176101) B3176101
theorem B11729123 : Blo 1372005 11729123 := bstep (se 1 (by rfl) ⟨8796842, by rfl⟩ : syracuseStep 11729123 = 17593685) B17593685
theorem B6953201 : Blo 1372005 6953201 := bstep (se 2 (by rfl) ⟨2607450, by rfl⟩ : syracuseStep 6953201 = 5214901) B5214901
theorem B2316593 : Blo 1372005 2316593 := bstep (se 2 (by rfl) ⟨868722, by rfl⟩ : syracuseStep 2316593 = 1737445) B1737445
theorem B3299633 : Blo 1372005 3299633 := bstep (se 2 (by rfl) ⟨1237362, by rfl⟩ : syracuseStep 3299633 = 2474725) B2474725
theorem B2931025 : Blo 1372005 2931025 := bstep (se 2 (by rfl) ⟨1099134, by rfl⟩ : syracuseStep 2931025 = 2198269) B2198269
theorem B8345969 : Blo 1372005 8345969 := bstep (se 2 (by rfl) ⟨3129738, by rfl⟩ : syracuseStep 8345969 = 6259477) B6259477
theorem B2316721 : Blo 1372005 2316721 := bstep (se 2 (by rfl) ⟨868770, by rfl⟩ : syracuseStep 2316721 = 1737541) B1737541
theorem B4635089 : Blo 1372005 4635089 := bstep (se 2 (by rfl) ⟨1738158, by rfl⟩ : syracuseStep 4635089 = 3476317) B3476317
theorem B2316755 : Blo 1372005 2316755 := bstep (se 1 (by rfl) ⟨1737566, by rfl⟩ : syracuseStep 2316755 = 3475133) B3475133
theorem B2472419 : Blo 1372005 2472419 := bstep (se 1 (by rfl) ⟨1854314, by rfl⟩ : syracuseStep 2472419 = 3708629) B3708629
theorem B3299825 : Blo 1372005 3299825 := bstep (se 2 (by rfl) ⟨1237434, by rfl⟩ : syracuseStep 3299825 = 2474869) B2474869
theorem B5216845 : Blo 1372005 5216845 := bstep (se 3 (by rfl) ⟨978158, by rfl⟩ : syracuseStep 5216845 = 1956317) B1956317
theorem B2316883 : Blo 1372005 2316883 := bstep (se 1 (by rfl) ⟨1737662, by rfl⟩ : syracuseStep 2316883 = 3475325) B3475325
theorem B1587811 : Blo 1372005 1587811 := bstep (se 1 (by rfl) ⟨1190858, by rfl⟩ : syracuseStep 1587811 = 2381717) B2381717
theorem B2317025 : Blo 1372005 2317025 := bstep (se 2 (by rfl) ⟨868884, by rfl⟩ : syracuseStep 2317025 = 1737769) B1737769
theorem B3087089 : Blo 1372005 3087089 := bstep (se 2 (by rfl) ⟨1157658, by rfl⟩ : syracuseStep 3087089 = 2315317) B2315317
theorem B3087107 : Blo 1372005 3087107 := bstep (se 1 (by rfl) ⟨2315330, by rfl⟩ : syracuseStep 3087107 = 4630661) B4630661
theorem B3709709 : Blo 1372005 3709709 := bstep (se 3 (by rfl) ⟨695570, by rfl⟩ : syracuseStep 3709709 = 1391141) B1391141
theorem B2317153 : Blo 1372005 2317153 := bstep (se 2 (by rfl) ⟨868932, by rfl⟩ : syracuseStep 2317153 = 1737865) B1737865
theorem B2317187 : Blo 1372005 2317187 := bstep (se 1 (by rfl) ⟨1737890, by rfl⟩ : syracuseStep 2317187 = 3475781) B3475781
theorem B4635629 : Blo 1372005 4635629 := bstep (se 3 (by rfl) ⟨869180, by rfl⟩ : syracuseStep 4635629 = 1738361) B1738361
theorem B2317315 : Blo 1372005 2317315 := bstep (se 1 (by rfl) ⟨1737986, by rfl⟩ : syracuseStep 2317315 = 3475973) B3475973
theorem B7519237 : Blo 1372005 7519237 := bstep (se 4 (by rfl) ⟨704928, by rfl⟩ : syracuseStep 7519237 = 1409857) B1409857
theorem B3087377 : Blo 1372005 3087377 := bstep (se 2 (by rfl) ⟨1157766, by rfl⟩ : syracuseStep 3087377 = 2315533) B2315533
theorem B3087395 : Blo 1372005 3087395 := bstep (se 1 (by rfl) ⟨2315546, by rfl⟩ : syracuseStep 3087395 = 4631093) B4631093
theorem B4635683 : Blo 1372005 4635683 := bstep (se 1 (by rfl) ⟨3476762, by rfl⟩ : syracuseStep 4635683 = 6953525) B6953525
theorem B9657413 : Blo 1372005 9657413 := bstep (se 4 (by rfl) ⟨905382, by rfl⟩ : syracuseStep 9657413 = 1810765) B1810765
theorem B3759203 : Blo 1372005 3759203 := bstep (se 1 (by rfl) ⟨2819402, by rfl⟩ : syracuseStep 3759203 = 5638805) B5638805
theorem B4947085 : Blo 1372005 4947085 := bstep (se 3 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 4947085 = 1855157) B1855157
theorem B2317457 : Blo 1372005 2317457 := bstep (se 2 (by rfl) ⟨869046, by rfl⟩ : syracuseStep 2317457 = 1738093) B1738093
theorem B26410211 : Blo 1372005 26410211 := bstep (se 1 (by rfl) ⟨19807658, by rfl⟩ : syracuseStep 26410211 = 39615317) B39615317
theorem B3300593 : Blo 1372005 3300593 := bstep (se 2 (by rfl) ⟨1237722, by rfl⟩ : syracuseStep 3300593 = 2475445) B2475445
theorem B2317585 : Blo 1372005 2317585 := bstep (se 2 (by rfl) ⟨869094, by rfl⟩ : syracuseStep 2317585 = 1738189) B1738189
theorem B3087665 : Blo 1372005 3087665 := bstep (se 2 (by rfl) ⟨1157874, by rfl⟩ : syracuseStep 3087665 = 2315749) B2315749
theorem B4635953 : Blo 1372005 4635953 := bstep (se 2 (by rfl) ⟨1738482, by rfl⟩ : syracuseStep 4635953 = 3476965) B3476965
theorem B2317619 : Blo 1372005 2317619 := bstep (se 1 (by rfl) ⟨1738214, by rfl⟩ : syracuseStep 2317619 = 3476429) B3476429
theorem B3087683 : Blo 1372005 3087683 := bstep (se 1 (by rfl) ⟨2315762, by rfl⟩ : syracuseStep 3087683 = 4631525) B4631525
theorem B14089571 : Blo 1372005 14089571 := bstep (se 1 (by rfl) ⟨10567178, by rfl⟩ : syracuseStep 14089571 = 21134357) B21134357
theorem B2317747 : Blo 1372005 2317747 := bstep (se 1 (by rfl) ⟨1738310, by rfl⟩ : syracuseStep 2317747 = 3476621) B3476621
theorem B4398563 : Blo 1372005 4398563 := bstep (se 1 (by rfl) ⟨3298922, by rfl⟩ : syracuseStep 4398563 = 6597845) B6597845
theorem B2317889 : Blo 1372005 2317889 := bstep (se 2 (by rfl) ⟨869208, by rfl⟩ : syracuseStep 2317889 = 1738417) B1738417
theorem B3710531 : Blo 1372005 3710531 := bstep (se 1 (by rfl) ⟨2782898, by rfl⟩ : syracuseStep 3710531 = 5565797) B5565797
theorem B3087953 : Blo 1372005 3087953 := bstep (se 2 (by rfl) ⟨1157982, by rfl⟩ : syracuseStep 3087953 = 2315965) B2315965
theorem B4349521 : Blo 1372005 4349521 := bstep (se 2 (by rfl) ⟨1631070, by rfl⟩ : syracuseStep 4349521 = 3262141) B3262141
theorem B3087971 : Blo 1372005 3087971 := bstep (se 1 (by rfl) ⟨2315978, by rfl⟩ : syracuseStep 3087971 = 4631957) B4631957
theorem B3473027 : Blo 1372005 3473027 := bstep (se 1 (by rfl) ⟨2604770, by rfl⟩ : syracuseStep 3473027 = 5209541) B5209541
theorem B7814789 : Blo 1372005 7814789 := bstep (se 4 (by rfl) ⟨732636, by rfl⟩ : syracuseStep 7814789 = 1465273) B1465273
theorem B6954659 : Blo 1372005 6954659 := bstep (se 1 (by rfl) ⟨5215994, by rfl⟩ : syracuseStep 6954659 = 10431989) B10431989
theorem B2318017 : Blo 1372005 2318017 := bstep (se 2 (by rfl) ⟨869256, by rfl⟩ : syracuseStep 2318017 = 1738513) B1738513
theorem B10428101 : Blo 1372005 10428101 := bstep (se 4 (by rfl) ⟨977634, by rfl⟩ : syracuseStep 10428101 = 1955269) B1955269
theorem B7421645 : Blo 1372005 7421645 := bstep (se 3 (by rfl) ⟨1391558, by rfl⟩ : syracuseStep 7421645 = 2783117) B2783117
theorem B2318051 : Blo 1372005 2318051 := bstep (se 1 (by rfl) ⟨1738538, by rfl⟩ : syracuseStep 2318051 = 3477077) B3477077
theorem B15040241 : Blo 1372005 15040241 := bstep (se 2 (by rfl) ⟨5640090, by rfl⟩ : syracuseStep 15040241 = 11280181) B11280181
theorem B2228003 : Blo 1372005 2228003 := bstep (se 1 (by rfl) ⟨1671002, by rfl⟩ : syracuseStep 2228003 = 3342005) B3342005
theorem B3473219 : Blo 1372005 3473219 := bstep (se 1 (by rfl) ⟨2604914, by rfl⟩ : syracuseStep 3473219 = 5209829) B5209829
theorem B4636493 : Blo 1372005 4636493 := bstep (se 3 (by rfl) ⟨869342, by rfl⟩ : syracuseStep 4636493 = 1738685) B1738685
theorem B2604899 : Blo 1372005 2604899 := bstep (se 1 (by rfl) ⟨1953674, by rfl⟩ : syracuseStep 2604899 = 3907349) B3907349
theorem B2318179 : Blo 1372005 2318179 := bstep (se 1 (by rfl) ⟨1738634, by rfl⟩ : syracuseStep 2318179 = 3477269) B3477269
theorem B3088241 : Blo 1372005 3088241 := bstep (se 2 (by rfl) ⟨1158090, by rfl⟩ : syracuseStep 3088241 = 2316181) B2316181
theorem B1736579 : Blo 1372005 1736579 := bstep (se 1 (by rfl) ⟨1302434, by rfl⟩ : syracuseStep 1736579 = 2604869) B2604869
theorem B3088259 : Blo 1372005 3088259 := bstep (se 1 (by rfl) ⟨2316194, by rfl⟩ : syracuseStep 3088259 = 4632389) B4632389
theorem B4636547 : Blo 1372005 4636547 := bstep (se 1 (by rfl) ⟨3477410, by rfl⟩ : syracuseStep 4636547 = 6954821) B6954821
theorem B15859637 : Blo 1372005 15859637 := bstep (se 5 (by rfl) ⟨743420, by rfl⟩ : syracuseStep 15859637 = 1486841) B1486841
theorem B2318321 : Blo 1372005 2318321 := bstep (se 2 (by rfl) ⟨869370, by rfl⟩ : syracuseStep 2318321 = 1738741) B1738741
theorem B3088385 : Blo 1372005 3088385 := bstep (se 2 (by rfl) ⟨1158144, by rfl⟩ : syracuseStep 3088385 = 2316289) B2316289
theorem B10420325 : Blo 1372005 10420325 := bstep (se 4 (by rfl) ⟨976905, by rfl⟩ : syracuseStep 10420325 = 1953811) B1953811
theorem B5210315 : Blo 1372005 5210315 := bstep (se 1 (by rfl) ⟨3907736, by rfl⟩ : syracuseStep 5210315 = 7815473) B7815473
theorem B3088601 : Blo 1372005 3088601 := bstep (se 2 (by rfl) ⟨1158225, by rfl⟩ : syracuseStep 3088601 = 2316451) B2316451
theorem B2973953 : Blo 1372005 2973953 := bstep (se 2 (by rfl) ⟨1115232, by rfl⟩ : syracuseStep 2973953 = 2230465) B2230465
theorem B3088691 : Blo 1372005 3088691 := bstep (se 1 (by rfl) ⟨2316518, by rfl⟩ : syracuseStep 3088691 = 4633037) B4633037
theorem B4636979 : Blo 1372005 4636979 := bstep (se 1 (by rfl) ⟨3477734, by rfl⟩ : syracuseStep 4636979 = 6955469) B6955469
theorem B1565015 : Blo 1372005 1565015 := bstep (se 1 (by rfl) ⟨1173761, by rfl⟩ : syracuseStep 1565015 = 2347523) B2347523
theorem B3088727 : Blo 1372005 3088727 := bstep (se 1 (by rfl) ⟨2316545, by rfl⟩ : syracuseStep 3088727 = 4633091) B4633091
theorem B5210513 : Blo 1372005 5210513 := bstep (se 2 (by rfl) ⟨1953942, by rfl⟩ : syracuseStep 5210513 = 3907885) B3907885
theorem B3908033 : Blo 1372005 3908033 := bstep (se 2 (by rfl) ⟨1465512, by rfl⟩ : syracuseStep 3908033 = 2931025) B2931025
theorem B3473867 : Blo 1372005 3473867 := bstep (se 1 (by rfl) ⟨2605400, by rfl⟩ : syracuseStep 3473867 = 5210801) B5210801
theorem B1737227 : Blo 1372005 1737227 := bstep (se 1 (by rfl) ⟨1302920, by rfl⟩ : syracuseStep 1737227 = 2605841) B2605841
theorem B3088907 : Blo 1372005 3088907 := bstep (se 1 (by rfl) ⟨2316680, by rfl⟩ : syracuseStep 3088907 = 4633361) B4633361
theorem B3088961 : Blo 1372005 3088961 := bstep (se 2 (by rfl) ⟨1158360, by rfl⟩ : syracuseStep 3088961 = 2316721) B2316721
theorem B4637249 : Blo 1372005 4637249 := bstep (se 2 (by rfl) ⟨1738968, by rfl⟩ : syracuseStep 4637249 = 3477937) B3477937
theorem B10420811 : Blo 1372005 10420811 := bstep (se 1 (by rfl) ⟨7815608, by rfl⟩ : syracuseStep 10420811 = 15631217) B15631217
theorem B2474753 : Blo 1372005 2474753 := bstep (se 2 (by rfl) ⟨928032, by rfl⟩ : syracuseStep 2474753 = 1856065) B1856065
theorem B6955793 : Blo 1372005 6955793 := bstep (se 2 (by rfl) ⟨2608422, by rfl⟩ : syracuseStep 6955793 = 5216845) B5216845
theorem B3908375 : Blo 1372005 3908375 := bstep (se 1 (by rfl) ⟨2931281, by rfl⟩ : syracuseStep 3908375 = 5862563) B5862563
theorem B4399895 : Blo 1372005 4399895 := bstep (se 1 (by rfl) ⟨3299921, by rfl⟩ : syracuseStep 4399895 = 6599843) B6599843
theorem B3089177 : Blo 1372005 3089177 := bstep (se 2 (by rfl) ⟨1158441, by rfl⟩ : syracuseStep 3089177 = 2316883) B2316883
theorem B3572531 : Blo 1372005 3572531 := bstep (se 1 (by rfl) ⟨2679398, by rfl⟩ : syracuseStep 3572531 = 5358797) B5358797
theorem B7824221 : Blo 1372005 7824221 := bstep (se 3 (by rfl) ⟨1467041, by rfl⟩ : syracuseStep 7824221 = 2934083) B2934083
theorem B3089267 : Blo 1372005 3089267 := bstep (se 1 (by rfl) ⟨2316950, by rfl⟩ : syracuseStep 3089267 = 4633901) B4633901
theorem B3089303 : Blo 1372005 3089303 := bstep (se 1 (by rfl) ⟨2316977, by rfl⟩ : syracuseStep 3089303 = 4633955) B4633955
theorem B5948333 : Blo 1372005 5948333 := bstep (se 3 (by rfl) ⟨1115312, by rfl⟩ : syracuseStep 5948333 = 2230625) B2230625
theorem B9896995 : Blo 1372005 9896995 := bstep (se 1 (by rfl) ⟨7422746, by rfl⟩ : syracuseStep 9896995 = 14845493) B14845493
theorem B3130433 : Blo 1372005 3130433 := bstep (se 2 (by rfl) ⟨1173912, by rfl⟩ : syracuseStep 3130433 = 2347825) B2347825
theorem B3089483 : Blo 1372005 3089483 := bstep (se 1 (by rfl) ⟨2317112, by rfl⟩ : syracuseStep 3089483 = 4634225) B4634225
theorem B4400203 : Blo 1372005 4400203 := bstep (se 1 (by rfl) ⟨3300152, by rfl⟩ : syracuseStep 4400203 = 6600305) B6600305
theorem B3089537 : Blo 1372005 3089537 := bstep (se 2 (by rfl) ⟨1158576, by rfl⟩ : syracuseStep 3089537 = 2317153) B2317153
theorem B5211287 : Blo 1372005 5211287 := bstep (se 1 (by rfl) ⟨3908465, by rfl⟩ : syracuseStep 5211287 = 7816931) B7816931
theorem B9397399 : Blo 1372005 9397399 := bstep (se 1 (by rfl) ⟨7048049, by rfl⟩ : syracuseStep 9397399 = 14096099) B14096099
theorem B50136245 : Blo 1372005 50136245 := bstep (se 5 (by rfl) ⟨2350136, by rfl⟩ : syracuseStep 50136245 = 4700273) B4700273
theorem B1737931 : Blo 1372005 1737931 := bstep (se 1 (by rfl) ⟨1303448, by rfl⟩ : syracuseStep 1737931 = 2606897) B2606897
theorem B2606411 : Blo 1372005 2606411 := bstep (se 1 (by rfl) ⟨1954808, by rfl⟩ : syracuseStep 2606411 = 3909617) B3909617
theorem B3089753 : Blo 1372005 3089753 := bstep (se 2 (by rfl) ⟨1158657, by rfl⟩ : syracuseStep 3089753 = 2317315) B2317315
theorem B5211485 : Blo 1372005 5211485 := bstep (se 3 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 5211485 = 1954307) B1954307
theorem B19785059 : Blo 1372005 19785059 := bstep (se 1 (by rfl) ⟨14838794, by rfl⟩ : syracuseStep 19785059 = 29677589) B29677589
theorem B3474839 : Blo 1372005 3474839 := bstep (se 1 (by rfl) ⟨2606129, by rfl⟩ : syracuseStep 3474839 = 5212259) B5212259
theorem B12387761 : Blo 1372005 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B3089843 : Blo 1372005 3089843 := bstep (se 1 (by rfl) ⟨2317382, by rfl⟩ : syracuseStep 3089843 = 4634765) B4634765
theorem B3089879 : Blo 1372005 3089879 := bstep (se 1 (by rfl) ⟨2317409, by rfl⟩ : syracuseStep 3089879 = 4634819) B4634819
theorem B1738199 : Blo 1372005 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B2606593 : Blo 1372005 2606593 := bstep (se 2 (by rfl) ⟨977472, by rfl⟩ : syracuseStep 2606593 = 1954945) B1954945
theorem B6596113 : Blo 1372005 6596113 := bstep (se 2 (by rfl) ⟨2473542, by rfl⟩ : syracuseStep 6596113 = 4947085) B4947085
theorem B5563979 : Blo 1372005 5563979 := bstep (se 1 (by rfl) ⟨4172984, by rfl⟩ : syracuseStep 5563979 = 8345969) B8345969
theorem B10430045 : Blo 1372005 10430045 := bstep (se 3 (by rfl) ⟨1955633, by rfl⟩ : syracuseStep 10430045 = 3911267) B3911267
theorem B3090059 : Blo 1372005 3090059 := bstep (se 1 (by rfl) ⟨2317544, by rfl⟩ : syracuseStep 3090059 = 4635089) B4635089
theorem B1648279 : Blo 1372005 1648279 := bstep (se 1 (by rfl) ⟨1236209, by rfl⟩ : syracuseStep 1648279 = 2472419) B2472419
theorem B6948503 : Blo 1372005 6948503 := bstep (se 1 (by rfl) ⟨5211377, by rfl⟩ : syracuseStep 6948503 = 10422755) B10422755
theorem B3090113 : Blo 1372005 3090113 := bstep (se 2 (by rfl) ⟨1158792, by rfl⟩ : syracuseStep 3090113 = 2317585) B2317585
theorem B2058059 : Blo 1372005 2058059 := bstep (se 1 (by rfl) ⟨1543544, by rfl⟩ : syracuseStep 2058059 = 3087089) B3087089
theorem B2058071 : Blo 1372005 2058071 := bstep (se 1 (by rfl) ⟨1543553, by rfl⟩ : syracuseStep 2058071 = 3087107) B3087107
theorem B1673047 : Blo 1372005 1673047 := bstep (se 1 (by rfl) ⟨1254785, by rfl⟩ : syracuseStep 1673047 = 2509571) B2509571
theorem B2058137 : Blo 1372005 2058137 := bstep (se 2 (by rfl) ⟨771801, by rfl⟩ : syracuseStep 2058137 = 1543603) B1543603
theorem B3090329 : Blo 1372005 3090329 := bstep (se 2 (by rfl) ⟨1158873, by rfl⟩ : syracuseStep 3090329 = 2317747) B2317747
theorem B2607041 : Blo 1372005 2607041 := bstep (se 2 (by rfl) ⟨977640, by rfl⟩ : syracuseStep 2607041 = 1955281) B1955281
theorem B11724749 : Blo 1372005 11724749 := bstep (se 3 (by rfl) ⟨2198390, by rfl⟩ : syracuseStep 11724749 = 4396781) B4396781
theorem B16074713 : Blo 1372005 16074713 := bstep (se 2 (by rfl) ⟨6028017, by rfl⟩ : syracuseStep 16074713 = 12056035) B12056035
theorem B3090419 : Blo 1372005 3090419 := bstep (se 1 (by rfl) ⟨2317814, by rfl⟩ : syracuseStep 3090419 = 4635629) B4635629
theorem B2058251 : Blo 1372005 2058251 := bstep (se 1 (by rfl) ⟨1543688, by rfl⟩ : syracuseStep 2058251 = 3087377) B3087377
theorem B2058263 : Blo 1372005 2058263 := bstep (se 1 (by rfl) ⟨1543697, by rfl⟩ : syracuseStep 2058263 = 3087395) B3087395
theorem B3090455 : Blo 1372005 3090455 := bstep (se 1 (by rfl) ⟨2317841, by rfl⟩ : syracuseStep 3090455 = 4635683) B4635683
theorem B3475507 : Blo 1372005 3475507 := bstep (se 1 (by rfl) ⟨2606630, by rfl⟩ : syracuseStep 3475507 = 5213261) B5213261
theorem B5867585 : Blo 1372005 5867585 := bstep (se 2 (by rfl) ⟨2200344, by rfl⟩ : syracuseStep 5867585 = 4400689) B4400689
theorem B2058329 : Blo 1372005 2058329 := bstep (se 2 (by rfl) ⟨771873, by rfl⟩ : syracuseStep 2058329 = 1543747) B1543747
theorem B7424131 : Blo 1372005 7424131 := bstep (se 1 (by rfl) ⟨5568098, by rfl⟩ : syracuseStep 7424131 = 11136197) B11136197
theorem B1738903 : Blo 1372005 1738903 := bstep (se 1 (by rfl) ⟨1304177, by rfl⟩ : syracuseStep 1738903 = 2608355) B2608355
theorem B17606807 : Blo 1372005 17606807 := bstep (se 1 (by rfl) ⟨13205105, by rfl⟩ : syracuseStep 17606807 = 26410211) B26410211
theorem B3475649 : Blo 1372005 3475649 := bstep (se 2 (by rfl) ⟨1303368, by rfl⟩ : syracuseStep 3475649 = 2606737) B2606737
theorem B2058443 : Blo 1372005 2058443 := bstep (se 1 (by rfl) ⟨1543832, by rfl⟩ : syracuseStep 2058443 = 3087665) B3087665
theorem B3090635 : Blo 1372005 3090635 := bstep (se 1 (by rfl) ⟨2317976, by rfl⟩ : syracuseStep 3090635 = 4635953) B4635953
theorem B2058455 : Blo 1372005 2058455 := bstep (se 1 (by rfl) ⟨1543841, by rfl⟩ : syracuseStep 2058455 = 3087683) B3087683
theorem B3090689 : Blo 1372005 3090689 := bstep (se 2 (by rfl) ⟨1159008, by rfl⟩ : syracuseStep 3090689 = 2318017) B2318017
theorem B2607383 : Blo 1372005 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B2058521 : Blo 1372005 2058521 := bstep (se 2 (by rfl) ⟨771945, by rfl⟩ : syracuseStep 2058521 = 1543891) B1543891
theorem B4630877 : Blo 1372005 4630877 := bstep (se 3 (by rfl) ⟨868289, by rfl⟩ : syracuseStep 4630877 = 1736579) B1736579
theorem B2058635 : Blo 1372005 2058635 := bstep (se 1 (by rfl) ⟨1543976, by rfl⟩ : syracuseStep 2058635 = 3087953) B3087953
theorem B2058647 : Blo 1372005 2058647 := bstep (se 1 (by rfl) ⟨1543985, by rfl⟩ : syracuseStep 2058647 = 3087971) B3087971
theorem B10570135 : Blo 1372005 10570135 := bstep (se 1 (by rfl) ⟨7927601, by rfl⟩ : syracuseStep 10570135 = 15855203) B15855203
theorem B5867927 : Blo 1372005 5867927 := bstep (se 1 (by rfl) ⟨4400945, by rfl⟩ : syracuseStep 5867927 = 8801891) B8801891
theorem B2058713 : Blo 1372005 2058713 := bstep (se 2 (by rfl) ⟨772017, by rfl⟩ : syracuseStep 2058713 = 1544035) B1544035
theorem B3090905 : Blo 1372005 3090905 := bstep (se 2 (by rfl) ⟨1159089, by rfl⟩ : syracuseStep 3090905 = 2318179) B2318179
theorem B1485335 : Blo 1372005 1485335 := bstep (se 1 (by rfl) ⟨1114001, by rfl⟩ : syracuseStep 1485335 = 2228003) B2228003
theorem B3090995 : Blo 1372005 3090995 := bstep (se 1 (by rfl) ⟨2318246, by rfl⟩ : syracuseStep 3090995 = 4636493) B4636493
theorem B2058827 : Blo 1372005 2058827 := bstep (se 1 (by rfl) ⟨1544120, by rfl⟩ : syracuseStep 2058827 = 3088241) B3088241
theorem B2058839 : Blo 1372005 2058839 := bstep (se 1 (by rfl) ⟨1544129, by rfl⟩ : syracuseStep 2058839 = 3088259) B3088259
theorem B3091031 : Blo 1372005 3091031 := bstep (se 1 (by rfl) ⟨2318273, by rfl⟩ : syracuseStep 3091031 = 4636547) B4636547
theorem B2058905 : Blo 1372005 2058905 := bstep (se 2 (by rfl) ⟨772089, by rfl⟩ : syracuseStep 2058905 = 1544179) B1544179
theorem B40102597 : Blo 1372005 40102597 := bstep (se 4 (by rfl) ⟨3759618, by rfl⟩ : syracuseStep 40102597 = 7519237) B7519237
theorem B9898757 : Blo 1372005 9898757 := bstep (se 4 (by rfl) ⟨928008, by rfl⟩ : syracuseStep 9898757 = 1856017) B1856017
theorem B2059019 : Blo 1372005 2059019 := bstep (se 1 (by rfl) ⟨1544264, by rfl⟩ : syracuseStep 2059019 = 3088529) B3088529
theorem B3091211 : Blo 1372005 3091211 := bstep (se 1 (by rfl) ⟨2318408, by rfl⟩ : syracuseStep 3091211 = 4636817) B4636817
theorem B2059031 : Blo 1372005 2059031 := bstep (se 1 (by rfl) ⟨1544273, by rfl⟩ : syracuseStep 2059031 = 3088547) B3088547
theorem B3091265 : Blo 1372005 3091265 := bstep (se 2 (by rfl) ⟨1159224, by rfl⟩ : syracuseStep 3091265 = 2318449) B2318449
theorem B2059097 : Blo 1372005 2059097 := bstep (se 2 (by rfl) ⟨772161, by rfl⟩ : syracuseStep 2059097 = 1544323) B1544323
theorem B3910493 : Blo 1372005 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B2198423 : Blo 1372005 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B2608051 : Blo 1372005 2608051 := bstep (se 1 (by rfl) ⟨1956038, by rfl⟩ : syracuseStep 2608051 = 3912077) B3912077
theorem B2059211 : Blo 1372005 2059211 := bstep (se 1 (by rfl) ⟨1544408, by rfl⟩ : syracuseStep 2059211 = 3088817) B3088817
theorem B2059223 : Blo 1372005 2059223 := bstep (se 1 (by rfl) ⟨1544417, by rfl⟩ : syracuseStep 2059223 = 3088835) B3088835
theorem B2059289 : Blo 1372005 2059289 := bstep (se 2 (by rfl) ⟨772233, by rfl⟩ : syracuseStep 2059289 = 1544467) B1544467
theorem B3091481 : Blo 1372005 3091481 := bstep (se 2 (by rfl) ⟨1159305, by rfl⟩ : syracuseStep 3091481 = 2318611) B2318611
theorem B5565505 : Blo 1372005 5565505 := bstep (se 2 (by rfl) ⟨2087064, by rfl⟩ : syracuseStep 5565505 = 4174129) B4174129
theorem B2059403 : Blo 1372005 2059403 := bstep (se 1 (by rfl) ⟨1544552, by rfl⟩ : syracuseStep 2059403 = 3089105) B3089105
theorem B2059415 : Blo 1372005 2059415 := bstep (se 1 (by rfl) ⟨1544561, by rfl⟩ : syracuseStep 2059415 = 3089123) B3089123
theorem B3910835 : Blo 1372005 3910835 := bstep (se 1 (by rfl) ⟨2933126, by rfl⟩ : syracuseStep 3910835 = 5866253) B5866253
theorem B28183733 : Blo 1372005 28183733 := bstep (se 5 (by rfl) ⟨1321112, by rfl⟩ : syracuseStep 28183733 = 2642225) B2642225
theorem B2059481 : Blo 1372005 2059481 := bstep (se 2 (by rfl) ⟨772305, by rfl⟩ : syracuseStep 2059481 = 1544611) B1544611
theorem B5213443 : Blo 1372005 5213443 := bstep (se 1 (by rfl) ⟨3910082, by rfl⟩ : syracuseStep 5213443 = 7820165) B7820165
theorem B2198807 : Blo 1372005 2198807 := bstep (se 1 (by rfl) ⟨1649105, by rfl⟩ : syracuseStep 2198807 = 3298211) B3298211
theorem B3132695 : Blo 1372005 3132695 := bstep (se 1 (by rfl) ⟨2349521, by rfl⟩ : syracuseStep 3132695 = 4699043) B4699043
theorem B2059595 : Blo 1372005 2059595 := bstep (se 1 (by rfl) ⟨1544696, by rfl⟩ : syracuseStep 2059595 = 3089393) B3089393
theorem B2059607 : Blo 1372005 2059607 := bstep (se 1 (by rfl) ⟨1544705, by rfl⟩ : syracuseStep 2059607 = 3089411) B3089411
theorem B1543531 : Blo 1372005 1543531 := bstep (se 1 (by rfl) ⟨1157648, by rfl⟩ : syracuseStep 1543531 = 2315297) B2315297
theorem B2198935 : Blo 1372005 2198935 := bstep (se 1 (by rfl) ⟨1649201, by rfl⟩ : syracuseStep 2198935 = 3298403) B3298403
theorem B2059673 : Blo 1372005 2059673 := bstep (se 2 (by rfl) ⟨772377, by rfl⟩ : syracuseStep 2059673 = 1544755) B1544755
theorem B3476915 : Blo 1372005 3476915 := bstep (se 1 (by rfl) ⟨2607686, by rfl⟩ : syracuseStep 3476915 = 5215373) B5215373
theorem B4632011 : Blo 1372005 4632011 := bstep (se 1 (by rfl) ⟨3474008, by rfl⟩ : syracuseStep 4632011 = 6948017) B6948017
theorem B1543639 : Blo 1372005 1543639 := bstep (se 1 (by rfl) ⟨1157729, by rfl⟩ : syracuseStep 1543639 = 2315459) B2315459
theorem B2117081 : Blo 1372005 2117081 := bstep (se 2 (by rfl) ⟨793905, by rfl⟩ : syracuseStep 2117081 = 1587811) B1587811
theorem B2059787 : Blo 1372005 2059787 := bstep (se 1 (by rfl) ⟨1544840, by rfl⟩ : syracuseStep 2059787 = 3089681) B3089681
theorem B2059799 : Blo 1372005 2059799 := bstep (se 1 (by rfl) ⟨1544849, by rfl⟩ : syracuseStep 2059799 = 3089699) B3089699
theorem B5213747 : Blo 1372005 5213747 := bstep (se 1 (by rfl) ⟨3910310, by rfl⟩ : syracuseStep 5213747 = 7820621) B7820621
theorem B2059865 : Blo 1372005 2059865 := bstep (se 2 (by rfl) ⟨772449, by rfl⟩ : syracuseStep 2059865 = 1544899) B1544899
theorem B8916581 : Blo 1372005 8916581 := bstep (se 4 (by rfl) ⟨835929, by rfl⟩ : syracuseStep 8916581 = 1671859) B1671859
theorem B1543819 : Blo 1372005 1543819 := bstep (se 1 (by rfl) ⟨1157864, by rfl⟩ : syracuseStep 1543819 = 2315729) B2315729
theorem B3296971 : Blo 1372005 3296971 := bstep (se 1 (by rfl) ⟨2472728, by rfl⟩ : syracuseStep 3296971 = 4945457) B4945457
theorem B2059979 : Blo 1372005 2059979 := bstep (se 1 (by rfl) ⟨1544984, by rfl⟩ : syracuseStep 2059979 = 3089969) B3089969
theorem B2059991 : Blo 1372005 2059991 := bstep (se 1 (by rfl) ⟨1544993, by rfl⟩ : syracuseStep 2059991 = 3089987) B3089987
theorem B4632281 : Blo 1372005 4632281 := bstep (se 2 (by rfl) ⟨1737105, by rfl⟩ : syracuseStep 4632281 = 3474211) B3474211
theorem B1543927 : Blo 1372005 1543927 := bstep (se 1 (by rfl) ⟨1157945, by rfl⟩ : syracuseStep 1543927 = 2315891) B2315891
theorem B2060057 : Blo 1372005 2060057 := bstep (se 2 (by rfl) ⟨772521, by rfl⟩ : syracuseStep 2060057 = 1545043) B1545043
theorem B1372011 : Blo 1372005 1372011 := bstep (se 1 (by rfl) ⟨1029008, by rfl⟩ : syracuseStep 1372011 = 2058017) B2058017
theorem B1372023 : Blo 1372005 1372023 := bstep (se 1 (by rfl) ⟨1029017, by rfl⟩ : syracuseStep 1372023 = 2058035) B2058035
theorem B1372043 : Blo 1372005 1372043 := bstep (se 1 (by rfl) ⟨1029032, by rfl⟩ : syracuseStep 1372043 = 2058065) B2058065
theorem B2060171 : Blo 1372005 2060171 := bstep (se 1 (by rfl) ⟨1545128, by rfl⟩ : syracuseStep 2060171 = 3090257) B3090257
theorem B1372055 : Blo 1372005 1372055 := bstep (se 1 (by rfl) ⟨1029041, by rfl⟩ : syracuseStep 1372055 = 2058083) B2058083
theorem B2060183 : Blo 1372005 2060183 := bstep (se 1 (by rfl) ⟨1545137, by rfl⟩ : syracuseStep 2060183 = 3090275) B3090275
theorem B1372075 : Blo 1372005 1372075 := bstep (se 1 (by rfl) ⟨1029056, by rfl⟩ : syracuseStep 1372075 = 2058113) B2058113
theorem B1544107 : Blo 1372005 1544107 := bstep (se 1 (by rfl) ⟨1158080, by rfl⟩ : syracuseStep 1544107 = 2316161) B2316161
theorem B1372087 : Blo 1372005 1372087 := bstep (se 1 (by rfl) ⟨1029065, by rfl⟩ : syracuseStep 1372087 = 2058131) B2058131
theorem B1372107 : Blo 1372005 1372107 := bstep (se 1 (by rfl) ⟨1029080, by rfl⟩ : syracuseStep 1372107 = 2058161) B2058161
theorem B3477451 : Blo 1372005 3477451 := bstep (se 1 (by rfl) ⟨2608088, by rfl⟩ : syracuseStep 3477451 = 5216177) B5216177
theorem B1372119 : Blo 1372005 1372119 := bstep (se 1 (by rfl) ⟨1029089, by rfl⟩ : syracuseStep 1372119 = 2058179) B2058179
theorem B2060249 : Blo 1372005 2060249 := bstep (se 2 (by rfl) ⟨772593, by rfl⟩ : syracuseStep 2060249 = 1545187) B1545187
theorem B1372139 : Blo 1372005 1372139 := bstep (se 1 (by rfl) ⟨1029104, by rfl⟩ : syracuseStep 1372139 = 2058209) B2058209
theorem B1372151 : Blo 1372005 1372151 := bstep (se 1 (by rfl) ⟨1029113, by rfl⟩ : syracuseStep 1372151 = 2058227) B2058227
theorem B1372171 : Blo 1372005 1372171 := bstep (se 1 (by rfl) ⟨1029128, by rfl⟩ : syracuseStep 1372171 = 2058257) B2058257
theorem B1372183 : Blo 1372005 1372183 := bstep (se 1 (by rfl) ⟨1029137, by rfl⟩ : syracuseStep 1372183 = 2058275) B2058275
theorem B1544215 : Blo 1372005 1544215 := bstep (se 1 (by rfl) ⟨1158161, by rfl⟩ : syracuseStep 1544215 = 2316323) B2316323
theorem B1372203 : Blo 1372005 1372203 := bstep (se 1 (by rfl) ⟨1029152, by rfl⟩ : syracuseStep 1372203 = 2058305) B2058305
theorem B1372215 : Blo 1372005 1372215 := bstep (se 1 (by rfl) ⟨1029161, by rfl⟩ : syracuseStep 1372215 = 2058323) B2058323
theorem B1372235 : Blo 1372005 1372235 := bstep (se 1 (by rfl) ⟨1029176, by rfl⟩ : syracuseStep 1372235 = 2058353) B2058353
theorem B2060363 : Blo 1372005 2060363 := bstep (se 1 (by rfl) ⟨1545272, by rfl⟩ : syracuseStep 2060363 = 3090545) B3090545
theorem B1372247 : Blo 1372005 1372247 := bstep (se 1 (by rfl) ⟨1029185, by rfl⟩ : syracuseStep 1372247 = 2058371) B2058371
theorem B2060375 : Blo 1372005 2060375 := bstep (se 1 (by rfl) ⟨1545281, by rfl⟩ : syracuseStep 2060375 = 3090563) B3090563
theorem B3477593 : Blo 1372005 3477593 := bstep (se 2 (by rfl) ⟨1304097, by rfl⟩ : syracuseStep 3477593 = 2608195) B2608195
theorem B1372267 : Blo 1372005 1372267 := bstep (se 1 (by rfl) ⟨1029200, by rfl⟩ : syracuseStep 1372267 = 2058401) B2058401
theorem B1372279 : Blo 1372005 1372279 := bstep (se 1 (by rfl) ⟨1029209, by rfl⟩ : syracuseStep 1372279 = 2058419) B2058419
theorem B11292803 : Blo 1372005 11292803 := bstep (se 1 (by rfl) ⟨8469602, by rfl⟩ : syracuseStep 11292803 = 16939205) B16939205
theorem B1372299 : Blo 1372005 1372299 := bstep (se 1 (by rfl) ⟨1029224, by rfl⟩ : syracuseStep 1372299 = 2058449) B2058449
theorem B1372311 : Blo 1372005 1372311 := bstep (se 1 (by rfl) ⟨1029233, by rfl⟩ : syracuseStep 1372311 = 2058467) B2058467
theorem B7819415 : Blo 1372005 7819415 := bstep (se 1 (by rfl) ⟨5864561, by rfl⟩ : syracuseStep 7819415 = 11729123) B11729123
theorem B11137175 : Blo 1372005 11137175 := bstep (se 1 (by rfl) ⟨8352881, by rfl⟩ : syracuseStep 11137175 = 16705763) B16705763
theorem B2060441 : Blo 1372005 2060441 := bstep (se 2 (by rfl) ⟨772665, by rfl⟩ : syracuseStep 2060441 = 1545331) B1545331
theorem B1372331 : Blo 1372005 1372331 := bstep (se 1 (by rfl) ⟨1029248, by rfl⟩ : syracuseStep 1372331 = 2058497) B2058497
theorem B5861555 : Blo 1372005 5861555 := bstep (se 1 (by rfl) ⟨4396166, by rfl⟩ : syracuseStep 5861555 = 8792333) B8792333
theorem B1372343 : Blo 1372005 1372343 := bstep (se 1 (by rfl) ⟨1029257, by rfl⟩ : syracuseStep 1372343 = 2058515) B2058515
theorem B5214401 : Blo 1372005 5214401 := bstep (se 2 (by rfl) ⟨1955400, by rfl⟩ : syracuseStep 5214401 = 3910801) B3910801
theorem B1372363 : Blo 1372005 1372363 := bstep (se 1 (by rfl) ⟨1029272, by rfl⟩ : syracuseStep 1372363 = 2058545) B2058545
theorem B1544395 : Blo 1372005 1544395 := bstep (se 1 (by rfl) ⟨1158296, by rfl⟩ : syracuseStep 1544395 = 2316593) B2316593
theorem B2199755 : Blo 1372005 2199755 := bstep (se 1 (by rfl) ⟨1649816, by rfl⟩ : syracuseStep 2199755 = 3299633) B3299633
theorem B1372375 : Blo 1372005 1372375 := bstep (se 1 (by rfl) ⟨1029281, by rfl⟩ : syracuseStep 1372375 = 2058563) B2058563
theorem B1372395 : Blo 1372005 1372395 := bstep (se 1 (by rfl) ⟨1029296, by rfl⟩ : syracuseStep 1372395 = 2058593) B2058593
theorem B1372407 : Blo 1372005 1372407 := bstep (se 1 (by rfl) ⟨1029305, by rfl⟩ : syracuseStep 1372407 = 2058611) B2058611
theorem B1372427 : Blo 1372005 1372427 := bstep (se 1 (by rfl) ⟨1029320, by rfl⟩ : syracuseStep 1372427 = 2058641) B2058641
theorem B2060555 : Blo 1372005 2060555 := bstep (se 1 (by rfl) ⟨1545416, by rfl⟩ : syracuseStep 2060555 = 3090833) B3090833
theorem B1372439 : Blo 1372005 1372439 := bstep (se 1 (by rfl) ⟨1029329, by rfl⟩ : syracuseStep 1372439 = 2058659) B2058659
theorem B2060567 : Blo 1372005 2060567 := bstep (se 1 (by rfl) ⟨1545425, by rfl⟩ : syracuseStep 2060567 = 3090851) B3090851
theorem B1372459 : Blo 1372005 1372459 := bstep (se 1 (by rfl) ⟨1029344, by rfl⟩ : syracuseStep 1372459 = 2058689) B2058689
theorem B1372471 : Blo 1372005 1372471 := bstep (se 1 (by rfl) ⟨1029353, by rfl⟩ : syracuseStep 1372471 = 2058707) B2058707
theorem B1544503 : Blo 1372005 1544503 := bstep (se 1 (by rfl) ⟨1158377, by rfl⟩ : syracuseStep 1544503 = 2316755) B2316755
theorem B1372491 : Blo 1372005 1372491 := bstep (se 1 (by rfl) ⟨1029368, by rfl⟩ : syracuseStep 1372491 = 2058737) B2058737
theorem B2199883 : Blo 1372005 2199883 := bstep (se 1 (by rfl) ⟨1649912, by rfl⟩ : syracuseStep 2199883 = 3299825) B3299825
theorem B1372503 : Blo 1372005 1372503 := bstep (se 1 (by rfl) ⟨1029377, by rfl⟩ : syracuseStep 1372503 = 2058755) B2058755
theorem B2060633 : Blo 1372005 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B1372523 : Blo 1372005 1372523 := bstep (se 1 (by rfl) ⟨1029392, by rfl⟩ : syracuseStep 1372523 = 2058785) B2058785
theorem B1372535 : Blo 1372005 1372535 := bstep (se 1 (by rfl) ⟨1029401, by rfl⟩ : syracuseStep 1372535 = 2058803) B2058803
theorem B1372555 : Blo 1372005 1372555 := bstep (se 1 (by rfl) ⟨1029416, by rfl⟩ : syracuseStep 1372555 = 2058833) B2058833
theorem B1372567 : Blo 1372005 1372567 := bstep (se 1 (by rfl) ⟨1029425, by rfl⟩ : syracuseStep 1372567 = 2058851) B2058851
theorem B4632983 : Blo 1372005 4632983 := bstep (se 1 (by rfl) ⟨3474737, by rfl⟩ : syracuseStep 4632983 = 6949475) B6949475
theorem B1372587 : Blo 1372005 1372587 := bstep (se 1 (by rfl) ⟨1029440, by rfl⟩ : syracuseStep 1372587 = 2058881) B2058881
theorem B11891123 : Blo 1372005 11891123 := bstep (se 1 (by rfl) ⟨8918342, by rfl⟩ : syracuseStep 11891123 = 17836685) B17836685
theorem B1372599 : Blo 1372005 1372599 := bstep (se 1 (by rfl) ⟨1029449, by rfl⟩ : syracuseStep 1372599 = 2058899) B2058899
theorem B5943745 : Blo 1372005 5943745 := bstep (se 2 (by rfl) ⟨2228904, by rfl⟩ : syracuseStep 5943745 = 4457809) B4457809
theorem B1372619 : Blo 1372005 1372619 := bstep (se 1 (by rfl) ⟨1029464, by rfl⟩ : syracuseStep 1372619 = 2058929) B2058929
theorem B2060747 : Blo 1372005 2060747 := bstep (se 1 (by rfl) ⟨1545560, by rfl⟩ : syracuseStep 2060747 = 3091121) B3091121
theorem B1372631 : Blo 1372005 1372631 := bstep (se 1 (by rfl) ⟨1029473, by rfl⟩ : syracuseStep 1372631 = 2058947) B2058947
theorem B2060759 : Blo 1372005 2060759 := bstep (se 1 (by rfl) ⟨1545569, by rfl⟩ : syracuseStep 2060759 = 3091139) B3091139
theorem B1372651 : Blo 1372005 1372651 := bstep (se 1 (by rfl) ⟨1029488, by rfl⟩ : syracuseStep 1372651 = 2058977) B2058977
theorem B1544683 : Blo 1372005 1544683 := bstep (se 1 (by rfl) ⟨1158512, by rfl⟩ : syracuseStep 1544683 = 2317025) B2317025
theorem B1372663 : Blo 1372005 1372663 := bstep (se 1 (by rfl) ⟨1029497, by rfl⟩ : syracuseStep 1372663 = 2058995) B2058995
theorem B12866053 : Blo 1372005 12866053 := bstep (se 4 (by rfl) ⟨1206192, by rfl⟩ : syracuseStep 12866053 = 2412385) B2412385
theorem B1372683 : Blo 1372005 1372683 := bstep (se 1 (by rfl) ⟨1029512, by rfl⟩ : syracuseStep 1372683 = 2059025) B2059025
theorem B23466509 : Blo 1372005 23466509 := bstep (se 3 (by rfl) ⟨4399970, by rfl⟩ : syracuseStep 23466509 = 8799941) B8799941
theorem B1372695 : Blo 1372005 1372695 := bstep (se 1 (by rfl) ⟨1029521, by rfl⟩ : syracuseStep 1372695 = 2059043) B2059043
theorem B2060825 : Blo 1372005 2060825 := bstep (se 2 (by rfl) ⟨772809, by rfl⟩ : syracuseStep 2060825 = 1545619) B1545619
theorem B1372715 : Blo 1372005 1372715 := bstep (se 1 (by rfl) ⟨1029536, by rfl⟩ : syracuseStep 1372715 = 2059073) B2059073
theorem B10711597 : Blo 1372005 10711597 := bstep (se 3 (by rfl) ⟨2008424, by rfl⟩ : syracuseStep 10711597 = 4016849) B4016849
theorem B1372727 : Blo 1372005 1372727 := bstep (se 1 (by rfl) ⟨1029545, by rfl⟩ : syracuseStep 1372727 = 2059091) B2059091
theorem B1372747 : Blo 1372005 1372747 := bstep (se 1 (by rfl) ⟨1029560, by rfl⟩ : syracuseStep 1372747 = 2059121) B2059121
theorem B1372759 : Blo 1372005 1372759 := bstep (se 1 (by rfl) ⟨1029569, by rfl⟩ : syracuseStep 1372759 = 2059139) B2059139
theorem B1544791 : Blo 1372005 1544791 := bstep (se 1 (by rfl) ⟨1158593, by rfl⟩ : syracuseStep 1544791 = 2317187) B2317187
theorem B5943901 : Blo 1372005 5943901 := bstep (se 3 (by rfl) ⟨1114481, by rfl⟩ : syracuseStep 5943901 = 2228963) B2228963
theorem B8802917 : Blo 1372005 8802917 := bstep (se 4 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 8802917 = 1650547) B1650547
theorem B1372779 : Blo 1372005 1372779 := bstep (se 1 (by rfl) ⟨1029584, by rfl⟩ : syracuseStep 1372779 = 2059169) B2059169
theorem B1372791 : Blo 1372005 1372791 := bstep (se 1 (by rfl) ⟨1029593, by rfl⟩ : syracuseStep 1372791 = 2059187) B2059187
theorem B1372811 : Blo 1372005 1372811 := bstep (se 1 (by rfl) ⟨1029608, by rfl⟩ : syracuseStep 1372811 = 2059217) B2059217
theorem B2060939 : Blo 1372005 2060939 := bstep (se 1 (by rfl) ⟨1545704, by rfl⟩ : syracuseStep 2060939 = 3091409) B3091409
theorem B1372823 : Blo 1372005 1372823 := bstep (se 1 (by rfl) ⟨1029617, by rfl⟩ : syracuseStep 1372823 = 2059235) B2059235
theorem B2060951 : Blo 1372005 2060951 := bstep (se 1 (by rfl) ⟨1545713, by rfl⟩ : syracuseStep 2060951 = 3091427) B3091427
theorem B1372843 : Blo 1372005 1372843 := bstep (se 1 (by rfl) ⟨1029632, by rfl⟩ : syracuseStep 1372843 = 2059265) B2059265
theorem B11285171 : Blo 1372005 11285171 := bstep (se 1 (by rfl) ⟨8463878, by rfl⟩ : syracuseStep 11285171 = 16927757) B16927757
theorem B1372855 : Blo 1372005 1372855 := bstep (se 1 (by rfl) ⟨1029641, by rfl⟩ : syracuseStep 1372855 = 2059283) B2059283
theorem B1372875 : Blo 1372005 1372875 := bstep (se 1 (by rfl) ⟨1029656, by rfl⟩ : syracuseStep 1372875 = 2059313) B2059313
theorem B1372887 : Blo 1372005 1372887 := bstep (se 1 (by rfl) ⟨1029665, by rfl⟩ : syracuseStep 1372887 = 2059331) B2059331
theorem B1372907 : Blo 1372005 1372907 := bstep (se 1 (by rfl) ⟨1029680, by rfl⟩ : syracuseStep 1372907 = 2059361) B2059361
theorem B1372919 : Blo 1372005 1372919 := bstep (se 1 (by rfl) ⟨1029689, by rfl⟩ : syracuseStep 1372919 = 2059379) B2059379
theorem B1372939 : Blo 1372005 1372939 := bstep (se 1 (by rfl) ⟨1029704, by rfl⟩ : syracuseStep 1372939 = 2059409) B2059409
theorem B1544971 : Blo 1372005 1544971 := bstep (se 1 (by rfl) ⟨1158728, by rfl⟩ : syracuseStep 1544971 = 2317457) B2317457
theorem B1372951 : Blo 1372005 1372951 := bstep (se 1 (by rfl) ⟨1029713, by rfl⟩ : syracuseStep 1372951 = 2059427) B2059427
theorem B1372971 : Blo 1372005 1372971 := bstep (se 1 (by rfl) ⟨1029728, by rfl⟩ : syracuseStep 1372971 = 2059457) B2059457
theorem B1372983 : Blo 1372005 1372983 := bstep (se 1 (by rfl) ⟨1029737, by rfl⟩ : syracuseStep 1372983 = 2059475) B2059475
theorem B3961675 : Blo 1372005 3961675 := bstep (se 1 (by rfl) ⟨2971256, by rfl⟩ : syracuseStep 3961675 = 5942513) B5942513
theorem B1373003 : Blo 1372005 1373003 := bstep (se 1 (by rfl) ⟨1029752, by rfl⟩ : syracuseStep 1373003 = 2059505) B2059505
theorem B1373015 : Blo 1372005 1373015 := bstep (se 1 (by rfl) ⟨1029761, by rfl⟩ : syracuseStep 1373015 = 2059523) B2059523
theorem B1373035 : Blo 1372005 1373035 := bstep (se 1 (by rfl) ⟨1029776, by rfl⟩ : syracuseStep 1373035 = 2059553) B2059553
theorem B1373047 : Blo 1372005 1373047 := bstep (se 1 (by rfl) ⟨1029785, by rfl⟩ : syracuseStep 1373047 = 2059571) B2059571
theorem B1545079 : Blo 1372005 1545079 := bstep (se 1 (by rfl) ⟨1158809, by rfl⟩ : syracuseStep 1545079 = 2317619) B2317619
theorem B1373067 : Blo 1372005 1373067 := bstep (se 1 (by rfl) ⟨1029800, by rfl⟩ : syracuseStep 1373067 = 2059601) B2059601
theorem B9393047 : Blo 1372005 9393047 := bstep (se 1 (by rfl) ⟨7044785, by rfl⟩ : syracuseStep 9393047 = 14089571) B14089571
theorem B1373079 : Blo 1372005 1373079 := bstep (se 1 (by rfl) ⟨1029809, by rfl⟩ : syracuseStep 1373079 = 2059619) B2059619
theorem B1373099 : Blo 1372005 1373099 := bstep (se 1 (by rfl) ⟨1029824, by rfl⟩ : syracuseStep 1373099 = 2059649) B2059649
theorem B4633523 : Blo 1372005 4633523 := bstep (se 1 (by rfl) ⟨3475142, by rfl⟩ : syracuseStep 4633523 = 6950285) B6950285
theorem B1373111 : Blo 1372005 1373111 := bstep (se 1 (by rfl) ⟨1029833, by rfl⟩ : syracuseStep 1373111 = 2059667) B2059667
theorem B1373131 : Blo 1372005 1373131 := bstep (se 1 (by rfl) ⟨1029848, by rfl⟩ : syracuseStep 1373131 = 2059697) B2059697
theorem B1373143 : Blo 1372005 1373143 := bstep (se 1 (by rfl) ⟨1029857, by rfl⟩ : syracuseStep 1373143 = 2059715) B2059715
theorem B1373163 : Blo 1372005 1373163 := bstep (se 1 (by rfl) ⟨1029872, by rfl⟩ : syracuseStep 1373163 = 2059745) B2059745
theorem B1373175 : Blo 1372005 1373175 := bstep (se 1 (by rfl) ⟨1029881, by rfl⟩ : syracuseStep 1373175 = 2059763) B2059763
theorem B1373195 : Blo 1372005 1373195 := bstep (se 1 (by rfl) ⟨1029896, by rfl⟩ : syracuseStep 1373195 = 2059793) B2059793
theorem B1373207 : Blo 1372005 1373207 := bstep (se 1 (by rfl) ⟨1029905, by rfl⟩ : syracuseStep 1373207 = 2059811) B2059811
theorem B1373227 : Blo 1372005 1373227 := bstep (se 1 (by rfl) ⟨1029920, by rfl⟩ : syracuseStep 1373227 = 2059841) B2059841
theorem B1545259 : Blo 1372005 1545259 := bstep (se 1 (by rfl) ⟨1158944, by rfl⟩ : syracuseStep 1545259 = 2317889) B2317889
theorem B1373239 : Blo 1372005 1373239 := bstep (se 1 (by rfl) ⟨1029929, by rfl⟩ : syracuseStep 1373239 = 2059859) B2059859
theorem B1373259 : Blo 1372005 1373259 := bstep (se 1 (by rfl) ⟨1029944, by rfl⟩ : syracuseStep 1373259 = 2059889) B2059889
theorem B2315351 : Blo 1372005 2315351 := bstep (se 1 (by rfl) ⟨1736513, by rfl⟩ : syracuseStep 2315351 = 3473027) B3473027
theorem B1373271 : Blo 1372005 1373271 := bstep (se 1 (by rfl) ⟨1029953, by rfl⟩ : syracuseStep 1373271 = 2059907) B2059907
theorem B1373291 : Blo 1372005 1373291 := bstep (se 1 (by rfl) ⟨1029968, by rfl⟩ : syracuseStep 1373291 = 2059937) B2059937
theorem B1373303 : Blo 1372005 1373303 := bstep (se 1 (by rfl) ⟨1029977, by rfl⟩ : syracuseStep 1373303 = 2059955) B2059955
theorem B6952067 : Blo 1372005 6952067 := bstep (se 1 (by rfl) ⟨5214050, by rfl⟩ : syracuseStep 6952067 = 10428101) B10428101
theorem B1373323 : Blo 1372005 1373323 := bstep (se 1 (by rfl) ⟨1029992, by rfl⟩ : syracuseStep 1373323 = 2059985) B2059985
theorem B1373335 : Blo 1372005 1373335 := bstep (se 1 (by rfl) ⟨1030001, by rfl⟩ : syracuseStep 1373335 = 2060003) B2060003
theorem B1545367 : Blo 1372005 1545367 := bstep (se 1 (by rfl) ⟨1159025, by rfl⟩ : syracuseStep 1545367 = 2318051) B2318051
theorem B1373355 : Blo 1372005 1373355 := bstep (se 1 (by rfl) ⟨1030016, by rfl⟩ : syracuseStep 1373355 = 2060033) B2060033
theorem B35206325 : Blo 1372005 35206325 := bstep (se 5 (by rfl) ⟨1650296, by rfl⟩ : syracuseStep 35206325 = 3300593) B3300593
theorem B1373367 : Blo 1372005 1373367 := bstep (se 1 (by rfl) ⟨1030025, by rfl⟩ : syracuseStep 1373367 = 2060051) B2060051
theorem B4633793 : Blo 1372005 4633793 := bstep (se 2 (by rfl) ⟨1737672, by rfl⟩ : syracuseStep 4633793 = 3475345) B3475345
theorem B1373387 : Blo 1372005 1373387 := bstep (se 1 (by rfl) ⟨1030040, by rfl⟩ : syracuseStep 1373387 = 2060081) B2060081
theorem B2315479 : Blo 1372005 2315479 := bstep (se 1 (by rfl) ⟨1736609, by rfl⟩ : syracuseStep 2315479 = 3473219) B3473219
theorem B1373399 : Blo 1372005 1373399 := bstep (se 1 (by rfl) ⟨1030049, by rfl⟩ : syracuseStep 1373399 = 2060099) B2060099
theorem B1373419 : Blo 1372005 1373419 := bstep (se 1 (by rfl) ⟨1030064, by rfl⟩ : syracuseStep 1373419 = 2060129) B2060129
theorem B1373431 : Blo 1372005 1373431 := bstep (se 1 (by rfl) ⟨1030073, by rfl⟩ : syracuseStep 1373431 = 2060147) B2060147
theorem B1373451 : Blo 1372005 1373451 := bstep (se 1 (by rfl) ⟨1030088, by rfl⟩ : syracuseStep 1373451 = 2060177) B2060177
theorem B1373463 : Blo 1372005 1373463 := bstep (se 1 (by rfl) ⟨1030097, by rfl⟩ : syracuseStep 1373463 = 2060195) B2060195
theorem B10573091 : Blo 1372005 10573091 := bstep (se 1 (by rfl) ⟨7929818, by rfl⟩ : syracuseStep 10573091 = 15859637) B15859637
theorem B1373483 : Blo 1372005 1373483 := bstep (se 1 (by rfl) ⟨1030112, by rfl⟩ : syracuseStep 1373483 = 2060225) B2060225
theorem B1373495 : Blo 1372005 1373495 := bstep (se 1 (by rfl) ⟨1030121, by rfl⟩ : syracuseStep 1373495 = 2060243) B2060243
theorem B1373515 : Blo 1372005 1373515 := bstep (se 1 (by rfl) ⟨1030136, by rfl⟩ : syracuseStep 1373515 = 2060273) B2060273
theorem B1545547 : Blo 1372005 1545547 := bstep (se 1 (by rfl) ⟨1159160, by rfl⟩ : syracuseStep 1545547 = 2318321) B2318321
theorem B1373527 : Blo 1372005 1373527 := bstep (se 1 (by rfl) ⟨1030145, by rfl⟩ : syracuseStep 1373527 = 2060291) B2060291
theorem B1373547 : Blo 1372005 1373547 := bstep (se 1 (by rfl) ⟨1030160, by rfl⟩ : syracuseStep 1373547 = 2060321) B2060321
theorem B1373559 : Blo 1372005 1373559 := bstep (se 1 (by rfl) ⟨1030169, by rfl⟩ : syracuseStep 1373559 = 2060339) B2060339
theorem B1373579 : Blo 1372005 1373579 := bstep (se 1 (by rfl) ⟨1030184, by rfl⟩ : syracuseStep 1373579 = 2060369) B2060369
theorem B1373591 : Blo 1372005 1373591 := bstep (se 1 (by rfl) ⟨1030193, by rfl⟩ : syracuseStep 1373591 = 2060387) B2060387
theorem B1373611 : Blo 1372005 1373611 := bstep (se 1 (by rfl) ⟨1030208, by rfl⟩ : syracuseStep 1373611 = 2060417) B2060417
theorem B5215661 : Blo 1372005 5215661 := bstep (se 3 (by rfl) ⟨977936, by rfl⟩ : syracuseStep 5215661 = 1955873) B1955873
theorem B1373623 : Blo 1372005 1373623 := bstep (se 1 (by rfl) ⟨1030217, by rfl⟩ : syracuseStep 1373623 = 2060435) B2060435
theorem B1545655 : Blo 1372005 1545655 := bstep (se 1 (by rfl) ⟨1159241, by rfl⟩ : syracuseStep 1545655 = 2318483) B2318483
theorem B1373643 : Blo 1372005 1373643 := bstep (se 1 (by rfl) ⟨1030232, by rfl⟩ : syracuseStep 1373643 = 2060465) B2060465
theorem B5215691 : Blo 1372005 5215691 := bstep (se 1 (by rfl) ⟨3911768, by rfl⟩ : syracuseStep 5215691 = 7823537) B7823537
theorem B1373655 : Blo 1372005 1373655 := bstep (se 1 (by rfl) ⟨1030241, by rfl⟩ : syracuseStep 1373655 = 2060483) B2060483
theorem B1373675 : Blo 1372005 1373675 := bstep (se 1 (by rfl) ⟨1030256, by rfl⟩ : syracuseStep 1373675 = 2060513) B2060513
theorem B1373687 : Blo 1372005 1373687 := bstep (se 1 (by rfl) ⟨1030265, by rfl⟩ : syracuseStep 1373687 = 2060531) B2060531
theorem B5281283 : Blo 1372005 5281283 := bstep (se 1 (by rfl) ⟨3960962, by rfl⟩ : syracuseStep 5281283 = 7921925) B7921925
theorem B1373707 : Blo 1372005 1373707 := bstep (se 1 (by rfl) ⟨1030280, by rfl⟩ : syracuseStep 1373707 = 2060561) B2060561
theorem B1373719 : Blo 1372005 1373719 := bstep (se 1 (by rfl) ⟨1030289, by rfl⟩ : syracuseStep 1373719 = 2060579) B2060579
theorem B1373739 : Blo 1372005 1373739 := bstep (se 1 (by rfl) ⟨1030304, by rfl⟩ : syracuseStep 1373739 = 2060609) B2060609
theorem B1373751 : Blo 1372005 1373751 := bstep (se 1 (by rfl) ⟨1030313, by rfl⟩ : syracuseStep 1373751 = 2060627) B2060627
theorem B1373771 : Blo 1372005 1373771 := bstep (se 1 (by rfl) ⟨1030328, by rfl⟩ : syracuseStep 1373771 = 2060657) B2060657
theorem B1373783 : Blo 1372005 1373783 := bstep (se 1 (by rfl) ⟨1030337, by rfl⟩ : syracuseStep 1373783 = 2060675) B2060675
theorem B10024541 : Blo 1372005 10024541 := bstep (se 3 (by rfl) ⟨1879601, by rfl⟩ : syracuseStep 10024541 = 3759203) B3759203
theorem B1373803 : Blo 1372005 1373803 := bstep (se 1 (by rfl) ⟨1030352, by rfl⟩ : syracuseStep 1373803 = 2060705) B2060705
theorem B1373815 : Blo 1372005 1373815 := bstep (se 1 (by rfl) ⟨1030361, by rfl⟩ : syracuseStep 1373815 = 2060723) B2060723
theorem B1373835 : Blo 1372005 1373835 := bstep (se 1 (by rfl) ⟨1030376, by rfl⟩ : syracuseStep 1373835 = 2060753) B2060753
theorem B1373847 : Blo 1372005 1373847 := bstep (se 1 (by rfl) ⟨1030385, by rfl⟩ : syracuseStep 1373847 = 2060771) B2060771
theorem B1373867 : Blo 1372005 1373867 := bstep (se 1 (by rfl) ⟨1030400, by rfl⟩ : syracuseStep 1373867 = 2060801) B2060801
theorem B1373879 : Blo 1372005 1373879 := bstep (se 1 (by rfl) ⟨1030409, by rfl⟩ : syracuseStep 1373879 = 2060819) B2060819
theorem B4175563 : Blo 1372005 4175563 := bstep (se 1 (by rfl) ⟨3131672, by rfl⟩ : syracuseStep 4175563 = 6263345) B6263345
theorem B1373899 : Blo 1372005 1373899 := bstep (se 1 (by rfl) ⟨1030424, by rfl⟩ : syracuseStep 1373899 = 2060849) B2060849
theorem B1373911 : Blo 1372005 1373911 := bstep (se 1 (by rfl) ⟨1030433, by rfl⟩ : syracuseStep 1373911 = 2060867) B2060867
theorem B2930393 : Blo 1372005 2930393 := bstep (se 2 (by rfl) ⟨1098897, by rfl⟩ : syracuseStep 2930393 = 2197795) B2197795
theorem B4634333 : Blo 1372005 4634333 := bstep (se 3 (by rfl) ⟨868937, by rfl⟩ : syracuseStep 4634333 = 1737875) B1737875
theorem B1373931 : Blo 1372005 1373931 := bstep (se 1 (by rfl) ⟨1030448, by rfl⟩ : syracuseStep 1373931 = 2060897) B2060897
theorem B1373943 : Blo 1372005 1373943 := bstep (se 1 (by rfl) ⟨1030457, by rfl⟩ : syracuseStep 1373943 = 2060915) B2060915
theorem B1373963 : Blo 1372005 1373963 := bstep (se 1 (by rfl) ⟨1030472, by rfl⟩ : syracuseStep 1373963 = 2060945) B2060945
theorem B1373975 : Blo 1372005 1373975 := bstep (se 1 (by rfl) ⟨1030481, by rfl⟩ : syracuseStep 1373975 = 2060963) B2060963
theorem B1373995 : Blo 1372005 1373995 := bstep (se 1 (by rfl) ⟨1030496, by rfl⟩ : syracuseStep 1373995 = 2060993) B2060993
theorem B10426157 : Blo 1372005 10426157 := bstep (se 3 (by rfl) ⟨1954904, by rfl⟩ : syracuseStep 10426157 = 3909809) B3909809
theorem B2316107 : Blo 1372005 2316107 := bstep (se 1 (by rfl) ⟨1737080, by rfl⟩ : syracuseStep 2316107 = 3474161) B3474161
theorem B2316235 : Blo 1372005 2316235 := bstep (se 1 (by rfl) ⟨1737176, by rfl⟩ : syracuseStep 2316235 = 3474353) B3474353
theorem B2316377 : Blo 1372005 2316377 := bstep (se 2 (by rfl) ⟨868641, by rfl⟩ : syracuseStep 2316377 = 1737283) B1737283
theorem B5216345 : Blo 1372005 5216345 := bstep (se 2 (by rfl) ⟨1956129, by rfl⟩ : syracuseStep 5216345 = 3912259) B3912259
theorem B1980619 : Blo 1372005 1980619 := bstep (se 1 (by rfl) ⟨1485464, by rfl⟩ : syracuseStep 1980619 = 2970929) B2970929
theorem B2316505 : Blo 1372005 2316505 := bstep (se 2 (by rfl) ⟨868689, by rfl⟩ : syracuseStep 2316505 = 1737379) B1737379
theorem B2898263 : Blo 1372005 2898263 := bstep (se 1 (by rfl) ⟨2173697, by rfl⟩ : syracuseStep 2898263 = 4347395) B4347395
theorem B8796509 : Blo 1372005 8796509 := bstep (se 3 (by rfl) ⟨1649345, by rfl⟩ : syracuseStep 8796509 = 3298691) B3298691
theorem B2931059 : Blo 1372005 2931059 := bstep (se 1 (by rfl) ⟨2198294, by rfl⟩ : syracuseStep 2931059 = 4396589) B4396589
theorem B5216663 : Blo 1372005 5216663 := bstep (se 1 (by rfl) ⟨3912497, by rfl⟩ : syracuseStep 5216663 = 7824995) B7824995
theorem B10418867 : Blo 1372005 10418867 := bstep (se 1 (by rfl) ⟨7814150, by rfl⟩ : syracuseStep 10418867 = 15628301) B15628301
theorem B36166385 : Blo 1372005 36166385 := bstep (se 2 (by rfl) ⟨13562394, by rfl⟩ : syracuseStep 36166385 = 27124789) B27124789
theorem B2317079 : Blo 1372005 2317079 := bstep (se 1 (by rfl) ⟨1737809, by rfl⟩ : syracuseStep 2317079 = 3475619) B3475619
theorem B1506091 : Blo 1372005 1506091 := bstep (se 1 (by rfl) ⟨1129568, by rfl⟩ : syracuseStep 1506091 = 2259137) B2259137
theorem B5864237 : Blo 1372005 5864237 := bstep (se 3 (by rfl) ⟨1099544, by rfl⟩ : syracuseStep 5864237 = 2199089) B2199089
theorem B6593345 : Blo 1372005 6593345 := bstep (se 2 (by rfl) ⟨2472504, by rfl⟩ : syracuseStep 6593345 = 4945009) B4945009
theorem B3087179 : Blo 1372005 3087179 := bstep (se 1 (by rfl) ⟨2315384, by rfl⟩ : syracuseStep 3087179 = 4630769) B4630769
theorem B4635467 : Blo 1372005 4635467 := bstep (se 1 (by rfl) ⟨3476600, by rfl⟩ : syracuseStep 4635467 = 6953201) B6953201
theorem B3087233 : Blo 1372005 3087233 := bstep (se 2 (by rfl) ⟨1157712, by rfl⟩ : syracuseStep 3087233 = 2315425) B2315425
theorem B2087831 : Blo 1372005 2087831 := bstep (se 1 (by rfl) ⟨1565873, by rfl⟩ : syracuseStep 2087831 = 3131747) B3131747
theorem B2317207 : Blo 1372005 2317207 := bstep (se 1 (by rfl) ⟨1737905, by rfl⟩ : syracuseStep 2317207 = 3475811) B3475811
theorem B19807249 : Blo 1372005 19807249 := bstep (se 2 (by rfl) ⟨7427718, by rfl⟩ : syracuseStep 19807249 = 14855437) B14855437
theorem B19307555 : Blo 1372005 19307555 := bstep (se 1 (by rfl) ⟨14480666, by rfl⟩ : syracuseStep 19307555 = 28961333) B28961333
theorem B11721773 : Blo 1372005 11721773 := bstep (se 3 (by rfl) ⟨2197832, by rfl⟩ : syracuseStep 11721773 = 4395665) B4395665
theorem B3087449 : Blo 1372005 3087449 := bstep (se 2 (by rfl) ⟨1157793, by rfl⟩ : syracuseStep 3087449 = 2315587) B2315587
theorem B4635737 : Blo 1372005 4635737 := bstep (se 2 (by rfl) ⟨1738401, by rfl⟩ : syracuseStep 4635737 = 3476803) B3476803
theorem B1465495 : Blo 1372005 1465495 := bstep (se 1 (by rfl) ⟨1099121, by rfl⟩ : syracuseStep 1465495 = 2198243) B2198243
theorem B3087539 : Blo 1372005 3087539 := bstep (se 1 (by rfl) ⟨2315654, by rfl⟩ : syracuseStep 3087539 = 4631309) B4631309
theorem B2473139 : Blo 1372005 2473139 := bstep (se 1 (by rfl) ⟨1854854, by rfl⟩ : syracuseStep 2473139 = 3709709) B3709709
theorem B19791053 : Blo 1372005 19791053 := bstep (se 3 (by rfl) ⟨3710822, by rfl⟩ : syracuseStep 19791053 = 7421645) B7421645
theorem B3087575 : Blo 1372005 3087575 := bstep (se 1 (by rfl) ⟨2315681, by rfl⟩ : syracuseStep 3087575 = 4631363) B4631363
theorem B2932033 : Blo 1372005 2932033 := bstep (se 2 (by rfl) ⟨1099512, by rfl⟩ : syracuseStep 2932033 = 2199025) B2199025
theorem B6438275 : Blo 1372005 6438275 := bstep (se 1 (by rfl) ⟨4828706, by rfl⟩ : syracuseStep 6438275 = 9657413) B9657413
theorem B3087755 : Blo 1372005 3087755 := bstep (se 1 (by rfl) ⟨2315816, by rfl⟩ : syracuseStep 3087755 = 4631633) B4631633
theorem B3087809 : Blo 1372005 3087809 := bstep (se 2 (by rfl) ⟨1157928, by rfl⟩ : syracuseStep 3087809 = 2315857) B2315857
theorem B5799361 : Blo 1372005 5799361 := bstep (se 2 (by rfl) ⟨2174760, by rfl⟩ : syracuseStep 5799361 = 4349521) B4349521
theorem B1465867 : Blo 1372005 1465867 := bstep (se 1 (by rfl) ⟨1099400, by rfl⟩ : syracuseStep 1465867 = 2198801) B2198801
theorem B2317835 : Blo 1372005 2317835 := bstep (se 1 (by rfl) ⟨1738376, by rfl⟩ : syracuseStep 2317835 = 3476753) B3476753
theorem B2932289 : Blo 1372005 2932289 := bstep (se 2 (by rfl) ⟨1099608, by rfl⟩ : syracuseStep 2932289 = 2199217) B2199217
theorem B6946397 : Blo 1372005 6946397 := bstep (se 3 (by rfl) ⟨1302449, by rfl⟩ : syracuseStep 6946397 = 2604899) B2604899
theorem B2317963 : Blo 1372005 2317963 := bstep (se 1 (by rfl) ⟨1738472, by rfl⟩ : syracuseStep 2317963 = 3476945) B3476945
theorem B2932375 : Blo 1372005 2932375 := bstep (se 1 (by rfl) ⟨2199281, by rfl⟩ : syracuseStep 2932375 = 4398563) B4398563
theorem B3088025 : Blo 1372005 3088025 := bstep (se 2 (by rfl) ⟨1158009, by rfl⟩ : syracuseStep 3088025 = 2316019) B2316019
theorem B2473687 : Blo 1372005 2473687 := bstep (se 1 (by rfl) ⟨1855265, by rfl⟩ : syracuseStep 2473687 = 3710531) B3710531
theorem B3088115 : Blo 1372005 3088115 := bstep (se 1 (by rfl) ⟨2316086, by rfl⟩ : syracuseStep 3088115 = 4632173) B4632173
theorem B5209859 : Blo 1372005 5209859 := bstep (se 1 (by rfl) ⟨3907394, by rfl⟩ : syracuseStep 5209859 = 7814789) B7814789
theorem B3088151 : Blo 1372005 3088151 := bstep (se 1 (by rfl) ⟨2316113, by rfl⟩ : syracuseStep 3088151 = 4632227) B4632227
theorem B4636439 : Blo 1372005 4636439 := bstep (se 1 (by rfl) ⟨3477329, by rfl⟩ : syracuseStep 4636439 = 6954659) B6954659
theorem B2318105 : Blo 1372005 2318105 := bstep (se 2 (by rfl) ⟨869289, by rfl⟩ : syracuseStep 2318105 = 1738579) B1738579
theorem B10026827 : Blo 1372005 10026827 := bstep (se 1 (by rfl) ⟨7520120, by rfl⟩ : syracuseStep 10026827 = 15040241) B15040241
theorem B2604953 : Blo 1372005 2604953 := bstep (se 2 (by rfl) ⟨976857, by rfl⟩ : syracuseStep 2604953 = 1953715) B1953715
theorem B2318233 : Blo 1372005 2318233 := bstep (se 2 (by rfl) ⟨869337, by rfl⟩ : syracuseStep 2318233 = 1738675) B1738675
theorem B3907531 : Blo 1372005 3907531 := bstep (se 1 (by rfl) ⟨2930648, by rfl⟩ : syracuseStep 3907531 = 5861297) B5861297
theorem B3088331 : Blo 1372005 3088331 := bstep (se 1 (by rfl) ⟨2316248, by rfl⟩ : syracuseStep 3088331 = 4632497) B4632497
theorem B2318395 : Blo 1372005 2318395 := bstep (se 1 (by rfl) ⟨1738796, by rfl⟩ : syracuseStep 2318395 = 3477593) B3477593
theorem B6946883 : Blo 1372005 6946883 := bstep (se 1 (by rfl) ⟨5210162, by rfl⟩ : syracuseStep 6946883 = 10420325) B10420325
theorem B7528535 : Blo 1372005 7528535 := bstep (se 1 (by rfl) ⟨5646401, by rfl⟩ : syracuseStep 7528535 = 11292803) B11292803
theorem B3907703 : Blo 1372005 3907703 := bstep (se 1 (by rfl) ⟨2930777, by rfl⟩ : syracuseStep 3907703 = 5861555) B5861555
theorem B3473543 : Blo 1372005 3473543 := bstep (se 1 (by rfl) ⟨2605157, by rfl⟩ : syracuseStep 3473543 = 5210315) B5210315
theorem B2318537 : Blo 1372005 2318537 := bstep (se 2 (by rfl) ⟨869451, by rfl⟩ : syracuseStep 2318537 = 1738903) B1738903
theorem B3473675 : Blo 1372005 3473675 := bstep (se 1 (by rfl) ⟨2605256, by rfl⟩ : syracuseStep 3473675 = 5210513) B5210513
theorem B3088655 : Blo 1372005 3088655 := bstep (se 1 (by rfl) ⟨2316491, by rfl⟩ : syracuseStep 3088655 = 4632983) B4632983
theorem B3088673 : Blo 1372005 3088673 := bstep (se 2 (by rfl) ⟨1158252, by rfl⟩ : syracuseStep 3088673 = 2316505) B2316505
theorem B2605355 : Blo 1372005 2605355 := bstep (se 1 (by rfl) ⟨1954016, by rfl⟩ : syracuseStep 2605355 = 3908033) B3908033
theorem B6947207 : Blo 1372005 6947207 := bstep (se 1 (by rfl) ⟨5210405, by rfl⟩ : syracuseStep 6947207 = 10420811) B10420811
theorem B2933177 : Blo 1372005 2933177 := bstep (se 2 (by rfl) ⟨1099941, by rfl⟩ : syracuseStep 2933177 = 2199883) B2199883
theorem B4637195 : Blo 1372005 4637195 := bstep (se 1 (by rfl) ⟨3477896, by rfl⟩ : syracuseStep 4637195 = 6955793) B6955793
theorem B2605583 : Blo 1372005 2605583 := bstep (se 1 (by rfl) ⟨1954187, by rfl⟩ : syracuseStep 2605583 = 3908375) B3908375
theorem B2933263 : Blo 1372005 2933263 := bstep (se 1 (by rfl) ⟨2199947, by rfl⟩ : syracuseStep 2933263 = 4399895) B4399895
theorem B5866013 : Blo 1372005 5866013 := bstep (se 3 (by rfl) ⟨1099877, by rfl⟩ : syracuseStep 5866013 = 2199755) B2199755
theorem B3965555 : Blo 1372005 3965555 := bstep (se 1 (by rfl) ⟨2974166, by rfl⟩ : syracuseStep 3965555 = 5948333) B5948333
theorem B3089015 : Blo 1372005 3089015 := bstep (se 1 (by rfl) ⟨2316761, by rfl⟩ : syracuseStep 3089015 = 4633523) B4633523
theorem B7930541 : Blo 1372005 7930541 := bstep (se 3 (by rfl) ⟨1486976, by rfl⟩ : syracuseStep 7930541 = 2973953) B2973953
theorem B17154737 : Blo 1372005 17154737 := bstep (se 2 (by rfl) ⟨6433026, by rfl⟩ : syracuseStep 17154737 = 12866053) B12866053
theorem B3474191 : Blo 1372005 3474191 := bstep (se 1 (by rfl) ⟨2605643, by rfl⟩ : syracuseStep 3474191 = 5211287) B5211287
theorem B23470883 : Blo 1372005 23470883 := bstep (se 1 (by rfl) ⟨17603162, by rfl⟩ : syracuseStep 23470883 = 35206325) B35206325
theorem B7815973 : Blo 1372005 7815973 := bstep (se 4 (by rfl) ⟨732747, by rfl⟩ : syracuseStep 7815973 = 1465495) B1465495
theorem B33424163 : Blo 1372005 33424163 := bstep (se 1 (by rfl) ⟨25068122, by rfl⟩ : syracuseStep 33424163 = 50136245) B50136245
theorem B3089195 : Blo 1372005 3089195 := bstep (se 1 (by rfl) ⟨2316896, by rfl⟩ : syracuseStep 3089195 = 4633793) B4633793
theorem B1737607 : Blo 1372005 1737607 := bstep (se 1 (by rfl) ⟨1303205, by rfl⟩ : syracuseStep 1737607 = 2606411) B2606411
theorem B3474323 : Blo 1372005 3474323 := bstep (se 1 (by rfl) ⟨2605742, by rfl⟩ : syracuseStep 3474323 = 5211485) B5211485
theorem B13190039 : Blo 1372005 13190039 := bstep (se 1 (by rfl) ⟨9892529, by rfl⟩ : syracuseStep 13190039 = 19785059) B19785059
theorem B53470129 : Blo 1372005 53470129 := bstep (se 2 (by rfl) ⟨20051298, by rfl⟩ : syracuseStep 53470129 = 40102597) B40102597
theorem B8258507 : Blo 1372005 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B2008121 : Blo 1372005 2008121 := bstep (se 2 (by rfl) ⟨753045, by rfl⟩ : syracuseStep 2008121 = 1506091) B1506091
theorem B3089555 : Blo 1372005 3089555 := bstep (se 1 (by rfl) ⟨2317166, by rfl⟩ : syracuseStep 3089555 = 4634333) B4634333
theorem B3089609 : Blo 1372005 3089609 := bstep (se 2 (by rfl) ⟨1158603, by rfl⟩ : syracuseStep 3089609 = 2317207) B2317207
theorem B1738027 : Blo 1372005 1738027 := bstep (se 1 (by rfl) ⟨1303520, by rfl⟩ : syracuseStep 1738027 = 2607041) B2607041
theorem B7816499 : Blo 1372005 7816499 := bstep (se 1 (by rfl) ⟨5862374, by rfl⟩ : syracuseStep 7816499 = 11724749) B11724749
theorem B10716475 : Blo 1372005 10716475 := bstep (se 1 (by rfl) ⟨8037356, by rfl⟩ : syracuseStep 10716475 = 16074713) B16074713
theorem B5866937 : Blo 1372005 5866937 := bstep (se 2 (by rfl) ⟨2200101, by rfl⟩ : syracuseStep 5866937 = 4400203) B4400203
theorem B1738255 : Blo 1372005 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B3909377 : Blo 1372005 3909377 := bstep (se 2 (by rfl) ⟨1466016, by rfl⟩ : syracuseStep 3909377 = 2932033) B2932033
theorem B2058041 : Blo 1372005 2058041 := bstep (se 2 (by rfl) ⟨771765, by rfl⟩ : syracuseStep 2058041 = 1543531) B1543531
theorem B3909491 : Blo 1372005 3909491 := bstep (se 1 (by rfl) ⟨2932118, by rfl⟩ : syracuseStep 3909491 = 5864237) B5864237
theorem B2058119 : Blo 1372005 2058119 := bstep (se 1 (by rfl) ⟨1543589, by rfl⟩ : syracuseStep 2058119 = 3087179) B3087179
theorem B3090311 : Blo 1372005 3090311 := bstep (se 1 (by rfl) ⟨2317733, by rfl⟩ : syracuseStep 3090311 = 4635467) B4635467
theorem B2606995 : Blo 1372005 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B2058155 : Blo 1372005 2058155 := bstep (se 1 (by rfl) ⟨1543616, by rfl⟩ : syracuseStep 2058155 = 3087233) B3087233
theorem B2058185 : Blo 1372005 2058185 := bstep (se 2 (by rfl) ⟨771819, by rfl⟩ : syracuseStep 2058185 = 1543639) B1543639
theorem B3475457 : Blo 1372005 3475457 := bstep (se 2 (by rfl) ⟨1303296, by rfl⟩ : syracuseStep 3475457 = 2606593) B2606593
theorem B12871703 : Blo 1372005 12871703 := bstep (se 1 (by rfl) ⟨9653777, by rfl⟩ : syracuseStep 12871703 = 19307555) B19307555
theorem B2058299 : Blo 1372005 2058299 := bstep (se 1 (by rfl) ⟨1543724, by rfl⟩ : syracuseStep 2058299 = 3087449) B3087449
theorem B3090491 : Blo 1372005 3090491 := bstep (se 1 (by rfl) ⟨2317868, by rfl⟩ : syracuseStep 3090491 = 4635737) B4635737
theorem B2058359 : Blo 1372005 2058359 := bstep (se 1 (by rfl) ⟨1543769, by rfl⟩ : syracuseStep 2058359 = 3087539) B3087539
theorem B1648759 : Blo 1372005 1648759 := bstep (se 1 (by rfl) ⟨1236569, by rfl⟩ : syracuseStep 1648759 = 2473139) B2473139
theorem B2607223 : Blo 1372005 2607223 := bstep (se 1 (by rfl) ⟨1955417, by rfl⟩ : syracuseStep 2607223 = 3910835) B3910835
theorem B2058383 : Blo 1372005 2058383 := bstep (se 1 (by rfl) ⟨1543787, by rfl⟩ : syracuseStep 2058383 = 3087575) B3087575
theorem B2058425 : Blo 1372005 2058425 := bstep (se 2 (by rfl) ⟨771909, by rfl⟩ : syracuseStep 2058425 = 1543819) B1543819
theorem B3090617 : Blo 1372005 3090617 := bstep (se 2 (by rfl) ⟨1158981, by rfl⟩ : syracuseStep 3090617 = 2317963) B2317963
theorem B2197705 : Blo 1372005 2197705 := bstep (se 2 (by rfl) ⟨824139, by rfl⟩ : syracuseStep 2197705 = 1648279) B1648279
theorem B3909833 : Blo 1372005 3909833 := bstep (se 2 (by rfl) ⟨1466187, by rfl⟩ : syracuseStep 3909833 = 2932375) B2932375
theorem B2058503 : Blo 1372005 2058503 := bstep (se 1 (by rfl) ⟨1543877, by rfl⟩ : syracuseStep 2058503 = 3087755) B3087755
theorem B2058539 : Blo 1372005 2058539 := bstep (se 1 (by rfl) ⟨1543904, by rfl⟩ : syracuseStep 2058539 = 3087809) B3087809
theorem B1411387 : Blo 1372005 1411387 := bstep (se 1 (by rfl) ⟨1058540, by rfl⟩ : syracuseStep 1411387 = 2117081) B2117081
theorem B2058569 : Blo 1372005 2058569 := bstep (se 2 (by rfl) ⟨771963, by rfl⟩ : syracuseStep 2058569 = 1543927) B1543927
theorem B3475831 : Blo 1372005 3475831 := bstep (se 1 (by rfl) ⟨2606873, by rfl⟩ : syracuseStep 3475831 = 5213747) B5213747
theorem B4630931 : Blo 1372005 4630931 := bstep (se 1 (by rfl) ⟨3473198, by rfl⟩ : syracuseStep 4630931 = 6946397) B6946397
theorem B2058683 : Blo 1372005 2058683 := bstep (se 1 (by rfl) ⟨1544012, by rfl⟩ : syracuseStep 2058683 = 3088025) B3088025
theorem B2230729 : Blo 1372005 2230729 := bstep (se 2 (by rfl) ⟨836523, by rfl⟩ : syracuseStep 2230729 = 1673047) B1673047
theorem B2058743 : Blo 1372005 2058743 := bstep (se 1 (by rfl) ⟨1544057, by rfl⟩ : syracuseStep 2058743 = 3088115) B3088115
theorem B2058767 : Blo 1372005 2058767 := bstep (se 1 (by rfl) ⟨1544075, by rfl⟩ : syracuseStep 2058767 = 3088151) B3088151
theorem B3090959 : Blo 1372005 3090959 := bstep (se 1 (by rfl) ⟨2318219, by rfl⟩ : syracuseStep 3090959 = 4636439) B4636439
theorem B3090977 : Blo 1372005 3090977 := bstep (se 2 (by rfl) ⟨1159116, by rfl⟩ : syracuseStep 3090977 = 2318233) B2318233
theorem B2058809 : Blo 1372005 2058809 := bstep (se 2 (by rfl) ⟨772053, by rfl⟩ : syracuseStep 2058809 = 1544107) B1544107
theorem B2058887 : Blo 1372005 2058887 := bstep (se 1 (by rfl) ⟨1544165, by rfl⟩ : syracuseStep 2058887 = 3088331) B3088331
theorem B2058923 : Blo 1372005 2058923 := bstep (se 1 (by rfl) ⟨1544192, by rfl⟩ : syracuseStep 2058923 = 3088385) B3088385
theorem B2058953 : Blo 1372005 2058953 := bstep (se 2 (by rfl) ⟨772107, by rfl⟩ : syracuseStep 2058953 = 1544215) B1544215
theorem B7817957 : Blo 1372005 7817957 := bstep (se 4 (by rfl) ⟨732933, by rfl⟩ : syracuseStep 7817957 = 1465867) B1465867
theorem B5212943 : Blo 1372005 5212943 := bstep (se 1 (by rfl) ⟨3909707, by rfl⟩ : syracuseStep 5212943 = 7819415) B7819415
theorem B7424783 : Blo 1372005 7424783 := bstep (se 1 (by rfl) ⟨5568587, by rfl⟩ : syracuseStep 7424783 = 11137175) B11137175
theorem B3476267 : Blo 1372005 3476267 := bstep (se 1 (by rfl) ⟨2607200, by rfl⟩ : syracuseStep 3476267 = 5214401) B5214401
theorem B2059067 : Blo 1372005 2059067 := bstep (se 1 (by rfl) ⟨1544300, by rfl⟩ : syracuseStep 2059067 = 3088601) B3088601
theorem B9898841 : Blo 1372005 9898841 := bstep (se 2 (by rfl) ⟨3712065, by rfl⟩ : syracuseStep 9898841 = 7424131) B7424131
theorem B2059127 : Blo 1372005 2059127 := bstep (se 1 (by rfl) ⟨1544345, by rfl⟩ : syracuseStep 2059127 = 3088691) B3088691
theorem B3091319 : Blo 1372005 3091319 := bstep (se 1 (by rfl) ⟨2318489, by rfl⟩ : syracuseStep 3091319 = 4636979) B4636979
theorem B2059151 : Blo 1372005 2059151 := bstep (se 1 (by rfl) ⟨1544363, by rfl⟩ : syracuseStep 2059151 = 3088727) B3088727
theorem B2059193 : Blo 1372005 2059193 := bstep (se 2 (by rfl) ⟨772197, by rfl⟩ : syracuseStep 2059193 = 1544395) B1544395
theorem B2059271 : Blo 1372005 2059271 := bstep (se 1 (by rfl) ⟨1544453, by rfl⟩ : syracuseStep 2059271 = 3088907) B3088907
theorem B2059307 : Blo 1372005 2059307 := bstep (se 1 (by rfl) ⟨1544480, by rfl⟩ : syracuseStep 2059307 = 3088961) B3088961
theorem B3091499 : Blo 1372005 3091499 := bstep (se 1 (by rfl) ⟨2318624, by rfl⟩ : syracuseStep 3091499 = 4637249) B4637249
theorem B5868611 : Blo 1372005 5868611 := bstep (se 1 (by rfl) ⟨4401458, by rfl⟩ : syracuseStep 5868611 = 8802917) B8802917
theorem B2059337 : Blo 1372005 2059337 := bstep (se 2 (by rfl) ⟨772251, by rfl⟩ : syracuseStep 2059337 = 1544503) B1544503
theorem B7523447 : Blo 1372005 7523447 := bstep (se 1 (by rfl) ⟨5642585, by rfl⟩ : syracuseStep 7523447 = 11285171) B11285171
theorem B2059451 : Blo 1372005 2059451 := bstep (se 1 (by rfl) ⟨1544588, by rfl⟩ : syracuseStep 2059451 = 3089177) B3089177
theorem B14093513 : Blo 1372005 14093513 := bstep (se 2 (by rfl) ⟨5285067, by rfl⟩ : syracuseStep 14093513 = 10570135) B10570135
theorem B2059511 : Blo 1372005 2059511 := bstep (se 1 (by rfl) ⟨1544633, by rfl⟩ : syracuseStep 2059511 = 3089267) B3089267
theorem B6262031 : Blo 1372005 6262031 := bstep (se 1 (by rfl) ⟨4696523, by rfl⟩ : syracuseStep 6262031 = 9393047) B9393047
theorem B2059535 : Blo 1372005 2059535 := bstep (se 1 (by rfl) ⟨1544651, by rfl⟩ : syracuseStep 2059535 = 3089303) B3089303
theorem B2059577 : Blo 1372005 2059577 := bstep (se 2 (by rfl) ⟨772341, by rfl⟩ : syracuseStep 2059577 = 1544683) B1544683
theorem B2059655 : Blo 1372005 2059655 := bstep (se 1 (by rfl) ⟨1544741, by rfl⟩ : syracuseStep 2059655 = 3089483) B3089483
theorem B1543567 : Blo 1372005 1543567 := bstep (se 1 (by rfl) ⟨1157675, by rfl⟩ : syracuseStep 1543567 = 2315351) B2315351
theorem B14282129 : Blo 1372005 14282129 := bstep (se 2 (by rfl) ⟨5355798, by rfl⟩ : syracuseStep 14282129 = 10711597) B10711597
theorem B2059691 : Blo 1372005 2059691 := bstep (se 1 (by rfl) ⟨1544768, by rfl⟩ : syracuseStep 2059691 = 3089537) B3089537
theorem B2059721 : Blo 1372005 2059721 := bstep (se 2 (by rfl) ⟨772395, by rfl⟩ : syracuseStep 2059721 = 1544791) B1544791
theorem B7925201 : Blo 1372005 7925201 := bstep (se 2 (by rfl) ⟨2971950, by rfl⟩ : syracuseStep 7925201 = 5943901) B5943901
theorem B7048727 : Blo 1372005 7048727 := bstep (se 1 (by rfl) ⟨5286545, by rfl⟩ : syracuseStep 7048727 = 10573091) B10573091
theorem B2059835 : Blo 1372005 2059835 := bstep (se 1 (by rfl) ⟨1544876, by rfl⟩ : syracuseStep 2059835 = 3089753) B3089753
theorem B4173373 : Blo 1372005 4173373 := bstep (se 3 (by rfl) ⟨782507, by rfl⟩ : syracuseStep 4173373 = 1565015) B1565015
theorem B3477107 : Blo 1372005 3477107 := bstep (se 1 (by rfl) ⟨2607830, by rfl⟩ : syracuseStep 3477107 = 5215661) B5215661
theorem B2059895 : Blo 1372005 2059895 := bstep (se 1 (by rfl) ⟨1544921, by rfl⟩ : syracuseStep 2059895 = 3089843) B3089843
theorem B3477127 : Blo 1372005 3477127 := bstep (se 1 (by rfl) ⟨2607845, by rfl⟩ : syracuseStep 3477127 = 5215691) B5215691
theorem B2059919 : Blo 1372005 2059919 := bstep (se 1 (by rfl) ⟨1544939, by rfl⟩ : syracuseStep 2059919 = 3089879) B3089879
theorem B2059961 : Blo 1372005 2059961 := bstep (se 2 (by rfl) ⟨772485, by rfl⟩ : syracuseStep 2059961 = 1544971) B1544971
theorem B10563301 : Blo 1372005 10563301 := bstep (se 4 (by rfl) ⟨990309, by rfl⟩ : syracuseStep 10563301 = 1980619) B1980619
theorem B2060039 : Blo 1372005 2060039 := bstep (se 1 (by rfl) ⟨1545029, by rfl⟩ : syracuseStep 2060039 = 3090059) B3090059
theorem B4632335 : Blo 1372005 4632335 := bstep (se 1 (by rfl) ⟨3474251, by rfl⟩ : syracuseStep 4632335 = 6948503) B6948503
theorem B2060075 : Blo 1372005 2060075 := bstep (se 1 (by rfl) ⟨1545056, by rfl⟩ : syracuseStep 2060075 = 3090113) B3090113
theorem B1953595 : Blo 1372005 1953595 := bstep (se 1 (by rfl) ⟨1465196, by rfl⟩ : syracuseStep 1953595 = 2930393) B2930393
theorem B2060105 : Blo 1372005 2060105 := bstep (se 2 (by rfl) ⟨772539, by rfl⟩ : syracuseStep 2060105 = 1545079) B1545079
theorem B6950771 : Blo 1372005 6950771 := bstep (se 1 (by rfl) ⟨5213078, by rfl⟩ : syracuseStep 6950771 = 10426157) B10426157
theorem B1372039 : Blo 1372005 1372039 := bstep (se 1 (by rfl) ⟨1029029, by rfl⟩ : syracuseStep 1372039 = 2058059) B2058059
theorem B1544071 : Blo 1372005 1544071 := bstep (se 1 (by rfl) ⟨1158053, by rfl⟩ : syracuseStep 1544071 = 2316107) B2316107
theorem B1372047 : Blo 1372005 1372047 := bstep (se 1 (by rfl) ⟨1029035, by rfl⟩ : syracuseStep 1372047 = 2058071) B2058071
theorem B3477401 : Blo 1372005 3477401 := bstep (se 2 (by rfl) ⟨1304025, by rfl⟩ : syracuseStep 3477401 = 2608051) B2608051
theorem B1372091 : Blo 1372005 1372091 := bstep (se 1 (by rfl) ⟨1029068, by rfl⟩ : syracuseStep 1372091 = 2058137) B2058137
theorem B2060219 : Blo 1372005 2060219 := bstep (se 1 (by rfl) ⟨1545164, by rfl⟩ : syracuseStep 2060219 = 3090329) B3090329
theorem B2060279 : Blo 1372005 2060279 := bstep (se 1 (by rfl) ⟨1545209, by rfl⟩ : syracuseStep 2060279 = 3090419) B3090419
theorem B1372167 : Blo 1372005 1372167 := bstep (se 1 (by rfl) ⟨1029125, by rfl⟩ : syracuseStep 1372167 = 2058251) B2058251
theorem B1372175 : Blo 1372005 1372175 := bstep (se 1 (by rfl) ⟨1029131, by rfl⟩ : syracuseStep 1372175 = 2058263) B2058263
theorem B2060303 : Blo 1372005 2060303 := bstep (se 1 (by rfl) ⟨1545227, by rfl⟩ : syracuseStep 2060303 = 3090455) B3090455
theorem B4632605 : Blo 1372005 4632605 := bstep (se 3 (by rfl) ⟨868613, by rfl⟩ : syracuseStep 4632605 = 1737227) B1737227
theorem B3911723 : Blo 1372005 3911723 := bstep (se 1 (by rfl) ⟨2933792, by rfl⟩ : syracuseStep 3911723 = 5867585) B5867585
theorem B2060345 : Blo 1372005 2060345 := bstep (se 2 (by rfl) ⟨772629, by rfl⟩ : syracuseStep 2060345 = 1545259) B1545259
theorem B1372219 : Blo 1372005 1372219 := bstep (se 1 (by rfl) ⟨1029164, by rfl⟩ : syracuseStep 1372219 = 2058329) B2058329
theorem B1544251 : Blo 1372005 1544251 := bstep (se 1 (by rfl) ⟨1158188, by rfl⟩ : syracuseStep 1544251 = 2316377) B2316377
theorem B3960893 : Blo 1372005 3960893 := bstep (se 3 (by rfl) ⟨742667, by rfl⟩ : syracuseStep 3960893 = 1485335) B1485335
theorem B3477563 : Blo 1372005 3477563 := bstep (se 1 (by rfl) ⟨2608172, by rfl⟩ : syracuseStep 3477563 = 5216345) B5216345
theorem B1372295 : Blo 1372005 1372295 := bstep (se 1 (by rfl) ⟨1029221, by rfl⟩ : syracuseStep 1372295 = 2058443) B2058443
theorem B2060423 : Blo 1372005 2060423 := bstep (se 1 (by rfl) ⟨1545317, by rfl⟩ : syracuseStep 2060423 = 3090635) B3090635
theorem B1372303 : Blo 1372005 1372303 := bstep (se 1 (by rfl) ⟨1029227, by rfl⟩ : syracuseStep 1372303 = 2058455) B2058455
theorem B2060459 : Blo 1372005 2060459 := bstep (se 1 (by rfl) ⟨1545344, by rfl⟩ : syracuseStep 2060459 = 3090689) B3090689
theorem B1372347 : Blo 1372005 1372347 := bstep (se 1 (by rfl) ⟨1029260, by rfl⟩ : syracuseStep 1372347 = 2058521) B2058521
theorem B12529865 : Blo 1372005 12529865 := bstep (se 2 (by rfl) ⟨4698699, by rfl⟩ : syracuseStep 12529865 = 9397399) B9397399
theorem B2060489 : Blo 1372005 2060489 := bstep (se 2 (by rfl) ⟨772683, by rfl⟩ : syracuseStep 2060489 = 1545367) B1545367
theorem B1954039 : Blo 1372005 1954039 := bstep (se 1 (by rfl) ⟨1465529, by rfl⟩ : syracuseStep 1954039 = 2931059) B2931059
theorem B1372423 : Blo 1372005 1372423 := bstep (se 1 (by rfl) ⟨1029317, by rfl⟩ : syracuseStep 1372423 = 2058635) B2058635
theorem B1372431 : Blo 1372005 1372431 := bstep (se 1 (by rfl) ⟨1029323, by rfl⟩ : syracuseStep 1372431 = 2058647) B2058647
theorem B3911951 : Blo 1372005 3911951 := bstep (se 1 (by rfl) ⟨2933963, by rfl⟩ : syracuseStep 3911951 = 5867927) B5867927
theorem B3477775 : Blo 1372005 3477775 := bstep (se 1 (by rfl) ⟨2608331, by rfl⟩ : syracuseStep 3477775 = 5216663) B5216663
theorem B1372475 : Blo 1372005 1372475 := bstep (se 1 (by rfl) ⟨1029356, by rfl⟩ : syracuseStep 1372475 = 2058713) B2058713
theorem B2060603 : Blo 1372005 2060603 := bstep (se 1 (by rfl) ⟨1545452, by rfl⟩ : syracuseStep 2060603 = 3090905) B3090905
theorem B6951257 : Blo 1372005 6951257 := bstep (se 2 (by rfl) ⟨2606721, by rfl⟩ : syracuseStep 6951257 = 5213443) B5213443
theorem B2060663 : Blo 1372005 2060663 := bstep (se 1 (by rfl) ⟨1545497, by rfl⟩ : syracuseStep 2060663 = 3090995) B3090995
theorem B1372551 : Blo 1372005 1372551 := bstep (se 1 (by rfl) ⟨1029413, by rfl⟩ : syracuseStep 1372551 = 2058827) B2058827
theorem B1372559 : Blo 1372005 1372559 := bstep (se 1 (by rfl) ⟨1029419, by rfl⟩ : syracuseStep 1372559 = 2058839) B2058839
theorem B2060687 : Blo 1372005 2060687 := bstep (se 1 (by rfl) ⟨1545515, by rfl⟩ : syracuseStep 2060687 = 3091031) B3091031
theorem B2060729 : Blo 1372005 2060729 := bstep (se 2 (by rfl) ⟨772773, by rfl⟩ : syracuseStep 2060729 = 1545547) B1545547
theorem B1372603 : Blo 1372005 1372603 := bstep (se 1 (by rfl) ⟨1029452, by rfl⟩ : syracuseStep 1372603 = 2058905) B2058905
theorem B1372679 : Blo 1372005 1372679 := bstep (se 1 (by rfl) ⟨1029509, by rfl⟩ : syracuseStep 1372679 = 2059019) B2059019
theorem B6599171 : Blo 1372005 6599171 := bstep (se 1 (by rfl) ⟨4949378, by rfl⟩ : syracuseStep 6599171 = 9898757) B9898757
theorem B2060807 : Blo 1372005 2060807 := bstep (se 1 (by rfl) ⟨1545605, by rfl⟩ : syracuseStep 2060807 = 3091211) B3091211
theorem B1372687 : Blo 1372005 1372687 := bstep (se 1 (by rfl) ⟨1029515, by rfl⟩ : syracuseStep 1372687 = 2059031) B2059031
theorem B1544719 : Blo 1372005 1544719 := bstep (se 1 (by rfl) ⟨1158539, by rfl⟩ : syracuseStep 1544719 = 2317079) B2317079
theorem B4395563 : Blo 1372005 4395563 := bstep (se 1 (by rfl) ⟨3296672, by rfl⟩ : syracuseStep 4395563 = 6593345) B6593345
theorem B2060843 : Blo 1372005 2060843 := bstep (se 1 (by rfl) ⟨1545632, by rfl⟩ : syracuseStep 2060843 = 3091265) B3091265
theorem B1372731 : Blo 1372005 1372731 := bstep (se 1 (by rfl) ⟨1029548, by rfl⟩ : syracuseStep 1372731 = 2059097) B2059097
theorem B2060873 : Blo 1372005 2060873 := bstep (se 2 (by rfl) ⟨772827, by rfl⟩ : syracuseStep 2060873 = 1545655) B1545655
theorem B1372807 : Blo 1372005 1372807 := bstep (se 1 (by rfl) ⟨1029605, by rfl⟩ : syracuseStep 1372807 = 2059211) B2059211
theorem B1372815 : Blo 1372005 1372815 := bstep (se 1 (by rfl) ⟨1029611, by rfl⟩ : syracuseStep 1372815 = 2059223) B2059223
theorem B6599341 : Blo 1372005 6599341 := bstep (se 3 (by rfl) ⟨1237376, by rfl⟩ : syracuseStep 6599341 = 2474753) B2474753
theorem B1372859 : Blo 1372005 1372859 := bstep (se 1 (by rfl) ⟨1029644, by rfl⟩ : syracuseStep 1372859 = 2059289) B2059289
theorem B2060987 : Blo 1372005 2060987 := bstep (se 1 (by rfl) ⟨1545740, by rfl⟩ : syracuseStep 2060987 = 3091481) B3091481
theorem B8794817 : Blo 1372005 8794817 := bstep (se 2 (by rfl) ⟨3298056, by rfl⟩ : syracuseStep 8794817 = 6596113) B6596113
theorem B1372935 : Blo 1372005 1372935 := bstep (se 1 (by rfl) ⟨1029701, by rfl⟩ : syracuseStep 1372935 = 2059403) B2059403
theorem B1372943 : Blo 1372005 1372943 := bstep (se 1 (by rfl) ⟨1029707, by rfl⟩ : syracuseStep 1372943 = 2059415) B2059415
theorem B18789155 : Blo 1372005 18789155 := bstep (se 1 (by rfl) ⟨14091866, by rfl⟩ : syracuseStep 18789155 = 28183733) B28183733
theorem B13194035 : Blo 1372005 13194035 := bstep (se 1 (by rfl) ⟨9895526, by rfl⟩ : syracuseStep 13194035 = 19791053) B19791053
theorem B1372987 : Blo 1372005 1372987 := bstep (se 1 (by rfl) ⟨1029740, by rfl⟩ : syracuseStep 1372987 = 2059481) B2059481
theorem B1373063 : Blo 1372005 1373063 := bstep (se 1 (by rfl) ⟨1029797, by rfl⟩ : syracuseStep 1373063 = 2059595) B2059595
theorem B1373071 : Blo 1372005 1373071 := bstep (se 1 (by rfl) ⟨1029803, by rfl⟩ : syracuseStep 1373071 = 2059607) B2059607
theorem B4395961 : Blo 1372005 4395961 := bstep (se 2 (by rfl) ⟨1648485, by rfl⟩ : syracuseStep 4395961 = 3296971) B3296971
theorem B5567417 : Blo 1372005 5567417 := bstep (se 2 (by rfl) ⟨2087781, by rfl⟩ : syracuseStep 5567417 = 4175563) B4175563
theorem B1373115 : Blo 1372005 1373115 := bstep (se 1 (by rfl) ⟨1029836, by rfl⟩ : syracuseStep 1373115 = 2059673) B2059673
theorem B3298249 : Blo 1372005 3298249 := bstep (se 2 (by rfl) ⟨1236843, by rfl⟩ : syracuseStep 3298249 = 2473687) B2473687
theorem B31699973 : Blo 1372005 31699973 := bstep (se 4 (by rfl) ⟨2971872, by rfl⟩ : syracuseStep 31699973 = 5943745) B5943745
theorem B1373191 : Blo 1372005 1373191 := bstep (se 1 (by rfl) ⟨1029893, by rfl⟩ : syracuseStep 1373191 = 2059787) B2059787
theorem B1545223 : Blo 1372005 1545223 := bstep (se 1 (by rfl) ⟨1158917, by rfl⟩ : syracuseStep 1545223 = 2317835) B2317835
theorem B1373199 : Blo 1372005 1373199 := bstep (se 1 (by rfl) ⟨1029899, by rfl⟩ : syracuseStep 1373199 = 2059799) B2059799
theorem B1954859 : Blo 1372005 1954859 := bstep (se 1 (by rfl) ⟨1466144, by rfl⟩ : syracuseStep 1954859 = 2932289) B2932289
theorem B1373243 : Blo 1372005 1373243 := bstep (se 1 (by rfl) ⟨1029932, by rfl⟩ : syracuseStep 1373243 = 2059865) B2059865
theorem B5944387 : Blo 1372005 5944387 := bstep (se 1 (by rfl) ⟨4458290, by rfl⟩ : syracuseStep 5944387 = 8916581) B8916581
theorem B1373319 : Blo 1372005 1373319 := bstep (se 1 (by rfl) ⟨1029989, by rfl⟩ : syracuseStep 1373319 = 2059979) B2059979
theorem B1373327 : Blo 1372005 1373327 := bstep (se 1 (by rfl) ⟨1029995, by rfl⟩ : syracuseStep 1373327 = 2059991) B2059991
theorem B1373371 : Blo 1372005 1373371 := bstep (se 1 (by rfl) ⟨1030028, by rfl⟩ : syracuseStep 1373371 = 2060057) B2060057
theorem B1545403 : Blo 1372005 1545403 := bstep (se 1 (by rfl) ⟨1159052, by rfl⟩ : syracuseStep 1545403 = 2318105) B2318105
theorem B1373447 : Blo 1372005 1373447 := bstep (se 1 (by rfl) ⟨1030085, by rfl⟩ : syracuseStep 1373447 = 2060171) B2060171
theorem B1373455 : Blo 1372005 1373455 := bstep (se 1 (by rfl) ⟨1030091, by rfl⟩ : syracuseStep 1373455 = 2060183) B2060183
theorem B1373499 : Blo 1372005 1373499 := bstep (se 1 (by rfl) ⟨1030124, by rfl⟩ : syracuseStep 1373499 = 2060249) B2060249
theorem B1373575 : Blo 1372005 1373575 := bstep (se 1 (by rfl) ⟨1030181, by rfl⟩ : syracuseStep 1373575 = 2060363) B2060363
theorem B1373583 : Blo 1372005 1373583 := bstep (se 1 (by rfl) ⟨1030187, by rfl⟩ : syracuseStep 1373583 = 2060375) B2060375
theorem B4634009 : Blo 1372005 4634009 := bstep (se 2 (by rfl) ⟨1737753, by rfl⟩ : syracuseStep 4634009 = 3475507) B3475507
theorem B1373627 : Blo 1372005 1373627 := bstep (se 1 (by rfl) ⟨1030220, by rfl⟩ : syracuseStep 1373627 = 2060441) B2060441
theorem B1373703 : Blo 1372005 1373703 := bstep (se 1 (by rfl) ⟨1030277, by rfl⟩ : syracuseStep 1373703 = 2060555) B2060555
theorem B1373711 : Blo 1372005 1373711 := bstep (se 1 (by rfl) ⟨1030283, by rfl⟩ : syracuseStep 1373711 = 2060567) B2060567
theorem B1373755 : Blo 1372005 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B7927415 : Blo 1372005 7927415 := bstep (se 1 (by rfl) ⟨5945561, by rfl⟩ : syracuseStep 7927415 = 11891123) B11891123
theorem B2315911 : Blo 1372005 2315911 := bstep (se 1 (by rfl) ⟨1736933, by rfl⟩ : syracuseStep 2315911 = 3473867) B3473867
theorem B1373831 : Blo 1372005 1373831 := bstep (se 1 (by rfl) ⟨1030373, by rfl⟩ : syracuseStep 1373831 = 2060747) B2060747
theorem B1373839 : Blo 1372005 1373839 := bstep (se 1 (by rfl) ⟨1030379, by rfl⟩ : syracuseStep 1373839 = 2060759) B2060759
theorem B15644339 : Blo 1372005 15644339 := bstep (se 1 (by rfl) ⟨11733254, by rfl⟩ : syracuseStep 15644339 = 23466509) B23466509
theorem B1373883 : Blo 1372005 1373883 := bstep (se 1 (by rfl) ⟨1030412, by rfl⟩ : syracuseStep 1373883 = 2060825) B2060825
theorem B1373959 : Blo 1372005 1373959 := bstep (se 1 (by rfl) ⟨1030469, by rfl⟩ : syracuseStep 1373959 = 2060939) B2060939
theorem B1373967 : Blo 1372005 1373967 := bstep (se 1 (by rfl) ⟨1030475, by rfl⟩ : syracuseStep 1373967 = 2060951) B2060951
theorem B2381687 : Blo 1372005 2381687 := bstep (se 1 (by rfl) ⟨1786265, by rfl⟩ : syracuseStep 2381687 = 3572531) B3572531
theorem B5216147 : Blo 1372005 5216147 := bstep (se 1 (by rfl) ⟨3912110, by rfl⟩ : syracuseStep 5216147 = 7824221) B7824221
theorem B2086955 : Blo 1372005 2086955 := bstep (se 1 (by rfl) ⟨1565216, by rfl⟩ : syracuseStep 2086955 = 3130433) B3130433
theorem B8353853 : Blo 1372005 8353853 := bstep (se 3 (by rfl) ⟨1566347, by rfl⟩ : syracuseStep 8353853 = 3132695) B3132695
theorem B4634711 : Blo 1372005 4634711 := bstep (se 1 (by rfl) ⟨3476033, by rfl⟩ : syracuseStep 4634711 = 6952067) B6952067
theorem B2316559 : Blo 1372005 2316559 := bstep (se 1 (by rfl) ⟨1737419, by rfl⟩ : syracuseStep 2316559 = 3474839) B3474839
theorem B106928437 : Blo 1372005 106928437 := bstep (se 5 (by rfl) ⟨5012270, by rfl⟩ : syracuseStep 106928437 = 10024541) B10024541
theorem B3520855 : Blo 1372005 3520855 := bstep (se 1 (by rfl) ⟨2640641, by rfl⟩ : syracuseStep 3520855 = 5281283) B5281283
theorem B3709319 : Blo 1372005 3709319 := bstep (se 1 (by rfl) ⟨2781989, by rfl⟩ : syracuseStep 3709319 = 5563979) B5563979
theorem B6953363 : Blo 1372005 6953363 := bstep (se 1 (by rfl) ⟨5215022, by rfl⟩ : syracuseStep 6953363 = 10430045) B10430045
theorem B5282233 : Blo 1372005 5282233 := bstep (se 2 (by rfl) ⟨1980837, by rfl⟩ : syracuseStep 5282233 = 3961675) B3961675
theorem B4635197 : Blo 1372005 4635197 := bstep (se 3 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 4635197 = 1738199) B1738199
theorem B26409665 : Blo 1372005 26409665 := bstep (se 2 (by rfl) ⟨9903624, by rfl⟩ : syracuseStep 26409665 = 19807249) B19807249
theorem B13195993 : Blo 1372005 13195993 := bstep (se 2 (by rfl) ⟨4948497, by rfl⟩ : syracuseStep 13195993 = 9896995) B9896995
theorem B7420673 : Blo 1372005 7420673 := bstep (se 2 (by rfl) ⟨2782752, by rfl⟩ : syracuseStep 7420673 = 5565505) B5565505
theorem B11737871 : Blo 1372005 11737871 := bstep (se 1 (by rfl) ⟨8803403, by rfl⟩ : syracuseStep 11737871 = 17606807) B17606807
theorem B2317099 : Blo 1372005 2317099 := bstep (se 1 (by rfl) ⟨1737824, by rfl⟩ : syracuseStep 2317099 = 3475649) B3475649
theorem B1932175 : Blo 1372005 1932175 := bstep (se 1 (by rfl) ⟨1449131, by rfl⟩ : syracuseStep 1932175 = 2898263) B2898263
theorem B3087251 : Blo 1372005 3087251 := bstep (se 1 (by rfl) ⟨2315438, by rfl⟩ : syracuseStep 3087251 = 4630877) B4630877
theorem B5864339 : Blo 1372005 5864339 := bstep (se 1 (by rfl) ⟨4398254, by rfl⟩ : syracuseStep 5864339 = 8796509) B8796509
theorem B2317241 : Blo 1372005 2317241 := bstep (se 2 (by rfl) ⟨868965, by rfl⟩ : syracuseStep 2317241 = 1737931) B1737931
theorem B3087305 : Blo 1372005 3087305 := bstep (se 2 (by rfl) ⟨1157739, by rfl⟩ : syracuseStep 3087305 = 2315479) B2315479
theorem B6945911 : Blo 1372005 6945911 := bstep (se 1 (by rfl) ⟨5209433, by rfl⟩ : syracuseStep 6945911 = 10418867) B10418867
theorem B2931913 : Blo 1372005 2931913 := bstep (se 2 (by rfl) ⟨1099467, by rfl⟩ : syracuseStep 2931913 = 2198935) B2198935
theorem B7732481 : Blo 1372005 7732481 := bstep (se 2 (by rfl) ⟨2899680, by rfl⟩ : syracuseStep 7732481 = 5799361) B5799361
theorem B1465615 : Blo 1372005 1465615 := bstep (se 1 (by rfl) ⟨1099211, by rfl⟩ : syracuseStep 1465615 = 2198423) B2198423
theorem B1391887 : Blo 1372005 1391887 := bstep (se 1 (by rfl) ⟨1043915, by rfl⟩ : syracuseStep 1391887 = 2087831) B2087831
theorem B96443693 : Blo 1372005 96443693 := bstep (se 3 (by rfl) ⟨18083192, by rfl⟩ : syracuseStep 96443693 = 36166385) B36166385
theorem B7814515 : Blo 1372005 7814515 := bstep (se 1 (by rfl) ⟨5860886, by rfl⟩ : syracuseStep 7814515 = 11721773) B11721773
theorem B1465871 : Blo 1372005 1465871 := bstep (se 1 (by rfl) ⟨1099403, by rfl⟩ : syracuseStep 1465871 = 2198807) B2198807
theorem B4292183 : Blo 1372005 4292183 := bstep (se 1 (by rfl) ⟨3219137, by rfl⟩ : syracuseStep 4292183 = 6438275) B6438275
theorem B2317943 : Blo 1372005 2317943 := bstep (se 1 (by rfl) ⟨1738457, by rfl⟩ : syracuseStep 2317943 = 3476915) B3476915
theorem B3088007 : Blo 1372005 3088007 := bstep (se 1 (by rfl) ⟨2316005, by rfl⟩ : syracuseStep 3088007 = 4632011) B4632011
theorem B3088187 : Blo 1372005 3088187 := bstep (se 1 (by rfl) ⟨2316140, by rfl⟩ : syracuseStep 3088187 = 4632281) B4632281
theorem B3473239 : Blo 1372005 3473239 := bstep (se 1 (by rfl) ⟨2604929, by rfl⟩ : syracuseStep 3473239 = 5209859) B5209859
theorem B6684551 : Blo 1372005 6684551 := bstep (se 1 (by rfl) ⟨5013413, by rfl⟩ : syracuseStep 6684551 = 10026827) B10026827
theorem B5210041 : Blo 1372005 5210041 := bstep (se 2 (by rfl) ⟨1953765, by rfl⟩ : syracuseStep 5210041 = 3907531) B3907531
theorem B3088313 : Blo 1372005 3088313 := bstep (se 2 (by rfl) ⟨1158117, by rfl⟩ : syracuseStep 3088313 = 2316235) B2316235
theorem B1736635 : Blo 1372005 1736635 := bstep (se 1 (by rfl) ⟨1302476, by rfl⟩ : syracuseStep 1736635 = 2604953) B2604953
theorem B4636601 : Blo 1372005 4636601 := bstep (se 2 (by rfl) ⟨1738725, by rfl⟩ : syracuseStep 4636601 = 3477451) B3477451
theorem B3088403 : Blo 1372005 3088403 := bstep (se 1 (by rfl) ⟨2316302, by rfl⟩ : syracuseStep 3088403 = 4632605) B4632605
theorem B2318375 : Blo 1372005 2318375 := bstep (se 1 (by rfl) ⟨1738781, by rfl⟩ : syracuseStep 2318375 = 3477563) B3477563
theorem B2605135 : Blo 1372005 2605135 := bstep (se 1 (by rfl) ⟨1953851, by rfl⟩ : syracuseStep 2605135 = 3907703) B3907703
theorem B1736903 : Blo 1372005 1736903 := bstep (se 1 (by rfl) ⟨1302677, by rfl⟩ : syracuseStep 1736903 = 2605355) B2605355
theorem B20062525 : Blo 1372005 20062525 := bstep (se 3 (by rfl) ⟨3761723, by rfl⟩ : syracuseStep 20062525 = 7523447) B7523447
theorem B22257989 : Blo 1372005 22257989 := bstep (se 4 (by rfl) ⟨2086686, by rfl⟩ : syracuseStep 22257989 = 4173373) B4173373
theorem B2605385 : Blo 1372005 2605385 := bstep (se 2 (by rfl) ⟨977019, by rfl⟩ : syracuseStep 2605385 = 1954039) B1954039
theorem B4399447 : Blo 1372005 4399447 := bstep (se 1 (by rfl) ⟨3299585, by rfl⟩ : syracuseStep 4399447 = 6599171) B6599171
theorem B1737055 : Blo 1372005 1737055 := bstep (se 1 (by rfl) ⟨1302791, by rfl⟩ : syracuseStep 1737055 = 2605583) B2605583
theorem B3088745 : Blo 1372005 3088745 := bstep (se 2 (by rfl) ⟨1158279, by rfl⟩ : syracuseStep 3088745 = 2316559) B2316559
theorem B4637033 : Blo 1372005 4637033 := bstep (se 2 (by rfl) ⟨1738887, by rfl⟩ : syracuseStep 4637033 = 3477775) B3477775
theorem B4694473 : Blo 1372005 4694473 := bstep (se 2 (by rfl) ⟨1760427, by rfl⟩ : syracuseStep 4694473 = 3520855) B3520855
theorem B11436491 : Blo 1372005 11436491 := bstep (se 1 (by rfl) ⟨8577368, by rfl⟩ : syracuseStep 11436491 = 17154737) B17154737
theorem B12526103 : Blo 1372005 12526103 := bstep (se 1 (by rfl) ⟨9394577, by rfl⟩ : syracuseStep 12526103 = 18789155) B18789155
theorem B15647255 : Blo 1372005 15647255 := bstep (se 1 (by rfl) ⟨11735441, by rfl⟩ : syracuseStep 15647255 = 23470883) B23470883
theorem B22282775 : Blo 1372005 22282775 := bstep (se 1 (by rfl) ⟨16712081, by rfl⟩ : syracuseStep 22282775 = 33424163) B33424163
theorem B3711611 : Blo 1372005 3711611 := bstep (se 1 (by rfl) ⟨2783708, by rfl⟩ : syracuseStep 3711611 = 5567417) B5567417
theorem B5505671 : Blo 1372005 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B20619949 : Blo 1372005 20619949 := bstep (se 3 (by rfl) ⟨3866240, by rfl⟩ : syracuseStep 20619949 = 7732481) B7732481
theorem B5210999 : Blo 1372005 5210999 := bstep (se 1 (by rfl) ⟨3908249, by rfl⟩ : syracuseStep 5210999 = 7816499) B7816499
theorem B8799121 : Blo 1372005 8799121 := bstep (se 2 (by rfl) ⟨3299670, by rfl⟩ : syracuseStep 8799121 = 6599341) B6599341
theorem B3089339 : Blo 1372005 3089339 := bstep (se 1 (by rfl) ⟨2317004, by rfl⟩ : syracuseStep 3089339 = 4634009) B4634009
theorem B38085677 : Blo 1372005 38085677 := bstep (se 3 (by rfl) ⟨7141064, by rfl⟩ : syracuseStep 38085677 = 14282129) B14282129
theorem B10421297 : Blo 1372005 10421297 := bstep (se 2 (by rfl) ⟨3907986, by rfl⟩ : syracuseStep 10421297 = 7815973) B7815973
theorem B3089465 : Blo 1372005 3089465 := bstep (se 2 (by rfl) ⟨1158549, by rfl⟩ : syracuseStep 3089465 = 2317099) B2317099
theorem B5284943 : Blo 1372005 5284943 := bstep (se 1 (by rfl) ⟨3963707, by rfl⟩ : syracuseStep 5284943 = 7927415) B7927415
theorem B10429559 : Blo 1372005 10429559 := bstep (se 1 (by rfl) ⟨7822169, by rfl⟩ : syracuseStep 10429559 = 15644339) B15644339
theorem B2606251 : Blo 1372005 2606251 := bstep (se 1 (by rfl) ⟨1954688, by rfl⟩ : syracuseStep 2606251 = 3909377) B3909377
theorem B2606327 : Blo 1372005 2606327 := bstep (se 1 (by rfl) ⟨1954745, by rfl⟩ : syracuseStep 2606327 = 3909491) B3909491
theorem B3908989 : Blo 1372005 3908989 := bstep (se 3 (by rfl) ⟨732935, by rfl⟩ : syracuseStep 3908989 = 1465871) B1465871
theorem B3089807 : Blo 1372005 3089807 := bstep (se 1 (by rfl) ⟨2317355, by rfl⟩ : syracuseStep 3089807 = 4634711) B4634711
theorem B7423397 : Blo 1372005 7423397 := bstep (se 4 (by rfl) ⟨695943, by rfl⟩ : syracuseStep 7423397 = 1391887) B1391887
theorem B2606555 : Blo 1372005 2606555 := bstep (se 1 (by rfl) ⟨1954916, by rfl⟩ : syracuseStep 2606555 = 3909833) B3909833
theorem B3909217 : Blo 1372005 3909217 := bstep (se 2 (by rfl) ⟨1465956, by rfl⟩ : syracuseStep 3909217 = 2931913) B2931913
theorem B3090131 : Blo 1372005 3090131 := bstep (se 1 (by rfl) ⟨2317598, by rfl⟩ : syracuseStep 3090131 = 4635197) B4635197
theorem B14288633 : Blo 1372005 14288633 := bstep (se 2 (by rfl) ⟨5358237, by rfl⟩ : syracuseStep 14288633 = 10716475) B10716475
theorem B17606443 : Blo 1372005 17606443 := bstep (se 1 (by rfl) ⟨13204832, by rfl⟩ : syracuseStep 17606443 = 26409665) B26409665
theorem B5211971 : Blo 1372005 5211971 := bstep (se 1 (by rfl) ⟨3908978, by rfl⟩ : syracuseStep 5211971 = 7817957) B7817957
theorem B3475295 : Blo 1372005 3475295 := bstep (se 1 (by rfl) ⟨2606471, by rfl⟩ : syracuseStep 3475295 = 5212943) B5212943
theorem B4949855 : Blo 1372005 4949855 := bstep (se 1 (by rfl) ⟨3712391, by rfl⟩ : syracuseStep 4949855 = 7424783) B7424783
theorem B7825247 : Blo 1372005 7825247 := bstep (se 1 (by rfl) ⟨5868935, by rfl⟩ : syracuseStep 7825247 = 11737871) B11737871
theorem B2058089 : Blo 1372005 2058089 := bstep (se 2 (by rfl) ⟨771783, by rfl⟩ : syracuseStep 2058089 = 1543567) B1543567
theorem B2058167 : Blo 1372005 2058167 := bstep (se 1 (by rfl) ⟨1543625, by rfl⟩ : syracuseStep 2058167 = 3087251) B3087251
theorem B3909559 : Blo 1372005 3909559 := bstep (se 1 (by rfl) ⟨2932169, by rfl⟩ : syracuseStep 3909559 = 5864339) B5864339
theorem B2058203 : Blo 1372005 2058203 := bstep (se 1 (by rfl) ⟨1543652, by rfl⟩ : syracuseStep 2058203 = 3087305) B3087305
theorem B4630607 : Blo 1372005 4630607 := bstep (se 1 (by rfl) ⟨3472955, by rfl⟩ : syracuseStep 4630607 = 6945911) B6945911
theorem B14084401 : Blo 1372005 14084401 := bstep (se 2 (by rfl) ⟨5281650, by rfl⟩ : syracuseStep 14084401 = 10563301) B10563301
theorem B11897221 : Blo 1372005 11897221 := bstep (se 4 (by rfl) ⟨1115364, by rfl⟩ : syracuseStep 11897221 = 2230729) B2230729
theorem B2861455 : Blo 1372005 2861455 := bstep (se 1 (by rfl) ⟨2146091, by rfl⟩ : syracuseStep 2861455 = 4292183) B4292183
theorem B2058671 : Blo 1372005 2058671 := bstep (se 1 (by rfl) ⟨1544003, by rfl⟩ : syracuseStep 2058671 = 3088007) B3088007
theorem B4630985 : Blo 1372005 4630985 := bstep (se 2 (by rfl) ⟨1736619, by rfl⟩ : syracuseStep 4630985 = 3473239) B3473239
theorem B2058761 : Blo 1372005 2058761 := bstep (se 2 (by rfl) ⟨772035, by rfl⟩ : syracuseStep 2058761 = 1544071) B1544071
theorem B3475993 : Blo 1372005 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B2058791 : Blo 1372005 2058791 := bstep (se 1 (by rfl) ⟨1544093, by rfl⟩ : syracuseStep 2058791 = 3088187) B3088187
theorem B2058875 : Blo 1372005 2058875 := bstep (se 1 (by rfl) ⟨1544156, by rfl⟩ : syracuseStep 2058875 = 3088313) B3088313
theorem B3091067 : Blo 1372005 3091067 := bstep (se 1 (by rfl) ⟨2318300, by rfl⟩ : syracuseStep 3091067 = 4636601) B4636601
theorem B2607815 : Blo 1372005 2607815 := bstep (se 1 (by rfl) ⟨1955861, by rfl⟩ : syracuseStep 2607815 = 3911723) B3911723
theorem B2640595 : Blo 1372005 2640595 := bstep (se 1 (by rfl) ⟨1980446, by rfl⟩ : syracuseStep 2640595 = 3960893) B3960893
theorem B4631255 : Blo 1372005 4631255 := bstep (se 1 (by rfl) ⟨3473441, by rfl⟩ : syracuseStep 4631255 = 6946883) B6946883
theorem B2059001 : Blo 1372005 2059001 := bstep (se 2 (by rfl) ⟨772125, by rfl⟩ : syracuseStep 2059001 = 1544251) B1544251
theorem B3091193 : Blo 1372005 3091193 := bstep (se 2 (by rfl) ⟨1159197, by rfl⟩ : syracuseStep 3091193 = 2318395) B2318395
theorem B5212957 : Blo 1372005 5212957 := bstep (se 3 (by rfl) ⟨977429, by rfl⟩ : syracuseStep 5212957 = 1954859) B1954859
theorem B2198345 : Blo 1372005 2198345 := bstep (se 2 (by rfl) ⟨824379, by rfl⟩ : syracuseStep 2198345 = 1648759) B1648759
theorem B3476297 : Blo 1372005 3476297 := bstep (se 2 (by rfl) ⟨1303611, by rfl⟩ : syracuseStep 3476297 = 2607223) B2607223
theorem B2059103 : Blo 1372005 2059103 := bstep (se 1 (by rfl) ⟨1544327, by rfl⟩ : syracuseStep 2059103 = 3088655) B3088655
theorem B2607967 : Blo 1372005 2607967 := bstep (se 1 (by rfl) ⟨1955975, by rfl⟩ : syracuseStep 2607967 = 3911951) B3911951
theorem B2059115 : Blo 1372005 2059115 := bstep (se 1 (by rfl) ⟨1544336, by rfl⟩ : syracuseStep 2059115 = 3088673) B3088673
theorem B4631471 : Blo 1372005 4631471 := bstep (se 1 (by rfl) ⟨3473603, by rfl⟩ : syracuseStep 4631471 = 6947207) B6947207
theorem B3091463 : Blo 1372005 3091463 := bstep (se 1 (by rfl) ⟨2318597, by rfl⟩ : syracuseStep 3091463 = 4637195) B4637195
theorem B3910675 : Blo 1372005 3910675 := bstep (se 1 (by rfl) ⟨2933006, by rfl⟩ : syracuseStep 3910675 = 5866013) B5866013
theorem B2059343 : Blo 1372005 2059343 := bstep (se 1 (by rfl) ⟨1544507, by rfl⟩ : syracuseStep 2059343 = 3089015) B3089015
theorem B5287027 : Blo 1372005 5287027 := bstep (se 1 (by rfl) ⟨3965270, by rfl⟩ : syracuseStep 5287027 = 7930541) B7930541
theorem B2059463 : Blo 1372005 2059463 := bstep (se 1 (by rfl) ⟨1544597, by rfl⟩ : syracuseStep 2059463 = 3089195) B3089195
theorem B8793359 : Blo 1372005 8793359 := bstep (se 1 (by rfl) ⟨6595019, by rfl⟩ : syracuseStep 8793359 = 13190039) B13190039
theorem B2059625 : Blo 1372005 2059625 := bstep (se 2 (by rfl) ⟨772359, by rfl⟩ : syracuseStep 2059625 = 1544719) B1544719
theorem B3911017 : Blo 1372005 3911017 := bstep (se 2 (by rfl) ⟨1466631, by rfl⟩ : syracuseStep 3911017 = 2933263) B2933263
theorem B2059703 : Blo 1372005 2059703 := bstep (se 1 (by rfl) ⟨1544777, by rfl⟩ : syracuseStep 2059703 = 3089555) B3089555
theorem B2059739 : Blo 1372005 2059739 := bstep (se 1 (by rfl) ⟨1544804, by rfl⟩ : syracuseStep 2059739 = 3089609) B3089609
theorem B3911291 : Blo 1372005 3911291 := bstep (se 1 (by rfl) ⟨2933468, by rfl⟩ : syracuseStep 3911291 = 5866937) B5866937
theorem B9891517 : Blo 1372005 9891517 := bstep (se 3 (by rfl) ⟨1854659, by rfl⟩ : syracuseStep 9891517 = 3709319) B3709319
theorem B2576233 : Blo 1372005 2576233 := bstep (se 2 (by rfl) ⟨966087, by rfl⟩ : syracuseStep 2576233 = 1932175) B1932175
theorem B1372027 : Blo 1372005 1372027 := bstep (se 1 (by rfl) ⟨1029020, by rfl⟩ : syracuseStep 1372027 = 2058041) B2058041
theorem B5861281 : Blo 1372005 5861281 := bstep (se 2 (by rfl) ⟨2197980, by rfl⟩ : syracuseStep 5861281 = 4395961) B4395961
theorem B1372079 : Blo 1372005 1372079 := bstep (se 1 (by rfl) ⟨1029059, by rfl⟩ : syracuseStep 1372079 = 2058119) B2058119
theorem B2060207 : Blo 1372005 2060207 := bstep (se 1 (by rfl) ⟨1545155, by rfl⟩ : syracuseStep 2060207 = 3090311) B3090311
theorem B3477431 : Blo 1372005 3477431 := bstep (se 1 (by rfl) ⟨2608073, by rfl⟩ : syracuseStep 3477431 = 5216147) B5216147
theorem B1372103 : Blo 1372005 1372103 := bstep (se 1 (by rfl) ⟨1029077, by rfl⟩ : syracuseStep 1372103 = 2058155) B2058155
theorem B1372123 : Blo 1372005 1372123 := bstep (se 1 (by rfl) ⟨1029092, by rfl⟩ : syracuseStep 1372123 = 2058185) B2058185
theorem B2060297 : Blo 1372005 2060297 := bstep (se 2 (by rfl) ⟨772611, by rfl⟩ : syracuseStep 2060297 = 1545223) B1545223
theorem B8581135 : Blo 1372005 8581135 := bstep (se 1 (by rfl) ⟨6435851, by rfl⟩ : syracuseStep 8581135 = 12871703) B12871703
theorem B1372199 : Blo 1372005 1372199 := bstep (se 1 (by rfl) ⟨1029149, by rfl⟩ : syracuseStep 1372199 = 2058299) B2058299
theorem B2060327 : Blo 1372005 2060327 := bstep (se 1 (by rfl) ⟨1545245, by rfl⟩ : syracuseStep 2060327 = 3090491) B3090491
theorem B1372239 : Blo 1372005 1372239 := bstep (se 1 (by rfl) ⟨1029179, by rfl⟩ : syracuseStep 1372239 = 2058359) B2058359
theorem B7925849 : Blo 1372005 7925849 := bstep (se 2 (by rfl) ⟨2972193, by rfl⟩ : syracuseStep 7925849 = 5944387) B5944387
theorem B1372255 : Blo 1372005 1372255 := bstep (se 1 (by rfl) ⟨1029191, by rfl⟩ : syracuseStep 1372255 = 2058383) B2058383
theorem B1372283 : Blo 1372005 1372283 := bstep (se 1 (by rfl) ⟨1029212, by rfl⟩ : syracuseStep 1372283 = 2058425) B2058425
theorem B2060411 : Blo 1372005 2060411 := bstep (se 1 (by rfl) ⟨1545308, by rfl⟩ : syracuseStep 2060411 = 3090617) B3090617
theorem B1372335 : Blo 1372005 1372335 := bstep (se 1 (by rfl) ⟨1029251, by rfl⟩ : syracuseStep 1372335 = 2058503) B2058503
theorem B1372359 : Blo 1372005 1372359 := bstep (se 1 (by rfl) ⟨1029269, by rfl⟩ : syracuseStep 1372359 = 2058539) B2058539
theorem B1372379 : Blo 1372005 1372379 := bstep (se 1 (by rfl) ⟨1029284, by rfl⟩ : syracuseStep 1372379 = 2058569) B2058569
theorem B2060537 : Blo 1372005 2060537 := bstep (se 2 (by rfl) ⟨772701, by rfl⟩ : syracuseStep 2060537 = 1545403) B1545403
theorem B1372455 : Blo 1372005 1372455 := bstep (se 1 (by rfl) ⟨1029341, by rfl⟩ : syracuseStep 1372455 = 2058683) B2058683
theorem B1372495 : Blo 1372005 1372495 := bstep (se 1 (by rfl) ⟨1029371, by rfl⟩ : syracuseStep 1372495 = 2058743) B2058743
theorem B1372511 : Blo 1372005 1372511 := bstep (se 1 (by rfl) ⟨1029383, by rfl⟩ : syracuseStep 1372511 = 2058767) B2058767
theorem B2060639 : Blo 1372005 2060639 := bstep (se 1 (by rfl) ⟨1545479, by rfl⟩ : syracuseStep 2060639 = 3090959) B3090959
theorem B1954153 : Blo 1372005 1954153 := bstep (se 2 (by rfl) ⟨732807, by rfl⟩ : syracuseStep 1954153 = 1465615) B1465615
theorem B2060651 : Blo 1372005 2060651 := bstep (se 1 (by rfl) ⟨1545488, by rfl⟩ : syracuseStep 2060651 = 3090977) B3090977
theorem B1372539 : Blo 1372005 1372539 := bstep (se 1 (by rfl) ⟨1029404, by rfl⟩ : syracuseStep 1372539 = 2058809) B2058809
theorem B1372591 : Blo 1372005 1372591 := bstep (se 1 (by rfl) ⟨1029443, by rfl⟩ : syracuseStep 1372591 = 2058887) B2058887
theorem B1372615 : Blo 1372005 1372615 := bstep (se 1 (by rfl) ⟨1029461, by rfl⟩ : syracuseStep 1372615 = 2058923) B2058923
theorem B1372635 : Blo 1372005 1372635 := bstep (se 1 (by rfl) ⟨1029476, by rfl⟩ : syracuseStep 1372635 = 2058953) B2058953
theorem B1372711 : Blo 1372005 1372711 := bstep (se 1 (by rfl) ⟨1029533, by rfl⟩ : syracuseStep 1372711 = 2059067) B2059067
theorem B6599227 : Blo 1372005 6599227 := bstep (se 1 (by rfl) ⟨4949420, by rfl⟩ : syracuseStep 6599227 = 9898841) B9898841
theorem B1372751 : Blo 1372005 1372751 := bstep (se 1 (by rfl) ⟨1029563, by rfl⟩ : syracuseStep 1372751 = 2059127) B2059127
theorem B2060879 : Blo 1372005 2060879 := bstep (se 1 (by rfl) ⟨1545659, by rfl⟩ : syracuseStep 2060879 = 3091319) B3091319
theorem B1372767 : Blo 1372005 1372767 := bstep (se 1 (by rfl) ⟨1029575, by rfl⟩ : syracuseStep 1372767 = 2059151) B2059151
theorem B1372795 : Blo 1372005 1372795 := bstep (se 1 (by rfl) ⟨1029596, by rfl⟩ : syracuseStep 1372795 = 2059193) B2059193
theorem B1544827 : Blo 1372005 1544827 := bstep (se 1 (by rfl) ⟨1158620, by rfl⟩ : syracuseStep 1544827 = 2317241) B2317241
theorem B1372847 : Blo 1372005 1372847 := bstep (se 1 (by rfl) ⟨1029635, by rfl⟩ : syracuseStep 1372847 = 2059271) B2059271
theorem B1372871 : Blo 1372005 1372871 := bstep (se 1 (by rfl) ⟨1029653, by rfl⟩ : syracuseStep 1372871 = 2059307) B2059307
theorem B2060999 : Blo 1372005 2060999 := bstep (se 1 (by rfl) ⟨1545749, by rfl⟩ : syracuseStep 2060999 = 3091499) B3091499
theorem B3912407 : Blo 1372005 3912407 := bstep (se 1 (by rfl) ⟨2934305, by rfl⟩ : syracuseStep 3912407 = 5868611) B5868611
theorem B1372891 : Blo 1372005 1372891 := bstep (se 1 (by rfl) ⟨1029668, by rfl⟩ : syracuseStep 1372891 = 2059337) B2059337
theorem B1372967 : Blo 1372005 1372967 := bstep (se 1 (by rfl) ⟨1029725, by rfl⟩ : syracuseStep 1372967 = 2059451) B2059451
theorem B1373007 : Blo 1372005 1373007 := bstep (se 1 (by rfl) ⟨1029755, by rfl⟩ : syracuseStep 1373007 = 2059511) B2059511
theorem B4174687 : Blo 1372005 4174687 := bstep (se 1 (by rfl) ⟨3131015, by rfl⟩ : syracuseStep 4174687 = 6262031) B6262031
theorem B1373023 : Blo 1372005 1373023 := bstep (se 1 (by rfl) ⟨1029767, by rfl⟩ : syracuseStep 1373023 = 2059535) B2059535
theorem B64295795 : Blo 1372005 64295795 := bstep (se 1 (by rfl) ⟨48221846, by rfl⟩ : syracuseStep 64295795 = 96443693) B96443693
theorem B1373051 : Blo 1372005 1373051 := bstep (se 1 (by rfl) ⟨1029788, by rfl⟩ : syracuseStep 1373051 = 2059577) B2059577
theorem B1373103 : Blo 1372005 1373103 := bstep (se 1 (by rfl) ⟨1029827, by rfl⟩ : syracuseStep 1373103 = 2059655) B2059655
theorem B1373127 : Blo 1372005 1373127 := bstep (se 1 (by rfl) ⟨1029845, by rfl⟩ : syracuseStep 1373127 = 2059691) B2059691
theorem B1373147 : Blo 1372005 1373147 := bstep (se 1 (by rfl) ⟨1029860, by rfl⟩ : syracuseStep 1373147 = 2059721) B2059721
theorem B4699151 : Blo 1372005 4699151 := bstep (se 1 (by rfl) ⟨3524363, by rfl⟩ : syracuseStep 4699151 = 7048727) B7048727
theorem B1373223 : Blo 1372005 1373223 := bstep (se 1 (by rfl) ⟨1029917, by rfl⟩ : syracuseStep 1373223 = 2059835) B2059835
theorem B1373263 : Blo 1372005 1373263 := bstep (se 1 (by rfl) ⟨1029947, by rfl⟩ : syracuseStep 1373263 = 2059895) B2059895
theorem B1545295 : Blo 1372005 1545295 := bstep (se 1 (by rfl) ⟨1158971, by rfl⟩ : syracuseStep 1545295 = 2317943) B2317943
theorem B1373279 : Blo 1372005 1373279 := bstep (se 1 (by rfl) ⟨1029959, by rfl⟩ : syracuseStep 1373279 = 2059919) B2059919
theorem B1373307 : Blo 1372005 1373307 := bstep (se 1 (by rfl) ⟨1029980, by rfl⟩ : syracuseStep 1373307 = 2059961) B2059961
theorem B1373359 : Blo 1372005 1373359 := bstep (se 1 (by rfl) ⟨1030019, by rfl⟩ : syracuseStep 1373359 = 2060039) B2060039
theorem B1373383 : Blo 1372005 1373383 := bstep (se 1 (by rfl) ⟨1030037, by rfl⟩ : syracuseStep 1373383 = 2060075) B2060075
theorem B1373403 : Blo 1372005 1373403 := bstep (se 1 (by rfl) ⟨1030052, by rfl⟩ : syracuseStep 1373403 = 2060105) B2060105
theorem B4633847 : Blo 1372005 4633847 := bstep (se 1 (by rfl) ⟨3475385, by rfl⟩ : syracuseStep 4633847 = 6950771) B6950771
theorem B2315513 : Blo 1372005 2315513 := bstep (se 2 (by rfl) ⟨868317, by rfl⟩ : syracuseStep 2315513 = 1736635) B1736635
theorem B1373479 : Blo 1372005 1373479 := bstep (se 1 (by rfl) ⟨1030109, by rfl⟩ : syracuseStep 1373479 = 2060219) B2060219
theorem B1373519 : Blo 1372005 1373519 := bstep (se 1 (by rfl) ⟨1030139, by rfl⟩ : syracuseStep 1373519 = 2060279) B2060279
theorem B1373535 : Blo 1372005 1373535 := bstep (se 1 (by rfl) ⟨1030151, by rfl⟩ : syracuseStep 1373535 = 2060303) B2060303
theorem B1373563 : Blo 1372005 1373563 := bstep (se 1 (by rfl) ⟨1030172, by rfl⟩ : syracuseStep 1373563 = 2060345) B2060345
theorem B5019023 : Blo 1372005 5019023 := bstep (se 1 (by rfl) ⟨3764267, by rfl⟩ : syracuseStep 5019023 = 7528535) B7528535
theorem B2315695 : Blo 1372005 2315695 := bstep (se 1 (by rfl) ⟨1736771, by rfl⟩ : syracuseStep 2315695 = 3473543) B3473543
theorem B1373615 : Blo 1372005 1373615 := bstep (se 1 (by rfl) ⟨1030211, by rfl⟩ : syracuseStep 1373615 = 2060423) B2060423
theorem B1373639 : Blo 1372005 1373639 := bstep (se 1 (by rfl) ⟨1030229, by rfl⟩ : syracuseStep 1373639 = 2060459) B2060459
theorem B8353243 : Blo 1372005 8353243 := bstep (se 1 (by rfl) ⟨6264932, by rfl⟩ : syracuseStep 8353243 = 12529865) B12529865
theorem B1373659 : Blo 1372005 1373659 := bstep (se 1 (by rfl) ⟨1030244, by rfl⟩ : syracuseStep 1373659 = 2060489) B2060489
theorem B1545691 : Blo 1372005 1545691 := bstep (se 1 (by rfl) ⟨1159268, by rfl⟩ : syracuseStep 1545691 = 2318537) B2318537
theorem B2315783 : Blo 1372005 2315783 := bstep (se 1 (by rfl) ⟨1736837, by rfl⟩ : syracuseStep 2315783 = 3473675) B3473675
theorem B1373735 : Blo 1372005 1373735 := bstep (se 1 (by rfl) ⟨1030301, by rfl⟩ : syracuseStep 1373735 = 2060603) B2060603
theorem B4634171 : Blo 1372005 4634171 := bstep (se 1 (by rfl) ⟨3475628, by rfl⟩ : syracuseStep 4634171 = 6951257) B6951257
theorem B1373775 : Blo 1372005 1373775 := bstep (se 1 (by rfl) ⟨1030331, by rfl⟩ : syracuseStep 1373775 = 2060663) B2060663
theorem B1373791 : Blo 1372005 1373791 := bstep (se 1 (by rfl) ⟨1030343, by rfl⟩ : syracuseStep 1373791 = 2060687) B2060687
theorem B2930273 : Blo 1372005 2930273 := bstep (se 2 (by rfl) ⟨1098852, by rfl⟩ : syracuseStep 2930273 = 2197705) B2197705
theorem B1373819 : Blo 1372005 1373819 := bstep (se 1 (by rfl) ⟨1030364, by rfl⟩ : syracuseStep 1373819 = 2060729) B2060729
theorem B1373871 : Blo 1372005 1373871 := bstep (se 1 (by rfl) ⟨1030403, by rfl⟩ : syracuseStep 1373871 = 2060807) B2060807
theorem B2930375 : Blo 1372005 2930375 := bstep (se 1 (by rfl) ⟨2197781, by rfl⟩ : syracuseStep 2930375 = 4395563) B4395563
theorem B1373895 : Blo 1372005 1373895 := bstep (se 1 (by rfl) ⟨1030421, by rfl⟩ : syracuseStep 1373895 = 2060843) B2060843
theorem B1373915 : Blo 1372005 1373915 := bstep (se 1 (by rfl) ⟨1030436, by rfl⟩ : syracuseStep 1373915 = 2060873) B2060873
theorem B142571249 : Blo 1372005 142571249 := bstep (se 2 (by rfl) ⟨53464218, by rfl⟩ : syracuseStep 142571249 = 106928437) B106928437
theorem B1373991 : Blo 1372005 1373991 := bstep (se 1 (by rfl) ⟨1030493, by rfl⟩ : syracuseStep 1373991 = 2060987) B2060987
theorem B5863211 : Blo 1372005 5863211 := bstep (se 1 (by rfl) ⟨4397408, by rfl⟩ : syracuseStep 5863211 = 8794817) B8794817
theorem B4634441 : Blo 1372005 4634441 := bstep (se 2 (by rfl) ⟨1737915, by rfl⟩ : syracuseStep 4634441 = 3475831) B3475831
theorem B2316127 : Blo 1372005 2316127 := bstep (se 1 (by rfl) ⟨1737095, by rfl⟩ : syracuseStep 2316127 = 3474191) B3474191
theorem B8796023 : Blo 1372005 8796023 := bstep (se 1 (by rfl) ⟨6597017, by rfl⟩ : syracuseStep 8796023 = 13194035) B13194035
theorem B21419957 : Blo 1372005 21419957 := bstep (se 5 (by rfl) ⟨1004060, by rfl⟩ : syracuseStep 21419957 = 2008121) B2008121
theorem B2316215 : Blo 1372005 2316215 := bstep (se 1 (by rfl) ⟨1737161, by rfl⟩ : syracuseStep 2316215 = 3474323) B3474323
theorem B21133315 : Blo 1372005 21133315 := bstep (se 1 (by rfl) ⟨15849986, by rfl⟩ : syracuseStep 21133315 = 31699973) B31699973
theorem B17594657 : Blo 1372005 17594657 := bstep (se 2 (by rfl) ⟨6597996, by rfl⟩ : syracuseStep 17594657 = 13195993) B13195993
theorem B7821805 : Blo 1372005 7821805 := bstep (se 3 (by rfl) ⟨1466588, by rfl⟩ : syracuseStep 7821805 = 2933177) B2933177
theorem B2316809 : Blo 1372005 2316809 := bstep (se 2 (by rfl) ⟨868803, by rfl⟩ : syracuseStep 2316809 = 1737607) B1737607
theorem B71293505 : Blo 1372005 71293505 := bstep (se 2 (by rfl) ⟨26735064, by rfl⟩ : syracuseStep 71293505 = 53470129) B53470129
theorem B1587791 : Blo 1372005 1587791 := bstep (se 1 (by rfl) ⟨1190843, by rfl⟩ : syracuseStep 1587791 = 2381687) B2381687
theorem B4397665 : Blo 1372005 4397665 := bstep (se 2 (by rfl) ⟨1649124, by rfl⟩ : syracuseStep 4397665 = 3298249) B3298249
theorem B2316971 : Blo 1372005 2316971 := bstep (se 1 (by rfl) ⟨1737728, by rfl⟩ : syracuseStep 2316971 = 3475457) B3475457
theorem B1391303 : Blo 1372005 1391303 := bstep (se 1 (by rfl) ⟨1043477, by rfl⟩ : syracuseStep 1391303 = 2086955) B2086955
theorem B5569235 : Blo 1372005 5569235 := bstep (se 1 (by rfl) ⟨4176926, by rfl⟩ : syracuseStep 5569235 = 8353853) B8353853
theorem B3087287 : Blo 1372005 3087287 := bstep (se 1 (by rfl) ⟨2315465, by rfl⟩ : syracuseStep 3087287 = 4630931) B4630931
theorem B4635575 : Blo 1372005 4635575 := bstep (se 1 (by rfl) ⟨3476681, by rfl⟩ : syracuseStep 4635575 = 6953363) B6953363
theorem B10574813 : Blo 1372005 10574813 := bstep (se 3 (by rfl) ⟨1982777, by rfl⟩ : syracuseStep 10574813 = 3965555) B3965555
theorem B7527397 : Blo 1372005 7527397 := bstep (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) B1411387
theorem B2317369 : Blo 1372005 2317369 := bstep (se 2 (by rfl) ⟨869013, by rfl⟩ : syracuseStep 2317369 = 1738027) B1738027
theorem B10419353 : Blo 1372005 10419353 := bstep (se 2 (by rfl) ⟨3907257, by rfl⟩ : syracuseStep 10419353 = 7814515) B7814515
theorem B4947115 : Blo 1372005 4947115 := bstep (se 1 (by rfl) ⟨3710336, by rfl⟩ : syracuseStep 4947115 = 7420673) B7420673
theorem B2317511 : Blo 1372005 2317511 := bstep (se 1 (by rfl) ⟨1738133, by rfl⟩ : syracuseStep 2317511 = 3476267) B3476267
theorem B2317673 : Blo 1372005 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B9395675 : Blo 1372005 9395675 := bstep (se 1 (by rfl) ⟨7046756, by rfl⟩ : syracuseStep 9395675 = 14093513) B14093513
theorem B3087881 : Blo 1372005 3087881 := bstep (se 2 (by rfl) ⟨1157955, by rfl⟩ : syracuseStep 3087881 = 2315911) B2315911
theorem B4636169 : Blo 1372005 4636169 := bstep (se 2 (by rfl) ⟨1738563, by rfl⟩ : syracuseStep 4636169 = 3477127) B3477127
theorem B28171909 : Blo 1372005 28171909 := bstep (se 4 (by rfl) ⟨2641116, by rfl⟩ : syracuseStep 28171909 = 5282233) B5282233
theorem B5283467 : Blo 1372005 5283467 := bstep (se 1 (by rfl) ⟨3962600, by rfl⟩ : syracuseStep 5283467 = 7925201) B7925201
theorem B2318071 : Blo 1372005 2318071 := bstep (se 1 (by rfl) ⟨1738553, by rfl⟩ : syracuseStep 2318071 = 3477107) B3477107
theorem B2604793 : Blo 1372005 2604793 := bstep (se 2 (by rfl) ⟨976797, by rfl⟩ : syracuseStep 2604793 = 1953595) B1953595
theorem B3088223 : Blo 1372005 3088223 := bstep (se 1 (by rfl) ⟨2316167, by rfl⟩ : syracuseStep 3088223 = 4632335) B4632335
theorem B6946721 : Blo 1372005 6946721 := bstep (se 2 (by rfl) ⟨2605020, by rfl⟩ : syracuseStep 6946721 = 5210041) B5210041
theorem B4456367 : Blo 1372005 4456367 := bstep (se 1 (by rfl) ⟨3342275, by rfl⟩ : syracuseStep 4456367 = 6684551) B6684551
theorem B2318267 : Blo 1372005 2318267 := bstep (se 1 (by rfl) ⟨1738700, by rfl⟩ : syracuseStep 2318267 = 3477401) B3477401
theorem B5283899 : Blo 1372005 5283899 := bstep (se 1 (by rfl) ⟨3962924, by rfl⟩ : syracuseStep 5283899 = 7925849) B7925849
theorem B3473513 : Blo 1372005 3473513 := bstep (se 2 (by rfl) ⟨1302567, by rfl⟩ : syracuseStep 3473513 = 2605135) B2605135
theorem B2474407 : Blo 1372005 2474407 := bstep (se 1 (by rfl) ⟨1855805, by rfl⟩ : syracuseStep 2474407 = 3711611) B3711611
theorem B3670447 : Blo 1372005 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B5865929 : Blo 1372005 5865929 := bstep (se 2 (by rfl) ⟨2199723, by rfl⟩ : syracuseStep 5865929 = 4399447) B4399447
theorem B2605537 : Blo 1372005 2605537 := bstep (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) B1954153
theorem B3473999 : Blo 1372005 3473999 := bstep (se 1 (by rfl) ⟨2605499, by rfl⟩ : syracuseStep 3473999 = 5210999) B5210999
theorem B6259297 : Blo 1372005 6259297 := bstep (se 2 (by rfl) ⟨2347236, by rfl⟩ : syracuseStep 6259297 = 4694473) B4694473
theorem B10429073 : Blo 1372005 10429073 := bstep (se 2 (by rfl) ⟨3910902, by rfl⟩ : syracuseStep 10429073 = 7821805) B7821805
theorem B6947531 : Blo 1372005 6947531 := bstep (se 1 (by rfl) ⟨5210648, by rfl⟩ : syracuseStep 6947531 = 10421297) B10421297
theorem B3523295 : Blo 1372005 3523295 := bstep (se 1 (by rfl) ⟨2642471, by rfl⟩ : syracuseStep 3523295 = 5284943) B5284943
theorem B8798969 : Blo 1372005 8798969 := bstep (se 2 (by rfl) ⟨3299613, by rfl⟩ : syracuseStep 8798969 = 6599227) B6599227
theorem B1737551 : Blo 1372005 1737551 := bstep (se 1 (by rfl) ⟨1303163, by rfl⟩ : syracuseStep 1737551 = 2606327) B2606327
theorem B3089231 : Blo 1372005 3089231 := bstep (se 1 (by rfl) ⟨2316923, by rfl⟩ : syracuseStep 3089231 = 4633847) B4633847
theorem B6947693 : Blo 1372005 6947693 := bstep (se 3 (by rfl) ⟨1302692, by rfl⟩ : syracuseStep 6947693 = 2605385) B2605385
theorem B27493265 : Blo 1372005 27493265 := bstep (se 2 (by rfl) ⟨10309974, by rfl⟩ : syracuseStep 27493265 = 20619949) B20619949
theorem B4948931 : Blo 1372005 4948931 := bstep (se 1 (by rfl) ⟨3711698, by rfl⟩ : syracuseStep 4948931 = 7423397) B7423397
theorem B1737703 : Blo 1372005 1737703 := bstep (se 1 (by rfl) ⟨1303277, by rfl⟩ : syracuseStep 1737703 = 2606555) B2606555
theorem B3089447 : Blo 1372005 3089447 := bstep (se 1 (by rfl) ⟨2317085, by rfl⟩ : syracuseStep 3089447 = 4634171) B4634171
theorem B11732161 : Blo 1372005 11732161 := bstep (se 2 (by rfl) ⟨4399560, by rfl⟩ : syracuseStep 11732161 = 8799121) B8799121
theorem B3908807 : Blo 1372005 3908807 := bstep (se 1 (by rfl) ⟨2931605, by rfl⟩ : syracuseStep 3908807 = 5863211) B5863211
theorem B3474647 : Blo 1372005 3474647 := bstep (se 1 (by rfl) ⟨2605985, by rfl⟩ : syracuseStep 3474647 = 5211971) B5211971
theorem B3089627 : Blo 1372005 3089627 := bstep (se 1 (by rfl) ⟨2317220, by rfl⟩ : syracuseStep 3089627 = 4634441) B4634441
theorem B14279971 : Blo 1372005 14279971 := bstep (se 1 (by rfl) ⟨10709978, by rfl⟩ : syracuseStep 14279971 = 21419957) B21419957
theorem B10036529 : Blo 1372005 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B3089825 : Blo 1372005 3089825 := bstep (se 2 (by rfl) ⟨1158684, by rfl⟩ : syracuseStep 3089825 = 2317369) B2317369
theorem B6596153 : Blo 1372005 6596153 := bstep (se 2 (by rfl) ⟨2473557, by rfl⟩ : syracuseStep 6596153 = 4947115) B4947115
theorem B3475001 : Blo 1372005 3475001 := bstep (se 2 (by rfl) ⟨1303125, by rfl⟩ : syracuseStep 3475001 = 2606251) B2606251
theorem B3712823 : Blo 1372005 3712823 := bstep (se 1 (by rfl) ⟨2784617, by rfl⟩ : syracuseStep 3712823 = 5569235) B5569235
theorem B5211985 : Blo 1372005 5211985 := bstep (se 2 (by rfl) ⟨1954494, by rfl⟩ : syracuseStep 5211985 = 3908989) B3908989
theorem B2058191 : Blo 1372005 2058191 := bstep (se 1 (by rfl) ⟨1543643, by rfl⟩ : syracuseStep 2058191 = 3087287) B3087287
theorem B3090383 : Blo 1372005 3090383 := bstep (se 1 (by rfl) ⟨2317787, by rfl⟩ : syracuseStep 3090383 = 4635575) B4635575
theorem B5212289 : Blo 1372005 5212289 := bstep (se 2 (by rfl) ⟨1954608, by rfl⟩ : syracuseStep 5212289 = 3909217) B3909217
theorem B37562545 : Blo 1372005 37562545 := bstep (se 2 (by rfl) ⟨14085954, by rfl⟩ : syracuseStep 37562545 = 28171909) B28171909
theorem B3090761 : Blo 1372005 3090761 := bstep (se 2 (by rfl) ⟨1159035, by rfl⟩ : syracuseStep 3090761 = 2318071) B2318071
theorem B2058587 : Blo 1372005 2058587 := bstep (se 1 (by rfl) ⟨1543940, by rfl⟩ : syracuseStep 2058587 = 3087881) B3087881
theorem B3090779 : Blo 1372005 3090779 := bstep (se 1 (by rfl) ⟨2318084, by rfl⟩ : syracuseStep 3090779 = 4636169) B4636169
theorem B2607527 : Blo 1372005 2607527 := bstep (se 1 (by rfl) ⟨1955645, by rfl⟩ : syracuseStep 2607527 = 3911291) B3911291
theorem B3434977 : Blo 1372005 3434977 := bstep (se 2 (by rfl) ⟨1288116, by rfl⟩ : syracuseStep 3434977 = 2576233) B2576233
theorem B2058815 : Blo 1372005 2058815 := bstep (se 1 (by rfl) ⟨1544111, by rfl⟩ : syracuseStep 2058815 = 3088223) B3088223
theorem B5212745 : Blo 1372005 5212745 := bstep (se 2 (by rfl) ⟨1954779, by rfl⟩ : syracuseStep 5212745 = 3909559) B3909559
theorem B4631147 : Blo 1372005 4631147 := bstep (se 1 (by rfl) ⟨3473360, by rfl⟩ : syracuseStep 4631147 = 6946721) B6946721
theorem B2058935 : Blo 1372005 2058935 := bstep (se 1 (by rfl) ⟨1544201, by rfl⟩ : syracuseStep 2058935 = 3088403) B3088403
theorem B14838659 : Blo 1372005 14838659 := bstep (se 1 (by rfl) ⟨11128994, by rfl⟩ : syracuseStep 14838659 = 22257989) B22257989
theorem B2059163 : Blo 1372005 2059163 := bstep (se 1 (by rfl) ⟨1544372, by rfl⟩ : syracuseStep 2059163 = 3088745) B3088745
theorem B3091355 : Blo 1372005 3091355 := bstep (se 1 (by rfl) ⟨2318516, by rfl⟩ : syracuseStep 3091355 = 4637033) B4637033
theorem B10431503 : Blo 1372005 10431503 := bstep (se 1 (by rfl) ⟨7823627, by rfl⟩ : syracuseStep 10431503 = 15647255) B15647255
theorem B14855183 : Blo 1372005 14855183 := bstep (se 1 (by rfl) ⟨11141387, by rfl⟩ : syracuseStep 14855183 = 22282775) B22282775
theorem B18779201 : Blo 1372005 18779201 := bstep (se 2 (by rfl) ⟨7042200, by rfl⟩ : syracuseStep 18779201 = 14084401) B14084401
theorem B26750033 : Blo 1372005 26750033 := bstep (se 2 (by rfl) ⟨10031262, by rfl⟩ : syracuseStep 26750033 = 20062525) B20062525
theorem B2608271 : Blo 1372005 2608271 := bstep (se 1 (by rfl) ⟨1956203, by rfl⟩ : syracuseStep 2608271 = 3912407) B3912407
theorem B15862961 : Blo 1372005 15862961 := bstep (se 2 (by rfl) ⟨5948610, by rfl⟩ : syracuseStep 15862961 = 11897221) B11897221
theorem B4631741 : Blo 1372005 4631741 := bstep (se 3 (by rfl) ⟨868451, by rfl⟩ : syracuseStep 4631741 = 1736903) B1736903
theorem B42863863 : Blo 1372005 42863863 := bstep (se 1 (by rfl) ⟨32147897, by rfl⟩ : syracuseStep 42863863 = 64295795) B64295795
theorem B2059559 : Blo 1372005 2059559 := bstep (se 1 (by rfl) ⟨1544669, by rfl⟩ : syracuseStep 2059559 = 3089339) B3089339
theorem B3132767 : Blo 1372005 3132767 := bstep (se 1 (by rfl) ⟨2349575, by rfl⟩ : syracuseStep 3132767 = 4699151) B4699151
theorem B25390451 : Blo 1372005 25390451 := bstep (se 1 (by rfl) ⟨19042838, by rfl⟩ : syracuseStep 25390451 = 38085677) B38085677
theorem B2059643 : Blo 1372005 2059643 := bstep (se 1 (by rfl) ⟨1544732, by rfl⟩ : syracuseStep 2059643 = 3089465) B3089465
theorem B23449013 : Blo 1372005 23449013 := bstep (se 5 (by rfl) ⟨1099172, by rfl⟩ : syracuseStep 23449013 = 2198345) B2198345
theorem B2059769 : Blo 1372005 2059769 := bstep (se 2 (by rfl) ⟨772413, by rfl⟩ : syracuseStep 2059769 = 1544827) B1544827
theorem B1543675 : Blo 1372005 1543675 := bstep (se 1 (by rfl) ⟨1157756, by rfl⟩ : syracuseStep 1543675 = 2315513) B2315513
theorem B2059871 : Blo 1372005 2059871 := bstep (se 1 (by rfl) ⟨1544903, by rfl⟩ : syracuseStep 2059871 = 3089807) B3089807
theorem B1543855 : Blo 1372005 1543855 := bstep (se 1 (by rfl) ⟨1157891, by rfl⟩ : syracuseStep 1543855 = 2315783) B2315783
theorem B6950609 : Blo 1372005 6950609 := bstep (se 2 (by rfl) ⟨2606478, by rfl⟩ : syracuseStep 6950609 = 5212957) B5212957
theorem B1953515 : Blo 1372005 1953515 := bstep (se 1 (by rfl) ⟨1465136, by rfl⟩ : syracuseStep 1953515 = 2930273) B2930273
theorem B5566249 : Blo 1372005 5566249 := bstep (se 2 (by rfl) ⟨2087343, by rfl⟩ : syracuseStep 5566249 = 4174687) B4174687
theorem B3477289 : Blo 1372005 3477289 := bstep (se 2 (by rfl) ⟨1303983, by rfl⟩ : syracuseStep 3477289 = 2607967) B2607967
theorem B2060087 : Blo 1372005 2060087 := bstep (se 1 (by rfl) ⟨1545065, by rfl⟩ : syracuseStep 2060087 = 3090131) B3090131
theorem B95047499 : Blo 1372005 95047499 := bstep (se 1 (by rfl) ⟨71285624, by rfl⟩ : syracuseStep 95047499 = 142571249) B142571249
theorem B1372059 : Blo 1372005 1372059 := bstep (se 1 (by rfl) ⟨1029044, by rfl⟩ : syracuseStep 1372059 = 2058089) B2058089
theorem B1372111 : Blo 1372005 1372111 := bstep (se 1 (by rfl) ⟨1029083, by rfl⟩ : syracuseStep 1372111 = 2058167) B2058167
theorem B1544143 : Blo 1372005 1544143 := bstep (se 1 (by rfl) ⟨1158107, by rfl⟩ : syracuseStep 1544143 = 2316215) B2316215
theorem B1372135 : Blo 1372005 1372135 := bstep (se 1 (by rfl) ⟨1029101, by rfl⟩ : syracuseStep 1372135 = 2058203) B2058203
theorem B5214233 : Blo 1372005 5214233 := bstep (se 2 (by rfl) ⟨1955337, by rfl⟩ : syracuseStep 5214233 = 3910675) B3910675
theorem B33402941 : Blo 1372005 33402941 := bstep (se 3 (by rfl) ⟨6263051, by rfl⟩ : syracuseStep 33402941 = 12526103) B12526103
theorem B2060393 : Blo 1372005 2060393 := bstep (se 2 (by rfl) ⟨772647, by rfl⟩ : syracuseStep 2060393 = 1545295) B1545295
theorem B7049369 : Blo 1372005 7049369 := bstep (se 2 (by rfl) ⟨2643513, by rfl⟩ : syracuseStep 7049369 = 5287027) B5287027
theorem B190116013 : Blo 1372005 190116013 := bstep (se 3 (by rfl) ⟨35646752, by rfl⟩ : syracuseStep 190116013 = 71293505) B71293505
theorem B1372447 : Blo 1372005 1372447 := bstep (se 1 (by rfl) ⟨1029335, by rfl⟩ : syracuseStep 1372447 = 2058671) B2058671
theorem B1372507 : Blo 1372005 1372507 := bstep (se 1 (by rfl) ⟨1029380, by rfl⟩ : syracuseStep 1372507 = 2058761) B2058761
theorem B1544539 : Blo 1372005 1544539 := bstep (se 1 (by rfl) ⟨1158404, by rfl⟩ : syracuseStep 1544539 = 2316809) B2316809
theorem B1372527 : Blo 1372005 1372527 := bstep (se 1 (by rfl) ⟨1029395, by rfl⟩ : syracuseStep 1372527 = 2058791) B2058791
theorem B1372583 : Blo 1372005 1372583 := bstep (se 1 (by rfl) ⟨1029437, by rfl⟩ : syracuseStep 1372583 = 2058875) B2058875
theorem B2060711 : Blo 1372005 2060711 := bstep (se 1 (by rfl) ⟨1545533, by rfl⟩ : syracuseStep 2060711 = 3091067) B3091067
theorem B1544647 : Blo 1372005 1544647 := bstep (se 1 (by rfl) ⟨1158485, by rfl⟩ : syracuseStep 1544647 = 2316971) B2316971
theorem B5214689 : Blo 1372005 5214689 := bstep (se 2 (by rfl) ⟨1955508, by rfl⟩ : syracuseStep 5214689 = 3911017) B3911017
theorem B1372667 : Blo 1372005 1372667 := bstep (se 1 (by rfl) ⟨1029500, by rfl⟩ : syracuseStep 1372667 = 2059001) B2059001
theorem B2060795 : Blo 1372005 2060795 := bstep (se 1 (by rfl) ⟨1545596, by rfl⟩ : syracuseStep 2060795 = 3091193) B3091193
theorem B1372735 : Blo 1372005 1372735 := bstep (se 1 (by rfl) ⟨1029551, by rfl⟩ : syracuseStep 1372735 = 2059103) B2059103
theorem B1372743 : Blo 1372005 1372743 := bstep (se 1 (by rfl) ⟨1029557, by rfl⟩ : syracuseStep 1372743 = 2059115) B2059115
theorem B11137657 : Blo 1372005 11137657 := bstep (se 2 (by rfl) ⟨4176621, by rfl⟩ : syracuseStep 11137657 = 8353243) B8353243
theorem B2060921 : Blo 1372005 2060921 := bstep (se 2 (by rfl) ⟨772845, by rfl⟩ : syracuseStep 2060921 = 1545691) B1545691
theorem B7049875 : Blo 1372005 7049875 := bstep (se 1 (by rfl) ⟨5287406, by rfl⟩ : syracuseStep 7049875 = 10574813) B10574813
theorem B2060975 : Blo 1372005 2060975 := bstep (se 1 (by rfl) ⟨1545731, by rfl⟩ : syracuseStep 2060975 = 3091463) B3091463
theorem B1372895 : Blo 1372005 1372895 := bstep (se 1 (by rfl) ⟨1029671, by rfl⟩ : syracuseStep 1372895 = 2059343) B2059343
theorem B1372975 : Blo 1372005 1372975 := bstep (se 1 (by rfl) ⟨1029731, by rfl⟩ : syracuseStep 1372975 = 2059463) B2059463
theorem B1545007 : Blo 1372005 1545007 := bstep (se 1 (by rfl) ⟨1158755, by rfl⟩ : syracuseStep 1545007 = 2317511) B2317511
theorem B5862239 : Blo 1372005 5862239 := bstep (se 1 (by rfl) ⟨4396679, by rfl⟩ : syracuseStep 5862239 = 8793359) B8793359
theorem B1373083 : Blo 1372005 1373083 := bstep (se 1 (by rfl) ⟨1029812, by rfl⟩ : syracuseStep 1373083 = 2059625) B2059625
theorem B1545115 : Blo 1372005 1545115 := bstep (se 1 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 1545115 = 2317673) B2317673
theorem B1373135 : Blo 1372005 1373135 := bstep (se 1 (by rfl) ⟨1029851, by rfl⟩ : syracuseStep 1373135 = 2059703) B2059703
theorem B1373159 : Blo 1372005 1373159 := bstep (se 1 (by rfl) ⟨1029869, by rfl⟩ : syracuseStep 1373159 = 2059739) B2059739
theorem B6263783 : Blo 1372005 6263783 := bstep (se 1 (by rfl) ⟨4697837, by rfl⟩ : syracuseStep 6263783 = 9395675) B9395675
theorem B23475257 : Blo 1372005 23475257 := bstep (se 2 (by rfl) ⟨8803221, by rfl⟩ : syracuseStep 23475257 = 17606443) B17606443
theorem B2970911 : Blo 1372005 2970911 := bstep (se 1 (by rfl) ⟨2228183, by rfl⟩ : syracuseStep 2970911 = 4456367) B4456367
theorem B1373471 : Blo 1372005 1373471 := bstep (se 1 (by rfl) ⟨1030103, by rfl⟩ : syracuseStep 1373471 = 2060207) B2060207
theorem B1545511 : Blo 1372005 1545511 := bstep (se 1 (by rfl) ⟨1159133, by rfl⟩ : syracuseStep 1545511 = 2318267) B2318267
theorem B28177753 : Blo 1372005 28177753 := bstep (se 2 (by rfl) ⟨10566657, by rfl⟩ : syracuseStep 28177753 = 21133315) B21133315
theorem B1373531 : Blo 1372005 1373531 := bstep (se 1 (by rfl) ⟨1030148, by rfl⟩ : syracuseStep 1373531 = 2060297) B2060297
theorem B11441513 : Blo 1372005 11441513 := bstep (se 2 (by rfl) ⟨4290567, by rfl⟩ : syracuseStep 11441513 = 8581135) B8581135
theorem B1373551 : Blo 1372005 1373551 := bstep (se 1 (by rfl) ⟨1030163, by rfl⟩ : syracuseStep 1373551 = 2060327) B2060327
theorem B1545583 : Blo 1372005 1545583 := bstep (se 1 (by rfl) ⟨1159187, by rfl⟩ : syracuseStep 1545583 = 2318375) B2318375
theorem B1373607 : Blo 1372005 1373607 := bstep (se 1 (by rfl) ⟨1030205, by rfl⟩ : syracuseStep 1373607 = 2060411) B2060411
theorem B1373691 : Blo 1372005 1373691 := bstep (se 1 (by rfl) ⟨1030268, by rfl⟩ : syracuseStep 1373691 = 2060537) B2060537
theorem B1373759 : Blo 1372005 1373759 := bstep (se 1 (by rfl) ⟨1030319, by rfl⟩ : syracuseStep 1373759 = 2060639) B2060639
theorem B1373767 : Blo 1372005 1373767 := bstep (se 1 (by rfl) ⟨1030325, by rfl⟩ : syracuseStep 1373767 = 2060651) B2060651
theorem B7624327 : Blo 1372005 7624327 := bstep (se 1 (by rfl) ⟨5718245, by rfl⟩ : syracuseStep 7624327 = 11436491) B11436491
theorem B1373919 : Blo 1372005 1373919 := bstep (se 1 (by rfl) ⟨1030439, by rfl⟩ : syracuseStep 1373919 = 2060879) B2060879
theorem B2316073 : Blo 1372005 2316073 := bstep (se 2 (by rfl) ⟨868527, by rfl⟩ : syracuseStep 2316073 = 1737055) B1737055
theorem B1373999 : Blo 1372005 1373999 := bstep (se 1 (by rfl) ⟨1030499, by rfl⟩ : syracuseStep 1373999 = 2060999) B2060999
theorem B3815273 : Blo 1372005 3815273 := bstep (se 2 (by rfl) ⟨1430727, by rfl⟩ : syracuseStep 3815273 = 2861455) B2861455
theorem B4634657 : Blo 1372005 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B6953039 : Blo 1372005 6953039 := bstep (se 1 (by rfl) ⟨5214779, by rfl⟩ : syracuseStep 6953039 = 10429559) B10429559
theorem B5863553 : Blo 1372005 5863553 := bstep (se 2 (by rfl) ⟨2198832, by rfl⟩ : syracuseStep 5863553 = 4397665) B4397665
theorem B3520793 : Blo 1372005 3520793 := bstep (se 2 (by rfl) ⟨1320297, by rfl⟩ : syracuseStep 3520793 = 2640595) B2640595
theorem B13384061 : Blo 1372005 13384061 := bstep (se 3 (by rfl) ⟨2509511, by rfl⟩ : syracuseStep 13384061 = 5019023) B5019023
theorem B9525755 : Blo 1372005 9525755 := bstep (se 1 (by rfl) ⟨7144316, by rfl⟩ : syracuseStep 9525755 = 14288633) B14288633
theorem B2316863 : Blo 1372005 2316863 := bstep (se 1 (by rfl) ⟨1737647, by rfl⟩ : syracuseStep 2316863 = 3475295) B3475295
theorem B3299903 : Blo 1372005 3299903 := bstep (se 1 (by rfl) ⟨2474927, by rfl⟩ : syracuseStep 3299903 = 4949855) B4949855
theorem B5216831 : Blo 1372005 5216831 := bstep (se 1 (by rfl) ⟨3912623, by rfl⟩ : syracuseStep 5216831 = 7825247) B7825247
theorem B5864015 : Blo 1372005 5864015 := bstep (se 1 (by rfl) ⟨4398011, by rfl⟩ : syracuseStep 5864015 = 8796023) B8796023
theorem B3087071 : Blo 1372005 3087071 := bstep (se 1 (by rfl) ⟨2315303, by rfl⟩ : syracuseStep 3087071 = 4630607) B4630607
theorem B11729771 : Blo 1372005 11729771 := bstep (se 1 (by rfl) ⟨8797328, by rfl⟩ : syracuseStep 11729771 = 17594657) B17594657
theorem B4234109 : Blo 1372005 4234109 := bstep (se 3 (by rfl) ⟨793895, by rfl⟩ : syracuseStep 4234109 = 1587791) B1587791
theorem B3087323 : Blo 1372005 3087323 := bstep (se 1 (by rfl) ⟨2315492, by rfl⟩ : syracuseStep 3087323 = 4630985) B4630985
theorem B3087503 : Blo 1372005 3087503 := bstep (se 1 (by rfl) ⟨2315627, by rfl⟩ : syracuseStep 3087503 = 4631255) B4631255
theorem B7814333 : Blo 1372005 7814333 := bstep (se 3 (by rfl) ⟨1465187, by rfl⟩ : syracuseStep 7814333 = 2930375) B2930375
theorem B3710141 : Blo 1372005 3710141 := bstep (se 3 (by rfl) ⟨695651, by rfl⟩ : syracuseStep 3710141 = 1391303) B1391303
theorem B6954173 : Blo 1372005 6954173 := bstep (se 3 (by rfl) ⟨1303907, by rfl⟩ : syracuseStep 6954173 = 2607815) B2607815
theorem B2317531 : Blo 1372005 2317531 := bstep (se 1 (by rfl) ⟨1738148, by rfl⟩ : syracuseStep 2317531 = 3476297) B3476297
theorem B3087593 : Blo 1372005 3087593 := bstep (se 2 (by rfl) ⟨1157847, by rfl⟩ : syracuseStep 3087593 = 2315695) B2315695
theorem B3087647 : Blo 1372005 3087647 := bstep (se 1 (by rfl) ⟨2315735, by rfl⟩ : syracuseStep 3087647 = 4631471) B4631471
theorem B6946235 : Blo 1372005 6946235 := bstep (se 1 (by rfl) ⟨5209676, by rfl⟩ : syracuseStep 6946235 = 10419353) B10419353
theorem B13188689 : Blo 1372005 13188689 := bstep (se 2 (by rfl) ⟨4945758, by rfl⟩ : syracuseStep 13188689 = 9891517) B9891517
theorem B3473057 : Blo 1372005 3473057 := bstep (se 2 (by rfl) ⟨1302396, by rfl⟩ : syracuseStep 3473057 = 2604793) B2604793
theorem B3522311 : Blo 1372005 3522311 := bstep (se 1 (by rfl) ⟨2641733, by rfl⟩ : syracuseStep 3522311 = 5283467) B5283467
theorem B3088169 : Blo 1372005 3088169 := bstep (se 2 (by rfl) ⟨1158063, by rfl⟩ : syracuseStep 3088169 = 2316127) B2316127
theorem B7815041 : Blo 1372005 7815041 := bstep (se 2 (by rfl) ⟨2930640, by rfl⟩ : syracuseStep 7815041 = 5861281) B5861281
theorem B2318287 : Blo 1372005 2318287 := bstep (se 1 (by rfl) ⟨1738715, by rfl⟩ : syracuseStep 2318287 = 3477431) B3477431
theorem B3522599 : Blo 1372005 3522599 := bstep (se 1 (by rfl) ⟨2641949, by rfl⟩ : syracuseStep 3522599 = 5283899) B5283899
theorem B5865979 : Blo 1372005 5865979 := bstep (se 1 (by rfl) ⟨4399484, by rfl⟩ : syracuseStep 5865979 = 8798969) B8798969
theorem B3908159 : Blo 1372005 3908159 := bstep (se 1 (by rfl) ⟨2931119, by rfl⟩ : syracuseStep 3908159 = 5862239) B5862239
theorem B3474049 : Blo 1372005 3474049 := bstep (se 2 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 3474049 = 2605537) B2605537
theorem B9388781 : Blo 1372005 9388781 := bstep (se 3 (by rfl) ⟨1760396, by rfl⟩ : syracuseStep 9388781 = 3520793) B3520793
theorem B2605871 : Blo 1372005 2605871 := bstep (se 1 (by rfl) ⟨1954403, by rfl⟩ : syracuseStep 2605871 = 3908807) B3908807
theorem B2475215 : Blo 1372005 2475215 := bstep (se 1 (by rfl) ⟨1856411, by rfl⟩ : syracuseStep 2475215 = 3712823) B3712823
theorem B3089771 : Blo 1372005 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B3909035 : Blo 1372005 3909035 := bstep (se 1 (by rfl) ⟨2931776, by rfl⟩ : syracuseStep 3909035 = 5863553) B5863553
theorem B3474859 : Blo 1372005 3474859 := bstep (se 1 (by rfl) ⟨2606144, by rfl⟩ : syracuseStep 3474859 = 5212289) B5212289
theorem B8922707 : Blo 1372005 8922707 := bstep (se 1 (by rfl) ⟨6692030, by rfl⟩ : syracuseStep 8922707 = 13384061) B13384061
theorem B1738351 : Blo 1372005 1738351 := bstep (se 1 (by rfl) ⟨1303763, by rfl⟩ : syracuseStep 1738351 = 2607527) B2607527
theorem B3090041 : Blo 1372005 3090041 := bstep (se 2 (by rfl) ⟨1158765, by rfl⟩ : syracuseStep 3090041 = 2317531) B2317531
theorem B6350503 : Blo 1372005 6350503 := bstep (se 1 (by rfl) ⟨4762877, by rfl⟩ : syracuseStep 6350503 = 9525755) B9525755
theorem B19039961 : Blo 1372005 19039961 := bstep (se 2 (by rfl) ⟨7139985, by rfl⟩ : syracuseStep 19039961 = 14279971) B14279971
theorem B3475163 : Blo 1372005 3475163 := bstep (se 1 (by rfl) ⟨2606372, by rfl⟩ : syracuseStep 3475163 = 5212745) B5212745
theorem B3909343 : Blo 1372005 3909343 := bstep (se 1 (by rfl) ⟨2932007, by rfl⟩ : syracuseStep 3909343 = 5864015) B5864015
theorem B37570337 : Blo 1372005 37570337 := bstep (se 2 (by rfl) ⟨14088876, by rfl⟩ : syracuseStep 37570337 = 28177753) B28177753
theorem B2058047 : Blo 1372005 2058047 := bstep (se 1 (by rfl) ⟨1543535, by rfl⟩ : syracuseStep 2058047 = 3087071) B3087071
theorem B2058215 : Blo 1372005 2058215 := bstep (se 1 (by rfl) ⟨1543661, by rfl⟩ : syracuseStep 2058215 = 3087323) B3087323
theorem B2058233 : Blo 1372005 2058233 := bstep (se 2 (by rfl) ⟨771837, by rfl⟩ : syracuseStep 2058233 = 1543675) B1543675
theorem B12519467 : Blo 1372005 12519467 := bstep (se 1 (by rfl) ⟨9389600, by rfl⟩ : syracuseStep 12519467 = 18779201) B18779201
theorem B2058335 : Blo 1372005 2058335 := bstep (se 1 (by rfl) ⟨1543751, by rfl⟩ : syracuseStep 2058335 = 3087503) B3087503
theorem B1738847 : Blo 1372005 1738847 := bstep (se 1 (by rfl) ⟨1304135, by rfl⟩ : syracuseStep 1738847 = 2608271) B2608271
theorem B2058395 : Blo 1372005 2058395 := bstep (se 1 (by rfl) ⟨1543796, by rfl⟩ : syracuseStep 2058395 = 3087593) B3087593
theorem B2058431 : Blo 1372005 2058431 := bstep (se 1 (by rfl) ⟨1543823, by rfl⟩ : syracuseStep 2058431 = 3087647) B3087647
theorem B2058473 : Blo 1372005 2058473 := bstep (se 2 (by rfl) ⟨771927, by rfl⟩ : syracuseStep 2058473 = 1543855) B1543855
theorem B16926967 : Blo 1372005 16926967 := bstep (se 1 (by rfl) ⟨12695225, by rfl⟩ : syracuseStep 16926967 = 25390451) B25390451
theorem B15632675 : Blo 1372005 15632675 := bstep (se 1 (by rfl) ⟨11724506, by rfl⟩ : syracuseStep 15632675 = 23449013) B23449013
theorem B4630823 : Blo 1372005 4630823 := bstep (se 1 (by rfl) ⟨3473117, by rfl⟩ : syracuseStep 4630823 = 6946235) B6946235
theorem B11290957 : Blo 1372005 11290957 := bstep (se 3 (by rfl) ⟨2117054, by rfl⟩ : syracuseStep 11290957 = 4234109) B4234109
theorem B8792459 : Blo 1372005 8792459 := bstep (se 1 (by rfl) ⟨6594344, by rfl⟩ : syracuseStep 8792459 = 13188689) B13188689
theorem B6949313 : Blo 1372005 6949313 := bstep (se 2 (by rfl) ⟨2605992, by rfl⟩ : syracuseStep 6949313 = 5211985) B5211985
theorem B18319877 : Blo 1372005 18319877 := bstep (se 4 (by rfl) ⟨1717488, by rfl⟩ : syracuseStep 18319877 = 3434977) B3434977
theorem B2058779 : Blo 1372005 2058779 := bstep (se 1 (by rfl) ⟨1544084, by rfl⟩ : syracuseStep 2058779 = 3088169) B3088169
theorem B2058857 : Blo 1372005 2058857 := bstep (se 2 (by rfl) ⟨772071, by rfl⟩ : syracuseStep 2058857 = 1544143) B1544143
theorem B3091049 : Blo 1372005 3091049 := bstep (se 2 (by rfl) ⟨1159143, by rfl⟩ : syracuseStep 3091049 = 2318287) B2318287
theorem B3476155 : Blo 1372005 3476155 := bstep (se 1 (by rfl) ⟨2607116, by rfl⟩ : syracuseStep 3476155 = 5214233) B5214233
theorem B22268627 : Blo 1372005 22268627 := bstep (se 1 (by rfl) ⟨16701470, by rfl⟩ : syracuseStep 22268627 = 33402941) B33402941
theorem B253488017 : Blo 1372005 253488017 := bstep (se 2 (by rfl) ⟨95058006, by rfl⟩ : syracuseStep 253488017 = 190116013) B190116013
theorem B3910619 : Blo 1372005 3910619 := bstep (se 1 (by rfl) ⟨2932964, by rfl⟩ : syracuseStep 3910619 = 5865929) B5865929
theorem B3476459 : Blo 1372005 3476459 := bstep (se 1 (by rfl) ⟨2607344, by rfl⟩ : syracuseStep 3476459 = 5214689) B5214689
theorem B2059385 : Blo 1372005 2059385 := bstep (se 2 (by rfl) ⟨772269, by rfl⟩ : syracuseStep 2059385 = 1544539) B1544539
theorem B4631687 : Blo 1372005 4631687 := bstep (se 1 (by rfl) ⟨3473765, by rfl⟩ : syracuseStep 4631687 = 6947531) B6947531
theorem B2059487 : Blo 1372005 2059487 := bstep (se 1 (by rfl) ⟨1544615, by rfl⟩ : syracuseStep 2059487 = 3089231) B3089231
theorem B4893929 : Blo 1372005 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B4631795 : Blo 1372005 4631795 := bstep (se 1 (by rfl) ⟨3473846, by rfl⟩ : syracuseStep 4631795 = 6947693) B6947693
theorem B2059529 : Blo 1372005 2059529 := bstep (se 2 (by rfl) ⟨772323, by rfl⟩ : syracuseStep 2059529 = 1544647) B1544647
theorem B18328843 : Blo 1372005 18328843 := bstep (se 1 (by rfl) ⟨13746632, by rfl⟩ : syracuseStep 18328843 = 27493265) B27493265
theorem B2059631 : Blo 1372005 2059631 := bstep (se 1 (by rfl) ⟨1544723, by rfl⟩ : syracuseStep 2059631 = 3089447) B3089447
theorem B15650171 : Blo 1372005 15650171 := bstep (se 1 (by rfl) ⟨11737628, by rfl⟩ : syracuseStep 15650171 = 23475257) B23475257
theorem B2059751 : Blo 1372005 2059751 := bstep (se 1 (by rfl) ⟨1544813, by rfl⟩ : syracuseStep 2059751 = 3089627) B3089627
theorem B9399833 : Blo 1372005 9399833 := bstep (se 2 (by rfl) ⟨3524937, by rfl⟩ : syracuseStep 9399833 = 7049875) B7049875
theorem B2059883 : Blo 1372005 2059883 := bstep (se 1 (by rfl) ⟨1544912, by rfl⟩ : syracuseStep 2059883 = 3089825) B3089825
theorem B30510701 : Blo 1372005 30510701 := bstep (se 3 (by rfl) ⟨5720756, by rfl⟩ : syracuseStep 30510701 = 11441513) B11441513
theorem B2060009 : Blo 1372005 2060009 := bstep (se 2 (by rfl) ⟨772503, by rfl⟩ : syracuseStep 2060009 = 1545007) B1545007
theorem B2060153 : Blo 1372005 2060153 := bstep (se 2 (by rfl) ⟨772557, by rfl⟩ : syracuseStep 2060153 = 1545115) B1545115
theorem B1372127 : Blo 1372005 1372127 := bstep (se 1 (by rfl) ⟨1029095, by rfl⟩ : syracuseStep 1372127 = 2058191) B2058191
theorem B2060255 : Blo 1372005 2060255 := bstep (se 1 (by rfl) ⟨1545191, by rfl⟩ : syracuseStep 2060255 = 3090383) B3090383
theorem B2060507 : Blo 1372005 2060507 := bstep (se 1 (by rfl) ⟨1545380, by rfl⟩ : syracuseStep 2060507 = 3090761) B3090761
theorem B1372391 : Blo 1372005 1372391 := bstep (se 1 (by rfl) ⟨1029293, by rfl⟩ : syracuseStep 1372391 = 2058587) B2058587
theorem B2060519 : Blo 1372005 2060519 := bstep (se 1 (by rfl) ⟨1545389, by rfl⟩ : syracuseStep 2060519 = 3090779) B3090779
theorem B15642881 : Blo 1372005 15642881 := bstep (se 2 (by rfl) ⟨5866080, by rfl⟩ : syracuseStep 15642881 = 11732161) B11732161
theorem B57151817 : Blo 1372005 57151817 := bstep (se 2 (by rfl) ⟨21431931, by rfl⟩ : syracuseStep 57151817 = 42863863) B42863863
theorem B1372543 : Blo 1372005 1372543 := bstep (se 1 (by rfl) ⟨1029407, by rfl⟩ : syracuseStep 1372543 = 2058815) B2058815
theorem B1544575 : Blo 1372005 1544575 := bstep (se 1 (by rfl) ⟨1158431, by rfl⟩ : syracuseStep 1544575 = 2316863) B2316863
theorem B2199935 : Blo 1372005 2199935 := bstep (se 1 (by rfl) ⟨1649951, by rfl⟩ : syracuseStep 2199935 = 3299903) B3299903
theorem B3477887 : Blo 1372005 3477887 := bstep (se 1 (by rfl) ⟨2608415, by rfl⟩ : syracuseStep 3477887 = 5216831) B5216831
theorem B2060681 : Blo 1372005 2060681 := bstep (se 2 (by rfl) ⟨772755, by rfl⟩ : syracuseStep 2060681 = 1545511) B1545511
theorem B1372623 : Blo 1372005 1372623 := bstep (se 1 (by rfl) ⟨1029467, by rfl⟩ : syracuseStep 1372623 = 2058935) B2058935
theorem B2060777 : Blo 1372005 2060777 := bstep (se 2 (by rfl) ⟨772791, by rfl⟩ : syracuseStep 2060777 = 1545583) B1545583
theorem B7819847 : Blo 1372005 7819847 := bstep (se 1 (by rfl) ⟨5864885, by rfl⟩ : syracuseStep 7819847 = 11729771) B11729771
theorem B9892439 : Blo 1372005 9892439 := bstep (se 1 (by rfl) ⟨7419329, by rfl⟩ : syracuseStep 9892439 = 14838659) B14838659
theorem B1372775 : Blo 1372005 1372775 := bstep (se 1 (by rfl) ⟨1029581, by rfl⟩ : syracuseStep 1372775 = 2059163) B2059163
theorem B2060903 : Blo 1372005 2060903 := bstep (se 1 (by rfl) ⟨1545677, by rfl⟩ : syracuseStep 2060903 = 3091355) B3091355
theorem B1373039 : Blo 1372005 1373039 := bstep (se 1 (by rfl) ⟨1029779, by rfl⟩ : syracuseStep 1373039 = 2059559) B2059559
theorem B4633469 : Blo 1372005 4633469 := bstep (se 3 (by rfl) ⟨868775, by rfl⟩ : syracuseStep 4633469 = 1737551) B1737551
theorem B1373095 : Blo 1372005 1373095 := bstep (se 1 (by rfl) ⟨1029821, by rfl⟩ : syracuseStep 1373095 = 2059643) B2059643
theorem B1373179 : Blo 1372005 1373179 := bstep (se 1 (by rfl) ⟨1029884, by rfl⟩ : syracuseStep 1373179 = 2059769) B2059769
theorem B1373247 : Blo 1372005 1373247 := bstep (se 1 (by rfl) ⟨1029935, by rfl⟩ : syracuseStep 1373247 = 2059871) B2059871
theorem B2315371 : Blo 1372005 2315371 := bstep (se 1 (by rfl) ⟨1736528, by rfl⟩ : syracuseStep 2315371 = 3473057) B3473057
theorem B4633739 : Blo 1372005 4633739 := bstep (se 1 (by rfl) ⟨3475304, by rfl⟩ : syracuseStep 4633739 = 6950609) B6950609
theorem B2348207 : Blo 1372005 2348207 := bstep (se 1 (by rfl) ⟨1761155, by rfl⟩ : syracuseStep 2348207 = 3522311) B3522311
theorem B1373391 : Blo 1372005 1373391 := bstep (se 1 (by rfl) ⟨1030043, by rfl⟩ : syracuseStep 1373391 = 2060087) B2060087
theorem B2315675 : Blo 1372005 2315675 := bstep (se 1 (by rfl) ⟨1736756, by rfl⟩ : syracuseStep 2315675 = 3473513) B3473513
theorem B1373595 : Blo 1372005 1373595 := bstep (se 1 (by rfl) ⟨1030196, by rfl⟩ : syracuseStep 1373595 = 2060393) B2060393
theorem B4699579 : Blo 1372005 4699579 := bstep (se 1 (by rfl) ⟨3524684, by rfl⟩ : syracuseStep 4699579 = 7049369) B7049369
theorem B50083393 : Blo 1372005 50083393 := bstep (se 2 (by rfl) ⟨18781272, by rfl⟩ : syracuseStep 50083393 = 37562545) B37562545
theorem B1373807 : Blo 1372005 1373807 := bstep (se 1 (by rfl) ⟨1030355, by rfl⟩ : syracuseStep 1373807 = 2060711) B2060711
theorem B1373863 : Blo 1372005 1373863 := bstep (se 1 (by rfl) ⟨1030397, by rfl⟩ : syracuseStep 1373863 = 2060795) B2060795
theorem B2315999 : Blo 1372005 2315999 := bstep (se 1 (by rfl) ⟨1736999, by rfl⟩ : syracuseStep 2315999 = 3473999) B3473999
theorem B1373947 : Blo 1372005 1373947 := bstep (se 1 (by rfl) ⟨1030460, by rfl⟩ : syracuseStep 1373947 = 2060921) B2060921
theorem B6952715 : Blo 1372005 6952715 := bstep (se 1 (by rfl) ⟨5214536, by rfl⟩ : syracuseStep 6952715 = 10429073) B10429073
theorem B1373983 : Blo 1372005 1373983 := bstep (se 1 (by rfl) ⟨1030487, by rfl⟩ : syracuseStep 1373983 = 2060975) B2060975
theorem B3299287 : Blo 1372005 3299287 := bstep (se 1 (by rfl) ⟨2474465, by rfl⟩ : syracuseStep 3299287 = 4948931) B4948931
theorem B4175855 : Blo 1372005 4175855 := bstep (se 1 (by rfl) ⟨3131891, by rfl⟩ : syracuseStep 4175855 = 6263783) B6263783
theorem B8345729 : Blo 1372005 8345729 := bstep (se 2 (by rfl) ⟨3129648, by rfl⟩ : syracuseStep 8345729 = 6259297) B6259297
theorem B2316431 : Blo 1372005 2316431 := bstep (se 1 (by rfl) ⟨1737323, by rfl⟩ : syracuseStep 2316431 = 3474647) B3474647
theorem B14850209 : Blo 1372005 14850209 := bstep (se 2 (by rfl) ⟨5568828, by rfl⟩ : syracuseStep 14850209 = 11137657) B11137657
theorem B1980607 : Blo 1372005 1980607 := bstep (se 1 (by rfl) ⟨1485455, by rfl⟩ : syracuseStep 1980607 = 2970911) B2970911
theorem B6691019 : Blo 1372005 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B4397435 : Blo 1372005 4397435 := bstep (se 1 (by rfl) ⟨3298076, by rfl⟩ : syracuseStep 4397435 = 6596153) B6596153
theorem B2316667 : Blo 1372005 2316667 := bstep (se 1 (by rfl) ⟨1737500, by rfl⟩ : syracuseStep 2316667 = 3475001) B3475001
theorem B2316937 : Blo 1372005 2316937 := bstep (se 2 (by rfl) ⟨868851, by rfl⟩ : syracuseStep 2316937 = 1737703) B1737703
theorem B4635359 : Blo 1372005 4635359 := bstep (se 1 (by rfl) ⟨3476519, by rfl⟩ : syracuseStep 4635359 = 6953039) B6953039
theorem B3087431 : Blo 1372005 3087431 := bstep (se 1 (by rfl) ⟨2315573, by rfl⟩ : syracuseStep 3087431 = 4631147) B4631147
theorem B9395453 : Blo 1372005 9395453 := bstep (se 3 (by rfl) ⟨1761647, by rfl⟩ : syracuseStep 9395453 = 3523295) B3523295
theorem B5209373 : Blo 1372005 5209373 := bstep (se 3 (by rfl) ⟨976757, by rfl⟩ : syracuseStep 5209373 = 1953515) B1953515
theorem B6954335 : Blo 1372005 6954335 := bstep (se 1 (by rfl) ⟨5215751, by rfl⟩ : syracuseStep 6954335 = 10431503) B10431503
theorem B9903455 : Blo 1372005 9903455 := bstep (se 1 (by rfl) ⟨7427591, by rfl⟩ : syracuseStep 9903455 = 14855183) B14855183
theorem B17833355 : Blo 1372005 17833355 := bstep (se 1 (by rfl) ⟨13375016, by rfl⟩ : syracuseStep 17833355 = 26750033) B26750033
theorem B10575307 : Blo 1372005 10575307 := bstep (se 1 (by rfl) ⟨7931480, by rfl⟩ : syracuseStep 10575307 = 15862961) B15862961
theorem B5209555 : Blo 1372005 5209555 := bstep (se 1 (by rfl) ⟨3907166, by rfl⟩ : syracuseStep 5209555 = 7814333) B7814333
theorem B3087827 : Blo 1372005 3087827 := bstep (se 1 (by rfl) ⟨2315870, by rfl⟩ : syracuseStep 3087827 = 4631741) B4631741
theorem B2473427 : Blo 1372005 2473427 := bstep (se 1 (by rfl) ⟨1855070, by rfl⟩ : syracuseStep 2473427 = 3710141) B3710141
theorem B4636115 : Blo 1372005 4636115 := bstep (se 1 (by rfl) ⟨3477086, by rfl⟩ : syracuseStep 4636115 = 6954173) B6954173
theorem B10165769 : Blo 1372005 10165769 := bstep (se 2 (by rfl) ⟨3812163, by rfl⟩ : syracuseStep 10165769 = 7624327) B7624327
theorem B13196837 : Blo 1372005 13196837 := bstep (se 4 (by rfl) ⟨1237203, by rfl⟩ : syracuseStep 13196837 = 2474407) B2474407
theorem B2088511 : Blo 1372005 2088511 := bstep (se 1 (by rfl) ⟨1566383, by rfl⟩ : syracuseStep 2088511 = 3132767) B3132767
theorem B10174061 : Blo 1372005 10174061 := bstep (se 3 (by rfl) ⟨1907636, by rfl⟩ : syracuseStep 10174061 = 3815273) B3815273
theorem B3088097 : Blo 1372005 3088097 := bstep (se 2 (by rfl) ⟨1158036, by rfl⟩ : syracuseStep 3088097 = 2316073) B2316073
theorem B7421665 : Blo 1372005 7421665 := bstep (se 2 (by rfl) ⟨2783124, by rfl⟩ : syracuseStep 7421665 = 5566249) B5566249
theorem B4636385 : Blo 1372005 4636385 := bstep (se 2 (by rfl) ⟨1738644, by rfl⟩ : syracuseStep 4636385 = 3477289) B3477289
theorem B63364999 : Blo 1372005 63364999 := bstep (se 1 (by rfl) ⟨47523749, by rfl⟩ : syracuseStep 63364999 = 95047499) B95047499
theorem B5210027 : Blo 1372005 5210027 := bstep (se 1 (by rfl) ⟨3907520, by rfl⟩ : syracuseStep 5210027 = 7815041) B7815041
theorem B10428587 : Blo 1372005 10428587 := bstep (se 1 (by rfl) ⟨7821440, by rfl⟩ : syracuseStep 10428587 = 15642881) B15642881
theorem B38101211 : Blo 1372005 38101211 := bstep (se 1 (by rfl) ⟨28575908, by rfl⟩ : syracuseStep 38101211 = 57151817) B57151817
theorem B4636925 : Blo 1372005 4636925 := bstep (se 3 (by rfl) ⟨869423, by rfl⟩ : syracuseStep 4636925 = 1738847) B1738847
theorem B1466623 : Blo 1372005 1466623 := bstep (se 1 (by rfl) ⟨1099967, by rfl⟩ : syracuseStep 1466623 = 2199935) B2199935
theorem B2318591 : Blo 1372005 2318591 := bstep (se 1 (by rfl) ⟨1738943, by rfl⟩ : syracuseStep 2318591 = 3477887) B3477887
theorem B22569289 : Blo 1372005 22569289 := bstep (se 2 (by rfl) ⟨8463483, by rfl⟩ : syracuseStep 22569289 = 16926967) B16926967
theorem B2605439 : Blo 1372005 2605439 := bstep (se 1 (by rfl) ⟨1954079, by rfl⟩ : syracuseStep 2605439 = 3908159) B3908159
theorem B6594959 : Blo 1372005 6594959 := bstep (se 1 (by rfl) ⟨4946219, by rfl⟩ : syracuseStep 6594959 = 9892439) B9892439
theorem B6259187 : Blo 1372005 6259187 := bstep (se 1 (by rfl) ⟨4694390, by rfl⟩ : syracuseStep 6259187 = 9388781) B9388781
theorem B3088889 : Blo 1372005 3088889 := bstep (se 2 (by rfl) ⟨1158333, by rfl⟩ : syracuseStep 3088889 = 2316667) B2316667
theorem B17842717 : Blo 1372005 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B3088979 : Blo 1372005 3088979 := bstep (se 1 (by rfl) ⟨2316734, by rfl⟩ : syracuseStep 3088979 = 4633469) B4633469
theorem B3089159 : Blo 1372005 3089159 := bstep (se 1 (by rfl) ⟨2316869, by rfl⟩ : syracuseStep 3089159 = 4633739) B4633739
theorem B1565471 : Blo 1372005 1565471 := bstep (se 1 (by rfl) ⟨1174103, by rfl⟩ : syracuseStep 1565471 = 2348207) B2348207
theorem B3089249 : Blo 1372005 3089249 := bstep (se 2 (by rfl) ⟨1158468, by rfl⟩ : syracuseStep 3089249 = 2316937) B2316937
theorem B2606023 : Blo 1372005 2606023 := bstep (se 1 (by rfl) ⟨1954517, by rfl⟩ : syracuseStep 2606023 = 3909035) B3909035
theorem B5948471 : Blo 1372005 5948471 := bstep (se 1 (by rfl) ⟨4461353, by rfl⟩ : syracuseStep 5948471 = 8922707) B8922707
theorem B6595805 : Blo 1372005 6595805 := bstep (se 3 (by rfl) ⟨1236713, by rfl⟩ : syracuseStep 6595805 = 2473427) B2473427
theorem B5563819 : Blo 1372005 5563819 := bstep (se 1 (by rfl) ⟨4172864, by rfl⟩ : syracuseStep 5563819 = 8345729) B8345729
theorem B10421783 : Blo 1372005 10421783 := bstep (se 1 (by rfl) ⟨7816337, by rfl⟩ : syracuseStep 10421783 = 15632675) B15632675
theorem B24438457 : Blo 1372005 24438457 := bstep (se 2 (by rfl) ⟨9164421, by rfl⟩ : syracuseStep 24438457 = 18328843) B18328843
theorem B14845751 : Blo 1372005 14845751 := bstep (se 1 (by rfl) ⟨11134313, by rfl⟩ : syracuseStep 14845751 = 22268627) B22268627
theorem B3090239 : Blo 1372005 3090239 := bstep (se 1 (by rfl) ⟨2317679, by rfl⟩ : syracuseStep 3090239 = 4635359) B4635359
theorem B14100409 : Blo 1372005 14100409 := bstep (se 2 (by rfl) ⟨5287653, by rfl⟩ : syracuseStep 14100409 = 10575307) B10575307
theorem B2607079 : Blo 1372005 2607079 := bstep (se 1 (by rfl) ⟨1955309, by rfl⟩ : syracuseStep 2607079 = 3910619) B3910619
theorem B2058287 : Blo 1372005 2058287 := bstep (se 1 (by rfl) ⟨1543715, by rfl⟩ : syracuseStep 2058287 = 3087431) B3087431
theorem B6948989 : Blo 1372005 6948989 := bstep (se 3 (by rfl) ⟨1302935, by rfl⟩ : syracuseStep 6948989 = 2605871) B2605871
theorem B3262619 : Blo 1372005 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B11888903 : Blo 1372005 11888903 := bstep (se 1 (by rfl) ⟨8916677, by rfl⟩ : syracuseStep 11888903 = 17833355) B17833355
theorem B5212457 : Blo 1372005 5212457 := bstep (se 2 (by rfl) ⟨1954671, by rfl⟩ : syracuseStep 5212457 = 3909343) B3909343
theorem B2058551 : Blo 1372005 2058551 := bstep (se 1 (by rfl) ⟨1543913, by rfl⟩ : syracuseStep 2058551 = 3087827) B3087827
theorem B3090743 : Blo 1372005 3090743 := bstep (se 1 (by rfl) ⟨2318057, by rfl⟩ : syracuseStep 3090743 = 4636115) B4636115
theorem B6777179 : Blo 1372005 6777179 := bstep (se 1 (by rfl) ⟨5082884, by rfl⟩ : syracuseStep 6777179 = 10165769) B10165769
theorem B2058731 : Blo 1372005 2058731 := bstep (se 1 (by rfl) ⟨1544048, by rfl⟩ : syracuseStep 2058731 = 3088097) B3088097
theorem B3090923 : Blo 1372005 3090923 := bstep (se 1 (by rfl) ⟨2318192, by rfl⟩ : syracuseStep 3090923 = 4636385) B4636385
theorem B84486665 : Blo 1372005 84486665 := bstep (se 2 (by rfl) ⟨31682499, by rfl⟩ : syracuseStep 84486665 = 63364999) B63364999
theorem B2640809 : Blo 1372005 2640809 := bstep (se 2 (by rfl) ⟨990303, by rfl⟩ : syracuseStep 2640809 = 1980607) B1980607
theorem B5213231 : Blo 1372005 5213231 := bstep (se 1 (by rfl) ⟨3909923, by rfl⟩ : syracuseStep 5213231 = 7819847) B7819847
theorem B2059433 : Blo 1372005 2059433 := bstep (se 2 (by rfl) ⟨772287, by rfl⟩ : syracuseStep 2059433 = 1544575) B1544575
theorem B1650143 : Blo 1372005 1650143 := bstep (se 1 (by rfl) ⟨1237607, by rfl⟩ : syracuseStep 1650143 = 2475215) B2475215
theorem B4632065 : Blo 1372005 4632065 := bstep (se 2 (by rfl) ⟨1737024, by rfl⟩ : syracuseStep 4632065 = 3474049) B3474049
theorem B2059847 : Blo 1372005 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B1543783 : Blo 1372005 1543783 := bstep (se 1 (by rfl) ⟨1157837, by rfl⟩ : syracuseStep 1543783 = 2315675) B2315675
theorem B2060027 : Blo 1372005 2060027 := bstep (se 1 (by rfl) ⟨1545020, by rfl⟩ : syracuseStep 2060027 = 3090041) B3090041
theorem B12693307 : Blo 1372005 12693307 := bstep (se 1 (by rfl) ⟨9519980, by rfl⟩ : syracuseStep 12693307 = 19039961) B19039961
theorem B1543999 : Blo 1372005 1543999 := bstep (se 1 (by rfl) ⟨1157999, by rfl⟩ : syracuseStep 1543999 = 2315999) B2315999
theorem B25046891 : Blo 1372005 25046891 := bstep (se 1 (by rfl) ⟨18785168, by rfl⟩ : syracuseStep 25046891 = 37570337) B37570337
theorem B1372031 : Blo 1372005 1372031 := bstep (se 1 (by rfl) ⟨1029023, by rfl⟩ : syracuseStep 1372031 = 2058047) B2058047
theorem B1372143 : Blo 1372005 1372143 := bstep (se 1 (by rfl) ⟨1029107, by rfl⟩ : syracuseStep 1372143 = 2058215) B2058215
theorem B1372155 : Blo 1372005 1372155 := bstep (se 1 (by rfl) ⟨1029116, by rfl⟩ : syracuseStep 1372155 = 2058233) B2058233
theorem B1372223 : Blo 1372005 1372223 := bstep (se 1 (by rfl) ⟨1029167, by rfl⟩ : syracuseStep 1372223 = 2058335) B2058335
theorem B1544287 : Blo 1372005 1544287 := bstep (se 1 (by rfl) ⟨1158215, by rfl⟩ : syracuseStep 1544287 = 2316431) B2316431
theorem B1372263 : Blo 1372005 1372263 := bstep (se 1 (by rfl) ⟨1029197, by rfl⟩ : syracuseStep 1372263 = 2058395) B2058395
theorem B9900139 : Blo 1372005 9900139 := bstep (se 1 (by rfl) ⟨7425104, by rfl⟩ : syracuseStep 9900139 = 14850209) B14850209
theorem B1372287 : Blo 1372005 1372287 := bstep (se 1 (by rfl) ⟨1029215, by rfl⟩ : syracuseStep 1372287 = 2058431) B2058431
theorem B1372315 : Blo 1372005 1372315 := bstep (se 1 (by rfl) ⟨1029236, by rfl⟩ : syracuseStep 1372315 = 2058473) B2058473
theorem B5861639 : Blo 1372005 5861639 := bstep (se 1 (by rfl) ⟨4396229, by rfl⟩ : syracuseStep 5861639 = 8792459) B8792459
theorem B4632875 : Blo 1372005 4632875 := bstep (se 1 (by rfl) ⟨3474656, by rfl⟩ : syracuseStep 4632875 = 6949313) B6949313
theorem B1372519 : Blo 1372005 1372519 := bstep (se 1 (by rfl) ⟨1029389, by rfl⟩ : syracuseStep 1372519 = 2058779) B2058779
theorem B1372571 : Blo 1372005 1372571 := bstep (se 1 (by rfl) ⟨1029428, by rfl⟩ : syracuseStep 1372571 = 2058857) B2058857
theorem B2060699 : Blo 1372005 2060699 := bstep (se 1 (by rfl) ⟨1545524, by rfl⟩ : syracuseStep 2060699 = 3091049) B3091049
theorem B4633145 : Blo 1372005 4633145 := bstep (se 2 (by rfl) ⟨1737429, by rfl⟩ : syracuseStep 4633145 = 3474859) B3474859
theorem B1372923 : Blo 1372005 1372923 := bstep (se 1 (by rfl) ⟨1029692, by rfl⟩ : syracuseStep 1372923 = 2059385) B2059385
theorem B66777857 : Blo 1372005 66777857 := bstep (se 2 (by rfl) ⟨25041696, by rfl⟩ : syracuseStep 66777857 = 50083393) B50083393
theorem B1372991 : Blo 1372005 1372991 := bstep (se 1 (by rfl) ⟨1029743, by rfl⟩ : syracuseStep 1372991 = 2059487) B2059487
theorem B6263635 : Blo 1372005 6263635 := bstep (se 1 (by rfl) ⟨4697726, by rfl⟩ : syracuseStep 6263635 = 9395453) B9395453
theorem B1373019 : Blo 1372005 1373019 := bstep (se 1 (by rfl) ⟨1029764, by rfl⟩ : syracuseStep 1373019 = 2059529) B2059529
theorem B8467337 : Blo 1372005 8467337 := bstep (se 2 (by rfl) ⟨3175251, by rfl⟩ : syracuseStep 8467337 = 6350503) B6350503
theorem B1373087 : Blo 1372005 1373087 := bstep (se 1 (by rfl) ⟨1029815, by rfl⟩ : syracuseStep 1373087 = 2059631) B2059631
theorem B10433447 : Blo 1372005 10433447 := bstep (se 1 (by rfl) ⟨7825085, by rfl⟩ : syracuseStep 10433447 = 15650171) B15650171
theorem B1373167 : Blo 1372005 1373167 := bstep (se 1 (by rfl) ⟨1029875, by rfl⟩ : syracuseStep 1373167 = 2059751) B2059751
theorem B1373255 : Blo 1372005 1373255 := bstep (se 1 (by rfl) ⟨1029941, by rfl⟩ : syracuseStep 1373255 = 2059883) B2059883
theorem B1373339 : Blo 1372005 1373339 := bstep (se 1 (by rfl) ⟨1030004, by rfl⟩ : syracuseStep 1373339 = 2060009) B2060009
theorem B1373435 : Blo 1372005 1373435 := bstep (se 1 (by rfl) ⟨1030076, by rfl⟩ : syracuseStep 1373435 = 2060153) B2060153
theorem B1373503 : Blo 1372005 1373503 := bstep (se 1 (by rfl) ⟨1030127, by rfl⟩ : syracuseStep 1373503 = 2060255) B2060255
theorem B2348399 : Blo 1372005 2348399 := bstep (se 1 (by rfl) ⟨1761299, by rfl⟩ : syracuseStep 2348399 = 3522599) B3522599
theorem B1373671 : Blo 1372005 1373671 := bstep (se 1 (by rfl) ⟨1030253, by rfl⟩ : syracuseStep 1373671 = 2060507) B2060507
theorem B1373679 : Blo 1372005 1373679 := bstep (se 1 (by rfl) ⟨1030259, by rfl⟩ : syracuseStep 1373679 = 2060519) B2060519
theorem B1373787 : Blo 1372005 1373787 := bstep (se 1 (by rfl) ⟨1030340, by rfl⟩ : syracuseStep 1373787 = 2060681) B2060681
theorem B1373851 : Blo 1372005 1373851 := bstep (se 1 (by rfl) ⟨1030388, by rfl⟩ : syracuseStep 1373851 = 2060777) B2060777
theorem B11138725 : Blo 1372005 11138725 := bstep (se 4 (by rfl) ⟨1044255, by rfl⟩ : syracuseStep 11138725 = 2088511) B2088511
theorem B1373935 : Blo 1372005 1373935 := bstep (se 1 (by rfl) ⟨1030451, by rfl⟩ : syracuseStep 1373935 = 2060903) B2060903
theorem B7821305 : Blo 1372005 7821305 := bstep (se 2 (by rfl) ⟨2932989, by rfl⟩ : syracuseStep 7821305 = 5865979) B5865979
theorem B4634873 : Blo 1372005 4634873 := bstep (se 2 (by rfl) ⟨1738077, by rfl⟩ : syracuseStep 4634873 = 3476155) B3476155
theorem B2316775 : Blo 1372005 2316775 := bstep (se 1 (by rfl) ⟨1737581, by rfl⟩ : syracuseStep 2316775 = 3475163) B3475163
theorem B4635143 : Blo 1372005 4635143 := bstep (se 1 (by rfl) ⟨3476357, by rfl⟩ : syracuseStep 4635143 = 6952715) B6952715
theorem B2783903 : Blo 1372005 2783903 := bstep (se 1 (by rfl) ⟨2087927, by rfl⟩ : syracuseStep 2783903 = 4175855) B4175855
theorem B8346311 : Blo 1372005 8346311 := bstep (se 1 (by rfl) ⟨6259733, by rfl⟩ : syracuseStep 8346311 = 12519467) B12519467
theorem B3087161 : Blo 1372005 3087161 := bstep (se 2 (by rfl) ⟨1157685, by rfl⟩ : syracuseStep 3087161 = 2315371) B2315371
theorem B3087215 : Blo 1372005 3087215 := bstep (se 1 (by rfl) ⟨2315411, by rfl⟩ : syracuseStep 3087215 = 4630823) B4630823
theorem B2931623 : Blo 1372005 2931623 := bstep (se 1 (by rfl) ⟨2198717, by rfl⟩ : syracuseStep 2931623 = 4397435) B4397435
theorem B12213251 : Blo 1372005 12213251 := bstep (se 1 (by rfl) ⟨9159938, by rfl⟩ : syracuseStep 12213251 = 18319877) B18319877
theorem B60218437 : Blo 1372005 60218437 := bstep (se 4 (by rfl) ⟨5645478, by rfl⟩ : syracuseStep 60218437 = 11290957) B11290957
theorem B6266105 : Blo 1372005 6266105 := bstep (se 2 (by rfl) ⟨2349789, by rfl⟩ : syracuseStep 6266105 = 4699579) B4699579
theorem B168992011 : Blo 1372005 168992011 := bstep (se 1 (by rfl) ⟨126744008, by rfl⟩ : syracuseStep 168992011 = 253488017) B253488017
theorem B6946073 : Blo 1372005 6946073 := bstep (se 2 (by rfl) ⟨2604777, by rfl⟩ : syracuseStep 6946073 = 5209555) B5209555
theorem B2317639 : Blo 1372005 2317639 := bstep (se 1 (by rfl) ⟨1738229, by rfl⟩ : syracuseStep 2317639 = 3476459) B3476459
theorem B3087791 : Blo 1372005 3087791 := bstep (se 1 (by rfl) ⟨2315843, by rfl⟩ : syracuseStep 3087791 = 4631687) B4631687
theorem B2317801 : Blo 1372005 2317801 := bstep (se 2 (by rfl) ⟨869175, by rfl⟩ : syracuseStep 2317801 = 1738351) B1738351
theorem B3087863 : Blo 1372005 3087863 := bstep (se 1 (by rfl) ⟨2315897, by rfl⟩ : syracuseStep 3087863 = 4631795) B4631795
theorem B3472915 : Blo 1372005 3472915 := bstep (se 1 (by rfl) ⟨2604686, by rfl⟩ : syracuseStep 3472915 = 5209373) B5209373
theorem B4636223 : Blo 1372005 4636223 := bstep (se 1 (by rfl) ⟨3477167, by rfl⟩ : syracuseStep 4636223 = 6954335) B6954335
theorem B6602303 : Blo 1372005 6602303 := bstep (se 1 (by rfl) ⟨4951727, by rfl⟩ : syracuseStep 6602303 = 9903455) B9903455
theorem B9895553 : Blo 1372005 9895553 := bstep (se 2 (by rfl) ⟨3710832, by rfl⟩ : syracuseStep 9895553 = 7421665) B7421665
theorem B6266555 : Blo 1372005 6266555 := bstep (se 1 (by rfl) ⟨4699916, by rfl⟩ : syracuseStep 6266555 = 9399833) B9399833
theorem B8797891 : Blo 1372005 8797891 := bstep (se 1 (by rfl) ⟨6598418, by rfl⟩ : syracuseStep 8797891 = 13196837) B13196837
theorem B20340467 : Blo 1372005 20340467 := bstep (se 1 (by rfl) ⟨15255350, by rfl⟩ : syracuseStep 20340467 = 30510701) B30510701
theorem B6782707 : Blo 1372005 6782707 := bstep (se 1 (by rfl) ⟨5087030, by rfl⟩ : syracuseStep 6782707 = 10174061) B10174061
theorem B3473351 : Blo 1372005 3473351 := bstep (se 1 (by rfl) ⟨2605013, by rfl⟩ : syracuseStep 3473351 = 5210027) B5210027
theorem B4399049 : Blo 1372005 4399049 := bstep (se 2 (by rfl) ⟨1649643, by rfl⟩ : syracuseStep 4399049 = 3299287) B3299287
theorem B3907759 : Blo 1372005 3907759 := bstep (se 1 (by rfl) ⟨2930819, by rfl⟩ : syracuseStep 3907759 = 5861639) B5861639
theorem B3088583 : Blo 1372005 3088583 := bstep (se 1 (by rfl) ⟨2316437, by rfl⟩ : syracuseStep 3088583 = 4632875) B4632875
theorem B1736959 : Blo 1372005 1736959 := bstep (se 1 (by rfl) ⟨1302719, by rfl⟩ : syracuseStep 1736959 = 2605439) B2605439
theorem B3088763 : Blo 1372005 3088763 := bstep (se 1 (by rfl) ⟨2316572, by rfl⟩ : syracuseStep 3088763 = 4633145) B4633145
theorem B8700317 : Blo 1372005 8700317 := bstep (se 3 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 8700317 = 3262619) B3262619
theorem B5644891 : Blo 1372005 5644891 := bstep (se 1 (by rfl) ⟨4233668, by rfl⟩ : syracuseStep 5644891 = 8467337) B8467337
theorem B6955631 : Blo 1372005 6955631 := bstep (se 1 (by rfl) ⟨5216723, by rfl⟩ : syracuseStep 6955631 = 10433447) B10433447
theorem B3089033 : Blo 1372005 3089033 := bstep (se 2 (by rfl) ⟨1158387, by rfl⟩ : syracuseStep 3089033 = 2316775) B2316775
theorem B3965647 : Blo 1372005 3965647 := bstep (se 1 (by rfl) ⟨2974235, by rfl⟩ : syracuseStep 3965647 = 5948471) B5948471
theorem B23790289 : Blo 1372005 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B1565599 : Blo 1372005 1565599 := bstep (se 1 (by rfl) ⟨1174199, by rfl⟩ : syracuseStep 1565599 = 2348399) B2348399
theorem B6947855 : Blo 1372005 6947855 := bstep (se 1 (by rfl) ⟨5210891, by rfl⟩ : syracuseStep 6947855 = 10421783) B10421783
theorem B9897167 : Blo 1372005 9897167 := bstep (se 1 (by rfl) ⟨7422875, by rfl⟩ : syracuseStep 9897167 = 14845751) B14845751
theorem B4400381 : Blo 1372005 4400381 := bstep (se 3 (by rfl) ⟨825071, by rfl⟩ : syracuseStep 4400381 = 1650143) B1650143
theorem B3474697 : Blo 1372005 3474697 := bstep (se 2 (by rfl) ⟨1303011, by rfl⟩ : syracuseStep 3474697 = 2606023) B2606023
theorem B80291249 : Blo 1372005 80291249 := bstep (se 2 (by rfl) ⟨30109218, by rfl⟩ : syracuseStep 80291249 = 60218437) B60218437
theorem B3089915 : Blo 1372005 3089915 := bstep (se 1 (by rfl) ⟨2317436, by rfl⟩ : syracuseStep 3089915 = 4634873) B4634873
theorem B481478165 : Blo 1372005 481478165 := bstep (se 6 (by rfl) ⟨11284644, by rfl⟩ : syracuseStep 481478165 = 22569289) B22569289
theorem B3474971 : Blo 1372005 3474971 := bstep (se 1 (by rfl) ⟨2606228, by rfl⟩ : syracuseStep 3474971 = 5212457) B5212457
theorem B3090095 : Blo 1372005 3090095 := bstep (se 1 (by rfl) ⟨2317571, by rfl⟩ : syracuseStep 3090095 = 4635143) B4635143
theorem B225322681 : Blo 1372005 225322681 := bstep (se 2 (by rfl) ⟨84496005, by rfl⟩ : syracuseStep 225322681 = 168992011) B168992011
theorem B7423741 : Blo 1372005 7423741 := bstep (se 3 (by rfl) ⟨1391951, by rfl⟩ : syracuseStep 7423741 = 2783903) B2783903
theorem B3090185 : Blo 1372005 3090185 := bstep (se 2 (by rfl) ⟨1158819, by rfl⟩ : syracuseStep 3090185 = 2317639) B2317639
theorem B5564207 : Blo 1372005 5564207 := bstep (se 1 (by rfl) ⟨4173155, by rfl⟩ : syracuseStep 5564207 = 8346311) B8346311
theorem B2058107 : Blo 1372005 2058107 := bstep (se 1 (by rfl) ⟨1543580, by rfl⟩ : syracuseStep 2058107 = 3087161) B3087161
theorem B2058143 : Blo 1372005 2058143 := bstep (se 1 (by rfl) ⟨1543607, by rfl⟩ : syracuseStep 2058143 = 3087215) B3087215
theorem B3090401 : Blo 1372005 3090401 := bstep (se 2 (by rfl) ⟨1158900, by rfl⟩ : syracuseStep 3090401 = 2317801) B2317801
theorem B4630553 : Blo 1372005 4630553 := bstep (se 2 (by rfl) ⟨1736457, by rfl⟩ : syracuseStep 4630553 = 3472915) B3472915
theorem B3475487 : Blo 1372005 3475487 := bstep (se 1 (by rfl) ⟨2606615, by rfl⟩ : syracuseStep 3475487 = 5213231) B5213231
theorem B2058377 : Blo 1372005 2058377 := bstep (se 2 (by rfl) ⟨771891, by rfl⟩ : syracuseStep 2058377 = 1543783) B1543783
theorem B4630715 : Blo 1372005 4630715 := bstep (se 1 (by rfl) ⟨3473036, by rfl⟩ : syracuseStep 4630715 = 6946073) B6946073
theorem B2058527 : Blo 1372005 2058527 := bstep (se 1 (by rfl) ⟨1543895, by rfl⟩ : syracuseStep 2058527 = 3087791) B3087791
theorem B2058575 : Blo 1372005 2058575 := bstep (se 1 (by rfl) ⟨1543931, by rfl⟩ : syracuseStep 2058575 = 3087863) B3087863
theorem B3090815 : Blo 1372005 3090815 := bstep (se 1 (by rfl) ⟨2318111, by rfl⟩ : syracuseStep 3090815 = 4636223) B4636223
theorem B4401535 : Blo 1372005 4401535 := bstep (se 1 (by rfl) ⟨3301151, by rfl⟩ : syracuseStep 4401535 = 6602303) B6602303
theorem B2058665 : Blo 1372005 2058665 := bstep (se 2 (by rfl) ⟨771999, by rfl⟩ : syracuseStep 2058665 = 1543999) B1543999
theorem B6597035 : Blo 1372005 6597035 := bstep (se 1 (by rfl) ⟨4947776, by rfl⟩ : syracuseStep 6597035 = 9895553) B9895553
theorem B13560311 : Blo 1372005 13560311 := bstep (se 1 (by rfl) ⟨10170233, by rfl⟩ : syracuseStep 13560311 = 20340467) B20340467
theorem B16697927 : Blo 1372005 16697927 := bstep (se 1 (by rfl) ⟨12523445, by rfl⟩ : syracuseStep 16697927 = 25046891) B25046891
theorem B3476105 : Blo 1372005 3476105 := bstep (se 2 (by rfl) ⟨1303539, by rfl⟩ : syracuseStep 3476105 = 2607079) B2607079
theorem B2059049 : Blo 1372005 2059049 := bstep (se 2 (by rfl) ⟨772143, by rfl⟩ : syracuseStep 2059049 = 1544287) B1544287
theorem B13200185 : Blo 1372005 13200185 := bstep (se 2 (by rfl) ⟨4950069, by rfl⟩ : syracuseStep 13200185 = 9900139) B9900139
theorem B3091283 : Blo 1372005 3091283 := bstep (se 1 (by rfl) ⟨2318462, by rfl⟩ : syracuseStep 3091283 = 4636925) B4636925
theorem B4172791 : Blo 1372005 4172791 := bstep (se 1 (by rfl) ⟨3129593, by rfl⟩ : syracuseStep 4172791 = 6259187) B6259187
theorem B2059259 : Blo 1372005 2059259 := bstep (se 1 (by rfl) ⟨1544444, by rfl⟩ : syracuseStep 2059259 = 3088889) B3088889
theorem B2059319 : Blo 1372005 2059319 := bstep (se 1 (by rfl) ⟨1544489, by rfl⟩ : syracuseStep 2059319 = 3088979) B3088979
theorem B44518571 : Blo 1372005 44518571 := bstep (se 1 (by rfl) ⟨33388928, by rfl⟩ : syracuseStep 44518571 = 66777857) B66777857
theorem B2059439 : Blo 1372005 2059439 := bstep (se 1 (by rfl) ⟨1544579, by rfl⟩ : syracuseStep 2059439 = 3089159) B3089159
theorem B2059499 : Blo 1372005 2059499 := bstep (se 1 (by rfl) ⟨1544624, by rfl⟩ : syracuseStep 2059499 = 3089249) B3089249
theorem B8351513 : Blo 1372005 8351513 := bstep (se 2 (by rfl) ⟨3131817, by rfl⟩ : syracuseStep 8351513 = 6263635) B6263635
theorem B2060159 : Blo 1372005 2060159 := bstep (se 1 (by rfl) ⟨1545119, by rfl⟩ : syracuseStep 2060159 = 3090239) B3090239
theorem B5214203 : Blo 1372005 5214203 := bstep (se 1 (by rfl) ⟨3910652, by rfl⟩ : syracuseStep 5214203 = 7821305) B7821305
theorem B1372191 : Blo 1372005 1372191 := bstep (se 1 (by rfl) ⟨1029143, by rfl⟩ : syracuseStep 1372191 = 2058287) B2058287
theorem B4632659 : Blo 1372005 4632659 := bstep (se 1 (by rfl) ⟨3474494, by rfl⟩ : syracuseStep 4632659 = 6948989) B6948989
theorem B7925935 : Blo 1372005 7925935 := bstep (se 1 (by rfl) ⟨5944451, by rfl⟩ : syracuseStep 7925935 = 11888903) B11888903
theorem B1372367 : Blo 1372005 1372367 := bstep (se 1 (by rfl) ⟨1029275, by rfl⟩ : syracuseStep 1372367 = 2058551) B2058551
theorem B2060495 : Blo 1372005 2060495 := bstep (se 1 (by rfl) ⟨1545371, by rfl⟩ : syracuseStep 2060495 = 3090743) B3090743
theorem B4518119 : Blo 1372005 4518119 := bstep (se 1 (by rfl) ⟨3388589, by rfl⟩ : syracuseStep 4518119 = 6777179) B6777179
theorem B1372487 : Blo 1372005 1372487 := bstep (se 1 (by rfl) ⟨1029365, by rfl⟩ : syracuseStep 1372487 = 2058731) B2058731
theorem B2060615 : Blo 1372005 2060615 := bstep (se 1 (by rfl) ⟨1545461, by rfl⟩ : syracuseStep 2060615 = 3090923) B3090923
theorem B56324443 : Blo 1372005 56324443 := bstep (se 1 (by rfl) ⟨42243332, by rfl⟩ : syracuseStep 56324443 = 84486665) B84486665
theorem B7418425 : Blo 1372005 7418425 := bstep (se 2 (by rfl) ⟨2781909, by rfl⟩ : syracuseStep 7418425 = 5563819) B5563819
theorem B1954415 : Blo 1372005 1954415 := bstep (se 1 (by rfl) ⟨1465811, by rfl⟩ : syracuseStep 1954415 = 2931623) B2931623
theorem B4174589 : Blo 1372005 4174589 := bstep (se 3 (by rfl) ⟨782735, by rfl⟩ : syracuseStep 4174589 = 1565471) B1565471
theorem B1372955 : Blo 1372005 1372955 := bstep (se 1 (by rfl) ⟨1029716, by rfl⟩ : syracuseStep 1372955 = 2059433) B2059433
theorem B32584609 : Blo 1372005 32584609 := bstep (se 2 (by rfl) ⟨12219228, by rfl⟩ : syracuseStep 32584609 = 24438457) B24438457
theorem B1373231 : Blo 1372005 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B7042157 : Blo 1372005 7042157 := bstep (se 3 (by rfl) ⟨1320404, by rfl⟩ : syracuseStep 7042157 = 2640809) B2640809
theorem B1373351 : Blo 1372005 1373351 := bstep (se 1 (by rfl) ⟨1030013, by rfl⟩ : syracuseStep 1373351 = 2060027) B2060027
theorem B2315567 : Blo 1372005 2315567 := bstep (se 1 (by rfl) ⟨1736675, by rfl⟩ : syracuseStep 2315567 = 3473351) B3473351
theorem B6952391 : Blo 1372005 6952391 := bstep (se 1 (by rfl) ⟨5214293, by rfl⟩ : syracuseStep 6952391 = 10428587) B10428587
theorem B25400807 : Blo 1372005 25400807 := bstep (se 1 (by rfl) ⟨19050605, by rfl⟩ : syracuseStep 25400807 = 38101211) B38101211
theorem B1545727 : Blo 1372005 1545727 := bstep (se 1 (by rfl) ⟨1159295, by rfl⟩ : syracuseStep 1545727 = 2318591) B2318591
theorem B1373799 : Blo 1372005 1373799 := bstep (se 1 (by rfl) ⟨1030349, by rfl⟩ : syracuseStep 1373799 = 2060699) B2060699
theorem B1955497 : Blo 1372005 1955497 := bstep (se 2 (by rfl) ⟨733311, by rfl⟩ : syracuseStep 1955497 = 1466623) B1466623
theorem B4397203 : Blo 1372005 4397203 := bstep (se 1 (by rfl) ⟨3297902, by rfl⟩ : syracuseStep 4397203 = 6595805) B6595805
theorem B17586557 : Blo 1372005 17586557 := bstep (se 3 (by rfl) ⟨3297479, by rfl⟩ : syracuseStep 17586557 = 6594959) B6594959
theorem B36174437 : Blo 1372005 36174437 := bstep (se 4 (by rfl) ⟨3391353, by rfl⟩ : syracuseStep 36174437 = 6782707) B6782707
theorem B8142167 : Blo 1372005 8142167 := bstep (se 1 (by rfl) ⟨6106625, by rfl⟩ : syracuseStep 8142167 = 12213251) B12213251
theorem B4177403 : Blo 1372005 4177403 := bstep (se 1 (by rfl) ⟨3133052, by rfl⟩ : syracuseStep 4177403 = 6266105) B6266105
theorem B14851633 : Blo 1372005 14851633 := bstep (se 2 (by rfl) ⟨5569362, by rfl⟩ : syracuseStep 14851633 = 11138725) B11138725
theorem B11730521 : Blo 1372005 11730521 := bstep (se 2 (by rfl) ⟨4398945, by rfl⟩ : syracuseStep 11730521 = 8797891) B8797891
theorem B3088043 : Blo 1372005 3088043 := bstep (se 1 (by rfl) ⟨2316032, by rfl⟩ : syracuseStep 3088043 = 4632065) B4632065
theorem B16924409 : Blo 1372005 16924409 := bstep (se 2 (by rfl) ⟨6346653, by rfl⟩ : syracuseStep 16924409 = 12693307) B12693307
theorem B4177703 : Blo 1372005 4177703 := bstep (se 1 (by rfl) ⟨3133277, by rfl⟩ : syracuseStep 4177703 = 6266555) B6266555
theorem B18800545 : Blo 1372005 18800545 := bstep (se 2 (by rfl) ⟨7050204, by rfl⟩ : syracuseStep 18800545 = 14100409) B14100409
theorem B2932699 : Blo 1372005 2932699 := bstep (se 1 (by rfl) ⟨2199524, by rfl⟩ : syracuseStep 2932699 = 4399049) B4399049
theorem B3088439 : Blo 1372005 3088439 := bstep (se 1 (by rfl) ⟨2316329, by rfl⟩ : syracuseStep 3088439 = 4632659) B4632659
theorem B5210345 : Blo 1372005 5210345 := bstep (se 2 (by rfl) ⟨1953879, by rfl⟩ : syracuseStep 5210345 = 3907759) B3907759
theorem B10567913 : Blo 1372005 10567913 := bstep (se 2 (by rfl) ⟨3962967, by rfl⟩ : syracuseStep 10567913 = 7925935) B7925935
theorem B5800211 : Blo 1372005 5800211 := bstep (se 1 (by rfl) ⟨4350158, by rfl⟩ : syracuseStep 5800211 = 8700317) B8700317
theorem B4637087 : Blo 1372005 4637087 := bstep (se 1 (by rfl) ⟨3477815, by rfl⟩ : syracuseStep 4637087 = 6955631) B6955631
theorem B4694771 : Blo 1372005 4694771 := bstep (se 1 (by rfl) ⟨3521078, by rfl⟩ : syracuseStep 4694771 = 7042157) B7042157
theorem B2933587 : Blo 1372005 2933587 := bstep (se 1 (by rfl) ⟨2200190, by rfl⟩ : syracuseStep 2933587 = 4400381) B4400381
theorem B31720385 : Blo 1372005 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B53527499 : Blo 1372005 53527499 := bstep (se 1 (by rfl) ⟨40145624, by rfl⟩ : syracuseStep 53527499 = 80291249) B80291249
theorem B16933871 : Blo 1372005 16933871 := bstep (se 1 (by rfl) ⟨12700403, by rfl⟩ : syracuseStep 16933871 = 25400807) B25400807
theorem B5563721 : Blo 1372005 5563721 := bstep (se 2 (by rfl) ⟨2086395, by rfl⟩ : syracuseStep 5563721 = 4172791) B4172791
theorem B11724371 : Blo 1372005 11724371 := bstep (se 1 (by rfl) ⟨8793278, by rfl⟩ : syracuseStep 11724371 = 17586557) B17586557
theorem B5211773 : Blo 1372005 5211773 := bstep (se 3 (by rfl) ⟨977207, by rfl⟩ : syracuseStep 5211773 = 1954415) B1954415
theorem B8800123 : Blo 1372005 8800123 := bstep (se 1 (by rfl) ⟨6600092, by rfl⟩ : syracuseStep 8800123 = 13200185) B13200185
theorem B19802177 : Blo 1372005 19802177 := bstep (se 2 (by rfl) ⟨7425816, by rfl⟩ : syracuseStep 19802177 = 14851633) B14851633
theorem B2607329 : Blo 1372005 2607329 := bstep (se 2 (by rfl) ⟨977748, by rfl⟩ : syracuseStep 2607329 = 1955497) B1955497
theorem B9898321 : Blo 1372005 9898321 := bstep (se 2 (by rfl) ⟨3711870, by rfl⟩ : syracuseStep 9898321 = 7423741) B7423741
theorem B2058695 : Blo 1372005 2058695 := bstep (se 1 (by rfl) ⟨1544021, by rfl⟩ : syracuseStep 2058695 = 3088043) B3088043
theorem B11282939 : Blo 1372005 11282939 := bstep (se 1 (by rfl) ⟨8462204, by rfl⟩ : syracuseStep 11282939 = 16924409) B16924409
theorem B3910265 : Blo 1372005 3910265 := bstep (se 2 (by rfl) ⟨1466349, by rfl⟩ : syracuseStep 3910265 = 2932699) B2932699
theorem B3476135 : Blo 1372005 3476135 := bstep (se 1 (by rfl) ⟨2607101, by rfl⟩ : syracuseStep 3476135 = 5214203) B5214203
theorem B2059055 : Blo 1372005 2059055 := bstep (se 1 (by rfl) ⟨1544291, by rfl⟩ : syracuseStep 2059055 = 3088583) B3088583
theorem B2059175 : Blo 1372005 2059175 := bstep (se 1 (by rfl) ⟨1544381, by rfl⟩ : syracuseStep 2059175 = 3088763) B3088763
theorem B2059355 : Blo 1372005 2059355 := bstep (se 1 (by rfl) ⟨1544516, by rfl⟩ : syracuseStep 2059355 = 3089033) B3089033
theorem B75099257 : Blo 1372005 75099257 := bstep (se 2 (by rfl) ⟨28162221, by rfl⟩ : syracuseStep 75099257 = 56324443) B56324443
theorem B5868713 : Blo 1372005 5868713 := bstep (se 2 (by rfl) ⟨2200767, by rfl⟩ : syracuseStep 5868713 = 4401535) B4401535
theorem B4631903 : Blo 1372005 4631903 := bstep (se 1 (by rfl) ⟨3473927, by rfl⟩ : syracuseStep 4631903 = 6947855) B6947855
theorem B9891233 : Blo 1372005 9891233 := bstep (se 2 (by rfl) ⟨3709212, by rfl⟩ : syracuseStep 9891233 = 7418425) B7418425
theorem B6598111 : Blo 1372005 6598111 := bstep (se 1 (by rfl) ⟨4948583, by rfl⟩ : syracuseStep 6598111 = 9897167) B9897167
theorem B1543711 : Blo 1372005 1543711 := bstep (se 1 (by rfl) ⟨1157783, by rfl⟩ : syracuseStep 1543711 = 2315567) B2315567
theorem B21712445 : Blo 1372005 21712445 := bstep (se 3 (by rfl) ⟨4071083, by rfl⟩ : syracuseStep 21712445 = 8142167) B8142167
theorem B5287529 : Blo 1372005 5287529 := bstep (se 2 (by rfl) ⟨1982823, by rfl⟩ : syracuseStep 5287529 = 3965647) B3965647
theorem B2059943 : Blo 1372005 2059943 := bstep (se 1 (by rfl) ⟨1544957, by rfl⟩ : syracuseStep 2059943 = 3089915) B3089915
theorem B2060063 : Blo 1372005 2060063 := bstep (se 1 (by rfl) ⟨1545047, by rfl⟩ : syracuseStep 2060063 = 3090095) B3090095
theorem B2060123 : Blo 1372005 2060123 := bstep (se 1 (by rfl) ⟨1545092, by rfl⟩ : syracuseStep 2060123 = 3090185) B3090185
theorem B43446145 : Blo 1372005 43446145 := bstep (se 2 (by rfl) ⟨16292304, by rfl⟩ : syracuseStep 43446145 = 32584609) B32584609
theorem B1372071 : Blo 1372005 1372071 := bstep (se 1 (by rfl) ⟨1029053, by rfl⟩ : syracuseStep 1372071 = 2058107) B2058107
theorem B1372095 : Blo 1372005 1372095 := bstep (se 1 (by rfl) ⟨1029071, by rfl⟩ : syracuseStep 1372095 = 2058143) B2058143
theorem B2060267 : Blo 1372005 2060267 := bstep (se 1 (by rfl) ⟨1545200, by rfl⟩ : syracuseStep 2060267 = 3090401) B3090401
theorem B1372251 : Blo 1372005 1372251 := bstep (se 1 (by rfl) ⟨1029188, by rfl⟩ : syracuseStep 1372251 = 2058377) B2058377
theorem B1372351 : Blo 1372005 1372351 := bstep (se 1 (by rfl) ⟨1029263, by rfl⟩ : syracuseStep 1372351 = 2058527) B2058527
theorem B1372383 : Blo 1372005 1372383 := bstep (se 1 (by rfl) ⟨1029287, by rfl⟩ : syracuseStep 1372383 = 2058575) B2058575
theorem B2060543 : Blo 1372005 2060543 := bstep (se 1 (by rfl) ⟨1545407, by rfl⟩ : syracuseStep 2060543 = 3090815) B3090815
theorem B1372443 : Blo 1372005 1372443 := bstep (se 1 (by rfl) ⟨1029332, by rfl⟩ : syracuseStep 1372443 = 2058665) B2058665
theorem B9040207 : Blo 1372005 9040207 := bstep (se 1 (by rfl) ⟨6780155, by rfl⟩ : syracuseStep 9040207 = 13560311) B13560311
theorem B4632929 : Blo 1372005 4632929 := bstep (se 2 (by rfl) ⟨1737348, by rfl⟩ : syracuseStep 4632929 = 3474697) B3474697
theorem B1372699 : Blo 1372005 1372699 := bstep (se 1 (by rfl) ⟨1029524, by rfl⟩ : syracuseStep 1372699 = 2059049) B2059049
theorem B2060855 : Blo 1372005 2060855 := bstep (se 1 (by rfl) ⟨1545641, by rfl⟩ : syracuseStep 2060855 = 3091283) B3091283
theorem B1372839 : Blo 1372005 1372839 := bstep (se 1 (by rfl) ⟨1029629, by rfl⟩ : syracuseStep 1372839 = 2059259) B2059259
theorem B2060969 : Blo 1372005 2060969 := bstep (se 2 (by rfl) ⟨772863, by rfl⟩ : syracuseStep 2060969 = 1545727) B1545727
theorem B1372879 : Blo 1372005 1372879 := bstep (se 1 (by rfl) ⟨1029659, by rfl⟩ : syracuseStep 1372879 = 2059319) B2059319
theorem B1372959 : Blo 1372005 1372959 := bstep (se 1 (by rfl) ⟨1029719, by rfl⟩ : syracuseStep 1372959 = 2059439) B2059439
theorem B1372999 : Blo 1372005 1372999 := bstep (se 1 (by rfl) ⟨1029749, by rfl⟩ : syracuseStep 1372999 = 2059499) B2059499
theorem B300430241 : Blo 1372005 300430241 := bstep (se 2 (by rfl) ⟨112661340, by rfl⟩ : syracuseStep 300430241 = 225322681) B225322681
theorem B7820347 : Blo 1372005 7820347 := bstep (se 1 (by rfl) ⟨5865260, by rfl⟩ : syracuseStep 7820347 = 11730521) B11730521
theorem B5567675 : Blo 1372005 5567675 := bstep (se 1 (by rfl) ⟨4175756, by rfl⟩ : syracuseStep 5567675 = 8351513) B8351513
theorem B1373439 : Blo 1372005 1373439 := bstep (se 1 (by rfl) ⟨1030079, by rfl⟩ : syracuseStep 1373439 = 2060159) B2060159
theorem B1373663 : Blo 1372005 1373663 := bstep (se 1 (by rfl) ⟨1030247, by rfl⟩ : syracuseStep 1373663 = 2060495) B2060495
theorem B3012079 : Blo 1372005 3012079 := bstep (se 1 (by rfl) ⟨2259059, by rfl⟩ : syracuseStep 3012079 = 4518119) B4518119
theorem B5862937 : Blo 1372005 5862937 := bstep (se 2 (by rfl) ⟨2198601, by rfl⟩ : syracuseStep 5862937 = 4397203) B4397203
theorem B1373743 : Blo 1372005 1373743 := bstep (se 1 (by rfl) ⟨1030307, by rfl⟩ : syracuseStep 1373743 = 2060615) B2060615
theorem B2315945 : Blo 1372005 2315945 := bstep (se 2 (by rfl) ⟨868479, by rfl⟩ : syracuseStep 2315945 = 1736959) B1736959
theorem B7526521 : Blo 1372005 7526521 := bstep (se 2 (by rfl) ⟨2822445, by rfl⟩ : syracuseStep 7526521 = 5644891) B5644891
theorem B4634927 : Blo 1372005 4634927 := bstep (se 1 (by rfl) ⟨3476195, by rfl⟩ : syracuseStep 4634927 = 6952391) B6952391
theorem B320985443 : Blo 1372005 320985443 := bstep (se 1 (by rfl) ⟨240739082, by rfl⟩ : syracuseStep 320985443 = 481478165) B481478165
theorem B2316647 : Blo 1372005 2316647 := bstep (se 1 (by rfl) ⟨1737485, by rfl⟩ : syracuseStep 2316647 = 3474971) B3474971
theorem B3709471 : Blo 1372005 3709471 := bstep (se 1 (by rfl) ⟨2782103, by rfl⟩ : syracuseStep 3709471 = 5564207) B5564207
theorem B2087465 : Blo 1372005 2087465 := bstep (se 2 (by rfl) ⟨782799, by rfl⟩ : syracuseStep 2087465 = 1565599) B1565599
theorem B3087035 : Blo 1372005 3087035 := bstep (se 1 (by rfl) ⟨2315276, by rfl⟩ : syracuseStep 3087035 = 4630553) B4630553
theorem B2316991 : Blo 1372005 2316991 := bstep (se 1 (by rfl) ⟨1737743, by rfl⟩ : syracuseStep 2316991 = 3475487) B3475487
theorem B3087143 : Blo 1372005 3087143 := bstep (se 1 (by rfl) ⟨2315357, by rfl⟩ : syracuseStep 3087143 = 4630715) B4630715
theorem B4398023 : Blo 1372005 4398023 := bstep (se 1 (by rfl) ⟨3298517, by rfl⟩ : syracuseStep 4398023 = 6597035) B6597035
theorem B11131951 : Blo 1372005 11131951 := bstep (se 1 (by rfl) ⟨8348963, by rfl⟩ : syracuseStep 11131951 = 16697927) B16697927
theorem B24116291 : Blo 1372005 24116291 := bstep (se 1 (by rfl) ⟨18087218, by rfl⟩ : syracuseStep 24116291 = 36174437) B36174437
theorem B2317403 : Blo 1372005 2317403 := bstep (se 1 (by rfl) ⟨1738052, by rfl⟩ : syracuseStep 2317403 = 3476105) B3476105
theorem B11132237 : Blo 1372005 11132237 := bstep (se 3 (by rfl) ⟨2087294, by rfl⟩ : syracuseStep 11132237 = 4174589) B4174589
theorem B11140541 : Blo 1372005 11140541 := bstep (se 3 (by rfl) ⟨2088851, by rfl⟩ : syracuseStep 11140541 = 4177703) B4177703
theorem B29679047 : Blo 1372005 29679047 := bstep (se 1 (by rfl) ⟨22259285, by rfl⟩ : syracuseStep 29679047 = 44518571) B44518571
theorem B2784935 : Blo 1372005 2784935 := bstep (se 1 (by rfl) ⟨2088701, by rfl⟩ : syracuseStep 2784935 = 4177403) B4177403
theorem B25067393 : Blo 1372005 25067393 := bstep (se 2 (by rfl) ⟨9400272, by rfl⟩ : syracuseStep 25067393 = 18800545) B18800545
theorem B3473563 : Blo 1372005 3473563 := bstep (se 1 (by rfl) ⟨2605172, by rfl⟩ : syracuseStep 3473563 = 5210345) B5210345
theorem B10035361 : Blo 1372005 10035361 := bstep (se 2 (by rfl) ⟨3763260, by rfl⟩ : syracuseStep 10035361 = 7526521) B7526521
theorem B3866807 : Blo 1372005 3866807 := bstep (se 1 (by rfl) ⟨2900105, by rfl⟩ : syracuseStep 3866807 = 5800211) B5800211
theorem B3088619 : Blo 1372005 3088619 := bstep (se 1 (by rfl) ⟨2316464, by rfl⟩ : syracuseStep 3088619 = 4632929) B4632929
theorem B13197761 : Blo 1372005 13197761 := bstep (se 2 (by rfl) ⟨4949160, by rfl⟩ : syracuseStep 13197761 = 9898321) B9898321
theorem B3129847 : Blo 1372005 3129847 := bstep (se 1 (by rfl) ⟨2347385, by rfl⟩ : syracuseStep 3129847 = 4694771) B4694771
theorem B200286827 : Blo 1372005 200286827 := bstep (se 1 (by rfl) ⟨150215120, by rfl⟩ : syracuseStep 200286827 = 300430241) B300430241
theorem B35684999 : Blo 1372005 35684999 := bstep (se 1 (by rfl) ⟨26763749, by rfl⟩ : syracuseStep 35684999 = 53527499) B53527499
theorem B3089321 : Blo 1372005 3089321 := bstep (se 2 (by rfl) ⟨1158495, by rfl⟩ : syracuseStep 3089321 = 2316991) B2316991
theorem B7816247 : Blo 1372005 7816247 := bstep (se 1 (by rfl) ⟨5862185, by rfl⟩ : syracuseStep 7816247 = 11724371) B11724371
theorem B3474515 : Blo 1372005 3474515 := bstep (se 1 (by rfl) ⟨2605886, by rfl⟩ : syracuseStep 3474515 = 5211773) B5211773
theorem B3089951 : Blo 1372005 3089951 := bstep (se 1 (by rfl) ⟨2317463, by rfl⟩ : syracuseStep 3089951 = 4634927) B4634927
theorem B14100077 : Blo 1372005 14100077 := bstep (se 3 (by rfl) ⟨2643764, by rfl⟩ : syracuseStep 14100077 = 5287529) B5287529
theorem B7521959 : Blo 1372005 7521959 := bstep (se 1 (by rfl) ⟨5641469, by rfl⟩ : syracuseStep 7521959 = 11282939) B11282939
theorem B2606843 : Blo 1372005 2606843 := bstep (se 1 (by rfl) ⟨1955132, by rfl⟩ : syracuseStep 2606843 = 3910265) B3910265
theorem B2058023 : Blo 1372005 2058023 := bstep (se 1 (by rfl) ⟨1543517, by rfl⟩ : syracuseStep 2058023 = 3087035) B3087035
theorem B2058095 : Blo 1372005 2058095 := bstep (se 1 (by rfl) ⟨1543571, by rfl⟩ : syracuseStep 2058095 = 3087143) B3087143
theorem B4016105 : Blo 1372005 4016105 := bstep (se 2 (by rfl) ⟨1506039, by rfl⟩ : syracuseStep 4016105 = 3012079) B3012079
theorem B7817249 : Blo 1372005 7817249 := bstep (se 2 (by rfl) ⟨2931468, by rfl⟩ : syracuseStep 7817249 = 5862937) B5862937
theorem B2058281 : Blo 1372005 2058281 := bstep (se 2 (by rfl) ⟨771855, by rfl⟩ : syracuseStep 2058281 = 1543711) B1543711
theorem B19786031 : Blo 1372005 19786031 := bstep (se 1 (by rfl) ⟨14839523, by rfl⟩ : syracuseStep 19786031 = 29679047) B29679047
theorem B112724405 : Blo 1372005 112724405 := bstep (se 5 (by rfl) ⟨5283956, by rfl⟩ : syracuseStep 112724405 = 10567913) B10567913
theorem B11733497 : Blo 1372005 11733497 := bstep (se 2 (by rfl) ⟨4400061, by rfl⟩ : syracuseStep 11733497 = 8800123) B8800123
theorem B57928193 : Blo 1372005 57928193 := bstep (se 2 (by rfl) ⟨21723072, by rfl⟩ : syracuseStep 57928193 = 43446145) B43446145
theorem B45156989 : Blo 1372005 45156989 := bstep (se 3 (by rfl) ⟨8466935, by rfl⟩ : syracuseStep 45156989 = 16933871) B16933871
theorem B2058959 : Blo 1372005 2058959 := bstep (se 1 (by rfl) ⟨1544219, by rfl⟩ : syracuseStep 2058959 = 3088439) B3088439
theorem B3091391 : Blo 1372005 3091391 := bstep (se 1 (by rfl) ⟨2318543, by rfl⟩ : syracuseStep 3091391 = 4637087) B4637087
theorem B12053609 : Blo 1372005 12053609 := bstep (se 2 (by rfl) ⟨4520103, by rfl⟩ : syracuseStep 12053609 = 9040207) B9040207
theorem B14847133 : Blo 1372005 14847133 := bstep (se 3 (by rfl) ⟨2783837, by rfl⟩ : syracuseStep 14847133 = 5567675) B5567675
theorem B21146923 : Blo 1372005 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B1543963 : Blo 1372005 1543963 := bstep (se 1 (by rfl) ⟨1157972, by rfl⟩ : syracuseStep 1543963 = 2315945) B2315945
theorem B13201451 : Blo 1372005 13201451 := bstep (se 1 (by rfl) ⟨9901088, by rfl⟩ : syracuseStep 13201451 = 19802177) B19802177
theorem B5566573 : Blo 1372005 5566573 := bstep (se 3 (by rfl) ⟨1043732, by rfl⟩ : syracuseStep 5566573 = 2087465) B2087465
theorem B1544431 : Blo 1372005 1544431 := bstep (se 1 (by rfl) ⟨1158323, by rfl⟩ : syracuseStep 1544431 = 2316647) B2316647
theorem B1372463 : Blo 1372005 1372463 := bstep (se 1 (by rfl) ⟨1029347, by rfl⟩ : syracuseStep 1372463 = 2058695) B2058695
theorem B1372703 : Blo 1372005 1372703 := bstep (se 1 (by rfl) ⟨1029527, by rfl⟩ : syracuseStep 1372703 = 2059055) B2059055
theorem B1372783 : Blo 1372005 1372783 := bstep (se 1 (by rfl) ⟨1029587, by rfl⟩ : syracuseStep 1372783 = 2059175) B2059175
theorem B16077527 : Blo 1372005 16077527 := bstep (se 1 (by rfl) ⟨12058145, by rfl⟩ : syracuseStep 16077527 = 24116291) B24116291
theorem B1372903 : Blo 1372005 1372903 := bstep (se 1 (by rfl) ⟨1029677, by rfl⟩ : syracuseStep 1372903 = 2059355) B2059355
theorem B1544935 : Blo 1372005 1544935 := bstep (se 1 (by rfl) ⟨1158701, by rfl⟩ : syracuseStep 1544935 = 2317403) B2317403
theorem B50066171 : Blo 1372005 50066171 := bstep (se 1 (by rfl) ⟨37549628, by rfl⟩ : syracuseStep 50066171 = 75099257) B75099257
theorem B3912475 : Blo 1372005 3912475 := bstep (se 1 (by rfl) ⟨2934356, by rfl⟩ : syracuseStep 3912475 = 5868713) B5868713
theorem B7427027 : Blo 1372005 7427027 := bstep (se 1 (by rfl) ⟨5570270, by rfl⟩ : syracuseStep 7427027 = 11140541) B11140541
theorem B1373295 : Blo 1372005 1373295 := bstep (se 1 (by rfl) ⟨1029971, by rfl⟩ : syracuseStep 1373295 = 2059943) B2059943
theorem B1856623 : Blo 1372005 1856623 := bstep (se 1 (by rfl) ⟨1392467, by rfl⟩ : syracuseStep 1856623 = 2784935) B2784935
theorem B11728061 : Blo 1372005 11728061 := bstep (se 3 (by rfl) ⟨2199011, by rfl⟩ : syracuseStep 11728061 = 4398023) B4398023
theorem B1373375 : Blo 1372005 1373375 := bstep (se 1 (by rfl) ⟨1030031, by rfl⟩ : syracuseStep 1373375 = 2060063) B2060063
theorem B1373415 : Blo 1372005 1373415 := bstep (se 1 (by rfl) ⟨1030061, by rfl⟩ : syracuseStep 1373415 = 2060123) B2060123
theorem B1373511 : Blo 1372005 1373511 := bstep (se 1 (by rfl) ⟨1030133, by rfl⟩ : syracuseStep 1373511 = 2060267) B2060267
theorem B1373695 : Blo 1372005 1373695 := bstep (se 1 (by rfl) ⟨1030271, by rfl⟩ : syracuseStep 1373695 = 2060543) B2060543
theorem B1373903 : Blo 1372005 1373903 := bstep (se 1 (by rfl) ⟨1030427, by rfl⟩ : syracuseStep 1373903 = 2060855) B2060855
theorem B1373979 : Blo 1372005 1373979 := bstep (se 1 (by rfl) ⟨1030484, by rfl⟩ : syracuseStep 1373979 = 2060969) B2060969
theorem B6952877 : Blo 1372005 6952877 := bstep (se 3 (by rfl) ⟨1303664, by rfl⟩ : syracuseStep 6952877 = 2607329) B2607329
theorem B4945961 : Blo 1372005 4945961 := bstep (se 2 (by rfl) ⟨1854735, by rfl⟩ : syracuseStep 4945961 = 3709471) B3709471
theorem B3709147 : Blo 1372005 3709147 := bstep (se 1 (by rfl) ⟨2781860, by rfl⟩ : syracuseStep 3709147 = 5563721) B5563721
theorem B14842601 : Blo 1372005 14842601 := bstep (se 2 (by rfl) ⟨5565975, by rfl⟩ : syracuseStep 14842601 = 11131951) B11131951
theorem B10427129 : Blo 1372005 10427129 := bstep (se 2 (by rfl) ⟨3910173, by rfl⟩ : syracuseStep 10427129 = 7820347) B7820347
theorem B213990295 : Blo 1372005 213990295 := bstep (se 1 (by rfl) ⟨160492721, by rfl⟩ : syracuseStep 213990295 = 320985443) B320985443
theorem B15645797 : Blo 1372005 15645797 := bstep (se 4 (by rfl) ⟨1466793, by rfl⟩ : syracuseStep 15645797 = 2933587) B2933587
theorem B2317423 : Blo 1372005 2317423 := bstep (se 1 (by rfl) ⟨1738067, by rfl⟩ : syracuseStep 2317423 = 3476135) B3476135
theorem B8797481 : Blo 1372005 8797481 := bstep (se 2 (by rfl) ⟨3299055, by rfl⟩ : syracuseStep 8797481 = 6598111) B6598111
theorem B7421491 : Blo 1372005 7421491 := bstep (se 1 (by rfl) ⟨5566118, by rfl⟩ : syracuseStep 7421491 = 11132237) B11132237
theorem B3087935 : Blo 1372005 3087935 := bstep (se 1 (by rfl) ⟨2315951, by rfl⟩ : syracuseStep 3087935 = 4631903) B4631903
theorem B6594155 : Blo 1372005 6594155 := bstep (se 1 (by rfl) ⟨4945616, by rfl⟩ : syracuseStep 6594155 = 9891233) B9891233
theorem B14474963 : Blo 1372005 14474963 := bstep (se 1 (by rfl) ⟨10856222, by rfl⟩ : syracuseStep 14474963 = 21712445) B21712445
theorem B16711595 : Blo 1372005 16711595 := bstep (se 1 (by rfl) ⟨12533696, by rfl⟩ : syracuseStep 16711595 = 25067393) B25067393
theorem B13189229 : Blo 1372005 13189229 := bstep (se 3 (by rfl) ⟨2472980, by rfl⟩ : syracuseStep 13189229 = 4945961) B4945961
theorem B8798507 : Blo 1372005 8798507 := bstep (se 1 (by rfl) ⟨6598880, by rfl⟩ : syracuseStep 8798507 = 13197761) B13197761
theorem B23789999 : Blo 1372005 23789999 := bstep (se 1 (by rfl) ⟨17842499, by rfl⟩ : syracuseStep 23789999 = 35684999) B35684999
theorem B29688389 : Blo 1372005 29688389 := bstep (se 4 (by rfl) ⟨2783286, by rfl⟩ : syracuseStep 29688389 = 5566573) B5566573
theorem B5210831 : Blo 1372005 5210831 := bstep (se 1 (by rfl) ⟨3908123, by rfl⟩ : syracuseStep 5210831 = 7816247) B7816247
theorem B5014639 : Blo 1372005 5014639 := bstep (se 1 (by rfl) ⟨3760979, by rfl⟩ : syracuseStep 5014639 = 7521959) B7521959
theorem B285320393 : Blo 1372005 285320393 := bstep (se 2 (by rfl) ⟨106995147, by rfl⟩ : syracuseStep 285320393 = 213990295) B213990295
theorem B5211499 : Blo 1372005 5211499 := bstep (se 1 (by rfl) ⟨3908624, by rfl⟩ : syracuseStep 5211499 = 7817249) B7817249
theorem B3089897 : Blo 1372005 3089897 := bstep (se 2 (by rfl) ⟨1158711, by rfl⟩ : syracuseStep 3089897 = 2317423) B2317423
theorem B2475497 : Blo 1372005 2475497 := bstep (se 2 (by rfl) ⟨928311, by rfl⟩ : syracuseStep 2475497 = 1856623) B1856623
theorem B13190687 : Blo 1372005 13190687 := bstep (se 1 (by rfl) ⟨9893015, by rfl⟩ : syracuseStep 13190687 = 19786031) B19786031
theorem B38618795 : Blo 1372005 38618795 := bstep (se 1 (by rfl) ⟨28964096, by rfl⟩ : syracuseStep 38618795 = 57928193) B57928193
theorem B10430531 : Blo 1372005 10430531 := bstep (se 1 (by rfl) ⟨7822898, by rfl⟩ : syracuseStep 10430531 = 15645797) B15645797
theorem B2058617 : Blo 1372005 2058617 := bstep (se 2 (by rfl) ⟨771981, by rfl⟩ : syracuseStep 2058617 = 1543963) B1543963
theorem B2058623 : Blo 1372005 2058623 := bstep (se 1 (by rfl) ⟨1543967, by rfl⟩ : syracuseStep 2058623 = 3087935) B3087935
theorem B8800967 : Blo 1372005 8800967 := bstep (se 1 (by rfl) ⟨6600725, by rfl⟩ : syracuseStep 8800967 = 13201451) B13201451
theorem B2059079 : Blo 1372005 2059079 := bstep (se 1 (by rfl) ⟨1544309, by rfl⟩ : syracuseStep 2059079 = 3088619) B3088619
theorem B4631417 : Blo 1372005 4631417 := bstep (se 2 (by rfl) ⟨1736781, by rfl⟩ : syracuseStep 4631417 = 3473563) B3473563
theorem B13380481 : Blo 1372005 13380481 := bstep (se 2 (by rfl) ⟨5017680, by rfl⟩ : syracuseStep 13380481 = 10035361) B10035361
theorem B2059241 : Blo 1372005 2059241 := bstep (se 2 (by rfl) ⟨772215, by rfl⟩ : syracuseStep 2059241 = 1544431) B1544431
theorem B133524551 : Blo 1372005 133524551 := bstep (se 1 (by rfl) ⟨100143413, by rfl⟩ : syracuseStep 133524551 = 200286827) B200286827
theorem B10718351 : Blo 1372005 10718351 := bstep (se 1 (by rfl) ⟨8038763, by rfl⟩ : syracuseStep 10718351 = 16077527) B16077527
theorem B33377447 : Blo 1372005 33377447 := bstep (se 1 (by rfl) ⟨25033085, by rfl⟩ : syracuseStep 33377447 = 50066171) B50066171
theorem B2059547 : Blo 1372005 2059547 := bstep (se 1 (by rfl) ⟨1544660, by rfl⟩ : syracuseStep 2059547 = 3089321) B3089321
theorem B4951351 : Blo 1372005 4951351 := bstep (se 1 (by rfl) ⟨3713513, by rfl⟩ : syracuseStep 4951351 = 7427027) B7427027
theorem B7818707 : Blo 1372005 7818707 := bstep (se 1 (by rfl) ⟨5864030, by rfl⟩ : syracuseStep 7818707 = 11728061) B11728061
theorem B2059913 : Blo 1372005 2059913 := bstep (se 2 (by rfl) ⟨772467, by rfl⟩ : syracuseStep 2059913 = 1544935) B1544935
theorem B2059967 : Blo 1372005 2059967 := bstep (se 1 (by rfl) ⟨1544975, by rfl⟩ : syracuseStep 2059967 = 3089951) B3089951
theorem B9400051 : Blo 1372005 9400051 := bstep (se 1 (by rfl) ⟨7050038, by rfl⟩ : syracuseStep 9400051 = 14100077) B14100077
theorem B1372015 : Blo 1372005 1372015 := bstep (se 1 (by rfl) ⟨1029011, by rfl⟩ : syracuseStep 1372015 = 2058023) B2058023
theorem B1372063 : Blo 1372005 1372063 := bstep (se 1 (by rfl) ⟨1029047, by rfl⟩ : syracuseStep 1372063 = 2058095) B2058095
theorem B1372187 : Blo 1372005 1372187 := bstep (se 1 (by rfl) ⟨1029140, by rfl⟩ : syracuseStep 1372187 = 2058281) B2058281
theorem B19796177 : Blo 1372005 19796177 := bstep (se 2 (by rfl) ⟨7423566, by rfl⟩ : syracuseStep 19796177 = 14847133) B14847133
theorem B112783589 : Blo 1372005 112783589 := bstep (se 4 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 112783589 = 21146923) B21146923
theorem B75149603 : Blo 1372005 75149603 := bstep (se 1 (by rfl) ⟨56362202, by rfl⟩ : syracuseStep 75149603 = 112724405) B112724405
theorem B1372639 : Blo 1372005 1372639 := bstep (se 1 (by rfl) ⟨1029479, by rfl⟩ : syracuseStep 1372639 = 2058959) B2058959
theorem B6951419 : Blo 1372005 6951419 := bstep (se 1 (by rfl) ⟨5213564, by rfl⟩ : syracuseStep 6951419 = 10427129) B10427129
theorem B2060927 : Blo 1372005 2060927 := bstep (se 1 (by rfl) ⟨1545695, by rfl⟩ : syracuseStep 2060927 = 3091391) B3091391
theorem B6951581 : Blo 1372005 6951581 := bstep (se 3 (by rfl) ⟨1303421, by rfl⟩ : syracuseStep 6951581 = 2606843) B2606843
theorem B4396103 : Blo 1372005 4396103 := bstep (se 1 (by rfl) ⟨3297077, by rfl⟩ : syracuseStep 4396103 = 6594155) B6594155
theorem B16692517 : Blo 1372005 16692517 := bstep (se 4 (by rfl) ⟨1564923, by rfl⟩ : syracuseStep 16692517 = 3129847) B3129847
theorem B2577871 : Blo 1372005 2577871 := bstep (se 1 (by rfl) ⟨1933403, by rfl⟩ : syracuseStep 2577871 = 3866807) B3866807
theorem B4945529 : Blo 1372005 4945529 := bstep (se 2 (by rfl) ⟨1854573, by rfl⟩ : syracuseStep 4945529 = 3709147) B3709147
theorem B2316343 : Blo 1372005 2316343 := bstep (se 1 (by rfl) ⟨1737257, by rfl⟩ : syracuseStep 2316343 = 3474515) B3474515
theorem B5216633 : Blo 1372005 5216633 := bstep (se 2 (by rfl) ⟨1956237, by rfl⟩ : syracuseStep 5216633 = 3912475) B3912475
theorem B4635251 : Blo 1372005 4635251 := bstep (se 1 (by rfl) ⟨3476438, by rfl⟩ : syracuseStep 4635251 = 6952877) B6952877
theorem B2677403 : Blo 1372005 2677403 := bstep (se 1 (by rfl) ⟨2008052, by rfl⟩ : syracuseStep 2677403 = 4016105) B4016105
theorem B7822331 : Blo 1372005 7822331 := bstep (se 1 (by rfl) ⟨5866748, by rfl⟩ : syracuseStep 7822331 = 11733497) B11733497
theorem B30104659 : Blo 1372005 30104659 := bstep (se 1 (by rfl) ⟨22578494, by rfl⟩ : syracuseStep 30104659 = 45156989) B45156989
theorem B9895067 : Blo 1372005 9895067 := bstep (se 1 (by rfl) ⟨7421300, by rfl⟩ : syracuseStep 9895067 = 14842601) B14842601
theorem B9895321 : Blo 1372005 9895321 := bstep (se 2 (by rfl) ⟨3710745, by rfl⟩ : syracuseStep 9895321 = 7421491) B7421491
theorem B8035739 : Blo 1372005 8035739 := bstep (se 1 (by rfl) ⟨6026804, by rfl⟩ : syracuseStep 8035739 = 12053609) B12053609
theorem B5864987 : Blo 1372005 5864987 := bstep (se 1 (by rfl) ⟨4398740, by rfl⟩ : syracuseStep 5864987 = 8797481) B8797481
theorem B9649975 : Blo 1372005 9649975 := bstep (se 1 (by rfl) ⟨7237481, by rfl⟩ : syracuseStep 9649975 = 14474963) B14474963
theorem B11141063 : Blo 1372005 11141063 := bstep (se 1 (by rfl) ⟨8355797, by rfl⟩ : syracuseStep 11141063 = 16711595) B16711595
theorem B3088457 : Blo 1372005 3088457 := bstep (se 2 (by rfl) ⟨1158171, by rfl⟩ : syracuseStep 3088457 = 2316343) B2316343
theorem B5865671 : Blo 1372005 5865671 := bstep (se 1 (by rfl) ⟨4399253, by rfl⟩ : syracuseStep 5865671 = 8798507) B8798507
theorem B15859999 : Blo 1372005 15859999 := bstep (se 1 (by rfl) ⟨11894999, by rfl⟩ : syracuseStep 15859999 = 23789999) B23789999
theorem B19792259 : Blo 1372005 19792259 := bstep (se 1 (by rfl) ⟨14844194, by rfl⟩ : syracuseStep 19792259 = 29688389) B29688389
theorem B89006525 : Blo 1372005 89006525 := bstep (se 3 (by rfl) ⟨16688723, by rfl⟩ : syracuseStep 89006525 = 33377447) B33377447
theorem B3473887 : Blo 1372005 3473887 := bstep (se 1 (by rfl) ⟨2605415, by rfl⟩ : syracuseStep 3473887 = 5210831) B5210831
theorem B52789805 : Blo 1372005 52789805 := bstep (se 3 (by rfl) ⟨9898088, by rfl⟩ : syracuseStep 52789805 = 19796177) B19796177
theorem B15639965 : Blo 1372005 15639965 := bstep (se 3 (by rfl) ⟨2932493, by rfl⟩ : syracuseStep 15639965 = 5864987) B5864987
theorem B3090167 : Blo 1372005 3090167 := bstep (se 1 (by rfl) ⟨2317625, by rfl⟩ : syracuseStep 3090167 = 4635251) B4635251
theorem B5867311 : Blo 1372005 5867311 := bstep (se 1 (by rfl) ⟨4400483, by rfl⟩ : syracuseStep 5867311 = 8800967) B8800967
theorem B6948665 : Blo 1372005 6948665 := bstep (se 2 (by rfl) ⟨2605749, by rfl⟩ : syracuseStep 6948665 = 5211499) B5211499
theorem B89016367 : Blo 1372005 89016367 := bstep (se 1 (by rfl) ⟨66762275, by rfl⟩ : syracuseStep 89016367 = 133524551) B133524551
theorem B7145567 : Blo 1372005 7145567 := bstep (se 1 (by rfl) ⟨5359175, by rfl⟩ : syracuseStep 7145567 = 10718351) B10718351
theorem B6596711 : Blo 1372005 6596711 := bstep (se 1 (by rfl) ⟨4947533, by rfl⟩ : syracuseStep 6596711 = 9895067) B9895067
theorem B5212471 : Blo 1372005 5212471 := bstep (se 1 (by rfl) ⟨3909353, by rfl⟩ : syracuseStep 5212471 = 7818707) B7818707
theorem B8792819 : Blo 1372005 8792819 := bstep (se 1 (by rfl) ⟨6594614, by rfl⟩ : syracuseStep 8792819 = 13189229) B13189229
theorem B75189059 : Blo 1372005 75189059 := bstep (se 1 (by rfl) ⟨56391794, by rfl⟩ : syracuseStep 75189059 = 112783589) B112783589
theorem B190213595 : Blo 1372005 190213595 := bstep (se 1 (by rfl) ⟨142660196, by rfl⟩ : syracuseStep 190213595 = 285320393) B285320393
theorem B2059931 : Blo 1372005 2059931 := bstep (se 1 (by rfl) ⟨1544948, by rfl⟩ : syracuseStep 2059931 = 3089897) B3089897
theorem B1650331 : Blo 1372005 1650331 := bstep (se 1 (by rfl) ⟨1237748, by rfl⟩ : syracuseStep 1650331 = 2475497) B2475497
theorem B8793791 : Blo 1372005 8793791 := bstep (se 1 (by rfl) ⟨6595343, by rfl⟩ : syracuseStep 8793791 = 13190687) B13190687
theorem B3297019 : Blo 1372005 3297019 := bstep (se 1 (by rfl) ⟨2472764, by rfl⟩ : syracuseStep 3297019 = 4945529) B4945529
theorem B1372411 : Blo 1372005 1372411 := bstep (se 1 (by rfl) ⟨1029308, by rfl⟩ : syracuseStep 1372411 = 2058617) B2058617
theorem B3477755 : Blo 1372005 3477755 := bstep (se 1 (by rfl) ⟨2608316, by rfl⟩ : syracuseStep 3477755 = 5216633) B5216633
theorem B1372415 : Blo 1372005 1372415 := bstep (se 1 (by rfl) ⟨1029311, by rfl⟩ : syracuseStep 1372415 = 2058623) B2058623
theorem B26407205 : Blo 1372005 26407205 := bstep (se 4 (by rfl) ⟨2475675, by rfl⟩ : syracuseStep 26407205 = 4951351) B4951351
theorem B13193761 : Blo 1372005 13193761 := bstep (se 2 (by rfl) ⟨4947660, by rfl⟩ : syracuseStep 13193761 = 9895321) B9895321
theorem B1372719 : Blo 1372005 1372719 := bstep (se 1 (by rfl) ⟨1029539, by rfl⟩ : syracuseStep 1372719 = 2059079) B2059079
theorem B3437161 : Blo 1372005 3437161 := bstep (se 2 (by rfl) ⟨1288935, by rfl⟩ : syracuseStep 3437161 = 2577871) B2577871
theorem B1372827 : Blo 1372005 1372827 := bstep (se 1 (by rfl) ⟨1029620, by rfl⟩ : syracuseStep 1372827 = 2059241) B2059241
theorem B5214887 : Blo 1372005 5214887 := bstep (se 1 (by rfl) ⟨3911165, by rfl⟩ : syracuseStep 5214887 = 7822331) B7822331
theorem B1373031 : Blo 1372005 1373031 := bstep (se 1 (by rfl) ⟨1029773, by rfl⟩ : syracuseStep 1373031 = 2059547) B2059547
theorem B12866633 : Blo 1372005 12866633 := bstep (se 2 (by rfl) ⟨4824987, by rfl⟩ : syracuseStep 12866633 = 9649975) B9649975
theorem B1373275 : Blo 1372005 1373275 := bstep (se 1 (by rfl) ⟨1029956, by rfl⟩ : syracuseStep 1373275 = 2059913) B2059913
theorem B1373311 : Blo 1372005 1373311 := bstep (se 1 (by rfl) ⟨1029983, by rfl⟩ : syracuseStep 1373311 = 2059967) B2059967
theorem B7427375 : Blo 1372005 7427375 := bstep (se 1 (by rfl) ⟨5570531, by rfl⟩ : syracuseStep 7427375 = 11141063) B11141063
theorem B50099735 : Blo 1372005 50099735 := bstep (se 1 (by rfl) ⟨37574801, by rfl⟩ : syracuseStep 50099735 = 75149603) B75149603
theorem B4634279 : Blo 1372005 4634279 := bstep (se 1 (by rfl) ⟨3475709, by rfl⟩ : syracuseStep 4634279 = 6951419) B6951419
theorem B1373951 : Blo 1372005 1373951 := bstep (se 1 (by rfl) ⟨1030463, by rfl⟩ : syracuseStep 1373951 = 2060927) B2060927
theorem B4634387 : Blo 1372005 4634387 := bstep (se 1 (by rfl) ⟨3475790, by rfl⟩ : syracuseStep 4634387 = 6951581) B6951581
theorem B26744741 : Blo 1372005 26744741 := bstep (se 4 (by rfl) ⟨2507319, by rfl⟩ : syracuseStep 26744741 = 5014639) B5014639
theorem B2930735 : Blo 1372005 2930735 := bstep (se 1 (by rfl) ⟨2198051, by rfl⟩ : syracuseStep 2930735 = 4396103) B4396103
theorem B25745863 : Blo 1372005 25745863 := bstep (se 1 (by rfl) ⟨19309397, by rfl⟩ : syracuseStep 25745863 = 38618795) B38618795
theorem B17840641 : Blo 1372005 17840641 := bstep (se 2 (by rfl) ⟨6690240, by rfl⟩ : syracuseStep 17840641 = 13380481) B13380481
theorem B6953687 : Blo 1372005 6953687 := bstep (se 1 (by rfl) ⟨5215265, by rfl⟩ : syracuseStep 6953687 = 10430531) B10430531
theorem B40139545 : Blo 1372005 40139545 := bstep (se 2 (by rfl) ⟨15052329, by rfl⟩ : syracuseStep 40139545 = 30104659) B30104659
theorem B22256689 : Blo 1372005 22256689 := bstep (se 2 (by rfl) ⟨8346258, by rfl⟩ : syracuseStep 22256689 = 16692517) B16692517
theorem B1784935 : Blo 1372005 1784935 := bstep (se 1 (by rfl) ⟨1338701, by rfl⟩ : syracuseStep 1784935 = 2677403) B2677403
theorem B3087611 : Blo 1372005 3087611 := bstep (se 1 (by rfl) ⟨2315708, by rfl⟩ : syracuseStep 3087611 = 4631417) B4631417
theorem B5357159 : Blo 1372005 5357159 := bstep (se 1 (by rfl) ⟨4017869, by rfl⟩ : syracuseStep 5357159 = 8035739) B8035739
theorem B12533401 : Blo 1372005 12533401 := bstep (se 2 (by rfl) ⟨4700025, by rfl⟩ : syracuseStep 12533401 = 9400051) B9400051
theorem B2318503 : Blo 1372005 2318503 := bstep (se 1 (by rfl) ⟨1738877, by rfl⟩ : syracuseStep 2318503 = 3477755) B3477755
theorem B17604803 : Blo 1372005 17604803 := bstep (se 1 (by rfl) ⟨13203602, by rfl⟩ : syracuseStep 17604803 = 26407205) B26407205
theorem B35193203 : Blo 1372005 35193203 := bstep (se 1 (by rfl) ⟨26394902, by rfl⟩ : syracuseStep 35193203 = 52789805) B52789805
theorem B9519653 : Blo 1372005 9519653 := bstep (se 4 (by rfl) ⟨892467, by rfl⟩ : syracuseStep 9519653 = 1784935) B1784935
theorem B8577755 : Blo 1372005 8577755 := bstep (se 1 (by rfl) ⟨6433316, by rfl⟩ : syracuseStep 8577755 = 12866633) B12866633
theorem B33399823 : Blo 1372005 33399823 := bstep (se 1 (by rfl) ⟨25049867, by rfl⟩ : syracuseStep 33399823 = 50099735) B50099735
theorem B53519393 : Blo 1372005 53519393 := bstep (se 2 (by rfl) ⟨20069772, by rfl⟩ : syracuseStep 53519393 = 40139545) B40139545
theorem B3089519 : Blo 1372005 3089519 := bstep (se 1 (by rfl) ⟨2317139, by rfl⟩ : syracuseStep 3089519 = 4634279) B4634279
theorem B3089591 : Blo 1372005 3089591 := bstep (se 1 (by rfl) ⟨2317193, by rfl⟩ : syracuseStep 3089591 = 4634387) B4634387
theorem B2058407 : Blo 1372005 2058407 := bstep (se 1 (by rfl) ⟨1543805, by rfl⟩ : syracuseStep 2058407 = 3087611) B3087611
theorem B2058971 : Blo 1372005 2058971 := bstep (se 1 (by rfl) ⟨1544228, by rfl⟩ : syracuseStep 2058971 = 3088457) B3088457
theorem B118688489 : Blo 1372005 118688489 := bstep (se 2 (by rfl) ⟨44508183, by rfl⟩ : syracuseStep 118688489 = 89016367) B89016367
theorem B3910447 : Blo 1372005 3910447 := bstep (se 1 (by rfl) ⟨2932835, by rfl⟩ : syracuseStep 3910447 = 5865671) B5865671
theorem B59337683 : Blo 1372005 59337683 := bstep (se 1 (by rfl) ⟨44503262, by rfl⟩ : syracuseStep 59337683 = 89006525) B89006525
theorem B21146665 : Blo 1372005 21146665 := bstep (se 2 (by rfl) ⟨7929999, by rfl⟩ : syracuseStep 21146665 = 15859999) B15859999
theorem B6949961 : Blo 1372005 6949961 := bstep (se 2 (by rfl) ⟨2606235, by rfl⟩ : syracuseStep 6949961 = 5212471) B5212471
theorem B3476591 : Blo 1372005 3476591 := bstep (se 1 (by rfl) ⟨2607443, by rfl⟩ : syracuseStep 3476591 = 5214887) B5214887
theorem B34327817 : Blo 1372005 34327817 := bstep (se 2 (by rfl) ⟨12872931, by rfl⟩ : syracuseStep 34327817 = 25745863) B25745863
theorem B4631849 : Blo 1372005 4631849 := bstep (se 2 (by rfl) ⟨1736943, by rfl⟩ : syracuseStep 4631849 = 3473887) B3473887
theorem B17591681 : Blo 1372005 17591681 := bstep (se 2 (by rfl) ⟨6596880, by rfl⟩ : syracuseStep 17591681 = 13193761) B13193761
theorem B4951583 : Blo 1372005 4951583 := bstep (se 1 (by rfl) ⟨3713687, by rfl⟩ : syracuseStep 4951583 = 7427375) B7427375
theorem B2060111 : Blo 1372005 2060111 := bstep (se 1 (by rfl) ⟨1545083, by rfl⟩ : syracuseStep 2060111 = 3090167) B3090167
theorem B4632443 : Blo 1372005 4632443 := bstep (se 1 (by rfl) ⟨3474332, by rfl⟩ : syracuseStep 4632443 = 6948665) B6948665
theorem B17829827 : Blo 1372005 17829827 := bstep (se 1 (by rfl) ⟨13372370, by rfl⟩ : syracuseStep 17829827 = 26744741) B26744741
theorem B1953823 : Blo 1372005 1953823 := bstep (se 1 (by rfl) ⟨1465367, by rfl⟩ : syracuseStep 1953823 = 2930735) B2930735
theorem B29675585 : Blo 1372005 29675585 := bstep (se 2 (by rfl) ⟨11128344, by rfl⟩ : syracuseStep 29675585 = 22256689) B22256689
theorem B4763711 : Blo 1372005 4763711 := bstep (se 1 (by rfl) ⟨3572783, by rfl⟩ : syracuseStep 4763711 = 7145567) B7145567
theorem B5861879 : Blo 1372005 5861879 := bstep (se 1 (by rfl) ⟨4396409, by rfl⟩ : syracuseStep 5861879 = 8792819) B8792819
theorem B2200441 : Blo 1372005 2200441 := bstep (se 2 (by rfl) ⟨825165, by rfl⟩ : syracuseStep 2200441 = 1650331) B1650331
theorem B126809063 : Blo 1372005 126809063 := bstep (se 1 (by rfl) ⟨95106797, by rfl⟩ : syracuseStep 126809063 = 190213595) B190213595
theorem B4396025 : Blo 1372005 4396025 := bstep (se 2 (by rfl) ⟨1648509, by rfl⟩ : syracuseStep 4396025 = 3297019) B3297019
theorem B1373287 : Blo 1372005 1373287 := bstep (se 1 (by rfl) ⟨1029965, by rfl⟩ : syracuseStep 1373287 = 2059931) B2059931
theorem B5862527 : Blo 1372005 5862527 := bstep (se 1 (by rfl) ⟨4396895, by rfl⟩ : syracuseStep 5862527 = 8793791) B8793791
theorem B13194839 : Blo 1372005 13194839 := bstep (se 1 (by rfl) ⟨9896129, by rfl⟩ : syracuseStep 13194839 = 19792259) B19792259
theorem B18331525 : Blo 1372005 18331525 := bstep (se 4 (by rfl) ⟨1718580, by rfl⟩ : syracuseStep 18331525 = 3437161) B3437161
theorem B23787521 : Blo 1372005 23787521 := bstep (se 2 (by rfl) ⟨8920320, by rfl⟩ : syracuseStep 23787521 = 17840641) B17840641
theorem B10426643 : Blo 1372005 10426643 := bstep (se 1 (by rfl) ⟨7819982, by rfl⟩ : syracuseStep 10426643 = 15639965) B15639965
theorem B4397807 : Blo 1372005 4397807 := bstep (se 1 (by rfl) ⟨3298355, by rfl⟩ : syracuseStep 4397807 = 6596711) B6596711
theorem B228572117 : Blo 1372005 228572117 := bstep (se 7 (by rfl) ⟨2678579, by rfl⟩ : syracuseStep 228572117 = 5357159) B5357159
theorem B4635791 : Blo 1372005 4635791 := bstep (se 1 (by rfl) ⟨3476843, by rfl⟩ : syracuseStep 4635791 = 6953687) B6953687
theorem B50126039 : Blo 1372005 50126039 := bstep (se 1 (by rfl) ⟨37594529, by rfl⟩ : syracuseStep 50126039 = 75189059) B75189059
theorem B16711201 : Blo 1372005 16711201 := bstep (se 2 (by rfl) ⟨6266700, by rfl⟩ : syracuseStep 16711201 = 12533401) B12533401
theorem B7823081 : Blo 1372005 7823081 := bstep (se 2 (by rfl) ⟨2933655, by rfl⟩ : syracuseStep 7823081 = 5867311) B5867311
theorem B2605097 : Blo 1372005 2605097 := bstep (se 2 (by rfl) ⟨976911, by rfl⟩ : syracuseStep 2605097 = 1953823) B1953823
theorem B19783723 : Blo 1372005 19783723 := bstep (se 1 (by rfl) ⟨14837792, by rfl⟩ : syracuseStep 19783723 = 29675585) B29675585
theorem B23462135 : Blo 1372005 23462135 := bstep (se 1 (by rfl) ⟨17596601, by rfl⟩ : syracuseStep 23462135 = 35193203) B35193203
theorem B3907919 : Blo 1372005 3907919 := bstep (se 1 (by rfl) ⟨2930939, by rfl⟩ : syracuseStep 3907919 = 5861879) B5861879
theorem B5718503 : Blo 1372005 5718503 := bstep (se 1 (by rfl) ⟨4288877, by rfl⟩ : syracuseStep 5718503 = 8577755) B8577755
theorem B3908351 : Blo 1372005 3908351 := bstep (se 1 (by rfl) ⟨2931263, by rfl⟩ : syracuseStep 3908351 = 5862527) B5862527
theorem B2933921 : Blo 1372005 2933921 := bstep (se 2 (by rfl) ⟨1100220, by rfl⟩ : syracuseStep 2933921 = 2200441) B2200441
theorem B44533097 : Blo 1372005 44533097 := bstep (se 2 (by rfl) ⟨16699911, by rfl⟩ : syracuseStep 44533097 = 33399823) B33399823
theorem B152381411 : Blo 1372005 152381411 := bstep (se 1 (by rfl) ⟨114286058, by rfl⟩ : syracuseStep 152381411 = 228572117) B228572117
theorem B3090527 : Blo 1372005 3090527 := bstep (se 1 (by rfl) ⟨2317895, by rfl⟩ : syracuseStep 3090527 = 4635791) B4635791
theorem B33417359 : Blo 1372005 33417359 := bstep (se 1 (by rfl) ⟨25063019, by rfl⟩ : syracuseStep 33417359 = 50126039) B50126039
theorem B3091337 : Blo 1372005 3091337 := bstep (se 2 (by rfl) ⟨1159251, by rfl⟩ : syracuseStep 3091337 = 2318503) B2318503
theorem B2059679 : Blo 1372005 2059679 := bstep (se 1 (by rfl) ⟨1544759, by rfl⟩ : syracuseStep 2059679 = 3089519) B3089519
theorem B2059727 : Blo 1372005 2059727 := bstep (se 1 (by rfl) ⟨1544795, by rfl⟩ : syracuseStep 2059727 = 3089591) B3089591
theorem B5213929 : Blo 1372005 5213929 := bstep (se 2 (by rfl) ⟨1955223, by rfl⟩ : syracuseStep 5213929 = 3910447) B3910447
theorem B1372271 : Blo 1372005 1372271 := bstep (se 1 (by rfl) ⟨1029203, by rfl⟩ : syracuseStep 1372271 = 2058407) B2058407
theorem B6951095 : Blo 1372005 6951095 := bstep (se 1 (by rfl) ⟨5213321, by rfl⟩ : syracuseStep 6951095 = 10426643) B10426643
theorem B1372647 : Blo 1372005 1372647 := bstep (se 1 (by rfl) ⟨1029485, by rfl⟩ : syracuseStep 1372647 = 2058971) B2058971
theorem B4633307 : Blo 1372005 4633307 := bstep (se 1 (by rfl) ⟨3474980, by rfl⟩ : syracuseStep 4633307 = 6949961) B6949961
theorem B22885211 : Blo 1372005 22885211 := bstep (se 1 (by rfl) ⟨17163908, by rfl⟩ : syracuseStep 22885211 = 34327817) B34327817
theorem B11727787 : Blo 1372005 11727787 := bstep (se 1 (by rfl) ⟨8795840, by rfl⟩ : syracuseStep 11727787 = 17591681) B17591681
theorem B5215387 : Blo 1372005 5215387 := bstep (se 1 (by rfl) ⟨3911540, by rfl⟩ : syracuseStep 5215387 = 7823081) B7823081
theorem B24442033 : Blo 1372005 24442033 := bstep (se 2 (by rfl) ⟨9165762, by rfl⟩ : syracuseStep 24442033 = 18331525) B18331525
theorem B1373407 : Blo 1372005 1373407 := bstep (se 1 (by rfl) ⟨1030055, by rfl⟩ : syracuseStep 1373407 = 2060111) B2060111
theorem B3175807 : Blo 1372005 3175807 := bstep (se 1 (by rfl) ⟨2381855, by rfl⟩ : syracuseStep 3175807 = 4763711) B4763711
theorem B142718381 : Blo 1372005 142718381 := bstep (se 3 (by rfl) ⟨26759696, by rfl⟩ : syracuseStep 142718381 = 53519393) B53519393
theorem B11736535 : Blo 1372005 11736535 := bstep (se 1 (by rfl) ⟨8802401, by rfl⟩ : syracuseStep 11736535 = 17604803) B17604803
theorem B6346435 : Blo 1372005 6346435 := bstep (se 1 (by rfl) ⟨4759826, by rfl⟩ : syracuseStep 6346435 = 9519653) B9519653
theorem B84539375 : Blo 1372005 84539375 := bstep (se 1 (by rfl) ⟨63404531, by rfl⟩ : syracuseStep 84539375 = 126809063) B126809063
theorem B2930683 : Blo 1372005 2930683 := bstep (se 1 (by rfl) ⟨2198012, by rfl⟩ : syracuseStep 2930683 = 4396025) B4396025
theorem B8796559 : Blo 1372005 8796559 := bstep (se 1 (by rfl) ⟨6597419, by rfl⟩ : syracuseStep 8796559 = 13194839) B13194839
theorem B15858347 : Blo 1372005 15858347 := bstep (se 1 (by rfl) ⟨11893760, by rfl⟩ : syracuseStep 15858347 = 23787521) B23787521
theorem B28195553 : Blo 1372005 28195553 := bstep (se 2 (by rfl) ⟨10573332, by rfl⟩ : syracuseStep 28195553 = 21146665) B21146665
theorem B79125659 : Blo 1372005 79125659 := bstep (se 1 (by rfl) ⟨59344244, by rfl⟩ : syracuseStep 79125659 = 118688489) B118688489
theorem B2931871 : Blo 1372005 2931871 := bstep (se 1 (by rfl) ⟨2198903, by rfl⟩ : syracuseStep 2931871 = 4397807) B4397807
theorem B39558455 : Blo 1372005 39558455 := bstep (se 1 (by rfl) ⟨29668841, by rfl⟩ : syracuseStep 39558455 = 59337683) B59337683
theorem B22281601 : Blo 1372005 22281601 := bstep (se 2 (by rfl) ⟨8355600, by rfl⟩ : syracuseStep 22281601 = 16711201) B16711201
theorem B2317727 : Blo 1372005 2317727 := bstep (se 1 (by rfl) ⟨1738295, by rfl⟩ : syracuseStep 2317727 = 3476591) B3476591
theorem B3087899 : Blo 1372005 3087899 := bstep (se 1 (by rfl) ⟨2315924, by rfl⟩ : syracuseStep 3087899 = 4631849) B4631849
theorem B3301055 : Blo 1372005 3301055 := bstep (se 1 (by rfl) ⟨2475791, by rfl⟩ : syracuseStep 3301055 = 4951583) B4951583
theorem B3088295 : Blo 1372005 3088295 := bstep (se 1 (by rfl) ⟨2316221, by rfl⟩ : syracuseStep 3088295 = 4632443) B4632443
theorem B11886551 : Blo 1372005 11886551 := bstep (se 1 (by rfl) ⟨8914913, by rfl⟩ : syracuseStep 11886551 = 17829827) B17829827
theorem B1736731 : Blo 1372005 1736731 := bstep (se 1 (by rfl) ⟨1302548, by rfl⟩ : syracuseStep 1736731 = 2605097) B2605097
theorem B26378297 : Blo 1372005 26378297 := bstep (se 2 (by rfl) ⟨9891861, by rfl⟩ : syracuseStep 26378297 = 19783723) B19783723
theorem B2605279 : Blo 1372005 2605279 := bstep (se 1 (by rfl) ⟨1953959, by rfl⟩ : syracuseStep 2605279 = 3907919) B3907919
theorem B7823789 : Blo 1372005 7823789 := bstep (se 3 (by rfl) ⟨1466960, by rfl⟩ : syracuseStep 7823789 = 2933921) B2933921
theorem B3088871 : Blo 1372005 3088871 := bstep (se 1 (by rfl) ⟨2316653, by rfl⟩ : syracuseStep 3088871 = 4633307) B4633307
theorem B29688731 : Blo 1372005 29688731 := bstep (se 1 (by rfl) ⟨22266548, by rfl⟩ : syracuseStep 29688731 = 44533097) B44533097
theorem B3909161 : Blo 1372005 3909161 := bstep (se 2 (by rfl) ⟨1465935, by rfl⟩ : syracuseStep 3909161 = 2931871) B2931871
theorem B32589377 : Blo 1372005 32589377 := bstep (se 2 (by rfl) ⟨12221016, by rfl⟩ : syracuseStep 32589377 = 24442033) B24442033
theorem B42288925 : Blo 1372005 42288925 := bstep (se 3 (by rfl) ⟨7929173, by rfl⟩ : syracuseStep 42288925 = 15858347) B15858347
theorem B15648713 : Blo 1372005 15648713 := bstep (se 2 (by rfl) ⟨5868267, by rfl⟩ : syracuseStep 15648713 = 11736535) B11736535
theorem B10422269 : Blo 1372005 10422269 := bstep (se 3 (by rfl) ⟨1954175, by rfl⟩ : syracuseStep 10422269 = 3908351) B3908351
theorem B52750439 : Blo 1372005 52750439 := bstep (se 1 (by rfl) ⟨39562829, by rfl⟩ : syracuseStep 52750439 = 79125659) B79125659
theorem B26372303 : Blo 1372005 26372303 := bstep (se 1 (by rfl) ⟨19779227, by rfl⟩ : syracuseStep 26372303 = 39558455) B39558455
theorem B2058599 : Blo 1372005 2058599 := bstep (se 1 (by rfl) ⟨1543949, by rfl⟩ : syracuseStep 2058599 = 3087899) B3087899
theorem B2058863 : Blo 1372005 2058863 := bstep (se 1 (by rfl) ⟨1544147, by rfl⟩ : syracuseStep 2058863 = 3088295) B3088295
theorem B7924367 : Blo 1372005 7924367 := bstep (se 1 (by rfl) ⟨5943275, by rfl⟩ : syracuseStep 7924367 = 11886551) B11886551
theorem B15641423 : Blo 1372005 15641423 := bstep (se 1 (by rfl) ⟨11731067, by rfl⟩ : syracuseStep 15641423 = 23462135) B23462135
theorem B3812335 : Blo 1372005 3812335 := bstep (se 1 (by rfl) ⟨2859251, by rfl⟩ : syracuseStep 3812335 = 5718503) B5718503
theorem B95145587 : Blo 1372005 95145587 := bstep (se 1 (by rfl) ⟨71359190, by rfl⟩ : syracuseStep 95145587 = 142718381) B142718381
theorem B2060351 : Blo 1372005 2060351 := bstep (se 1 (by rfl) ⟨1545263, by rfl⟩ : syracuseStep 2060351 = 3090527) B3090527
theorem B22278239 : Blo 1372005 22278239 := bstep (se 1 (by rfl) ⟨16708679, by rfl⟩ : syracuseStep 22278239 = 33417359) B33417359
theorem B18797035 : Blo 1372005 18797035 := bstep (se 1 (by rfl) ⟨14097776, by rfl⟩ : syracuseStep 18797035 = 28195553) B28195553
theorem B29708801 : Blo 1372005 29708801 := bstep (se 2 (by rfl) ⟨11140800, by rfl⟩ : syracuseStep 29708801 = 22281601) B22281601
theorem B2060891 : Blo 1372005 2060891 := bstep (se 1 (by rfl) ⟨1545668, by rfl⟩ : syracuseStep 2060891 = 3091337) B3091337
theorem B61027229 : Blo 1372005 61027229 := bstep (se 3 (by rfl) ⟨11442605, by rfl⟩ : syracuseStep 61027229 = 22885211) B22885211
theorem B1373119 : Blo 1372005 1373119 := bstep (se 1 (by rfl) ⟨1029839, by rfl⟩ : syracuseStep 1373119 = 2059679) B2059679
theorem B1545151 : Blo 1372005 1545151 := bstep (se 1 (by rfl) ⟨1158863, by rfl⟩ : syracuseStep 1545151 = 2317727) B2317727
theorem B1373151 : Blo 1372005 1373151 := bstep (se 1 (by rfl) ⟨1029863, by rfl⟩ : syracuseStep 1373151 = 2059727) B2059727
theorem B6951905 : Blo 1372005 6951905 := bstep (se 2 (by rfl) ⟨2606964, by rfl⟩ : syracuseStep 6951905 = 5213929) B5213929
theorem B2200703 : Blo 1372005 2200703 := bstep (se 1 (by rfl) ⟨1650527, by rfl⟩ : syracuseStep 2200703 = 3301055) B3301055
theorem B4634063 : Blo 1372005 4634063 := bstep (se 1 (by rfl) ⟨3475547, by rfl⟩ : syracuseStep 4634063 = 6951095) B6951095
theorem B11728745 : Blo 1372005 11728745 := bstep (se 2 (by rfl) ⟨4398279, by rfl⟩ : syracuseStep 11728745 = 8796559) B8796559
theorem B15637049 : Blo 1372005 15637049 := bstep (se 2 (by rfl) ⟨5863893, by rfl⟩ : syracuseStep 15637049 = 11727787) B11727787
theorem B101587607 : Blo 1372005 101587607 := bstep (se 1 (by rfl) ⟨76190705, by rfl⟩ : syracuseStep 101587607 = 152381411) B152381411
theorem B56359583 : Blo 1372005 56359583 := bstep (se 1 (by rfl) ⟨42269687, by rfl⟩ : syracuseStep 56359583 = 84539375) B84539375
theorem B6953849 : Blo 1372005 6953849 := bstep (se 2 (by rfl) ⟨2607693, by rfl⟩ : syracuseStep 6953849 = 5215387) B5215387
theorem B4234409 : Blo 1372005 4234409 := bstep (se 2 (by rfl) ⟨1587903, by rfl⟩ : syracuseStep 4234409 = 3175807) B3175807
theorem B3907577 : Blo 1372005 3907577 := bstep (se 2 (by rfl) ⟨1465341, by rfl⟩ : syracuseStep 3907577 = 2930683) B2930683
theorem B8461913 : Blo 1372005 8461913 := bstep (se 2 (by rfl) ⟨3173217, by rfl⟩ : syracuseStep 8461913 = 6346435) B6346435
theorem B14852159 : Blo 1372005 14852159 := bstep (se 1 (by rfl) ⟨11139119, by rfl⟩ : syracuseStep 14852159 = 22278239) B22278239
theorem B3473705 : Blo 1372005 3473705 := bstep (se 2 (by rfl) ⟨1302639, by rfl⟩ : syracuseStep 3473705 = 2605279) B2605279
theorem B19792487 : Blo 1372005 19792487 := bstep (se 1 (by rfl) ⟨14844365, by rfl⟩ : syracuseStep 19792487 = 29688731) B29688731
theorem B3089375 : Blo 1372005 3089375 := bstep (se 1 (by rfl) ⟨2317031, by rfl⟩ : syracuseStep 3089375 = 4634063) B4634063
theorem B2606107 : Blo 1372005 2606107 := bstep (se 1 (by rfl) ⟨1954580, by rfl⟩ : syracuseStep 2606107 = 3909161) B3909161
theorem B21726251 : Blo 1372005 21726251 := bstep (se 1 (by rfl) ⟨16294688, by rfl⟩ : syracuseStep 21726251 = 32589377) B32589377
theorem B6948179 : Blo 1372005 6948179 := bstep (se 1 (by rfl) ⟨5211134, by rfl⟩ : syracuseStep 6948179 = 10422269) B10422269
theorem B17581535 : Blo 1372005 17581535 := bstep (se 1 (by rfl) ⟨13186151, by rfl⟩ : syracuseStep 17581535 = 26372303) B26372303
theorem B67725071 : Blo 1372005 67725071 := bstep (se 1 (by rfl) ⟨50793803, by rfl⟩ : syracuseStep 67725071 = 101587607) B101587607
theorem B2059247 : Blo 1372005 2059247 := bstep (se 1 (by rfl) ⟨1544435, by rfl⟩ : syracuseStep 2059247 = 3088871) B3088871
theorem B5868541 : Blo 1372005 5868541 := bstep (se 3 (by rfl) ⟨1100351, by rfl⟩ : syracuseStep 5868541 = 2200703) B2200703
theorem B25062713 : Blo 1372005 25062713 := bstep (se 2 (by rfl) ⟨9398517, by rfl⟩ : syracuseStep 25062713 = 18797035) B18797035
theorem B7819163 : Blo 1372005 7819163 := bstep (se 1 (by rfl) ⟨5864372, by rfl⟩ : syracuseStep 7819163 = 11728745) B11728745
theorem B2060201 : Blo 1372005 2060201 := bstep (se 2 (by rfl) ⟨772575, by rfl⟩ : syracuseStep 2060201 = 1545151) B1545151
theorem B10432475 : Blo 1372005 10432475 := bstep (se 1 (by rfl) ⟨7824356, by rfl⟩ : syracuseStep 10432475 = 15648713) B15648713
theorem B22565101 : Blo 1372005 22565101 := bstep (se 3 (by rfl) ⟨4230956, by rfl⟩ : syracuseStep 22565101 = 8461913) B8461913
theorem B1372399 : Blo 1372005 1372399 := bstep (se 1 (by rfl) ⟨1029299, by rfl⟩ : syracuseStep 1372399 = 2058599) B2058599
theorem B10424699 : Blo 1372005 10424699 := bstep (se 1 (by rfl) ⟨7818524, by rfl⟩ : syracuseStep 10424699 = 15637049) B15637049
theorem B1372575 : Blo 1372005 1372575 := bstep (se 1 (by rfl) ⟨1029431, by rfl⟩ : syracuseStep 1372575 = 2058863) B2058863
theorem B37573055 : Blo 1372005 37573055 := bstep (se 1 (by rfl) ⟨28179791, by rfl⟩ : syracuseStep 37573055 = 56359583) B56359583
theorem B2822939 : Blo 1372005 2822939 := bstep (se 1 (by rfl) ⟨2117204, by rfl⟩ : syracuseStep 2822939 = 4234409) B4234409
theorem B162739277 : Blo 1372005 162739277 := bstep (se 3 (by rfl) ⟨30513614, by rfl⟩ : syracuseStep 162739277 = 61027229) B61027229
theorem B2315641 : Blo 1372005 2315641 := bstep (se 2 (by rfl) ⟨868365, by rfl⟩ : syracuseStep 2315641 = 1736731) B1736731
theorem B17585531 : Blo 1372005 17585531 := bstep (se 1 (by rfl) ⟨13189148, by rfl⟩ : syracuseStep 17585531 = 26378297) B26378297
theorem B1373567 : Blo 1372005 1373567 := bstep (se 1 (by rfl) ⟨1030175, by rfl⟩ : syracuseStep 1373567 = 2060351) B2060351
theorem B5215859 : Blo 1372005 5215859 := bstep (se 1 (by rfl) ⟨3911894, by rfl⟩ : syracuseStep 5215859 = 7823789) B7823789
theorem B19805867 : Blo 1372005 19805867 := bstep (se 1 (by rfl) ⟨14854400, by rfl⟩ : syracuseStep 19805867 = 29708801) B29708801
theorem B1373927 : Blo 1372005 1373927 := bstep (se 1 (by rfl) ⟨1030445, by rfl⟩ : syracuseStep 1373927 = 2060891) B2060891
theorem B4634603 : Blo 1372005 4634603 := bstep (se 1 (by rfl) ⟨3475952, by rfl⟩ : syracuseStep 4634603 = 6951905) B6951905
theorem B35166959 : Blo 1372005 35166959 := bstep (se 1 (by rfl) ⟨26375219, by rfl⟩ : syracuseStep 35166959 = 52750439) B52750439
theorem B5282911 : Blo 1372005 5282911 := bstep (se 1 (by rfl) ⟨3962183, by rfl⟩ : syracuseStep 5282911 = 7924367) B7924367
theorem B10427615 : Blo 1372005 10427615 := bstep (se 1 (by rfl) ⟨7820711, by rfl⟩ : syracuseStep 10427615 = 15641423) B15641423
theorem B4635899 : Blo 1372005 4635899 := bstep (se 1 (by rfl) ⟨3476924, by rfl⟩ : syracuseStep 4635899 = 6953849) B6953849
theorem B56385233 : Blo 1372005 56385233 := bstep (se 2 (by rfl) ⟨21144462, by rfl⟩ : syracuseStep 56385233 = 42288925) B42288925
theorem B63430391 : Blo 1372005 63430391 := bstep (se 1 (by rfl) ⟨47572793, by rfl⟩ : syracuseStep 63430391 = 95145587) B95145587
theorem B20332453 : Blo 1372005 20332453 := bstep (se 4 (by rfl) ⟨1906167, by rfl⟩ : syracuseStep 20332453 = 3812335) B3812335
theorem B2605051 : Blo 1372005 2605051 := bstep (se 1 (by rfl) ⟨1953788, by rfl⟩ : syracuseStep 2605051 = 3907577) B3907577
theorem B14484167 : Blo 1372005 14484167 := bstep (se 1 (by rfl) ⟨10863125, by rfl⟩ : syracuseStep 14484167 = 21726251) B21726251
theorem B11723687 : Blo 1372005 11723687 := bstep (se 1 (by rfl) ⟨8792765, by rfl⟩ : syracuseStep 11723687 = 17585531) B17585531
theorem B3089735 : Blo 1372005 3089735 := bstep (se 1 (by rfl) ⟨2317301, by rfl⟩ : syracuseStep 3089735 = 4634603) B4634603
theorem B7824721 : Blo 1372005 7824721 := bstep (se 2 (by rfl) ⟨2934270, by rfl⟩ : syracuseStep 7824721 = 5868541) B5868541
theorem B3474809 : Blo 1372005 3474809 := bstep (se 2 (by rfl) ⟨1303053, by rfl⟩ : syracuseStep 3474809 = 2606107) B2606107
theorem B3090599 : Blo 1372005 3090599 := bstep (se 1 (by rfl) ⟨2317949, by rfl⟩ : syracuseStep 3090599 = 4635899) B4635899
theorem B27109937 : Blo 1372005 27109937 := bstep (se 2 (by rfl) ⟨10166226, by rfl⟩ : syracuseStep 27109937 = 20332453) B20332453
theorem B5212775 : Blo 1372005 5212775 := bstep (se 1 (by rfl) ⟨3909581, by rfl⟩ : syracuseStep 5212775 = 7819163) B7819163
theorem B6949799 : Blo 1372005 6949799 := bstep (se 1 (by rfl) ⟨5212349, by rfl⟩ : syracuseStep 6949799 = 10424699) B10424699
theorem B28175525 : Blo 1372005 28175525 := bstep (se 4 (by rfl) ⟨2641455, by rfl⟩ : syracuseStep 28175525 = 5282911) B5282911
theorem B2059583 : Blo 1372005 2059583 := bstep (se 1 (by rfl) ⟨1544687, by rfl⟩ : syracuseStep 2059583 = 3089375) B3089375
theorem B4632119 : Blo 1372005 4632119 := bstep (se 1 (by rfl) ⟨3474089, by rfl⟩ : syracuseStep 4632119 = 6948179) B6948179
theorem B3477239 : Blo 1372005 3477239 := bstep (se 1 (by rfl) ⟨2607929, by rfl⟩ : syracuseStep 3477239 = 5215859) B5215859
theorem B45150047 : Blo 1372005 45150047 := bstep (se 1 (by rfl) ⟨33862535, by rfl⟩ : syracuseStep 45150047 = 67725071) B67725071
theorem B1372831 : Blo 1372005 1372831 := bstep (se 1 (by rfl) ⟨1029623, by rfl⟩ : syracuseStep 1372831 = 2059247) B2059247
theorem B6951743 : Blo 1372005 6951743 := bstep (se 1 (by rfl) ⟨5213807, by rfl⟩ : syracuseStep 6951743 = 10427615) B10427615
theorem B16708475 : Blo 1372005 16708475 := bstep (se 1 (by rfl) ⟨12531356, by rfl⟩ : syracuseStep 16708475 = 25062713) B25062713
theorem B37590155 : Blo 1372005 37590155 := bstep (se 1 (by rfl) ⟨28192616, by rfl⟩ : syracuseStep 37590155 = 56385233) B56385233
theorem B1373467 : Blo 1372005 1373467 := bstep (se 1 (by rfl) ⟨1030100, by rfl⟩ : syracuseStep 1373467 = 2060201) B2060201
theorem B9901439 : Blo 1372005 9901439 := bstep (se 1 (by rfl) ⟨7426079, by rfl⟩ : syracuseStep 9901439 = 14852159) B14852159
theorem B2315803 : Blo 1372005 2315803 := bstep (se 1 (by rfl) ⟨1736852, by rfl⟩ : syracuseStep 2315803 = 3473705) B3473705
theorem B25048703 : Blo 1372005 25048703 := bstep (se 1 (by rfl) ⟨18786527, by rfl⟩ : syracuseStep 25048703 = 37573055) B37573055
theorem B30086801 : Blo 1372005 30086801 := bstep (se 2 (by rfl) ⟨11282550, by rfl⟩ : syracuseStep 30086801 = 22565101) B22565101
theorem B13194991 : Blo 1372005 13194991 := bstep (se 1 (by rfl) ⟨9896243, by rfl⟩ : syracuseStep 13194991 = 19792487) B19792487
theorem B1881959 : Blo 1372005 1881959 := bstep (se 1 (by rfl) ⟨1411469, by rfl⟩ : syracuseStep 1881959 = 2822939) B2822939
theorem B108492851 : Blo 1372005 108492851 := bstep (se 1 (by rfl) ⟨81369638, by rfl⟩ : syracuseStep 108492851 = 162739277) B162739277
theorem B11721023 : Blo 1372005 11721023 := bstep (se 1 (by rfl) ⟨8790767, by rfl⟩ : syracuseStep 11721023 = 17581535) B17581535
theorem B13203911 : Blo 1372005 13203911 := bstep (se 1 (by rfl) ⟨9902933, by rfl⟩ : syracuseStep 13203911 = 19805867) B19805867
theorem B23444639 : Blo 1372005 23444639 := bstep (se 1 (by rfl) ⟨17583479, by rfl⟩ : syracuseStep 23444639 = 35166959) B35166959
theorem B3087521 : Blo 1372005 3087521 := bstep (se 2 (by rfl) ⟨1157820, by rfl⟩ : syracuseStep 3087521 = 2315641) B2315641
theorem B42286927 : Blo 1372005 42286927 := bstep (se 1 (by rfl) ⟨31715195, by rfl⟩ : syracuseStep 42286927 = 63430391) B63430391
theorem B6954983 : Blo 1372005 6954983 := bstep (se 1 (by rfl) ⟨5216237, by rfl⟩ : syracuseStep 6954983 = 10432475) B10432475
theorem B3473401 : Blo 1372005 3473401 := bstep (se 2 (by rfl) ⟨1302525, by rfl⟩ : syracuseStep 3473401 = 2605051) B2605051
theorem B7815791 : Blo 1372005 7815791 := bstep (se 1 (by rfl) ⟨5861843, by rfl⟩ : syracuseStep 7815791 = 11723687) B11723687
theorem B25060103 : Blo 1372005 25060103 := bstep (se 1 (by rfl) ⟨18795077, by rfl⟩ : syracuseStep 25060103 = 37590155) B37590155
theorem B72328567 : Blo 1372005 72328567 := bstep (se 1 (by rfl) ⟨54246425, by rfl⟩ : syracuseStep 72328567 = 108492851) B108492851
theorem B3475183 : Blo 1372005 3475183 := bstep (se 1 (by rfl) ⟨2606387, by rfl⟩ : syracuseStep 3475183 = 5212775) B5212775
theorem B2058347 : Blo 1372005 2058347 := bstep (se 1 (by rfl) ⟨1543760, by rfl⟩ : syracuseStep 2058347 = 3087521) B3087521
theorem B30100031 : Blo 1372005 30100031 := bstep (se 1 (by rfl) ⟨22575023, by rfl⟩ : syracuseStep 30100031 = 45150047) B45150047
theorem B4631201 : Blo 1372005 4631201 := bstep (se 2 (by rfl) ⟨1736700, by rfl⟩ : syracuseStep 4631201 = 3473401) B3473401
theorem B2059823 : Blo 1372005 2059823 := bstep (se 1 (by rfl) ⟨1544867, by rfl⟩ : syracuseStep 2059823 = 3089735) B3089735
theorem B20074229 : Blo 1372005 20074229 := bstep (se 5 (by rfl) ⟨940979, by rfl⟩ : syracuseStep 20074229 = 1881959) B1881959
theorem B16699135 : Blo 1372005 16699135 := bstep (se 1 (by rfl) ⟨12524351, by rfl⟩ : syracuseStep 16699135 = 25048703) B25048703
theorem B20057867 : Blo 1372005 20057867 := bstep (se 1 (by rfl) ⟨15043400, by rfl⟩ : syracuseStep 20057867 = 30086801) B30086801
theorem B2060399 : Blo 1372005 2060399 := bstep (se 1 (by rfl) ⟨1545299, by rfl⟩ : syracuseStep 2060399 = 3090599) B3090599
theorem B8802607 : Blo 1372005 8802607 := bstep (se 1 (by rfl) ⟨6601955, by rfl⟩ : syracuseStep 8802607 = 13203911) B13203911
theorem B10432961 : Blo 1372005 10432961 := bstep (se 2 (by rfl) ⟨3912360, by rfl⟩ : syracuseStep 10432961 = 7824721) B7824721
theorem B4633199 : Blo 1372005 4633199 := bstep (se 1 (by rfl) ⟨3474899, by rfl⟩ : syracuseStep 4633199 = 6949799) B6949799
theorem B1373055 : Blo 1372005 1373055 := bstep (se 1 (by rfl) ⟨1029791, by rfl⟩ : syracuseStep 1373055 = 2059583) B2059583
theorem B17593321 : Blo 1372005 17593321 := bstep (se 2 (by rfl) ⟨6597495, by rfl⟩ : syracuseStep 17593321 = 13194991) B13194991
theorem B56382569 : Blo 1372005 56382569 := bstep (se 2 (by rfl) ⟨21143463, by rfl⟩ : syracuseStep 56382569 = 42286927) B42286927
theorem B9656111 : Blo 1372005 9656111 := bstep (se 1 (by rfl) ⟨7242083, by rfl⟩ : syracuseStep 9656111 = 14484167) B14484167
theorem B4634495 : Blo 1372005 4634495 := bstep (se 1 (by rfl) ⟨3475871, by rfl⟩ : syracuseStep 4634495 = 6951743) B6951743
theorem B2316539 : Blo 1372005 2316539 := bstep (se 1 (by rfl) ⟨1737404, by rfl⟩ : syracuseStep 2316539 = 3474809) B3474809
theorem B6600959 : Blo 1372005 6600959 := bstep (se 1 (by rfl) ⟨4950719, by rfl⟩ : syracuseStep 6600959 = 9901439) B9901439
theorem B72293165 : Blo 1372005 72293165 := bstep (se 3 (by rfl) ⟨13554968, by rfl⟩ : syracuseStep 72293165 = 27109937) B27109937
theorem B7814015 : Blo 1372005 7814015 := bstep (se 1 (by rfl) ⟨5860511, by rfl⟩ : syracuseStep 7814015 = 11721023) B11721023
theorem B3087737 : Blo 1372005 3087737 := bstep (se 2 (by rfl) ⟨1157901, by rfl⟩ : syracuseStep 3087737 = 2315803) B2315803
theorem B15629759 : Blo 1372005 15629759 := bstep (se 1 (by rfl) ⟨11722319, by rfl⟩ : syracuseStep 15629759 = 23444639) B23444639
theorem B18783683 : Blo 1372005 18783683 := bstep (se 1 (by rfl) ⟨14087762, by rfl⟩ : syracuseStep 18783683 = 28175525) B28175525
theorem B44555933 : Blo 1372005 44555933 := bstep (se 3 (by rfl) ⟨8354237, by rfl⟩ : syracuseStep 44555933 = 16708475) B16708475
theorem B3088079 : Blo 1372005 3088079 := bstep (se 1 (by rfl) ⟨2316059, by rfl⟩ : syracuseStep 3088079 = 4632119) B4632119
theorem B2318159 : Blo 1372005 2318159 := bstep (se 1 (by rfl) ⟨1738619, by rfl⟩ : syracuseStep 2318159 = 3477239) B3477239
theorem B4636655 : Blo 1372005 4636655 := bstep (se 1 (by rfl) ⟨3477491, by rfl⟩ : syracuseStep 4636655 = 6954983) B6954983
theorem B6955307 : Blo 1372005 6955307 := bstep (se 1 (by rfl) ⟨5216480, by rfl⟩ : syracuseStep 6955307 = 10432961) B10432961
theorem B5210527 : Blo 1372005 5210527 := bstep (se 1 (by rfl) ⟨3907895, by rfl⟩ : syracuseStep 5210527 = 7815791) B7815791
theorem B3088799 : Blo 1372005 3088799 := bstep (se 1 (by rfl) ⟨2316599, by rfl⟩ : syracuseStep 3088799 = 4633199) B4633199
theorem B3089663 : Blo 1372005 3089663 := bstep (se 1 (by rfl) ⟨2317247, by rfl⟩ : syracuseStep 3089663 = 4634495) B4634495
theorem B4400639 : Blo 1372005 4400639 := bstep (se 1 (by rfl) ⟨3300479, by rfl⟩ : syracuseStep 4400639 = 6600959) B6600959
theorem B96438089 : Blo 1372005 96438089 := bstep (se 2 (by rfl) ⟨36164283, by rfl⟩ : syracuseStep 96438089 = 72328567) B72328567
theorem B48195443 : Blo 1372005 48195443 := bstep (se 1 (by rfl) ⟨36146582, by rfl⟩ : syracuseStep 48195443 = 72293165) B72293165
theorem B2058491 : Blo 1372005 2058491 := bstep (se 1 (by rfl) ⟨1543868, by rfl⟩ : syracuseStep 2058491 = 3087737) B3087737
theorem B2058719 : Blo 1372005 2058719 := bstep (se 1 (by rfl) ⟨1544039, by rfl⟩ : syracuseStep 2058719 = 3088079) B3088079
theorem B13371911 : Blo 1372005 13371911 := bstep (se 1 (by rfl) ⟨10028933, by rfl⟩ : syracuseStep 13371911 = 20057867) B20057867
theorem B3091103 : Blo 1372005 3091103 := bstep (se 1 (by rfl) ⟨2318327, by rfl⟩ : syracuseStep 3091103 = 4636655) B4636655
theorem B16706735 : Blo 1372005 16706735 := bstep (se 1 (by rfl) ⟨12530051, by rfl⟩ : syracuseStep 16706735 = 25060103) B25060103
theorem B37588379 : Blo 1372005 37588379 := bstep (se 1 (by rfl) ⟨28191284, by rfl⟩ : syracuseStep 37588379 = 56382569) B56382569
theorem B23457761 : Blo 1372005 23457761 := bstep (se 2 (by rfl) ⟨8796660, by rfl⟩ : syracuseStep 23457761 = 17593321) B17593321
theorem B1372231 : Blo 1372005 1372231 := bstep (se 1 (by rfl) ⟨1029173, by rfl⟩ : syracuseStep 1372231 = 2058347) B2058347
theorem B1544359 : Blo 1372005 1544359 := bstep (se 1 (by rfl) ⟨1158269, by rfl⟩ : syracuseStep 1544359 = 2316539) B2316539
theorem B20066687 : Blo 1372005 20066687 := bstep (se 1 (by rfl) ⟨15050015, by rfl⟩ : syracuseStep 20066687 = 30100031) B30100031
theorem B12522455 : Blo 1372005 12522455 := bstep (se 1 (by rfl) ⟨9391841, by rfl⟩ : syracuseStep 12522455 = 18783683) B18783683
theorem B4633577 : Blo 1372005 4633577 := bstep (se 2 (by rfl) ⟨1737591, by rfl⟩ : syracuseStep 4633577 = 3475183) B3475183
theorem B1373215 : Blo 1372005 1373215 := bstep (se 1 (by rfl) ⟨1029911, by rfl⟩ : syracuseStep 1373215 = 2059823) B2059823
theorem B13382819 : Blo 1372005 13382819 := bstep (se 1 (by rfl) ⟨10037114, by rfl⟩ : syracuseStep 13382819 = 20074229) B20074229
theorem B1545439 : Blo 1372005 1545439 := bstep (se 1 (by rfl) ⟨1159079, by rfl⟩ : syracuseStep 1545439 = 2318159) B2318159
theorem B1373599 : Blo 1372005 1373599 := bstep (se 1 (by rfl) ⟨1030199, by rfl⟩ : syracuseStep 1373599 = 2060399) B2060399
theorem B11736809 : Blo 1372005 11736809 := bstep (se 2 (by rfl) ⟨4401303, by rfl⟩ : syracuseStep 11736809 = 8802607) B8802607
theorem B6437407 : Blo 1372005 6437407 := bstep (se 1 (by rfl) ⟨4828055, by rfl⟩ : syracuseStep 6437407 = 9656111) B9656111
theorem B3087467 : Blo 1372005 3087467 := bstep (se 1 (by rfl) ⟨2315600, by rfl⟩ : syracuseStep 3087467 = 4631201) B4631201
theorem B5209343 : Blo 1372005 5209343 := bstep (se 1 (by rfl) ⟨3907007, by rfl⟩ : syracuseStep 5209343 = 7814015) B7814015
theorem B10419839 : Blo 1372005 10419839 := bstep (se 1 (by rfl) ⟨7814879, by rfl⟩ : syracuseStep 10419839 = 15629759) B15629759
theorem B22265513 : Blo 1372005 22265513 := bstep (se 2 (by rfl) ⟨8349567, by rfl⟩ : syracuseStep 22265513 = 16699135) B16699135
theorem B29703955 : Blo 1372005 29703955 := bstep (se 1 (by rfl) ⟨22277966, by rfl⟩ : syracuseStep 29703955 = 44555933) B44555933
theorem B4636871 : Blo 1372005 4636871 := bstep (se 1 (by rfl) ⟨3477653, by rfl⟩ : syracuseStep 4636871 = 6955307) B6955307
theorem B13377791 : Blo 1372005 13377791 := bstep (se 1 (by rfl) ⟨10033343, by rfl⟩ : syracuseStep 13377791 = 20066687) B20066687
theorem B6947369 : Blo 1372005 6947369 := bstep (se 2 (by rfl) ⟨2605263, by rfl⟩ : syracuseStep 6947369 = 5210527) B5210527
theorem B8348303 : Blo 1372005 8348303 := bstep (se 1 (by rfl) ⟨6261227, by rfl⟩ : syracuseStep 8348303 = 12522455) B12522455
theorem B3089051 : Blo 1372005 3089051 := bstep (se 1 (by rfl) ⟨2316788, by rfl⟩ : syracuseStep 3089051 = 4633577) B4633577
theorem B8921879 : Blo 1372005 8921879 := bstep (se 1 (by rfl) ⟨6691409, by rfl⟩ : syracuseStep 8921879 = 13382819) B13382819
theorem B2933759 : Blo 1372005 2933759 := bstep (se 1 (by rfl) ⟨2200319, by rfl⟩ : syracuseStep 2933759 = 4400639) B4400639
theorem B7824539 : Blo 1372005 7824539 := bstep (se 1 (by rfl) ⟨5868404, by rfl⟩ : syracuseStep 7824539 = 11736809) B11736809
theorem B64292059 : Blo 1372005 64292059 := bstep (se 1 (by rfl) ⟨48219044, by rfl⟩ : syracuseStep 64292059 = 96438089) B96438089
theorem B8914607 : Blo 1372005 8914607 := bstep (se 1 (by rfl) ⟨6685955, by rfl⟩ : syracuseStep 8914607 = 13371911) B13371911
theorem B2058311 : Blo 1372005 2058311 := bstep (se 1 (by rfl) ⟨1543733, by rfl⟩ : syracuseStep 2058311 = 3087467) B3087467
theorem B2059145 : Blo 1372005 2059145 := bstep (se 2 (by rfl) ⟨772179, by rfl⟩ : syracuseStep 2059145 = 1544359) B1544359
theorem B2059199 : Blo 1372005 2059199 := bstep (se 1 (by rfl) ⟨1544399, by rfl⟩ : syracuseStep 2059199 = 3088799) B3088799
theorem B2059775 : Blo 1372005 2059775 := bstep (se 1 (by rfl) ⟨1544831, by rfl⟩ : syracuseStep 2059775 = 3089663) B3089663
theorem B1372327 : Blo 1372005 1372327 := bstep (se 1 (by rfl) ⟨1029245, by rfl⟩ : syracuseStep 1372327 = 2058491) B2058491
theorem B2060585 : Blo 1372005 2060585 := bstep (se 2 (by rfl) ⟨772719, by rfl⟩ : syracuseStep 2060585 = 1545439) B1545439
theorem B1372479 : Blo 1372005 1372479 := bstep (se 1 (by rfl) ⟨1029359, by rfl⟩ : syracuseStep 1372479 = 2058719) B2058719
theorem B2060735 : Blo 1372005 2060735 := bstep (se 1 (by rfl) ⟨1545551, by rfl⟩ : syracuseStep 2060735 = 3091103) B3091103
theorem B11137823 : Blo 1372005 11137823 := bstep (se 1 (by rfl) ⟨8353367, by rfl⟩ : syracuseStep 11137823 = 16706735) B16706735
theorem B128521181 : Blo 1372005 128521181 := bstep (se 3 (by rfl) ⟨24097721, by rfl⟩ : syracuseStep 128521181 = 48195443) B48195443
theorem B39605273 : Blo 1372005 39605273 := bstep (se 2 (by rfl) ⟨14851977, by rfl⟩ : syracuseStep 39605273 = 29703955) B29703955
theorem B8583209 : Blo 1372005 8583209 := bstep (se 2 (by rfl) ⟨3218703, by rfl⟩ : syracuseStep 8583209 = 6437407) B6437407
theorem B100235677 : Blo 1372005 100235677 := bstep (se 3 (by rfl) ⟨18794189, by rfl⟩ : syracuseStep 100235677 = 37588379) B37588379
theorem B3472895 : Blo 1372005 3472895 := bstep (se 1 (by rfl) ⟨2604671, by rfl⟩ : syracuseStep 3472895 = 5209343) B5209343
theorem B6946559 : Blo 1372005 6946559 := bstep (se 1 (by rfl) ⟨5209919, by rfl⟩ : syracuseStep 6946559 = 10419839) B10419839
theorem B14843675 : Blo 1372005 14843675 := bstep (se 1 (by rfl) ⟨11132756, by rfl⟩ : syracuseStep 14843675 = 22265513) B22265513
theorem B15638507 : Blo 1372005 15638507 := bstep (se 1 (by rfl) ⟨11728880, by rfl⟩ : syracuseStep 15638507 = 23457761) B23457761
theorem B5947919 : Blo 1372005 5947919 := bstep (se 1 (by rfl) ⟨4460939, by rfl⟩ : syracuseStep 5947919 = 8921879) B8921879
theorem B85680787 : Blo 1372005 85680787 := bstep (se 1 (by rfl) ⟨64260590, by rfl⟩ : syracuseStep 85680787 = 128521181) B128521181
theorem B26403515 : Blo 1372005 26403515 := bstep (se 1 (by rfl) ⟨19802636, by rfl⟩ : syracuseStep 26403515 = 39605273) B39605273
theorem B4631039 : Blo 1372005 4631039 := bstep (se 1 (by rfl) ⟨3473279, by rfl⟩ : syracuseStep 4631039 = 6946559) B6946559
theorem B3091247 : Blo 1372005 3091247 := bstep (se 1 (by rfl) ⟨2318435, by rfl⟩ : syracuseStep 3091247 = 4636871) B4636871
theorem B4631579 : Blo 1372005 4631579 := bstep (se 1 (by rfl) ⟨3473684, by rfl⟩ : syracuseStep 4631579 = 6947369) B6947369
theorem B2059367 : Blo 1372005 2059367 := bstep (se 1 (by rfl) ⟨1544525, by rfl⟩ : syracuseStep 2059367 = 3089051) B3089051
theorem B7425215 : Blo 1372005 7425215 := bstep (se 1 (by rfl) ⟨5568911, by rfl⟩ : syracuseStep 7425215 = 11137823) B11137823
theorem B133647569 : Blo 1372005 133647569 := bstep (se 2 (by rfl) ⟨50117838, by rfl⟩ : syracuseStep 133647569 = 100235677) B100235677
theorem B5943071 : Blo 1372005 5943071 := bstep (se 1 (by rfl) ⟨4457303, by rfl⟩ : syracuseStep 5943071 = 8914607) B8914607
theorem B5722139 : Blo 1372005 5722139 := bstep (se 1 (by rfl) ⟨4291604, by rfl⟩ : syracuseStep 5722139 = 8583209) B8583209
theorem B1372207 : Blo 1372005 1372207 := bstep (se 1 (by rfl) ⟨1029155, by rfl⟩ : syracuseStep 1372207 = 2058311) B2058311
theorem B22262141 : Blo 1372005 22262141 := bstep (se 3 (by rfl) ⟨4174151, by rfl⟩ : syracuseStep 22262141 = 8348303) B8348303
theorem B1372763 : Blo 1372005 1372763 := bstep (se 1 (by rfl) ⟨1029572, by rfl⟩ : syracuseStep 1372763 = 2059145) B2059145
theorem B1372799 : Blo 1372005 1372799 := bstep (se 1 (by rfl) ⟨1029599, by rfl⟩ : syracuseStep 1372799 = 2059199) B2059199
theorem B2315263 : Blo 1372005 2315263 := bstep (se 1 (by rfl) ⟨1736447, by rfl⟩ : syracuseStep 2315263 = 3472895) B3472895
theorem B1373183 : Blo 1372005 1373183 := bstep (se 1 (by rfl) ⟨1029887, by rfl⟩ : syracuseStep 1373183 = 2059775) B2059775
theorem B10425671 : Blo 1372005 10425671 := bstep (se 1 (by rfl) ⟨7819253, by rfl⟩ : syracuseStep 10425671 = 15638507) B15638507
theorem B8918527 : Blo 1372005 8918527 := bstep (se 1 (by rfl) ⟨6688895, by rfl⟩ : syracuseStep 8918527 = 13377791) B13377791
theorem B1373723 : Blo 1372005 1373723 := bstep (se 1 (by rfl) ⟨1030292, by rfl⟩ : syracuseStep 1373723 = 2060585) B2060585
theorem B1373823 : Blo 1372005 1373823 := bstep (se 1 (by rfl) ⟨1030367, by rfl⟩ : syracuseStep 1373823 = 2060735) B2060735
theorem B1955839 : Blo 1372005 1955839 := bstep (se 1 (by rfl) ⟨1466879, by rfl⟩ : syracuseStep 1955839 = 2933759) B2933759
theorem B5216359 : Blo 1372005 5216359 := bstep (se 1 (by rfl) ⟨3912269, by rfl⟩ : syracuseStep 5216359 = 7824539) B7824539
theorem B342890981 : Blo 1372005 342890981 := bstep (se 4 (by rfl) ⟨32146029, by rfl⟩ : syracuseStep 342890981 = 64292059) B64292059
theorem B9895783 : Blo 1372005 9895783 := bstep (se 1 (by rfl) ⟨7421837, by rfl⟩ : syracuseStep 9895783 = 14843675) B14843675
theorem B6955145 : Blo 1372005 6955145 := bstep (se 2 (by rfl) ⟨2608179, by rfl⟩ : syracuseStep 6955145 = 5216359) B5216359
theorem B3965279 : Blo 1372005 3965279 := bstep (se 1 (by rfl) ⟨2973959, by rfl⟩ : syracuseStep 3965279 = 5947919) B5947919
theorem B4950143 : Blo 1372005 4950143 := bstep (se 1 (by rfl) ⟨3712607, by rfl⟩ : syracuseStep 4950143 = 7425215) B7425215
theorem B89098379 : Blo 1372005 89098379 := bstep (se 1 (by rfl) ⟨66823784, by rfl⟩ : syracuseStep 89098379 = 133647569) B133647569
theorem B2607785 : Blo 1372005 2607785 := bstep (se 2 (by rfl) ⟨977919, by rfl⟩ : syracuseStep 2607785 = 1955839) B1955839
theorem B114241049 : Blo 1372005 114241049 := bstep (se 2 (by rfl) ⟨42840393, by rfl⟩ : syracuseStep 114241049 = 85680787) B85680787
theorem B6950447 : Blo 1372005 6950447 := bstep (se 1 (by rfl) ⟨5212835, by rfl⟩ : syracuseStep 6950447 = 10425671) B10425671
theorem B228593987 : Blo 1372005 228593987 := bstep (se 1 (by rfl) ⟨171445490, by rfl⟩ : syracuseStep 228593987 = 342890981) B342890981
theorem B2060831 : Blo 1372005 2060831 := bstep (se 1 (by rfl) ⟨1545623, by rfl⟩ : syracuseStep 2060831 = 3091247) B3091247
theorem B11891369 : Blo 1372005 11891369 := bstep (se 2 (by rfl) ⟨4459263, by rfl⟩ : syracuseStep 11891369 = 8918527) B8918527
theorem B1372911 : Blo 1372005 1372911 := bstep (se 1 (by rfl) ⟨1029683, by rfl⟩ : syracuseStep 1372911 = 2059367) B2059367
theorem B13194377 : Blo 1372005 13194377 := bstep (se 2 (by rfl) ⟨4947891, by rfl⟩ : syracuseStep 13194377 = 9895783) B9895783
theorem B3962047 : Blo 1372005 3962047 := bstep (se 1 (by rfl) ⟨2971535, by rfl⟩ : syracuseStep 3962047 = 5943071) B5943071
theorem B3814759 : Blo 1372005 3814759 := bstep (se 1 (by rfl) ⟨2861069, by rfl⟩ : syracuseStep 3814759 = 5722139) B5722139
theorem B14841427 : Blo 1372005 14841427 := bstep (se 1 (by rfl) ⟨11131070, by rfl⟩ : syracuseStep 14841427 = 22262141) B22262141
theorem B17602343 : Blo 1372005 17602343 := bstep (se 1 (by rfl) ⟨13201757, by rfl⟩ : syracuseStep 17602343 = 26403515) B26403515
theorem B3087017 : Blo 1372005 3087017 := bstep (se 2 (by rfl) ⟨1157631, by rfl⟩ : syracuseStep 3087017 = 2315263) B2315263
theorem B3087359 : Blo 1372005 3087359 := bstep (se 1 (by rfl) ⟨2315519, by rfl⟩ : syracuseStep 3087359 = 4631039) B4631039
theorem B3087719 : Blo 1372005 3087719 := bstep (se 1 (by rfl) ⟨2315789, by rfl⟩ : syracuseStep 3087719 = 4631579) B4631579
theorem B4636763 : Blo 1372005 4636763 := bstep (se 1 (by rfl) ⟨3477572, by rfl⟩ : syracuseStep 4636763 = 6955145) B6955145
theorem B152395991 : Blo 1372005 152395991 := bstep (se 1 (by rfl) ⟨114296993, by rfl⟩ : syracuseStep 152395991 = 228593987) B228593987
theorem B2058011 : Blo 1372005 2058011 := bstep (se 1 (by rfl) ⟨1543508, by rfl⟩ : syracuseStep 2058011 = 3087017) B3087017
theorem B1738523 : Blo 1372005 1738523 := bstep (se 1 (by rfl) ⟨1303892, by rfl⟩ : syracuseStep 1738523 = 2607785) B2607785
theorem B2058239 : Blo 1372005 2058239 := bstep (se 1 (by rfl) ⟨1543679, by rfl⟩ : syracuseStep 2058239 = 3087359) B3087359
theorem B2058479 : Blo 1372005 2058479 := bstep (se 1 (by rfl) ⟨1543859, by rfl⟩ : syracuseStep 2058479 = 3087719) B3087719
theorem B11734895 : Blo 1372005 11734895 := bstep (se 1 (by rfl) ⟨8801171, by rfl⟩ : syracuseStep 11734895 = 17602343) B17602343
theorem B20345381 : Blo 1372005 20345381 := bstep (se 4 (by rfl) ⟨1907379, by rfl⟩ : syracuseStep 20345381 = 3814759) B3814759
theorem B19788569 : Blo 1372005 19788569 := bstep (se 2 (by rfl) ⟨7420713, by rfl⟩ : syracuseStep 19788569 = 14841427) B14841427
theorem B4633631 : Blo 1372005 4633631 := bstep (se 1 (by rfl) ⟨3475223, by rfl⟩ : syracuseStep 4633631 = 6950447) B6950447
theorem B1373887 : Blo 1372005 1373887 := bstep (se 1 (by rfl) ⟨1030415, by rfl⟩ : syracuseStep 1373887 = 2060831) B2060831
theorem B7927579 : Blo 1372005 7927579 := bstep (se 1 (by rfl) ⟨5945684, by rfl⟩ : syracuseStep 7927579 = 11891369) B11891369
theorem B8796251 : Blo 1372005 8796251 := bstep (se 1 (by rfl) ⟨6597188, by rfl⟩ : syracuseStep 8796251 = 13194377) B13194377
theorem B10574077 : Blo 1372005 10574077 := bstep (se 3 (by rfl) ⟨1982639, by rfl⟩ : syracuseStep 10574077 = 3965279) B3965279
theorem B3300095 : Blo 1372005 3300095 := bstep (se 1 (by rfl) ⟨2475071, by rfl⟩ : syracuseStep 3300095 = 4950143) B4950143
theorem B59398919 : Blo 1372005 59398919 := bstep (se 1 (by rfl) ⟨44549189, by rfl⟩ : syracuseStep 59398919 = 89098379) B89098379
theorem B5282729 : Blo 1372005 5282729 := bstep (se 2 (by rfl) ⟨1981023, by rfl⟩ : syracuseStep 5282729 = 3962047) B3962047
theorem B76160699 : Blo 1372005 76160699 := bstep (se 1 (by rfl) ⟨57120524, by rfl⟩ : syracuseStep 76160699 = 114241049) B114241049
theorem B101597327 : Blo 1372005 101597327 := bstep (se 1 (by rfl) ⟨76197995, by rfl⟩ : syracuseStep 101597327 = 152395991) B152395991
theorem B14098769 : Blo 1372005 14098769 := bstep (se 2 (by rfl) ⟨5287038, by rfl⟩ : syracuseStep 14098769 = 10574077) B10574077
theorem B3089087 : Blo 1372005 3089087 := bstep (se 1 (by rfl) ⟨2316815, by rfl⟩ : syracuseStep 3089087 = 4633631) B4633631
theorem B10570105 : Blo 1372005 10570105 := bstep (se 2 (by rfl) ⟨3963789, by rfl⟩ : syracuseStep 10570105 = 7927579) B7927579
theorem B3091175 : Blo 1372005 3091175 := bstep (se 1 (by rfl) ⟨2318381, by rfl⟩ : syracuseStep 3091175 = 4636763) B4636763
theorem B13192379 : Blo 1372005 13192379 := bstep (se 1 (by rfl) ⟨9894284, by rfl⟩ : syracuseStep 13192379 = 19788569) B19788569
theorem B1372007 : Blo 1372005 1372007 := bstep (se 1 (by rfl) ⟨1029005, by rfl⟩ : syracuseStep 1372007 = 2058011) B2058011
theorem B1372159 : Blo 1372005 1372159 := bstep (se 1 (by rfl) ⟨1029119, by rfl⟩ : syracuseStep 1372159 = 2058239) B2058239
theorem B1372319 : Blo 1372005 1372319 := bstep (se 1 (by rfl) ⟨1029239, by rfl⟩ : syracuseStep 1372319 = 2058479) B2058479
theorem B2200063 : Blo 1372005 2200063 := bstep (se 1 (by rfl) ⟨1650047, by rfl⟩ : syracuseStep 2200063 = 3300095) B3300095
theorem B13563587 : Blo 1372005 13563587 := bstep (se 1 (by rfl) ⟨10172690, by rfl⟩ : syracuseStep 13563587 = 20345381) B20345381
theorem B5864167 : Blo 1372005 5864167 := bstep (se 1 (by rfl) ⟨4398125, by rfl⟩ : syracuseStep 5864167 = 8796251) B8796251
theorem B39599279 : Blo 1372005 39599279 := bstep (se 1 (by rfl) ⟨29699459, by rfl⟩ : syracuseStep 39599279 = 59398919) B59398919
theorem B3521819 : Blo 1372005 3521819 := bstep (se 1 (by rfl) ⟨2641364, by rfl⟩ : syracuseStep 3521819 = 5282729) B5282729
theorem B4636061 : Blo 1372005 4636061 := bstep (se 3 (by rfl) ⟨869261, by rfl⟩ : syracuseStep 4636061 = 1738523) B1738523
theorem B50773799 : Blo 1372005 50773799 := bstep (se 1 (by rfl) ⟨38080349, by rfl⟩ : syracuseStep 50773799 = 76160699) B76160699
theorem B7823263 : Blo 1372005 7823263 := bstep (se 1 (by rfl) ⟨5867447, by rfl⟩ : syracuseStep 7823263 = 11734895) B11734895
theorem B67731551 : Blo 1372005 67731551 := bstep (se 1 (by rfl) ⟨50798663, by rfl⟩ : syracuseStep 67731551 = 101597327) B101597327
theorem B2933417 : Blo 1372005 2933417 := bstep (se 2 (by rfl) ⟨1100031, by rfl⟩ : syracuseStep 2933417 = 2200063) B2200063
theorem B3090707 : Blo 1372005 3090707 := bstep (se 1 (by rfl) ⟨2318030, by rfl⟩ : syracuseStep 3090707 = 4636061) B4636061
theorem B10431017 : Blo 1372005 10431017 := bstep (se 2 (by rfl) ⟨3911631, by rfl⟩ : syracuseStep 10431017 = 7823263) B7823263
theorem B9399179 : Blo 1372005 9399179 := bstep (se 1 (by rfl) ⟨7049384, by rfl⟩ : syracuseStep 9399179 = 14098769) B14098769
theorem B2059391 : Blo 1372005 2059391 := bstep (se 1 (by rfl) ⟨1544543, by rfl⟩ : syracuseStep 2059391 = 3089087) B3089087
theorem B14093473 : Blo 1372005 14093473 := bstep (se 2 (by rfl) ⟨5285052, by rfl⟩ : syracuseStep 14093473 = 10570105) B10570105
theorem B7818889 : Blo 1372005 7818889 := bstep (se 2 (by rfl) ⟨2932083, by rfl⟩ : syracuseStep 7818889 = 5864167) B5864167
theorem B2060783 : Blo 1372005 2060783 := bstep (se 1 (by rfl) ⟨1545587, by rfl⟩ : syracuseStep 2060783 = 3091175) B3091175
theorem B26399519 : Blo 1372005 26399519 := bstep (se 1 (by rfl) ⟨19799639, by rfl⟩ : syracuseStep 26399519 = 39599279) B39599279
theorem B8794919 : Blo 1372005 8794919 := bstep (se 1 (by rfl) ⟨6596189, by rfl⟩ : syracuseStep 8794919 = 13192379) B13192379
theorem B2347879 : Blo 1372005 2347879 := bstep (se 1 (by rfl) ⟨1760909, by rfl⟩ : syracuseStep 2347879 = 3521819) B3521819
theorem B9042391 : Blo 1372005 9042391 := bstep (se 1 (by rfl) ⟨6781793, by rfl⟩ : syracuseStep 9042391 = 13563587) B13563587
theorem B33849199 : Blo 1372005 33849199 := bstep (se 1 (by rfl) ⟨25386899, by rfl⟩ : syracuseStep 33849199 = 50773799) B50773799
theorem B45154367 : Blo 1372005 45154367 := bstep (se 1 (by rfl) ⟨33865775, by rfl⟩ : syracuseStep 45154367 = 67731551) B67731551
theorem B3130505 : Blo 1372005 3130505 := bstep (se 2 (by rfl) ⟨1173939, by rfl⟩ : syracuseStep 3130505 = 2347879) B2347879
theorem B45132265 : Blo 1372005 45132265 := bstep (se 2 (by rfl) ⟨16924599, by rfl⟩ : syracuseStep 45132265 = 33849199) B33849199
theorem B17599679 : Blo 1372005 17599679 := bstep (se 1 (by rfl) ⟨13199759, by rfl⟩ : syracuseStep 17599679 = 26399519) B26399519
theorem B2060471 : Blo 1372005 2060471 := bstep (se 1 (by rfl) ⟨1545353, by rfl⟩ : syracuseStep 2060471 = 3090707) B3090707
theorem B1372927 : Blo 1372005 1372927 := bstep (se 1 (by rfl) ⟨1029695, by rfl⟩ : syracuseStep 1372927 = 2059391) B2059391
theorem B10425185 : Blo 1372005 10425185 := bstep (se 2 (by rfl) ⟨3909444, by rfl⟩ : syracuseStep 10425185 = 7818889) B7818889
theorem B25064477 : Blo 1372005 25064477 := bstep (se 3 (by rfl) ⟨4699589, by rfl⟩ : syracuseStep 25064477 = 9399179) B9399179
theorem B1373855 : Blo 1372005 1373855 := bstep (se 1 (by rfl) ⟨1030391, by rfl⟩ : syracuseStep 1373855 = 2060783) B2060783
theorem B1955611 : Blo 1372005 1955611 := bstep (se 1 (by rfl) ⟨1466708, by rfl⟩ : syracuseStep 1955611 = 2933417) B2933417
theorem B5863279 : Blo 1372005 5863279 := bstep (se 1 (by rfl) ⟨4397459, by rfl⟩ : syracuseStep 5863279 = 8794919) B8794919
theorem B12056521 : Blo 1372005 12056521 := bstep (se 2 (by rfl) ⟨4521195, by rfl⟩ : syracuseStep 12056521 = 9042391) B9042391
theorem B18791297 : Blo 1372005 18791297 := bstep (se 2 (by rfl) ⟨7046736, by rfl⟩ : syracuseStep 18791297 = 14093473) B14093473
theorem B6954011 : Blo 1372005 6954011 := bstep (se 1 (by rfl) ⟨5215508, by rfl⟩ : syracuseStep 6954011 = 10431017) B10431017
theorem B12527531 : Blo 1372005 12527531 := bstep (se 1 (by rfl) ⟨9395648, by rfl⟩ : syracuseStep 12527531 = 18791297) B18791297
theorem B11733119 : Blo 1372005 11733119 := bstep (se 1 (by rfl) ⟨8799839, by rfl⟩ : syracuseStep 11733119 = 17599679) B17599679
theorem B2607481 : Blo 1372005 2607481 := bstep (se 2 (by rfl) ⟨977805, by rfl⟩ : syracuseStep 2607481 = 1955611) B1955611
theorem B7817705 : Blo 1372005 7817705 := bstep (se 2 (by rfl) ⟨2931639, by rfl⟩ : syracuseStep 7817705 = 5863279) B5863279
theorem B16075361 : Blo 1372005 16075361 := bstep (se 2 (by rfl) ⟨6028260, by rfl⟩ : syracuseStep 16075361 = 12056521) B12056521
theorem B6950123 : Blo 1372005 6950123 := bstep (se 1 (by rfl) ⟨5212592, by rfl⟩ : syracuseStep 6950123 = 10425185) B10425185
theorem B30102911 : Blo 1372005 30102911 := bstep (se 1 (by rfl) ⟨22577183, by rfl⟩ : syracuseStep 30102911 = 45154367) B45154367
theorem B1373647 : Blo 1372005 1373647 := bstep (se 1 (by rfl) ⟨1030235, by rfl⟩ : syracuseStep 1373647 = 2060471) B2060471
theorem B60176353 : Blo 1372005 60176353 := bstep (se 2 (by rfl) ⟨22566132, by rfl⟩ : syracuseStep 60176353 = 45132265) B45132265
theorem B16709651 : Blo 1372005 16709651 := bstep (se 1 (by rfl) ⟨12532238, by rfl⟩ : syracuseStep 16709651 = 25064477) B25064477
theorem B2087003 : Blo 1372005 2087003 := bstep (se 1 (by rfl) ⟨1565252, by rfl⟩ : syracuseStep 2087003 = 3130505) B3130505
theorem B4636007 : Blo 1372005 4636007 := bstep (se 1 (by rfl) ⟨3477005, by rfl⟩ : syracuseStep 4636007 = 6954011) B6954011
theorem B5211803 : Blo 1372005 5211803 := bstep (se 1 (by rfl) ⟨3908852, by rfl⟩ : syracuseStep 5211803 = 7817705) B7817705
theorem B10716907 : Blo 1372005 10716907 := bstep (se 1 (by rfl) ⟨8037680, by rfl⟩ : syracuseStep 10716907 = 16075361) B16075361
theorem B3090671 : Blo 1372005 3090671 := bstep (se 1 (by rfl) ⟨2318003, by rfl⟩ : syracuseStep 3090671 = 4636007) B4636007
theorem B80235137 : Blo 1372005 80235137 := bstep (se 2 (by rfl) ⟨30088176, by rfl⟩ : syracuseStep 80235137 = 60176353) B60176353
theorem B5565341 : Blo 1372005 5565341 := bstep (se 3 (by rfl) ⟨1043501, by rfl⟩ : syracuseStep 5565341 = 2087003) B2087003
theorem B3476641 : Blo 1372005 3476641 := bstep (se 2 (by rfl) ⟨1303740, by rfl⟩ : syracuseStep 3476641 = 2607481) B2607481
theorem B8351687 : Blo 1372005 8351687 := bstep (se 1 (by rfl) ⟨6263765, by rfl⟩ : syracuseStep 8351687 = 12527531) B12527531
theorem B4633415 : Blo 1372005 4633415 := bstep (se 1 (by rfl) ⟨3475061, by rfl⟩ : syracuseStep 4633415 = 6950123) B6950123
theorem B20068607 : Blo 1372005 20068607 := bstep (se 1 (by rfl) ⟨15051455, by rfl⟩ : syracuseStep 20068607 = 30102911) B30102911
theorem B11139767 : Blo 1372005 11139767 := bstep (se 1 (by rfl) ⟨8354825, by rfl⟩ : syracuseStep 11139767 = 16709651) B16709651
theorem B7822079 : Blo 1372005 7822079 := bstep (se 1 (by rfl) ⟨5866559, by rfl⟩ : syracuseStep 7822079 = 11733119) B11733119
theorem B3088943 : Blo 1372005 3088943 := bstep (se 1 (by rfl) ⟨2316707, by rfl⟩ : syracuseStep 3088943 = 4633415) B4633415
theorem B3474535 : Blo 1372005 3474535 := bstep (se 1 (by rfl) ⟨2605901, by rfl⟩ : syracuseStep 3474535 = 5211803) B5211803
theorem B14289209 : Blo 1372005 14289209 := bstep (se 2 (by rfl) ⟨5358453, by rfl⟩ : syracuseStep 14289209 = 10716907) B10716907
theorem B2060447 : Blo 1372005 2060447 := bstep (se 1 (by rfl) ⟨1545335, by rfl⟩ : syracuseStep 2060447 = 3090671) B3090671
theorem B53490091 : Blo 1372005 53490091 := bstep (se 1 (by rfl) ⟨40117568, by rfl⟩ : syracuseStep 53490091 = 80235137) B80235137
theorem B7426511 : Blo 1372005 7426511 := bstep (se 1 (by rfl) ⟨5569883, by rfl⟩ : syracuseStep 7426511 = 11139767) B11139767
theorem B5214719 : Blo 1372005 5214719 := bstep (se 1 (by rfl) ⟨3911039, by rfl⟩ : syracuseStep 5214719 = 7822079) B7822079
theorem B5567791 : Blo 1372005 5567791 := bstep (se 1 (by rfl) ⟨4175843, by rfl⟩ : syracuseStep 5567791 = 8351687) B8351687
theorem B53516285 : Blo 1372005 53516285 := bstep (se 3 (by rfl) ⟨10034303, by rfl⟩ : syracuseStep 53516285 = 20068607) B20068607
theorem B4635521 : Blo 1372005 4635521 := bstep (se 2 (by rfl) ⟨1738320, by rfl⟩ : syracuseStep 4635521 = 3476641) B3476641
theorem B3710227 : Blo 1372005 3710227 := bstep (se 1 (by rfl) ⟨2782670, by rfl⟩ : syracuseStep 3710227 = 5565341) B5565341
theorem B71320121 : Blo 1372005 71320121 := bstep (se 2 (by rfl) ⟨26745045, by rfl⟩ : syracuseStep 71320121 = 53490091) B53490091
theorem B35677523 : Blo 1372005 35677523 := bstep (se 1 (by rfl) ⟨26758142, by rfl⟩ : syracuseStep 35677523 = 53516285) B53516285
theorem B7423721 : Blo 1372005 7423721 := bstep (se 2 (by rfl) ⟨2783895, by rfl⟩ : syracuseStep 7423721 = 5567791) B5567791
theorem B3090347 : Blo 1372005 3090347 := bstep (se 1 (by rfl) ⟨2317760, by rfl⟩ : syracuseStep 3090347 = 4635521) B4635521
theorem B4951007 : Blo 1372005 4951007 := bstep (se 1 (by rfl) ⟨3713255, by rfl⟩ : syracuseStep 4951007 = 7426511) B7426511
theorem B3476479 : Blo 1372005 3476479 := bstep (se 1 (by rfl) ⟨2607359, by rfl⟩ : syracuseStep 3476479 = 5214719) B5214719
theorem B2059295 : Blo 1372005 2059295 := bstep (se 1 (by rfl) ⟨1544471, by rfl⟩ : syracuseStep 2059295 = 3088943) B3088943
theorem B4632713 : Blo 1372005 4632713 := bstep (se 2 (by rfl) ⟨1737267, by rfl⟩ : syracuseStep 4632713 = 3474535) B3474535
theorem B1373631 : Blo 1372005 1373631 := bstep (se 1 (by rfl) ⟨1030223, by rfl⟩ : syracuseStep 1373631 = 2060447) B2060447
theorem B9526139 : Blo 1372005 9526139 := bstep (se 1 (by rfl) ⟨7144604, by rfl⟩ : syracuseStep 9526139 = 14289209) B14289209
theorem B4946969 : Blo 1372005 4946969 := bstep (se 2 (by rfl) ⟨1855113, by rfl⟩ : syracuseStep 4946969 = 3710227) B3710227
theorem B3088475 : Blo 1372005 3088475 := bstep (se 1 (by rfl) ⟨2316356, by rfl⟩ : syracuseStep 3088475 = 4632713) B4632713
theorem B47546747 : Blo 1372005 47546747 := bstep (se 1 (by rfl) ⟨35660060, by rfl⟩ : syracuseStep 47546747 = 71320121) B71320121
theorem B4949147 : Blo 1372005 4949147 := bstep (se 1 (by rfl) ⟨3711860, by rfl⟩ : syracuseStep 4949147 = 7423721) B7423721
theorem B6350759 : Blo 1372005 6350759 := bstep (se 1 (by rfl) ⟨4763069, by rfl⟩ : syracuseStep 6350759 = 9526139) B9526139
theorem B23785015 : Blo 1372005 23785015 := bstep (se 1 (by rfl) ⟨17838761, by rfl⟩ : syracuseStep 23785015 = 35677523) B35677523
theorem B2060231 : Blo 1372005 2060231 := bstep (se 1 (by rfl) ⟨1545173, by rfl⟩ : syracuseStep 2060231 = 3090347) B3090347
theorem B3297979 : Blo 1372005 3297979 := bstep (se 1 (by rfl) ⟨2473484, by rfl⟩ : syracuseStep 3297979 = 4946969) B4946969
theorem B1372863 : Blo 1372005 1372863 := bstep (se 1 (by rfl) ⟨1029647, by rfl⟩ : syracuseStep 1372863 = 2059295) B2059295
theorem B4635305 : Blo 1372005 4635305 := bstep (se 2 (by rfl) ⟨1738239, by rfl⟩ : syracuseStep 4635305 = 3476479) B3476479
theorem B3300671 : Blo 1372005 3300671 := bstep (se 1 (by rfl) ⟨2475503, by rfl⟩ : syracuseStep 3300671 = 4951007) B4951007
theorem B13197725 : Blo 1372005 13197725 := bstep (se 3 (by rfl) ⟨2474573, by rfl⟩ : syracuseStep 13197725 = 4949147) B4949147
theorem B17589221 : Blo 1372005 17589221 := bstep (se 4 (by rfl) ⟨1648989, by rfl⟩ : syracuseStep 17589221 = 3297979) B3297979
theorem B67741429 : Blo 1372005 67741429 := bstep (se 5 (by rfl) ⟨3175379, by rfl⟩ : syracuseStep 67741429 = 6350759) B6350759
theorem B3090203 : Blo 1372005 3090203 := bstep (se 1 (by rfl) ⟨2317652, by rfl⟩ : syracuseStep 3090203 = 4635305) B4635305
theorem B31713353 : Blo 1372005 31713353 := bstep (se 2 (by rfl) ⟨11892507, by rfl⟩ : syracuseStep 31713353 = 23785015) B23785015
theorem B2058983 : Blo 1372005 2058983 := bstep (se 1 (by rfl) ⟨1544237, by rfl⟩ : syracuseStep 2058983 = 3088475) B3088475
theorem B31697831 : Blo 1372005 31697831 := bstep (se 1 (by rfl) ⟨23773373, by rfl⟩ : syracuseStep 31697831 = 47546747) B47546747
theorem B2200447 : Blo 1372005 2200447 := bstep (se 1 (by rfl) ⟨1650335, by rfl⟩ : syracuseStep 2200447 = 3300671) B3300671
theorem B1373487 : Blo 1372005 1373487 := bstep (se 1 (by rfl) ⟨1030115, by rfl⟩ : syracuseStep 1373487 = 2060231) B2060231
theorem B8798483 : Blo 1372005 8798483 := bstep (se 1 (by rfl) ⟨6598862, by rfl⟩ : syracuseStep 8798483 = 13197725) B13197725
theorem B2933929 : Blo 1372005 2933929 := bstep (se 2 (by rfl) ⟨1100223, by rfl⟩ : syracuseStep 2933929 = 2200447) B2200447
theorem B84527549 : Blo 1372005 84527549 := bstep (se 3 (by rfl) ⟨15848915, by rfl⟩ : syracuseStep 84527549 = 31697831) B31697831
theorem B11726147 : Blo 1372005 11726147 := bstep (se 1 (by rfl) ⟨8794610, by rfl⟩ : syracuseStep 11726147 = 17589221) B17589221
theorem B2060135 : Blo 1372005 2060135 := bstep (se 1 (by rfl) ⟨1545101, by rfl⟩ : syracuseStep 2060135 = 3090203) B3090203
theorem B1372655 : Blo 1372005 1372655 := bstep (se 1 (by rfl) ⟨1029491, by rfl⟩ : syracuseStep 1372655 = 2058983) B2058983
theorem B90321905 : Blo 1372005 90321905 := bstep (se 2 (by rfl) ⟨33870714, by rfl⟩ : syracuseStep 90321905 = 67741429) B67741429
theorem B21142235 : Blo 1372005 21142235 := bstep (se 1 (by rfl) ⟨15856676, by rfl⟩ : syracuseStep 21142235 = 31713353) B31713353
theorem B5865655 : Blo 1372005 5865655 := bstep (se 1 (by rfl) ⟨4399241, by rfl⟩ : syracuseStep 5865655 = 8798483) B8798483
theorem B7817431 : Blo 1372005 7817431 := bstep (se 1 (by rfl) ⟨5863073, by rfl⟩ : syracuseStep 7817431 = 11726147) B11726147
theorem B60214603 : Blo 1372005 60214603 := bstep (se 1 (by rfl) ⟨45160952, by rfl⟩ : syracuseStep 60214603 = 90321905) B90321905
theorem B3911905 : Blo 1372005 3911905 := bstep (se 2 (by rfl) ⟨1466964, by rfl⟩ : syracuseStep 3911905 = 2933929) B2933929
theorem B14094823 : Blo 1372005 14094823 := bstep (se 1 (by rfl) ⟨10571117, by rfl⟩ : syracuseStep 14094823 = 21142235) B21142235
theorem B1373423 : Blo 1372005 1373423 := bstep (se 1 (by rfl) ⟨1030067, by rfl⟩ : syracuseStep 1373423 = 2060135) B2060135
theorem B56351699 : Blo 1372005 56351699 := bstep (se 1 (by rfl) ⟨42263774, by rfl⟩ : syracuseStep 56351699 = 84527549) B84527549
theorem B18793097 : Blo 1372005 18793097 := bstep (se 2 (by rfl) ⟨7047411, by rfl⟩ : syracuseStep 18793097 = 14094823) B14094823
theorem B10423241 : Blo 1372005 10423241 := bstep (se 2 (by rfl) ⟨3908715, by rfl⟩ : syracuseStep 10423241 = 7817431) B7817431
theorem B80286137 : Blo 1372005 80286137 := bstep (se 2 (by rfl) ⟨30107301, by rfl⟩ : syracuseStep 80286137 = 60214603) B60214603
theorem B7820873 : Blo 1372005 7820873 := bstep (se 2 (by rfl) ⟨2932827, by rfl⟩ : syracuseStep 7820873 = 5865655) B5865655
theorem B5215873 : Blo 1372005 5215873 := bstep (se 2 (by rfl) ⟨1955952, by rfl⟩ : syracuseStep 5215873 = 3911905) B3911905
theorem B37567799 : Blo 1372005 37567799 := bstep (se 1 (by rfl) ⟨28175849, by rfl⟩ : syracuseStep 37567799 = 56351699) B56351699
theorem B6948827 : Blo 1372005 6948827 := bstep (se 1 (by rfl) ⟨5211620, by rfl⟩ : syracuseStep 6948827 = 10423241) B10423241
theorem B25045199 : Blo 1372005 25045199 := bstep (se 1 (by rfl) ⟨18783899, by rfl⟩ : syracuseStep 25045199 = 37567799) B37567799
theorem B12528731 : Blo 1372005 12528731 := bstep (se 1 (by rfl) ⟨9396548, by rfl⟩ : syracuseStep 12528731 = 18793097) B18793097
theorem B5213915 : Blo 1372005 5213915 := bstep (se 1 (by rfl) ⟨3910436, by rfl⟩ : syracuseStep 5213915 = 7820873) B7820873
theorem B53524091 : Blo 1372005 53524091 := bstep (se 1 (by rfl) ⟨40143068, by rfl⟩ : syracuseStep 53524091 = 80286137) B80286137
theorem B6954497 : Blo 1372005 6954497 := bstep (se 2 (by rfl) ⟨2607936, by rfl⟩ : syracuseStep 6954497 = 5215873) B5215873
theorem B16696799 : Blo 1372005 16696799 := bstep (se 1 (by rfl) ⟨12522599, by rfl⟩ : syracuseStep 16696799 = 25045199) B25045199
theorem B3475943 : Blo 1372005 3475943 := bstep (se 1 (by rfl) ⟨2606957, by rfl⟩ : syracuseStep 3475943 = 5213915) B5213915
theorem B4632551 : Blo 1372005 4632551 := bstep (se 1 (by rfl) ⟨3474413, by rfl⟩ : syracuseStep 4632551 = 6948827) B6948827
theorem B8352487 : Blo 1372005 8352487 := bstep (se 1 (by rfl) ⟨6264365, by rfl⟩ : syracuseStep 8352487 = 12528731) B12528731
theorem B35682727 : Blo 1372005 35682727 := bstep (se 1 (by rfl) ⟨26762045, by rfl⟩ : syracuseStep 35682727 = 53524091) B53524091
theorem B4636331 : Blo 1372005 4636331 := bstep (se 1 (by rfl) ⟨3477248, by rfl⟩ : syracuseStep 4636331 = 6954497) B6954497
theorem B3090887 : Blo 1372005 3090887 := bstep (se 1 (by rfl) ⟨2318165, by rfl⟩ : syracuseStep 3090887 = 4636331) B4636331
theorem B11136649 : Blo 1372005 11136649 := bstep (se 2 (by rfl) ⟨4176243, by rfl⟩ : syracuseStep 11136649 = 8352487) B8352487
theorem B47576969 : Blo 1372005 47576969 := bstep (se 2 (by rfl) ⟨17841363, by rfl⟩ : syracuseStep 47576969 = 35682727) B35682727
theorem B11131199 : Blo 1372005 11131199 := bstep (se 1 (by rfl) ⟨8348399, by rfl⟩ : syracuseStep 11131199 = 16696799) B16696799
theorem B2317295 : Blo 1372005 2317295 := bstep (se 1 (by rfl) ⟨1737971, by rfl⟩ : syracuseStep 2317295 = 3475943) B3475943
theorem B3088367 : Blo 1372005 3088367 := bstep (se 1 (by rfl) ⟨2316275, by rfl⟩ : syracuseStep 3088367 = 4632551) B4632551
theorem B2058911 : Blo 1372005 2058911 := bstep (se 1 (by rfl) ⟨1544183, by rfl⟩ : syracuseStep 2058911 = 3088367) B3088367
theorem B2060591 : Blo 1372005 2060591 := bstep (se 1 (by rfl) ⟨1545443, by rfl⟩ : syracuseStep 2060591 = 3090887) B3090887
theorem B1544863 : Blo 1372005 1544863 := bstep (se 1 (by rfl) ⟨1158647, by rfl⟩ : syracuseStep 1544863 = 2317295) B2317295
theorem B14848865 : Blo 1372005 14848865 := bstep (se 2 (by rfl) ⟨5568324, by rfl⟩ : syracuseStep 14848865 = 11136649) B11136649
theorem B31717979 : Blo 1372005 31717979 := bstep (se 1 (by rfl) ⟨23788484, by rfl⟩ : syracuseStep 31717979 = 47576969) B47576969
theorem B7420799 : Blo 1372005 7420799 := bstep (se 1 (by rfl) ⟨5565599, by rfl⟩ : syracuseStep 7420799 = 11131199) B11131199
theorem B21145319 : Blo 1372005 21145319 := bstep (se 1 (by rfl) ⟨15858989, by rfl⟩ : syracuseStep 21145319 = 31717979) B31717979
theorem B9899243 : Blo 1372005 9899243 := bstep (se 1 (by rfl) ⟨7424432, by rfl⟩ : syracuseStep 9899243 = 14848865) B14848865
theorem B2059817 : Blo 1372005 2059817 := bstep (se 2 (by rfl) ⟨772431, by rfl⟩ : syracuseStep 2059817 = 1544863) B1544863
theorem B1372607 : Blo 1372005 1372607 := bstep (se 1 (by rfl) ⟨1029455, by rfl⟩ : syracuseStep 1372607 = 2058911) B2058911
theorem B1373727 : Blo 1372005 1373727 := bstep (se 1 (by rfl) ⟨1030295, by rfl⟩ : syracuseStep 1373727 = 2060591) B2060591
theorem B4947199 : Blo 1372005 4947199 := bstep (se 1 (by rfl) ⟨3710399, by rfl⟩ : syracuseStep 4947199 = 7420799) B7420799
theorem B6599495 : Blo 1372005 6599495 := bstep (se 1 (by rfl) ⟨4949621, by rfl⟩ : syracuseStep 6599495 = 9899243) B9899243
theorem B1373211 : Blo 1372005 1373211 := bstep (se 1 (by rfl) ⟨1029908, by rfl⟩ : syracuseStep 1373211 = 2059817) B2059817
theorem B14096879 : Blo 1372005 14096879 := bstep (se 1 (by rfl) ⟨10572659, by rfl⟩ : syracuseStep 14096879 = 21145319) B21145319
theorem B26385061 : Blo 1372005 26385061 := bstep (se 4 (by rfl) ⟨2473599, by rfl⟩ : syracuseStep 26385061 = 4947199) B4947199
theorem B9397919 : Blo 1372005 9397919 := bstep (se 1 (by rfl) ⟨7048439, by rfl⟩ : syracuseStep 9397919 = 14096879) B14096879
theorem B17598653 : Blo 1372005 17598653 := bstep (se 3 (by rfl) ⟨3299747, by rfl⟩ : syracuseStep 17598653 = 6599495) B6599495
theorem B35180081 : Blo 1372005 35180081 := bstep (se 2 (by rfl) ⟨13192530, by rfl⟩ : syracuseStep 35180081 = 26385061) B26385061
theorem B11732435 : Blo 1372005 11732435 := bstep (se 1 (by rfl) ⟨8799326, by rfl⟩ : syracuseStep 11732435 = 17598653) B17598653
theorem B6265279 : Blo 1372005 6265279 := bstep (se 1 (by rfl) ⟨4698959, by rfl⟩ : syracuseStep 6265279 = 9397919) B9397919
theorem B23453387 : Blo 1372005 23453387 := bstep (se 1 (by rfl) ⟨17590040, by rfl⟩ : syracuseStep 23453387 = 35180081) B35180081
theorem B15635591 : Blo 1372005 15635591 := bstep (se 1 (by rfl) ⟨11726693, by rfl⟩ : syracuseStep 15635591 = 23453387) B23453387
theorem B8353705 : Blo 1372005 8353705 := bstep (se 2 (by rfl) ⟨3132639, by rfl⟩ : syracuseStep 8353705 = 6265279) B6265279
theorem B7821623 : Blo 1372005 7821623 := bstep (se 1 (by rfl) ⟨5866217, by rfl⟩ : syracuseStep 7821623 = 11732435) B11732435
theorem B10423727 : Blo 1372005 10423727 := bstep (se 1 (by rfl) ⟨7817795, by rfl⟩ : syracuseStep 10423727 = 15635591) B15635591
theorem B5214415 : Blo 1372005 5214415 := bstep (se 1 (by rfl) ⟨3910811, by rfl⟩ : syracuseStep 5214415 = 7821623) B7821623
theorem B11138273 : Blo 1372005 11138273 := bstep (se 2 (by rfl) ⟨4176852, by rfl⟩ : syracuseStep 11138273 = 8353705) B8353705
theorem B6949151 : Blo 1372005 6949151 := bstep (se 1 (by rfl) ⟨5211863, by rfl⟩ : syracuseStep 6949151 = 10423727) B10423727
theorem B7425515 : Blo 1372005 7425515 := bstep (se 1 (by rfl) ⟨5569136, by rfl⟩ : syracuseStep 7425515 = 11138273) B11138273
theorem B6952553 : Blo 1372005 6952553 := bstep (se 2 (by rfl) ⟨2607207, by rfl⟩ : syracuseStep 6952553 = 5214415) B5214415
theorem B4950343 : Blo 1372005 4950343 := bstep (se 1 (by rfl) ⟨3712757, by rfl⟩ : syracuseStep 4950343 = 7425515) B7425515
theorem B4632767 : Blo 1372005 4632767 := bstep (se 1 (by rfl) ⟨3474575, by rfl⟩ : syracuseStep 4632767 = 6949151) B6949151
theorem B4635035 : Blo 1372005 4635035 := bstep (se 1 (by rfl) ⟨3476276, by rfl⟩ : syracuseStep 4635035 = 6952553) B6952553
theorem B3088511 : Blo 1372005 3088511 := bstep (se 1 (by rfl) ⟨2316383, by rfl⟩ : syracuseStep 3088511 = 4632767) B4632767
theorem B3090023 : Blo 1372005 3090023 := bstep (se 1 (by rfl) ⟨2317517, by rfl⟩ : syracuseStep 3090023 = 4635035) B4635035
theorem B6600457 : Blo 1372005 6600457 := bstep (se 2 (by rfl) ⟨2475171, by rfl⟩ : syracuseStep 6600457 = 4950343) B4950343
theorem B8800609 : Blo 1372005 8800609 := bstep (se 2 (by rfl) ⟨3300228, by rfl⟩ : syracuseStep 8800609 = 6600457) B6600457
theorem B2059007 : Blo 1372005 2059007 := bstep (se 1 (by rfl) ⟨1544255, by rfl⟩ : syracuseStep 2059007 = 3088511) B3088511
theorem B2060015 : Blo 1372005 2060015 := bstep (se 1 (by rfl) ⟨1545011, by rfl⟩ : syracuseStep 2060015 = 3090023) B3090023
theorem B11734145 : Blo 1372005 11734145 := bstep (se 2 (by rfl) ⟨4400304, by rfl⟩ : syracuseStep 11734145 = 8800609) B8800609
theorem B1372671 : Blo 1372005 1372671 := bstep (se 1 (by rfl) ⟨1029503, by rfl⟩ : syracuseStep 1372671 = 2059007) B2059007
theorem B1373343 : Blo 1372005 1373343 := bstep (se 1 (by rfl) ⟨1030007, by rfl⟩ : syracuseStep 1373343 = 2060015) B2060015
theorem B7822763 : Blo 1372005 7822763 := bstep (se 1 (by rfl) ⟨5867072, by rfl⟩ : syracuseStep 7822763 = 11734145) B11734145
theorem B5215175 : Blo 1372005 5215175 := bstep (se 1 (by rfl) ⟨3911381, by rfl⟩ : syracuseStep 5215175 = 7822763) B7822763
theorem B3476783 : Blo 1372005 3476783 := bstep (se 1 (by rfl) ⟨2607587, by rfl⟩ : syracuseStep 3476783 = 5215175) B5215175
theorem B2317855 : Blo 1372005 2317855 := bstep (se 1 (by rfl) ⟨1738391, by rfl⟩ : syracuseStep 2317855 = 3476783) B3476783
theorem B3090473 : Blo 1372005 3090473 := bstep (se 2 (by rfl) ⟨1158927, by rfl⟩ : syracuseStep 3090473 = 2317855) B2317855
theorem B2060315 : Blo 1372005 2060315 := bstep (se 1 (by rfl) ⟨1545236, by rfl⟩ : syracuseStep 2060315 = 3090473) B3090473
theorem B1373543 : Blo 1372005 1373543 := bstep (se 1 (by rfl) ⟨1030157, by rfl⟩ : syracuseStep 1373543 = 2060315) B2060315

theorem C0 (j : ℕ) (h1 : 343001 ≤ j) (h2 : j ≤ 343500) : Blo 1372005 (4 * j + 3) := by
  interval_cases j
  · exact B1372007
  · exact B1372011
  · exact B1372015
  · exact B1372019
  · exact B1372023
  · exact B1372027
  · exact B1372031
  · exact B1372035
  · exact B1372039
  · exact B1372043
  · exact B1372047
  · exact B1372051
  · exact B1372055
  · exact B1372059
  · exact B1372063
  · exact B1372067
  · exact B1372071
  · exact B1372075
  · exact B1372079
  · exact B1372083
  · exact B1372087
  · exact B1372091
  · exact B1372095
  · exact B1372099
  · exact B1372103
  · exact B1372107
  · exact B1372111
  · exact B1372115
  · exact B1372119
  · exact B1372123
  · exact B1372127
  · exact B1372131
  · exact B1372135
  · exact B1372139
  · exact B1372143
  · exact B1372147
  · exact B1372151
  · exact B1372155
  · exact B1372159
  · exact B1372163
  · exact B1372167
  · exact B1372171
  · exact B1372175
  · exact B1372179
  · exact B1372183
  · exact B1372187
  · exact B1372191
  · exact B1372195
  · exact B1372199
  · exact B1372203
  · exact B1372207
  · exact B1372211
  · exact B1372215
  · exact B1372219
  · exact B1372223
  · exact B1372227
  · exact B1372231
  · exact B1372235
  · exact B1372239
  · exact B1372243
  · exact B1372247
  · exact B1372251
  · exact B1372255
  · exact B1372259
  · exact B1372263
  · exact B1372267
  · exact B1372271
  · exact B1372275
  · exact B1372279
  · exact B1372283
  · exact B1372287
  · exact B1372291
  · exact B1372295
  · exact B1372299
  · exact B1372303
  · exact B1372307
  · exact B1372311
  · exact B1372315
  · exact B1372319
  · exact B1372323
  · exact B1372327
  · exact B1372331
  · exact B1372335
  · exact B1372339
  · exact B1372343
  · exact B1372347
  · exact B1372351
  · exact B1372355
  · exact B1372359
  · exact B1372363
  · exact B1372367
  · exact B1372371
  · exact B1372375
  · exact B1372379
  · exact B1372383
  · exact B1372387
  · exact B1372391
  · exact B1372395
  · exact B1372399
  · exact B1372403
  · exact B1372407
  · exact B1372411
  · exact B1372415
  · exact B1372419
  · exact B1372423
  · exact B1372427
  · exact B1372431
  · exact B1372435
  · exact B1372439
  · exact B1372443
  · exact B1372447
  · exact B1372451
  · exact B1372455
  · exact B1372459
  · exact B1372463
  · exact B1372467
  · exact B1372471
  · exact B1372475
  · exact B1372479
  · exact B1372483
  · exact B1372487
  · exact B1372491
  · exact B1372495
  · exact B1372499
  · exact B1372503
  · exact B1372507
  · exact B1372511
  · exact B1372515
  · exact B1372519
  · exact B1372523
  · exact B1372527
  · exact B1372531
  · exact B1372535
  · exact B1372539
  · exact B1372543
  · exact B1372547
  · exact B1372551
  · exact B1372555
  · exact B1372559
  · exact B1372563
  · exact B1372567
  · exact B1372571
  · exact B1372575
  · exact B1372579
  · exact B1372583
  · exact B1372587
  · exact B1372591
  · exact B1372595
  · exact B1372599
  · exact B1372603
  · exact B1372607
  · exact B1372611
  · exact B1372615
  · exact B1372619
  · exact B1372623
  · exact B1372627
  · exact B1372631
  · exact B1372635
  · exact B1372639
  · exact B1372643
  · exact B1372647
  · exact B1372651
  · exact B1372655
  · exact B1372659
  · exact B1372663
  · exact B1372667
  · exact B1372671
  · exact B1372675
  · exact B1372679
  · exact B1372683
  · exact B1372687
  · exact B1372691
  · exact B1372695
  · exact B1372699
  · exact B1372703
  · exact B1372707
  · exact B1372711
  · exact B1372715
  · exact B1372719
  · exact B1372723
  · exact B1372727
  · exact B1372731
  · exact B1372735
  · exact B1372739
  · exact B1372743
  · exact B1372747
  · exact B1372751
  · exact B1372755
  · exact B1372759
  · exact B1372763
  · exact B1372767
  · exact B1372771
  · exact B1372775
  · exact B1372779
  · exact B1372783
  · exact B1372787
  · exact B1372791
  · exact B1372795
  · exact B1372799
  · exact B1372803
  · exact B1372807
  · exact B1372811
  · exact B1372815
  · exact B1372819
  · exact B1372823
  · exact B1372827
  · exact B1372831
  · exact B1372835
  · exact B1372839
  · exact B1372843
  · exact B1372847
  · exact B1372851
  · exact B1372855
  · exact B1372859
  · exact B1372863
  · exact B1372867
  · exact B1372871
  · exact B1372875
  · exact B1372879
  · exact B1372883
  · exact B1372887
  · exact B1372891
  · exact B1372895
  · exact B1372899
  · exact B1372903
  · exact B1372907
  · exact B1372911
  · exact B1372915
  · exact B1372919
  · exact B1372923
  · exact B1372927
  · exact B1372931
  · exact B1372935
  · exact B1372939
  · exact B1372943
  · exact B1372947
  · exact B1372951
  · exact B1372955
  · exact B1372959
  · exact B1372963
  · exact B1372967
  · exact B1372971
  · exact B1372975
  · exact B1372979
  · exact B1372983
  · exact B1372987
  · exact B1372991
  · exact B1372995
  · exact B1372999
  · exact B1373003
  · exact B1373007
  · exact B1373011
  · exact B1373015
  · exact B1373019
  · exact B1373023
  · exact B1373027
  · exact B1373031
  · exact B1373035
  · exact B1373039
  · exact B1373043
  · exact B1373047
  · exact B1373051
  · exact B1373055
  · exact B1373059
  · exact B1373063
  · exact B1373067
  · exact B1373071
  · exact B1373075
  · exact B1373079
  · exact B1373083
  · exact B1373087
  · exact B1373091
  · exact B1373095
  · exact B1373099
  · exact B1373103
  · exact B1373107
  · exact B1373111
  · exact B1373115
  · exact B1373119
  · exact B1373123
  · exact B1373127
  · exact B1373131
  · exact B1373135
  · exact B1373139
  · exact B1373143
  · exact B1373147
  · exact B1373151
  · exact B1373155
  · exact B1373159
  · exact B1373163
  · exact B1373167
  · exact B1373171
  · exact B1373175
  · exact B1373179
  · exact B1373183
  · exact B1373187
  · exact B1373191
  · exact B1373195
  · exact B1373199
  · exact B1373203
  · exact B1373207
  · exact B1373211
  · exact B1373215
  · exact B1373219
  · exact B1373223
  · exact B1373227
  · exact B1373231
  · exact B1373235
  · exact B1373239
  · exact B1373243
  · exact B1373247
  · exact B1373251
  · exact B1373255
  · exact B1373259
  · exact B1373263
  · exact B1373267
  · exact B1373271
  · exact B1373275
  · exact B1373279
  · exact B1373283
  · exact B1373287
  · exact B1373291
  · exact B1373295
  · exact B1373299
  · exact B1373303
  · exact B1373307
  · exact B1373311
  · exact B1373315
  · exact B1373319
  · exact B1373323
  · exact B1373327
  · exact B1373331
  · exact B1373335
  · exact B1373339
  · exact B1373343
  · exact B1373347
  · exact B1373351
  · exact B1373355
  · exact B1373359
  · exact B1373363
  · exact B1373367
  · exact B1373371
  · exact B1373375
  · exact B1373379
  · exact B1373383
  · exact B1373387
  · exact B1373391
  · exact B1373395
  · exact B1373399
  · exact B1373403
  · exact B1373407
  · exact B1373411
  · exact B1373415
  · exact B1373419
  · exact B1373423
  · exact B1373427
  · exact B1373431
  · exact B1373435
  · exact B1373439
  · exact B1373443
  · exact B1373447
  · exact B1373451
  · exact B1373455
  · exact B1373459
  · exact B1373463
  · exact B1373467
  · exact B1373471
  · exact B1373475
  · exact B1373479
  · exact B1373483
  · exact B1373487
  · exact B1373491
  · exact B1373495
  · exact B1373499
  · exact B1373503
  · exact B1373507
  · exact B1373511
  · exact B1373515
  · exact B1373519
  · exact B1373523
  · exact B1373527
  · exact B1373531
  · exact B1373535
  · exact B1373539
  · exact B1373543
  · exact B1373547
  · exact B1373551
  · exact B1373555
  · exact B1373559
  · exact B1373563
  · exact B1373567
  · exact B1373571
  · exact B1373575
  · exact B1373579
  · exact B1373583
  · exact B1373587
  · exact B1373591
  · exact B1373595
  · exact B1373599
  · exact B1373603
  · exact B1373607
  · exact B1373611
  · exact B1373615
  · exact B1373619
  · exact B1373623
  · exact B1373627
  · exact B1373631
  · exact B1373635
  · exact B1373639
  · exact B1373643
  · exact B1373647
  · exact B1373651
  · exact B1373655
  · exact B1373659
  · exact B1373663
  · exact B1373667
  · exact B1373671
  · exact B1373675
  · exact B1373679
  · exact B1373683
  · exact B1373687
  · exact B1373691
  · exact B1373695
  · exact B1373699
  · exact B1373703
  · exact B1373707
  · exact B1373711
  · exact B1373715
  · exact B1373719
  · exact B1373723
  · exact B1373727
  · exact B1373731
  · exact B1373735
  · exact B1373739
  · exact B1373743
  · exact B1373747
  · exact B1373751
  · exact B1373755
  · exact B1373759
  · exact B1373763
  · exact B1373767
  · exact B1373771
  · exact B1373775
  · exact B1373779
  · exact B1373783
  · exact B1373787
  · exact B1373791
  · exact B1373795
  · exact B1373799
  · exact B1373803
  · exact B1373807
  · exact B1373811
  · exact B1373815
  · exact B1373819
  · exact B1373823
  · exact B1373827
  · exact B1373831
  · exact B1373835
  · exact B1373839
  · exact B1373843
  · exact B1373847
  · exact B1373851
  · exact B1373855
  · exact B1373859
  · exact B1373863
  · exact B1373867
  · exact B1373871
  · exact B1373875
  · exact B1373879
  · exact B1373883
  · exact B1373887
  · exact B1373891
  · exact B1373895
  · exact B1373899
  · exact B1373903
  · exact B1373907
  · exact B1373911
  · exact B1373915
  · exact B1373919
  · exact B1373923
  · exact B1373927
  · exact B1373931
  · exact B1373935
  · exact B1373939
  · exact B1373943
  · exact B1373947
  · exact B1373951
  · exact B1373955
  · exact B1373959
  · exact B1373963
  · exact B1373967
  · exact B1373971
  · exact B1373975
  · exact B1373979
  · exact B1373983
  · exact B1373987
  · exact B1373991
  · exact B1373995
  · exact B1373999
  · exact B1374003

theorem solution (m : ℕ) (hlo : 1372005 ≤ m) (hhi : m ≤ 1374005) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 343001 ≤ j := by omega
    have hj2 : j ≤ 343500 := by omega
    have hb : Blo 1372005 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
