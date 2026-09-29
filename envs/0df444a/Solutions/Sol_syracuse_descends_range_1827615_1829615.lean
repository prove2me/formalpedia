-- Prove2me | solution 1 for syracuse_descends_range_1827615_1829615
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:58:41.329953+00:00
-- url     : https://prove2.me/submissions/7484441d-55b0-4789-bc12-9ccf64decb30

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


theorem B6168581 : Blo 1827615 6168581 := bbase (se 4 (by rfl) ⟨578304, by rfl⟩ : syracuseStep 6168581 = 1156609) (by norm_num)
theorem B6021125 : Blo 1827615 6021125 := bbase (se 4 (by rfl) ⟨564480, by rfl⟩ : syracuseStep 6021125 = 1128961) (by norm_num)
theorem B2744333 : Blo 1827615 2744333 := bbase (se 3 (by rfl) ⟨514562, by rfl⟩ : syracuseStep 2744333 = 1029125) (by norm_num)
theorem B4112405 : Blo 1827615 4112405 := bbase (se 6 (by rfl) ⟨96384, by rfl⟩ : syracuseStep 4112405 = 192769) (by norm_num)
theorem B2056225 : Blo 1827615 2056225 := bbase (se 2 (by rfl) ⟨771084, by rfl⟩ : syracuseStep 2056225 = 1542169) (by norm_num)
theorem B2744357 : Blo 1827615 2744357 := bbase (se 4 (by rfl) ⟨257283, by rfl⟩ : syracuseStep 2744357 = 514567) (by norm_num)
theorem B2744381 : Blo 1827615 2744381 := bbase (se 3 (by rfl) ⟨514571, by rfl⟩ : syracuseStep 2744381 = 1029143) (by norm_num)
theorem B2056261 : Blo 1827615 2056261 := bbase (se 4 (by rfl) ⟨192774, by rfl⟩ : syracuseStep 2056261 = 385549) (by norm_num)
theorem B2744405 : Blo 1827615 2744405 := bbase (se 8 (by rfl) ⟨16080, by rfl⟩ : syracuseStep 2744405 = 32161) (by norm_num)
theorem B4112477 : Blo 1827615 4112477 := bbase (se 3 (by rfl) ⟨771089, by rfl⟩ : syracuseStep 4112477 = 1542179) (by norm_num)
theorem B4628573 : Blo 1827615 4628573 := bbase (se 3 (by rfl) ⟨867857, by rfl⟩ : syracuseStep 4628573 = 1735715) (by norm_num)
theorem B2056297 : Blo 1827615 2056297 := bbase (se 2 (by rfl) ⟨771111, by rfl⟩ : syracuseStep 2056297 = 1542223) (by norm_num)
theorem B2056333 : Blo 1827615 2056333 := bbase (se 3 (by rfl) ⟨385562, by rfl⟩ : syracuseStep 2056333 = 771125) (by norm_num)
theorem B4112549 : Blo 1827615 4112549 := bbase (se 4 (by rfl) ⟨385551, by rfl⟩ : syracuseStep 4112549 = 771103) (by norm_num)
theorem B2056369 : Blo 1827615 2056369 := bbase (se 2 (by rfl) ⟨771138, by rfl⟩ : syracuseStep 2056369 = 1542277) (by norm_num)
theorem B2056405 : Blo 1827615 2056405 := bbase (se 7 (by rfl) ⟨24098, by rfl⟩ : syracuseStep 2056405 = 48197) (by norm_num)
theorem B2195689 : Blo 1827615 2195689 := bbase (se 2 (by rfl) ⟨823383, by rfl⟩ : syracuseStep 2195689 = 1646767) (by norm_num)
theorem B4112621 : Blo 1827615 4112621 := bbase (se 3 (by rfl) ⟨771116, by rfl⟩ : syracuseStep 4112621 = 1542233) (by norm_num)
theorem B2056441 : Blo 1827615 2056441 := bbase (se 2 (by rfl) ⟨771165, by rfl⟩ : syracuseStep 2056441 = 1542331) (by norm_num)
theorem B19775765 : Blo 1827615 19775765 := bbase (se 6 (by rfl) ⟨463494, by rfl⟩ : syracuseStep 19775765 = 926989) (by norm_num)
theorem B2056477 : Blo 1827615 2056477 := bbase (se 3 (by rfl) ⟨385589, by rfl⟩ : syracuseStep 2056477 = 771179) (by norm_num)
theorem B4628765 : Blo 1827615 4628765 := bbase (se 3 (by rfl) ⟨867893, by rfl⟩ : syracuseStep 4628765 = 1735787) (by norm_num)
theorem B4112693 : Blo 1827615 4112693 := bbase (se 5 (by rfl) ⟨192782, by rfl⟩ : syracuseStep 4112693 = 385565) (by norm_num)
theorem B2007349 : Blo 1827615 2007349 := bbase (se 5 (by rfl) ⟨94094, by rfl⟩ : syracuseStep 2007349 = 188189) (by norm_num)
theorem B2056513 : Blo 1827615 2056513 := bbase (se 2 (by rfl) ⟨771192, by rfl⟩ : syracuseStep 2056513 = 1542385) (by norm_num)
theorem B2056549 : Blo 1827615 2056549 := bbase (se 4 (by rfl) ⟨192801, by rfl⟩ : syracuseStep 2056549 = 385603) (by norm_num)
theorem B4112765 : Blo 1827615 4112765 := bbase (se 3 (by rfl) ⟨771143, by rfl⟩ : syracuseStep 4112765 = 1542287) (by norm_num)
theorem B2056585 : Blo 1827615 2056585 := bbase (se 2 (by rfl) ⟨771219, by rfl⟩ : syracuseStep 2056585 = 1542439) (by norm_num)
theorem B4391309 : Blo 1827615 4391309 := bbase (se 3 (by rfl) ⟨823370, by rfl⟩ : syracuseStep 4391309 = 1646741) (by norm_num)
theorem B3293597 : Blo 1827615 3293597 := bbase (se 3 (by rfl) ⟨617549, by rfl⟩ : syracuseStep 3293597 = 1235099) (by norm_num)
theorem B2056621 : Blo 1827615 2056621 := bbase (se 3 (by rfl) ⟨385616, by rfl⟩ : syracuseStep 2056621 = 771233) (by norm_num)
theorem B6169013 : Blo 1827615 6169013 := bbase (se 5 (by rfl) ⟨289172, by rfl⟩ : syracuseStep 6169013 = 578345) (by norm_num)
theorem B4112837 : Blo 1827615 4112837 := bbase (se 4 (by rfl) ⟨385578, by rfl⟩ : syracuseStep 4112837 = 771157) (by norm_num)
theorem B2056657 : Blo 1827615 2056657 := bbase (se 2 (by rfl) ⟨771246, by rfl⟩ : syracuseStep 2056657 = 1542493) (by norm_num)
theorem B8028629 : Blo 1827615 8028629 := bbase (se 7 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 8028629 = 188171) (by norm_num)
theorem B2056693 : Blo 1827615 2056693 := bbase (se 5 (by rfl) ⟨96407, by rfl⟩ : syracuseStep 2056693 = 192815) (by norm_num)
theorem B4112909 : Blo 1827615 4112909 := bbase (se 3 (by rfl) ⟨771170, by rfl⟩ : syracuseStep 4112909 = 1542341) (by norm_num)
theorem B2056729 : Blo 1827615 2056729 := bbase (se 2 (by rfl) ⟨771273, by rfl⟩ : syracuseStep 2056729 = 1542547) (by norm_num)
theorem B2056765 : Blo 1827615 2056765 := bbase (se 3 (by rfl) ⟨385643, by rfl⟩ : syracuseStep 2056765 = 771287) (by norm_num)
theorem B4112981 : Blo 1827615 4112981 := bbase (se 8 (by rfl) ⟨24099, by rfl⟩ : syracuseStep 4112981 = 48199) (by norm_num)
theorem B2056801 : Blo 1827615 2056801 := bbase (se 2 (by rfl) ⟨771300, by rfl⟩ : syracuseStep 2056801 = 1542601) (by norm_num)
theorem B2196073 : Blo 1827615 2196073 := bbase (se 2 (by rfl) ⟨823527, by rfl⟩ : syracuseStep 2196073 = 1647055) (by norm_num)
theorem B2196077 : Blo 1827615 2196077 := bbase (se 3 (by rfl) ⟨411764, by rfl⟩ : syracuseStep 2196077 = 823529) (by norm_num)
theorem B4629109 : Blo 1827615 4629109 := bbase (se 5 (by rfl) ⟨216989, by rfl⟩ : syracuseStep 4629109 = 433979) (by norm_num)
theorem B2056837 : Blo 1827615 2056837 := bbase (se 4 (by rfl) ⟨192828, by rfl⟩ : syracuseStep 2056837 = 385657) (by norm_num)
theorem B4113053 : Blo 1827615 4113053 := bbase (se 3 (by rfl) ⟨771197, by rfl⟩ : syracuseStep 4113053 = 1542395) (by norm_num)
theorem B2056873 : Blo 1827615 2056873 := bbase (se 2 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 2056873 = 1542655) (by norm_num)
theorem B2056909 : Blo 1827615 2056909 := bbase (se 3 (by rfl) ⟨385670, by rfl⟩ : syracuseStep 2056909 = 771341) (by norm_num)
theorem B4113125 : Blo 1827615 4113125 := bbase (se 4 (by rfl) ⟨385605, by rfl⟩ : syracuseStep 4113125 = 771211) (by norm_num)
theorem B4629221 : Blo 1827615 4629221 := bbase (se 4 (by rfl) ⟨433989, by rfl⟩ : syracuseStep 4629221 = 867979) (by norm_num)
theorem B2056945 : Blo 1827615 2056945 := bbase (se 2 (by rfl) ⟨771354, by rfl⟩ : syracuseStep 2056945 = 1542709) (by norm_num)
theorem B2056981 : Blo 1827615 2056981 := bbase (se 6 (by rfl) ⟨48210, by rfl⟩ : syracuseStep 2056981 = 96421) (by norm_num)
theorem B4113197 : Blo 1827615 4113197 := bbase (se 3 (by rfl) ⟨771224, by rfl⟩ : syracuseStep 4113197 = 1542449) (by norm_num)
theorem B2057017 : Blo 1827615 2057017 := bbase (se 2 (by rfl) ⟨771381, by rfl⟩ : syracuseStep 2057017 = 1542763) (by norm_num)
theorem B9257813 : Blo 1827615 9257813 := bbase (se 9 (by rfl) ⟨27122, by rfl⟩ : syracuseStep 9257813 = 54245) (by norm_num)
theorem B2057053 : Blo 1827615 2057053 := bbase (se 3 (by rfl) ⟨385697, by rfl⟩ : syracuseStep 2057053 = 771395) (by norm_num)
theorem B6169445 : Blo 1827615 6169445 := bbase (se 4 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 6169445 = 1156771) (by norm_num)
theorem B4113269 : Blo 1827615 4113269 := bbase (se 5 (by rfl) ⟨192809, by rfl⟩ : syracuseStep 4113269 = 385619) (by norm_num)
theorem B2057089 : Blo 1827615 2057089 := bbase (se 2 (by rfl) ⟨771408, by rfl⟩ : syracuseStep 2057089 = 1542817) (by norm_num)
theorem B2057125 : Blo 1827615 2057125 := bbase (se 4 (by rfl) ⟨192855, by rfl⟩ : syracuseStep 2057125 = 385711) (by norm_num)
theorem B4629413 : Blo 1827615 4629413 := bbase (se 4 (by rfl) ⟨434007, by rfl⟩ : syracuseStep 4629413 = 868015) (by norm_num)
theorem B4113341 : Blo 1827615 4113341 := bbase (se 3 (by rfl) ⟨771251, by rfl⟩ : syracuseStep 4113341 = 1542503) (by norm_num)
theorem B4940741 : Blo 1827615 4940741 := bbase (se 4 (by rfl) ⟨463194, by rfl⟩ : syracuseStep 4940741 = 926389) (by norm_num)
theorem B2057161 : Blo 1827615 2057161 := bbase (se 2 (by rfl) ⟨771435, by rfl⟩ : syracuseStep 2057161 = 1542871) (by norm_num)
theorem B10560469 : Blo 1827615 10560469 := bbase (se 7 (by rfl) ⟨123755, by rfl⟩ : syracuseStep 10560469 = 247511) (by norm_num)
theorem B2057197 : Blo 1827615 2057197 := bbase (se 3 (by rfl) ⟨385724, by rfl⟩ : syracuseStep 2057197 = 771449) (by norm_num)
theorem B2196481 : Blo 1827615 2196481 := bbase (se 2 (by rfl) ⟨823680, by rfl⟩ : syracuseStep 2196481 = 1647361) (by norm_num)
theorem B4113413 : Blo 1827615 4113413 := bbase (se 4 (by rfl) ⟨385632, by rfl⟩ : syracuseStep 4113413 = 771265) (by norm_num)
theorem B2057233 : Blo 1827615 2057233 := bbase (se 2 (by rfl) ⟨771462, by rfl⟩ : syracuseStep 2057233 = 1542925) (by norm_num)
theorem B6939701 : Blo 1827615 6939701 := bbase (se 5 (by rfl) ⟨325298, by rfl⟩ : syracuseStep 6939701 = 650597) (by norm_num)
theorem B2057269 : Blo 1827615 2057269 := bbase (se 5 (by rfl) ⟨96434, by rfl⟩ : syracuseStep 2057269 = 192869) (by norm_num)
theorem B7808069 : Blo 1827615 7808069 := bbase (se 4 (by rfl) ⟨732006, by rfl⟩ : syracuseStep 7808069 = 1464013) (by norm_num)
theorem B4113485 : Blo 1827615 4113485 := bbase (se 3 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 4113485 = 1542557) (by norm_num)
theorem B9880661 : Blo 1827615 9880661 := bbase (se 8 (by rfl) ⟨57894, by rfl⟩ : syracuseStep 9880661 = 115789) (by norm_num)
theorem B2057305 : Blo 1827615 2057305 := bbase (se 2 (by rfl) ⟨771489, by rfl⟩ : syracuseStep 2057305 = 1542979) (by norm_num)
theorem B2057341 : Blo 1827615 2057341 := bbase (se 3 (by rfl) ⟨385751, by rfl⟩ : syracuseStep 2057341 = 771503) (by norm_num)
theorem B4392077 : Blo 1827615 4392077 := bbase (se 3 (by rfl) ⟨823514, by rfl⟩ : syracuseStep 4392077 = 1647029) (by norm_num)
theorem B4113557 : Blo 1827615 4113557 := bbase (se 6 (by rfl) ⟨96411, by rfl⟩ : syracuseStep 4113557 = 192823) (by norm_num)
theorem B2057377 : Blo 1827615 2057377 := bbase (se 2 (by rfl) ⟨771516, by rfl⟩ : syracuseStep 2057377 = 1543033) (by norm_num)
theorem B2057413 : Blo 1827615 2057413 := bbase (se 4 (by rfl) ⟨192882, by rfl⟩ : syracuseStep 2057413 = 385765) (by norm_num)
theorem B15623381 : Blo 1827615 15623381 := bbase (se 7 (by rfl) ⟨183086, by rfl⟩ : syracuseStep 15623381 = 366173) (by norm_num)
theorem B4113629 : Blo 1827615 4113629 := bbase (se 3 (by rfl) ⟨771305, by rfl⟩ : syracuseStep 4113629 = 1542611) (by norm_num)
theorem B2057449 : Blo 1827615 2057449 := bbase (se 2 (by rfl) ⟨771543, by rfl⟩ : syracuseStep 2057449 = 1543087) (by norm_num)
theorem B4629757 : Blo 1827615 4629757 := bbase (se 3 (by rfl) ⟨868079, by rfl⟩ : syracuseStep 4629757 = 1736159) (by norm_num)
theorem B2057485 : Blo 1827615 2057485 := bbase (se 3 (by rfl) ⟨385778, by rfl⟩ : syracuseStep 2057485 = 771557) (by norm_num)
theorem B6169877 : Blo 1827615 6169877 := bbase (se 6 (by rfl) ⟨144606, by rfl⟩ : syracuseStep 6169877 = 289213) (by norm_num)
theorem B4113701 : Blo 1827615 4113701 := bbase (se 4 (by rfl) ⟨385659, by rfl⟩ : syracuseStep 4113701 = 771319) (by norm_num)
theorem B2057521 : Blo 1827615 2057521 := bbase (se 2 (by rfl) ⟨771570, by rfl⟩ : syracuseStep 2057521 = 1543141) (by norm_num)
theorem B7808309 : Blo 1827615 7808309 := bbase (se 5 (by rfl) ⟨366014, by rfl⟩ : syracuseStep 7808309 = 732029) (by norm_num)
theorem B6939989 : Blo 1827615 6939989 := bbase (se 12 (by rfl) ⟨2541, by rfl⟩ : syracuseStep 6939989 = 5083) (by norm_num)
theorem B2057557 : Blo 1827615 2057557 := bbase (se 12 (by rfl) ⟨753, by rfl⟩ : syracuseStep 2057557 = 1507) (by norm_num)
theorem B4113773 : Blo 1827615 4113773 := bbase (se 3 (by rfl) ⟨771332, by rfl⟩ : syracuseStep 4113773 = 1542665) (by norm_num)
theorem B4629869 : Blo 1827615 4629869 := bbase (se 3 (by rfl) ⟨868100, by rfl⟩ : syracuseStep 4629869 = 1736201) (by norm_num)
theorem B2057593 : Blo 1827615 2057593 := bbase (se 2 (by rfl) ⟨771597, by rfl⟩ : syracuseStep 2057593 = 1543195) (by norm_num)
theorem B5858693 : Blo 1827615 5858693 := bbase (se 4 (by rfl) ⟨549252, by rfl⟩ : syracuseStep 5858693 = 1098505) (by norm_num)
theorem B2057629 : Blo 1827615 2057629 := bbase (se 3 (by rfl) ⟨385805, by rfl⟩ : syracuseStep 2057629 = 771611) (by norm_num)
theorem B4113845 : Blo 1827615 4113845 := bbase (se 5 (by rfl) ⟨192836, by rfl⟩ : syracuseStep 4113845 = 385673) (by norm_num)
theorem B2057665 : Blo 1827615 2057665 := bbase (se 2 (by rfl) ⟨771624, by rfl⟩ : syracuseStep 2057665 = 1543249) (by norm_num)
theorem B2057701 : Blo 1827615 2057701 := bbase (se 4 (by rfl) ⟨192909, by rfl⟩ : syracuseStep 2057701 = 385819) (by norm_num)
theorem B4113917 : Blo 1827615 4113917 := bbase (se 3 (by rfl) ⟨771359, by rfl⟩ : syracuseStep 4113917 = 1542719) (by norm_num)
theorem B2057737 : Blo 1827615 2057737 := bbase (se 2 (by rfl) ⟨771651, by rfl⟩ : syracuseStep 2057737 = 1543303) (by norm_num)
theorem B2057773 : Blo 1827615 2057773 := bbase (se 3 (by rfl) ⟨385832, by rfl⟩ : syracuseStep 2057773 = 771665) (by norm_num)
theorem B4630061 : Blo 1827615 4630061 := bbase (se 3 (by rfl) ⟨868136, by rfl⟩ : syracuseStep 4630061 = 1736273) (by norm_num)
theorem B4113989 : Blo 1827615 4113989 := bbase (se 4 (by rfl) ⟨385686, by rfl⟩ : syracuseStep 4113989 = 771373) (by norm_num)
theorem B2057809 : Blo 1827615 2057809 := bbase (se 2 (by rfl) ⟨771678, by rfl⟩ : syracuseStep 2057809 = 1543357) (by norm_num)
theorem B2057845 : Blo 1827615 2057845 := bbase (se 5 (by rfl) ⟨96461, by rfl⟩ : syracuseStep 2057845 = 192923) (by norm_num)
theorem B4114061 : Blo 1827615 4114061 := bbase (se 3 (by rfl) ⟨771386, by rfl⟩ : syracuseStep 4114061 = 1542773) (by norm_num)
theorem B2057881 : Blo 1827615 2057881 := bbase (se 2 (by rfl) ⟨771705, by rfl⟩ : syracuseStep 2057881 = 1543411) (by norm_num)
theorem B2057917 : Blo 1827615 2057917 := bbase (se 3 (by rfl) ⟨385859, by rfl⟩ : syracuseStep 2057917 = 771719) (by norm_num)
theorem B6170309 : Blo 1827615 6170309 := bbase (se 4 (by rfl) ⟨578466, by rfl⟩ : syracuseStep 6170309 = 1156933) (by norm_num)
theorem B4114133 : Blo 1827615 4114133 := bbase (se 7 (by rfl) ⟨48212, by rfl⟩ : syracuseStep 4114133 = 96425) (by norm_num)
theorem B2057953 : Blo 1827615 2057953 := bbase (se 2 (by rfl) ⟨771732, by rfl⟩ : syracuseStep 2057953 = 1543465) (by norm_num)
theorem B7415525 : Blo 1827615 7415525 := bbase (se 4 (by rfl) ⟨695205, by rfl⟩ : syracuseStep 7415525 = 1390411) (by norm_num)
theorem B2057989 : Blo 1827615 2057989 := bbase (se 4 (by rfl) ⟨192936, by rfl⟩ : syracuseStep 2057989 = 385873) (by norm_num)
theorem B4114205 : Blo 1827615 4114205 := bbase (se 3 (by rfl) ⟨771413, by rfl⟩ : syracuseStep 4114205 = 1542827) (by norm_num)
theorem B2058025 : Blo 1827615 2058025 := bbase (se 2 (by rfl) ⟨771759, by rfl⟩ : syracuseStep 2058025 = 1543519) (by norm_num)
theorem B2058061 : Blo 1827615 2058061 := bbase (se 3 (by rfl) ⟨385886, by rfl⟩ : syracuseStep 2058061 = 771773) (by norm_num)
theorem B4114277 : Blo 1827615 4114277 := bbase (se 4 (by rfl) ⟨385713, by rfl⟩ : syracuseStep 4114277 = 771427) (by norm_num)
theorem B2058097 : Blo 1827615 2058097 := bbase (se 2 (by rfl) ⟨771786, by rfl⟩ : syracuseStep 2058097 = 1543573) (by norm_num)
theorem B4630405 : Blo 1827615 4630405 := bbase (se 4 (by rfl) ⟨434100, by rfl⟩ : syracuseStep 4630405 = 868201) (by norm_num)
theorem B2058133 : Blo 1827615 2058133 := bbase (se 6 (by rfl) ⟨48237, by rfl⟩ : syracuseStep 2058133 = 96475) (by norm_num)
theorem B4229029 : Blo 1827615 4229029 := bbase (se 4 (by rfl) ⟨396471, by rfl⟩ : syracuseStep 4229029 = 792943) (by norm_num)
theorem B4114349 : Blo 1827615 4114349 := bbase (se 3 (by rfl) ⟨771440, by rfl⟩ : syracuseStep 4114349 = 1542881) (by norm_num)
theorem B2058169 : Blo 1827615 2058169 := bbase (se 2 (by rfl) ⟨771813, by rfl⟩ : syracuseStep 2058169 = 1543627) (by norm_num)
theorem B2058205 : Blo 1827615 2058205 := bbase (se 3 (by rfl) ⟨385913, by rfl⟩ : syracuseStep 2058205 = 771827) (by norm_num)
theorem B4114421 : Blo 1827615 4114421 := bbase (se 5 (by rfl) ⟨192863, by rfl⟩ : syracuseStep 4114421 = 385727) (by norm_num)
theorem B4630517 : Blo 1827615 4630517 := bbase (se 5 (by rfl) ⟨217055, by rfl⟩ : syracuseStep 4630517 = 434111) (by norm_num)
theorem B2058241 : Blo 1827615 2058241 := bbase (se 2 (by rfl) ⟨771840, by rfl⟩ : syracuseStep 2058241 = 1543681) (by norm_num)
theorem B2058277 : Blo 1827615 2058277 := bbase (se 4 (by rfl) ⟨192963, by rfl⟩ : syracuseStep 2058277 = 385927) (by norm_num)
theorem B2345017 : Blo 1827615 2345017 := bbase (se 2 (by rfl) ⟨879381, by rfl⟩ : syracuseStep 2345017 = 1758763) (by norm_num)
theorem B4114493 : Blo 1827615 4114493 := bbase (se 3 (by rfl) ⟨771467, by rfl⟩ : syracuseStep 4114493 = 1542935) (by norm_num)
theorem B1878089 : Blo 1827615 1878089 := bbase (se 2 (by rfl) ⟨704283, by rfl⟩ : syracuseStep 1878089 = 1408567) (by norm_num)
theorem B2058313 : Blo 1827615 2058313 := bbase (se 2 (by rfl) ⟨771867, by rfl⟩ : syracuseStep 2058313 = 1543735) (by norm_num)
theorem B1853533 : Blo 1827615 1853533 := bbase (se 3 (by rfl) ⟨347537, by rfl⟩ : syracuseStep 1853533 = 695075) (by norm_num)
theorem B9259109 : Blo 1827615 9259109 := bbase (se 4 (by rfl) ⟨868041, by rfl⟩ : syracuseStep 9259109 = 1736083) (by norm_num)
theorem B6170741 : Blo 1827615 6170741 := bbase (se 5 (by rfl) ⟨289253, by rfl⟩ : syracuseStep 6170741 = 578507) (by norm_num)
theorem B4114565 : Blo 1827615 4114565 := bbase (se 4 (by rfl) ⟨385740, by rfl⟩ : syracuseStep 4114565 = 771481) (by norm_num)
theorem B1853585 : Blo 1827615 1853585 := bbase (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) (by norm_num)
theorem B4630709 : Blo 1827615 4630709 := bbase (se 5 (by rfl) ⟨217064, by rfl⟩ : syracuseStep 4630709 = 434129) (by norm_num)
theorem B1951949 : Blo 1827615 1951949 := bbase (se 3 (by rfl) ⟨365990, by rfl⟩ : syracuseStep 1951949 = 731981) (by norm_num)
theorem B4114637 : Blo 1827615 4114637 := bbase (se 3 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 4114637 = 1542989) (by norm_num)
theorem B4114709 : Blo 1827615 4114709 := bbase (se 6 (by rfl) ⟨96438, by rfl⟩ : syracuseStep 4114709 = 192877) (by norm_num)
theorem B5007653 : Blo 1827615 5007653 := bbase (se 4 (by rfl) ⟨469467, by rfl⟩ : syracuseStep 5007653 = 938935) (by norm_num)
theorem B4114781 : Blo 1827615 4114781 := bbase (se 3 (by rfl) ⟨771521, by rfl⟩ : syracuseStep 4114781 = 1543043) (by norm_num)
theorem B2197865 : Blo 1827615 2197865 := bbase (se 2 (by rfl) ⟨824199, by rfl⟩ : syracuseStep 2197865 = 1648399) (by norm_num)
theorem B1853813 : Blo 1827615 1853813 := bbase (se 5 (by rfl) ⟨86897, by rfl⟩ : syracuseStep 1853813 = 173795) (by norm_num)
theorem B1952137 : Blo 1827615 1952137 := bbase (se 2 (by rfl) ⟨732051, by rfl⟩ : syracuseStep 1952137 = 1464103) (by norm_num)
theorem B4114853 : Blo 1827615 4114853 := bbase (se 4 (by rfl) ⟨385767, by rfl⟩ : syracuseStep 4114853 = 771535) (by norm_num)
theorem B4114925 : Blo 1827615 4114925 := bbase (se 3 (by rfl) ⟨771548, by rfl⟩ : syracuseStep 4114925 = 1543097) (by norm_num)
theorem B6941173 : Blo 1827615 6941173 := bbase (se 5 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 6941173 = 650735) (by norm_num)
theorem B4631053 : Blo 1827615 4631053 := bbase (se 3 (by rfl) ⟨868322, by rfl⟩ : syracuseStep 4631053 = 1736645) (by norm_num)
theorem B6171173 : Blo 1827615 6171173 := bbase (se 4 (by rfl) ⟨578547, by rfl⟩ : syracuseStep 6171173 = 1157095) (by norm_num)
theorem B5712437 : Blo 1827615 5712437 := bbase (se 5 (by rfl) ⟨267770, by rfl⟩ : syracuseStep 5712437 = 535541) (by norm_num)
theorem B4114997 : Blo 1827615 4114997 := bbase (se 5 (by rfl) ⟨192890, by rfl⟩ : syracuseStep 4114997 = 385781) (by norm_num)
theorem B4115069 : Blo 1827615 4115069 := bbase (se 3 (by rfl) ⟨771575, by rfl⟩ : syracuseStep 4115069 = 1543151) (by norm_num)
theorem B4631165 : Blo 1827615 4631165 := bbase (se 3 (by rfl) ⟨868343, by rfl⟩ : syracuseStep 4631165 = 1736687) (by norm_num)
theorem B5638805 : Blo 1827615 5638805 := bbase (se 6 (by rfl) ⟨132159, by rfl⟩ : syracuseStep 5638805 = 264319) (by norm_num)
theorem B4115141 : Blo 1827615 4115141 := bbase (se 4 (by rfl) ⟨385794, by rfl⟩ : syracuseStep 4115141 = 771589) (by norm_num)
theorem B1854149 : Blo 1827615 1854149 := bbase (se 4 (by rfl) ⟨173826, by rfl⟩ : syracuseStep 1854149 = 347653) (by norm_num)
theorem B4238021 : Blo 1827615 4238021 := bbase (se 4 (by rfl) ⟨397314, by rfl⟩ : syracuseStep 4238021 = 794629) (by norm_num)
theorem B4115213 : Blo 1827615 4115213 := bbase (se 3 (by rfl) ⟨771602, by rfl⟩ : syracuseStep 4115213 = 1543205) (by norm_num)
theorem B6941477 : Blo 1827615 6941477 := bbase (se 4 (by rfl) ⟨650763, by rfl⟩ : syracuseStep 6941477 = 1301527) (by norm_num)
theorem B4115285 : Blo 1827615 4115285 := bbase (se 9 (by rfl) ⟨12056, by rfl⟩ : syracuseStep 4115285 = 24113) (by norm_num)
theorem B13732757 : Blo 1827615 13732757 := bbase (se 6 (by rfl) ⟨321861, by rfl⟩ : syracuseStep 13732757 = 643723) (by norm_num)
theorem B4393885 : Blo 1827615 4393885 := bbase (se 3 (by rfl) ⟨823853, by rfl⟩ : syracuseStep 4393885 = 1647707) (by norm_num)
theorem B4115357 : Blo 1827615 4115357 := bbase (se 3 (by rfl) ⟨771629, by rfl⟩ : syracuseStep 4115357 = 1543259) (by norm_num)
theorem B2313137 : Blo 1827615 2313137 := bbase (se 2 (by rfl) ⟨867426, by rfl⟩ : syracuseStep 2313137 = 1734853) (by norm_num)
theorem B6171605 : Blo 1827615 6171605 := bbase (se 7 (by rfl) ⟨72323, by rfl⟩ : syracuseStep 6171605 = 144647) (by norm_num)
theorem B4115429 : Blo 1827615 4115429 := bbase (se 4 (by rfl) ⟨385821, by rfl⟩ : syracuseStep 4115429 = 771643) (by norm_num)
theorem B2313193 : Blo 1827615 2313193 := bbase (se 2 (by rfl) ⟨867447, by rfl⟩ : syracuseStep 2313193 = 1734895) (by norm_num)
theorem B4115501 : Blo 1827615 4115501 := bbase (se 3 (by rfl) ⟨771656, by rfl⟩ : syracuseStep 4115501 = 1543313) (by norm_num)
theorem B14822453 : Blo 1827615 14822453 := bbase (se 5 (by rfl) ⟨694802, by rfl⟩ : syracuseStep 14822453 = 1389605) (by norm_num)
theorem B2313289 : Blo 1827615 2313289 := bbase (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) (by norm_num)
theorem B2927693 : Blo 1827615 2927693 := bbase (se 3 (by rfl) ⟨548942, by rfl⟩ : syracuseStep 2927693 = 1097885) (by norm_num)
theorem B3386453 : Blo 1827615 3386453 := bbase (se 8 (by rfl) ⟨19842, by rfl⟩ : syracuseStep 3386453 = 39685) (by norm_num)
theorem B4115573 : Blo 1827615 4115573 := bbase (se 5 (by rfl) ⟨192917, by rfl⟩ : syracuseStep 4115573 = 385835) (by norm_num)
theorem B1952957 : Blo 1827615 1952957 := bbase (se 3 (by rfl) ⟨366179, by rfl⟩ : syracuseStep 1952957 = 732359) (by norm_num)
theorem B4115645 : Blo 1827615 4115645 := bbase (se 3 (by rfl) ⟨771683, by rfl⟩ : syracuseStep 4115645 = 1543367) (by norm_num)
theorem B2927821 : Blo 1827615 2927821 := bbase (se 3 (by rfl) ⟨548966, by rfl⟩ : syracuseStep 2927821 = 1097933) (by norm_num)
theorem B3706069 : Blo 1827615 3706069 := bbase (se 7 (by rfl) ⟨43430, by rfl⟩ : syracuseStep 3706069 = 86861) (by norm_num)
theorem B2313461 : Blo 1827615 2313461 := bbase (se 5 (by rfl) ⟨108443, by rfl⟩ : syracuseStep 2313461 = 216887) (by norm_num)
theorem B4115717 : Blo 1827615 4115717 := bbase (se 4 (by rfl) ⟨385848, by rfl⟩ : syracuseStep 4115717 = 771697) (by norm_num)
theorem B2313517 : Blo 1827615 2313517 := bbase (se 3 (by rfl) ⟨433784, by rfl⟩ : syracuseStep 2313517 = 867569) (by norm_num)
theorem B2780477 : Blo 1827615 2780477 := bbase (se 3 (by rfl) ⟨521339, by rfl⟩ : syracuseStep 2780477 = 1042679) (by norm_num)
theorem B4115789 : Blo 1827615 4115789 := bbase (se 3 (by rfl) ⟨771710, by rfl⟩ : syracuseStep 4115789 = 1543421) (by norm_num)
theorem B9260405 : Blo 1827615 9260405 := bbase (se 5 (by rfl) ⟨434081, by rfl⟩ : syracuseStep 9260405 = 868163) (by norm_num)
theorem B6172037 : Blo 1827615 6172037 := bbase (se 4 (by rfl) ⟨578628, by rfl⟩ : syracuseStep 6172037 = 1157257) (by norm_num)
theorem B2313613 : Blo 1827615 2313613 := bbase (se 3 (by rfl) ⟨433802, by rfl⟩ : syracuseStep 2313613 = 867605) (by norm_num)
theorem B4115861 : Blo 1827615 4115861 := bbase (se 6 (by rfl) ⟨96465, by rfl⟩ : syracuseStep 4115861 = 192931) (by norm_num)
theorem B4394405 : Blo 1827615 4394405 := bbase (se 4 (by rfl) ⟨411975, by rfl⟩ : syracuseStep 4394405 = 823951) (by norm_num)
theorem B3517877 : Blo 1827615 3517877 := bbase (se 5 (by rfl) ⟨164900, by rfl⟩ : syracuseStep 3517877 = 329801) (by norm_num)
theorem B4115933 : Blo 1827615 4115933 := bbase (se 3 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 4115933 = 1543475) (by norm_num)
theorem B7810597 : Blo 1827615 7810597 := bbase (se 4 (by rfl) ⟨732243, by rfl⟩ : syracuseStep 7810597 = 1464487) (by norm_num)
theorem B4116005 : Blo 1827615 4116005 := bbase (se 4 (by rfl) ⟨385875, by rfl⟩ : syracuseStep 4116005 = 771751) (by norm_num)
theorem B2313785 : Blo 1827615 2313785 := bbase (se 2 (by rfl) ⟨867669, by rfl⟩ : syracuseStep 2313785 = 1735339) (by norm_num)
theorem B8343125 : Blo 1827615 8343125 := bbase (se 8 (by rfl) ⟨48885, by rfl⟩ : syracuseStep 8343125 = 97771) (by norm_num)
theorem B4116077 : Blo 1827615 4116077 := bbase (se 3 (by rfl) ⟨771764, by rfl⟩ : syracuseStep 4116077 = 1543529) (by norm_num)
theorem B2313841 : Blo 1827615 2313841 := bbase (se 2 (by rfl) ⟨867690, by rfl⟩ : syracuseStep 2313841 = 1735381) (by norm_num)
theorem B1953401 : Blo 1827615 1953401 := bbase (se 2 (by rfl) ⟨732525, by rfl⟩ : syracuseStep 1953401 = 1465051) (by norm_num)
theorem B5205653 : Blo 1827615 5205653 := bbase (se 6 (by rfl) ⟨122007, by rfl⟩ : syracuseStep 5205653 = 244015) (by norm_num)
theorem B4116149 : Blo 1827615 4116149 := bbase (se 5 (by rfl) ⟨192944, by rfl⟩ : syracuseStep 4116149 = 385889) (by norm_num)
theorem B2313937 : Blo 1827615 2313937 := bbase (se 2 (by rfl) ⟨867726, by rfl⟩ : syracuseStep 2313937 = 1735453) (by norm_num)
theorem B10415861 : Blo 1827615 10415861 := bbase (se 5 (by rfl) ⟨488243, by rfl⟩ : syracuseStep 10415861 = 976487) (by norm_num)
theorem B4116221 : Blo 1827615 4116221 := bbase (se 3 (by rfl) ⟨771791, by rfl⟩ : syracuseStep 4116221 = 1543583) (by norm_num)
theorem B5713669 : Blo 1827615 5713669 := bbase (se 4 (by rfl) ⟨535656, by rfl⟩ : syracuseStep 5713669 = 1071313) (by norm_num)
theorem B9252629 : Blo 1827615 9252629 := bbase (se 6 (by rfl) ⟨216858, by rfl⟩ : syracuseStep 9252629 = 433717) (by norm_num)
theorem B4394789 : Blo 1827615 4394789 := bbase (se 4 (by rfl) ⟨412011, by rfl⟩ : syracuseStep 4394789 = 824023) (by norm_num)
theorem B6172469 : Blo 1827615 6172469 := bbase (se 5 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 6172469 = 578669) (by norm_num)
theorem B4116293 : Blo 1827615 4116293 := bbase (se 4 (by rfl) ⟨385902, by rfl⟩ : syracuseStep 4116293 = 771805) (by norm_num)
theorem B3903317 : Blo 1827615 3903317 := bbase (se 9 (by rfl) ⟨11435, by rfl⟩ : syracuseStep 3903317 = 22871) (by norm_num)
theorem B240422741 : Blo 1827615 240422741 := bbase (se 9 (by rfl) ⟨704363, by rfl⟩ : syracuseStep 240422741 = 1408727) (by norm_num)
theorem B4394837 : Blo 1827615 4394837 := bbase (se 9 (by rfl) ⟨12875, by rfl⟩ : syracuseStep 4394837 = 25751) (by norm_num)
theorem B4394845 : Blo 1827615 4394845 := bbase (se 3 (by rfl) ⟨824033, by rfl⟩ : syracuseStep 4394845 = 1648067) (by norm_num)
theorem B3518309 : Blo 1827615 3518309 := bbase (se 4 (by rfl) ⟨329841, by rfl⟩ : syracuseStep 3518309 = 659683) (by norm_num)
theorem B1953649 : Blo 1827615 1953649 := bbase (se 2 (by rfl) ⟨732618, by rfl⟩ : syracuseStep 1953649 = 1465237) (by norm_num)
theorem B3084149 : Blo 1827615 3084149 := bbase (se 5 (by rfl) ⟨144569, by rfl⟩ : syracuseStep 3084149 = 289139) (by norm_num)
theorem B2314109 : Blo 1827615 2314109 := bbase (se 3 (by rfl) ⟨433895, by rfl⟩ : syracuseStep 2314109 = 867791) (by norm_num)
theorem B4116365 : Blo 1827615 4116365 := bbase (se 3 (by rfl) ⟨771818, by rfl⟩ : syracuseStep 4116365 = 1543637) (by norm_num)
theorem B2314165 : Blo 1827615 2314165 := bbase (se 5 (by rfl) ⟨108476, by rfl⟩ : syracuseStep 2314165 = 216953) (by norm_num)
theorem B4116437 : Blo 1827615 4116437 := bbase (se 7 (by rfl) ⟨48239, by rfl⟩ : syracuseStep 4116437 = 96479) (by norm_num)
theorem B3706853 : Blo 1827615 3706853 := bbase (se 4 (by rfl) ⟨347517, by rfl⟩ : syracuseStep 3706853 = 695035) (by norm_num)
theorem B3084277 : Blo 1827615 3084277 := bbase (se 5 (by rfl) ⟨144575, by rfl⟩ : syracuseStep 3084277 = 289151) (by norm_num)
theorem B2928629 : Blo 1827615 2928629 := bbase (se 5 (by rfl) ⟨137279, by rfl⟩ : syracuseStep 2928629 = 274559) (by norm_num)
theorem B2314261 : Blo 1827615 2314261 := bbase (se 6 (by rfl) ⟨54240, by rfl⟩ : syracuseStep 2314261 = 108481) (by norm_num)
theorem B4116509 : Blo 1827615 4116509 := bbase (se 3 (by rfl) ⟨771845, by rfl⟩ : syracuseStep 4116509 = 1543691) (by norm_num)
theorem B3084365 : Blo 1827615 3084365 := bbase (se 3 (by rfl) ⟨578318, by rfl⟩ : syracuseStep 3084365 = 1156637) (by norm_num)
theorem B3518549 : Blo 1827615 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B4116581 : Blo 1827615 4116581 := bbase (se 4 (by rfl) ⟨385929, by rfl⟩ : syracuseStep 4116581 = 771859) (by norm_num)
theorem B15626357 : Blo 1827615 15626357 := bbase (se 5 (by rfl) ⟨732485, by rfl⟩ : syracuseStep 15626357 = 1464971) (by norm_num)
theorem B2314433 : Blo 1827615 2314433 := bbase (se 2 (by rfl) ⟨867912, by rfl⟩ : syracuseStep 2314433 = 1735825) (by norm_num)
theorem B3084493 : Blo 1827615 3084493 := bbase (se 3 (by rfl) ⟨578342, by rfl⟩ : syracuseStep 3084493 = 1156685) (by norm_num)
theorem B3518677 : Blo 1827615 3518677 := bbase (se 7 (by rfl) ⟨41234, by rfl⟩ : syracuseStep 3518677 = 82469) (by norm_num)
theorem B6172901 : Blo 1827615 6172901 := bbase (se 4 (by rfl) ⟨578709, by rfl⟩ : syracuseStep 6172901 = 1157419) (by norm_num)
theorem B2314489 : Blo 1827615 2314489 := bbase (se 2 (by rfl) ⟨867933, by rfl⟩ : syracuseStep 2314489 = 1735867) (by norm_num)
theorem B2928917 : Blo 1827615 2928917 := bbase (se 6 (by rfl) ⟨68646, by rfl⟩ : syracuseStep 2928917 = 137293) (by norm_num)
theorem B3084581 : Blo 1827615 3084581 := bbase (se 4 (by rfl) ⟨289179, by rfl⟩ : syracuseStep 3084581 = 578359) (by norm_num)
theorem B3469645 : Blo 1827615 3469645 := bbase (se 3 (by rfl) ⟨650558, by rfl⟩ : syracuseStep 3469645 = 1301117) (by norm_num)
theorem B2085197 : Blo 1827615 2085197 := bbase (se 3 (by rfl) ⟨390974, by rfl⟩ : syracuseStep 2085197 = 781949) (by norm_num)
theorem B2314585 : Blo 1827615 2314585 := bbase (se 2 (by rfl) ⟨867969, by rfl⟩ : syracuseStep 2314585 = 1735939) (by norm_num)
theorem B3567997 : Blo 1827615 3567997 := bbase (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) (by norm_num)
theorem B3084709 : Blo 1827615 3084709 := bbase (se 4 (by rfl) ⟨289191, by rfl⟩ : syracuseStep 3084709 = 578383) (by norm_num)
theorem B3084797 : Blo 1827615 3084797 := bbase (se 3 (by rfl) ⟨578399, by rfl⟩ : syracuseStep 3084797 = 1156799) (by norm_num)
theorem B2314757 : Blo 1827615 2314757 := bbase (se 4 (by rfl) ⟨217008, by rfl⟩ : syracuseStep 2314757 = 434017) (by norm_num)
theorem B2314813 : Blo 1827615 2314813 := bbase (se 3 (by rfl) ⟨434027, by rfl⟩ : syracuseStep 2314813 = 868055) (by norm_num)
theorem B8786501 : Blo 1827615 8786501 := bbase (se 4 (by rfl) ⟨823734, by rfl⟩ : syracuseStep 8786501 = 1647469) (by norm_num)
theorem B3469949 : Blo 1827615 3469949 := bbase (se 3 (by rfl) ⟨650615, by rfl⟩ : syracuseStep 3469949 = 1301231) (by norm_num)
theorem B3084925 : Blo 1827615 3084925 := bbase (se 3 (by rfl) ⟨578423, by rfl⟩ : syracuseStep 3084925 = 1156847) (by norm_num)
theorem B9261701 : Blo 1827615 9261701 := bbase (se 4 (by rfl) ⟨868284, by rfl⟩ : syracuseStep 9261701 = 1736569) (by norm_num)
theorem B6173333 : Blo 1827615 6173333 := bbase (se 6 (by rfl) ⟨144687, by rfl⟩ : syracuseStep 6173333 = 289375) (by norm_num)
theorem B2314909 : Blo 1827615 2314909 := bbase (se 3 (by rfl) ⟨434045, by rfl⟩ : syracuseStep 2314909 = 868091) (by norm_num)
theorem B2929333 : Blo 1827615 2929333 := bbase (se 5 (by rfl) ⟨137312, by rfl⟩ : syracuseStep 2929333 = 274625) (by norm_num)
theorem B12513973 : Blo 1827615 12513973 := bbase (se 5 (by rfl) ⟨586592, by rfl⟩ : syracuseStep 12513973 = 1173185) (by norm_num)
theorem B3904205 : Blo 1827615 3904205 := bbase (se 3 (by rfl) ⟨732038, by rfl⟩ : syracuseStep 3904205 = 1464077) (by norm_num)
theorem B3085013 : Blo 1827615 3085013 := bbase (se 7 (by rfl) ⟨36152, by rfl⟩ : syracuseStep 3085013 = 72305) (by norm_num)
theorem B3756773 : Blo 1827615 3756773 := bbase (se 4 (by rfl) ⟨352197, by rfl⟩ : syracuseStep 3756773 = 704395) (by norm_num)
theorem B7516901 : Blo 1827615 7516901 := bbase (se 4 (by rfl) ⟨704709, by rfl⟩ : syracuseStep 7516901 = 1409419) (by norm_num)
theorem B5206837 : Blo 1827615 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B4395845 : Blo 1827615 4395845 := bbase (se 4 (by rfl) ⟨412110, by rfl⟩ : syracuseStep 4395845 = 824221) (by norm_num)
theorem B2315081 : Blo 1827615 2315081 := bbase (se 2 (by rfl) ⟨868155, by rfl⟩ : syracuseStep 2315081 = 1736311) (by norm_num)
theorem B3085141 : Blo 1827615 3085141 := bbase (se 9 (by rfl) ⟨9038, by rfl⟩ : syracuseStep 3085141 = 18077) (by norm_num)
theorem B6943589 : Blo 1827615 6943589 := bbase (se 4 (by rfl) ⟨650961, by rfl⟩ : syracuseStep 6943589 = 1301923) (by norm_num)
theorem B2315137 : Blo 1827615 2315137 := bbase (se 2 (by rfl) ⟨868176, by rfl⟩ : syracuseStep 2315137 = 1736353) (by norm_num)
theorem B10417045 : Blo 1827615 10417045 := bbase (se 6 (by rfl) ⟨244149, by rfl⟩ : syracuseStep 10417045 = 488299) (by norm_num)
theorem B3085229 : Blo 1827615 3085229 := bbase (se 3 (by rfl) ⟨578480, by rfl⟩ : syracuseStep 3085229 = 1156961) (by norm_num)
theorem B3904445 : Blo 1827615 3904445 := bbase (se 3 (by rfl) ⟨732083, by rfl⟩ : syracuseStep 3904445 = 1464167) (by norm_num)
theorem B5206997 : Blo 1827615 5206997 := bbase (se 7 (by rfl) ⟨61019, by rfl⟩ : syracuseStep 5206997 = 122039) (by norm_num)
theorem B2315233 : Blo 1827615 2315233 := bbase (se 2 (by rfl) ⟨868212, by rfl⟩ : syracuseStep 2315233 = 1736425) (by norm_num)
theorem B7812085 : Blo 1827615 7812085 := bbase (se 5 (by rfl) ⟨366191, by rfl⟩ : syracuseStep 7812085 = 732383) (by norm_num)
theorem B7812101 : Blo 1827615 7812101 := bbase (se 4 (by rfl) ⟨732384, by rfl⟩ : syracuseStep 7812101 = 1464769) (by norm_num)
theorem B4396037 : Blo 1827615 4396037 := bbase (se 4 (by rfl) ⟨412128, by rfl⟩ : syracuseStep 4396037 = 824257) (by norm_num)
theorem B2470933 : Blo 1827615 2470933 := bbase (se 6 (by rfl) ⟨57912, by rfl⟩ : syracuseStep 2470933 = 115825) (by norm_num)
theorem B9253925 : Blo 1827615 9253925 := bbase (se 4 (by rfl) ⟨867555, by rfl⟩ : syracuseStep 9253925 = 1735111) (by norm_num)
theorem B3085357 : Blo 1827615 3085357 := bbase (se 3 (by rfl) ⟨578504, by rfl⟩ : syracuseStep 3085357 = 1157009) (by norm_num)
theorem B3519533 : Blo 1827615 3519533 := bbase (se 3 (by rfl) ⟨659912, by rfl⟩ : syracuseStep 3519533 = 1319825) (by norm_num)
theorem B6173765 : Blo 1827615 6173765 := bbase (se 4 (by rfl) ⟨578790, by rfl⟩ : syracuseStep 6173765 = 1157581) (by norm_num)
theorem B6255701 : Blo 1827615 6255701 := bbase (se 8 (by rfl) ⟨36654, by rfl⟩ : syracuseStep 6255701 = 73309) (by norm_num)
theorem B3085445 : Blo 1827615 3085445 := bbase (se 4 (by rfl) ⟨289260, by rfl⟩ : syracuseStep 3085445 = 578521) (by norm_num)
theorem B6943877 : Blo 1827615 6943877 := bbase (se 4 (by rfl) ⟨650988, by rfl⟩ : syracuseStep 6943877 = 1301977) (by norm_num)
theorem B2315405 : Blo 1827615 2315405 := bbase (se 3 (by rfl) ⟨434138, by rfl⟩ : syracuseStep 2315405 = 868277) (by norm_num)
theorem B2741429 : Blo 1827615 2741429 := bbase (se 5 (by rfl) ⟨128504, by rfl⟩ : syracuseStep 2741429 = 257009) (by norm_num)
theorem B5207237 : Blo 1827615 5207237 := bbase (se 4 (by rfl) ⟨488178, by rfl⟩ : syracuseStep 5207237 = 976357) (by norm_num)
theorem B2315461 : Blo 1827615 2315461 := bbase (se 4 (by rfl) ⟨217074, by rfl⟩ : syracuseStep 2315461 = 434149) (by norm_num)
theorem B2741453 : Blo 1827615 2741453 := bbase (se 3 (by rfl) ⟨514022, by rfl⟩ : syracuseStep 2741453 = 1028045) (by norm_num)
theorem B2741477 : Blo 1827615 2741477 := bbase (se 4 (by rfl) ⟨257013, by rfl⟩ : syracuseStep 2741477 = 514027) (by norm_num)
theorem B2741501 : Blo 1827615 2741501 := bbase (se 3 (by rfl) ⟨514031, by rfl⟩ : syracuseStep 2741501 = 1028063) (by norm_num)
theorem B3085573 : Blo 1827615 3085573 := bbase (se 4 (by rfl) ⟨289272, by rfl⟩ : syracuseStep 3085573 = 578545) (by norm_num)
theorem B2741525 : Blo 1827615 2741525 := bbase (se 6 (by rfl) ⟨64254, by rfl⟩ : syracuseStep 2741525 = 128509) (by norm_num)
theorem B2315557 : Blo 1827615 2315557 := bbase (se 4 (by rfl) ⟨217083, by rfl⟩ : syracuseStep 2315557 = 434167) (by norm_num)
theorem B2741549 : Blo 1827615 2741549 := bbase (se 3 (by rfl) ⟨514040, by rfl⟩ : syracuseStep 2741549 = 1028081) (by norm_num)
theorem B2741573 : Blo 1827615 2741573 := bbase (se 4 (by rfl) ⟨257022, by rfl⟩ : syracuseStep 2741573 = 514045) (by norm_num)
theorem B2602325 : Blo 1827615 2602325 := bbase (se 13 (by rfl) ⟨476, by rfl⟩ : syracuseStep 2602325 = 953) (by norm_num)
theorem B2741597 : Blo 1827615 2741597 := bbase (se 3 (by rfl) ⟨514049, by rfl⟩ : syracuseStep 2741597 = 1028099) (by norm_num)
theorem B3085661 : Blo 1827615 3085661 := bbase (se 3 (by rfl) ⟨578561, by rfl⟩ : syracuseStep 3085661 = 1157123) (by norm_num)
theorem B3470701 : Blo 1827615 3470701 := bbase (se 3 (by rfl) ⟨650756, by rfl⟩ : syracuseStep 3470701 = 1301513) (by norm_num)
theorem B2741621 : Blo 1827615 2741621 := bbase (se 5 (by rfl) ⟨128513, by rfl⟩ : syracuseStep 2741621 = 257027) (by norm_num)
theorem B5207429 : Blo 1827615 5207429 := bbase (se 4 (by rfl) ⟨488196, by rfl⟩ : syracuseStep 5207429 = 976393) (by norm_num)
theorem B2741645 : Blo 1827615 2741645 := bbase (se 3 (by rfl) ⟨514058, by rfl⟩ : syracuseStep 2741645 = 1028117) (by norm_num)
theorem B25367957 : Blo 1827615 25367957 := bbase (se 6 (by rfl) ⟨594561, by rfl⟩ : syracuseStep 25367957 = 1189123) (by norm_num)
theorem B2602405 : Blo 1827615 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B2741669 : Blo 1827615 2741669 := bbase (se 4 (by rfl) ⟨257031, by rfl⟩ : syracuseStep 2741669 = 514063) (by norm_num)
theorem B3904949 : Blo 1827615 3904949 := bbase (se 5 (by rfl) ⟨183044, by rfl⟩ : syracuseStep 3904949 = 366089) (by norm_num)
theorem B2741693 : Blo 1827615 2741693 := bbase (se 3 (by rfl) ⟨514067, by rfl⟩ : syracuseStep 2741693 = 1028135) (by norm_num)
theorem B3904957 : Blo 1827615 3904957 := bbase (se 3 (by rfl) ⟨732179, by rfl⟩ : syracuseStep 3904957 = 1464359) (by norm_num)
theorem B5559749 : Blo 1827615 5559749 := bbase (se 4 (by rfl) ⟨521226, by rfl⟩ : syracuseStep 5559749 = 1042453) (by norm_num)
theorem B4945349 : Blo 1827615 4945349 := bbase (se 4 (by rfl) ⟨463626, by rfl⟩ : syracuseStep 4945349 = 927253) (by norm_num)
theorem B2741717 : Blo 1827615 2741717 := bbase (se 7 (by rfl) ⟨32129, by rfl⟩ : syracuseStep 2741717 = 64259) (by norm_num)
theorem B3085789 : Blo 1827615 3085789 := bbase (se 3 (by rfl) ⟨578585, by rfl⟩ : syracuseStep 3085789 = 1157171) (by norm_num)
theorem B2741741 : Blo 1827615 2741741 := bbase (se 3 (by rfl) ⟨514076, by rfl⟩ : syracuseStep 2741741 = 1028153) (by norm_num)
theorem B6174197 : Blo 1827615 6174197 := bbase (se 5 (by rfl) ⟨289415, by rfl⟩ : syracuseStep 6174197 = 578831) (by norm_num)
theorem B3470845 : Blo 1827615 3470845 := bbase (se 3 (by rfl) ⟨650783, by rfl⟩ : syracuseStep 3470845 = 1301567) (by norm_num)
theorem B2741765 : Blo 1827615 2741765 := bbase (se 4 (by rfl) ⟨257040, by rfl⟩ : syracuseStep 2741765 = 514081) (by norm_num)
theorem B2602525 : Blo 1827615 2602525 := bbase (se 3 (by rfl) ⟨487973, by rfl⟩ : syracuseStep 2602525 = 975947) (by norm_num)
theorem B2741789 : Blo 1827615 2741789 := bbase (se 3 (by rfl) ⟨514085, by rfl⟩ : syracuseStep 2741789 = 1028171) (by norm_num)
theorem B2741813 : Blo 1827615 2741813 := bbase (se 5 (by rfl) ⟨128522, by rfl⟩ : syracuseStep 2741813 = 257045) (by norm_num)
theorem B11712053 : Blo 1827615 11712053 := bbase (se 5 (by rfl) ⟨549002, by rfl⟩ : syracuseStep 11712053 = 1098005) (by norm_num)
theorem B3085877 : Blo 1827615 3085877 := bbase (se 5 (by rfl) ⟨144650, by rfl⟩ : syracuseStep 3085877 = 289301) (by norm_num)
theorem B2741837 : Blo 1827615 2741837 := bbase (se 3 (by rfl) ⟨514094, by rfl⟩ : syracuseStep 2741837 = 1028189) (by norm_num)
theorem B2930269 : Blo 1827615 2930269 := bbase (se 3 (by rfl) ⟨549425, by rfl⟩ : syracuseStep 2930269 = 1098851) (by norm_num)
theorem B2741861 : Blo 1827615 2741861 := bbase (se 4 (by rfl) ⟨257049, by rfl⟩ : syracuseStep 2741861 = 514099) (by norm_num)
theorem B2602621 : Blo 1827615 2602621 := bbase (se 3 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 2602621 = 975983) (by norm_num)
theorem B2741885 : Blo 1827615 2741885 := bbase (se 3 (by rfl) ⟨514103, by rfl⟩ : syracuseStep 2741885 = 1028207) (by norm_num)
theorem B2741909 : Blo 1827615 2741909 := bbase (se 6 (by rfl) ⟨64263, by rfl⟩ : syracuseStep 2741909 = 128527) (by norm_num)
theorem B3471005 : Blo 1827615 3471005 := bbase (se 3 (by rfl) ⟨650813, by rfl⟩ : syracuseStep 3471005 = 1301627) (by norm_num)
theorem B2741933 : Blo 1827615 2741933 := bbase (se 3 (by rfl) ⟨514112, by rfl⟩ : syracuseStep 2741933 = 1028225) (by norm_num)
theorem B3086005 : Blo 1827615 3086005 := bbase (se 5 (by rfl) ⟨144656, by rfl⟩ : syracuseStep 3086005 = 289313) (by norm_num)
theorem B2741957 : Blo 1827615 2741957 := bbase (se 4 (by rfl) ⟨257058, by rfl⟩ : syracuseStep 2741957 = 514117) (by norm_num)
theorem B2741981 : Blo 1827615 2741981 := bbase (se 3 (by rfl) ⟨514121, by rfl⟩ : syracuseStep 2741981 = 1028243) (by norm_num)
theorem B2742005 : Blo 1827615 2742005 := bbase (se 5 (by rfl) ⟨128531, by rfl⟩ : syracuseStep 2742005 = 257063) (by norm_num)
theorem B4626173 : Blo 1827615 4626173 := bbase (se 3 (by rfl) ⟨867407, by rfl⟩ : syracuseStep 4626173 = 1734815) (by norm_num)
theorem B2742029 : Blo 1827615 2742029 := bbase (se 3 (by rfl) ⟨514130, by rfl⟩ : syracuseStep 2742029 = 1028261) (by norm_num)
theorem B3086093 : Blo 1827615 3086093 := bbase (se 3 (by rfl) ⟨578642, by rfl⟩ : syracuseStep 3086093 = 1157285) (by norm_num)
theorem B7034645 : Blo 1827615 7034645 := bbase (se 6 (by rfl) ⟨164874, by rfl⟩ : syracuseStep 7034645 = 329749) (by norm_num)
theorem B2742053 : Blo 1827615 2742053 := bbase (se 4 (by rfl) ⟨257067, by rfl⟩ : syracuseStep 2742053 = 514135) (by norm_num)
theorem B3471149 : Blo 1827615 3471149 := bbase (se 3 (by rfl) ⟨650840, by rfl⟩ : syracuseStep 3471149 = 1301681) (by norm_num)
theorem B2742077 : Blo 1827615 2742077 := bbase (se 3 (by rfl) ⟨514139, by rfl⟩ : syracuseStep 2742077 = 1028279) (by norm_num)
theorem B2742101 : Blo 1827615 2742101 := bbase (se 9 (by rfl) ⟨8033, by rfl⟩ : syracuseStep 2742101 = 16067) (by norm_num)
theorem B2742125 : Blo 1827615 2742125 := bbase (se 3 (by rfl) ⟨514148, by rfl⟩ : syracuseStep 2742125 = 1028297) (by norm_num)
theorem B2742149 : Blo 1827615 2742149 := bbase (se 4 (by rfl) ⟨257076, by rfl⟩ : syracuseStep 2742149 = 514153) (by norm_num)
theorem B8787845 : Blo 1827615 8787845 := bbase (se 4 (by rfl) ⟨823860, by rfl⟩ : syracuseStep 8787845 = 1647721) (by norm_num)
theorem B3086221 : Blo 1827615 3086221 := bbase (se 3 (by rfl) ⟨578666, by rfl⟩ : syracuseStep 3086221 = 1157333) (by norm_num)
theorem B2742173 : Blo 1827615 2742173 := bbase (se 3 (by rfl) ⟨514157, by rfl⟩ : syracuseStep 2742173 = 1028315) (by norm_num)
theorem B6174629 : Blo 1827615 6174629 := bbase (se 4 (by rfl) ⟨578871, by rfl⟩ : syracuseStep 6174629 = 1157743) (by norm_num)
theorem B2742197 : Blo 1827615 2742197 := bbase (se 5 (by rfl) ⟨128540, by rfl⟩ : syracuseStep 2742197 = 257081) (by norm_num)
theorem B2742221 : Blo 1827615 2742221 := bbase (se 3 (by rfl) ⟨514166, by rfl⟩ : syracuseStep 2742221 = 1028333) (by norm_num)
theorem B2742245 : Blo 1827615 2742245 := bbase (se 4 (by rfl) ⟨257085, by rfl⟩ : syracuseStep 2742245 = 514171) (by norm_num)
theorem B3086309 : Blo 1827615 3086309 := bbase (se 4 (by rfl) ⟨289341, by rfl⟩ : syracuseStep 3086309 = 578683) (by norm_num)
theorem B2742269 : Blo 1827615 2742269 := bbase (se 3 (by rfl) ⟨514175, by rfl⟩ : syracuseStep 2742269 = 1028351) (by norm_num)
theorem B2742293 : Blo 1827615 2742293 := bbase (se 6 (by rfl) ⟨64272, by rfl⟩ : syracuseStep 2742293 = 128545) (by norm_num)
theorem B2742317 : Blo 1827615 2742317 := bbase (se 3 (by rfl) ⟨514184, by rfl⟩ : syracuseStep 2742317 = 1028369) (by norm_num)
theorem B2742341 : Blo 1827615 2742341 := bbase (se 4 (by rfl) ⟨257094, by rfl⟩ : syracuseStep 2742341 = 514189) (by norm_num)
theorem B3471437 : Blo 1827615 3471437 := bbase (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) (by norm_num)
theorem B4626517 : Blo 1827615 4626517 := bbase (se 8 (by rfl) ⟨27108, by rfl⟩ : syracuseStep 4626517 = 54217) (by norm_num)
theorem B2742365 : Blo 1827615 2742365 := bbase (se 3 (by rfl) ⟨514193, by rfl⟩ : syracuseStep 2742365 = 1028387) (by norm_num)
theorem B3086437 : Blo 1827615 3086437 := bbase (se 4 (by rfl) ⟨289353, by rfl⟩ : syracuseStep 3086437 = 578707) (by norm_num)
theorem B2603117 : Blo 1827615 2603117 := bbase (se 3 (by rfl) ⟨488084, by rfl⟩ : syracuseStep 2603117 = 976169) (by norm_num)
theorem B2742389 : Blo 1827615 2742389 := bbase (se 5 (by rfl) ⟨128549, by rfl⟩ : syracuseStep 2742389 = 257099) (by norm_num)
theorem B2742413 : Blo 1827615 2742413 := bbase (se 3 (by rfl) ⟨514202, by rfl⟩ : syracuseStep 2742413 = 1028405) (by norm_num)
theorem B2742437 : Blo 1827615 2742437 := bbase (se 4 (by rfl) ⟨257103, by rfl⟩ : syracuseStep 2742437 = 514207) (by norm_num)
theorem B3709093 : Blo 1827615 3709093 := bbase (se 4 (by rfl) ⟨347727, by rfl⟩ : syracuseStep 3709093 = 695455) (by norm_num)
theorem B2742461 : Blo 1827615 2742461 := bbase (se 3 (by rfl) ⟨514211, by rfl⟩ : syracuseStep 2742461 = 1028423) (by norm_num)
theorem B3086525 : Blo 1827615 3086525 := bbase (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) (by norm_num)
theorem B4626629 : Blo 1827615 4626629 := bbase (se 4 (by rfl) ⟨433746, by rfl⟩ : syracuseStep 4626629 = 867493) (by norm_num)
theorem B2742485 : Blo 1827615 2742485 := bbase (se 7 (by rfl) ⟨32138, by rfl⟩ : syracuseStep 2742485 = 64277) (by norm_num)
theorem B3471589 : Blo 1827615 3471589 := bbase (se 4 (by rfl) ⟨325461, by rfl⟩ : syracuseStep 3471589 = 650923) (by norm_num)
theorem B2742509 : Blo 1827615 2742509 := bbase (se 3 (by rfl) ⟨514220, by rfl⟩ : syracuseStep 2742509 = 1028441) (by norm_num)
theorem B2742533 : Blo 1827615 2742533 := bbase (se 4 (by rfl) ⟨257112, by rfl⟩ : syracuseStep 2742533 = 514225) (by norm_num)
theorem B2742557 : Blo 1827615 2742557 := bbase (se 3 (by rfl) ⟨514229, by rfl⟩ : syracuseStep 2742557 = 1028459) (by norm_num)
theorem B2226469 : Blo 1827615 2226469 := bbase (se 4 (by rfl) ⟨208731, by rfl⟩ : syracuseStep 2226469 = 417463) (by norm_num)
theorem B6945061 : Blo 1827615 6945061 := bbase (se 4 (by rfl) ⟨651099, by rfl⟩ : syracuseStep 6945061 = 1302199) (by norm_num)
theorem B9255221 : Blo 1827615 9255221 := bbase (se 5 (by rfl) ⟨433838, by rfl⟩ : syracuseStep 9255221 = 867677) (by norm_num)
theorem B2742581 : Blo 1827615 2742581 := bbase (se 5 (by rfl) ⟨128558, by rfl⟩ : syracuseStep 2742581 = 257117) (by norm_num)
theorem B3086653 : Blo 1827615 3086653 := bbase (se 3 (by rfl) ⟨578747, by rfl⟩ : syracuseStep 3086653 = 1157495) (by norm_num)
theorem B2742605 : Blo 1827615 2742605 := bbase (se 3 (by rfl) ⟨514238, by rfl⟩ : syracuseStep 2742605 = 1028477) (by norm_num)
theorem B2742629 : Blo 1827615 2742629 := bbase (se 4 (by rfl) ⟨257121, by rfl⟩ : syracuseStep 2742629 = 514243) (by norm_num)
theorem B5208421 : Blo 1827615 5208421 := bbase (se 4 (by rfl) ⟨488289, by rfl⟩ : syracuseStep 5208421 = 976579) (by norm_num)
theorem B2742653 : Blo 1827615 2742653 := bbase (se 3 (by rfl) ⟨514247, by rfl⟩ : syracuseStep 2742653 = 1028495) (by norm_num)
theorem B4626821 : Blo 1827615 4626821 := bbase (se 4 (by rfl) ⟨433764, by rfl⟩ : syracuseStep 4626821 = 867529) (by norm_num)
theorem B2742677 : Blo 1827615 2742677 := bbase (se 6 (by rfl) ⟨64281, by rfl⟩ : syracuseStep 2742677 = 128563) (by norm_num)
theorem B3086741 : Blo 1827615 3086741 := bbase (se 6 (by rfl) ⟨72345, by rfl⟩ : syracuseStep 3086741 = 144691) (by norm_num)
theorem B2742701 : Blo 1827615 2742701 := bbase (se 3 (by rfl) ⟨514256, by rfl⟩ : syracuseStep 2742701 = 1028513) (by norm_num)
theorem B2742725 : Blo 1827615 2742725 := bbase (se 4 (by rfl) ⟨257130, by rfl⟩ : syracuseStep 2742725 = 514261) (by norm_num)
theorem B6683093 : Blo 1827615 6683093 := bbase (se 7 (by rfl) ⟨78317, by rfl⟩ : syracuseStep 6683093 = 156635) (by norm_num)
theorem B2742749 : Blo 1827615 2742749 := bbase (se 3 (by rfl) ⟨514265, by rfl⟩ : syracuseStep 2742749 = 1028531) (by norm_num)
theorem B2742773 : Blo 1827615 2742773 := bbase (se 5 (by rfl) ⟨128567, by rfl⟩ : syracuseStep 2742773 = 257135) (by norm_num)
theorem B2742797 : Blo 1827615 2742797 := bbase (se 3 (by rfl) ⟨514274, by rfl⟩ : syracuseStep 2742797 = 1028549) (by norm_num)
theorem B3471893 : Blo 1827615 3471893 := bbase (se 6 (by rfl) ⟨81372, by rfl⟩ : syracuseStep 3471893 = 162745) (by norm_num)
theorem B3086869 : Blo 1827615 3086869 := bbase (se 6 (by rfl) ⟨72348, by rfl⟩ : syracuseStep 3086869 = 144697) (by norm_num)
theorem B2742821 : Blo 1827615 2742821 := bbase (se 4 (by rfl) ⟨257139, by rfl⟩ : syracuseStep 2742821 = 514279) (by norm_num)
theorem B3906085 : Blo 1827615 3906085 := bbase (se 4 (by rfl) ⟨366195, by rfl⟩ : syracuseStep 3906085 = 732391) (by norm_num)
theorem B2742845 : Blo 1827615 2742845 := bbase (se 3 (by rfl) ⟨514283, by rfl⟩ : syracuseStep 2742845 = 1028567) (by norm_num)
theorem B2742869 : Blo 1827615 2742869 := bbase (se 8 (by rfl) ⟨16071, by rfl⟩ : syracuseStep 2742869 = 32143) (by norm_num)
theorem B6945365 : Blo 1827615 6945365 := bbase (se 8 (by rfl) ⟨40695, by rfl⟩ : syracuseStep 6945365 = 81391) (by norm_num)
theorem B2226781 : Blo 1827615 2226781 := bbase (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) (by norm_num)
theorem B2742893 : Blo 1827615 2742893 := bbase (se 3 (by rfl) ⟨514292, by rfl⟩ : syracuseStep 2742893 = 1028585) (by norm_num)
theorem B3086957 : Blo 1827615 3086957 := bbase (se 3 (by rfl) ⟨578804, by rfl⟩ : syracuseStep 3086957 = 1157609) (by norm_num)
theorem B2742917 : Blo 1827615 2742917 := bbase (se 4 (by rfl) ⟨257148, by rfl⟩ : syracuseStep 2742917 = 514297) (by norm_num)
theorem B2603669 : Blo 1827615 2603669 := bbase (se 6 (by rfl) ⟨61023, by rfl⟩ : syracuseStep 2603669 = 122047) (by norm_num)
theorem B2742941 : Blo 1827615 2742941 := bbase (se 3 (by rfl) ⟨514301, by rfl⟩ : syracuseStep 2742941 = 1028603) (by norm_num)
theorem B2742965 : Blo 1827615 2742965 := bbase (se 5 (by rfl) ⟨128576, by rfl⟩ : syracuseStep 2742965 = 257153) (by norm_num)
theorem B13187765 : Blo 1827615 13187765 := bbase (se 5 (by rfl) ⟨618176, by rfl⟩ : syracuseStep 13187765 = 1236353) (by norm_num)
theorem B2742989 : Blo 1827615 2742989 := bbase (se 3 (by rfl) ⟨514310, by rfl⟩ : syracuseStep 2742989 = 1028621) (by norm_num)
theorem B9026261 : Blo 1827615 9026261 := bbase (se 7 (by rfl) ⟨105776, by rfl⟩ : syracuseStep 9026261 = 211553) (by norm_num)
theorem B13892309 : Blo 1827615 13892309 := bbase (se 7 (by rfl) ⟨162800, by rfl⟩ : syracuseStep 13892309 = 325601) (by norm_num)
theorem B4627165 : Blo 1827615 4627165 := bbase (se 3 (by rfl) ⟨867593, by rfl⟩ : syracuseStep 4627165 = 1735187) (by norm_num)
theorem B2743013 : Blo 1827615 2743013 := bbase (se 4 (by rfl) ⟨257157, by rfl⟩ : syracuseStep 2743013 = 514315) (by norm_num)
theorem B3087085 : Blo 1827615 3087085 := bbase (se 3 (by rfl) ⟨578828, by rfl⟩ : syracuseStep 3087085 = 1157657) (by norm_num)
theorem B5855989 : Blo 1827615 5855989 := bbase (se 5 (by rfl) ⟨274499, by rfl⟩ : syracuseStep 5855989 = 548999) (by norm_num)
theorem B2743037 : Blo 1827615 2743037 := bbase (se 3 (by rfl) ⟨514319, by rfl⟩ : syracuseStep 2743037 = 1028639) (by norm_num)
theorem B2743061 : Blo 1827615 2743061 := bbase (se 6 (by rfl) ⟨64290, by rfl⟩ : syracuseStep 2743061 = 128581) (by norm_num)
theorem B2743085 : Blo 1827615 2743085 := bbase (se 3 (by rfl) ⟨514328, by rfl⟩ : syracuseStep 2743085 = 1028657) (by norm_num)
theorem B2743109 : Blo 1827615 2743109 := bbase (se 4 (by rfl) ⟨257166, by rfl⟩ : syracuseStep 2743109 = 514333) (by norm_num)
theorem B3087173 : Blo 1827615 3087173 := bbase (se 4 (by rfl) ⟨289422, by rfl⟩ : syracuseStep 3087173 = 578845) (by norm_num)
theorem B4627277 : Blo 1827615 4627277 := bbase (se 3 (by rfl) ⟨867614, by rfl⟩ : syracuseStep 4627277 = 1735229) (by norm_num)
theorem B3169109 : Blo 1827615 3169109 := bbase (se 9 (by rfl) ⟨9284, by rfl⟩ : syracuseStep 3169109 = 18569) (by norm_num)
theorem B10419029 : Blo 1827615 10419029 := bbase (se 9 (by rfl) ⟨30524, by rfl⟩ : syracuseStep 10419029 = 61049) (by norm_num)
theorem B2743133 : Blo 1827615 2743133 := bbase (se 3 (by rfl) ⟨514337, by rfl⟩ : syracuseStep 2743133 = 1028675) (by norm_num)
theorem B2743157 : Blo 1827615 2743157 := bbase (se 5 (by rfl) ⟨128585, by rfl⟩ : syracuseStep 2743157 = 257171) (by norm_num)
theorem B2743181 : Blo 1827615 2743181 := bbase (se 3 (by rfl) ⟨514346, by rfl⟩ : syracuseStep 2743181 = 1028693) (by norm_num)
theorem B3906461 : Blo 1827615 3906461 := bbase (se 3 (by rfl) ⟨732461, by rfl⟩ : syracuseStep 3906461 = 1464923) (by norm_num)
theorem B2743205 : Blo 1827615 2743205 := bbase (se 4 (by rfl) ⟨257175, by rfl⟩ : syracuseStep 2743205 = 514351) (by norm_num)
theorem B2743229 : Blo 1827615 2743229 := bbase (se 3 (by rfl) ⟨514355, by rfl⟩ : syracuseStep 2743229 = 1028711) (by norm_num)
theorem B7134149 : Blo 1827615 7134149 := bbase (se 4 (by rfl) ⟨668826, by rfl⟩ : syracuseStep 7134149 = 1337653) (by norm_num)
theorem B3087301 : Blo 1827615 3087301 := bbase (se 4 (by rfl) ⟨289434, by rfl⟩ : syracuseStep 3087301 = 578869) (by norm_num)
theorem B2743253 : Blo 1827615 2743253 := bbase (se 7 (by rfl) ⟨32147, by rfl⟩ : syracuseStep 2743253 = 64295) (by norm_num)
theorem B2743277 : Blo 1827615 2743277 := bbase (se 3 (by rfl) ⟨514364, by rfl⟩ : syracuseStep 2743277 = 1028729) (by norm_num)
theorem B6593525 : Blo 1827615 6593525 := bbase (se 5 (by rfl) ⟨309071, by rfl⟩ : syracuseStep 6593525 = 618143) (by norm_num)
theorem B2743301 : Blo 1827615 2743301 := bbase (se 4 (by rfl) ⟨257184, by rfl⟩ : syracuseStep 2743301 = 514369) (by norm_num)
theorem B4627469 : Blo 1827615 4627469 := bbase (se 3 (by rfl) ⟨867650, by rfl⟩ : syracuseStep 4627469 = 1735301) (by norm_num)
theorem B2743325 : Blo 1827615 2743325 := bbase (se 3 (by rfl) ⟨514373, by rfl⟩ : syracuseStep 2743325 = 1028747) (by norm_num)
theorem B3087389 : Blo 1827615 3087389 := bbase (se 3 (by rfl) ⟨578885, by rfl⟩ : syracuseStep 3087389 = 1157771) (by norm_num)
theorem B2743349 : Blo 1827615 2743349 := bbase (se 5 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 2743349 = 257189) (by norm_num)
theorem B2743373 : Blo 1827615 2743373 := bbase (se 3 (by rfl) ⟨514382, by rfl⟩ : syracuseStep 2743373 = 1028765) (by norm_num)
theorem B2743397 : Blo 1827615 2743397 := bbase (se 4 (by rfl) ⟨257193, by rfl⟩ : syracuseStep 2743397 = 514387) (by norm_num)
theorem B13884533 : Blo 1827615 13884533 := bbase (se 5 (by rfl) ⟨650837, by rfl⟩ : syracuseStep 13884533 = 1301675) (by norm_num)
theorem B2743421 : Blo 1827615 2743421 := bbase (se 3 (by rfl) ⟨514391, by rfl⟩ : syracuseStep 2743421 = 1028783) (by norm_num)
theorem B2743445 : Blo 1827615 2743445 := bbase (se 6 (by rfl) ⟨64299, by rfl⟩ : syracuseStep 2743445 = 128599) (by norm_num)
theorem B2743469 : Blo 1827615 2743469 := bbase (se 3 (by rfl) ⟨514400, by rfl⟩ : syracuseStep 2743469 = 1028801) (by norm_num)
theorem B5856437 : Blo 1827615 5856437 := bbase (se 5 (by rfl) ⟨274520, by rfl⟩ : syracuseStep 5856437 = 549041) (by norm_num)
theorem B2743493 : Blo 1827615 2743493 := bbase (se 4 (by rfl) ⟨257202, by rfl⟩ : syracuseStep 2743493 = 514405) (by norm_num)
theorem B7814357 : Blo 1827615 7814357 := bbase (se 7 (by rfl) ⟨91574, by rfl⟩ : syracuseStep 7814357 = 183149) (by norm_num)
theorem B2743517 : Blo 1827615 2743517 := bbase (se 3 (by rfl) ⟨514409, by rfl⟩ : syracuseStep 2743517 = 1028819) (by norm_num)
theorem B2743541 : Blo 1827615 2743541 := bbase (se 5 (by rfl) ⟨128603, by rfl⟩ : syracuseStep 2743541 = 257207) (by norm_num)
theorem B3472645 : Blo 1827615 3472645 := bbase (se 4 (by rfl) ⟨325560, by rfl⟩ : syracuseStep 3472645 = 651121) (by norm_num)
theorem B7519493 : Blo 1827615 7519493 := bbase (se 4 (by rfl) ⟨704952, by rfl⟩ : syracuseStep 7519493 = 1409905) (by norm_num)
theorem B2743565 : Blo 1827615 2743565 := bbase (se 3 (by rfl) ⟨514418, by rfl⟩ : syracuseStep 2743565 = 1028837) (by norm_num)
theorem B8789269 : Blo 1827615 8789269 := bbase (se 6 (by rfl) ⟨205998, by rfl⟩ : syracuseStep 8789269 = 411997) (by norm_num)
theorem B2743589 : Blo 1827615 2743589 := bbase (se 4 (by rfl) ⟨257211, by rfl⟩ : syracuseStep 2743589 = 514423) (by norm_num)
theorem B2743613 : Blo 1827615 2743613 := bbase (se 3 (by rfl) ⟨514427, by rfl⟩ : syracuseStep 2743613 = 1028855) (by norm_num)
theorem B12508501 : Blo 1827615 12508501 := bbase (se 11 (by rfl) ⟨9161, by rfl⟩ : syracuseStep 12508501 = 18323) (by norm_num)
theorem B2743637 : Blo 1827615 2743637 := bbase (se 11 (by rfl) ⟨2009, by rfl⟩ : syracuseStep 2743637 = 4019) (by norm_num)
theorem B4627813 : Blo 1827615 4627813 := bbase (se 4 (by rfl) ⟨433857, by rfl⟩ : syracuseStep 4627813 = 867715) (by norm_num)
theorem B2743661 : Blo 1827615 2743661 := bbase (se 3 (by rfl) ⟨514436, by rfl⟩ : syracuseStep 2743661 = 1028873) (by norm_num)
theorem B2743685 : Blo 1827615 2743685 := bbase (se 4 (by rfl) ⟨257220, by rfl⟩ : syracuseStep 2743685 = 514441) (by norm_num)
theorem B2604421 : Blo 1827615 2604421 := bbase (se 4 (by rfl) ⟨244164, by rfl⟩ : syracuseStep 2604421 = 488329) (by norm_num)
theorem B3128725 : Blo 1827615 3128725 := bbase (se 6 (by rfl) ⟨73329, by rfl⟩ : syracuseStep 3128725 = 146659) (by norm_num)
theorem B3472789 : Blo 1827615 3472789 := bbase (se 6 (by rfl) ⟨81393, by rfl⟩ : syracuseStep 3472789 = 162787) (by norm_num)
theorem B2743709 : Blo 1827615 2743709 := bbase (se 3 (by rfl) ⟨514445, by rfl⟩ : syracuseStep 2743709 = 1028891) (by norm_num)
theorem B2743733 : Blo 1827615 2743733 := bbase (se 5 (by rfl) ⟨128612, by rfl⟩ : syracuseStep 2743733 = 257225) (by norm_num)
theorem B5209525 : Blo 1827615 5209525 := bbase (se 5 (by rfl) ⟨244196, by rfl⟩ : syracuseStep 5209525 = 488393) (by norm_num)
theorem B2743757 : Blo 1827615 2743757 := bbase (se 3 (by rfl) ⟨514454, by rfl⟩ : syracuseStep 2743757 = 1028909) (by norm_num)
theorem B4627925 : Blo 1827615 4627925 := bbase (se 7 (by rfl) ⟨54233, by rfl⟩ : syracuseStep 4627925 = 108467) (by norm_num)
theorem B2743781 : Blo 1827615 2743781 := bbase (se 4 (by rfl) ⟨257229, by rfl⟩ : syracuseStep 2743781 = 514459) (by norm_num)
theorem B11722229 : Blo 1827615 11722229 := bbase (se 5 (by rfl) ⟨549479, by rfl⟩ : syracuseStep 11722229 = 1098959) (by norm_num)
theorem B2743805 : Blo 1827615 2743805 := bbase (se 3 (by rfl) ⟨514463, by rfl⟩ : syracuseStep 2743805 = 1028927) (by norm_num)
theorem B2743829 : Blo 1827615 2743829 := bbase (se 6 (by rfl) ⟨64308, by rfl⟩ : syracuseStep 2743829 = 128617) (by norm_num)
theorem B2743853 : Blo 1827615 2743853 := bbase (se 3 (by rfl) ⟨514472, by rfl⟩ : syracuseStep 2743853 = 1028945) (by norm_num)
theorem B3472949 : Blo 1827615 3472949 := bbase (se 5 (by rfl) ⟨162794, by rfl⟩ : syracuseStep 3472949 = 325589) (by norm_num)
theorem B9256517 : Blo 1827615 9256517 := bbase (se 4 (by rfl) ⟨867798, by rfl⟩ : syracuseStep 9256517 = 1735597) (by norm_num)
theorem B2743877 : Blo 1827615 2743877 := bbase (se 4 (by rfl) ⟨257238, by rfl⟩ : syracuseStep 2743877 = 514477) (by norm_num)
theorem B2743901 : Blo 1827615 2743901 := bbase (se 3 (by rfl) ⟨514481, by rfl⟩ : syracuseStep 2743901 = 1028963) (by norm_num)
theorem B2743925 : Blo 1827615 2743925 := bbase (se 5 (by rfl) ⟨128621, by rfl⟩ : syracuseStep 2743925 = 257243) (by norm_num)
theorem B2817677 : Blo 1827615 2817677 := bbase (se 3 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 2817677 = 1056629) (by norm_num)
theorem B2743949 : Blo 1827615 2743949 := bbase (se 3 (by rfl) ⟨514490, by rfl⟩ : syracuseStep 2743949 = 1028981) (by norm_num)
theorem B4628117 : Blo 1827615 4628117 := bbase (se 6 (by rfl) ⟨108471, by rfl⟩ : syracuseStep 4628117 = 216943) (by norm_num)
theorem B2743973 : Blo 1827615 2743973 := bbase (se 4 (by rfl) ⟨257247, by rfl⟩ : syracuseStep 2743973 = 514495) (by norm_num)
theorem B2743997 : Blo 1827615 2743997 := bbase (se 3 (by rfl) ⟨514499, by rfl⟩ : syracuseStep 2743997 = 1028999) (by norm_num)
theorem B3473093 : Blo 1827615 3473093 := bbase (se 4 (by rfl) ⟨325602, by rfl⟩ : syracuseStep 3473093 = 651205) (by norm_num)
theorem B2744021 : Blo 1827615 2744021 := bbase (se 7 (by rfl) ⟨32156, by rfl⟩ : syracuseStep 2744021 = 64313) (by norm_num)
theorem B2744045 : Blo 1827615 2744045 := bbase (se 3 (by rfl) ⟨514508, by rfl⟩ : syracuseStep 2744045 = 1029017) (by norm_num)
theorem B2744069 : Blo 1827615 2744069 := bbase (se 4 (by rfl) ⟨257256, by rfl⟩ : syracuseStep 2744069 = 514513) (by norm_num)
theorem B2744093 : Blo 1827615 2744093 := bbase (se 3 (by rfl) ⟨514517, by rfl⟩ : syracuseStep 2744093 = 1029035) (by norm_num)
theorem B2744117 : Blo 1827615 2744117 := bbase (se 5 (by rfl) ⟨128630, by rfl⟩ : syracuseStep 2744117 = 257261) (by norm_num)
theorem B4112189 : Blo 1827615 4112189 := bbase (se 3 (by rfl) ⟨771035, by rfl⟩ : syracuseStep 4112189 = 1542071) (by norm_num)
theorem B2744141 : Blo 1827615 2744141 := bbase (se 3 (by rfl) ⟨514526, by rfl⟩ : syracuseStep 2744141 = 1029053) (by norm_num)
theorem B4169573 : Blo 1827615 4169573 := bbase (se 4 (by rfl) ⟨390897, by rfl⟩ : syracuseStep 4169573 = 781795) (by norm_num)
theorem B2744165 : Blo 1827615 2744165 := bbase (se 4 (by rfl) ⟨257265, by rfl⟩ : syracuseStep 2744165 = 514531) (by norm_num)
theorem B2744189 : Blo 1827615 2744189 := bbase (se 3 (by rfl) ⟨514535, by rfl⟩ : syracuseStep 2744189 = 1029071) (by norm_num)
theorem B4112261 : Blo 1827615 4112261 := bbase (se 4 (by rfl) ⟨385524, by rfl⟩ : syracuseStep 4112261 = 771049) (by norm_num)
theorem B2056081 : Blo 1827615 2056081 := bbase (se 2 (by rfl) ⟨771030, by rfl⟩ : syracuseStep 2056081 = 1542061) (by norm_num)
theorem B2744213 : Blo 1827615 2744213 := bbase (se 6 (by rfl) ⟨64317, by rfl⟩ : syracuseStep 2744213 = 128635) (by norm_num)
theorem B2744237 : Blo 1827615 2744237 := bbase (se 3 (by rfl) ⟨514544, by rfl⟩ : syracuseStep 2744237 = 1029089) (by norm_num)
theorem B2056117 : Blo 1827615 2056117 := bbase (se 5 (by rfl) ⟨96380, by rfl⟩ : syracuseStep 2056117 = 192761) (by norm_num)
theorem B2744261 : Blo 1827615 2744261 := bbase (se 4 (by rfl) ⟨257274, by rfl⟩ : syracuseStep 2744261 = 514549) (by norm_num)
theorem B4112333 : Blo 1827615 4112333 := bbase (se 3 (by rfl) ⟨771062, by rfl⟩ : syracuseStep 4112333 = 1542125) (by norm_num)
theorem B2056153 : Blo 1827615 2056153 := bbase (se 2 (by rfl) ⟨771057, by rfl⟩ : syracuseStep 2056153 = 1542115) (by norm_num)
theorem B2744285 : Blo 1827615 2744285 := bbase (se 3 (by rfl) ⟨514553, by rfl⟩ : syracuseStep 2744285 = 1029107) (by norm_num)
theorem B3473381 : Blo 1827615 3473381 := bbase (se 4 (by rfl) ⟨325629, by rfl⟩ : syracuseStep 3473381 = 651259) (by norm_num)
theorem B4628461 : Blo 1827615 4628461 := bbase (se 3 (by rfl) ⟨867836, by rfl⟩ : syracuseStep 4628461 = 1735673) (by norm_num)
theorem B14073845 : Blo 1827615 14073845 := bbase (se 5 (by rfl) ⟨659711, by rfl⟩ : syracuseStep 14073845 = 1319423) (by norm_num)
theorem B2744309 : Blo 1827615 2744309 := bbase (se 5 (by rfl) ⟨128639, by rfl⟩ : syracuseStep 2744309 = 257279) (by norm_num)
theorem B2056189 : Blo 1827615 2056189 := bbase (se 3 (by rfl) ⟨385535, by rfl⟩ : syracuseStep 2056189 = 771071) (by norm_num)
theorem B2744321 : Blo 1827615 2744321 := bstep (se 2 (by rfl) ⟨1029120, by rfl⟩ : syracuseStep 2744321 = 2058241) B2058241
theorem B4112387 : Blo 1827615 4112387 := bstep (se 1 (by rfl) ⟨3084290, by rfl⟩ : syracuseStep 4112387 = 6168581) B6168581
theorem B4014083 : Blo 1827615 4014083 := bstep (se 1 (by rfl) ⟨3010562, by rfl⟩ : syracuseStep 4014083 = 6021125) B6021125
theorem B11722765 : Blo 1827615 11722765 := bstep (se 3 (by rfl) ⟨2198018, by rfl⟩ : syracuseStep 11722765 = 4396037) B4396037
theorem B2744339 : Blo 1827615 2744339 := bstep (se 1 (by rfl) ⟨2058254, by rfl⟩ : syracuseStep 2744339 = 4116509) B4116509
theorem B2744369 : Blo 1827615 2744369 := bstep (se 2 (by rfl) ⟨1029138, by rfl⟩ : syracuseStep 2744369 = 2058277) B2058277
theorem B2056243 : Blo 1827615 2056243 := bstep (se 1 (by rfl) ⟨1542182, by rfl⟩ : syracuseStep 2056243 = 3084365) B3084365
theorem B2744387 : Blo 1827615 2744387 := bstep (se 1 (by rfl) ⟨2058290, by rfl⟩ : syracuseStep 2744387 = 4116581) B4116581
theorem B2744417 : Blo 1827615 2744417 := bstep (se 2 (by rfl) ⟨1029156, by rfl⟩ : syracuseStep 2744417 = 2058313) B2058313
theorem B6168689 : Blo 1827615 6168689 := bstep (se 2 (by rfl) ⟨2313258, by rfl⟩ : syracuseStep 6168689 = 4626517) B4626517
theorem B39526541 : Blo 1827615 39526541 := bstep (se 3 (by rfl) ⟨7411226, by rfl⟩ : syracuseStep 39526541 = 14822453) B14822453
theorem B2056387 : Blo 1827615 2056387 := bstep (se 1 (by rfl) ⟨1542290, by rfl⟩ : syracuseStep 2056387 = 3084581) B3084581
theorem B9257165 : Blo 1827615 9257165 := bstep (se 3 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 9257165 = 3471437) B3471437
theorem B4112657 : Blo 1827615 4112657 := bstep (se 2 (by rfl) ⟨1542246, by rfl⟩ : syracuseStep 4112657 = 3084493) B3084493
theorem B2195731 : Blo 1827615 2195731 := bstep (se 1 (by rfl) ⟨1646798, by rfl⟩ : syracuseStep 2195731 = 3293597) B3293597
theorem B4112675 : Blo 1827615 4112675 := bstep (se 1 (by rfl) ⟨3084506, by rfl⟩ : syracuseStep 4112675 = 6169013) B6169013
theorem B4628785 : Blo 1827615 4628785 := bstep (se 2 (by rfl) ⟨1735794, by rfl⟩ : syracuseStep 4628785 = 3471589) B3471589
theorem B2056531 : Blo 1827615 2056531 := bstep (se 1 (by rfl) ⟨1542398, by rfl⟩ : syracuseStep 2056531 = 3084797) B3084797
theorem B5857667 : Blo 1827615 5857667 := bstep (se 1 (by rfl) ⟨4393250, by rfl⟩ : syracuseStep 5857667 = 8786501) B8786501
theorem B2056675 : Blo 1827615 2056675 := bstep (se 1 (by rfl) ⟨1542506, by rfl⟩ : syracuseStep 2056675 = 3085013) B3085013
theorem B4112945 : Blo 1827615 4112945 := bstep (se 2 (by rfl) ⟨1542354, by rfl⟩ : syracuseStep 4112945 = 3084709) B3084709
theorem B4112963 : Blo 1827615 4112963 := bstep (se 1 (by rfl) ⟨3084722, by rfl⟩ : syracuseStep 4112963 = 6169445) B6169445
theorem B4629059 : Blo 1827615 4629059 := bstep (se 1 (by rfl) ⟨3471794, by rfl⟩ : syracuseStep 4629059 = 6943589) B6943589
theorem B2056819 : Blo 1827615 2056819 := bstep (se 1 (by rfl) ⟨1542614, by rfl⟩ : syracuseStep 2056819 = 3085229) B3085229
theorem B3293827 : Blo 1827615 3293827 := bstep (se 1 (by rfl) ⟨2470370, by rfl⟩ : syracuseStep 3293827 = 4940741) B4940741
theorem B6169229 : Blo 1827615 6169229 := bstep (se 3 (by rfl) ⟨1156730, by rfl⟩ : syracuseStep 6169229 = 2313461) B2313461
theorem B6169283 : Blo 1827615 6169283 := bstep (se 1 (by rfl) ⟨4626962, by rfl⟩ : syracuseStep 6169283 = 9253925) B9253925
theorem B79086293 : Blo 1827615 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B4170467 : Blo 1827615 4170467 := bstep (se 1 (by rfl) ⟨3127850, by rfl⟩ : syracuseStep 4170467 = 6255701) B6255701
theorem B2056963 : Blo 1827615 2056963 := bstep (se 1 (by rfl) ⟨1542722, by rfl⟩ : syracuseStep 2056963 = 3085445) B3085445
theorem B4629251 : Blo 1827615 4629251 := bstep (se 1 (by rfl) ⟨3471938, by rfl⟩ : syracuseStep 4629251 = 6943877) B6943877
theorem B1827619 : Blo 1827615 1827619 := bstep (se 1 (by rfl) ⟨1370714, by rfl⟩ : syracuseStep 1827619 = 2741429) B2741429
theorem B1827635 : Blo 1827615 1827635 := bstep (se 1 (by rfl) ⟨1370726, by rfl⟩ : syracuseStep 1827635 = 2741453) B2741453
theorem B1827651 : Blo 1827615 1827651 := bstep (se 1 (by rfl) ⟨1370738, by rfl⟩ : syracuseStep 1827651 = 2741477) B2741477
theorem B4113233 : Blo 1827615 4113233 := bstep (se 2 (by rfl) ⟨1542462, by rfl⟩ : syracuseStep 4113233 = 3084925) B3084925
theorem B1827667 : Blo 1827615 1827667 := bstep (se 1 (by rfl) ⟨1370750, by rfl⟩ : syracuseStep 1827667 = 2741501) B2741501
theorem B1827683 : Blo 1827615 1827683 := bstep (se 1 (by rfl) ⟨1370762, by rfl⟩ : syracuseStep 1827683 = 2741525) B2741525
theorem B4113251 : Blo 1827615 4113251 := bstep (se 1 (by rfl) ⟨3084938, by rfl⟩ : syracuseStep 4113251 = 6169877) B6169877
theorem B1827699 : Blo 1827615 1827699 := bstep (se 1 (by rfl) ⟨1370774, by rfl⟩ : syracuseStep 1827699 = 2741549) B2741549
theorem B1827715 : Blo 1827615 1827715 := bstep (se 1 (by rfl) ⟨1370786, by rfl⟩ : syracuseStep 1827715 = 2741573) B2741573
theorem B6939533 : Blo 1827615 6939533 := bstep (se 3 (by rfl) ⟨1301162, by rfl⟩ : syracuseStep 6939533 = 2602325) B2602325
theorem B1827731 : Blo 1827615 1827731 := bstep (se 1 (by rfl) ⟨1370798, by rfl⟩ : syracuseStep 1827731 = 2741597) B2741597
theorem B2057107 : Blo 1827615 2057107 := bstep (se 1 (by rfl) ⟨1542830, by rfl⟩ : syracuseStep 2057107 = 3085661) B3085661
theorem B1827747 : Blo 1827615 1827747 := bstep (se 1 (by rfl) ⟨1370810, by rfl⟩ : syracuseStep 1827747 = 2741621) B2741621
theorem B1827763 : Blo 1827615 1827763 := bstep (se 1 (by rfl) ⟨1370822, by rfl⟩ : syracuseStep 1827763 = 2741645) B2741645
theorem B1827779 : Blo 1827615 1827779 := bstep (se 1 (by rfl) ⟨1370834, by rfl⟩ : syracuseStep 1827779 = 2741669) B2741669
theorem B6169553 : Blo 1827615 6169553 := bstep (se 2 (by rfl) ⟨2313582, by rfl⟩ : syracuseStep 6169553 = 4627165) B4627165
theorem B1827795 : Blo 1827615 1827795 := bstep (se 1 (by rfl) ⟨1370846, by rfl⟩ : syracuseStep 1827795 = 2741693) B2741693
theorem B1827811 : Blo 1827615 1827811 := bstep (se 1 (by rfl) ⟨1370858, by rfl⟩ : syracuseStep 1827811 = 2741717) B2741717
theorem B7807985 : Blo 1827615 7807985 := bstep (se 2 (by rfl) ⟨2927994, by rfl⟩ : syracuseStep 7807985 = 5855989) B5855989
theorem B1827827 : Blo 1827615 1827827 := bstep (se 1 (by rfl) ⟨1370870, by rfl⟩ : syracuseStep 1827827 = 2741741) B2741741
theorem B1827843 : Blo 1827615 1827843 := bstep (se 1 (by rfl) ⟨1370882, by rfl⟩ : syracuseStep 1827843 = 2741765) B2741765
theorem B13886477 : Blo 1827615 13886477 := bstep (se 3 (by rfl) ⟨2603714, by rfl⟩ : syracuseStep 13886477 = 5207429) B5207429
theorem B1827859 : Blo 1827615 1827859 := bstep (se 1 (by rfl) ⟨1370894, by rfl⟩ : syracuseStep 1827859 = 2741789) B2741789
theorem B1827875 : Blo 1827615 1827875 := bstep (se 1 (by rfl) ⟨1370906, by rfl⟩ : syracuseStep 1827875 = 2741813) B2741813
theorem B7808035 : Blo 1827615 7808035 := bstep (se 1 (by rfl) ⟨5856026, by rfl⟩ : syracuseStep 7808035 = 11712053) B11712053
theorem B2057251 : Blo 1827615 2057251 := bstep (se 1 (by rfl) ⟨1542938, by rfl⟩ : syracuseStep 2057251 = 3085877) B3085877
theorem B1827891 : Blo 1827615 1827891 := bstep (se 1 (by rfl) ⟨1370918, by rfl⟩ : syracuseStep 1827891 = 2741837) B2741837
theorem B1827907 : Blo 1827615 1827907 := bstep (se 1 (by rfl) ⟨1370930, by rfl⟩ : syracuseStep 1827907 = 2741861) B2741861
theorem B1827923 : Blo 1827615 1827923 := bstep (se 1 (by rfl) ⟨1370942, by rfl⟩ : syracuseStep 1827923 = 2741885) B2741885
theorem B1827939 : Blo 1827615 1827939 := bstep (se 1 (by rfl) ⟨1370954, by rfl⟩ : syracuseStep 1827939 = 2741909) B2741909
theorem B4113521 : Blo 1827615 4113521 := bstep (se 2 (by rfl) ⟨1542570, by rfl⟩ : syracuseStep 4113521 = 3085141) B3085141
theorem B1827955 : Blo 1827615 1827955 := bstep (se 1 (by rfl) ⟨1370966, by rfl⟩ : syracuseStep 1827955 = 2741933) B2741933
theorem B1827971 : Blo 1827615 1827971 := bstep (se 1 (by rfl) ⟨1370978, by rfl⟩ : syracuseStep 1827971 = 2741957) B2741957
theorem B4113539 : Blo 1827615 4113539 := bstep (se 1 (by rfl) ⟨3085154, by rfl⟩ : syracuseStep 4113539 = 6170309) B6170309
theorem B9381005 : Blo 1827615 9381005 := bstep (se 3 (by rfl) ⟨1758938, by rfl⟩ : syracuseStep 9381005 = 3517877) B3517877
theorem B10413197 : Blo 1827615 10413197 := bstep (se 3 (by rfl) ⟨1952474, by rfl⟩ : syracuseStep 10413197 = 3904949) B3904949
theorem B1827987 : Blo 1827615 1827987 := bstep (se 1 (by rfl) ⟨1370990, by rfl⟩ : syracuseStep 1827987 = 2741981) B2741981
theorem B1828003 : Blo 1827615 1828003 := bstep (se 1 (by rfl) ⟨1371002, by rfl⟩ : syracuseStep 1828003 = 2742005) B2742005
theorem B1828019 : Blo 1827615 1828019 := bstep (se 1 (by rfl) ⟨1371014, by rfl⟩ : syracuseStep 1828019 = 2742029) B2742029
theorem B2057395 : Blo 1827615 2057395 := bstep (se 1 (by rfl) ⟨1543046, by rfl⟩ : syracuseStep 2057395 = 3086093) B3086093
theorem B1828035 : Blo 1827615 1828035 := bstep (se 1 (by rfl) ⟨1371026, by rfl⟩ : syracuseStep 1828035 = 2742053) B2742053
theorem B5858513 : Blo 1827615 5858513 := bstep (se 2 (by rfl) ⟨2196942, by rfl⟩ : syracuseStep 5858513 = 4393885) B4393885
theorem B1828051 : Blo 1827615 1828051 := bstep (se 1 (by rfl) ⟨1371038, by rfl⟩ : syracuseStep 1828051 = 2742077) B2742077
theorem B1828067 : Blo 1827615 1828067 := bstep (se 1 (by rfl) ⟨1371050, by rfl⟩ : syracuseStep 1828067 = 2742101) B2742101
theorem B1828083 : Blo 1827615 1828083 := bstep (se 1 (by rfl) ⟨1371062, by rfl⟩ : syracuseStep 1828083 = 2742125) B2742125
theorem B1828099 : Blo 1827615 1828099 := bstep (se 1 (by rfl) ⟨1371074, by rfl⟩ : syracuseStep 1828099 = 2742149) B2742149
theorem B5858563 : Blo 1827615 5858563 := bstep (se 1 (by rfl) ⟨4393922, by rfl⟩ : syracuseStep 5858563 = 8787845) B8787845
theorem B1828115 : Blo 1827615 1828115 := bstep (se 1 (by rfl) ⟨1371086, by rfl⟩ : syracuseStep 1828115 = 2742173) B2742173
theorem B1828131 : Blo 1827615 1828131 := bstep (se 1 (by rfl) ⟨1371098, by rfl⟩ : syracuseStep 1828131 = 2742197) B2742197
theorem B1828147 : Blo 1827615 1828147 := bstep (se 1 (by rfl) ⟨1371110, by rfl⟩ : syracuseStep 1828147 = 2742221) B2742221
theorem B1828163 : Blo 1827615 1828163 := bstep (se 1 (by rfl) ⟨1371122, by rfl⟩ : syracuseStep 1828163 = 2742245) B2742245
theorem B2057539 : Blo 1827615 2057539 := bstep (se 1 (by rfl) ⟨1543154, by rfl⟩ : syracuseStep 2057539 = 3086309) B3086309
theorem B1828179 : Blo 1827615 1828179 := bstep (se 1 (by rfl) ⟨1371134, by rfl⟩ : syracuseStep 1828179 = 2742269) B2742269
theorem B1828195 : Blo 1827615 1828195 := bstep (se 1 (by rfl) ⟨1371146, by rfl⟩ : syracuseStep 1828195 = 2742293) B2742293
theorem B3294577 : Blo 1827615 3294577 := bstep (se 2 (by rfl) ⟨1235466, by rfl⟩ : syracuseStep 3294577 = 2470933) B2470933
theorem B1828211 : Blo 1827615 1828211 := bstep (se 1 (by rfl) ⟨1371158, by rfl⟩ : syracuseStep 1828211 = 2742317) B2742317
theorem B1828227 : Blo 1827615 1828227 := bstep (se 1 (by rfl) ⟨1371170, by rfl⟩ : syracuseStep 1828227 = 2742341) B2742341
theorem B4113809 : Blo 1827615 4113809 := bstep (se 2 (by rfl) ⟨1542678, by rfl⟩ : syracuseStep 4113809 = 3085357) B3085357
theorem B1828243 : Blo 1827615 1828243 := bstep (se 1 (by rfl) ⟨1371182, by rfl⟩ : syracuseStep 1828243 = 2742365) B2742365
theorem B1828259 : Blo 1827615 1828259 := bstep (se 1 (by rfl) ⟨1371194, by rfl⟩ : syracuseStep 1828259 = 2742389) B2742389
theorem B4113827 : Blo 1827615 4113827 := bstep (se 1 (by rfl) ⟨3085370, by rfl⟩ : syracuseStep 4113827 = 6170741) B6170741
theorem B1828275 : Blo 1827615 1828275 := bstep (se 1 (by rfl) ⟨1371206, by rfl⟩ : syracuseStep 1828275 = 2742413) B2742413
theorem B1828291 : Blo 1827615 1828291 := bstep (se 1 (by rfl) ⟨1371218, by rfl⟩ : syracuseStep 1828291 = 2742437) B2742437
theorem B1828307 : Blo 1827615 1828307 := bstep (se 1 (by rfl) ⟨1371230, by rfl⟩ : syracuseStep 1828307 = 2742461) B2742461
theorem B2057683 : Blo 1827615 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B1828323 : Blo 1827615 1828323 := bstep (se 1 (by rfl) ⟨1371242, by rfl⟩ : syracuseStep 1828323 = 2742485) B2742485
theorem B6170093 : Blo 1827615 6170093 := bstep (se 3 (by rfl) ⟨1156892, by rfl⟩ : syracuseStep 6170093 = 2313785) B2313785
theorem B1828339 : Blo 1827615 1828339 := bstep (se 1 (by rfl) ⟨1371254, by rfl⟩ : syracuseStep 1828339 = 2742509) B2742509
theorem B1828355 : Blo 1827615 1828355 := bstep (se 1 (by rfl) ⟨1371266, by rfl⟩ : syracuseStep 1828355 = 2742533) B2742533
theorem B1828371 : Blo 1827615 1828371 := bstep (se 1 (by rfl) ⟨1371278, by rfl⟩ : syracuseStep 1828371 = 2742557) B2742557
theorem B6170147 : Blo 1827615 6170147 := bstep (se 1 (by rfl) ⟨4627610, by rfl⟩ : syracuseStep 6170147 = 9255221) B9255221
theorem B1828387 : Blo 1827615 1828387 := bstep (se 1 (by rfl) ⟨1371290, by rfl⟩ : syracuseStep 1828387 = 2742581) B2742581
theorem B1828403 : Blo 1827615 1828403 := bstep (se 1 (by rfl) ⟨1371302, by rfl⟩ : syracuseStep 1828403 = 2742605) B2742605
theorem B1828419 : Blo 1827615 1828419 := bstep (se 1 (by rfl) ⟨1371314, by rfl⟩ : syracuseStep 1828419 = 2742629) B2742629
theorem B1828435 : Blo 1827615 1828435 := bstep (se 1 (by rfl) ⟨1371326, by rfl⟩ : syracuseStep 1828435 = 2742653) B2742653
theorem B1828451 : Blo 1827615 1828451 := bstep (se 1 (by rfl) ⟨1371338, by rfl⟩ : syracuseStep 1828451 = 2742677) B2742677
theorem B2057827 : Blo 1827615 2057827 := bstep (se 1 (by rfl) ⟨1543370, by rfl⟩ : syracuseStep 2057827 = 3086741) B3086741
theorem B4941425 : Blo 1827615 4941425 := bstep (se 2 (by rfl) ⟨1853034, by rfl⟩ : syracuseStep 4941425 = 3706069) B3706069
theorem B1828467 : Blo 1827615 1828467 := bstep (se 1 (by rfl) ⟨1371350, by rfl⟩ : syracuseStep 1828467 = 2742701) B2742701
theorem B1828483 : Blo 1827615 1828483 := bstep (se 1 (by rfl) ⟨1371362, by rfl⟩ : syracuseStep 1828483 = 2742725) B2742725
theorem B1828499 : Blo 1827615 1828499 := bstep (se 1 (by rfl) ⟨1371374, by rfl⟩ : syracuseStep 1828499 = 2742749) B2742749
theorem B1828515 : Blo 1827615 1828515 := bstep (se 1 (by rfl) ⟨1371386, by rfl⟩ : syracuseStep 1828515 = 2742773) B2742773
theorem B4114097 : Blo 1827615 4114097 := bstep (se 2 (by rfl) ⟨1542786, by rfl⟩ : syracuseStep 4114097 = 3085573) B3085573
theorem B4630193 : Blo 1827615 4630193 := bstep (se 2 (by rfl) ⟨1736322, by rfl⟩ : syracuseStep 4630193 = 3472645) B3472645
theorem B1828531 : Blo 1827615 1828531 := bstep (se 1 (by rfl) ⟨1371398, by rfl⟩ : syracuseStep 1828531 = 2742797) B2742797
theorem B4114115 : Blo 1827615 4114115 := bstep (se 1 (by rfl) ⟨3085586, by rfl⟩ : syracuseStep 4114115 = 6171173) B6171173
theorem B1828547 : Blo 1827615 1828547 := bstep (se 1 (by rfl) ⟨1371410, by rfl⟩ : syracuseStep 1828547 = 2742821) B2742821
theorem B7513805 : Blo 1827615 7513805 := bstep (se 3 (by rfl) ⟨1408838, by rfl⟩ : syracuseStep 7513805 = 2817677) B2817677
theorem B1828563 : Blo 1827615 1828563 := bstep (se 1 (by rfl) ⟨1371422, by rfl⟩ : syracuseStep 1828563 = 2742845) B2742845
theorem B1828579 : Blo 1827615 1828579 := bstep (se 1 (by rfl) ⟨1371434, by rfl⟩ : syracuseStep 1828579 = 2742869) B2742869
theorem B4630243 : Blo 1827615 4630243 := bstep (se 1 (by rfl) ⟨3472682, by rfl⟩ : syracuseStep 4630243 = 6945365) B6945365
theorem B1828595 : Blo 1827615 1828595 := bstep (se 1 (by rfl) ⟨1371446, by rfl⟩ : syracuseStep 1828595 = 2742893) B2742893
theorem B2057971 : Blo 1827615 2057971 := bstep (se 1 (by rfl) ⟨1543478, by rfl⟩ : syracuseStep 2057971 = 3086957) B3086957
theorem B1828611 : Blo 1827615 1828611 := bstep (se 1 (by rfl) ⟨1371458, by rfl⟩ : syracuseStep 1828611 = 2742917) B2742917
theorem B1828627 : Blo 1827615 1828627 := bstep (se 1 (by rfl) ⟨1371470, by rfl⟩ : syracuseStep 1828627 = 2742941) B2742941
theorem B1828643 : Blo 1827615 1828643 := bstep (se 1 (by rfl) ⟨1371482, by rfl⟩ : syracuseStep 1828643 = 2742965) B2742965
theorem B8791843 : Blo 1827615 8791843 := bstep (se 1 (by rfl) ⟨6593882, by rfl⟩ : syracuseStep 8791843 = 13187765) B13187765
theorem B6170417 : Blo 1827615 6170417 := bstep (se 2 (by rfl) ⟨2313906, by rfl⟩ : syracuseStep 6170417 = 4627813) B4627813
theorem B1828659 : Blo 1827615 1828659 := bstep (se 1 (by rfl) ⟨1371494, by rfl⟩ : syracuseStep 1828659 = 2742989) B2742989
theorem B1828675 : Blo 1827615 1828675 := bstep (se 1 (by rfl) ⟨1371506, by rfl⟩ : syracuseStep 1828675 = 2743013) B2743013
theorem B1828691 : Blo 1827615 1828691 := bstep (se 1 (by rfl) ⟨1371518, by rfl⟩ : syracuseStep 1828691 = 2743037) B2743037
theorem B1828707 : Blo 1827615 1828707 := bstep (se 1 (by rfl) ⟨1371530, by rfl⟩ : syracuseStep 1828707 = 2743061) B2743061
theorem B4630385 : Blo 1827615 4630385 := bstep (se 2 (by rfl) ⟨1736394, by rfl⟩ : syracuseStep 4630385 = 3472789) B3472789
theorem B1828723 : Blo 1827615 1828723 := bstep (se 1 (by rfl) ⟨1371542, by rfl⟩ : syracuseStep 1828723 = 2743085) B2743085
theorem B1828739 : Blo 1827615 1828739 := bstep (se 1 (by rfl) ⟨1371554, by rfl⟩ : syracuseStep 1828739 = 2743109) B2743109
theorem B2058115 : Blo 1827615 2058115 := bstep (se 1 (by rfl) ⟨1543586, by rfl⟩ : syracuseStep 2058115 = 3087173) B3087173
theorem B1828755 : Blo 1827615 1828755 := bstep (se 1 (by rfl) ⟨1371566, by rfl⟩ : syracuseStep 1828755 = 2743133) B2743133
theorem B1828771 : Blo 1827615 1828771 := bstep (se 1 (by rfl) ⟨1371578, by rfl⟩ : syracuseStep 1828771 = 2743157) B2743157
theorem B1828787 : Blo 1827615 1828787 := bstep (se 1 (by rfl) ⟨1371590, by rfl⟩ : syracuseStep 1828787 = 2743181) B2743181
theorem B1828803 : Blo 1827615 1828803 := bstep (se 1 (by rfl) ⟨1371602, by rfl⟩ : syracuseStep 1828803 = 2743205) B2743205
theorem B4114385 : Blo 1827615 4114385 := bstep (se 2 (by rfl) ⟨1542894, by rfl⟩ : syracuseStep 4114385 = 3085789) B3085789
theorem B1828819 : Blo 1827615 1828819 := bstep (se 1 (by rfl) ⟨1371614, by rfl⟩ : syracuseStep 1828819 = 2743229) B2743229
theorem B4114403 : Blo 1827615 4114403 := bstep (se 1 (by rfl) ⟨3085802, by rfl⟩ : syracuseStep 4114403 = 6171605) B6171605
theorem B1828835 : Blo 1827615 1828835 := bstep (se 1 (by rfl) ⟨1371626, by rfl⟩ : syracuseStep 1828835 = 2743253) B2743253
theorem B1828851 : Blo 1827615 1828851 := bstep (se 1 (by rfl) ⟨1371638, by rfl⟩ : syracuseStep 1828851 = 2743277) B2743277
theorem B1828867 : Blo 1827615 1828867 := bstep (se 1 (by rfl) ⟨1371650, by rfl⟩ : syracuseStep 1828867 = 2743301) B2743301
theorem B1828883 : Blo 1827615 1828883 := bstep (se 1 (by rfl) ⟨1371662, by rfl⟩ : syracuseStep 1828883 = 2743325) B2743325
theorem B2058259 : Blo 1827615 2058259 := bstep (se 1 (by rfl) ⟨1543694, by rfl⟩ : syracuseStep 2058259 = 3087389) B3087389
theorem B1828899 : Blo 1827615 1828899 := bstep (se 1 (by rfl) ⟨1371674, by rfl⟩ : syracuseStep 1828899 = 2743349) B2743349
theorem B10414129 : Blo 1827615 10414129 := bstep (se 2 (by rfl) ⟨3905298, by rfl⟩ : syracuseStep 10414129 = 7810597) B7810597
theorem B1951795 : Blo 1827615 1951795 := bstep (se 1 (by rfl) ⟨1463846, by rfl⟩ : syracuseStep 1951795 = 2927693) B2927693
theorem B1828915 : Blo 1827615 1828915 := bstep (se 1 (by rfl) ⟨1371686, by rfl⟩ : syracuseStep 1828915 = 2743373) B2743373
theorem B1828931 : Blo 1827615 1828931 := bstep (se 1 (by rfl) ⟨1371698, by rfl⟩ : syracuseStep 1828931 = 2743397) B2743397
theorem B1828947 : Blo 1827615 1828947 := bstep (se 1 (by rfl) ⟨1371710, by rfl⟩ : syracuseStep 1828947 = 2743421) B2743421
theorem B1828963 : Blo 1827615 1828963 := bstep (se 1 (by rfl) ⟨1371722, by rfl⟩ : syracuseStep 1828963 = 2743445) B2743445
theorem B1828979 : Blo 1827615 1828979 := bstep (se 1 (by rfl) ⟨1371734, by rfl⟩ : syracuseStep 1828979 = 2743469) B2743469
theorem B1828995 : Blo 1827615 1828995 := bstep (se 1 (by rfl) ⟨1371746, by rfl⟩ : syracuseStep 1828995 = 2743493) B2743493
theorem B1829011 : Blo 1827615 1829011 := bstep (se 1 (by rfl) ⟨1371758, by rfl⟩ : syracuseStep 1829011 = 2743517) B2743517
theorem B1829027 : Blo 1827615 1829027 := bstep (se 1 (by rfl) ⟨1371770, by rfl⟩ : syracuseStep 1829027 = 2743541) B2743541
theorem B1829043 : Blo 1827615 1829043 := bstep (se 1 (by rfl) ⟨1371782, by rfl⟩ : syracuseStep 1829043 = 2743565) B2743565
theorem B1829059 : Blo 1827615 1829059 := bstep (se 1 (by rfl) ⟨1371794, by rfl⟩ : syracuseStep 1829059 = 2743589) B2743589
theorem B22554821 : Blo 1827615 22554821 := bstep (se 4 (by rfl) ⟨2114514, by rfl⟩ : syracuseStep 22554821 = 4229029) B4229029
theorem B1853651 : Blo 1827615 1853651 := bstep (se 1 (by rfl) ⟨1390238, by rfl⟩ : syracuseStep 1853651 = 2780477) B2780477
theorem B1829075 : Blo 1827615 1829075 := bstep (se 1 (by rfl) ⟨1371806, by rfl⟩ : syracuseStep 1829075 = 2743613) B2743613
theorem B1829091 : Blo 1827615 1829091 := bstep (se 1 (by rfl) ⟨1371818, by rfl⟩ : syracuseStep 1829091 = 2743637) B2743637
theorem B4114673 : Blo 1827615 4114673 := bstep (se 2 (by rfl) ⟨1543002, by rfl⟩ : syracuseStep 4114673 = 3086005) B3086005
theorem B1829107 : Blo 1827615 1829107 := bstep (se 1 (by rfl) ⟨1371830, by rfl⟩ : syracuseStep 1829107 = 2743661) B2743661
theorem B4114691 : Blo 1827615 4114691 := bstep (se 1 (by rfl) ⟨3086018, by rfl⟩ : syracuseStep 4114691 = 6172037) B6172037
theorem B1829123 : Blo 1827615 1829123 := bstep (se 1 (by rfl) ⟨1371842, by rfl⟩ : syracuseStep 1829123 = 2743685) B2743685
theorem B1829139 : Blo 1827615 1829139 := bstep (se 1 (by rfl) ⟨1371854, by rfl⟩ : syracuseStep 1829139 = 2743709) B2743709
theorem B1829155 : Blo 1827615 1829155 := bstep (se 1 (by rfl) ⟨1371866, by rfl⟩ : syracuseStep 1829155 = 2743733) B2743733
theorem B1829171 : Blo 1827615 1829171 := bstep (se 1 (by rfl) ⟨1371878, by rfl⟩ : syracuseStep 1829171 = 2743757) B2743757
theorem B1829187 : Blo 1827615 1829187 := bstep (se 1 (by rfl) ⟨1371890, by rfl⟩ : syracuseStep 1829187 = 2743781) B2743781
theorem B6170957 : Blo 1827615 6170957 := bstep (se 3 (by rfl) ⟨1157054, by rfl⟩ : syracuseStep 6170957 = 2314109) B2314109
theorem B1829203 : Blo 1827615 1829203 := bstep (se 1 (by rfl) ⟨1371902, by rfl⟩ : syracuseStep 1829203 = 2743805) B2743805
theorem B1829219 : Blo 1827615 1829219 := bstep (se 1 (by rfl) ⟨1371914, by rfl⟩ : syracuseStep 1829219 = 2743829) B2743829
theorem B1829235 : Blo 1827615 1829235 := bstep (se 1 (by rfl) ⟨1371926, by rfl⟩ : syracuseStep 1829235 = 2743853) B2743853
theorem B6171011 : Blo 1827615 6171011 := bstep (se 1 (by rfl) ⟨4628258, by rfl⟩ : syracuseStep 6171011 = 9256517) B9256517
theorem B1829251 : Blo 1827615 1829251 := bstep (se 1 (by rfl) ⟨1371938, by rfl⟩ : syracuseStep 1829251 = 2743877) B2743877
theorem B1829267 : Blo 1827615 1829267 := bstep (se 1 (by rfl) ⟨1371950, by rfl⟩ : syracuseStep 1829267 = 2743901) B2743901
theorem B1829283 : Blo 1827615 1829283 := bstep (se 1 (by rfl) ⟨1371962, by rfl⟩ : syracuseStep 1829283 = 2743925) B2743925
theorem B1829299 : Blo 1827615 1829299 := bstep (se 1 (by rfl) ⟨1371974, by rfl⟩ : syracuseStep 1829299 = 2743949) B2743949
theorem B1829315 : Blo 1827615 1829315 := bstep (se 1 (by rfl) ⟨1371986, by rfl⟩ : syracuseStep 1829315 = 2743973) B2743973
theorem B5859793 : Blo 1827615 5859793 := bstep (se 2 (by rfl) ⟨2197422, by rfl⟩ : syracuseStep 5859793 = 4394845) B4394845
theorem B1829331 : Blo 1827615 1829331 := bstep (se 1 (by rfl) ⟨1371998, by rfl⟩ : syracuseStep 1829331 = 2743997) B2743997
theorem B1829347 : Blo 1827615 1829347 := bstep (se 1 (by rfl) ⟨1372010, by rfl⟩ : syracuseStep 1829347 = 2744021) B2744021
theorem B1829363 : Blo 1827615 1829363 := bstep (se 1 (by rfl) ⟨1372022, by rfl⟩ : syracuseStep 1829363 = 2744045) B2744045
theorem B1829379 : Blo 1827615 1829379 := bstep (se 1 (by rfl) ⟨1372034, by rfl⟩ : syracuseStep 1829379 = 2744069) B2744069
theorem B4114961 : Blo 1827615 4114961 := bstep (se 2 (by rfl) ⟨1543110, by rfl⟩ : syracuseStep 4114961 = 3086221) B3086221
theorem B1829395 : Blo 1827615 1829395 := bstep (se 1 (by rfl) ⟨1372046, by rfl⟩ : syracuseStep 1829395 = 2744093) B2744093
theorem B4114979 : Blo 1827615 4114979 := bstep (se 1 (by rfl) ⟨3086234, by rfl⟩ : syracuseStep 4114979 = 6172469) B6172469
theorem B1829411 : Blo 1827615 1829411 := bstep (se 1 (by rfl) ⟨1372058, by rfl⟩ : syracuseStep 1829411 = 2744117) B2744117
theorem B1829427 : Blo 1827615 1829427 := bstep (se 1 (by rfl) ⟨1372070, by rfl⟩ : syracuseStep 1829427 = 2744141) B2744141
theorem B2779715 : Blo 1827615 2779715 := bstep (se 1 (by rfl) ⟨2084786, by rfl⟩ : syracuseStep 2779715 = 4169573) B4169573
theorem B2345539 : Blo 1827615 2345539 := bstep (se 1 (by rfl) ⟨1759154, by rfl⟩ : syracuseStep 2345539 = 3518309) B3518309
theorem B1829443 : Blo 1827615 1829443 := bstep (se 1 (by rfl) ⟨1372082, by rfl⟩ : syracuseStep 1829443 = 2744165) B2744165
theorem B1829459 : Blo 1827615 1829459 := bstep (se 1 (by rfl) ⟨1372094, by rfl⟩ : syracuseStep 1829459 = 2744189) B2744189
theorem B1829475 : Blo 1827615 1829475 := bstep (se 1 (by rfl) ⟨1372106, by rfl⟩ : syracuseStep 1829475 = 2744213) B2744213
theorem B1829491 : Blo 1827615 1829491 := bstep (se 1 (by rfl) ⟨1372118, by rfl⟩ : syracuseStep 1829491 = 2744237) B2744237
theorem B1829507 : Blo 1827615 1829507 := bstep (se 1 (by rfl) ⟨1372130, by rfl⟩ : syracuseStep 1829507 = 2744261) B2744261
theorem B37530253 : Blo 1827615 37530253 := bstep (se 3 (by rfl) ⟨7036922, by rfl⟩ : syracuseStep 37530253 = 14073845) B14073845
theorem B6171281 : Blo 1827615 6171281 := bstep (se 2 (by rfl) ⟨2314230, by rfl⟩ : syracuseStep 6171281 = 4628461) B4628461
theorem B1829523 : Blo 1827615 1829523 := bstep (se 1 (by rfl) ⟨1372142, by rfl⟩ : syracuseStep 1829523 = 2744285) B2744285
theorem B1952419 : Blo 1827615 1952419 := bstep (se 1 (by rfl) ⟨1464314, by rfl⟩ : syracuseStep 1952419 = 2928629) B2928629
theorem B1829539 : Blo 1827615 1829539 := bstep (se 1 (by rfl) ⟨1372154, by rfl⟩ : syracuseStep 1829539 = 2744309) B2744309
theorem B1829555 : Blo 1827615 1829555 := bstep (se 1 (by rfl) ⟨1372166, by rfl⟩ : syracuseStep 1829555 = 2744333) B2744333
theorem B1829571 : Blo 1827615 1829571 := bstep (se 1 (by rfl) ⟨1372178, by rfl⟩ : syracuseStep 1829571 = 2744357) B2744357
theorem B1829587 : Blo 1827615 1829587 := bstep (se 1 (by rfl) ⟨1372190, by rfl⟩ : syracuseStep 1829587 = 2744381) B2744381
theorem B2345699 : Blo 1827615 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B1829603 : Blo 1827615 1829603 := bstep (se 1 (by rfl) ⟨1372202, by rfl⟩ : syracuseStep 1829603 = 2744405) B2744405
theorem B4115249 : Blo 1827615 4115249 := bstep (se 2 (by rfl) ⟨1543218, by rfl⟩ : syracuseStep 4115249 = 3086437) B3086437
theorem B4115267 : Blo 1827615 4115267 := bstep (se 1 (by rfl) ⟨3086450, by rfl⟩ : syracuseStep 4115267 = 6172901) B6172901
theorem B26348429 : Blo 1827615 26348429 := bstep (se 3 (by rfl) ⟨4940330, by rfl⟩ : syracuseStep 26348429 = 9880661) B9880661
theorem B9030541 : Blo 1827615 9030541 := bstep (se 3 (by rfl) ⟨1693226, by rfl⟩ : syracuseStep 9030541 = 3386453) B3386453
theorem B2927539 : Blo 1827615 2927539 := bstep (se 1 (by rfl) ⟨2195654, by rfl⟩ : syracuseStep 2927539 = 4391309) B4391309
theorem B6941645 : Blo 1827615 6941645 := bstep (se 3 (by rfl) ⟨1301558, by rfl⟩ : syracuseStep 6941645 = 2603117) B2603117
theorem B2927585 : Blo 1827615 2927585 := bstep (se 2 (by rfl) ⟨1097844, by rfl⟩ : syracuseStep 2927585 = 2195689) B2195689
theorem B5352419 : Blo 1827615 5352419 := bstep (se 1 (by rfl) ⟨4014314, by rfl⟩ : syracuseStep 5352419 = 8028629) B8028629
theorem B2968625 : Blo 1827615 2968625 := bstep (se 2 (by rfl) ⟨1113234, by rfl⟩ : syracuseStep 2968625 = 2226469) B2226469
theorem B9260081 : Blo 1827615 9260081 := bstep (se 2 (by rfl) ⟨3472530, by rfl⟩ : syracuseStep 9260081 = 6945061) B6945061
theorem B4115537 : Blo 1827615 4115537 := bstep (se 2 (by rfl) ⟨1543326, by rfl⟩ : syracuseStep 4115537 = 3086653) B3086653
theorem B2313299 : Blo 1827615 2313299 := bstep (se 1 (by rfl) ⟨1734974, by rfl⟩ : syracuseStep 2313299 = 3469949) B3469949
theorem B4115555 : Blo 1827615 4115555 := bstep (se 1 (by rfl) ⟨3086666, by rfl⟩ : syracuseStep 4115555 = 6173333) B6173333
theorem B6171821 : Blo 1827615 6171821 := bstep (se 3 (by rfl) ⟨1157216, by rfl⟩ : syracuseStep 6171821 = 2314433) B2314433
theorem B5205197 : Blo 1827615 5205197 := bstep (se 3 (by rfl) ⟨975974, by rfl⟩ : syracuseStep 5205197 = 1951949) B1951949
theorem B6171875 : Blo 1827615 6171875 := bstep (se 1 (by rfl) ⟨4628906, by rfl⟩ : syracuseStep 6171875 = 9257813) B9257813
theorem B13880645 : Blo 1827615 13880645 := bstep (se 4 (by rfl) ⟨1301310, by rfl⟩ : syracuseStep 13880645 = 2602621) B2602621
theorem B4115825 : Blo 1827615 4115825 := bstep (se 2 (by rfl) ⟨1543434, by rfl⟩ : syracuseStep 4115825 = 3086869) B3086869
theorem B2346355 : Blo 1827615 2346355 := bstep (se 1 (by rfl) ⟨1759766, by rfl⟩ : syracuseStep 2346355 = 3519533) B3519533
theorem B5205379 : Blo 1827615 5205379 := bstep (se 1 (by rfl) ⟨3904034, by rfl⟩ : syracuseStep 5205379 = 7808069) B7808069
theorem B4115843 : Blo 1827615 4115843 := bstep (se 1 (by rfl) ⟨3086882, by rfl⟩ : syracuseStep 4115843 = 6173765) B6173765
theorem B7810445 : Blo 1827615 7810445 := bstep (se 3 (by rfl) ⟨1464458, by rfl⟩ : syracuseStep 7810445 = 2928917) B2928917
theorem B52735373 : Blo 1827615 52735373 := bstep (se 3 (by rfl) ⟨9887882, by rfl⟩ : syracuseStep 52735373 = 19775765) B19775765
theorem B20032949 : Blo 1827615 20032949 := bstep (se 5 (by rfl) ⟨939044, by rfl⟩ : syracuseStep 20032949 = 1878089) B1878089
theorem B2969041 : Blo 1827615 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B2928097 : Blo 1827615 2928097 := bstep (se 2 (by rfl) ⟨1098036, by rfl⟩ : syracuseStep 2928097 = 2196073) B2196073
theorem B10415587 : Blo 1827615 10415587 := bstep (se 1 (by rfl) ⟨7811690, by rfl⟩ : syracuseStep 10415587 = 15623381) B15623381
theorem B6172145 : Blo 1827615 6172145 := bstep (se 2 (by rfl) ⟨2314554, by rfl⟩ : syracuseStep 6172145 = 4629109) B4629109
theorem B5205539 : Blo 1827615 5205539 := bstep (se 1 (by rfl) ⟨3904154, by rfl⟩ : syracuseStep 5205539 = 7808309) B7808309
theorem B16911971 : Blo 1827615 16911971 := bstep (se 1 (by rfl) ⟨12683978, by rfl⟩ : syracuseStep 16911971 = 25367957) B25367957
theorem B5860973 : Blo 1827615 5860973 := bstep (se 3 (by rfl) ⟨1098932, by rfl⟩ : syracuseStep 5860973 = 2197865) B2197865
theorem B3706499 : Blo 1827615 3706499 := bstep (se 1 (by rfl) ⟨2779874, by rfl⟩ : syracuseStep 3706499 = 5559749) B5559749
theorem B3296899 : Blo 1827615 3296899 := bstep (se 1 (by rfl) ⟨2472674, by rfl⟩ : syracuseStep 3296899 = 4945349) B4945349
theorem B4943501 : Blo 1827615 4943501 := bstep (se 3 (by rfl) ⟨926906, by rfl⟩ : syracuseStep 4943501 = 1853813) B1853813
theorem B4116113 : Blo 1827615 4116113 := bstep (se 2 (by rfl) ⟨1543542, by rfl⟩ : syracuseStep 4116113 = 3087085) B3087085
theorem B4116131 : Blo 1827615 4116131 := bstep (se 1 (by rfl) ⟨3087098, by rfl⟩ : syracuseStep 4116131 = 6174197) B6174197
theorem B6942449 : Blo 1827615 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B2314003 : Blo 1827615 2314003 := bstep (se 1 (by rfl) ⟨1735502, by rfl⟩ : syracuseStep 2314003 = 3471005) B3471005
theorem B23424821 : Blo 1827615 23424821 := bstep (se 5 (by rfl) ⟨1098038, by rfl⟩ : syracuseStep 23424821 = 2196077) B2196077
theorem B4943683 : Blo 1827615 4943683 := bstep (se 1 (by rfl) ⟨3707762, by rfl⟩ : syracuseStep 4943683 = 7415525) B7415525
theorem B3084115 : Blo 1827615 3084115 := bstep (se 1 (by rfl) ⟨2313086, by rfl⟩ : syracuseStep 3084115 = 4626173) B4626173
theorem B13889393 : Blo 1827615 13889393 := bstep (se 2 (by rfl) ⟨5208522, by rfl⟩ : syracuseStep 13889393 = 10417045) B10417045
theorem B2314099 : Blo 1827615 2314099 := bstep (se 1 (by rfl) ⟨1735574, by rfl⟩ : syracuseStep 2314099 = 3471149) B3471149
theorem B4116401 : Blo 1827615 4116401 := bstep (se 2 (by rfl) ⟨1543650, by rfl⟩ : syracuseStep 4116401 = 3087301) B3087301
theorem B20836277 : Blo 1827615 20836277 := bstep (se 5 (by rfl) ⟨976700, by rfl⟩ : syracuseStep 20836277 = 1953401) B1953401
theorem B4116419 : Blo 1827615 4116419 := bstep (se 1 (by rfl) ⟨3087314, by rfl⟩ : syracuseStep 4116419 = 6174629) B6174629
theorem B3084257 : Blo 1827615 3084257 := bstep (se 2 (by rfl) ⟨1156596, by rfl⟩ : syracuseStep 3084257 = 2313193) B2313193
theorem B10416113 : Blo 1827615 10416113 := bstep (se 2 (by rfl) ⟨3906042, by rfl⟩ : syracuseStep 10416113 = 7812085) B7812085
theorem B2928641 : Blo 1827615 2928641 := bstep (se 2 (by rfl) ⟨1098240, by rfl⟩ : syracuseStep 2928641 = 2196481) B2196481
theorem B6172685 : Blo 1827615 6172685 := bstep (se 3 (by rfl) ⟨1157378, by rfl⟩ : syracuseStep 6172685 = 2314757) B2314757
theorem B6172739 : Blo 1827615 6172739 := bstep (se 1 (by rfl) ⟨4629554, by rfl⟩ : syracuseStep 6172739 = 9259109) B9259109
theorem B3084385 : Blo 1827615 3084385 := bstep (se 2 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 3084385 = 2313289) B2313289
theorem B3084419 : Blo 1827615 3084419 := bstep (se 1 (by rfl) ⟨2313314, by rfl⟩ : syracuseStep 3084419 = 4626629) B4626629
theorem B3338435 : Blo 1827615 3338435 := bstep (se 1 (by rfl) ⟨2503826, by rfl⟩ : syracuseStep 3338435 = 5007653) B5007653
theorem B3084547 : Blo 1827615 3084547 := bstep (se 1 (by rfl) ⟨2313410, by rfl⟩ : syracuseStep 3084547 = 4626821) B4626821
theorem B3903761 : Blo 1827615 3903761 := bstep (se 2 (by rfl) ⟨1463910, by rfl⟩ : syracuseStep 3903761 = 2927821) B2927821
theorem B6173009 : Blo 1827615 6173009 := bstep (se 2 (by rfl) ⟨2314878, by rfl⟩ : syracuseStep 6173009 = 4629757) B4629757
theorem B2314595 : Blo 1827615 2314595 := bstep (se 1 (by rfl) ⟨1735946, by rfl⟩ : syracuseStep 2314595 = 3471893) B3471893
theorem B11719025 : Blo 1827615 11719025 := bstep (se 2 (by rfl) ⟨4394634, by rfl⟩ : syracuseStep 11719025 = 8789269) B8789269
theorem B6943117 : Blo 1827615 6943117 := bstep (se 3 (by rfl) ⟨1301834, by rfl⟩ : syracuseStep 6943117 = 2603669) B2603669
theorem B3084689 : Blo 1827615 3084689 := bstep (se 2 (by rfl) ⟨1156758, by rfl⟩ : syracuseStep 3084689 = 2313517) B2313517
theorem B6017507 : Blo 1827615 6017507 := bstep (se 1 (by rfl) ⟨4513130, by rfl⟩ : syracuseStep 6017507 = 9026261) B9026261
theorem B9261539 : Blo 1827615 9261539 := bstep (se 1 (by rfl) ⟨6946154, by rfl⟩ : syracuseStep 9261539 = 13892309) B13892309
theorem B4944397 : Blo 1827615 4944397 := bstep (se 3 (by rfl) ⟨927074, by rfl⟩ : syracuseStep 4944397 = 1854149) B1854149
theorem B11301389 : Blo 1827615 11301389 := bstep (se 3 (by rfl) ⟨2119010, by rfl⟩ : syracuseStep 11301389 = 4238021) B4238021
theorem B3084817 : Blo 1827615 3084817 := bstep (se 2 (by rfl) ⟨1156806, by rfl⟩ : syracuseStep 3084817 = 2313613) B2313613
theorem B3469873 : Blo 1827615 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B3084851 : Blo 1827615 3084851 := bstep (se 1 (by rfl) ⟨2313638, by rfl⟩ : syracuseStep 3084851 = 4627277) B4627277
theorem B5206609 : Blo 1827615 5206609 := bstep (se 2 (by rfl) ⟨1952478, by rfl⟩ : syracuseStep 5206609 = 3904957) B3904957
theorem B9155171 : Blo 1827615 9155171 := bstep (se 1 (by rfl) ⟨6866378, by rfl⟩ : syracuseStep 9155171 = 13732757) B13732757
theorem B4756099 : Blo 1827615 4756099 := bstep (se 1 (by rfl) ⟨3567074, by rfl⟩ : syracuseStep 4756099 = 7134149) B7134149
theorem B4395683 : Blo 1827615 4395683 := bstep (se 1 (by rfl) ⟨3296762, by rfl⟩ : syracuseStep 4395683 = 6593525) B6593525
theorem B3084979 : Blo 1827615 3084979 := bstep (se 1 (by rfl) ⟨2313734, by rfl⟩ : syracuseStep 3084979 = 4627469) B4627469
theorem B3470033 : Blo 1827615 3470033 := bstep (se 2 (by rfl) ⟨1301262, by rfl⟩ : syracuseStep 3470033 = 2602525) B2602525
theorem B3904291 : Blo 1827615 3904291 := bstep (se 1 (by rfl) ⟨2928218, by rfl⟩ : syracuseStep 3904291 = 5856437) B5856437
theorem B3085121 : Blo 1827615 3085121 := bstep (se 2 (by rfl) ⟨1156920, by rfl⟩ : syracuseStep 3085121 = 2313841) B2313841
theorem B6173549 : Blo 1827615 6173549 := bstep (se 3 (by rfl) ⟨1157540, by rfl⟩ : syracuseStep 6173549 = 2315081) B2315081
theorem B11719565 : Blo 1827615 11719565 := bstep (se 3 (by rfl) ⟨2197418, by rfl⟩ : syracuseStep 11719565 = 4394837) B4394837
theorem B6173603 : Blo 1827615 6173603 := bstep (se 1 (by rfl) ⟨4630202, by rfl⟩ : syracuseStep 6173603 = 9260405) B9260405
theorem B3085249 : Blo 1827615 3085249 := bstep (se 2 (by rfl) ⟨1156968, by rfl⟩ : syracuseStep 3085249 = 2313937) B2313937
theorem B2929603 : Blo 1827615 2929603 := bstep (se 1 (by rfl) ⟨2197202, by rfl⟩ : syracuseStep 2929603 = 4394405) B4394405
theorem B3085283 : Blo 1827615 3085283 := bstep (se 1 (by rfl) ⟨2313962, by rfl⟩ : syracuseStep 3085283 = 4627925) B4627925
theorem B2315299 : Blo 1827615 2315299 := bstep (se 1 (by rfl) ⟨1736474, by rfl⟩ : syracuseStep 2315299 = 3472949) B3472949
theorem B39539765 : Blo 1827615 39539765 := bstep (se 5 (by rfl) ⟨1853426, by rfl⟩ : syracuseStep 39539765 = 3706853) B3706853
theorem B3470435 : Blo 1827615 3470435 := bstep (se 1 (by rfl) ⟨2602826, by rfl⟩ : syracuseStep 3470435 = 5205653) B5205653
theorem B3085411 : Blo 1827615 3085411 := bstep (se 1 (by rfl) ⟨2314058, by rfl⟩ : syracuseStep 3085411 = 4628117) B4628117
theorem B2315395 : Blo 1827615 2315395 := bstep (se 1 (by rfl) ⟨1736546, by rfl⟩ : syracuseStep 2315395 = 3473093) B3473093
theorem B6943907 : Blo 1827615 6943907 := bstep (se 1 (by rfl) ⟨5207930, by rfl⟩ : syracuseStep 6943907 = 10415861) B10415861
theorem B6173873 : Blo 1827615 6173873 := bstep (se 2 (by rfl) ⟨2315202, by rfl⟩ : syracuseStep 6173873 = 4630405) B4630405
theorem B2741441 : Blo 1827615 2741441 := bstep (se 2 (by rfl) ⟨1028040, by rfl⟩ : syracuseStep 2741441 = 2056081) B2056081
theorem B2929859 : Blo 1827615 2929859 := bstep (se 1 (by rfl) ⟨2197394, by rfl⟩ : syracuseStep 2929859 = 4394789) B4394789
theorem B2741459 : Blo 1827615 2741459 := bstep (se 1 (by rfl) ⟨2056094, by rfl⟩ : syracuseStep 2741459 = 4112189) B4112189
theorem B2602211 : Blo 1827615 2602211 := bstep (se 1 (by rfl) ⟨1951658, by rfl⟩ : syracuseStep 2602211 = 3903317) B3903317
theorem B160281827 : Blo 1827615 160281827 := bstep (se 1 (by rfl) ⟨120211370, by rfl⟩ : syracuseStep 160281827 = 240422741) B240422741
theorem B2741489 : Blo 1827615 2741489 := bstep (se 2 (by rfl) ⟨1028058, by rfl⟩ : syracuseStep 2741489 = 2056117) B2056117
theorem B3085553 : Blo 1827615 3085553 := bstep (se 2 (by rfl) ⟨1157082, by rfl⟩ : syracuseStep 3085553 = 2314165) B2314165
theorem B2741507 : Blo 1827615 2741507 := bstep (se 1 (by rfl) ⟨2056130, by rfl⟩ : syracuseStep 2741507 = 4112261) B4112261
theorem B9262349 : Blo 1827615 9262349 := bstep (se 3 (by rfl) ⟨1736690, by rfl⟩ : syracuseStep 9262349 = 3473381) B3473381
theorem B2741537 : Blo 1827615 2741537 := bstep (se 2 (by rfl) ⟨1028076, by rfl⟩ : syracuseStep 2741537 = 2056153) B2056153
theorem B2741555 : Blo 1827615 2741555 := bstep (se 1 (by rfl) ⟨2056166, by rfl⟩ : syracuseStep 2741555 = 4112333) B4112333
theorem B2741585 : Blo 1827615 2741585 := bstep (se 2 (by rfl) ⟨1028094, by rfl⟩ : syracuseStep 2741585 = 2056189) B2056189
theorem B2741603 : Blo 1827615 2741603 := bstep (se 1 (by rfl) ⟨2056202, by rfl⟩ : syracuseStep 2741603 = 4112405) B4112405
theorem B3085681 : Blo 1827615 3085681 := bstep (se 2 (by rfl) ⟨1157130, by rfl⟩ : syracuseStep 3085681 = 2314261) B2314261
theorem B2741633 : Blo 1827615 2741633 := bstep (se 2 (by rfl) ⟨1028112, by rfl⟩ : syracuseStep 2741633 = 2056225) B2056225
theorem B2741651 : Blo 1827615 2741651 := bstep (se 1 (by rfl) ⟨2056238, by rfl⟩ : syracuseStep 2741651 = 4112477) B4112477
theorem B3085715 : Blo 1827615 3085715 := bstep (se 1 (by rfl) ⟨2314286, by rfl⟩ : syracuseStep 3085715 = 4628573) B4628573
theorem B3126689 : Blo 1827615 3126689 := bstep (se 2 (by rfl) ⟨1172508, by rfl⟩ : syracuseStep 3126689 = 2345017) B2345017
theorem B10417571 : Blo 1827615 10417571 := bstep (se 1 (by rfl) ⟨7813178, by rfl⟩ : syracuseStep 10417571 = 15626357) B15626357
theorem B2741681 : Blo 1827615 2741681 := bstep (se 2 (by rfl) ⟨1028130, by rfl⟩ : syracuseStep 2741681 = 2056261) B2056261
theorem B2741699 : Blo 1827615 2741699 := bstep (se 1 (by rfl) ⟨2056274, by rfl⟩ : syracuseStep 2741699 = 4112549) B4112549
theorem B2471377 : Blo 1827615 2471377 := bstep (se 2 (by rfl) ⟨926766, by rfl⟩ : syracuseStep 2471377 = 1853533) B1853533
theorem B2741729 : Blo 1827615 2741729 := bstep (se 2 (by rfl) ⟨1028148, by rfl⟩ : syracuseStep 2741729 = 2056297) B2056297
theorem B2741747 : Blo 1827615 2741747 := bstep (se 1 (by rfl) ⟨2056310, by rfl⟩ : syracuseStep 2741747 = 4112621) B4112621
theorem B2741777 : Blo 1827615 2741777 := bstep (se 2 (by rfl) ⟨1028166, by rfl⟩ : syracuseStep 2741777 = 2056333) B2056333
theorem B3085843 : Blo 1827615 3085843 := bstep (se 1 (by rfl) ⟨2314382, by rfl⟩ : syracuseStep 3085843 = 4628765) B4628765
theorem B2741795 : Blo 1827615 2741795 := bstep (se 1 (by rfl) ⟨2056346, by rfl⟩ : syracuseStep 2741795 = 4112693) B4112693
theorem B4945457 : Blo 1827615 4945457 := bstep (se 2 (by rfl) ⟨1854546, by rfl⟩ : syracuseStep 4945457 = 3709093) B3709093
theorem B2741825 : Blo 1827615 2741825 := bstep (se 2 (by rfl) ⟨1028184, by rfl⟩ : syracuseStep 2741825 = 2056369) B2056369
theorem B2741843 : Blo 1827615 2741843 := bstep (se 1 (by rfl) ⟨2056382, by rfl⟩ : syracuseStep 2741843 = 4112765) B4112765
theorem B2741873 : Blo 1827615 2741873 := bstep (se 2 (by rfl) ⟨1028202, by rfl⟩ : syracuseStep 2741873 = 2056405) B2056405
theorem B4691569 : Blo 1827615 4691569 := bstep (se 2 (by rfl) ⟨1759338, by rfl⟩ : syracuseStep 4691569 = 3518677) B3518677
theorem B2741891 : Blo 1827615 2741891 := bstep (se 1 (by rfl) ⟨2056418, by rfl⟩ : syracuseStep 2741891 = 4112837) B4112837
theorem B2741921 : Blo 1827615 2741921 := bstep (se 2 (by rfl) ⟨1028220, by rfl⟩ : syracuseStep 2741921 = 2056441) B2056441
theorem B3085985 : Blo 1827615 3085985 := bstep (se 2 (by rfl) ⟨1157244, by rfl⟩ : syracuseStep 3085985 = 2314489) B2314489
theorem B2741939 : Blo 1827615 2741939 := bstep (se 1 (by rfl) ⟨2056454, by rfl⟩ : syracuseStep 2741939 = 4112909) B4112909
theorem B11712205 : Blo 1827615 11712205 := bstep (se 3 (by rfl) ⟨2196038, by rfl⟩ : syracuseStep 11712205 = 4392077) B4392077
theorem B6174413 : Blo 1827615 6174413 := bstep (se 3 (by rfl) ⟨1157702, by rfl⟩ : syracuseStep 6174413 = 2315405) B2315405
theorem B2741969 : Blo 1827615 2741969 := bstep (se 2 (by rfl) ⟨1028238, by rfl⟩ : syracuseStep 2741969 = 2056477) B2056477
theorem B2741987 : Blo 1827615 2741987 := bstep (se 1 (by rfl) ⟨2056490, by rfl⟩ : syracuseStep 2741987 = 4112981) B4112981
theorem B2742017 : Blo 1827615 2742017 := bstep (se 2 (by rfl) ⟨1028256, by rfl⟩ : syracuseStep 2742017 = 2056513) B2056513
theorem B6174467 : Blo 1827615 6174467 := bstep (se 1 (by rfl) ⟨4630850, by rfl⟩ : syracuseStep 6174467 = 9261701) B9261701
theorem B4626193 : Blo 1827615 4626193 := bstep (se 2 (by rfl) ⟨1734822, by rfl⟩ : syracuseStep 4626193 = 3469645) B3469645
theorem B2742035 : Blo 1827615 2742035 := bstep (se 1 (by rfl) ⟨2056526, by rfl⟩ : syracuseStep 2742035 = 4113053) B4113053
theorem B3086113 : Blo 1827615 3086113 := bstep (se 2 (by rfl) ⟨1157292, by rfl⟩ : syracuseStep 3086113 = 2314585) B2314585
theorem B2742065 : Blo 1827615 2742065 := bstep (se 2 (by rfl) ⟨1028274, by rfl⟩ : syracuseStep 2742065 = 2056549) B2056549
theorem B6944561 : Blo 1827615 6944561 := bstep (se 2 (by rfl) ⟨2604210, by rfl⟩ : syracuseStep 6944561 = 5208421) B5208421
theorem B2742083 : Blo 1827615 2742083 := bstep (se 1 (by rfl) ⟨2056562, by rfl⟩ : syracuseStep 2742083 = 4113125) B4113125
theorem B2504515 : Blo 1827615 2504515 := bstep (se 1 (by rfl) ⟨1878386, by rfl⟩ : syracuseStep 2504515 = 3756773) B3756773
theorem B3086147 : Blo 1827615 3086147 := bstep (se 1 (by rfl) ⟨2314610, by rfl⟩ : syracuseStep 3086147 = 4629221) B4629221
theorem B5011267 : Blo 1827615 5011267 := bstep (se 1 (by rfl) ⟨3758450, by rfl⟩ : syracuseStep 5011267 = 7516901) B7516901
theorem B5207885 : Blo 1827615 5207885 := bstep (se 3 (by rfl) ⟨976478, by rfl⟩ : syracuseStep 5207885 = 1952957) B1952957
theorem B4757329 : Blo 1827615 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B2602849 : Blo 1827615 2602849 := bstep (se 2 (by rfl) ⟨976068, by rfl⟩ : syracuseStep 2602849 = 1952137) B1952137
theorem B2742113 : Blo 1827615 2742113 := bstep (se 2 (by rfl) ⟨1028292, by rfl⟩ : syracuseStep 2742113 = 2056585) B2056585
theorem B2742131 : Blo 1827615 2742131 := bstep (se 1 (by rfl) ⟨2056598, by rfl⟩ : syracuseStep 2742131 = 4113197) B4113197
theorem B2930563 : Blo 1827615 2930563 := bstep (se 1 (by rfl) ⟨2197922, by rfl⟩ : syracuseStep 2930563 = 4395845) B4395845
theorem B2742161 : Blo 1827615 2742161 := bstep (se 2 (by rfl) ⟨1028310, by rfl⟩ : syracuseStep 2742161 = 2056621) B2056621
theorem B2742179 : Blo 1827615 2742179 := bstep (se 1 (by rfl) ⟨2056634, by rfl⟩ : syracuseStep 2742179 = 4113269) B4113269
theorem B2742209 : Blo 1827615 2742209 := bstep (se 2 (by rfl) ⟨1028328, by rfl⟩ : syracuseStep 2742209 = 2056657) B2056657
theorem B3086275 : Blo 1827615 3086275 := bstep (se 1 (by rfl) ⟨2314706, by rfl⟩ : syracuseStep 3086275 = 4629413) B4629413
theorem B2602963 : Blo 1827615 2602963 := bstep (se 1 (by rfl) ⟨1952222, by rfl⟩ : syracuseStep 2602963 = 3904445) B3904445
theorem B2742227 : Blo 1827615 2742227 := bstep (se 1 (by rfl) ⟨2056670, by rfl⟩ : syracuseStep 2742227 = 4113341) B4113341
theorem B3471331 : Blo 1827615 3471331 := bstep (se 1 (by rfl) ⟨2603498, by rfl⟩ : syracuseStep 3471331 = 5206997) B5206997
theorem B9254897 : Blo 1827615 9254897 := bstep (se 2 (by rfl) ⟨3470586, by rfl⟩ : syracuseStep 9254897 = 6941173) B6941173
theorem B2742257 : Blo 1827615 2742257 := bstep (se 2 (by rfl) ⟨1028346, by rfl⟩ : syracuseStep 2742257 = 2056693) B2056693
theorem B2742275 : Blo 1827615 2742275 := bstep (se 1 (by rfl) ⟨2056706, by rfl⟩ : syracuseStep 2742275 = 4113413) B4113413
theorem B5208067 : Blo 1827615 5208067 := bstep (se 1 (by rfl) ⟨3906050, by rfl⟩ : syracuseStep 5208067 = 7812101) B7812101
theorem B20051981 : Blo 1827615 20051981 := bstep (se 3 (by rfl) ⟨3759746, by rfl⟩ : syracuseStep 20051981 = 7519493) B7519493
theorem B6174737 : Blo 1827615 6174737 := bstep (se 2 (by rfl) ⟨2315526, by rfl⟩ : syracuseStep 6174737 = 4631053) B4631053
theorem B2742305 : Blo 1827615 2742305 := bstep (se 2 (by rfl) ⟨1028364, by rfl⟩ : syracuseStep 2742305 = 2056729) B2056729
theorem B4626467 : Blo 1827615 4626467 := bstep (se 1 (by rfl) ⟨3469850, by rfl⟩ : syracuseStep 4626467 = 6939701) B6939701
theorem B5208113 : Blo 1827615 5208113 := bstep (se 2 (by rfl) ⟨1953042, by rfl⟩ : syracuseStep 5208113 = 3906085) B3906085
theorem B2742323 : Blo 1827615 2742323 := bstep (se 1 (by rfl) ⟨2056742, by rfl⟩ : syracuseStep 2742323 = 4113485) B4113485
theorem B2742353 : Blo 1827615 2742353 := bstep (se 2 (by rfl) ⟨1028382, by rfl⟩ : syracuseStep 2742353 = 2056765) B2056765
theorem B3086417 : Blo 1827615 3086417 := bstep (se 2 (by rfl) ⟨1157406, by rfl⟩ : syracuseStep 3086417 = 2314813) B2314813
theorem B2742371 : Blo 1827615 2742371 := bstep (se 1 (by rfl) ⟨2056778, by rfl⟩ : syracuseStep 2742371 = 4113557) B4113557
theorem B2742401 : Blo 1827615 2742401 := bstep (se 2 (by rfl) ⟨1028400, by rfl⟩ : syracuseStep 2742401 = 2056801) B2056801
theorem B3471491 : Blo 1827615 3471491 := bstep (se 1 (by rfl) ⟨2603618, by rfl⟩ : syracuseStep 3471491 = 5207237) B5207237
theorem B2742419 : Blo 1827615 2742419 := bstep (se 1 (by rfl) ⟨2056814, by rfl⟩ : syracuseStep 2742419 = 4113629) B4113629
theorem B2742449 : Blo 1827615 2742449 := bstep (se 2 (by rfl) ⟨1028418, by rfl⟩ : syracuseStep 2742449 = 2056837) B2056837
theorem B2742467 : Blo 1827615 2742467 := bstep (se 1 (by rfl) ⟨2056850, by rfl⟩ : syracuseStep 2742467 = 4113701) B4113701
theorem B5560525 : Blo 1827615 5560525 := bstep (se 3 (by rfl) ⟨1042598, by rfl⟩ : syracuseStep 5560525 = 2085197) B2085197
theorem B3086545 : Blo 1827615 3086545 := bstep (se 2 (by rfl) ⟨1157454, by rfl⟩ : syracuseStep 3086545 = 2314909) B2314909
theorem B2742497 : Blo 1827615 2742497 := bstep (se 2 (by rfl) ⟨1028436, by rfl⟩ : syracuseStep 2742497 = 2056873) B2056873
theorem B4626659 : Blo 1827615 4626659 := bstep (se 1 (by rfl) ⟨3469994, by rfl⟩ : syracuseStep 4626659 = 6939989) B6939989
theorem B3905777 : Blo 1827615 3905777 := bstep (se 2 (by rfl) ⟨1464666, by rfl⟩ : syracuseStep 3905777 = 2929333) B2929333
theorem B16685297 : Blo 1827615 16685297 := bstep (se 2 (by rfl) ⟨6256986, by rfl⟩ : syracuseStep 16685297 = 12513973) B12513973
theorem B2742515 : Blo 1827615 2742515 := bstep (se 1 (by rfl) ⟨2056886, by rfl⟩ : syracuseStep 2742515 = 4113773) B4113773
theorem B3086579 : Blo 1827615 3086579 := bstep (se 1 (by rfl) ⟨2314934, by rfl⟩ : syracuseStep 3086579 = 4629869) B4629869
theorem B3905795 : Blo 1827615 3905795 := bstep (se 1 (by rfl) ⟨2929346, by rfl⟩ : syracuseStep 3905795 = 5858693) B5858693
theorem B2742545 : Blo 1827615 2742545 := bstep (se 2 (by rfl) ⟨1028454, by rfl⟩ : syracuseStep 2742545 = 2056909) B2056909
theorem B2742563 : Blo 1827615 2742563 := bstep (se 1 (by rfl) ⟨2056922, by rfl⟩ : syracuseStep 2742563 = 4113845) B4113845
theorem B2742593 : Blo 1827615 2742593 := bstep (se 2 (by rfl) ⟨1028472, by rfl⟩ : syracuseStep 2742593 = 2056945) B2056945
theorem B2742611 : Blo 1827615 2742611 := bstep (se 1 (by rfl) ⟨2056958, by rfl⟩ : syracuseStep 2742611 = 4113917) B4113917
theorem B2742641 : Blo 1827615 2742641 := bstep (se 2 (by rfl) ⟨1028490, by rfl⟩ : syracuseStep 2742641 = 2056981) B2056981
theorem B3086707 : Blo 1827615 3086707 := bstep (se 1 (by rfl) ⟨2315030, by rfl⟩ : syracuseStep 3086707 = 4630061) B4630061
theorem B2742659 : Blo 1827615 2742659 := bstep (se 1 (by rfl) ⟨2056994, by rfl⟩ : syracuseStep 2742659 = 4113989) B4113989
theorem B2742689 : Blo 1827615 2742689 := bstep (se 2 (by rfl) ⟨1028508, by rfl⟩ : syracuseStep 2742689 = 2057017) B2057017
theorem B2742707 : Blo 1827615 2742707 := bstep (se 1 (by rfl) ⟨2057030, by rfl⟩ : syracuseStep 2742707 = 4114061) B4114061
theorem B2742737 : Blo 1827615 2742737 := bstep (se 2 (by rfl) ⟨1028526, by rfl⟩ : syracuseStep 2742737 = 2057053) B2057053
theorem B2742755 : Blo 1827615 2742755 := bstep (se 1 (by rfl) ⟨2057066, by rfl⟩ : syracuseStep 2742755 = 4114133) B4114133
theorem B2742785 : Blo 1827615 2742785 := bstep (se 2 (by rfl) ⟨1028544, by rfl⟩ : syracuseStep 2742785 = 2057089) B2057089
theorem B3086849 : Blo 1827615 3086849 := bstep (se 2 (by rfl) ⟨1157568, by rfl⟩ : syracuseStep 3086849 = 2315137) B2315137
theorem B2742803 : Blo 1827615 2742803 := bstep (se 1 (by rfl) ⟨2057102, by rfl⟩ : syracuseStep 2742803 = 4114205) B4114205
theorem B2742833 : Blo 1827615 2742833 := bstep (se 2 (by rfl) ⟨1028562, by rfl⟩ : syracuseStep 2742833 = 2057125) B2057125
theorem B2742851 : Blo 1827615 2742851 := bstep (se 1 (by rfl) ⟨2057138, by rfl⟩ : syracuseStep 2742851 = 4114277) B4114277
theorem B2742881 : Blo 1827615 2742881 := bstep (se 2 (by rfl) ⟨1028580, by rfl⟩ : syracuseStep 2742881 = 2057161) B2057161
theorem B14080625 : Blo 1827615 14080625 := bstep (se 2 (by rfl) ⟨5280234, by rfl⟩ : syracuseStep 14080625 = 10560469) B10560469
theorem B2742899 : Blo 1827615 2742899 := bstep (se 1 (by rfl) ⟨2057174, by rfl⟩ : syracuseStep 2742899 = 4114349) B4114349
theorem B3086977 : Blo 1827615 3086977 := bstep (se 2 (by rfl) ⟨1157616, by rfl⟩ : syracuseStep 3086977 = 2315233) B2315233
theorem B2742929 : Blo 1827615 2742929 := bstep (se 2 (by rfl) ⟨1028598, by rfl⟩ : syracuseStep 2742929 = 2057197) B2057197
theorem B2742947 : Blo 1827615 2742947 := bstep (se 1 (by rfl) ⟨2057210, by rfl⟩ : syracuseStep 2742947 = 4114421) B4114421
theorem B3087011 : Blo 1827615 3087011 := bstep (se 1 (by rfl) ⟨2315258, by rfl⟩ : syracuseStep 3087011 = 4630517) B4630517
theorem B2742977 : Blo 1827615 2742977 := bstep (se 2 (by rfl) ⟨1028616, by rfl⟩ : syracuseStep 2742977 = 2057233) B2057233
theorem B2742995 : Blo 1827615 2742995 := bstep (se 1 (by rfl) ⟨2057246, by rfl⟩ : syracuseStep 2742995 = 4114493) B4114493
theorem B2743025 : Blo 1827615 2743025 := bstep (se 2 (by rfl) ⟨1028634, by rfl⟩ : syracuseStep 2743025 = 2057269) B2057269
theorem B2743043 : Blo 1827615 2743043 := bstep (se 1 (by rfl) ⟨2057282, by rfl⟩ : syracuseStep 2743043 = 4114565) B4114565
theorem B2743073 : Blo 1827615 2743073 := bstep (se 2 (by rfl) ⟨1028652, by rfl⟩ : syracuseStep 2743073 = 2057305) B2057305
theorem B3087139 : Blo 1827615 3087139 := bstep (se 1 (by rfl) ⟨2315354, by rfl⟩ : syracuseStep 3087139 = 4630709) B4630709
theorem B2743091 : Blo 1827615 2743091 := bstep (se 1 (by rfl) ⟨2057318, by rfl⟩ : syracuseStep 2743091 = 4114637) B4114637
theorem B2743121 : Blo 1827615 2743121 := bstep (se 2 (by rfl) ⟨1028670, by rfl⟩ : syracuseStep 2743121 = 2057341) B2057341
theorem B2743139 : Blo 1827615 2743139 := bstep (se 1 (by rfl) ⟨2057354, by rfl⟩ : syracuseStep 2743139 = 4114709) B4114709
theorem B2743169 : Blo 1827615 2743169 := bstep (se 2 (by rfl) ⟨1028688, by rfl⟩ : syracuseStep 2743169 = 2057377) B2057377
theorem B2743187 : Blo 1827615 2743187 := bstep (se 1 (by rfl) ⟨2057390, by rfl⟩ : syracuseStep 2743187 = 4114781) B4114781
theorem B2743217 : Blo 1827615 2743217 := bstep (se 2 (by rfl) ⟨1028706, by rfl⟩ : syracuseStep 2743217 = 2057413) B2057413
theorem B3087281 : Blo 1827615 3087281 := bstep (se 2 (by rfl) ⟨1157730, by rfl⟩ : syracuseStep 3087281 = 2315461) B2315461
theorem B2743235 : Blo 1827615 2743235 := bstep (se 1 (by rfl) ⟨2057426, by rfl⟩ : syracuseStep 2743235 = 4114853) B4114853
theorem B10705861 : Blo 1827615 10705861 := bstep (se 4 (by rfl) ⟨1003674, by rfl⟩ : syracuseStep 10705861 = 2007349) B2007349
theorem B2743265 : Blo 1827615 2743265 := bstep (se 2 (by rfl) ⟨1028724, by rfl⟩ : syracuseStep 2743265 = 2057449) B2057449
theorem B4455395 : Blo 1827615 4455395 := bstep (se 1 (by rfl) ⟨3341546, by rfl⟩ : syracuseStep 4455395 = 6683093) B6683093
theorem B2743283 : Blo 1827615 2743283 := bstep (se 1 (by rfl) ⟨2057462, by rfl⟩ : syracuseStep 2743283 = 4114925) B4114925
theorem B2743313 : Blo 1827615 2743313 := bstep (se 2 (by rfl) ⟨1028742, by rfl⟩ : syracuseStep 2743313 = 2057485) B2057485
theorem B3808291 : Blo 1827615 3808291 := bstep (se 1 (by rfl) ⟨2856218, by rfl⟩ : syracuseStep 3808291 = 5712437) B5712437
theorem B2743331 : Blo 1827615 2743331 := bstep (se 1 (by rfl) ⟨2057498, by rfl⟩ : syracuseStep 2743331 = 4114997) B4114997
theorem B3087409 : Blo 1827615 3087409 := bstep (se 2 (by rfl) ⟨1157778, by rfl⟩ : syracuseStep 3087409 = 2315557) B2315557
theorem B2743361 : Blo 1827615 2743361 := bstep (se 2 (by rfl) ⟨1028760, by rfl⟩ : syracuseStep 2743361 = 2057521) B2057521
theorem B2743379 : Blo 1827615 2743379 := bstep (se 1 (by rfl) ⟨2057534, by rfl⟩ : syracuseStep 2743379 = 4115069) B4115069
theorem B3087443 : Blo 1827615 3087443 := bstep (se 1 (by rfl) ⟨2315582, by rfl⟩ : syracuseStep 3087443 = 4631165) B4631165
theorem B3759203 : Blo 1827615 3759203 := bstep (se 1 (by rfl) ⟨2819402, by rfl⟩ : syracuseStep 3759203 = 5638805) B5638805
theorem B16678001 : Blo 1827615 16678001 := bstep (se 2 (by rfl) ⟨6254250, by rfl⟩ : syracuseStep 16678001 = 12508501) B12508501
theorem B2743409 : Blo 1827615 2743409 := bstep (se 2 (by rfl) ⟨1028778, by rfl⟩ : syracuseStep 2743409 = 2057557) B2057557
theorem B2743427 : Blo 1827615 2743427 := bstep (se 1 (by rfl) ⟨2057570, by rfl⟩ : syracuseStep 2743427 = 4115141) B4115141
theorem B4627601 : Blo 1827615 4627601 := bstep (se 2 (by rfl) ⟨1735350, by rfl⟩ : syracuseStep 4627601 = 3470701) B3470701
theorem B2743457 : Blo 1827615 2743457 := bstep (se 2 (by rfl) ⟨1028796, by rfl⟩ : syracuseStep 2743457 = 2057593) B2057593
theorem B3472561 : Blo 1827615 3472561 := bstep (se 2 (by rfl) ⟨1302210, by rfl⟩ : syracuseStep 3472561 = 2604421) B2604421
theorem B2743475 : Blo 1827615 2743475 := bstep (se 1 (by rfl) ⟨2057606, by rfl⟩ : syracuseStep 2743475 = 4115213) B4115213
theorem B4627651 : Blo 1827615 4627651 := bstep (se 1 (by rfl) ⟨3470738, by rfl⟩ : syracuseStep 4627651 = 6941477) B6941477
theorem B10411213 : Blo 1827615 10411213 := bstep (se 3 (by rfl) ⟨1952102, by rfl⟩ : syracuseStep 10411213 = 3904205) B3904205
theorem B2743505 : Blo 1827615 2743505 := bstep (se 2 (by rfl) ⟨1028814, by rfl⟩ : syracuseStep 2743505 = 2057629) B2057629
theorem B2112739 : Blo 1827615 2112739 := bstep (se 1 (by rfl) ⟨1584554, by rfl⟩ : syracuseStep 2112739 = 3169109) B3169109
theorem B2743523 : Blo 1827615 2743523 := bstep (se 1 (by rfl) ⟨2057642, by rfl⟩ : syracuseStep 2743523 = 4115285) B4115285
theorem B6946019 : Blo 1827615 6946019 := bstep (se 1 (by rfl) ⟨5209514, by rfl⟩ : syracuseStep 6946019 = 10419029) B10419029
theorem B6946033 : Blo 1827615 6946033 := bstep (se 2 (by rfl) ⟨2604762, by rfl⟩ : syracuseStep 6946033 = 5209525) B5209525
theorem B2743553 : Blo 1827615 2743553 := bstep (se 2 (by rfl) ⟨1028832, by rfl⟩ : syracuseStep 2743553 = 2057665) B2057665
theorem B10419461 : Blo 1827615 10419461 := bstep (se 4 (by rfl) ⟨976824, by rfl⟩ : syracuseStep 10419461 = 1953649) B1953649
theorem B2743571 : Blo 1827615 2743571 := bstep (se 1 (by rfl) ⟨2057678, by rfl⟩ : syracuseStep 2743571 = 4115357) B4115357
theorem B2604307 : Blo 1827615 2604307 := bstep (se 1 (by rfl) ⟨1953230, by rfl⟩ : syracuseStep 2604307 = 3906461) B3906461
theorem B2743601 : Blo 1827615 2743601 := bstep (se 2 (by rfl) ⟨1028850, by rfl⟩ : syracuseStep 2743601 = 2057701) B2057701
theorem B2743619 : Blo 1827615 2743619 := bstep (se 1 (by rfl) ⟨2057714, by rfl⟩ : syracuseStep 2743619 = 4115429) B4115429
theorem B4627793 : Blo 1827615 4627793 := bstep (se 2 (by rfl) ⟨1735422, by rfl⟩ : syracuseStep 4627793 = 3470845) B3470845
theorem B2743649 : Blo 1827615 2743649 := bstep (se 2 (by rfl) ⟨1028868, by rfl⟩ : syracuseStep 2743649 = 2057737) B2057737
theorem B2743667 : Blo 1827615 2743667 := bstep (se 1 (by rfl) ⟨2057750, by rfl⟩ : syracuseStep 2743667 = 4115501) B4115501
theorem B18759053 : Blo 1827615 18759053 := bstep (se 3 (by rfl) ⟨3517322, by rfl⟩ : syracuseStep 18759053 = 7034645) B7034645
theorem B2743697 : Blo 1827615 2743697 := bstep (se 2 (by rfl) ⟨1028886, by rfl⟩ : syracuseStep 2743697 = 2057773) B2057773
theorem B9256355 : Blo 1827615 9256355 := bstep (se 1 (by rfl) ⟨6942266, by rfl⟩ : syracuseStep 9256355 = 13884533) B13884533
theorem B2743715 : Blo 1827615 2743715 := bstep (se 1 (by rfl) ⟨2057786, by rfl⟩ : syracuseStep 2743715 = 4115573) B4115573
theorem B2743745 : Blo 1827615 2743745 := bstep (se 2 (by rfl) ⟨1028904, by rfl⟩ : syracuseStep 2743745 = 2057809) B2057809
theorem B16686533 : Blo 1827615 16686533 := bstep (se 4 (by rfl) ⟨1564362, by rfl⟩ : syracuseStep 16686533 = 3128725) B3128725
theorem B3907025 : Blo 1827615 3907025 := bstep (se 2 (by rfl) ⟨1465134, by rfl⟩ : syracuseStep 3907025 = 2930269) B2930269
theorem B2743763 : Blo 1827615 2743763 := bstep (se 1 (by rfl) ⟨2057822, by rfl⟩ : syracuseStep 2743763 = 4115645) B4115645
theorem B5209571 : Blo 1827615 5209571 := bstep (se 1 (by rfl) ⟨3907178, by rfl⟩ : syracuseStep 5209571 = 7814357) B7814357
theorem B2743793 : Blo 1827615 2743793 := bstep (se 2 (by rfl) ⟨1028922, by rfl⟩ : syracuseStep 2743793 = 2057845) B2057845
theorem B2743811 : Blo 1827615 2743811 := bstep (se 1 (by rfl) ⟨2057858, by rfl⟩ : syracuseStep 2743811 = 4115717) B4115717
theorem B2743841 : Blo 1827615 2743841 := bstep (se 2 (by rfl) ⟨1028940, by rfl⟩ : syracuseStep 2743841 = 2057881) B2057881
theorem B2743859 : Blo 1827615 2743859 := bstep (se 1 (by rfl) ⟨2057894, by rfl⟩ : syracuseStep 2743859 = 4115789) B4115789
theorem B2743889 : Blo 1827615 2743889 := bstep (se 2 (by rfl) ⟨1028958, by rfl⟩ : syracuseStep 2743889 = 2057917) B2057917
theorem B2743907 : Blo 1827615 2743907 := bstep (se 1 (by rfl) ⟨2057930, by rfl⟩ : syracuseStep 2743907 = 4115861) B4115861
theorem B2743937 : Blo 1827615 2743937 := bstep (se 2 (by rfl) ⟨1028976, by rfl⟩ : syracuseStep 2743937 = 2057953) B2057953
theorem B2743955 : Blo 1827615 2743955 := bstep (se 1 (by rfl) ⟨2057966, by rfl⟩ : syracuseStep 2743955 = 4115933) B4115933
theorem B7814819 : Blo 1827615 7814819 := bstep (se 1 (by rfl) ⟨5861114, by rfl⟩ : syracuseStep 7814819 = 11722229) B11722229
theorem B7618225 : Blo 1827615 7618225 := bstep (se 2 (by rfl) ⟨2856834, by rfl⟩ : syracuseStep 7618225 = 5713669) B5713669
theorem B2743985 : Blo 1827615 2743985 := bstep (se 2 (by rfl) ⟨1028994, by rfl⟩ : syracuseStep 2743985 = 2057989) B2057989
theorem B2744003 : Blo 1827615 2744003 := bstep (se 1 (by rfl) ⟨2058002, by rfl⟩ : syracuseStep 2744003 = 4116005) B4116005
theorem B2744033 : Blo 1827615 2744033 := bstep (se 2 (by rfl) ⟨1029012, by rfl⟩ : syracuseStep 2744033 = 2058025) B2058025
theorem B5562083 : Blo 1827615 5562083 := bstep (se 1 (by rfl) ⟨4171562, by rfl⟩ : syracuseStep 5562083 = 8343125) B8343125
theorem B2744051 : Blo 1827615 2744051 := bstep (se 1 (by rfl) ⟨2058038, by rfl⟩ : syracuseStep 2744051 = 4116077) B4116077
theorem B2744081 : Blo 1827615 2744081 := bstep (se 2 (by rfl) ⟨1029030, by rfl⟩ : syracuseStep 2744081 = 2058061) B2058061
theorem B2744099 : Blo 1827615 2744099 := bstep (se 1 (by rfl) ⟨2058074, by rfl⟩ : syracuseStep 2744099 = 4116149) B4116149
theorem B6168365 : Blo 1827615 6168365 := bstep (se 3 (by rfl) ⟨1156568, by rfl⟩ : syracuseStep 6168365 = 2313137) B2313137
theorem B2744129 : Blo 1827615 2744129 := bstep (se 2 (by rfl) ⟨1029048, by rfl⟩ : syracuseStep 2744129 = 2058097) B2058097
theorem B2744147 : Blo 1827615 2744147 := bstep (se 1 (by rfl) ⟨2058110, by rfl⟩ : syracuseStep 2744147 = 4116221) B4116221
theorem B6168419 : Blo 1827615 6168419 := bstep (se 1 (by rfl) ⟨4626314, by rfl⟩ : syracuseStep 6168419 = 9252629) B9252629
theorem B2744177 : Blo 1827615 2744177 := bstep (se 2 (by rfl) ⟨1029066, by rfl⟩ : syracuseStep 2744177 = 2058133) B2058133
theorem B2744195 : Blo 1827615 2744195 := bstep (se 1 (by rfl) ⟨2058146, by rfl⟩ : syracuseStep 2744195 = 4116293) B4116293
theorem B2744225 : Blo 1827615 2744225 := bstep (se 2 (by rfl) ⟨1029084, by rfl⟩ : syracuseStep 2744225 = 2058169) B2058169
theorem B2056099 : Blo 1827615 2056099 := bstep (se 1 (by rfl) ⟨1542074, by rfl⟩ : syracuseStep 2056099 = 3084149) B3084149
theorem B2744243 : Blo 1827615 2744243 := bstep (se 1 (by rfl) ⟨2058182, by rfl⟩ : syracuseStep 2744243 = 4116365) B4116365
theorem B2744273 : Blo 1827615 2744273 := bstep (se 2 (by rfl) ⟨1029102, by rfl⟩ : syracuseStep 2744273 = 2058205) B2058205
theorem B2744291 : Blo 1827615 2744291 := bstep (se 1 (by rfl) ⟨2058218, by rfl⟩ : syracuseStep 2744291 = 4116437) B4116437
theorem B4112369 : Blo 1827615 4112369 := bstep (se 2 (by rfl) ⟨1542138, by rfl⟩ : syracuseStep 4112369 = 3084277) B3084277
theorem B15630353 : Blo 1827615 15630353 := bstep (se 2 (by rfl) ⟨5861382, by rfl⟩ : syracuseStep 15630353 = 11722765) B11722765
theorem B2744345 : Blo 1827615 2744345 := bstep (se 2 (by rfl) ⟨1029129, by rfl⟩ : syracuseStep 2744345 = 2058259) B2058259
theorem B13885505 : Blo 1827615 13885505 := bstep (se 2 (by rfl) ⟨5207064, by rfl⟩ : syracuseStep 13885505 = 10414129) B10414129
theorem B4112459 : Blo 1827615 4112459 := bstep (se 1 (by rfl) ⟨3084344, by rfl⟩ : syracuseStep 4112459 = 6168689) B6168689
theorem B2056279 : Blo 1827615 2056279 := bstep (se 1 (by rfl) ⟨1542209, by rfl⟩ : syracuseStep 2056279 = 3084419) B3084419
theorem B4112513 : Blo 1827615 4112513 := bstep (se 2 (by rfl) ⟨1542192, by rfl⟩ : syracuseStep 4112513 = 3084385) B3084385
theorem B6168797 : Blo 1827615 6168797 := bstep (se 3 (by rfl) ⟨1156649, by rfl⟩ : syracuseStep 6168797 = 2313299) B2313299
theorem B2056459 : Blo 1827615 2056459 := bstep (se 1 (by rfl) ⟨1542344, by rfl⟩ : syracuseStep 2056459 = 3084689) B3084689
theorem B7414033 : Blo 1827615 7414033 := bstep (se 2 (by rfl) ⟨2780262, by rfl⟩ : syracuseStep 7414033 = 5560525) B5560525
theorem B4112729 : Blo 1827615 4112729 := bstep (se 2 (by rfl) ⟨1542273, by rfl⟩ : syracuseStep 4112729 = 3084547) B3084547
theorem B2056567 : Blo 1827615 2056567 := bstep (se 1 (by rfl) ⟨1542425, by rfl⟩ : syracuseStep 2056567 = 3084851) B3084851
theorem B4112819 : Blo 1827615 4112819 := bstep (se 1 (by rfl) ⟨3084614, by rfl⟩ : syracuseStep 4112819 = 6169229) B6169229
theorem B4112855 : Blo 1827615 4112855 := bstep (se 1 (by rfl) ⟨3084641, by rfl⟩ : syracuseStep 4112855 = 6169283) B6169283
theorem B52724195 : Blo 1827615 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B9257489 : Blo 1827615 9257489 := bstep (se 2 (by rfl) ⟨3471558, by rfl⟩ : syracuseStep 9257489 = 6943117) B6943117
theorem B2056747 : Blo 1827615 2056747 := bstep (se 1 (by rfl) ⟨1542560, by rfl⟩ : syracuseStep 2056747 = 3085121) B3085121
theorem B6939229 : Blo 1827615 6939229 := bstep (se 3 (by rfl) ⟨1301105, by rfl⟩ : syracuseStep 6939229 = 2602211) B2602211
theorem B4113035 : Blo 1827615 4113035 := bstep (se 1 (by rfl) ⟨3084776, by rfl⟩ : syracuseStep 4113035 = 6169553) B6169553
theorem B2056855 : Blo 1827615 2056855 := bstep (se 1 (by rfl) ⟨1542641, by rfl⟩ : syracuseStep 2056855 = 3085283) B3085283
theorem B9257651 : Blo 1827615 9257651 := bstep (se 1 (by rfl) ⟨6943238, by rfl⟩ : syracuseStep 9257651 = 13886477) B13886477
theorem B4113089 : Blo 1827615 4113089 := bstep (se 2 (by rfl) ⟨1542408, by rfl⟩ : syracuseStep 4113089 = 3084817) B3084817
theorem B4629271 : Blo 1827615 4629271 := bstep (se 1 (by rfl) ⟨3471953, by rfl⟩ : syracuseStep 4629271 = 6943907) B6943907
theorem B1827627 : Blo 1827615 1827627 := bstep (se 1 (by rfl) ⟨1370720, by rfl⟩ : syracuseStep 1827627 = 2741441) B2741441
theorem B1827639 : Blo 1827615 1827639 := bstep (se 1 (by rfl) ⟨1370729, by rfl⟩ : syracuseStep 1827639 = 2741459) B2741459
theorem B1827659 : Blo 1827615 1827659 := bstep (se 1 (by rfl) ⟨1370744, by rfl⟩ : syracuseStep 1827659 = 2741489) B2741489
theorem B2057035 : Blo 1827615 2057035 := bstep (se 1 (by rfl) ⟨1542776, by rfl⟩ : syracuseStep 2057035 = 3085553) B3085553
theorem B1827671 : Blo 1827615 1827671 := bstep (se 1 (by rfl) ⟨1370753, by rfl⟩ : syracuseStep 1827671 = 2741507) B2741507
theorem B6341465 : Blo 1827615 6341465 := bstep (se 2 (by rfl) ⟨2378049, by rfl⟩ : syracuseStep 6341465 = 4756099) B4756099
theorem B1827691 : Blo 1827615 1827691 := bstep (se 1 (by rfl) ⟨1370768, by rfl⟩ : syracuseStep 1827691 = 2741537) B2741537
theorem B1827703 : Blo 1827615 1827703 := bstep (se 1 (by rfl) ⟨1370777, by rfl⟩ : syracuseStep 1827703 = 2741555) B2741555
theorem B1827723 : Blo 1827615 1827723 := bstep (se 1 (by rfl) ⟨1370792, by rfl⟩ : syracuseStep 1827723 = 2741585) B2741585
theorem B1827735 : Blo 1827615 1827735 := bstep (se 1 (by rfl) ⟨1370801, by rfl⟩ : syracuseStep 1827735 = 2741603) B2741603
theorem B4113305 : Blo 1827615 4113305 := bstep (se 2 (by rfl) ⟨1542489, by rfl⟩ : syracuseStep 4113305 = 3084979) B3084979
theorem B1827755 : Blo 1827615 1827755 := bstep (se 1 (by rfl) ⟨1370816, by rfl⟩ : syracuseStep 1827755 = 2741633) B2741633
theorem B1827767 : Blo 1827615 1827767 := bstep (se 1 (by rfl) ⟨1370825, by rfl⟩ : syracuseStep 1827767 = 2741651) B2741651
theorem B2057143 : Blo 1827615 2057143 := bstep (se 1 (by rfl) ⟨1542857, by rfl⟩ : syracuseStep 2057143 = 3085715) B3085715
theorem B1827787 : Blo 1827615 1827787 := bstep (se 1 (by rfl) ⟨1370840, by rfl⟩ : syracuseStep 1827787 = 2741681) B2741681
theorem B1827799 : Blo 1827615 1827799 := bstep (se 1 (by rfl) ⟨1370849, by rfl⟩ : syracuseStep 1827799 = 2741699) B2741699
theorem B1827819 : Blo 1827615 1827819 := bstep (se 1 (by rfl) ⟨1370864, by rfl⟩ : syracuseStep 1827819 = 2741729) B2741729
theorem B4113395 : Blo 1827615 4113395 := bstep (se 1 (by rfl) ⟨3085046, by rfl⟩ : syracuseStep 4113395 = 6170093) B6170093
theorem B1827831 : Blo 1827615 1827831 := bstep (se 1 (by rfl) ⟨1370873, by rfl⟩ : syracuseStep 1827831 = 2741747) B2741747
theorem B1827851 : Blo 1827615 1827851 := bstep (se 1 (by rfl) ⟨1370888, by rfl⟩ : syracuseStep 1827851 = 2741777) B2741777
theorem B1827863 : Blo 1827615 1827863 := bstep (se 1 (by rfl) ⟨1370897, by rfl⟩ : syracuseStep 1827863 = 2741795) B2741795
theorem B4113431 : Blo 1827615 4113431 := bstep (se 1 (by rfl) ⟨3085073, by rfl⟩ : syracuseStep 4113431 = 6170147) B6170147
theorem B1827883 : Blo 1827615 1827883 := bstep (se 1 (by rfl) ⟨1370912, by rfl⟩ : syracuseStep 1827883 = 2741825) B2741825
theorem B1827895 : Blo 1827615 1827895 := bstep (se 1 (by rfl) ⟨1370921, by rfl⟩ : syracuseStep 1827895 = 2741843) B2741843
theorem B1827915 : Blo 1827615 1827915 := bstep (se 1 (by rfl) ⟨1370936, by rfl⟩ : syracuseStep 1827915 = 2741873) B2741873
theorem B3294283 : Blo 1827615 3294283 := bstep (se 1 (by rfl) ⟨2470712, by rfl⟩ : syracuseStep 3294283 = 4941425) B4941425
theorem B1827927 : Blo 1827615 1827927 := bstep (se 1 (by rfl) ⟨1370945, by rfl⟩ : syracuseStep 1827927 = 2741891) B2741891
theorem B1827947 : Blo 1827615 1827947 := bstep (se 1 (by rfl) ⟨1370960, by rfl⟩ : syracuseStep 1827947 = 2741921) B2741921
theorem B2057323 : Blo 1827615 2057323 := bstep (se 1 (by rfl) ⟨1542992, by rfl⟩ : syracuseStep 2057323 = 3085985) B3085985
theorem B1827959 : Blo 1827615 1827959 := bstep (se 1 (by rfl) ⟨1370969, by rfl⟩ : syracuseStep 1827959 = 2741939) B2741939
theorem B1827979 : Blo 1827615 1827979 := bstep (se 1 (by rfl) ⟨1370984, by rfl⟩ : syracuseStep 1827979 = 2741969) B2741969
theorem B1827991 : Blo 1827615 1827991 := bstep (se 1 (by rfl) ⟨1370993, by rfl⟩ : syracuseStep 1827991 = 2741987) B2741987
theorem B1828011 : Blo 1827615 1828011 := bstep (se 1 (by rfl) ⟨1371008, by rfl⟩ : syracuseStep 1828011 = 2742017) B2742017
theorem B1828023 : Blo 1827615 1828023 := bstep (se 1 (by rfl) ⟨1371017, by rfl⟩ : syracuseStep 1828023 = 2742035) B2742035
theorem B1828043 : Blo 1827615 1828043 := bstep (se 1 (by rfl) ⟨1371032, by rfl⟩ : syracuseStep 1828043 = 2742065) B2742065
theorem B4113611 : Blo 1827615 4113611 := bstep (se 1 (by rfl) ⟨3085208, by rfl⟩ : syracuseStep 4113611 = 6170417) B6170417
theorem B4629707 : Blo 1827615 4629707 := bstep (se 1 (by rfl) ⟨3472280, by rfl⟩ : syracuseStep 4629707 = 6944561) B6944561
theorem B1828055 : Blo 1827615 1828055 := bstep (se 1 (by rfl) ⟨1371041, by rfl⟩ : syracuseStep 1828055 = 2742083) B2742083
theorem B2057431 : Blo 1827615 2057431 := bstep (se 1 (by rfl) ⟨1543073, by rfl⟩ : syracuseStep 2057431 = 3086147) B3086147
theorem B1828075 : Blo 1827615 1828075 := bstep (se 1 (by rfl) ⟨1371056, by rfl⟩ : syracuseStep 1828075 = 2742113) B2742113
theorem B1828087 : Blo 1827615 1828087 := bstep (se 1 (by rfl) ⟨1371065, by rfl⟩ : syracuseStep 1828087 = 2742131) B2742131
theorem B4113665 : Blo 1827615 4113665 := bstep (se 2 (by rfl) ⟨1542624, by rfl⟩ : syracuseStep 4113665 = 3085249) B3085249
theorem B1828107 : Blo 1827615 1828107 := bstep (se 1 (by rfl) ⟨1371080, by rfl⟩ : syracuseStep 1828107 = 2742161) B2742161
theorem B1828119 : Blo 1827615 1828119 := bstep (se 1 (by rfl) ⟨1371089, by rfl⟩ : syracuseStep 1828119 = 2742179) B2742179
theorem B1828139 : Blo 1827615 1828139 := bstep (se 1 (by rfl) ⟨1371104, by rfl⟩ : syracuseStep 1828139 = 2742209) B2742209
theorem B1828151 : Blo 1827615 1828151 := bstep (se 1 (by rfl) ⟨1371113, by rfl⟩ : syracuseStep 1828151 = 2742227) B2742227
theorem B6169931 : Blo 1827615 6169931 := bstep (se 1 (by rfl) ⟨4627448, by rfl⟩ : syracuseStep 6169931 = 9254897) B9254897
theorem B1828171 : Blo 1827615 1828171 := bstep (se 1 (by rfl) ⟨1371128, by rfl⟩ : syracuseStep 1828171 = 2742257) B2742257
theorem B1828183 : Blo 1827615 1828183 := bstep (se 1 (by rfl) ⟨1371137, by rfl⟩ : syracuseStep 1828183 = 2742275) B2742275
theorem B1828203 : Blo 1827615 1828203 := bstep (se 1 (by rfl) ⟨1371152, by rfl⟩ : syracuseStep 1828203 = 2742305) B2742305
theorem B1828215 : Blo 1827615 1828215 := bstep (se 1 (by rfl) ⟨1371161, by rfl⟩ : syracuseStep 1828215 = 2742323) B2742323
theorem B1828235 : Blo 1827615 1828235 := bstep (se 1 (by rfl) ⟨1371176, by rfl⟩ : syracuseStep 1828235 = 2742353) B2742353
theorem B2057611 : Blo 1827615 2057611 := bstep (se 1 (by rfl) ⟨1543208, by rfl⟩ : syracuseStep 2057611 = 3086417) B3086417
theorem B1828247 : Blo 1827615 1828247 := bstep (se 1 (by rfl) ⟨1371185, by rfl⟩ : syracuseStep 1828247 = 2742371) B2742371
theorem B1828267 : Blo 1827615 1828267 := bstep (se 1 (by rfl) ⟨1371200, by rfl⟩ : syracuseStep 1828267 = 2742401) B2742401
theorem B1828279 : Blo 1827615 1828279 := bstep (se 1 (by rfl) ⟨1371209, by rfl⟩ : syracuseStep 1828279 = 2742419) B2742419
theorem B1828299 : Blo 1827615 1828299 := bstep (se 1 (by rfl) ⟨1371224, by rfl⟩ : syracuseStep 1828299 = 2742449) B2742449
theorem B1828311 : Blo 1827615 1828311 := bstep (se 1 (by rfl) ⟨1371233, by rfl⟩ : syracuseStep 1828311 = 2742467) B2742467
theorem B4113881 : Blo 1827615 4113881 := bstep (se 2 (by rfl) ⟨1542705, by rfl⟩ : syracuseStep 4113881 = 3085411) B3085411
theorem B1828331 : Blo 1827615 1828331 := bstep (se 1 (by rfl) ⟨1371248, by rfl⟩ : syracuseStep 1828331 = 2742497) B2742497
theorem B1828343 : Blo 1827615 1828343 := bstep (se 1 (by rfl) ⟨1371257, by rfl⟩ : syracuseStep 1828343 = 2742515) B2742515
theorem B2057719 : Blo 1827615 2057719 := bstep (se 1 (by rfl) ⟨1543289, by rfl⟩ : syracuseStep 2057719 = 3086579) B3086579
theorem B1828363 : Blo 1827615 1828363 := bstep (se 1 (by rfl) ⟨1371272, by rfl⟩ : syracuseStep 1828363 = 2742545) B2742545
theorem B1828375 : Blo 1827615 1828375 := bstep (se 1 (by rfl) ⟨1371281, by rfl⟩ : syracuseStep 1828375 = 2742563) B2742563
theorem B1828395 : Blo 1827615 1828395 := bstep (se 1 (by rfl) ⟨1371296, by rfl⟩ : syracuseStep 1828395 = 2742593) B2742593
theorem B4113971 : Blo 1827615 4113971 := bstep (se 1 (by rfl) ⟨3085478, by rfl⟩ : syracuseStep 4113971 = 6170957) B6170957
theorem B1828407 : Blo 1827615 1828407 := bstep (se 1 (by rfl) ⟨1371305, by rfl⟩ : syracuseStep 1828407 = 2742611) B2742611
theorem B4630081 : Blo 1827615 4630081 := bstep (se 2 (by rfl) ⟨1736280, by rfl⟩ : syracuseStep 4630081 = 3472561) B3472561
theorem B1828427 : Blo 1827615 1828427 := bstep (se 1 (by rfl) ⟨1371320, by rfl⟩ : syracuseStep 1828427 = 2742641) B2742641
theorem B1828439 : Blo 1827615 1828439 := bstep (se 1 (by rfl) ⟨1371329, by rfl⟩ : syracuseStep 1828439 = 2742659) B2742659
theorem B4114007 : Blo 1827615 4114007 := bstep (se 1 (by rfl) ⟨3085505, by rfl⟩ : syracuseStep 4114007 = 6171011) B6171011
theorem B6170201 : Blo 1827615 6170201 := bstep (se 2 (by rfl) ⟨2313825, by rfl⟩ : syracuseStep 6170201 = 4627651) B4627651
theorem B24413789 : Blo 1827615 24413789 := bstep (se 3 (by rfl) ⟨4577585, by rfl⟩ : syracuseStep 24413789 = 9155171) B9155171
theorem B1828459 : Blo 1827615 1828459 := bstep (se 1 (by rfl) ⟨1371344, by rfl⟩ : syracuseStep 1828459 = 2742689) B2742689
theorem B1828471 : Blo 1827615 1828471 := bstep (se 1 (by rfl) ⟨1371353, by rfl⟩ : syracuseStep 1828471 = 2742707) B2742707
theorem B1828491 : Blo 1827615 1828491 := bstep (se 1 (by rfl) ⟨1371368, by rfl⟩ : syracuseStep 1828491 = 2742737) B2742737
theorem B1828503 : Blo 1827615 1828503 := bstep (se 1 (by rfl) ⟨1371377, by rfl⟩ : syracuseStep 1828503 = 2742755) B2742755
theorem B1828523 : Blo 1827615 1828523 := bstep (se 1 (by rfl) ⟨1371392, by rfl⟩ : syracuseStep 1828523 = 2742785) B2742785
theorem B2057899 : Blo 1827615 2057899 := bstep (se 1 (by rfl) ⟨1543424, by rfl⟩ : syracuseStep 2057899 = 3086849) B3086849
theorem B1828535 : Blo 1827615 1828535 := bstep (se 1 (by rfl) ⟨1371401, by rfl⟩ : syracuseStep 1828535 = 2742803) B2742803
theorem B1828555 : Blo 1827615 1828555 := bstep (se 1 (by rfl) ⟨1371416, by rfl⟩ : syracuseStep 1828555 = 2742833) B2742833
theorem B1828567 : Blo 1827615 1828567 := bstep (se 1 (by rfl) ⟨1371425, by rfl⟩ : syracuseStep 1828567 = 2742851) B2742851
theorem B1828587 : Blo 1827615 1828587 := bstep (se 1 (by rfl) ⟨1371440, by rfl⟩ : syracuseStep 1828587 = 2742881) B2742881
theorem B1828599 : Blo 1827615 1828599 := bstep (se 1 (by rfl) ⟨1371449, by rfl⟩ : syracuseStep 1828599 = 2742899) B2742899
theorem B4114187 : Blo 1827615 4114187 := bstep (se 1 (by rfl) ⟨3085640, by rfl⟩ : syracuseStep 4114187 = 6171281) B6171281
theorem B1828619 : Blo 1827615 1828619 := bstep (se 1 (by rfl) ⟨1371464, by rfl⟩ : syracuseStep 1828619 = 2742929) B2742929
theorem B1828631 : Blo 1827615 1828631 := bstep (se 1 (by rfl) ⟨1371473, by rfl⟩ : syracuseStep 1828631 = 2742947) B2742947
theorem B2058007 : Blo 1827615 2058007 := bstep (se 1 (by rfl) ⟨1543505, by rfl⟩ : syracuseStep 2058007 = 3087011) B3087011
theorem B1828651 : Blo 1827615 1828651 := bstep (se 1 (by rfl) ⟨1371488, by rfl⟩ : syracuseStep 1828651 = 2742977) B2742977
theorem B1828663 : Blo 1827615 1828663 := bstep (se 1 (by rfl) ⟨1371497, by rfl⟩ : syracuseStep 1828663 = 2742995) B2742995
theorem B4114241 : Blo 1827615 4114241 := bstep (se 2 (by rfl) ⟨1542840, by rfl⟩ : syracuseStep 4114241 = 3085681) B3085681
theorem B1828683 : Blo 1827615 1828683 := bstep (se 1 (by rfl) ⟨1371512, by rfl⟩ : syracuseStep 1828683 = 2743025) B2743025
theorem B1828695 : Blo 1827615 1828695 := bstep (se 1 (by rfl) ⟨1371521, by rfl⟩ : syracuseStep 1828695 = 2743043) B2743043
theorem B6940505 : Blo 1827615 6940505 := bstep (se 2 (by rfl) ⟨2602689, by rfl⟩ : syracuseStep 6940505 = 5205379) B5205379
theorem B1828715 : Blo 1827615 1828715 := bstep (se 1 (by rfl) ⟨1371536, by rfl⟩ : syracuseStep 1828715 = 2743073) B2743073
theorem B1828727 : Blo 1827615 1828727 := bstep (se 1 (by rfl) ⟨1371545, by rfl⟩ : syracuseStep 1828727 = 2743091) B2743091
theorem B1828747 : Blo 1827615 1828747 := bstep (se 1 (by rfl) ⟨1371560, by rfl⟩ : syracuseStep 1828747 = 2743121) B2743121
theorem B1828759 : Blo 1827615 1828759 := bstep (se 1 (by rfl) ⟨1371569, by rfl⟩ : syracuseStep 1828759 = 2743139) B2743139
theorem B1828779 : Blo 1827615 1828779 := bstep (se 1 (by rfl) ⟨1371584, by rfl⟩ : syracuseStep 1828779 = 2743169) B2743169
theorem B17565619 : Blo 1827615 17565619 := bstep (se 1 (by rfl) ⟨13174214, by rfl⟩ : syracuseStep 17565619 = 26348429) B26348429
theorem B1828791 : Blo 1827615 1828791 := bstep (se 1 (by rfl) ⟨1371593, by rfl⟩ : syracuseStep 1828791 = 2743187) B2743187
theorem B3295169 : Blo 1827615 3295169 := bstep (se 2 (by rfl) ⟨1235688, by rfl⟩ : syracuseStep 3295169 = 2471377) B2471377
theorem B3958721 : Blo 1827615 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B1828811 : Blo 1827615 1828811 := bstep (se 1 (by rfl) ⟨1371608, by rfl⟩ : syracuseStep 1828811 = 2743217) B2743217
theorem B2058187 : Blo 1827615 2058187 := bstep (se 1 (by rfl) ⟨1543640, by rfl⟩ : syracuseStep 2058187 = 3087281) B3087281
theorem B1828823 : Blo 1827615 1828823 := bstep (se 1 (by rfl) ⟨1371617, by rfl⟩ : syracuseStep 1828823 = 2743235) B2743235
theorem B13887449 : Blo 1827615 13887449 := bstep (se 2 (by rfl) ⟨5207793, by rfl⟩ : syracuseStep 13887449 = 10415587) B10415587
theorem B1951723 : Blo 1827615 1951723 := bstep (se 1 (by rfl) ⟨1463792, by rfl⟩ : syracuseStep 1951723 = 2927585) B2927585
theorem B1828843 : Blo 1827615 1828843 := bstep (se 1 (by rfl) ⟨1371632, by rfl⟩ : syracuseStep 1828843 = 2743265) B2743265
theorem B1828855 : Blo 1827615 1828855 := bstep (se 1 (by rfl) ⟨1371641, by rfl⟩ : syracuseStep 1828855 = 2743283) B2743283
theorem B1828875 : Blo 1827615 1828875 := bstep (se 1 (by rfl) ⟨1371656, by rfl⟩ : syracuseStep 1828875 = 2743313) B2743313
theorem B1828887 : Blo 1827615 1828887 := bstep (se 1 (by rfl) ⟨1371665, by rfl⟩ : syracuseStep 1828887 = 2743331) B2743331
theorem B4114457 : Blo 1827615 4114457 := bstep (se 2 (by rfl) ⟨1542921, by rfl⟩ : syracuseStep 4114457 = 3085843) B3085843
theorem B1828907 : Blo 1827615 1828907 := bstep (se 1 (by rfl) ⟨1371680, by rfl⟩ : syracuseStep 1828907 = 2743361) B2743361
theorem B1828919 : Blo 1827615 1828919 := bstep (se 1 (by rfl) ⟨1371689, by rfl⟩ : syracuseStep 1828919 = 2743379) B2743379
theorem B2058295 : Blo 1827615 2058295 := bstep (se 1 (by rfl) ⟨1543721, by rfl⟩ : syracuseStep 2058295 = 3087443) B3087443
theorem B11118667 : Blo 1827615 11118667 := bstep (se 1 (by rfl) ⟨8339000, by rfl⟩ : syracuseStep 11118667 = 16678001) B16678001
theorem B1828939 : Blo 1827615 1828939 := bstep (se 1 (by rfl) ⟨1371704, by rfl⟩ : syracuseStep 1828939 = 2743409) B2743409
theorem B1828951 : Blo 1827615 1828951 := bstep (se 1 (by rfl) ⟨1371713, by rfl⟩ : syracuseStep 1828951 = 2743427) B2743427
theorem B1828971 : Blo 1827615 1828971 := bstep (se 1 (by rfl) ⟨1371728, by rfl⟩ : syracuseStep 1828971 = 2743457) B2743457
theorem B4114547 : Blo 1827615 4114547 := bstep (se 1 (by rfl) ⟨3085910, by rfl⟩ : syracuseStep 4114547 = 6171821) B6171821
theorem B1828983 : Blo 1827615 1828983 := bstep (se 1 (by rfl) ⟨1371737, by rfl⟩ : syracuseStep 1828983 = 2743475) B2743475
theorem B1829003 : Blo 1827615 1829003 := bstep (se 1 (by rfl) ⟨1371752, by rfl⟩ : syracuseStep 1829003 = 2743505) B2743505
theorem B4114583 : Blo 1827615 4114583 := bstep (se 1 (by rfl) ⟨3085937, by rfl⟩ : syracuseStep 4114583 = 6171875) B6171875
theorem B1829015 : Blo 1827615 1829015 := bstep (se 1 (by rfl) ⟨1371761, by rfl⟩ : syracuseStep 1829015 = 2743523) B2743523
theorem B4630679 : Blo 1827615 4630679 := bstep (se 1 (by rfl) ⟨3473009, by rfl⟩ : syracuseStep 4630679 = 6946019) B6946019
theorem B1829035 : Blo 1827615 1829035 := bstep (se 1 (by rfl) ⟨1371776, by rfl⟩ : syracuseStep 1829035 = 2743553) B2743553
theorem B1829047 : Blo 1827615 1829047 := bstep (se 1 (by rfl) ⟨1371785, by rfl⟩ : syracuseStep 1829047 = 2743571) B2743571
theorem B1829067 : Blo 1827615 1829067 := bstep (se 1 (by rfl) ⟨1371800, by rfl⟩ : syracuseStep 1829067 = 2743601) B2743601
theorem B1829079 : Blo 1827615 1829079 := bstep (se 1 (by rfl) ⟨1371809, by rfl⟩ : syracuseStep 1829079 = 2743619) B2743619
theorem B1829099 : Blo 1827615 1829099 := bstep (se 1 (by rfl) ⟨1371824, by rfl⟩ : syracuseStep 1829099 = 2743649) B2743649
theorem B1829111 : Blo 1827615 1829111 := bstep (se 1 (by rfl) ⟨1371833, by rfl⟩ : syracuseStep 1829111 = 2743667) B2743667
theorem B1829131 : Blo 1827615 1829131 := bstep (se 1 (by rfl) ⟨1371848, by rfl⟩ : syracuseStep 1829131 = 2743697) B2743697
theorem B15616273 : Blo 1827615 15616273 := bstep (se 2 (by rfl) ⟨5856102, by rfl⟩ : syracuseStep 15616273 = 11712205) B11712205
theorem B6170903 : Blo 1827615 6170903 := bstep (se 1 (by rfl) ⟨4628177, by rfl⟩ : syracuseStep 6170903 = 9256355) B9256355
theorem B1829143 : Blo 1827615 1829143 := bstep (se 1 (by rfl) ⟨1371857, by rfl⟩ : syracuseStep 1829143 = 2743715) B2743715
theorem B13355299 : Blo 1827615 13355299 := bstep (se 1 (by rfl) ⟨10016474, by rfl⟩ : syracuseStep 13355299 = 20032949) B20032949
theorem B1829163 : Blo 1827615 1829163 := bstep (se 1 (by rfl) ⟨1371872, by rfl⟩ : syracuseStep 1829163 = 2743745) B2743745
theorem B1829175 : Blo 1827615 1829175 := bstep (se 1 (by rfl) ⟨1371881, by rfl⟩ : syracuseStep 1829175 = 2743763) B2743763
theorem B4114763 : Blo 1827615 4114763 := bstep (se 1 (by rfl) ⟨3086072, by rfl⟩ : syracuseStep 4114763 = 6172145) B6172145
theorem B1829195 : Blo 1827615 1829195 := bstep (se 1 (by rfl) ⟨1371896, by rfl⟩ : syracuseStep 1829195 = 2743793) B2743793
theorem B1829207 : Blo 1827615 1829207 := bstep (se 1 (by rfl) ⟨1371905, by rfl⟩ : syracuseStep 1829207 = 2743811) B2743811
theorem B1829227 : Blo 1827615 1829227 := bstep (se 1 (by rfl) ⟨1371920, by rfl⟩ : syracuseStep 1829227 = 2743841) B2743841
theorem B1829239 : Blo 1827615 1829239 := bstep (se 1 (by rfl) ⟨1371929, by rfl⟩ : syracuseStep 1829239 = 2743859) B2743859
theorem B4114817 : Blo 1827615 4114817 := bstep (se 2 (by rfl) ⟨1543056, by rfl⟩ : syracuseStep 4114817 = 3086113) B3086113
theorem B1829259 : Blo 1827615 1829259 := bstep (se 1 (by rfl) ⟨1371944, by rfl⟩ : syracuseStep 1829259 = 2743889) B2743889
theorem B11274647 : Blo 1827615 11274647 := bstep (se 1 (by rfl) ⟨8455985, by rfl⟩ : syracuseStep 11274647 = 16911971) B16911971
theorem B1829271 : Blo 1827615 1829271 := bstep (se 1 (by rfl) ⟨1371953, by rfl⟩ : syracuseStep 1829271 = 2743907) B2743907
theorem B1829291 : Blo 1827615 1829291 := bstep (se 1 (by rfl) ⟨1371968, by rfl⟩ : syracuseStep 1829291 = 2743937) B2743937
theorem B3295667 : Blo 1827615 3295667 := bstep (se 1 (by rfl) ⟨2471750, by rfl⟩ : syracuseStep 3295667 = 4943501) B4943501
theorem B1829303 : Blo 1827615 1829303 := bstep (se 1 (by rfl) ⟨1371977, by rfl⟩ : syracuseStep 1829303 = 2743955) B2743955
theorem B6343105 : Blo 1827615 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B1829323 : Blo 1827615 1829323 := bstep (se 1 (by rfl) ⟨1371992, by rfl⟩ : syracuseStep 1829323 = 2743985) B2743985
theorem B1829335 : Blo 1827615 1829335 := bstep (se 1 (by rfl) ⟨1372001, by rfl⟩ : syracuseStep 1829335 = 2744003) B2744003
theorem B1829355 : Blo 1827615 1829355 := bstep (se 1 (by rfl) ⟨1372016, by rfl⟩ : syracuseStep 1829355 = 2744033) B2744033
theorem B1829367 : Blo 1827615 1829367 := bstep (se 1 (by rfl) ⟨1372025, by rfl⟩ : syracuseStep 1829367 = 2744051) B2744051
theorem B1829387 : Blo 1827615 1829387 := bstep (se 1 (by rfl) ⟨1372040, by rfl⟩ : syracuseStep 1829387 = 2744081) B2744081
theorem B1829399 : Blo 1827615 1829399 := bstep (se 1 (by rfl) ⟨1372049, by rfl⟩ : syracuseStep 1829399 = 2744099) B2744099
theorem B15616547 : Blo 1827615 15616547 := bstep (se 1 (by rfl) ⟨11712410, by rfl⟩ : syracuseStep 15616547 = 23424821) B23424821
theorem B1829419 : Blo 1827615 1829419 := bstep (se 1 (by rfl) ⟨1372064, by rfl⟩ : syracuseStep 1829419 = 2744129) B2744129
theorem B1829431 : Blo 1827615 1829431 := bstep (se 1 (by rfl) ⟨1372073, by rfl⟩ : syracuseStep 1829431 = 2744147) B2744147
theorem B9259595 : Blo 1827615 9259595 := bstep (se 1 (by rfl) ⟨6944696, by rfl⟩ : syracuseStep 9259595 = 13889393) B13889393
theorem B1829451 : Blo 1827615 1829451 := bstep (se 1 (by rfl) ⟨1372088, by rfl⟩ : syracuseStep 1829451 = 2744177) B2744177
theorem B1829463 : Blo 1827615 1829463 := bstep (se 1 (by rfl) ⟨1372097, by rfl⟩ : syracuseStep 1829463 = 2744195) B2744195
theorem B4115033 : Blo 1827615 4115033 := bstep (se 2 (by rfl) ⟨1543137, by rfl⟩ : syracuseStep 4115033 = 3086275) B3086275
theorem B1829483 : Blo 1827615 1829483 := bstep (se 1 (by rfl) ⟨1372112, by rfl⟩ : syracuseStep 1829483 = 2744225) B2744225
theorem B1829495 : Blo 1827615 1829495 := bstep (se 1 (by rfl) ⟨1372121, by rfl⟩ : syracuseStep 1829495 = 2744243) B2744243
theorem B1829515 : Blo 1827615 1829515 := bstep (se 1 (by rfl) ⟨1372136, by rfl⟩ : syracuseStep 1829515 = 2744273) B2744273
theorem B1829527 : Blo 1827615 1829527 := bstep (se 1 (by rfl) ⟨1372145, by rfl⟩ : syracuseStep 1829527 = 2744291) B2744291
theorem B1829547 : Blo 1827615 1829547 := bstep (se 1 (by rfl) ⟨1372160, by rfl⟩ : syracuseStep 1829547 = 2744321) B2744321
theorem B7809709 : Blo 1827615 7809709 := bstep (se 3 (by rfl) ⟨1464320, by rfl⟩ : syracuseStep 7809709 = 2928641) B2928641
theorem B4115123 : Blo 1827615 4115123 := bstep (se 1 (by rfl) ⟨3086342, by rfl⟩ : syracuseStep 4115123 = 6172685) B6172685
theorem B1829559 : Blo 1827615 1829559 := bstep (se 1 (by rfl) ⟨1372169, by rfl⟩ : syracuseStep 1829559 = 2744339) B2744339
theorem B1829579 : Blo 1827615 1829579 := bstep (se 1 (by rfl) ⟨1372184, by rfl⟩ : syracuseStep 1829579 = 2744369) B2744369
theorem B4115159 : Blo 1827615 4115159 := bstep (se 1 (by rfl) ⟨3086369, by rfl⟩ : syracuseStep 4115159 = 6172739) B6172739
theorem B1829591 : Blo 1827615 1829591 := bstep (se 1 (by rfl) ⟨1372193, by rfl⟩ : syracuseStep 1829591 = 2744387) B2744387
theorem B1829611 : Blo 1827615 1829611 := bstep (se 1 (by rfl) ⟨1372208, by rfl⟩ : syracuseStep 1829611 = 2744417) B2744417
theorem B6171443 : Blo 1827615 6171443 := bstep (se 1 (by rfl) ⟨4628582, by rfl⟩ : syracuseStep 6171443 = 9257165) B9257165
theorem B4115339 : Blo 1827615 4115339 := bstep (se 1 (by rfl) ⟨3086504, by rfl⟩ : syracuseStep 4115339 = 6173009) B6173009
theorem B4115393 : Blo 1827615 4115393 := bstep (se 2 (by rfl) ⟨1543272, by rfl⟩ : syracuseStep 4115393 = 3086545) B3086545
theorem B6171713 : Blo 1827615 6171713 := bstep (se 2 (by rfl) ⟨2314392, by rfl⟩ : syracuseStep 6171713 = 4628785) B4628785
theorem B2313355 : Blo 1827615 2313355 := bstep (se 1 (by rfl) ⟨1735016, by rfl⟩ : syracuseStep 2313355 = 3470033) B3470033
theorem B4115609 : Blo 1827615 4115609 := bstep (se 2 (by rfl) ⟨1543353, by rfl⟩ : syracuseStep 4115609 = 3086707) B3086707
theorem B4943069 : Blo 1827615 4943069 := bstep (se 3 (by rfl) ⟨926825, by rfl⟩ : syracuseStep 4943069 = 1853651) B1853651
theorem B4115699 : Blo 1827615 4115699 := bstep (se 1 (by rfl) ⟨3086774, by rfl⟩ : syracuseStep 4115699 = 6173549) B6173549
theorem B4115735 : Blo 1827615 4115735 := bstep (se 1 (by rfl) ⟨3086801, by rfl⟩ : syracuseStep 4115735 = 6173603) B6173603
theorem B10415405 : Blo 1827615 10415405 := bstep (se 3 (by rfl) ⟨1952888, by rfl⟩ : syracuseStep 10415405 = 3905777) B3905777
theorem B5205323 : Blo 1827615 5205323 := bstep (se 1 (by rfl) ⟨3903992, by rfl⟩ : syracuseStep 5205323 = 7807985) B7807985
theorem B2313623 : Blo 1827615 2313623 := bstep (se 1 (by rfl) ⟨1735217, by rfl⟩ : syracuseStep 2313623 = 3470435) B3470435
theorem B6942131 : Blo 1827615 6942131 := bstep (se 1 (by rfl) ⟨5206598, by rfl⟩ : syracuseStep 6942131 = 10413197) B10413197
theorem B6254003 : Blo 1827615 6254003 := bstep (se 1 (by rfl) ⟨4690502, by rfl⟩ : syracuseStep 6254003 = 9381005) B9381005
theorem B6942145 : Blo 1827615 6942145 := bstep (se 2 (by rfl) ⟨2603304, by rfl⟩ : syracuseStep 6942145 = 5206609) B5206609
theorem B4115915 : Blo 1827615 4115915 := bstep (se 1 (by rfl) ⟨3086936, by rfl⟩ : syracuseStep 4115915 = 6173873) B6173873
theorem B1953239 : Blo 1827615 1953239 := bstep (se 1 (by rfl) ⟨1464929, by rfl⟩ : syracuseStep 1953239 = 2929859) B2929859
theorem B4115969 : Blo 1827615 4115969 := bstep (se 2 (by rfl) ⟨1543488, by rfl⟩ : syracuseStep 4115969 = 3086977) B3086977
theorem B50040337 : Blo 1827615 50040337 := bstep (se 2 (by rfl) ⟨18765126, by rfl⟩ : syracuseStep 50040337 = 37530253) B37530253
theorem B6172253 : Blo 1827615 6172253 := bstep (se 3 (by rfl) ⟨1157297, by rfl⟩ : syracuseStep 6172253 = 2314595) B2314595
theorem B2084459 : Blo 1827615 2084459 := bstep (se 1 (by rfl) ⟨1563344, by rfl⟩ : syracuseStep 2084459 = 3126689) B3126689
theorem B3296971 : Blo 1827615 3296971 := bstep (se 1 (by rfl) ⟨2472728, by rfl⟩ : syracuseStep 3296971 = 4945457) B4945457
theorem B50024141 : Blo 1827615 50024141 := bstep (se 3 (by rfl) ⟨9379526, by rfl⟩ : syracuseStep 50024141 = 18759053) B18759053
theorem B5205721 : Blo 1827615 5205721 := bstep (se 2 (by rfl) ⟨1952145, by rfl⟩ : syracuseStep 5205721 = 3904291) B3904291
theorem B4116185 : Blo 1827615 4116185 := bstep (se 2 (by rfl) ⟨1543569, by rfl⟩ : syracuseStep 4116185 = 3087139) B3087139
theorem B5009203 : Blo 1827615 5009203 := bstep (se 1 (by rfl) ⟨3756902, by rfl⟩ : syracuseStep 5009203 = 7513805) B7513805
theorem B4116275 : Blo 1827615 4116275 := bstep (se 1 (by rfl) ⟨3087206, by rfl⟩ : syracuseStep 4116275 = 6174413) B6174413
theorem B4116311 : Blo 1827615 4116311 := bstep (se 1 (by rfl) ⟨3087233, by rfl⟩ : syracuseStep 4116311 = 6174467) B6174467
theorem B3903385 : Blo 1827615 3903385 := bstep (se 2 (by rfl) ⟨1463769, by rfl⟩ : syracuseStep 3903385 = 2927539) B2927539
theorem B14274481 : Blo 1827615 14274481 := bstep (se 2 (by rfl) ⟨5352930, by rfl⟩ : syracuseStep 14274481 = 10705861) B10705861
theorem B4116491 : Blo 1827615 4116491 := bstep (se 1 (by rfl) ⟨3087368, by rfl⟩ : syracuseStep 4116491 = 6174737) B6174737
theorem B3084311 : Blo 1827615 3084311 := bstep (se 1 (by rfl) ⟨2313233, by rfl⟩ : syracuseStep 3084311 = 4626467) B4626467
theorem B4116545 : Blo 1827615 4116545 := bstep (se 2 (by rfl) ⟨1543704, by rfl⟩ : syracuseStep 4116545 = 3087409) B3087409
theorem B2314327 : Blo 1827615 2314327 := bstep (se 1 (by rfl) ⟨1735745, by rfl⟩ : syracuseStep 2314327 = 3471491) B3471491
theorem B11710565 : Blo 1827615 11710565 := bstep (se 4 (by rfl) ⟨1097865, by rfl⟩ : syracuseStep 11710565 = 2195731) B2195731
theorem B15036547 : Blo 1827615 15036547 := bstep (se 1 (by rfl) ⟨11277410, by rfl⟩ : syracuseStep 15036547 = 22554821) B22554821
theorem B3084439 : Blo 1827615 3084439 := bstep (se 1 (by rfl) ⟨2313329, by rfl⟩ : syracuseStep 3084439 = 4626659) B4626659
theorem B13881617 : Blo 1827615 13881617 := bstep (se 2 (by rfl) ⟨5205606, by rfl⟩ : syracuseStep 13881617 = 10411213) B10411213
theorem B9261377 : Blo 1827615 9261377 := bstep (se 2 (by rfl) ⟨3473016, by rfl⟩ : syracuseStep 9261377 = 6946033) B6946033
theorem B7811417 : Blo 1827615 7811417 := bstep (se 2 (by rfl) ⟨2929281, by rfl⟩ : syracuseStep 7811417 = 5858563) B5858563
theorem B6255197 : Blo 1827615 6255197 := bstep (se 3 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 6255197 = 2345699) B2345699
theorem B11121245 : Blo 1827615 11121245 := bstep (se 3 (by rfl) ⟨2085233, by rfl⟩ : syracuseStep 11121245 = 4170467) B4170467
theorem B3904129 : Blo 1827615 3904129 := bstep (se 2 (by rfl) ⟨1464048, by rfl⟩ : syracuseStep 3904129 = 2928097) B2928097
theorem B3568279 : Blo 1827615 3568279 := bstep (se 1 (by rfl) ⟨2676209, by rfl⟩ : syracuseStep 3568279 = 5352419) B5352419
theorem B2970263 : Blo 1827615 2970263 := bstep (se 1 (by rfl) ⟨2227697, by rfl⟩ : syracuseStep 2970263 = 4455395) B4455395
theorem B1979083 : Blo 1827615 1979083 := bstep (se 1 (by rfl) ⟨1484312, by rfl⟩ : syracuseStep 1979083 = 2968625) B2968625
theorem B6173387 : Blo 1827615 6173387 := bstep (se 1 (by rfl) ⟨4630040, by rfl⟩ : syracuseStep 6173387 = 9260081) B9260081
theorem B3085067 : Blo 1827615 3085067 := bstep (se 1 (by rfl) ⟨2313800, by rfl⟩ : syracuseStep 3085067 = 4627601) B4627601
theorem B3470131 : Blo 1827615 3470131 := bstep (se 1 (by rfl) ⟨2602598, by rfl⟩ : syracuseStep 3470131 = 5205197) B5205197
theorem B6255425 : Blo 1827615 6255425 := bstep (se 2 (by rfl) ⟨2345784, by rfl⟩ : syracuseStep 6255425 = 4691569) B4691569
theorem B4395865 : Blo 1827615 4395865 := bstep (se 2 (by rfl) ⟨1648449, by rfl⟩ : syracuseStep 4395865 = 3296899) B3296899
theorem B9253763 : Blo 1827615 9253763 := bstep (se 1 (by rfl) ⟨6940322, by rfl⟩ : syracuseStep 9253763 = 13880645) B13880645
theorem B3085195 : Blo 1827615 3085195 := bstep (se 1 (by rfl) ⟨2313896, by rfl⟩ : syracuseStep 3085195 = 4627793) B4627793
theorem B5206963 : Blo 1827615 5206963 := bstep (se 1 (by rfl) ⟨3905222, by rfl⟩ : syracuseStep 5206963 = 7810445) B7810445
theorem B35156915 : Blo 1827615 35156915 := bstep (se 1 (by rfl) ⟨26367686, by rfl⟩ : syracuseStep 35156915 = 52735373) B52735373
theorem B6173657 : Blo 1827615 6173657 := bstep (se 2 (by rfl) ⟨2315121, by rfl⟩ : syracuseStep 6173657 = 4630243) B4630243
theorem B3470359 : Blo 1827615 3470359 := bstep (se 1 (by rfl) ⟨2602769, by rfl⟩ : syracuseStep 3470359 = 5205539) B5205539
theorem B3085337 : Blo 1827615 3085337 := bstep (se 2 (by rfl) ⟨1157001, by rfl⟩ : syracuseStep 3085337 = 2314003) B2314003
theorem B2470999 : Blo 1827615 2470999 := bstep (se 1 (by rfl) ⟨1853249, by rfl⟩ : syracuseStep 2470999 = 3706499) B3706499
theorem B3339353 : Blo 1827615 3339353 := bstep (se 2 (by rfl) ⟨1252257, by rfl⟩ : syracuseStep 3339353 = 2504515) B2504515
theorem B6591577 : Blo 1827615 6591577 := bstep (se 2 (by rfl) ⟨2471841, by rfl⟩ : syracuseStep 6591577 = 4943683) B4943683
theorem B6681689 : Blo 1827615 6681689 := bstep (se 2 (by rfl) ⟨2505633, by rfl⟩ : syracuseStep 6681689 = 5011267) B5011267
theorem B3470465 : Blo 1827615 3470465 := bstep (se 2 (by rfl) ⟨1301424, by rfl⟩ : syracuseStep 3470465 = 2602849) B2602849
theorem B3708055 : Blo 1827615 3708055 := bstep (se 1 (by rfl) ⟨2781041, by rfl⟩ : syracuseStep 3708055 = 5562083) B5562083
theorem B3085465 : Blo 1827615 3085465 := bstep (se 2 (by rfl) ⟨1157049, by rfl⟩ : syracuseStep 3085465 = 2314099) B2314099
theorem B2741465 : Blo 1827615 2741465 := bstep (se 2 (by rfl) ⟨1028049, by rfl⟩ : syracuseStep 2741465 = 2056099) B2056099
theorem B3470617 : Blo 1827615 3470617 := bstep (se 2 (by rfl) ⟨1301481, by rfl⟩ : syracuseStep 3470617 = 2602963) B2602963
theorem B13890851 : Blo 1827615 13890851 := bstep (se 1 (by rfl) ⟨10418138, by rfl⟩ : syracuseStep 13890851 = 20836277) B20836277
theorem B2741579 : Blo 1827615 2741579 := bstep (se 1 (by rfl) ⟨2056184, by rfl⟩ : syracuseStep 2741579 = 4112369) B4112369
theorem B6944075 : Blo 1827615 6944075 := bstep (se 1 (by rfl) ⟨5208056, by rfl⟩ : syracuseStep 6944075 = 10416113) B10416113
theorem B2741591 : Blo 1827615 2741591 := bstep (se 1 (by rfl) ⟨2056193, by rfl⟩ : syracuseStep 2741591 = 4112387) B4112387
theorem B6944089 : Blo 1827615 6944089 := bstep (se 2 (by rfl) ⟨2604033, by rfl⟩ : syracuseStep 6944089 = 5208067) B5208067
theorem B10704221 : Blo 1827615 10704221 := bstep (se 3 (by rfl) ⟨2007041, by rfl⟩ : syracuseStep 10704221 = 4014083) B4014083
theorem B70268309 : Blo 1827615 70268309 := bstep (se 6 (by rfl) ⟨1646913, by rfl⟩ : syracuseStep 70268309 = 3293827) B3293827
theorem B2741657 : Blo 1827615 2741657 := bstep (se 2 (by rfl) ⟨1028121, by rfl⟩ : syracuseStep 2741657 = 2056243) B2056243
theorem B26351027 : Blo 1827615 26351027 := bstep (se 1 (by rfl) ⟨19763270, by rfl⟩ : syracuseStep 26351027 = 39526541) B39526541
theorem B2741771 : Blo 1827615 2741771 := bstep (se 1 (by rfl) ⟨2056328, by rfl⟩ : syracuseStep 2741771 = 4112657) B4112657
theorem B2741783 : Blo 1827615 2741783 := bstep (se 1 (by rfl) ⟨2056337, by rfl⟩ : syracuseStep 2741783 = 4112675) B4112675
theorem B7812683 : Blo 1827615 7812683 := bstep (se 1 (by rfl) ⟨5859512, by rfl⟩ : syracuseStep 7812683 = 11719025) B11719025
theorem B3905111 : Blo 1827615 3905111 := bstep (se 1 (by rfl) ⟨2928833, by rfl⟩ : syracuseStep 3905111 = 5857667) B5857667
theorem B2741849 : Blo 1827615 2741849 := bstep (se 2 (by rfl) ⟨1028193, by rfl⟩ : syracuseStep 2741849 = 2056387) B2056387
theorem B10024541 : Blo 1827615 10024541 := bstep (se 3 (by rfl) ⟨1879601, by rfl⟩ : syracuseStep 10024541 = 3759203) B3759203
theorem B10409573 : Blo 1827615 10409573 := bstep (se 4 (by rfl) ⟨975897, by rfl⟩ : syracuseStep 10409573 = 1951795) B1951795
theorem B4011671 : Blo 1827615 4011671 := bstep (se 1 (by rfl) ⟨3008753, by rfl⟩ : syracuseStep 4011671 = 6017507) B6017507
theorem B6174359 : Blo 1827615 6174359 := bstep (se 1 (by rfl) ⟨4630769, by rfl⟩ : syracuseStep 6174359 = 9261539) B9261539
theorem B7534259 : Blo 1827615 7534259 := bstep (se 1 (by rfl) ⟨5650694, by rfl⟩ : syracuseStep 7534259 = 11301389) B11301389
theorem B2741963 : Blo 1827615 2741963 := bstep (se 1 (by rfl) ⟨2056472, by rfl⟩ : syracuseStep 2741963 = 4112945) B4112945
theorem B2741975 : Blo 1827615 2741975 := bstep (se 1 (by rfl) ⟨2056481, by rfl⟩ : syracuseStep 2741975 = 4112963) B4112963
theorem B3086039 : Blo 1827615 3086039 := bstep (se 1 (by rfl) ⟨2314529, by rfl⟩ : syracuseStep 3086039 = 4629059) B4629059
theorem B2930455 : Blo 1827615 2930455 := bstep (se 1 (by rfl) ⟨2197841, by rfl⟩ : syracuseStep 2930455 = 4395683) B4395683
theorem B2742041 : Blo 1827615 2742041 := bstep (se 2 (by rfl) ⟨1028265, by rfl⟩ : syracuseStep 2742041 = 2056531) B2056531
theorem B3086167 : Blo 1827615 3086167 := bstep (se 1 (by rfl) ⟨2314625, by rfl⟩ : syracuseStep 3086167 = 4629251) B4629251
theorem B8902493 : Blo 1827615 8902493 := bstep (se 3 (by rfl) ⟨1669217, by rfl⟩ : syracuseStep 8902493 = 3338435) B3338435
theorem B2742155 : Blo 1827615 2742155 := bstep (se 1 (by rfl) ⟨2056616, by rfl⟩ : syracuseStep 2742155 = 4113233) B4113233
theorem B2742167 : Blo 1827615 2742167 := bstep (se 1 (by rfl) ⟨2056625, by rfl⟩ : syracuseStep 2742167 = 4113251) B4113251
theorem B4626355 : Blo 1827615 4626355 := bstep (se 1 (by rfl) ⟨3469766, by rfl⟩ : syracuseStep 4626355 = 6939533) B6939533
theorem B7813043 : Blo 1827615 7813043 := bstep (se 1 (by rfl) ⟨5859782, by rfl⟩ : syracuseStep 7813043 = 11719565) B11719565
theorem B2742233 : Blo 1827615 2742233 := bstep (se 2 (by rfl) ⟨1028337, by rfl⟩ : syracuseStep 2742233 = 2056675) B2056675
theorem B6592529 : Blo 1827615 6592529 := bstep (se 2 (by rfl) ⟨2472198, by rfl⟩ : syracuseStep 6592529 = 4944397) B4944397
theorem B26359843 : Blo 1827615 26359843 := bstep (se 1 (by rfl) ⟨19769882, by rfl⟩ : syracuseStep 26359843 = 39539765) B39539765
theorem B10410029 : Blo 1827615 10410029 := bstep (se 3 (by rfl) ⟨1951880, by rfl⟩ : syracuseStep 10410029 = 3903761) B3903761
theorem B4626497 : Blo 1827615 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B2742347 : Blo 1827615 2742347 := bstep (se 1 (by rfl) ⟨2056760, by rfl⟩ : syracuseStep 2742347 = 4113521) B4113521
theorem B2742359 : Blo 1827615 2742359 := bstep (se 1 (by rfl) ⟨2056769, by rfl⟩ : syracuseStep 2742359 = 4113539) B4113539
theorem B3127385 : Blo 1827615 3127385 := bstep (se 2 (by rfl) ⟨1172769, by rfl⟩ : syracuseStep 3127385 = 2345539) B2345539
theorem B3905675 : Blo 1827615 3905675 := bstep (se 1 (by rfl) ⟨2929256, by rfl⟩ : syracuseStep 3905675 = 5858513) B5858513
theorem B106854551 : Blo 1827615 106854551 := bstep (se 1 (by rfl) ⟨80140913, by rfl⟩ : syracuseStep 106854551 = 160281827) B160281827
theorem B2742425 : Blo 1827615 2742425 := bstep (se 2 (by rfl) ⟨1028409, by rfl⟩ : syracuseStep 2742425 = 2056819) B2056819
theorem B6174899 : Blo 1827615 6174899 := bstep (se 1 (by rfl) ⟨4631174, by rfl⟩ : syracuseStep 6174899 = 9262349) B9262349
theorem B2603225 : Blo 1827615 2603225 := bstep (se 2 (by rfl) ⟨976209, by rfl⟩ : syracuseStep 2603225 = 1952419) B1952419
theorem B2742539 : Blo 1827615 2742539 := bstep (se 1 (by rfl) ⟨2056904, by rfl⟩ : syracuseStep 2742539 = 4113809) B4113809
theorem B2742551 : Blo 1827615 2742551 := bstep (se 1 (by rfl) ⟨2056913, by rfl⟩ : syracuseStep 2742551 = 4113827) B4113827
theorem B6945047 : Blo 1827615 6945047 := bstep (se 1 (by rfl) ⟨5208785, by rfl⟩ : syracuseStep 6945047 = 10417571) B10417571
theorem B2742617 : Blo 1827615 2742617 := bstep (se 2 (by rfl) ⟨1028481, by rfl⟩ : syracuseStep 2742617 = 2056963) B2056963
theorem B2742731 : Blo 1827615 2742731 := bstep (se 1 (by rfl) ⟨2057048, by rfl⟩ : syracuseStep 2742731 = 4114097) B4114097
theorem B3086795 : Blo 1827615 3086795 := bstep (se 1 (by rfl) ⟨2315096, by rfl⟩ : syracuseStep 3086795 = 4630193) B4630193
theorem B2742743 : Blo 1827615 2742743 := bstep (se 1 (by rfl) ⟨2057057, by rfl⟩ : syracuseStep 2742743 = 4114115) B4114115
theorem B44497421 : Blo 1827615 44497421 := bstep (se 3 (by rfl) ⟨8343266, by rfl⟩ : syracuseStep 44497421 = 16686533) B16686533
theorem B12040721 : Blo 1827615 12040721 := bstep (se 2 (by rfl) ⟨4515270, by rfl⟩ : syracuseStep 12040721 = 9030541) B9030541
theorem B2742809 : Blo 1827615 2742809 := bstep (se 2 (by rfl) ⟨1028553, by rfl⟩ : syracuseStep 2742809 = 2057107) B2057107
theorem B3471923 : Blo 1827615 3471923 := bstep (se 1 (by rfl) ⟨2603942, by rfl⟩ : syracuseStep 3471923 = 5207885) B5207885
theorem B3086923 : Blo 1827615 3086923 := bstep (se 1 (by rfl) ⟨2315192, by rfl⟩ : syracuseStep 3086923 = 4630385) B4630385
theorem B3906137 : Blo 1827615 3906137 := bstep (se 2 (by rfl) ⟨1464801, by rfl⟩ : syracuseStep 3906137 = 2929603) B2929603
theorem B2742923 : Blo 1827615 2742923 := bstep (se 1 (by rfl) ⟨2057192, by rfl⟩ : syracuseStep 2742923 = 4114385) B4114385
theorem B2742935 : Blo 1827615 2742935 := bstep (se 1 (by rfl) ⟨2057201, by rfl⟩ : syracuseStep 2742935 = 4114403) B4114403
theorem B13367987 : Blo 1827615 13367987 := bstep (se 1 (by rfl) ⟨10025990, by rfl⟩ : syracuseStep 13367987 = 20051981) B20051981
theorem B3472075 : Blo 1827615 3472075 := bstep (se 1 (by rfl) ⟨2604056, by rfl⟩ : syracuseStep 3472075 = 5208113) B5208113
theorem B10410713 : Blo 1827615 10410713 := bstep (se 2 (by rfl) ⟨3904017, by rfl⟩ : syracuseStep 10410713 = 7808035) B7808035
theorem B5077721 : Blo 1827615 5077721 := bstep (se 2 (by rfl) ⟨1904145, by rfl⟩ : syracuseStep 5077721 = 3808291) B3808291
theorem B2743001 : Blo 1827615 2743001 := bstep (se 2 (by rfl) ⟨1028625, by rfl⟩ : syracuseStep 2743001 = 2057251) B2057251
theorem B3087065 : Blo 1827615 3087065 := bstep (se 2 (by rfl) ⟨1157649, by rfl⟩ : syracuseStep 3087065 = 2315299) B2315299
theorem B2743115 : Blo 1827615 2743115 := bstep (se 1 (by rfl) ⟨2057336, by rfl⟩ : syracuseStep 2743115 = 4114673) B4114673
theorem B11123531 : Blo 1827615 11123531 := bstep (se 1 (by rfl) ⟨8342648, by rfl⟩ : syracuseStep 11123531 = 16685297) B16685297
theorem B2743127 : Blo 1827615 2743127 := bstep (se 1 (by rfl) ⟨2057345, by rfl⟩ : syracuseStep 2743127 = 4114691) B4114691
theorem B2603863 : Blo 1827615 2603863 := bstep (se 1 (by rfl) ⟨1952897, by rfl⟩ : syracuseStep 2603863 = 3905795) B3905795
theorem B3087193 : Blo 1827615 3087193 := bstep (se 2 (by rfl) ⟨1157697, by rfl⟩ : syracuseStep 3087193 = 2315395) B2315395
theorem B7412573 : Blo 1827615 7412573 := bstep (se 3 (by rfl) ⟨1389857, by rfl⟩ : syracuseStep 7412573 = 2779715) B2779715
theorem B2743193 : Blo 1827615 2743193 := bstep (se 2 (by rfl) ⟨1028697, by rfl⟩ : syracuseStep 2743193 = 2057395) B2057395
theorem B2743307 : Blo 1827615 2743307 := bstep (se 1 (by rfl) ⟨2057480, by rfl⟩ : syracuseStep 2743307 = 4114961) B4114961
theorem B2743319 : Blo 1827615 2743319 := bstep (se 1 (by rfl) ⟨2057489, by rfl⟩ : syracuseStep 2743319 = 4114979) B4114979
theorem B3472409 : Blo 1827615 3472409 := bstep (se 2 (by rfl) ⟨1302153, by rfl⟩ : syracuseStep 3472409 = 2604307) B2604307
theorem B9387083 : Blo 1827615 9387083 := bstep (se 1 (by rfl) ⟨7040312, by rfl⟩ : syracuseStep 9387083 = 14080625) B14080625
theorem B2743385 : Blo 1827615 2743385 := bstep (se 2 (by rfl) ⟨1028769, by rfl⟩ : syracuseStep 2743385 = 2057539) B2057539
theorem B3128473 : Blo 1827615 3128473 := bstep (se 2 (by rfl) ⟨1173177, by rfl⟩ : syracuseStep 3128473 = 2346355) B2346355
theorem B2743499 : Blo 1827615 2743499 := bstep (se 1 (by rfl) ⟨2057624, by rfl⟩ : syracuseStep 2743499 = 4115249) B4115249
theorem B2743511 : Blo 1827615 2743511 := bstep (se 1 (by rfl) ⟨2057633, by rfl⟩ : syracuseStep 2743511 = 4115267) B4115267
theorem B17571077 : Blo 1827615 17571077 := bstep (se 4 (by rfl) ⟨1647288, by rfl⟩ : syracuseStep 17571077 = 3294577) B3294577
theorem B2743577 : Blo 1827615 2743577 := bstep (se 2 (by rfl) ⟨1028841, by rfl⟩ : syracuseStep 2743577 = 2057683) B2057683
theorem B4627763 : Blo 1827615 4627763 := bstep (se 1 (by rfl) ⟨3470822, by rfl⟩ : syracuseStep 4627763 = 6941645) B6941645
theorem B15629669 : Blo 1827615 15629669 := bstep (se 4 (by rfl) ⟨1465281, by rfl⟩ : syracuseStep 15629669 = 2930563) B2930563
theorem B2743691 : Blo 1827615 2743691 := bstep (se 1 (by rfl) ⟨2057768, by rfl⟩ : syracuseStep 2743691 = 4115537) B4115537
theorem B45071765 : Blo 1827615 45071765 := bstep (se 6 (by rfl) ⟨1056369, by rfl⟩ : syracuseStep 45071765 = 2112739) B2112739
theorem B2743703 : Blo 1827615 2743703 := bstep (se 1 (by rfl) ⟨2057777, by rfl⟩ : syracuseStep 2743703 = 4115555) B4115555
theorem B2743769 : Blo 1827615 2743769 := bstep (se 2 (by rfl) ⟨1028913, by rfl⟩ : syracuseStep 2743769 = 2057827) B2057827
theorem B6946307 : Blo 1827615 6946307 := bstep (se 1 (by rfl) ⟨5209730, by rfl⟩ : syracuseStep 6946307 = 10419461) B10419461
theorem B10157633 : Blo 1827615 10157633 := bstep (se 2 (by rfl) ⟨3809112, by rfl⟩ : syracuseStep 10157633 = 7618225) B7618225
theorem B2743883 : Blo 1827615 2743883 := bstep (se 1 (by rfl) ⟨2057912, by rfl⟩ : syracuseStep 2743883 = 4115825) B4115825
theorem B2743895 : Blo 1827615 2743895 := bstep (se 1 (by rfl) ⟨2057921, by rfl⟩ : syracuseStep 2743895 = 4115843) B4115843
theorem B2604683 : Blo 1827615 2604683 := bstep (se 1 (by rfl) ⟨1953512, by rfl⟩ : syracuseStep 2604683 = 3907025) B3907025
theorem B3473047 : Blo 1827615 3473047 := bstep (se 1 (by rfl) ⟨2604785, by rfl⟩ : syracuseStep 3473047 = 5209571) B5209571
theorem B2743961 : Blo 1827615 2743961 := bstep (se 2 (by rfl) ⟨1028985, by rfl⟩ : syracuseStep 2743961 = 2057971) B2057971
theorem B6168257 : Blo 1827615 6168257 := bstep (se 2 (by rfl) ⟨2313096, by rfl⟩ : syracuseStep 6168257 = 4626193) B4626193
theorem B11722457 : Blo 1827615 11722457 := bstep (se 2 (by rfl) ⟨4395921, by rfl⟩ : syracuseStep 11722457 = 8791843) B8791843
theorem B3907315 : Blo 1827615 3907315 := bstep (se 1 (by rfl) ⟨2930486, by rfl⟩ : syracuseStep 3907315 = 5860973) B5860973
theorem B31252229 : Blo 1827615 31252229 := bstep (se 4 (by rfl) ⟨2929896, by rfl⟩ : syracuseStep 31252229 = 5859793) B5859793
theorem B2744075 : Blo 1827615 2744075 := bstep (se 1 (by rfl) ⟨2058056, by rfl⟩ : syracuseStep 2744075 = 4116113) B4116113
theorem B2744087 : Blo 1827615 2744087 := bstep (se 1 (by rfl) ⟨2058065, by rfl⟩ : syracuseStep 2744087 = 4116131) B4116131
theorem B5209879 : Blo 1827615 5209879 := bstep (se 1 (by rfl) ⟨3907409, by rfl⟩ : syracuseStep 5209879 = 7814819) B7814819
theorem B4112153 : Blo 1827615 4112153 := bstep (se 2 (by rfl) ⟨1542057, by rfl⟩ : syracuseStep 4112153 = 3084115) B3084115
theorem B4628299 : Blo 1827615 4628299 := bstep (se 1 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 4628299 = 6942449) B6942449
theorem B2744153 : Blo 1827615 2744153 := bstep (se 2 (by rfl) ⟨1029057, by rfl⟩ : syracuseStep 2744153 = 2058115) B2058115
theorem B4112243 : Blo 1827615 4112243 := bstep (se 1 (by rfl) ⟨3084182, by rfl⟩ : syracuseStep 4112243 = 6168365) B6168365
theorem B4112279 : Blo 1827615 4112279 := bstep (se 1 (by rfl) ⟨3084209, by rfl⟩ : syracuseStep 4112279 = 6168419) B6168419
theorem B2744267 : Blo 1827615 2744267 := bstep (se 1 (by rfl) ⟨2058200, by rfl⟩ : syracuseStep 2744267 = 4116401) B4116401
theorem B2744279 : Blo 1827615 2744279 := bstep (se 1 (by rfl) ⟨2058209, by rfl⟩ : syracuseStep 2744279 = 4116419) B4116419
theorem B4628441 : Blo 1827615 4628441 := bstep (se 2 (by rfl) ⟨1735665, by rfl⟩ : syracuseStep 4628441 = 3471331) B3471331
theorem B2056171 : Blo 1827615 2056171 := bstep (se 1 (by rfl) ⟨1542128, by rfl⟩ : syracuseStep 2056171 = 3084257) B3084257
theorem B2744327 : Blo 1827615 2744327 := bstep (se 1 (by rfl) ⟨2058245, by rfl⟩ : syracuseStep 2744327 = 4116491) B4116491
theorem B10420235 : Blo 1827615 10420235 := bstep (se 1 (by rfl) ⟨7815176, by rfl⟩ : syracuseStep 10420235 = 15630353) B15630353
theorem B2056207 : Blo 1827615 2056207 := bstep (se 1 (by rfl) ⟨1542155, by rfl⟩ : syracuseStep 2056207 = 3084311) B3084311
theorem B9257003 : Blo 1827615 9257003 := bstep (se 1 (by rfl) ⟨6942752, by rfl⟩ : syracuseStep 9257003 = 13885505) B13885505
theorem B2744363 : Blo 1827615 2744363 := bstep (se 1 (by rfl) ⟨2058272, by rfl⟩ : syracuseStep 2744363 = 4116545) B4116545
theorem B17580077 : Blo 1827615 17580077 := bstep (se 3 (by rfl) ⟨3296264, by rfl⟩ : syracuseStep 17580077 = 6592529) B6592529
theorem B7807043 : Blo 1827615 7807043 := bstep (se 1 (by rfl) ⟨5855282, by rfl⟩ : syracuseStep 7807043 = 11710565) B11710565
theorem B2744393 : Blo 1827615 2744393 := bstep (se 2 (by rfl) ⟨1029147, by rfl⟩ : syracuseStep 2744393 = 2058295) B2058295
theorem B4112531 : Blo 1827615 4112531 := bstep (se 1 (by rfl) ⟨3084398, by rfl⟩ : syracuseStep 4112531 = 6168797) B6168797
theorem B4112585 : Blo 1827615 4112585 := bstep (se 2 (by rfl) ⟨1542219, by rfl⟩ : syracuseStep 4112585 = 3084439) B3084439
theorem B8904941 : Blo 1827615 8904941 := bstep (se 3 (by rfl) ⟨1669676, by rfl⟩ : syracuseStep 8904941 = 3339353) B3339353
theorem B4170131 : Blo 1827615 4170131 := bstep (se 1 (by rfl) ⟨3127598, by rfl⟩ : syracuseStep 4170131 = 6255197) B6255197
theorem B7414163 : Blo 1827615 7414163 := bstep (se 1 (by rfl) ⟨5560622, by rfl⟩ : syracuseStep 7414163 = 11121245) B11121245
theorem B2056711 : Blo 1827615 2056711 := bstep (se 1 (by rfl) ⟨1542533, by rfl⟩ : syracuseStep 2056711 = 3085067) B3085067
theorem B4227643 : Blo 1827615 4227643 := bstep (se 1 (by rfl) ⟨3170732, by rfl⟩ : syracuseStep 4227643 = 6341465) B6341465
theorem B6169175 : Blo 1827615 6169175 := bstep (se 1 (by rfl) ⟨4626881, by rfl⟩ : syracuseStep 6169175 = 9253763) B9253763
theorem B23437943 : Blo 1827615 23437943 := bstep (se 1 (by rfl) ⟨17578457, by rfl⟩ : syracuseStep 23437943 = 35156915) B35156915
theorem B2056891 : Blo 1827615 2056891 := bstep (se 1 (by rfl) ⟨1542668, by rfl⟩ : syracuseStep 2056891 = 3085337) B3085337
theorem B1827643 : Blo 1827615 1827643 := bstep (se 1 (by rfl) ⟨1370732, by rfl⟩ : syracuseStep 1827643 = 2741465) B2741465
theorem B1827719 : Blo 1827615 1827719 := bstep (se 1 (by rfl) ⟨1370789, by rfl⟩ : syracuseStep 1827719 = 2741579) B2741579
theorem B4113287 : Blo 1827615 4113287 := bstep (se 1 (by rfl) ⟨3084965, by rfl⟩ : syracuseStep 4113287 = 6169931) B6169931
theorem B4629383 : Blo 1827615 4629383 := bstep (se 1 (by rfl) ⟨3472037, by rfl⟩ : syracuseStep 4629383 = 6944075) B6944075
theorem B1827727 : Blo 1827615 1827727 := bstep (se 1 (by rfl) ⟨1370795, by rfl⟩ : syracuseStep 1827727 = 2741591) B2741591
theorem B10412945 : Blo 1827615 10412945 := bstep (se 2 (by rfl) ⟨3904854, by rfl⟩ : syracuseStep 10412945 = 7809709) B7809709
theorem B7136147 : Blo 1827615 7136147 := bstep (se 1 (by rfl) ⟨5352110, by rfl⟩ : syracuseStep 7136147 = 10704221) B10704221
theorem B4629433 : Blo 1827615 4629433 := bstep (se 2 (by rfl) ⟨1736037, by rfl⟩ : syracuseStep 4629433 = 3472075) B3472075
theorem B1827771 : Blo 1827615 1827771 := bstep (se 1 (by rfl) ⟨1370828, by rfl⟩ : syracuseStep 1827771 = 2741657) B2741657
theorem B1827847 : Blo 1827615 1827847 := bstep (se 1 (by rfl) ⟨1370885, by rfl⟩ : syracuseStep 1827847 = 2741771) B2741771
theorem B1827855 : Blo 1827615 1827855 := bstep (se 1 (by rfl) ⟨1370891, by rfl⟩ : syracuseStep 1827855 = 2741783) B2741783
theorem B1827899 : Blo 1827615 1827899 := bstep (se 1 (by rfl) ⟨1370924, by rfl⟩ : syracuseStep 1827899 = 2741849) B2741849
theorem B4113467 : Blo 1827615 4113467 := bstep (se 1 (by rfl) ⟨3085100, by rfl⟩ : syracuseStep 4113467 = 6170201) B6170201
theorem B6169661 : Blo 1827615 6169661 := bstep (se 3 (by rfl) ⟨1156811, by rfl⟩ : syracuseStep 6169661 = 2313623) B2313623
theorem B30065725 : Blo 1827615 30065725 := bstep (se 3 (by rfl) ⟨5637323, by rfl⟩ : syracuseStep 30065725 = 11274647) B11274647
theorem B6939715 : Blo 1827615 6939715 := bstep (se 1 (by rfl) ⟨5204786, by rfl⟩ : syracuseStep 6939715 = 10409573) B10409573
theorem B5022839 : Blo 1827615 5022839 := bstep (se 1 (by rfl) ⟨3767129, by rfl⟩ : syracuseStep 5022839 = 7534259) B7534259
theorem B1827975 : Blo 1827615 1827975 := bstep (se 1 (by rfl) ⟨1370981, by rfl⟩ : syracuseStep 1827975 = 2741963) B2741963
theorem B1827983 : Blo 1827615 1827983 := bstep (se 1 (by rfl) ⟨1370987, by rfl⟩ : syracuseStep 1827983 = 2741975) B2741975
theorem B2057359 : Blo 1827615 2057359 := bstep (se 1 (by rfl) ⟨1543019, by rfl⟩ : syracuseStep 2057359 = 3086039) B3086039
theorem B4113593 : Blo 1827615 4113593 := bstep (se 2 (by rfl) ⟨1542597, by rfl⟩ : syracuseStep 4113593 = 3085195) B3085195
theorem B1828027 : Blo 1827615 1828027 := bstep (se 1 (by rfl) ⟨1371020, by rfl⟩ : syracuseStep 1828027 = 2742041) B2742041
theorem B1828103 : Blo 1827615 1828103 := bstep (se 1 (by rfl) ⟨1371077, by rfl⟩ : syracuseStep 1828103 = 2742155) B2742155
theorem B1828111 : Blo 1827615 1828111 := bstep (se 1 (by rfl) ⟨1371083, by rfl⟩ : syracuseStep 1828111 = 2742167) B2742167
theorem B2196779 : Blo 1827615 2196779 := bstep (se 1 (by rfl) ⟨1647584, by rfl⟩ : syracuseStep 2196779 = 3295169) B3295169
theorem B2639147 : Blo 1827615 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B1828155 : Blo 1827615 1828155 := bstep (se 1 (by rfl) ⟨1371116, by rfl⟩ : syracuseStep 1828155 = 2742233) B2742233
theorem B9258299 : Blo 1827615 9258299 := bstep (se 1 (by rfl) ⟨6943724, by rfl⟩ : syracuseStep 9258299 = 13887449) B13887449
theorem B6940019 : Blo 1827615 6940019 := bstep (se 1 (by rfl) ⟨5205014, by rfl⟩ : syracuseStep 6940019 = 10410029) B10410029
theorem B1828231 : Blo 1827615 1828231 := bstep (se 1 (by rfl) ⟨1371173, by rfl⟩ : syracuseStep 1828231 = 2742347) B2742347
theorem B1828239 : Blo 1827615 1828239 := bstep (se 1 (by rfl) ⟨1371179, by rfl⟩ : syracuseStep 1828239 = 2742359) B2742359
theorem B4392377 : Blo 1827615 4392377 := bstep (se 2 (by rfl) ⟨1647141, by rfl⟩ : syracuseStep 4392377 = 3294283) B3294283
theorem B1828283 : Blo 1827615 1828283 := bstep (se 1 (by rfl) ⟨1371212, by rfl⟩ : syracuseStep 1828283 = 2742425) B2742425
theorem B3294665 : Blo 1827615 3294665 := bstep (se 2 (by rfl) ⟨1235499, by rfl⟩ : syracuseStep 3294665 = 2470999) B2470999
theorem B9258461 : Blo 1827615 9258461 := bstep (se 3 (by rfl) ⟨1735961, by rfl⟩ : syracuseStep 9258461 = 3471923) B3471923
theorem B1828359 : Blo 1827615 1828359 := bstep (se 1 (by rfl) ⟨1371269, by rfl⟩ : syracuseStep 1828359 = 2742539) B2742539
theorem B1828367 : Blo 1827615 1828367 := bstep (se 1 (by rfl) ⟨1371275, by rfl⟩ : syracuseStep 1828367 = 2742551) B2742551
theorem B4113935 : Blo 1827615 4113935 := bstep (se 1 (by rfl) ⟨3085451, by rfl⟩ : syracuseStep 4113935 = 6170903) B6170903
theorem B4630031 : Blo 1827615 4630031 := bstep (se 1 (by rfl) ⟨3472523, by rfl⟩ : syracuseStep 4630031 = 6945047) B6945047
theorem B4113953 : Blo 1827615 4113953 := bstep (se 2 (by rfl) ⟨1542732, by rfl⟩ : syracuseStep 4113953 = 3085465) B3085465
theorem B1828411 : Blo 1827615 1828411 := bstep (se 1 (by rfl) ⟨1371308, by rfl⟩ : syracuseStep 1828411 = 2742617) B2742617
theorem B10413629 : Blo 1827615 10413629 := bstep (se 3 (by rfl) ⟨1952555, by rfl⟩ : syracuseStep 10413629 = 3905111) B3905111
theorem B65103437 : Blo 1827615 65103437 := bstep (se 3 (by rfl) ⟨12206894, by rfl⟩ : syracuseStep 65103437 = 24413789) B24413789
theorem B1828487 : Blo 1827615 1828487 := bstep (se 1 (by rfl) ⟨1371365, by rfl⟩ : syracuseStep 1828487 = 2742731) B2742731
theorem B2057863 : Blo 1827615 2057863 := bstep (se 1 (by rfl) ⟨1543397, by rfl⟩ : syracuseStep 2057863 = 3086795) B3086795
theorem B1828495 : Blo 1827615 1828495 := bstep (se 1 (by rfl) ⟨1371371, by rfl⟩ : syracuseStep 1828495 = 2742743) B2742743
theorem B29664947 : Blo 1827615 29664947 := bstep (se 1 (by rfl) ⟨22248710, by rfl⟩ : syracuseStep 29664947 = 44497421) B44497421
theorem B1828539 : Blo 1827615 1828539 := bstep (se 1 (by rfl) ⟨1371404, by rfl⟩ : syracuseStep 1828539 = 2742809) B2742809
theorem B1828615 : Blo 1827615 1828615 := bstep (se 1 (by rfl) ⟨1371461, by rfl⟩ : syracuseStep 1828615 = 2742923) B2742923
theorem B1828623 : Blo 1827615 1828623 := bstep (se 1 (by rfl) ⟨1371467, by rfl⟩ : syracuseStep 1828623 = 2742935) B2742935
theorem B9258785 : Blo 1827615 9258785 := bstep (se 2 (by rfl) ⟨3472044, by rfl⟩ : syracuseStep 9258785 = 6944089) B6944089
theorem B6940475 : Blo 1827615 6940475 := bstep (se 1 (by rfl) ⟨5205356, by rfl⟩ : syracuseStep 6940475 = 10410713) B10410713
theorem B1828667 : Blo 1827615 1828667 := bstep (se 1 (by rfl) ⟨1371500, by rfl⟩ : syracuseStep 1828667 = 2743001) B2743001
theorem B2058043 : Blo 1827615 2058043 := bstep (se 1 (by rfl) ⟨1543532, by rfl⟩ : syracuseStep 2058043 = 3087065) B3087065
theorem B4114295 : Blo 1827615 4114295 := bstep (se 1 (by rfl) ⟨3085721, by rfl⟩ : syracuseStep 4114295 = 6171443) B6171443
theorem B1828743 : Blo 1827615 1828743 := bstep (se 1 (by rfl) ⟨1371557, by rfl⟩ : syracuseStep 1828743 = 2743115) B2743115
theorem B7415687 : Blo 1827615 7415687 := bstep (se 1 (by rfl) ⟨5561765, by rfl⟩ : syracuseStep 7415687 = 11123531) B11123531
theorem B1828751 : Blo 1827615 1828751 := bstep (se 1 (by rfl) ⟨1371563, by rfl⟩ : syracuseStep 1828751 = 2743127) B2743127
theorem B4941715 : Blo 1827615 4941715 := bstep (se 1 (by rfl) ⟨3706286, by rfl⟩ : syracuseStep 4941715 = 7412573) B7412573
theorem B1828795 : Blo 1827615 1828795 := bstep (se 1 (by rfl) ⟨1371596, by rfl⟩ : syracuseStep 1828795 = 2743193) B2743193
theorem B1828871 : Blo 1827615 1828871 := bstep (se 1 (by rfl) ⟨1371653, by rfl⟩ : syracuseStep 1828871 = 2743307) B2743307
theorem B1828879 : Blo 1827615 1828879 := bstep (se 1 (by rfl) ⟨1371659, by rfl⟩ : syracuseStep 1828879 = 2743319) B2743319
theorem B4114475 : Blo 1827615 4114475 := bstep (se 1 (by rfl) ⟨3085856, by rfl⟩ : syracuseStep 4114475 = 6171713) B6171713
theorem B1828923 : Blo 1827615 1828923 := bstep (se 1 (by rfl) ⟨1371692, by rfl⟩ : syracuseStep 1828923 = 2743385) B2743385
theorem B1828999 : Blo 1827615 1828999 := bstep (se 1 (by rfl) ⟨1371749, by rfl⟩ : syracuseStep 1828999 = 2743499) B2743499
theorem B1829007 : Blo 1827615 1829007 := bstep (se 1 (by rfl) ⟨1371755, by rfl⟩ : syracuseStep 1829007 = 2743511) B2743511
theorem B3295379 : Blo 1827615 3295379 := bstep (se 1 (by rfl) ⟨2471534, by rfl⟩ : syracuseStep 3295379 = 4943069) B4943069
theorem B16681133 : Blo 1827615 16681133 := bstep (se 3 (by rfl) ⟨3127712, by rfl⟩ : syracuseStep 16681133 = 6255425) B6255425
theorem B1829051 : Blo 1827615 1829051 := bstep (se 1 (by rfl) ⟨1371788, by rfl⟩ : syracuseStep 1829051 = 2743577) B2743577
theorem B4630729 : Blo 1827615 4630729 := bstep (se 2 (by rfl) ⟨1736523, by rfl⟩ : syracuseStep 4630729 = 3473047) B3473047
theorem B1829127 : Blo 1827615 1829127 := bstep (se 1 (by rfl) ⟨1371845, by rfl⟩ : syracuseStep 1829127 = 2743691) B2743691
theorem B1829135 : Blo 1827615 1829135 := bstep (se 1 (by rfl) ⟨1371851, by rfl⟩ : syracuseStep 1829135 = 2743703) B2743703
theorem B6940961 : Blo 1827615 6940961 := bstep (se 2 (by rfl) ⟨2602860, by rfl⟩ : syracuseStep 6940961 = 5205721) B5205721
theorem B1829179 : Blo 1827615 1829179 := bstep (se 1 (by rfl) ⟨1371884, by rfl⟩ : syracuseStep 1829179 = 2743769) B2743769
theorem B4630871 : Blo 1827615 4630871 := bstep (se 1 (by rfl) ⟨3473153, by rfl⟩ : syracuseStep 4630871 = 6946307) B6946307
theorem B1829255 : Blo 1827615 1829255 := bstep (se 1 (by rfl) ⟨1371941, by rfl⟩ : syracuseStep 1829255 = 2743883) B2743883
theorem B1829263 : Blo 1827615 1829263 := bstep (se 1 (by rfl) ⟨1371947, by rfl⟩ : syracuseStep 1829263 = 2743895) B2743895
theorem B4114835 : Blo 1827615 4114835 := bstep (se 1 (by rfl) ⟨3086126, by rfl⟩ : syracuseStep 4114835 = 6172253) B6172253
theorem B6678937 : Blo 1827615 6678937 := bstep (se 2 (by rfl) ⟨2504601, by rfl⟩ : syracuseStep 6678937 = 5009203) B5009203
theorem B6171065 : Blo 1827615 6171065 := bstep (se 2 (by rfl) ⟨2314149, by rfl⟩ : syracuseStep 6171065 = 4628299) B4628299
theorem B1829307 : Blo 1827615 1829307 := bstep (se 1 (by rfl) ⟨1371980, by rfl⟩ : syracuseStep 1829307 = 2743961) B2743961
theorem B4114889 : Blo 1827615 4114889 := bstep (se 2 (by rfl) ⟨1543083, by rfl⟩ : syracuseStep 4114889 = 3086167) B3086167
theorem B20834819 : Blo 1827615 20834819 := bstep (se 1 (by rfl) ⟨15626114, by rfl⟩ : syracuseStep 20834819 = 31252229) B31252229
theorem B1829383 : Blo 1827615 1829383 := bstep (se 1 (by rfl) ⟨1372037, by rfl⟩ : syracuseStep 1829383 = 2744075) B2744075
theorem B1829391 : Blo 1827615 1829391 := bstep (se 1 (by rfl) ⟨1372043, by rfl⟩ : syracuseStep 1829391 = 2744087) B2744087
theorem B5204513 : Blo 1827615 5204513 := bstep (se 2 (by rfl) ⟨1951692, by rfl⟩ : syracuseStep 5204513 = 3903385) B3903385
theorem B1829435 : Blo 1827615 1829435 := bstep (se 1 (by rfl) ⟨1372076, by rfl⟩ : syracuseStep 1829435 = 2744153) B2744153
theorem B19032641 : Blo 1827615 19032641 := bstep (se 2 (by rfl) ⟨7137240, by rfl⟩ : syracuseStep 19032641 = 14274481) B14274481
theorem B1829511 : Blo 1827615 1829511 := bstep (se 1 (by rfl) ⟨1372133, by rfl⟩ : syracuseStep 1829511 = 2744267) B2744267
theorem B1829519 : Blo 1827615 1829519 := bstep (se 1 (by rfl) ⟨1372139, by rfl⟩ : syracuseStep 1829519 = 2744279) B2744279
theorem B1829563 : Blo 1827615 1829563 := bstep (se 1 (by rfl) ⟨1372172, by rfl⟩ : syracuseStep 1829563 = 2744345) B2744345
theorem B35146457 : Blo 1827615 35146457 := bstep (se 2 (by rfl) ⟨13179921, by rfl⟩ : syracuseStep 35146457 = 26359843) B26359843
theorem B9259757 : Blo 1827615 9259757 := bstep (se 3 (by rfl) ⟨1736204, by rfl⟩ : syracuseStep 9259757 = 3472409) B3472409
theorem B20048729 : Blo 1827615 20048729 := bstep (se 2 (by rfl) ⟨7518273, by rfl⟩ : syracuseStep 20048729 = 15036547) B15036547
theorem B6171659 : Blo 1827615 6171659 := bstep (se 1 (by rfl) ⟨4628744, by rfl⟩ : syracuseStep 6171659 = 9257489) B9257489
theorem B6171767 : Blo 1827615 6171767 := bstep (se 1 (by rfl) ⟨4628825, by rfl⟩ : syracuseStep 6171767 = 9257651) B9257651
theorem B4115591 : Blo 1827615 4115591 := bstep (se 1 (by rfl) ⟨3086693, by rfl⟩ : syracuseStep 4115591 = 6173387) B6173387
theorem B6941933 : Blo 1827615 6941933 := bstep (se 3 (by rfl) ⟨1301612, by rfl⟩ : syracuseStep 6941933 = 2603225) B2603225
theorem B8457473 : Blo 1827615 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B4115771 : Blo 1827615 4115771 := bstep (se 1 (by rfl) ⟨3086828, by rfl⟩ : syracuseStep 4115771 = 6173657) B6173657
theorem B4115897 : Blo 1827615 4115897 := bstep (se 2 (by rfl) ⟨1543461, by rfl⟩ : syracuseStep 4115897 = 3086923) B3086923
theorem B9252305 : Blo 1827615 9252305 := bstep (se 2 (by rfl) ⟨3469614, by rfl⟩ : syracuseStep 9252305 = 6939229) B6939229
theorem B5205505 : Blo 1827615 5205505 := bstep (se 2 (by rfl) ⟨1952064, by rfl⟩ : syracuseStep 5205505 = 3904129) B3904129
theorem B9260567 : Blo 1827615 9260567 := bstep (se 1 (by rfl) ⟨6945425, by rfl⟩ : syracuseStep 9260567 = 13890851) B13890851
theorem B46845539 : Blo 1827615 46845539 := bstep (se 1 (by rfl) ⟨35134154, by rfl⟩ : syracuseStep 46845539 = 70268309) B70268309
theorem B17567351 : Blo 1827615 17567351 := bstep (se 1 (by rfl) ⟨13175513, by rfl⟩ : syracuseStep 17567351 = 26351027) B26351027
theorem B6172361 : Blo 1827615 6172361 := bstep (se 2 (by rfl) ⟨2314635, by rfl⟩ : syracuseStep 6172361 = 4629271) B4629271
theorem B10555109 : Blo 1827615 10555109 := bstep (se 4 (by rfl) ⟨989541, by rfl⟩ : syracuseStep 10555109 = 1979083) B1979083
theorem B2674447 : Blo 1827615 2674447 := bstep (se 1 (by rfl) ⟨2005835, by rfl⟩ : syracuseStep 2674447 = 4011671) B4011671
theorem B4116239 : Blo 1827615 4116239 := bstep (se 1 (by rfl) ⟨3087179, by rfl⟩ : syracuseStep 4116239 = 6174359) B6174359
theorem B4116257 : Blo 1827615 4116257 := bstep (se 2 (by rfl) ⟨1543596, by rfl⟩ : syracuseStep 4116257 = 3087193) B3087193
theorem B5861153 : Blo 1827615 5861153 := bstep (se 2 (by rfl) ⟨2197932, by rfl⟩ : syracuseStep 5861153 = 4395865) B4395865
theorem B5934995 : Blo 1827615 5934995 := bstep (se 1 (by rfl) ⟨4451246, by rfl⟩ : syracuseStep 5934995 = 8902493) B8902493
theorem B6942617 : Blo 1827615 6942617 := bstep (se 2 (by rfl) ⟨2603481, by rfl⟩ : syracuseStep 6942617 = 5206963) B5206963
theorem B3084331 : Blo 1827615 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B2084923 : Blo 1827615 2084923 := bstep (se 1 (by rfl) ⟨1563692, by rfl⟩ : syracuseStep 2084923 = 3127385) B3127385
theorem B4116599 : Blo 1827615 4116599 := bstep (se 1 (by rfl) ⟨3087449, by rfl⟩ : syracuseStep 4116599 = 6174899) B6174899
theorem B3084473 : Blo 1827615 3084473 := bstep (se 2 (by rfl) ⟨1156677, by rfl⟩ : syracuseStep 3084473 = 2313355) B2313355
theorem B4944073 : Blo 1827615 4944073 := bstep (se 2 (by rfl) ⟨1854027, by rfl⟩ : syracuseStep 4944073 = 3708055) B3708055
theorem B5558557 : Blo 1827615 5558557 := bstep (se 3 (by rfl) ⟨1042229, by rfl⟩ : syracuseStep 5558557 = 2084459) B2084459
theorem B6173063 : Blo 1827615 6173063 := bstep (se 1 (by rfl) ⟨4629797, by rfl⟩ : syracuseStep 6173063 = 9259595) B9259595
theorem B66720449 : Blo 1827615 66720449 := bstep (se 2 (by rfl) ⟨25020168, by rfl⟩ : syracuseStep 66720449 = 50040337) B50040337
theorem B6173441 : Blo 1827615 6173441 := bstep (se 2 (by rfl) ⟨2315040, by rfl⟩ : syracuseStep 6173441 = 4630081) B4630081
theorem B6943603 : Blo 1827615 6943603 := bstep (se 1 (by rfl) ⟨5207702, by rfl⟩ : syracuseStep 6943603 = 10415405) B10415405
theorem B3085175 : Blo 1827615 3085175 := bstep (se 1 (by rfl) ⟨2313881, by rfl⟩ : syracuseStep 3085175 = 4627763) B4627763
theorem B3470215 : Blo 1827615 3470215 := bstep (se 1 (by rfl) ⟨2602661, by rfl⟩ : syracuseStep 3470215 = 5205323) B5205323
theorem B4395961 : Blo 1827615 4395961 := bstep (se 2 (by rfl) ⟨1648485, by rfl⟩ : syracuseStep 4395961 = 3296971) B3296971
theorem B6771755 : Blo 1827615 6771755 := bstep (se 1 (by rfl) ⟨5078816, by rfl⟩ : syracuseStep 6771755 = 10157633) B10157633
theorem B2741435 : Blo 1827615 2741435 := bstep (se 1 (by rfl) ⟨2056076, by rfl⟩ : syracuseStep 2741435 = 4112153) B4112153
theorem B2741495 : Blo 1827615 2741495 := bstep (se 1 (by rfl) ⟨2056121, by rfl⟩ : syracuseStep 2741495 = 4112243) B4112243
theorem B2741519 : Blo 1827615 2741519 := bstep (se 1 (by rfl) ⟨2056139, by rfl⟩ : syracuseStep 2741519 = 4112279) B4112279
theorem B2602297 : Blo 1827615 2602297 := bstep (se 2 (by rfl) ⟨975861, by rfl⟩ : syracuseStep 2602297 = 1951723) B1951723
theorem B2741561 : Blo 1827615 2741561 := bstep (se 2 (by rfl) ⟨1028085, by rfl⟩ : syracuseStep 2741561 = 2056171) B2056171
theorem B3085627 : Blo 1827615 3085627 := bstep (se 1 (by rfl) ⟨2314220, by rfl⟩ : syracuseStep 3085627 = 4628441) B4628441
theorem B2741639 : Blo 1827615 2741639 := bstep (se 1 (by rfl) ⟨2056229, by rfl⟩ : syracuseStep 2741639 = 4112459) B4112459
theorem B2741675 : Blo 1827615 2741675 := bstep (se 1 (by rfl) ⟨2056256, by rfl⟩ : syracuseStep 2741675 = 4112513) B4112513
theorem B14824889 : Blo 1827615 14824889 := bstep (se 2 (by rfl) ⟨5559333, by rfl⟩ : syracuseStep 14824889 = 11118667) B11118667
theorem B2741705 : Blo 1827615 2741705 := bstep (se 2 (by rfl) ⟨1028139, by rfl⟩ : syracuseStep 2741705 = 2056279) B2056279
theorem B3085769 : Blo 1827615 3085769 := bstep (se 2 (by rfl) ⟨1157163, by rfl⟩ : syracuseStep 3085769 = 2314327) B2314327
theorem B9254411 : Blo 1827615 9254411 := bstep (se 1 (by rfl) ⟨6940808, by rfl⟩ : syracuseStep 9254411 = 13881617) B13881617
theorem B6174251 : Blo 1827615 6174251 := bstep (se 1 (by rfl) ⟨4630688, by rfl⟩ : syracuseStep 6174251 = 9261377) B9261377
theorem B2741819 : Blo 1827615 2741819 := bstep (se 1 (by rfl) ⟨2056364, by rfl⟩ : syracuseStep 2741819 = 4112729) B4112729
theorem B2741879 : Blo 1827615 2741879 := bstep (se 1 (by rfl) ⟨2056409, by rfl⟩ : syracuseStep 2741879 = 4112819) B4112819
theorem B2741903 : Blo 1827615 2741903 := bstep (se 1 (by rfl) ⟨2056427, by rfl⟩ : syracuseStep 2741903 = 4112855) B4112855
theorem B35149463 : Blo 1827615 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B9254573 : Blo 1827615 9254573 := bstep (se 3 (by rfl) ⟨1735232, by rfl⟩ : syracuseStep 9254573 = 3470465) B3470465
theorem B2741945 : Blo 1827615 2741945 := bstep (se 2 (by rfl) ⟨1028229, by rfl⟩ : syracuseStep 2741945 = 2056459) B2056459
theorem B20821697 : Blo 1827615 20821697 := bstep (se 2 (by rfl) ⟨7808136, by rfl⟩ : syracuseStep 20821697 = 15616273) B15616273
theorem B9885377 : Blo 1827615 9885377 := bstep (se 2 (by rfl) ⟨3707016, by rfl⟩ : syracuseStep 9885377 = 7414033) B7414033
theorem B2742023 : Blo 1827615 2742023 := bstep (se 1 (by rfl) ⟨2056517, by rfl⟩ : syracuseStep 2742023 = 4113035) B4113035
theorem B1980175 : Blo 1827615 1980175 := bstep (se 1 (by rfl) ⟨1485131, by rfl⟩ : syracuseStep 1980175 = 2970263) B2970263
theorem B2742059 : Blo 1827615 2742059 := bstep (se 1 (by rfl) ⟨2056544, by rfl⟩ : syracuseStep 2742059 = 4113089) B4113089
theorem B2742089 : Blo 1827615 2742089 := bstep (se 2 (by rfl) ⟨1028283, by rfl⟩ : syracuseStep 2742089 = 2056567) B2056567
theorem B2742203 : Blo 1827615 2742203 := bstep (se 1 (by rfl) ⟨2056652, by rfl⟩ : syracuseStep 2742203 = 4113305) B4113305
theorem B2742263 : Blo 1827615 2742263 := bstep (se 1 (by rfl) ⟨2056697, by rfl⟩ : syracuseStep 2742263 = 4113395) B4113395
theorem B2742287 : Blo 1827615 2742287 := bstep (se 1 (by rfl) ⟨2056715, by rfl⟩ : syracuseStep 2742287 = 4113431) B4113431
theorem B2742329 : Blo 1827615 2742329 := bstep (se 2 (by rfl) ⟨1028373, by rfl⟩ : syracuseStep 2742329 = 2056747) B2056747
theorem B4454459 : Blo 1827615 4454459 := bstep (se 1 (by rfl) ⟨3340844, by rfl⟩ : syracuseStep 4454459 = 6681689) B6681689
theorem B16685189 : Blo 1827615 16685189 := bstep (se 4 (by rfl) ⟨1564236, by rfl⟩ : syracuseStep 16685189 = 3128473) B3128473
theorem B2742407 : Blo 1827615 2742407 := bstep (se 1 (by rfl) ⟨2056805, by rfl⟩ : syracuseStep 2742407 = 4113611) B4113611
theorem B3086471 : Blo 1827615 3086471 := bstep (se 1 (by rfl) ⟨2314853, by rfl⟩ : syracuseStep 3086471 = 4629707) B4629707
theorem B2742443 : Blo 1827615 2742443 := bstep (se 1 (by rfl) ⟨2056832, by rfl⟩ : syracuseStep 2742443 = 4113665) B4113665
theorem B2742473 : Blo 1827615 2742473 := bstep (se 2 (by rfl) ⟨1028427, by rfl⟩ : syracuseStep 2742473 = 2056855) B2056855
theorem B4757705 : Blo 1827615 4757705 := bstep (se 2 (by rfl) ⟨1784139, by rfl⟩ : syracuseStep 4757705 = 3568279) B3568279
theorem B20830445 : Blo 1827615 20830445 := bstep (se 3 (by rfl) ⟨3905708, by rfl⟩ : syracuseStep 20830445 = 7811417) B7811417
theorem B106928437 : Blo 1827615 106928437 := bstep (se 5 (by rfl) ⟨5012270, by rfl⟩ : syracuseStep 106928437 = 10024541) B10024541
theorem B2742587 : Blo 1827615 2742587 := bstep (se 1 (by rfl) ⟨2056940, by rfl⟩ : syracuseStep 2742587 = 4113881) B4113881
theorem B2742647 : Blo 1827615 2742647 := bstep (se 1 (by rfl) ⟨2056985, by rfl⟩ : syracuseStep 2742647 = 4113971) B4113971
theorem B5208455 : Blo 1827615 5208455 := bstep (se 1 (by rfl) ⟨3906341, by rfl⟩ : syracuseStep 5208455 = 7812683) B7812683
theorem B2742671 : Blo 1827615 2742671 := bstep (se 1 (by rfl) ⟨2057003, by rfl⟩ : syracuseStep 2742671 = 4114007) B4114007
theorem B4626841 : Blo 1827615 4626841 := bstep (se 2 (by rfl) ⟨1735065, by rfl⟩ : syracuseStep 4626841 = 3470131) B3470131
theorem B2742713 : Blo 1827615 2742713 := bstep (se 2 (by rfl) ⟨1028517, by rfl⟩ : syracuseStep 2742713 = 2057035) B2057035
theorem B3471817 : Blo 1827615 3471817 := bstep (se 2 (by rfl) ⟨1301931, by rfl⟩ : syracuseStep 3471817 = 2603863) B2603863
theorem B8788445 : Blo 1827615 8788445 := bstep (se 3 (by rfl) ⟨1647833, by rfl⟩ : syracuseStep 8788445 = 3295667) B3295667
theorem B2742791 : Blo 1827615 2742791 := bstep (se 1 (by rfl) ⟨2057093, by rfl⟩ : syracuseStep 2742791 = 4114187) B4114187
theorem B2742827 : Blo 1827615 2742827 := bstep (se 1 (by rfl) ⟨2057120, by rfl⟩ : syracuseStep 2742827 = 4114241) B4114241
theorem B4627003 : Blo 1827615 4627003 := bstep (se 1 (by rfl) ⟨3470252, by rfl⟩ : syracuseStep 4627003 = 6940505) B6940505
theorem B5208637 : Blo 1827615 5208637 := bstep (se 3 (by rfl) ⟨976619, by rfl⟩ : syracuseStep 5208637 = 1953239) B1953239
theorem B2742857 : Blo 1827615 2742857 := bstep (se 2 (by rfl) ⟨1028571, by rfl⟩ : syracuseStep 2742857 = 2057143) B2057143
theorem B5208695 : Blo 1827615 5208695 := bstep (se 1 (by rfl) ⟨3906521, by rfl⟩ : syracuseStep 5208695 = 7813043) B7813043
theorem B2742971 : Blo 1827615 2742971 := bstep (se 1 (by rfl) ⟨2057228, by rfl⟩ : syracuseStep 2742971 = 4114457) B4114457
theorem B4627145 : Blo 1827615 4627145 := bstep (se 2 (by rfl) ⟨1735179, by rfl⟩ : syracuseStep 4627145 = 3470359) B3470359
theorem B2743031 : Blo 1827615 2743031 := bstep (se 1 (by rfl) ⟨2057273, by rfl⟩ : syracuseStep 2743031 = 4114547) B4114547
theorem B2603783 : Blo 1827615 2603783 := bstep (se 1 (by rfl) ⟨1952837, by rfl⟩ : syracuseStep 2603783 = 3905675) B3905675
theorem B71236367 : Blo 1827615 71236367 := bstep (se 1 (by rfl) ⟨53427275, by rfl⟩ : syracuseStep 71236367 = 106854551) B106854551
theorem B2743055 : Blo 1827615 2743055 := bstep (se 1 (by rfl) ⟨2057291, by rfl⟩ : syracuseStep 2743055 = 4114583) B4114583
theorem B3087119 : Blo 1827615 3087119 := bstep (se 1 (by rfl) ⟨2315339, by rfl⟩ : syracuseStep 3087119 = 4630679) B4630679
theorem B8788769 : Blo 1827615 8788769 := bstep (se 2 (by rfl) ⟨3295788, by rfl⟩ : syracuseStep 8788769 = 6591577) B6591577
theorem B2743097 : Blo 1827615 2743097 := bstep (se 2 (by rfl) ⟨1028661, by rfl⟩ : syracuseStep 2743097 = 2057323) B2057323
theorem B71228261 : Blo 1827615 71228261 := bstep (se 4 (by rfl) ⟨6677649, by rfl⟩ : syracuseStep 71228261 = 13355299) B13355299
theorem B2743175 : Blo 1827615 2743175 := bstep (se 1 (by rfl) ⟨2057381, by rfl⟩ : syracuseStep 2743175 = 4114763) B4114763
theorem B2743211 : Blo 1827615 2743211 := bstep (se 1 (by rfl) ⟨2057408, by rfl⟩ : syracuseStep 2743211 = 4114817) B4114817
theorem B2743241 : Blo 1827615 2743241 := bstep (se 2 (by rfl) ⟨1028715, by rfl⟩ : syracuseStep 2743241 = 2057431) B2057431
theorem B8027147 : Blo 1827615 8027147 := bstep (se 1 (by rfl) ⟨6020360, by rfl⟩ : syracuseStep 8027147 = 12040721) B12040721
theorem B10411031 : Blo 1827615 10411031 := bstep (se 1 (by rfl) ⟨7808273, by rfl⟩ : syracuseStep 10411031 = 15616547) B15616547
theorem B6945821 : Blo 1827615 6945821 := bstep (se 3 (by rfl) ⟨1302341, by rfl⟩ : syracuseStep 6945821 = 2604683) B2604683
theorem B4627489 : Blo 1827615 4627489 := bstep (se 2 (by rfl) ⟨1735308, by rfl⟩ : syracuseStep 4627489 = 3470617) B3470617
theorem B2743355 : Blo 1827615 2743355 := bstep (se 1 (by rfl) ⟨2057516, by rfl⟩ : syracuseStep 2743355 = 4115033) B4115033
theorem B2604091 : Blo 1827615 2604091 := bstep (se 1 (by rfl) ⟨1953068, by rfl⟩ : syracuseStep 2604091 = 3906137) B3906137
theorem B2743415 : Blo 1827615 2743415 := bstep (se 1 (by rfl) ⟨2057561, by rfl⟩ : syracuseStep 2743415 = 4115123) B4115123
theorem B8911991 : Blo 1827615 8911991 := bstep (se 1 (by rfl) ⟨6683993, by rfl⟩ : syracuseStep 8911991 = 13367987) B13367987
theorem B2743439 : Blo 1827615 2743439 := bstep (se 1 (by rfl) ⟨2057579, by rfl⟩ : syracuseStep 2743439 = 4115159) B4115159
theorem B2743481 : Blo 1827615 2743481 := bstep (se 2 (by rfl) ⟨1028805, by rfl⟩ : syracuseStep 2743481 = 2057611) B2057611
theorem B13540589 : Blo 1827615 13540589 := bstep (se 3 (by rfl) ⟨2538860, by rfl⟩ : syracuseStep 13540589 = 5077721) B5077721
theorem B9256193 : Blo 1827615 9256193 := bstep (se 2 (by rfl) ⟨3471072, by rfl⟩ : syracuseStep 9256193 = 6942145) B6942145
theorem B2743559 : Blo 1827615 2743559 := bstep (se 1 (by rfl) ⟨2057669, by rfl⟩ : syracuseStep 2743559 = 4115339) B4115339
theorem B2743595 : Blo 1827615 2743595 := bstep (se 1 (by rfl) ⟨2057696, by rfl⟩ : syracuseStep 2743595 = 4115393) B4115393
theorem B2743625 : Blo 1827615 2743625 := bstep (se 2 (by rfl) ⟨1028859, by rfl⟩ : syracuseStep 2743625 = 2057719) B2057719
theorem B6258055 : Blo 1827615 6258055 := bstep (se 1 (by rfl) ⟨4693541, by rfl⟩ : syracuseStep 6258055 = 9387083) B9387083
theorem B2743739 : Blo 1827615 2743739 := bstep (se 1 (by rfl) ⟨2057804, by rfl⟩ : syracuseStep 2743739 = 4115609) B4115609
theorem B2743799 : Blo 1827615 2743799 := bstep (se 1 (by rfl) ⟨2057849, by rfl⟩ : syracuseStep 2743799 = 4115699) B4115699
theorem B11714051 : Blo 1827615 11714051 := bstep (se 1 (by rfl) ⟨8785538, by rfl⟩ : syracuseStep 11714051 = 17571077) B17571077
theorem B2743823 : Blo 1827615 2743823 := bstep (se 1 (by rfl) ⟨2057867, by rfl⟩ : syracuseStep 2743823 = 4115735) B4115735
theorem B2743865 : Blo 1827615 2743865 := bstep (se 2 (by rfl) ⟨1028949, by rfl⟩ : syracuseStep 2743865 = 2057899) B2057899
theorem B10419779 : Blo 1827615 10419779 := bstep (se 1 (by rfl) ⟨7814834, by rfl⟩ : syracuseStep 10419779 = 15629669) B15629669
theorem B30047843 : Blo 1827615 30047843 := bstep (se 1 (by rfl) ⟨22535882, by rfl⟩ : syracuseStep 30047843 = 45071765) B45071765
theorem B4169335 : Blo 1827615 4169335 := bstep (se 1 (by rfl) ⟨3127001, by rfl⟩ : syracuseStep 4169335 = 6254003) B6254003
theorem B4628087 : Blo 1827615 4628087 := bstep (se 1 (by rfl) ⟨3471065, by rfl⟩ : syracuseStep 4628087 = 6942131) B6942131
theorem B2743943 : Blo 1827615 2743943 := bstep (se 1 (by rfl) ⟨2057957, by rfl⟩ : syracuseStep 2743943 = 4115915) B4115915
theorem B5209753 : Blo 1827615 5209753 := bstep (se 2 (by rfl) ⟨1953657, by rfl⟩ : syracuseStep 5209753 = 3907315) B3907315
theorem B2743979 : Blo 1827615 2743979 := bstep (se 1 (by rfl) ⟨2057984, by rfl⟩ : syracuseStep 2743979 = 4115969) B4115969
theorem B2744009 : Blo 1827615 2744009 := bstep (se 2 (by rfl) ⟨1029003, by rfl⟩ : syracuseStep 2744009 = 2058007) B2058007
theorem B3907273 : Blo 1827615 3907273 := bstep (se 2 (by rfl) ⟨1465227, by rfl⟩ : syracuseStep 3907273 = 2930455) B2930455
theorem B6946505 : Blo 1827615 6946505 := bstep (se 2 (by rfl) ⟨2604939, by rfl⟩ : syracuseStep 6946505 = 5209879) B5209879
theorem B4112171 : Blo 1827615 4112171 := bstep (se 1 (by rfl) ⟨3084128, by rfl⟩ : syracuseStep 4112171 = 6168257) B6168257
theorem B33349427 : Blo 1827615 33349427 := bstep (se 1 (by rfl) ⟨25012070, by rfl⟩ : syracuseStep 33349427 = 50024141) B50024141
theorem B2744123 : Blo 1827615 2744123 := bstep (se 1 (by rfl) ⟨2058092, by rfl⟩ : syracuseStep 2744123 = 4116185) B4116185
theorem B7814971 : Blo 1827615 7814971 := bstep (se 1 (by rfl) ⟨5861228, by rfl⟩ : syracuseStep 7814971 = 11722457) B11722457
theorem B2744183 : Blo 1827615 2744183 := bstep (se 1 (by rfl) ⟨2058137, by rfl⟩ : syracuseStep 2744183 = 4116275) B4116275
theorem B2744207 : Blo 1827615 2744207 := bstep (se 1 (by rfl) ⟨2058155, by rfl⟩ : syracuseStep 2744207 = 4116311) B4116311
theorem B23420825 : Blo 1827615 23420825 := bstep (se 2 (by rfl) ⟨8782809, by rfl⟩ : syracuseStep 23420825 = 17565619) B17565619
theorem B6168473 : Blo 1827615 6168473 := bstep (se 2 (by rfl) ⟨2313177, by rfl⟩ : syracuseStep 6168473 = 4626355) B4626355
theorem B2744249 : Blo 1827615 2744249 := bstep (se 2 (by rfl) ⟨1029093, by rfl⟩ : syracuseStep 2744249 = 2058187) B2058187
theorem B6946823 : Blo 1827615 6946823 := bstep (se 1 (by rfl) ⟨5210117, by rfl⟩ : syracuseStep 6946823 = 10420235) B10420235
theorem B21405725 : Blo 1827615 21405725 := bstep (se 3 (by rfl) ⟨4013573, by rfl⟩ : syracuseStep 21405725 = 8027147) B8027147
theorem B4112441 : Blo 1827615 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B2744399 : Blo 1827615 2744399 := bstep (se 1 (by rfl) ⟨2058299, by rfl⟩ : syracuseStep 2744399 = 4116599) B4116599
theorem B2056315 : Blo 1827615 2056315 := bstep (se 1 (by rfl) ⟨1542236, by rfl⟩ : syracuseStep 2056315 = 3084473) B3084473
theorem B23765309 : Blo 1827615 23765309 := bstep (se 3 (by rfl) ⟨4455995, by rfl⟩ : syracuseStep 23765309 = 8911991) B8911991
theorem B160350533 : Blo 1827615 160350533 := bstep (se 4 (by rfl) ⟨15032862, by rfl⟩ : syracuseStep 160350533 = 30065725) B30065725
theorem B4112783 : Blo 1827615 4112783 := bstep (se 1 (by rfl) ⟨3084587, by rfl⟩ : syracuseStep 4112783 = 6169175) B6169175
theorem B6169121 : Blo 1827615 6169121 := bstep (se 2 (by rfl) ⟨2313420, by rfl⟩ : syracuseStep 6169121 = 4626841) B4626841
theorem B8905249 : Blo 1827615 8905249 := bstep (se 2 (by rfl) ⟨3339468, by rfl⟩ : syracuseStep 8905249 = 6678937) B6678937
theorem B2056783 : Blo 1827615 2056783 := bstep (se 1 (by rfl) ⟨1542587, by rfl⟩ : syracuseStep 2056783 = 3085175) B3085175
theorem B4629089 : Blo 1827615 4629089 := bstep (se 2 (by rfl) ⟨1735908, by rfl⟩ : syracuseStep 4629089 = 3471817) B3471817
theorem B22553261 : Blo 1827615 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B4514503 : Blo 1827615 4514503 := bstep (se 1 (by rfl) ⟨3385877, by rfl⟩ : syracuseStep 4514503 = 6771755) B6771755
theorem B4113107 : Blo 1827615 4113107 := bstep (se 1 (by rfl) ⟨3084830, by rfl⟩ : syracuseStep 4113107 = 6169661) B6169661
theorem B6169337 : Blo 1827615 6169337 := bstep (se 2 (by rfl) ⟨2313501, by rfl⟩ : syracuseStep 6169337 = 4627003) B4627003
theorem B5636857 : Blo 1827615 5636857 := bstep (se 2 (by rfl) ⟨2113821, by rfl⟩ : syracuseStep 5636857 = 4227643) B4227643
theorem B5858077 : Blo 1827615 5858077 := bstep (se 3 (by rfl) ⟨1098389, by rfl⟩ : syracuseStep 5858077 = 2196779) B2196779
theorem B7037725 : Blo 1827615 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B1827623 : Blo 1827615 1827623 := bstep (se 1 (by rfl) ⟨1370717, by rfl⟩ : syracuseStep 1827623 = 2741435) B2741435
theorem B1827663 : Blo 1827615 1827663 := bstep (se 1 (by rfl) ⟨1370747, by rfl⟩ : syracuseStep 1827663 = 2741495) B2741495
theorem B1827679 : Blo 1827615 1827679 := bstep (se 1 (by rfl) ⟨1370759, by rfl⟩ : syracuseStep 1827679 = 2741519) B2741519
theorem B1827707 : Blo 1827615 1827707 := bstep (se 1 (by rfl) ⟨1370780, by rfl⟩ : syracuseStep 1827707 = 2741561) B2741561
theorem B1827759 : Blo 1827615 1827759 := bstep (se 1 (by rfl) ⟨1370819, by rfl⟩ : syracuseStep 1827759 = 2741639) B2741639
theorem B1827783 : Blo 1827615 1827783 := bstep (se 1 (by rfl) ⟨1370837, by rfl⟩ : syracuseStep 1827783 = 2741675) B2741675
theorem B1827803 : Blo 1827615 1827803 := bstep (se 1 (by rfl) ⟨1370852, by rfl⟩ : syracuseStep 1827803 = 2741705) B2741705
theorem B2196443 : Blo 1827615 2196443 := bstep (se 1 (by rfl) ⟨1647332, by rfl⟩ : syracuseStep 2196443 = 3294665) B3294665
theorem B2057179 : Blo 1827615 2057179 := bstep (se 1 (by rfl) ⟨1542884, by rfl⟩ : syracuseStep 2057179 = 3085769) B3085769
theorem B6169607 : Blo 1827615 6169607 := bstep (se 1 (by rfl) ⟨4627205, by rfl⟩ : syracuseStep 6169607 = 9254411) B9254411
theorem B1827879 : Blo 1827615 1827879 := bstep (se 1 (by rfl) ⟨1370909, by rfl⟩ : syracuseStep 1827879 = 2741819) B2741819
theorem B43402291 : Blo 1827615 43402291 := bstep (se 1 (by rfl) ⟨32551718, by rfl⟩ : syracuseStep 43402291 = 65103437) B65103437
theorem B1827919 : Blo 1827615 1827919 := bstep (se 1 (by rfl) ⟨1370939, by rfl⟩ : syracuseStep 1827919 = 2741879) B2741879
theorem B1827935 : Blo 1827615 1827935 := bstep (se 1 (by rfl) ⟨1370951, by rfl⟩ : syracuseStep 1827935 = 2741903) B2741903
theorem B6169715 : Blo 1827615 6169715 := bstep (se 1 (by rfl) ⟨4627286, by rfl⟩ : syracuseStep 6169715 = 9254573) B9254573
theorem B19776631 : Blo 1827615 19776631 := bstep (se 1 (by rfl) ⟨14832473, by rfl⟩ : syracuseStep 19776631 = 29664947) B29664947
theorem B1827963 : Blo 1827615 1827963 := bstep (se 1 (by rfl) ⟨1370972, by rfl⟩ : syracuseStep 1827963 = 2741945) B2741945
theorem B9258137 : Blo 1827615 9258137 := bstep (se 2 (by rfl) ⟨3471801, by rfl⟩ : syracuseStep 9258137 = 6943603) B6943603
theorem B1828015 : Blo 1827615 1828015 := bstep (se 1 (by rfl) ⟨1371011, by rfl⟩ : syracuseStep 1828015 = 2742023) B2742023
theorem B1828039 : Blo 1827615 1828039 := bstep (se 1 (by rfl) ⟨1371029, by rfl⟩ : syracuseStep 1828039 = 2742059) B2742059
theorem B1828059 : Blo 1827615 1828059 := bstep (se 1 (by rfl) ⟨1371044, by rfl⟩ : syracuseStep 1828059 = 2742089) B2742089
theorem B1828135 : Blo 1827615 1828135 := bstep (se 1 (by rfl) ⟨1371101, by rfl⟩ : syracuseStep 1828135 = 2742203) B2742203
theorem B1828175 : Blo 1827615 1828175 := bstep (se 1 (by rfl) ⟨1371131, by rfl⟩ : syracuseStep 1828175 = 2742263) B2742263
theorem B1828191 : Blo 1827615 1828191 := bstep (se 1 (by rfl) ⟨1371143, by rfl⟩ : syracuseStep 1828191 = 2742287) B2742287
theorem B1828219 : Blo 1827615 1828219 := bstep (se 1 (by rfl) ⟨1371164, by rfl⟩ : syracuseStep 1828219 = 2742329) B2742329
theorem B6169985 : Blo 1827615 6169985 := bstep (se 2 (by rfl) ⟨2313744, by rfl⟩ : syracuseStep 6169985 = 4627489) B4627489
theorem B14263717 : Blo 1827615 14263717 := bstep (se 4 (by rfl) ⟨1337223, by rfl⟩ : syracuseStep 14263717 = 2674447) B2674447
theorem B13878701 : Blo 1827615 13878701 := bstep (se 3 (by rfl) ⟨2602256, by rfl⟩ : syracuseStep 13878701 = 5204513) B5204513
theorem B1828271 : Blo 1827615 1828271 := bstep (se 1 (by rfl) ⟨1371203, by rfl⟩ : syracuseStep 1828271 = 2742407) B2742407
theorem B2057647 : Blo 1827615 2057647 := bstep (se 1 (by rfl) ⟨1543235, by rfl⟩ : syracuseStep 2057647 = 3086471) B3086471
theorem B2196919 : Blo 1827615 2196919 := bstep (se 1 (by rfl) ⟨1647689, by rfl⟩ : syracuseStep 2196919 = 3295379) B3295379
theorem B1828295 : Blo 1827615 1828295 := bstep (se 1 (by rfl) ⟨1371221, by rfl⟩ : syracuseStep 1828295 = 2742443) B2742443
theorem B1828315 : Blo 1827615 1828315 := bstep (se 1 (by rfl) ⟨1371236, by rfl⟩ : syracuseStep 1828315 = 2742473) B2742473
theorem B3171803 : Blo 1827615 3171803 := bstep (se 1 (by rfl) ⟨2378852, by rfl⟩ : syracuseStep 3171803 = 4757705) B4757705
theorem B13886963 : Blo 1827615 13886963 := bstep (se 1 (by rfl) ⟨10415222, by rfl⟩ : syracuseStep 13886963 = 20830445) B20830445
theorem B1828391 : Blo 1827615 1828391 := bstep (se 1 (by rfl) ⟨1371293, by rfl⟩ : syracuseStep 1828391 = 2742587) B2742587
theorem B1828431 : Blo 1827615 1828431 := bstep (se 1 (by rfl) ⟨1371323, by rfl⟩ : syracuseStep 1828431 = 2742647) B2742647
theorem B1828447 : Blo 1827615 1828447 := bstep (se 1 (by rfl) ⟨1371335, by rfl⟩ : syracuseStep 1828447 = 2742671) B2742671
theorem B4114043 : Blo 1827615 4114043 := bstep (se 1 (by rfl) ⟨3085532, by rfl⟩ : syracuseStep 4114043 = 6171065) B6171065
theorem B1828475 : Blo 1827615 1828475 := bstep (se 1 (by rfl) ⟨1371356, by rfl⟩ : syracuseStep 1828475 = 2742713) B2742713
theorem B5858963 : Blo 1827615 5858963 := bstep (se 1 (by rfl) ⟨4394222, by rfl⟩ : syracuseStep 5858963 = 8788445) B8788445
theorem B1828527 : Blo 1827615 1828527 := bstep (se 1 (by rfl) ⟨1371395, by rfl⟩ : syracuseStep 1828527 = 2742791) B2742791
theorem B1828551 : Blo 1827615 1828551 := bstep (se 1 (by rfl) ⟨1371413, by rfl⟩ : syracuseStep 1828551 = 2742827) B2742827
theorem B1828571 : Blo 1827615 1828571 := bstep (se 1 (by rfl) ⟨1371428, by rfl⟩ : syracuseStep 1828571 = 2742857) B2742857
theorem B4114169 : Blo 1827615 4114169 := bstep (se 2 (by rfl) ⟨1542813, by rfl⟩ : syracuseStep 4114169 = 3085627) B3085627
theorem B1828647 : Blo 1827615 1828647 := bstep (se 1 (by rfl) ⟨1371485, by rfl⟩ : syracuseStep 1828647 = 2742971) B2742971
theorem B23430971 : Blo 1827615 23430971 := bstep (se 1 (by rfl) ⟨17573228, by rfl⟩ : syracuseStep 23430971 = 35146457) B35146457
theorem B1828687 : Blo 1827615 1828687 := bstep (se 1 (by rfl) ⟨1371515, by rfl⟩ : syracuseStep 1828687 = 2743031) B2743031
theorem B47490911 : Blo 1827615 47490911 := bstep (se 1 (by rfl) ⟨35618183, by rfl⟩ : syracuseStep 47490911 = 71236367) B71236367
theorem B1828703 : Blo 1827615 1828703 := bstep (se 1 (by rfl) ⟨1371527, by rfl⟩ : syracuseStep 1828703 = 2743055) B2743055
theorem B2058079 : Blo 1827615 2058079 := bstep (se 1 (by rfl) ⟨1543559, by rfl⟩ : syracuseStep 2058079 = 3087119) B3087119
theorem B5859179 : Blo 1827615 5859179 := bstep (se 1 (by rfl) ⟨4394384, by rfl⟩ : syracuseStep 5859179 = 8788769) B8788769
theorem B1828731 : Blo 1827615 1828731 := bstep (se 1 (by rfl) ⟨1371548, by rfl⟩ : syracuseStep 1828731 = 2743097) B2743097
theorem B1828783 : Blo 1827615 1828783 := bstep (se 1 (by rfl) ⟨1371587, by rfl⟩ : syracuseStep 1828783 = 2743175) B2743175
theorem B1828807 : Blo 1827615 1828807 := bstep (se 1 (by rfl) ⟨1371605, by rfl⟩ : syracuseStep 1828807 = 2743211) B2743211
theorem B1828827 : Blo 1827615 1828827 := bstep (se 1 (by rfl) ⟨1371620, by rfl⟩ : syracuseStep 1828827 = 2743241) B2743241
theorem B6940673 : Blo 1827615 6940673 := bstep (se 2 (by rfl) ⟨2602752, by rfl⟩ : syracuseStep 6940673 = 5205505) B5205505
theorem B4114439 : Blo 1827615 4114439 := bstep (se 1 (by rfl) ⟨3085829, by rfl⟩ : syracuseStep 4114439 = 6171659) B6171659
theorem B6940687 : Blo 1827615 6940687 := bstep (se 1 (by rfl) ⟨5205515, by rfl⟩ : syracuseStep 6940687 = 10411031) B10411031
theorem B4630547 : Blo 1827615 4630547 := bstep (se 1 (by rfl) ⟨3472910, by rfl⟩ : syracuseStep 4630547 = 6945821) B6945821
theorem B1828903 : Blo 1827615 1828903 := bstep (se 1 (by rfl) ⟨1371677, by rfl⟩ : syracuseStep 1828903 = 2743355) B2743355
theorem B4114511 : Blo 1827615 4114511 := bstep (se 1 (by rfl) ⟨3085883, by rfl⟩ : syracuseStep 4114511 = 6171767) B6171767
theorem B1828943 : Blo 1827615 1828943 := bstep (se 1 (by rfl) ⟨1371707, by rfl⟩ : syracuseStep 1828943 = 2743415) B2743415
theorem B1828959 : Blo 1827615 1828959 := bstep (se 1 (by rfl) ⟨1371719, by rfl⟩ : syracuseStep 1828959 = 2743439) B2743439
theorem B1828987 : Blo 1827615 1828987 := bstep (se 1 (by rfl) ⟨1371740, by rfl⟩ : syracuseStep 1828987 = 2743481) B2743481
theorem B6170795 : Blo 1827615 6170795 := bstep (se 1 (by rfl) ⟨4628096, by rfl⟩ : syracuseStep 6170795 = 9256193) B9256193
theorem B1829039 : Blo 1827615 1829039 := bstep (se 1 (by rfl) ⟨1371779, by rfl⟩ : syracuseStep 1829039 = 2743559) B2743559
theorem B1829063 : Blo 1827615 1829063 := bstep (se 1 (by rfl) ⟨1371797, by rfl⟩ : syracuseStep 1829063 = 2743595) B2743595
theorem B1829083 : Blo 1827615 1829083 := bstep (se 1 (by rfl) ⟨1371812, by rfl⟩ : syracuseStep 1829083 = 2743625) B2743625
theorem B53463277 : Blo 1827615 53463277 := bstep (se 3 (by rfl) ⟨10024364, by rfl⟩ : syracuseStep 53463277 = 20048729) B20048729
theorem B189942029 : Blo 1827615 189942029 := bstep (se 3 (by rfl) ⟨35614130, by rfl⟩ : syracuseStep 189942029 = 71228261) B71228261
theorem B1829159 : Blo 1827615 1829159 := bstep (se 1 (by rfl) ⟨1371869, by rfl⟩ : syracuseStep 1829159 = 2743739) B2743739
theorem B1829199 : Blo 1827615 1829199 := bstep (se 1 (by rfl) ⟨1371899, by rfl⟩ : syracuseStep 1829199 = 2743799) B2743799
theorem B7809367 : Blo 1827615 7809367 := bstep (se 1 (by rfl) ⟨5857025, by rfl⟩ : syracuseStep 7809367 = 11714051) B11714051
theorem B1829215 : Blo 1827615 1829215 := bstep (se 1 (by rfl) ⟨1371911, by rfl⟩ : syracuseStep 1829215 = 2743823) B2743823
theorem B2640233 : Blo 1827615 2640233 := bstep (se 2 (by rfl) ⟨990087, by rfl⟩ : syracuseStep 2640233 = 1980175) B1980175
theorem B1829243 : Blo 1827615 1829243 := bstep (se 1 (by rfl) ⟨1371932, by rfl⟩ : syracuseStep 1829243 = 2743865) B2743865
theorem B20031895 : Blo 1827615 20031895 := bstep (se 1 (by rfl) ⟨15023921, by rfl⟩ : syracuseStep 20031895 = 30047843) B30047843
theorem B31230359 : Blo 1827615 31230359 := bstep (se 1 (by rfl) ⟨23422769, by rfl⟩ : syracuseStep 31230359 = 46845539) B46845539
theorem B1829295 : Blo 1827615 1829295 := bstep (se 1 (by rfl) ⟨1371971, by rfl⟩ : syracuseStep 1829295 = 2743943) B2743943
theorem B1829319 : Blo 1827615 1829319 := bstep (se 1 (by rfl) ⟨1371989, by rfl⟩ : syracuseStep 1829319 = 2743979) B2743979
theorem B4114907 : Blo 1827615 4114907 := bstep (se 1 (by rfl) ⟨3086180, by rfl⟩ : syracuseStep 4114907 = 6172361) B6172361
theorem B1829339 : Blo 1827615 1829339 := bstep (se 1 (by rfl) ⟨1372004, by rfl⟩ : syracuseStep 1829339 = 2744009) B2744009
theorem B4631003 : Blo 1827615 4631003 := bstep (se 1 (by rfl) ⟨3473252, by rfl⟩ : syracuseStep 4631003 = 6946505) B6946505
theorem B6588953 : Blo 1827615 6588953 := bstep (se 2 (by rfl) ⟨2470857, by rfl⟩ : syracuseStep 6588953 = 4941715) B4941715
theorem B1829415 : Blo 1827615 1829415 := bstep (se 1 (by rfl) ⟨1372061, by rfl⟩ : syracuseStep 1829415 = 2744123) B2744123
theorem B1829455 : Blo 1827615 1829455 := bstep (se 1 (by rfl) ⟨1372091, by rfl⟩ : syracuseStep 1829455 = 2744183) B2744183
theorem B1829471 : Blo 1827615 1829471 := bstep (se 1 (by rfl) ⟨1372103, by rfl⟩ : syracuseStep 1829471 = 2744207) B2744207
theorem B1829499 : Blo 1827615 1829499 := bstep (se 1 (by rfl) ⟨1372124, by rfl⟩ : syracuseStep 1829499 = 2744249) B2744249
theorem B1829551 : Blo 1827615 1829551 := bstep (se 1 (by rfl) ⟨1372163, by rfl⟩ : syracuseStep 1829551 = 2744327) B2744327
theorem B6171335 : Blo 1827615 6171335 := bstep (se 1 (by rfl) ⟨4628501, by rfl⟩ : syracuseStep 6171335 = 9257003) B9257003
theorem B1829575 : Blo 1827615 1829575 := bstep (se 1 (by rfl) ⟨1372181, by rfl⟩ : syracuseStep 1829575 = 2744363) B2744363
theorem B1829595 : Blo 1827615 1829595 := bstep (se 1 (by rfl) ⟨1372196, by rfl⟩ : syracuseStep 1829595 = 2744393) B2744393
theorem B20818781 : Blo 1827615 20818781 := bstep (se 3 (by rfl) ⟨3903521, by rfl⟩ : syracuseStep 20818781 = 7807043) B7807043
theorem B4115375 : Blo 1827615 4115375 := bstep (se 1 (by rfl) ⟨3086531, by rfl⟩ : syracuseStep 4115375 = 6173063) B6173063
theorem B2780087 : Blo 1827615 2780087 := bstep (se 1 (by rfl) ⟨2085065, by rfl⟩ : syracuseStep 2780087 = 4170131) B4170131
theorem B4942775 : Blo 1827615 4942775 := bstep (se 1 (by rfl) ⟨3707081, by rfl⟩ : syracuseStep 4942775 = 7414163) B7414163
theorem B11119589 : Blo 1827615 11119589 := bstep (se 4 (by rfl) ⟨1042461, by rfl⟩ : syracuseStep 11119589 = 2084923) B2084923
theorem B15625295 : Blo 1827615 15625295 := bstep (se 1 (by rfl) ⟨11718971, by rfl⟩ : syracuseStep 15625295 = 23437943) B23437943
theorem B4115627 : Blo 1827615 4115627 := bstep (se 1 (by rfl) ⟨3086720, by rfl⟩ : syracuseStep 4115627 = 6173441) B6173441
theorem B6941963 : Blo 1827615 6941963 := bstep (se 1 (by rfl) ⟨5206472, by rfl⟩ : syracuseStep 6941963 = 10412945) B10412945
theorem B6172199 : Blo 1827615 6172199 := bstep (se 1 (by rfl) ⟨4629149, by rfl⟩ : syracuseStep 6172199 = 9258299) B9258299
theorem B2928251 : Blo 1827615 2928251 := bstep (se 1 (by rfl) ⟨2196188, by rfl⟩ : syracuseStep 2928251 = 4392377) B4392377
theorem B9883259 : Blo 1827615 9883259 := bstep (se 1 (by rfl) ⟨7412444, by rfl⟩ : syracuseStep 9883259 = 14824889) B14824889
theorem B6172307 : Blo 1827615 6172307 := bstep (se 1 (by rfl) ⟨4629230, by rfl⟩ : syracuseStep 6172307 = 9258461) B9258461
theorem B4116167 : Blo 1827615 4116167 := bstep (se 1 (by rfl) ⟨3087125, by rfl⟩ : syracuseStep 4116167 = 6174251) B6174251
theorem B6942419 : Blo 1827615 6942419 := bstep (se 1 (by rfl) ⟨5206814, by rfl⟩ : syracuseStep 6942419 = 10413629) B10413629
theorem B23432975 : Blo 1827615 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B13881131 : Blo 1827615 13881131 := bstep (se 1 (by rfl) ⟨10410848, by rfl⟩ : syracuseStep 13881131 = 20821697) B20821697
theorem B6590251 : Blo 1827615 6590251 := bstep (se 1 (by rfl) ⟨4942688, by rfl⟩ : syracuseStep 6590251 = 9885377) B9885377
theorem B6172523 : Blo 1827615 6172523 := bstep (se 1 (by rfl) ⟨4629392, by rfl⟩ : syracuseStep 6172523 = 9258785) B9258785
theorem B6172577 : Blo 1827615 6172577 := bstep (se 2 (by rfl) ⟨2314716, by rfl⟩ : syracuseStep 6172577 = 4629433) B4629433
theorem B5861281 : Blo 1827615 5861281 := bstep (se 2 (by rfl) ⟨2197980, by rfl⟩ : syracuseStep 5861281 = 4395961) B4395961
theorem B4943791 : Blo 1827615 4943791 := bstep (se 1 (by rfl) ⟨3707843, by rfl⟩ : syracuseStep 4943791 = 7415687) B7415687
theorem B2969639 : Blo 1827615 2969639 := bstep (se 1 (by rfl) ⟨2227229, by rfl⟩ : syracuseStep 2969639 = 4454459) B4454459
theorem B9252953 : Blo 1827615 9252953 := bstep (se 2 (by rfl) ⟨3469857, by rfl⟩ : syracuseStep 9252953 = 6939715) B6939715
theorem B11120755 : Blo 1827615 11120755 := bstep (se 1 (by rfl) ⟨8340566, by rfl⟩ : syracuseStep 11120755 = 16681133) B16681133
theorem B13889879 : Blo 1827615 13889879 := bstep (se 1 (by rfl) ⟨10417409, by rfl⟩ : syracuseStep 13889879 = 20834819) B20834819
theorem B3469729 : Blo 1827615 3469729 := bstep (se 2 (by rfl) ⟨1301148, by rfl⟩ : syracuseStep 3469729 = 2602297) B2602297
theorem B3084763 : Blo 1827615 3084763 := bstep (se 1 (by rfl) ⟨2313572, by rfl⟩ : syracuseStep 3084763 = 4627145) B4627145
theorem B6173171 : Blo 1827615 6173171 := bstep (se 1 (by rfl) ⟨4629878, by rfl⟩ : syracuseStep 6173171 = 9259757) B9259757
theorem B8344073 : Blo 1827615 8344073 := bstep (se 2 (by rfl) ⟨3129027, by rfl⟩ : syracuseStep 8344073 = 6258055) B6258055
theorem B6943421 : Blo 1827615 6943421 := bstep (se 3 (by rfl) ⟨1301891, by rfl⟩ : syracuseStep 6943421 = 2603783) B2603783
theorem B5559113 : Blo 1827615 5559113 := bstep (se 2 (by rfl) ⟨2084667, by rfl⟩ : syracuseStep 5559113 = 4169335) B4169335
theorem B6173711 : Blo 1827615 6173711 := bstep (se 1 (by rfl) ⟨4630283, by rfl⟩ : syracuseStep 6173711 = 9260567) B9260567
theorem B11711567 : Blo 1827615 11711567 := bstep (se 1 (by rfl) ⟨8783675, by rfl⟩ : syracuseStep 11711567 = 17567351) B17567351
theorem B3085391 : Blo 1827615 3085391 := bstep (se 1 (by rfl) ⟨2314043, by rfl⟩ : syracuseStep 3085391 = 4628087) B4628087
theorem B2741447 : Blo 1827615 2741447 := bstep (se 1 (by rfl) ⟨2056085, by rfl⟩ : syracuseStep 2741447 = 4112171) B4112171
theorem B2741609 : Blo 1827615 2741609 := bstep (se 2 (by rfl) ⟨1028103, by rfl⟩ : syracuseStep 2741609 = 2056207) B2056207
theorem B11720051 : Blo 1827615 11720051 := bstep (se 1 (by rfl) ⟨8790038, by rfl⟩ : syracuseStep 11720051 = 17580077) B17580077
theorem B2741687 : Blo 1827615 2741687 := bstep (se 1 (by rfl) ⟨2056265, by rfl⟩ : syracuseStep 2741687 = 4112531) B4112531
theorem B2741723 : Blo 1827615 2741723 := bstep (se 1 (by rfl) ⟨2056292, by rfl⟩ : syracuseStep 2741723 = 4112585) B4112585
theorem B5936627 : Blo 1827615 5936627 := bstep (se 1 (by rfl) ⟨4452470, by rfl⟩ : syracuseStep 5936627 = 8904941) B8904941
theorem B6592097 : Blo 1827615 6592097 := bstep (se 2 (by rfl) ⟨2472036, by rfl⟩ : syracuseStep 6592097 = 4944073) B4944073
theorem B6174305 : Blo 1827615 6174305 := bstep (se 2 (by rfl) ⟨2315364, by rfl⟩ : syracuseStep 6174305 = 4630729) B4630729
theorem B7411409 : Blo 1827615 7411409 := bstep (se 2 (by rfl) ⟨2779278, by rfl⟩ : syracuseStep 7411409 = 5558557) B5558557
theorem B142571249 : Blo 1827615 142571249 := bstep (se 2 (by rfl) ⟨53464218, by rfl⟩ : syracuseStep 142571249 = 106928437) B106928437
theorem B44480299 : Blo 1827615 44480299 := bstep (se 1 (by rfl) ⟨33360224, by rfl⟩ : syracuseStep 44480299 = 66720449) B66720449
theorem B2742191 : Blo 1827615 2742191 := bstep (se 1 (by rfl) ⟨2056643, by rfl⟩ : syracuseStep 2742191 = 4113287) B4113287
theorem B3086255 : Blo 1827615 3086255 := bstep (se 1 (by rfl) ⟨2314691, by rfl⟩ : syracuseStep 3086255 = 4629383) B4629383
theorem B2742281 : Blo 1827615 2742281 := bstep (se 2 (by rfl) ⟨1028355, by rfl⟩ : syracuseStep 2742281 = 2056711) B2056711
theorem B2742311 : Blo 1827615 2742311 := bstep (se 1 (by rfl) ⟨2056733, by rfl⟩ : syracuseStep 2742311 = 4113467) B4113467
theorem B3348559 : Blo 1827615 3348559 := bstep (se 1 (by rfl) ⟨2511419, by rfl⟩ : syracuseStep 3348559 = 5022839) B5022839
theorem B6944849 : Blo 1827615 6944849 := bstep (se 2 (by rfl) ⟨2604318, by rfl⟩ : syracuseStep 6944849 = 5208637) B5208637
theorem B2742395 : Blo 1827615 2742395 := bstep (se 1 (by rfl) ⟨2056796, by rfl⟩ : syracuseStep 2742395 = 4113593) B4113593
theorem B4626679 : Blo 1827615 4626679 := bstep (se 1 (by rfl) ⟨3470009, by rfl⟩ : syracuseStep 4626679 = 6940019) B6940019
theorem B2742521 : Blo 1827615 2742521 := bstep (se 2 (by rfl) ⟨1028445, by rfl⟩ : syracuseStep 2742521 = 2056891) B2056891
theorem B2742623 : Blo 1827615 2742623 := bstep (se 1 (by rfl) ⟨2056967, by rfl⟩ : syracuseStep 2742623 = 4113935) B4113935
theorem B3086687 : Blo 1827615 3086687 := bstep (se 1 (by rfl) ⟨2315015, by rfl⟩ : syracuseStep 3086687 = 4630031) B4630031
theorem B2742635 : Blo 1827615 2742635 := bstep (se 1 (by rfl) ⟨2056976, by rfl⟩ : syracuseStep 2742635 = 4113953) B4113953
theorem B4626953 : Blo 1827615 4626953 := bstep (se 2 (by rfl) ⟨1735107, by rfl⟩ : syracuseStep 4626953 = 3470215) B3470215
theorem B4626983 : Blo 1827615 4626983 := bstep (se 1 (by rfl) ⟨3470237, by rfl⟩ : syracuseStep 4626983 = 6940475) B6940475
theorem B2742863 : Blo 1827615 2742863 := bstep (se 1 (by rfl) ⟨2057147, by rfl⟩ : syracuseStep 2742863 = 4114295) B4114295
theorem B2742983 : Blo 1827615 2742983 := bstep (se 1 (by rfl) ⟨2057237, by rfl⟩ : syracuseStep 2742983 = 4114475) B4114475
theorem B3472121 : Blo 1827615 3472121 := bstep (se 2 (by rfl) ⟨1302045, by rfl⟩ : syracuseStep 3472121 = 2604091) B2604091
theorem B11123459 : Blo 1827615 11123459 := bstep (se 1 (by rfl) ⟨8342594, by rfl⟩ : syracuseStep 11123459 = 16685189) B16685189
theorem B2743145 : Blo 1827615 2743145 := bstep (se 2 (by rfl) ⟨1028679, by rfl⟩ : syracuseStep 2743145 = 2057359) B2057359
theorem B4627307 : Blo 1827615 4627307 := bstep (se 1 (by rfl) ⟨3470480, by rfl⟩ : syracuseStep 4627307 = 6940961) B6940961
theorem B3087247 : Blo 1827615 3087247 := bstep (se 1 (by rfl) ⟨2315435, by rfl⟩ : syracuseStep 3087247 = 4630871) B4630871
theorem B3472303 : Blo 1827615 3472303 := bstep (se 1 (by rfl) ⟨2604227, by rfl⟩ : syracuseStep 3472303 = 5208455) B5208455
theorem B2743223 : Blo 1827615 2743223 := bstep (se 1 (by rfl) ⟨2057417, by rfl⟩ : syracuseStep 2743223 = 4114835) B4114835
theorem B2743259 : Blo 1827615 2743259 := bstep (se 1 (by rfl) ⟨2057444, by rfl⟩ : syracuseStep 2743259 = 4114889) B4114889
theorem B12688427 : Blo 1827615 12688427 := bstep (se 1 (by rfl) ⟨9516320, by rfl⟩ : syracuseStep 12688427 = 19032641) B19032641
theorem B3472463 : Blo 1827615 3472463 := bstep (se 1 (by rfl) ⟨2604347, by rfl⟩ : syracuseStep 3472463 = 5208695) B5208695
theorem B2743727 : Blo 1827615 2743727 := bstep (se 1 (by rfl) ⟨2057795, by rfl⟩ : syracuseStep 2743727 = 4115591) B4115591
theorem B9027059 : Blo 1827615 9027059 := bstep (se 1 (by rfl) ⟨6770294, by rfl⟩ : syracuseStep 9027059 = 13540589) B13540589
theorem B4627955 : Blo 1827615 4627955 := bstep (se 1 (by rfl) ⟨3470966, by rfl⟩ : syracuseStep 4627955 = 6941933) B6941933
theorem B2743817 : Blo 1827615 2743817 := bstep (se 2 (by rfl) ⟨1028931, by rfl⟩ : syracuseStep 2743817 = 2057863) B2057863
theorem B6946337 : Blo 1827615 6946337 := bstep (se 2 (by rfl) ⟨2604876, by rfl⟩ : syracuseStep 6946337 = 5209753) B5209753
theorem B2743847 : Blo 1827615 2743847 := bstep (se 1 (by rfl) ⟨2057885, by rfl⟩ : syracuseStep 2743847 = 4115771) B4115771
theorem B5209697 : Blo 1827615 5209697 := bstep (se 2 (by rfl) ⟨1953636, by rfl⟩ : syracuseStep 5209697 = 3907273) B3907273
theorem B2743931 : Blo 1827615 2743931 := bstep (se 1 (by rfl) ⟨2057948, by rfl⟩ : syracuseStep 2743931 = 4115897) B4115897
theorem B6168203 : Blo 1827615 6168203 := bstep (se 1 (by rfl) ⟨4626152, by rfl⟩ : syracuseStep 6168203 = 9252305) B9252305
theorem B6946519 : Blo 1827615 6946519 := bstep (se 1 (by rfl) ⟨5209889, by rfl⟩ : syracuseStep 6946519 = 10419779) B10419779
theorem B19029725 : Blo 1827615 19029725 := bstep (se 3 (by rfl) ⟨3568073, by rfl⟩ : syracuseStep 19029725 = 7136147) B7136147
theorem B2744057 : Blo 1827615 2744057 := bstep (se 2 (by rfl) ⟨1029021, by rfl⟩ : syracuseStep 2744057 = 2058043) B2058043
theorem B10419961 : Blo 1827615 10419961 := bstep (se 2 (by rfl) ⟨3907485, by rfl⟩ : syracuseStep 10419961 = 7814971) B7814971
theorem B7036739 : Blo 1827615 7036739 := bstep (se 1 (by rfl) ⟨5277554, by rfl⟩ : syracuseStep 7036739 = 10555109) B10555109
theorem B2744159 : Blo 1827615 2744159 := bstep (se 1 (by rfl) ⟨2058119, by rfl⟩ : syracuseStep 2744159 = 4116239) B4116239
theorem B2744171 : Blo 1827615 2744171 := bstep (se 1 (by rfl) ⟨2058128, by rfl⟩ : syracuseStep 2744171 = 4116257) B4116257
theorem B3907435 : Blo 1827615 3907435 := bstep (se 1 (by rfl) ⟨2930576, by rfl⟩ : syracuseStep 3907435 = 5861153) B5861153
theorem B22232951 : Blo 1827615 22232951 := bstep (se 1 (by rfl) ⟨16674713, by rfl⟩ : syracuseStep 22232951 = 33349427) B33349427
theorem B3956663 : Blo 1827615 3956663 := bstep (se 1 (by rfl) ⟨2967497, by rfl⟩ : syracuseStep 3956663 = 5934995) B5934995
theorem B15613883 : Blo 1827615 15613883 := bstep (se 1 (by rfl) ⟨11710412, by rfl⟩ : syracuseStep 15613883 = 23420825) B23420825
theorem B4112315 : Blo 1827615 4112315 := bstep (se 1 (by rfl) ⟨3084236, by rfl⟩ : syracuseStep 4112315 = 6168473) B6168473
theorem B4628411 : Blo 1827615 4628411 := bstep (se 1 (by rfl) ⟨3471308, by rfl⟩ : syracuseStep 4628411 = 6942617) B6942617
theorem B14270483 : Blo 1827615 14270483 := bstep (se 1 (by rfl) ⟨10702862, by rfl⟩ : syracuseStep 14270483 = 21405725) B21405725
theorem B6168635 : Blo 1827615 6168635 := bstep (se 1 (by rfl) ⟨4626476, by rfl⟩ : syracuseStep 6168635 = 9252953) B9252953
theorem B14827673 : Blo 1827615 14827673 := bstep (se 2 (by rfl) ⟨5560377, by rfl⟩ : syracuseStep 14827673 = 11120755) B11120755
theorem B15843539 : Blo 1827615 15843539 := bstep (se 1 (by rfl) ⟨11882654, by rfl⟩ : syracuseStep 15843539 = 23765309) B23765309
theorem B6168905 : Blo 1827615 6168905 := bstep (se 2 (by rfl) ⟨2313339, by rfl⟩ : syracuseStep 6168905 = 4626679) B4626679
theorem B5562715 : Blo 1827615 5562715 := bstep (se 1 (by rfl) ⟨4172036, by rfl⟩ : syracuseStep 5562715 = 8344073) B8344073
theorem B4112747 : Blo 1827615 4112747 := bstep (se 1 (by rfl) ⟨3084560, by rfl⟩ : syracuseStep 4112747 = 6169121) B6169121
theorem B17858981 : Blo 1827615 17858981 := bstep (se 4 (by rfl) ⟨1674279, by rfl⟩ : syracuseStep 17858981 = 3348559) B3348559
theorem B10412489 : Blo 1827615 10412489 := bstep (se 2 (by rfl) ⟨3904683, by rfl⟩ : syracuseStep 10412489 = 7809367) B7809367
theorem B4628947 : Blo 1827615 4628947 := bstep (se 1 (by rfl) ⟨3471710, by rfl⟩ : syracuseStep 4628947 = 6943421) B6943421
theorem B4112891 : Blo 1827615 4112891 := bstep (se 1 (by rfl) ⟨3084668, by rfl⟩ : syracuseStep 4112891 = 6169337) B6169337
theorem B4113017 : Blo 1827615 4113017 := bstep (se 2 (by rfl) ⟨1542381, by rfl⟩ : syracuseStep 4113017 = 3084763) B3084763
theorem B4113071 : Blo 1827615 4113071 := bstep (se 1 (by rfl) ⟨3084803, by rfl⟩ : syracuseStep 4113071 = 6169607) B6169607
theorem B7807711 : Blo 1827615 7807711 := bstep (se 1 (by rfl) ⟨5855783, by rfl⟩ : syracuseStep 7807711 = 11711567) B11711567
theorem B2056927 : Blo 1827615 2056927 := bstep (se 1 (by rfl) ⟨1542695, by rfl⟩ : syracuseStep 2056927 = 3085391) B3085391
theorem B4113143 : Blo 1827615 4113143 := bstep (se 1 (by rfl) ⟨3084857, by rfl⟩ : syracuseStep 4113143 = 6169715) B6169715
theorem B1827631 : Blo 1827615 1827631 := bstep (se 1 (by rfl) ⟨1370723, by rfl⟩ : syracuseStep 1827631 = 2741447) B2741447
theorem B1827739 : Blo 1827615 1827739 := bstep (se 1 (by rfl) ⟨1370804, by rfl⟩ : syracuseStep 1827739 = 2741609) B2741609
theorem B4113323 : Blo 1827615 4113323 := bstep (se 1 (by rfl) ⟨3084992, by rfl⟩ : syracuseStep 4113323 = 6169985) B6169985
theorem B1827791 : Blo 1827615 1827791 := bstep (se 1 (by rfl) ⟨1370843, by rfl⟩ : syracuseStep 1827791 = 2741687) B2741687
theorem B1827815 : Blo 1827615 1827815 := bstep (se 1 (by rfl) ⟨1370861, by rfl⟩ : syracuseStep 1827815 = 2741723) B2741723
theorem B3957751 : Blo 1827615 3957751 := bstep (se 1 (by rfl) ⟨2968313, by rfl⟩ : syracuseStep 3957751 = 5936627) B5936627
theorem B9257975 : Blo 1827615 9257975 := bstep (se 1 (by rfl) ⟨6943481, by rfl⟩ : syracuseStep 9257975 = 13886963) B13886963
theorem B4940939 : Blo 1827615 4940939 := bstep (se 1 (by rfl) ⟨3705704, by rfl⟩ : syracuseStep 4940939 = 7411409) B7411409
theorem B4629737 : Blo 1827615 4629737 := bstep (se 2 (by rfl) ⟨1736151, by rfl⟩ : syracuseStep 4629737 = 3472303) B3472303
theorem B1828127 : Blo 1827615 1828127 := bstep (se 1 (by rfl) ⟨1371095, by rfl⟩ : syracuseStep 1828127 = 2742191) B2742191
theorem B2057503 : Blo 1827615 2057503 := bstep (se 1 (by rfl) ⟨1543127, by rfl⟩ : syracuseStep 2057503 = 3086255) B3086255
theorem B1828187 : Blo 1827615 1828187 := bstep (se 1 (by rfl) ⟨1371140, by rfl⟩ : syracuseStep 1828187 = 2742281) B2742281
theorem B1828207 : Blo 1827615 1828207 := bstep (se 1 (by rfl) ⟨1371155, by rfl⟩ : syracuseStep 1828207 = 2742311) B2742311
theorem B4629899 : Blo 1827615 4629899 := bstep (se 1 (by rfl) ⟨3472424, by rfl⟩ : syracuseStep 4629899 = 6944849) B6944849
theorem B1828263 : Blo 1827615 1828263 := bstep (se 1 (by rfl) ⟨1371197, by rfl⟩ : syracuseStep 1828263 = 2742395) B2742395
theorem B4113863 : Blo 1827615 4113863 := bstep (se 1 (by rfl) ⟨3085397, by rfl⟩ : syracuseStep 4113863 = 6170795) B6170795
theorem B1828347 : Blo 1827615 1828347 := bstep (se 1 (by rfl) ⟨1371260, by rfl⟩ : syracuseStep 1828347 = 2742521) B2742521
theorem B1828415 : Blo 1827615 1828415 := bstep (se 1 (by rfl) ⟨1371311, by rfl⟩ : syracuseStep 1828415 = 2742623) B2742623
theorem B2057791 : Blo 1827615 2057791 := bstep (se 1 (by rfl) ⟨1543343, by rfl⟩ : syracuseStep 2057791 = 3086687) B3086687
theorem B1828423 : Blo 1827615 1828423 := bstep (se 1 (by rfl) ⟨1371317, by rfl⟩ : syracuseStep 1828423 = 2742635) B2742635
theorem B7808669 : Blo 1827615 7808669 := bstep (se 3 (by rfl) ⟨1464125, by rfl⟩ : syracuseStep 7808669 = 2928251) B2928251
theorem B4392635 : Blo 1827615 4392635 := bstep (se 1 (by rfl) ⟨3294476, by rfl⟩ : syracuseStep 4392635 = 6588953) B6588953
theorem B1828575 : Blo 1827615 1828575 := bstep (se 1 (by rfl) ⟨1371431, by rfl⟩ : syracuseStep 1828575 = 2742863) B2742863
theorem B4114223 : Blo 1827615 4114223 := bstep (se 1 (by rfl) ⟨3085667, by rfl⟩ : syracuseStep 4114223 = 6171335) B6171335
theorem B1828655 : Blo 1827615 1828655 := bstep (se 1 (by rfl) ⟨1371491, by rfl⟩ : syracuseStep 1828655 = 2742983) B2742983
theorem B7415639 : Blo 1827615 7415639 := bstep (se 1 (by rfl) ⟨5561729, by rfl⟩ : syracuseStep 7415639 = 11123459) B11123459
theorem B13879187 : Blo 1827615 13879187 := bstep (se 1 (by rfl) ⟨10409390, by rfl⟩ : syracuseStep 13879187 = 20818781) B20818781
theorem B1828763 : Blo 1827615 1828763 := bstep (se 1 (by rfl) ⟨1371572, by rfl⟩ : syracuseStep 1828763 = 2743145) B2743145
theorem B3295183 : Blo 1827615 3295183 := bstep (se 1 (by rfl) ⟨2471387, by rfl⟩ : syracuseStep 3295183 = 4942775) B4942775
theorem B1828815 : Blo 1827615 1828815 := bstep (se 1 (by rfl) ⟨1371611, by rfl⟩ : syracuseStep 1828815 = 2743223) B2743223
theorem B1828839 : Blo 1827615 1828839 := bstep (se 1 (by rfl) ⟨1371629, by rfl⟩ : syracuseStep 1828839 = 2743259) B2743259
theorem B1829151 : Blo 1827615 1829151 := bstep (se 1 (by rfl) ⟨1371863, by rfl⟩ : syracuseStep 1829151 = 2743727) B2743727
theorem B1829211 : Blo 1827615 1829211 := bstep (se 1 (by rfl) ⟨1371908, by rfl⟩ : syracuseStep 1829211 = 2743817) B2743817
theorem B4630891 : Blo 1827615 4630891 := bstep (se 1 (by rfl) ⟨3473168, by rfl⟩ : syracuseStep 4630891 = 6946337) B6946337
theorem B4114799 : Blo 1827615 4114799 := bstep (se 1 (by rfl) ⟨3086099, by rfl⟩ : syracuseStep 4114799 = 6172199) B6172199
theorem B1829231 : Blo 1827615 1829231 := bstep (se 1 (by rfl) ⟨1371923, by rfl⟩ : syracuseStep 1829231 = 2743847) B2743847
theorem B6588839 : Blo 1827615 6588839 := bstep (se 1 (by rfl) ⟨4941629, by rfl⟩ : syracuseStep 6588839 = 9883259) B9883259
theorem B1829287 : Blo 1827615 1829287 := bstep (se 1 (by rfl) ⟨1371965, by rfl⟩ : syracuseStep 1829287 = 2743931) B2743931
theorem B4114871 : Blo 1827615 4114871 := bstep (se 1 (by rfl) ⟨3086153, by rfl⟩ : syracuseStep 4114871 = 6172307) B6172307
theorem B1829371 : Blo 1827615 1829371 := bstep (se 1 (by rfl) ⟨1372028, by rfl⟩ : syracuseStep 1829371 = 2744057) B2744057
theorem B1829439 : Blo 1827615 1829439 := bstep (se 1 (by rfl) ⟨1372079, by rfl⟩ : syracuseStep 1829439 = 2744159) B2744159
theorem B4115015 : Blo 1827615 4115015 := bstep (se 1 (by rfl) ⟨3086261, by rfl⟩ : syracuseStep 4115015 = 6172523) B6172523
theorem B1829447 : Blo 1827615 1829447 := bstep (se 1 (by rfl) ⟨1372085, by rfl⟩ : syracuseStep 1829447 = 2744171) B2744171
theorem B14821967 : Blo 1827615 14821967 := bstep (se 1 (by rfl) ⟨11116475, by rfl⟩ : syracuseStep 14821967 = 22232951) B22232951
theorem B4115051 : Blo 1827615 4115051 := bstep (se 1 (by rfl) ⟨3086288, by rfl⟩ : syracuseStep 4115051 = 6172577) B6172577
theorem B4631215 : Blo 1827615 4631215 := bstep (se 1 (by rfl) ⟨3473411, by rfl⟩ : syracuseStep 4631215 = 6946823) B6946823
theorem B1829599 : Blo 1827615 1829599 := bstep (se 1 (by rfl) ⟨1372199, by rfl⟩ : syracuseStep 1829599 = 2744399) B2744399
theorem B106900355 : Blo 1827615 106900355 := bstep (se 1 (by rfl) ⟨80175266, by rfl⟩ : syracuseStep 106900355 = 160350533) B160350533
theorem B9259919 : Blo 1827615 9259919 := bstep (se 1 (by rfl) ⟨6944939, by rfl⟩ : syracuseStep 9259919 = 13889879) B13889879
theorem B4115447 : Blo 1827615 4115447 := bstep (se 1 (by rfl) ⟨3086585, by rfl⟩ : syracuseStep 4115447 = 6173171) B6173171
theorem B15035507 : Blo 1827615 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B26709193 : Blo 1827615 26709193 := bstep (se 2 (by rfl) ⟨10015947, by rfl⟩ : syracuseStep 26709193 = 20031895) B20031895
theorem B3706075 : Blo 1827615 3706075 := bstep (se 1 (by rfl) ⟨2779556, by rfl⟩ : syracuseStep 3706075 = 5559113) B5559113
theorem B4115807 : Blo 1827615 4115807 := bstep (se 1 (by rfl) ⟨3086855, by rfl⟩ : syracuseStep 4115807 = 6173711) B6173711
theorem B11873665 : Blo 1827615 11873665 := bstep (se 2 (by rfl) ⟨4452624, by rfl⟩ : syracuseStep 11873665 = 8905249) B8905249
theorem B6172091 : Blo 1827615 6172091 := bstep (se 1 (by rfl) ⟨4629068, by rfl⟩ : syracuseStep 6172091 = 9258137) B9258137
theorem B7040621 : Blo 1827615 7040621 := bstep (se 3 (by rfl) ⟨1320116, by rfl⟩ : syracuseStep 7040621 = 2640233) B2640233
theorem B9252467 : Blo 1827615 9252467 := bstep (se 1 (by rfl) ⟨6939350, by rfl⟩ : syracuseStep 9252467 = 13878701) B13878701
theorem B7515809 : Blo 1827615 7515809 := bstep (se 2 (by rfl) ⟨2818428, by rfl⟩ : syracuseStep 7515809 = 5636857) B5636857
theorem B7810769 : Blo 1827615 7810769 := bstep (se 2 (by rfl) ⟨2929038, by rfl⟩ : syracuseStep 7810769 = 5858077) B5858077
theorem B9383633 : Blo 1827615 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B4394731 : Blo 1827615 4394731 := bstep (se 1 (by rfl) ⟨3296048, by rfl⟩ : syracuseStep 4394731 = 6592097) B6592097
theorem B4116203 : Blo 1827615 4116203 := bstep (se 1 (by rfl) ⟨3087152, by rfl⟩ : syracuseStep 4116203 = 6174305) B6174305
theorem B95047499 : Blo 1827615 95047499 := bstep (se 1 (by rfl) ⟨71285624, by rfl⟩ : syracuseStep 95047499 = 142571249) B142571249
theorem B4116329 : Blo 1827615 4116329 := bstep (se 2 (by rfl) ⟨1543623, by rfl⟩ : syracuseStep 4116329 = 3087247) B3087247
theorem B8458141 : Blo 1827615 8458141 := bstep (se 3 (by rfl) ⟨1585901, by rfl⟩ : syracuseStep 8458141 = 3171803) B3171803
theorem B24072157 : Blo 1827615 24072157 := bstep (se 3 (by rfl) ⟨4513529, by rfl⟩ : syracuseStep 24072157 = 9027059) B9027059
theorem B126628019 : Blo 1827615 126628019 := bstep (se 1 (by rfl) ⟨94971014, by rfl⟩ : syracuseStep 126628019 = 189942029) B189942029
theorem B20820239 : Blo 1827615 20820239 := bstep (se 1 (by rfl) ⟨15615179, by rfl⟩ : syracuseStep 20820239 = 31230359) B31230359
theorem B3084635 : Blo 1827615 3084635 := bstep (se 1 (by rfl) ⟨2313476, by rfl⟩ : syracuseStep 3084635 = 4626953) B4626953
theorem B3084655 : Blo 1827615 3084655 := bstep (se 1 (by rfl) ⟨2313491, by rfl⟩ : syracuseStep 3084655 = 4626983) B4626983
theorem B2314747 : Blo 1827615 2314747 := bstep (se 1 (by rfl) ⟨1736060, by rfl⟩ : syracuseStep 2314747 = 3472121) B3472121
theorem B19018289 : Blo 1827615 19018289 := bstep (se 2 (by rfl) ⟨7131858, by rfl⟩ : syracuseStep 19018289 = 14263717) B14263717
theorem B3084871 : Blo 1827615 3084871 := bstep (se 1 (by rfl) ⟨2313653, by rfl⟩ : syracuseStep 3084871 = 4627307) B4627307
theorem B2929225 : Blo 1827615 2929225 := bstep (se 2 (by rfl) ⟨1098459, by rfl⟩ : syracuseStep 2929225 = 2196919) B2196919
theorem B8458951 : Blo 1827615 8458951 := bstep (se 1 (by rfl) ⟨6344213, by rfl⟩ : syracuseStep 8458951 = 12688427) B12688427
theorem B10416863 : Blo 1827615 10416863 := bstep (se 1 (by rfl) ⟨7812647, by rfl⟩ : syracuseStep 10416863 = 15625295) B15625295
theorem B2314975 : Blo 1827615 2314975 := bstep (se 1 (by rfl) ⟨1736231, by rfl⟩ : syracuseStep 2314975 = 3472463) B3472463
theorem B9262025 : Blo 1827615 9262025 := bstep (se 2 (by rfl) ⟨3473259, by rfl⟩ : syracuseStep 9262025 = 6946519) B6946519
theorem B3085303 : Blo 1827615 3085303 := bstep (se 1 (by rfl) ⟨2313977, by rfl⟩ : syracuseStep 3085303 = 4627955) B4627955
theorem B59307065 : Blo 1827615 59307065 := bstep (se 2 (by rfl) ⟨22240149, by rfl⟩ : syracuseStep 59307065 = 44480299) B44480299
theorem B8787001 : Blo 1827615 8787001 := bstep (se 2 (by rfl) ⟨3295125, by rfl⟩ : syracuseStep 8787001 = 6590251) B6590251
theorem B12686483 : Blo 1827615 12686483 := bstep (se 1 (by rfl) ⟨9514862, by rfl⟩ : syracuseStep 12686483 = 19029725) B19029725
theorem B9254087 : Blo 1827615 9254087 := bstep (se 1 (by rfl) ⟨6940565, by rfl⟩ : syracuseStep 9254087 = 13881131) B13881131
theorem B4691159 : Blo 1827615 4691159 := bstep (se 1 (by rfl) ⟨3518369, by rfl⟩ : syracuseStep 4691159 = 7036739) B7036739
theorem B6591721 : Blo 1827615 6591721 := bstep (se 2 (by rfl) ⟨2471895, by rfl⟩ : syracuseStep 6591721 = 4943791) B4943791
theorem B10409255 : Blo 1827615 10409255 := bstep (se 1 (by rfl) ⟨7806941, by rfl⟩ : syracuseStep 10409255 = 15613883) B15613883
theorem B2741543 : Blo 1827615 2741543 := bstep (se 1 (by rfl) ⟨2056157, by rfl⟩ : syracuseStep 2741543 = 4112315) B4112315
theorem B3085607 : Blo 1827615 3085607 := bstep (se 1 (by rfl) ⟨2314205, by rfl⟩ : syracuseStep 3085607 = 4628411) B4628411
theorem B9254249 : Blo 1827615 9254249 := bstep (se 2 (by rfl) ⟨3470343, by rfl⟩ : syracuseStep 9254249 = 6940687) B6940687
theorem B1979759 : Blo 1827615 1979759 := bstep (se 1 (by rfl) ⟨1484819, by rfl⟩ : syracuseStep 1979759 = 2969639) B2969639
theorem B2741627 : Blo 1827615 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B2741753 : Blo 1827615 2741753 := bstep (se 2 (by rfl) ⟨1028157, by rfl⟩ : syracuseStep 2741753 = 2056315) B2056315
theorem B2741855 : Blo 1827615 2741855 := bstep (se 1 (by rfl) ⟨2056391, by rfl⟩ : syracuseStep 2741855 = 4112783) B4112783
theorem B231478885 : Blo 1827615 231478885 := bstep (se 4 (by rfl) ⟨21701145, by rfl⟩ : syracuseStep 231478885 = 43402291) B43402291
theorem B71284369 : Blo 1827615 71284369 := bstep (se 2 (by rfl) ⟨26731638, by rfl⟩ : syracuseStep 71284369 = 53463277) B53463277
theorem B3086059 : Blo 1827615 3086059 := bstep (se 1 (by rfl) ⟨2314544, by rfl⟩ : syracuseStep 3086059 = 4629089) B4629089
theorem B2742071 : Blo 1827615 2742071 := bstep (se 1 (by rfl) ⟨2056553, by rfl⟩ : syracuseStep 2742071 = 4113107) B4113107
theorem B4626305 : Blo 1827615 4626305 := bstep (se 2 (by rfl) ⟨1734864, by rfl⟩ : syracuseStep 4626305 = 3469729) B3469729
theorem B2742377 : Blo 1827615 2742377 := bstep (se 2 (by rfl) ⟨1028391, by rfl⟩ : syracuseStep 2742377 = 2056783) B2056783
theorem B7813367 : Blo 1827615 7813367 := bstep (se 1 (by rfl) ⟨5860025, by rfl⟩ : syracuseStep 7813367 = 11720051) B11720051
theorem B6019337 : Blo 1827615 6019337 := bstep (se 2 (by rfl) ⟨2257251, by rfl⟩ : syracuseStep 6019337 = 4514503) B4514503
theorem B2742695 : Blo 1827615 2742695 := bstep (se 1 (by rfl) ⟨2057021, by rfl⟩ : syracuseStep 2742695 = 4114043) B4114043
theorem B3905975 : Blo 1827615 3905975 := bstep (se 1 (by rfl) ⟨2929481, by rfl⟩ : syracuseStep 3905975 = 5858963) B5858963
theorem B2742779 : Blo 1827615 2742779 := bstep (se 1 (by rfl) ⟨2057084, by rfl⟩ : syracuseStep 2742779 = 4114169) B4114169
theorem B15620647 : Blo 1827615 15620647 := bstep (se 1 (by rfl) ⟨11715485, by rfl⟩ : syracuseStep 15620647 = 23430971) B23430971
theorem B31660607 : Blo 1827615 31660607 := bstep (se 1 (by rfl) ⟨23745455, by rfl⟩ : syracuseStep 31660607 = 47490911) B47490911
theorem B3906119 : Blo 1827615 3906119 := bstep (se 1 (by rfl) ⟨2929589, by rfl⟩ : syracuseStep 3906119 = 5859179) B5859179
theorem B2742905 : Blo 1827615 2742905 := bstep (se 2 (by rfl) ⟨1028589, by rfl⟩ : syracuseStep 2742905 = 2057179) B2057179
theorem B4627115 : Blo 1827615 4627115 := bstep (se 1 (by rfl) ⟨3470336, by rfl⟩ : syracuseStep 4627115 = 6940673) B6940673
theorem B2742959 : Blo 1827615 2742959 := bstep (se 1 (by rfl) ⟨2057219, by rfl⟩ : syracuseStep 2742959 = 4114439) B4114439
theorem B3087031 : Blo 1827615 3087031 := bstep (se 1 (by rfl) ⟨2315273, by rfl⟩ : syracuseStep 3087031 = 4630547) B4630547
theorem B2743007 : Blo 1827615 2743007 := bstep (se 1 (by rfl) ⟨2057255, by rfl⟩ : syracuseStep 2743007 = 4114511) B4114511
theorem B26368841 : Blo 1827615 26368841 := bstep (se 2 (by rfl) ⟨9888315, by rfl⟩ : syracuseStep 26368841 = 19776631) B19776631
theorem B2743271 : Blo 1827615 2743271 := bstep (se 1 (by rfl) ⟨2057453, by rfl⟩ : syracuseStep 2743271 = 4114907) B4114907
theorem B3087335 : Blo 1827615 3087335 := bstep (se 1 (by rfl) ⟨2315501, by rfl⟩ : syracuseStep 3087335 = 4631003) B4631003
theorem B2743529 : Blo 1827615 2743529 := bstep (se 2 (by rfl) ⟨1028823, by rfl⟩ : syracuseStep 2743529 = 2057647) B2057647
theorem B2743583 : Blo 1827615 2743583 := bstep (se 1 (by rfl) ⟨2057687, by rfl⟩ : syracuseStep 2743583 = 4115375) B4115375
theorem B7413059 : Blo 1827615 7413059 := bstep (se 1 (by rfl) ⟨5559794, by rfl⟩ : syracuseStep 7413059 = 11119589) B11119589
theorem B2743751 : Blo 1827615 2743751 := bstep (se 1 (by rfl) ⟨2057813, by rfl⟩ : syracuseStep 2743751 = 4115627) B4115627
theorem B4627975 : Blo 1827615 4627975 := bstep (se 1 (by rfl) ⟨3470981, by rfl⟩ : syracuseStep 4627975 = 6941963) B6941963
theorem B13893281 : Blo 1827615 13893281 := bstep (se 2 (by rfl) ⟨5209980, by rfl⟩ : syracuseStep 13893281 = 10419961) B10419961
theorem B3473131 : Blo 1827615 3473131 := bstep (se 1 (by rfl) ⟨2604848, by rfl⟩ : syracuseStep 3473131 = 5209697) B5209697
theorem B4112135 : Blo 1827615 4112135 := bstep (se 1 (by rfl) ⟨3084101, by rfl⟩ : syracuseStep 4112135 = 6168203) B6168203
theorem B2744105 : Blo 1827615 2744105 := bstep (se 2 (by rfl) ⟨1029039, by rfl⟩ : syracuseStep 2744105 = 2058079) B2058079
theorem B2744111 : Blo 1827615 2744111 := bstep (se 1 (by rfl) ⟨2058083, by rfl⟩ : syracuseStep 2744111 = 4116167) B4116167
theorem B4628279 : Blo 1827615 4628279 := bstep (se 1 (by rfl) ⟨3471209, by rfl⟩ : syracuseStep 4628279 = 6942419) B6942419
theorem B5209913 : Blo 1827615 5209913 := bstep (se 2 (by rfl) ⟨1953717, by rfl⟩ : syracuseStep 5209913 = 3907435) B3907435
theorem B7413565 : Blo 1827615 7413565 := bstep (se 3 (by rfl) ⟨1390043, by rfl⟩ : syracuseStep 7413565 = 2780087) B2780087
theorem B15621983 : Blo 1827615 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B7815041 : Blo 1827615 7815041 := bstep (se 2 (by rfl) ⟨2930640, by rfl⟩ : syracuseStep 7815041 = 5861281) B5861281
theorem B5857181 : Blo 1827615 5857181 := bstep (se 3 (by rfl) ⟨1098221, by rfl⟩ : syracuseStep 5857181 = 2196443) B2196443
theorem B2637775 : Blo 1827615 2637775 := bstep (se 1 (by rfl) ⟨1978331, by rfl⟩ : syracuseStep 2637775 = 3956663) B3956663
theorem B4112423 : Blo 1827615 4112423 := bstep (se 1 (by rfl) ⟨3084317, by rfl⟩ : syracuseStep 4112423 = 6168635) B6168635
theorem B84418679 : Blo 1827615 84418679 := bstep (se 1 (by rfl) ⟨63314009, by rfl⟩ : syracuseStep 84418679 = 126628019) B126628019
theorem B4112603 : Blo 1827615 4112603 := bstep (se 1 (by rfl) ⟨3084452, by rfl⟩ : syracuseStep 4112603 = 6168905) B6168905
theorem B2056423 : Blo 1827615 2056423 := bstep (se 1 (by rfl) ⟨1542317, by rfl⟩ : syracuseStep 2056423 = 3084635) B3084635
theorem B4112873 : Blo 1827615 4112873 := bstep (se 2 (by rfl) ⟨1542327, by rfl⟩ : syracuseStep 4112873 = 3084655) B3084655
theorem B3293959 : Blo 1827615 3293959 := bstep (se 1 (by rfl) ⟨2470469, by rfl⟩ : syracuseStep 3293959 = 4940939) B4940939
theorem B4113161 : Blo 1827615 4113161 := bstep (se 2 (by rfl) ⟨1542435, by rfl⟩ : syracuseStep 4113161 = 3084871) B3084871
theorem B6169391 : Blo 1827615 6169391 := bstep (se 1 (by rfl) ⟨4627043, by rfl⟩ : syracuseStep 6169391 = 9254087) B9254087
theorem B19768157 : Blo 1827615 19768157 := bstep (se 3 (by rfl) ⟨3706529, by rfl⟩ : syracuseStep 19768157 = 7413059) B7413059
theorem B6939503 : Blo 1827615 6939503 := bstep (se 1 (by rfl) ⟨5204627, by rfl⟩ : syracuseStep 6939503 = 10409255) B10409255
theorem B1827695 : Blo 1827615 1827695 := bstep (se 1 (by rfl) ⟨1370771, by rfl⟩ : syracuseStep 1827695 = 2741543) B2741543
theorem B2057071 : Blo 1827615 2057071 := bstep (se 1 (by rfl) ⟨1542803, by rfl⟩ : syracuseStep 2057071 = 3085607) B3085607
theorem B6169499 : Blo 1827615 6169499 := bstep (se 1 (by rfl) ⟨4627124, by rfl⟩ : syracuseStep 6169499 = 9254249) B9254249
theorem B1827751 : Blo 1827615 1827751 := bstep (se 1 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 1827751 = 2741627) B2741627
theorem B1827835 : Blo 1827615 1827835 := bstep (se 1 (by rfl) ⟨1370876, by rfl⟩ : syracuseStep 1827835 = 2741753) B2741753
theorem B1827903 : Blo 1827615 1827903 := bstep (se 1 (by rfl) ⟨1370927, by rfl⟩ : syracuseStep 1827903 = 2741855) B2741855
theorem B1828047 : Blo 1827615 1828047 := bstep (se 1 (by rfl) ⟨1371035, by rfl⟩ : syracuseStep 1828047 = 2742071) B2742071
theorem B4113737 : Blo 1827615 4113737 := bstep (se 2 (by rfl) ⟨1542651, by rfl⟩ : syracuseStep 4113737 = 3085303) B3085303
theorem B5277001 : Blo 1827615 5277001 := bstep (se 2 (by rfl) ⟨1978875, by rfl⟩ : syracuseStep 5277001 = 3957751) B3957751
theorem B1828251 : Blo 1827615 1828251 := bstep (se 1 (by rfl) ⟨1371188, by rfl⟩ : syracuseStep 1828251 = 2742377) B2742377
theorem B11716001 : Blo 1827615 11716001 := bstep (se 2 (by rfl) ⟨4393500, by rfl⟩ : syracuseStep 11716001 = 8787001) B8787001
theorem B35612257 : Blo 1827615 35612257 := bstep (se 2 (by rfl) ⟨13354596, by rfl⟩ : syracuseStep 35612257 = 26709193) B26709193
theorem B4392559 : Blo 1827615 4392559 := bstep (se 1 (by rfl) ⟨3294419, by rfl⟩ : syracuseStep 4392559 = 6588839) B6588839
theorem B1828463 : Blo 1827615 1828463 := bstep (se 1 (by rfl) ⟨1371347, by rfl⟩ : syracuseStep 1828463 = 2742695) B2742695
theorem B4941433 : Blo 1827615 4941433 := bstep (se 2 (by rfl) ⟨1853037, by rfl⟩ : syracuseStep 4941433 = 3706075) B3706075
theorem B1828519 : Blo 1827615 1828519 := bstep (se 1 (by rfl) ⟨1371389, by rfl⟩ : syracuseStep 1828519 = 2742779) B2742779
theorem B9881311 : Blo 1827615 9881311 := bstep (se 1 (by rfl) ⟨7410983, by rfl⟩ : syracuseStep 9881311 = 14821967) B14821967
theorem B1828603 : Blo 1827615 1828603 := bstep (se 1 (by rfl) ⟨1371452, by rfl⟩ : syracuseStep 1828603 = 2742905) B2742905
theorem B1828639 : Blo 1827615 1828639 := bstep (se 1 (by rfl) ⟨1371479, by rfl⟩ : syracuseStep 1828639 = 2742959) B2742959
theorem B1828671 : Blo 1827615 1828671 := bstep (se 1 (by rfl) ⟨1371503, by rfl⟩ : syracuseStep 1828671 = 2743007) B2743007
theorem B1828847 : Blo 1827615 1828847 := bstep (se 1 (by rfl) ⟨1371635, by rfl⟩ : syracuseStep 1828847 = 2743271) B2743271
theorem B2058223 : Blo 1827615 2058223 := bstep (se 1 (by rfl) ⟨1543667, by rfl⟩ : syracuseStep 2058223 = 3087335) B3087335
theorem B6170633 : Blo 1827615 6170633 := bstep (se 2 (by rfl) ⟨2313987, by rfl⟩ : syracuseStep 6170633 = 4627975) B4627975
theorem B1829019 : Blo 1827615 1829019 := bstep (se 1 (by rfl) ⟨1371764, by rfl⟩ : syracuseStep 1829019 = 2743529) B2743529
theorem B1829055 : Blo 1827615 1829055 := bstep (se 1 (by rfl) ⟨1371791, by rfl⟩ : syracuseStep 1829055 = 2743583) B2743583
theorem B95045825 : Blo 1827615 95045825 := bstep (se 2 (by rfl) ⟨35642184, by rfl⟩ : syracuseStep 95045825 = 71284369) B71284369
theorem B4114727 : Blo 1827615 4114727 := bstep (se 1 (by rfl) ⟨3086045, by rfl⟩ : syracuseStep 4114727 = 6172091) B6172091
theorem B1829167 : Blo 1827615 1829167 := bstep (se 1 (by rfl) ⟨1371875, by rfl⟩ : syracuseStep 1829167 = 2743751) B2743751
theorem B4114745 : Blo 1827615 4114745 := bstep (se 2 (by rfl) ⟨1543029, by rfl⟩ : syracuseStep 4114745 = 3086059) B3086059
theorem B5859641 : Blo 1827615 5859641 := bstep (se 2 (by rfl) ⟨2197365, by rfl⟩ : syracuseStep 5859641 = 4394731) B4394731
theorem B4630841 : Blo 1827615 4630841 := bstep (se 2 (by rfl) ⟨1736565, by rfl⟩ : syracuseStep 4630841 = 3473131) B3473131
theorem B285067613 : Blo 1827615 285067613 := bstep (se 3 (by rfl) ⟨53450177, by rfl⟩ : syracuseStep 285067613 = 106900355) B106900355
theorem B1829403 : Blo 1827615 1829403 := bstep (se 1 (by rfl) ⟨1372052, by rfl⟩ : syracuseStep 1829403 = 2744105) B2744105
theorem B1829407 : Blo 1827615 1829407 := bstep (se 1 (by rfl) ⟨1372055, by rfl⟩ : syracuseStep 1829407 = 2744111) B2744111
theorem B10414655 : Blo 1827615 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B3517033 : Blo 1827615 3517033 := bstep (se 2 (by rfl) ⟨1318887, by rfl⟩ : syracuseStep 3517033 = 2637775) B2637775
theorem B4393577 : Blo 1827615 4393577 := bstep (se 2 (by rfl) ⟨1647591, by rfl⟩ : syracuseStep 4393577 = 3295183) B3295183
theorem B9513655 : Blo 1827615 9513655 := bstep (se 1 (by rfl) ⟨7135241, by rfl⟩ : syracuseStep 9513655 = 14270483) B14270483
theorem B13880159 : Blo 1827615 13880159 := bstep (se 1 (by rfl) ⟨10410119, by rfl⟩ : syracuseStep 13880159 = 20820239) B20820239
theorem B11905987 : Blo 1827615 11905987 := bstep (se 1 (by rfl) ⟨8929490, by rfl⟩ : syracuseStep 11905987 = 17858981) B17858981
theorem B6941659 : Blo 1827615 6941659 := bstep (se 1 (by rfl) ⟨5206244, by rfl⟩ : syracuseStep 6941659 = 10412489) B10412489
theorem B7416953 : Blo 1827615 7416953 := bstep (se 2 (by rfl) ⟨2781357, by rfl⟩ : syracuseStep 7416953 = 5562715) B5562715
theorem B42249437 : Blo 1827615 42249437 := bstep (se 3 (by rfl) ⟨7921769, by rfl⟩ : syracuseStep 42249437 = 15843539) B15843539
theorem B6171929 : Blo 1827615 6171929 := bstep (se 2 (by rfl) ⟨2314473, by rfl⟩ : syracuseStep 6171929 = 4628947) B4628947
theorem B6171983 : Blo 1827615 6171983 := bstep (se 1 (by rfl) ⟨4628987, by rfl⟩ : syracuseStep 6171983 = 9257975) B9257975
theorem B39538043 : Blo 1827615 39538043 := bstep (se 1 (by rfl) ⟨29653532, by rfl⟩ : syracuseStep 39538043 = 59307065) B59307065
theorem B20827529 : Blo 1827615 20827529 := bstep (se 2 (by rfl) ⟨7810323, by rfl⟩ : syracuseStep 20827529 = 15620647) B15620647
theorem B4116041 : Blo 1827615 4116041 := bstep (se 2 (by rfl) ⟨1543515, by rfl⟩ : syracuseStep 4116041 = 3087031) B3087031
theorem B5279357 : Blo 1827615 5279357 := bstep (se 3 (by rfl) ⟨989879, by rfl⟩ : syracuseStep 5279357 = 1979759) B1979759
theorem B5205779 : Blo 1827615 5205779 := bstep (se 1 (by rfl) ⟨3904334, by rfl⟩ : syracuseStep 5205779 = 7808669) B7808669
theorem B4943759 : Blo 1827615 4943759 := bstep (se 1 (by rfl) ⟨3707819, by rfl⟩ : syracuseStep 4943759 = 7415639) B7415639
theorem B3084203 : Blo 1827615 3084203 := bstep (se 1 (by rfl) ⟨2313152, by rfl⟩ : syracuseStep 3084203 = 4626305) B4626305
theorem B9252791 : Blo 1827615 9252791 := bstep (se 1 (by rfl) ⟨6939593, by rfl⟩ : syracuseStep 9252791 = 13879187) B13879187
theorem B21107071 : Blo 1827615 21107071 := bstep (se 1 (by rfl) ⟨15830303, by rfl⟩ : syracuseStep 21107071 = 31660607) B31660607
theorem B3084743 : Blo 1827615 3084743 := bstep (se 1 (by rfl) ⟨2313557, by rfl⟩ : syracuseStep 3084743 = 4627115) B4627115
theorem B15831553 : Blo 1827615 15831553 := bstep (se 2 (by rfl) ⟨5936832, by rfl⟩ : syracuseStep 15831553 = 11873665) B11873665
theorem B6173279 : Blo 1827615 6173279 := bstep (se 1 (by rfl) ⟨4629959, by rfl⟩ : syracuseStep 6173279 = 9259919) B9259919
theorem B10023671 : Blo 1827615 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B308638513 : Blo 1827615 308638513 := bstep (se 2 (by rfl) ⟨115739442, by rfl⟩ : syracuseStep 308638513 = 231478885) B231478885
theorem B9884753 : Blo 1827615 9884753 := bstep (se 2 (by rfl) ⟨3706782, by rfl⟩ : syracuseStep 9884753 = 7413565) B7413565
theorem B5010539 : Blo 1827615 5010539 := bstep (se 1 (by rfl) ⟨3757904, by rfl⟩ : syracuseStep 5010539 = 7515809) B7515809
theorem B9262187 : Blo 1827615 9262187 := bstep (se 1 (by rfl) ⟨6946640, by rfl⟩ : syracuseStep 9262187 = 13893281) B13893281
theorem B5207179 : Blo 1827615 5207179 := bstep (se 1 (by rfl) ⟨3905384, by rfl⟩ : syracuseStep 5207179 = 7810769) B7810769
theorem B6255755 : Blo 1827615 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B2741423 : Blo 1827615 2741423 := bstep (se 1 (by rfl) ⟨2056067, by rfl⟩ : syracuseStep 2741423 = 4112135) B4112135
theorem B3085519 : Blo 1827615 3085519 := bstep (se 1 (by rfl) ⟨2314139, by rfl⟩ : syracuseStep 3085519 = 4628279) B4628279
theorem B11277521 : Blo 1827615 11277521 := bstep (se 2 (by rfl) ⟨4229070, by rfl⟩ : syracuseStep 11277521 = 8458141) B8458141
theorem B3904787 : Blo 1827615 3904787 := bstep (se 1 (by rfl) ⟨2928590, by rfl⟩ : syracuseStep 3904787 = 5857181) B5857181
theorem B9885115 : Blo 1827615 9885115 := bstep (se 1 (by rfl) ⟨7413836, by rfl⟩ : syracuseStep 9885115 = 14827673) B14827673
theorem B2741831 : Blo 1827615 2741831 := bstep (se 1 (by rfl) ⟨2056373, by rfl⟩ : syracuseStep 2741831 = 4112747) B4112747
theorem B2741927 : Blo 1827615 2741927 := bstep (se 1 (by rfl) ⟨2056445, by rfl⟩ : syracuseStep 2741927 = 4112891) B4112891
theorem B12678859 : Blo 1827615 12678859 := bstep (se 1 (by rfl) ⟨9509144, by rfl⟩ : syracuseStep 12678859 = 19018289) B19018289
theorem B33830621 : Blo 1827615 33830621 := bstep (se 3 (by rfl) ⟨6343241, by rfl⟩ : syracuseStep 33830621 = 12686483) B12686483
theorem B2742011 : Blo 1827615 2742011 := bstep (se 1 (by rfl) ⟨2056508, by rfl⟩ : syracuseStep 2742011 = 4113017) B4113017
theorem B2742047 : Blo 1827615 2742047 := bstep (se 1 (by rfl) ⟨2056535, by rfl⟩ : syracuseStep 2742047 = 4113071) B4113071
theorem B6174521 : Blo 1827615 6174521 := bstep (se 2 (by rfl) ⟨2315445, by rfl⟩ : syracuseStep 6174521 = 4630891) B4630891
theorem B6944575 : Blo 1827615 6944575 := bstep (se 1 (by rfl) ⟨5208431, by rfl⟩ : syracuseStep 6944575 = 10416863) B10416863
theorem B2742095 : Blo 1827615 2742095 := bstep (se 1 (by rfl) ⟨2056571, by rfl⟩ : syracuseStep 2742095 = 4113143) B4113143
theorem B2742215 : Blo 1827615 2742215 := bstep (se 1 (by rfl) ⟨2056661, by rfl⟩ : syracuseStep 2742215 = 4113323) B4113323
theorem B6174683 : Blo 1827615 6174683 := bstep (se 1 (by rfl) ⟨4631012, by rfl⟩ : syracuseStep 6174683 = 9262025) B9262025
theorem B3086329 : Blo 1827615 3086329 := bstep (se 2 (by rfl) ⟨1157373, by rfl⟩ : syracuseStep 3086329 = 2314747) B2314747
theorem B3905633 : Blo 1827615 3905633 := bstep (se 2 (by rfl) ⟨1464612, by rfl⟩ : syracuseStep 3905633 = 2929225) B2929225
theorem B3127439 : Blo 1827615 3127439 := bstep (se 1 (by rfl) ⟨2345579, by rfl⟩ : syracuseStep 3127439 = 4691159) B4691159
theorem B3086491 : Blo 1827615 3086491 := bstep (se 1 (by rfl) ⟨2314868, by rfl⟩ : syracuseStep 3086491 = 4629737) B4629737
theorem B6174953 : Blo 1827615 6174953 := bstep (se 2 (by rfl) ⟨2315607, by rfl⟩ : syracuseStep 6174953 = 4631215) B4631215
theorem B3086599 : Blo 1827615 3086599 := bstep (se 1 (by rfl) ⟨2314949, by rfl⟩ : syracuseStep 3086599 = 4629899) B4629899
theorem B11278601 : Blo 1827615 11278601 := bstep (se 2 (by rfl) ⟨4229475, by rfl⟩ : syracuseStep 11278601 = 8458951) B8458951
theorem B10410281 : Blo 1827615 10410281 := bstep (se 2 (by rfl) ⟨3903855, by rfl⟩ : syracuseStep 10410281 = 7807711) B7807711
theorem B2742569 : Blo 1827615 2742569 := bstep (se 2 (by rfl) ⟨1028463, by rfl⟩ : syracuseStep 2742569 = 2056927) B2056927
theorem B3086633 : Blo 1827615 3086633 := bstep (se 2 (by rfl) ⟨1157487, by rfl⟩ : syracuseStep 3086633 = 2314975) B2314975
theorem B2742575 : Blo 1827615 2742575 := bstep (se 1 (by rfl) ⟨2056931, by rfl⟩ : syracuseStep 2742575 = 4113863) B4113863
theorem B2742815 : Blo 1827615 2742815 := bstep (se 1 (by rfl) ⟨2057111, by rfl⟩ : syracuseStep 2742815 = 4114223) B4114223
theorem B5208911 : Blo 1827615 5208911 := bstep (se 1 (by rfl) ⟨3906683, by rfl⟩ : syracuseStep 5208911 = 7813367) B7813367
theorem B4012891 : Blo 1827615 4012891 := bstep (se 1 (by rfl) ⟨3009668, by rfl⟩ : syracuseStep 4012891 = 6019337) B6019337
theorem B2743199 : Blo 1827615 2743199 := bstep (se 1 (by rfl) ⟨2057399, by rfl⟩ : syracuseStep 2743199 = 4114799) B4114799
theorem B2743247 : Blo 1827615 2743247 := bstep (se 1 (by rfl) ⟨2057435, by rfl⟩ : syracuseStep 2743247 = 4114871) B4114871
theorem B2603983 : Blo 1827615 2603983 := bstep (se 1 (by rfl) ⟨1952987, by rfl⟩ : syracuseStep 2603983 = 3905975) B3905975
theorem B8788961 : Blo 1827615 8788961 := bstep (se 2 (by rfl) ⟨3295860, by rfl⟩ : syracuseStep 8788961 = 6591721) B6591721
theorem B2743337 : Blo 1827615 2743337 := bstep (se 2 (by rfl) ⟨1028751, by rfl⟩ : syracuseStep 2743337 = 2057503) B2057503
theorem B2743343 : Blo 1827615 2743343 := bstep (se 1 (by rfl) ⟨2057507, by rfl⟩ : syracuseStep 2743343 = 4115015) B4115015
theorem B2604079 : Blo 1827615 2604079 := bstep (se 1 (by rfl) ⟨1953059, by rfl⟩ : syracuseStep 2604079 = 3906119) B3906119
theorem B2743367 : Blo 1827615 2743367 := bstep (se 1 (by rfl) ⟨2057525, by rfl⟩ : syracuseStep 2743367 = 4115051) B4115051
theorem B11713693 : Blo 1827615 11713693 := bstep (se 3 (by rfl) ⟨2196317, by rfl⟩ : syracuseStep 11713693 = 4392635) B4392635
theorem B17579227 : Blo 1827615 17579227 := bstep (se 1 (by rfl) ⟨13184420, by rfl⟩ : syracuseStep 17579227 = 26368841) B26368841
theorem B2743631 : Blo 1827615 2743631 := bstep (se 1 (by rfl) ⟨2057723, by rfl⟩ : syracuseStep 2743631 = 4115447) B4115447
theorem B2743721 : Blo 1827615 2743721 := bstep (se 2 (by rfl) ⟨1028895, by rfl⟩ : syracuseStep 2743721 = 2057791) B2057791
theorem B2743871 : Blo 1827615 2743871 := bstep (se 1 (by rfl) ⟨2057903, by rfl⟩ : syracuseStep 2743871 = 4115807) B4115807
theorem B4693747 : Blo 1827615 4693747 := bstep (se 1 (by rfl) ⟨3520310, by rfl⟩ : syracuseStep 4693747 = 7040621) B7040621
theorem B6168311 : Blo 1827615 6168311 := bstep (se 1 (by rfl) ⟨4626233, by rfl⟩ : syracuseStep 6168311 = 9252467) B9252467
theorem B128384837 : Blo 1827615 128384837 := bstep (se 4 (by rfl) ⟨12036078, by rfl⟩ : syracuseStep 128384837 = 24072157) B24072157
theorem B2744135 : Blo 1827615 2744135 := bstep (se 1 (by rfl) ⟨2058101, by rfl⟩ : syracuseStep 2744135 = 4116203) B4116203
theorem B3473275 : Blo 1827615 3473275 := bstep (se 1 (by rfl) ⟨2604956, by rfl⟩ : syracuseStep 3473275 = 5209913) B5209913
theorem B63364999 : Blo 1827615 63364999 := bstep (se 1 (by rfl) ⟨47523749, by rfl⟩ : syracuseStep 63364999 = 95047499) B95047499
theorem B2744219 : Blo 1827615 2744219 := bstep (se 1 (by rfl) ⟨2058164, by rfl⟩ : syracuseStep 2744219 = 4116329) B4116329
theorem B5210027 : Blo 1827615 5210027 := bstep (se 1 (by rfl) ⟨3907520, by rfl⟩ : syracuseStep 5210027 = 7815041) B7815041
theorem B56279119 : Blo 1827615 56279119 := bstep (se 1 (by rfl) ⟨42209339, by rfl⟩ : syracuseStep 56279119 = 84418679) B84418679
theorem B13361437 : Blo 1827615 13361437 := bstep (se 3 (by rfl) ⟨2505269, by rfl⟩ : syracuseStep 13361437 = 5010539) B5010539
theorem B2056495 : Blo 1827615 2056495 := bstep (se 1 (by rfl) ⟨1542371, by rfl⟩ : syracuseStep 2056495 = 3084743) B3084743
theorem B4112927 : Blo 1827615 4112927 := bstep (se 1 (by rfl) ⟨3084695, by rfl⟩ : syracuseStep 4112927 = 6169391) B6169391
theorem B4112999 : Blo 1827615 4112999 := bstep (se 1 (by rfl) ⟨3084749, by rfl⟩ : syracuseStep 4112999 = 6169499) B6169499
theorem B4170503 : Blo 1827615 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B1827615 : Blo 1827615 1827615 := bstep (se 1 (by rfl) ⟨1370711, by rfl⟩ : syracuseStep 1827615 = 2741423) B2741423
theorem B4391945 : Blo 1827615 4391945 := bstep (se 2 (by rfl) ⟨1646979, by rfl⟩ : syracuseStep 4391945 = 3293959) B3293959
theorem B1827887 : Blo 1827615 1827887 := bstep (se 1 (by rfl) ⟨1370915, by rfl⟩ : syracuseStep 1827887 = 2741831) B2741831
theorem B411518017 : Blo 1827615 411518017 := bstep (se 2 (by rfl) ⟨154319256, by rfl⟩ : syracuseStep 411518017 = 308638513) B308638513
theorem B1827951 : Blo 1827615 1827951 := bstep (se 1 (by rfl) ⟨1370963, by rfl⟩ : syracuseStep 1827951 = 2741927) B2741927
theorem B22553747 : Blo 1827615 22553747 := bstep (se 1 (by rfl) ⟨16915310, by rfl⟩ : syracuseStep 22553747 = 33830621) B33830621
theorem B1828007 : Blo 1827615 1828007 := bstep (se 1 (by rfl) ⟨1371005, by rfl⟩ : syracuseStep 1828007 = 2742011) B2742011
theorem B1828031 : Blo 1827615 1828031 := bstep (se 1 (by rfl) ⟨1371023, by rfl⟩ : syracuseStep 1828031 = 2742047) B2742047
theorem B1828063 : Blo 1827615 1828063 := bstep (se 1 (by rfl) ⟨1371047, by rfl⟩ : syracuseStep 1828063 = 2742095) B2742095
theorem B1828143 : Blo 1827615 1828143 := bstep (se 1 (by rfl) ⟨1371107, by rfl⟩ : syracuseStep 1828143 = 2742215) B2742215
theorem B4113755 : Blo 1827615 4113755 := bstep (se 1 (by rfl) ⟨3085316, by rfl⟩ : syracuseStep 4113755 = 6170633) B6170633
theorem B6940187 : Blo 1827615 6940187 := bstep (se 1 (by rfl) ⟨5205140, by rfl⟩ : syracuseStep 6940187 = 10410281) B10410281
theorem B1828379 : Blo 1827615 1828379 := bstep (se 1 (by rfl) ⟨1371284, by rfl⟩ : syracuseStep 1828379 = 2742569) B2742569
theorem B2057755 : Blo 1827615 2057755 := bstep (se 1 (by rfl) ⟨1543316, by rfl⟩ : syracuseStep 2057755 = 3086633) B3086633
theorem B1828383 : Blo 1827615 1828383 := bstep (se 1 (by rfl) ⟨1371287, by rfl⟩ : syracuseStep 1828383 = 2742575) B2742575
theorem B4114025 : Blo 1827615 4114025 := bstep (se 2 (by rfl) ⟨1542759, by rfl⟩ : syracuseStep 4114025 = 3085519) B3085519
theorem B23438969 : Blo 1827615 23438969 := bstep (se 2 (by rfl) ⟨8789613, by rfl⟩ : syracuseStep 23438969 = 17579227) B17579227
theorem B1828543 : Blo 1827615 1828543 := bstep (se 1 (by rfl) ⟨1371407, by rfl⟩ : syracuseStep 1828543 = 2742815) B2742815
theorem B1828799 : Blo 1827615 1828799 := bstep (se 1 (by rfl) ⟨1371599, by rfl⟩ : syracuseStep 1828799 = 2743199) B2743199
theorem B1828831 : Blo 1827615 1828831 := bstep (se 1 (by rfl) ⟨1371623, by rfl⟩ : syracuseStep 1828831 = 2743247) B2743247
theorem B5859307 : Blo 1827615 5859307 := bstep (se 1 (by rfl) ⟨4394480, by rfl⟩ : syracuseStep 5859307 = 8788961) B8788961
theorem B1828891 : Blo 1827615 1828891 := bstep (se 1 (by rfl) ⟨1371668, by rfl⟩ : syracuseStep 1828891 = 2743337) B2743337
theorem B1828895 : Blo 1827615 1828895 := bstep (se 1 (by rfl) ⟨1371671, by rfl⟩ : syracuseStep 1828895 = 2743343) B2743343
theorem B1828911 : Blo 1827615 1828911 := bstep (se 1 (by rfl) ⟨1371683, by rfl⟩ : syracuseStep 1828911 = 2743367) B2743367
theorem B47483009 : Blo 1827615 47483009 := bstep (se 2 (by rfl) ⟨17806128, by rfl⟩ : syracuseStep 47483009 = 35612257) B35612257
theorem B28166291 : Blo 1827615 28166291 := bstep (se 1 (by rfl) ⟨21124718, by rfl⟩ : syracuseStep 28166291 = 42249437) B42249437
theorem B6588577 : Blo 1827615 6588577 := bstep (se 2 (by rfl) ⟨2470716, by rfl⟩ : syracuseStep 6588577 = 4941433) B4941433
theorem B4114619 : Blo 1827615 4114619 := bstep (se 1 (by rfl) ⟨3085964, by rfl⟩ : syracuseStep 4114619 = 6171929) B6171929
theorem B4114655 : Blo 1827615 4114655 := bstep (se 1 (by rfl) ⟨3085991, by rfl⟩ : syracuseStep 4114655 = 6171983) B6171983
theorem B1829087 : Blo 1827615 1829087 := bstep (se 1 (by rfl) ⟨1371815, by rfl⟩ : syracuseStep 1829087 = 2743631) B2743631
theorem B1829147 : Blo 1827615 1829147 := bstep (se 1 (by rfl) ⟨1371860, by rfl⟩ : syracuseStep 1829147 = 2743721) B2743721
theorem B13175081 : Blo 1827615 13175081 := bstep (se 2 (by rfl) ⟨4940655, by rfl⟩ : syracuseStep 13175081 = 9881311) B9881311
theorem B13183357 : Blo 1827615 13183357 := bstep (se 3 (by rfl) ⟨2471879, by rfl⟩ : syracuseStep 13183357 = 4943759) B4943759
theorem B1829247 : Blo 1827615 1829247 := bstep (se 1 (by rfl) ⟨1371935, by rfl⟩ : syracuseStep 1829247 = 2743871) B2743871
theorem B9259433 : Blo 1827615 9259433 := bstep (se 2 (by rfl) ⟨3472287, by rfl⟩ : syracuseStep 9259433 = 6944575) B6944575
theorem B4631033 : Blo 1827615 4631033 := bstep (se 2 (by rfl) ⟨1736637, by rfl⟩ : syracuseStep 4631033 = 3473275) B3473275
theorem B84486665 : Blo 1827615 84486665 := bstep (se 2 (by rfl) ⟨31682499, by rfl⟩ : syracuseStep 84486665 = 63364999) B63364999
theorem B1829423 : Blo 1827615 1829423 := bstep (se 1 (by rfl) ⟨1372067, by rfl⟩ : syracuseStep 1829423 = 2744135) B2744135
theorem B1829479 : Blo 1827615 1829479 := bstep (se 1 (by rfl) ⟨1372109, by rfl⟩ : syracuseStep 1829479 = 2744219) B2744219
theorem B4115105 : Blo 1827615 4115105 := bstep (se 2 (by rfl) ⟨1543164, by rfl⟩ : syracuseStep 4115105 = 3086329) B3086329
theorem B4115321 : Blo 1827615 4115321 := bstep (se 2 (by rfl) ⟨1543245, by rfl⟩ : syracuseStep 4115321 = 3086491) B3086491
theorem B13888421 : Blo 1827615 13888421 := bstep (se 4 (by rfl) ⟨1302039, by rfl⟩ : syracuseStep 13888421 = 2604079) B2604079
theorem B4115465 : Blo 1827615 4115465 := bstep (se 2 (by rfl) ⟨1543299, by rfl⟩ : syracuseStep 4115465 = 3086599) B3086599
theorem B4115519 : Blo 1827615 4115519 := bstep (se 1 (by rfl) ⟨3086639, by rfl⟩ : syracuseStep 4115519 = 6173279) B6173279
theorem B28142761 : Blo 1827615 28142761 := bstep (se 2 (by rfl) ⟨10553535, by rfl⟩ : syracuseStep 28142761 = 21107071) B21107071
theorem B6589835 : Blo 1827615 6589835 := bstep (se 1 (by rfl) ⟨4942376, by rfl⟩ : syracuseStep 6589835 = 9884753) B9884753
theorem B4689377 : Blo 1827615 4689377 := bstep (se 2 (by rfl) ⟨1758516, by rfl⟩ : syracuseStep 4689377 = 3517033) B3517033
theorem B760180301 : Blo 1827615 760180301 := bstep (se 3 (by rfl) ⟨142533806, by rfl⟩ : syracuseStep 760180301 = 285067613) B285067613
theorem B7810667 : Blo 1827615 7810667 := bstep (se 1 (by rfl) ⟨5858000, by rfl⟩ : syracuseStep 7810667 = 11716001) B11716001
theorem B4116347 : Blo 1827615 4116347 := bstep (se 1 (by rfl) ⟨3087260, by rfl⟩ : syracuseStep 4116347 = 6174521) B6174521
theorem B4116455 : Blo 1827615 4116455 := bstep (se 1 (by rfl) ⟨3087341, by rfl⟩ : syracuseStep 4116455 = 6174683) B6174683
theorem B2084959 : Blo 1827615 2084959 := bstep (se 1 (by rfl) ⟨1563719, by rfl⟩ : syracuseStep 2084959 = 3127439) B3127439
theorem B4116635 : Blo 1827615 4116635 := bstep (se 1 (by rfl) ⟨3087476, by rfl⟩ : syracuseStep 4116635 = 6174953) B6174953
theorem B6942905 : Blo 1827615 6942905 := bstep (se 2 (by rfl) ⟨2603589, by rfl⟩ : syracuseStep 6942905 = 5207179) B5207179
theorem B15618257 : Blo 1827615 15618257 := bstep (se 2 (by rfl) ⟨5856846, by rfl⟩ : syracuseStep 15618257 = 11713693) B11713693
theorem B6943103 : Blo 1827615 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B2929051 : Blo 1827615 2929051 := bstep (se 1 (by rfl) ⟨2196788, by rfl⟩ : syracuseStep 2929051 = 4393577) B4393577
theorem B21402085 : Blo 1827615 21402085 := bstep (se 4 (by rfl) ⟨2006445, by rfl⟩ : syracuseStep 21402085 = 4012891) B4012891
theorem B9253439 : Blo 1827615 9253439 := bstep (se 1 (by rfl) ⟨6940079, by rfl⟩ : syracuseStep 9253439 = 13880159) B13880159
theorem B4944635 : Blo 1827615 4944635 := bstep (se 1 (by rfl) ⟨3708476, by rfl⟩ : syracuseStep 4944635 = 7416953) B7416953
theorem B26358695 : Blo 1827615 26358695 := bstep (se 1 (by rfl) ⟨19769021, by rfl⟩ : syracuseStep 26358695 = 39538043) B39538043
theorem B16905145 : Blo 1827615 16905145 := bstep (se 2 (by rfl) ⟨6339429, by rfl⟩ : syracuseStep 16905145 = 12678859) B12678859
theorem B3519571 : Blo 1827615 3519571 := bstep (se 1 (by rfl) ⟨2639678, by rfl⟩ : syracuseStep 3519571 = 5279357) B5279357
theorem B3470519 : Blo 1827615 3470519 := bstep (se 1 (by rfl) ⟨2602889, by rfl⟩ : syracuseStep 3470519 = 5205779) B5205779
theorem B2741615 : Blo 1827615 2741615 := bstep (se 1 (by rfl) ⟨2056211, by rfl⟩ : syracuseStep 2741615 = 4112423) B4112423
theorem B2741735 : Blo 1827615 2741735 := bstep (se 1 (by rfl) ⟨2056301, by rfl⟩ : syracuseStep 2741735 = 4112603) B4112603
theorem B2741897 : Blo 1827615 2741897 := bstep (se 2 (by rfl) ⟨1028211, by rfl⟩ : syracuseStep 2741897 = 2056423) B2056423
theorem B2741915 : Blo 1827615 2741915 := bstep (se 1 (by rfl) ⟨2056436, by rfl⟩ : syracuseStep 2741915 = 4112873) B4112873
theorem B6682447 : Blo 1827615 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B2742107 : Blo 1827615 2742107 := bstep (se 1 (by rfl) ⟨2056580, by rfl⟩ : syracuseStep 2742107 = 4113161) B4113161
theorem B13178771 : Blo 1827615 13178771 := bstep (se 1 (by rfl) ⟨9884078, by rfl⟩ : syracuseStep 13178771 = 19768157) B19768157
theorem B4626335 : Blo 1827615 4626335 := bstep (se 1 (by rfl) ⟨3469751, by rfl⟩ : syracuseStep 4626335 = 6939503) B6939503
theorem B21108737 : Blo 1827615 21108737 := bstep (se 2 (by rfl) ⟨7915776, by rfl⟩ : syracuseStep 21108737 = 15831553) B15831553
theorem B6174791 : Blo 1827615 6174791 := bstep (se 1 (by rfl) ⟨4631093, by rfl⟩ : syracuseStep 6174791 = 9262187) B9262187
theorem B7518347 : Blo 1827615 7518347 := bstep (se 1 (by rfl) ⟨5638760, by rfl⟩ : syracuseStep 7518347 = 11277521) B11277521
theorem B2603191 : Blo 1827615 2603191 := bstep (se 1 (by rfl) ⟨1952393, by rfl⟩ : syracuseStep 2603191 = 3904787) B3904787
theorem B2742491 : Blo 1827615 2742491 := bstep (se 1 (by rfl) ⟨2056868, by rfl⟩ : syracuseStep 2742491 = 4113737) B4113737
theorem B50739493 : Blo 1827615 50739493 := bstep (se 4 (by rfl) ⟨4756827, by rfl⟩ : syracuseStep 50739493 = 9513655) B9513655
theorem B2742761 : Blo 1827615 2742761 := bstep (se 2 (by rfl) ⟨1028535, by rfl⟩ : syracuseStep 2742761 = 2057071) B2057071
theorem B15874649 : Blo 1827615 15874649 := bstep (se 2 (by rfl) ⟨5952993, by rfl⟩ : syracuseStep 15874649 = 11905987) B11905987
theorem B3471977 : Blo 1827615 3471977 := bstep (se 2 (by rfl) ⟨1301991, by rfl⟩ : syracuseStep 3471977 = 2603983) B2603983
theorem B9255545 : Blo 1827615 9255545 := bstep (se 2 (by rfl) ⟨3470829, by rfl⟩ : syracuseStep 9255545 = 6941659) B6941659
theorem B2603755 : Blo 1827615 2603755 := bstep (se 1 (by rfl) ⟨1952816, by rfl⟩ : syracuseStep 2603755 = 3905633) B3905633
theorem B63363883 : Blo 1827615 63363883 := bstep (se 1 (by rfl) ⟨47522912, by rfl⟩ : syracuseStep 63363883 = 95045825) B95045825
theorem B7519067 : Blo 1827615 7519067 := bstep (se 1 (by rfl) ⟨5639300, by rfl⟩ : syracuseStep 7519067 = 11278601) B11278601
theorem B2743151 : Blo 1827615 2743151 := bstep (se 1 (by rfl) ⟨2057363, by rfl⟩ : syracuseStep 2743151 = 4114727) B4114727
theorem B2743163 : Blo 1827615 2743163 := bstep (se 1 (by rfl) ⟨2057372, by rfl⟩ : syracuseStep 2743163 = 4114745) B4114745
theorem B3906427 : Blo 1827615 3906427 := bstep (se 1 (by rfl) ⟨2929820, by rfl⟩ : syracuseStep 3906427 = 5859641) B5859641
theorem B3087227 : Blo 1827615 3087227 := bstep (se 1 (by rfl) ⟨2315420, by rfl⟩ : syracuseStep 3087227 = 4630841) B4630841
theorem B7036001 : Blo 1827615 7036001 := bstep (se 2 (by rfl) ⟨2638500, by rfl⟩ : syracuseStep 7036001 = 5277001) B5277001
theorem B3472607 : Blo 1827615 3472607 := bstep (se 1 (by rfl) ⟨2604455, by rfl⟩ : syracuseStep 3472607 = 5208911) B5208911
theorem B13180153 : Blo 1827615 13180153 := bstep (se 2 (by rfl) ⟨4942557, by rfl⟩ : syracuseStep 13180153 = 9885115) B9885115
theorem B5856745 : Blo 1827615 5856745 := bstep (se 2 (by rfl) ⟨2196279, by rfl⟩ : syracuseStep 5856745 = 4392559) B4392559
theorem B13885019 : Blo 1827615 13885019 := bstep (se 1 (by rfl) ⟨10413764, by rfl⟩ : syracuseStep 13885019 = 20827529) B20827529
theorem B6258329 : Blo 1827615 6258329 := bstep (se 2 (by rfl) ⟨2346873, by rfl⟩ : syracuseStep 6258329 = 4693747) B4693747
theorem B2744027 : Blo 1827615 2744027 := bstep (se 1 (by rfl) ⟨2058020, by rfl⟩ : syracuseStep 2744027 = 4116041) B4116041
theorem B4112207 : Blo 1827615 4112207 := bstep (se 1 (by rfl) ⟨3084155, by rfl⟩ : syracuseStep 4112207 = 6168311) B6168311
theorem B85589891 : Blo 1827615 85589891 := bstep (se 1 (by rfl) ⟨64192418, by rfl⟩ : syracuseStep 85589891 = 128384837) B128384837
theorem B2056135 : Blo 1827615 2056135 := bstep (se 1 (by rfl) ⟨1542101, by rfl⟩ : syracuseStep 2056135 = 3084203) B3084203
theorem B3473351 : Blo 1827615 3473351 := bstep (se 1 (by rfl) ⟨2605013, by rfl⟩ : syracuseStep 3473351 = 5210027) B5210027
theorem B6168527 : Blo 1827615 6168527 := bstep (se 1 (by rfl) ⟨4626395, by rfl⟩ : syracuseStep 6168527 = 9252791) B9252791
theorem B2744297 : Blo 1827615 2744297 := bstep (se 2 (by rfl) ⟨1029111, by rfl⟩ : syracuseStep 2744297 = 2058223) B2058223
theorem B2744423 : Blo 1827615 2744423 := bstep (se 1 (by rfl) ⟨2058317, by rfl⟩ : syracuseStep 2744423 = 4116635) B4116635
theorem B75038825 : Blo 1827615 75038825 := bstep (se 2 (by rfl) ⟨28139559, by rfl⟩ : syracuseStep 75038825 = 56279119) B56279119
theorem B4628603 : Blo 1827615 4628603 := bstep (se 1 (by rfl) ⟨3471452, by rfl⟩ : syracuseStep 4628603 = 6942905) B6942905
theorem B10412171 : Blo 1827615 10412171 := bstep (se 1 (by rfl) ⟨7809128, by rfl⟩ : syracuseStep 10412171 = 15618257) B15618257
theorem B4628735 : Blo 1827615 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B6168959 : Blo 1827615 6168959 := bstep (se 1 (by rfl) ⟨4626719, by rfl⟩ : syracuseStep 6168959 = 9253439) B9253439
theorem B17572463 : Blo 1827615 17572463 := bstep (se 1 (by rfl) ⟨13179347, by rfl⟩ : syracuseStep 17572463 = 26358695) B26358695
theorem B1827743 : Blo 1827615 1827743 := bstep (se 1 (by rfl) ⟨1370807, by rfl⟩ : syracuseStep 1827743 = 2741615) B2741615
theorem B1827823 : Blo 1827615 1827823 := bstep (se 1 (by rfl) ⟨1370867, by rfl⟩ : syracuseStep 1827823 = 2741735) B2741735
theorem B84485177 : Blo 1827615 84485177 := bstep (se 2 (by rfl) ⟨31681941, by rfl⟩ : syracuseStep 84485177 = 63363883) B63363883
theorem B1827931 : Blo 1827615 1827931 := bstep (se 1 (by rfl) ⟨1370948, by rfl⟩ : syracuseStep 1827931 = 2741897) B2741897
theorem B1827943 : Blo 1827615 1827943 := bstep (se 1 (by rfl) ⟨1370957, by rfl⟩ : syracuseStep 1827943 = 2741915) B2741915
theorem B1828071 : Blo 1827615 1828071 := bstep (se 1 (by rfl) ⟨1371053, by rfl⟩ : syracuseStep 1828071 = 2742107) B2742107
theorem B31655339 : Blo 1827615 31655339 := bstep (se 1 (by rfl) ⟨23741504, by rfl⟩ : syracuseStep 31655339 = 47483009) B47483009
theorem B18777527 : Blo 1827615 18777527 := bstep (se 1 (by rfl) ⟨14083145, by rfl⟩ : syracuseStep 18777527 = 28166291) B28166291
theorem B1828327 : Blo 1827615 1828327 := bstep (se 1 (by rfl) ⟨1371245, by rfl⟩ : syracuseStep 1828327 = 2742491) B2742491
theorem B8783387 : Blo 1827615 8783387 := bstep (se 1 (by rfl) ⟨6587540, by rfl⟩ : syracuseStep 8783387 = 13175081) B13175081
theorem B1828507 : Blo 1827615 1828507 := bstep (se 1 (by rfl) ⟨1371380, by rfl⟩ : syracuseStep 1828507 = 2742761) B2742761
theorem B17573537 : Blo 1827615 17573537 := bstep (se 2 (by rfl) ⟨6590076, by rfl⟩ : syracuseStep 17573537 = 13180153) B13180153
theorem B6170363 : Blo 1827615 6170363 := bstep (se 1 (by rfl) ⟨4627772, by rfl⟩ : syracuseStep 6170363 = 9255545) B9255545
theorem B1828767 : Blo 1827615 1828767 := bstep (se 1 (by rfl) ⟨1371575, by rfl⟩ : syracuseStep 1828767 = 2743151) B2743151
theorem B1828775 : Blo 1827615 1828775 := bstep (se 1 (by rfl) ⟨1371581, by rfl⟩ : syracuseStep 1828775 = 2743163) B2743163
theorem B2058151 : Blo 1827615 2058151 := bstep (se 1 (by rfl) ⟨1543613, by rfl⟩ : syracuseStep 2058151 = 3087227) B3087227
theorem B9258947 : Blo 1827615 9258947 := bstep (se 1 (by rfl) ⟨6944210, by rfl⟩ : syracuseStep 9258947 = 13888421) B13888421
theorem B7808993 : Blo 1827615 7808993 := bstep (se 2 (by rfl) ⟨2928372, by rfl⟩ : syracuseStep 7808993 = 5856745) B5856745
theorem B4393223 : Blo 1827615 4393223 := bstep (se 1 (by rfl) ⟨3294917, by rfl⟩ : syracuseStep 4393223 = 6589835) B6589835
theorem B4172219 : Blo 1827615 4172219 := bstep (se 1 (by rfl) ⟨3129164, by rfl⟩ : syracuseStep 4172219 = 6258329) B6258329
theorem B1829351 : Blo 1827615 1829351 := bstep (se 1 (by rfl) ⟨1372013, by rfl⟩ : syracuseStep 1829351 = 2744027) B2744027
theorem B57059927 : Blo 1827615 57059927 := bstep (se 1 (by rfl) ⟨42794945, by rfl⟩ : syracuseStep 57059927 = 85589891) B85589891
theorem B1829531 : Blo 1827615 1829531 := bstep (se 1 (by rfl) ⟨1372148, by rfl⟩ : syracuseStep 1829531 = 2744297) B2744297
theorem B8784769 : Blo 1827615 8784769 := bstep (se 2 (by rfl) ⟨3294288, by rfl⟩ : syracuseStep 8784769 = 6588577) B6588577
theorem B67652657 : Blo 1827615 67652657 := bstep (se 2 (by rfl) ⟨25369746, by rfl⟩ : syracuseStep 67652657 = 50739493) B50739493
theorem B11119781 : Blo 1827615 11119781 := bstep (se 4 (by rfl) ⟨1042479, by rfl⟩ : syracuseStep 11119781 = 2084959) B2084959
theorem B3296423 : Blo 1827615 3296423 := bstep (se 1 (by rfl) ⟨2472317, by rfl⟩ : syracuseStep 3296423 = 4944635) B4944635
theorem B2780335 : Blo 1827615 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B28536113 : Blo 1827615 28536113 := bstep (se 2 (by rfl) ⟨10701042, by rfl⟩ : syracuseStep 28536113 = 21402085) B21402085
theorem B2927963 : Blo 1827615 2927963 := bstep (se 1 (by rfl) ⟨2195972, by rfl⟩ : syracuseStep 2927963 = 4391945) B4391945
theorem B15035831 : Blo 1827615 15035831 := bstep (se 1 (by rfl) ⟨11276873, by rfl⟩ : syracuseStep 15035831 = 22553747) B22553747
theorem B2313679 : Blo 1827615 2313679 := bstep (se 1 (by rfl) ⟨1735259, by rfl⟩ : syracuseStep 2313679 = 3470519) B3470519
theorem B15625979 : Blo 1827615 15625979 := bstep (se 1 (by rfl) ⟨11719484, by rfl⟩ : syracuseStep 15625979 = 23438969) B23438969
theorem B22540193 : Blo 1827615 22540193 := bstep (se 2 (by rfl) ⟨8452572, by rfl⟩ : syracuseStep 22540193 = 16905145) B16905145
theorem B8785847 : Blo 1827615 8785847 := bstep (se 1 (by rfl) ⟨6589385, by rfl⟩ : syracuseStep 8785847 = 13178771) B13178771
theorem B3084223 : Blo 1827615 3084223 := bstep (se 1 (by rfl) ⟨2313167, by rfl⟩ : syracuseStep 3084223 = 4626335) B4626335
theorem B4116527 : Blo 1827615 4116527 := bstep (se 1 (by rfl) ⟨3087395, by rfl⟩ : syracuseStep 4116527 = 6174791) B6174791
theorem B37523681 : Blo 1827615 37523681 := bstep (se 2 (by rfl) ⟨14071380, by rfl⟩ : syracuseStep 37523681 = 28142761) B28142761
theorem B6172955 : Blo 1827615 6172955 := bstep (se 1 (by rfl) ⟨4629716, by rfl⟩ : syracuseStep 6172955 = 9259433) B9259433
theorem B56324443 : Blo 1827615 56324443 := bstep (se 1 (by rfl) ⟨42243332, by rfl⟩ : syracuseStep 56324443 = 84486665) B84486665
theorem B2314651 : Blo 1827615 2314651 := bstep (se 1 (by rfl) ⟨1735988, by rfl⟩ : syracuseStep 2314651 = 3471977) B3471977
theorem B4690667 : Blo 1827615 4690667 := bstep (se 1 (by rfl) ⟨3518000, by rfl⟩ : syracuseStep 4690667 = 7036001) B7036001
theorem B2315071 : Blo 1827615 2315071 := bstep (se 1 (by rfl) ⟨1736303, by rfl⟩ : syracuseStep 2315071 = 3472607) B3472607
theorem B3126251 : Blo 1827615 3126251 := bstep (se 1 (by rfl) ⟨2344688, by rfl⟩ : syracuseStep 3126251 = 4689377) B4689377
theorem B506786867 : Blo 1827615 506786867 := bstep (se 1 (by rfl) ⟨380090150, by rfl⟩ : syracuseStep 506786867 = 760180301) B760180301
theorem B5207111 : Blo 1827615 5207111 := bstep (se 1 (by rfl) ⟨3905333, by rfl⟩ : syracuseStep 5207111 = 7810667) B7810667
theorem B8909929 : Blo 1827615 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B2741471 : Blo 1827615 2741471 := bstep (se 1 (by rfl) ⟨2056103, by rfl⟩ : syracuseStep 2741471 = 4112207) B4112207
theorem B2741513 : Blo 1827615 2741513 := bstep (se 2 (by rfl) ⟨1028067, by rfl⟩ : syracuseStep 2741513 = 2056135) B2056135
theorem B2315567 : Blo 1827615 2315567 := bstep (se 1 (by rfl) ⟨1736675, by rfl⟩ : syracuseStep 2315567 = 3473351) B3473351
theorem B7812409 : Blo 1827615 7812409 := bstep (se 2 (by rfl) ⟨2929653, by rfl⟩ : syracuseStep 7812409 = 5859307) B5859307
theorem B3470921 : Blo 1827615 3470921 := bstep (se 2 (by rfl) ⟨1301595, by rfl⟩ : syracuseStep 3470921 = 2603191) B2603191
theorem B2741951 : Blo 1827615 2741951 := bstep (se 1 (by rfl) ⟨2056463, by rfl⟩ : syracuseStep 2741951 = 4112927) B4112927
theorem B17815249 : Blo 1827615 17815249 := bstep (se 2 (by rfl) ⟨6680718, by rfl⟩ : syracuseStep 17815249 = 13361437) B13361437
theorem B2741993 : Blo 1827615 2741993 := bstep (se 2 (by rfl) ⟨1028247, by rfl⟩ : syracuseStep 2741993 = 2056495) B2056495
theorem B2741999 : Blo 1827615 2741999 := bstep (se 1 (by rfl) ⟨2056499, by rfl⟩ : syracuseStep 2741999 = 4112999) B4112999
theorem B17577809 : Blo 1827615 17577809 := bstep (se 2 (by rfl) ⟨6591678, by rfl⟩ : syracuseStep 17577809 = 13183357) B13183357
theorem B2742503 : Blo 1827615 2742503 := bstep (se 1 (by rfl) ⟨2056877, by rfl⟩ : syracuseStep 2742503 = 4113755) B4113755
theorem B3471673 : Blo 1827615 3471673 := bstep (se 2 (by rfl) ⟨1301877, by rfl⟩ : syracuseStep 3471673 = 2603755) B2603755
theorem B4626791 : Blo 1827615 4626791 := bstep (se 1 (by rfl) ⟨3470093, by rfl⟩ : syracuseStep 4626791 = 6940187) B6940187
theorem B2742683 : Blo 1827615 2742683 := bstep (se 1 (by rfl) ⟨2057012, by rfl⟩ : syracuseStep 2742683 = 4114025) B4114025
theorem B5208569 : Blo 1827615 5208569 := bstep (se 2 (by rfl) ⟨1953213, by rfl⟩ : syracuseStep 5208569 = 3906427) B3906427
theorem B14072491 : Blo 1827615 14072491 := bstep (se 1 (by rfl) ⟨10554368, by rfl⟩ : syracuseStep 14072491 = 21108737) B21108737
theorem B548690689 : Blo 1827615 548690689 := bstep (se 2 (by rfl) ⟨205759008, by rfl⟩ : syracuseStep 548690689 = 411518017) B411518017
theorem B5012231 : Blo 1827615 5012231 := bstep (se 1 (by rfl) ⟨3759173, by rfl⟩ : syracuseStep 5012231 = 7518347) B7518347
theorem B4692761 : Blo 1827615 4692761 := bstep (se 2 (by rfl) ⟨1759785, by rfl⟩ : syracuseStep 4692761 = 3519571) B3519571
theorem B2743079 : Blo 1827615 2743079 := bstep (se 1 (by rfl) ⟨2057309, by rfl⟩ : syracuseStep 2743079 = 4114619) B4114619
theorem B2743103 : Blo 1827615 2743103 := bstep (se 1 (by rfl) ⟨2057327, by rfl⟩ : syracuseStep 2743103 = 4114655) B4114655
theorem B3087355 : Blo 1827615 3087355 := bstep (se 1 (by rfl) ⟨2315516, by rfl⟩ : syracuseStep 3087355 = 4631033) B4631033
theorem B10583099 : Blo 1827615 10583099 := bstep (se 1 (by rfl) ⟨7937324, by rfl⟩ : syracuseStep 10583099 = 15874649) B15874649
theorem B2743403 : Blo 1827615 2743403 := bstep (se 1 (by rfl) ⟨2057552, by rfl⟩ : syracuseStep 2743403 = 4115105) B4115105
theorem B5012711 : Blo 1827615 5012711 := bstep (se 1 (by rfl) ⟨3759533, by rfl⟩ : syracuseStep 5012711 = 7519067) B7519067
theorem B2743547 : Blo 1827615 2743547 := bstep (se 1 (by rfl) ⟨2057660, by rfl⟩ : syracuseStep 2743547 = 4115321) B4115321
theorem B2743643 : Blo 1827615 2743643 := bstep (se 1 (by rfl) ⟨2057732, by rfl⟩ : syracuseStep 2743643 = 4115465) B4115465
theorem B2743673 : Blo 1827615 2743673 := bstep (se 2 (by rfl) ⟨1028877, by rfl⟩ : syracuseStep 2743673 = 2057755) B2057755
theorem B2743679 : Blo 1827615 2743679 := bstep (se 1 (by rfl) ⟨2057759, by rfl⟩ : syracuseStep 2743679 = 4115519) B4115519
theorem B15621605 : Blo 1827615 15621605 := bstep (se 4 (by rfl) ⟨1464525, by rfl⟩ : syracuseStep 15621605 = 2929051) B2929051
theorem B9256679 : Blo 1827615 9256679 := bstep (se 1 (by rfl) ⟨6942509, by rfl⟩ : syracuseStep 9256679 = 13885019) B13885019
theorem B2744231 : Blo 1827615 2744231 := bstep (se 1 (by rfl) ⟨2058173, by rfl⟩ : syracuseStep 2744231 = 4116347) B4116347
theorem B4112351 : Blo 1827615 4112351 := bstep (se 1 (by rfl) ⟨3084263, by rfl⟩ : syracuseStep 4112351 = 6168527) B6168527
theorem B2744303 : Blo 1827615 2744303 := bstep (se 1 (by rfl) ⟨2058227, by rfl⟩ : syracuseStep 2744303 = 4116455) B4116455
theorem B2744351 : Blo 1827615 2744351 := bstep (se 1 (by rfl) ⟨2058263, by rfl⟩ : syracuseStep 2744351 = 4116527) B4116527
theorem B4112639 : Blo 1827615 4112639 := bstep (se 1 (by rfl) ⟨3084479, by rfl⟩ : syracuseStep 4112639 = 6168959) B6168959
theorem B11714975 : Blo 1827615 11714975 := bstep (se 1 (by rfl) ⟨8786231, by rfl⟩ : syracuseStep 11714975 = 17572463) B17572463
theorem B4628897 : Blo 1827615 4628897 := bstep (se 2 (by rfl) ⟨1735836, by rfl⟩ : syracuseStep 4628897 = 3471673) B3471673
theorem B1827647 : Blo 1827615 1827647 := bstep (se 1 (by rfl) ⟨1370735, by rfl⟩ : syracuseStep 1827647 = 2741471) B2741471
theorem B1827675 : Blo 1827615 1827675 := bstep (se 1 (by rfl) ⟨1370756, by rfl⟩ : syracuseStep 1827675 = 2741513) B2741513
theorem B21103559 : Blo 1827615 21103559 := bstep (se 1 (by rfl) ⟨15827669, by rfl⟩ : syracuseStep 21103559 = 31655339) B31655339
theorem B12518351 : Blo 1827615 12518351 := bstep (se 1 (by rfl) ⟨9388763, by rfl⟩ : syracuseStep 12518351 = 18777527) B18777527
theorem B731587585 : Blo 1827615 731587585 := bstep (se 2 (by rfl) ⟨274345344, by rfl⟩ : syracuseStep 731587585 = 548690689) B548690689
theorem B11715691 : Blo 1827615 11715691 := bstep (se 1 (by rfl) ⟨8786768, by rfl⟩ : syracuseStep 11715691 = 17573537) B17573537
theorem B1827967 : Blo 1827615 1827967 := bstep (se 1 (by rfl) ⟨1370975, by rfl⟩ : syracuseStep 1827967 = 2741951) B2741951
theorem B1827995 : Blo 1827615 1827995 := bstep (se 1 (by rfl) ⟨1370996, by rfl⟩ : syracuseStep 1827995 = 2741993) B2741993
theorem B1827999 : Blo 1827615 1827999 := bstep (se 1 (by rfl) ⟨1370999, by rfl⟩ : syracuseStep 1827999 = 2741999) B2741999
theorem B4113575 : Blo 1827615 4113575 := bstep (se 1 (by rfl) ⟨3085181, by rfl⟩ : syracuseStep 4113575 = 6170363) B6170363
theorem B11879905 : Blo 1827615 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B1828335 : Blo 1827615 1828335 := bstep (se 1 (by rfl) ⟨1371251, by rfl⟩ : syracuseStep 1828335 = 2742503) B2742503
theorem B1828455 : Blo 1827615 1828455 := bstep (se 1 (by rfl) ⟨1371341, by rfl⟩ : syracuseStep 1828455 = 2742683) B2742683
theorem B1828719 : Blo 1827615 1828719 := bstep (se 1 (by rfl) ⟨1371539, by rfl⟩ : syracuseStep 1828719 = 2743079) B2743079
theorem B1828735 : Blo 1827615 1828735 := bstep (se 1 (by rfl) ⟨1371551, by rfl⟩ : syracuseStep 1828735 = 2743103) B2743103
theorem B7055399 : Blo 1827615 7055399 := bstep (se 1 (by rfl) ⟨5291549, by rfl⟩ : syracuseStep 7055399 = 10583099) B10583099
theorem B1828935 : Blo 1827615 1828935 := bstep (se 1 (by rfl) ⟨1371701, by rfl⟩ : syracuseStep 1828935 = 2743403) B2743403
theorem B2197615 : Blo 1827615 2197615 := bstep (se 1 (by rfl) ⟨1648211, by rfl⟩ : syracuseStep 2197615 = 3296423) B3296423
theorem B1829031 : Blo 1827615 1829031 := bstep (se 1 (by rfl) ⟨1371773, by rfl⟩ : syracuseStep 1829031 = 2743547) B2743547
theorem B19024075 : Blo 1827615 19024075 := bstep (se 1 (by rfl) ⟨14268056, by rfl⟩ : syracuseStep 19024075 = 28536113) B28536113
theorem B1951975 : Blo 1827615 1951975 := bstep (se 1 (by rfl) ⟨1463981, by rfl⟩ : syracuseStep 1951975 = 2927963) B2927963
theorem B1829095 : Blo 1827615 1829095 := bstep (se 1 (by rfl) ⟨1371821, by rfl⟩ : syracuseStep 1829095 = 2743643) B2743643
theorem B1829115 : Blo 1827615 1829115 := bstep (se 1 (by rfl) ⟨1371836, by rfl⟩ : syracuseStep 1829115 = 2743673) B2743673
theorem B1829119 : Blo 1827615 1829119 := bstep (se 1 (by rfl) ⟨1371839, by rfl⟩ : syracuseStep 1829119 = 2743679) B2743679
theorem B10414403 : Blo 1827615 10414403 := bstep (se 1 (by rfl) ⟨7810802, by rfl⟩ : syracuseStep 10414403 = 15621605) B15621605
theorem B6171119 : Blo 1827615 6171119 := bstep (se 1 (by rfl) ⟨4628339, by rfl⟩ : syracuseStep 6171119 = 9256679) B9256679
theorem B15026795 : Blo 1827615 15026795 := bstep (se 1 (by rfl) ⟨11270096, by rfl⟩ : syracuseStep 15026795 = 22540193) B22540193
theorem B1829487 : Blo 1827615 1829487 := bstep (se 1 (by rfl) ⟨1372115, by rfl⟩ : syracuseStep 1829487 = 2744231) B2744231
theorem B1829535 : Blo 1827615 1829535 := bstep (se 1 (by rfl) ⟨1372151, by rfl⟩ : syracuseStep 1829535 = 2744303) B2744303
theorem B1829615 : Blo 1827615 1829615 := bstep (se 1 (by rfl) ⟨1372211, by rfl⟩ : syracuseStep 1829615 = 2744423) B2744423
theorem B53463797 : Blo 1827615 53463797 := bstep (se 5 (by rfl) ⟨2506115, by rfl⟩ : syracuseStep 53463797 = 5012231) B5012231
theorem B6941447 : Blo 1827615 6941447 := bstep (se 1 (by rfl) ⟨5206085, by rfl⟩ : syracuseStep 6941447 = 10412171) B10412171
theorem B4115303 : Blo 1827615 4115303 := bstep (se 1 (by rfl) ⟨3086477, by rfl⟩ : syracuseStep 4115303 = 6172955) B6172955
theorem B75099257 : Blo 1827615 75099257 := bstep (se 2 (by rfl) ⟨28162221, by rfl⟩ : syracuseStep 75099257 = 56324443) B56324443
theorem B2084167 : Blo 1827615 2084167 := bstep (se 1 (by rfl) ⟨1563125, by rfl⟩ : syracuseStep 2084167 = 3126251) B3126251
theorem B337857911 : Blo 1827615 337857911 := bstep (se 1 (by rfl) ⟨253393433, by rfl⟩ : syracuseStep 337857911 = 506786867) B506786867
theorem B56323451 : Blo 1827615 56323451 := bstep (se 1 (by rfl) ⟨42242588, by rfl⟩ : syracuseStep 56323451 = 84485177) B84485177
theorem B18763321 : Blo 1827615 18763321 := bstep (se 2 (by rfl) ⟨7036245, by rfl⟩ : syracuseStep 18763321 = 14072491) B14072491
theorem B2313947 : Blo 1827615 2313947 := bstep (se 1 (by rfl) ⟨1735460, by rfl⟩ : syracuseStep 2313947 = 3470921) B3470921
theorem B11718539 : Blo 1827615 11718539 := bstep (se 1 (by rfl) ⟨8788904, by rfl⟩ : syracuseStep 11718539 = 17577809) B17577809
theorem B6172631 : Blo 1827615 6172631 := bstep (se 1 (by rfl) ⟨4629473, by rfl⟩ : syracuseStep 6172631 = 9258947) B9258947
theorem B5205995 : Blo 1827615 5205995 := bstep (se 1 (by rfl) ⟨3904496, by rfl⟩ : syracuseStep 5205995 = 7808993) B7808993
theorem B4116473 : Blo 1827615 4116473 := bstep (se 2 (by rfl) ⟨1543677, by rfl⟩ : syracuseStep 4116473 = 3087355) B3087355
theorem B2928815 : Blo 1827615 2928815 := bstep (se 1 (by rfl) ⟨2196611, by rfl⟩ : syracuseStep 2928815 = 4393223) B4393223
theorem B3707113 : Blo 1827615 3707113 := bstep (se 2 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 3707113 = 2780335) B2780335
theorem B3084527 : Blo 1827615 3084527 := bstep (se 1 (by rfl) ⟨2313395, by rfl⟩ : syracuseStep 3084527 = 4626791) B4626791
theorem B2781479 : Blo 1827615 2781479 := bstep (se 1 (by rfl) ⟨2086109, by rfl⟩ : syracuseStep 2781479 = 4172219) B4172219
theorem B38039951 : Blo 1827615 38039951 := bstep (se 1 (by rfl) ⟨28529963, by rfl⟩ : syracuseStep 38039951 = 57059927) B57059927
theorem B10416545 : Blo 1827615 10416545 := bstep (se 2 (by rfl) ⟨3906204, by rfl⟩ : syracuseStep 10416545 = 7812409) B7812409
theorem B3084905 : Blo 1827615 3084905 := bstep (se 2 (by rfl) ⟨1156839, by rfl⟩ : syracuseStep 3084905 = 2313679) B2313679
theorem B45101771 : Blo 1827615 45101771 := bstep (se 1 (by rfl) ⟨33826328, by rfl⟩ : syracuseStep 45101771 = 67652657) B67652657
theorem B23753665 : Blo 1827615 23753665 := bstep (se 2 (by rfl) ⟨8907624, by rfl⟩ : syracuseStep 23753665 = 17815249) B17815249
theorem B10023887 : Blo 1827615 10023887 := bstep (se 1 (by rfl) ⟨7517915, by rfl⟩ : syracuseStep 10023887 = 15035831) B15035831
theorem B10417319 : Blo 1827615 10417319 := bstep (se 1 (by rfl) ⟨7812989, by rfl⟩ : syracuseStep 10417319 = 15625979) B15625979
theorem B2741567 : Blo 1827615 2741567 := bstep (se 1 (by rfl) ⟨2056175, by rfl⟩ : syracuseStep 2741567 = 4112351) B4112351
theorem B50025883 : Blo 1827615 50025883 := bstep (se 1 (by rfl) ⟨37519412, by rfl⟩ : syracuseStep 50025883 = 75038825) B75038825
theorem B3085735 : Blo 1827615 3085735 := bstep (se 1 (by rfl) ⟨2314301, by rfl⟩ : syracuseStep 3085735 = 4628603) B4628603
theorem B25015787 : Blo 1827615 25015787 := bstep (se 1 (by rfl) ⟨18761840, by rfl⟩ : syracuseStep 25015787 = 37523681) B37523681
theorem B3085823 : Blo 1827615 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B29652749 : Blo 1827615 29652749 := bstep (se 3 (by rfl) ⟨5559890, by rfl⟩ : syracuseStep 29652749 = 11119781) B11119781
theorem B3086201 : Blo 1827615 3086201 := bstep (se 2 (by rfl) ⟨1157325, by rfl⟩ : syracuseStep 3086201 = 2314651) B2314651
theorem B3471407 : Blo 1827615 3471407 := bstep (se 1 (by rfl) ⟨2603555, by rfl⟩ : syracuseStep 3471407 = 5207111) B5207111
theorem B6174845 : Blo 1827615 6174845 := bstep (se 3 (by rfl) ⟨1157783, by rfl⟩ : syracuseStep 6174845 = 2315567) B2315567
theorem B5855591 : Blo 1827615 5855591 := bstep (se 1 (by rfl) ⟨4391693, by rfl⟩ : syracuseStep 5855591 = 8783387) B8783387
theorem B3086761 : Blo 1827615 3086761 := bstep (se 2 (by rfl) ⟨1157535, by rfl⟩ : syracuseStep 3086761 = 2315071) B2315071
theorem B11713025 : Blo 1827615 11713025 := bstep (se 2 (by rfl) ⟨4392384, by rfl⟩ : syracuseStep 11713025 = 8784769) B8784769
theorem B3472379 : Blo 1827615 3472379 := bstep (se 1 (by rfl) ⟨2604284, by rfl⟩ : syracuseStep 3472379 = 5208569) B5208569
theorem B3128507 : Blo 1827615 3128507 := bstep (se 1 (by rfl) ⟨2346380, by rfl⟩ : syracuseStep 3128507 = 4692761) B4692761
theorem B12508445 : Blo 1827615 12508445 := bstep (se 3 (by rfl) ⟨2345333, by rfl⟩ : syracuseStep 12508445 = 4690667) B4690667
theorem B3341807 : Blo 1827615 3341807 := bstep (se 1 (by rfl) ⟨2506355, by rfl⟩ : syracuseStep 3341807 = 5012711) B5012711
theorem B2744201 : Blo 1827615 2744201 := bstep (se 2 (by rfl) ⟨1029075, by rfl⟩ : syracuseStep 2744201 = 2058151) B2058151
theorem B4112297 : Blo 1827615 4112297 := bstep (se 2 (by rfl) ⟨1542111, by rfl⟩ : syracuseStep 4112297 = 3084223) B3084223
theorem B5857231 : Blo 1827615 5857231 := bstep (se 1 (by rfl) ⟨4392923, by rfl⟩ : syracuseStep 5857231 = 8785847) B8785847
theorem B2056351 : Blo 1827615 2056351 := bstep (se 1 (by rfl) ⟨1542263, by rfl⟩ : syracuseStep 2056351 = 3084527) B3084527
theorem B2056603 : Blo 1827615 2056603 := bstep (se 1 (by rfl) ⟨1542452, by rfl⟩ : syracuseStep 2056603 = 3084905) B3084905
theorem B1827711 : Blo 1827615 1827711 := bstep (se 1 (by rfl) ⟨1370783, by rfl⟩ : syracuseStep 1827711 = 2741567) B2741567
theorem B2057215 : Blo 1827615 2057215 := bstep (se 1 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 2057215 = 3085823) B3085823
theorem B19768499 : Blo 1827615 19768499 := bstep (se 1 (by rfl) ⟨14826374, by rfl⟩ : syracuseStep 19768499 = 29652749) B29652749
theorem B2057467 : Blo 1827615 2057467 := bstep (se 1 (by rfl) ⟨1543100, by rfl⟩ : syracuseStep 2057467 = 3086201) B3086201
theorem B4703599 : Blo 1827615 4703599 := bstep (se 1 (by rfl) ⟨3527699, by rfl⟩ : syracuseStep 4703599 = 7055399) B7055399
theorem B4114079 : Blo 1827615 4114079 := bstep (se 1 (by rfl) ⟨3085559, by rfl⟩ : syracuseStep 4114079 = 6171119) B6171119
theorem B2778889 : Blo 1827615 2778889 := bstep (se 2 (by rfl) ⟨1042083, by rfl⟩ : syracuseStep 2778889 = 2084167) B2084167
theorem B66701177 : Blo 1827615 66701177 := bstep (se 2 (by rfl) ⟨25012941, by rfl⟩ : syracuseStep 66701177 = 50025883) B50025883
theorem B4114313 : Blo 1827615 4114313 := bstep (se 2 (by rfl) ⟨1542867, by rfl⟩ : syracuseStep 4114313 = 3085735) B3085735
theorem B6170525 : Blo 1827615 6170525 := bstep (se 3 (by rfl) ⟨1156973, by rfl⟩ : syracuseStep 6170525 = 2313947) B2313947
theorem B1829467 : Blo 1827615 1829467 := bstep (se 1 (by rfl) ⟨1372100, by rfl⟩ : syracuseStep 1829467 = 2744201) B2744201
theorem B7809641 : Blo 1827615 7809641 := bstep (se 2 (by rfl) ⟨2928615, by rfl⟩ : syracuseStep 7809641 = 5857231) B5857231
theorem B4115087 : Blo 1827615 4115087 := bstep (se 1 (by rfl) ⟨3086315, by rfl⟩ : syracuseStep 4115087 = 6172631) B6172631
theorem B1829567 : Blo 1827615 1829567 := bstep (se 1 (by rfl) ⟨1372175, by rfl⟩ : syracuseStep 1829567 = 2744351) B2744351
theorem B1952543 : Blo 1827615 1952543 := bstep (se 1 (by rfl) ⟨1464407, by rfl⟩ : syracuseStep 1952543 = 2928815) B2928815
theorem B7809983 : Blo 1827615 7809983 := bstep (se 1 (by rfl) ⟨5857487, by rfl⟩ : syracuseStep 7809983 = 11714975) B11714975
theorem B4942817 : Blo 1827615 4942817 := bstep (se 2 (by rfl) ⟨1853556, by rfl⟩ : syracuseStep 4942817 = 3707113) B3707113
theorem B30067847 : Blo 1827615 30067847 := bstep (se 1 (by rfl) ⟨22550885, by rfl⟩ : syracuseStep 30067847 = 45101771) B45101771
theorem B4115681 : Blo 1827615 4115681 := bstep (se 2 (by rfl) ⟨1543380, by rfl⟩ : syracuseStep 4115681 = 3086761) B3086761
theorem B7417277 : Blo 1827615 7417277 := bstep (se 3 (by rfl) ⟨1390739, by rfl⟩ : syracuseStep 7417277 = 2781479) B2781479
theorem B150195869 : Blo 1827615 150195869 := bstep (se 3 (by rfl) ⟨28161725, by rfl⟩ : syracuseStep 150195869 = 56323451) B56323451
theorem B101461733 : Blo 1827615 101461733 := bstep (se 4 (by rfl) ⟨9512037, by rfl⟩ : syracuseStep 101461733 = 19024075) B19024075
theorem B975450113 : Blo 1827615 975450113 := bstep (se 2 (by rfl) ⟨365793792, by rfl⟩ : syracuseStep 975450113 = 731587585) B731587585
theorem B2314271 : Blo 1827615 2314271 := bstep (se 1 (by rfl) ⟨1735703, by rfl⟩ : syracuseStep 2314271 = 3471407) B3471407
theorem B4116563 : Blo 1827615 4116563 := bstep (se 1 (by rfl) ⟨3087422, by rfl⟩ : syracuseStep 4116563 = 6174845) B6174845
theorem B6942935 : Blo 1827615 6942935 := bstep (se 1 (by rfl) ⟨5207201, by rfl⟩ : syracuseStep 6942935 = 10414403) B10414403
theorem B3903727 : Blo 1827615 3903727 := bstep (se 1 (by rfl) ⟨2927795, by rfl⟩ : syracuseStep 3903727 = 5855591) B5855591
theorem B15839873 : Blo 1827615 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B2314919 : Blo 1827615 2314919 := bstep (se 1 (by rfl) ⟨1736189, by rfl⟩ : syracuseStep 2314919 = 3472379) B3472379
theorem B225104629 : Blo 1827615 225104629 := bstep (se 5 (by rfl) ⟨10551779, by rfl⟩ : syracuseStep 225104629 = 21103559) B21103559
theorem B50066171 : Blo 1827615 50066171 := bstep (se 1 (by rfl) ⟨37549628, by rfl⟩ : syracuseStep 50066171 = 75099257) B75099257
theorem B2085671 : Blo 1827615 2085671 := bstep (se 1 (by rfl) ⟨1564253, by rfl⟩ : syracuseStep 2085671 = 3128507) B3128507
theorem B126686213 : Blo 1827615 126686213 := bstep (se 4 (by rfl) ⟨11876832, by rfl⟩ : syracuseStep 126686213 = 23753665) B23753665
theorem B7812359 : Blo 1827615 7812359 := bstep (se 1 (by rfl) ⟨5859269, by rfl⟩ : syracuseStep 7812359 = 11718539) B11718539
theorem B2741531 : Blo 1827615 2741531 := bstep (se 1 (by rfl) ⟨2056148, by rfl⟩ : syracuseStep 2741531 = 4112297) B4112297
theorem B3470663 : Blo 1827615 3470663 := bstep (se 1 (by rfl) ⟨2602997, by rfl⟩ : syracuseStep 3470663 = 5205995) B5205995
theorem B2930153 : Blo 1827615 2930153 := bstep (se 2 (by rfl) ⟨1098807, by rfl⟩ : syracuseStep 2930153 = 2197615) B2197615
theorem B2741759 : Blo 1827615 2741759 := bstep (se 1 (by rfl) ⟨2056319, by rfl⟩ : syracuseStep 2741759 = 4112639) B4112639
theorem B25359967 : Blo 1827615 25359967 := bstep (se 1 (by rfl) ⟨19019975, by rfl⟩ : syracuseStep 25359967 = 38039951) B38039951
theorem B3085931 : Blo 1827615 3085931 := bstep (se 1 (by rfl) ⟨2314448, by rfl⟩ : syracuseStep 3085931 = 4628897) B4628897
theorem B6944363 : Blo 1827615 6944363 := bstep (se 1 (by rfl) ⟨5208272, by rfl⟩ : syracuseStep 6944363 = 10416545) B10416545
theorem B2602633 : Blo 1827615 2602633 := bstep (se 2 (by rfl) ⟨975987, by rfl⟩ : syracuseStep 2602633 = 1951975) B1951975
theorem B6682591 : Blo 1827615 6682591 := bstep (se 1 (by rfl) ⟨5011943, by rfl⟩ : syracuseStep 6682591 = 10023887) B10023887
theorem B8345567 : Blo 1827615 8345567 := bstep (se 1 (by rfl) ⟨6259175, by rfl⟩ : syracuseStep 8345567 = 12518351) B12518351
theorem B2742383 : Blo 1827615 2742383 := bstep (se 1 (by rfl) ⟨2056787, by rfl⟩ : syracuseStep 2742383 = 4113575) B4113575
theorem B6944879 : Blo 1827615 6944879 := bstep (se 1 (by rfl) ⟨5208659, by rfl⟩ : syracuseStep 6944879 = 10417319) B10417319
theorem B16677191 : Blo 1827615 16677191 := bstep (se 1 (by rfl) ⟨12507893, by rfl⟩ : syracuseStep 16677191 = 25015787) B25015787
theorem B31234733 : Blo 1827615 31234733 := bstep (se 3 (by rfl) ⟨5856512, by rfl⟩ : syracuseStep 31234733 = 11713025) B11713025
theorem B15620921 : Blo 1827615 15620921 := bstep (se 2 (by rfl) ⟨5857845, by rfl⟩ : syracuseStep 15620921 = 11715691) B11715691
theorem B10017863 : Blo 1827615 10017863 := bstep (se 1 (by rfl) ⟨7513397, by rfl⟩ : syracuseStep 10017863 = 15026795) B15026795
theorem B35642531 : Blo 1827615 35642531 := bstep (se 1 (by rfl) ⟨26731898, by rfl⟩ : syracuseStep 35642531 = 53463797) B53463797
theorem B4627631 : Blo 1827615 4627631 := bstep (se 1 (by rfl) ⟨3470723, by rfl⟩ : syracuseStep 4627631 = 6941447) B6941447
theorem B2743535 : Blo 1827615 2743535 := bstep (se 1 (by rfl) ⟨2057651, by rfl⟩ : syracuseStep 2743535 = 4115303) B4115303
theorem B25017761 : Blo 1827615 25017761 := bstep (se 2 (by rfl) ⟨9381660, by rfl⟩ : syracuseStep 25017761 = 18763321) B18763321
theorem B8338963 : Blo 1827615 8338963 := bstep (se 1 (by rfl) ⟨6254222, by rfl⟩ : syracuseStep 8338963 = 12508445) B12508445
theorem B225238607 : Blo 1827615 225238607 := bstep (se 1 (by rfl) ⟨168928955, by rfl⟩ : syracuseStep 225238607 = 337857911) B337857911
theorem B2227871 : Blo 1827615 2227871 := bstep (se 1 (by rfl) ⟨1670903, by rfl⟩ : syracuseStep 2227871 = 3341807) B3341807
theorem B2744315 : Blo 1827615 2744315 := bstep (se 1 (by rfl) ⟨2058236, by rfl⟩ : syracuseStep 2744315 = 4116473) B4116473
theorem B2744375 : Blo 1827615 2744375 := bstep (se 1 (by rfl) ⟨2058281, by rfl⟩ : syracuseStep 2744375 = 4116563) B4116563
theorem B4628623 : Blo 1827615 4628623 := bstep (se 1 (by rfl) ⟨3471467, by rfl⟩ : syracuseStep 4628623 = 6942935) B6942935
theorem B10559915 : Blo 1827615 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B1827687 : Blo 1827615 1827687 := bstep (se 1 (by rfl) ⟨1370765, by rfl⟩ : syracuseStep 1827687 = 2741531) B2741531
theorem B300139505 : Blo 1827615 300139505 := bstep (se 2 (by rfl) ⟨112552314, by rfl⟩ : syracuseStep 300139505 = 225104629) B225104629
theorem B1827839 : Blo 1827615 1827839 := bstep (se 1 (by rfl) ⟨1370879, by rfl⟩ : syracuseStep 1827839 = 2741759) B2741759
theorem B2057287 : Blo 1827615 2057287 := bstep (se 1 (by rfl) ⟨1542965, by rfl⟩ : syracuseStep 2057287 = 3085931) B3085931
theorem B4629575 : Blo 1827615 4629575 := bstep (se 1 (by rfl) ⟨3472181, by rfl⟩ : syracuseStep 4629575 = 6944363) B6944363
theorem B44467451 : Blo 1827615 44467451 := bstep (se 1 (by rfl) ⟨33350588, by rfl⟩ : syracuseStep 44467451 = 66701177) B66701177
theorem B4113683 : Blo 1827615 4113683 := bstep (se 1 (by rfl) ⟨3085262, by rfl⟩ : syracuseStep 4113683 = 6170525) B6170525
theorem B5563711 : Blo 1827615 5563711 := bstep (se 1 (by rfl) ⟨4172783, by rfl⟩ : syracuseStep 5563711 = 8345567) B8345567
theorem B1828255 : Blo 1827615 1828255 := bstep (se 1 (by rfl) ⟨1371191, by rfl⟩ : syracuseStep 1828255 = 2742383) B2742383
theorem B4629919 : Blo 1827615 4629919 := bstep (se 1 (by rfl) ⟨3472439, by rfl⟩ : syracuseStep 4629919 = 6944879) B6944879
theorem B5940989 : Blo 1827615 5940989 := bstep (se 3 (by rfl) ⟨1113935, by rfl⟩ : syracuseStep 5940989 = 2227871) B2227871
theorem B10413947 : Blo 1827615 10413947 := bstep (se 1 (by rfl) ⟨7810460, by rfl⟩ : syracuseStep 10413947 = 15620921) B15620921
theorem B25085861 : Blo 1827615 25085861 := bstep (se 4 (by rfl) ⟨2351799, by rfl⟩ : syracuseStep 25085861 = 4703599) B4703599
theorem B3295211 : Blo 1827615 3295211 := bstep (se 1 (by rfl) ⟨2471408, by rfl⟩ : syracuseStep 3295211 = 4942817) B4942817
theorem B11118617 : Blo 1827615 11118617 := bstep (se 2 (by rfl) ⟨4169481, by rfl⟩ : syracuseStep 11118617 = 8338963) B8338963
theorem B6678575 : Blo 1827615 6678575 := bstep (se 1 (by rfl) ⟨5008931, by rfl⟩ : syracuseStep 6678575 = 10017863) B10017863
theorem B1829023 : Blo 1827615 1829023 := bstep (se 1 (by rfl) ⟨1371767, by rfl⟩ : syracuseStep 1829023 = 2743535) B2743535
theorem B3705185 : Blo 1827615 3705185 := bstep (se 2 (by rfl) ⟨1389444, by rfl⟩ : syracuseStep 3705185 = 2778889) B2778889
theorem B1829543 : Blo 1827615 1829543 := bstep (se 1 (by rfl) ⟨1372157, by rfl⟩ : syracuseStep 1829543 = 2744315) B2744315
theorem B650300075 : Blo 1827615 650300075 := bstep (se 1 (by rfl) ⟨487725056, by rfl⟩ : syracuseStep 650300075 = 975450113) B975450113
theorem B6171389 : Blo 1827615 6171389 := bstep (se 3 (by rfl) ⟨1157135, by rfl⟩ : syracuseStep 6171389 = 2314271) B2314271
theorem B5204969 : Blo 1827615 5204969 := bstep (se 2 (by rfl) ⟨1951863, by rfl⟩ : syracuseStep 5204969 = 3903727) B3903727
theorem B135253157 : Blo 1827615 135253157 := bstep (se 4 (by rfl) ⟨12679983, by rfl⟩ : syracuseStep 135253157 = 25359967) B25359967
theorem B33377447 : Blo 1827615 33377447 := bstep (se 1 (by rfl) ⟨25033085, by rfl⟩ : syracuseStep 33377447 = 50066171) B50066171
theorem B2313775 : Blo 1827615 2313775 := bstep (se 1 (by rfl) ⟨1735331, by rfl⟩ : syracuseStep 2313775 = 3470663) B3470663
theorem B5206427 : Blo 1827615 5206427 := bstep (se 1 (by rfl) ⟨3904820, by rfl⟩ : syracuseStep 5206427 = 7809641) B7809641
theorem B6173117 : Blo 1827615 6173117 := bstep (se 3 (by rfl) ⟨1157459, by rfl⟩ : syracuseStep 6173117 = 2314919) B2314919
theorem B5206655 : Blo 1827615 5206655 := bstep (se 1 (by rfl) ⟨3904991, by rfl⟩ : syracuseStep 5206655 = 7809983) B7809983
theorem B5206781 : Blo 1827615 5206781 := bstep (se 3 (by rfl) ⟨976271, by rfl⟩ : syracuseStep 5206781 = 1952543) B1952543
theorem B23761687 : Blo 1827615 23761687 := bstep (se 1 (by rfl) ⟨17821265, by rfl⟩ : syracuseStep 23761687 = 35642531) B35642531
theorem B3085087 : Blo 1827615 3085087 := bstep (se 1 (by rfl) ⟨2313815, by rfl⟩ : syracuseStep 3085087 = 4627631) B4627631
theorem B3470177 : Blo 1827615 3470177 := bstep (se 2 (by rfl) ⟨1301316, by rfl⟩ : syracuseStep 3470177 = 2602633) B2602633
theorem B4944851 : Blo 1827615 4944851 := bstep (se 1 (by rfl) ⟨3708638, by rfl⟩ : syracuseStep 4944851 = 7417277) B7417277
theorem B8910121 : Blo 1827615 8910121 := bstep (se 2 (by rfl) ⟨3341295, by rfl⟩ : syracuseStep 8910121 = 6682591) B6682591
theorem B2741801 : Blo 1827615 2741801 := bstep (se 2 (by rfl) ⟨1028175, by rfl⟩ : syracuseStep 2741801 = 2056351) B2056351
theorem B2742137 : Blo 1827615 2742137 := bstep (se 2 (by rfl) ⟨1028301, by rfl⟩ : syracuseStep 2742137 = 2056603) B2056603
theorem B84457475 : Blo 1827615 84457475 := bstep (se 1 (by rfl) ⟨63343106, by rfl⟩ : syracuseStep 84457475 = 126686213) B126686213
theorem B13178999 : Blo 1827615 13178999 := bstep (se 1 (by rfl) ⟨9884249, by rfl⟩ : syracuseStep 13178999 = 19768499) B19768499
theorem B5208239 : Blo 1827615 5208239 := bstep (se 1 (by rfl) ⟨3906179, by rfl⟩ : syracuseStep 5208239 = 7812359) B7812359
theorem B44472509 : Blo 1827615 44472509 := bstep (se 3 (by rfl) ⟨8338595, by rfl⟩ : syracuseStep 44472509 = 16677191) B16677191
theorem B2742719 : Blo 1827615 2742719 := bstep (se 1 (by rfl) ⟨2057039, by rfl⟩ : syracuseStep 2742719 = 4114079) B4114079
theorem B2742875 : Blo 1827615 2742875 := bstep (se 1 (by rfl) ⟨2057156, by rfl⟩ : syracuseStep 2742875 = 4114313) B4114313
theorem B7813741 : Blo 1827615 7813741 := bstep (se 3 (by rfl) ⟨1465076, by rfl⟩ : syracuseStep 7813741 = 2930153) B2930153
theorem B2742953 : Blo 1827615 2742953 := bstep (se 2 (by rfl) ⟨1028607, by rfl⟩ : syracuseStep 2742953 = 2057215) B2057215
theorem B2743289 : Blo 1827615 2743289 := bstep (se 2 (by rfl) ⟨1028733, by rfl⟩ : syracuseStep 2743289 = 2057467) B2057467
theorem B2743391 : Blo 1827615 2743391 := bstep (se 1 (by rfl) ⟨2057543, by rfl⟩ : syracuseStep 2743391 = 4115087) B4115087
theorem B20823155 : Blo 1827615 20823155 := bstep (se 1 (by rfl) ⟨15617366, by rfl⟩ : syracuseStep 20823155 = 31234733) B31234733
theorem B20045231 : Blo 1827615 20045231 := bstep (se 1 (by rfl) ⟨15033923, by rfl⟩ : syracuseStep 20045231 = 30067847) B30067847
theorem B5561789 : Blo 1827615 5561789 := bstep (se 3 (by rfl) ⟨1042835, by rfl⟩ : syracuseStep 5561789 = 2085671) B2085671
theorem B2743787 : Blo 1827615 2743787 := bstep (se 1 (by rfl) ⟨2057840, by rfl⟩ : syracuseStep 2743787 = 4115681) B4115681
theorem B16678507 : Blo 1827615 16678507 := bstep (se 1 (by rfl) ⟨12508880, by rfl⟩ : syracuseStep 16678507 = 25017761) B25017761
theorem B150159071 : Blo 1827615 150159071 := bstep (se 1 (by rfl) ⟨112619303, by rfl⟩ : syracuseStep 150159071 = 225238607) B225238607
theorem B100130579 : Blo 1827615 100130579 := bstep (se 1 (by rfl) ⟨75097934, by rfl⟩ : syracuseStep 100130579 = 150195869) B150195869
theorem B67641155 : Blo 1827615 67641155 := bstep (se 1 (by rfl) ⟨50730866, by rfl⟩ : syracuseStep 67641155 = 101461733) B101461733
theorem B89006525 : Blo 1827615 89006525 := bstep (se 3 (by rfl) ⟨16688723, by rfl⟩ : syracuseStep 89006525 = 33377447) B33377447
theorem B1827867 : Blo 1827615 1827867 := bstep (se 1 (by rfl) ⟨1370900, by rfl⟩ : syracuseStep 1827867 = 2741801) B2741801
theorem B4113449 : Blo 1827615 4113449 := bstep (se 2 (by rfl) ⟨1542543, by rfl⟩ : syracuseStep 4113449 = 3085087) B3085087
theorem B1828091 : Blo 1827615 1828091 := bstep (se 1 (by rfl) ⟨1371068, by rfl⟩ : syracuseStep 1828091 = 2742137) B2742137
theorem B56304983 : Blo 1827615 56304983 := bstep (se 1 (by rfl) ⟨42228737, by rfl⟩ : syracuseStep 56304983 = 84457475) B84457475
theorem B29648339 : Blo 1827615 29648339 := bstep (se 1 (by rfl) ⟨22236254, by rfl⟩ : syracuseStep 29648339 = 44472509) B44472509
theorem B1828479 : Blo 1827615 1828479 := bstep (se 1 (by rfl) ⟨1371359, by rfl⟩ : syracuseStep 1828479 = 2742719) B2742719
theorem B29673125 : Blo 1827615 29673125 := bstep (se 4 (by rfl) ⟨2781855, by rfl⟩ : syracuseStep 29673125 = 5563711) B5563711
theorem B11880161 : Blo 1827615 11880161 := bstep (se 2 (by rfl) ⟨4455060, by rfl⟩ : syracuseStep 11880161 = 8910121) B8910121
theorem B1828583 : Blo 1827615 1828583 := bstep (se 1 (by rfl) ⟨1371437, by rfl⟩ : syracuseStep 1828583 = 2742875) B2742875
theorem B1828635 : Blo 1827615 1828635 := bstep (se 1 (by rfl) ⟨1371476, by rfl⟩ : syracuseStep 1828635 = 2742953) B2742953
theorem B4114259 : Blo 1827615 4114259 := bstep (se 1 (by rfl) ⟨3085694, by rfl⟩ : syracuseStep 4114259 = 6171389) B6171389
theorem B1828859 : Blo 1827615 1828859 := bstep (se 1 (by rfl) ⟨1371644, by rfl⟩ : syracuseStep 1828859 = 2743289) B2743289
theorem B1828927 : Blo 1827615 1828927 := bstep (se 1 (by rfl) ⟨1371695, by rfl⟩ : syracuseStep 1828927 = 2743391) B2743391
theorem B13363487 : Blo 1827615 13363487 := bstep (se 1 (by rfl) ⟨10022615, by rfl⟩ : syracuseStep 13363487 = 20045231) B20045231
theorem B1829191 : Blo 1827615 1829191 := bstep (se 1 (by rfl) ⟨1371893, by rfl⟩ : syracuseStep 1829191 = 2743787) B2743787
theorem B1829583 : Blo 1827615 1829583 := bstep (se 1 (by rfl) ⟨1372187, by rfl⟩ : syracuseStep 1829583 = 2744375) B2744375
theorem B6171497 : Blo 1827615 6171497 := bstep (se 2 (by rfl) ⟨2314311, by rfl⟩ : syracuseStep 6171497 = 4628623) B4628623
theorem B7039943 : Blo 1827615 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B4115411 : Blo 1827615 4115411 := bstep (se 1 (by rfl) ⟨3086558, by rfl⟩ : syracuseStep 4115411 = 6173117) B6173117
theorem B2313451 : Blo 1827615 2313451 := bstep (se 1 (by rfl) ⟨1735088, by rfl⟩ : syracuseStep 2313451 = 3470177) B3470177
theorem B3296567 : Blo 1827615 3296567 := bstep (se 1 (by rfl) ⟨2472425, by rfl⟩ : syracuseStep 3296567 = 4944851) B4944851
theorem B200093003 : Blo 1827615 200093003 := bstep (se 1 (by rfl) ⟨150069752, by rfl⟩ : syracuseStep 200093003 = 300139505) B300139505
theorem B31682249 : Blo 1827615 31682249 := bstep (se 2 (by rfl) ⟨11880843, by rfl⟩ : syracuseStep 31682249 = 23761687) B23761687
theorem B14831437 : Blo 1827615 14831437 := bstep (se 3 (by rfl) ⟨2780894, by rfl⟩ : syracuseStep 14831437 = 5561789) B5561789
theorem B3960659 : Blo 1827615 3960659 := bstep (se 1 (by rfl) ⟨2970494, by rfl⟩ : syracuseStep 3960659 = 5940989) B5940989
theorem B6942631 : Blo 1827615 6942631 := bstep (se 1 (by rfl) ⟨5206973, by rfl⟩ : syracuseStep 6942631 = 10413947) B10413947
theorem B16723907 : Blo 1827615 16723907 := bstep (se 1 (by rfl) ⟨12542930, by rfl⟩ : syracuseStep 16723907 = 25085861) B25085861
theorem B4452383 : Blo 1827615 4452383 := bstep (se 1 (by rfl) ⟨3339287, by rfl⟩ : syracuseStep 4452383 = 6678575) B6678575
theorem B8785999 : Blo 1827615 8785999 := bstep (se 1 (by rfl) ⟨6589499, by rfl⟩ : syracuseStep 8785999 = 13178999) B13178999
theorem B2470123 : Blo 1827615 2470123 := bstep (se 1 (by rfl) ⟨1852592, by rfl⟩ : syracuseStep 2470123 = 3705185) B3705185
theorem B433533383 : Blo 1827615 433533383 := bstep (se 1 (by rfl) ⟨325150037, by rfl⟩ : syracuseStep 433533383 = 650300075) B650300075
theorem B6173225 : Blo 1827615 6173225 := bstep (se 2 (by rfl) ⟨2314959, by rfl⟩ : syracuseStep 6173225 = 4629919) B4629919
theorem B3469979 : Blo 1827615 3469979 := bstep (se 1 (by rfl) ⟨2602484, by rfl⟩ : syracuseStep 3469979 = 5204969) B5204969
theorem B3085033 : Blo 1827615 3085033 := bstep (se 2 (by rfl) ⟨1156887, by rfl⟩ : syracuseStep 3085033 = 2313775) B2313775
theorem B13882103 : Blo 1827615 13882103 := bstep (se 1 (by rfl) ⟨10411577, by rfl⟩ : syracuseStep 13882103 = 20823155) B20823155
theorem B22238009 : Blo 1827615 22238009 := bstep (se 2 (by rfl) ⟨8339253, by rfl⟩ : syracuseStep 22238009 = 16678507) B16678507
theorem B35148917 : Blo 1827615 35148917 := bstep (se 5 (by rfl) ⟨1647605, by rfl⟩ : syracuseStep 35148917 = 3295211) B3295211
theorem B66753719 : Blo 1827615 66753719 := bstep (se 1 (by rfl) ⟨50065289, by rfl⟩ : syracuseStep 66753719 = 100130579) B100130579
theorem B45094103 : Blo 1827615 45094103 := bstep (se 1 (by rfl) ⟨33820577, by rfl⟩ : syracuseStep 45094103 = 67641155) B67641155
theorem B3470951 : Blo 1827615 3470951 := bstep (se 1 (by rfl) ⟨2603213, by rfl⟩ : syracuseStep 3470951 = 5206427) B5206427
theorem B3471103 : Blo 1827615 3471103 := bstep (se 1 (by rfl) ⟨2603327, by rfl⟩ : syracuseStep 3471103 = 5206655) B5206655
theorem B3471187 : Blo 1827615 3471187 := bstep (se 1 (by rfl) ⟨2603390, by rfl⟩ : syracuseStep 3471187 = 5206781) B5206781
theorem B3086383 : Blo 1827615 3086383 := bstep (se 1 (by rfl) ⟨2314787, by rfl⟩ : syracuseStep 3086383 = 4629575) B4629575
theorem B10418321 : Blo 1827615 10418321 := bstep (se 2 (by rfl) ⟨3906870, by rfl⟩ : syracuseStep 10418321 = 7813741) B7813741
theorem B29644967 : Blo 1827615 29644967 := bstep (se 1 (by rfl) ⟨22233725, by rfl⟩ : syracuseStep 29644967 = 44467451) B44467451
theorem B2742455 : Blo 1827615 2742455 := bstep (se 1 (by rfl) ⟨2056841, by rfl⟩ : syracuseStep 2742455 = 4113683) B4113683
theorem B7412411 : Blo 1827615 7412411 := bstep (se 1 (by rfl) ⟨5559308, by rfl⟩ : syracuseStep 7412411 = 11118617) B11118617
theorem B2743049 : Blo 1827615 2743049 := bstep (se 2 (by rfl) ⟨1028643, by rfl⟩ : syracuseStep 2743049 = 2057287) B2057287
theorem B3472159 : Blo 1827615 3472159 := bstep (se 1 (by rfl) ⟨2604119, by rfl⟩ : syracuseStep 3472159 = 5208239) B5208239
theorem B1442700341 : Blo 1827615 1442700341 := bstep (se 5 (by rfl) ⟨67626578, by rfl⟩ : syracuseStep 1442700341 = 135253157) B135253157
theorem B100106047 : Blo 1827615 100106047 := bstep (se 1 (by rfl) ⟨75079535, by rfl⟩ : syracuseStep 100106047 = 150159071) B150159071
theorem B289022255 : Blo 1827615 289022255 := bstep (se 1 (by rfl) ⟨216766691, by rfl⟩ : syracuseStep 289022255 = 433533383) B433533383
theorem B3293497 : Blo 1827615 3293497 := bstep (se 2 (by rfl) ⟨1235061, by rfl⟩ : syracuseStep 3293497 = 2470123) B2470123
theorem B46858661 : Blo 1827615 46858661 := bstep (se 4 (by rfl) ⟨4392999, by rfl⟩ : syracuseStep 46858661 = 8785999) B8785999
theorem B37536655 : Blo 1827615 37536655 := bstep (se 1 (by rfl) ⟨28152491, by rfl⟩ : syracuseStep 37536655 = 56304983) B56304983
theorem B4113377 : Blo 1827615 4113377 := bstep (se 2 (by rfl) ⟨1542516, by rfl⟩ : syracuseStep 4113377 = 3085033) B3085033
theorem B4629545 : Blo 1827615 4629545 := bstep (se 2 (by rfl) ⟨1736079, by rfl⟩ : syracuseStep 4629545 = 3472159) B3472159
theorem B1828303 : Blo 1827615 1828303 := bstep (se 1 (by rfl) ⟨1371227, by rfl⟩ : syracuseStep 1828303 = 2742455) B2742455
theorem B4941607 : Blo 1827615 4941607 := bstep (se 1 (by rfl) ⟨3706205, by rfl⟩ : syracuseStep 4941607 = 7412411) B7412411
theorem B1828699 : Blo 1827615 1828699 := bstep (se 1 (by rfl) ⟨1371524, by rfl⟩ : syracuseStep 1828699 = 2743049) B2743049
theorem B4114331 : Blo 1827615 4114331 := bstep (se 1 (by rfl) ⟨3085748, by rfl⟩ : syracuseStep 4114331 = 6171497) B6171497
theorem B961800227 : Blo 1827615 961800227 := bstep (se 1 (by rfl) ⟨721350170, by rfl⟩ : syracuseStep 961800227 = 1442700341) B1442700341
theorem B2197711 : Blo 1827615 2197711 := bstep (se 1 (by rfl) ⟨1648283, by rfl⟩ : syracuseStep 2197711 = 3296567) B3296567
theorem B133474729 : Blo 1827615 133474729 := bstep (se 2 (by rfl) ⟨50053023, by rfl⟩ : syracuseStep 133474729 = 100106047) B100106047
theorem B21121499 : Blo 1827615 21121499 := bstep (se 1 (by rfl) ⟨15841124, by rfl⟩ : syracuseStep 21121499 = 31682249) B31682249
theorem B2640439 : Blo 1827615 2640439 := bstep (se 1 (by rfl) ⟨1980329, by rfl⟩ : syracuseStep 2640439 = 3960659) B3960659
theorem B2968255 : Blo 1827615 2968255 := bstep (se 1 (by rfl) ⟨2226191, by rfl⟩ : syracuseStep 2968255 = 4452383) B4452383
theorem B4115177 : Blo 1827615 4115177 := bstep (se 2 (by rfl) ⟨1543191, by rfl⟩ : syracuseStep 4115177 = 3086383) B3086383
theorem B59337683 : Blo 1827615 59337683 := bstep (se 1 (by rfl) ⟨44503262, by rfl⟩ : syracuseStep 59337683 = 89006525) B89006525
theorem B4115483 : Blo 1827615 4115483 := bstep (se 1 (by rfl) ⟨3086612, by rfl⟩ : syracuseStep 4115483 = 6173225) B6173225
theorem B23432611 : Blo 1827615 23432611 := bstep (se 1 (by rfl) ⟨17574458, by rfl⟩ : syracuseStep 23432611 = 35148917) B35148917
theorem B44502479 : Blo 1827615 44502479 := bstep (se 1 (by rfl) ⟨33376859, by rfl⟩ : syracuseStep 44502479 = 66753719) B66753719
theorem B19763311 : Blo 1827615 19763311 := bstep (se 1 (by rfl) ⟨14822483, by rfl⟩ : syracuseStep 19763311 = 29644967) B29644967
theorem B8908991 : Blo 1827615 8908991 := bstep (se 1 (by rfl) ⟨6681743, by rfl⟩ : syracuseStep 8908991 = 13363487) B13363487
theorem B3084601 : Blo 1827615 3084601 := bstep (se 2 (by rfl) ⟨1156725, by rfl⟩ : syracuseStep 3084601 = 2313451) B2313451
theorem B9253277 : Blo 1827615 9253277 := bstep (se 3 (by rfl) ⟨1734989, by rfl⟩ : syracuseStep 9253277 = 3469979) B3469979
theorem B133395335 : Blo 1827615 133395335 := bstep (se 1 (by rfl) ⟨100046501, by rfl⟩ : syracuseStep 133395335 = 200093003) B200093003
theorem B9254735 : Blo 1827615 9254735 := bstep (se 1 (by rfl) ⟨6941051, by rfl⟩ : syracuseStep 9254735 = 13882103) B13882103
theorem B14825339 : Blo 1827615 14825339 := bstep (se 1 (by rfl) ⟨11119004, by rfl⟩ : syracuseStep 14825339 = 22238009) B22238009
theorem B2742299 : Blo 1827615 2742299 := bstep (se 1 (by rfl) ⟨2056724, by rfl⟩ : syracuseStep 2742299 = 4113449) B4113449
theorem B30062735 : Blo 1827615 30062735 := bstep (se 1 (by rfl) ⟨22547051, by rfl⟩ : syracuseStep 30062735 = 45094103) B45094103
theorem B19765559 : Blo 1827615 19765559 := bstep (se 1 (by rfl) ⟨14824169, by rfl⟩ : syracuseStep 19765559 = 29648339) B29648339
theorem B19782083 : Blo 1827615 19782083 := bstep (se 1 (by rfl) ⟨14836562, by rfl⟩ : syracuseStep 19782083 = 29673125) B29673125
theorem B7920107 : Blo 1827615 7920107 := bstep (se 1 (by rfl) ⟨5940080, by rfl⟩ : syracuseStep 7920107 = 11880161) B11880161
theorem B2742839 : Blo 1827615 2742839 := bstep (se 1 (by rfl) ⟨2057129, by rfl⟩ : syracuseStep 2742839 = 4114259) B4114259
theorem B6945547 : Blo 1827615 6945547 := bstep (se 1 (by rfl) ⟨5209160, by rfl⟩ : syracuseStep 6945547 = 10418321) B10418321
theorem B9255869 : Blo 1827615 9255869 := bstep (se 3 (by rfl) ⟨1735475, by rfl⟩ : syracuseStep 9255869 = 3470951) B3470951
theorem B4693295 : Blo 1827615 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B2743607 : Blo 1827615 2743607 := bstep (se 1 (by rfl) ⟨2057705, by rfl⟩ : syracuseStep 2743607 = 4115411) B4115411
theorem B4628137 : Blo 1827615 4628137 := bstep (se 2 (by rfl) ⟨1735551, by rfl⟩ : syracuseStep 4628137 = 3471103) B3471103
theorem B19775249 : Blo 1827615 19775249 := bstep (se 2 (by rfl) ⟨7415718, by rfl⟩ : syracuseStep 19775249 = 14831437) B14831437
theorem B4628249 : Blo 1827615 4628249 := bstep (se 2 (by rfl) ⟨1735593, by rfl⟩ : syracuseStep 4628249 = 3471187) B3471187
theorem B9256841 : Blo 1827615 9256841 := bstep (se 2 (by rfl) ⟨3471315, by rfl⟩ : syracuseStep 9256841 = 6942631) B6942631
theorem B11149271 : Blo 1827615 11149271 := bstep (se 1 (by rfl) ⟨8361953, by rfl⟩ : syracuseStep 11149271 = 16723907) B16723907
theorem B5939327 : Blo 1827615 5939327 := bstep (se 1 (by rfl) ⟨4454495, by rfl⟩ : syracuseStep 5939327 = 8908991) B8908991
theorem B6168851 : Blo 1827615 6168851 := bstep (se 1 (by rfl) ⟨4626638, by rfl⟩ : syracuseStep 6168851 = 9253277) B9253277
theorem B14082341 : Blo 1827615 14082341 := bstep (se 4 (by rfl) ⟨1320219, by rfl⟩ : syracuseStep 14082341 = 2640439) B2640439
theorem B4391329 : Blo 1827615 4391329 := bstep (se 2 (by rfl) ⟨1646748, by rfl⟩ : syracuseStep 4391329 = 3293497) B3293497
theorem B4112801 : Blo 1827615 4112801 := bstep (se 2 (by rfl) ⟨1542300, by rfl⟩ : syracuseStep 4112801 = 3084601) B3084601
theorem B52708157 : Blo 1827615 52708157 := bstep (se 3 (by rfl) ⟨9882779, by rfl⟩ : syracuseStep 52708157 = 19765559) B19765559
theorem B3957673 : Blo 1827615 3957673 := bstep (se 2 (by rfl) ⟨1484127, by rfl⟩ : syracuseStep 3957673 = 2968255) B2968255
theorem B6169823 : Blo 1827615 6169823 := bstep (se 1 (by rfl) ⟨4627367, by rfl⟩ : syracuseStep 6169823 = 9254735) B9254735
theorem B1828199 : Blo 1827615 1828199 := bstep (se 1 (by rfl) ⟨1371149, by rfl⟩ : syracuseStep 1828199 = 2742299) B2742299
theorem B1828559 : Blo 1827615 1828559 := bstep (se 1 (by rfl) ⟨1371419, by rfl⟩ : syracuseStep 1828559 = 2742839) B2742839
theorem B6170579 : Blo 1827615 6170579 := bstep (se 1 (by rfl) ⟨4627934, by rfl⟩ : syracuseStep 6170579 = 9255869) B9255869
theorem B1829071 : Blo 1827615 1829071 := bstep (se 1 (by rfl) ⟨1371803, by rfl⟩ : syracuseStep 1829071 = 2743607) B2743607
theorem B6170849 : Blo 1827615 6170849 := bstep (se 2 (by rfl) ⟨2314068, by rfl⟩ : syracuseStep 6170849 = 4628137) B4628137
theorem B6588809 : Blo 1827615 6588809 := bstep (se 2 (by rfl) ⟨2470803, by rfl⟩ : syracuseStep 6588809 = 4941607) B4941607
theorem B13183499 : Blo 1827615 13183499 := bstep (se 1 (by rfl) ⟨9887624, by rfl⟩ : syracuseStep 13183499 = 19775249) B19775249
theorem B6171227 : Blo 1827615 6171227 := bstep (se 1 (by rfl) ⟨4628420, by rfl⟩ : syracuseStep 6171227 = 9256841) B9256841
theorem B7432847 : Blo 1827615 7432847 := bstep (se 1 (by rfl) ⟨5574635, by rfl⟩ : syracuseStep 7432847 = 11149271) B11149271
theorem B31239107 : Blo 1827615 31239107 := bstep (se 1 (by rfl) ⟨23429330, by rfl⟩ : syracuseStep 31239107 = 46858661) B46858661
theorem B177966305 : Blo 1827615 177966305 := bstep (se 2 (by rfl) ⟨66737364, by rfl⟩ : syracuseStep 177966305 = 133474729) B133474729
theorem B9260729 : Blo 1827615 9260729 := bstep (se 2 (by rfl) ⟨3472773, by rfl⟩ : syracuseStep 9260729 = 6945547) B6945547
theorem B50048873 : Blo 1827615 50048873 := bstep (se 2 (by rfl) ⟨18768327, by rfl⟩ : syracuseStep 50048873 = 37536655) B37536655
theorem B9883559 : Blo 1827615 9883559 := bstep (se 1 (by rfl) ⟨7412669, by rfl⟩ : syracuseStep 9883559 = 14825339) B14825339
theorem B641200151 : Blo 1827615 641200151 := bstep (se 1 (by rfl) ⟨480900113, by rfl⟩ : syracuseStep 641200151 = 961800227) B961800227
theorem B20041823 : Blo 1827615 20041823 := bstep (se 1 (by rfl) ⟨15031367, by rfl⟩ : syracuseStep 20041823 = 30062735) B30062735
theorem B5280071 : Blo 1827615 5280071 := bstep (se 1 (by rfl) ⟨3960053, by rfl⟩ : syracuseStep 5280071 = 7920107) B7920107
theorem B29668319 : Blo 1827615 29668319 := bstep (se 1 (by rfl) ⟨22251239, by rfl⟩ : syracuseStep 29668319 = 44502479) B44502479
theorem B3085499 : Blo 1827615 3085499 := bstep (se 1 (by rfl) ⟨2314124, by rfl⟩ : syracuseStep 3085499 = 4628249) B4628249
theorem B26351081 : Blo 1827615 26351081 := bstep (se 2 (by rfl) ⟨9881655, by rfl⟩ : syracuseStep 26351081 = 19763311) B19763311
theorem B192681503 : Blo 1827615 192681503 := bstep (se 1 (by rfl) ⟨144511127, by rfl⟩ : syracuseStep 192681503 = 289022255) B289022255
theorem B88930223 : Blo 1827615 88930223 := bstep (se 1 (by rfl) ⟨66697667, by rfl⟩ : syracuseStep 88930223 = 133395335) B133395335
theorem B2742251 : Blo 1827615 2742251 := bstep (se 1 (by rfl) ⟨2056688, by rfl⟩ : syracuseStep 2742251 = 4113377) B4113377
theorem B3086363 : Blo 1827615 3086363 := bstep (se 1 (by rfl) ⟨2314772, by rfl⟩ : syracuseStep 3086363 = 4629545) B4629545
theorem B11721125 : Blo 1827615 11721125 := bstep (se 4 (by rfl) ⟨1098855, by rfl⟩ : syracuseStep 11721125 = 2197711) B2197711
theorem B2742887 : Blo 1827615 2742887 := bstep (se 1 (by rfl) ⟨2057165, by rfl⟩ : syracuseStep 2742887 = 4114331) B4114331
theorem B13188055 : Blo 1827615 13188055 := bstep (se 1 (by rfl) ⟨9891041, by rfl⟩ : syracuseStep 13188055 = 19782083) B19782083
theorem B14080999 : Blo 1827615 14080999 := bstep (se 1 (by rfl) ⟨10560749, by rfl⟩ : syracuseStep 14080999 = 21121499) B21121499
theorem B2743451 : Blo 1827615 2743451 := bstep (se 1 (by rfl) ⟨2057588, by rfl⟩ : syracuseStep 2743451 = 4115177) B4115177
theorem B31243481 : Blo 1827615 31243481 := bstep (se 2 (by rfl) ⟨11716305, by rfl⟩ : syracuseStep 31243481 = 23432611) B23432611
theorem B39558455 : Blo 1827615 39558455 := bstep (se 1 (by rfl) ⟨29668841, by rfl⟩ : syracuseStep 39558455 = 59337683) B59337683
theorem B2743655 : Blo 1827615 2743655 := bstep (se 1 (by rfl) ⟨2057741, by rfl⟩ : syracuseStep 2743655 = 4115483) B4115483
theorem B3128863 : Blo 1827615 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B427466767 : Blo 1827615 427466767 := bstep (se 1 (by rfl) ⟨320600075, by rfl⟩ : syracuseStep 427466767 = 641200151) B641200151
theorem B13361215 : Blo 1827615 13361215 := bstep (se 1 (by rfl) ⟨10020911, by rfl⟩ : syracuseStep 13361215 = 20041823) B20041823
theorem B4112567 : Blo 1827615 4112567 := bstep (se 1 (by rfl) ⟨3084425, by rfl⟩ : syracuseStep 4112567 = 6168851) B6168851
theorem B37552909 : Blo 1827615 37552909 := bstep (se 3 (by rfl) ⟨7041170, by rfl⟩ : syracuseStep 37552909 = 14082341) B14082341
theorem B2056999 : Blo 1827615 2056999 := bstep (se 1 (by rfl) ⟨1542749, by rfl⟩ : syracuseStep 2056999 = 3085499) B3085499
theorem B4113215 : Blo 1827615 4113215 := bstep (se 1 (by rfl) ⟨3084911, by rfl⟩ : syracuseStep 4113215 = 6169823) B6169823
theorem B5276897 : Blo 1827615 5276897 := bstep (se 2 (by rfl) ⟨1978836, by rfl⟩ : syracuseStep 5276897 = 3957673) B3957673
theorem B59286815 : Blo 1827615 59286815 := bstep (se 1 (by rfl) ⟨44465111, by rfl⟩ : syracuseStep 59286815 = 88930223) B88930223
theorem B4113719 : Blo 1827615 4113719 := bstep (se 1 (by rfl) ⟨3085289, by rfl⟩ : syracuseStep 4113719 = 6170579) B6170579
theorem B1828167 : Blo 1827615 1828167 := bstep (se 1 (by rfl) ⟨1371125, by rfl⟩ : syracuseStep 1828167 = 2742251) B2742251
theorem B2057575 : Blo 1827615 2057575 := bstep (se 1 (by rfl) ⟨1543181, by rfl⟩ : syracuseStep 2057575 = 3086363) B3086363
theorem B4113899 : Blo 1827615 4113899 := bstep (se 1 (by rfl) ⟨3085424, by rfl⟩ : syracuseStep 4113899 = 6170849) B6170849
theorem B4392539 : Blo 1827615 4392539 := bstep (se 1 (by rfl) ⟨3294404, by rfl⟩ : syracuseStep 4392539 = 6588809) B6588809
theorem B4114151 : Blo 1827615 4114151 := bstep (se 1 (by rfl) ⟨3085613, by rfl⟩ : syracuseStep 4114151 = 6171227) B6171227
theorem B1828591 : Blo 1827615 1828591 := bstep (se 1 (by rfl) ⟨1371443, by rfl⟩ : syracuseStep 1828591 = 2742887) B2742887
theorem B20826071 : Blo 1827615 20826071 := bstep (se 1 (by rfl) ⟨15619553, by rfl⟩ : syracuseStep 20826071 = 31239107) B31239107
theorem B4171817 : Blo 1827615 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B1828967 : Blo 1827615 1828967 := bstep (se 1 (by rfl) ⟨1371725, by rfl⟩ : syracuseStep 1828967 = 2743451) B2743451
theorem B26372303 : Blo 1827615 26372303 := bstep (se 1 (by rfl) ⟨19779227, by rfl⟩ : syracuseStep 26372303 = 39558455) B39558455
theorem B1829103 : Blo 1827615 1829103 := bstep (se 1 (by rfl) ⟨1371827, by rfl⟩ : syracuseStep 1829103 = 2743655) B2743655
theorem B6589039 : Blo 1827615 6589039 := bstep (se 1 (by rfl) ⟨4941779, by rfl⟩ : syracuseStep 6589039 = 9883559) B9883559
theorem B3959551 : Blo 1827615 3959551 := bstep (se 1 (by rfl) ⟨2969663, by rfl⟩ : syracuseStep 3959551 = 5939327) B5939327
theorem B35138771 : Blo 1827615 35138771 := bstep (se 1 (by rfl) ⟨26354078, by rfl⟩ : syracuseStep 35138771 = 52708157) B52708157
theorem B19778879 : Blo 1827615 19778879 := bstep (se 1 (by rfl) ⟨14834159, by rfl⟩ : syracuseStep 19778879 = 29668319) B29668319
theorem B17567387 : Blo 1827615 17567387 := bstep (se 1 (by rfl) ⟨13175540, by rfl⟩ : syracuseStep 17567387 = 26351081) B26351081
theorem B128454335 : Blo 1827615 128454335 := bstep (se 1 (by rfl) ⟨96340751, by rfl⟩ : syracuseStep 128454335 = 192681503) B192681503
theorem B17584073 : Blo 1827615 17584073 := bstep (se 2 (by rfl) ⟨6594027, by rfl⟩ : syracuseStep 17584073 = 13188055) B13188055
theorem B20828987 : Blo 1827615 20828987 := bstep (se 1 (by rfl) ⟨15621740, by rfl⟩ : syracuseStep 20828987 = 31243481) B31243481
theorem B6173819 : Blo 1827615 6173819 := bstep (se 1 (by rfl) ⟨4630364, by rfl⟩ : syracuseStep 6173819 = 9260729) B9260729
theorem B2741867 : Blo 1827615 2741867 := bstep (se 1 (by rfl) ⟨2056400, by rfl⟩ : syracuseStep 2741867 = 4112801) B4112801
theorem B5855105 : Blo 1827615 5855105 := bstep (se 2 (by rfl) ⟨2195664, by rfl⟩ : syracuseStep 5855105 = 4391329) B4391329
theorem B14080189 : Blo 1827615 14080189 := bstep (se 3 (by rfl) ⟨2640035, by rfl⟩ : syracuseStep 14080189 = 5280071) B5280071
theorem B18774665 : Blo 1827615 18774665 := bstep (se 2 (by rfl) ⟨7040499, by rfl⟩ : syracuseStep 18774665 = 14080999) B14080999
theorem B7814083 : Blo 1827615 7814083 := bstep (se 1 (by rfl) ⟨5860562, by rfl⟩ : syracuseStep 7814083 = 11721125) B11721125
theorem B8788999 : Blo 1827615 8788999 := bstep (se 1 (by rfl) ⟨6591749, by rfl⟩ : syracuseStep 8788999 = 13183499) B13183499
theorem B4955231 : Blo 1827615 4955231 := bstep (se 1 (by rfl) ⟨3716423, by rfl⟩ : syracuseStep 4955231 = 7432847) B7432847
theorem B118644203 : Blo 1827615 118644203 := bstep (se 1 (by rfl) ⟨88983152, by rfl⟩ : syracuseStep 118644203 = 177966305) B177966305
theorem B33365915 : Blo 1827615 33365915 := bstep (se 1 (by rfl) ⟨25024436, by rfl⟩ : syracuseStep 33365915 = 50048873) B50048873
theorem B13213949 : Blo 1827615 13213949 := bstep (se 3 (by rfl) ⟨2477615, by rfl⟩ : syracuseStep 13213949 = 4955231) B4955231
theorem B13885991 : Blo 1827615 13885991 := bstep (se 1 (by rfl) ⟨10414493, by rfl⟩ : syracuseStep 13885991 = 20828987) B20828987
theorem B50070545 : Blo 1827615 50070545 := bstep (se 2 (by rfl) ⟨18776454, by rfl⟩ : syracuseStep 50070545 = 37552909) B37552909
theorem B1827911 : Blo 1827615 1827911 := bstep (se 1 (by rfl) ⟨1370933, by rfl⟩ : syracuseStep 1827911 = 2741867) B2741867
theorem B17581535 : Blo 1827615 17581535 := bstep (se 1 (by rfl) ⟨13186151, by rfl⟩ : syracuseStep 17581535 = 26372303) B26372303
theorem B79096135 : Blo 1827615 79096135 := bstep (se 1 (by rfl) ⟨59322101, by rfl⟩ : syracuseStep 79096135 = 118644203) B118644203
theorem B22243943 : Blo 1827615 22243943 := bstep (se 1 (by rfl) ⟨16682957, by rfl⟩ : syracuseStep 22243943 = 33365915) B33365915
theorem B4115879 : Blo 1827615 4115879 := bstep (se 1 (by rfl) ⟨3086909, by rfl⟩ : syracuseStep 4115879 = 6173819) B6173819
theorem B8785385 : Blo 1827615 8785385 := bstep (se 2 (by rfl) ⟨3294519, by rfl⟩ : syracuseStep 8785385 = 6589039) B6589039
theorem B3517931 : Blo 1827615 3517931 := bstep (se 1 (by rfl) ⟨2638448, by rfl⟩ : syracuseStep 3517931 = 5276897) B5276897
theorem B5279401 : Blo 1827615 5279401 := bstep (se 2 (by rfl) ⟨1979775, by rfl⟩ : syracuseStep 5279401 = 3959551) B3959551
theorem B2928359 : Blo 1827615 2928359 := bstep (se 1 (by rfl) ⟨2196269, by rfl⟩ : syracuseStep 2928359 = 4392539) B4392539
theorem B3903403 : Blo 1827615 3903403 := bstep (se 1 (by rfl) ⟨2927552, by rfl⟩ : syracuseStep 3903403 = 5855105) B5855105
theorem B11718665 : Blo 1827615 11718665 := bstep (se 2 (by rfl) ⟨4394499, by rfl⟩ : syracuseStep 11718665 = 8788999) B8788999
theorem B2781211 : Blo 1827615 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B23425847 : Blo 1827615 23425847 := bstep (se 1 (by rfl) ⟨17569385, by rfl⟩ : syracuseStep 23425847 = 35138771) B35138771
theorem B13185919 : Blo 1827615 13185919 := bstep (se 1 (by rfl) ⟨9889439, by rfl⟩ : syracuseStep 13185919 = 19778879) B19778879
theorem B11711591 : Blo 1827615 11711591 := bstep (se 1 (by rfl) ⟨8783693, by rfl⟩ : syracuseStep 11711591 = 17567387) B17567387
theorem B85636223 : Blo 1827615 85636223 := bstep (se 1 (by rfl) ⟨64227167, by rfl⟩ : syracuseStep 85636223 = 128454335) B128454335
theorem B569955689 : Blo 1827615 569955689 := bstep (se 2 (by rfl) ⟨213733383, by rfl⟩ : syracuseStep 569955689 = 427466767) B427466767
theorem B17814953 : Blo 1827615 17814953 := bstep (se 2 (by rfl) ⟨6680607, by rfl⟩ : syracuseStep 17814953 = 13361215) B13361215
theorem B2741711 : Blo 1827615 2741711 := bstep (se 1 (by rfl) ⟨2056283, by rfl⟩ : syracuseStep 2741711 = 4112567) B4112567
theorem B18773585 : Blo 1827615 18773585 := bstep (se 2 (by rfl) ⟨7040094, by rfl⟩ : syracuseStep 18773585 = 14080189) B14080189
theorem B2742143 : Blo 1827615 2742143 := bstep (se 1 (by rfl) ⟨2056607, by rfl⟩ : syracuseStep 2742143 = 4113215) B4113215
theorem B39524543 : Blo 1827615 39524543 := bstep (se 1 (by rfl) ⟨29643407, by rfl⟩ : syracuseStep 39524543 = 59286815) B59286815
theorem B2742479 : Blo 1827615 2742479 := bstep (se 1 (by rfl) ⟨2056859, by rfl⟩ : syracuseStep 2742479 = 4113719) B4113719
theorem B2742599 : Blo 1827615 2742599 := bstep (se 1 (by rfl) ⟨2056949, by rfl⟩ : syracuseStep 2742599 = 4113899) B4113899
theorem B2742665 : Blo 1827615 2742665 := bstep (se 2 (by rfl) ⟨1028499, by rfl⟩ : syracuseStep 2742665 = 2056999) B2056999
theorem B2742767 : Blo 1827615 2742767 := bstep (se 1 (by rfl) ⟨2057075, by rfl⟩ : syracuseStep 2742767 = 4114151) B4114151
theorem B10418777 : Blo 1827615 10418777 := bstep (se 2 (by rfl) ⟨3907041, by rfl⟩ : syracuseStep 10418777 = 7814083) B7814083
theorem B13884047 : Blo 1827615 13884047 := bstep (se 1 (by rfl) ⟨10413035, by rfl⟩ : syracuseStep 13884047 = 20826071) B20826071
theorem B12516443 : Blo 1827615 12516443 := bstep (se 1 (by rfl) ⟨9387332, by rfl⟩ : syracuseStep 12516443 = 18774665) B18774665
theorem B2743433 : Blo 1827615 2743433 := bstep (se 2 (by rfl) ⟨1028787, by rfl⟩ : syracuseStep 2743433 = 2057575) B2057575
theorem B11722715 : Blo 1827615 11722715 := bstep (se 1 (by rfl) ⟨8792036, by rfl⟩ : syracuseStep 11722715 = 17584073) B17584073
theorem B9257327 : Blo 1827615 9257327 := bstep (se 1 (by rfl) ⟨6942995, by rfl⟩ : syracuseStep 9257327 = 13885991) B13885991
theorem B7807727 : Blo 1827615 7807727 := bstep (se 1 (by rfl) ⟨5855795, by rfl⟩ : syracuseStep 7807727 = 11711591) B11711591
theorem B57090815 : Blo 1827615 57090815 := bstep (se 1 (by rfl) ⟨42818111, by rfl⟩ : syracuseStep 57090815 = 85636223) B85636223
theorem B28156805 : Blo 1827615 28156805 := bstep (se 4 (by rfl) ⟨2639700, by rfl⟩ : syracuseStep 28156805 = 5279401) B5279401
theorem B379970459 : Blo 1827615 379970459 := bstep (se 1 (by rfl) ⟨284977844, by rfl⟩ : syracuseStep 379970459 = 569955689) B569955689
theorem B1827807 : Blo 1827615 1827807 := bstep (se 1 (by rfl) ⟨1370855, by rfl⟩ : syracuseStep 1827807 = 2741711) B2741711
theorem B17581225 : Blo 1827615 17581225 := bstep (se 2 (by rfl) ⟨6592959, by rfl⟩ : syracuseStep 17581225 = 13185919) B13185919
theorem B1828095 : Blo 1827615 1828095 := bstep (se 1 (by rfl) ⟨1371071, by rfl⟩ : syracuseStep 1828095 = 2742143) B2742143
theorem B9381149 : Blo 1827615 9381149 := bstep (se 3 (by rfl) ⟨1758965, by rfl⟩ : syracuseStep 9381149 = 3517931) B3517931
theorem B1828319 : Blo 1827615 1828319 := bstep (se 1 (by rfl) ⟨1371239, by rfl⟩ : syracuseStep 1828319 = 2742479) B2742479
theorem B1828399 : Blo 1827615 1828399 := bstep (se 1 (by rfl) ⟨1371299, by rfl⟩ : syracuseStep 1828399 = 2742599) B2742599
theorem B1828443 : Blo 1827615 1828443 := bstep (se 1 (by rfl) ⟨1371332, by rfl⟩ : syracuseStep 1828443 = 2742665) B2742665
theorem B1828511 : Blo 1827615 1828511 := bstep (se 1 (by rfl) ⟨1371383, by rfl⟩ : syracuseStep 1828511 = 2742767) B2742767
theorem B7808957 : Blo 1827615 7808957 := bstep (se 3 (by rfl) ⟨1464179, by rfl⟩ : syracuseStep 7808957 = 2928359) B2928359
theorem B1828955 : Blo 1827615 1828955 := bstep (se 1 (by rfl) ⟨1371716, by rfl⟩ : syracuseStep 1828955 = 2743433) B2743433
theorem B5204537 : Blo 1827615 5204537 := bstep (se 2 (by rfl) ⟨1951701, by rfl⟩ : syracuseStep 5204537 = 3903403) B3903403
theorem B15617231 : Blo 1827615 15617231 := bstep (se 1 (by rfl) ⟨11712923, by rfl⟩ : syracuseStep 15617231 = 23425847) B23425847
theorem B35237197 : Blo 1827615 35237197 := bstep (se 3 (by rfl) ⟨6606974, by rfl⟩ : syracuseStep 35237197 = 13213949) B13213949
theorem B26349695 : Blo 1827615 26349695 := bstep (se 1 (by rfl) ⟨19762271, by rfl⟩ : syracuseStep 26349695 = 39524543) B39524543
theorem B8344295 : Blo 1827615 8344295 := bstep (se 1 (by rfl) ⟨6258221, by rfl⟩ : syracuseStep 8344295 = 12516443) B12516443
theorem B7812443 : Blo 1827615 7812443 := bstep (se 1 (by rfl) ⟨5859332, by rfl⟩ : syracuseStep 7812443 = 11718665) B11718665
theorem B3708281 : Blo 1827615 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B105461513 : Blo 1827615 105461513 := bstep (se 2 (by rfl) ⟨39548067, by rfl⟩ : syracuseStep 105461513 = 79096135) B79096135
theorem B33380363 : Blo 1827615 33380363 := bstep (se 1 (by rfl) ⟨25035272, by rfl⟩ : syracuseStep 33380363 = 50070545) B50070545
theorem B11876635 : Blo 1827615 11876635 := bstep (se 1 (by rfl) ⟨8907476, by rfl⟩ : syracuseStep 11876635 = 17814953) B17814953
theorem B11721023 : Blo 1827615 11721023 := bstep (se 1 (by rfl) ⟨8790767, by rfl⟩ : syracuseStep 11721023 = 17581535) B17581535
theorem B12515723 : Blo 1827615 12515723 := bstep (se 1 (by rfl) ⟨9386792, by rfl⟩ : syracuseStep 12515723 = 18773585) B18773585
theorem B59317181 : Blo 1827615 59317181 := bstep (se 3 (by rfl) ⟨11121971, by rfl⟩ : syracuseStep 59317181 = 22243943) B22243943
theorem B6945851 : Blo 1827615 6945851 := bstep (se 1 (by rfl) ⟨5209388, by rfl⟩ : syracuseStep 6945851 = 10418777) B10418777
theorem B9256031 : Blo 1827615 9256031 := bstep (se 1 (by rfl) ⟨6942023, by rfl⟩ : syracuseStep 9256031 = 13884047) B13884047
theorem B2743919 : Blo 1827615 2743919 := bstep (se 1 (by rfl) ⟨2057939, by rfl⟩ : syracuseStep 2743919 = 4115879) B4115879
theorem B5856923 : Blo 1827615 5856923 := bstep (se 1 (by rfl) ⟨4392692, by rfl⟩ : syracuseStep 5856923 = 8785385) B8785385
theorem B7815143 : Blo 1827615 7815143 := bstep (se 1 (by rfl) ⟨5861357, by rfl⟩ : syracuseStep 7815143 = 11722715) B11722715
theorem B15835513 : Blo 1827615 15835513 := bstep (se 2 (by rfl) ⟨5938317, by rfl⟩ : syracuseStep 15835513 = 11876635) B11876635
theorem B5562863 : Blo 1827615 5562863 := bstep (se 1 (by rfl) ⟨4172147, by rfl⟩ : syracuseStep 5562863 = 8344295) B8344295
theorem B38060543 : Blo 1827615 38060543 := bstep (se 1 (by rfl) ⟨28545407, by rfl⟩ : syracuseStep 38060543 = 57090815) B57090815
theorem B253313639 : Blo 1827615 253313639 := bstep (se 1 (by rfl) ⟨189985229, by rfl⟩ : syracuseStep 253313639 = 379970459) B379970459
theorem B9888749 : Blo 1827615 9888749 := bstep (se 3 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 9888749 = 3708281) B3708281
theorem B46982929 : Blo 1827615 46982929 := bstep (se 2 (by rfl) ⟨17618598, by rfl⟩ : syracuseStep 46982929 = 35237197) B35237197
theorem B39544787 : Blo 1827615 39544787 := bstep (se 1 (by rfl) ⟨29658590, by rfl⟩ : syracuseStep 39544787 = 59317181) B59317181
theorem B4630567 : Blo 1827615 4630567 := bstep (se 1 (by rfl) ⟨3472925, by rfl⟩ : syracuseStep 4630567 = 6945851) B6945851
theorem B6170687 : Blo 1827615 6170687 := bstep (se 1 (by rfl) ⟨4628015, by rfl⟩ : syracuseStep 6170687 = 9256031) B9256031
theorem B1829279 : Blo 1827615 1829279 := bstep (se 1 (by rfl) ⟨1371959, by rfl⟩ : syracuseStep 1829279 = 2743919) B2743919
theorem B17566463 : Blo 1827615 17566463 := bstep (se 1 (by rfl) ⟨13174847, by rfl⟩ : syracuseStep 17566463 = 26349695) B26349695
theorem B6171551 : Blo 1827615 6171551 := bstep (se 1 (by rfl) ⟨4628663, by rfl⟩ : syracuseStep 6171551 = 9257327) B9257327
theorem B5205151 : Blo 1827615 5205151 := bstep (se 1 (by rfl) ⟨3903863, by rfl⟩ : syracuseStep 5205151 = 7807727) B7807727
theorem B18771203 : Blo 1827615 18771203 := bstep (se 1 (by rfl) ⟨14078402, by rfl⟩ : syracuseStep 18771203 = 28156805) B28156805
theorem B6254099 : Blo 1827615 6254099 := bstep (se 1 (by rfl) ⟨4690574, by rfl⟩ : syracuseStep 6254099 = 9381149) B9381149
theorem B70307675 : Blo 1827615 70307675 := bstep (se 1 (by rfl) ⟨52730756, by rfl⟩ : syracuseStep 70307675 = 105461513) B105461513
theorem B5205971 : Blo 1827615 5205971 := bstep (se 1 (by rfl) ⟨3904478, by rfl⟩ : syracuseStep 5205971 = 7808957) B7808957
theorem B22253575 : Blo 1827615 22253575 := bstep (se 1 (by rfl) ⟨16690181, by rfl⟩ : syracuseStep 22253575 = 33380363) B33380363
theorem B23441633 : Blo 1827615 23441633 := bstep (se 2 (by rfl) ⟨8790612, by rfl⟩ : syracuseStep 23441633 = 17581225) B17581225
theorem B8343815 : Blo 1827615 8343815 := bstep (se 1 (by rfl) ⟨6257861, by rfl⟩ : syracuseStep 8343815 = 12515723) B12515723
theorem B3469691 : Blo 1827615 3469691 := bstep (se 1 (by rfl) ⟨2602268, by rfl⟩ : syracuseStep 3469691 = 5204537) B5204537
theorem B3904615 : Blo 1827615 3904615 := bstep (se 1 (by rfl) ⟨2928461, by rfl⟩ : syracuseStep 3904615 = 5856923) B5856923
theorem B5208295 : Blo 1827615 5208295 := bstep (se 1 (by rfl) ⟨3906221, by rfl⟩ : syracuseStep 5208295 = 7812443) B7812443
theorem B7814015 : Blo 1827615 7814015 := bstep (se 1 (by rfl) ⟨5860511, by rfl⟩ : syracuseStep 7814015 = 11721023) B11721023
theorem B10411487 : Blo 1827615 10411487 := bstep (se 1 (by rfl) ⟨7808615, by rfl⟩ : syracuseStep 10411487 = 15617231) B15617231
theorem B5210095 : Blo 1827615 5210095 := bstep (se 1 (by rfl) ⟨3907571, by rfl⟩ : syracuseStep 5210095 = 7815143) B7815143
theorem B29671433 : Blo 1827615 29671433 := bstep (se 2 (by rfl) ⟨11126787, by rfl⟩ : syracuseStep 29671433 = 22253575) B22253575
theorem B20824613 : Blo 1827615 20824613 := bstep (se 4 (by rfl) ⟨1952307, by rfl⟩ : syracuseStep 20824613 = 3904615) B3904615
theorem B22250173 : Blo 1827615 22250173 := bstep (se 3 (by rfl) ⟨4171907, by rfl⟩ : syracuseStep 22250173 = 8343815) B8343815
theorem B26363191 : Blo 1827615 26363191 := bstep (se 1 (by rfl) ⟨19772393, by rfl⟩ : syracuseStep 26363191 = 39544787) B39544787
theorem B4113791 : Blo 1827615 4113791 := bstep (se 1 (by rfl) ⟨3085343, by rfl⟩ : syracuseStep 4113791 = 6170687) B6170687
theorem B6940201 : Blo 1827615 6940201 := bstep (se 2 (by rfl) ⟨2602575, by rfl⟩ : syracuseStep 6940201 = 5205151) B5205151
theorem B4114367 : Blo 1827615 4114367 := bstep (se 1 (by rfl) ⟨3085775, by rfl⟩ : syracuseStep 4114367 = 6171551) B6171551
theorem B6940991 : Blo 1827615 6940991 := bstep (se 1 (by rfl) ⟨5205743, by rfl⟩ : syracuseStep 6940991 = 10411487) B10411487
theorem B2313127 : Blo 1827615 2313127 := bstep (se 1 (by rfl) ⟨1734845, by rfl⟩ : syracuseStep 2313127 = 3469691) B3469691
theorem B25373695 : Blo 1827615 25373695 := bstep (se 1 (by rfl) ⟨19030271, by rfl⟩ : syracuseStep 25373695 = 38060543) B38060543
theorem B21114017 : Blo 1827615 21114017 := bstep (se 2 (by rfl) ⟨7917756, by rfl⟩ : syracuseStep 21114017 = 15835513) B15835513
theorem B11710975 : Blo 1827615 11710975 := bstep (se 1 (by rfl) ⟨8783231, by rfl⟩ : syracuseStep 11710975 = 17566463) B17566463
theorem B12514135 : Blo 1827615 12514135 := bstep (se 1 (by rfl) ⟨9385601, by rfl⟩ : syracuseStep 12514135 = 18771203) B18771203
theorem B13882589 : Blo 1827615 13882589 := bstep (se 3 (by rfl) ⟨2602985, by rfl⟩ : syracuseStep 13882589 = 5205971) B5205971
theorem B46871783 : Blo 1827615 46871783 := bstep (se 1 (by rfl) ⟨35153837, by rfl⟩ : syracuseStep 46871783 = 70307675) B70307675
theorem B6174089 : Blo 1827615 6174089 := bstep (se 2 (by rfl) ⟨2315283, by rfl⟩ : syracuseStep 6174089 = 4630567) B4630567
theorem B15627755 : Blo 1827615 15627755 := bstep (se 1 (by rfl) ⟨11720816, by rfl⟩ : syracuseStep 15627755 = 23441633) B23441633
theorem B6944393 : Blo 1827615 6944393 := bstep (se 2 (by rfl) ⟨2604147, by rfl⟩ : syracuseStep 6944393 = 5208295) B5208295
theorem B3708575 : Blo 1827615 3708575 := bstep (se 1 (by rfl) ⟨2781431, by rfl⟩ : syracuseStep 3708575 = 5562863) B5562863
theorem B168875759 : Blo 1827615 168875759 := bstep (se 1 (by rfl) ⟨126656819, by rfl⟩ : syracuseStep 168875759 = 253313639) B253313639
theorem B6592499 : Blo 1827615 6592499 := bstep (se 1 (by rfl) ⟨4944374, by rfl⟩ : syracuseStep 6592499 = 9888749) B9888749
theorem B5209343 : Blo 1827615 5209343 := bstep (se 1 (by rfl) ⟨3907007, by rfl⟩ : syracuseStep 5209343 = 7814015) B7814015
theorem B4169399 : Blo 1827615 4169399 := bstep (se 1 (by rfl) ⟨3127049, by rfl⟩ : syracuseStep 4169399 = 6254099) B6254099
theorem B62643905 : Blo 1827615 62643905 := bstep (se 2 (by rfl) ⟨23491464, by rfl⟩ : syracuseStep 62643905 = 46982929) B46982929
theorem B6946793 : Blo 1827615 6946793 := bstep (se 2 (by rfl) ⟨2605047, by rfl⟩ : syracuseStep 6946793 = 5210095) B5210095
theorem B15614633 : Blo 1827615 15614633 := bstep (se 2 (by rfl) ⟨5855487, by rfl⟩ : syracuseStep 15614633 = 11710975) B11710975
theorem B4629595 : Blo 1827615 4629595 := bstep (se 1 (by rfl) ⟨3472196, by rfl⟩ : syracuseStep 4629595 = 6944393) B6944393
theorem B112583839 : Blo 1827615 112583839 := bstep (se 1 (by rfl) ⟨84437879, by rfl⟩ : syracuseStep 112583839 = 168875759) B168875759
theorem B11118397 : Blo 1827615 11118397 := bstep (se 3 (by rfl) ⟨2084699, by rfl⟩ : syracuseStep 11118397 = 4169399) B4169399
theorem B14076011 : Blo 1827615 14076011 := bstep (se 1 (by rfl) ⟨10557008, by rfl⟩ : syracuseStep 14076011 = 21114017) B21114017
theorem B4631195 : Blo 1827615 4631195 := bstep (se 1 (by rfl) ⟨3473396, by rfl⟩ : syracuseStep 4631195 = 6946793) B6946793
theorem B31247855 : Blo 1827615 31247855 := bstep (se 1 (by rfl) ⟨23435891, by rfl⟩ : syracuseStep 31247855 = 46871783) B46871783
theorem B29666897 : Blo 1827615 29666897 := bstep (se 2 (by rfl) ⟨11125086, by rfl⟩ : syracuseStep 29666897 = 22250173) B22250173
theorem B4116059 : Blo 1827615 4116059 := bstep (se 1 (by rfl) ⟨3087044, by rfl⟩ : syracuseStep 4116059 = 6174089) B6174089
theorem B3084169 : Blo 1827615 3084169 := bstep (se 2 (by rfl) ⟨1156563, by rfl⟩ : syracuseStep 3084169 = 2313127) B2313127
theorem B4394999 : Blo 1827615 4394999 := bstep (se 1 (by rfl) ⟨3296249, by rfl⟩ : syracuseStep 4394999 = 6592499) B6592499
theorem B9253601 : Blo 1827615 9253601 := bstep (se 2 (by rfl) ⟨3470100, by rfl⟩ : syracuseStep 9253601 = 6940201) B6940201
theorem B19780955 : Blo 1827615 19780955 := bstep (se 1 (by rfl) ⟨14835716, by rfl⟩ : syracuseStep 19780955 = 29671433) B29671433
theorem B13883075 : Blo 1827615 13883075 := bstep (se 1 (by rfl) ⟨10412306, by rfl⟩ : syracuseStep 13883075 = 20824613) B20824613
theorem B9255059 : Blo 1827615 9255059 := bstep (se 1 (by rfl) ⟨6941294, by rfl⟩ : syracuseStep 9255059 = 13882589) B13882589
theorem B2742527 : Blo 1827615 2742527 := bstep (se 1 (by rfl) ⟨2056895, by rfl⟩ : syracuseStep 2742527 = 4113791) B4113791
theorem B10418503 : Blo 1827615 10418503 := bstep (se 1 (by rfl) ⟨7813877, by rfl⟩ : syracuseStep 10418503 = 15627755) B15627755
theorem B2472383 : Blo 1827615 2472383 := bstep (se 1 (by rfl) ⟨1854287, by rfl⟩ : syracuseStep 2472383 = 3708575) B3708575
theorem B16685513 : Blo 1827615 16685513 := bstep (se 2 (by rfl) ⟨6257067, by rfl⟩ : syracuseStep 16685513 = 12514135) B12514135
theorem B2742911 : Blo 1827615 2742911 := bstep (se 1 (by rfl) ⟨2057183, by rfl⟩ : syracuseStep 2742911 = 4114367) B4114367
theorem B33831593 : Blo 1827615 33831593 := bstep (se 2 (by rfl) ⟨12686847, by rfl⟩ : syracuseStep 33831593 = 25373695) B25373695
theorem B4627327 : Blo 1827615 4627327 := bstep (se 1 (by rfl) ⟨3470495, by rfl⟩ : syracuseStep 4627327 = 6940991) B6940991
theorem B35150921 : Blo 1827615 35150921 := bstep (se 2 (by rfl) ⟨13181595, by rfl⟩ : syracuseStep 35150921 = 26363191) B26363191
theorem B3472895 : Blo 1827615 3472895 := bstep (se 1 (by rfl) ⟨2604671, by rfl⟩ : syracuseStep 3472895 = 5209343) B5209343
theorem B41762603 : Blo 1827615 41762603 := bstep (se 1 (by rfl) ⟨31321952, by rfl⟩ : syracuseStep 41762603 = 62643905) B62643905
theorem B6169067 : Blo 1827615 6169067 := bstep (se 1 (by rfl) ⟨4626800, by rfl⟩ : syracuseStep 6169067 = 9253601) B9253601
theorem B6169769 : Blo 1827615 6169769 := bstep (se 2 (by rfl) ⟨2313663, by rfl⟩ : syracuseStep 6169769 = 4627327) B4627327
theorem B6170039 : Blo 1827615 6170039 := bstep (se 1 (by rfl) ⟨4627529, by rfl⟩ : syracuseStep 6170039 = 9255059) B9255059
theorem B1828351 : Blo 1827615 1828351 := bstep (se 1 (by rfl) ⟨1371263, by rfl⟩ : syracuseStep 1828351 = 2742527) B2742527
theorem B150111785 : Blo 1827615 150111785 := bstep (se 2 (by rfl) ⟨56291919, by rfl⟩ : syracuseStep 150111785 = 112583839) B112583839
theorem B1828607 : Blo 1827615 1828607 := bstep (se 1 (by rfl) ⟨1371455, by rfl⟩ : syracuseStep 1828607 = 2742911) B2742911
theorem B22554395 : Blo 1827615 22554395 := bstep (se 1 (by rfl) ⟨16915796, by rfl⟩ : syracuseStep 22554395 = 33831593) B33831593
theorem B19777931 : Blo 1827615 19777931 := bstep (se 1 (by rfl) ⟨14833448, by rfl⟩ : syracuseStep 19777931 = 29666897) B29666897
theorem B9261053 : Blo 1827615 9261053 := bstep (se 3 (by rfl) ⟨1736447, by rfl⟩ : syracuseStep 9261053 = 3472895) B3472895
theorem B9384007 : Blo 1827615 9384007 := bstep (se 1 (by rfl) ⟨7038005, by rfl⟩ : syracuseStep 9384007 = 14076011) B14076011
theorem B6172793 : Blo 1827615 6172793 := bstep (se 2 (by rfl) ⟨2314797, by rfl⟩ : syracuseStep 6172793 = 4629595) B4629595
theorem B23433947 : Blo 1827615 23433947 := bstep (se 1 (by rfl) ⟨17575460, by rfl⟩ : syracuseStep 23433947 = 35150921) B35150921
theorem B14824529 : Blo 1827615 14824529 := bstep (se 2 (by rfl) ⟨5559198, by rfl⟩ : syracuseStep 14824529 = 11118397) B11118397
theorem B27841735 : Blo 1827615 27841735 := bstep (se 1 (by rfl) ⟨20881301, by rfl⟩ : syracuseStep 27841735 = 41762603) B41762603
theorem B11719997 : Blo 1827615 11719997 := bstep (se 3 (by rfl) ⟨2197499, by rfl⟩ : syracuseStep 11719997 = 4394999) B4394999
theorem B13891337 : Blo 1827615 13891337 := bstep (se 2 (by rfl) ⟨5209251, by rfl⟩ : syracuseStep 13891337 = 10418503) B10418503
theorem B10409755 : Blo 1827615 10409755 := bstep (se 1 (by rfl) ⟨7807316, by rfl⟩ : syracuseStep 10409755 = 15614633) B15614633
theorem B13187303 : Blo 1827615 13187303 := bstep (se 1 (by rfl) ⟨9890477, by rfl⟩ : syracuseStep 13187303 = 19780955) B19780955
theorem B9255383 : Blo 1827615 9255383 := bstep (se 1 (by rfl) ⟨6941537, by rfl⟩ : syracuseStep 9255383 = 13883075) B13883075
theorem B6593021 : Blo 1827615 6593021 := bstep (se 3 (by rfl) ⟨1236191, by rfl⟩ : syracuseStep 6593021 = 2472383) B2472383
theorem B11123675 : Blo 1827615 11123675 := bstep (se 1 (by rfl) ⟨8342756, by rfl⟩ : syracuseStep 11123675 = 16685513) B16685513
theorem B3087463 : Blo 1827615 3087463 := bstep (se 1 (by rfl) ⟨2315597, by rfl⟩ : syracuseStep 3087463 = 4631195) B4631195
theorem B20831903 : Blo 1827615 20831903 := bstep (se 1 (by rfl) ⟨15623927, by rfl⟩ : syracuseStep 20831903 = 31247855) B31247855
theorem B2744039 : Blo 1827615 2744039 := bstep (se 1 (by rfl) ⟨2058029, by rfl⟩ : syracuseStep 2744039 = 4116059) B4116059
theorem B4112225 : Blo 1827615 4112225 := bstep (se 2 (by rfl) ⟨1542084, by rfl⟩ : syracuseStep 4112225 = 3084169) B3084169
theorem B4112711 : Blo 1827615 4112711 := bstep (se 1 (by rfl) ⟨3084533, by rfl⟩ : syracuseStep 4112711 = 6169067) B6169067
theorem B15622631 : Blo 1827615 15622631 := bstep (se 1 (by rfl) ⟨11716973, by rfl⟩ : syracuseStep 15622631 = 23433947) B23433947
theorem B4113179 : Blo 1827615 4113179 := bstep (se 1 (by rfl) ⟨3084884, by rfl⟩ : syracuseStep 4113179 = 6169769) B6169769
theorem B4113359 : Blo 1827615 4113359 := bstep (se 1 (by rfl) ⟨3085019, by rfl⟩ : syracuseStep 4113359 = 6170039) B6170039
theorem B100074523 : Blo 1827615 100074523 := bstep (se 1 (by rfl) ⟨75055892, by rfl⟩ : syracuseStep 100074523 = 150111785) B150111785
theorem B8791535 : Blo 1827615 8791535 := bstep (se 1 (by rfl) ⟨6593651, by rfl⟩ : syracuseStep 8791535 = 13187303) B13187303
theorem B6170255 : Blo 1827615 6170255 := bstep (se 1 (by rfl) ⟨4627691, by rfl⟩ : syracuseStep 6170255 = 9255383) B9255383
theorem B7415783 : Blo 1827615 7415783 := bstep (se 1 (by rfl) ⟨5561837, by rfl⟩ : syracuseStep 7415783 = 11123675) B11123675
theorem B13879673 : Blo 1827615 13879673 := bstep (se 2 (by rfl) ⟨5204877, by rfl⟩ : syracuseStep 13879673 = 10409755) B10409755
theorem B13887935 : Blo 1827615 13887935 := bstep (se 1 (by rfl) ⟨10415951, by rfl⟩ : syracuseStep 13887935 = 20831903) B20831903
theorem B1829359 : Blo 1827615 1829359 := bstep (se 1 (by rfl) ⟨1372019, by rfl⟩ : syracuseStep 1829359 = 2744039) B2744039
theorem B4115195 : Blo 1827615 4115195 := bstep (se 1 (by rfl) ⟨3086396, by rfl⟩ : syracuseStep 4115195 = 6172793) B6172793
theorem B12512009 : Blo 1827615 12512009 := bstep (se 2 (by rfl) ⟨4692003, by rfl⟩ : syracuseStep 12512009 = 9384007) B9384007
theorem B9883019 : Blo 1827615 9883019 := bstep (se 1 (by rfl) ⟨7412264, by rfl⟩ : syracuseStep 9883019 = 14824529) B14824529
theorem B9260891 : Blo 1827615 9260891 := bstep (se 1 (by rfl) ⟨6945668, by rfl⟩ : syracuseStep 9260891 = 13891337) B13891337
theorem B15036263 : Blo 1827615 15036263 := bstep (se 1 (by rfl) ⟨11277197, by rfl⟩ : syracuseStep 15036263 = 22554395) B22554395
theorem B4116617 : Blo 1827615 4116617 := bstep (se 2 (by rfl) ⟨1543731, by rfl⟩ : syracuseStep 4116617 = 3087463) B3087463
theorem B13185287 : Blo 1827615 13185287 := bstep (se 1 (by rfl) ⟨9888965, by rfl⟩ : syracuseStep 13185287 = 19777931) B19777931
theorem B37122313 : Blo 1827615 37122313 := bstep (se 2 (by rfl) ⟨13920867, by rfl⟩ : syracuseStep 37122313 = 27841735) B27841735
theorem B4395347 : Blo 1827615 4395347 := bstep (se 1 (by rfl) ⟨3296510, by rfl⟩ : syracuseStep 4395347 = 6593021) B6593021
theorem B2741483 : Blo 1827615 2741483 := bstep (se 1 (by rfl) ⟨2056112, by rfl⟩ : syracuseStep 2741483 = 4112225) B4112225
theorem B6174035 : Blo 1827615 6174035 := bstep (se 1 (by rfl) ⟨4630526, by rfl⟩ : syracuseStep 6174035 = 9261053) B9261053
theorem B7813331 : Blo 1827615 7813331 := bstep (se 1 (by rfl) ⟨5859998, by rfl⟩ : syracuseStep 7813331 = 11719997) B11719997
theorem B2744411 : Blo 1827615 2744411 := bstep (se 1 (by rfl) ⟨2058308, by rfl⟩ : syracuseStep 2744411 = 4116617) B4116617
theorem B8790191 : Blo 1827615 8790191 := bstep (se 1 (by rfl) ⟨6592643, by rfl⟩ : syracuseStep 8790191 = 13185287) B13185287
theorem B49496417 : Blo 1827615 49496417 := bstep (se 2 (by rfl) ⟨18561156, by rfl⟩ : syracuseStep 49496417 = 37122313) B37122313
theorem B1827655 : Blo 1827615 1827655 := bstep (se 1 (by rfl) ⟨1370741, by rfl⟩ : syracuseStep 1827655 = 2741483) B2741483
theorem B26354717 : Blo 1827615 26354717 := bstep (se 3 (by rfl) ⟨4941509, by rfl⟩ : syracuseStep 26354717 = 9883019) B9883019
theorem B4113503 : Blo 1827615 4113503 := bstep (se 1 (by rfl) ⟨3085127, by rfl⟩ : syracuseStep 4113503 = 6170255) B6170255
theorem B133432697 : Blo 1827615 133432697 := bstep (se 2 (by rfl) ⟨50037261, by rfl⟩ : syracuseStep 133432697 = 100074523) B100074523
theorem B9258623 : Blo 1827615 9258623 := bstep (se 1 (by rfl) ⟨6943967, by rfl⟩ : syracuseStep 9258623 = 13887935) B13887935
theorem B8341339 : Blo 1827615 8341339 := bstep (se 1 (by rfl) ⟨6256004, by rfl⟩ : syracuseStep 8341339 = 12512009) B12512009
theorem B10415087 : Blo 1827615 10415087 := bstep (se 1 (by rfl) ⟨7811315, by rfl⟩ : syracuseStep 10415087 = 15622631) B15622631
theorem B4116023 : Blo 1827615 4116023 := bstep (se 1 (by rfl) ⟨3087017, by rfl⟩ : syracuseStep 4116023 = 6174035) B6174035
theorem B4943855 : Blo 1827615 4943855 := bstep (se 1 (by rfl) ⟨3707891, by rfl⟩ : syracuseStep 4943855 = 7415783) B7415783
theorem B9253115 : Blo 1827615 9253115 := bstep (se 1 (by rfl) ⟨6939836, by rfl⟩ : syracuseStep 9253115 = 13879673) B13879673
theorem B6173927 : Blo 1827615 6173927 := bstep (se 1 (by rfl) ⟨4630445, by rfl⟩ : syracuseStep 6173927 = 9260891) B9260891
theorem B10024175 : Blo 1827615 10024175 := bstep (se 1 (by rfl) ⟨7518131, by rfl⟩ : syracuseStep 10024175 = 15036263) B15036263
theorem B2741807 : Blo 1827615 2741807 := bstep (se 1 (by rfl) ⟨2056355, by rfl⟩ : syracuseStep 2741807 = 4112711) B4112711
theorem B2930231 : Blo 1827615 2930231 := bstep (se 1 (by rfl) ⟨2197673, by rfl⟩ : syracuseStep 2930231 = 4395347) B4395347
theorem B2742119 : Blo 1827615 2742119 := bstep (se 1 (by rfl) ⟨2056589, by rfl⟩ : syracuseStep 2742119 = 4113179) B4113179
theorem B2742239 : Blo 1827615 2742239 := bstep (se 1 (by rfl) ⟨2056679, by rfl⟩ : syracuseStep 2742239 = 4113359) B4113359
theorem B23444093 : Blo 1827615 23444093 := bstep (se 3 (by rfl) ⟨4395767, by rfl⟩ : syracuseStep 23444093 = 8791535) B8791535
theorem B5208887 : Blo 1827615 5208887 := bstep (se 1 (by rfl) ⟨3906665, by rfl⟩ : syracuseStep 5208887 = 7813331) B7813331
theorem B2743463 : Blo 1827615 2743463 := bstep (se 1 (by rfl) ⟨2057597, by rfl⟩ : syracuseStep 2743463 = 4115195) B4115195
theorem B6168743 : Blo 1827615 6168743 := bstep (se 1 (by rfl) ⟨4626557, by rfl⟩ : syracuseStep 6168743 = 9253115) B9253115
theorem B32997611 : Blo 1827615 32997611 := bstep (se 1 (by rfl) ⟨24748208, by rfl⟩ : syracuseStep 32997611 = 49496417) B49496417
theorem B26731133 : Blo 1827615 26731133 := bstep (se 3 (by rfl) ⟨5012087, by rfl⟩ : syracuseStep 26731133 = 10024175) B10024175
theorem B1827871 : Blo 1827615 1827871 := bstep (se 1 (by rfl) ⟨1370903, by rfl⟩ : syracuseStep 1827871 = 2741807) B2741807
theorem B1828079 : Blo 1827615 1828079 := bstep (se 1 (by rfl) ⟨1371059, by rfl⟩ : syracuseStep 1828079 = 2742119) B2742119
theorem B1828159 : Blo 1827615 1828159 := bstep (se 1 (by rfl) ⟨1371119, by rfl⟩ : syracuseStep 1828159 = 2742239) B2742239
theorem B1828975 : Blo 1827615 1828975 := bstep (se 1 (by rfl) ⟨1371731, by rfl⟩ : syracuseStep 1828975 = 2743463) B2743463
theorem B13183613 : Blo 1827615 13183613 := bstep (se 3 (by rfl) ⟨2471927, by rfl⟩ : syracuseStep 13183613 = 4943855) B4943855
theorem B1829607 : Blo 1827615 1829607 := bstep (se 1 (by rfl) ⟨1372205, by rfl⟩ : syracuseStep 1829607 = 2744411) B2744411
theorem B5860127 : Blo 1827615 5860127 := bstep (se 1 (by rfl) ⟨4395095, by rfl⟩ : syracuseStep 5860127 = 8790191) B8790191
theorem B4115951 : Blo 1827615 4115951 := bstep (se 1 (by rfl) ⟨3086963, by rfl⟩ : syracuseStep 4115951 = 6173927) B6173927
theorem B1953487 : Blo 1827615 1953487 := bstep (se 1 (by rfl) ⟨1465115, by rfl⟩ : syracuseStep 1953487 = 2930231) B2930231
theorem B6172415 : Blo 1827615 6172415 := bstep (se 1 (by rfl) ⟨4629311, by rfl⟩ : syracuseStep 6172415 = 9258623) B9258623
theorem B6943391 : Blo 1827615 6943391 := bstep (se 1 (by rfl) ⟨5207543, by rfl⟩ : syracuseStep 6943391 = 10415087) B10415087
theorem B13890365 : Blo 1827615 13890365 := bstep (se 3 (by rfl) ⟨2604443, by rfl⟩ : syracuseStep 13890365 = 5208887) B5208887
theorem B11121785 : Blo 1827615 11121785 := bstep (se 2 (by rfl) ⟨4170669, by rfl⟩ : syracuseStep 11121785 = 8341339) B8341339
theorem B17569811 : Blo 1827615 17569811 := bstep (se 1 (by rfl) ⟨13177358, by rfl⟩ : syracuseStep 17569811 = 26354717) B26354717
theorem B2742335 : Blo 1827615 2742335 := bstep (se 1 (by rfl) ⟨2056751, by rfl⟩ : syracuseStep 2742335 = 4113503) B4113503
theorem B88955131 : Blo 1827615 88955131 := bstep (se 1 (by rfl) ⟨66716348, by rfl⟩ : syracuseStep 88955131 = 133432697) B133432697
theorem B15629395 : Blo 1827615 15629395 := bstep (se 1 (by rfl) ⟨11722046, by rfl⟩ : syracuseStep 15629395 = 23444093) B23444093
theorem B2744015 : Blo 1827615 2744015 := bstep (se 1 (by rfl) ⟨2058011, by rfl⟩ : syracuseStep 2744015 = 4116023) B4116023
theorem B4112495 : Blo 1827615 4112495 := bstep (se 1 (by rfl) ⟨3084371, by rfl⟩ : syracuseStep 4112495 = 6168743) B6168743
theorem B4628927 : Blo 1827615 4628927 := bstep (se 1 (by rfl) ⟨3471695, by rfl⟩ : syracuseStep 4628927 = 6943391) B6943391
theorem B7414523 : Blo 1827615 7414523 := bstep (se 1 (by rfl) ⟨5560892, by rfl⟩ : syracuseStep 7414523 = 11121785) B11121785
theorem B1828223 : Blo 1827615 1828223 := bstep (se 1 (by rfl) ⟨1371167, by rfl⟩ : syracuseStep 1828223 = 2742335) B2742335
theorem B1829343 : Blo 1827615 1829343 := bstep (se 1 (by rfl) ⟨1372007, by rfl⟩ : syracuseStep 1829343 = 2744015) B2744015
theorem B4114943 : Blo 1827615 4114943 := bstep (se 1 (by rfl) ⟨3086207, by rfl⟩ : syracuseStep 4114943 = 6172415) B6172415
theorem B21998407 : Blo 1827615 21998407 := bstep (se 1 (by rfl) ⟨16498805, by rfl⟩ : syracuseStep 21998407 = 32997611) B32997611
theorem B118606841 : Blo 1827615 118606841 := bstep (se 2 (by rfl) ⟨44477565, by rfl⟩ : syracuseStep 118606841 = 88955131) B88955131
theorem B17820755 : Blo 1827615 17820755 := bstep (se 1 (by rfl) ⟨13365566, by rfl⟩ : syracuseStep 17820755 = 26731133) B26731133
theorem B9260243 : Blo 1827615 9260243 := bstep (se 1 (by rfl) ⟨6945182, by rfl⟩ : syracuseStep 9260243 = 13890365) B13890365
theorem B15627005 : Blo 1827615 15627005 := bstep (se 3 (by rfl) ⟨2930063, by rfl⟩ : syracuseStep 15627005 = 5860127) B5860127
theorem B11713207 : Blo 1827615 11713207 := bstep (se 1 (by rfl) ⟨8784905, by rfl⟩ : syracuseStep 11713207 = 17569811) B17569811
theorem B20839193 : Blo 1827615 20839193 := bstep (se 2 (by rfl) ⟨7814697, by rfl⟩ : syracuseStep 20839193 = 15629395) B15629395
theorem B8789075 : Blo 1827615 8789075 := bstep (se 1 (by rfl) ⟨6591806, by rfl⟩ : syracuseStep 8789075 = 13183613) B13183613
theorem B2604649 : Blo 1827615 2604649 := bstep (se 2 (by rfl) ⟨976743, by rfl⟩ : syracuseStep 2604649 = 1953487) B1953487
theorem B2743967 : Blo 1827615 2743967 := bstep (se 1 (by rfl) ⟨2057975, by rfl⟩ : syracuseStep 2743967 = 4115951) B4115951
theorem B79071227 : Blo 1827615 79071227 := bstep (se 1 (by rfl) ⟨59303420, by rfl⟩ : syracuseStep 79071227 = 118606841) B118606841
theorem B5859383 : Blo 1827615 5859383 := bstep (se 1 (by rfl) ⟨4394537, by rfl⟩ : syracuseStep 5859383 = 8789075) B8789075
theorem B11880503 : Blo 1827615 11880503 := bstep (se 1 (by rfl) ⟨8910377, by rfl⟩ : syracuseStep 11880503 = 17820755) B17820755
theorem B1829311 : Blo 1827615 1829311 := bstep (se 1 (by rfl) ⟨1371983, by rfl⟩ : syracuseStep 1829311 = 2743967) B2743967
theorem B4943015 : Blo 1827615 4943015 := bstep (se 1 (by rfl) ⟨3707261, by rfl⟩ : syracuseStep 4943015 = 7414523) B7414523
theorem B15617609 : Blo 1827615 15617609 := bstep (se 2 (by rfl) ⟨5856603, by rfl⟩ : syracuseStep 15617609 = 11713207) B11713207
theorem B29331209 : Blo 1827615 29331209 := bstep (se 2 (by rfl) ⟨10999203, by rfl⟩ : syracuseStep 29331209 = 21998407) B21998407
theorem B6173495 : Blo 1827615 6173495 := bstep (se 1 (by rfl) ⟨4630121, by rfl⟩ : syracuseStep 6173495 = 9260243) B9260243
theorem B2741663 : Blo 1827615 2741663 := bstep (se 1 (by rfl) ⟨2056247, by rfl⟩ : syracuseStep 2741663 = 4112495) B4112495
theorem B3085951 : Blo 1827615 3085951 := bstep (se 1 (by rfl) ⟨2314463, by rfl⟩ : syracuseStep 3085951 = 4628927) B4628927
theorem B10418003 : Blo 1827615 10418003 := bstep (se 1 (by rfl) ⟨7813502, by rfl⟩ : syracuseStep 10418003 = 15627005) B15627005
theorem B2743295 : Blo 1827615 2743295 := bstep (se 1 (by rfl) ⟨2057471, by rfl⟩ : syracuseStep 2743295 = 4114943) B4114943
theorem B13892795 : Blo 1827615 13892795 := bstep (se 1 (by rfl) ⟨10419596, by rfl⟩ : syracuseStep 13892795 = 20839193) B20839193
theorem B3472865 : Blo 1827615 3472865 := bstep (se 2 (by rfl) ⟨1302324, by rfl⟩ : syracuseStep 3472865 = 2604649) B2604649
theorem B1827775 : Blo 1827615 1827775 := bstep (se 1 (by rfl) ⟨1370831, by rfl⟩ : syracuseStep 1827775 = 2741663) B2741663
theorem B1828863 : Blo 1827615 1828863 := bstep (se 1 (by rfl) ⟨1371647, by rfl⟩ : syracuseStep 1828863 = 2743295) B2743295
theorem B3295343 : Blo 1827615 3295343 := bstep (se 1 (by rfl) ⟨2471507, by rfl⟩ : syracuseStep 3295343 = 4943015) B4943015
theorem B4114601 : Blo 1827615 4114601 := bstep (se 2 (by rfl) ⟨1542975, by rfl⟩ : syracuseStep 4114601 = 3085951) B3085951
theorem B15625021 : Blo 1827615 15625021 := bstep (se 3 (by rfl) ⟨2929691, by rfl⟩ : syracuseStep 15625021 = 5859383) B5859383
theorem B4115663 : Blo 1827615 4115663 := bstep (se 1 (by rfl) ⟨3086747, by rfl⟩ : syracuseStep 4115663 = 6173495) B6173495
theorem B9261863 : Blo 1827615 9261863 := bstep (se 1 (by rfl) ⟨6946397, by rfl⟩ : syracuseStep 9261863 = 13892795) B13892795
theorem B2315243 : Blo 1827615 2315243 := bstep (se 1 (by rfl) ⟨1736432, by rfl⟩ : syracuseStep 2315243 = 3472865) B3472865
theorem B6945335 : Blo 1827615 6945335 := bstep (se 1 (by rfl) ⟨5209001, by rfl⟩ : syracuseStep 6945335 = 10418003) B10418003
theorem B52714151 : Blo 1827615 52714151 := bstep (se 1 (by rfl) ⟨39535613, by rfl⟩ : syracuseStep 52714151 = 79071227) B79071227
theorem B7920335 : Blo 1827615 7920335 := bstep (se 1 (by rfl) ⟨5940251, by rfl⟩ : syracuseStep 7920335 = 11880503) B11880503
theorem B10411739 : Blo 1827615 10411739 := bstep (se 1 (by rfl) ⟨7808804, by rfl⟩ : syracuseStep 10411739 = 15617609) B15617609
theorem B19554139 : Blo 1827615 19554139 := bstep (se 1 (by rfl) ⟨14665604, by rfl⟩ : syracuseStep 19554139 = 29331209) B29331209
theorem B20833361 : Blo 1827615 20833361 := bstep (se 2 (by rfl) ⟨7812510, by rfl⟩ : syracuseStep 20833361 = 15625021) B15625021
theorem B2196895 : Blo 1827615 2196895 := bstep (se 1 (by rfl) ⟨1647671, by rfl⟩ : syracuseStep 2196895 = 3295343) B3295343
theorem B4630223 : Blo 1827615 4630223 := bstep (se 1 (by rfl) ⟨3472667, by rfl⟩ : syracuseStep 4630223 = 6945335) B6945335
theorem B6941159 : Blo 1827615 6941159 := bstep (se 1 (by rfl) ⟨5205869, by rfl⟩ : syracuseStep 6941159 = 10411739) B10411739
theorem B5280223 : Blo 1827615 5280223 := bstep (se 1 (by rfl) ⟨3960167, by rfl⟩ : syracuseStep 5280223 = 7920335) B7920335
theorem B104288741 : Blo 1827615 104288741 := bstep (se 4 (by rfl) ⟨9777069, by rfl⟩ : syracuseStep 104288741 = 19554139) B19554139
theorem B6173981 : Blo 1827615 6173981 := bstep (se 3 (by rfl) ⟨1157621, by rfl⟩ : syracuseStep 6173981 = 2315243) B2315243
theorem B6174575 : Blo 1827615 6174575 := bstep (se 1 (by rfl) ⟨4630931, by rfl⟩ : syracuseStep 6174575 = 9261863) B9261863
theorem B2743067 : Blo 1827615 2743067 := bstep (se 1 (by rfl) ⟨2057300, by rfl⟩ : syracuseStep 2743067 = 4114601) B4114601
theorem B35142767 : Blo 1827615 35142767 := bstep (se 1 (by rfl) ⟨26357075, by rfl⟩ : syracuseStep 35142767 = 52714151) B52714151
theorem B2743775 : Blo 1827615 2743775 := bstep (se 1 (by rfl) ⟨2057831, by rfl⟩ : syracuseStep 2743775 = 4115663) B4115663
theorem B69525827 : Blo 1827615 69525827 := bstep (se 1 (by rfl) ⟨52144370, by rfl⟩ : syracuseStep 69525827 = 104288741) B104288741
theorem B1828711 : Blo 1827615 1828711 := bstep (se 1 (by rfl) ⟨1371533, by rfl⟩ : syracuseStep 1828711 = 2743067) B2743067
theorem B1829183 : Blo 1827615 1829183 := bstep (se 1 (by rfl) ⟨1371887, by rfl⟩ : syracuseStep 1829183 = 2743775) B2743775
theorem B7040297 : Blo 1827615 7040297 := bstep (se 2 (by rfl) ⟨2640111, by rfl⟩ : syracuseStep 7040297 = 5280223) B5280223
theorem B13888907 : Blo 1827615 13888907 := bstep (se 1 (by rfl) ⟨10416680, by rfl⟩ : syracuseStep 13888907 = 20833361) B20833361
theorem B4115987 : Blo 1827615 4115987 := bstep (se 1 (by rfl) ⟨3086990, by rfl⟩ : syracuseStep 4115987 = 6173981) B6173981
theorem B4116383 : Blo 1827615 4116383 := bstep (se 1 (by rfl) ⟨3087287, by rfl⟩ : syracuseStep 4116383 = 6174575) B6174575
theorem B2929193 : Blo 1827615 2929193 := bstep (se 2 (by rfl) ⟨1098447, by rfl⟩ : syracuseStep 2929193 = 2196895) B2196895
theorem B3086815 : Blo 1827615 3086815 := bstep (se 1 (by rfl) ⟨2315111, by rfl⟩ : syracuseStep 3086815 = 4630223) B4630223
theorem B4627439 : Blo 1827615 4627439 := bstep (se 1 (by rfl) ⟨3470579, by rfl⟩ : syracuseStep 4627439 = 6941159) B6941159
theorem B23428511 : Blo 1827615 23428511 := bstep (se 1 (by rfl) ⟨17571383, by rfl⟩ : syracuseStep 23428511 = 35142767) B35142767
theorem B46350551 : Blo 1827615 46350551 := bstep (se 1 (by rfl) ⟨34762913, by rfl⟩ : syracuseStep 46350551 = 69525827) B69525827
theorem B9259271 : Blo 1827615 9259271 := bstep (se 1 (by rfl) ⟨6944453, by rfl⟩ : syracuseStep 9259271 = 13888907) B13888907
theorem B1952795 : Blo 1827615 1952795 := bstep (se 1 (by rfl) ⟨1464596, by rfl⟩ : syracuseStep 1952795 = 2929193) B2929193
theorem B4115753 : Blo 1827615 4115753 := bstep (se 2 (by rfl) ⟨1543407, by rfl⟩ : syracuseStep 4115753 = 3086815) B3086815
theorem B3084959 : Blo 1827615 3084959 := bstep (se 1 (by rfl) ⟨2313719, by rfl⟩ : syracuseStep 3084959 = 4627439) B4627439
theorem B15619007 : Blo 1827615 15619007 := bstep (se 1 (by rfl) ⟨11714255, by rfl⟩ : syracuseStep 15619007 = 23428511) B23428511
theorem B18774125 : Blo 1827615 18774125 := bstep (se 3 (by rfl) ⟨3520148, by rfl⟩ : syracuseStep 18774125 = 7040297) B7040297
theorem B2743991 : Blo 1827615 2743991 := bstep (se 1 (by rfl) ⟨2057993, by rfl⟩ : syracuseStep 2743991 = 4115987) B4115987
theorem B2744255 : Blo 1827615 2744255 := bstep (se 1 (by rfl) ⟨2058191, by rfl⟩ : syracuseStep 2744255 = 4116383) B4116383
theorem B30900367 : Blo 1827615 30900367 := bstep (se 1 (by rfl) ⟨23175275, by rfl⟩ : syracuseStep 30900367 = 46350551) B46350551
theorem B2056639 : Blo 1827615 2056639 := bstep (se 1 (by rfl) ⟨1542479, by rfl⟩ : syracuseStep 2056639 = 3084959) B3084959
theorem B10412671 : Blo 1827615 10412671 := bstep (se 1 (by rfl) ⟨7809503, by rfl⟩ : syracuseStep 10412671 = 15619007) B15619007
theorem B1829327 : Blo 1827615 1829327 := bstep (se 1 (by rfl) ⟨1371995, by rfl⟩ : syracuseStep 1829327 = 2743991) B2743991
theorem B1829503 : Blo 1827615 1829503 := bstep (se 1 (by rfl) ⟨1372127, by rfl⟩ : syracuseStep 1829503 = 2744255) B2744255
theorem B6172847 : Blo 1827615 6172847 := bstep (se 1 (by rfl) ⟨4629635, by rfl⟩ : syracuseStep 6172847 = 9259271) B9259271
theorem B5207453 : Blo 1827615 5207453 := bstep (se 3 (by rfl) ⟨976397, by rfl⟩ : syracuseStep 5207453 = 1952795) B1952795
theorem B12516083 : Blo 1827615 12516083 := bstep (se 1 (by rfl) ⟨9387062, by rfl⟩ : syracuseStep 12516083 = 18774125) B18774125
theorem B2743835 : Blo 1827615 2743835 := bstep (se 1 (by rfl) ⟨2057876, by rfl⟩ : syracuseStep 2743835 = 4115753) B4115753
theorem B1829223 : Blo 1827615 1829223 := bstep (se 1 (by rfl) ⟨1371917, by rfl⟩ : syracuseStep 1829223 = 2743835) B2743835
theorem B4115231 : Blo 1827615 4115231 := bstep (se 1 (by rfl) ⟨3086423, by rfl⟩ : syracuseStep 4115231 = 6172847) B6172847
theorem B41200489 : Blo 1827615 41200489 := bstep (se 2 (by rfl) ⟨15450183, by rfl⟩ : syracuseStep 41200489 = 30900367) B30900367
theorem B8344055 : Blo 1827615 8344055 := bstep (se 1 (by rfl) ⟨6258041, by rfl⟩ : syracuseStep 8344055 = 12516083) B12516083
theorem B2742185 : Blo 1827615 2742185 := bstep (se 2 (by rfl) ⟨1028319, by rfl⟩ : syracuseStep 2742185 = 2056639) B2056639
theorem B13883561 : Blo 1827615 13883561 := bstep (se 2 (by rfl) ⟨5206335, by rfl⟩ : syracuseStep 13883561 = 10412671) B10412671
theorem B3471635 : Blo 1827615 3471635 := bstep (se 1 (by rfl) ⟨2603726, by rfl⟩ : syracuseStep 3471635 = 5207453) B5207453
theorem B5562703 : Blo 1827615 5562703 := bstep (se 1 (by rfl) ⟨4172027, by rfl⟩ : syracuseStep 5562703 = 8344055) B8344055
theorem B1828123 : Blo 1827615 1828123 := bstep (se 1 (by rfl) ⟨1371092, by rfl⟩ : syracuseStep 1828123 = 2742185) B2742185
theorem B2314423 : Blo 1827615 2314423 := bstep (se 1 (by rfl) ⟨1735817, by rfl⟩ : syracuseStep 2314423 = 3471635) B3471635
theorem B54933985 : Blo 1827615 54933985 := bstep (se 2 (by rfl) ⟨20600244, by rfl⟩ : syracuseStep 54933985 = 41200489) B41200489
theorem B9255707 : Blo 1827615 9255707 := bstep (se 1 (by rfl) ⟨6941780, by rfl⟩ : syracuseStep 9255707 = 13883561) B13883561
theorem B2743487 : Blo 1827615 2743487 := bstep (se 1 (by rfl) ⟨2057615, by rfl⟩ : syracuseStep 2743487 = 4115231) B4115231
theorem B73245313 : Blo 1827615 73245313 := bstep (se 2 (by rfl) ⟨27466992, by rfl⟩ : syracuseStep 73245313 = 54933985) B54933985
theorem B6170471 : Blo 1827615 6170471 := bstep (se 1 (by rfl) ⟨4627853, by rfl⟩ : syracuseStep 6170471 = 9255707) B9255707
theorem B1828991 : Blo 1827615 1828991 := bstep (se 1 (by rfl) ⟨1371743, by rfl⟩ : syracuseStep 1828991 = 2743487) B2743487
theorem B7416937 : Blo 1827615 7416937 := bstep (se 2 (by rfl) ⟨2781351, by rfl⟩ : syracuseStep 7416937 = 5562703) B5562703
theorem B3085897 : Blo 1827615 3085897 := bstep (se 2 (by rfl) ⟨1157211, by rfl⟩ : syracuseStep 3085897 = 2314423) B2314423
theorem B4113647 : Blo 1827615 4113647 := bstep (se 1 (by rfl) ⟨3085235, by rfl⟩ : syracuseStep 4113647 = 6170471) B6170471
theorem B9889249 : Blo 1827615 9889249 := bstep (se 2 (by rfl) ⟨3708468, by rfl⟩ : syracuseStep 9889249 = 7416937) B7416937
theorem B4114529 : Blo 1827615 4114529 := bstep (se 2 (by rfl) ⟨1542948, by rfl⟩ : syracuseStep 4114529 = 3085897) B3085897
theorem B97660417 : Blo 1827615 97660417 := bstep (se 2 (by rfl) ⟨36622656, by rfl⟩ : syracuseStep 97660417 = 73245313) B73245313
theorem B130213889 : Blo 1827615 130213889 := bstep (se 2 (by rfl) ⟨48830208, by rfl⟩ : syracuseStep 130213889 = 97660417) B97660417
theorem B13185665 : Blo 1827615 13185665 := bstep (se 2 (by rfl) ⟨4944624, by rfl⟩ : syracuseStep 13185665 = 9889249) B9889249
theorem B2742431 : Blo 1827615 2742431 := bstep (se 1 (by rfl) ⟨2056823, by rfl⟩ : syracuseStep 2742431 = 4113647) B4113647
theorem B2743019 : Blo 1827615 2743019 := bstep (se 1 (by rfl) ⟨2057264, by rfl⟩ : syracuseStep 2743019 = 4114529) B4114529
theorem B8790443 : Blo 1827615 8790443 := bstep (se 1 (by rfl) ⟨6592832, by rfl⟩ : syracuseStep 8790443 = 13185665) B13185665
theorem B1828287 : Blo 1827615 1828287 := bstep (se 1 (by rfl) ⟨1371215, by rfl⟩ : syracuseStep 1828287 = 2742431) B2742431
theorem B1828679 : Blo 1827615 1828679 := bstep (se 1 (by rfl) ⟨1371509, by rfl⟩ : syracuseStep 1828679 = 2743019) B2743019
theorem B86809259 : Blo 1827615 86809259 := bstep (se 1 (by rfl) ⟨65106944, by rfl⟩ : syracuseStep 86809259 = 130213889) B130213889
theorem B5860295 : Blo 1827615 5860295 := bstep (se 1 (by rfl) ⟨4395221, by rfl⟩ : syracuseStep 5860295 = 8790443) B8790443
theorem B57872839 : Blo 1827615 57872839 := bstep (se 1 (by rfl) ⟨43404629, by rfl⟩ : syracuseStep 57872839 = 86809259) B86809259
theorem B77163785 : Blo 1827615 77163785 := bstep (se 2 (by rfl) ⟨28936419, by rfl⟩ : syracuseStep 77163785 = 57872839) B57872839
theorem B3906863 : Blo 1827615 3906863 := bstep (se 1 (by rfl) ⟨2930147, by rfl⟩ : syracuseStep 3906863 = 5860295) B5860295
theorem B51442523 : Blo 1827615 51442523 := bstep (se 1 (by rfl) ⟨38581892, by rfl⟩ : syracuseStep 51442523 = 77163785) B77163785
theorem B2604575 : Blo 1827615 2604575 := bstep (se 1 (by rfl) ⟨1953431, by rfl⟩ : syracuseStep 2604575 = 3906863) B3906863
theorem B34295015 : Blo 1827615 34295015 := bstep (se 1 (by rfl) ⟨25721261, by rfl⟩ : syracuseStep 34295015 = 51442523) B51442523
theorem B6945533 : Blo 1827615 6945533 := bstep (se 3 (by rfl) ⟨1302287, by rfl⟩ : syracuseStep 6945533 = 2604575) B2604575
theorem B4630355 : Blo 1827615 4630355 := bstep (se 1 (by rfl) ⟨3472766, by rfl⟩ : syracuseStep 4630355 = 6945533) B6945533
theorem B22863343 : Blo 1827615 22863343 := bstep (se 1 (by rfl) ⟨17147507, by rfl⟩ : syracuseStep 22863343 = 34295015) B34295015
theorem B30484457 : Blo 1827615 30484457 := bstep (se 2 (by rfl) ⟨11431671, by rfl⟩ : syracuseStep 30484457 = 22863343) B22863343
theorem B3086903 : Blo 1827615 3086903 := bstep (se 1 (by rfl) ⟨2315177, by rfl⟩ : syracuseStep 3086903 = 4630355) B4630355
theorem B2057935 : Blo 1827615 2057935 := bstep (se 1 (by rfl) ⟨1543451, by rfl⟩ : syracuseStep 2057935 = 3086903) B3086903
theorem B20322971 : Blo 1827615 20322971 := bstep (se 1 (by rfl) ⟨15242228, by rfl⟩ : syracuseStep 20322971 = 30484457) B30484457
theorem B13548647 : Blo 1827615 13548647 := bstep (se 1 (by rfl) ⟨10161485, by rfl⟩ : syracuseStep 13548647 = 20322971) B20322971
theorem B2743913 : Blo 1827615 2743913 := bstep (se 2 (by rfl) ⟨1028967, by rfl⟩ : syracuseStep 2743913 = 2057935) B2057935
theorem B1829275 : Blo 1827615 1829275 := bstep (se 1 (by rfl) ⟨1371956, by rfl⟩ : syracuseStep 1829275 = 2743913) B2743913
theorem B36129725 : Blo 1827615 36129725 := bstep (se 3 (by rfl) ⟨6774323, by rfl⟩ : syracuseStep 36129725 = 13548647) B13548647
theorem B24086483 : Blo 1827615 24086483 := bstep (se 1 (by rfl) ⟨18064862, by rfl⟩ : syracuseStep 24086483 = 36129725) B36129725
theorem B16057655 : Blo 1827615 16057655 := bstep (se 1 (by rfl) ⟨12043241, by rfl⟩ : syracuseStep 16057655 = 24086483) B24086483
theorem B10705103 : Blo 1827615 10705103 := bstep (se 1 (by rfl) ⟨8028827, by rfl⟩ : syracuseStep 10705103 = 16057655) B16057655
theorem B114187765 : Blo 1827615 114187765 := bstep (se 5 (by rfl) ⟨5352551, by rfl⟩ : syracuseStep 114187765 = 10705103) B10705103
theorem B152250353 : Blo 1827615 152250353 := bstep (se 2 (by rfl) ⟨57093882, by rfl⟩ : syracuseStep 152250353 = 114187765) B114187765
theorem B101500235 : Blo 1827615 101500235 := bstep (se 1 (by rfl) ⟨76125176, by rfl⟩ : syracuseStep 101500235 = 152250353) B152250353
theorem B67666823 : Blo 1827615 67666823 := bstep (se 1 (by rfl) ⟨50750117, by rfl⟩ : syracuseStep 67666823 = 101500235) B101500235
theorem B45111215 : Blo 1827615 45111215 := bstep (se 1 (by rfl) ⟨33833411, by rfl⟩ : syracuseStep 45111215 = 67666823) B67666823
theorem B120296573 : Blo 1827615 120296573 := bstep (se 3 (by rfl) ⟨22555607, by rfl⟩ : syracuseStep 120296573 = 45111215) B45111215
theorem B80197715 : Blo 1827615 80197715 := bstep (se 1 (by rfl) ⟨60148286, by rfl⟩ : syracuseStep 80197715 = 120296573) B120296573
theorem B53465143 : Blo 1827615 53465143 := bstep (se 1 (by rfl) ⟨40098857, by rfl⟩ : syracuseStep 53465143 = 80197715) B80197715
theorem B71286857 : Blo 1827615 71286857 := bstep (se 2 (by rfl) ⟨26732571, by rfl⟩ : syracuseStep 71286857 = 53465143) B53465143
theorem B47524571 : Blo 1827615 47524571 := bstep (se 1 (by rfl) ⟨35643428, by rfl⟩ : syracuseStep 47524571 = 71286857) B71286857
theorem B31683047 : Blo 1827615 31683047 := bstep (se 1 (by rfl) ⟨23762285, by rfl⟩ : syracuseStep 31683047 = 47524571) B47524571
theorem B84488125 : Blo 1827615 84488125 := bstep (se 3 (by rfl) ⟨15841523, by rfl⟩ : syracuseStep 84488125 = 31683047) B31683047
theorem B112650833 : Blo 1827615 112650833 := bstep (se 2 (by rfl) ⟨42244062, by rfl⟩ : syracuseStep 112650833 = 84488125) B84488125
theorem B75100555 : Blo 1827615 75100555 := bstep (se 1 (by rfl) ⟨56325416, by rfl⟩ : syracuseStep 75100555 = 112650833) B112650833
theorem B100134073 : Blo 1827615 100134073 := bstep (se 2 (by rfl) ⟨37550277, by rfl⟩ : syracuseStep 100134073 = 75100555) B75100555
theorem B133512097 : Blo 1827615 133512097 := bstep (se 2 (by rfl) ⟨50067036, by rfl⟩ : syracuseStep 133512097 = 100134073) B100134073
theorem B178016129 : Blo 1827615 178016129 := bstep (se 2 (by rfl) ⟨66756048, by rfl⟩ : syracuseStep 178016129 = 133512097) B133512097
theorem B118677419 : Blo 1827615 118677419 := bstep (se 1 (by rfl) ⟨89008064, by rfl⟩ : syracuseStep 118677419 = 178016129) B178016129
theorem B79118279 : Blo 1827615 79118279 := bstep (se 1 (by rfl) ⟨59338709, by rfl⟩ : syracuseStep 79118279 = 118677419) B118677419
theorem B52745519 : Blo 1827615 52745519 := bstep (se 1 (by rfl) ⟨39559139, by rfl⟩ : syracuseStep 52745519 = 79118279) B79118279
theorem B35163679 : Blo 1827615 35163679 := bstep (se 1 (by rfl) ⟨26372759, by rfl⟩ : syracuseStep 35163679 = 52745519) B52745519
theorem B46884905 : Blo 1827615 46884905 := bstep (se 2 (by rfl) ⟨17581839, by rfl⟩ : syracuseStep 46884905 = 35163679) B35163679
theorem B31256603 : Blo 1827615 31256603 := bstep (se 1 (by rfl) ⟨23442452, by rfl⟩ : syracuseStep 31256603 = 46884905) B46884905
theorem B20837735 : Blo 1827615 20837735 := bstep (se 1 (by rfl) ⟨15628301, by rfl⟩ : syracuseStep 20837735 = 31256603) B31256603
theorem B13891823 : Blo 1827615 13891823 := bstep (se 1 (by rfl) ⟨10418867, by rfl⟩ : syracuseStep 13891823 = 20837735) B20837735
theorem B9261215 : Blo 1827615 9261215 := bstep (se 1 (by rfl) ⟨6945911, by rfl⟩ : syracuseStep 9261215 = 13891823) B13891823
theorem B6174143 : Blo 1827615 6174143 := bstep (se 1 (by rfl) ⟨4630607, by rfl⟩ : syracuseStep 6174143 = 9261215) B9261215
theorem B4116095 : Blo 1827615 4116095 := bstep (se 1 (by rfl) ⟨3087071, by rfl⟩ : syracuseStep 4116095 = 6174143) B6174143
theorem B2744063 : Blo 1827615 2744063 := bstep (se 1 (by rfl) ⟨2058047, by rfl⟩ : syracuseStep 2744063 = 4116095) B4116095
theorem B1829375 : Blo 1827615 1829375 := bstep (se 1 (by rfl) ⟨1372031, by rfl⟩ : syracuseStep 1829375 = 2744063) B2744063

theorem C0 (j : ℕ) (h1 : 456903 ≤ j) (h2 : j ≤ 457403) : Blo 1827615 (4 * j + 3) := by
  interval_cases j
  · exact B1827615
  · exact B1827619
  · exact B1827623
  · exact B1827627
  · exact B1827631
  · exact B1827635
  · exact B1827639
  · exact B1827643
  · exact B1827647
  · exact B1827651
  · exact B1827655
  · exact B1827659
  · exact B1827663
  · exact B1827667
  · exact B1827671
  · exact B1827675
  · exact B1827679
  · exact B1827683
  · exact B1827687
  · exact B1827691
  · exact B1827695
  · exact B1827699
  · exact B1827703
  · exact B1827707
  · exact B1827711
  · exact B1827715
  · exact B1827719
  · exact B1827723
  · exact B1827727
  · exact B1827731
  · exact B1827735
  · exact B1827739
  · exact B1827743
  · exact B1827747
  · exact B1827751
  · exact B1827755
  · exact B1827759
  · exact B1827763
  · exact B1827767
  · exact B1827771
  · exact B1827775
  · exact B1827779
  · exact B1827783
  · exact B1827787
  · exact B1827791
  · exact B1827795
  · exact B1827799
  · exact B1827803
  · exact B1827807
  · exact B1827811
  · exact B1827815
  · exact B1827819
  · exact B1827823
  · exact B1827827
  · exact B1827831
  · exact B1827835
  · exact B1827839
  · exact B1827843
  · exact B1827847
  · exact B1827851
  · exact B1827855
  · exact B1827859
  · exact B1827863
  · exact B1827867
  · exact B1827871
  · exact B1827875
  · exact B1827879
  · exact B1827883
  · exact B1827887
  · exact B1827891
  · exact B1827895
  · exact B1827899
  · exact B1827903
  · exact B1827907
  · exact B1827911
  · exact B1827915
  · exact B1827919
  · exact B1827923
  · exact B1827927
  · exact B1827931
  · exact B1827935
  · exact B1827939
  · exact B1827943
  · exact B1827947
  · exact B1827951
  · exact B1827955
  · exact B1827959
  · exact B1827963
  · exact B1827967
  · exact B1827971
  · exact B1827975
  · exact B1827979
  · exact B1827983
  · exact B1827987
  · exact B1827991
  · exact B1827995
  · exact B1827999
  · exact B1828003
  · exact B1828007
  · exact B1828011
  · exact B1828015
  · exact B1828019
  · exact B1828023
  · exact B1828027
  · exact B1828031
  · exact B1828035
  · exact B1828039
  · exact B1828043
  · exact B1828047
  · exact B1828051
  · exact B1828055
  · exact B1828059
  · exact B1828063
  · exact B1828067
  · exact B1828071
  · exact B1828075
  · exact B1828079
  · exact B1828083
  · exact B1828087
  · exact B1828091
  · exact B1828095
  · exact B1828099
  · exact B1828103
  · exact B1828107
  · exact B1828111
  · exact B1828115
  · exact B1828119
  · exact B1828123
  · exact B1828127
  · exact B1828131
  · exact B1828135
  · exact B1828139
  · exact B1828143
  · exact B1828147
  · exact B1828151
  · exact B1828155
  · exact B1828159
  · exact B1828163
  · exact B1828167
  · exact B1828171
  · exact B1828175
  · exact B1828179
  · exact B1828183
  · exact B1828187
  · exact B1828191
  · exact B1828195
  · exact B1828199
  · exact B1828203
  · exact B1828207
  · exact B1828211
  · exact B1828215
  · exact B1828219
  · exact B1828223
  · exact B1828227
  · exact B1828231
  · exact B1828235
  · exact B1828239
  · exact B1828243
  · exact B1828247
  · exact B1828251
  · exact B1828255
  · exact B1828259
  · exact B1828263
  · exact B1828267
  · exact B1828271
  · exact B1828275
  · exact B1828279
  · exact B1828283
  · exact B1828287
  · exact B1828291
  · exact B1828295
  · exact B1828299
  · exact B1828303
  · exact B1828307
  · exact B1828311
  · exact B1828315
  · exact B1828319
  · exact B1828323
  · exact B1828327
  · exact B1828331
  · exact B1828335
  · exact B1828339
  · exact B1828343
  · exact B1828347
  · exact B1828351
  · exact B1828355
  · exact B1828359
  · exact B1828363
  · exact B1828367
  · exact B1828371
  · exact B1828375
  · exact B1828379
  · exact B1828383
  · exact B1828387
  · exact B1828391
  · exact B1828395
  · exact B1828399
  · exact B1828403
  · exact B1828407
  · exact B1828411
  · exact B1828415
  · exact B1828419
  · exact B1828423
  · exact B1828427
  · exact B1828431
  · exact B1828435
  · exact B1828439
  · exact B1828443
  · exact B1828447
  · exact B1828451
  · exact B1828455
  · exact B1828459
  · exact B1828463
  · exact B1828467
  · exact B1828471
  · exact B1828475
  · exact B1828479
  · exact B1828483
  · exact B1828487
  · exact B1828491
  · exact B1828495
  · exact B1828499
  · exact B1828503
  · exact B1828507
  · exact B1828511
  · exact B1828515
  · exact B1828519
  · exact B1828523
  · exact B1828527
  · exact B1828531
  · exact B1828535
  · exact B1828539
  · exact B1828543
  · exact B1828547
  · exact B1828551
  · exact B1828555
  · exact B1828559
  · exact B1828563
  · exact B1828567
  · exact B1828571
  · exact B1828575
  · exact B1828579
  · exact B1828583
  · exact B1828587
  · exact B1828591
  · exact B1828595
  · exact B1828599
  · exact B1828603
  · exact B1828607
  · exact B1828611
  · exact B1828615
  · exact B1828619
  · exact B1828623
  · exact B1828627
  · exact B1828631
  · exact B1828635
  · exact B1828639
  · exact B1828643
  · exact B1828647
  · exact B1828651
  · exact B1828655
  · exact B1828659
  · exact B1828663
  · exact B1828667
  · exact B1828671
  · exact B1828675
  · exact B1828679
  · exact B1828683
  · exact B1828687
  · exact B1828691
  · exact B1828695
  · exact B1828699
  · exact B1828703
  · exact B1828707
  · exact B1828711
  · exact B1828715
  · exact B1828719
  · exact B1828723
  · exact B1828727
  · exact B1828731
  · exact B1828735
  · exact B1828739
  · exact B1828743
  · exact B1828747
  · exact B1828751
  · exact B1828755
  · exact B1828759
  · exact B1828763
  · exact B1828767
  · exact B1828771
  · exact B1828775
  · exact B1828779
  · exact B1828783
  · exact B1828787
  · exact B1828791
  · exact B1828795
  · exact B1828799
  · exact B1828803
  · exact B1828807
  · exact B1828811
  · exact B1828815
  · exact B1828819
  · exact B1828823
  · exact B1828827
  · exact B1828831
  · exact B1828835
  · exact B1828839
  · exact B1828843
  · exact B1828847
  · exact B1828851
  · exact B1828855
  · exact B1828859
  · exact B1828863
  · exact B1828867
  · exact B1828871
  · exact B1828875
  · exact B1828879
  · exact B1828883
  · exact B1828887
  · exact B1828891
  · exact B1828895
  · exact B1828899
  · exact B1828903
  · exact B1828907
  · exact B1828911
  · exact B1828915
  · exact B1828919
  · exact B1828923
  · exact B1828927
  · exact B1828931
  · exact B1828935
  · exact B1828939
  · exact B1828943
  · exact B1828947
  · exact B1828951
  · exact B1828955
  · exact B1828959
  · exact B1828963
  · exact B1828967
  · exact B1828971
  · exact B1828975
  · exact B1828979
  · exact B1828983
  · exact B1828987
  · exact B1828991
  · exact B1828995
  · exact B1828999
  · exact B1829003
  · exact B1829007
  · exact B1829011
  · exact B1829015
  · exact B1829019
  · exact B1829023
  · exact B1829027
  · exact B1829031
  · exact B1829035
  · exact B1829039
  · exact B1829043
  · exact B1829047
  · exact B1829051
  · exact B1829055
  · exact B1829059
  · exact B1829063
  · exact B1829067
  · exact B1829071
  · exact B1829075
  · exact B1829079
  · exact B1829083
  · exact B1829087
  · exact B1829091
  · exact B1829095
  · exact B1829099
  · exact B1829103
  · exact B1829107
  · exact B1829111
  · exact B1829115
  · exact B1829119
  · exact B1829123
  · exact B1829127
  · exact B1829131
  · exact B1829135
  · exact B1829139
  · exact B1829143
  · exact B1829147
  · exact B1829151
  · exact B1829155
  · exact B1829159
  · exact B1829163
  · exact B1829167
  · exact B1829171
  · exact B1829175
  · exact B1829179
  · exact B1829183
  · exact B1829187
  · exact B1829191
  · exact B1829195
  · exact B1829199
  · exact B1829203
  · exact B1829207
  · exact B1829211
  · exact B1829215
  · exact B1829219
  · exact B1829223
  · exact B1829227
  · exact B1829231
  · exact B1829235
  · exact B1829239
  · exact B1829243
  · exact B1829247
  · exact B1829251
  · exact B1829255
  · exact B1829259
  · exact B1829263
  · exact B1829267
  · exact B1829271
  · exact B1829275
  · exact B1829279
  · exact B1829283
  · exact B1829287
  · exact B1829291
  · exact B1829295
  · exact B1829299
  · exact B1829303
  · exact B1829307
  · exact B1829311
  · exact B1829315
  · exact B1829319
  · exact B1829323
  · exact B1829327
  · exact B1829331
  · exact B1829335
  · exact B1829339
  · exact B1829343
  · exact B1829347
  · exact B1829351
  · exact B1829355
  · exact B1829359
  · exact B1829363
  · exact B1829367
  · exact B1829371
  · exact B1829375
  · exact B1829379
  · exact B1829383
  · exact B1829387
  · exact B1829391
  · exact B1829395
  · exact B1829399
  · exact B1829403
  · exact B1829407
  · exact B1829411
  · exact B1829415
  · exact B1829419
  · exact B1829423
  · exact B1829427
  · exact B1829431
  · exact B1829435
  · exact B1829439
  · exact B1829443
  · exact B1829447
  · exact B1829451
  · exact B1829455
  · exact B1829459
  · exact B1829463
  · exact B1829467
  · exact B1829471
  · exact B1829475
  · exact B1829479
  · exact B1829483
  · exact B1829487
  · exact B1829491
  · exact B1829495
  · exact B1829499
  · exact B1829503
  · exact B1829507
  · exact B1829511
  · exact B1829515
  · exact B1829519
  · exact B1829523
  · exact B1829527
  · exact B1829531
  · exact B1829535
  · exact B1829539
  · exact B1829543
  · exact B1829547
  · exact B1829551
  · exact B1829555
  · exact B1829559
  · exact B1829563
  · exact B1829567
  · exact B1829571
  · exact B1829575
  · exact B1829579
  · exact B1829583
  · exact B1829587
  · exact B1829591
  · exact B1829595
  · exact B1829599
  · exact B1829603
  · exact B1829607
  · exact B1829611
  · exact B1829615

theorem solution (m : ℕ) (hlo : 1827615 ≤ m) (hhi : m ≤ 1829615) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 456903 ≤ j := by omega
    have hj2 : j ≤ 457403 := by omega
    have hb : Blo 1827615 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
