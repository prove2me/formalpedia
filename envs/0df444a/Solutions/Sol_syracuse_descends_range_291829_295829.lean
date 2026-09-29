-- Prove2me | solution 1 for syracuse_descends_range_291829_295829
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:17.255818+00:00
-- url     : https://prove2.me/submissions/00b05abd-bb2c-423b-99bd-d32408d8f4f1

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


theorem B557093 : Blo 291829 557093 := bbase (se 4 (by rfl) ⟨52227, by rfl⟩ : syracuseStep 557093 = 104455) (by norm_num)
theorem B2228309 : Blo 291829 2228309 := bbase (se 8 (by rfl) ⟨13056, by rfl⟩ : syracuseStep 2228309 = 26113) (by norm_num)
theorem B753893 : Blo 291829 753893 := bbase (se 4 (by rfl) ⟨70677, by rfl⟩ : syracuseStep 753893 = 141355) (by norm_num)
theorem B557381 : Blo 291829 557381 := bbase (se 4 (by rfl) ⟨52254, by rfl⟩ : syracuseStep 557381 = 104509) (by norm_num)
theorem B557533 : Blo 291829 557533 := bbase (se 3 (by rfl) ⟨104537, by rfl⟩ : syracuseStep 557533 = 209075) (by norm_num)
theorem B295529 : Blo 291829 295529 := bbase (se 2 (by rfl) ⟨110823, by rfl⟩ : syracuseStep 295529 = 221647) (by norm_num)
theorem B328333 : Blo 291829 328333 := bbase (se 3 (by rfl) ⟨61562, by rfl⟩ : syracuseStep 328333 = 123125) (by norm_num)
theorem B328369 : Blo 291829 328369 := bbase (se 2 (by rfl) ⟨123138, by rfl⟩ : syracuseStep 328369 = 246277) (by norm_num)
theorem B328405 : Blo 291829 328405 := bbase (se 7 (by rfl) ⟨3848, by rfl⟩ : syracuseStep 328405 = 7697) (by norm_num)
theorem B328441 : Blo 291829 328441 := bbase (se 2 (by rfl) ⟨123165, by rfl⟩ : syracuseStep 328441 = 246331) (by norm_num)
theorem B557837 : Blo 291829 557837 := bbase (se 3 (by rfl) ⟨104594, by rfl⟩ : syracuseStep 557837 = 209189) (by norm_num)
theorem B328477 : Blo 291829 328477 := bbase (se 3 (by rfl) ⟨61589, by rfl⟩ : syracuseStep 328477 = 123179) (by norm_num)
theorem B328513 : Blo 291829 328513 := bbase (se 2 (by rfl) ⟨123192, by rfl⟩ : syracuseStep 328513 = 246385) (by norm_num)
theorem B328549 : Blo 291829 328549 := bbase (se 4 (by rfl) ⟨30801, by rfl⟩ : syracuseStep 328549 = 61603) (by norm_num)
theorem B328585 : Blo 291829 328585 := bbase (se 2 (by rfl) ⟨123219, by rfl⟩ : syracuseStep 328585 = 246439) (by norm_num)
theorem B328621 : Blo 291829 328621 := bbase (se 3 (by rfl) ⟨61616, by rfl⟩ : syracuseStep 328621 = 123233) (by norm_num)
theorem B492493 : Blo 291829 492493 := bbase (se 3 (by rfl) ⟨92342, by rfl⟩ : syracuseStep 492493 = 184685) (by norm_num)
theorem B328657 : Blo 291829 328657 := bbase (se 2 (by rfl) ⟨123246, by rfl⟩ : syracuseStep 328657 = 246493) (by norm_num)
theorem B328693 : Blo 291829 328693 := bbase (se 5 (by rfl) ⟨15407, by rfl⟩ : syracuseStep 328693 = 30815) (by norm_num)
theorem B623629 : Blo 291829 623629 := bbase (se 3 (by rfl) ⟨116930, by rfl⟩ : syracuseStep 623629 = 233861) (by norm_num)
theorem B328729 : Blo 291829 328729 := bbase (se 2 (by rfl) ⟨123273, by rfl⟩ : syracuseStep 328729 = 246547) (by norm_num)
theorem B492581 : Blo 291829 492581 := bbase (se 4 (by rfl) ⟨46179, by rfl⟩ : syracuseStep 492581 = 92359) (by norm_num)
theorem B328765 : Blo 291829 328765 := bbase (se 3 (by rfl) ⟨61643, by rfl⟩ : syracuseStep 328765 = 123287) (by norm_num)
theorem B2688085 : Blo 291829 2688085 := bbase (se 8 (by rfl) ⟨15750, by rfl⟩ : syracuseStep 2688085 = 31501) (by norm_num)
theorem B328801 : Blo 291829 328801 := bbase (se 2 (by rfl) ⟨123300, by rfl⟩ : syracuseStep 328801 = 246601) (by norm_num)
theorem B328837 : Blo 291829 328837 := bbase (se 4 (by rfl) ⟨30828, by rfl⟩ : syracuseStep 328837 = 61657) (by norm_num)
theorem B492709 : Blo 291829 492709 := bbase (se 4 (by rfl) ⟨46191, by rfl⟩ : syracuseStep 492709 = 92383) (by norm_num)
theorem B328873 : Blo 291829 328873 := bbase (se 2 (by rfl) ⟨123327, by rfl⟩ : syracuseStep 328873 = 246655) (by norm_num)
theorem B328909 : Blo 291829 328909 := bbase (se 3 (by rfl) ⟨61670, by rfl⟩ : syracuseStep 328909 = 123341) (by norm_num)
theorem B2819285 : Blo 291829 2819285 := bbase (se 7 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 2819285 = 66077) (by norm_num)
theorem B656621 : Blo 291829 656621 := bbase (se 3 (by rfl) ⟨123116, by rfl⟩ : syracuseStep 656621 = 246233) (by norm_num)
theorem B328945 : Blo 291829 328945 := bbase (se 2 (by rfl) ⟨123354, by rfl⟩ : syracuseStep 328945 = 246709) (by norm_num)
theorem B492797 : Blo 291829 492797 := bbase (se 3 (by rfl) ⟨92399, by rfl⟩ : syracuseStep 492797 = 184799) (by norm_num)
theorem B328981 : Blo 291829 328981 := bbase (se 6 (by rfl) ⟨7710, by rfl⟩ : syracuseStep 328981 = 15421) (by norm_num)
theorem B656693 : Blo 291829 656693 := bbase (se 5 (by rfl) ⟨30782, by rfl⟩ : syracuseStep 656693 = 61565) (by norm_num)
theorem B329017 : Blo 291829 329017 := bbase (se 2 (by rfl) ⟨123381, by rfl⟩ : syracuseStep 329017 = 246763) (by norm_num)
theorem B1115477 : Blo 291829 1115477 := bbase (se 12 (by rfl) ⟨408, by rfl⟩ : syracuseStep 1115477 = 817) (by norm_num)
theorem B329053 : Blo 291829 329053 := bbase (se 3 (by rfl) ⟨61697, by rfl⟩ : syracuseStep 329053 = 123395) (by norm_num)
theorem B296309 : Blo 291829 296309 := bbase (se 5 (by rfl) ⟨13889, by rfl⟩ : syracuseStep 296309 = 27779) (by norm_num)
theorem B656765 : Blo 291829 656765 := bbase (se 3 (by rfl) ⟨123143, by rfl⟩ : syracuseStep 656765 = 246287) (by norm_num)
theorem B492925 : Blo 291829 492925 := bbase (se 3 (by rfl) ⟨92423, by rfl⟩ : syracuseStep 492925 = 184847) (by norm_num)
theorem B329089 : Blo 291829 329089 := bbase (se 2 (by rfl) ⟨123408, by rfl⟩ : syracuseStep 329089 = 246817) (by norm_num)
theorem B329125 : Blo 291829 329125 := bbase (se 4 (by rfl) ⟨30855, by rfl⟩ : syracuseStep 329125 = 61711) (by norm_num)
theorem B656837 : Blo 291829 656837 := bbase (se 4 (by rfl) ⟨61578, by rfl⟩ : syracuseStep 656837 = 123157) (by norm_num)
theorem B329161 : Blo 291829 329161 := bbase (se 2 (by rfl) ⟨123435, by rfl⟩ : syracuseStep 329161 = 246871) (by norm_num)
theorem B493013 : Blo 291829 493013 := bbase (se 7 (by rfl) ⟨5777, by rfl⟩ : syracuseStep 493013 = 11555) (by norm_num)
theorem B329197 : Blo 291829 329197 := bbase (se 3 (by rfl) ⟨61724, by rfl⟩ : syracuseStep 329197 = 123449) (by norm_num)
theorem B394733 : Blo 291829 394733 := bbase (se 3 (by rfl) ⟨74012, by rfl⟩ : syracuseStep 394733 = 148025) (by norm_num)
theorem B558589 : Blo 291829 558589 := bbase (se 3 (by rfl) ⟨104735, by rfl⟩ : syracuseStep 558589 = 209471) (by norm_num)
theorem B656909 : Blo 291829 656909 := bbase (se 3 (by rfl) ⟨123170, by rfl⟩ : syracuseStep 656909 = 246341) (by norm_num)
theorem B329233 : Blo 291829 329233 := bbase (se 2 (by rfl) ⟨123462, by rfl⟩ : syracuseStep 329233 = 246925) (by norm_num)
theorem B329269 : Blo 291829 329269 := bbase (se 5 (by rfl) ⟨15434, by rfl⟩ : syracuseStep 329269 = 30869) (by norm_num)
theorem B362053 : Blo 291829 362053 := bbase (se 4 (by rfl) ⟨33942, by rfl⟩ : syracuseStep 362053 = 67885) (by norm_num)
theorem B656981 : Blo 291829 656981 := bbase (se 8 (by rfl) ⟨3849, by rfl⟩ : syracuseStep 656981 = 7699) (by norm_num)
theorem B493141 : Blo 291829 493141 := bbase (se 8 (by rfl) ⟨2889, by rfl⟩ : syracuseStep 493141 = 5779) (by norm_num)
theorem B329305 : Blo 291829 329305 := bbase (se 2 (by rfl) ⟨123489, by rfl⟩ : syracuseStep 329305 = 246979) (by norm_num)
theorem B1115765 : Blo 291829 1115765 := bbase (se 5 (by rfl) ⟨52301, by rfl⟩ : syracuseStep 1115765 = 104603) (by norm_num)
theorem B329341 : Blo 291829 329341 := bbase (se 3 (by rfl) ⟨61751, by rfl⟩ : syracuseStep 329341 = 123503) (by norm_num)
theorem B558733 : Blo 291829 558733 := bbase (se 3 (by rfl) ⟨104762, by rfl⟩ : syracuseStep 558733 = 209525) (by norm_num)
theorem B657053 : Blo 291829 657053 := bbase (se 3 (by rfl) ⟨123197, by rfl⟩ : syracuseStep 657053 = 246395) (by norm_num)
theorem B329377 : Blo 291829 329377 := bbase (se 2 (by rfl) ⟨123516, by rfl⟩ : syracuseStep 329377 = 247033) (by norm_num)
theorem B493229 : Blo 291829 493229 := bbase (se 3 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 493229 = 184961) (by norm_num)
theorem B296629 : Blo 291829 296629 := bbase (se 5 (by rfl) ⟨13904, by rfl⟩ : syracuseStep 296629 = 27809) (by norm_num)
theorem B329413 : Blo 291829 329413 := bbase (se 4 (by rfl) ⟨30882, by rfl⟩ : syracuseStep 329413 = 61765) (by norm_num)
theorem B657125 : Blo 291829 657125 := bbase (se 4 (by rfl) ⟨61605, by rfl⟩ : syracuseStep 657125 = 123211) (by norm_num)
theorem B329449 : Blo 291829 329449 := bbase (se 2 (by rfl) ⟨123543, by rfl⟩ : syracuseStep 329449 = 247087) (by norm_num)
theorem B329485 : Blo 291829 329485 := bbase (se 3 (by rfl) ⟨61778, by rfl⟩ : syracuseStep 329485 = 123557) (by norm_num)
theorem B657197 : Blo 291829 657197 := bbase (se 3 (by rfl) ⟨123224, by rfl⟩ : syracuseStep 657197 = 246449) (by norm_num)
theorem B493357 : Blo 291829 493357 := bbase (se 3 (by rfl) ⟨92504, by rfl⟩ : syracuseStep 493357 = 185009) (by norm_num)
theorem B558893 : Blo 291829 558893 := bbase (se 3 (by rfl) ⟨104792, by rfl⟩ : syracuseStep 558893 = 209585) (by norm_num)
theorem B329521 : Blo 291829 329521 := bbase (se 2 (by rfl) ⟨123570, by rfl⟩ : syracuseStep 329521 = 247141) (by norm_num)
theorem B329557 : Blo 291829 329557 := bbase (se 9 (by rfl) ⟨965, by rfl⟩ : syracuseStep 329557 = 1931) (by norm_num)
theorem B591709 : Blo 291829 591709 := bbase (se 3 (by rfl) ⟨110945, by rfl⟩ : syracuseStep 591709 = 221891) (by norm_num)
theorem B657269 : Blo 291829 657269 := bbase (se 5 (by rfl) ⟨30809, by rfl⟩ : syracuseStep 657269 = 61619) (by norm_num)
theorem B329593 : Blo 291829 329593 := bbase (se 2 (by rfl) ⟨123597, by rfl⟩ : syracuseStep 329593 = 247195) (by norm_num)
theorem B493445 : Blo 291829 493445 := bbase (se 4 (by rfl) ⟨46260, by rfl⟩ : syracuseStep 493445 = 92521) (by norm_num)
theorem B1410949 : Blo 291829 1410949 := bbase (se 4 (by rfl) ⟨132276, by rfl⟩ : syracuseStep 1410949 = 264553) (by norm_num)
theorem B395165 : Blo 291829 395165 := bbase (se 3 (by rfl) ⟨74093, by rfl⟩ : syracuseStep 395165 = 148187) (by norm_num)
theorem B329629 : Blo 291829 329629 := bbase (se 3 (by rfl) ⟨61805, by rfl⟩ : syracuseStep 329629 = 123611) (by norm_num)
theorem B985013 : Blo 291829 985013 := bbase (se 5 (by rfl) ⟨46172, by rfl⟩ : syracuseStep 985013 = 92345) (by norm_num)
theorem B657341 : Blo 291829 657341 := bbase (se 3 (by rfl) ⟨123251, by rfl⟩ : syracuseStep 657341 = 246503) (by norm_num)
theorem B296893 : Blo 291829 296893 := bbase (se 3 (by rfl) ⟨55667, by rfl⟩ : syracuseStep 296893 = 111335) (by norm_num)
theorem B559037 : Blo 291829 559037 := bbase (se 3 (by rfl) ⟨104819, by rfl⟩ : syracuseStep 559037 = 209639) (by norm_num)
theorem B329665 : Blo 291829 329665 := bbase (se 2 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 329665 = 247249) (by norm_num)
theorem B329701 : Blo 291829 329701 := bbase (se 4 (by rfl) ⟨30909, by rfl⟩ : syracuseStep 329701 = 61819) (by norm_num)
theorem B657413 : Blo 291829 657413 := bbase (se 4 (by rfl) ⟨61632, by rfl⟩ : syracuseStep 657413 = 123265) (by norm_num)
theorem B493573 : Blo 291829 493573 := bbase (se 4 (by rfl) ⟨46272, by rfl⟩ : syracuseStep 493573 = 92545) (by norm_num)
theorem B329737 : Blo 291829 329737 := bbase (se 2 (by rfl) ⟨123651, by rfl⟩ : syracuseStep 329737 = 247303) (by norm_num)
theorem B1673237 : Blo 291829 1673237 := bbase (se 6 (by rfl) ⟨39216, by rfl⟩ : syracuseStep 1673237 = 78433) (by norm_num)
theorem B329773 : Blo 291829 329773 := bbase (se 3 (by rfl) ⟨61832, by rfl⟩ : syracuseStep 329773 = 123665) (by norm_num)
theorem B657485 : Blo 291829 657485 := bbase (se 3 (by rfl) ⟨123278, by rfl⟩ : syracuseStep 657485 = 246557) (by norm_num)
theorem B329809 : Blo 291829 329809 := bbase (se 2 (by rfl) ⟨123678, by rfl⟩ : syracuseStep 329809 = 247357) (by norm_num)
theorem B493661 : Blo 291829 493661 := bbase (se 3 (by rfl) ⟨92561, by rfl⟩ : syracuseStep 493661 = 185123) (by norm_num)
theorem B395381 : Blo 291829 395381 := bbase (se 5 (by rfl) ⟨18533, by rfl⟩ : syracuseStep 395381 = 37067) (by norm_num)
theorem B329845 : Blo 291829 329845 := bbase (se 5 (by rfl) ⟨15461, by rfl⟩ : syracuseStep 329845 = 30923) (by norm_num)
theorem B657557 : Blo 291829 657557 := bbase (se 6 (by rfl) ⟨15411, by rfl⟩ : syracuseStep 657557 = 30823) (by norm_num)
theorem B329881 : Blo 291829 329881 := bbase (se 2 (by rfl) ⟨123705, by rfl⟩ : syracuseStep 329881 = 247411) (by norm_num)
theorem B329917 : Blo 291829 329917 := bbase (se 3 (by rfl) ⟨61859, by rfl⟩ : syracuseStep 329917 = 123719) (by norm_num)
theorem B657629 : Blo 291829 657629 := bbase (se 3 (by rfl) ⟨123305, by rfl⟩ : syracuseStep 657629 = 246611) (by norm_num)
theorem B493789 : Blo 291829 493789 := bbase (se 3 (by rfl) ⟨92585, by rfl⟩ : syracuseStep 493789 = 185171) (by norm_num)
theorem B559325 : Blo 291829 559325 := bbase (se 3 (by rfl) ⟨104873, by rfl⟩ : syracuseStep 559325 = 209747) (by norm_num)
theorem B329953 : Blo 291829 329953 := bbase (se 2 (by rfl) ⟨123732, by rfl⟩ : syracuseStep 329953 = 247465) (by norm_num)
theorem B297193 : Blo 291829 297193 := bbase (se 2 (by rfl) ⟨111447, by rfl⟩ : syracuseStep 297193 = 222895) (by norm_num)
theorem B329989 : Blo 291829 329989 := bbase (se 4 (by rfl) ⟨30936, by rfl⟩ : syracuseStep 329989 = 61873) (by norm_num)
theorem B657701 : Blo 291829 657701 := bbase (se 4 (by rfl) ⟨61659, by rfl⟩ : syracuseStep 657701 = 123319) (by norm_num)
theorem B330025 : Blo 291829 330025 := bbase (se 2 (by rfl) ⟨123759, by rfl⟩ : syracuseStep 330025 = 247519) (by norm_num)
theorem B493877 : Blo 291829 493877 := bbase (se 5 (by rfl) ⟨23150, by rfl⟩ : syracuseStep 493877 = 46301) (by norm_num)
theorem B330061 : Blo 291829 330061 := bbase (se 3 (by rfl) ⟨61886, by rfl⟩ : syracuseStep 330061 = 123773) (by norm_num)
theorem B985445 : Blo 291829 985445 := bbase (se 4 (by rfl) ⟨92385, by rfl⟩ : syracuseStep 985445 = 184771) (by norm_num)
theorem B657773 : Blo 291829 657773 := bbase (se 3 (by rfl) ⟨123332, by rfl⟩ : syracuseStep 657773 = 246665) (by norm_num)
theorem B330097 : Blo 291829 330097 := bbase (se 2 (by rfl) ⟨123786, by rfl⟩ : syracuseStep 330097 = 247573) (by norm_num)
theorem B559477 : Blo 291829 559477 := bbase (se 5 (by rfl) ⟨26225, by rfl⟩ : syracuseStep 559477 = 52451) (by norm_num)
theorem B330133 : Blo 291829 330133 := bbase (se 6 (by rfl) ⟨7737, by rfl⟩ : syracuseStep 330133 = 15475) (by norm_num)
theorem B1247669 : Blo 291829 1247669 := bbase (se 5 (by rfl) ⟨58484, by rfl⟩ : syracuseStep 1247669 = 116969) (by norm_num)
theorem B657845 : Blo 291829 657845 := bbase (se 5 (by rfl) ⟨30836, by rfl⟩ : syracuseStep 657845 = 61673) (by norm_num)
theorem B494005 : Blo 291829 494005 := bbase (se 5 (by rfl) ⟨23156, by rfl⟩ : syracuseStep 494005 = 46313) (by norm_num)
theorem B330169 : Blo 291829 330169 := bbase (se 2 (by rfl) ⟨123813, by rfl⟩ : syracuseStep 330169 = 247627) (by norm_num)
theorem B330205 : Blo 291829 330205 := bbase (se 3 (by rfl) ⟨61913, by rfl⟩ : syracuseStep 330205 = 123827) (by norm_num)
theorem B625133 : Blo 291829 625133 := bbase (se 3 (by rfl) ⟨117212, by rfl⟩ : syracuseStep 625133 = 234425) (by norm_num)
theorem B657917 : Blo 291829 657917 := bbase (se 3 (by rfl) ⟨123359, by rfl⟩ : syracuseStep 657917 = 246719) (by norm_num)
theorem B330241 : Blo 291829 330241 := bbase (se 2 (by rfl) ⟨123840, by rfl⟩ : syracuseStep 330241 = 247681) (by norm_num)
theorem B494093 : Blo 291829 494093 := bbase (se 3 (by rfl) ⟨92642, by rfl⟩ : syracuseStep 494093 = 185285) (by norm_num)
theorem B330277 : Blo 291829 330277 := bbase (se 4 (by rfl) ⟨30963, by rfl⟩ : syracuseStep 330277 = 61927) (by norm_num)
theorem B657989 : Blo 291829 657989 := bbase (se 4 (by rfl) ⟨61686, by rfl⟩ : syracuseStep 657989 = 123373) (by norm_num)
theorem B330313 : Blo 291829 330313 := bbase (se 2 (by rfl) ⟨123867, by rfl⟩ : syracuseStep 330313 = 247735) (by norm_num)
theorem B330349 : Blo 291829 330349 := bbase (se 3 (by rfl) ⟨61940, by rfl⟩ : syracuseStep 330349 = 123881) (by norm_num)
theorem B625277 : Blo 291829 625277 := bbase (se 3 (by rfl) ⟨117239, by rfl⟩ : syracuseStep 625277 = 234479) (by norm_num)
theorem B658061 : Blo 291829 658061 := bbase (se 3 (by rfl) ⟨123386, by rfl⟩ : syracuseStep 658061 = 246773) (by norm_num)
theorem B494221 : Blo 291829 494221 := bbase (se 3 (by rfl) ⟨92666, by rfl⟩ : syracuseStep 494221 = 185333) (by norm_num)
theorem B330385 : Blo 291829 330385 := bbase (se 2 (by rfl) ⟨123894, by rfl⟩ : syracuseStep 330385 = 247789) (by norm_num)
theorem B559781 : Blo 291829 559781 := bbase (se 4 (by rfl) ⟨52479, by rfl⟩ : syracuseStep 559781 = 104959) (by norm_num)
theorem B330421 : Blo 291829 330421 := bbase (se 5 (by rfl) ⟨15488, by rfl⟩ : syracuseStep 330421 = 30977) (by norm_num)
theorem B395965 : Blo 291829 395965 := bbase (se 3 (by rfl) ⟨74243, by rfl⟩ : syracuseStep 395965 = 148487) (by norm_num)
theorem B1247957 : Blo 291829 1247957 := bbase (se 7 (by rfl) ⟨14624, by rfl⟩ : syracuseStep 1247957 = 29249) (by norm_num)
theorem B658133 : Blo 291829 658133 := bbase (se 7 (by rfl) ⟨7712, by rfl⟩ : syracuseStep 658133 = 15425) (by norm_num)
theorem B330457 : Blo 291829 330457 := bbase (se 2 (by rfl) ⟨123921, by rfl⟩ : syracuseStep 330457 = 247843) (by norm_num)
theorem B494309 : Blo 291829 494309 := bbase (se 4 (by rfl) ⟨46341, by rfl⟩ : syracuseStep 494309 = 92683) (by norm_num)
theorem B330493 : Blo 291829 330493 := bbase (se 3 (by rfl) ⟨61967, by rfl⟩ : syracuseStep 330493 = 123935) (by norm_num)
theorem B985877 : Blo 291829 985877 := bbase (se 6 (by rfl) ⟨23106, by rfl⟩ : syracuseStep 985877 = 46213) (by norm_num)
theorem B1116949 : Blo 291829 1116949 := bbase (se 6 (by rfl) ⟨26178, by rfl⟩ : syracuseStep 1116949 = 52357) (by norm_num)
theorem B658205 : Blo 291829 658205 := bbase (se 3 (by rfl) ⟨123413, by rfl⟩ : syracuseStep 658205 = 246827) (by norm_num)
theorem B330529 : Blo 291829 330529 := bbase (se 2 (by rfl) ⟨123948, by rfl⟩ : syracuseStep 330529 = 247897) (by norm_num)
theorem B363317 : Blo 291829 363317 := bbase (se 5 (by rfl) ⟨17030, by rfl⟩ : syracuseStep 363317 = 34061) (by norm_num)
theorem B330565 : Blo 291829 330565 := bbase (se 4 (by rfl) ⟨30990, by rfl⟩ : syracuseStep 330565 = 61981) (by norm_num)
theorem B658277 : Blo 291829 658277 := bbase (se 4 (by rfl) ⟨61713, by rfl⟩ : syracuseStep 658277 = 123427) (by norm_num)
theorem B494437 : Blo 291829 494437 := bbase (se 4 (by rfl) ⟨46353, by rfl⟩ : syracuseStep 494437 = 92707) (by norm_num)
theorem B330601 : Blo 291829 330601 := bbase (se 2 (by rfl) ⟨123975, by rfl⟩ : syracuseStep 330601 = 247951) (by norm_num)
theorem B330637 : Blo 291829 330637 := bbase (se 3 (by rfl) ⟨61994, by rfl⟩ : syracuseStep 330637 = 123989) (by norm_num)
theorem B658349 : Blo 291829 658349 := bbase (se 3 (by rfl) ⟨123440, by rfl⟩ : syracuseStep 658349 = 246881) (by norm_num)
theorem B330673 : Blo 291829 330673 := bbase (se 2 (by rfl) ⟨124002, by rfl⟩ : syracuseStep 330673 = 248005) (by norm_num)
theorem B494525 : Blo 291829 494525 := bbase (se 3 (by rfl) ⟨92723, by rfl⟩ : syracuseStep 494525 = 185447) (by norm_num)
theorem B330709 : Blo 291829 330709 := bbase (se 7 (by rfl) ⟨3875, by rfl⟩ : syracuseStep 330709 = 7751) (by norm_num)
theorem B625637 : Blo 291829 625637 := bbase (se 4 (by rfl) ⟨58653, by rfl⟩ : syracuseStep 625637 = 117307) (by norm_num)
theorem B658421 : Blo 291829 658421 := bbase (se 5 (by rfl) ⟨30863, by rfl⟩ : syracuseStep 658421 = 61727) (by norm_num)
theorem B330745 : Blo 291829 330745 := bbase (se 2 (by rfl) ⟨124029, by rfl⟩ : syracuseStep 330745 = 248059) (by norm_num)
theorem B330781 : Blo 291829 330781 := bbase (se 3 (by rfl) ⟨62021, by rfl⟩ : syracuseStep 330781 = 124043) (by norm_num)
theorem B658493 : Blo 291829 658493 := bbase (se 3 (by rfl) ⟨123467, by rfl⟩ : syracuseStep 658493 = 246935) (by norm_num)
theorem B494653 : Blo 291829 494653 := bbase (se 3 (by rfl) ⟨92747, by rfl⟩ : syracuseStep 494653 = 185495) (by norm_num)
theorem B330817 : Blo 291829 330817 := bbase (se 2 (by rfl) ⟨124056, by rfl⟩ : syracuseStep 330817 = 248113) (by norm_num)
theorem B1117253 : Blo 291829 1117253 := bbase (se 4 (by rfl) ⟨104742, by rfl⟩ : syracuseStep 1117253 = 209485) (by norm_num)
theorem B330853 : Blo 291829 330853 := bbase (se 4 (by rfl) ⟨31017, by rfl⟩ : syracuseStep 330853 = 62035) (by norm_num)
theorem B527477 : Blo 291829 527477 := bbase (se 5 (by rfl) ⟨24725, by rfl⟩ : syracuseStep 527477 = 49451) (by norm_num)
theorem B658565 : Blo 291829 658565 := bbase (se 4 (by rfl) ⟨61740, by rfl⟩ : syracuseStep 658565 = 123481) (by norm_num)
theorem B756869 : Blo 291829 756869 := bbase (se 4 (by rfl) ⟨70956, by rfl⟩ : syracuseStep 756869 = 141913) (by norm_num)
theorem B330889 : Blo 291829 330889 := bbase (se 2 (by rfl) ⟨124083, by rfl⟩ : syracuseStep 330889 = 248167) (by norm_num)
theorem B494741 : Blo 291829 494741 := bbase (se 6 (by rfl) ⟨11595, by rfl⟩ : syracuseStep 494741 = 23191) (by norm_num)
theorem B330925 : Blo 291829 330925 := bbase (se 3 (by rfl) ⟨62048, by rfl⟩ : syracuseStep 330925 = 124097) (by norm_num)
theorem B986309 : Blo 291829 986309 := bbase (se 4 (by rfl) ⟨92466, by rfl⟩ : syracuseStep 986309 = 184933) (by norm_num)
theorem B658637 : Blo 291829 658637 := bbase (se 3 (by rfl) ⟨123494, by rfl⟩ : syracuseStep 658637 = 246989) (by norm_num)
theorem B330961 : Blo 291829 330961 := bbase (se 2 (by rfl) ⟨124110, by rfl⟩ : syracuseStep 330961 = 248221) (by norm_num)
theorem B330997 : Blo 291829 330997 := bbase (se 5 (by rfl) ⟨15515, by rfl⟩ : syracuseStep 330997 = 31031) (by norm_num)
theorem B658709 : Blo 291829 658709 := bbase (se 6 (by rfl) ⟨15438, by rfl⟩ : syracuseStep 658709 = 30877) (by norm_num)
theorem B494869 : Blo 291829 494869 := bbase (se 6 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 494869 = 23197) (by norm_num)
theorem B331033 : Blo 291829 331033 := bbase (se 2 (by rfl) ⟨124137, by rfl⟩ : syracuseStep 331033 = 248275) (by norm_num)
theorem B1477925 : Blo 291829 1477925 := bbase (se 4 (by rfl) ⟨138555, by rfl⟩ : syracuseStep 1477925 = 277111) (by norm_num)
theorem B331069 : Blo 291829 331069 := bbase (se 3 (by rfl) ⟨62075, by rfl⟩ : syracuseStep 331069 = 124151) (by norm_num)
theorem B658781 : Blo 291829 658781 := bbase (se 3 (by rfl) ⟨123521, by rfl⟩ : syracuseStep 658781 = 247043) (by norm_num)
theorem B331105 : Blo 291829 331105 := bbase (se 2 (by rfl) ⟨124164, by rfl⟩ : syracuseStep 331105 = 248329) (by norm_num)
theorem B494957 : Blo 291829 494957 := bbase (se 3 (by rfl) ⟨92804, by rfl⟩ : syracuseStep 494957 = 185609) (by norm_num)
theorem B331141 : Blo 291829 331141 := bbase (se 4 (by rfl) ⟨31044, by rfl⟩ : syracuseStep 331141 = 62089) (by norm_num)
theorem B560533 : Blo 291829 560533 := bbase (se 6 (by rfl) ⟨13137, by rfl⟩ : syracuseStep 560533 = 26275) (by norm_num)
theorem B658853 : Blo 291829 658853 := bbase (se 4 (by rfl) ⟨61767, by rfl⟩ : syracuseStep 658853 = 123535) (by norm_num)
theorem B331177 : Blo 291829 331177 := bbase (se 2 (by rfl) ⟨124191, by rfl⟩ : syracuseStep 331177 = 248383) (by norm_num)
theorem B396733 : Blo 291829 396733 := bbase (se 3 (by rfl) ⟨74387, by rfl⟩ : syracuseStep 396733 = 148775) (by norm_num)
theorem B1248709 : Blo 291829 1248709 := bbase (se 4 (by rfl) ⟨117066, by rfl⟩ : syracuseStep 1248709 = 234133) (by norm_num)
theorem B331213 : Blo 291829 331213 := bbase (se 3 (by rfl) ⟨62102, by rfl⟩ : syracuseStep 331213 = 124205) (by norm_num)
theorem B658925 : Blo 291829 658925 := bbase (se 3 (by rfl) ⟨123548, by rfl⟩ : syracuseStep 658925 = 247097) (by norm_num)
theorem B495085 : Blo 291829 495085 := bbase (se 3 (by rfl) ⟨92828, by rfl⟩ : syracuseStep 495085 = 185657) (by norm_num)
theorem B331249 : Blo 291829 331249 := bbase (se 2 (by rfl) ⟨124218, by rfl⟩ : syracuseStep 331249 = 248437) (by norm_num)
theorem B2395637 : Blo 291829 2395637 := bbase (se 5 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 2395637 = 224591) (by norm_num)
theorem B331285 : Blo 291829 331285 := bbase (se 6 (by rfl) ⟨7764, by rfl⟩ : syracuseStep 331285 = 15529) (by norm_num)
theorem B560677 : Blo 291829 560677 := bbase (se 4 (by rfl) ⟨52563, by rfl⟩ : syracuseStep 560677 = 105127) (by norm_num)
theorem B658997 : Blo 291829 658997 := bbase (se 5 (by rfl) ⟨30890, by rfl⟩ : syracuseStep 658997 = 61781) (by norm_num)
theorem B331321 : Blo 291829 331321 := bbase (se 2 (by rfl) ⟨124245, by rfl⟩ : syracuseStep 331321 = 248491) (by norm_num)
theorem B495173 : Blo 291829 495173 := bbase (se 4 (by rfl) ⟨46422, by rfl⟩ : syracuseStep 495173 = 92845) (by norm_num)
theorem B331357 : Blo 291829 331357 := bbase (se 3 (by rfl) ⟨62129, by rfl⟩ : syracuseStep 331357 = 124259) (by norm_num)
theorem B986741 : Blo 291829 986741 := bbase (se 5 (by rfl) ⟨46253, by rfl⟩ : syracuseStep 986741 = 92507) (by norm_num)
theorem B659069 : Blo 291829 659069 := bbase (se 3 (by rfl) ⟨123575, by rfl⟩ : syracuseStep 659069 = 247151) (by norm_num)
theorem B331393 : Blo 291829 331393 := bbase (se 2 (by rfl) ⟨124272, by rfl⟩ : syracuseStep 331393 = 248545) (by norm_num)
theorem B1085093 : Blo 291829 1085093 := bbase (se 4 (by rfl) ⟨101727, by rfl⟩ : syracuseStep 1085093 = 203455) (by norm_num)
theorem B331429 : Blo 291829 331429 := bbase (se 4 (by rfl) ⟨31071, by rfl⟩ : syracuseStep 331429 = 62143) (by norm_num)
theorem B659141 : Blo 291829 659141 := bbase (se 4 (by rfl) ⟨61794, by rfl⟩ : syracuseStep 659141 = 123589) (by norm_num)
theorem B495301 : Blo 291829 495301 := bbase (se 4 (by rfl) ⟨46434, by rfl⟩ : syracuseStep 495301 = 92869) (by norm_num)
theorem B560837 : Blo 291829 560837 := bbase (se 4 (by rfl) ⟨52578, by rfl⟩ : syracuseStep 560837 = 105157) (by norm_num)
theorem B331465 : Blo 291829 331465 := bbase (se 2 (by rfl) ⟨124299, by rfl⟩ : syracuseStep 331465 = 248599) (by norm_num)
theorem B331501 : Blo 291829 331501 := bbase (se 3 (by rfl) ⟨62156, by rfl⟩ : syracuseStep 331501 = 124313) (by norm_num)
theorem B659213 : Blo 291829 659213 := bbase (se 3 (by rfl) ⟨123602, by rfl⟩ : syracuseStep 659213 = 247205) (by norm_num)
theorem B331537 : Blo 291829 331537 := bbase (se 2 (by rfl) ⟨124326, by rfl⟩ : syracuseStep 331537 = 248653) (by norm_num)
theorem B495389 : Blo 291829 495389 := bbase (se 3 (by rfl) ⟨92885, by rfl⟩ : syracuseStep 495389 = 185771) (by norm_num)
theorem B331573 : Blo 291829 331573 := bbase (se 5 (by rfl) ⟨15542, by rfl⟩ : syracuseStep 331573 = 31085) (by norm_num)
theorem B659285 : Blo 291829 659285 := bbase (se 9 (by rfl) ⟨1931, by rfl⟩ : syracuseStep 659285 = 3863) (by norm_num)
theorem B560981 : Blo 291829 560981 := bbase (se 9 (by rfl) ⟨1643, by rfl⟩ : syracuseStep 560981 = 3287) (by norm_num)
theorem B331609 : Blo 291829 331609 := bbase (se 2 (by rfl) ⟨124353, by rfl⟩ : syracuseStep 331609 = 248707) (by norm_num)
theorem B626525 : Blo 291829 626525 := bbase (se 3 (by rfl) ⟨117473, by rfl⟩ : syracuseStep 626525 = 234947) (by norm_num)
theorem B790373 : Blo 291829 790373 := bbase (se 4 (by rfl) ⟨74097, by rfl⟩ : syracuseStep 790373 = 148195) (by norm_num)
theorem B331645 : Blo 291829 331645 := bbase (se 3 (by rfl) ⟨62183, by rfl⟩ : syracuseStep 331645 = 124367) (by norm_num)
theorem B659357 : Blo 291829 659357 := bbase (se 3 (by rfl) ⟨123629, by rfl⟩ : syracuseStep 659357 = 247259) (by norm_num)
theorem B495517 : Blo 291829 495517 := bbase (se 3 (by rfl) ⟨92909, by rfl⟩ : syracuseStep 495517 = 185819) (by norm_num)
theorem B331681 : Blo 291829 331681 := bbase (se 2 (by rfl) ⟨124380, by rfl⟩ : syracuseStep 331681 = 248761) (by norm_num)
theorem B331717 : Blo 291829 331717 := bbase (se 4 (by rfl) ⟨31098, by rfl⟩ : syracuseStep 331717 = 62197) (by norm_num)
theorem B659429 : Blo 291829 659429 := bbase (se 4 (by rfl) ⟨61821, by rfl⟩ : syracuseStep 659429 = 123643) (by norm_num)
theorem B331753 : Blo 291829 331753 := bbase (se 2 (by rfl) ⟨124407, by rfl⟩ : syracuseStep 331753 = 248815) (by norm_num)
theorem B298985 : Blo 291829 298985 := bbase (se 2 (by rfl) ⟨112119, by rfl⟩ : syracuseStep 298985 = 224239) (by norm_num)
theorem B495605 : Blo 291829 495605 := bbase (se 5 (by rfl) ⟨23231, by rfl⟩ : syracuseStep 495605 = 46463) (by norm_num)
theorem B331789 : Blo 291829 331789 := bbase (se 3 (by rfl) ⟨62210, by rfl⟩ : syracuseStep 331789 = 124421) (by norm_num)
theorem B987173 : Blo 291829 987173 := bbase (se 4 (by rfl) ⟨92547, by rfl⟩ : syracuseStep 987173 = 185095) (by norm_num)
theorem B659501 : Blo 291829 659501 := bbase (se 3 (by rfl) ⟨123656, by rfl⟩ : syracuseStep 659501 = 247313) (by norm_num)
theorem B331825 : Blo 291829 331825 := bbase (se 2 (by rfl) ⟨124434, by rfl⟩ : syracuseStep 331825 = 248869) (by norm_num)
theorem B626773 : Blo 291829 626773 := bbase (se 8 (by rfl) ⟨3672, by rfl⟩ : syracuseStep 626773 = 7345) (by norm_num)
theorem B331861 : Blo 291829 331861 := bbase (se 8 (by rfl) ⟨1944, by rfl⟩ : syracuseStep 331861 = 3889) (by norm_num)
theorem B659573 : Blo 291829 659573 := bbase (se 5 (by rfl) ⟨30917, by rfl⟩ : syracuseStep 659573 = 61835) (by norm_num)
theorem B495733 : Blo 291829 495733 := bbase (se 5 (by rfl) ⟨23237, by rfl⟩ : syracuseStep 495733 = 46475) (by norm_num)
theorem B561269 : Blo 291829 561269 := bbase (se 5 (by rfl) ⟨26309, by rfl⟩ : syracuseStep 561269 = 52619) (by norm_num)
theorem B331897 : Blo 291829 331897 := bbase (se 2 (by rfl) ⟨124461, by rfl⟩ : syracuseStep 331897 = 248923) (by norm_num)
theorem B331933 : Blo 291829 331933 := bbase (se 3 (by rfl) ⟨62237, by rfl⟩ : syracuseStep 331933 = 124475) (by norm_num)
theorem B1249445 : Blo 291829 1249445 := bbase (se 4 (by rfl) ⟨117135, by rfl⟩ : syracuseStep 1249445 = 234271) (by norm_num)
theorem B659645 : Blo 291829 659645 := bbase (se 3 (by rfl) ⟨123683, by rfl⟩ : syracuseStep 659645 = 247367) (by norm_num)
theorem B331969 : Blo 291829 331969 := bbase (se 2 (by rfl) ⟨124488, by rfl⟩ : syracuseStep 331969 = 248977) (by norm_num)
theorem B495821 : Blo 291829 495821 := bbase (se 3 (by rfl) ⟨92966, by rfl⟩ : syracuseStep 495821 = 185933) (by norm_num)
theorem B332005 : Blo 291829 332005 := bbase (se 4 (by rfl) ⟨31125, by rfl⟩ : syracuseStep 332005 = 62251) (by norm_num)
theorem B659717 : Blo 291829 659717 := bbase (se 4 (by rfl) ⟨61848, by rfl⟩ : syracuseStep 659717 = 123697) (by norm_num)
theorem B299269 : Blo 291829 299269 := bbase (se 4 (by rfl) ⟨28056, by rfl⟩ : syracuseStep 299269 = 56113) (by norm_num)
theorem B332041 : Blo 291829 332041 := bbase (se 2 (by rfl) ⟨124515, by rfl⟩ : syracuseStep 332041 = 249031) (by norm_num)
theorem B561421 : Blo 291829 561421 := bbase (se 3 (by rfl) ⟨105266, by rfl⟩ : syracuseStep 561421 = 210533) (by norm_num)
theorem B2265365 : Blo 291829 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B332077 : Blo 291829 332077 := bbase (se 3 (by rfl) ⟨62264, by rfl⟩ : syracuseStep 332077 = 124529) (by norm_num)
theorem B659789 : Blo 291829 659789 := bbase (se 3 (by rfl) ⟨123710, by rfl⟩ : syracuseStep 659789 = 247421) (by norm_num)
theorem B495949 : Blo 291829 495949 := bbase (se 3 (by rfl) ⟨92990, by rfl⟩ : syracuseStep 495949 = 185981) (by norm_num)
theorem B332113 : Blo 291829 332113 := bbase (se 2 (by rfl) ⟨124542, by rfl⟩ : syracuseStep 332113 = 249085) (by norm_num)
theorem B4297045 : Blo 291829 4297045 := bbase (se 10 (by rfl) ⟨6294, by rfl⟩ : syracuseStep 4297045 = 12589) (by norm_num)
theorem B332149 : Blo 291829 332149 := bbase (se 5 (by rfl) ⟨15569, by rfl⟩ : syracuseStep 332149 = 31139) (by norm_num)
theorem B659861 : Blo 291829 659861 := bbase (se 6 (by rfl) ⟨15465, by rfl⟩ : syracuseStep 659861 = 30931) (by norm_num)
theorem B332185 : Blo 291829 332185 := bbase (se 2 (by rfl) ⟨124569, by rfl⟩ : syracuseStep 332185 = 249139) (by norm_num)
theorem B496037 : Blo 291829 496037 := bbase (se 4 (by rfl) ⟨46503, by rfl⟩ : syracuseStep 496037 = 93007) (by norm_num)
theorem B1053109 : Blo 291829 1053109 := bbase (se 5 (by rfl) ⟨49364, by rfl⟩ : syracuseStep 1053109 = 98729) (by norm_num)
theorem B332221 : Blo 291829 332221 := bbase (se 3 (by rfl) ⟨62291, by rfl⟩ : syracuseStep 332221 = 124583) (by norm_num)
theorem B987605 : Blo 291829 987605 := bbase (se 7 (by rfl) ⟨11573, by rfl⟩ : syracuseStep 987605 = 23147) (by norm_num)
theorem B659933 : Blo 291829 659933 := bbase (se 3 (by rfl) ⟨123737, by rfl⟩ : syracuseStep 659933 = 247475) (by norm_num)
theorem B332257 : Blo 291829 332257 := bbase (se 2 (by rfl) ⟨124596, by rfl⟩ : syracuseStep 332257 = 249193) (by norm_num)
theorem B332293 : Blo 291829 332293 := bbase (se 4 (by rfl) ⟨31152, by rfl⟩ : syracuseStep 332293 = 62305) (by norm_num)
theorem B299549 : Blo 291829 299549 := bbase (se 3 (by rfl) ⟨56165, by rfl⟩ : syracuseStep 299549 = 112331) (by norm_num)
theorem B660005 : Blo 291829 660005 := bbase (se 4 (by rfl) ⟨61875, by rfl⟩ : syracuseStep 660005 = 123751) (by norm_num)
theorem B496165 : Blo 291829 496165 := bbase (se 4 (by rfl) ⟨46515, by rfl⟩ : syracuseStep 496165 = 93031) (by norm_num)
theorem B332329 : Blo 291829 332329 := bbase (se 2 (by rfl) ⟨124623, by rfl⟩ : syracuseStep 332329 = 249247) (by norm_num)
theorem B1479221 : Blo 291829 1479221 := bbase (se 5 (by rfl) ⟨69338, by rfl⟩ : syracuseStep 1479221 = 138677) (by norm_num)
theorem B627277 : Blo 291829 627277 := bbase (se 3 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 627277 = 235229) (by norm_num)
theorem B332365 : Blo 291829 332365 := bbase (se 3 (by rfl) ⟨62318, by rfl⟩ : syracuseStep 332365 = 124637) (by norm_num)
theorem B1512037 : Blo 291829 1512037 := bbase (se 4 (by rfl) ⟨141753, by rfl⟩ : syracuseStep 1512037 = 283507) (by norm_num)
theorem B660077 : Blo 291829 660077 := bbase (se 3 (by rfl) ⟨123764, by rfl⟩ : syracuseStep 660077 = 247529) (by norm_num)
theorem B332401 : Blo 291829 332401 := bbase (se 2 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 332401 = 249301) (by norm_num)
theorem B594557 : Blo 291829 594557 := bbase (se 3 (by rfl) ⟨111479, by rfl⟩ : syracuseStep 594557 = 222959) (by norm_num)
theorem B496253 : Blo 291829 496253 := bbase (se 3 (by rfl) ⟨93047, by rfl⟩ : syracuseStep 496253 = 186095) (by norm_num)
theorem B332437 : Blo 291829 332437 := bbase (se 6 (by rfl) ⟨7791, by rfl⟩ : syracuseStep 332437 = 15583) (by norm_num)
theorem B660149 : Blo 291829 660149 := bbase (se 5 (by rfl) ⟨30944, by rfl⟩ : syracuseStep 660149 = 61889) (by norm_num)
theorem B332473 : Blo 291829 332473 := bbase (se 2 (by rfl) ⟨124677, by rfl⟩ : syracuseStep 332473 = 249355) (by norm_num)
theorem B332509 : Blo 291829 332509 := bbase (se 3 (by rfl) ⟨62345, by rfl⟩ : syracuseStep 332509 = 124691) (by norm_num)
theorem B660221 : Blo 291829 660221 := bbase (se 3 (by rfl) ⟨123791, by rfl⟩ : syracuseStep 660221 = 247583) (by norm_num)
theorem B496381 : Blo 291829 496381 := bbase (se 3 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 496381 = 186143) (by norm_num)
theorem B332545 : Blo 291829 332545 := bbase (se 2 (by rfl) ⟨124704, by rfl⟩ : syracuseStep 332545 = 249409) (by norm_num)
theorem B398101 : Blo 291829 398101 := bbase (se 6 (by rfl) ⟨9330, by rfl⟩ : syracuseStep 398101 = 18661) (by norm_num)
theorem B299809 : Blo 291829 299809 := bbase (se 2 (by rfl) ⟨112428, by rfl⟩ : syracuseStep 299809 = 224857) (by norm_num)
theorem B332581 : Blo 291829 332581 := bbase (se 4 (by rfl) ⟨31179, by rfl⟩ : syracuseStep 332581 = 62359) (by norm_num)
theorem B660293 : Blo 291829 660293 := bbase (se 4 (by rfl) ⟨61902, by rfl⟩ : syracuseStep 660293 = 123805) (by norm_num)
theorem B332617 : Blo 291829 332617 := bbase (se 2 (by rfl) ⟨124731, by rfl⟩ : syracuseStep 332617 = 249463) (by norm_num)
theorem B496469 : Blo 291829 496469 := bbase (se 9 (by rfl) ⟨1454, by rfl⟩ : syracuseStep 496469 = 2909) (by norm_num)
theorem B332653 : Blo 291829 332653 := bbase (se 3 (by rfl) ⟨62372, by rfl⟩ : syracuseStep 332653 = 124745) (by norm_num)
theorem B988037 : Blo 291829 988037 := bbase (se 4 (by rfl) ⟨92628, by rfl⟩ : syracuseStep 988037 = 185257) (by norm_num)
theorem B660365 : Blo 291829 660365 := bbase (se 3 (by rfl) ⟨123818, by rfl⟩ : syracuseStep 660365 = 247637) (by norm_num)
theorem B332689 : Blo 291829 332689 := bbase (se 2 (by rfl) ⟨124758, by rfl⟩ : syracuseStep 332689 = 249517) (by norm_num)
theorem B332725 : Blo 291829 332725 := bbase (se 5 (by rfl) ⟨15596, by rfl⟩ : syracuseStep 332725 = 31193) (by norm_num)
theorem B660437 : Blo 291829 660437 := bbase (se 7 (by rfl) ⟨7739, by rfl⟩ : syracuseStep 660437 = 15479) (by norm_num)
theorem B496597 : Blo 291829 496597 := bbase (se 7 (by rfl) ⟨5819, by rfl⟩ : syracuseStep 496597 = 11639) (by norm_num)
theorem B332761 : Blo 291829 332761 := bbase (se 2 (by rfl) ⟨124785, by rfl⟩ : syracuseStep 332761 = 249571) (by norm_num)
theorem B332797 : Blo 291829 332797 := bbase (se 3 (by rfl) ⟨62399, by rfl⟩ : syracuseStep 332797 = 124799) (by norm_num)
theorem B3052565 : Blo 291829 3052565 := bbase (se 6 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 3052565 = 143089) (by norm_num)
theorem B660509 : Blo 291829 660509 := bbase (se 3 (by rfl) ⟨123845, by rfl⟩ : syracuseStep 660509 = 247691) (by norm_num)
theorem B496685 : Blo 291829 496685 := bbase (se 3 (by rfl) ⟨93128, by rfl⟩ : syracuseStep 496685 = 186257) (by norm_num)
theorem B660581 : Blo 291829 660581 := bbase (se 4 (by rfl) ⟨61929, by rfl⟩ : syracuseStep 660581 = 123859) (by norm_num)
theorem B1119365 : Blo 291829 1119365 := bbase (se 4 (by rfl) ⟨104940, by rfl⟩ : syracuseStep 1119365 = 209881) (by norm_num)
theorem B660653 : Blo 291829 660653 := bbase (se 3 (by rfl) ⟨123872, by rfl⟩ : syracuseStep 660653 = 247745) (by norm_num)
theorem B496813 : Blo 291829 496813 := bbase (se 3 (by rfl) ⟨93152, by rfl⟩ : syracuseStep 496813 = 186305) (by norm_num)
theorem B595181 : Blo 291829 595181 := bbase (se 3 (by rfl) ⟨111596, by rfl⟩ : syracuseStep 595181 = 223193) (by norm_num)
theorem B660725 : Blo 291829 660725 := bbase (se 5 (by rfl) ⟨30971, by rfl⟩ : syracuseStep 660725 = 61943) (by norm_num)
theorem B496901 : Blo 291829 496901 := bbase (se 4 (by rfl) ⟨46584, by rfl⟩ : syracuseStep 496901 = 93169) (by norm_num)
theorem B333065 : Blo 291829 333065 := bbase (se 2 (by rfl) ⟨124899, by rfl⟩ : syracuseStep 333065 = 249799) (by norm_num)
theorem B988469 : Blo 291829 988469 := bbase (se 5 (by rfl) ⟨46334, by rfl⟩ : syracuseStep 988469 = 92669) (by norm_num)
theorem B660797 : Blo 291829 660797 := bbase (se 3 (by rfl) ⟨123899, by rfl⟩ : syracuseStep 660797 = 247799) (by norm_num)
theorem B595277 : Blo 291829 595277 := bbase (se 3 (by rfl) ⟨111614, by rfl⟩ : syracuseStep 595277 = 223229) (by norm_num)
theorem B791909 : Blo 291829 791909 := bbase (se 4 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 791909 = 148483) (by norm_num)
theorem B660869 : Blo 291829 660869 := bbase (se 4 (by rfl) ⟨61956, by rfl⟩ : syracuseStep 660869 = 123913) (by norm_num)
theorem B497029 : Blo 291829 497029 := bbase (se 4 (by rfl) ⟨46596, by rfl⟩ : syracuseStep 497029 = 93193) (by norm_num)
theorem B1054117 : Blo 291829 1054117 := bbase (se 4 (by rfl) ⟨98823, by rfl⟩ : syracuseStep 1054117 = 197647) (by norm_num)
theorem B1119653 : Blo 291829 1119653 := bbase (se 4 (by rfl) ⟨104967, by rfl⟩ : syracuseStep 1119653 = 209935) (by norm_num)
theorem B628165 : Blo 291829 628165 := bbase (se 4 (by rfl) ⟨58890, by rfl⟩ : syracuseStep 628165 = 117781) (by norm_num)
theorem B660941 : Blo 291829 660941 := bbase (se 3 (by rfl) ⟨123926, by rfl⟩ : syracuseStep 660941 = 247853) (by norm_num)
theorem B2004437 : Blo 291829 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B497117 : Blo 291829 497117 := bbase (se 3 (by rfl) ⟨93209, by rfl⟩ : syracuseStep 497117 = 186419) (by norm_num)
theorem B661013 : Blo 291829 661013 := bbase (se 6 (by rfl) ⟨15492, by rfl⟩ : syracuseStep 661013 = 30985) (by norm_num)
theorem B661085 : Blo 291829 661085 := bbase (se 3 (by rfl) ⟨123953, by rfl⟩ : syracuseStep 661085 = 247907) (by norm_num)
theorem B497245 : Blo 291829 497245 := bbase (se 3 (by rfl) ⟨93233, by rfl⟩ : syracuseStep 497245 = 186467) (by norm_num)
theorem B661157 : Blo 291829 661157 := bbase (se 4 (by rfl) ⟨61983, by rfl⟩ : syracuseStep 661157 = 123967) (by norm_num)
theorem B497333 : Blo 291829 497333 := bbase (se 5 (by rfl) ⟨23312, by rfl⟩ : syracuseStep 497333 = 46625) (by norm_num)
theorem B1414853 : Blo 291829 1414853 := bbase (se 4 (by rfl) ⟨132642, by rfl⟩ : syracuseStep 1414853 = 265285) (by norm_num)
theorem B988901 : Blo 291829 988901 := bbase (se 4 (by rfl) ⟨92709, by rfl⟩ : syracuseStep 988901 = 185419) (by norm_num)
theorem B661229 : Blo 291829 661229 := bbase (se 3 (by rfl) ⟨123980, by rfl⟩ : syracuseStep 661229 = 247961) (by norm_num)
theorem B530173 : Blo 291829 530173 := bbase (se 3 (by rfl) ⟨99407, by rfl⟩ : syracuseStep 530173 = 198815) (by norm_num)
theorem B661301 : Blo 291829 661301 := bbase (se 5 (by rfl) ⟨30998, by rfl⟩ : syracuseStep 661301 = 61997) (by norm_num)
theorem B497461 : Blo 291829 497461 := bbase (se 5 (by rfl) ⟨23318, by rfl⟩ : syracuseStep 497461 = 46637) (by norm_num)
theorem B1480517 : Blo 291829 1480517 := bbase (se 4 (by rfl) ⟨138798, by rfl⟩ : syracuseStep 1480517 = 277597) (by norm_num)
theorem B530245 : Blo 291829 530245 := bbase (se 4 (by rfl) ⟨49710, by rfl⟩ : syracuseStep 530245 = 99421) (by norm_num)
theorem B661373 : Blo 291829 661373 := bbase (se 3 (by rfl) ⟨124007, by rfl⟩ : syracuseStep 661373 = 248015) (by norm_num)
theorem B497549 : Blo 291829 497549 := bbase (se 3 (by rfl) ⟨93290, by rfl⟩ : syracuseStep 497549 = 186581) (by norm_num)
theorem B628661 : Blo 291829 628661 := bbase (se 5 (by rfl) ⟨29468, by rfl⟩ : syracuseStep 628661 = 58937) (by norm_num)
theorem B661445 : Blo 291829 661445 := bbase (se 4 (by rfl) ⟨62010, by rfl⟩ : syracuseStep 661445 = 124021) (by norm_num)
theorem B956357 : Blo 291829 956357 := bbase (se 4 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 956357 = 179317) (by norm_num)
theorem B661517 : Blo 291829 661517 := bbase (se 3 (by rfl) ⟨124034, by rfl⟩ : syracuseStep 661517 = 248069) (by norm_num)
theorem B497677 : Blo 291829 497677 := bbase (se 3 (by rfl) ⟨93314, by rfl⟩ : syracuseStep 497677 = 186629) (by norm_num)
theorem B661589 : Blo 291829 661589 := bbase (se 8 (by rfl) ⟨3876, by rfl⟩ : syracuseStep 661589 = 7753) (by norm_num)
theorem B497765 : Blo 291829 497765 := bbase (se 4 (by rfl) ⟨46665, by rfl⟩ : syracuseStep 497765 = 93331) (by norm_num)
theorem B989333 : Blo 291829 989333 := bbase (se 6 (by rfl) ⟨23187, by rfl⟩ : syracuseStep 989333 = 46375) (by norm_num)
theorem B661661 : Blo 291829 661661 := bbase (se 3 (by rfl) ⟨124061, by rfl⟩ : syracuseStep 661661 = 248123) (by norm_num)
theorem B1022149 : Blo 291829 1022149 := bbase (se 4 (by rfl) ⟨95826, by rfl⟩ : syracuseStep 1022149 = 191653) (by norm_num)
theorem B661733 : Blo 291829 661733 := bbase (se 4 (by rfl) ⟨62037, by rfl⟩ : syracuseStep 661733 = 124075) (by norm_num)
theorem B497893 : Blo 291829 497893 := bbase (se 4 (by rfl) ⟨46677, by rfl⟩ : syracuseStep 497893 = 93355) (by norm_num)
theorem B661805 : Blo 291829 661805 := bbase (se 3 (by rfl) ⟨124088, by rfl⟩ : syracuseStep 661805 = 248177) (by norm_num)
theorem B497981 : Blo 291829 497981 := bbase (se 3 (by rfl) ⟨93371, by rfl⟩ : syracuseStep 497981 = 186743) (by norm_num)
theorem B661877 : Blo 291829 661877 := bbase (se 5 (by rfl) ⟨31025, by rfl⟩ : syracuseStep 661877 = 62051) (by norm_num)
theorem B596413 : Blo 291829 596413 := bbase (se 3 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 596413 = 223655) (by norm_num)
theorem B661949 : Blo 291829 661949 := bbase (se 3 (by rfl) ⟨124115, by rfl⟩ : syracuseStep 661949 = 248231) (by norm_num)
theorem B498109 : Blo 291829 498109 := bbase (se 3 (by rfl) ⟨93395, by rfl⟩ : syracuseStep 498109 = 186791) (by norm_num)
theorem B662021 : Blo 291829 662021 := bbase (se 4 (by rfl) ⟨62064, by rfl⟩ : syracuseStep 662021 = 124129) (by norm_num)
theorem B498197 : Blo 291829 498197 := bbase (se 6 (by rfl) ⟨11676, by rfl⟩ : syracuseStep 498197 = 23353) (by norm_num)
theorem B989765 : Blo 291829 989765 := bbase (se 4 (by rfl) ⟨92790, by rfl⟩ : syracuseStep 989765 = 185581) (by norm_num)
theorem B1120837 : Blo 291829 1120837 := bbase (se 4 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 1120837 = 210157) (by norm_num)
theorem B662093 : Blo 291829 662093 := bbase (se 3 (by rfl) ⟨124142, by rfl⟩ : syracuseStep 662093 = 248285) (by norm_num)
theorem B662165 : Blo 291829 662165 := bbase (se 6 (by rfl) ⟨15519, by rfl⟩ : syracuseStep 662165 = 31039) (by norm_num)
theorem B498325 : Blo 291829 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B3185365 : Blo 291829 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B662237 : Blo 291829 662237 := bbase (se 3 (by rfl) ⟨124169, by rfl⟩ : syracuseStep 662237 = 248339) (by norm_num)
theorem B498413 : Blo 291829 498413 := bbase (se 3 (by rfl) ⟨93452, by rfl⟩ : syracuseStep 498413 = 186905) (by norm_num)
theorem B662309 : Blo 291829 662309 := bbase (se 4 (by rfl) ⟨62091, by rfl⟩ : syracuseStep 662309 = 124183) (by norm_num)
theorem B629549 : Blo 291829 629549 := bbase (se 3 (by rfl) ⟨118040, by rfl⟩ : syracuseStep 629549 = 236081) (by norm_num)
theorem B531269 : Blo 291829 531269 := bbase (se 4 (by rfl) ⟨49806, by rfl⟩ : syracuseStep 531269 = 99613) (by norm_num)
theorem B891749 : Blo 291829 891749 := bbase (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) (by norm_num)
theorem B662381 : Blo 291829 662381 := bbase (se 3 (by rfl) ⟨124196, by rfl⟩ : syracuseStep 662381 = 248393) (by norm_num)
theorem B498541 : Blo 291829 498541 := bbase (se 3 (by rfl) ⟨93476, by rfl⟩ : syracuseStep 498541 = 186953) (by norm_num)
theorem B1121141 : Blo 291829 1121141 := bbase (se 5 (by rfl) ⟨52553, by rfl⟩ : syracuseStep 1121141 = 105107) (by norm_num)
theorem B629669 : Blo 291829 629669 := bbase (se 4 (by rfl) ⟨59031, by rfl⟩ : syracuseStep 629669 = 118063) (by norm_num)
theorem B662453 : Blo 291829 662453 := bbase (se 5 (by rfl) ⟨31052, by rfl⟩ : syracuseStep 662453 = 62105) (by norm_num)
theorem B498629 : Blo 291829 498629 := bbase (se 4 (by rfl) ⟨46746, by rfl⟩ : syracuseStep 498629 = 93493) (by norm_num)
theorem B990197 : Blo 291829 990197 := bbase (se 5 (by rfl) ⟨46415, by rfl⟩ : syracuseStep 990197 = 92831) (by norm_num)
theorem B662525 : Blo 291829 662525 := bbase (se 3 (by rfl) ⟨124223, by rfl⟩ : syracuseStep 662525 = 248447) (by norm_num)
theorem B2104373 : Blo 291829 2104373 := bbase (se 5 (by rfl) ⟨98642, by rfl⟩ : syracuseStep 2104373 = 197285) (by norm_num)
theorem B662597 : Blo 291829 662597 := bbase (se 4 (by rfl) ⟨62118, by rfl⟩ : syracuseStep 662597 = 124237) (by norm_num)
theorem B498757 : Blo 291829 498757 := bbase (se 4 (by rfl) ⟨46758, by rfl⟩ : syracuseStep 498757 = 93517) (by norm_num)
theorem B1481813 : Blo 291829 1481813 := bbase (se 8 (by rfl) ⟨8682, by rfl⟩ : syracuseStep 1481813 = 17365) (by norm_num)
theorem B662669 : Blo 291829 662669 := bbase (se 3 (by rfl) ⟨124250, by rfl⟩ : syracuseStep 662669 = 248501) (by norm_num)
theorem B498845 : Blo 291829 498845 := bbase (se 3 (by rfl) ⟨93533, by rfl⟩ : syracuseStep 498845 = 187067) (by norm_num)
theorem B662741 : Blo 291829 662741 := bbase (se 7 (by rfl) ⟨7766, by rfl⟩ : syracuseStep 662741 = 15533) (by norm_num)
theorem B662813 : Blo 291829 662813 := bbase (se 3 (by rfl) ⟨124277, by rfl⟩ : syracuseStep 662813 = 248555) (by norm_num)
theorem B498973 : Blo 291829 498973 := bbase (se 3 (by rfl) ⟨93557, by rfl⟩ : syracuseStep 498973 = 187115) (by norm_num)
theorem B662885 : Blo 291829 662885 := bbase (se 4 (by rfl) ⟨62145, by rfl⟩ : syracuseStep 662885 = 124291) (by norm_num)
theorem B499061 : Blo 291829 499061 := bbase (se 5 (by rfl) ⟨23393, by rfl⟩ : syracuseStep 499061 = 46787) (by norm_num)
theorem B1252741 : Blo 291829 1252741 := bbase (se 4 (by rfl) ⟨117444, by rfl⟩ : syracuseStep 1252741 = 234889) (by norm_num)
theorem B990629 : Blo 291829 990629 := bbase (se 4 (by rfl) ⟨92871, by rfl⟩ : syracuseStep 990629 = 185743) (by norm_num)
theorem B662957 : Blo 291829 662957 := bbase (se 3 (by rfl) ⟨124304, by rfl⟩ : syracuseStep 662957 = 248609) (by norm_num)
theorem B663029 : Blo 291829 663029 := bbase (se 5 (by rfl) ⟨31079, by rfl⟩ : syracuseStep 663029 = 62159) (by norm_num)
theorem B499189 : Blo 291829 499189 := bbase (se 5 (by rfl) ⟨23399, by rfl⟩ : syracuseStep 499189 = 46799) (by norm_num)
theorem B630301 : Blo 291829 630301 := bbase (se 3 (by rfl) ⟨118181, by rfl⟩ : syracuseStep 630301 = 236363) (by norm_num)
theorem B663101 : Blo 291829 663101 := bbase (se 3 (by rfl) ⟨124331, by rfl⟩ : syracuseStep 663101 = 248663) (by norm_num)
theorem B597613 : Blo 291829 597613 := bbase (se 3 (by rfl) ⟨112052, by rfl⟩ : syracuseStep 597613 = 224105) (by norm_num)
theorem B663173 : Blo 291829 663173 := bbase (se 4 (by rfl) ⟨62172, by rfl⟩ : syracuseStep 663173 = 124345) (by norm_num)
theorem B1416869 : Blo 291829 1416869 := bbase (se 4 (by rfl) ⟨132831, by rfl⟩ : syracuseStep 1416869 = 265663) (by norm_num)
theorem B2236085 : Blo 291829 2236085 := bbase (se 5 (by rfl) ⟨104816, by rfl⟩ : syracuseStep 2236085 = 209633) (by norm_num)
theorem B892613 : Blo 291829 892613 := bbase (se 4 (by rfl) ⟨83682, by rfl⟩ : syracuseStep 892613 = 167365) (by norm_num)
theorem B663245 : Blo 291829 663245 := bbase (se 3 (by rfl) ⟨124358, by rfl⟩ : syracuseStep 663245 = 248717) (by norm_num)
theorem B663317 : Blo 291829 663317 := bbase (se 6 (by rfl) ⟨15546, by rfl⟩ : syracuseStep 663317 = 31093) (by norm_num)
theorem B991061 : Blo 291829 991061 := bbase (se 9 (by rfl) ⟨2903, by rfl⟩ : syracuseStep 991061 = 5807) (by norm_num)
theorem B663389 : Blo 291829 663389 := bbase (se 3 (by rfl) ⟨124385, by rfl⟩ : syracuseStep 663389 = 248771) (by norm_num)
theorem B663461 : Blo 291829 663461 := bbase (se 4 (by rfl) ⟨62199, by rfl⟩ : syracuseStep 663461 = 124399) (by norm_num)
theorem B663533 : Blo 291829 663533 := bbase (se 3 (by rfl) ⟨124412, by rfl⟩ : syracuseStep 663533 = 248825) (by norm_num)
theorem B663605 : Blo 291829 663605 := bbase (se 5 (by rfl) ⟨31106, by rfl⟩ : syracuseStep 663605 = 62213) (by norm_num)
theorem B335993 : Blo 291829 335993 := bbase (se 2 (by rfl) ⟨125997, by rfl⟩ : syracuseStep 335993 = 251995) (by norm_num)
theorem B663677 : Blo 291829 663677 := bbase (se 3 (by rfl) ⟨124439, by rfl⟩ : syracuseStep 663677 = 248879) (by norm_num)
theorem B663749 : Blo 291829 663749 := bbase (se 4 (by rfl) ⟨62226, by rfl⟩ : syracuseStep 663749 = 124453) (by norm_num)
theorem B598213 : Blo 291829 598213 := bbase (se 4 (by rfl) ⟨56082, by rfl⟩ : syracuseStep 598213 = 112165) (by norm_num)
theorem B991493 : Blo 291829 991493 := bbase (se 4 (by rfl) ⟨92952, by rfl⟩ : syracuseStep 991493 = 185905) (by norm_num)
theorem B663821 : Blo 291829 663821 := bbase (se 3 (by rfl) ⟨124466, by rfl⟩ : syracuseStep 663821 = 248933) (by norm_num)
theorem B663893 : Blo 291829 663893 := bbase (se 10 (by rfl) ⟨972, by rfl⟩ : syracuseStep 663893 = 1945) (by norm_num)
theorem B1483109 : Blo 291829 1483109 := bbase (se 4 (by rfl) ⟨139041, by rfl⟩ : syracuseStep 1483109 = 278083) (by norm_num)
theorem B1417621 : Blo 291829 1417621 := bbase (se 6 (by rfl) ⟨33225, by rfl⟩ : syracuseStep 1417621 = 66451) (by norm_num)
theorem B631189 : Blo 291829 631189 := bbase (se 6 (by rfl) ⟨14793, by rfl⟩ : syracuseStep 631189 = 29587) (by norm_num)
theorem B663965 : Blo 291829 663965 := bbase (se 3 (by rfl) ⟨124493, by rfl⟩ : syracuseStep 663965 = 248987) (by norm_num)
theorem B664037 : Blo 291829 664037 := bbase (se 4 (by rfl) ⟨62253, by rfl⟩ : syracuseStep 664037 = 124507) (by norm_num)
theorem B631309 : Blo 291829 631309 := bbase (se 3 (by rfl) ⟨118370, by rfl⟩ : syracuseStep 631309 = 236741) (by norm_num)
theorem B664109 : Blo 291829 664109 := bbase (se 3 (by rfl) ⟨124520, by rfl⟩ : syracuseStep 664109 = 249041) (by norm_num)
theorem B467549 : Blo 291829 467549 := bbase (se 3 (by rfl) ⟨87665, by rfl⟩ : syracuseStep 467549 = 175331) (by norm_num)
theorem B664181 : Blo 291829 664181 := bbase (se 5 (by rfl) ⟨31133, by rfl⟩ : syracuseStep 664181 = 62267) (by norm_num)
theorem B991925 : Blo 291829 991925 := bbase (se 5 (by rfl) ⟨46496, by rfl⟩ : syracuseStep 991925 = 92993) (by norm_num)
theorem B664253 : Blo 291829 664253 := bbase (se 3 (by rfl) ⟨124547, by rfl⟩ : syracuseStep 664253 = 249095) (by norm_num)
theorem B664325 : Blo 291829 664325 := bbase (se 4 (by rfl) ⟨62280, by rfl⟩ : syracuseStep 664325 = 124561) (by norm_num)
theorem B631565 : Blo 291829 631565 := bbase (se 3 (by rfl) ⟨118418, by rfl⟩ : syracuseStep 631565 = 236837) (by norm_num)
theorem B467741 : Blo 291829 467741 := bbase (se 3 (by rfl) ⟨87701, by rfl⟩ : syracuseStep 467741 = 175403) (by norm_num)
theorem B369461 : Blo 291829 369461 := bbase (se 5 (by rfl) ⟨17318, by rfl⟩ : syracuseStep 369461 = 34637) (by norm_num)
theorem B664397 : Blo 291829 664397 := bbase (se 3 (by rfl) ⟨124574, by rfl⟩ : syracuseStep 664397 = 249149) (by norm_num)
theorem B369517 : Blo 291829 369517 := bbase (se 3 (by rfl) ⟨69284, by rfl⟩ : syracuseStep 369517 = 138569) (by norm_num)
theorem B664469 : Blo 291829 664469 := bbase (se 6 (by rfl) ⟨15573, by rfl⟩ : syracuseStep 664469 = 31147) (by norm_num)
theorem B369613 : Blo 291829 369613 := bbase (se 3 (by rfl) ⟨69302, by rfl⟩ : syracuseStep 369613 = 138605) (by norm_num)
theorem B664541 : Blo 291829 664541 := bbase (se 3 (by rfl) ⟨124601, by rfl⟩ : syracuseStep 664541 = 249203) (by norm_num)
theorem B2499605 : Blo 291829 2499605 := bbase (se 6 (by rfl) ⟨58584, by rfl⟩ : syracuseStep 2499605 = 117169) (by norm_num)
theorem B664613 : Blo 291829 664613 := bbase (se 4 (by rfl) ⟨62307, by rfl⟩ : syracuseStep 664613 = 124615) (by norm_num)
theorem B992357 : Blo 291829 992357 := bbase (se 4 (by rfl) ⟨93033, by rfl⟩ : syracuseStep 992357 = 186067) (by norm_num)
theorem B664685 : Blo 291829 664685 := bbase (se 3 (by rfl) ⟨124628, by rfl⟩ : syracuseStep 664685 = 249257) (by norm_num)
theorem B369785 : Blo 291829 369785 := bbase (se 2 (by rfl) ⟨138669, by rfl⟩ : syracuseStep 369785 = 277339) (by norm_num)
theorem B369841 : Blo 291829 369841 := bbase (se 2 (by rfl) ⟨138690, by rfl⟩ : syracuseStep 369841 = 277381) (by norm_num)
theorem B664757 : Blo 291829 664757 := bbase (se 5 (by rfl) ⟨31160, by rfl⟩ : syracuseStep 664757 = 62321) (by norm_num)
theorem B664829 : Blo 291829 664829 := bbase (se 3 (by rfl) ⟨124655, by rfl⟩ : syracuseStep 664829 = 249311) (by norm_num)
theorem B369937 : Blo 291829 369937 := bbase (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) (by norm_num)
theorem B664901 : Blo 291829 664901 := bbase (se 4 (by rfl) ⟨62334, by rfl⟩ : syracuseStep 664901 = 124669) (by norm_num)
theorem B599381 : Blo 291829 599381 := bbase (se 12 (by rfl) ⟨219, by rfl⟩ : syracuseStep 599381 = 439) (by norm_num)
theorem B599429 : Blo 291829 599429 := bbase (se 4 (by rfl) ⟨56196, by rfl⟩ : syracuseStep 599429 = 112393) (by norm_num)
theorem B664973 : Blo 291829 664973 := bbase (se 3 (by rfl) ⟨124682, by rfl⟩ : syracuseStep 664973 = 249365) (by norm_num)
theorem B370109 : Blo 291829 370109 := bbase (se 3 (by rfl) ⟨69395, by rfl⟩ : syracuseStep 370109 = 138791) (by norm_num)
theorem B665045 : Blo 291829 665045 := bbase (se 7 (by rfl) ⟨7793, by rfl⟩ : syracuseStep 665045 = 15587) (by norm_num)
theorem B4793813 : Blo 291829 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B370165 : Blo 291829 370165 := bbase (se 5 (by rfl) ⟨17351, by rfl⟩ : syracuseStep 370165 = 34703) (by norm_num)
theorem B1877525 : Blo 291829 1877525 := bbase (se 6 (by rfl) ⟨44004, by rfl⟩ : syracuseStep 1877525 = 88009) (by norm_num)
theorem B992789 : Blo 291829 992789 := bbase (se 6 (by rfl) ⟨23268, by rfl⟩ : syracuseStep 992789 = 46537) (by norm_num)
theorem B665117 : Blo 291829 665117 := bbase (se 3 (by rfl) ⟨124709, by rfl⟩ : syracuseStep 665117 = 249419) (by norm_num)
theorem B370261 : Blo 291829 370261 := bbase (se 8 (by rfl) ⟨2169, by rfl⟩ : syracuseStep 370261 = 4339) (by norm_num)
theorem B665189 : Blo 291829 665189 := bbase (se 4 (by rfl) ⟨62361, by rfl⟩ : syracuseStep 665189 = 124723) (by norm_num)
theorem B1484405 : Blo 291829 1484405 := bbase (se 5 (by rfl) ⟨69581, by rfl⟩ : syracuseStep 1484405 = 139163) (by norm_num)
theorem B665261 : Blo 291829 665261 := bbase (se 3 (by rfl) ⟨124736, by rfl⟩ : syracuseStep 665261 = 249473) (by norm_num)
theorem B1058501 : Blo 291829 1058501 := bbase (se 4 (by rfl) ⟨99234, by rfl⟩ : syracuseStep 1058501 = 198469) (by norm_num)
theorem B665333 : Blo 291829 665333 := bbase (se 5 (by rfl) ⟨31187, by rfl⟩ : syracuseStep 665333 = 62375) (by norm_num)
theorem B370433 : Blo 291829 370433 := bbase (se 2 (by rfl) ⟨138912, by rfl⟩ : syracuseStep 370433 = 277825) (by norm_num)
theorem B370489 : Blo 291829 370489 := bbase (se 2 (by rfl) ⟨138933, by rfl⟩ : syracuseStep 370489 = 277867) (by norm_num)
theorem B665405 : Blo 291829 665405 := bbase (se 3 (by rfl) ⟨124763, by rfl⟩ : syracuseStep 665405 = 249527) (by norm_num)
theorem B1058645 : Blo 291829 1058645 := bbase (se 9 (by rfl) ⟨3101, by rfl⟩ : syracuseStep 1058645 = 6203) (by norm_num)
theorem B665477 : Blo 291829 665477 := bbase (se 4 (by rfl) ⟨62388, by rfl⟩ : syracuseStep 665477 = 124777) (by norm_num)
theorem B370585 : Blo 291829 370585 := bbase (se 2 (by rfl) ⟨138969, by rfl⟩ : syracuseStep 370585 = 277939) (by norm_num)
theorem B993221 : Blo 291829 993221 := bbase (se 4 (by rfl) ⟨93114, by rfl⟩ : syracuseStep 993221 = 186229) (by norm_num)
theorem B665549 : Blo 291829 665549 := bbase (se 3 (by rfl) ⟨124790, by rfl⟩ : syracuseStep 665549 = 249581) (by norm_num)
theorem B469061 : Blo 291829 469061 := bbase (se 4 (by rfl) ⟨43974, by rfl⟩ : syracuseStep 469061 = 87949) (by norm_num)
theorem B370757 : Blo 291829 370757 := bbase (se 4 (by rfl) ⟨34758, by rfl⟩ : syracuseStep 370757 = 69517) (by norm_num)
theorem B370813 : Blo 291829 370813 := bbase (se 3 (by rfl) ⟨69527, by rfl⟩ : syracuseStep 370813 = 139055) (by norm_num)
theorem B469157 : Blo 291829 469157 := bbase (se 4 (by rfl) ⟨43983, by rfl⟩ : syracuseStep 469157 = 87967) (by norm_num)
theorem B469189 : Blo 291829 469189 := bbase (se 4 (by rfl) ⟨43986, by rfl⟩ : syracuseStep 469189 = 87973) (by norm_num)
theorem B370909 : Blo 291829 370909 := bbase (se 3 (by rfl) ⟨69545, by rfl⟩ : syracuseStep 370909 = 139091) (by norm_num)
theorem B600301 : Blo 291829 600301 := bbase (se 3 (by rfl) ⟨112556, by rfl⟩ : syracuseStep 600301 = 225113) (by norm_num)
theorem B1255733 : Blo 291829 1255733 := bbase (se 5 (by rfl) ⟨58862, by rfl⟩ : syracuseStep 1255733 = 117725) (by norm_num)
theorem B993653 : Blo 291829 993653 := bbase (se 5 (by rfl) ⟨46577, by rfl⟩ : syracuseStep 993653 = 93155) (by norm_num)
theorem B895349 : Blo 291829 895349 := bbase (se 5 (by rfl) ⟨41969, by rfl⟩ : syracuseStep 895349 = 83939) (by norm_num)
theorem B371081 : Blo 291829 371081 := bbase (se 2 (by rfl) ⟨139155, by rfl⟩ : syracuseStep 371081 = 278311) (by norm_num)
theorem B371137 : Blo 291829 371137 := bbase (se 2 (by rfl) ⟨139176, by rfl⟩ : syracuseStep 371137 = 278353) (by norm_num)
theorem B371233 : Blo 291829 371233 := bbase (se 2 (by rfl) ⟨139212, by rfl⟩ : syracuseStep 371233 = 278425) (by norm_num)
theorem B633413 : Blo 291829 633413 := bbase (se 4 (by rfl) ⟨59382, by rfl⟩ : syracuseStep 633413 = 118765) (by norm_num)
theorem B1092197 : Blo 291829 1092197 := bbase (se 4 (by rfl) ⟨102393, by rfl⟩ : syracuseStep 1092197 = 204787) (by norm_num)
theorem B371405 : Blo 291829 371405 := bbase (se 3 (by rfl) ⟨69638, by rfl⟩ : syracuseStep 371405 = 139277) (by norm_num)
theorem B371461 : Blo 291829 371461 := bbase (se 4 (by rfl) ⟨34824, by rfl⟩ : syracuseStep 371461 = 69649) (by norm_num)
theorem B994085 : Blo 291829 994085 := bbase (se 4 (by rfl) ⟨93195, by rfl⟩ : syracuseStep 994085 = 186391) (by norm_num)
theorem B1059653 : Blo 291829 1059653 := bbase (se 4 (by rfl) ⟨99342, by rfl⟩ : syracuseStep 1059653 = 198685) (by norm_num)
theorem B371557 : Blo 291829 371557 := bbase (se 4 (by rfl) ⟨34833, by rfl⟩ : syracuseStep 371557 = 69667) (by norm_num)
theorem B1485701 : Blo 291829 1485701 := bbase (se 4 (by rfl) ⟨139284, by rfl⟩ : syracuseStep 1485701 = 278569) (by norm_num)
theorem B371729 : Blo 291829 371729 := bbase (se 2 (by rfl) ⟨139398, by rfl⟩ : syracuseStep 371729 = 278797) (by norm_num)
theorem B371785 : Blo 291829 371785 := bbase (se 2 (by rfl) ⟨139419, by rfl⟩ : syracuseStep 371785 = 278839) (by norm_num)
theorem B797845 : Blo 291829 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B371881 : Blo 291829 371881 := bbase (se 2 (by rfl) ⟨139455, by rfl⟩ : syracuseStep 371881 = 278911) (by norm_num)
theorem B994517 : Blo 291829 994517 := bbase (se 7 (by rfl) ⟨11654, by rfl⟩ : syracuseStep 994517 = 23309) (by norm_num)
theorem B1256741 : Blo 291829 1256741 := bbase (se 4 (by rfl) ⟨117819, by rfl⟩ : syracuseStep 1256741 = 235639) (by norm_num)
theorem B372053 : Blo 291829 372053 := bbase (se 11 (by rfl) ⟨272, by rfl⟩ : syracuseStep 372053 = 545) (by norm_num)
theorem B372109 : Blo 291829 372109 := bbase (se 3 (by rfl) ⟨69770, by rfl⟩ : syracuseStep 372109 = 139541) (by norm_num)
theorem B372205 : Blo 291829 372205 := bbase (se 3 (by rfl) ⟨69788, by rfl⟩ : syracuseStep 372205 = 139577) (by norm_num)
theorem B667133 : Blo 291829 667133 := bbase (se 3 (by rfl) ⟨125087, by rfl⟩ : syracuseStep 667133 = 250175) (by norm_num)
theorem B437765 : Blo 291829 437765 := bbase (se 4 (by rfl) ⟨41040, by rfl⟩ : syracuseStep 437765 = 82081) (by norm_num)
theorem B437789 : Blo 291829 437789 := bbase (se 3 (by rfl) ⟨82085, by rfl⟩ : syracuseStep 437789 = 164171) (by norm_num)
theorem B437813 : Blo 291829 437813 := bbase (se 5 (by rfl) ⟨20522, by rfl⟩ : syracuseStep 437813 = 41045) (by norm_num)
theorem B437837 : Blo 291829 437837 := bbase (se 3 (by rfl) ⟨82094, by rfl⟩ : syracuseStep 437837 = 164189) (by norm_num)
theorem B437861 : Blo 291829 437861 := bbase (se 4 (by rfl) ⟨41049, by rfl⟩ : syracuseStep 437861 = 82099) (by norm_num)
theorem B437885 : Blo 291829 437885 := bbase (se 3 (by rfl) ⟨82103, by rfl⟩ : syracuseStep 437885 = 164207) (by norm_num)
theorem B994949 : Blo 291829 994949 := bbase (se 4 (by rfl) ⟨93276, by rfl⟩ : syracuseStep 994949 = 186553) (by norm_num)
theorem B437909 : Blo 291829 437909 := bbase (se 6 (by rfl) ⟨10263, by rfl⟩ : syracuseStep 437909 = 20527) (by norm_num)
theorem B372377 : Blo 291829 372377 := bbase (se 2 (by rfl) ⟨139641, by rfl⟩ : syracuseStep 372377 = 279283) (by norm_num)
theorem B798373 : Blo 291829 798373 := bbase (se 4 (by rfl) ⟨74847, by rfl⟩ : syracuseStep 798373 = 149695) (by norm_num)
theorem B437933 : Blo 291829 437933 := bbase (se 3 (by rfl) ⟨82112, by rfl⟩ : syracuseStep 437933 = 164225) (by norm_num)
theorem B470701 : Blo 291829 470701 := bbase (se 3 (by rfl) ⟨88256, by rfl⟩ : syracuseStep 470701 = 176513) (by norm_num)
theorem B1683125 : Blo 291829 1683125 := bbase (se 5 (by rfl) ⟨78896, by rfl⟩ : syracuseStep 1683125 = 157793) (by norm_num)
theorem B437957 : Blo 291829 437957 := bbase (se 4 (by rfl) ⟨41058, by rfl⟩ : syracuseStep 437957 = 82117) (by norm_num)
theorem B372433 : Blo 291829 372433 := bbase (se 2 (by rfl) ⟨139662, by rfl⟩ : syracuseStep 372433 = 279325) (by norm_num)
theorem B569045 : Blo 291829 569045 := bbase (se 7 (by rfl) ⟨6668, by rfl⟩ : syracuseStep 569045 = 13337) (by norm_num)
theorem B437981 : Blo 291829 437981 := bbase (se 3 (by rfl) ⟨82121, by rfl⟩ : syracuseStep 437981 = 164243) (by norm_num)
theorem B765677 : Blo 291829 765677 := bbase (se 3 (by rfl) ⟨143564, by rfl⟩ : syracuseStep 765677 = 287129) (by norm_num)
theorem B438005 : Blo 291829 438005 := bbase (se 5 (by rfl) ⟨20531, by rfl⟩ : syracuseStep 438005 = 41063) (by norm_num)
theorem B339709 : Blo 291829 339709 := bbase (se 3 (by rfl) ⟨63695, by rfl⟩ : syracuseStep 339709 = 127391) (by norm_num)
theorem B438029 : Blo 291829 438029 := bbase (se 3 (by rfl) ⟨82130, by rfl⟩ : syracuseStep 438029 = 164261) (by norm_num)
theorem B438053 : Blo 291829 438053 := bbase (se 4 (by rfl) ⟨41067, by rfl⟩ : syracuseStep 438053 = 82135) (by norm_num)
theorem B372529 : Blo 291829 372529 := bbase (se 2 (by rfl) ⟨139698, by rfl⟩ : syracuseStep 372529 = 279397) (by norm_num)
theorem B438077 : Blo 291829 438077 := bbase (se 3 (by rfl) ⟨82139, by rfl⟩ : syracuseStep 438077 = 164279) (by norm_num)
theorem B438101 : Blo 291829 438101 := bbase (se 9 (by rfl) ⟨1283, by rfl⟩ : syracuseStep 438101 = 2567) (by norm_num)
theorem B438125 : Blo 291829 438125 := bbase (se 3 (by rfl) ⟨82148, by rfl⟩ : syracuseStep 438125 = 164297) (by norm_num)
theorem B438149 : Blo 291829 438149 := bbase (se 4 (by rfl) ⟨41076, by rfl⟩ : syracuseStep 438149 = 82153) (by norm_num)
theorem B438173 : Blo 291829 438173 := bbase (se 3 (by rfl) ⟨82157, by rfl⟩ : syracuseStep 438173 = 164315) (by norm_num)
theorem B438197 : Blo 291829 438197 := bbase (se 5 (by rfl) ⟨20540, by rfl⟩ : syracuseStep 438197 = 41081) (by norm_num)
theorem B438221 : Blo 291829 438221 := bbase (se 3 (by rfl) ⟨82166, by rfl⟩ : syracuseStep 438221 = 164333) (by norm_num)
theorem B798677 : Blo 291829 798677 := bbase (se 7 (by rfl) ⟨9359, by rfl⟩ : syracuseStep 798677 = 18719) (by norm_num)
theorem B372701 : Blo 291829 372701 := bbase (se 3 (by rfl) ⟨69881, by rfl⟩ : syracuseStep 372701 = 139763) (by norm_num)
theorem B438245 : Blo 291829 438245 := bbase (se 4 (by rfl) ⟨41085, by rfl⟩ : syracuseStep 438245 = 82171) (by norm_num)
theorem B438269 : Blo 291829 438269 := bbase (se 3 (by rfl) ⟨82175, by rfl⟩ : syracuseStep 438269 = 164351) (by norm_num)
theorem B438293 : Blo 291829 438293 := bbase (se 6 (by rfl) ⟨10272, by rfl⟩ : syracuseStep 438293 = 20545) (by norm_num)
theorem B372757 : Blo 291829 372757 := bbase (se 6 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 372757 = 17473) (by norm_num)
theorem B438317 : Blo 291829 438317 := bbase (se 3 (by rfl) ⟨82184, by rfl⟩ : syracuseStep 438317 = 164369) (by norm_num)
theorem B995381 : Blo 291829 995381 := bbase (se 5 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 995381 = 93317) (by norm_num)
theorem B438341 : Blo 291829 438341 := bbase (se 4 (by rfl) ⟨41094, by rfl⟩ : syracuseStep 438341 = 82189) (by norm_num)
theorem B438365 : Blo 291829 438365 := bbase (se 3 (by rfl) ⟨82193, by rfl⟩ : syracuseStep 438365 = 164387) (by norm_num)
theorem B438389 : Blo 291829 438389 := bbase (se 5 (by rfl) ⟨20549, by rfl⟩ : syracuseStep 438389 = 41099) (by norm_num)
theorem B372853 : Blo 291829 372853 := bbase (se 5 (by rfl) ⟨17477, by rfl⟩ : syracuseStep 372853 = 34955) (by norm_num)
theorem B438413 : Blo 291829 438413 := bbase (se 3 (by rfl) ⟨82202, by rfl⟩ : syracuseStep 438413 = 164405) (by norm_num)
theorem B1486997 : Blo 291829 1486997 := bbase (se 6 (by rfl) ⟨34851, by rfl⟩ : syracuseStep 1486997 = 69703) (by norm_num)
theorem B831653 : Blo 291829 831653 := bbase (se 4 (by rfl) ⟨77967, by rfl⟩ : syracuseStep 831653 = 155935) (by norm_num)
theorem B438437 : Blo 291829 438437 := bbase (se 4 (by rfl) ⟨41103, by rfl⟩ : syracuseStep 438437 = 82207) (by norm_num)
theorem B438461 : Blo 291829 438461 := bbase (se 3 (by rfl) ⟨82211, by rfl⟩ : syracuseStep 438461 = 164423) (by norm_num)
theorem B438485 : Blo 291829 438485 := bbase (se 7 (by rfl) ⟨5138, by rfl⟩ : syracuseStep 438485 = 10277) (by norm_num)
theorem B438509 : Blo 291829 438509 := bbase (se 3 (by rfl) ⟨82220, by rfl⟩ : syracuseStep 438509 = 164441) (by norm_num)
theorem B438533 : Blo 291829 438533 := bbase (se 4 (by rfl) ⟨41112, by rfl⟩ : syracuseStep 438533 = 82225) (by norm_num)
theorem B438557 : Blo 291829 438557 := bbase (se 3 (by rfl) ⟨82229, by rfl⟩ : syracuseStep 438557 = 164459) (by norm_num)
theorem B373025 : Blo 291829 373025 := bbase (se 2 (by rfl) ⟨139884, by rfl⟩ : syracuseStep 373025 = 279769) (by norm_num)
theorem B438581 : Blo 291829 438581 := bbase (se 5 (by rfl) ⟨20558, by rfl⟩ : syracuseStep 438581 = 41117) (by norm_num)
theorem B438605 : Blo 291829 438605 := bbase (se 3 (by rfl) ⟨82238, by rfl⟩ : syracuseStep 438605 = 164477) (by norm_num)
theorem B373081 : Blo 291829 373081 := bbase (se 2 (by rfl) ⟨139905, by rfl⟩ : syracuseStep 373081 = 279811) (by norm_num)
theorem B438629 : Blo 291829 438629 := bbase (se 4 (by rfl) ⟨41121, by rfl⟩ : syracuseStep 438629 = 82243) (by norm_num)
theorem B471413 : Blo 291829 471413 := bbase (se 5 (by rfl) ⟨22097, by rfl⟩ : syracuseStep 471413 = 44195) (by norm_num)
theorem B438653 : Blo 291829 438653 := bbase (se 3 (by rfl) ⟨82247, by rfl⟩ : syracuseStep 438653 = 164495) (by norm_num)
theorem B438677 : Blo 291829 438677 := bbase (se 6 (by rfl) ⟨10281, by rfl⟩ : syracuseStep 438677 = 20563) (by norm_num)
theorem B438701 : Blo 291829 438701 := bbase (se 3 (by rfl) ⟨82256, by rfl⟩ : syracuseStep 438701 = 164513) (by norm_num)
theorem B373177 : Blo 291829 373177 := bbase (se 2 (by rfl) ⟨139941, by rfl⟩ : syracuseStep 373177 = 279883) (by norm_num)
theorem B438725 : Blo 291829 438725 := bbase (se 4 (by rfl) ⟨41130, by rfl⟩ : syracuseStep 438725 = 82261) (by norm_num)
theorem B438749 : Blo 291829 438749 := bbase (se 3 (by rfl) ⟨82265, by rfl⟩ : syracuseStep 438749 = 164531) (by norm_num)
theorem B995813 : Blo 291829 995813 := bbase (se 4 (by rfl) ⟨93357, by rfl⟩ : syracuseStep 995813 = 186715) (by norm_num)
theorem B438773 : Blo 291829 438773 := bbase (se 5 (by rfl) ⟨20567, by rfl⟩ : syracuseStep 438773 = 41135) (by norm_num)
theorem B438797 : Blo 291829 438797 := bbase (se 3 (by rfl) ⟨82274, by rfl⟩ : syracuseStep 438797 = 164549) (by norm_num)
theorem B438821 : Blo 291829 438821 := bbase (se 4 (by rfl) ⟨41139, by rfl⟩ : syracuseStep 438821 = 82279) (by norm_num)
theorem B438845 : Blo 291829 438845 := bbase (se 3 (by rfl) ⟨82283, by rfl⟩ : syracuseStep 438845 = 164567) (by norm_num)
theorem B438869 : Blo 291829 438869 := bbase (se 8 (by rfl) ⟨2571, by rfl⟩ : syracuseStep 438869 = 5143) (by norm_num)
theorem B373349 : Blo 291829 373349 := bbase (se 4 (by rfl) ⟨35001, by rfl⟩ : syracuseStep 373349 = 70003) (by norm_num)
theorem B438893 : Blo 291829 438893 := bbase (se 3 (by rfl) ⟨82292, by rfl⟩ : syracuseStep 438893 = 164585) (by norm_num)
theorem B1192565 : Blo 291829 1192565 := bbase (se 5 (by rfl) ⟨55901, by rfl⟩ : syracuseStep 1192565 = 111803) (by norm_num)
theorem B438917 : Blo 291829 438917 := bbase (se 4 (by rfl) ⟨41148, by rfl⟩ : syracuseStep 438917 = 82297) (by norm_num)
theorem B438941 : Blo 291829 438941 := bbase (se 3 (by rfl) ⟨82301, by rfl⟩ : syracuseStep 438941 = 164603) (by norm_num)
theorem B373405 : Blo 291829 373405 := bbase (se 3 (by rfl) ⟨70013, by rfl⟩ : syracuseStep 373405 = 140027) (by norm_num)
theorem B438965 : Blo 291829 438965 := bbase (se 5 (by rfl) ⟨20576, by rfl⟩ : syracuseStep 438965 = 41153) (by norm_num)
theorem B438989 : Blo 291829 438989 := bbase (se 3 (by rfl) ⟨82310, by rfl⟩ : syracuseStep 438989 = 164621) (by norm_num)
theorem B439013 : Blo 291829 439013 := bbase (se 4 (by rfl) ⟨41157, by rfl⟩ : syracuseStep 439013 = 82315) (by norm_num)
theorem B1127141 : Blo 291829 1127141 := bbase (se 4 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 1127141 = 211339) (by norm_num)
theorem B439037 : Blo 291829 439037 := bbase (se 3 (by rfl) ⟨82319, by rfl⟩ : syracuseStep 439037 = 164639) (by norm_num)
theorem B373501 : Blo 291829 373501 := bbase (se 3 (by rfl) ⟨70031, by rfl⟩ : syracuseStep 373501 = 140063) (by norm_num)
theorem B439061 : Blo 291829 439061 := bbase (se 6 (by rfl) ⟨10290, by rfl⟩ : syracuseStep 439061 = 20581) (by norm_num)
theorem B439085 : Blo 291829 439085 := bbase (se 3 (by rfl) ⟨82328, by rfl⟩ : syracuseStep 439085 = 164657) (by norm_num)
theorem B439109 : Blo 291829 439109 := bbase (se 4 (by rfl) ⟨41166, by rfl⟩ : syracuseStep 439109 = 82333) (by norm_num)
theorem B308057 : Blo 291829 308057 := bbase (se 2 (by rfl) ⟨115521, by rfl⟩ : syracuseStep 308057 = 231043) (by norm_num)
theorem B439133 : Blo 291829 439133 := bbase (se 3 (by rfl) ⟨82337, by rfl⟩ : syracuseStep 439133 = 164675) (by norm_num)
theorem B439157 : Blo 291829 439157 := bbase (se 5 (by rfl) ⟨20585, by rfl⟩ : syracuseStep 439157 = 41171) (by norm_num)
theorem B799621 : Blo 291829 799621 := bbase (se 4 (by rfl) ⟨74964, by rfl⟩ : syracuseStep 799621 = 149929) (by norm_num)
theorem B439181 : Blo 291829 439181 := bbase (se 3 (by rfl) ⟨82346, by rfl⟩ : syracuseStep 439181 = 164693) (by norm_num)
theorem B996245 : Blo 291829 996245 := bbase (se 6 (by rfl) ⟨23349, by rfl⟩ : syracuseStep 996245 = 46699) (by norm_num)
theorem B439205 : Blo 291829 439205 := bbase (se 4 (by rfl) ⟨41175, by rfl⟩ : syracuseStep 439205 = 82351) (by norm_num)
theorem B373673 : Blo 291829 373673 := bbase (se 2 (by rfl) ⟨140127, by rfl⟩ : syracuseStep 373673 = 280255) (by norm_num)
theorem B439229 : Blo 291829 439229 := bbase (se 3 (by rfl) ⟨82355, by rfl⟩ : syracuseStep 439229 = 164711) (by norm_num)
theorem B439253 : Blo 291829 439253 := bbase (se 7 (by rfl) ⟨5147, by rfl⟩ : syracuseStep 439253 = 10295) (by norm_num)
theorem B373729 : Blo 291829 373729 := bbase (se 2 (by rfl) ⟨140148, by rfl⟩ : syracuseStep 373729 = 280297) (by norm_num)
theorem B439277 : Blo 291829 439277 := bbase (se 3 (by rfl) ⟨82364, by rfl⟩ : syracuseStep 439277 = 164729) (by norm_num)
theorem B439301 : Blo 291829 439301 := bbase (se 4 (by rfl) ⟨41184, by rfl⟩ : syracuseStep 439301 = 82369) (by norm_num)
theorem B1258517 : Blo 291829 1258517 := bbase (se 6 (by rfl) ⟨29496, by rfl⟩ : syracuseStep 1258517 = 58993) (by norm_num)
theorem B472085 : Blo 291829 472085 := bbase (se 6 (by rfl) ⟨11064, by rfl⟩ : syracuseStep 472085 = 22129) (by norm_num)
theorem B439325 : Blo 291829 439325 := bbase (se 3 (by rfl) ⟨82373, by rfl⟩ : syracuseStep 439325 = 164747) (by norm_num)
theorem B701477 : Blo 291829 701477 := bbase (se 4 (by rfl) ⟨65763, by rfl⟩ : syracuseStep 701477 = 131527) (by norm_num)
theorem B439349 : Blo 291829 439349 := bbase (se 5 (by rfl) ⟨20594, by rfl⟩ : syracuseStep 439349 = 41189) (by norm_num)
theorem B373825 : Blo 291829 373825 := bbase (se 2 (by rfl) ⟨140184, by rfl⟩ : syracuseStep 373825 = 280369) (by norm_num)
theorem B439373 : Blo 291829 439373 := bbase (se 3 (by rfl) ⟨82382, by rfl⟩ : syracuseStep 439373 = 164765) (by norm_num)
theorem B439397 : Blo 291829 439397 := bbase (se 4 (by rfl) ⟨41193, by rfl⟩ : syracuseStep 439397 = 82387) (by norm_num)
theorem B439421 : Blo 291829 439421 := bbase (se 3 (by rfl) ⟨82391, by rfl⟩ : syracuseStep 439421 = 164783) (by norm_num)
theorem B439445 : Blo 291829 439445 := bbase (se 6 (by rfl) ⟨10299, by rfl⟩ : syracuseStep 439445 = 20599) (by norm_num)
theorem B439469 : Blo 291829 439469 := bbase (se 3 (by rfl) ⟨82400, by rfl⟩ : syracuseStep 439469 = 164801) (by norm_num)
theorem B439493 : Blo 291829 439493 := bbase (se 4 (by rfl) ⟨41202, by rfl⟩ : syracuseStep 439493 = 82405) (by norm_num)
theorem B439517 : Blo 291829 439517 := bbase (se 3 (by rfl) ⟨82409, by rfl⟩ : syracuseStep 439517 = 164819) (by norm_num)
theorem B701669 : Blo 291829 701669 := bbase (se 4 (by rfl) ⟨65781, by rfl⟩ : syracuseStep 701669 = 131563) (by norm_num)
theorem B373997 : Blo 291829 373997 := bbase (se 3 (by rfl) ⟨70124, by rfl⟩ : syracuseStep 373997 = 140249) (by norm_num)
theorem B439541 : Blo 291829 439541 := bbase (se 5 (by rfl) ⟨20603, by rfl⟩ : syracuseStep 439541 = 41207) (by norm_num)
theorem B439565 : Blo 291829 439565 := bbase (se 3 (by rfl) ⟨82418, by rfl⟩ : syracuseStep 439565 = 164837) (by norm_num)
theorem B439589 : Blo 291829 439589 := bbase (se 4 (by rfl) ⟨41211, by rfl⟩ : syracuseStep 439589 = 82423) (by norm_num)
theorem B374053 : Blo 291829 374053 := bbase (se 4 (by rfl) ⟨35067, by rfl⟩ : syracuseStep 374053 = 70135) (by norm_num)
theorem B439613 : Blo 291829 439613 := bbase (se 3 (by rfl) ⟨82427, by rfl⟩ : syracuseStep 439613 = 164855) (by norm_num)
theorem B832837 : Blo 291829 832837 := bbase (se 4 (by rfl) ⟨78078, by rfl⟩ : syracuseStep 832837 = 156157) (by norm_num)
theorem B996677 : Blo 291829 996677 := bbase (se 4 (by rfl) ⟨93438, by rfl⟩ : syracuseStep 996677 = 186877) (by norm_num)
theorem B439637 : Blo 291829 439637 := bbase (se 13 (by rfl) ⟨80, by rfl⟩ : syracuseStep 439637 = 161) (by norm_num)
theorem B865637 : Blo 291829 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B439661 : Blo 291829 439661 := bbase (se 3 (by rfl) ⟨82436, by rfl⟩ : syracuseStep 439661 = 164873) (by norm_num)
theorem B439685 : Blo 291829 439685 := bbase (se 4 (by rfl) ⟨41220, by rfl⟩ : syracuseStep 439685 = 82441) (by norm_num)
theorem B374149 : Blo 291829 374149 := bbase (se 4 (by rfl) ⟨35076, by rfl⟩ : syracuseStep 374149 = 70153) (by norm_num)
theorem B439709 : Blo 291829 439709 := bbase (se 3 (by rfl) ⟨82445, by rfl⟩ : syracuseStep 439709 = 164891) (by norm_num)
theorem B1488293 : Blo 291829 1488293 := bbase (se 4 (by rfl) ⟨139527, by rfl⟩ : syracuseStep 1488293 = 279055) (by norm_num)
theorem B439733 : Blo 291829 439733 := bbase (se 5 (by rfl) ⟨20612, by rfl⟩ : syracuseStep 439733 = 41225) (by norm_num)
theorem B439757 : Blo 291829 439757 := bbase (se 3 (by rfl) ⟨82454, by rfl⟩ : syracuseStep 439757 = 164909) (by norm_num)
theorem B832997 : Blo 291829 832997 := bbase (se 4 (by rfl) ⟨78093, by rfl⟩ : syracuseStep 832997 = 156187) (by norm_num)
theorem B439781 : Blo 291829 439781 := bbase (se 4 (by rfl) ⟨41229, by rfl⟩ : syracuseStep 439781 = 82459) (by norm_num)
theorem B439805 : Blo 291829 439805 := bbase (se 3 (by rfl) ⟨82463, by rfl⟩ : syracuseStep 439805 = 164927) (by norm_num)
theorem B439829 : Blo 291829 439829 := bbase (se 6 (by rfl) ⟨10308, by rfl⟩ : syracuseStep 439829 = 20617) (by norm_num)
theorem B472597 : Blo 291829 472597 := bbase (se 6 (by rfl) ⟨11076, by rfl⟩ : syracuseStep 472597 = 22153) (by norm_num)
theorem B439853 : Blo 291829 439853 := bbase (se 3 (by rfl) ⟨82472, by rfl⟩ : syracuseStep 439853 = 164945) (by norm_num)
theorem B374321 : Blo 291829 374321 := bbase (se 2 (by rfl) ⟨140370, by rfl⟩ : syracuseStep 374321 = 280741) (by norm_num)
theorem B439877 : Blo 291829 439877 := bbase (se 4 (by rfl) ⟨41238, by rfl⟩ : syracuseStep 439877 = 82477) (by norm_num)
theorem B439901 : Blo 291829 439901 := bbase (se 3 (by rfl) ⟨82481, by rfl⟩ : syracuseStep 439901 = 164963) (by norm_num)
theorem B374377 : Blo 291829 374377 := bbase (se 2 (by rfl) ⟨140391, by rfl⟩ : syracuseStep 374377 = 280783) (by norm_num)
theorem B439925 : Blo 291829 439925 := bbase (se 5 (by rfl) ⟨20621, by rfl⟩ : syracuseStep 439925 = 41243) (by norm_num)
theorem B439949 : Blo 291829 439949 := bbase (se 3 (by rfl) ⟨82490, by rfl⟩ : syracuseStep 439949 = 164981) (by norm_num)
theorem B439973 : Blo 291829 439973 := bbase (se 4 (by rfl) ⟨41247, by rfl⟩ : syracuseStep 439973 = 82495) (by norm_num)
theorem B439997 : Blo 291829 439997 := bbase (se 3 (by rfl) ⟨82499, by rfl⟩ : syracuseStep 439997 = 164999) (by norm_num)
theorem B505549 : Blo 291829 505549 := bbase (se 3 (by rfl) ⟨94790, by rfl⟩ : syracuseStep 505549 = 189581) (by norm_num)
theorem B833237 : Blo 291829 833237 := bbase (se 7 (by rfl) ⟨9764, by rfl⟩ : syracuseStep 833237 = 19529) (by norm_num)
theorem B440021 : Blo 291829 440021 := bbase (se 7 (by rfl) ⟨5156, by rfl⟩ : syracuseStep 440021 = 10313) (by norm_num)
theorem B440045 : Blo 291829 440045 := bbase (se 3 (by rfl) ⟨82508, by rfl⟩ : syracuseStep 440045 = 165017) (by norm_num)
theorem B997109 : Blo 291829 997109 := bbase (se 5 (by rfl) ⟨46739, by rfl⟩ : syracuseStep 997109 = 93479) (by norm_num)
theorem B440069 : Blo 291829 440069 := bbase (se 4 (by rfl) ⟨41256, by rfl⟩ : syracuseStep 440069 = 82513) (by norm_num)
theorem B440093 : Blo 291829 440093 := bbase (se 3 (by rfl) ⟨82517, by rfl⟩ : syracuseStep 440093 = 165035) (by norm_num)
theorem B440117 : Blo 291829 440117 := bbase (se 5 (by rfl) ⟨20630, by rfl⟩ : syracuseStep 440117 = 41261) (by norm_num)
theorem B374605 : Blo 291829 374605 := bbase (se 3 (by rfl) ⟨70238, by rfl⟩ : syracuseStep 374605 = 140477) (by norm_num)
theorem B440141 : Blo 291829 440141 := bbase (se 3 (by rfl) ⟨82526, by rfl⟩ : syracuseStep 440141 = 165053) (by norm_num)
theorem B440165 : Blo 291829 440165 := bbase (se 4 (by rfl) ⟨41265, by rfl⟩ : syracuseStep 440165 = 82531) (by norm_num)
theorem B669541 : Blo 291829 669541 := bbase (se 4 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 669541 = 125539) (by norm_num)
theorem B440189 : Blo 291829 440189 := bbase (se 3 (by rfl) ⟨82535, by rfl⟩ : syracuseStep 440189 = 165071) (by norm_num)
theorem B833429 : Blo 291829 833429 := bbase (se 6 (by rfl) ⟨19533, by rfl⟩ : syracuseStep 833429 = 39067) (by norm_num)
theorem B440213 : Blo 291829 440213 := bbase (se 6 (by rfl) ⟨10317, by rfl⟩ : syracuseStep 440213 = 20635) (by norm_num)
theorem B440237 : Blo 291829 440237 := bbase (se 3 (by rfl) ⟨82544, by rfl⟩ : syracuseStep 440237 = 165089) (by norm_num)
theorem B2996149 : Blo 291829 2996149 := bbase (se 5 (by rfl) ⟨140444, by rfl⟩ : syracuseStep 2996149 = 280889) (by norm_num)
theorem B440261 : Blo 291829 440261 := bbase (se 4 (by rfl) ⟨41274, by rfl⟩ : syracuseStep 440261 = 82549) (by norm_num)
theorem B440285 : Blo 291829 440285 := bbase (se 3 (by rfl) ⟨82553, by rfl⟩ : syracuseStep 440285 = 165107) (by norm_num)
theorem B473053 : Blo 291829 473053 := bbase (se 3 (by rfl) ⟨88697, by rfl⟩ : syracuseStep 473053 = 177395) (by norm_num)
theorem B702437 : Blo 291829 702437 := bbase (se 4 (by rfl) ⟨65853, by rfl⟩ : syracuseStep 702437 = 131707) (by norm_num)
theorem B440309 : Blo 291829 440309 := bbase (se 5 (by rfl) ⟨20639, by rfl⟩ : syracuseStep 440309 = 41279) (by norm_num)
theorem B1718261 : Blo 291829 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B604157 : Blo 291829 604157 := bbase (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) (by norm_num)
theorem B440333 : Blo 291829 440333 := bbase (se 3 (by rfl) ⟨82562, by rfl⟩ : syracuseStep 440333 = 165125) (by norm_num)
theorem B440357 : Blo 291829 440357 := bbase (se 4 (by rfl) ⟨41283, by rfl⟩ : syracuseStep 440357 = 82567) (by norm_num)
theorem B440381 : Blo 291829 440381 := bbase (se 3 (by rfl) ⟨82571, by rfl⟩ : syracuseStep 440381 = 165143) (by norm_num)
theorem B440405 : Blo 291829 440405 := bbase (se 8 (by rfl) ⟨2580, by rfl⟩ : syracuseStep 440405 = 5161) (by norm_num)
theorem B440429 : Blo 291829 440429 := bbase (se 3 (by rfl) ⟨82580, by rfl⟩ : syracuseStep 440429 = 165161) (by norm_num)
theorem B440453 : Blo 291829 440453 := bbase (se 4 (by rfl) ⟨41292, by rfl⟩ : syracuseStep 440453 = 82585) (by norm_num)
theorem B440477 : Blo 291829 440477 := bbase (se 3 (by rfl) ⟨82589, by rfl⟩ : syracuseStep 440477 = 165179) (by norm_num)
theorem B997541 : Blo 291829 997541 := bbase (se 4 (by rfl) ⟨93519, by rfl⟩ : syracuseStep 997541 = 187039) (by norm_num)
theorem B440501 : Blo 291829 440501 := bbase (se 5 (by rfl) ⟨20648, by rfl⟩ : syracuseStep 440501 = 41297) (by norm_num)
theorem B440525 : Blo 291829 440525 := bbase (se 3 (by rfl) ⟨82598, by rfl⟩ : syracuseStep 440525 = 165197) (by norm_num)
theorem B440549 : Blo 291829 440549 := bbase (se 4 (by rfl) ⟨41301, by rfl⟩ : syracuseStep 440549 = 82603) (by norm_num)
theorem B440573 : Blo 291829 440573 := bbase (se 3 (by rfl) ⟨82607, by rfl⟩ : syracuseStep 440573 = 165215) (by norm_num)
theorem B440597 : Blo 291829 440597 := bbase (se 6 (by rfl) ⟨10326, by rfl⟩ : syracuseStep 440597 = 20653) (by norm_num)
theorem B604445 : Blo 291829 604445 := bbase (se 3 (by rfl) ⟨113333, by rfl⟩ : syracuseStep 604445 = 226667) (by norm_num)
theorem B440621 : Blo 291829 440621 := bbase (se 3 (by rfl) ⟨82616, by rfl⟩ : syracuseStep 440621 = 165233) (by norm_num)
theorem B440645 : Blo 291829 440645 := bbase (se 4 (by rfl) ⟨41310, by rfl⟩ : syracuseStep 440645 = 82621) (by norm_num)
theorem B440669 : Blo 291829 440669 := bbase (se 3 (by rfl) ⟨82625, by rfl⟩ : syracuseStep 440669 = 165251) (by norm_num)
theorem B440693 : Blo 291829 440693 := bbase (se 5 (by rfl) ⟨20657, by rfl⟩ : syracuseStep 440693 = 41315) (by norm_num)
theorem B440717 : Blo 291829 440717 := bbase (se 3 (by rfl) ⟨82634, by rfl⟩ : syracuseStep 440717 = 165269) (by norm_num)
theorem B440741 : Blo 291829 440741 := bbase (se 4 (by rfl) ⟨41319, by rfl⟩ : syracuseStep 440741 = 82639) (by norm_num)
theorem B440765 : Blo 291829 440765 := bbase (se 3 (by rfl) ⟨82643, by rfl⟩ : syracuseStep 440765 = 165287) (by norm_num)
theorem B1423813 : Blo 291829 1423813 := bbase (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) (by norm_num)
theorem B440789 : Blo 291829 440789 := bbase (se 7 (by rfl) ⟨5165, by rfl⟩ : syracuseStep 440789 = 10331) (by norm_num)
theorem B440813 : Blo 291829 440813 := bbase (se 3 (by rfl) ⟨82652, by rfl⟩ : syracuseStep 440813 = 165305) (by norm_num)
theorem B440837 : Blo 291829 440837 := bbase (se 4 (by rfl) ⟨41328, by rfl⟩ : syracuseStep 440837 = 82657) (by norm_num)
theorem B440861 : Blo 291829 440861 := bbase (se 3 (by rfl) ⟨82661, by rfl⟩ : syracuseStep 440861 = 165323) (by norm_num)
theorem B440885 : Blo 291829 440885 := bbase (se 5 (by rfl) ⟨20666, by rfl⟩ : syracuseStep 440885 = 41333) (by norm_num)
theorem B440909 : Blo 291829 440909 := bbase (se 3 (by rfl) ⟨82670, by rfl⟩ : syracuseStep 440909 = 165341) (by norm_num)
theorem B997973 : Blo 291829 997973 := bbase (se 8 (by rfl) ⟨5847, by rfl⟩ : syracuseStep 997973 = 11695) (by norm_num)
theorem B375385 : Blo 291829 375385 := bbase (se 2 (by rfl) ⟨140769, by rfl⟩ : syracuseStep 375385 = 281539) (by norm_num)
theorem B440933 : Blo 291829 440933 := bbase (se 4 (by rfl) ⟨41337, by rfl⟩ : syracuseStep 440933 = 82675) (by norm_num)
theorem B440957 : Blo 291829 440957 := bbase (se 3 (by rfl) ⟨82679, by rfl⟩ : syracuseStep 440957 = 165359) (by norm_num)
theorem B473725 : Blo 291829 473725 := bbase (se 3 (by rfl) ⟨88823, by rfl⟩ : syracuseStep 473725 = 177647) (by norm_num)
theorem B440981 : Blo 291829 440981 := bbase (se 6 (by rfl) ⟨10335, by rfl⟩ : syracuseStep 440981 = 20671) (by norm_num)
theorem B441005 : Blo 291829 441005 := bbase (se 3 (by rfl) ⟨82688, by rfl⟩ : syracuseStep 441005 = 165377) (by norm_num)
theorem B1489589 : Blo 291829 1489589 := bbase (se 5 (by rfl) ⟨69824, by rfl⟩ : syracuseStep 1489589 = 139649) (by norm_num)
theorem B441029 : Blo 291829 441029 := bbase (se 4 (by rfl) ⟨41346, by rfl⟩ : syracuseStep 441029 = 82693) (by norm_num)
theorem B441053 : Blo 291829 441053 := bbase (se 3 (by rfl) ⟨82697, by rfl⟩ : syracuseStep 441053 = 165395) (by norm_num)
theorem B441077 : Blo 291829 441077 := bbase (se 5 (by rfl) ⟨20675, by rfl⟩ : syracuseStep 441077 = 41351) (by norm_num)
theorem B441101 : Blo 291829 441101 := bbase (se 3 (by rfl) ⟨82706, by rfl⟩ : syracuseStep 441101 = 165413) (by norm_num)
theorem B441125 : Blo 291829 441125 := bbase (se 4 (by rfl) ⟨41355, by rfl⟩ : syracuseStep 441125 = 82711) (by norm_num)
theorem B441149 : Blo 291829 441149 := bbase (se 3 (by rfl) ⟨82715, by rfl⟩ : syracuseStep 441149 = 165431) (by norm_num)
theorem B441173 : Blo 291829 441173 := bbase (se 9 (by rfl) ⟨1292, by rfl⟩ : syracuseStep 441173 = 2585) (by norm_num)
theorem B441197 : Blo 291829 441197 := bbase (se 3 (by rfl) ⟨82724, by rfl⟩ : syracuseStep 441197 = 165449) (by norm_num)
theorem B834421 : Blo 291829 834421 := bbase (se 5 (by rfl) ⟨39113, by rfl⟩ : syracuseStep 834421 = 78227) (by norm_num)
theorem B441221 : Blo 291829 441221 := bbase (se 4 (by rfl) ⟨41364, by rfl⟩ : syracuseStep 441221 = 82729) (by norm_num)
theorem B441245 : Blo 291829 441245 := bbase (se 3 (by rfl) ⟨82733, by rfl⟩ : syracuseStep 441245 = 165467) (by norm_num)
theorem B441269 : Blo 291829 441269 := bbase (se 5 (by rfl) ⟨20684, by rfl⟩ : syracuseStep 441269 = 41369) (by norm_num)
theorem B441293 : Blo 291829 441293 := bbase (se 3 (by rfl) ⟨82742, by rfl⟩ : syracuseStep 441293 = 165485) (by norm_num)
theorem B441317 : Blo 291829 441317 := bbase (se 4 (by rfl) ⟨41373, by rfl⟩ : syracuseStep 441317 = 82747) (by norm_num)
theorem B375797 : Blo 291829 375797 := bbase (se 5 (by rfl) ⟨17615, by rfl⟩ : syracuseStep 375797 = 35231) (by norm_num)
theorem B670709 : Blo 291829 670709 := bbase (se 5 (by rfl) ⟨31439, by rfl⟩ : syracuseStep 670709 = 62879) (by norm_num)
theorem B441341 : Blo 291829 441341 := bbase (se 3 (by rfl) ⟨82751, by rfl⟩ : syracuseStep 441341 = 165503) (by norm_num)
theorem B998405 : Blo 291829 998405 := bbase (se 4 (by rfl) ⟨93600, by rfl⟩ : syracuseStep 998405 = 187201) (by norm_num)
theorem B441365 : Blo 291829 441365 := bbase (se 6 (by rfl) ⟨10344, by rfl⟩ : syracuseStep 441365 = 20689) (by norm_num)
theorem B441389 : Blo 291829 441389 := bbase (se 3 (by rfl) ⟨82760, by rfl⟩ : syracuseStep 441389 = 165521) (by norm_num)
theorem B1883189 : Blo 291829 1883189 := bbase (se 5 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 1883189 = 176549) (by norm_num)
theorem B441413 : Blo 291829 441413 := bbase (se 4 (by rfl) ⟨41382, by rfl⟩ : syracuseStep 441413 = 82765) (by norm_num)
theorem B441437 : Blo 291829 441437 := bbase (se 3 (by rfl) ⟨82769, by rfl⟩ : syracuseStep 441437 = 165539) (by norm_num)
theorem B441461 : Blo 291829 441461 := bbase (se 5 (by rfl) ⟨20693, by rfl⟩ : syracuseStep 441461 = 41387) (by norm_num)
theorem B441485 : Blo 291829 441485 := bbase (se 3 (by rfl) ⟨82778, by rfl⟩ : syracuseStep 441485 = 165557) (by norm_num)
theorem B441509 : Blo 291829 441509 := bbase (se 4 (by rfl) ⟨41391, by rfl⟩ : syracuseStep 441509 = 82783) (by norm_num)
theorem B441533 : Blo 291829 441533 := bbase (se 3 (by rfl) ⟨82787, by rfl⟩ : syracuseStep 441533 = 165575) (by norm_num)
theorem B441557 : Blo 291829 441557 := bbase (se 7 (by rfl) ⟨5174, by rfl⟩ : syracuseStep 441557 = 10349) (by norm_num)
theorem B441581 : Blo 291829 441581 := bbase (se 3 (by rfl) ⟨82796, by rfl⟩ : syracuseStep 441581 = 165593) (by norm_num)
theorem B441605 : Blo 291829 441605 := bbase (se 4 (by rfl) ⟨41400, by rfl⟩ : syracuseStep 441605 = 82801) (by norm_num)
theorem B2243861 : Blo 291829 2243861 := bbase (se 6 (by rfl) ⟨52590, by rfl⟩ : syracuseStep 2243861 = 105181) (by norm_num)
theorem B441629 : Blo 291829 441629 := bbase (se 3 (by rfl) ⟨82805, by rfl⟩ : syracuseStep 441629 = 165611) (by norm_num)
theorem B441653 : Blo 291829 441653 := bbase (se 5 (by rfl) ⟨20702, by rfl⟩ : syracuseStep 441653 = 41405) (by norm_num)
theorem B441677 : Blo 291829 441677 := bbase (se 3 (by rfl) ⟨82814, by rfl⟩ : syracuseStep 441677 = 165629) (by norm_num)
theorem B441701 : Blo 291829 441701 := bbase (se 4 (by rfl) ⟨41409, by rfl⟩ : syracuseStep 441701 = 82819) (by norm_num)
theorem B441725 : Blo 291829 441725 := bbase (se 3 (by rfl) ⟨82823, by rfl⟩ : syracuseStep 441725 = 165647) (by norm_num)
theorem B441749 : Blo 291829 441749 := bbase (se 6 (by rfl) ⟨10353, by rfl⟩ : syracuseStep 441749 = 20707) (by norm_num)
theorem B441773 : Blo 291829 441773 := bbase (se 3 (by rfl) ⟨82832, by rfl⟩ : syracuseStep 441773 = 165665) (by norm_num)
theorem B441797 : Blo 291829 441797 := bbase (se 4 (by rfl) ⟨41418, by rfl⟩ : syracuseStep 441797 = 82837) (by norm_num)
theorem B441821 : Blo 291829 441821 := bbase (se 3 (by rfl) ⟨82841, by rfl⟩ : syracuseStep 441821 = 165683) (by norm_num)
theorem B441845 : Blo 291829 441845 := bbase (se 5 (by rfl) ⟨20711, by rfl⟩ : syracuseStep 441845 = 41423) (by norm_num)
theorem B441869 : Blo 291829 441869 := bbase (se 3 (by rfl) ⟨82850, by rfl⟩ : syracuseStep 441869 = 165701) (by norm_num)
theorem B441893 : Blo 291829 441893 := bbase (se 4 (by rfl) ⟨41427, by rfl⟩ : syracuseStep 441893 = 82855) (by norm_num)
theorem B441917 : Blo 291829 441917 := bbase (se 3 (by rfl) ⟨82859, by rfl⟩ : syracuseStep 441917 = 165719) (by norm_num)
theorem B441941 : Blo 291829 441941 := bbase (se 8 (by rfl) ⟨2589, by rfl⟩ : syracuseStep 441941 = 5179) (by norm_num)
theorem B441965 : Blo 291829 441965 := bbase (se 3 (by rfl) ⟨82868, by rfl⟩ : syracuseStep 441965 = 165737) (by norm_num)
theorem B441989 : Blo 291829 441989 := bbase (se 4 (by rfl) ⟨41436, by rfl⟩ : syracuseStep 441989 = 82873) (by norm_num)
theorem B442013 : Blo 291829 442013 := bbase (se 3 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 442013 = 165755) (by norm_num)
theorem B442037 : Blo 291829 442037 := bbase (se 5 (by rfl) ⟨20720, by rfl⟩ : syracuseStep 442037 = 41441) (by norm_num)
theorem B442061 : Blo 291829 442061 := bbase (se 3 (by rfl) ⟨82886, by rfl⟩ : syracuseStep 442061 = 165773) (by norm_num)
theorem B442085 : Blo 291829 442085 := bbase (se 4 (by rfl) ⟨41445, by rfl⟩ : syracuseStep 442085 = 82891) (by norm_num)
theorem B442109 : Blo 291829 442109 := bbase (se 3 (by rfl) ⟨82895, by rfl⟩ : syracuseStep 442109 = 165791) (by norm_num)
theorem B442133 : Blo 291829 442133 := bbase (se 6 (by rfl) ⟨10362, by rfl⟩ : syracuseStep 442133 = 20725) (by norm_num)
theorem B442157 : Blo 291829 442157 := bbase (se 3 (by rfl) ⟨82904, by rfl⟩ : syracuseStep 442157 = 165809) (by norm_num)
theorem B442181 : Blo 291829 442181 := bbase (se 4 (by rfl) ⟨41454, by rfl⟩ : syracuseStep 442181 = 82909) (by norm_num)
theorem B442205 : Blo 291829 442205 := bbase (se 3 (by rfl) ⟨82913, by rfl⟩ : syracuseStep 442205 = 165827) (by norm_num)
theorem B442229 : Blo 291829 442229 := bbase (se 5 (by rfl) ⟨20729, by rfl⟩ : syracuseStep 442229 = 41459) (by norm_num)
theorem B442253 : Blo 291829 442253 := bbase (se 3 (by rfl) ⟨82922, by rfl⟩ : syracuseStep 442253 = 165845) (by norm_num)
theorem B376741 : Blo 291829 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B442277 : Blo 291829 442277 := bbase (se 4 (by rfl) ⟨41463, by rfl⟩ : syracuseStep 442277 = 82927) (by norm_num)
theorem B442301 : Blo 291829 442301 := bbase (se 3 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 442301 = 165863) (by norm_num)
theorem B835525 : Blo 291829 835525 := bbase (se 4 (by rfl) ⟨78330, by rfl⟩ : syracuseStep 835525 = 156661) (by norm_num)
theorem B1490885 : Blo 291829 1490885 := bbase (se 4 (by rfl) ⟨139770, by rfl⟩ : syracuseStep 1490885 = 279541) (by norm_num)
theorem B2015189 : Blo 291829 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B442325 : Blo 291829 442325 := bbase (se 7 (by rfl) ⟨5183, by rfl⟩ : syracuseStep 442325 = 10367) (by norm_num)
theorem B1196005 : Blo 291829 1196005 := bbase (se 4 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 1196005 = 224251) (by norm_num)
theorem B442349 : Blo 291829 442349 := bbase (se 3 (by rfl) ⟨82940, by rfl⟩ : syracuseStep 442349 = 165881) (by norm_num)
theorem B442373 : Blo 291829 442373 := bbase (se 4 (by rfl) ⟨41472, by rfl⟩ : syracuseStep 442373 = 82945) (by norm_num)
theorem B704533 : Blo 291829 704533 := bbase (se 6 (by rfl) ⟨16512, by rfl⟩ : syracuseStep 704533 = 33025) (by norm_num)
theorem B442397 : Blo 291829 442397 := bbase (se 3 (by rfl) ⟨82949, by rfl⟩ : syracuseStep 442397 = 165899) (by norm_num)
theorem B442421 : Blo 291829 442421 := bbase (se 5 (by rfl) ⟨20738, by rfl⟩ : syracuseStep 442421 = 41477) (by norm_num)
theorem B442445 : Blo 291829 442445 := bbase (se 3 (by rfl) ⟨82958, by rfl⟩ : syracuseStep 442445 = 165917) (by norm_num)
theorem B442469 : Blo 291829 442469 := bbase (se 4 (by rfl) ⟨41481, by rfl⟩ : syracuseStep 442469 = 82963) (by norm_num)
theorem B442493 : Blo 291829 442493 := bbase (se 3 (by rfl) ⟨82967, by rfl⟩ : syracuseStep 442493 = 165935) (by norm_num)
theorem B442517 : Blo 291829 442517 := bbase (se 6 (by rfl) ⟨10371, by rfl⟩ : syracuseStep 442517 = 20743) (by norm_num)
theorem B442541 : Blo 291829 442541 := bbase (se 3 (by rfl) ⟨82976, by rfl⟩ : syracuseStep 442541 = 165953) (by norm_num)
theorem B442565 : Blo 291829 442565 := bbase (se 4 (by rfl) ⟨41490, by rfl⟩ : syracuseStep 442565 = 82981) (by norm_num)
theorem B442589 : Blo 291829 442589 := bbase (se 3 (by rfl) ⟨82985, by rfl⟩ : syracuseStep 442589 = 165971) (by norm_num)
theorem B442613 : Blo 291829 442613 := bbase (se 5 (by rfl) ⟨20747, by rfl⟩ : syracuseStep 442613 = 41495) (by norm_num)
theorem B442637 : Blo 291829 442637 := bbase (se 3 (by rfl) ⟨82994, by rfl⟩ : syracuseStep 442637 = 165989) (by norm_num)
theorem B442661 : Blo 291829 442661 := bbase (se 4 (by rfl) ⟨41499, by rfl⟩ : syracuseStep 442661 = 82999) (by norm_num)
theorem B442685 : Blo 291829 442685 := bbase (se 3 (by rfl) ⟨83003, by rfl⟩ : syracuseStep 442685 = 166007) (by norm_num)
theorem B442709 : Blo 291829 442709 := bbase (se 10 (by rfl) ⟨648, by rfl⟩ : syracuseStep 442709 = 1297) (by norm_num)
theorem B442733 : Blo 291829 442733 := bbase (se 3 (by rfl) ⟨83012, by rfl⟩ : syracuseStep 442733 = 166025) (by norm_num)
theorem B442757 : Blo 291829 442757 := bbase (se 4 (by rfl) ⟨41508, by rfl⟩ : syracuseStep 442757 = 83017) (by norm_num)
theorem B1589653 : Blo 291829 1589653 := bbase (se 6 (by rfl) ⟨37257, by rfl⟩ : syracuseStep 1589653 = 74515) (by norm_num)
theorem B442781 : Blo 291829 442781 := bbase (se 3 (by rfl) ⟨83021, by rfl⟩ : syracuseStep 442781 = 166043) (by norm_num)
theorem B311725 : Blo 291829 311725 := bbase (se 3 (by rfl) ⟨58448, by rfl⟩ : syracuseStep 311725 = 116897) (by norm_num)
theorem B442805 : Blo 291829 442805 := bbase (se 5 (by rfl) ⟨20756, by rfl⟩ : syracuseStep 442805 = 41513) (by norm_num)
theorem B442829 : Blo 291829 442829 := bbase (se 3 (by rfl) ⟨83030, by rfl⟩ : syracuseStep 442829 = 166061) (by norm_num)
theorem B442853 : Blo 291829 442853 := bbase (se 4 (by rfl) ⟨41517, by rfl⟩ : syracuseStep 442853 = 83035) (by norm_num)
theorem B442877 : Blo 291829 442877 := bbase (se 3 (by rfl) ⟨83039, by rfl⟩ : syracuseStep 442877 = 166079) (by norm_num)
theorem B442901 : Blo 291829 442901 := bbase (se 6 (by rfl) ⟨10380, by rfl⟩ : syracuseStep 442901 = 20761) (by norm_num)
theorem B442925 : Blo 291829 442925 := bbase (se 3 (by rfl) ⟨83048, by rfl⟩ : syracuseStep 442925 = 166097) (by norm_num)
theorem B442949 : Blo 291829 442949 := bbase (se 4 (by rfl) ⟨41526, by rfl⟩ : syracuseStep 442949 = 83053) (by norm_num)
theorem B442973 : Blo 291829 442973 := bbase (se 3 (by rfl) ⟨83057, by rfl⟩ : syracuseStep 442973 = 166115) (by norm_num)
theorem B442997 : Blo 291829 442997 := bbase (se 5 (by rfl) ⟨20765, by rfl⟩ : syracuseStep 442997 = 41531) (by norm_num)
theorem B705149 : Blo 291829 705149 := bbase (se 3 (by rfl) ⟨132215, by rfl⟩ : syracuseStep 705149 = 264431) (by norm_num)
theorem B443021 : Blo 291829 443021 := bbase (se 3 (by rfl) ⟨83066, by rfl⟩ : syracuseStep 443021 = 166133) (by norm_num)
theorem B443045 : Blo 291829 443045 := bbase (se 4 (by rfl) ⟨41535, by rfl⟩ : syracuseStep 443045 = 83071) (by norm_num)
theorem B705205 : Blo 291829 705205 := bbase (se 5 (by rfl) ⟨33056, by rfl⟩ : syracuseStep 705205 = 66113) (by norm_num)
theorem B443069 : Blo 291829 443069 := bbase (se 3 (by rfl) ⟨83075, by rfl⟩ : syracuseStep 443069 = 166151) (by norm_num)
theorem B443093 : Blo 291829 443093 := bbase (se 7 (by rfl) ⟨5192, by rfl⟩ : syracuseStep 443093 = 10385) (by norm_num)
theorem B443117 : Blo 291829 443117 := bbase (se 3 (by rfl) ⟨83084, by rfl⟩ : syracuseStep 443117 = 166169) (by norm_num)
theorem B443141 : Blo 291829 443141 := bbase (se 4 (by rfl) ⟨41544, by rfl⟩ : syracuseStep 443141 = 83089) (by norm_num)
theorem B443165 : Blo 291829 443165 := bbase (se 3 (by rfl) ⟨83093, by rfl⟩ : syracuseStep 443165 = 166187) (by norm_num)
theorem B443189 : Blo 291829 443189 := bbase (se 5 (by rfl) ⟨20774, by rfl⟩ : syracuseStep 443189 = 41549) (by norm_num)
theorem B443213 : Blo 291829 443213 := bbase (se 3 (by rfl) ⟨83102, by rfl⟩ : syracuseStep 443213 = 166205) (by norm_num)
theorem B443237 : Blo 291829 443237 := bbase (se 4 (by rfl) ⟨41553, by rfl⟩ : syracuseStep 443237 = 83107) (by norm_num)
theorem B312169 : Blo 291829 312169 := bbase (se 2 (by rfl) ⟨117063, by rfl⟩ : syracuseStep 312169 = 234127) (by norm_num)
theorem B443261 : Blo 291829 443261 := bbase (se 3 (by rfl) ⟨83111, by rfl⟩ : syracuseStep 443261 = 166223) (by norm_num)
theorem B2507669 : Blo 291829 2507669 := bbase (se 6 (by rfl) ⟨58773, by rfl⟩ : syracuseStep 2507669 = 117547) (by norm_num)
theorem B443285 : Blo 291829 443285 := bbase (se 6 (by rfl) ⟨10389, by rfl⟩ : syracuseStep 443285 = 20779) (by norm_num)
theorem B443309 : Blo 291829 443309 := bbase (se 3 (by rfl) ⟨83120, by rfl⟩ : syracuseStep 443309 = 166241) (by norm_num)
theorem B443333 : Blo 291829 443333 := bbase (se 4 (by rfl) ⟨41562, by rfl⟩ : syracuseStep 443333 = 83125) (by norm_num)
theorem B443357 : Blo 291829 443357 := bbase (se 3 (by rfl) ⟨83129, by rfl⟩ : syracuseStep 443357 = 166259) (by norm_num)
theorem B312293 : Blo 291829 312293 := bbase (se 4 (by rfl) ⟨29277, by rfl⟩ : syracuseStep 312293 = 58555) (by norm_num)
theorem B443381 : Blo 291829 443381 := bbase (se 5 (by rfl) ⟨20783, by rfl⟩ : syracuseStep 443381 = 41567) (by norm_num)
theorem B443405 : Blo 291829 443405 := bbase (se 3 (by rfl) ⟨83138, by rfl⟩ : syracuseStep 443405 = 166277) (by norm_num)
theorem B967717 : Blo 291829 967717 := bbase (se 4 (by rfl) ⟨90723, by rfl⟩ : syracuseStep 967717 = 181447) (by norm_num)
theorem B443429 : Blo 291829 443429 := bbase (se 4 (by rfl) ⟨41571, by rfl⟩ : syracuseStep 443429 = 83143) (by norm_num)
theorem B443453 : Blo 291829 443453 := bbase (se 3 (by rfl) ⟨83147, by rfl⟩ : syracuseStep 443453 = 166295) (by norm_num)
theorem B443477 : Blo 291829 443477 := bbase (se 8 (by rfl) ⟨2598, by rfl⟩ : syracuseStep 443477 = 5197) (by norm_num)
theorem B443501 : Blo 291829 443501 := bbase (se 3 (by rfl) ⟨83156, by rfl⟩ : syracuseStep 443501 = 166313) (by norm_num)
theorem B443525 : Blo 291829 443525 := bbase (se 4 (by rfl) ⟨41580, by rfl⟩ : syracuseStep 443525 = 83161) (by norm_num)
theorem B443549 : Blo 291829 443549 := bbase (se 3 (by rfl) ⟨83165, by rfl⟩ : syracuseStep 443549 = 166331) (by norm_num)
theorem B443573 : Blo 291829 443573 := bbase (se 5 (by rfl) ⟨20792, by rfl⟩ : syracuseStep 443573 = 41585) (by norm_num)
theorem B1262789 : Blo 291829 1262789 := bbase (se 4 (by rfl) ⟨118386, by rfl⟩ : syracuseStep 1262789 = 236773) (by norm_num)
theorem B443597 : Blo 291829 443597 := bbase (se 3 (by rfl) ⟨83174, by rfl⟩ : syracuseStep 443597 = 166349) (by norm_num)
theorem B1492181 : Blo 291829 1492181 := bbase (se 7 (by rfl) ⟨17486, by rfl⟩ : syracuseStep 1492181 = 34973) (by norm_num)
theorem B312545 : Blo 291829 312545 := bbase (se 2 (by rfl) ⟨117204, by rfl⟩ : syracuseStep 312545 = 234409) (by norm_num)
theorem B443621 : Blo 291829 443621 := bbase (se 4 (by rfl) ⟨41589, by rfl⟩ : syracuseStep 443621 = 83179) (by norm_num)
theorem B443645 : Blo 291829 443645 := bbase (se 3 (by rfl) ⟨83183, by rfl⟩ : syracuseStep 443645 = 166367) (by norm_num)
theorem B443669 : Blo 291829 443669 := bbase (se 6 (by rfl) ⟨10398, by rfl⟩ : syracuseStep 443669 = 20797) (by norm_num)
theorem B443693 : Blo 291829 443693 := bbase (se 3 (by rfl) ⟨83192, by rfl⟩ : syracuseStep 443693 = 166385) (by norm_num)
theorem B443717 : Blo 291829 443717 := bbase (se 4 (by rfl) ⟨41598, by rfl⟩ : syracuseStep 443717 = 83197) (by norm_num)
theorem B443741 : Blo 291829 443741 := bbase (se 3 (by rfl) ⟨83201, by rfl⟩ : syracuseStep 443741 = 166403) (by norm_num)
theorem B837029 : Blo 291829 837029 := bbase (se 4 (by rfl) ⟨78471, by rfl⟩ : syracuseStep 837029 = 156943) (by norm_num)
theorem B10765781 : Blo 291829 10765781 := bbase (se 7 (by rfl) ⟨126161, by rfl⟩ : syracuseStep 10765781 = 252323) (by norm_num)
theorem B738821 : Blo 291829 738821 := bbase (se 4 (by rfl) ⟨69264, by rfl⟩ : syracuseStep 738821 = 138529) (by norm_num)
theorem B673429 : Blo 291829 673429 := bbase (se 6 (by rfl) ⟨15783, by rfl⟩ : syracuseStep 673429 = 31567) (by norm_num)
theorem B312989 : Blo 291829 312989 := bbase (se 3 (by rfl) ⟨58685, by rfl⟩ : syracuseStep 312989 = 117371) (by norm_num)
theorem B706205 : Blo 291829 706205 := bbase (se 3 (by rfl) ⟨132413, by rfl⟩ : syracuseStep 706205 = 264827) (by norm_num)
theorem B444197 : Blo 291829 444197 := bbase (se 4 (by rfl) ⟨41643, by rfl⟩ : syracuseStep 444197 = 83287) (by norm_num)
theorem B739165 : Blo 291829 739165 := bbase (se 3 (by rfl) ⟨138593, by rfl⟩ : syracuseStep 739165 = 277187) (by norm_num)
theorem B313237 : Blo 291829 313237 := bbase (se 6 (by rfl) ⟨7341, by rfl⟩ : syracuseStep 313237 = 14683) (by norm_num)
theorem B739277 : Blo 291829 739277 := bbase (se 3 (by rfl) ⟨138614, by rfl⟩ : syracuseStep 739277 = 277229) (by norm_num)
theorem B477173 : Blo 291829 477173 := bbase (se 5 (by rfl) ⟨22367, by rfl⟩ : syracuseStep 477173 = 44735) (by norm_num)
theorem B1427557 : Blo 291829 1427557 := bbase (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) (by norm_num)
theorem B1001605 : Blo 291829 1001605 := bbase (se 4 (by rfl) ⟨93900, by rfl⟩ : syracuseStep 1001605 = 187801) (by norm_num)
theorem B739469 : Blo 291829 739469 := bbase (se 3 (by rfl) ⟨138650, by rfl⟩ : syracuseStep 739469 = 277301) (by norm_num)
theorem B313681 : Blo 291829 313681 := bbase (se 2 (by rfl) ⟨117630, by rfl⟩ : syracuseStep 313681 = 235261) (by norm_num)
theorem B1198469 : Blo 291829 1198469 := bbase (se 4 (by rfl) ⟨112356, by rfl⟩ : syracuseStep 1198469 = 224713) (by norm_num)
theorem B313741 : Blo 291829 313741 := bbase (se 3 (by rfl) ⟨58826, by rfl⟩ : syracuseStep 313741 = 117653) (by norm_num)
theorem B739813 : Blo 291829 739813 := bbase (se 4 (by rfl) ⟨69357, by rfl⟩ : syracuseStep 739813 = 138715) (by norm_num)
theorem B1493477 : Blo 291829 1493477 := bbase (se 4 (by rfl) ⟨140013, by rfl⟩ : syracuseStep 1493477 = 280027) (by norm_num)
theorem B739925 : Blo 291829 739925 := bbase (se 8 (by rfl) ⟨4335, by rfl⟩ : syracuseStep 739925 = 8671) (by norm_num)
theorem B1428101 : Blo 291829 1428101 := bbase (se 4 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 1428101 = 267769) (by norm_num)
theorem B314057 : Blo 291829 314057 := bbase (se 2 (by rfl) ⟨117771, by rfl⟩ : syracuseStep 314057 = 235543) (by norm_num)
theorem B740117 : Blo 291829 740117 := bbase (se 6 (by rfl) ⟨17346, by rfl⟩ : syracuseStep 740117 = 34693) (by norm_num)
theorem B1002341 : Blo 291829 1002341 := bbase (se 4 (by rfl) ⟨93969, by rfl⟩ : syracuseStep 1002341 = 187939) (by norm_num)
theorem B543629 : Blo 291829 543629 := bbase (se 3 (by rfl) ⟨101930, by rfl⟩ : syracuseStep 543629 = 203861) (by norm_num)
theorem B2837429 : Blo 291829 2837429 := bbase (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) (by norm_num)
theorem B936917 : Blo 291829 936917 := bbase (se 7 (by rfl) ⟨10979, by rfl⟩ : syracuseStep 936917 = 21959) (by norm_num)
theorem B838613 : Blo 291829 838613 := bbase (se 7 (by rfl) ⟨9827, by rfl⟩ : syracuseStep 838613 = 19655) (by norm_num)
theorem B740461 : Blo 291829 740461 := bbase (se 3 (by rfl) ⟨138836, by rfl⟩ : syracuseStep 740461 = 277673) (by norm_num)
theorem B314501 : Blo 291829 314501 := bbase (se 4 (by rfl) ⟨29484, by rfl⟩ : syracuseStep 314501 = 58969) (by norm_num)
theorem B314561 : Blo 291829 314561 := bbase (se 2 (by rfl) ⟨117960, by rfl⟩ : syracuseStep 314561 = 235921) (by norm_num)
theorem B740573 : Blo 291829 740573 := bbase (se 3 (by rfl) ⟨138857, by rfl⟩ : syracuseStep 740573 = 277715) (by norm_num)
theorem B1002725 : Blo 291829 1002725 := bbase (se 4 (by rfl) ⟨94005, by rfl⟩ : syracuseStep 1002725 = 188011) (by norm_num)
theorem B478469 : Blo 291829 478469 := bbase (se 4 (by rfl) ⟨44856, by rfl⟩ : syracuseStep 478469 = 89713) (by norm_num)
theorem B2379029 : Blo 291829 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B314689 : Blo 291829 314689 := bbase (se 2 (by rfl) ⟨118008, by rfl⟩ : syracuseStep 314689 = 236017) (by norm_num)
theorem B740765 : Blo 291829 740765 := bbase (se 3 (by rfl) ⟨138893, by rfl⟩ : syracuseStep 740765 = 277787) (by norm_num)
theorem B839285 : Blo 291829 839285 := bbase (se 5 (by rfl) ⟨39341, by rfl⟩ : syracuseStep 839285 = 78683) (by norm_num)
theorem B2248373 : Blo 291829 2248373 := bbase (se 5 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 2248373 = 210785) (by norm_num)
theorem B741109 : Blo 291829 741109 := bbase (se 5 (by rfl) ⟨34739, by rfl⟩ : syracuseStep 741109 = 69479) (by norm_num)
theorem B1494773 : Blo 291829 1494773 := bbase (se 5 (by rfl) ⟨70067, by rfl⟩ : syracuseStep 1494773 = 140135) (by norm_num)
theorem B315133 : Blo 291829 315133 := bbase (se 3 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 315133 = 118175) (by norm_num)
theorem B937813 : Blo 291829 937813 := bbase (se 9 (by rfl) ⟨2747, by rfl⟩ : syracuseStep 937813 = 5495) (by norm_num)
theorem B2117461 : Blo 291829 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B741221 : Blo 291829 741221 := bbase (se 4 (by rfl) ⟨69489, by rfl⟩ : syracuseStep 741221 = 138979) (by norm_num)
theorem B315253 : Blo 291829 315253 := bbase (se 5 (by rfl) ⟨14777, by rfl⟩ : syracuseStep 315253 = 29555) (by norm_num)
theorem B708581 : Blo 291829 708581 := bbase (se 4 (by rfl) ⟨66429, by rfl⟩ : syracuseStep 708581 = 132859) (by norm_num)
theorem B741413 : Blo 291829 741413 := bbase (se 4 (by rfl) ⟨69507, by rfl⟩ : syracuseStep 741413 = 139015) (by norm_num)
theorem B446501 : Blo 291829 446501 := bbase (se 4 (by rfl) ⟨41859, by rfl⟩ : syracuseStep 446501 = 83719) (by norm_num)
theorem B839717 : Blo 291829 839717 := bbase (se 4 (by rfl) ⟨78723, by rfl⟩ : syracuseStep 839717 = 157447) (by norm_num)
theorem B315505 : Blo 291829 315505 := bbase (se 2 (by rfl) ⟨118314, by rfl⟩ : syracuseStep 315505 = 236629) (by norm_num)
theorem B315509 : Blo 291829 315509 := bbase (se 5 (by rfl) ⟨14789, by rfl⟩ : syracuseStep 315509 = 29579) (by norm_num)
theorem B512173 : Blo 291829 512173 := bbase (se 3 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 512173 = 192065) (by norm_num)
theorem B938213 : Blo 291829 938213 := bbase (se 4 (by rfl) ⟨87957, by rfl⟩ : syracuseStep 938213 = 175915) (by norm_num)
theorem B708965 : Blo 291829 708965 := bbase (se 4 (by rfl) ⟨66465, by rfl⟩ : syracuseStep 708965 = 132931) (by norm_num)
theorem B1134965 : Blo 291829 1134965 := bbase (se 5 (by rfl) ⟨53201, by rfl⟩ : syracuseStep 1134965 = 106403) (by norm_num)
theorem B741757 : Blo 291829 741757 := bbase (se 3 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 741757 = 278159) (by norm_num)
theorem B741869 : Blo 291829 741869 := bbase (se 3 (by rfl) ⟨139100, by rfl⟩ : syracuseStep 741869 = 278201) (by norm_num)
theorem B709165 : Blo 291829 709165 := bbase (se 3 (by rfl) ⟨132968, by rfl⟩ : syracuseStep 709165 = 265937) (by norm_num)
theorem B742061 : Blo 291829 742061 := bbase (se 3 (by rfl) ⟨139136, by rfl⟩ : syracuseStep 742061 = 278273) (by norm_num)
theorem B840469 : Blo 291829 840469 := bbase (se 6 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 840469 = 39397) (by norm_num)
theorem B3363605 : Blo 291829 3363605 := bbase (se 6 (by rfl) ⟨78834, by rfl⟩ : syracuseStep 3363605 = 157669) (by norm_num)
theorem B742405 : Blo 291829 742405 := bbase (se 4 (by rfl) ⟨69600, by rfl⟩ : syracuseStep 742405 = 139201) (by norm_num)
theorem B1496069 : Blo 291829 1496069 := bbase (se 4 (by rfl) ⟨140256, by rfl⟩ : syracuseStep 1496069 = 280513) (by norm_num)
theorem B2249845 : Blo 291829 2249845 := bbase (se 5 (by rfl) ⟨105461, by rfl⟩ : syracuseStep 2249845 = 210923) (by norm_num)
theorem B742517 : Blo 291829 742517 := bbase (se 5 (by rfl) ⟨34805, by rfl⟩ : syracuseStep 742517 = 69611) (by norm_num)
theorem B742709 : Blo 291829 742709 := bbase (se 5 (by rfl) ⟨34814, by rfl⟩ : syracuseStep 742709 = 69629) (by norm_num)
theorem B447869 : Blo 291829 447869 := bbase (se 3 (by rfl) ⟨83975, by rfl⟩ : syracuseStep 447869 = 167951) (by norm_num)
theorem B1136117 : Blo 291829 1136117 := bbase (se 5 (by rfl) ⟨53255, by rfl⟩ : syracuseStep 1136117 = 106511) (by norm_num)
theorem B1070725 : Blo 291829 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B743053 : Blo 291829 743053 := bbase (se 3 (by rfl) ⟨139322, by rfl⟩ : syracuseStep 743053 = 278645) (by norm_num)
theorem B743165 : Blo 291829 743165 := bbase (se 3 (by rfl) ⟨139343, by rfl⟩ : syracuseStep 743165 = 278687) (by norm_num)
theorem B415525 : Blo 291829 415525 := bbase (se 4 (by rfl) ⟨38955, by rfl⟩ : syracuseStep 415525 = 77911) (by norm_num)
theorem B1595189 : Blo 291829 1595189 := bbase (se 5 (by rfl) ⟨74774, by rfl⟩ : syracuseStep 1595189 = 149549) (by norm_num)
theorem B415621 : Blo 291829 415621 := bbase (se 4 (by rfl) ⟨38964, by rfl⟩ : syracuseStep 415621 = 77929) (by norm_num)
theorem B743357 : Blo 291829 743357 := bbase (se 3 (by rfl) ⟨139379, by rfl⟩ : syracuseStep 743357 = 278759) (by norm_num)
theorem B448453 : Blo 291829 448453 := bbase (se 4 (by rfl) ⟨42042, by rfl⟩ : syracuseStep 448453 = 84085) (by norm_num)
theorem B710741 : Blo 291829 710741 := bbase (se 8 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 710741 = 8329) (by norm_num)
theorem B743701 : Blo 291829 743701 := bbase (se 6 (by rfl) ⟨17430, by rfl⟩ : syracuseStep 743701 = 34861) (by norm_num)
theorem B1497365 : Blo 291829 1497365 := bbase (se 6 (by rfl) ⟨35094, by rfl⟩ : syracuseStep 1497365 = 70189) (by norm_num)
theorem B1136933 : Blo 291829 1136933 := bbase (se 4 (by rfl) ⟨106587, by rfl⟩ : syracuseStep 1136933 = 213175) (by norm_num)
theorem B416117 : Blo 291829 416117 := bbase (se 5 (by rfl) ⟨19505, by rfl⟩ : syracuseStep 416117 = 39011) (by norm_num)
theorem B743813 : Blo 291829 743813 := bbase (se 4 (by rfl) ⟨69732, by rfl⟩ : syracuseStep 743813 = 139465) (by norm_num)
theorem B744005 : Blo 291829 744005 := bbase (se 4 (by rfl) ⟨69750, by rfl⟩ : syracuseStep 744005 = 139501) (by norm_num)
theorem B351065 : Blo 291829 351065 := bbase (se 2 (by rfl) ⟨131649, by rfl⟩ : syracuseStep 351065 = 263299) (by norm_num)
theorem B416669 : Blo 291829 416669 := bbase (se 3 (by rfl) ⟨78125, by rfl⟩ : syracuseStep 416669 = 156251) (by norm_num)
theorem B744349 : Blo 291829 744349 := bbase (se 3 (by rfl) ⟨139565, by rfl⟩ : syracuseStep 744349 = 279131) (by norm_num)
theorem B318425 : Blo 291829 318425 := bbase (se 2 (by rfl) ⟨119409, by rfl⟩ : syracuseStep 318425 = 238819) (by norm_num)
theorem B744461 : Blo 291829 744461 := bbase (se 3 (by rfl) ⟨139586, by rfl⟩ : syracuseStep 744461 = 279173) (by norm_num)
theorem B351253 : Blo 291829 351253 := bbase (se 6 (by rfl) ⟨8232, by rfl⟩ : syracuseStep 351253 = 16465) (by norm_num)
theorem B744653 : Blo 291829 744653 := bbase (se 3 (by rfl) ⟨139622, by rfl⟩ : syracuseStep 744653 = 279245) (by norm_num)
theorem B351469 : Blo 291829 351469 := bbase (se 3 (by rfl) ⟨65900, by rfl⟩ : syracuseStep 351469 = 131801) (by norm_num)
theorem B351757 : Blo 291829 351757 := bbase (se 3 (by rfl) ⟨65954, by rfl⟩ : syracuseStep 351757 = 131909) (by norm_num)
theorem B744997 : Blo 291829 744997 := bbase (se 4 (by rfl) ⟨69843, by rfl⟩ : syracuseStep 744997 = 139687) (by norm_num)
theorem B2022965 : Blo 291829 2022965 := bbase (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) (by norm_num)
theorem B417421 : Blo 291829 417421 := bbase (se 3 (by rfl) ⟨78266, by rfl⟩ : syracuseStep 417421 = 156533) (by norm_num)
theorem B745109 : Blo 291829 745109 := bbase (se 6 (by rfl) ⟨17463, by rfl⟩ : syracuseStep 745109 = 34927) (by norm_num)
theorem B745301 : Blo 291829 745301 := bbase (se 9 (by rfl) ⟨2183, by rfl⟩ : syracuseStep 745301 = 4367) (by norm_num)
theorem B942005 : Blo 291829 942005 := bbase (se 5 (by rfl) ⟨44156, by rfl⟩ : syracuseStep 942005 = 88313) (by norm_num)
theorem B319469 : Blo 291829 319469 := bbase (se 3 (by rfl) ⟨59900, by rfl⟩ : syracuseStep 319469 = 119801) (by norm_num)
theorem B745645 : Blo 291829 745645 := bbase (se 3 (by rfl) ⟨139808, by rfl⟩ : syracuseStep 745645 = 279617) (by norm_num)
theorem B745757 : Blo 291829 745757 := bbase (se 3 (by rfl) ⟨139829, by rfl⟩ : syracuseStep 745757 = 279659) (by norm_num)
theorem B418213 : Blo 291829 418213 := bbase (se 4 (by rfl) ⟨39207, by rfl⟩ : syracuseStep 418213 = 78415) (by norm_num)
theorem B745949 : Blo 291829 745949 := bbase (se 3 (by rfl) ⟨139865, by rfl⟩ : syracuseStep 745949 = 279731) (by norm_num)
theorem B2220533 : Blo 291829 2220533 := bbase (se 5 (by rfl) ⟨104087, by rfl⟩ : syracuseStep 2220533 = 208175) (by norm_num)
theorem B418549 : Blo 291829 418549 := bbase (se 5 (by rfl) ⟨19619, by rfl⟩ : syracuseStep 418549 = 39239) (by norm_num)
theorem B353045 : Blo 291829 353045 := bbase (se 6 (by rfl) ⟨8274, by rfl⟩ : syracuseStep 353045 = 16549) (by norm_num)
theorem B746293 : Blo 291829 746293 := bbase (se 5 (by rfl) ⟨34982, by rfl⟩ : syracuseStep 746293 = 69965) (by norm_num)
theorem B746405 : Blo 291829 746405 := bbase (se 4 (by rfl) ⟨69975, by rfl⟩ : syracuseStep 746405 = 139951) (by norm_num)
theorem B418765 : Blo 291829 418765 := bbase (se 3 (by rfl) ⟨78518, by rfl⟩ : syracuseStep 418765 = 157037) (by norm_num)
theorem B943093 : Blo 291829 943093 := bbase (se 5 (by rfl) ⟨44207, by rfl⟩ : syracuseStep 943093 = 88415) (by norm_num)
theorem B746597 : Blo 291829 746597 := bbase (se 4 (by rfl) ⟨69993, by rfl⟩ : syracuseStep 746597 = 139987) (by norm_num)
theorem B419141 : Blo 291829 419141 := bbase (se 4 (by rfl) ⟨39294, by rfl⟩ : syracuseStep 419141 = 78589) (by norm_num)
theorem B353641 : Blo 291829 353641 := bbase (se 2 (by rfl) ⟨132615, by rfl⟩ : syracuseStep 353641 = 265231) (by norm_num)
theorem B746941 : Blo 291829 746941 := bbase (se 3 (by rfl) ⟨140051, by rfl⟩ : syracuseStep 746941 = 280103) (by norm_num)
theorem B353737 : Blo 291829 353737 := bbase (se 2 (by rfl) ⟨132651, by rfl⟩ : syracuseStep 353737 = 265303) (by norm_num)
theorem B747053 : Blo 291829 747053 := bbase (se 3 (by rfl) ⟨140072, by rfl⟩ : syracuseStep 747053 = 280145) (by norm_num)
theorem B747245 : Blo 291829 747245 := bbase (se 3 (by rfl) ⟨140108, by rfl⟩ : syracuseStep 747245 = 280217) (by norm_num)
theorem B747589 : Blo 291829 747589 := bbase (se 4 (by rfl) ⟨70086, by rfl⟩ : syracuseStep 747589 = 140173) (by norm_num)
theorem B944261 : Blo 291829 944261 := bbase (se 4 (by rfl) ⟨88524, by rfl⟩ : syracuseStep 944261 = 177049) (by norm_num)
theorem B1403029 : Blo 291829 1403029 := bbase (se 6 (by rfl) ⟨32883, by rfl⟩ : syracuseStep 1403029 = 65767) (by norm_num)
theorem B747701 : Blo 291829 747701 := bbase (se 5 (by rfl) ⟨35048, by rfl⟩ : syracuseStep 747701 = 70097) (by norm_num)
theorem B3565781 : Blo 291829 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B747893 : Blo 291829 747893 := bbase (se 5 (by rfl) ⟨35057, by rfl⟩ : syracuseStep 747893 = 70115) (by norm_num)
theorem B354881 : Blo 291829 354881 := bbase (se 2 (by rfl) ⟨133080, by rfl⟩ : syracuseStep 354881 = 266161) (by norm_num)
theorem B748237 : Blo 291829 748237 := bbase (se 3 (by rfl) ⟨140294, by rfl⟩ : syracuseStep 748237 = 280589) (by norm_num)
theorem B420565 : Blo 291829 420565 := bbase (se 7 (by rfl) ⟨4928, by rfl⟩ : syracuseStep 420565 = 9857) (by norm_num)
theorem B1338133 : Blo 291829 1338133 := bbase (se 6 (by rfl) ⟨31362, by rfl⟩ : syracuseStep 1338133 = 62725) (by norm_num)
theorem B748349 : Blo 291829 748349 := bbase (se 3 (by rfl) ⟨140315, by rfl⟩ : syracuseStep 748349 = 280631) (by norm_num)
theorem B355213 : Blo 291829 355213 := bbase (se 3 (by rfl) ⟨66602, by rfl⟩ : syracuseStep 355213 = 133205) (by norm_num)
theorem B748541 : Blo 291829 748541 := bbase (se 3 (by rfl) ⟨140351, by rfl⟩ : syracuseStep 748541 = 280703) (by norm_num)
theorem B1109173 : Blo 291829 1109173 := bbase (se 5 (by rfl) ⟨51992, by rfl⟩ : syracuseStep 1109173 = 103985) (by norm_num)
theorem B421157 : Blo 291829 421157 := bbase (se 4 (by rfl) ⟨39483, by rfl⟩ : syracuseStep 421157 = 78967) (by norm_num)
theorem B1109477 : Blo 291829 1109477 := bbase (se 4 (by rfl) ⟨104013, by rfl⟩ : syracuseStep 1109477 = 208027) (by norm_num)
theorem B716701 : Blo 291829 716701 := bbase (se 3 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 716701 = 268763) (by norm_num)
theorem B946117 : Blo 291829 946117 := bbase (se 4 (by rfl) ⟨88698, by rfl⟩ : syracuseStep 946117 = 177397) (by norm_num)
theorem B749645 : Blo 291829 749645 := bbase (se 3 (by rfl) ⟨140558, by rfl⟩ : syracuseStep 749645 = 281117) (by norm_num)
theorem B1667861 : Blo 291829 1667861 := bbase (se 6 (by rfl) ⟨39090, by rfl⟩ : syracuseStep 1667861 = 78181) (by norm_num)
theorem B5043221 : Blo 291829 5043221 := bbase (se 6 (by rfl) ⟨118200, by rfl⟩ : syracuseStep 5043221 = 236401) (by norm_num)
theorem B947477 : Blo 291829 947477 := bbase (se 6 (by rfl) ⟨22206, by rfl⟩ : syracuseStep 947477 = 44413) (by norm_num)
theorem B1340837 : Blo 291829 1340837 := bbase (se 4 (by rfl) ⟨125703, by rfl⟩ : syracuseStep 1340837 = 251407) (by norm_num)
theorem B1111589 : Blo 291829 1111589 := bbase (se 4 (by rfl) ⟨104211, by rfl⟩ : syracuseStep 1111589 = 208423) (by norm_num)
theorem B1898101 : Blo 291829 1898101 := bbase (se 5 (by rfl) ⟨88973, by rfl⟩ : syracuseStep 1898101 = 177947) (by norm_num)
theorem B1406645 : Blo 291829 1406645 := bbase (se 5 (by rfl) ⟨65936, by rfl⟩ : syracuseStep 1406645 = 131873) (by norm_num)
theorem B554701 : Blo 291829 554701 := bbase (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) (by norm_num)
theorem B1111877 : Blo 291829 1111877 := bbase (se 4 (by rfl) ⟨104238, by rfl⟩ : syracuseStep 1111877 = 208477) (by norm_num)
theorem B554845 : Blo 291829 554845 := bbase (se 3 (by rfl) ⟨104033, by rfl⟩ : syracuseStep 554845 = 208067) (by norm_num)
theorem B1669045 : Blo 291829 1669045 := bbase (se 5 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 1669045 = 156473) (by norm_num)
theorem B555005 : Blo 291829 555005 := bbase (se 3 (by rfl) ⟨104063, by rfl⟩ : syracuseStep 555005 = 208127) (by norm_num)
theorem B555149 : Blo 291829 555149 := bbase (se 3 (by rfl) ⟨104090, by rfl⟩ : syracuseStep 555149 = 208181) (by norm_num)
theorem B555437 : Blo 291829 555437 := bbase (se 3 (by rfl) ⟨104144, by rfl⟩ : syracuseStep 555437 = 208289) (by norm_num)
theorem B1800629 : Blo 291829 1800629 := bbase (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) (by norm_num)
theorem B555589 : Blo 291829 555589 := bbase (se 4 (by rfl) ⟨52086, by rfl⟩ : syracuseStep 555589 = 104173) (by norm_num)
theorem B424525 : Blo 291829 424525 := bbase (se 3 (by rfl) ⟨79598, by rfl⟩ : syracuseStep 424525 = 159197) (by norm_num)
theorem B1079957 : Blo 291829 1079957 := bbase (se 6 (by rfl) ⟨25311, by rfl⟩ : syracuseStep 1079957 = 50623) (by norm_num)
theorem B359257 : Blo 291829 359257 := bbase (se 2 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 359257 = 269443) (by norm_num)
theorem B555893 : Blo 291829 555893 := bbase (se 5 (by rfl) ⟨26057, by rfl⟩ : syracuseStep 555893 = 52115) (by norm_num)
theorem B1113061 : Blo 291829 1113061 := bbase (se 4 (by rfl) ⟨104349, by rfl⟩ : syracuseStep 1113061 = 208699) (by norm_num)
theorem B1113365 : Blo 291829 1113365 := bbase (se 6 (by rfl) ⟨26094, by rfl⟩ : syracuseStep 1113365 = 52189) (by norm_num)
theorem B753029 : Blo 291829 753029 := bbase (se 4 (by rfl) ⟨70596, by rfl⟩ : syracuseStep 753029 = 141193) (by norm_num)
theorem B1408549 : Blo 291829 1408549 := bbase (se 4 (by rfl) ⟨132051, by rfl⟩ : syracuseStep 1408549 = 264103) (by norm_num)
theorem B1408565 : Blo 291829 1408565 := bbase (se 5 (by rfl) ⟨66026, by rfl⟩ : syracuseStep 1408565 = 132053) (by norm_num)
theorem B556645 : Blo 291829 556645 := bbase (se 4 (by rfl) ⟨52185, by rfl⟩ : syracuseStep 556645 = 104371) (by norm_num)
theorem B556789 : Blo 291829 556789 := bbase (se 5 (by rfl) ⟨26099, by rfl⟩ : syracuseStep 556789 = 52199) (by norm_num)
theorem B1671029 : Blo 291829 1671029 := bbase (se 5 (by rfl) ⟨78329, by rfl⟩ : syracuseStep 1671029 = 156659) (by norm_num)
theorem B556949 : Blo 291829 556949 := bbase (se 6 (by rfl) ⟨13053, by rfl⟩ : syracuseStep 556949 = 26107) (by norm_num)
theorem B655285 : Blo 291829 655285 := bbase (se 5 (by rfl) ⟨30716, by rfl⟩ : syracuseStep 655285 = 61433) (by norm_num)
theorem B294915 : Blo 291829 294915 := bstep (se 1 (by rfl) ⟨221186, by rfl⟩ : syracuseStep 294915 = 442373) B442373
theorem B294931 : Blo 291829 294931 := bstep (se 1 (by rfl) ⟨221198, by rfl⟩ : syracuseStep 294931 = 442397) B442397
theorem B294947 : Blo 291829 294947 := bstep (se 1 (by rfl) ⟨221210, by rfl⟩ : syracuseStep 294947 = 442421) B442421
theorem B294963 : Blo 291829 294963 := bstep (se 1 (by rfl) ⟨221222, by rfl⟩ : syracuseStep 294963 = 442445) B442445
theorem B294979 : Blo 291829 294979 := bstep (se 1 (by rfl) ⟨221234, by rfl⟩ : syracuseStep 294979 = 442469) B442469
theorem B294995 : Blo 291829 294995 := bstep (se 1 (by rfl) ⟨221246, by rfl⟩ : syracuseStep 294995 = 442493) B442493
theorem B295011 : Blo 291829 295011 := bstep (se 1 (by rfl) ⟨221258, by rfl⟩ : syracuseStep 295011 = 442517) B442517
theorem B295027 : Blo 291829 295027 := bstep (se 1 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 295027 = 442541) B442541
theorem B295043 : Blo 291829 295043 := bstep (se 1 (by rfl) ⟨221282, by rfl⟩ : syracuseStep 295043 = 442565) B442565
theorem B295059 : Blo 291829 295059 := bstep (se 1 (by rfl) ⟨221294, by rfl⟩ : syracuseStep 295059 = 442589) B442589
theorem B295075 : Blo 291829 295075 := bstep (se 1 (by rfl) ⟨221306, by rfl⟩ : syracuseStep 295075 = 442613) B442613
theorem B295091 : Blo 291829 295091 := bstep (se 1 (by rfl) ⟨221318, by rfl⟩ : syracuseStep 295091 = 442637) B442637
theorem B295107 : Blo 291829 295107 := bstep (se 1 (by rfl) ⟨221330, by rfl⟩ : syracuseStep 295107 = 442661) B442661
theorem B295123 : Blo 291829 295123 := bstep (se 1 (by rfl) ⟨221342, by rfl⟩ : syracuseStep 295123 = 442685) B442685
theorem B295139 : Blo 291829 295139 := bstep (se 1 (by rfl) ⟨221354, by rfl⟩ : syracuseStep 295139 = 442709) B442709
theorem B295155 : Blo 291829 295155 := bstep (se 1 (by rfl) ⟨221366, by rfl⟩ : syracuseStep 295155 = 442733) B442733
theorem B295171 : Blo 291829 295171 := bstep (se 1 (by rfl) ⟨221378, by rfl⟩ : syracuseStep 295171 = 442757) B442757
theorem B295187 : Blo 291829 295187 := bstep (se 1 (by rfl) ⟨221390, by rfl⟩ : syracuseStep 295187 = 442781) B442781
theorem B295203 : Blo 291829 295203 := bstep (se 1 (by rfl) ⟨221402, by rfl⟩ : syracuseStep 295203 = 442805) B442805
theorem B295219 : Blo 291829 295219 := bstep (se 1 (by rfl) ⟨221414, by rfl⟩ : syracuseStep 295219 = 442829) B442829
theorem B295235 : Blo 291829 295235 := bstep (se 1 (by rfl) ⟨221426, by rfl⟩ : syracuseStep 295235 = 442853) B442853
theorem B295251 : Blo 291829 295251 := bstep (se 1 (by rfl) ⟨221438, by rfl⟩ : syracuseStep 295251 = 442877) B442877
theorem B295267 : Blo 291829 295267 := bstep (se 1 (by rfl) ⟨221450, by rfl⟩ : syracuseStep 295267 = 442901) B442901
theorem B295283 : Blo 291829 295283 := bstep (se 1 (by rfl) ⟨221462, by rfl⟩ : syracuseStep 295283 = 442925) B442925
theorem B295299 : Blo 291829 295299 := bstep (se 1 (by rfl) ⟨221474, by rfl⟩ : syracuseStep 295299 = 442949) B442949
theorem B295315 : Blo 291829 295315 := bstep (se 1 (by rfl) ⟨221486, by rfl⟩ : syracuseStep 295315 = 442973) B442973
theorem B295331 : Blo 291829 295331 := bstep (se 1 (by rfl) ⟨221498, by rfl⟩ : syracuseStep 295331 = 442997) B442997
theorem B295347 : Blo 291829 295347 := bstep (se 1 (by rfl) ⟨221510, by rfl⟩ : syracuseStep 295347 = 443021) B443021
theorem B295363 : Blo 291829 295363 := bstep (se 1 (by rfl) ⟨221522, by rfl⟩ : syracuseStep 295363 = 443045) B443045
theorem B295379 : Blo 291829 295379 := bstep (se 1 (by rfl) ⟨221534, by rfl⟩ : syracuseStep 295379 = 443069) B443069
theorem B295395 : Blo 291829 295395 := bstep (se 1 (by rfl) ⟨221546, by rfl⟩ : syracuseStep 295395 = 443093) B443093
theorem B295411 : Blo 291829 295411 := bstep (se 1 (by rfl) ⟨221558, by rfl⟩ : syracuseStep 295411 = 443117) B443117
theorem B295427 : Blo 291829 295427 := bstep (se 1 (by rfl) ⟨221570, by rfl⟩ : syracuseStep 295427 = 443141) B443141
theorem B295443 : Blo 291829 295443 := bstep (se 1 (by rfl) ⟨221582, by rfl⟩ : syracuseStep 295443 = 443165) B443165
theorem B295459 : Blo 291829 295459 := bstep (se 1 (by rfl) ⟨221594, by rfl⟩ : syracuseStep 295459 = 443189) B443189
theorem B557617 : Blo 291829 557617 := bstep (se 2 (by rfl) ⟨209106, by rfl⟩ : syracuseStep 557617 = 418213) B418213
theorem B295475 : Blo 291829 295475 := bstep (se 1 (by rfl) ⟨221606, by rfl⟩ : syracuseStep 295475 = 443213) B443213
theorem B295491 : Blo 291829 295491 := bstep (se 1 (by rfl) ⟨221618, by rfl⟩ : syracuseStep 295491 = 443237) B443237
theorem B295507 : Blo 291829 295507 := bstep (se 1 (by rfl) ⟨221630, by rfl⟩ : syracuseStep 295507 = 443261) B443261
theorem B1671779 : Blo 291829 1671779 := bstep (se 1 (by rfl) ⟨1253834, by rfl⟩ : syracuseStep 1671779 = 2507669) B2507669
theorem B295523 : Blo 291829 295523 := bstep (se 1 (by rfl) ⟨221642, by rfl⟩ : syracuseStep 295523 = 443285) B443285
theorem B295539 : Blo 291829 295539 := bstep (se 1 (by rfl) ⟨221654, by rfl⟩ : syracuseStep 295539 = 443309) B443309
theorem B295555 : Blo 291829 295555 := bstep (se 1 (by rfl) ⟨221666, by rfl⟩ : syracuseStep 295555 = 443333) B443333
theorem B295571 : Blo 291829 295571 := bstep (se 1 (by rfl) ⟨221678, by rfl⟩ : syracuseStep 295571 = 443357) B443357
theorem B295587 : Blo 291829 295587 := bstep (se 1 (by rfl) ⟨221690, by rfl⟩ : syracuseStep 295587 = 443381) B443381
theorem B295603 : Blo 291829 295603 := bstep (se 1 (by rfl) ⟨221702, by rfl⟩ : syracuseStep 295603 = 443405) B443405
theorem B328387 : Blo 291829 328387 := bstep (se 1 (by rfl) ⟨246290, by rfl⟩ : syracuseStep 328387 = 492581) B492581
theorem B295619 : Blo 291829 295619 := bstep (se 1 (by rfl) ⟨221714, by rfl⟩ : syracuseStep 295619 = 443429) B443429
theorem B295635 : Blo 291829 295635 := bstep (se 1 (by rfl) ⟨221726, by rfl⟩ : syracuseStep 295635 = 443453) B443453
theorem B295651 : Blo 291829 295651 := bstep (se 1 (by rfl) ⟨221738, by rfl⟩ : syracuseStep 295651 = 443477) B443477
theorem B295667 : Blo 291829 295667 := bstep (se 1 (by rfl) ⟨221750, by rfl⟩ : syracuseStep 295667 = 443501) B443501
theorem B295683 : Blo 291829 295683 := bstep (se 1 (by rfl) ⟨221762, by rfl⟩ : syracuseStep 295683 = 443525) B443525
theorem B295699 : Blo 291829 295699 := bstep (se 1 (by rfl) ⟨221774, by rfl⟩ : syracuseStep 295699 = 443549) B443549
theorem B295715 : Blo 291829 295715 := bstep (se 1 (by rfl) ⟨221786, by rfl⟩ : syracuseStep 295715 = 443573) B443573
theorem B295731 : Blo 291829 295731 := bstep (se 1 (by rfl) ⟨221798, by rfl⟩ : syracuseStep 295731 = 443597) B443597
theorem B295747 : Blo 291829 295747 := bstep (se 1 (by rfl) ⟨221810, by rfl⟩ : syracuseStep 295747 = 443621) B443621
theorem B328531 : Blo 291829 328531 := bstep (se 1 (by rfl) ⟨246398, by rfl⟩ : syracuseStep 328531 = 492797) B492797
theorem B295763 : Blo 291829 295763 := bstep (se 1 (by rfl) ⟨221822, by rfl⟩ : syracuseStep 295763 = 443645) B443645
theorem B295779 : Blo 291829 295779 := bstep (se 1 (by rfl) ⟨221834, by rfl⟩ : syracuseStep 295779 = 443669) B443669
theorem B295795 : Blo 291829 295795 := bstep (se 1 (by rfl) ⟨221846, by rfl⟩ : syracuseStep 295795 = 443693) B443693
theorem B295811 : Blo 291829 295811 := bstep (se 1 (by rfl) ⟨221858, by rfl⟩ : syracuseStep 295811 = 443717) B443717
theorem B295827 : Blo 291829 295827 := bstep (se 1 (by rfl) ⟨221870, by rfl⟩ : syracuseStep 295827 = 443741) B443741
theorem B558019 : Blo 291829 558019 := bstep (se 1 (by rfl) ⟨418514, by rfl⟩ : syracuseStep 558019 = 837029) B837029
theorem B328675 : Blo 291829 328675 := bstep (se 1 (by rfl) ⟨246506, by rfl⟩ : syracuseStep 328675 = 493013) B493013
theorem B7177187 : Blo 291829 7177187 := bstep (se 1 (by rfl) ⟨5382890, by rfl⟩ : syracuseStep 7177187 = 10765781) B10765781
theorem B558065 : Blo 291829 558065 := bstep (se 2 (by rfl) ⟨209274, by rfl⟩ : syracuseStep 558065 = 418549) B418549
theorem B492547 : Blo 291829 492547 := bstep (se 1 (by rfl) ⟨369410, by rfl⟩ : syracuseStep 492547 = 738821) B738821
theorem B328819 : Blo 291829 328819 := bstep (se 1 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 328819 = 493229) B493229
theorem B492689 : Blo 291829 492689 := bstep (se 2 (by rfl) ⟨184758, by rfl⟩ : syracuseStep 492689 = 369517) B369517
theorem B296131 : Blo 291829 296131 := bstep (se 1 (by rfl) ⟨222098, by rfl⟩ : syracuseStep 296131 = 444197) B444197
theorem B328963 : Blo 291829 328963 := bstep (se 1 (by rfl) ⟨246722, by rfl⟩ : syracuseStep 328963 = 493445) B493445
theorem B656657 : Blo 291829 656657 := bstep (se 2 (by rfl) ⟨246246, by rfl⟩ : syracuseStep 656657 = 492493) B492493
theorem B492817 : Blo 291829 492817 := bstep (se 2 (by rfl) ⟨184806, by rfl⟩ : syracuseStep 492817 = 369613) B369613
theorem B558353 : Blo 291829 558353 := bstep (se 2 (by rfl) ⟨209382, by rfl⟩ : syracuseStep 558353 = 418765) B418765
theorem B656675 : Blo 291829 656675 := bstep (se 1 (by rfl) ⟨492506, by rfl⟩ : syracuseStep 656675 = 985013) B985013
theorem B492851 : Blo 291829 492851 := bstep (se 1 (by rfl) ⟨369638, by rfl⟩ : syracuseStep 492851 = 739277) B739277
theorem B1115491 : Blo 291829 1115491 := bstep (se 1 (by rfl) ⟨836618, by rfl⟩ : syracuseStep 1115491 = 1673237) B1673237
theorem B329107 : Blo 291829 329107 := bstep (se 1 (by rfl) ⟨246830, by rfl⟩ : syracuseStep 329107 = 493661) B493661
theorem B492979 : Blo 291829 492979 := bstep (se 1 (by rfl) ⟨369734, by rfl⟩ : syracuseStep 492979 = 739469) B739469
theorem B329251 : Blo 291829 329251 := bstep (se 1 (by rfl) ⟨246938, by rfl⟩ : syracuseStep 329251 = 493877) B493877
theorem B656945 : Blo 291829 656945 := bstep (se 2 (by rfl) ⟨246354, by rfl⟩ : syracuseStep 656945 = 492709) B492709
theorem B493121 : Blo 291829 493121 := bstep (se 2 (by rfl) ⟨184920, by rfl⟩ : syracuseStep 493121 = 369841) B369841
theorem B656963 : Blo 291829 656963 := bstep (se 1 (by rfl) ⟨492722, by rfl⟩ : syracuseStep 656963 = 985445) B985445
theorem B788077 : Blo 291829 788077 := bstep (se 3 (by rfl) ⟨147764, by rfl⟩ : syracuseStep 788077 = 295529) B295529
theorem B329395 : Blo 291829 329395 := bstep (se 1 (by rfl) ⟨247046, by rfl⟩ : syracuseStep 329395 = 494093) B494093
theorem B493249 : Blo 291829 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B493283 : Blo 291829 493283 := bstep (se 1 (by rfl) ⟨369962, by rfl⟩ : syracuseStep 493283 = 739925) B739925
theorem B952067 : Blo 291829 952067 := bstep (se 1 (by rfl) ⟨714050, by rfl⟩ : syracuseStep 952067 = 1428101) B1428101
theorem B329539 : Blo 291829 329539 := bstep (se 1 (by rfl) ⟨247154, by rfl⟩ : syracuseStep 329539 = 494309) B494309
theorem B657233 : Blo 291829 657233 := bstep (se 2 (by rfl) ⟨246462, by rfl⟩ : syracuseStep 657233 = 492925) B492925
theorem B657251 : Blo 291829 657251 := bstep (se 1 (by rfl) ⟨492938, by rfl⟩ : syracuseStep 657251 = 985877) B985877
theorem B493411 : Blo 291829 493411 := bstep (se 1 (by rfl) ⟨370058, by rfl⟩ : syracuseStep 493411 = 740117) B740117
theorem B329683 : Blo 291829 329683 := bstep (se 1 (by rfl) ⟨247262, by rfl⟩ : syracuseStep 329683 = 494525) B494525
theorem B624611 : Blo 291829 624611 := bstep (se 1 (by rfl) ⟨468458, by rfl⟩ : syracuseStep 624611 = 936917) B936917
theorem B559075 : Blo 291829 559075 := bstep (se 1 (by rfl) ⟨419306, by rfl⟩ : syracuseStep 559075 = 838613) B838613
theorem B493553 : Blo 291829 493553 := bstep (se 2 (by rfl) ⟨185082, by rfl⟩ : syracuseStep 493553 = 370165) B370165
theorem B1247309 : Blo 291829 1247309 := bstep (se 3 (by rfl) ⟨233870, by rfl⟩ : syracuseStep 1247309 = 467741) B467741
theorem B329827 : Blo 291829 329827 := bstep (se 1 (by rfl) ⟨247370, by rfl⟩ : syracuseStep 329827 = 494741) B494741
theorem B657521 : Blo 291829 657521 := bstep (se 2 (by rfl) ⟨246570, by rfl⟩ : syracuseStep 657521 = 493141) B493141
theorem B493681 : Blo 291829 493681 := bstep (se 2 (by rfl) ⟨185130, by rfl⟩ : syracuseStep 493681 = 370261) B370261
theorem B657539 : Blo 291829 657539 := bstep (se 1 (by rfl) ⟨493154, by rfl⟩ : syracuseStep 657539 = 986309) B986309
theorem B985229 : Blo 291829 985229 := bstep (se 3 (by rfl) ⟨184730, by rfl⟩ : syracuseStep 985229 = 369461) B369461
theorem B493715 : Blo 291829 493715 := bstep (se 1 (by rfl) ⟨370286, by rfl⟩ : syracuseStep 493715 = 740573) B740573
theorem B985283 : Blo 291829 985283 := bstep (se 1 (by rfl) ⟨738962, by rfl⟩ : syracuseStep 985283 = 1477925) B1477925
theorem B821485 : Blo 291829 821485 := bstep (se 3 (by rfl) ⟨154028, by rfl⟩ : syracuseStep 821485 = 308057) B308057
theorem B329971 : Blo 291829 329971 := bstep (se 1 (by rfl) ⟨247478, by rfl⟩ : syracuseStep 329971 = 494957) B494957
theorem B493843 : Blo 291829 493843 := bstep (se 1 (by rfl) ⟨370382, by rfl⟩ : syracuseStep 493843 = 740765) B740765
theorem B3180869 : Blo 291829 3180869 := bstep (se 4 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 3180869 = 596413) B596413
theorem B330115 : Blo 291829 330115 := bstep (se 1 (by rfl) ⟨247586, by rfl⟩ : syracuseStep 330115 = 495173) B495173
theorem B657809 : Blo 291829 657809 := bstep (se 2 (by rfl) ⟨246678, by rfl⟩ : syracuseStep 657809 = 493357) B493357
theorem B493985 : Blo 291829 493985 := bstep (se 2 (by rfl) ⟨185244, by rfl⟩ : syracuseStep 493985 = 370489) B370489
theorem B657827 : Blo 291829 657827 := bstep (se 1 (by rfl) ⟨493370, by rfl⟩ : syracuseStep 657827 = 986741) B986741
theorem B559523 : Blo 291829 559523 := bstep (se 1 (by rfl) ⟨419642, by rfl⟩ : syracuseStep 559523 = 839285) B839285
theorem B723395 : Blo 291829 723395 := bstep (se 1 (by rfl) ⟨542546, by rfl⟩ : syracuseStep 723395 = 1085093) B1085093
theorem B788945 : Blo 291829 788945 := bstep (se 2 (by rfl) ⟨295854, by rfl⟩ : syracuseStep 788945 = 591709) B591709
theorem B985553 : Blo 291829 985553 := bstep (se 2 (by rfl) ⟨369582, by rfl⟩ : syracuseStep 985553 = 739165) B739165
theorem B330259 : Blo 291829 330259 := bstep (se 1 (by rfl) ⟨247694, by rfl⟩ : syracuseStep 330259 = 495389) B495389
theorem B494113 : Blo 291829 494113 := bstep (se 2 (by rfl) ⟨185292, by rfl⟩ : syracuseStep 494113 = 370585) B370585
theorem B526915 : Blo 291829 526915 := bstep (se 1 (by rfl) ⟨395186, by rfl⟩ : syracuseStep 526915 = 790373) B790373
theorem B494147 : Blo 291829 494147 := bstep (se 1 (by rfl) ⟨370610, by rfl⟩ : syracuseStep 494147 = 741221) B741221
theorem B395857 : Blo 291829 395857 := bstep (se 2 (by rfl) ⟨148446, by rfl⟩ : syracuseStep 395857 = 296893) B296893
theorem B330403 : Blo 291829 330403 := bstep (se 1 (by rfl) ⟨247802, by rfl⟩ : syracuseStep 330403 = 495605) B495605
theorem B658097 : Blo 291829 658097 := bstep (se 2 (by rfl) ⟨246786, by rfl⟩ : syracuseStep 658097 = 493573) B493573
theorem B658115 : Blo 291829 658115 := bstep (se 1 (by rfl) ⟨493586, by rfl⟩ : syracuseStep 658115 = 987173) B987173
theorem B494275 : Blo 291829 494275 := bstep (se 1 (by rfl) ⟨370706, by rfl⟩ : syracuseStep 494275 = 741413) B741413
theorem B297667 : Blo 291829 297667 := bstep (se 1 (by rfl) ⟨223250, by rfl⟩ : syracuseStep 297667 = 446501) B446501
theorem B559811 : Blo 291829 559811 := bstep (se 1 (by rfl) ⟨419858, by rfl⟩ : syracuseStep 559811 = 839717) B839717
theorem B1903409 : Blo 291829 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B330547 : Blo 291829 330547 := bstep (se 1 (by rfl) ⟨247910, by rfl⟩ : syracuseStep 330547 = 495821) B495821
theorem B625475 : Blo 291829 625475 := bstep (se 1 (by rfl) ⟨469106, by rfl⟩ : syracuseStep 625475 = 938213) B938213
theorem B494417 : Blo 291829 494417 := bstep (se 2 (by rfl) ⟨185406, by rfl⟩ : syracuseStep 494417 = 370813) B370813
theorem B1870705 : Blo 291829 1870705 := bstep (se 2 (by rfl) ⟨701514, by rfl⟩ : syracuseStep 1870705 = 1403029) B1403029
theorem B756643 : Blo 291829 756643 := bstep (se 1 (by rfl) ⟨567482, by rfl⟩ : syracuseStep 756643 = 1134965) B1134965
theorem B625585 : Blo 291829 625585 := bstep (se 2 (by rfl) ⟨234594, by rfl⟩ : syracuseStep 625585 = 469189) B469189
theorem B330691 : Blo 291829 330691 := bstep (se 1 (by rfl) ⟨248018, by rfl⟩ : syracuseStep 330691 = 496037) B496037
theorem B658385 : Blo 291829 658385 := bstep (se 2 (by rfl) ⟨246894, by rfl⟩ : syracuseStep 658385 = 493789) B493789
theorem B494545 : Blo 291829 494545 := bstep (se 2 (by rfl) ⟨185454, by rfl⟩ : syracuseStep 494545 = 370909) B370909
theorem B396257 : Blo 291829 396257 := bstep (se 2 (by rfl) ⟨148596, by rfl⟩ : syracuseStep 396257 = 297193) B297193
theorem B658403 : Blo 291829 658403 := bstep (se 1 (by rfl) ⟨493802, by rfl⟩ : syracuseStep 658403 = 987605) B987605
theorem B986093 : Blo 291829 986093 := bstep (se 3 (by rfl) ⟨184892, by rfl⟩ : syracuseStep 986093 = 369785) B369785
theorem B494579 : Blo 291829 494579 := bstep (se 1 (by rfl) ⟨370934, by rfl⟩ : syracuseStep 494579 = 741869) B741869
theorem B986147 : Blo 291829 986147 := bstep (se 1 (by rfl) ⟨739610, by rfl⟩ : syracuseStep 986147 = 1479221) B1479221
theorem B396371 : Blo 291829 396371 := bstep (se 1 (by rfl) ⟨297278, by rfl⟩ : syracuseStep 396371 = 594557) B594557
theorem B330835 : Blo 291829 330835 := bstep (se 1 (by rfl) ⟨248126, by rfl⟩ : syracuseStep 330835 = 496253) B496253
theorem B494707 : Blo 291829 494707 := bstep (se 1 (by rfl) ⟨371030, by rfl⟩ : syracuseStep 494707 = 742061) B742061
theorem B330979 : Blo 291829 330979 := bstep (se 1 (by rfl) ⟨248234, by rfl⟩ : syracuseStep 330979 = 496469) B496469
theorem B658673 : Blo 291829 658673 := bstep (se 2 (by rfl) ⟨247002, by rfl⟩ : syracuseStep 658673 = 494005) B494005
theorem B494849 : Blo 291829 494849 := bstep (se 2 (by rfl) ⟨185568, by rfl⟩ : syracuseStep 494849 = 371137) B371137
theorem B658691 : Blo 291829 658691 := bstep (se 1 (by rfl) ⟨494018, by rfl⟩ : syracuseStep 658691 = 988037) B988037
theorem B986417 : Blo 291829 986417 := bstep (se 2 (by rfl) ⟨369906, by rfl⟩ : syracuseStep 986417 = 739813) B739813
theorem B2035043 : Blo 291829 2035043 := bstep (se 1 (by rfl) ⟨1526282, by rfl⟩ : syracuseStep 2035043 = 3052565) B3052565
theorem B888173 : Blo 291829 888173 := bstep (se 3 (by rfl) ⟨166532, by rfl⟩ : syracuseStep 888173 = 333065) B333065
theorem B331123 : Blo 291829 331123 := bstep (se 1 (by rfl) ⟨248342, by rfl⟩ : syracuseStep 331123 = 496685) B496685
theorem B494977 : Blo 291829 494977 := bstep (se 2 (by rfl) ⟨185616, by rfl⟩ : syracuseStep 494977 = 371233) B371233
theorem B495011 : Blo 291829 495011 := bstep (se 1 (by rfl) ⟨371258, by rfl⟩ : syracuseStep 495011 = 742517) B742517
theorem B396787 : Blo 291829 396787 := bstep (se 1 (by rfl) ⟨297590, by rfl⟩ : syracuseStep 396787 = 595181) B595181
theorem B331267 : Blo 291829 331267 := bstep (se 1 (by rfl) ⟨248450, by rfl⟩ : syracuseStep 331267 = 496901) B496901
theorem B1117709 : Blo 291829 1117709 := bstep (se 3 (by rfl) ⟨209570, by rfl⟩ : syracuseStep 1117709 = 419141) B419141
theorem B658961 : Blo 291829 658961 := bstep (se 2 (by rfl) ⟨247110, by rfl⟩ : syracuseStep 658961 = 494221) B494221
theorem B658979 : Blo 291829 658979 := bstep (se 1 (by rfl) ⟨494234, by rfl⟩ : syracuseStep 658979 = 988469) B988469
theorem B495139 : Blo 291829 495139 := bstep (se 1 (by rfl) ⟨371354, by rfl⟩ : syracuseStep 495139 = 742709) B742709
theorem B396851 : Blo 291829 396851 := bstep (se 1 (by rfl) ⟨297638, by rfl⟩ : syracuseStep 396851 = 595277) B595277
theorem B527939 : Blo 291829 527939 := bstep (se 1 (by rfl) ⟨395954, by rfl⟩ : syracuseStep 527939 = 791909) B791909
theorem B527953 : Blo 291829 527953 := bstep (se 2 (by rfl) ⟨197982, by rfl⟩ : syracuseStep 527953 = 395965) B395965
theorem B560753 : Blo 291829 560753 := bstep (se 2 (by rfl) ⟨210282, by rfl⟩ : syracuseStep 560753 = 420565) B420565
theorem B790157 : Blo 291829 790157 := bstep (se 3 (by rfl) ⟨148154, by rfl⟩ : syracuseStep 790157 = 296309) B296309
theorem B331411 : Blo 291829 331411 := bstep (se 1 (by rfl) ⟨248558, by rfl⟩ : syracuseStep 331411 = 497117) B497117
theorem B495281 : Blo 291829 495281 := bstep (se 2 (by rfl) ⟨185730, by rfl⟩ : syracuseStep 495281 = 371461) B371461
theorem B331555 : Blo 291829 331555 := bstep (se 1 (by rfl) ⟨248666, by rfl⟩ : syracuseStep 331555 = 497333) B497333
theorem B659249 : Blo 291829 659249 := bstep (se 2 (by rfl) ⟨247218, by rfl⟩ : syracuseStep 659249 = 494437) B494437
theorem B495409 : Blo 291829 495409 := bstep (se 2 (by rfl) ⟨185778, by rfl⟩ : syracuseStep 495409 = 371557) B371557
theorem B659267 : Blo 291829 659267 := bstep (se 1 (by rfl) ⟨494450, by rfl⟩ : syracuseStep 659267 = 988901) B988901
theorem B986957 : Blo 291829 986957 := bstep (se 3 (by rfl) ⟨185054, by rfl⟩ : syracuseStep 986957 = 370109) B370109
theorem B495443 : Blo 291829 495443 := bstep (se 1 (by rfl) ⟨371582, by rfl⟩ : syracuseStep 495443 = 743165) B743165
theorem B987011 : Blo 291829 987011 := bstep (se 1 (by rfl) ⟨740258, by rfl⟩ : syracuseStep 987011 = 1480517) B1480517
theorem B5345165 : Blo 291829 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B331699 : Blo 291829 331699 := bstep (se 1 (by rfl) ⟨248774, by rfl⟩ : syracuseStep 331699 = 497549) B497549
theorem B1052621 : Blo 291829 1052621 := bstep (se 3 (by rfl) ⟨197366, by rfl⟩ : syracuseStep 1052621 = 394733) B394733
theorem B495571 : Blo 291829 495571 := bstep (se 1 (by rfl) ⟨371678, by rfl⟩ : syracuseStep 495571 = 743357) B743357
theorem B331843 : Blo 291829 331843 := bstep (se 1 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 331843 = 497765) B497765
theorem B659537 : Blo 291829 659537 := bstep (se 2 (by rfl) ⟨247326, by rfl⟩ : syracuseStep 659537 = 494653) B494653
theorem B495713 : Blo 291829 495713 := bstep (se 2 (by rfl) ⟨185892, by rfl⟩ : syracuseStep 495713 = 371785) B371785
theorem B659555 : Blo 291829 659555 := bstep (se 1 (by rfl) ⟨494666, by rfl⟩ : syracuseStep 659555 = 989333) B989333
theorem B987281 : Blo 291829 987281 := bstep (se 2 (by rfl) ⟨370230, by rfl⟩ : syracuseStep 987281 = 740461) B740461
theorem B757955 : Blo 291829 757955 := bstep (se 1 (by rfl) ⟨568466, by rfl⟩ : syracuseStep 757955 = 1136933) B1136933
theorem B331987 : Blo 291829 331987 := bstep (se 1 (by rfl) ⟨248990, by rfl⟩ : syracuseStep 331987 = 497981) B497981
theorem B495841 : Blo 291829 495841 := bstep (se 2 (by rfl) ⟨185940, by rfl⟩ : syracuseStep 495841 = 371881) B371881
theorem B1478897 : Blo 291829 1478897 := bstep (se 2 (by rfl) ⟨554586, by rfl⟩ : syracuseStep 1478897 = 1109173) B1109173
theorem B495875 : Blo 291829 495875 := bstep (se 1 (by rfl) ⟨371906, by rfl⟩ : syracuseStep 495875 = 743813) B743813
theorem B332131 : Blo 291829 332131 := bstep (se 1 (by rfl) ⟨249098, by rfl⟩ : syracuseStep 332131 = 498197) B498197
theorem B659825 : Blo 291829 659825 := bstep (se 2 (by rfl) ⟨247434, by rfl⟩ : syracuseStep 659825 = 494869) B494869
theorem B659843 : Blo 291829 659843 := bstep (se 1 (by rfl) ⟨494882, by rfl⟩ : syracuseStep 659843 = 989765) B989765
theorem B496003 : Blo 291829 496003 := bstep (se 1 (by rfl) ⟨372002, by rfl⟩ : syracuseStep 496003 = 744005) B744005
theorem B332275 : Blo 291829 332275 := bstep (se 1 (by rfl) ⟨249206, by rfl⟩ : syracuseStep 332275 = 498413) B498413
theorem B496145 : Blo 291829 496145 := bstep (se 2 (by rfl) ⟨186054, by rfl⟩ : syracuseStep 496145 = 372109) B372109
theorem B528977 : Blo 291829 528977 := bstep (se 2 (by rfl) ⟨198366, by rfl⟩ : syracuseStep 528977 = 396733) B396733
theorem B332419 : Blo 291829 332419 := bstep (se 1 (by rfl) ⟨249314, by rfl⟩ : syracuseStep 332419 = 498629) B498629
theorem B660113 : Blo 291829 660113 := bstep (se 2 (by rfl) ⟨247542, by rfl⟩ : syracuseStep 660113 = 495085) B495085
theorem B496273 : Blo 291829 496273 := bstep (se 2 (by rfl) ⟨186102, by rfl⟩ : syracuseStep 496273 = 372205) B372205
theorem B660131 : Blo 291829 660131 := bstep (se 1 (by rfl) ⟨495098, by rfl⟩ : syracuseStep 660131 = 990197) B990197
theorem B987821 : Blo 291829 987821 := bstep (se 3 (by rfl) ⟨185216, by rfl⟩ : syracuseStep 987821 = 370433) B370433
theorem B496307 : Blo 291829 496307 := bstep (se 1 (by rfl) ⟨372230, by rfl⟩ : syracuseStep 496307 = 744461) B744461
theorem B4264645 : Blo 291829 4264645 := bstep (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) B799621
theorem B987875 : Blo 291829 987875 := bstep (se 1 (by rfl) ⟨740906, by rfl⟩ : syracuseStep 987875 = 1481813) B1481813
theorem B332563 : Blo 291829 332563 := bstep (se 1 (by rfl) ⟨249422, by rfl⟩ : syracuseStep 332563 = 498845) B498845
theorem B496435 : Blo 291829 496435 := bstep (se 1 (by rfl) ⟨372326, by rfl⟩ : syracuseStep 496435 = 744653) B744653
theorem B627601 : Blo 291829 627601 := bstep (se 2 (by rfl) ⟨235350, by rfl⟩ : syracuseStep 627601 = 470701) B470701
theorem B332707 : Blo 291829 332707 := bstep (se 1 (by rfl) ⟨249530, by rfl⟩ : syracuseStep 332707 = 499061) B499061
theorem B660401 : Blo 291829 660401 := bstep (se 2 (by rfl) ⟨247650, by rfl⟩ : syracuseStep 660401 = 495301) B495301
theorem B496577 : Blo 291829 496577 := bstep (se 2 (by rfl) ⟨186216, by rfl⟩ : syracuseStep 496577 = 372433) B372433
theorem B660419 : Blo 291829 660419 := bstep (se 1 (by rfl) ⟨495314, by rfl⟩ : syracuseStep 660419 = 990629) B990629
theorem B988145 : Blo 291829 988145 := bstep (se 2 (by rfl) ⟨370554, by rfl⟩ : syracuseStep 988145 = 741109) B741109
theorem B1348643 : Blo 291829 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B496705 : Blo 291829 496705 := bstep (se 2 (by rfl) ⟨186264, by rfl⟩ : syracuseStep 496705 = 372529) B372529
theorem B1053773 : Blo 291829 1053773 := bstep (se 3 (by rfl) ⟨197582, by rfl⟩ : syracuseStep 1053773 = 395165) B395165
theorem B496739 : Blo 291829 496739 := bstep (se 1 (by rfl) ⟨372554, by rfl⟩ : syracuseStep 496739 = 745109) B745109
theorem B1250417 : Blo 291829 1250417 := bstep (se 2 (by rfl) ⟨468906, by rfl⟩ : syracuseStep 1250417 = 937813) B937813
theorem B2823281 : Blo 291829 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B595075 : Blo 291829 595075 := bstep (se 1 (by rfl) ⟨446306, by rfl⟩ : syracuseStep 595075 = 892613) B892613
theorem B660689 : Blo 291829 660689 := bstep (se 2 (by rfl) ⟨247758, by rfl⟩ : syracuseStep 660689 = 495517) B495517
theorem B955601 : Blo 291829 955601 := bstep (se 2 (by rfl) ⟨358350, by rfl⟩ : syracuseStep 955601 = 716701) B716701
theorem B660707 : Blo 291829 660707 := bstep (se 1 (by rfl) ⟨495530, by rfl⟩ : syracuseStep 660707 = 991061) B991061
theorem B496867 : Blo 291829 496867 := bstep (se 1 (by rfl) ⟨372650, by rfl⟩ : syracuseStep 496867 = 745301) B745301
theorem B628003 : Blo 291829 628003 := bstep (se 1 (by rfl) ⟨471002, by rfl⟩ : syracuseStep 628003 = 942005) B942005
theorem B1611085 : Blo 291829 1611085 := bstep (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) B604157
theorem B497009 : Blo 291829 497009 := bstep (se 2 (by rfl) ⟨186378, by rfl⟩ : syracuseStep 497009 = 372757) B372757
theorem B660977 : Blo 291829 660977 := bstep (se 2 (by rfl) ⟨247866, by rfl⟩ : syracuseStep 660977 = 495733) B495733
theorem B497137 : Blo 291829 497137 := bstep (se 2 (by rfl) ⟨186426, by rfl⟩ : syracuseStep 497137 = 372853) B372853
theorem B660995 : Blo 291829 660995 := bstep (se 1 (by rfl) ⟨495746, by rfl⟩ : syracuseStep 660995 = 991493) B991493
theorem B988685 : Blo 291829 988685 := bstep (se 3 (by rfl) ⟨185378, by rfl⟩ : syracuseStep 988685 = 370757) B370757
theorem B497171 : Blo 291829 497171 := bstep (se 1 (by rfl) ⟨372878, by rfl⟩ : syracuseStep 497171 = 745757) B745757
theorem B988739 : Blo 291829 988739 := bstep (se 1 (by rfl) ⟨741554, by rfl⟩ : syracuseStep 988739 = 1483109) B1483109
theorem B1054349 : Blo 291829 1054349 := bstep (se 3 (by rfl) ⟨197690, by rfl⟩ : syracuseStep 1054349 = 395381) B395381
theorem B497299 : Blo 291829 497299 := bstep (se 1 (by rfl) ⟨372974, by rfl⟩ : syracuseStep 497299 = 745949) B745949
theorem B1480355 : Blo 291829 1480355 := bstep (se 1 (by rfl) ⟨1110266, by rfl⟩ : syracuseStep 1480355 = 2220533) B2220533
theorem B399025 : Blo 291829 399025 := bstep (se 2 (by rfl) ⟨149634, by rfl⟩ : syracuseStep 399025 = 299269) B299269
theorem B1251085 : Blo 291829 1251085 := bstep (se 3 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 1251085 = 469157) B469157
theorem B661265 : Blo 291829 661265 := bstep (se 2 (by rfl) ⟨247974, by rfl⟩ : syracuseStep 661265 = 495949) B495949
theorem B497441 : Blo 291829 497441 := bstep (se 2 (by rfl) ⟨186540, by rfl⟩ : syracuseStep 497441 = 373081) B373081
theorem B661283 : Blo 291829 661283 := bstep (se 1 (by rfl) ⟨495962, by rfl⟩ : syracuseStep 661283 = 991925) B991925
theorem B989009 : Blo 291829 989009 := bstep (se 2 (by rfl) ⟨370878, by rfl⟩ : syracuseStep 989009 = 741757) B741757
theorem B497569 : Blo 291829 497569 := bstep (se 2 (by rfl) ⟨186588, by rfl⟩ : syracuseStep 497569 = 373177) B373177
theorem B497603 : Blo 291829 497603 := bstep (se 1 (by rfl) ⟨373202, by rfl⟩ : syracuseStep 497603 = 746405) B746405
theorem B11999173 : Blo 291829 11999173 := bstep (se 4 (by rfl) ⟨1124922, by rfl⟩ : syracuseStep 11999173 = 2249845) B2249845
theorem B661553 : Blo 291829 661553 := bstep (se 2 (by rfl) ⟨248082, by rfl⟩ : syracuseStep 661553 = 496165) B496165
theorem B661571 : Blo 291829 661571 := bstep (se 1 (by rfl) ⟨496178, by rfl⟩ : syracuseStep 661571 = 992357) B992357
theorem B497731 : Blo 291829 497731 := bstep (se 1 (by rfl) ⟨373298, by rfl⟩ : syracuseStep 497731 = 746597) B746597
theorem B497873 : Blo 291829 497873 := bstep (se 2 (by rfl) ⟨186702, by rfl⟩ : syracuseStep 497873 = 373405) B373405
theorem B399587 : Blo 291829 399587 := bstep (se 1 (by rfl) ⟨299690, by rfl⟩ : syracuseStep 399587 = 599381) B599381
theorem B399619 : Blo 291829 399619 := bstep (se 1 (by rfl) ⟨299714, by rfl⟩ : syracuseStep 399619 = 599429) B599429
theorem B661841 : Blo 291829 661841 := bstep (se 2 (by rfl) ⟨248190, by rfl⟩ : syracuseStep 661841 = 496381) B496381
theorem B498001 : Blo 291829 498001 := bstep (se 2 (by rfl) ⟨186750, by rfl⟩ : syracuseStep 498001 = 373501) B373501
theorem B1251683 : Blo 291829 1251683 := bstep (se 1 (by rfl) ⟨938762, by rfl⟩ : syracuseStep 1251683 = 1877525) B1877525
theorem B661859 : Blo 291829 661859 := bstep (se 1 (by rfl) ⟨496394, by rfl⟩ : syracuseStep 661859 = 992789) B992789
theorem B989549 : Blo 291829 989549 := bstep (se 3 (by rfl) ⟨185540, by rfl⟩ : syracuseStep 989549 = 371081) B371081
theorem B1120625 : Blo 291829 1120625 := bstep (se 2 (by rfl) ⟨420234, by rfl⟩ : syracuseStep 1120625 = 840469) B840469
theorem B530801 : Blo 291829 530801 := bstep (se 2 (by rfl) ⟨199050, by rfl⟩ : syracuseStep 530801 = 398101) B398101
theorem B498035 : Blo 291829 498035 := bstep (se 1 (by rfl) ⟨373526, by rfl⟩ : syracuseStep 498035 = 747053) B747053
theorem B399745 : Blo 291829 399745 := bstep (se 2 (by rfl) ⟨149904, by rfl⟩ : syracuseStep 399745 = 299809) B299809
theorem B989603 : Blo 291829 989603 := bstep (se 1 (by rfl) ⟨742202, by rfl⟩ : syracuseStep 989603 = 1484405) B1484405
theorem B1481165 : Blo 291829 1481165 := bstep (se 3 (by rfl) ⟨277718, by rfl⟩ : syracuseStep 1481165 = 555437) B555437
theorem B498163 : Blo 291829 498163 := bstep (se 1 (by rfl) ⟨373622, by rfl⟩ : syracuseStep 498163 = 747245) B747245
theorem B1874501 : Blo 291829 1874501 := bstep (se 4 (by rfl) ⟨175734, by rfl⟩ : syracuseStep 1874501 = 351469) B351469
theorem B662129 : Blo 291829 662129 := bstep (se 2 (by rfl) ⟨248298, by rfl⟩ : syracuseStep 662129 = 496597) B496597
theorem B498305 : Blo 291829 498305 := bstep (se 2 (by rfl) ⟨186864, by rfl⟩ : syracuseStep 498305 = 373729) B373729
theorem B662147 : Blo 291829 662147 := bstep (se 1 (by rfl) ⟨496610, by rfl⟩ : syracuseStep 662147 = 993221) B993221
theorem B989873 : Blo 291829 989873 := bstep (se 2 (by rfl) ⟨371202, by rfl⟩ : syracuseStep 989873 = 742405) B742405
theorem B498433 : Blo 291829 498433 := bstep (se 2 (by rfl) ⟨186912, by rfl⟩ : syracuseStep 498433 = 373825) B373825
theorem B629507 : Blo 291829 629507 := bstep (se 1 (by rfl) ⟨472130, by rfl⟩ : syracuseStep 629507 = 944261) B944261
theorem B498467 : Blo 291829 498467 := bstep (se 1 (by rfl) ⟨373850, by rfl⟩ : syracuseStep 498467 = 747701) B747701
theorem B662417 : Blo 291829 662417 := bstep (se 2 (by rfl) ⟨248406, by rfl⟩ : syracuseStep 662417 = 496813) B496813
theorem B662435 : Blo 291829 662435 := bstep (se 1 (by rfl) ⟨496826, by rfl⟩ : syracuseStep 662435 = 993653) B993653
theorem B596899 : Blo 291829 596899 := bstep (se 1 (by rfl) ⟨447674, by rfl⟩ : syracuseStep 596899 = 895349) B895349
theorem B498595 : Blo 291829 498595 := bstep (se 1 (by rfl) ⟨373946, by rfl⟩ : syracuseStep 498595 = 747893) B747893
theorem B498737 : Blo 291829 498737 := bstep (se 2 (by rfl) ⟨187026, by rfl⟩ : syracuseStep 498737 = 374053) B374053
theorem B728131 : Blo 291829 728131 := bstep (se 1 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 728131 = 1092197) B1092197
theorem B662705 : Blo 291829 662705 := bstep (se 2 (by rfl) ⟨248514, by rfl⟩ : syracuseStep 662705 = 497029) B497029
theorem B498865 : Blo 291829 498865 := bstep (se 2 (by rfl) ⟨187074, by rfl⟩ : syracuseStep 498865 = 374149) B374149
theorem B662723 : Blo 291829 662723 := bstep (se 1 (by rfl) ⟨497042, by rfl⟩ : syracuseStep 662723 = 994085) B994085
theorem B990413 : Blo 291829 990413 := bstep (se 3 (by rfl) ⟨185702, by rfl⟩ : syracuseStep 990413 = 371405) B371405
theorem B498899 : Blo 291829 498899 := bstep (se 1 (by rfl) ⟨374174, by rfl⟩ : syracuseStep 498899 = 748349) B748349
theorem B990467 : Blo 291829 990467 := bstep (se 1 (by rfl) ⟨742850, by rfl⟩ : syracuseStep 990467 = 1485701) B1485701
theorem B499027 : Blo 291829 499027 := bstep (se 1 (by rfl) ⟨374270, by rfl⟩ : syracuseStep 499027 = 748541) B748541
theorem B662993 : Blo 291829 662993 := bstep (se 2 (by rfl) ⟨248622, by rfl⟩ : syracuseStep 662993 = 497245) B497245
theorem B499169 : Blo 291829 499169 := bstep (se 2 (by rfl) ⟨187188, by rfl⟩ : syracuseStep 499169 = 374377) B374377
theorem B663011 : Blo 291829 663011 := bstep (se 1 (by rfl) ⟨497258, by rfl⟩ : syracuseStep 663011 = 994517) B994517
theorem B2530801 : Blo 291829 2530801 := bstep (se 2 (by rfl) ⟨949050, by rfl⟩ : syracuseStep 2530801 = 1898101) B1898101
theorem B2825741 : Blo 291829 2825741 := bstep (se 3 (by rfl) ⟨529826, by rfl⟩ : syracuseStep 2825741 = 1059653) B1059653
theorem B990737 : Blo 291829 990737 := bstep (se 2 (by rfl) ⟨371526, by rfl⟩ : syracuseStep 990737 = 743053) B743053
theorem B1449677 : Blo 291829 1449677 := bstep (se 3 (by rfl) ⟨271814, by rfl⟩ : syracuseStep 1449677 = 543629) B543629
theorem B663281 : Blo 291829 663281 := bstep (se 2 (by rfl) ⟨248730, by rfl⟩ : syracuseStep 663281 = 497461) B497461
theorem B663299 : Blo 291829 663299 := bstep (se 1 (by rfl) ⟨497474, by rfl⟩ : syracuseStep 663299 = 994949) B994949
theorem B1122083 : Blo 291829 1122083 := bstep (se 1 (by rfl) ⟨841562, by rfl⟩ : syracuseStep 1122083 = 1683125) B1683125
theorem B892721 : Blo 291829 892721 := bstep (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) B669541
theorem B597937 : Blo 291829 597937 := bstep (se 2 (by rfl) ⟨224226, by rfl⟩ : syracuseStep 597937 = 448453) B448453
theorem B630737 : Blo 291829 630737 := bstep (se 2 (by rfl) ⟨236526, by rfl⟩ : syracuseStep 630737 = 473053) B473053
theorem B532451 : Blo 291829 532451 := bstep (se 1 (by rfl) ⟨399338, by rfl⟩ : syracuseStep 532451 = 798677) B798677
theorem B663569 : Blo 291829 663569 := bstep (se 2 (by rfl) ⟨248838, by rfl⟩ : syracuseStep 663569 = 497677) B497677
theorem B663587 : Blo 291829 663587 := bstep (se 1 (by rfl) ⟨497690, by rfl⟩ : syracuseStep 663587 = 995381) B995381
theorem B991277 : Blo 291829 991277 := bstep (se 3 (by rfl) ⟨185864, by rfl⟩ : syracuseStep 991277 = 371729) B371729
theorem B499763 : Blo 291829 499763 := bstep (se 1 (by rfl) ⟨374822, by rfl⟩ : syracuseStep 499763 = 749645) B749645
theorem B991331 : Blo 291829 991331 := bstep (se 1 (by rfl) ⟨743498, by rfl⟩ : syracuseStep 991331 = 1486997) B1486997
theorem B663857 : Blo 291829 663857 := bstep (se 2 (by rfl) ⟨248946, by rfl⟩ : syracuseStep 663857 = 497893) B497893
theorem B663875 : Blo 291829 663875 := bstep (se 1 (by rfl) ⟨497906, by rfl⟩ : syracuseStep 663875 = 995813) B995813
theorem B991601 : Blo 291829 991601 := bstep (se 2 (by rfl) ⟨371850, by rfl⟩ : syracuseStep 991601 = 743701) B743701
theorem B795043 : Blo 291829 795043 := bstep (se 1 (by rfl) ⟨596282, by rfl⟩ : syracuseStep 795043 = 1192565) B1192565
theorem B3875381 : Blo 291829 3875381 := bstep (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) B363317
theorem B664145 : Blo 291829 664145 := bstep (se 2 (by rfl) ⟨249054, by rfl⟩ : syracuseStep 664145 = 498109) B498109
theorem B664163 : Blo 291829 664163 := bstep (se 1 (by rfl) ⟨498122, by rfl⟩ : syracuseStep 664163 = 996245) B996245
theorem B467651 : Blo 291829 467651 := bstep (se 1 (by rfl) ⟨350738, by rfl⟩ : syracuseStep 467651 = 701477) B701477
theorem B1123085 : Blo 291829 1123085 := bstep (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) B421157
theorem B566033 : Blo 291829 566033 := bstep (se 2 (by rfl) ⟨212262, by rfl⟩ : syracuseStep 566033 = 424525) B424525
theorem B500513 : Blo 291829 500513 := bstep (se 2 (by rfl) ⟨187692, by rfl⟩ : syracuseStep 500513 = 375385) B375385
theorem B467779 : Blo 291829 467779 := bstep (se 1 (by rfl) ⟨350834, by rfl⟩ : syracuseStep 467779 = 701669) B701669
theorem B631633 : Blo 291829 631633 := bstep (se 2 (by rfl) ⟨236862, by rfl⟩ : syracuseStep 631633 = 473725) B473725
theorem B631651 : Blo 291829 631651 := bstep (se 1 (by rfl) ⟨473738, by rfl⟩ : syracuseStep 631651 = 947477) B947477
theorem B664433 : Blo 291829 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B664451 : Blo 291829 664451 := bstep (se 1 (by rfl) ⟨498338, by rfl⟩ : syracuseStep 664451 = 996677) B996677
theorem B992141 : Blo 291829 992141 := bstep (se 3 (by rfl) ⟨186026, by rfl⟩ : syracuseStep 992141 = 372053) B372053
theorem B893891 : Blo 291829 893891 := bstep (se 1 (by rfl) ⟨670418, by rfl⟩ : syracuseStep 893891 = 1340837) B1340837
theorem B992195 : Blo 291829 992195 := bstep (se 1 (by rfl) ⟨744146, by rfl⟩ : syracuseStep 992195 = 1488293) B1488293
theorem B1582021 : Blo 291829 1582021 := bstep (se 4 (by rfl) ⟨148314, by rfl⟩ : syracuseStep 1582021 = 296629) B296629
theorem B664721 : Blo 291829 664721 := bstep (se 2 (by rfl) ⟨249270, by rfl⟩ : syracuseStep 664721 = 498541) B498541
theorem B664739 : Blo 291829 664739 := bstep (se 1 (by rfl) ⟨498554, by rfl⟩ : syracuseStep 664739 = 997109) B997109
theorem B992465 : Blo 291829 992465 := bstep (se 2 (by rfl) ⟨372174, by rfl⟩ : syracuseStep 992465 = 744349) B744349
theorem B1484081 : Blo 291829 1484081 := bstep (se 2 (by rfl) ⟨556530, by rfl⟩ : syracuseStep 1484081 = 1113061) B1113061
theorem B1680709 : Blo 291829 1680709 := bstep (se 4 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 1680709 = 315133) B315133
theorem B370003 : Blo 291829 370003 := bstep (se 1 (by rfl) ⟨277502, by rfl⟩ : syracuseStep 370003 = 555005) B555005
theorem B468337 : Blo 291829 468337 := bstep (se 2 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 468337 = 351253) B351253
theorem B665009 : Blo 291829 665009 := bstep (se 2 (by rfl) ⟨249378, by rfl⟩ : syracuseStep 665009 = 498757) B498757
theorem B370099 : Blo 291829 370099 := bstep (se 1 (by rfl) ⟨277574, by rfl⟩ : syracuseStep 370099 = 555149) B555149
theorem B665027 : Blo 291829 665027 := bstep (se 1 (by rfl) ⟨498770, by rfl⟩ : syracuseStep 665027 = 997541) B997541
theorem B2827973 : Blo 291829 2827973 := bstep (se 4 (by rfl) ⟨265122, by rfl⟩ : syracuseStep 2827973 = 530245) B530245
theorem B665297 : Blo 291829 665297 := bstep (se 2 (by rfl) ⟨249486, by rfl⟩ : syracuseStep 665297 = 498973) B498973
theorem B665315 : Blo 291829 665315 := bstep (se 1 (by rfl) ⟨498986, by rfl⟩ : syracuseStep 665315 = 997973) B997973
theorem B993005 : Blo 291829 993005 := bstep (se 3 (by rfl) ⟨186188, by rfl⟩ : syracuseStep 993005 = 372377) B372377
theorem B993059 : Blo 291829 993059 := bstep (se 1 (by rfl) ⟨744794, by rfl⟩ : syracuseStep 993059 = 1489589) B1489589
theorem B1517453 : Blo 291829 1517453 := bstep (se 3 (by rfl) ⟨284522, by rfl⟩ : syracuseStep 1517453 = 569045) B569045
theorem B370595 : Blo 291829 370595 := bstep (se 1 (by rfl) ⟨277946, by rfl⟩ : syracuseStep 370595 = 555893) B555893
theorem B665585 : Blo 291829 665585 := bstep (se 2 (by rfl) ⟨249594, by rfl⟩ : syracuseStep 665585 = 499189) B499189
theorem B665603 : Blo 291829 665603 := bstep (se 1 (by rfl) ⟨499202, by rfl⟩ : syracuseStep 665603 = 998405) B998405
theorem B469009 : Blo 291829 469009 := bstep (se 2 (by rfl) ⟨175878, by rfl⟩ : syracuseStep 469009 = 351757) B351757
theorem B1255459 : Blo 291829 1255459 := bstep (se 1 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 1255459 = 1883189) B1883189
theorem B1878065 : Blo 291829 1878065 := bstep (se 2 (by rfl) ⟨704274, by rfl⟩ : syracuseStep 1878065 = 1408549) B1408549
theorem B993329 : Blo 291829 993329 := bstep (se 2 (by rfl) ⟨372498, by rfl⟩ : syracuseStep 993329 = 744997) B744997
theorem B796817 : Blo 291829 796817 := bstep (se 2 (by rfl) ⟨298806, by rfl⟩ : syracuseStep 796817 = 597613) B597613
theorem B2009285 : Blo 291829 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B502019 : Blo 291829 502019 := bstep (se 1 (by rfl) ⟨376514, by rfl⟩ : syracuseStep 502019 = 753029) B753029
theorem B993869 : Blo 291829 993869 := bstep (se 3 (by rfl) ⟨186350, by rfl⟩ : syracuseStep 993869 = 372701) B372701
theorem B371299 : Blo 291829 371299 := bstep (se 1 (by rfl) ⟨278474, by rfl⟩ : syracuseStep 371299 = 556949) B556949
theorem B797293 : Blo 291829 797293 := bstep (se 3 (by rfl) ⟨149492, by rfl⟩ : syracuseStep 797293 = 298985) B298985
theorem B993923 : Blo 291829 993923 := bstep (se 1 (by rfl) ⟨745442, by rfl⟩ : syracuseStep 993923 = 1490885) B1490885
theorem B371395 : Blo 291829 371395 := bstep (se 1 (by rfl) ⟨278546, by rfl⟩ : syracuseStep 371395 = 557093) B557093
theorem B1485539 : Blo 291829 1485539 := bstep (se 1 (by rfl) ⟨1114154, by rfl⟩ : syracuseStep 1485539 = 2228309) B2228309
theorem B502595 : Blo 291829 502595 := bstep (se 1 (by rfl) ⟨376946, by rfl⟩ : syracuseStep 502595 = 753893) B753893
theorem B994193 : Blo 291829 994193 := bstep (se 2 (by rfl) ⟨372822, by rfl⟩ : syracuseStep 994193 = 745645) B745645
theorem B797617 : Blo 291829 797617 := bstep (se 2 (by rfl) ⟨299106, by rfl⟩ : syracuseStep 797617 = 598213) B598213
theorem B470099 : Blo 291829 470099 := bstep (se 1 (by rfl) ⟨352574, by rfl⟩ : syracuseStep 470099 = 705149) B705149
theorem B371891 : Blo 291829 371891 := bstep (se 1 (by rfl) ⟨278918, by rfl⟩ : syracuseStep 371891 = 557837) B557837
theorem B1682693 : Blo 291829 1682693 := bstep (se 4 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 1682693 = 315505) B315505
theorem B6040973 : Blo 291829 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B994733 : Blo 291829 994733 := bstep (se 3 (by rfl) ⟨186512, by rfl⟩ : syracuseStep 994733 = 373025) B373025
theorem B1879523 : Blo 291829 1879523 := bstep (se 1 (by rfl) ⟨1409642, by rfl⟩ : syracuseStep 1879523 = 2819285) B2819285
theorem B994787 : Blo 291829 994787 := bstep (se 1 (by rfl) ⟨746090, by rfl⟩ : syracuseStep 994787 = 1492181) B1492181
theorem B437747 : Blo 291829 437747 := bstep (se 1 (by rfl) ⟨328310, by rfl⟩ : syracuseStep 437747 = 656621) B656621
theorem B1486349 : Blo 291829 1486349 := bstep (se 3 (by rfl) ⟨278690, by rfl⟩ : syracuseStep 1486349 = 557381) B557381
theorem B437777 : Blo 291829 437777 := bstep (se 2 (by rfl) ⟨164166, by rfl⟩ : syracuseStep 437777 = 328333) B328333
theorem B437795 : Blo 291829 437795 := bstep (se 1 (by rfl) ⟨328346, by rfl⟩ : syracuseStep 437795 = 656693) B656693
theorem B437825 : Blo 291829 437825 := bstep (se 2 (by rfl) ⟨164184, by rfl⟩ : syracuseStep 437825 = 328369) B328369
theorem B437843 : Blo 291829 437843 := bstep (se 1 (by rfl) ⟨328382, by rfl⟩ : syracuseStep 437843 = 656765) B656765
theorem B437873 : Blo 291829 437873 := bstep (se 2 (by rfl) ⟨164202, by rfl⟩ : syracuseStep 437873 = 328405) B328405
theorem B437891 : Blo 291829 437891 := bstep (se 1 (by rfl) ⟨328418, by rfl⟩ : syracuseStep 437891 = 656837) B656837
theorem B437921 : Blo 291829 437921 := bstep (se 2 (by rfl) ⟨164220, by rfl⟩ : syracuseStep 437921 = 328441) B328441
theorem B437939 : Blo 291829 437939 := bstep (se 1 (by rfl) ⟨328454, by rfl⟩ : syracuseStep 437939 = 656909) B656909
theorem B5451461 : Blo 291829 5451461 := bstep (se 4 (by rfl) ⟨511074, by rfl⟩ : syracuseStep 5451461 = 1022149) B1022149
theorem B437969 : Blo 291829 437969 := bstep (se 2 (by rfl) ⟨164238, by rfl⟩ : syracuseStep 437969 = 328477) B328477
theorem B437987 : Blo 291829 437987 := bstep (se 1 (by rfl) ⟨328490, by rfl⟩ : syracuseStep 437987 = 656981) B656981
theorem B995057 : Blo 291829 995057 := bstep (se 2 (by rfl) ⟨373146, by rfl⟩ : syracuseStep 995057 = 746293) B746293
theorem B438017 : Blo 291829 438017 := bstep (se 2 (by rfl) ⟨164256, by rfl⟩ : syracuseStep 438017 = 328513) B328513
theorem B438035 : Blo 291829 438035 := bstep (se 1 (by rfl) ⟨328526, by rfl⟩ : syracuseStep 438035 = 657053) B657053
theorem B438065 : Blo 291829 438065 := bstep (se 2 (by rfl) ⟨164274, by rfl⟩ : syracuseStep 438065 = 328549) B328549
theorem B438083 : Blo 291829 438083 := bstep (se 1 (by rfl) ⟨328562, by rfl⟩ : syracuseStep 438083 = 657125) B657125
theorem B438113 : Blo 291829 438113 := bstep (se 2 (by rfl) ⟨164292, by rfl⟩ : syracuseStep 438113 = 328585) B328585
theorem B438131 : Blo 291829 438131 := bstep (se 1 (by rfl) ⟨328598, by rfl⟩ : syracuseStep 438131 = 657197) B657197
theorem B372595 : Blo 291829 372595 := bstep (se 1 (by rfl) ⟨279446, by rfl⟩ : syracuseStep 372595 = 558893) B558893
theorem B438161 : Blo 291829 438161 := bstep (se 2 (by rfl) ⟨164310, by rfl⟩ : syracuseStep 438161 = 328621) B328621
theorem B438179 : Blo 291829 438179 := bstep (se 1 (by rfl) ⟨328634, by rfl⟩ : syracuseStep 438179 = 657269) B657269
theorem B3583925 : Blo 291829 3583925 := bstep (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) B335993
theorem B438209 : Blo 291829 438209 := bstep (se 2 (by rfl) ⟨164328, by rfl⟩ : syracuseStep 438209 = 328657) B328657
theorem B438227 : Blo 291829 438227 := bstep (se 1 (by rfl) ⟨328670, by rfl⟩ : syracuseStep 438227 = 657341) B657341
theorem B372691 : Blo 291829 372691 := bstep (se 1 (by rfl) ⟨279518, by rfl⟩ : syracuseStep 372691 = 559037) B559037
theorem B438257 : Blo 291829 438257 := bstep (se 2 (by rfl) ⟨164346, by rfl⟩ : syracuseStep 438257 = 328693) B328693
theorem B1257457 : Blo 291829 1257457 := bstep (se 2 (by rfl) ⟨471546, by rfl⟩ : syracuseStep 1257457 = 943093) B943093
theorem B438275 : Blo 291829 438275 := bstep (se 1 (by rfl) ⟨328706, by rfl⟩ : syracuseStep 438275 = 657413) B657413
theorem B831505 : Blo 291829 831505 := bstep (se 2 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 831505 = 623629) B623629
theorem B438305 : Blo 291829 438305 := bstep (se 2 (by rfl) ⟨164364, by rfl⟩ : syracuseStep 438305 = 328729) B328729
theorem B1290289 : Blo 291829 1290289 := bstep (se 2 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 1290289 = 967717) B967717
theorem B438323 : Blo 291829 438323 := bstep (se 1 (by rfl) ⟨328742, by rfl⟩ : syracuseStep 438323 = 657485) B657485
theorem B798797 : Blo 291829 798797 := bstep (se 3 (by rfl) ⟨149774, by rfl⟩ : syracuseStep 798797 = 299549) B299549
theorem B438353 : Blo 291829 438353 := bstep (se 2 (by rfl) ⟨164382, by rfl⟩ : syracuseStep 438353 = 328765) B328765
theorem B438371 : Blo 291829 438371 := bstep (se 1 (by rfl) ⟨328778, by rfl⟩ : syracuseStep 438371 = 657557) B657557
theorem B438401 : Blo 291829 438401 := bstep (se 2 (by rfl) ⟨164400, by rfl⟩ : syracuseStep 438401 = 328801) B328801
theorem B438419 : Blo 291829 438419 := bstep (se 1 (by rfl) ⟨328814, by rfl⟩ : syracuseStep 438419 = 657629) B657629
theorem B438449 : Blo 291829 438449 := bstep (se 2 (by rfl) ⟨164418, by rfl⟩ : syracuseStep 438449 = 328837) B328837
theorem B438467 : Blo 291829 438467 := bstep (se 1 (by rfl) ⟨328850, by rfl⟩ : syracuseStep 438467 = 657701) B657701
theorem B438497 : Blo 291829 438497 := bstep (se 2 (by rfl) ⟨164436, by rfl⟩ : syracuseStep 438497 = 328873) B328873
theorem B438515 : Blo 291829 438515 := bstep (se 1 (by rfl) ⟨328886, by rfl⟩ : syracuseStep 438515 = 657773) B657773
theorem B798979 : Blo 291829 798979 := bstep (se 1 (by rfl) ⟨599234, by rfl⟩ : syracuseStep 798979 = 1198469) B1198469
theorem B995597 : Blo 291829 995597 := bstep (se 3 (by rfl) ⟨186674, by rfl⟩ : syracuseStep 995597 = 373349) B373349
theorem B438545 : Blo 291829 438545 := bstep (se 2 (by rfl) ⟨164454, by rfl⟩ : syracuseStep 438545 = 328909) B328909
theorem B831779 : Blo 291829 831779 := bstep (se 1 (by rfl) ⟨623834, by rfl⟩ : syracuseStep 831779 = 1247669) B1247669
theorem B438563 : Blo 291829 438563 := bstep (se 1 (by rfl) ⟨328922, by rfl⟩ : syracuseStep 438563 = 657845) B657845
theorem B438593 : Blo 291829 438593 := bstep (se 2 (by rfl) ⟨164472, by rfl⟩ : syracuseStep 438593 = 328945) B328945
theorem B995651 : Blo 291829 995651 := bstep (se 1 (by rfl) ⟨746738, by rfl⟩ : syracuseStep 995651 = 1493477) B1493477
theorem B438611 : Blo 291829 438611 := bstep (se 1 (by rfl) ⟨328958, by rfl⟩ : syracuseStep 438611 = 657917) B657917
theorem B438641 : Blo 291829 438641 := bstep (se 2 (by rfl) ⟨164490, by rfl⟩ : syracuseStep 438641 = 328981) B328981
theorem B438659 : Blo 291829 438659 := bstep (se 1 (by rfl) ⟨328994, by rfl⟩ : syracuseStep 438659 = 657989) B657989
theorem B438689 : Blo 291829 438689 := bstep (se 2 (by rfl) ⟨164508, by rfl⟩ : syracuseStep 438689 = 329017) B329017
theorem B438707 : Blo 291829 438707 := bstep (se 1 (by rfl) ⟨329030, by rfl⟩ : syracuseStep 438707 = 658061) B658061
theorem B373187 : Blo 291829 373187 := bstep (se 1 (by rfl) ⟨279890, by rfl⟩ : syracuseStep 373187 = 559781) B559781
theorem B438737 : Blo 291829 438737 := bstep (se 2 (by rfl) ⟨164526, by rfl⟩ : syracuseStep 438737 = 329053) B329053
theorem B471521 : Blo 291829 471521 := bstep (se 2 (by rfl) ⟨176820, by rfl⟩ : syracuseStep 471521 = 353641) B353641
theorem B831971 : Blo 291829 831971 := bstep (se 1 (by rfl) ⟨623978, by rfl⟩ : syracuseStep 831971 = 1247957) B1247957
theorem B438755 : Blo 291829 438755 := bstep (se 1 (by rfl) ⟨329066, by rfl⟩ : syracuseStep 438755 = 658133) B658133
theorem B438785 : Blo 291829 438785 := bstep (se 2 (by rfl) ⟨164544, by rfl⟩ : syracuseStep 438785 = 329089) B329089
theorem B438803 : Blo 291829 438803 := bstep (se 1 (by rfl) ⟨329102, by rfl⟩ : syracuseStep 438803 = 658205) B658205
theorem B438833 : Blo 291829 438833 := bstep (se 2 (by rfl) ⟨164562, by rfl⟩ : syracuseStep 438833 = 329125) B329125
theorem B438851 : Blo 291829 438851 := bstep (se 1 (by rfl) ⟨329138, by rfl⟩ : syracuseStep 438851 = 658277) B658277
theorem B995921 : Blo 291829 995921 := bstep (se 2 (by rfl) ⟨373470, by rfl⟩ : syracuseStep 995921 = 746941) B746941
theorem B438881 : Blo 291829 438881 := bstep (se 2 (by rfl) ⟨164580, by rfl⟩ : syracuseStep 438881 = 329161) B329161
theorem B438899 : Blo 291829 438899 := bstep (se 1 (by rfl) ⟨329174, by rfl⟩ : syracuseStep 438899 = 658349) B658349
theorem B438929 : Blo 291829 438929 := bstep (se 2 (by rfl) ⟨164598, by rfl⟩ : syracuseStep 438929 = 329197) B329197
theorem B438947 : Blo 291829 438947 := bstep (se 1 (by rfl) ⟨329210, by rfl⟩ : syracuseStep 438947 = 658421) B658421
theorem B438977 : Blo 291829 438977 := bstep (se 2 (by rfl) ⟨164616, by rfl⟩ : syracuseStep 438977 = 329233) B329233
theorem B438995 : Blo 291829 438995 := bstep (se 1 (by rfl) ⟨329246, by rfl⟩ : syracuseStep 438995 = 658493) B658493
theorem B439025 : Blo 291829 439025 := bstep (se 2 (by rfl) ⟨164634, by rfl⟩ : syracuseStep 439025 = 329269) B329269
theorem B439043 : Blo 291829 439043 := bstep (se 1 (by rfl) ⟨329282, by rfl⟩ : syracuseStep 439043 = 658565) B658565
theorem B439073 : Blo 291829 439073 := bstep (se 2 (by rfl) ⟨164652, by rfl⟩ : syracuseStep 439073 = 329305) B329305
theorem B439091 : Blo 291829 439091 := bstep (se 1 (by rfl) ⟨329318, by rfl⟩ : syracuseStep 439091 = 658637) B658637
theorem B668483 : Blo 291829 668483 := bstep (se 1 (by rfl) ⟨501362, by rfl⟩ : syracuseStep 668483 = 1002725) B1002725
theorem B439121 : Blo 291829 439121 := bstep (se 2 (by rfl) ⟨164670, by rfl⟩ : syracuseStep 439121 = 329341) B329341
theorem B439139 : Blo 291829 439139 := bstep (se 1 (by rfl) ⟨329354, by rfl⟩ : syracuseStep 439139 = 658709) B658709
theorem B897905 : Blo 291829 897905 := bstep (se 2 (by rfl) ⟨336714, by rfl⟩ : syracuseStep 897905 = 673429) B673429
theorem B439169 : Blo 291829 439169 := bstep (se 2 (by rfl) ⟨164688, by rfl⟩ : syracuseStep 439169 = 329377) B329377
theorem B439187 : Blo 291829 439187 := bstep (se 1 (by rfl) ⟨329390, by rfl⟩ : syracuseStep 439187 = 658781) B658781
theorem B439217 : Blo 291829 439217 := bstep (se 2 (by rfl) ⟨164706, by rfl⟩ : syracuseStep 439217 = 329413) B329413
theorem B439235 : Blo 291829 439235 := bstep (se 1 (by rfl) ⟨329426, by rfl⟩ : syracuseStep 439235 = 658853) B658853
theorem B439265 : Blo 291829 439265 := bstep (se 2 (by rfl) ⟨164724, by rfl⟩ : syracuseStep 439265 = 329449) B329449
theorem B439283 : Blo 291829 439283 := bstep (se 1 (by rfl) ⟨329462, by rfl⟩ : syracuseStep 439283 = 658925) B658925
theorem B439313 : Blo 291829 439313 := bstep (se 2 (by rfl) ⟨164742, by rfl⟩ : syracuseStep 439313 = 329485) B329485
theorem B439331 : Blo 291829 439331 := bstep (se 1 (by rfl) ⟨329498, by rfl⟩ : syracuseStep 439331 = 658997) B658997
theorem B439361 : Blo 291829 439361 := bstep (se 2 (by rfl) ⟨164760, by rfl⟩ : syracuseStep 439361 = 329521) B329521
theorem B439379 : Blo 291829 439379 := bstep (se 1 (by rfl) ⟨329534, by rfl⟩ : syracuseStep 439379 = 659069) B659069
theorem B996461 : Blo 291829 996461 := bstep (se 3 (by rfl) ⟨186836, by rfl⟩ : syracuseStep 996461 = 373673) B373673
theorem B439409 : Blo 291829 439409 := bstep (se 2 (by rfl) ⟨164778, by rfl⟩ : syracuseStep 439409 = 329557) B329557
theorem B439427 : Blo 291829 439427 := bstep (se 1 (by rfl) ⟨329570, by rfl⟩ : syracuseStep 439427 = 659141) B659141
theorem B373891 : Blo 291829 373891 := bstep (se 1 (by rfl) ⟨280418, by rfl⟩ : syracuseStep 373891 = 560837) B560837
theorem B439457 : Blo 291829 439457 := bstep (se 2 (by rfl) ⟨164796, by rfl⟩ : syracuseStep 439457 = 329593) B329593
theorem B996515 : Blo 291829 996515 := bstep (se 1 (by rfl) ⟨747386, by rfl⟩ : syracuseStep 996515 = 1494773) B1494773
theorem B1881265 : Blo 291829 1881265 := bstep (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) B1410949
theorem B439475 : Blo 291829 439475 := bstep (se 1 (by rfl) ⟨329606, by rfl⟩ : syracuseStep 439475 = 659213) B659213
theorem B439505 : Blo 291829 439505 := bstep (se 2 (by rfl) ⟨164814, by rfl⟩ : syracuseStep 439505 = 329629) B329629
theorem B439523 : Blo 291829 439523 := bstep (se 1 (by rfl) ⟨329642, by rfl⟩ : syracuseStep 439523 = 659285) B659285
theorem B373987 : Blo 291829 373987 := bstep (se 1 (by rfl) ⟨280490, by rfl⟩ : syracuseStep 373987 = 560981) B560981
theorem B439553 : Blo 291829 439553 := bstep (se 2 (by rfl) ⟨164832, by rfl⟩ : syracuseStep 439553 = 329665) B329665
theorem B832781 : Blo 291829 832781 := bstep (se 3 (by rfl) ⟨156146, by rfl⟩ : syracuseStep 832781 = 312293) B312293
theorem B439571 : Blo 291829 439571 := bstep (se 1 (by rfl) ⟨329678, by rfl⟩ : syracuseStep 439571 = 659357) B659357
theorem B439601 : Blo 291829 439601 := bstep (se 2 (by rfl) ⟨164850, by rfl⟩ : syracuseStep 439601 = 329701) B329701
theorem B439619 : Blo 291829 439619 := bstep (se 1 (by rfl) ⟨329714, by rfl⟩ : syracuseStep 439619 = 659429) B659429
theorem B472387 : Blo 291829 472387 := bstep (se 1 (by rfl) ⟨354290, by rfl⟩ : syracuseStep 472387 = 708581) B708581
theorem B439649 : Blo 291829 439649 := bstep (se 2 (by rfl) ⟨164868, by rfl⟩ : syracuseStep 439649 = 329737) B329737
theorem B439667 : Blo 291829 439667 := bstep (se 1 (by rfl) ⟨329750, by rfl⟩ : syracuseStep 439667 = 659501) B659501
theorem B439697 : Blo 291829 439697 := bstep (se 2 (by rfl) ⟨164886, by rfl⟩ : syracuseStep 439697 = 329773) B329773
theorem B439715 : Blo 291829 439715 := bstep (se 1 (by rfl) ⟨329786, by rfl⟩ : syracuseStep 439715 = 659573) B659573
theorem B996785 : Blo 291829 996785 := bstep (se 2 (by rfl) ⟨373794, by rfl⟩ : syracuseStep 996785 = 747589) B747589
theorem B439745 : Blo 291829 439745 := bstep (se 2 (by rfl) ⟨164904, by rfl⟩ : syracuseStep 439745 = 329809) B329809
theorem B832963 : Blo 291829 832963 := bstep (se 1 (by rfl) ⟨624722, by rfl⟩ : syracuseStep 832963 = 1249445) B1249445
theorem B439763 : Blo 291829 439763 := bstep (se 1 (by rfl) ⟨329822, by rfl⟩ : syracuseStep 439763 = 659645) B659645
theorem B439793 : Blo 291829 439793 := bstep (se 2 (by rfl) ⟨164922, by rfl⟩ : syracuseStep 439793 = 329845) B329845
theorem B439811 : Blo 291829 439811 := bstep (se 1 (by rfl) ⟨329858, by rfl⟩ : syracuseStep 439811 = 659717) B659717
theorem B439841 : Blo 291829 439841 := bstep (se 2 (by rfl) ⟨164940, by rfl⟩ : syracuseStep 439841 = 329881) B329881
theorem B439859 : Blo 291829 439859 := bstep (se 1 (by rfl) ⟨329894, by rfl⟩ : syracuseStep 439859 = 659789) B659789
theorem B472643 : Blo 291829 472643 := bstep (se 1 (by rfl) ⟨354482, by rfl⟩ : syracuseStep 472643 = 708965) B708965
theorem B3782213 : Blo 291829 3782213 := bstep (se 4 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 3782213 = 709165) B709165
theorem B439889 : Blo 291829 439889 := bstep (se 2 (by rfl) ⟨164958, by rfl⟩ : syracuseStep 439889 = 329917) B329917
theorem B439907 : Blo 291829 439907 := bstep (se 1 (by rfl) ⟨329930, by rfl⟩ : syracuseStep 439907 = 659861) B659861
theorem B439937 : Blo 291829 439937 := bstep (se 2 (by rfl) ⟨164976, by rfl⟩ : syracuseStep 439937 = 329953) B329953
theorem B800401 : Blo 291829 800401 := bstep (se 2 (by rfl) ⟨300150, by rfl⟩ : syracuseStep 800401 = 600301) B600301
theorem B439955 : Blo 291829 439955 := bstep (se 1 (by rfl) ⟨329966, by rfl⟩ : syracuseStep 439955 = 659933) B659933
theorem B439985 : Blo 291829 439985 := bstep (se 2 (by rfl) ⟨164994, by rfl⟩ : syracuseStep 439985 = 329989) B329989
theorem B440003 : Blo 291829 440003 := bstep (se 1 (by rfl) ⟨330002, by rfl⟩ : syracuseStep 440003 = 660005) B660005
theorem B440033 : Blo 291829 440033 := bstep (se 2 (by rfl) ⟨165012, by rfl⟩ : syracuseStep 440033 = 330025) B330025
theorem B440051 : Blo 291829 440051 := bstep (se 1 (by rfl) ⟨330038, by rfl⟩ : syracuseStep 440051 = 660077) B660077
theorem B440081 : Blo 291829 440081 := bstep (se 2 (by rfl) ⟨165030, by rfl⟩ : syracuseStep 440081 = 330061) B330061
theorem B440099 : Blo 291829 440099 := bstep (se 1 (by rfl) ⟨330074, by rfl⟩ : syracuseStep 440099 = 660149) B660149
theorem B440129 : Blo 291829 440129 := bstep (se 2 (by rfl) ⟨165048, by rfl⟩ : syracuseStep 440129 = 330097) B330097
theorem B440147 : Blo 291829 440147 := bstep (se 1 (by rfl) ⟨330110, by rfl⟩ : syracuseStep 440147 = 660221) B660221
theorem B2242403 : Blo 291829 2242403 := bstep (se 1 (by rfl) ⟨1681802, by rfl⟩ : syracuseStep 2242403 = 3363605) B3363605
theorem B440177 : Blo 291829 440177 := bstep (se 2 (by rfl) ⟨165066, by rfl⟩ : syracuseStep 440177 = 330133) B330133
theorem B440195 : Blo 291829 440195 := bstep (se 1 (by rfl) ⟨330146, by rfl⟩ : syracuseStep 440195 = 660293) B660293
theorem B440225 : Blo 291829 440225 := bstep (se 2 (by rfl) ⟨165084, by rfl⟩ : syracuseStep 440225 = 330169) B330169
theorem B833453 : Blo 291829 833453 := bstep (se 3 (by rfl) ⟨156272, by rfl⟩ : syracuseStep 833453 = 312545) B312545
theorem B440243 : Blo 291829 440243 := bstep (se 1 (by rfl) ⟨330182, by rfl⟩ : syracuseStep 440243 = 660365) B660365
theorem B997325 : Blo 291829 997325 := bstep (se 3 (by rfl) ⟨186998, by rfl⟩ : syracuseStep 997325 = 373997) B373997
theorem B440273 : Blo 291829 440273 := bstep (se 2 (by rfl) ⟨165102, by rfl⟩ : syracuseStep 440273 = 330205) B330205
theorem B440291 : Blo 291829 440291 := bstep (se 1 (by rfl) ⟨330218, by rfl⟩ : syracuseStep 440291 = 660437) B660437
theorem B440321 : Blo 291829 440321 := bstep (se 2 (by rfl) ⟨165120, by rfl⟩ : syracuseStep 440321 = 330241) B330241
theorem B997379 : Blo 291829 997379 := bstep (se 1 (by rfl) ⟨748034, by rfl⟩ : syracuseStep 997379 = 1496069) B1496069
theorem B440339 : Blo 291829 440339 := bstep (se 1 (by rfl) ⟨330254, by rfl⟩ : syracuseStep 440339 = 660509) B660509
theorem B440369 : Blo 291829 440369 := bstep (se 2 (by rfl) ⟨165138, by rfl⟩ : syracuseStep 440369 = 330277) B330277
theorem B440387 : Blo 291829 440387 := bstep (se 1 (by rfl) ⟨330290, by rfl⟩ : syracuseStep 440387 = 660581) B660581
theorem B440417 : Blo 291829 440417 := bstep (se 2 (by rfl) ⟨165156, by rfl⟩ : syracuseStep 440417 = 330313) B330313
theorem B440435 : Blo 291829 440435 := bstep (se 1 (by rfl) ⟨330326, by rfl⟩ : syracuseStep 440435 = 660653) B660653
theorem B440465 : Blo 291829 440465 := bstep (se 2 (by rfl) ⟨165174, by rfl⟩ : syracuseStep 440465 = 330349) B330349
theorem B440483 : Blo 291829 440483 := bstep (se 1 (by rfl) ⟨330362, by rfl⟩ : syracuseStep 440483 = 660725) B660725
theorem B440513 : Blo 291829 440513 := bstep (se 2 (by rfl) ⟨165192, by rfl⟩ : syracuseStep 440513 = 330385) B330385
theorem B440531 : Blo 291829 440531 := bstep (se 1 (by rfl) ⟨330398, by rfl⟩ : syracuseStep 440531 = 660797) B660797
theorem B440561 : Blo 291829 440561 := bstep (se 2 (by rfl) ⟨165210, by rfl⟩ : syracuseStep 440561 = 330421) B330421
theorem B440579 : Blo 291829 440579 := bstep (se 1 (by rfl) ⟨330434, by rfl⟩ : syracuseStep 440579 = 660869) B660869
theorem B997649 : Blo 291829 997649 := bstep (se 2 (by rfl) ⟨374118, by rfl⟩ : syracuseStep 997649 = 748237) B748237
theorem B440609 : Blo 291829 440609 := bstep (se 2 (by rfl) ⟨165228, by rfl⟩ : syracuseStep 440609 = 330457) B330457
theorem B440627 : Blo 291829 440627 := bstep (se 1 (by rfl) ⟨330470, by rfl⟩ : syracuseStep 440627 = 660941) B660941
theorem B1194317 : Blo 291829 1194317 := bstep (se 3 (by rfl) ⟨223934, by rfl⟩ : syracuseStep 1194317 = 447869) B447869
theorem B440657 : Blo 291829 440657 := bstep (se 2 (by rfl) ⟨165246, by rfl⟩ : syracuseStep 440657 = 330493) B330493
theorem B440675 : Blo 291829 440675 := bstep (se 1 (by rfl) ⟨330506, by rfl⟩ : syracuseStep 440675 = 661013) B661013
theorem B1784177 : Blo 291829 1784177 := bstep (se 2 (by rfl) ⟨669066, by rfl⟩ : syracuseStep 1784177 = 1338133) B1338133
theorem B1489265 : Blo 291829 1489265 := bstep (se 2 (by rfl) ⟨558474, by rfl⟩ : syracuseStep 1489265 = 1116949) B1116949
theorem B440705 : Blo 291829 440705 := bstep (se 2 (by rfl) ⟨165264, by rfl⟩ : syracuseStep 440705 = 330529) B330529
theorem B440723 : Blo 291829 440723 := bstep (se 1 (by rfl) ⟨330542, by rfl⟩ : syracuseStep 440723 = 661085) B661085
theorem B440753 : Blo 291829 440753 := bstep (se 2 (by rfl) ⟨165282, by rfl⟩ : syracuseStep 440753 = 330565) B330565
theorem B440771 : Blo 291829 440771 := bstep (se 1 (by rfl) ⟨330578, by rfl⟩ : syracuseStep 440771 = 661157) B661157
theorem B440801 : Blo 291829 440801 := bstep (se 2 (by rfl) ⟨165300, by rfl⟩ : syracuseStep 440801 = 330601) B330601
theorem B440819 : Blo 291829 440819 := bstep (se 1 (by rfl) ⟨330614, by rfl⟩ : syracuseStep 440819 = 661229) B661229
theorem B440849 : Blo 291829 440849 := bstep (se 2 (by rfl) ⟨165318, by rfl⟩ : syracuseStep 440849 = 330637) B330637
theorem B473617 : Blo 291829 473617 := bstep (se 2 (by rfl) ⟨177606, by rfl⟩ : syracuseStep 473617 = 355213) B355213
theorem B440867 : Blo 291829 440867 := bstep (se 1 (by rfl) ⟨330650, by rfl⟩ : syracuseStep 440867 = 661301) B661301
theorem B1063459 : Blo 291829 1063459 := bstep (se 1 (by rfl) ⟨797594, by rfl⟩ : syracuseStep 1063459 = 1595189) B1595189
theorem B440897 : Blo 291829 440897 := bstep (se 2 (by rfl) ⟨165336, by rfl⟩ : syracuseStep 440897 = 330673) B330673
theorem B440915 : Blo 291829 440915 := bstep (se 1 (by rfl) ⟨330686, by rfl⟩ : syracuseStep 440915 = 661373) B661373
theorem B440945 : Blo 291829 440945 := bstep (se 2 (by rfl) ⟨165354, by rfl⟩ : syracuseStep 440945 = 330709) B330709
theorem B440963 : Blo 291829 440963 := bstep (se 1 (by rfl) ⟨330722, by rfl⟩ : syracuseStep 440963 = 661445) B661445
theorem B637571 : Blo 291829 637571 := bstep (se 1 (by rfl) ⟨478178, by rfl⟩ : syracuseStep 637571 = 956357) B956357
theorem B3029645 : Blo 291829 3029645 := bstep (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) B1136117
theorem B440993 : Blo 291829 440993 := bstep (se 2 (by rfl) ⟨165372, by rfl⟩ : syracuseStep 440993 = 330745) B330745
theorem B441011 : Blo 291829 441011 := bstep (se 1 (by rfl) ⟨330758, by rfl⟩ : syracuseStep 441011 = 661517) B661517
theorem B441041 : Blo 291829 441041 := bstep (se 2 (by rfl) ⟨165390, by rfl⟩ : syracuseStep 441041 = 330781) B330781
theorem B441059 : Blo 291829 441059 := bstep (se 1 (by rfl) ⟨330794, by rfl⟩ : syracuseStep 441059 = 661589) B661589
theorem B441089 : Blo 291829 441089 := bstep (se 2 (by rfl) ⟨165408, by rfl⟩ : syracuseStep 441089 = 330817) B330817
theorem B441107 : Blo 291829 441107 := bstep (se 1 (by rfl) ⟨330830, by rfl⟩ : syracuseStep 441107 = 661661) B661661
theorem B998189 : Blo 291829 998189 := bstep (se 3 (by rfl) ⟨187160, by rfl⟩ : syracuseStep 998189 = 374321) B374321
theorem B441137 : Blo 291829 441137 := bstep (se 2 (by rfl) ⟨165426, by rfl⟩ : syracuseStep 441137 = 330853) B330853
theorem B441155 : Blo 291829 441155 := bstep (se 1 (by rfl) ⟨330866, by rfl⟩ : syracuseStep 441155 = 661733) B661733
theorem B441185 : Blo 291829 441185 := bstep (se 2 (by rfl) ⟨165444, by rfl⟩ : syracuseStep 441185 = 330889) B330889
theorem B998243 : Blo 291829 998243 := bstep (se 1 (by rfl) ⟨748682, by rfl⟩ : syracuseStep 998243 = 1497365) B1497365
theorem B1063793 : Blo 291829 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B441203 : Blo 291829 441203 := bstep (se 1 (by rfl) ⟨330902, by rfl⟩ : syracuseStep 441203 = 661805) B661805
theorem B441233 : Blo 291829 441233 := bstep (se 2 (by rfl) ⟨165462, by rfl⟩ : syracuseStep 441233 = 330925) B330925
theorem B441251 : Blo 291829 441251 := bstep (se 1 (by rfl) ⟨330938, by rfl⟩ : syracuseStep 441251 = 661877) B661877
theorem B441281 : Blo 291829 441281 := bstep (se 2 (by rfl) ⟨165480, by rfl⟩ : syracuseStep 441281 = 330961) B330961
theorem B441299 : Blo 291829 441299 := bstep (se 1 (by rfl) ⟨330974, by rfl⟩ : syracuseStep 441299 = 661949) B661949
theorem B441329 : Blo 291829 441329 := bstep (se 2 (by rfl) ⟨165498, by rfl⟩ : syracuseStep 441329 = 330997) B330997
theorem B441347 : Blo 291829 441347 := bstep (se 1 (by rfl) ⟨331010, by rfl⟩ : syracuseStep 441347 = 662021) B662021
theorem B441377 : Blo 291829 441377 := bstep (se 2 (by rfl) ⟨165516, by rfl⟩ : syracuseStep 441377 = 331033) B331033
theorem B441395 : Blo 291829 441395 := bstep (se 1 (by rfl) ⟨331046, by rfl⟩ : syracuseStep 441395 = 662093) B662093
theorem B834637 : Blo 291829 834637 := bstep (se 3 (by rfl) ⟨156494, by rfl⟩ : syracuseStep 834637 = 312989) B312989
theorem B1883213 : Blo 291829 1883213 := bstep (se 3 (by rfl) ⟨353102, by rfl⟩ : syracuseStep 1883213 = 706205) B706205
theorem B441425 : Blo 291829 441425 := bstep (se 2 (by rfl) ⟨165534, by rfl⟩ : syracuseStep 441425 = 331069) B331069
theorem B441443 : Blo 291829 441443 := bstep (se 1 (by rfl) ⟨331082, by rfl⟩ : syracuseStep 441443 = 662165) B662165
theorem B441473 : Blo 291829 441473 := bstep (se 2 (by rfl) ⟨165552, by rfl⟩ : syracuseStep 441473 = 331105) B331105
theorem B441491 : Blo 291829 441491 := bstep (se 1 (by rfl) ⟨331118, by rfl⟩ : syracuseStep 441491 = 662237) B662237
theorem B441521 : Blo 291829 441521 := bstep (se 2 (by rfl) ⟨165570, by rfl⟩ : syracuseStep 441521 = 331141) B331141
theorem B441539 : Blo 291829 441539 := bstep (se 1 (by rfl) ⟨331154, by rfl⟩ : syracuseStep 441539 = 662309) B662309
theorem B441569 : Blo 291829 441569 := bstep (se 2 (by rfl) ⟨165588, by rfl⟩ : syracuseStep 441569 = 331177) B331177
theorem B441587 : Blo 291829 441587 := bstep (se 1 (by rfl) ⟨331190, by rfl⟩ : syracuseStep 441587 = 662381) B662381
theorem B441617 : Blo 291829 441617 := bstep (se 2 (by rfl) ⟨165606, by rfl⟩ : syracuseStep 441617 = 331213) B331213
theorem B441635 : Blo 291829 441635 := bstep (se 1 (by rfl) ⟨331226, by rfl⟩ : syracuseStep 441635 = 662453) B662453
theorem B441665 : Blo 291829 441665 := bstep (se 2 (by rfl) ⟨165624, by rfl⟩ : syracuseStep 441665 = 331249) B331249
theorem B441683 : Blo 291829 441683 := bstep (se 1 (by rfl) ⟨331262, by rfl⟩ : syracuseStep 441683 = 662525) B662525
theorem B441713 : Blo 291829 441713 := bstep (se 2 (by rfl) ⟨165642, by rfl⟩ : syracuseStep 441713 = 331285) B331285
theorem B441731 : Blo 291829 441731 := bstep (se 1 (by rfl) ⟨331298, by rfl⟩ : syracuseStep 441731 = 662597) B662597
theorem B441761 : Blo 291829 441761 := bstep (se 2 (by rfl) ⟨165660, by rfl⟩ : syracuseStep 441761 = 331321) B331321
theorem B441779 : Blo 291829 441779 := bstep (se 1 (by rfl) ⟨331334, by rfl⟩ : syracuseStep 441779 = 662669) B662669
theorem B441809 : Blo 291829 441809 := bstep (se 2 (by rfl) ⟨165678, by rfl⟩ : syracuseStep 441809 = 331357) B331357
theorem B441827 : Blo 291829 441827 := bstep (se 1 (by rfl) ⟨331370, by rfl⟩ : syracuseStep 441827 = 662741) B662741
theorem B441857 : Blo 291829 441857 := bstep (se 2 (by rfl) ⟨165696, by rfl⟩ : syracuseStep 441857 = 331393) B331393
theorem B441875 : Blo 291829 441875 := bstep (se 1 (by rfl) ⟨331406, by rfl⟩ : syracuseStep 441875 = 662813) B662813
theorem B441905 : Blo 291829 441905 := bstep (se 2 (by rfl) ⟨165714, by rfl⟩ : syracuseStep 441905 = 331429) B331429
theorem B1064497 : Blo 291829 1064497 := bstep (se 2 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 1064497 = 798373) B798373
theorem B441923 : Blo 291829 441923 := bstep (se 1 (by rfl) ⟨331442, by rfl⟩ : syracuseStep 441923 = 662885) B662885
theorem B441953 : Blo 291829 441953 := bstep (se 2 (by rfl) ⟨165732, by rfl⟩ : syracuseStep 441953 = 331465) B331465
theorem B441971 : Blo 291829 441971 := bstep (se 1 (by rfl) ⟨331478, by rfl⟩ : syracuseStep 441971 = 662957) B662957
theorem B442001 : Blo 291829 442001 := bstep (se 2 (by rfl) ⟨165750, by rfl⟩ : syracuseStep 442001 = 331501) B331501
theorem B442019 : Blo 291829 442019 := bstep (se 1 (by rfl) ⟨331514, by rfl⟩ : syracuseStep 442019 = 663029) B663029
theorem B442049 : Blo 291829 442049 := bstep (se 2 (by rfl) ⟨165768, by rfl⟩ : syracuseStep 442049 = 331537) B331537
theorem B442067 : Blo 291829 442067 := bstep (se 1 (by rfl) ⟨331550, by rfl⟩ : syracuseStep 442067 = 663101) B663101
theorem B442097 : Blo 291829 442097 := bstep (se 2 (by rfl) ⟨165786, by rfl⟩ : syracuseStep 442097 = 331573) B331573
theorem B442115 : Blo 291829 442115 := bstep (se 1 (by rfl) ⟨331586, by rfl⟩ : syracuseStep 442115 = 663173) B663173
theorem B442145 : Blo 291829 442145 := bstep (se 2 (by rfl) ⟨165804, by rfl⟩ : syracuseStep 442145 = 331609) B331609
theorem B1490723 : Blo 291829 1490723 := bstep (se 1 (by rfl) ⟨1118042, by rfl⟩ : syracuseStep 1490723 = 2236085) B2236085
theorem B442163 : Blo 291829 442163 := bstep (se 1 (by rfl) ⟨331622, by rfl⟩ : syracuseStep 442163 = 663245) B663245
theorem B442193 : Blo 291829 442193 := bstep (se 2 (by rfl) ⟨165822, by rfl⟩ : syracuseStep 442193 = 331645) B331645
theorem B442211 : Blo 291829 442211 := bstep (se 1 (by rfl) ⟨331658, by rfl⟩ : syracuseStep 442211 = 663317) B663317
theorem B442241 : Blo 291829 442241 := bstep (se 2 (by rfl) ⟨165840, by rfl⟩ : syracuseStep 442241 = 331681) B331681
theorem B442259 : Blo 291829 442259 := bstep (se 1 (by rfl) ⟨331694, by rfl⟩ : syracuseStep 442259 = 663389) B663389
theorem B442289 : Blo 291829 442289 := bstep (se 2 (by rfl) ⟨165858, by rfl⟩ : syracuseStep 442289 = 331717) B331717
theorem B1261489 : Blo 291829 1261489 := bstep (se 2 (by rfl) ⟨473058, by rfl⟩ : syracuseStep 1261489 = 946117) B946117
theorem B442307 : Blo 291829 442307 := bstep (se 1 (by rfl) ⟨331730, by rfl⟩ : syracuseStep 442307 = 663461) B663461
theorem B442337 : Blo 291829 442337 := bstep (se 2 (by rfl) ⟨165876, by rfl⟩ : syracuseStep 442337 = 331753) B331753
theorem B442355 : Blo 291829 442355 := bstep (se 1 (by rfl) ⟨331766, by rfl⟩ : syracuseStep 442355 = 663533) B663533
theorem B442385 : Blo 291829 442385 := bstep (se 2 (by rfl) ⟨165894, by rfl⟩ : syracuseStep 442385 = 331789) B331789
theorem B442403 : Blo 291829 442403 := bstep (se 1 (by rfl) ⟨331802, by rfl⟩ : syracuseStep 442403 = 663605) B663605
theorem B442433 : Blo 291829 442433 := bstep (se 2 (by rfl) ⟨165912, by rfl⟩ : syracuseStep 442433 = 331825) B331825
theorem B442451 : Blo 291829 442451 := bstep (se 1 (by rfl) ⟨331838, by rfl⟩ : syracuseStep 442451 = 663677) B663677
theorem B835697 : Blo 291829 835697 := bstep (se 2 (by rfl) ⟨313386, by rfl⟩ : syracuseStep 835697 = 626773) B626773
theorem B442481 : Blo 291829 442481 := bstep (se 2 (by rfl) ⟨165930, by rfl⟩ : syracuseStep 442481 = 331861) B331861
theorem B442499 : Blo 291829 442499 := bstep (se 1 (by rfl) ⟨331874, by rfl⟩ : syracuseStep 442499 = 663749) B663749
theorem B442529 : Blo 291829 442529 := bstep (se 2 (by rfl) ⟨165948, by rfl⟩ : syracuseStep 442529 = 331897) B331897
theorem B442547 : Blo 291829 442547 := bstep (se 1 (by rfl) ⟨331910, by rfl⟩ : syracuseStep 442547 = 663821) B663821
theorem B442577 : Blo 291829 442577 := bstep (se 2 (by rfl) ⟨165966, by rfl⟩ : syracuseStep 442577 = 331933) B331933
theorem B442595 : Blo 291829 442595 := bstep (se 1 (by rfl) ⟨331946, by rfl⟩ : syracuseStep 442595 = 663893) B663893
theorem B442625 : Blo 291829 442625 := bstep (se 2 (by rfl) ⟨165984, by rfl⟩ : syracuseStep 442625 = 331969) B331969
theorem B442643 : Blo 291829 442643 := bstep (se 1 (by rfl) ⟨331982, by rfl⟩ : syracuseStep 442643 = 663965) B663965
theorem B442673 : Blo 291829 442673 := bstep (se 2 (by rfl) ⟨166002, by rfl⟩ : syracuseStep 442673 = 332005) B332005
theorem B442691 : Blo 291829 442691 := bstep (se 1 (by rfl) ⟨332018, by rfl⟩ : syracuseStep 442691 = 664037) B664037
theorem B442721 : Blo 291829 442721 := bstep (se 2 (by rfl) ⟨166020, by rfl⟩ : syracuseStep 442721 = 332041) B332041
theorem B442739 : Blo 291829 442739 := bstep (se 1 (by rfl) ⟨332054, by rfl⟩ : syracuseStep 442739 = 664109) B664109
theorem B442769 : Blo 291829 442769 := bstep (se 2 (by rfl) ⟨166038, by rfl⟩ : syracuseStep 442769 = 332077) B332077
theorem B311699 : Blo 291829 311699 := bstep (se 1 (by rfl) ⟨233774, by rfl⟩ : syracuseStep 311699 = 467549) B467549
theorem B442787 : Blo 291829 442787 := bstep (se 1 (by rfl) ⟨332090, by rfl⟩ : syracuseStep 442787 = 664181) B664181
theorem B442817 : Blo 291829 442817 := bstep (se 2 (by rfl) ⟨166056, by rfl⟩ : syracuseStep 442817 = 332113) B332113
theorem B14336453 : Blo 291829 14336453 := bstep (se 4 (by rfl) ⟨1344042, by rfl⟩ : syracuseStep 14336453 = 2688085) B2688085
theorem B442835 : Blo 291829 442835 := bstep (se 1 (by rfl) ⟨332126, by rfl⟩ : syracuseStep 442835 = 664253) B664253
theorem B442865 : Blo 291829 442865 := bstep (se 2 (by rfl) ⟨166074, by rfl⟩ : syracuseStep 442865 = 332149) B332149
theorem B442883 : Blo 291829 442883 := bstep (se 1 (by rfl) ⟨332162, by rfl⟩ : syracuseStep 442883 = 664325) B664325
theorem B442913 : Blo 291829 442913 := bstep (se 2 (by rfl) ⟨166092, by rfl⟩ : syracuseStep 442913 = 332185) B332185
theorem B442931 : Blo 291829 442931 := bstep (se 1 (by rfl) ⟨332198, by rfl⟩ : syracuseStep 442931 = 664397) B664397
theorem B1491533 : Blo 291829 1491533 := bstep (se 3 (by rfl) ⟨279662, by rfl⟩ : syracuseStep 1491533 = 559325) B559325
theorem B442961 : Blo 291829 442961 := bstep (se 2 (by rfl) ⟨166110, by rfl⟩ : syracuseStep 442961 = 332221) B332221
theorem B442979 : Blo 291829 442979 := bstep (se 1 (by rfl) ⟨332234, by rfl⟩ : syracuseStep 442979 = 664469) B664469
theorem B443009 : Blo 291829 443009 := bstep (se 2 (by rfl) ⟨166128, by rfl⟩ : syracuseStep 443009 = 332257) B332257
theorem B443027 : Blo 291829 443027 := bstep (se 1 (by rfl) ⟨332270, by rfl⟩ : syracuseStep 443027 = 664541) B664541
theorem B443057 : Blo 291829 443057 := bstep (se 2 (by rfl) ⟨166146, by rfl⟩ : syracuseStep 443057 = 332293) B332293
theorem B443075 : Blo 291829 443075 := bstep (se 1 (by rfl) ⟨332306, by rfl⟩ : syracuseStep 443075 = 664613) B664613
theorem B443105 : Blo 291829 443105 := bstep (se 2 (by rfl) ⟨166164, by rfl⟩ : syracuseStep 443105 = 332329) B332329
theorem B443123 : Blo 291829 443123 := bstep (se 1 (by rfl) ⟨332342, by rfl⟩ : syracuseStep 443123 = 664685) B664685
theorem B836369 : Blo 291829 836369 := bstep (se 2 (by rfl) ⟨313638, by rfl⟩ : syracuseStep 836369 = 627277) B627277
theorem B443153 : Blo 291829 443153 := bstep (se 2 (by rfl) ⟨166182, by rfl⟩ : syracuseStep 443153 = 332365) B332365
theorem B443171 : Blo 291829 443171 := bstep (se 1 (by rfl) ⟨332378, by rfl⟩ : syracuseStep 443171 = 664757) B664757
theorem B2016049 : Blo 291829 2016049 := bstep (se 2 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 2016049 = 1512037) B1512037
theorem B443201 : Blo 291829 443201 := bstep (se 2 (by rfl) ⟨166200, by rfl⟩ : syracuseStep 443201 = 332401) B332401
theorem B443219 : Blo 291829 443219 := bstep (se 1 (by rfl) ⟨332414, by rfl⟩ : syracuseStep 443219 = 664829) B664829
theorem B443249 : Blo 291829 443249 := bstep (se 2 (by rfl) ⟨166218, by rfl⟩ : syracuseStep 443249 = 332437) B332437
theorem B443267 : Blo 291829 443267 := bstep (se 1 (by rfl) ⟨332450, by rfl⟩ : syracuseStep 443267 = 664901) B664901
theorem B443297 : Blo 291829 443297 := bstep (se 2 (by rfl) ⟨166236, by rfl⟩ : syracuseStep 443297 = 332473) B332473
theorem B443315 : Blo 291829 443315 := bstep (se 1 (by rfl) ⟨332486, by rfl⟩ : syracuseStep 443315 = 664973) B664973
theorem B443345 : Blo 291829 443345 := bstep (se 2 (by rfl) ⟨166254, by rfl⟩ : syracuseStep 443345 = 332509) B332509
theorem B443363 : Blo 291829 443363 := bstep (se 1 (by rfl) ⟨332522, by rfl⟩ : syracuseStep 443363 = 665045) B665045
theorem B3195875 : Blo 291829 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B443393 : Blo 291829 443393 := bstep (se 2 (by rfl) ⟨166272, by rfl⟩ : syracuseStep 443393 = 332545) B332545
theorem B443411 : Blo 291829 443411 := bstep (se 1 (by rfl) ⟨332558, by rfl⟩ : syracuseStep 443411 = 665117) B665117
theorem B443441 : Blo 291829 443441 := bstep (se 2 (by rfl) ⟨166290, by rfl⟩ : syracuseStep 443441 = 332581) B332581
theorem B443459 : Blo 291829 443459 := bstep (se 1 (by rfl) ⟨332594, by rfl⟩ : syracuseStep 443459 = 665189) B665189
theorem B443489 : Blo 291829 443489 := bstep (se 2 (by rfl) ⟨166308, by rfl⟩ : syracuseStep 443489 = 332617) B332617
theorem B443507 : Blo 291829 443507 := bstep (se 1 (by rfl) ⟨332630, by rfl⟩ : syracuseStep 443507 = 665261) B665261
theorem B705667 : Blo 291829 705667 := bstep (se 1 (by rfl) ⟨529250, by rfl⟩ : syracuseStep 705667 = 1058501) B1058501
theorem B443537 : Blo 291829 443537 := bstep (se 2 (by rfl) ⟨166326, by rfl⟩ : syracuseStep 443537 = 332653) B332653
theorem B443555 : Blo 291829 443555 := bstep (se 1 (by rfl) ⟨332666, by rfl⟩ : syracuseStep 443555 = 665333) B665333
theorem B443585 : Blo 291829 443585 := bstep (se 2 (by rfl) ⟨166344, by rfl⟩ : syracuseStep 443585 = 332689) B332689
theorem B443603 : Blo 291829 443603 := bstep (se 1 (by rfl) ⟨332702, by rfl⟩ : syracuseStep 443603 = 665405) B665405
theorem B705763 : Blo 291829 705763 := bstep (se 1 (by rfl) ⟨529322, by rfl⟩ : syracuseStep 705763 = 1058645) B1058645
theorem B443633 : Blo 291829 443633 := bstep (se 2 (by rfl) ⟨166362, by rfl⟩ : syracuseStep 443633 = 332725) B332725
theorem B443651 : Blo 291829 443651 := bstep (se 1 (by rfl) ⟨332738, by rfl⟩ : syracuseStep 443651 = 665477) B665477
theorem B443681 : Blo 291829 443681 := bstep (se 2 (by rfl) ⟨166380, by rfl⟩ : syracuseStep 443681 = 332761) B332761
theorem B443699 : Blo 291829 443699 := bstep (se 1 (by rfl) ⟨332774, by rfl⟩ : syracuseStep 443699 = 665549) B665549
theorem B443729 : Blo 291829 443729 := bstep (se 2 (by rfl) ⟨166398, by rfl⟩ : syracuseStep 443729 = 332797) B332797
theorem B312707 : Blo 291829 312707 := bstep (se 1 (by rfl) ⟨234530, by rfl⟩ : syracuseStep 312707 = 469061) B469061
theorem B2377187 : Blo 291829 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B837155 : Blo 291829 837155 := bstep (se 1 (by rfl) ⟨627866, by rfl⟩ : syracuseStep 837155 = 1255733) B1255733
theorem B837485 : Blo 291829 837485 := bstep (se 3 (by rfl) ⟨157028, by rfl⟩ : syracuseStep 837485 = 314057) B314057
theorem B837553 : Blo 291829 837553 := bstep (se 2 (by rfl) ⟨314082, by rfl⟩ : syracuseStep 837553 = 628165) B628165
theorem B1427633 : Blo 291829 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B837827 : Blo 291829 837827 := bstep (se 1 (by rfl) ⟨628370, by rfl⟩ : syracuseStep 837827 = 1256741) B1256741
theorem B5621957 : Blo 291829 5621957 := bstep (se 4 (by rfl) ⟨527058, by rfl⟩ : syracuseStep 5621957 = 1054117) B1054117
theorem B936173 : Blo 291829 936173 := bstep (se 3 (by rfl) ⟨175532, by rfl⟩ : syracuseStep 936173 = 351065) B351065
theorem B2672909 : Blo 291829 2672909 := bstep (se 3 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 2672909 = 1002341) B1002341
theorem B2377997 : Blo 291829 2377997 := bstep (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) B891749
theorem B739601 : Blo 291829 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B674065 : Blo 291829 674065 := bstep (se 2 (by rfl) ⟨252774, by rfl⟩ : syracuseStep 674065 = 505549) B505549
theorem B739651 : Blo 291829 739651 := bstep (se 1 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 739651 = 1109477) B1109477
theorem B706897 : Blo 291829 706897 := bstep (se 2 (by rfl) ⟨265086, by rfl⟩ : syracuseStep 706897 = 530173) B530173
theorem B444755 : Blo 291829 444755 := bstep (se 1 (by rfl) ⟨333566, by rfl⟩ : syracuseStep 444755 = 667133) B667133
theorem B1886597 : Blo 291829 1886597 := bstep (se 4 (by rfl) ⟨176868, by rfl⟩ : syracuseStep 1886597 = 353737) B353737
theorem B739793 : Blo 291829 739793 := bstep (se 2 (by rfl) ⟨277422, by rfl⟩ : syracuseStep 739793 = 554845) B554845
theorem B510451 : Blo 291829 510451 := bstep (se 1 (by rfl) ⟨382838, by rfl⟩ : syracuseStep 510451 = 765677) B765677
theorem B1002125 : Blo 291829 1002125 := bstep (se 3 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 1002125 = 375797) B375797
theorem B314275 : Blo 291829 314275 := bstep (se 1 (by rfl) ⟨235706, by rfl⟩ : syracuseStep 314275 = 471413) B471413
theorem B838669 : Blo 291829 838669 := bstep (se 3 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 838669 = 314501) B314501
theorem B2018317 : Blo 291829 2018317 := bstep (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) B756869
theorem B838829 : Blo 291829 838829 := bstep (se 3 (by rfl) ⟨157280, by rfl⟩ : syracuseStep 838829 = 314561) B314561
theorem B839011 : Blo 291829 839011 := bstep (se 1 (by rfl) ⟨629258, by rfl⟩ : syracuseStep 839011 = 1258517) B1258517
theorem B314723 : Blo 291829 314723 := bstep (se 1 (by rfl) ⟨236042, by rfl⟩ : syracuseStep 314723 = 472085) B472085
theorem B3362147 : Blo 291829 3362147 := bstep (se 1 (by rfl) ⟨2521610, by rfl⟩ : syracuseStep 3362147 = 5043221) B5043221
theorem B6344077 : Blo 291829 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B740785 : Blo 291829 740785 := bstep (se 2 (by rfl) ⟨277794, by rfl⟩ : syracuseStep 740785 = 555589) B555589
theorem B1494449 : Blo 291829 1494449 := bstep (se 2 (by rfl) ⟨560418, by rfl⟩ : syracuseStep 1494449 = 1120837) B1120837
theorem B577091 : Blo 291829 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B4247153 : Blo 291829 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B741059 : Blo 291829 741059 := bstep (se 1 (by rfl) ⟨555794, by rfl⟩ : syracuseStep 741059 = 1111589) B1111589
theorem B479009 : Blo 291829 479009 := bstep (se 2 (by rfl) ⟨179628, by rfl⟩ : syracuseStep 479009 = 359257) B359257
theorem B937763 : Blo 291829 937763 := bstep (se 1 (by rfl) ⟨703322, by rfl⟩ : syracuseStep 937763 = 1406645) B1406645
theorem B741251 : Blo 291829 741251 := bstep (se 1 (by rfl) ⟨555938, by rfl⟩ : syracuseStep 741251 = 1111877) B1111877
theorem B1200419 : Blo 291829 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B447139 : Blo 291829 447139 := bstep (se 1 (by rfl) ⟨335354, by rfl⟩ : syracuseStep 447139 = 670709) B670709
theorem B2216645 : Blo 291829 2216645 := bstep (se 4 (by rfl) ⟨207810, by rfl⟩ : syracuseStep 2216645 = 415621) B415621
theorem B840401 : Blo 291829 840401 := bstep (se 2 (by rfl) ⟨315150, by rfl⟩ : syracuseStep 840401 = 630301) B630301
theorem B742193 : Blo 291829 742193 := bstep (se 2 (by rfl) ⟨278322, by rfl⟩ : syracuseStep 742193 = 556645) B556645
theorem B742243 : Blo 291829 742243 := bstep (se 1 (by rfl) ⟨556682, by rfl⟩ : syracuseStep 742243 = 1113365) B1113365
theorem B1495907 : Blo 291829 1495907 := bstep (se 1 (by rfl) ⟨1121930, by rfl⟩ : syracuseStep 1495907 = 2243861) B2243861
theorem B742385 : Blo 291829 742385 := bstep (se 2 (by rfl) ⟨278394, by rfl⟩ : syracuseStep 742385 = 556789) B556789
theorem B939043 : Blo 291829 939043 := bstep (se 1 (by rfl) ⟨704282, by rfl⟩ : syracuseStep 939043 = 1408565) B1408565
theorem B7492661 : Blo 291829 7492661 := bstep (se 5 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 7492661 = 702437) B702437
theorem B873713 : Blo 291829 873713 := bstep (se 2 (by rfl) ⟨327642, by rfl⟩ : syracuseStep 873713 = 655285) B655285
theorem B1594673 : Blo 291829 1594673 := bstep (se 2 (by rfl) ⟨598002, by rfl⟩ : syracuseStep 1594673 = 1196005) B1196005
theorem B939377 : Blo 291829 939377 := bstep (se 2 (by rfl) ⟨352266, by rfl⟩ : syracuseStep 939377 = 704533) B704533
theorem B841357 : Blo 291829 841357 := bstep (se 3 (by rfl) ⟨157754, by rfl⟩ : syracuseStep 841357 = 315509) B315509
theorem B1496717 : Blo 291829 1496717 := bstep (se 3 (by rfl) ⟨280634, by rfl⟩ : syracuseStep 1496717 = 561269) B561269
theorem B2119537 : Blo 291829 2119537 := bstep (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) B1589653
theorem B1890161 : Blo 291829 1890161 := bstep (se 2 (by rfl) ⟨708810, by rfl⟩ : syracuseStep 1890161 = 1417621) B1417621
theorem B841585 : Blo 291829 841585 := bstep (se 2 (by rfl) ⟨315594, by rfl⟩ : syracuseStep 841585 = 631189) B631189
theorem B415633 : Blo 291829 415633 := bstep (se 2 (by rfl) ⟨155862, by rfl⟩ : syracuseStep 415633 = 311725) B311725
theorem B743377 : Blo 291829 743377 := bstep (se 2 (by rfl) ⟨278766, by rfl⟩ : syracuseStep 743377 = 557533) B557533
theorem B841745 : Blo 291829 841745 := bstep (se 2 (by rfl) ⟨315654, by rfl⟩ : syracuseStep 841745 = 631309) B631309
theorem B841859 : Blo 291829 841859 := bstep (se 1 (by rfl) ⟨631394, by rfl⟩ : syracuseStep 841859 = 1262789) B1262789
theorem B743651 : Blo 291829 743651 := bstep (se 1 (by rfl) ⟨557738, by rfl⟩ : syracuseStep 743651 = 1115477) B1115477
theorem B743843 : Blo 291829 743843 := bstep (se 1 (by rfl) ⟨557882, by rfl⟩ : syracuseStep 743843 = 1115765) B1115765
theorem B416225 : Blo 291829 416225 := bstep (se 2 (by rfl) ⟨156084, by rfl⟩ : syracuseStep 416225 = 312169) B312169
theorem B5626421 : Blo 291829 5626421 := bstep (se 5 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 5626421 = 527477) B527477
theorem B318115 : Blo 291829 318115 := bstep (se 1 (by rfl) ⟨238586, by rfl⟩ : syracuseStep 318115 = 477173) B477173
theorem B416755 : Blo 291829 416755 := bstep (se 1 (by rfl) ⟨312566, by rfl⟩ : syracuseStep 416755 = 625133) B625133
theorem B1891619 : Blo 291829 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B417091 : Blo 291829 417091 := bstep (se 1 (by rfl) ⟨312818, by rfl⟩ : syracuseStep 417091 = 625637) B625637
theorem B744785 : Blo 291829 744785 := bstep (se 2 (by rfl) ⟨279294, by rfl⟩ : syracuseStep 744785 = 558589) B558589
theorem B744835 : Blo 291829 744835 := bstep (se 1 (by rfl) ⟨558626, by rfl⟩ : syracuseStep 744835 = 1117253) B1117253
theorem B941453 : Blo 291829 941453 := bstep (se 3 (by rfl) ⟨176522, by rfl⟩ : syracuseStep 941453 = 353045) B353045
theorem B482737 : Blo 291829 482737 := bstep (se 2 (by rfl) ⟨181026, by rfl⟩ : syracuseStep 482737 = 362053) B362053
theorem B318979 : Blo 291829 318979 := bstep (se 1 (by rfl) ⟨239234, by rfl⟩ : syracuseStep 318979 = 478469) B478469
theorem B744977 : Blo 291829 744977 := bstep (se 2 (by rfl) ⟨279366, by rfl⟩ : syracuseStep 744977 = 558733) B558733
theorem B1597091 : Blo 291829 1597091 := bstep (se 1 (by rfl) ⟨1197818, by rfl⟩ : syracuseStep 1597091 = 2395637) B2395637
theorem B1498915 : Blo 291829 1498915 := bstep (se 1 (by rfl) ⟨1124186, by rfl⟩ : syracuseStep 1498915 = 2248373) B2248373
theorem B417649 : Blo 291829 417649 := bstep (se 2 (by rfl) ⟨156618, by rfl⟩ : syracuseStep 417649 = 313237) B313237
theorem B417683 : Blo 291829 417683 := bstep (se 1 (by rfl) ⟨313262, by rfl⟩ : syracuseStep 417683 = 626525) B626525
theorem B1335473 : Blo 291829 1335473 := bstep (se 2 (by rfl) ⟨500802, by rfl⟩ : syracuseStep 1335473 = 1001605) B1001605
theorem B6447413 : Blo 291829 6447413 := bstep (se 5 (by rfl) ⟨302222, by rfl⟩ : syracuseStep 6447413 = 604445) B604445
theorem B418241 : Blo 291829 418241 := bstep (se 2 (by rfl) ⟨156840, by rfl⟩ : syracuseStep 418241 = 313681) B313681
theorem B745969 : Blo 291829 745969 := bstep (se 2 (by rfl) ⟨279738, by rfl⟩ : syracuseStep 745969 = 559477) B559477
theorem B418321 : Blo 291829 418321 := bstep (se 2 (by rfl) ⟨156870, by rfl⟩ : syracuseStep 418321 = 313741) B313741
theorem B746243 : Blo 291829 746243 := bstep (se 1 (by rfl) ⟨559682, by rfl⟩ : syracuseStep 746243 = 1119365) B1119365
theorem B746435 : Blo 291829 746435 := bstep (se 1 (by rfl) ⟨559826, by rfl⟩ : syracuseStep 746435 = 1119653) B1119653
theorem B3761093 : Blo 291829 3761093 := bstep (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) B705205
theorem B943235 : Blo 291829 943235 := bstep (se 1 (by rfl) ⟨707426, by rfl⟩ : syracuseStep 943235 = 1414853) B1414853
theorem B419107 : Blo 291829 419107 := bstep (se 1 (by rfl) ⟨314330, by rfl⟩ : syracuseStep 419107 = 628661) B628661
theorem B419585 : Blo 291829 419585 := bstep (se 2 (by rfl) ⟨157344, by rfl⟩ : syracuseStep 419585 = 314689) B314689
theorem B747377 : Blo 291829 747377 := bstep (se 2 (by rfl) ⟨280266, by rfl⟩ : syracuseStep 747377 = 560533) B560533
theorem B419699 : Blo 291829 419699 := bstep (se 1 (by rfl) ⟨314774, by rfl⟩ : syracuseStep 419699 = 629549) B629549
theorem B354179 : Blo 291829 354179 := bstep (se 1 (by rfl) ⟨265634, by rfl⟩ : syracuseStep 354179 = 531269) B531269
theorem B747427 : Blo 291829 747427 := bstep (se 1 (by rfl) ⟨560570, by rfl⟩ : syracuseStep 747427 = 1121141) B1121141
theorem B1664945 : Blo 291829 1664945 := bstep (se 2 (by rfl) ⟨624354, by rfl⟩ : syracuseStep 1664945 = 1248709) B1248709
theorem B419779 : Blo 291829 419779 := bstep (se 1 (by rfl) ⟨314834, by rfl⟩ : syracuseStep 419779 = 629669) B629669
theorem B1402915 : Blo 291829 1402915 := bstep (se 1 (by rfl) ⟨1052186, by rfl⟩ : syracuseStep 1402915 = 2104373) B2104373
theorem B747569 : Blo 291829 747569 := bstep (se 2 (by rfl) ⟨280338, by rfl⟩ : syracuseStep 747569 = 560677) B560677
theorem B452945 : Blo 291829 452945 := bstep (se 2 (by rfl) ⟨169854, by rfl⟩ : syracuseStep 452945 = 339709) B339709
theorem B2222477 : Blo 291829 2222477 := bstep (se 3 (by rfl) ⟨416714, by rfl⟩ : syracuseStep 2222477 = 833429) B833429
theorem B944579 : Blo 291829 944579 := bstep (se 1 (by rfl) ⟨708434, by rfl⟩ : syracuseStep 944579 = 1416869) B1416869
theorem B420337 : Blo 291829 420337 := bstep (se 2 (by rfl) ⟨157626, by rfl⟩ : syracuseStep 420337 = 315253) B315253
theorem B1895309 : Blo 291829 1895309 := bstep (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) B710741
theorem B682897 : Blo 291829 682897 := bstep (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) B512173
theorem B748561 : Blo 291829 748561 := bstep (se 2 (by rfl) ⟨280710, by rfl⟩ : syracuseStep 748561 = 561421) B561421
theorem B5729393 : Blo 291829 5729393 := bstep (se 2 (by rfl) ⟨2148522, by rfl⟩ : syracuseStep 5729393 = 4297045) B4297045
theorem B421043 : Blo 291829 421043 := bstep (se 1 (by rfl) ⟨315782, by rfl⟩ : syracuseStep 421043 = 631565) B631565
theorem B1404145 : Blo 291829 1404145 := bstep (se 2 (by rfl) ⟨526554, by rfl⟩ : syracuseStep 1404145 = 1053109) B1053109
theorem B1666403 : Blo 291829 1666403 := bstep (se 1 (by rfl) ⟨1249802, by rfl⟩ : syracuseStep 1666403 = 2499605) B2499605
theorem B1109645 : Blo 291829 1109645 := bstep (se 3 (by rfl) ⟨208058, by rfl⟩ : syracuseStep 1109645 = 416117) B416117
theorem B946349 : Blo 291829 946349 := bstep (se 3 (by rfl) ⟨177440, by rfl⟩ : syracuseStep 946349 = 354881) B354881
theorem B1667405 : Blo 291829 1667405 := bstep (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) B625277
theorem B422275 : Blo 291829 422275 := bstep (se 1 (by rfl) ⟨316706, by rfl⟩ : syracuseStep 422275 = 633413) B633413
theorem B1110449 : Blo 291829 1110449 := bstep (se 2 (by rfl) ⟨416418, by rfl⟩ : syracuseStep 1110449 = 832837) B832837
theorem B291843 : Blo 291829 291843 := bstep (se 1 (by rfl) ⟨218882, by rfl⟩ : syracuseStep 291843 = 437765) B437765
theorem B291859 : Blo 291829 291859 := bstep (se 1 (by rfl) ⟨218894, by rfl⟩ : syracuseStep 291859 = 437789) B437789
theorem B291875 : Blo 291829 291875 := bstep (se 1 (by rfl) ⟨218906, by rfl⟩ : syracuseStep 291875 = 437813) B437813
theorem B554033 : Blo 291829 554033 := bstep (se 2 (by rfl) ⟨207762, by rfl⟩ : syracuseStep 554033 = 415525) B415525
theorem B291891 : Blo 291829 291891 := bstep (se 1 (by rfl) ⟨218918, by rfl⟩ : syracuseStep 291891 = 437837) B437837
theorem B291907 : Blo 291829 291907 := bstep (se 1 (by rfl) ⟨218930, by rfl⟩ : syracuseStep 291907 = 437861) B437861
theorem B1111117 : Blo 291829 1111117 := bstep (se 3 (by rfl) ⟨208334, by rfl⟩ : syracuseStep 1111117 = 416669) B416669
theorem B291923 : Blo 291829 291923 := bstep (se 1 (by rfl) ⟨218942, by rfl⟩ : syracuseStep 291923 = 437885) B437885
theorem B291939 : Blo 291829 291939 := bstep (se 1 (by rfl) ⟨218954, by rfl⟩ : syracuseStep 291939 = 437909) B437909
theorem B291955 : Blo 291829 291955 := bstep (se 1 (by rfl) ⟨218966, by rfl⟩ : syracuseStep 291955 = 437933) B437933
theorem B291971 : Blo 291829 291971 := bstep (se 1 (by rfl) ⟨218978, by rfl⟩ : syracuseStep 291971 = 437957) B437957
theorem B291987 : Blo 291829 291987 := bstep (se 1 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 291987 = 437981) B437981
theorem B292003 : Blo 291829 292003 := bstep (se 1 (by rfl) ⟨219002, by rfl⟩ : syracuseStep 292003 = 438005) B438005
theorem B292019 : Blo 291829 292019 := bstep (se 1 (by rfl) ⟨219014, by rfl⟩ : syracuseStep 292019 = 438029) B438029
theorem B292035 : Blo 291829 292035 := bstep (se 1 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 292035 = 438053) B438053
theorem B292051 : Blo 291829 292051 := bstep (se 1 (by rfl) ⟨219038, by rfl⟩ : syracuseStep 292051 = 438077) B438077
theorem B292067 : Blo 291829 292067 := bstep (se 1 (by rfl) ⟨219050, by rfl⟩ : syracuseStep 292067 = 438101) B438101
theorem B849133 : Blo 291829 849133 := bstep (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) B318425
theorem B3994865 : Blo 291829 3994865 := bstep (se 2 (by rfl) ⟨1498074, by rfl⟩ : syracuseStep 3994865 = 2996149) B2996149
theorem B2225393 : Blo 291829 2225393 := bstep (se 2 (by rfl) ⟨834522, by rfl⟩ : syracuseStep 2225393 = 1669045) B1669045
theorem B292083 : Blo 291829 292083 := bstep (se 1 (by rfl) ⟨219062, by rfl⟩ : syracuseStep 292083 = 438125) B438125
theorem B292099 : Blo 291829 292099 := bstep (se 1 (by rfl) ⟨219074, by rfl⟩ : syracuseStep 292099 = 438149) B438149
theorem B292115 : Blo 291829 292115 := bstep (se 1 (by rfl) ⟨219086, by rfl⟩ : syracuseStep 292115 = 438173) B438173
theorem B292131 : Blo 291829 292131 := bstep (se 1 (by rfl) ⟨219098, by rfl⟩ : syracuseStep 292131 = 438197) B438197
theorem B292147 : Blo 291829 292147 := bstep (se 1 (by rfl) ⟨219110, by rfl⟩ : syracuseStep 292147 = 438221) B438221
theorem B292163 : Blo 291829 292163 := bstep (se 1 (by rfl) ⟨219122, by rfl⟩ : syracuseStep 292163 = 438245) B438245
theorem B292179 : Blo 291829 292179 := bstep (se 1 (by rfl) ⟨219134, by rfl⟩ : syracuseStep 292179 = 438269) B438269
theorem B292195 : Blo 291829 292195 := bstep (se 1 (by rfl) ⟨219146, by rfl⟩ : syracuseStep 292195 = 438293) B438293
theorem B292211 : Blo 291829 292211 := bstep (se 1 (by rfl) ⟨219158, by rfl⟩ : syracuseStep 292211 = 438317) B438317
theorem B292227 : Blo 291829 292227 := bstep (se 1 (by rfl) ⟨219170, by rfl⟩ : syracuseStep 292227 = 438341) B438341
theorem B292243 : Blo 291829 292243 := bstep (se 1 (by rfl) ⟨219182, by rfl⟩ : syracuseStep 292243 = 438365) B438365
theorem B292259 : Blo 291829 292259 := bstep (se 1 (by rfl) ⟨219194, by rfl⟩ : syracuseStep 292259 = 438389) B438389
theorem B292275 : Blo 291829 292275 := bstep (se 1 (by rfl) ⟨219206, by rfl⟩ : syracuseStep 292275 = 438413) B438413
theorem B554435 : Blo 291829 554435 := bstep (se 1 (by rfl) ⟨415826, by rfl⟩ : syracuseStep 554435 = 831653) B831653
theorem B292291 : Blo 291829 292291 := bstep (se 1 (by rfl) ⟨219218, by rfl⟩ : syracuseStep 292291 = 438437) B438437
theorem B2520517 : Blo 291829 2520517 := bstep (se 4 (by rfl) ⟨236298, by rfl⟩ : syracuseStep 2520517 = 472597) B472597
theorem B292307 : Blo 291829 292307 := bstep (se 1 (by rfl) ⟨219230, by rfl⟩ : syracuseStep 292307 = 438461) B438461
theorem B292323 : Blo 291829 292323 := bstep (se 1 (by rfl) ⟨219242, by rfl⟩ : syracuseStep 292323 = 438485) B438485
theorem B292339 : Blo 291829 292339 := bstep (se 1 (by rfl) ⟨219254, by rfl⟩ : syracuseStep 292339 = 438509) B438509
theorem B292355 : Blo 291829 292355 := bstep (se 1 (by rfl) ⟨219266, by rfl⟩ : syracuseStep 292355 = 438533) B438533
theorem B292371 : Blo 291829 292371 := bstep (se 1 (by rfl) ⟨219278, by rfl⟩ : syracuseStep 292371 = 438557) B438557
theorem B292387 : Blo 291829 292387 := bstep (se 1 (by rfl) ⟨219290, by rfl⟩ : syracuseStep 292387 = 438581) B438581
theorem B292403 : Blo 291829 292403 := bstep (se 1 (by rfl) ⟨219302, by rfl⟩ : syracuseStep 292403 = 438605) B438605
theorem B292419 : Blo 291829 292419 := bstep (se 1 (by rfl) ⟨219314, by rfl⟩ : syracuseStep 292419 = 438629) B438629
theorem B292435 : Blo 291829 292435 := bstep (se 1 (by rfl) ⟨219326, by rfl⟩ : syracuseStep 292435 = 438653) B438653
theorem B292451 : Blo 291829 292451 := bstep (se 1 (by rfl) ⟨219338, by rfl⟩ : syracuseStep 292451 = 438677) B438677
theorem B292467 : Blo 291829 292467 := bstep (se 1 (by rfl) ⟨219350, by rfl⟩ : syracuseStep 292467 = 438701) B438701
theorem B292483 : Blo 291829 292483 := bstep (se 1 (by rfl) ⟨219362, by rfl⟩ : syracuseStep 292483 = 438725) B438725
theorem B292499 : Blo 291829 292499 := bstep (se 1 (by rfl) ⟨219374, by rfl⟩ : syracuseStep 292499 = 438749) B438749
theorem B292515 : Blo 291829 292515 := bstep (se 1 (by rfl) ⟨219386, by rfl⟩ : syracuseStep 292515 = 438773) B438773
theorem B292531 : Blo 291829 292531 := bstep (se 1 (by rfl) ⟨219398, by rfl⟩ : syracuseStep 292531 = 438797) B438797
theorem B292547 : Blo 291829 292547 := bstep (se 1 (by rfl) ⟨219410, by rfl⟩ : syracuseStep 292547 = 438821) B438821
theorem B292563 : Blo 291829 292563 := bstep (se 1 (by rfl) ⟨219422, by rfl⟩ : syracuseStep 292563 = 438845) B438845
theorem B292579 : Blo 291829 292579 := bstep (se 1 (by rfl) ⟨219434, by rfl⟩ : syracuseStep 292579 = 438869) B438869
theorem B292595 : Blo 291829 292595 := bstep (se 1 (by rfl) ⟨219446, by rfl⟩ : syracuseStep 292595 = 438893) B438893
theorem B292611 : Blo 291829 292611 := bstep (se 1 (by rfl) ⟨219458, by rfl⟩ : syracuseStep 292611 = 438917) B438917
theorem B292627 : Blo 291829 292627 := bstep (se 1 (by rfl) ⟨219470, by rfl⟩ : syracuseStep 292627 = 438941) B438941
theorem B292643 : Blo 291829 292643 := bstep (se 1 (by rfl) ⟨219482, by rfl⟩ : syracuseStep 292643 = 438965) B438965
theorem B292659 : Blo 291829 292659 := bstep (se 1 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 292659 = 438989) B438989
theorem B292675 : Blo 291829 292675 := bstep (se 1 (by rfl) ⟨219506, by rfl⟩ : syracuseStep 292675 = 439013) B439013
theorem B751427 : Blo 291829 751427 := bstep (se 1 (by rfl) ⟨563570, by rfl⟩ : syracuseStep 751427 = 1127141) B1127141
theorem B292691 : Blo 291829 292691 := bstep (se 1 (by rfl) ⟨219518, by rfl⟩ : syracuseStep 292691 = 439037) B439037
theorem B292707 : Blo 291829 292707 := bstep (se 1 (by rfl) ⟨219530, by rfl⟩ : syracuseStep 292707 = 439061) B439061
theorem B1111907 : Blo 291829 1111907 := bstep (se 1 (by rfl) ⟨833930, by rfl⟩ : syracuseStep 1111907 = 1667861) B1667861
theorem B292723 : Blo 291829 292723 := bstep (se 1 (by rfl) ⟨219542, by rfl⟩ : syracuseStep 292723 = 439085) B439085
theorem B292739 : Blo 291829 292739 := bstep (se 1 (by rfl) ⟨219554, by rfl⟩ : syracuseStep 292739 = 439109) B439109
theorem B292755 : Blo 291829 292755 := bstep (se 1 (by rfl) ⟨219566, by rfl⟩ : syracuseStep 292755 = 439133) B439133
theorem B292771 : Blo 291829 292771 := bstep (se 1 (by rfl) ⟨219578, by rfl⟩ : syracuseStep 292771 = 439157) B439157
theorem B1898417 : Blo 291829 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B292787 : Blo 291829 292787 := bstep (se 1 (by rfl) ⟨219590, by rfl⟩ : syracuseStep 292787 = 439181) B439181
theorem B292803 : Blo 291829 292803 := bstep (se 1 (by rfl) ⟨219602, by rfl⟩ : syracuseStep 292803 = 439205) B439205
theorem B292819 : Blo 291829 292819 := bstep (se 1 (by rfl) ⟨219614, by rfl⟩ : syracuseStep 292819 = 439229) B439229
theorem B292835 : Blo 291829 292835 := bstep (se 1 (by rfl) ⟨219626, by rfl⟩ : syracuseStep 292835 = 439253) B439253
theorem B292851 : Blo 291829 292851 := bstep (se 1 (by rfl) ⟨219638, by rfl⟩ : syracuseStep 292851 = 439277) B439277
theorem B292867 : Blo 291829 292867 := bstep (se 1 (by rfl) ⟨219650, by rfl⟩ : syracuseStep 292867 = 439301) B439301
theorem B292883 : Blo 291829 292883 := bstep (se 1 (by rfl) ⟨219662, by rfl⟩ : syracuseStep 292883 = 439325) B439325
theorem B292899 : Blo 291829 292899 := bstep (se 1 (by rfl) ⟨219674, by rfl⟩ : syracuseStep 292899 = 439349) B439349
theorem B292915 : Blo 291829 292915 := bstep (se 1 (by rfl) ⟨219686, by rfl⟩ : syracuseStep 292915 = 439373) B439373
theorem B292931 : Blo 291829 292931 := bstep (se 1 (by rfl) ⟨219698, by rfl⟩ : syracuseStep 292931 = 439397) B439397
theorem B292947 : Blo 291829 292947 := bstep (se 1 (by rfl) ⟨219710, by rfl⟩ : syracuseStep 292947 = 439421) B439421
theorem B292963 : Blo 291829 292963 := bstep (se 1 (by rfl) ⟨219722, by rfl⟩ : syracuseStep 292963 = 439445) B439445
theorem B292979 : Blo 291829 292979 := bstep (se 1 (by rfl) ⟨219734, by rfl⟩ : syracuseStep 292979 = 439469) B439469
theorem B292995 : Blo 291829 292995 := bstep (se 1 (by rfl) ⟨219746, by rfl⟩ : syracuseStep 292995 = 439493) B439493
theorem B293011 : Blo 291829 293011 := bstep (se 1 (by rfl) ⟨219758, by rfl⟩ : syracuseStep 293011 = 439517) B439517
theorem B293027 : Blo 291829 293027 := bstep (se 1 (by rfl) ⟨219770, by rfl⟩ : syracuseStep 293027 = 439541) B439541
theorem B293043 : Blo 291829 293043 := bstep (se 1 (by rfl) ⟨219782, by rfl⟩ : syracuseStep 293043 = 439565) B439565
theorem B293059 : Blo 291829 293059 := bstep (se 1 (by rfl) ⟨219794, by rfl⟩ : syracuseStep 293059 = 439589) B439589
theorem B293075 : Blo 291829 293075 := bstep (se 1 (by rfl) ⟨219806, by rfl⟩ : syracuseStep 293075 = 439613) B439613
theorem B293091 : Blo 291829 293091 := bstep (se 1 (by rfl) ⟨219818, by rfl⟩ : syracuseStep 293091 = 439637) B439637
theorem B293107 : Blo 291829 293107 := bstep (se 1 (by rfl) ⟨219830, by rfl⟩ : syracuseStep 293107 = 439661) B439661
theorem B293123 : Blo 291829 293123 := bstep (se 1 (by rfl) ⟨219842, by rfl⟩ : syracuseStep 293123 = 439685) B439685
theorem B293139 : Blo 291829 293139 := bstep (se 1 (by rfl) ⟨219854, by rfl⟩ : syracuseStep 293139 = 439709) B439709
theorem B293155 : Blo 291829 293155 := bstep (se 1 (by rfl) ⟨219866, by rfl⟩ : syracuseStep 293155 = 439733) B439733
theorem B293171 : Blo 291829 293171 := bstep (se 1 (by rfl) ⟨219878, by rfl⟩ : syracuseStep 293171 = 439757) B439757
theorem B555331 : Blo 291829 555331 := bstep (se 1 (by rfl) ⟨416498, by rfl⟩ : syracuseStep 555331 = 832997) B832997
theorem B293187 : Blo 291829 293187 := bstep (se 1 (by rfl) ⟨219890, by rfl⟩ : syracuseStep 293187 = 439781) B439781
theorem B293203 : Blo 291829 293203 := bstep (se 1 (by rfl) ⟨219902, by rfl⟩ : syracuseStep 293203 = 439805) B439805
theorem B293219 : Blo 291829 293219 := bstep (se 1 (by rfl) ⟨219914, by rfl⟩ : syracuseStep 293219 = 439829) B439829
theorem B293235 : Blo 291829 293235 := bstep (se 1 (by rfl) ⟨219926, by rfl⟩ : syracuseStep 293235 = 439853) B439853
theorem B293251 : Blo 291829 293251 := bstep (se 1 (by rfl) ⟨219938, by rfl⟩ : syracuseStep 293251 = 439877) B439877
theorem B293267 : Blo 291829 293267 := bstep (se 1 (by rfl) ⟨219950, by rfl⟩ : syracuseStep 293267 = 439901) B439901
theorem B293283 : Blo 291829 293283 := bstep (se 1 (by rfl) ⟨219962, by rfl⟩ : syracuseStep 293283 = 439925) B439925
theorem B293299 : Blo 291829 293299 := bstep (se 1 (by rfl) ⟨219974, by rfl⟩ : syracuseStep 293299 = 439949) B439949
theorem B293315 : Blo 291829 293315 := bstep (se 1 (by rfl) ⟨219986, by rfl⟩ : syracuseStep 293315 = 439973) B439973
theorem B293331 : Blo 291829 293331 := bstep (se 1 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 293331 = 439997) B439997
theorem B555491 : Blo 291829 555491 := bstep (se 1 (by rfl) ⟨416618, by rfl⟩ : syracuseStep 555491 = 833237) B833237
theorem B293347 : Blo 291829 293347 := bstep (se 1 (by rfl) ⟨220010, by rfl⟩ : syracuseStep 293347 = 440021) B440021
theorem B1112561 : Blo 291829 1112561 := bstep (se 2 (by rfl) ⟨417210, by rfl⟩ : syracuseStep 1112561 = 834421) B834421
theorem B293363 : Blo 291829 293363 := bstep (se 1 (by rfl) ⟨220022, by rfl⟩ : syracuseStep 293363 = 440045) B440045
theorem B293379 : Blo 291829 293379 := bstep (se 1 (by rfl) ⟨220034, by rfl⟩ : syracuseStep 293379 = 440069) B440069
theorem B293395 : Blo 291829 293395 := bstep (se 1 (by rfl) ⟨220046, by rfl⟩ : syracuseStep 293395 = 440093) B440093
theorem B293411 : Blo 291829 293411 := bstep (se 1 (by rfl) ⟨220058, by rfl⟩ : syracuseStep 293411 = 440117) B440117
theorem B293427 : Blo 291829 293427 := bstep (se 1 (by rfl) ⟨220070, by rfl⟩ : syracuseStep 293427 = 440141) B440141
theorem B293443 : Blo 291829 293443 := bstep (se 1 (by rfl) ⟨220082, by rfl⟩ : syracuseStep 293443 = 440165) B440165
theorem B293459 : Blo 291829 293459 := bstep (se 1 (by rfl) ⟨220094, by rfl⟩ : syracuseStep 293459 = 440189) B440189
theorem B293475 : Blo 291829 293475 := bstep (se 1 (by rfl) ⟨220106, by rfl⟩ : syracuseStep 293475 = 440213) B440213
theorem B293491 : Blo 291829 293491 := bstep (se 1 (by rfl) ⟨220118, by rfl⟩ : syracuseStep 293491 = 440237) B440237
theorem B293507 : Blo 291829 293507 := bstep (se 1 (by rfl) ⟨220130, by rfl⟩ : syracuseStep 293507 = 440261) B440261
theorem B293523 : Blo 291829 293523 := bstep (se 1 (by rfl) ⟨220142, by rfl⟩ : syracuseStep 293523 = 440285) B440285
theorem B293539 : Blo 291829 293539 := bstep (se 1 (by rfl) ⟨220154, by rfl⟩ : syracuseStep 293539 = 440309) B440309
theorem B1145507 : Blo 291829 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B293555 : Blo 291829 293555 := bstep (se 1 (by rfl) ⟨220166, by rfl⟩ : syracuseStep 293555 = 440333) B440333
theorem B293571 : Blo 291829 293571 := bstep (se 1 (by rfl) ⟨220178, by rfl⟩ : syracuseStep 293571 = 440357) B440357
theorem B293587 : Blo 291829 293587 := bstep (se 1 (by rfl) ⟨220190, by rfl⟩ : syracuseStep 293587 = 440381) B440381
theorem B293603 : Blo 291829 293603 := bstep (se 1 (by rfl) ⟨220202, by rfl⟩ : syracuseStep 293603 = 440405) B440405
theorem B293619 : Blo 291829 293619 := bstep (se 1 (by rfl) ⟨220214, by rfl⟩ : syracuseStep 293619 = 440429) B440429
theorem B293635 : Blo 291829 293635 := bstep (se 1 (by rfl) ⟨220226, by rfl⟩ : syracuseStep 293635 = 440453) B440453
theorem B293651 : Blo 291829 293651 := bstep (se 1 (by rfl) ⟨220238, by rfl⟩ : syracuseStep 293651 = 440477) B440477
theorem B293667 : Blo 291829 293667 := bstep (se 1 (by rfl) ⟨220250, by rfl⟩ : syracuseStep 293667 = 440501) B440501
theorem B293683 : Blo 291829 293683 := bstep (se 1 (by rfl) ⟨220262, by rfl⟩ : syracuseStep 293683 = 440525) B440525
theorem B293699 : Blo 291829 293699 := bstep (se 1 (by rfl) ⟨220274, by rfl⟩ : syracuseStep 293699 = 440549) B440549
theorem B293715 : Blo 291829 293715 := bstep (se 1 (by rfl) ⟨220286, by rfl⟩ : syracuseStep 293715 = 440573) B440573
theorem B293731 : Blo 291829 293731 := bstep (se 1 (by rfl) ⟨220298, by rfl⟩ : syracuseStep 293731 = 440597) B440597
theorem B293747 : Blo 291829 293747 := bstep (se 1 (by rfl) ⟨220310, by rfl⟩ : syracuseStep 293747 = 440621) B440621
theorem B293763 : Blo 291829 293763 := bstep (se 1 (by rfl) ⟨220322, by rfl⟩ : syracuseStep 293763 = 440645) B440645
theorem B293779 : Blo 291829 293779 := bstep (se 1 (by rfl) ⟨220334, by rfl⟩ : syracuseStep 293779 = 440669) B440669
theorem B293795 : Blo 291829 293795 := bstep (se 1 (by rfl) ⟨220346, by rfl⟩ : syracuseStep 293795 = 440693) B440693
theorem B293811 : Blo 291829 293811 := bstep (se 1 (by rfl) ⟨220358, by rfl⟩ : syracuseStep 293811 = 440717) B440717
theorem B293827 : Blo 291829 293827 := bstep (se 1 (by rfl) ⟨220370, by rfl⟩ : syracuseStep 293827 = 440741) B440741
theorem B293843 : Blo 291829 293843 := bstep (se 1 (by rfl) ⟨220382, by rfl⟩ : syracuseStep 293843 = 440765) B440765
theorem B293859 : Blo 291829 293859 := bstep (se 1 (by rfl) ⟨220394, by rfl⟩ : syracuseStep 293859 = 440789) B440789
theorem B293875 : Blo 291829 293875 := bstep (se 1 (by rfl) ⟨220406, by rfl⟩ : syracuseStep 293875 = 440813) B440813
theorem B293891 : Blo 291829 293891 := bstep (se 1 (by rfl) ⟨220418, by rfl⟩ : syracuseStep 293891 = 440837) B440837
theorem B293907 : Blo 291829 293907 := bstep (se 1 (by rfl) ⟨220430, by rfl⟩ : syracuseStep 293907 = 440861) B440861
theorem B293923 : Blo 291829 293923 := bstep (se 1 (by rfl) ⟨220442, by rfl⟩ : syracuseStep 293923 = 440885) B440885
theorem B293939 : Blo 291829 293939 := bstep (se 1 (by rfl) ⟨220454, by rfl⟩ : syracuseStep 293939 = 440909) B440909
theorem B293955 : Blo 291829 293955 := bstep (se 1 (by rfl) ⟨220466, by rfl⟩ : syracuseStep 293955 = 440933) B440933
theorem B1997893 : Blo 291829 1997893 := bstep (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) B374605
theorem B293971 : Blo 291829 293971 := bstep (se 1 (by rfl) ⟨220478, by rfl⟩ : syracuseStep 293971 = 440957) B440957
theorem B293987 : Blo 291829 293987 := bstep (se 1 (by rfl) ⟨220490, by rfl⟩ : syracuseStep 293987 = 440981) B440981
theorem B719971 : Blo 291829 719971 := bstep (se 1 (by rfl) ⟨539978, by rfl⟩ : syracuseStep 719971 = 1079957) B1079957
theorem B294003 : Blo 291829 294003 := bstep (se 1 (by rfl) ⟨220502, by rfl⟩ : syracuseStep 294003 = 441005) B441005
theorem B294019 : Blo 291829 294019 := bstep (se 1 (by rfl) ⟨220514, by rfl⟩ : syracuseStep 294019 = 441029) B441029
theorem B294035 : Blo 291829 294035 := bstep (se 1 (by rfl) ⟨220526, by rfl⟩ : syracuseStep 294035 = 441053) B441053
theorem B294051 : Blo 291829 294051 := bstep (se 1 (by rfl) ⟨220538, by rfl⟩ : syracuseStep 294051 = 441077) B441077
theorem B1670321 : Blo 291829 1670321 := bstep (se 2 (by rfl) ⟨626370, by rfl⟩ : syracuseStep 1670321 = 1252741) B1252741
theorem B294067 : Blo 291829 294067 := bstep (se 1 (by rfl) ⟨220550, by rfl⟩ : syracuseStep 294067 = 441101) B441101
theorem B294083 : Blo 291829 294083 := bstep (se 1 (by rfl) ⟨220562, by rfl⟩ : syracuseStep 294083 = 441125) B441125
theorem B294099 : Blo 291829 294099 := bstep (se 1 (by rfl) ⟨220574, by rfl⟩ : syracuseStep 294099 = 441149) B441149
theorem B294115 : Blo 291829 294115 := bstep (se 1 (by rfl) ⟨220586, by rfl⟩ : syracuseStep 294115 = 441173) B441173
theorem B294131 : Blo 291829 294131 := bstep (se 1 (by rfl) ⟨220598, by rfl⟩ : syracuseStep 294131 = 441197) B441197
theorem B294147 : Blo 291829 294147 := bstep (se 1 (by rfl) ⟨220610, by rfl⟩ : syracuseStep 294147 = 441221) B441221
theorem B294163 : Blo 291829 294163 := bstep (se 1 (by rfl) ⟨220622, by rfl⟩ : syracuseStep 294163 = 441245) B441245
theorem B294179 : Blo 291829 294179 := bstep (se 1 (by rfl) ⟨220634, by rfl⟩ : syracuseStep 294179 = 441269) B441269
theorem B294195 : Blo 291829 294195 := bstep (se 1 (by rfl) ⟨220646, by rfl⟩ : syracuseStep 294195 = 441293) B441293
theorem B294211 : Blo 291829 294211 := bstep (se 1 (by rfl) ⟨220658, by rfl⟩ : syracuseStep 294211 = 441317) B441317
theorem B294227 : Blo 291829 294227 := bstep (se 1 (by rfl) ⟨220670, by rfl⟩ : syracuseStep 294227 = 441341) B441341
theorem B294243 : Blo 291829 294243 := bstep (se 1 (by rfl) ⟨220682, by rfl⟩ : syracuseStep 294243 = 441365) B441365
theorem B294259 : Blo 291829 294259 := bstep (se 1 (by rfl) ⟨220694, by rfl⟩ : syracuseStep 294259 = 441389) B441389
theorem B294275 : Blo 291829 294275 := bstep (se 1 (by rfl) ⟨220706, by rfl⟩ : syracuseStep 294275 = 441413) B441413
theorem B294291 : Blo 291829 294291 := bstep (se 1 (by rfl) ⟨220718, by rfl⟩ : syracuseStep 294291 = 441437) B441437
theorem B294307 : Blo 291829 294307 := bstep (se 1 (by rfl) ⟨220730, by rfl⟩ : syracuseStep 294307 = 441461) B441461
theorem B294323 : Blo 291829 294323 := bstep (se 1 (by rfl) ⟨220742, by rfl⟩ : syracuseStep 294323 = 441485) B441485
theorem B294339 : Blo 291829 294339 := bstep (se 1 (by rfl) ⟨220754, by rfl⟩ : syracuseStep 294339 = 441509) B441509
theorem B294355 : Blo 291829 294355 := bstep (se 1 (by rfl) ⟨220766, by rfl⟩ : syracuseStep 294355 = 441533) B441533
theorem B294371 : Blo 291829 294371 := bstep (se 1 (by rfl) ⟨220778, by rfl⟩ : syracuseStep 294371 = 441557) B441557
theorem B294387 : Blo 291829 294387 := bstep (se 1 (by rfl) ⟨220790, by rfl⟩ : syracuseStep 294387 = 441581) B441581
theorem B294403 : Blo 291829 294403 := bstep (se 1 (by rfl) ⟨220802, by rfl⟩ : syracuseStep 294403 = 441605) B441605
theorem B556561 : Blo 291829 556561 := bstep (se 2 (by rfl) ⟨208710, by rfl⟩ : syracuseStep 556561 = 417421) B417421
theorem B294419 : Blo 291829 294419 := bstep (se 1 (by rfl) ⟨220814, by rfl⟩ : syracuseStep 294419 = 441629) B441629
theorem B294435 : Blo 291829 294435 := bstep (se 1 (by rfl) ⟨220826, by rfl⟩ : syracuseStep 294435 = 441653) B441653
theorem B294451 : Blo 291829 294451 := bstep (se 1 (by rfl) ⟨220838, by rfl⟩ : syracuseStep 294451 = 441677) B441677
theorem B294467 : Blo 291829 294467 := bstep (se 1 (by rfl) ⟨220850, by rfl⟩ : syracuseStep 294467 = 441701) B441701
theorem B294483 : Blo 291829 294483 := bstep (se 1 (by rfl) ⟨220862, by rfl⟩ : syracuseStep 294483 = 441725) B441725
theorem B294499 : Blo 291829 294499 := bstep (se 1 (by rfl) ⟨220874, by rfl⟩ : syracuseStep 294499 = 441749) B441749
theorem B294515 : Blo 291829 294515 := bstep (se 1 (by rfl) ⟨220886, by rfl⟩ : syracuseStep 294515 = 441773) B441773
theorem B294531 : Blo 291829 294531 := bstep (se 1 (by rfl) ⟨220898, by rfl⟩ : syracuseStep 294531 = 441797) B441797
theorem B294547 : Blo 291829 294547 := bstep (se 1 (by rfl) ⟨220910, by rfl⟩ : syracuseStep 294547 = 441821) B441821
theorem B294563 : Blo 291829 294563 := bstep (se 1 (by rfl) ⟨220922, by rfl⟩ : syracuseStep 294563 = 441845) B441845
theorem B294579 : Blo 291829 294579 := bstep (se 1 (by rfl) ⟨220934, by rfl⟩ : syracuseStep 294579 = 441869) B441869
theorem B294595 : Blo 291829 294595 := bstep (se 1 (by rfl) ⟨220946, by rfl⟩ : syracuseStep 294595 = 441893) B441893
theorem B294611 : Blo 291829 294611 := bstep (se 1 (by rfl) ⟨220958, by rfl⟩ : syracuseStep 294611 = 441917) B441917
theorem B294627 : Blo 291829 294627 := bstep (se 1 (by rfl) ⟨220970, by rfl⟩ : syracuseStep 294627 = 441941) B441941
theorem B294643 : Blo 291829 294643 := bstep (se 1 (by rfl) ⟨220982, by rfl⟩ : syracuseStep 294643 = 441965) B441965
theorem B294659 : Blo 291829 294659 := bstep (se 1 (by rfl) ⟨220994, by rfl⟩ : syracuseStep 294659 = 441989) B441989
theorem B294675 : Blo 291829 294675 := bstep (se 1 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 294675 = 442013) B442013
theorem B294691 : Blo 291829 294691 := bstep (se 1 (by rfl) ⟨221018, by rfl⟩ : syracuseStep 294691 = 442037) B442037
theorem B294707 : Blo 291829 294707 := bstep (se 1 (by rfl) ⟨221030, by rfl⟩ : syracuseStep 294707 = 442061) B442061
theorem B294723 : Blo 291829 294723 := bstep (se 1 (by rfl) ⟨221042, by rfl⟩ : syracuseStep 294723 = 442085) B442085
theorem B294739 : Blo 291829 294739 := bstep (se 1 (by rfl) ⟨221054, by rfl⟩ : syracuseStep 294739 = 442109) B442109
theorem B294755 : Blo 291829 294755 := bstep (se 1 (by rfl) ⟨221066, by rfl⟩ : syracuseStep 294755 = 442133) B442133
theorem B294771 : Blo 291829 294771 := bstep (se 1 (by rfl) ⟨221078, by rfl⟩ : syracuseStep 294771 = 442157) B442157
theorem B294787 : Blo 291829 294787 := bstep (se 1 (by rfl) ⟨221090, by rfl⟩ : syracuseStep 294787 = 442181) B442181
theorem B294803 : Blo 291829 294803 := bstep (se 1 (by rfl) ⟨221102, by rfl⟩ : syracuseStep 294803 = 442205) B442205
theorem B1114019 : Blo 291829 1114019 := bstep (se 1 (by rfl) ⟨835514, by rfl⟩ : syracuseStep 1114019 = 1671029) B1671029
theorem B294819 : Blo 291829 294819 := bstep (se 1 (by rfl) ⟨221114, by rfl⟩ : syracuseStep 294819 = 442229) B442229
theorem B1114033 : Blo 291829 1114033 := bstep (se 2 (by rfl) ⟨417762, by rfl⟩ : syracuseStep 1114033 = 835525) B835525
theorem B294835 : Blo 291829 294835 := bstep (se 1 (by rfl) ⟨221126, by rfl⟩ : syracuseStep 294835 = 442253) B442253
theorem B294851 : Blo 291829 294851 := bstep (se 1 (by rfl) ⟨221138, by rfl⟩ : syracuseStep 294851 = 442277) B442277
theorem B851917 : Blo 291829 851917 := bstep (se 3 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 851917 = 319469) B319469
theorem B294867 : Blo 291829 294867 := bstep (se 1 (by rfl) ⟨221150, by rfl⟩ : syracuseStep 294867 = 442301) B442301
theorem B1343459 : Blo 291829 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B294883 : Blo 291829 294883 := bstep (se 1 (by rfl) ⟨221162, by rfl⟩ : syracuseStep 294883 = 442325) B442325
theorem B294899 : Blo 291829 294899 := bstep (se 1 (by rfl) ⟨221174, by rfl⟩ : syracuseStep 294899 = 442349) B442349
theorem B294923 : Blo 291829 294923 := bstep (se 1 (by rfl) ⟨221192, by rfl⟩ : syracuseStep 294923 = 442385) B442385
theorem B294935 : Blo 291829 294935 := bstep (se 1 (by rfl) ⟨221201, by rfl⟩ : syracuseStep 294935 = 442403) B442403
theorem B294955 : Blo 291829 294955 := bstep (se 1 (by rfl) ⟨221216, by rfl⟩ : syracuseStep 294955 = 442433) B442433
theorem B294967 : Blo 291829 294967 := bstep (se 1 (by rfl) ⟨221225, by rfl⟩ : syracuseStep 294967 = 442451) B442451
theorem B557131 : Blo 291829 557131 := bstep (se 1 (by rfl) ⟨417848, by rfl⟩ : syracuseStep 557131 = 835697) B835697
theorem B294987 : Blo 291829 294987 := bstep (se 1 (by rfl) ⟨221240, by rfl⟩ : syracuseStep 294987 = 442481) B442481
theorem B294999 : Blo 291829 294999 := bstep (se 1 (by rfl) ⟨221249, by rfl⟩ : syracuseStep 294999 = 442499) B442499
theorem B295019 : Blo 291829 295019 := bstep (se 1 (by rfl) ⟨221264, by rfl⟩ : syracuseStep 295019 = 442529) B442529
theorem B295031 : Blo 291829 295031 := bstep (se 1 (by rfl) ⟨221273, by rfl⟩ : syracuseStep 295031 = 442547) B442547
theorem B295051 : Blo 291829 295051 := bstep (se 1 (by rfl) ⟨221288, by rfl⟩ : syracuseStep 295051 = 442577) B442577
theorem B295063 : Blo 291829 295063 := bstep (se 1 (by rfl) ⟨221297, by rfl⟩ : syracuseStep 295063 = 442595) B442595
theorem B295083 : Blo 291829 295083 := bstep (se 1 (by rfl) ⟨221312, by rfl⟩ : syracuseStep 295083 = 442625) B442625
theorem B295095 : Blo 291829 295095 := bstep (se 1 (by rfl) ⟨221321, by rfl⟩ : syracuseStep 295095 = 442643) B442643
theorem B295115 : Blo 291829 295115 := bstep (se 1 (by rfl) ⟨221336, by rfl⟩ : syracuseStep 295115 = 442673) B442673
theorem B295127 : Blo 291829 295127 := bstep (se 1 (by rfl) ⟨221345, by rfl⟩ : syracuseStep 295127 = 442691) B442691
theorem B295147 : Blo 291829 295147 := bstep (se 1 (by rfl) ⟨221360, by rfl⟩ : syracuseStep 295147 = 442721) B442721
theorem B295159 : Blo 291829 295159 := bstep (se 1 (by rfl) ⟨221369, by rfl⟩ : syracuseStep 295159 = 442739) B442739
theorem B295179 : Blo 291829 295179 := bstep (se 1 (by rfl) ⟨221384, by rfl⟩ : syracuseStep 295179 = 442769) B442769
theorem B295191 : Blo 291829 295191 := bstep (se 1 (by rfl) ⟨221393, by rfl⟩ : syracuseStep 295191 = 442787) B442787
theorem B295211 : Blo 291829 295211 := bstep (se 1 (by rfl) ⟨221408, by rfl⟩ : syracuseStep 295211 = 442817) B442817
theorem B295223 : Blo 291829 295223 := bstep (se 1 (by rfl) ⟨221417, by rfl⟩ : syracuseStep 295223 = 442835) B442835
theorem B295243 : Blo 291829 295243 := bstep (se 1 (by rfl) ⟨221432, by rfl⟩ : syracuseStep 295243 = 442865) B442865
theorem B295255 : Blo 291829 295255 := bstep (se 1 (by rfl) ⟨221441, by rfl⟩ : syracuseStep 295255 = 442883) B442883
theorem B295275 : Blo 291829 295275 := bstep (se 1 (by rfl) ⟨221456, by rfl⟩ : syracuseStep 295275 = 442913) B442913
theorem B295287 : Blo 291829 295287 := bstep (se 1 (by rfl) ⟨221465, by rfl⟩ : syracuseStep 295287 = 442931) B442931
theorem B295307 : Blo 291829 295307 := bstep (se 1 (by rfl) ⟨221480, by rfl⟩ : syracuseStep 295307 = 442961) B442961
theorem B1114519 : Blo 291829 1114519 := bstep (se 1 (by rfl) ⟨835889, by rfl⟩ : syracuseStep 1114519 = 1671779) B1671779
theorem B295319 : Blo 291829 295319 := bstep (se 1 (by rfl) ⟨221489, by rfl⟩ : syracuseStep 295319 = 442979) B442979
theorem B295339 : Blo 291829 295339 := bstep (se 1 (by rfl) ⟨221504, by rfl⟩ : syracuseStep 295339 = 443009) B443009
theorem B295351 : Blo 291829 295351 := bstep (se 1 (by rfl) ⟨221513, by rfl⟩ : syracuseStep 295351 = 443027) B443027
theorem B295371 : Blo 291829 295371 := bstep (se 1 (by rfl) ⟨221528, by rfl⟩ : syracuseStep 295371 = 443057) B443057
theorem B295383 : Blo 291829 295383 := bstep (se 1 (by rfl) ⟨221537, by rfl⟩ : syracuseStep 295383 = 443075) B443075
theorem B295403 : Blo 291829 295403 := bstep (se 1 (by rfl) ⟨221552, by rfl⟩ : syracuseStep 295403 = 443105) B443105
theorem B295415 : Blo 291829 295415 := bstep (se 1 (by rfl) ⟨221561, by rfl⟩ : syracuseStep 295415 = 443123) B443123
theorem B557579 : Blo 291829 557579 := bstep (se 1 (by rfl) ⟨418184, by rfl⟩ : syracuseStep 557579 = 836369) B836369
theorem B295435 : Blo 291829 295435 := bstep (se 1 (by rfl) ⟨221576, by rfl⟩ : syracuseStep 295435 = 443153) B443153
theorem B295447 : Blo 291829 295447 := bstep (se 1 (by rfl) ⟨221585, by rfl⟩ : syracuseStep 295447 = 443171) B443171
theorem B295467 : Blo 291829 295467 := bstep (se 1 (by rfl) ⟨221600, by rfl⟩ : syracuseStep 295467 = 443201) B443201
theorem B295479 : Blo 291829 295479 := bstep (se 1 (by rfl) ⟨221609, by rfl⟩ : syracuseStep 295479 = 443219) B443219
theorem B295499 : Blo 291829 295499 := bstep (se 1 (by rfl) ⟨221624, by rfl⟩ : syracuseStep 295499 = 443249) B443249
theorem B295511 : Blo 291829 295511 := bstep (se 1 (by rfl) ⟨221633, by rfl⟩ : syracuseStep 295511 = 443267) B443267
theorem B295531 : Blo 291829 295531 := bstep (se 1 (by rfl) ⟨221648, by rfl⟩ : syracuseStep 295531 = 443297) B443297
theorem B295543 : Blo 291829 295543 := bstep (se 1 (by rfl) ⟨221657, by rfl⟩ : syracuseStep 295543 = 443315) B443315
theorem B295563 : Blo 291829 295563 := bstep (se 1 (by rfl) ⟨221672, by rfl⟩ : syracuseStep 295563 = 443345) B443345
theorem B4784791 : Blo 291829 4784791 := bstep (se 1 (by rfl) ⟨3588593, by rfl⟩ : syracuseStep 4784791 = 7177187) B7177187
theorem B295575 : Blo 291829 295575 := bstep (se 1 (by rfl) ⟨221681, by rfl⟩ : syracuseStep 295575 = 443363) B443363
theorem B2130583 : Blo 291829 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B295595 : Blo 291829 295595 := bstep (se 1 (by rfl) ⟨221696, by rfl⟩ : syracuseStep 295595 = 443393) B443393
theorem B295607 : Blo 291829 295607 := bstep (se 1 (by rfl) ⟨221705, by rfl⟩ : syracuseStep 295607 = 443411) B443411
theorem B557761 : Blo 291829 557761 := bstep (se 2 (by rfl) ⟨209160, by rfl⟩ : syracuseStep 557761 = 418321) B418321
theorem B295627 : Blo 291829 295627 := bstep (se 1 (by rfl) ⟨221720, by rfl⟩ : syracuseStep 295627 = 443441) B443441
theorem B295639 : Blo 291829 295639 := bstep (se 1 (by rfl) ⟨221729, by rfl⟩ : syracuseStep 295639 = 443459) B443459
theorem B295659 : Blo 291829 295659 := bstep (se 1 (by rfl) ⟨221744, by rfl⟩ : syracuseStep 295659 = 443489) B443489
theorem B295671 : Blo 291829 295671 := bstep (se 1 (by rfl) ⟨221753, by rfl⟩ : syracuseStep 295671 = 443507) B443507
theorem B328459 : Blo 291829 328459 := bstep (se 1 (by rfl) ⟨246344, by rfl⟩ : syracuseStep 328459 = 492689) B492689
theorem B295691 : Blo 291829 295691 := bstep (se 1 (by rfl) ⟨221768, by rfl⟩ : syracuseStep 295691 = 443537) B443537
theorem B295703 : Blo 291829 295703 := bstep (se 1 (by rfl) ⟨221777, by rfl⟩ : syracuseStep 295703 = 443555) B443555
theorem B295723 : Blo 291829 295723 := bstep (se 1 (by rfl) ⟨221792, by rfl⟩ : syracuseStep 295723 = 443585) B443585
theorem B295735 : Blo 291829 295735 := bstep (se 1 (by rfl) ⟨221801, by rfl⟩ : syracuseStep 295735 = 443603) B443603
theorem B295755 : Blo 291829 295755 := bstep (se 1 (by rfl) ⟨221816, by rfl⟩ : syracuseStep 295755 = 443633) B443633
theorem B295767 : Blo 291829 295767 := bstep (se 1 (by rfl) ⟨221825, by rfl⟩ : syracuseStep 295767 = 443651) B443651
theorem B295787 : Blo 291829 295787 := bstep (se 1 (by rfl) ⟨221840, by rfl⟩ : syracuseStep 295787 = 443681) B443681
theorem B328567 : Blo 291829 328567 := bstep (se 1 (by rfl) ⟨246425, by rfl⟩ : syracuseStep 328567 = 492851) B492851
theorem B295799 : Blo 291829 295799 := bstep (se 1 (by rfl) ⟨221849, by rfl⟩ : syracuseStep 295799 = 443699) B443699
theorem B295819 : Blo 291829 295819 := bstep (se 1 (by rfl) ⟨221864, by rfl⟩ : syracuseStep 295819 = 443729) B443729
theorem B558103 : Blo 291829 558103 := bstep (se 1 (by rfl) ⟨418577, by rfl⟩ : syracuseStep 558103 = 837155) B837155
theorem B328747 : Blo 291829 328747 := bstep (se 1 (by rfl) ⟨246560, by rfl⟩ : syracuseStep 328747 = 493121) B493121
theorem B2688065 : Blo 291829 2688065 := bstep (se 2 (by rfl) ⟨1008024, by rfl⟩ : syracuseStep 2688065 = 2016049) B2016049
theorem B623705 : Blo 291829 623705 := bstep (se 2 (by rfl) ⟨233889, by rfl⟩ : syracuseStep 623705 = 467779) B467779
theorem B328855 : Blo 291829 328855 := bstep (se 1 (by rfl) ⟨246641, by rfl⟩ : syracuseStep 328855 = 493283) B493283
theorem B1115309 : Blo 291829 1115309 := bstep (se 3 (by rfl) ⟨209120, by rfl⟩ : syracuseStep 1115309 = 418241) B418241
theorem B558323 : Blo 291829 558323 := bstep (se 1 (by rfl) ⟨418742, by rfl⟩ : syracuseStep 558323 = 837485) B837485
theorem B329035 : Blo 291829 329035 := bstep (se 1 (by rfl) ⟨246776, by rfl⟩ : syracuseStep 329035 = 493553) B493553
theorem B656729 : Blo 291829 656729 := bstep (se 2 (by rfl) ⟨246273, by rfl⟩ : syracuseStep 656729 = 492547) B492547
theorem B656819 : Blo 291829 656819 := bstep (se 1 (by rfl) ⟨492614, by rfl⟩ : syracuseStep 656819 = 985229) B985229
theorem B329143 : Blo 291829 329143 := bstep (se 1 (by rfl) ⟨246857, by rfl⟩ : syracuseStep 329143 = 493715) B493715
theorem B951755 : Blo 291829 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B656855 : Blo 291829 656855 := bstep (se 1 (by rfl) ⟨492641, by rfl⟩ : syracuseStep 656855 = 985283) B985283
theorem B558551 : Blo 291829 558551 := bstep (se 1 (by rfl) ⟨418913, by rfl⟩ : syracuseStep 558551 = 837827) B837827
theorem B624115 : Blo 291829 624115 := bstep (se 1 (by rfl) ⟨468086, by rfl⟩ : syracuseStep 624115 = 936173) B936173
theorem B493067 : Blo 291829 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B1410605 : Blo 291829 1410605 := bstep (se 3 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 1410605 = 528977) B528977
theorem B296503 : Blo 291829 296503 := bstep (se 1 (by rfl) ⟨222377, by rfl⟩ : syracuseStep 296503 = 444755) B444755
theorem B394841 : Blo 291829 394841 := bstep (se 2 (by rfl) ⟨148065, by rfl⟩ : syracuseStep 394841 = 296131) B296131
theorem B329323 : Blo 291829 329323 := bstep (se 1 (by rfl) ⟨246992, by rfl⟩ : syracuseStep 329323 = 493985) B493985
theorem B657035 : Blo 291829 657035 := bstep (se 1 (by rfl) ⟨492776, by rfl⟩ : syracuseStep 657035 = 985553) B985553
theorem B493195 : Blo 291829 493195 := bstep (se 1 (by rfl) ⟨369896, by rfl⟩ : syracuseStep 493195 = 739793) B739793
theorem B657089 : Blo 291829 657089 := bstep (se 2 (by rfl) ⟨246408, by rfl⟩ : syracuseStep 657089 = 492817) B492817
theorem B329431 : Blo 291829 329431 := bstep (se 1 (by rfl) ⟨247073, by rfl⟩ : syracuseStep 329431 = 494147) B494147
theorem B558809 : Blo 291829 558809 := bstep (se 2 (by rfl) ⟨209553, by rfl⟩ : syracuseStep 558809 = 419107) B419107
theorem B493337 : Blo 291829 493337 := bstep (se 2 (by rfl) ⟨185001, by rfl⟩ : syracuseStep 493337 = 370003) B370003
theorem B624449 : Blo 291829 624449 := bstep (se 2 (by rfl) ⟨234168, by rfl⟩ : syracuseStep 624449 = 468337) B468337
theorem B1247069 : Blo 291829 1247069 := bstep (se 3 (by rfl) ⟨233825, by rfl⟩ : syracuseStep 1247069 = 467651) B467651
theorem B329611 : Blo 291829 329611 := bstep (se 1 (by rfl) ⟨247208, by rfl⟩ : syracuseStep 329611 = 494417) B494417
theorem B657305 : Blo 291829 657305 := bstep (se 2 (by rfl) ⟨246489, by rfl⟩ : syracuseStep 657305 = 492979) B492979
theorem B493465 : Blo 291829 493465 := bstep (se 2 (by rfl) ⟨185049, by rfl⟩ : syracuseStep 493465 = 370099) B370099
theorem B657395 : Blo 291829 657395 := bstep (se 1 (by rfl) ⟨493046, by rfl⟩ : syracuseStep 657395 = 986093) B986093
theorem B329719 : Blo 291829 329719 := bstep (se 1 (by rfl) ⟨247289, by rfl⟩ : syracuseStep 329719 = 494579) B494579
theorem B657431 : Blo 291829 657431 := bstep (se 1 (by rfl) ⟨493073, by rfl⟩ : syracuseStep 657431 = 986147) B986147
theorem B559219 : Blo 291829 559219 := bstep (se 1 (by rfl) ⟨419414, by rfl⟩ : syracuseStep 559219 = 838829) B838829
theorem B1050769 : Blo 291829 1050769 := bstep (se 2 (by rfl) ⟨394038, by rfl⟩ : syracuseStep 1050769 = 788077) B788077
theorem B329899 : Blo 291829 329899 := bstep (se 1 (by rfl) ⟨247424, by rfl⟩ : syracuseStep 329899 = 494849) B494849
theorem B657611 : Blo 291829 657611 := bstep (se 1 (by rfl) ⟨493208, by rfl⟩ : syracuseStep 657611 = 986417) B986417
theorem B592115 : Blo 291829 592115 := bstep (se 1 (by rfl) ⟨444086, by rfl⟩ : syracuseStep 592115 = 888173) B888173
theorem B657665 : Blo 291829 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B330007 : Blo 291829 330007 := bstep (se 1 (by rfl) ⟨247505, by rfl⟩ : syracuseStep 330007 = 495011) B495011
theorem B526771 : Blo 291829 526771 := bstep (se 1 (by rfl) ⟨395078, by rfl⟩ : syracuseStep 526771 = 790157) B790157
theorem B330187 : Blo 291829 330187 := bstep (se 1 (by rfl) ⟨247640, by rfl⟩ : syracuseStep 330187 = 495281) B495281
theorem B494039 : Blo 291829 494039 := bstep (se 1 (by rfl) ⟨370529, by rfl⟩ : syracuseStep 494039 = 741059) B741059
theorem B657881 : Blo 291829 657881 := bstep (se 2 (by rfl) ⟨246705, by rfl⟩ : syracuseStep 657881 = 493411) B493411
theorem B625175 : Blo 291829 625175 := bstep (se 1 (by rfl) ⟨468881, by rfl⟩ : syracuseStep 625175 = 937763) B937763
theorem B657971 : Blo 291829 657971 := bstep (se 1 (by rfl) ⟨493478, by rfl⟩ : syracuseStep 657971 = 986957) B986957
theorem B330295 : Blo 291829 330295 := bstep (se 1 (by rfl) ⟨247721, by rfl⟩ : syracuseStep 330295 = 495443) B495443
theorem B1116737 : Blo 291829 1116737 := bstep (se 2 (by rfl) ⟨418776, by rfl⟩ : syracuseStep 1116737 = 837553) B837553
theorem B658007 : Blo 291829 658007 := bstep (se 1 (by rfl) ⟨493505, by rfl⟩ : syracuseStep 658007 = 987011) B987011
theorem B494167 : Blo 291829 494167 := bstep (se 1 (by rfl) ⟨370625, by rfl⟩ : syracuseStep 494167 = 741251) B741251
theorem B559705 : Blo 291829 559705 := bstep (se 2 (by rfl) ⟨209889, by rfl⟩ : syracuseStep 559705 = 419779) B419779
theorem B2722405 : Blo 291829 2722405 := bstep (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) B510451
theorem B1870553 : Blo 291829 1870553 := bstep (se 2 (by rfl) ⟨701457, by rfl⟩ : syracuseStep 1870553 = 1402915) B1402915
theorem B1673945 : Blo 291829 1673945 := bstep (se 2 (by rfl) ⟨627729, by rfl⟩ : syracuseStep 1673945 = 1255459) B1255459
theorem B330475 : Blo 291829 330475 := bstep (se 1 (by rfl) ⟨247856, by rfl⟩ : syracuseStep 330475 = 495713) B495713
theorem B658187 : Blo 291829 658187 := bstep (se 1 (by rfl) ⟨493640, by rfl⟩ : syracuseStep 658187 = 987281) B987281
theorem B658241 : Blo 291829 658241 := bstep (se 2 (by rfl) ⟨246840, by rfl⟩ : syracuseStep 658241 = 493681) B493681
theorem B985931 : Blo 291829 985931 := bstep (se 1 (by rfl) ⟨739448, by rfl⟩ : syracuseStep 985931 = 1478897) B1478897
theorem B330583 : Blo 291829 330583 := bstep (se 1 (by rfl) ⟨247937, by rfl⟩ : syracuseStep 330583 = 495875) B495875
theorem B5671781 : Blo 291829 5671781 := bstep (se 4 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 5671781 = 1063459) B1063459
theorem B330763 : Blo 291829 330763 := bstep (se 1 (by rfl) ⟨248072, by rfl⟩ : syracuseStep 330763 = 496145) B496145
theorem B658457 : Blo 291829 658457 := bstep (se 2 (by rfl) ⟨246921, by rfl⟩ : syracuseStep 658457 = 493843) B493843
theorem B986201 : Blo 291829 986201 := bstep (se 2 (by rfl) ⟨369825, by rfl⟩ : syracuseStep 986201 = 739651) B739651
theorem B658547 : Blo 291829 658547 := bstep (se 1 (by rfl) ⟨493910, by rfl⟩ : syracuseStep 658547 = 987821) B987821
theorem B330871 : Blo 291829 330871 := bstep (se 1 (by rfl) ⟨248153, by rfl⟩ : syracuseStep 330871 = 496307) B496307
theorem B1477763 : Blo 291829 1477763 := bstep (se 1 (by rfl) ⟨1108322, by rfl⟩ : syracuseStep 1477763 = 2216645) B2216645
theorem B560267 : Blo 291829 560267 := bstep (se 1 (by rfl) ⟨420200, by rfl⟩ : syracuseStep 560267 = 840401) B840401
theorem B658583 : Blo 291829 658583 := bstep (se 1 (by rfl) ⟨493937, by rfl⟩ : syracuseStep 658583 = 987875) B987875
theorem B494795 : Blo 291829 494795 := bstep (se 1 (by rfl) ⟨371096, by rfl⟩ : syracuseStep 494795 = 742193) B742193
theorem B331051 : Blo 291829 331051 := bstep (se 1 (by rfl) ⟨248288, by rfl⟩ : syracuseStep 331051 = 496577) B496577
theorem B560449 : Blo 291829 560449 := bstep (se 2 (by rfl) ⟨210168, by rfl⟩ : syracuseStep 560449 = 420337) B420337
theorem B658763 : Blo 291829 658763 := bstep (se 1 (by rfl) ⟨494072, by rfl⟩ : syracuseStep 658763 = 988145) B988145
theorem B494923 : Blo 291829 494923 := bstep (se 1 (by rfl) ⟨371192, by rfl⟩ : syracuseStep 494923 = 742385) B742385
theorem B658817 : Blo 291829 658817 := bstep (se 2 (by rfl) ⟨247056, by rfl⟩ : syracuseStep 658817 = 494113) B494113
theorem B331159 : Blo 291829 331159 := bstep (se 1 (by rfl) ⟨248369, by rfl⟩ : syracuseStep 331159 = 496739) B496739
theorem B527809 : Blo 291829 527809 := bstep (se 2 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 527809 = 395857) B395857
theorem B495065 : Blo 291829 495065 := bstep (se 2 (by rfl) ⟨185649, by rfl⟩ : syracuseStep 495065 = 371299) B371299
theorem B331339 : Blo 291829 331339 := bstep (se 1 (by rfl) ⟨248504, by rfl⟩ : syracuseStep 331339 = 497009) B497009
theorem B659033 : Blo 291829 659033 := bstep (se 2 (by rfl) ⟨247137, by rfl⟩ : syracuseStep 659033 = 494275) B494275
theorem B495193 : Blo 291829 495193 := bstep (se 2 (by rfl) ⟨185697, by rfl⟩ : syracuseStep 495193 = 371395) B371395
theorem B659123 : Blo 291829 659123 := bstep (se 1 (by rfl) ⟨494342, by rfl⟩ : syracuseStep 659123 = 988685) B988685
theorem B331447 : Blo 291829 331447 := bstep (se 1 (by rfl) ⟨248585, by rfl⟩ : syracuseStep 331447 = 497171) B497171
theorem B659159 : Blo 291829 659159 := bstep (se 1 (by rfl) ⟨494369, by rfl⟩ : syracuseStep 659159 = 988739) B988739
theorem B986903 : Blo 291829 986903 := bstep (se 1 (by rfl) ⟨740177, by rfl⟩ : syracuseStep 986903 = 1480355) B1480355
theorem B2494273 : Blo 291829 2494273 := bstep (se 2 (by rfl) ⟨935352, by rfl⟩ : syracuseStep 2494273 = 1870705) B1870705
theorem B331627 : Blo 291829 331627 := bstep (se 1 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 331627 = 497441) B497441
theorem B659339 : Blo 291829 659339 := bstep (se 1 (by rfl) ⟨494504, by rfl⟩ : syracuseStep 659339 = 989009) B989009
theorem B659393 : Blo 291829 659393 := bstep (se 2 (by rfl) ⟨247272, by rfl⟩ : syracuseStep 659393 = 494545) B494545
theorem B331735 : Blo 291829 331735 := bstep (se 1 (by rfl) ⟨248801, by rfl⟩ : syracuseStep 331735 = 497603) B497603
theorem B561163 : Blo 291829 561163 := bstep (se 1 (by rfl) ⟨420872, by rfl⟩ : syracuseStep 561163 = 841745) B841745
theorem B1118225 : Blo 291829 1118225 := bstep (se 2 (by rfl) ⟨419334, by rfl⟩ : syracuseStep 1118225 = 838669) B838669
theorem B2691089 : Blo 291829 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B561239 : Blo 291829 561239 := bstep (se 1 (by rfl) ⟨420929, by rfl⟩ : syracuseStep 561239 = 841859) B841859
theorem B331915 : Blo 291829 331915 := bstep (se 1 (by rfl) ⟨248936, by rfl⟩ : syracuseStep 331915 = 497873) B497873
theorem B495767 : Blo 291829 495767 := bstep (se 1 (by rfl) ⟨371825, by rfl⟩ : syracuseStep 495767 = 743651) B743651
theorem B659609 : Blo 291829 659609 := bstep (se 2 (by rfl) ⟨247353, by rfl⟩ : syracuseStep 659609 = 494707) B494707
theorem B659699 : Blo 291829 659699 := bstep (se 1 (by rfl) ⟨494774, by rfl⟩ : syracuseStep 659699 = 989549) B989549
theorem B332023 : Blo 291829 332023 := bstep (se 1 (by rfl) ⟨249017, by rfl⟩ : syracuseStep 332023 = 498035) B498035
theorem B659735 : Blo 291829 659735 := bstep (se 1 (by rfl) ⟨494801, by rfl⟩ : syracuseStep 659735 = 989603) B989603
theorem B495895 : Blo 291829 495895 := bstep (se 1 (by rfl) ⟨371921, by rfl⟩ : syracuseStep 495895 = 743843) B743843
theorem B987443 : Blo 291829 987443 := bstep (se 1 (by rfl) ⟨740582, by rfl⟩ : syracuseStep 987443 = 1481165) B1481165
theorem B1872193 : Blo 291829 1872193 := bstep (se 2 (by rfl) ⟨702072, by rfl⟩ : syracuseStep 1872193 = 1404145) B1404145
theorem B1249667 : Blo 291829 1249667 := bstep (se 1 (by rfl) ⟨937250, by rfl⟩ : syracuseStep 1249667 = 1874501) B1874501
theorem B332203 : Blo 291829 332203 := bstep (se 1 (by rfl) ⟨249152, by rfl⟩ : syracuseStep 332203 = 498305) B498305
theorem B659915 : Blo 291829 659915 := bstep (se 1 (by rfl) ⟨494936, by rfl⟩ : syracuseStep 659915 = 989873) B989873
theorem B1118681 : Blo 291829 1118681 := bstep (se 2 (by rfl) ⟨419505, by rfl⟩ : syracuseStep 1118681 = 839011) B839011
theorem B659969 : Blo 291829 659969 := bstep (se 2 (by rfl) ⟨247488, by rfl⟩ : syracuseStep 659969 = 494977) B494977
theorem B8458769 : Blo 291829 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B332311 : Blo 291829 332311 := bstep (se 1 (by rfl) ⟨249233, by rfl⟩ : syracuseStep 332311 = 498467) B498467
theorem B987713 : Blo 291829 987713 := bstep (se 2 (by rfl) ⟨370392, by rfl⟩ : syracuseStep 987713 = 740785) B740785
theorem B529049 : Blo 291829 529049 := bstep (se 2 (by rfl) ⟨198393, by rfl⟩ : syracuseStep 529049 = 396787) B396787
theorem B1118893 : Blo 291829 1118893 := bstep (se 3 (by rfl) ⟨209792, by rfl⟩ : syracuseStep 1118893 = 419585) B419585
theorem B332491 : Blo 291829 332491 := bstep (se 1 (by rfl) ⟨249368, by rfl⟩ : syracuseStep 332491 = 498737) B498737
theorem B660185 : Blo 291829 660185 := bstep (se 2 (by rfl) ⟨247569, by rfl⟩ : syracuseStep 660185 = 495139) B495139
theorem B660275 : Blo 291829 660275 := bstep (se 1 (by rfl) ⟨495206, by rfl⟩ : syracuseStep 660275 = 990413) B990413
theorem B332599 : Blo 291829 332599 := bstep (se 1 (by rfl) ⟨249449, by rfl⟩ : syracuseStep 332599 = 498899) B498899
theorem B660311 : Blo 291829 660311 := bstep (se 1 (by rfl) ⟨495233, by rfl⟩ : syracuseStep 660311 = 990467) B990467
theorem B3183461 : Blo 291829 3183461 := bstep (se 4 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 3183461 = 596899) B596899
theorem B496523 : Blo 291829 496523 := bstep (se 1 (by rfl) ⟨372392, by rfl⟩ : syracuseStep 496523 = 744785) B744785
theorem B627635 : Blo 291829 627635 := bstep (se 1 (by rfl) ⟨470726, by rfl⟩ : syracuseStep 627635 = 941453) B941453
theorem B1119197 : Blo 291829 1119197 := bstep (se 3 (by rfl) ⟨209849, by rfl⟩ : syracuseStep 1119197 = 419699) B419699
theorem B332779 : Blo 291829 332779 := bstep (se 1 (by rfl) ⟨249584, by rfl⟩ : syracuseStep 332779 = 499169) B499169
theorem B660491 : Blo 291829 660491 := bstep (se 1 (by rfl) ⟨495368, by rfl⟩ : syracuseStep 660491 = 990737) B990737
theorem B496651 : Blo 291829 496651 := bstep (se 1 (by rfl) ⟨372488, by rfl⟩ : syracuseStep 496651 = 744977) B744977
theorem B660545 : Blo 291829 660545 := bstep (se 2 (by rfl) ⟨247704, by rfl⟩ : syracuseStep 660545 = 495409) B495409
theorem B988253 : Blo 291829 988253 := bstep (se 3 (by rfl) ⟨185297, by rfl⟩ : syracuseStep 988253 = 370595) B370595
theorem B496793 : Blo 291829 496793 := bstep (se 2 (by rfl) ⟨186297, by rfl⟩ : syracuseStep 496793 = 372595) B372595
theorem B660761 : Blo 291829 660761 := bstep (se 2 (by rfl) ⟨247785, by rfl⟩ : syracuseStep 660761 = 495571) B495571
theorem B496921 : Blo 291829 496921 := bstep (se 2 (by rfl) ⟨186345, by rfl⟩ : syracuseStep 496921 = 372691) B372691
theorem B1676609 : Blo 291829 1676609 := bstep (se 2 (by rfl) ⟨628728, by rfl⟩ : syracuseStep 1676609 = 1257457) B1257457
theorem B660851 : Blo 291829 660851 := bstep (se 1 (by rfl) ⟨495638, by rfl⟩ : syracuseStep 660851 = 991277) B991277
theorem B333175 : Blo 291829 333175 := bstep (se 1 (by rfl) ⟨249881, by rfl⟩ : syracuseStep 333175 = 499763) B499763
theorem B660887 : Blo 291829 660887 := bstep (se 1 (by rfl) ⟨495665, by rfl⟩ : syracuseStep 660887 = 991331) B991331
theorem B890315 : Blo 291829 890315 := bstep (se 1 (by rfl) ⟨667736, by rfl⟩ : syracuseStep 890315 = 1335473) B1335473
theorem B4298275 : Blo 291829 4298275 := bstep (se 1 (by rfl) ⟨3223706, by rfl⟩ : syracuseStep 4298275 = 6447413) B6447413
theorem B661067 : Blo 291829 661067 := bstep (se 1 (by rfl) ⟨495800, by rfl⟩ : syracuseStep 661067 = 991601) B991601
theorem B661121 : Blo 291829 661121 := bstep (se 2 (by rfl) ⟨247920, by rfl⟩ : syracuseStep 661121 = 495841) B495841
theorem B497495 : Blo 291829 497495 := bstep (se 1 (by rfl) ⟨373121, by rfl⟩ : syracuseStep 497495 = 746243) B746243
theorem B563033 : Blo 291829 563033 := bstep (se 2 (by rfl) ⟨211137, by rfl⟩ : syracuseStep 563033 = 422275) B422275
theorem B661337 : Blo 291829 661337 := bstep (se 2 (by rfl) ⟨248001, by rfl⟩ : syracuseStep 661337 = 496003) B496003
theorem B3839845 : Blo 291829 3839845 := bstep (se 4 (by rfl) ⟨359985, by rfl⟩ : syracuseStep 3839845 = 719971) B719971
theorem B661427 : Blo 291829 661427 := bstep (se 1 (by rfl) ⟨496070, by rfl⟩ : syracuseStep 661427 = 992141) B992141
theorem B595927 : Blo 291829 595927 := bstep (se 1 (by rfl) ⟨446945, by rfl⟩ : syracuseStep 595927 = 893891) B893891
theorem B661463 : Blo 291829 661463 := bstep (se 1 (by rfl) ⟨496097, by rfl⟩ : syracuseStep 661463 = 992195) B992195
theorem B497623 : Blo 291829 497623 := bstep (se 1 (by rfl) ⟨373217, by rfl⟩ : syracuseStep 497623 = 746435) B746435
theorem B628823 : Blo 291829 628823 := bstep (se 1 (by rfl) ⟨471617, by rfl⟩ : syracuseStep 628823 = 943235) B943235
theorem B661643 : Blo 291829 661643 := bstep (se 1 (by rfl) ⟨496232, by rfl⟩ : syracuseStep 661643 = 992465) B992465
theorem B661697 : Blo 291829 661697 := bstep (se 2 (by rfl) ⟨248136, by rfl⟩ : syracuseStep 661697 = 496273) B496273
theorem B989387 : Blo 291829 989387 := bstep (se 1 (by rfl) ⟨742040, by rfl⟩ : syracuseStep 989387 = 1484081) B1484081
theorem B661913 : Blo 291829 661913 := bstep (se 2 (by rfl) ⟨248217, by rfl⟩ : syracuseStep 661913 = 496435) B496435
theorem B989657 : Blo 291829 989657 := bstep (se 2 (by rfl) ⟨371121, by rfl⟩ : syracuseStep 989657 = 742243) B742243
theorem B662003 : Blo 291829 662003 := bstep (se 1 (by rfl) ⟨496502, by rfl⟩ : syracuseStep 662003 = 993005) B993005
theorem B662039 : Blo 291829 662039 := bstep (se 1 (by rfl) ⟨496529, by rfl⟩ : syracuseStep 662039 = 993059) B993059
theorem B2103853 : Blo 291829 2103853 := bstep (se 3 (by rfl) ⟨394472, by rfl⟩ : syracuseStep 2103853 = 788945) B788945
theorem B4528709 : Blo 291829 4528709 := bstep (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) B849133
theorem B498251 : Blo 291829 498251 := bstep (se 1 (by rfl) ⟨373688, by rfl⟩ : syracuseStep 498251 = 747377) B747377
theorem B1252043 : Blo 291829 1252043 := bstep (se 1 (by rfl) ⟨939032, by rfl⟩ : syracuseStep 1252043 = 1878065) B1878065
theorem B662219 : Blo 291829 662219 := bstep (se 1 (by rfl) ⟨496664, by rfl⟩ : syracuseStep 662219 = 993329) B993329
theorem B498379 : Blo 291829 498379 := bstep (se 1 (by rfl) ⟨373784, by rfl⟩ : syracuseStep 498379 = 747569) B747569
theorem B662273 : Blo 291829 662273 := bstep (se 2 (by rfl) ⟨248352, by rfl⟩ : syracuseStep 662273 = 496705) B496705
theorem B531211 : Blo 291829 531211 := bstep (se 1 (by rfl) ⟨398408, by rfl⟩ : syracuseStep 531211 = 796817) B796817
theorem B1481489 : Blo 291829 1481489 := bstep (se 2 (by rfl) ⟨555558, by rfl⟩ : syracuseStep 1481489 = 1111117) B1111117
theorem B793433 : Blo 291829 793433 := bstep (se 2 (by rfl) ⟨297537, by rfl⟩ : syracuseStep 793433 = 595075) B595075
theorem B498521 : Blo 291829 498521 := bstep (se 2 (by rfl) ⟨186945, by rfl⟩ : syracuseStep 498521 = 373891) B373891
theorem B301963 : Blo 291829 301963 := bstep (se 1 (by rfl) ⟨226472, by rfl⟩ : syracuseStep 301963 = 452945) B452945
theorem B1481651 : Blo 291829 1481651 := bstep (se 1 (by rfl) ⟨1111238, by rfl⟩ : syracuseStep 1481651 = 2222477) B2222477
theorem B662489 : Blo 291829 662489 := bstep (se 2 (by rfl) ⟨248433, by rfl⟩ : syracuseStep 662489 = 496867) B496867
theorem B498649 : Blo 291829 498649 := bstep (se 2 (by rfl) ⟨186993, by rfl⟩ : syracuseStep 498649 = 373987) B373987
theorem B662579 : Blo 291829 662579 := bstep (se 1 (by rfl) ⟨496934, by rfl⟩ : syracuseStep 662579 = 993869) B993869
theorem B662615 : Blo 291829 662615 := bstep (se 1 (by rfl) ⟨496961, by rfl⟩ : syracuseStep 662615 = 993923) B993923
theorem B629849 : Blo 291829 629849 := bstep (se 2 (by rfl) ⟨236193, by rfl⟩ : syracuseStep 629849 = 472387) B472387
theorem B3054685 : Blo 291829 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B990359 : Blo 291829 990359 := bstep (se 1 (by rfl) ⟨742769, by rfl⟩ : syracuseStep 990359 = 1485539) B1485539
theorem B335063 : Blo 291829 335063 := bstep (se 1 (by rfl) ⟨251297, by rfl⟩ : syracuseStep 335063 = 502595) B502595
theorem B662795 : Blo 291829 662795 := bstep (se 1 (by rfl) ⟨497096, by rfl⟩ : syracuseStep 662795 = 994193) B994193
theorem B662849 : Blo 291829 662849 := bstep (se 2 (by rfl) ⟨248568, by rfl⟩ : syracuseStep 662849 = 497137) B497137
theorem B1121795 : Blo 291829 1121795 := bstep (se 1 (by rfl) ⟨841346, by rfl⟩ : syracuseStep 1121795 = 1682693) B1682693
theorem B1121809 : Blo 291829 1121809 := bstep (se 2 (by rfl) ⟨420678, by rfl⟩ : syracuseStep 1121809 = 841357) B841357
theorem B663065 : Blo 291829 663065 := bstep (se 2 (by rfl) ⟨248649, by rfl⟩ : syracuseStep 663065 = 497299) B497299
theorem B663155 : Blo 291829 663155 := bstep (se 1 (by rfl) ⟨497366, by rfl⟩ : syracuseStep 663155 = 994733) B994733
theorem B1253015 : Blo 291829 1253015 := bstep (se 1 (by rfl) ⟨939761, by rfl⟩ : syracuseStep 1253015 = 1879523) B1879523
theorem B663191 : Blo 291829 663191 := bstep (se 1 (by rfl) ⟨497393, by rfl⟩ : syracuseStep 663191 = 994787) B994787
theorem B990899 : Blo 291829 990899 := bstep (se 1 (by rfl) ⟨743174, by rfl⟩ : syracuseStep 990899 = 1486349) B1486349
theorem B2826049 : Blo 291829 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B1122113 : Blo 291829 1122113 := bstep (se 2 (by rfl) ⟨420792, by rfl⟩ : syracuseStep 1122113 = 841585) B841585
theorem B663371 : Blo 291829 663371 := bstep (se 1 (by rfl) ⟨497528, by rfl⟩ : syracuseStep 663371 = 995057) B995057
theorem B663425 : Blo 291829 663425 := bstep (se 2 (by rfl) ⟨248784, by rfl⟩ : syracuseStep 663425 = 497569) B497569
theorem B15998897 : Blo 291829 15998897 := bstep (se 2 (by rfl) ⟨5999586, by rfl⟩ : syracuseStep 15998897 = 11999173) B11999173
theorem B991169 : Blo 291829 991169 := bstep (se 2 (by rfl) ⟨371688, by rfl⟩ : syracuseStep 991169 = 743377) B743377
theorem B532531 : Blo 291829 532531 := bstep (se 1 (by rfl) ⟨399398, by rfl⟩ : syracuseStep 532531 = 798797) B798797
theorem B663641 : Blo 291829 663641 := bstep (se 2 (by rfl) ⟨248865, by rfl⟩ : syracuseStep 663641 = 497731) B497731
theorem B630899 : Blo 291829 630899 := bstep (se 1 (by rfl) ⟨473174, by rfl⟩ : syracuseStep 630899 = 946349) B946349
theorem B663731 : Blo 291829 663731 := bstep (se 1 (by rfl) ⟨497798, by rfl⟩ : syracuseStep 663731 = 995597) B995597
theorem B6037685 : Blo 291829 6037685 := bstep (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) B566033
theorem B663767 : Blo 291829 663767 := bstep (se 1 (by rfl) ⟨497825, by rfl⟩ : syracuseStep 663767 = 995651) B995651
theorem B1056989 : Blo 291829 1056989 := bstep (se 3 (by rfl) ⟨198185, by rfl⟩ : syracuseStep 1056989 = 396371) B396371
theorem B532825 : Blo 291829 532825 := bstep (se 2 (by rfl) ⟨199809, by rfl⟩ : syracuseStep 532825 = 399619) B399619
theorem B663947 : Blo 291829 663947 := bstep (se 1 (by rfl) ⟨497960, by rfl⟩ : syracuseStep 663947 = 995921) B995921
theorem B664001 : Blo 291829 664001 := bstep (se 2 (by rfl) ⟨249000, by rfl⟩ : syracuseStep 664001 = 498001) B498001
theorem B991709 : Blo 291829 991709 := bstep (se 3 (by rfl) ⟨185945, by rfl⟩ : syracuseStep 991709 = 371891) B371891
theorem B1122781 : Blo 291829 1122781 := bstep (se 3 (by rfl) ⟨210521, by rfl⟩ : syracuseStep 1122781 = 421043) B421043
theorem B532993 : Blo 291829 532993 := bstep (se 2 (by rfl) ⟨199872, by rfl⟩ : syracuseStep 532993 = 399745) B399745
theorem B598603 : Blo 291829 598603 := bstep (se 1 (by rfl) ⟨448952, by rfl⟩ : syracuseStep 598603 = 897905) B897905
theorem B664217 : Blo 291829 664217 := bstep (se 2 (by rfl) ⟨249081, by rfl⟩ : syracuseStep 664217 = 498163) B498163
theorem B631489 : Blo 291829 631489 := bstep (se 2 (by rfl) ⟨236808, by rfl⟩ : syracuseStep 631489 = 473617) B473617
theorem B369355 : Blo 291829 369355 := bstep (se 1 (by rfl) ⟨277016, by rfl⟩ : syracuseStep 369355 = 554033) B554033
theorem B664307 : Blo 291829 664307 := bstep (se 1 (by rfl) ⟨498230, by rfl⟩ : syracuseStep 664307 = 996461) B996461
theorem B664343 : Blo 291829 664343 := bstep (se 1 (by rfl) ⟨498257, by rfl⟩ : syracuseStep 664343 = 996515) B996515
theorem B2663243 : Blo 291829 2663243 := bstep (se 1 (by rfl) ⟨1997432, by rfl⟩ : syracuseStep 2663243 = 3994865) B3994865
theorem B1483595 : Blo 291829 1483595 := bstep (se 1 (by rfl) ⟨1112696, by rfl⟩ : syracuseStep 1483595 = 2225393) B2225393
theorem B664523 : Blo 291829 664523 := bstep (se 1 (by rfl) ⟨498392, by rfl⟩ : syracuseStep 664523 = 996785) B996785
theorem B294903 : Blo 291829 294903 := bstep (se 1 (by rfl) ⟨221177, by rfl⟩ : syracuseStep 294903 = 442355) B442355
theorem B369623 : Blo 291829 369623 := bstep (se 1 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 369623 = 554435) B554435
theorem B664577 : Blo 291829 664577 := bstep (se 2 (by rfl) ⟨249216, by rfl⟩ : syracuseStep 664577 = 498433) B498433
theorem B10298389 : Blo 291829 10298389 := bstep (se 6 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 10298389 = 482737) B482737
theorem B500951 : Blo 291829 500951 := bstep (se 1 (by rfl) ⟨375713, by rfl⟩ : syracuseStep 500951 = 751427) B751427
theorem B664793 : Blo 291829 664793 := bstep (se 2 (by rfl) ⟨249297, by rfl⟩ : syracuseStep 664793 = 498595) B498595
theorem B664883 : Blo 291829 664883 := bstep (se 1 (by rfl) ⟨498662, by rfl⟩ : syracuseStep 664883 = 997325) B997325
theorem B664919 : Blo 291829 664919 := bstep (se 1 (by rfl) ⟨498689, by rfl⟩ : syracuseStep 664919 = 997379) B997379
theorem B2663857 : Blo 291829 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B1058269 : Blo 291829 1058269 := bstep (se 3 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 1058269 = 396851) B396851
theorem B665099 : Blo 291829 665099 := bstep (se 1 (by rfl) ⟨498824, by rfl⟩ : syracuseStep 665099 = 997649) B997649
theorem B796211 : Blo 291829 796211 := bstep (se 1 (by rfl) ⟨597158, by rfl⟩ : syracuseStep 796211 = 1194317) B1194317
theorem B665153 : Blo 291829 665153 := bstep (se 2 (by rfl) ⟨249432, by rfl⟩ : syracuseStep 665153 = 498865) B498865
theorem B1189451 : Blo 291829 1189451 := bstep (se 1 (by rfl) ⟨892088, by rfl⟩ : syracuseStep 1189451 = 1784177) B1784177
theorem B992843 : Blo 291829 992843 := bstep (se 1 (by rfl) ⟨744632, by rfl⟩ : syracuseStep 992843 = 1489265) B1489265
theorem B370327 : Blo 291829 370327 := bstep (se 1 (by rfl) ⟨277745, by rfl⟩ : syracuseStep 370327 = 555491) B555491
theorem B665369 : Blo 291829 665369 := bstep (se 2 (by rfl) ⟨249513, by rfl⟩ : syracuseStep 665369 = 499027) B499027
theorem B993113 : Blo 291829 993113 := bstep (se 2 (by rfl) ⟨372417, by rfl⟩ : syracuseStep 993113 = 744835) B744835
theorem B665459 : Blo 291829 665459 := bstep (se 1 (by rfl) ⟨499094, by rfl⟩ : syracuseStep 665459 = 998189) B998189
theorem B665495 : Blo 291829 665495 := bstep (se 1 (by rfl) ⟨499121, by rfl⟩ : syracuseStep 665495 = 998243) B998243
theorem B1255475 : Blo 291829 1255475 := bstep (se 1 (by rfl) ⟨941606, by rfl⟩ : syracuseStep 1255475 = 1883213) B1883213
theorem B1419329 : Blo 291829 1419329 := bstep (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) B1064497
theorem B993815 : Blo 291829 993815 := bstep (se 1 (by rfl) ⟨745361, by rfl⟩ : syracuseStep 993815 = 1490723) B1490723
theorem B1485377 : Blo 291829 1485377 := bstep (se 2 (by rfl) ⟨557016, by rfl⟩ : syracuseStep 1485377 = 1114033) B1114033
theorem B797249 : Blo 291829 797249 := bstep (se 2 (by rfl) ⟨298968, by rfl⟩ : syracuseStep 797249 = 597937) B597937
theorem B1681985 : Blo 291829 1681985 := bstep (se 2 (by rfl) ⟨630744, by rfl⟩ : syracuseStep 1681985 = 1261489) B1261489
theorem B3582557 : Blo 291829 3582557 := bstep (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) B1343459
theorem B1419869 : Blo 291829 1419869 := bstep (se 3 (by rfl) ⟨266225, by rfl⟩ : syracuseStep 1419869 = 532451) B532451
theorem B2501381 : Blo 291829 2501381 := bstep (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) B469009
theorem B994355 : Blo 291829 994355 := bstep (se 1 (by rfl) ⟨745766, by rfl⟩ : syracuseStep 994355 = 1491533) B1491533
theorem B1060057 : Blo 291829 1060057 := bstep (se 2 (by rfl) ⟨397521, by rfl⟩ : syracuseStep 1060057 = 795043) B795043
theorem B994625 : Blo 291829 994625 := bstep (se 2 (by rfl) ⟨372984, by rfl⟩ : syracuseStep 994625 = 745969) B745969
theorem B372043 : Blo 291829 372043 := bstep (se 1 (by rfl) ⟨279032, by rfl⟩ : syracuseStep 372043 = 558065) B558065
theorem B437771 : Blo 291829 437771 := bstep (se 1 (by rfl) ⟨328328, by rfl⟩ : syracuseStep 437771 = 656657) B656657
theorem B437783 : Blo 291829 437783 := bstep (se 1 (by rfl) ⟨328337, by rfl⟩ : syracuseStep 437783 = 656675) B656675
theorem B437849 : Blo 291829 437849 := bstep (se 2 (by rfl) ⟨164193, by rfl⟩ : syracuseStep 437849 = 328387) B328387
theorem B1584791 : Blo 291829 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B437963 : Blo 291829 437963 := bstep (se 1 (by rfl) ⟨328472, by rfl⟩ : syracuseStep 437963 = 656945) B656945
theorem B437975 : Blo 291829 437975 := bstep (se 1 (by rfl) ⟨328481, by rfl⟩ : syracuseStep 437975 = 656963) B656963
theorem B831197 : Blo 291829 831197 := bstep (se 3 (by rfl) ⟨155849, by rfl⟩ : syracuseStep 831197 = 311699) B311699
theorem B438041 : Blo 291829 438041 := bstep (se 2 (by rfl) ⟨164265, by rfl⟩ : syracuseStep 438041 = 328531) B328531
theorem B634711 : Blo 291829 634711 := bstep (se 1 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 634711 = 952067) B952067
theorem B995165 : Blo 291829 995165 := bstep (se 3 (by rfl) ⟨186593, by rfl⟩ : syracuseStep 995165 = 373187) B373187
theorem B438155 : Blo 291829 438155 := bstep (se 1 (by rfl) ⟨328616, by rfl⟩ : syracuseStep 438155 = 657233) B657233
theorem B438167 : Blo 291829 438167 := bstep (se 1 (by rfl) ⟨328625, by rfl⟩ : syracuseStep 438167 = 657251) B657251
theorem B1257389 : Blo 291829 1257389 := bstep (se 3 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 1257389 = 471521) B471521
theorem B438233 : Blo 291829 438233 := bstep (se 2 (by rfl) ⟨164337, by rfl⟩ : syracuseStep 438233 = 328675) B328675
theorem B831539 : Blo 291829 831539 := bstep (se 1 (by rfl) ⟨623654, by rfl⟩ : syracuseStep 831539 = 1247309) B1247309
theorem B438347 : Blo 291829 438347 := bstep (se 1 (by rfl) ⟨328760, by rfl⟩ : syracuseStep 438347 = 657521) B657521
theorem B438359 : Blo 291829 438359 := bstep (se 1 (by rfl) ⟨328769, by rfl⟩ : syracuseStep 438359 = 657539) B657539
theorem B3747971 : Blo 291829 3747971 := bstep (se 1 (by rfl) ⟨2810978, by rfl⟩ : syracuseStep 3747971 = 5621957) B5621957
theorem B438425 : Blo 291829 438425 := bstep (se 2 (by rfl) ⟨164409, by rfl⟩ : syracuseStep 438425 = 328819) B328819
theorem B1781939 : Blo 291829 1781939 := bstep (se 1 (by rfl) ⟨1336454, by rfl⟩ : syracuseStep 1781939 = 2672909) B2672909
theorem B1585331 : Blo 291829 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B1257731 : Blo 291829 1257731 := bstep (se 1 (by rfl) ⟨943298, by rfl⟩ : syracuseStep 1257731 = 1886597) B1886597
theorem B438539 : Blo 291829 438539 := bstep (se 1 (by rfl) ⟨328904, by rfl⟩ : syracuseStep 438539 = 657809) B657809
theorem B438551 : Blo 291829 438551 := bstep (se 1 (by rfl) ⟨328913, by rfl⟩ : syracuseStep 438551 = 657827) B657827
theorem B373015 : Blo 291829 373015 := bstep (se 1 (by rfl) ⟨279761, by rfl⟩ : syracuseStep 373015 = 559523) B559523
theorem B438617 : Blo 291829 438617 := bstep (se 2 (by rfl) ⟨164481, by rfl⟩ : syracuseStep 438617 = 328963) B328963
theorem B2240945 : Blo 291829 2240945 := bstep (se 2 (by rfl) ⟨840354, by rfl⟩ : syracuseStep 2240945 = 1680709) B1680709
theorem B668083 : Blo 291829 668083 := bstep (se 1 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 668083 = 1002125) B1002125
theorem B438731 : Blo 291829 438731 := bstep (se 1 (by rfl) ⟨329048, by rfl⟩ : syracuseStep 438731 = 658097) B658097
theorem B438743 : Blo 291829 438743 := bstep (se 1 (by rfl) ⟨329057, by rfl⟩ : syracuseStep 438743 = 658115) B658115
theorem B1487321 : Blo 291829 1487321 := bstep (se 2 (by rfl) ⟨557745, by rfl⟩ : syracuseStep 1487321 = 1115491) B1115491
theorem B438809 : Blo 291829 438809 := bstep (se 2 (by rfl) ⟨164553, by rfl⟩ : syracuseStep 438809 = 329107) B329107
theorem B438923 : Blo 291829 438923 := bstep (se 1 (by rfl) ⟨329192, by rfl⟩ : syracuseStep 438923 = 658385) B658385
theorem B438935 : Blo 291829 438935 := bstep (se 1 (by rfl) ⟨329201, by rfl⟩ : syracuseStep 438935 = 658403) B658403
theorem B439001 : Blo 291829 439001 := bstep (se 2 (by rfl) ⟨164625, by rfl⟩ : syracuseStep 439001 = 329251) B329251
theorem B439115 : Blo 291829 439115 := bstep (se 1 (by rfl) ⟨329336, by rfl⟩ : syracuseStep 439115 = 658673) B658673
theorem B439127 : Blo 291829 439127 := bstep (se 1 (by rfl) ⟨329345, by rfl⟩ : syracuseStep 439127 = 658691) B658691
theorem B1356695 : Blo 291829 1356695 := bstep (se 1 (by rfl) ⟨1017521, by rfl⟩ : syracuseStep 1356695 = 2035043) B2035043
theorem B2241431 : Blo 291829 2241431 := bstep (se 1 (by rfl) ⟨1681073, by rfl⟩ : syracuseStep 2241431 = 3362147) B3362147
theorem B439193 : Blo 291829 439193 := bstep (se 2 (by rfl) ⟨164697, by rfl⟩ : syracuseStep 439193 = 329395) B329395
theorem B996299 : Blo 291829 996299 := bstep (se 1 (by rfl) ⟨747224, by rfl⟩ : syracuseStep 996299 = 1494449) B1494449
theorem B439307 : Blo 291829 439307 := bstep (se 1 (by rfl) ⟨329480, by rfl⟩ : syracuseStep 439307 = 658961) B658961
theorem B439319 : Blo 291829 439319 := bstep (se 1 (by rfl) ⟨329489, by rfl⟩ : syracuseStep 439319 = 658979) B658979
theorem B2831435 : Blo 291829 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B373835 : Blo 291829 373835 := bstep (se 1 (by rfl) ⟨280376, by rfl⟩ : syracuseStep 373835 = 560753) B560753
theorem B439385 : Blo 291829 439385 := bstep (se 2 (by rfl) ⟨164769, by rfl⟩ : syracuseStep 439385 = 329539) B329539
theorem B439499 : Blo 291829 439499 := bstep (se 1 (by rfl) ⟨329624, by rfl⟩ : syracuseStep 439499 = 659249) B659249
theorem B439511 : Blo 291829 439511 := bstep (se 1 (by rfl) ⟨329633, by rfl⟩ : syracuseStep 439511 = 659267) B659267
theorem B996569 : Blo 291829 996569 := bstep (se 2 (by rfl) ⟨373713, by rfl⟩ : syracuseStep 996569 = 747427) B747427
theorem B439577 : Blo 291829 439577 := bstep (se 2 (by rfl) ⟨164841, by rfl⟩ : syracuseStep 439577 = 329683) B329683
theorem B701747 : Blo 291829 701747 := bstep (se 1 (by rfl) ⟨526310, by rfl⟩ : syracuseStep 701747 = 1052621) B1052621
theorem B5354869 : Blo 291829 5354869 := bstep (se 5 (by rfl) ⟨251009, by rfl⟩ : syracuseStep 5354869 = 502019) B502019
theorem B439691 : Blo 291829 439691 := bstep (se 1 (by rfl) ⟨329768, by rfl⟩ : syracuseStep 439691 = 659537) B659537
theorem B439703 : Blo 291829 439703 := bstep (se 1 (by rfl) ⟨329777, by rfl⟩ : syracuseStep 439703 = 659555) B659555
theorem B439769 : Blo 291829 439769 := bstep (se 2 (by rfl) ⟨164913, by rfl⟩ : syracuseStep 439769 = 329827) B329827
theorem B800279 : Blo 291829 800279 := bstep (se 1 (by rfl) ⟨600209, by rfl⟩ : syracuseStep 800279 = 1200419) B1200419
theorem B439883 : Blo 291829 439883 := bstep (se 1 (by rfl) ⟨329912, by rfl⟩ : syracuseStep 439883 = 659825) B659825
theorem B439895 : Blo 291829 439895 := bstep (se 1 (by rfl) ⟨329921, by rfl⟩ : syracuseStep 439895 = 659843) B659843
theorem B439961 : Blo 291829 439961 := bstep (se 2 (by rfl) ⟨164985, by rfl⟩ : syracuseStep 439961 = 329971) B329971
theorem B440075 : Blo 291829 440075 := bstep (se 1 (by rfl) ⟨330056, by rfl⟩ : syracuseStep 440075 = 660113) B660113
theorem B440087 : Blo 291829 440087 := bstep (se 1 (by rfl) ⟨330065, by rfl⟩ : syracuseStep 440087 = 660131) B660131
theorem B440153 : Blo 291829 440153 := bstep (se 2 (by rfl) ⟨165057, by rfl⟩ : syracuseStep 440153 = 330115) B330115
theorem B997271 : Blo 291829 997271 := bstep (se 1 (by rfl) ⟨747953, by rfl⟩ : syracuseStep 997271 = 1495907) B1495907
theorem B440267 : Blo 291829 440267 := bstep (se 1 (by rfl) ⟨330200, by rfl⟩ : syracuseStep 440267 = 660401) B660401
theorem B440279 : Blo 291829 440279 := bstep (se 1 (by rfl) ⟨330209, by rfl⟩ : syracuseStep 440279 = 660419) B660419
theorem B899095 : Blo 291829 899095 := bstep (se 1 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 899095 = 1348643) B1348643
theorem B440345 : Blo 291829 440345 := bstep (se 2 (by rfl) ⟨165129, by rfl⟩ : syracuseStep 440345 = 330259) B330259
theorem B4995107 : Blo 291829 4995107 := bstep (se 1 (by rfl) ⟨3746330, by rfl⟩ : syracuseStep 4995107 = 7492661) B7492661
theorem B1488941 : Blo 291829 1488941 := bstep (se 3 (by rfl) ⟨279176, by rfl⟩ : syracuseStep 1488941 = 558353) B558353
theorem B702515 : Blo 291829 702515 := bstep (se 1 (by rfl) ⟨526886, by rfl⟩ : syracuseStep 702515 = 1053773) B1053773
theorem B1882187 : Blo 291829 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B440459 : Blo 291829 440459 := bstep (se 1 (by rfl) ⟨330344, by rfl⟩ : syracuseStep 440459 = 660689) B660689
theorem B637067 : Blo 291829 637067 := bstep (se 1 (by rfl) ⟨477800, by rfl⟩ : syracuseStep 637067 = 955601) B955601
theorem B1063057 : Blo 291829 1063057 := bstep (se 2 (by rfl) ⟨398646, by rfl⟩ : syracuseStep 1063057 = 797293) B797293
theorem B440471 : Blo 291829 440471 := bstep (se 1 (by rfl) ⟨330353, by rfl⟩ : syracuseStep 440471 = 660707) B660707
theorem B1063115 : Blo 291829 1063115 := bstep (se 1 (by rfl) ⟨797336, by rfl⟩ : syracuseStep 1063115 = 1594673) B1594673
theorem B440537 : Blo 291829 440537 := bstep (se 2 (by rfl) ⟨165201, by rfl⟩ : syracuseStep 440537 = 330403) B330403
theorem B2505005 : Blo 291829 2505005 := bstep (se 3 (by rfl) ⟨469688, by rfl⟩ : syracuseStep 2505005 = 939377) B939377
theorem B440651 : Blo 291829 440651 := bstep (se 1 (by rfl) ⟨330488, by rfl⟩ : syracuseStep 440651 = 660977) B660977
theorem B440663 : Blo 291829 440663 := bstep (se 1 (by rfl) ⟨330497, by rfl⟩ : syracuseStep 440663 = 660995) B660995
theorem B833885 : Blo 291829 833885 := bstep (se 3 (by rfl) ⟨156353, by rfl⟩ : syracuseStep 833885 = 312707) B312707
theorem B1587557 : Blo 291829 1587557 := bstep (se 4 (by rfl) ⟨148833, by rfl⟩ : syracuseStep 1587557 = 297667) B297667
theorem B440729 : Blo 291829 440729 := bstep (se 2 (by rfl) ⟨165273, by rfl⟩ : syracuseStep 440729 = 330547) B330547
theorem B702899 : Blo 291829 702899 := bstep (se 1 (by rfl) ⟨527174, by rfl⟩ : syracuseStep 702899 = 1054349) B1054349
theorem B997811 : Blo 291829 997811 := bstep (se 1 (by rfl) ⟨748358, by rfl⟩ : syracuseStep 997811 = 1496717) B1496717
theorem B440843 : Blo 291829 440843 := bstep (se 1 (by rfl) ⟨330632, by rfl⟩ : syracuseStep 440843 = 661265) B661265
theorem B440855 : Blo 291829 440855 := bstep (se 1 (by rfl) ⟨330641, by rfl⟩ : syracuseStep 440855 = 661283) B661283
theorem B834113 : Blo 291829 834113 := bstep (se 2 (by rfl) ⟨312792, by rfl⟩ : syracuseStep 834113 = 625585) B625585
theorem B1260107 : Blo 291829 1260107 := bstep (se 1 (by rfl) ⟨945080, by rfl⟩ : syracuseStep 1260107 = 1890161) B1890161
theorem B440921 : Blo 291829 440921 := bstep (se 2 (by rfl) ⟨165345, by rfl⟩ : syracuseStep 440921 = 330691) B330691
theorem B998081 : Blo 291829 998081 := bstep (se 2 (by rfl) ⟨374280, by rfl⟩ : syracuseStep 998081 = 748561) B748561
theorem B441035 : Blo 291829 441035 := bstep (se 1 (by rfl) ⟨330776, by rfl⟩ : syracuseStep 441035 = 661553) B661553
theorem B441047 : Blo 291829 441047 := bstep (se 1 (by rfl) ⟨330785, by rfl⟩ : syracuseStep 441047 = 661571) B661571
theorem B441113 : Blo 291829 441113 := bstep (se 2 (by rfl) ⟨165417, by rfl⟩ : syracuseStep 441113 = 330835) B330835
theorem B441227 : Blo 291829 441227 := bstep (se 1 (by rfl) ⟨330920, by rfl⟩ : syracuseStep 441227 = 661841) B661841
theorem B834455 : Blo 291829 834455 := bstep (se 1 (by rfl) ⟨625841, by rfl⟩ : syracuseStep 834455 = 1251683) B1251683
theorem B441239 : Blo 291829 441239 := bstep (se 1 (by rfl) ⟨330929, by rfl⟩ : syracuseStep 441239 = 661859) B661859
theorem B441305 : Blo 291829 441305 := bstep (se 2 (by rfl) ⟨165489, by rfl⟩ : syracuseStep 441305 = 330979) B330979
theorem B3750947 : Blo 291829 3750947 := bstep (se 1 (by rfl) ⟨2813210, by rfl⟩ : syracuseStep 3750947 = 5626421) B5626421
theorem B441419 : Blo 291829 441419 := bstep (se 1 (by rfl) ⟨331064, by rfl⟩ : syracuseStep 441419 = 662129) B662129
theorem B441431 : Blo 291829 441431 := bstep (se 1 (by rfl) ⟨331073, by rfl⟩ : syracuseStep 441431 = 662147) B662147
theorem B441497 : Blo 291829 441497 := bstep (se 2 (by rfl) ⟨165561, by rfl⟩ : syracuseStep 441497 = 331123) B331123
theorem B441611 : Blo 291829 441611 := bstep (se 1 (by rfl) ⟨331208, by rfl⟩ : syracuseStep 441611 = 662417) B662417
theorem B441623 : Blo 291829 441623 := bstep (se 1 (by rfl) ⟨331217, by rfl⟩ : syracuseStep 441623 = 662435) B662435
theorem B441689 : Blo 291829 441689 := bstep (se 2 (by rfl) ⟨165633, by rfl⟩ : syracuseStep 441689 = 331267) B331267
theorem B703937 : Blo 291829 703937 := bstep (se 2 (by rfl) ⟨263976, by rfl⟩ : syracuseStep 703937 = 527953) B527953
theorem B441803 : Blo 291829 441803 := bstep (se 1 (by rfl) ⟨331352, by rfl⟩ : syracuseStep 441803 = 662705) B662705
theorem B441815 : Blo 291829 441815 := bstep (se 1 (by rfl) ⟨331361, by rfl⟩ : syracuseStep 441815 = 662723) B662723
theorem B1261079 : Blo 291829 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B441881 : Blo 291829 441881 := bstep (se 2 (by rfl) ⟨165705, by rfl⟩ : syracuseStep 441881 = 331411) B331411
theorem B441995 : Blo 291829 441995 := bstep (se 1 (by rfl) ⟨331496, by rfl⟩ : syracuseStep 441995 = 662993) B662993
theorem B442007 : Blo 291829 442007 := bstep (se 1 (by rfl) ⟨331505, by rfl⟩ : syracuseStep 442007 = 663011) B663011
theorem B1883827 : Blo 291829 1883827 := bstep (se 1 (by rfl) ⟨1412870, by rfl⟩ : syracuseStep 1883827 = 2825741) B2825741
theorem B8437445 : Blo 291829 8437445 := bstep (se 4 (by rfl) ⟨791010, by rfl⟩ : syracuseStep 8437445 = 1582021) B1582021
theorem B442073 : Blo 291829 442073 := bstep (se 2 (by rfl) ⟨165777, by rfl⟩ : syracuseStep 442073 = 331555) B331555
theorem B5062445 : Blo 291829 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B966451 : Blo 291829 966451 := bstep (se 1 (by rfl) ⟨724838, by rfl⟩ : syracuseStep 966451 = 1449677) B1449677
theorem B442187 : Blo 291829 442187 := bstep (se 1 (by rfl) ⟨331640, by rfl⟩ : syracuseStep 442187 = 663281) B663281
theorem B442199 : Blo 291829 442199 := bstep (se 1 (by rfl) ⟨331649, by rfl⟩ : syracuseStep 442199 = 663299) B663299
theorem B442265 : Blo 291829 442265 := bstep (se 2 (by rfl) ⟨165849, by rfl⟩ : syracuseStep 442265 = 331699) B331699
theorem B442379 : Blo 291829 442379 := bstep (se 1 (by rfl) ⟨331784, by rfl⟩ : syracuseStep 442379 = 663569) B663569
theorem B442391 : Blo 291829 442391 := bstep (se 1 (by rfl) ⟨331793, by rfl⟩ : syracuseStep 442391 = 663587) B663587
theorem B1720385 : Blo 291829 1720385 := bstep (se 2 (by rfl) ⟨645144, by rfl⟩ : syracuseStep 1720385 = 1290289) B1290289
theorem B442457 : Blo 291829 442457 := bstep (se 2 (by rfl) ⟨165921, by rfl⟩ : syracuseStep 442457 = 331843) B331843
theorem B442571 : Blo 291829 442571 := bstep (se 1 (by rfl) ⟨331928, by rfl⟩ : syracuseStep 442571 = 663857) B663857
theorem B442583 : Blo 291829 442583 := bstep (se 1 (by rfl) ⟨331937, by rfl⟩ : syracuseStep 442583 = 663875) B663875
theorem B442649 : Blo 291829 442649 := bstep (se 2 (by rfl) ⟨165993, by rfl⟩ : syracuseStep 442649 = 331987) B331987
theorem B1065305 : Blo 291829 1065305 := bstep (se 2 (by rfl) ⟨399489, by rfl⟩ : syracuseStep 1065305 = 798979) B798979
theorem B442763 : Blo 291829 442763 := bstep (se 1 (by rfl) ⟨332072, by rfl⟩ : syracuseStep 442763 = 664145) B664145
theorem B442775 : Blo 291829 442775 := bstep (se 1 (by rfl) ⟨332081, by rfl⟩ : syracuseStep 442775 = 664163) B664163
theorem B442841 : Blo 291829 442841 := bstep (se 2 (by rfl) ⟨166065, by rfl⟩ : syracuseStep 442841 = 332131) B332131
theorem B442955 : Blo 291829 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B442967 : Blo 291829 442967 := bstep (se 1 (by rfl) ⟨332225, by rfl⟩ : syracuseStep 442967 = 664451) B664451
theorem B1065565 : Blo 291829 1065565 := bstep (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) B399587
theorem B2507395 : Blo 291829 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B443033 : Blo 291829 443033 := bstep (se 2 (by rfl) ⟨166137, by rfl⟩ : syracuseStep 443033 = 332275) B332275
theorem B443147 : Blo 291829 443147 := bstep (se 1 (by rfl) ⟨332360, by rfl⟩ : syracuseStep 443147 = 664721) B664721
theorem B443159 : Blo 291829 443159 := bstep (se 1 (by rfl) ⟨332369, by rfl⟩ : syracuseStep 443159 = 664739) B664739
theorem B443225 : Blo 291829 443225 := bstep (se 2 (by rfl) ⟨166209, by rfl⟩ : syracuseStep 443225 = 332419) B332419
theorem B5686193 : Blo 291829 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B443339 : Blo 291829 443339 := bstep (se 1 (by rfl) ⟨332504, by rfl⟩ : syracuseStep 443339 = 665009) B665009
theorem B443351 : Blo 291829 443351 := bstep (se 1 (by rfl) ⟨332513, by rfl⟩ : syracuseStep 443351 = 665027) B665027
theorem B443417 : Blo 291829 443417 := bstep (se 2 (by rfl) ⟨166281, by rfl⟩ : syracuseStep 443417 = 332563) B332563
theorem B1885315 : Blo 291829 1885315 := bstep (se 1 (by rfl) ⟨1413986, by rfl⟩ : syracuseStep 1885315 = 2827973) B2827973
theorem B443531 : Blo 291829 443531 := bstep (se 1 (by rfl) ⟨332648, by rfl⟩ : syracuseStep 443531 = 665297) B665297
theorem B443543 : Blo 291829 443543 := bstep (se 1 (by rfl) ⟨332657, by rfl⟩ : syracuseStep 443543 = 665315) B665315
theorem B836801 : Blo 291829 836801 := bstep (se 2 (by rfl) ⟨313800, by rfl⟩ : syracuseStep 836801 = 627601) B627601
theorem B443609 : Blo 291829 443609 := bstep (se 2 (by rfl) ⟨166353, by rfl⟩ : syracuseStep 443609 = 332707) B332707
theorem B443723 : Blo 291829 443723 := bstep (se 1 (by rfl) ⟨332792, by rfl⟩ : syracuseStep 443723 = 665585) B665585
theorem B443735 : Blo 291829 443735 := bstep (se 1 (by rfl) ⟨332801, by rfl⟩ : syracuseStep 443735 = 665603) B665603
theorem B2508353 : Blo 291829 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B837337 : Blo 291829 837337 := bstep (se 2 (by rfl) ⟨314001, by rfl⟩ : syracuseStep 837337 = 628003) B628003
theorem B2148113 : Blo 291829 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B1492829 : Blo 291829 1492829 := bstep (se 3 (by rfl) ⟨279905, by rfl⟩ : syracuseStep 1492829 = 559811) B559811
theorem B3360689 : Blo 291829 3360689 := bstep (se 2 (by rfl) ⟨1260258, by rfl⟩ : syracuseStep 3360689 = 2520517) B2520517
theorem B1263539 : Blo 291829 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B313399 : Blo 291829 313399 := bstep (se 1 (by rfl) ⟨235049, by rfl⟩ : syracuseStep 313399 = 470099) B470099
theorem B3819595 : Blo 291829 3819595 := bstep (se 1 (by rfl) ⟨2864696, by rfl⟩ : syracuseStep 3819595 = 5729393) B5729393
theorem B1067201 : Blo 291829 1067201 := bstep (se 2 (by rfl) ⟨400200, by rfl⟩ : syracuseStep 1067201 = 800401) B800401
theorem B2836781 : Blo 291829 2836781 := bstep (se 3 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 2836781 = 1063793) B1063793
theorem B739763 : Blo 291829 739763 := bstep (se 1 (by rfl) ⟨554822, by rfl⟩ : syracuseStep 739763 = 1109645) B1109645
theorem B740299 : Blo 291829 740299 := bstep (se 1 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 740299 = 1110449) B1110449
theorem B740441 : Blo 291829 740441 := bstep (se 2 (by rfl) ⟨277665, by rfl⟩ : syracuseStep 740441 = 555331) B555331
theorem B445655 : Blo 291829 445655 := bstep (se 1 (by rfl) ⟨334241, by rfl⟩ : syracuseStep 445655 = 668483) B668483
theorem B839261 : Blo 291829 839261 := bstep (se 3 (by rfl) ⟨157361, by rfl⟩ : syracuseStep 839261 = 314723) B314723
theorem B315095 : Blo 291829 315095 := bstep (se 1 (by rfl) ⟨236321, by rfl⟩ : syracuseStep 315095 = 472643) B472643
theorem B741271 : Blo 291829 741271 := bstep (se 1 (by rfl) ⟨555953, by rfl⟩ : syracuseStep 741271 = 1111907) B1111907
theorem B1494935 : Blo 291829 1494935 := bstep (se 1 (by rfl) ⟨1121201, by rfl⟩ : syracuseStep 1494935 = 2242403) B2242403
theorem B970841 : Blo 291829 970841 := bstep (se 2 (by rfl) ⟨364065, by rfl⟩ : syracuseStep 970841 = 728131) B728131
theorem B741707 : Blo 291829 741707 := bstep (se 1 (by rfl) ⟨556280, by rfl⟩ : syracuseStep 741707 = 1112561) B1112561
theorem B2019763 : Blo 291829 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B742081 : Blo 291829 742081 := bstep (se 2 (by rfl) ⟨278280, by rfl⟩ : syracuseStep 742081 = 556561) B556561
theorem B2380589 : Blo 291829 2380589 := bstep (se 3 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 2380589 = 892721) B892721
theorem B1135889 : Blo 291829 1135889 := bstep (se 2 (by rfl) ⟨425958, by rfl⟩ : syracuseStep 1135889 = 851917) B851917
theorem B742679 : Blo 291829 742679 := bstep (se 1 (by rfl) ⟨557009, by rfl⟩ : syracuseStep 742679 = 1114019) B1114019
theorem B9557635 : Blo 291829 9557635 := bstep (se 1 (by rfl) ⟨7168226, by rfl⟩ : syracuseStep 9557635 = 14336453) B14336453
theorem B2021213 : Blo 291829 2021213 := bstep (se 3 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 2021213 = 757955) B757955
theorem B743489 : Blo 291829 743489 := bstep (se 2 (by rfl) ⟨278808, by rfl⟩ : syracuseStep 743489 = 557617) B557617
theorem B842177 : Blo 291829 842177 := bstep (se 2 (by rfl) ⟨315816, by rfl⟩ : syracuseStep 842177 = 631633) B631633
theorem B842201 : Blo 291829 842201 := bstep (se 2 (by rfl) ⟨315825, by rfl⟩ : syracuseStep 842201 = 631651) B631651
theorem B4381253 : Blo 291829 4381253 := bstep (se 4 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 4381253 = 821485) B821485
theorem B744025 : Blo 291829 744025 := bstep (se 2 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 744025 = 558019) B558019
theorem B2218589 : Blo 291829 2218589 := bstep (se 3 (by rfl) ⟨415985, by rfl⟩ : syracuseStep 2218589 = 831971) B831971
theorem B3595013 : Blo 291829 3595013 := bstep (se 4 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 3595013 = 674065) B674065
theorem B940889 : Blo 291829 940889 := bstep (se 2 (by rfl) ⟨352833, by rfl⟩ : syracuseStep 940889 = 705667) B705667
theorem B2120579 : Blo 291829 2120579 := bstep (se 1 (by rfl) ⟨1590434, by rfl⟩ : syracuseStep 2120579 = 3180869) B3180869
theorem B1268939 : Blo 291829 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B416983 : Blo 291829 416983 := bstep (se 1 (by rfl) ⟨312737, by rfl⟩ : syracuseStep 416983 = 625475) B625475
theorem B1334701 : Blo 291829 1334701 := bstep (se 3 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 1334701 = 500513) B500513
theorem B745139 : Blo 291829 745139 := bstep (se 1 (by rfl) ⟨558854, by rfl⟩ : syracuseStep 745139 = 1117709) B1117709
theorem B351959 : Blo 291829 351959 := bstep (se 1 (by rfl) ⟨263969, by rfl⟩ : syracuseStep 351959 = 527939) B527939
theorem B319339 : Blo 291829 319339 := bstep (se 1 (by rfl) ⟨239504, by rfl⟩ : syracuseStep 319339 = 479009) B479009
theorem B3563443 : Blo 291829 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B745433 : Blo 291829 745433 := bstep (se 2 (by rfl) ⟨279537, by rfl⟩ : syracuseStep 745433 = 559075) B559075
theorem B3334445 : Blo 291829 3334445 := bstep (se 3 (by rfl) ⟨625208, by rfl⟩ : syracuseStep 3334445 = 1250417) B1250417
theorem B2810213 : Blo 291829 2810213 := bstep (se 4 (by rfl) ⟨263457, by rfl⟩ : syracuseStep 2810213 = 526915) B526915
theorem B942529 : Blo 291829 942529 := bstep (se 2 (by rfl) ⟨353448, by rfl⟩ : syracuseStep 942529 = 706897) B706897
theorem B582475 : Blo 291829 582475 := bstep (se 1 (by rfl) ⟨436856, by rfl⟩ : syracuseStep 582475 = 873713) B873713
theorem B2384741 : Blo 291829 2384741 := bstep (se 4 (by rfl) ⟨223569, by rfl⟩ : syracuseStep 2384741 = 447139) B447139
theorem B910529 : Blo 291829 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B419033 : Blo 291829 419033 := bstep (se 2 (by rfl) ⟨157137, by rfl⟩ : syracuseStep 419033 = 314275) B314275
theorem B1008857 : Blo 291829 1008857 := bstep (se 2 (by rfl) ⟨378321, by rfl⟩ : syracuseStep 1008857 = 756643) B756643
theorem B353867 : Blo 291829 353867 := bstep (se 1 (by rfl) ⟨265400, by rfl⟩ : syracuseStep 353867 = 530801) B530801
theorem B747083 : Blo 291829 747083 := bstep (se 1 (by rfl) ⟨560312, by rfl⟩ : syracuseStep 747083 = 1120625) B1120625
theorem B419671 : Blo 291829 419671 := bstep (se 1 (by rfl) ⟨314753, by rfl⟩ : syracuseStep 419671 = 629507) B629507
theorem B4253957 : Blo 291829 4253957 := bstep (se 4 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 4253957 = 797617) B797617
theorem B944477 : Blo 291829 944477 := bstep (se 3 (by rfl) ⟨177089, by rfl⟩ : syracuseStep 944477 = 354179) B354179
theorem B748055 : Blo 291829 748055 := bstep (se 1 (by rfl) ⟨561041, by rfl⟩ : syracuseStep 748055 = 1122083) B1122083
theorem B1665629 : Blo 291829 1665629 := bstep (se 3 (by rfl) ⟨312305, by rfl⟩ : syracuseStep 1665629 = 624611) B624611
theorem B420491 : Blo 291829 420491 := bstep (se 1 (by rfl) ⟨315368, by rfl⟩ : syracuseStep 420491 = 630737) B630737
theorem B1108673 : Blo 291829 1108673 := bstep (se 2 (by rfl) ⟨415752, by rfl⟩ : syracuseStep 1108673 = 831505) B831505
theorem B5008229 : Blo 291829 5008229 := bstep (se 4 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 5008229 = 939043) B939043
theorem B2583587 : Blo 291829 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B748723 : Blo 291829 748723 := bstep (se 1 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 748723 = 1123085) B1123085
theorem B1929053 : Blo 291829 1929053 := bstep (se 3 (by rfl) ⟨361697, by rfl⟩ : syracuseStep 1929053 = 723395) B723395
theorem B2518877 : Blo 291829 2518877 := bstep (se 3 (by rfl) ⟨472289, by rfl⟩ : syracuseStep 2518877 = 944579) B944579
theorem B3764069 : Blo 291829 3764069 := bstep (se 4 (by rfl) ⟨352881, by rfl⟩ : syracuseStep 3764069 = 705763) B705763
theorem B1109933 : Blo 291829 1109933 := bstep (se 3 (by rfl) ⟨208112, by rfl⟩ : syracuseStep 1109933 = 416225) B416225
theorem B1011635 : Blo 291829 1011635 := bstep (se 1 (by rfl) ⟨758726, by rfl⟩ : syracuseStep 1011635 = 1517453) B1517453
theorem B1109963 : Blo 291829 1109963 := bstep (se 1 (by rfl) ⟨832472, by rfl⟩ : syracuseStep 1109963 = 1664945) B1664945
theorem B1339523 : Blo 291829 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B1700189 : Blo 291829 1700189 := bstep (se 3 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 1700189 = 637571) B637571
theorem B1110617 : Blo 291829 1110617 := bstep (se 2 (by rfl) ⟨416481, by rfl⟩ : syracuseStep 1110617 = 832963) B832963
theorem B1110935 : Blo 291829 1110935 := bstep (se 1 (by rfl) ⟨833201, by rfl⟩ : syracuseStep 1110935 = 1666403) B1666403
theorem B4027315 : Blo 291829 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B291831 : Blo 291829 291831 := bstep (se 1 (by rfl) ⟨218873, by rfl⟩ : syracuseStep 291831 = 437747) B437747
theorem B291851 : Blo 291829 291851 := bstep (se 1 (by rfl) ⟨218888, by rfl⟩ : syracuseStep 291851 = 437777) B437777
theorem B1668113 : Blo 291829 1668113 := bstep (se 2 (by rfl) ⟨625542, by rfl⟩ : syracuseStep 1668113 = 1251085) B1251085
theorem B291863 : Blo 291829 291863 := bstep (se 1 (by rfl) ⟨218897, by rfl⟩ : syracuseStep 291863 = 437795) B437795
theorem B291883 : Blo 291829 291883 := bstep (se 1 (by rfl) ⟨218912, by rfl⟩ : syracuseStep 291883 = 437825) B437825
theorem B291895 : Blo 291829 291895 := bstep (se 1 (by rfl) ⟨218921, by rfl⟩ : syracuseStep 291895 = 437843) B437843
theorem B291915 : Blo 291829 291915 := bstep (se 1 (by rfl) ⟨218936, by rfl⟩ : syracuseStep 291915 = 437873) B437873
theorem B291927 : Blo 291829 291927 := bstep (se 1 (by rfl) ⟨218945, by rfl⟩ : syracuseStep 291927 = 437891) B437891
theorem B291947 : Blo 291829 291947 := bstep (se 1 (by rfl) ⟨218960, by rfl⟩ : syracuseStep 291947 = 437921) B437921
theorem B291959 : Blo 291829 291959 := bstep (se 1 (by rfl) ⟨218969, by rfl⟩ : syracuseStep 291959 = 437939) B437939
theorem B3634307 : Blo 291829 3634307 := bstep (se 1 (by rfl) ⟨2725730, by rfl⟩ : syracuseStep 3634307 = 5451461) B5451461
theorem B291979 : Blo 291829 291979 := bstep (se 1 (by rfl) ⟨218984, by rfl⟩ : syracuseStep 291979 = 437969) B437969
theorem B291991 : Blo 291829 291991 := bstep (se 1 (by rfl) ⟨218993, by rfl⟩ : syracuseStep 291991 = 437987) B437987
theorem B292011 : Blo 291829 292011 := bstep (se 1 (by rfl) ⟨219008, by rfl⟩ : syracuseStep 292011 = 438017) B438017
theorem B292023 : Blo 291829 292023 := bstep (se 1 (by rfl) ⟨219017, by rfl⟩ : syracuseStep 292023 = 438035) B438035
theorem B554177 : Blo 291829 554177 := bstep (se 2 (by rfl) ⟨207816, by rfl⟩ : syracuseStep 554177 = 415633) B415633
theorem B292043 : Blo 291829 292043 := bstep (se 1 (by rfl) ⟨219032, by rfl⟩ : syracuseStep 292043 = 438065) B438065
theorem B292055 : Blo 291829 292055 := bstep (se 1 (by rfl) ⟨219041, by rfl⟩ : syracuseStep 292055 = 438083) B438083
theorem B292075 : Blo 291829 292075 := bstep (se 1 (by rfl) ⟨219056, by rfl⟩ : syracuseStep 292075 = 438113) B438113
theorem B292087 : Blo 291829 292087 := bstep (se 1 (by rfl) ⟨219065, by rfl⟩ : syracuseStep 292087 = 438131) B438131
theorem B292107 : Blo 291829 292107 := bstep (se 1 (by rfl) ⟨219080, by rfl⟩ : syracuseStep 292107 = 438161) B438161
theorem B292119 : Blo 291829 292119 := bstep (se 1 (by rfl) ⟨219089, by rfl⟩ : syracuseStep 292119 = 438179) B438179
theorem B2389283 : Blo 291829 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B292139 : Blo 291829 292139 := bstep (se 1 (by rfl) ⟨219104, by rfl⟩ : syracuseStep 292139 = 438209) B438209
theorem B292151 : Blo 291829 292151 := bstep (se 1 (by rfl) ⟨219113, by rfl⟩ : syracuseStep 292151 = 438227) B438227
theorem B292171 : Blo 291829 292171 := bstep (se 1 (by rfl) ⟨219128, by rfl⟩ : syracuseStep 292171 = 438257) B438257
theorem B292183 : Blo 291829 292183 := bstep (se 1 (by rfl) ⟨219137, by rfl⟩ : syracuseStep 292183 = 438275) B438275
theorem B292203 : Blo 291829 292203 := bstep (se 1 (by rfl) ⟨219152, by rfl⟩ : syracuseStep 292203 = 438305) B438305
theorem B292215 : Blo 291829 292215 := bstep (se 1 (by rfl) ⟨219161, by rfl⟩ : syracuseStep 292215 = 438323) B438323
theorem B292235 : Blo 291829 292235 := bstep (se 1 (by rfl) ⟨219176, by rfl⟩ : syracuseStep 292235 = 438353) B438353
theorem B292247 : Blo 291829 292247 := bstep (se 1 (by rfl) ⟨219185, by rfl⟩ : syracuseStep 292247 = 438371) B438371
theorem B292267 : Blo 291829 292267 := bstep (se 1 (by rfl) ⟨219200, by rfl⟩ : syracuseStep 292267 = 438401) B438401
theorem B292279 : Blo 291829 292279 := bstep (se 1 (by rfl) ⟨219209, by rfl⟩ : syracuseStep 292279 = 438419) B438419
theorem B292299 : Blo 291829 292299 := bstep (se 1 (by rfl) ⟨219224, by rfl⟩ : syracuseStep 292299 = 438449) B438449
theorem B292311 : Blo 291829 292311 := bstep (se 1 (by rfl) ⟨219233, by rfl⟩ : syracuseStep 292311 = 438467) B438467
theorem B292331 : Blo 291829 292331 := bstep (se 1 (by rfl) ⟨219248, by rfl⟩ : syracuseStep 292331 = 438497) B438497
theorem B292343 : Blo 291829 292343 := bstep (se 1 (by rfl) ⟨219257, by rfl⟩ : syracuseStep 292343 = 438515) B438515
theorem B292363 : Blo 291829 292363 := bstep (se 1 (by rfl) ⟨219272, by rfl⟩ : syracuseStep 292363 = 438545) B438545
theorem B554519 : Blo 291829 554519 := bstep (se 1 (by rfl) ⟨415889, by rfl⟩ : syracuseStep 554519 = 831779) B831779
theorem B292375 : Blo 291829 292375 := bstep (se 1 (by rfl) ⟨219281, by rfl⟩ : syracuseStep 292375 = 438563) B438563
theorem B292395 : Blo 291829 292395 := bstep (se 1 (by rfl) ⟨219296, by rfl⟩ : syracuseStep 292395 = 438593) B438593
theorem B1111603 : Blo 291829 1111603 := bstep (se 1 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 1111603 = 1667405) B1667405
theorem B292407 : Blo 291829 292407 := bstep (se 1 (by rfl) ⟨219305, by rfl⟩ : syracuseStep 292407 = 438611) B438611
theorem B292427 : Blo 291829 292427 := bstep (se 1 (by rfl) ⟨219320, by rfl⟩ : syracuseStep 292427 = 438641) B438641
theorem B292439 : Blo 291829 292439 := bstep (se 1 (by rfl) ⟨219329, by rfl⟩ : syracuseStep 292439 = 438659) B438659
theorem B292459 : Blo 291829 292459 := bstep (se 1 (by rfl) ⟨219344, by rfl⟩ : syracuseStep 292459 = 438689) B438689
theorem B292471 : Blo 291829 292471 := bstep (se 1 (by rfl) ⟨219353, by rfl⟩ : syracuseStep 292471 = 438707) B438707
theorem B292491 : Blo 291829 292491 := bstep (se 1 (by rfl) ⟨219368, by rfl⟩ : syracuseStep 292491 = 438737) B438737
theorem B292503 : Blo 291829 292503 := bstep (se 1 (by rfl) ⟨219377, by rfl⟩ : syracuseStep 292503 = 438755) B438755
theorem B292523 : Blo 291829 292523 := bstep (se 1 (by rfl) ⟨219392, by rfl⟩ : syracuseStep 292523 = 438785) B438785
theorem B292535 : Blo 291829 292535 := bstep (se 1 (by rfl) ⟨219401, by rfl⟩ : syracuseStep 292535 = 438803) B438803
theorem B292555 : Blo 291829 292555 := bstep (se 1 (by rfl) ⟨219416, by rfl⟩ : syracuseStep 292555 = 438833) B438833
theorem B292567 : Blo 291829 292567 := bstep (se 1 (by rfl) ⟨219425, by rfl⟩ : syracuseStep 292567 = 438851) B438851
theorem B292587 : Blo 291829 292587 := bstep (se 1 (by rfl) ⟨219440, by rfl⟩ : syracuseStep 292587 = 438881) B438881
theorem B292599 : Blo 291829 292599 := bstep (se 1 (by rfl) ⟨219449, by rfl⟩ : syracuseStep 292599 = 438899) B438899
theorem B292619 : Blo 291829 292619 := bstep (se 1 (by rfl) ⟨219464, by rfl⟩ : syracuseStep 292619 = 438929) B438929
theorem B292631 : Blo 291829 292631 := bstep (se 1 (by rfl) ⟨219473, by rfl⟩ : syracuseStep 292631 = 438947) B438947
theorem B292651 : Blo 291829 292651 := bstep (se 1 (by rfl) ⟨219488, by rfl⟩ : syracuseStep 292651 = 438977) B438977
theorem B292663 : Blo 291829 292663 := bstep (se 1 (by rfl) ⟨219497, by rfl⟩ : syracuseStep 292663 = 438995) B438995
theorem B292683 : Blo 291829 292683 := bstep (se 1 (by rfl) ⟨219512, by rfl⟩ : syracuseStep 292683 = 439025) B439025
theorem B292695 : Blo 291829 292695 := bstep (se 1 (by rfl) ⟨219521, by rfl⟩ : syracuseStep 292695 = 439043) B439043
theorem B292715 : Blo 291829 292715 := bstep (se 1 (by rfl) ⟨219536, by rfl⟩ : syracuseStep 292715 = 439073) B439073
theorem B292727 : Blo 291829 292727 := bstep (se 1 (by rfl) ⟨219545, by rfl⟩ : syracuseStep 292727 = 439091) B439091
theorem B292747 : Blo 291829 292747 := bstep (se 1 (by rfl) ⟨219560, by rfl⟩ : syracuseStep 292747 = 439121) B439121
theorem B292759 : Blo 291829 292759 := bstep (se 1 (by rfl) ⟨219569, by rfl⟩ : syracuseStep 292759 = 439139) B439139
theorem B292779 : Blo 291829 292779 := bstep (se 1 (by rfl) ⟨219584, by rfl⟩ : syracuseStep 292779 = 439169) B439169
theorem B292791 : Blo 291829 292791 := bstep (se 1 (by rfl) ⟨219593, by rfl⟩ : syracuseStep 292791 = 439187) B439187
theorem B292811 : Blo 291829 292811 := bstep (se 1 (by rfl) ⟨219608, by rfl⟩ : syracuseStep 292811 = 439217) B439217
theorem B292823 : Blo 291829 292823 := bstep (se 1 (by rfl) ⟨219617, by rfl⟩ : syracuseStep 292823 = 439235) B439235
theorem B292843 : Blo 291829 292843 := bstep (se 1 (by rfl) ⟨219632, by rfl⟩ : syracuseStep 292843 = 439265) B439265
theorem B292855 : Blo 291829 292855 := bstep (se 1 (by rfl) ⟨219641, by rfl⟩ : syracuseStep 292855 = 439283) B439283
theorem B292875 : Blo 291829 292875 := bstep (se 1 (by rfl) ⟨219656, by rfl⟩ : syracuseStep 292875 = 439313) B439313
theorem B292887 : Blo 291829 292887 := bstep (se 1 (by rfl) ⟨219665, by rfl⟩ : syracuseStep 292887 = 439331) B439331
theorem B292907 : Blo 291829 292907 := bstep (se 1 (by rfl) ⟨219680, by rfl⟩ : syracuseStep 292907 = 439361) B439361
theorem B292919 : Blo 291829 292919 := bstep (se 1 (by rfl) ⟨219689, by rfl⟩ : syracuseStep 292919 = 439379) B439379
theorem B292939 : Blo 291829 292939 := bstep (se 1 (by rfl) ⟨219704, by rfl⟩ : syracuseStep 292939 = 439409) B439409
theorem B292951 : Blo 291829 292951 := bstep (se 1 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 292951 = 439427) B439427
theorem B292971 : Blo 291829 292971 := bstep (se 1 (by rfl) ⟨219728, by rfl⟩ : syracuseStep 292971 = 439457) B439457
theorem B292983 : Blo 291829 292983 := bstep (se 1 (by rfl) ⟨219737, by rfl⟩ : syracuseStep 292983 = 439475) B439475
theorem B293003 : Blo 291829 293003 := bstep (se 1 (by rfl) ⟨219752, by rfl⟩ : syracuseStep 293003 = 439505) B439505
theorem B293015 : Blo 291829 293015 := bstep (se 1 (by rfl) ⟨219761, by rfl⟩ : syracuseStep 293015 = 439523) B439523
theorem B293035 : Blo 291829 293035 := bstep (se 1 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 293035 = 439553) B439553
theorem B555187 : Blo 291829 555187 := bstep (se 1 (by rfl) ⟨416390, by rfl⟩ : syracuseStep 555187 = 832781) B832781
theorem B293047 : Blo 291829 293047 := bstep (se 1 (by rfl) ⟨219785, by rfl⟩ : syracuseStep 293047 = 439571) B439571
theorem B293067 : Blo 291829 293067 := bstep (se 1 (by rfl) ⟨219800, by rfl⟩ : syracuseStep 293067 = 439601) B439601
theorem B293079 : Blo 291829 293079 := bstep (se 1 (by rfl) ⟨219809, by rfl⟩ : syracuseStep 293079 = 439619) B439619
theorem B424153 : Blo 291829 424153 := bstep (se 2 (by rfl) ⟨159057, by rfl⟩ : syracuseStep 424153 = 318115) B318115
theorem B293099 : Blo 291829 293099 := bstep (se 1 (by rfl) ⟨219824, by rfl⟩ : syracuseStep 293099 = 439649) B439649
theorem B293111 : Blo 291829 293111 := bstep (se 1 (by rfl) ⟨219833, by rfl⟩ : syracuseStep 293111 = 439667) B439667
theorem B2128133 : Blo 291829 2128133 := bstep (se 4 (by rfl) ⟨199512, by rfl⟩ : syracuseStep 2128133 = 399025) B399025
theorem B293131 : Blo 291829 293131 := bstep (se 1 (by rfl) ⟨219848, by rfl⟩ : syracuseStep 293131 = 439697) B439697
theorem B293143 : Blo 291829 293143 := bstep (se 1 (by rfl) ⟨219857, by rfl⟩ : syracuseStep 293143 = 439715) B439715
theorem B293163 : Blo 291829 293163 := bstep (se 1 (by rfl) ⟨219872, by rfl⟩ : syracuseStep 293163 = 439745) B439745
theorem B293175 : Blo 291829 293175 := bstep (se 1 (by rfl) ⟨219881, by rfl⟩ : syracuseStep 293175 = 439763) B439763
theorem B293195 : Blo 291829 293195 := bstep (se 1 (by rfl) ⟨219896, by rfl⟩ : syracuseStep 293195 = 439793) B439793
theorem B293207 : Blo 291829 293207 := bstep (se 1 (by rfl) ⟨219905, by rfl⟩ : syracuseStep 293207 = 439811) B439811
theorem B293227 : Blo 291829 293227 := bstep (se 1 (by rfl) ⟨219920, by rfl⟩ : syracuseStep 293227 = 439841) B439841
theorem B293239 : Blo 291829 293239 := bstep (se 1 (by rfl) ⟨219929, by rfl⟩ : syracuseStep 293239 = 439859) B439859
theorem B2521475 : Blo 291829 2521475 := bstep (se 1 (by rfl) ⟨1891106, by rfl⟩ : syracuseStep 2521475 = 3782213) B3782213
theorem B293259 : Blo 291829 293259 := bstep (se 1 (by rfl) ⟨219944, by rfl⟩ : syracuseStep 293259 = 439889) B439889
theorem B293271 : Blo 291829 293271 := bstep (se 1 (by rfl) ⟨219953, by rfl⟩ : syracuseStep 293271 = 439907) B439907
theorem B293291 : Blo 291829 293291 := bstep (se 1 (by rfl) ⟨219968, by rfl⟩ : syracuseStep 293291 = 439937) B439937
theorem B293303 : Blo 291829 293303 := bstep (se 1 (by rfl) ⟨219977, by rfl⟩ : syracuseStep 293303 = 439955) B439955
theorem B293323 : Blo 291829 293323 := bstep (se 1 (by rfl) ⟨219992, by rfl⟩ : syracuseStep 293323 = 439985) B439985
theorem B293335 : Blo 291829 293335 := bstep (se 1 (by rfl) ⟨220001, by rfl⟩ : syracuseStep 293335 = 440003) B440003
theorem B293355 : Blo 291829 293355 := bstep (se 1 (by rfl) ⟨220016, by rfl⟩ : syracuseStep 293355 = 440033) B440033
theorem B293367 : Blo 291829 293367 := bstep (se 1 (by rfl) ⟨220025, by rfl⟩ : syracuseStep 293367 = 440051) B440051
theorem B293387 : Blo 291829 293387 := bstep (se 1 (by rfl) ⟨220040, by rfl⟩ : syracuseStep 293387 = 440081) B440081
theorem B293399 : Blo 291829 293399 := bstep (se 1 (by rfl) ⟨220049, by rfl⟩ : syracuseStep 293399 = 440099) B440099
theorem B293419 : Blo 291829 293419 := bstep (se 1 (by rfl) ⟨220064, by rfl⟩ : syracuseStep 293419 = 440129) B440129
theorem B293431 : Blo 291829 293431 := bstep (se 1 (by rfl) ⟨220073, by rfl⟩ : syracuseStep 293431 = 440147) B440147
theorem B293451 : Blo 291829 293451 := bstep (se 1 (by rfl) ⟨220088, by rfl⟩ : syracuseStep 293451 = 440177) B440177
theorem B293463 : Blo 291829 293463 := bstep (se 1 (by rfl) ⟨220097, by rfl⟩ : syracuseStep 293463 = 440195) B440195
theorem B293483 : Blo 291829 293483 := bstep (se 1 (by rfl) ⟨220112, by rfl⟩ : syracuseStep 293483 = 440225) B440225
theorem B555635 : Blo 291829 555635 := bstep (se 1 (by rfl) ⟨416726, by rfl⟩ : syracuseStep 555635 = 833453) B833453
theorem B293495 : Blo 291829 293495 := bstep (se 1 (by rfl) ⟨220121, by rfl⟩ : syracuseStep 293495 = 440243) B440243
theorem B293515 : Blo 291829 293515 := bstep (se 1 (by rfl) ⟨220136, by rfl⟩ : syracuseStep 293515 = 440273) B440273
theorem B293527 : Blo 291829 293527 := bstep (se 1 (by rfl) ⟨220145, by rfl⟩ : syracuseStep 293527 = 440291) B440291
theorem B555673 : Blo 291829 555673 := bstep (se 2 (by rfl) ⟨208377, by rfl⟩ : syracuseStep 555673 = 416755) B416755
theorem B293547 : Blo 291829 293547 := bstep (se 1 (by rfl) ⟨220160, by rfl⟩ : syracuseStep 293547 = 440321) B440321
theorem B293559 : Blo 291829 293559 := bstep (se 1 (by rfl) ⟨220169, by rfl⟩ : syracuseStep 293559 = 440339) B440339
theorem B293579 : Blo 291829 293579 := bstep (se 1 (by rfl) ⟨220184, by rfl⟩ : syracuseStep 293579 = 440369) B440369
theorem B293591 : Blo 291829 293591 := bstep (se 1 (by rfl) ⟨220193, by rfl⟩ : syracuseStep 293591 = 440387) B440387
theorem B293611 : Blo 291829 293611 := bstep (se 1 (by rfl) ⟨220208, by rfl⟩ : syracuseStep 293611 = 440417) B440417
theorem B293623 : Blo 291829 293623 := bstep (se 1 (by rfl) ⟨220217, by rfl⟩ : syracuseStep 293623 = 440435) B440435
theorem B293643 : Blo 291829 293643 := bstep (se 1 (by rfl) ⟨220232, by rfl⟩ : syracuseStep 293643 = 440465) B440465
theorem B1112849 : Blo 291829 1112849 := bstep (se 2 (by rfl) ⟨417318, by rfl⟩ : syracuseStep 1112849 = 834637) B834637
theorem B293655 : Blo 291829 293655 := bstep (se 1 (by rfl) ⟨220241, by rfl⟩ : syracuseStep 293655 = 440483) B440483
theorem B293675 : Blo 291829 293675 := bstep (se 1 (by rfl) ⟨220256, by rfl⟩ : syracuseStep 293675 = 440513) B440513
theorem B293687 : Blo 291829 293687 := bstep (se 1 (by rfl) ⟨220265, by rfl⟩ : syracuseStep 293687 = 440531) B440531
theorem B293707 : Blo 291829 293707 := bstep (se 1 (by rfl) ⟨220280, by rfl⟩ : syracuseStep 293707 = 440561) B440561
theorem B293719 : Blo 291829 293719 := bstep (se 1 (by rfl) ⟨220289, by rfl⟩ : syracuseStep 293719 = 440579) B440579
theorem B1538909 : Blo 291829 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B293739 : Blo 291829 293739 := bstep (se 1 (by rfl) ⟨220304, by rfl⟩ : syracuseStep 293739 = 440609) B440609
theorem B293751 : Blo 291829 293751 := bstep (se 1 (by rfl) ⟨220313, by rfl⟩ : syracuseStep 293751 = 440627) B440627
theorem B293771 : Blo 291829 293771 := bstep (se 1 (by rfl) ⟨220328, by rfl⟩ : syracuseStep 293771 = 440657) B440657
theorem B293783 : Blo 291829 293783 := bstep (se 1 (by rfl) ⟨220337, by rfl⟩ : syracuseStep 293783 = 440675) B440675
theorem B293803 : Blo 291829 293803 := bstep (se 1 (by rfl) ⟨220352, by rfl⟩ : syracuseStep 293803 = 440705) B440705
theorem B293815 : Blo 291829 293815 := bstep (se 1 (by rfl) ⟨220361, by rfl⟩ : syracuseStep 293815 = 440723) B440723
theorem B293835 : Blo 291829 293835 := bstep (se 1 (by rfl) ⟨220376, by rfl⟩ : syracuseStep 293835 = 440753) B440753
theorem B293847 : Blo 291829 293847 := bstep (se 1 (by rfl) ⟨220385, by rfl⟩ : syracuseStep 293847 = 440771) B440771
theorem B293867 : Blo 291829 293867 := bstep (se 1 (by rfl) ⟨220400, by rfl⟩ : syracuseStep 293867 = 440801) B440801
theorem B293879 : Blo 291829 293879 := bstep (se 1 (by rfl) ⟨220409, by rfl⟩ : syracuseStep 293879 = 440819) B440819
theorem B293899 : Blo 291829 293899 := bstep (se 1 (by rfl) ⟨220424, by rfl⟩ : syracuseStep 293899 = 440849) B440849
theorem B293911 : Blo 291829 293911 := bstep (se 1 (by rfl) ⟨220433, by rfl⟩ : syracuseStep 293911 = 440867) B440867
theorem B293931 : Blo 291829 293931 := bstep (se 1 (by rfl) ⟨220448, by rfl⟩ : syracuseStep 293931 = 440897) B440897
theorem B293943 : Blo 291829 293943 := bstep (se 1 (by rfl) ⟨220457, by rfl⟩ : syracuseStep 293943 = 440915) B440915
theorem B293963 : Blo 291829 293963 := bstep (se 1 (by rfl) ⟨220472, by rfl⟩ : syracuseStep 293963 = 440945) B440945
theorem B293975 : Blo 291829 293975 := bstep (se 1 (by rfl) ⟨220481, by rfl⟩ : syracuseStep 293975 = 440963) B440963
theorem B556121 : Blo 291829 556121 := bstep (se 2 (by rfl) ⟨208545, by rfl⟩ : syracuseStep 556121 = 417091) B417091
theorem B4258909 : Blo 291829 4258909 := bstep (se 3 (by rfl) ⟨798545, by rfl⟩ : syracuseStep 4258909 = 1597091) B1597091
theorem B293995 : Blo 291829 293995 := bstep (se 1 (by rfl) ⟨220496, by rfl⟩ : syracuseStep 293995 = 440993) B440993
theorem B294007 : Blo 291829 294007 := bstep (se 1 (by rfl) ⟨220505, by rfl⟩ : syracuseStep 294007 = 441011) B441011
theorem B294027 : Blo 291829 294027 := bstep (se 1 (by rfl) ⟨220520, by rfl⟩ : syracuseStep 294027 = 441041) B441041
theorem B294039 : Blo 291829 294039 := bstep (se 1 (by rfl) ⟨220529, by rfl⟩ : syracuseStep 294039 = 441059) B441059
theorem B294059 : Blo 291829 294059 := bstep (se 1 (by rfl) ⟨220544, by rfl⟩ : syracuseStep 294059 = 441089) B441089
theorem B294071 : Blo 291829 294071 := bstep (se 1 (by rfl) ⟨220553, by rfl⟩ : syracuseStep 294071 = 441107) B441107
theorem B294091 : Blo 291829 294091 := bstep (se 1 (by rfl) ⟨220568, by rfl⟩ : syracuseStep 294091 = 441137) B441137
theorem B294103 : Blo 291829 294103 := bstep (se 1 (by rfl) ⟨220577, by rfl⟩ : syracuseStep 294103 = 441155) B441155
theorem B294123 : Blo 291829 294123 := bstep (se 1 (by rfl) ⟨220592, by rfl⟩ : syracuseStep 294123 = 441185) B441185
theorem B294135 : Blo 291829 294135 := bstep (se 1 (by rfl) ⟨220601, by rfl⟩ : syracuseStep 294135 = 441203) B441203
theorem B294155 : Blo 291829 294155 := bstep (se 1 (by rfl) ⟨220616, by rfl⟩ : syracuseStep 294155 = 441233) B441233
theorem B294167 : Blo 291829 294167 := bstep (se 1 (by rfl) ⟨220625, by rfl⟩ : syracuseStep 294167 = 441251) B441251
theorem B294187 : Blo 291829 294187 := bstep (se 1 (by rfl) ⟨220640, by rfl⟩ : syracuseStep 294187 = 441281) B441281
theorem B294199 : Blo 291829 294199 := bstep (se 1 (by rfl) ⟨220649, by rfl⟩ : syracuseStep 294199 = 441299) B441299
theorem B3374401 : Blo 291829 3374401 := bstep (se 2 (by rfl) ⟨1265400, by rfl⟩ : syracuseStep 3374401 = 2530801) B2530801
theorem B294219 : Blo 291829 294219 := bstep (se 1 (by rfl) ⟨220664, by rfl⟩ : syracuseStep 294219 = 441329) B441329
theorem B294231 : Blo 291829 294231 := bstep (se 1 (by rfl) ⟨220673, by rfl⟩ : syracuseStep 294231 = 441347) B441347
theorem B425305 : Blo 291829 425305 := bstep (se 2 (by rfl) ⟨159489, by rfl⟩ : syracuseStep 425305 = 318979) B318979
theorem B294251 : Blo 291829 294251 := bstep (se 1 (by rfl) ⟨220688, by rfl⟩ : syracuseStep 294251 = 441377) B441377
theorem B294263 : Blo 291829 294263 := bstep (se 1 (by rfl) ⟨220697, by rfl⟩ : syracuseStep 294263 = 441395) B441395
theorem B294283 : Blo 291829 294283 := bstep (se 1 (by rfl) ⟨220712, by rfl⟩ : syracuseStep 294283 = 441425) B441425
theorem B294295 : Blo 291829 294295 := bstep (se 1 (by rfl) ⟨220721, by rfl⟩ : syracuseStep 294295 = 441443) B441443
theorem B294315 : Blo 291829 294315 := bstep (se 1 (by rfl) ⟨220736, by rfl⟩ : syracuseStep 294315 = 441473) B441473
theorem B294327 : Blo 291829 294327 := bstep (se 1 (by rfl) ⟨220745, by rfl⟩ : syracuseStep 294327 = 441491) B441491
theorem B1113547 : Blo 291829 1113547 := bstep (se 1 (by rfl) ⟨835160, by rfl⟩ : syracuseStep 1113547 = 1670321) B1670321
theorem B294347 : Blo 291829 294347 := bstep (se 1 (by rfl) ⟨220760, by rfl⟩ : syracuseStep 294347 = 441521) B441521
theorem B294359 : Blo 291829 294359 := bstep (se 1 (by rfl) ⟨220769, by rfl⟩ : syracuseStep 294359 = 441539) B441539
theorem B294379 : Blo 291829 294379 := bstep (se 1 (by rfl) ⟨220784, by rfl⟩ : syracuseStep 294379 = 441569) B441569
theorem B294391 : Blo 291829 294391 := bstep (se 1 (by rfl) ⟨220793, by rfl⟩ : syracuseStep 294391 = 441587) B441587
theorem B294411 : Blo 291829 294411 := bstep (se 1 (by rfl) ⟨220808, by rfl⟩ : syracuseStep 294411 = 441617) B441617
theorem B294423 : Blo 291829 294423 := bstep (se 1 (by rfl) ⟨220817, by rfl⟩ : syracuseStep 294423 = 441635) B441635
theorem B294443 : Blo 291829 294443 := bstep (se 1 (by rfl) ⟨220832, by rfl⟩ : syracuseStep 294443 = 441665) B441665
theorem B294455 : Blo 291829 294455 := bstep (se 1 (by rfl) ⟨220841, by rfl⟩ : syracuseStep 294455 = 441683) B441683
theorem B294475 : Blo 291829 294475 := bstep (se 1 (by rfl) ⟨220856, by rfl⟩ : syracuseStep 294475 = 441713) B441713
theorem B294487 : Blo 291829 294487 := bstep (se 1 (by rfl) ⟨220865, by rfl⟩ : syracuseStep 294487 = 441731) B441731
theorem B294507 : Blo 291829 294507 := bstep (se 1 (by rfl) ⟨220880, by rfl⟩ : syracuseStep 294507 = 441761) B441761
theorem B294519 : Blo 291829 294519 := bstep (se 1 (by rfl) ⟨220889, by rfl⟩ : syracuseStep 294519 = 441779) B441779
theorem B294539 : Blo 291829 294539 := bstep (se 1 (by rfl) ⟨220904, by rfl⟩ : syracuseStep 294539 = 441809) B441809
theorem B294551 : Blo 291829 294551 := bstep (se 1 (by rfl) ⟨220913, by rfl⟩ : syracuseStep 294551 = 441827) B441827
theorem B294571 : Blo 291829 294571 := bstep (se 1 (by rfl) ⟨220928, by rfl⟩ : syracuseStep 294571 = 441857) B441857
theorem B4226741 : Blo 291829 4226741 := bstep (se 5 (by rfl) ⟨198128, by rfl⟩ : syracuseStep 4226741 = 396257) B396257
theorem B294583 : Blo 291829 294583 := bstep (se 1 (by rfl) ⟨220937, by rfl⟩ : syracuseStep 294583 = 441875) B441875
theorem B294603 : Blo 291829 294603 := bstep (se 1 (by rfl) ⟨220952, by rfl⟩ : syracuseStep 294603 = 441905) B441905
theorem B294615 : Blo 291829 294615 := bstep (se 1 (by rfl) ⟨220961, by rfl⟩ : syracuseStep 294615 = 441923) B441923
theorem B1998553 : Blo 291829 1998553 := bstep (se 2 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 1998553 = 1498915) B1498915
theorem B1113821 : Blo 291829 1113821 := bstep (se 3 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 1113821 = 417683) B417683
theorem B294635 : Blo 291829 294635 := bstep (se 1 (by rfl) ⟨220976, by rfl⟩ : syracuseStep 294635 = 441953) B441953
theorem B294647 : Blo 291829 294647 := bstep (se 1 (by rfl) ⟨220985, by rfl⟩ : syracuseStep 294647 = 441971) B441971
theorem B294667 : Blo 291829 294667 := bstep (se 1 (by rfl) ⟨221000, by rfl⟩ : syracuseStep 294667 = 442001) B442001
theorem B294679 : Blo 291829 294679 := bstep (se 1 (by rfl) ⟨221009, by rfl⟩ : syracuseStep 294679 = 442019) B442019
theorem B294699 : Blo 291829 294699 := bstep (se 1 (by rfl) ⟨221024, by rfl⟩ : syracuseStep 294699 = 442049) B442049
theorem B294711 : Blo 291829 294711 := bstep (se 1 (by rfl) ⟨221033, by rfl⟩ : syracuseStep 294711 = 442067) B442067
theorem B556865 : Blo 291829 556865 := bstep (se 2 (by rfl) ⟨208824, by rfl⟩ : syracuseStep 556865 = 417649) B417649
theorem B294731 : Blo 291829 294731 := bstep (se 1 (by rfl) ⟨221048, by rfl⟩ : syracuseStep 294731 = 442097) B442097
theorem B294743 : Blo 291829 294743 := bstep (se 1 (by rfl) ⟨221057, by rfl⟩ : syracuseStep 294743 = 442115) B442115
theorem B294763 : Blo 291829 294763 := bstep (se 1 (by rfl) ⟨221072, by rfl⟩ : syracuseStep 294763 = 442145) B442145
theorem B294775 : Blo 291829 294775 := bstep (se 1 (by rfl) ⟨221081, by rfl⟩ : syracuseStep 294775 = 442163) B442163
theorem B294795 : Blo 291829 294795 := bstep (se 1 (by rfl) ⟨221096, by rfl⟩ : syracuseStep 294795 = 442193) B442193
theorem B294807 : Blo 291829 294807 := bstep (se 1 (by rfl) ⟨221105, by rfl⟩ : syracuseStep 294807 = 442211) B442211
theorem B294827 : Blo 291829 294827 := bstep (se 1 (by rfl) ⟨221120, by rfl⟩ : syracuseStep 294827 = 442241) B442241
theorem B294839 : Blo 291829 294839 := bstep (se 1 (by rfl) ⟨221129, by rfl⟩ : syracuseStep 294839 = 442259) B442259
theorem B294859 : Blo 291829 294859 := bstep (se 1 (by rfl) ⟨221144, by rfl⟩ : syracuseStep 294859 = 442289) B442289
theorem B294871 : Blo 291829 294871 := bstep (se 1 (by rfl) ⟨221153, by rfl⟩ : syracuseStep 294871 = 442307) B442307
theorem B294891 : Blo 291829 294891 := bstep (se 1 (by rfl) ⟨221168, by rfl⟩ : syracuseStep 294891 = 442337) B442337
theorem B294919 : Blo 291829 294919 := bstep (se 1 (by rfl) ⟨221189, by rfl⟩ : syracuseStep 294919 = 442379) B442379
theorem B294927 : Blo 291829 294927 := bstep (se 1 (by rfl) ⟨221195, by rfl⟩ : syracuseStep 294927 = 442391) B442391
theorem B1146923 : Blo 291829 1146923 := bstep (se 1 (by rfl) ⟨860192, by rfl⟩ : syracuseStep 1146923 = 1720385) B1720385
theorem B294971 : Blo 291829 294971 := bstep (se 1 (by rfl) ⟨221228, by rfl⟩ : syracuseStep 294971 = 442457) B442457
theorem B295047 : Blo 291829 295047 := bstep (se 1 (by rfl) ⟨221285, by rfl⟩ : syracuseStep 295047 = 442571) B442571
theorem B295055 : Blo 291829 295055 := bstep (se 1 (by rfl) ⟨221291, by rfl⟩ : syracuseStep 295055 = 442583) B442583
theorem B295099 : Blo 291829 295099 := bstep (se 1 (by rfl) ⟨221324, by rfl⟩ : syracuseStep 295099 = 442649) B442649
theorem B295175 : Blo 291829 295175 := bstep (se 1 (by rfl) ⟨221381, by rfl⟩ : syracuseStep 295175 = 442763) B442763
theorem B295183 : Blo 291829 295183 := bstep (se 1 (by rfl) ⟨221387, by rfl⟩ : syracuseStep 295183 = 442775) B442775
theorem B1671461 : Blo 291829 1671461 := bstep (se 4 (by rfl) ⟨156699, by rfl⟩ : syracuseStep 1671461 = 313399) B313399
theorem B295227 : Blo 291829 295227 := bstep (se 1 (by rfl) ⟨221420, by rfl⟩ : syracuseStep 295227 = 442841) B442841
theorem B295303 : Blo 291829 295303 := bstep (se 1 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 295303 = 442955) B442955
theorem B295311 : Blo 291829 295311 := bstep (se 1 (by rfl) ⟨221483, by rfl⟩ : syracuseStep 295311 = 442967) B442967
theorem B295355 : Blo 291829 295355 := bstep (se 1 (by rfl) ⟨221516, by rfl⟩ : syracuseStep 295355 = 443033) B443033
theorem B295431 : Blo 291829 295431 := bstep (se 1 (by rfl) ⟨221573, by rfl⟩ : syracuseStep 295431 = 443147) B443147
theorem B295439 : Blo 291829 295439 := bstep (se 1 (by rfl) ⟨221579, by rfl⟩ : syracuseStep 295439 = 443159) B443159
theorem B295483 : Blo 291829 295483 := bstep (se 1 (by rfl) ⟨221612, by rfl⟩ : syracuseStep 295483 = 443225) B443225
theorem B295559 : Blo 291829 295559 := bstep (se 1 (by rfl) ⟨221669, by rfl⟩ : syracuseStep 295559 = 443339) B443339
theorem B295567 : Blo 291829 295567 := bstep (se 1 (by rfl) ⟨221675, by rfl⟩ : syracuseStep 295567 = 443351) B443351
theorem B295611 : Blo 291829 295611 := bstep (se 1 (by rfl) ⟨221708, by rfl⟩ : syracuseStep 295611 = 443417) B443417
theorem B295687 : Blo 291829 295687 := bstep (se 1 (by rfl) ⟨221765, by rfl⟩ : syracuseStep 295687 = 443531) B443531
theorem B295695 : Blo 291829 295695 := bstep (se 1 (by rfl) ⟨221771, by rfl⟩ : syracuseStep 295695 = 443543) B443543
theorem B557867 : Blo 291829 557867 := bstep (se 1 (by rfl) ⟨418400, by rfl⟩ : syracuseStep 557867 = 836801) B836801
theorem B295739 : Blo 291829 295739 := bstep (se 1 (by rfl) ⟨221804, by rfl⟩ : syracuseStep 295739 = 443609) B443609
theorem B3343193 : Blo 291829 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B295815 : Blo 291829 295815 := bstep (se 1 (by rfl) ⟨221861, by rfl⟩ : syracuseStep 295815 = 443723) B443723
theorem B295823 : Blo 291829 295823 := bstep (se 1 (by rfl) ⟨221867, by rfl⟩ : syracuseStep 295823 = 443735) B443735
theorem B492473 : Blo 291829 492473 := bstep (se 2 (by rfl) ⟨184677, by rfl⟩ : syracuseStep 492473 = 369355) B369355
theorem B328711 : Blo 291829 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B1672235 : Blo 291829 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B6325397 : Blo 291829 6325397 := bstep (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) B296503
theorem B328891 : Blo 291829 328891 := bstep (se 1 (by rfl) ⟨246668, by rfl⟩ : syracuseStep 328891 = 493337) B493337
theorem B13731185 : Blo 291829 13731185 := bstep (se 2 (by rfl) ⟨5149194, by rfl⟩ : syracuseStep 13731185 = 10298389) B10298389
theorem B493175 : Blo 291829 493175 := bstep (se 1 (by rfl) ⟨369881, by rfl⟩ : syracuseStep 493175 = 739763) B739763
theorem B329359 : Blo 291829 329359 := bstep (se 1 (by rfl) ⟨247019, by rfl⟩ : syracuseStep 329359 = 494039) B494039
theorem B1410797 : Blo 291829 1410797 := bstep (se 3 (by rfl) ⟨264524, by rfl⟩ : syracuseStep 1410797 = 529049) B529049
theorem B1247035 : Blo 291829 1247035 := bstep (se 1 (by rfl) ⟨935276, by rfl⟩ : syracuseStep 1247035 = 1870553) B1870553
theorem B1115963 : Blo 291829 1115963 := bstep (se 1 (by rfl) ⟨836972, by rfl⟩ : syracuseStep 1115963 = 1673945) B1673945
theorem B657287 : Blo 291829 657287 := bstep (se 1 (by rfl) ⟨492965, by rfl⟩ : syracuseStep 657287 = 985931) B985931
theorem B1411025 : Blo 291829 1411025 := bstep (se 2 (by rfl) ⟨529134, by rfl⟩ : syracuseStep 1411025 = 1058269) B1058269
theorem B657467 : Blo 291829 657467 := bstep (se 1 (by rfl) ⟨493100, by rfl⟩ : syracuseStep 657467 = 986201) B986201
theorem B493627 : Blo 291829 493627 := bstep (se 1 (by rfl) ⟨370220, by rfl⟩ : syracuseStep 493627 = 740441) B740441
theorem B985175 : Blo 291829 985175 := bstep (se 1 (by rfl) ⟨738881, by rfl⟩ : syracuseStep 985175 = 1477763) B1477763
theorem B329863 : Blo 291829 329863 := bstep (se 1 (by rfl) ⟨247397, by rfl⟩ : syracuseStep 329863 = 494795) B494795
theorem B657593 : Blo 291829 657593 := bstep (se 2 (by rfl) ⟨246597, by rfl⟩ : syracuseStep 657593 = 493195) B493195
theorem B493769 : Blo 291829 493769 := bstep (se 2 (by rfl) ⟨185163, by rfl⟩ : syracuseStep 493769 = 370327) B370327
theorem B1116449 : Blo 291829 1116449 := bstep (se 2 (by rfl) ⟨418668, by rfl⟩ : syracuseStep 1116449 = 837337) B837337
theorem B330043 : Blo 291829 330043 := bstep (se 1 (by rfl) ⟨247532, by rfl⟩ : syracuseStep 330043 = 495065) B495065
theorem B559561 : Blo 291829 559561 := bstep (se 2 (by rfl) ⟨209835, by rfl⟩ : syracuseStep 559561 = 419671) B419671
theorem B1673693 : Blo 291829 1673693 := bstep (se 3 (by rfl) ⟨313817, by rfl⟩ : syracuseStep 1673693 = 627635) B627635
theorem B657935 : Blo 291829 657935 := bstep (se 1 (by rfl) ⟨493451, by rfl⟩ : syracuseStep 657935 = 986903) B986903
theorem B657953 : Blo 291829 657953 := bstep (se 2 (by rfl) ⟨246732, by rfl⟩ : syracuseStep 657953 = 493465) B493465
theorem B985661 : Blo 291829 985661 := bstep (se 3 (by rfl) ⟨184811, by rfl⟩ : syracuseStep 985661 = 369623) B369623
theorem B330511 : Blo 291829 330511 := bstep (se 1 (by rfl) ⟨247883, by rfl⟩ : syracuseStep 330511 = 495767) B495767
theorem B658295 : Blo 291829 658295 := bstep (se 1 (by rfl) ⟨493721, by rfl⟩ : syracuseStep 658295 = 987443) B987443
theorem B494471 : Blo 291829 494471 := bstep (se 1 (by rfl) ⟨370853, by rfl⟩ : syracuseStep 494471 = 741707) B741707
theorem B5639179 : Blo 291829 5639179 := bstep (se 1 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 5639179 = 8458769) B8458769
theorem B658475 : Blo 291829 658475 := bstep (se 1 (by rfl) ⟨493856, by rfl⟩ : syracuseStep 658475 = 987713) B987713
theorem B1117421 : Blo 291829 1117421 := bstep (se 3 (by rfl) ⟨209516, by rfl⟩ : syracuseStep 1117421 = 419033) B419033
theorem B331015 : Blo 291829 331015 := bstep (se 1 (by rfl) ⟨248261, by rfl⟩ : syracuseStep 331015 = 496523) B496523
theorem B658835 : Blo 291829 658835 := bstep (se 1 (by rfl) ⟨494126, by rfl⟩ : syracuseStep 658835 = 988253) B988253
theorem B331195 : Blo 291829 331195 := bstep (se 1 (by rfl) ⟨248396, by rfl⟩ : syracuseStep 331195 = 496793) B496793
theorem B658889 : Blo 291829 658889 := bstep (se 2 (by rfl) ⟨247083, by rfl⟩ : syracuseStep 658889 = 494167) B494167
theorem B757259 : Blo 291829 757259 := bstep (se 1 (by rfl) ⟨567944, by rfl⟩ : syracuseStep 757259 = 1135889) B1135889
theorem B495119 : Blo 291829 495119 := bstep (se 1 (by rfl) ⟨371339, by rfl⟩ : syracuseStep 495119 = 742679) B742679
theorem B1117739 : Blo 291829 1117739 := bstep (se 1 (by rfl) ⟨838304, by rfl⟩ : syracuseStep 1117739 = 1676609) B1676609
theorem B593543 : Blo 291829 593543 := bstep (se 1 (by rfl) ⟨445157, by rfl⟩ : syracuseStep 593543 = 890315) B890315
theorem B331663 : Blo 291829 331663 := bstep (se 1 (by rfl) ⟨248747, by rfl⟩ : syracuseStep 331663 = 497495) B497495
theorem B1347475 : Blo 291829 1347475 := bstep (se 1 (by rfl) ⟨1010606, by rfl⟩ : syracuseStep 1347475 = 2021213) B2021213
theorem B987065 : Blo 291829 987065 := bstep (se 2 (by rfl) ⟨370149, by rfl⟩ : syracuseStep 987065 = 740299) B740299
theorem B495659 : Blo 291829 495659 := bstep (se 1 (by rfl) ⟨371744, by rfl⟩ : syracuseStep 495659 = 743489) B743489
theorem B659591 : Blo 291829 659591 := bstep (se 1 (by rfl) ⟨494693, by rfl⟩ : syracuseStep 659591 = 989387) B989387
theorem B1052909 : Blo 291829 1052909 := bstep (se 3 (by rfl) ⟨197420, by rfl⟩ : syracuseStep 1052909 = 394841) B394841
theorem B659771 : Blo 291829 659771 := bstep (se 1 (by rfl) ⟨494828, by rfl⟩ : syracuseStep 659771 = 989657) B989657
theorem B561467 : Blo 291829 561467 := bstep (se 1 (by rfl) ⟨421100, by rfl⟩ : syracuseStep 561467 = 842201) B842201
theorem B3019139 : Blo 291829 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B332167 : Blo 291829 332167 := bstep (se 1 (by rfl) ⟨249125, by rfl⟩ : syracuseStep 332167 = 498251) B498251
theorem B2920835 : Blo 291829 2920835 := bstep (se 1 (by rfl) ⟨2190626, by rfl⟩ : syracuseStep 2920835 = 4381253) B4381253
theorem B1479059 : Blo 291829 1479059 := bstep (se 1 (by rfl) ⟨1109294, by rfl⟩ : syracuseStep 1479059 = 2218589) B2218589
theorem B659897 : Blo 291829 659897 := bstep (se 2 (by rfl) ⟨247461, by rfl⟩ : syracuseStep 659897 = 494923) B494923
theorem B496057 : Blo 291829 496057 := bstep (se 2 (by rfl) ⟨186021, by rfl⟩ : syracuseStep 496057 = 372043) B372043
theorem B2396675 : Blo 291829 2396675 := bstep (se 1 (by rfl) ⟨1797506, by rfl⟩ : syracuseStep 2396675 = 3595013) B3595013
theorem B987659 : Blo 291829 987659 := bstep (se 1 (by rfl) ⟨740744, by rfl⟩ : syracuseStep 987659 = 1481489) B1481489
theorem B627259 : Blo 291829 627259 := bstep (se 1 (by rfl) ⟨470444, by rfl⟩ : syracuseStep 627259 = 940889) B940889
theorem B332347 : Blo 291829 332347 := bstep (se 1 (by rfl) ⟨249260, by rfl⟩ : syracuseStep 332347 = 498521) B498521
theorem B1413719 : Blo 291829 1413719 := bstep (se 1 (by rfl) ⟨1060289, by rfl⟩ : syracuseStep 1413719 = 2120579) B2120579
theorem B987767 : Blo 291829 987767 := bstep (se 1 (by rfl) ⟨740825, by rfl⟩ : syracuseStep 987767 = 1481651) B1481651
theorem B660239 : Blo 291829 660239 := bstep (se 1 (by rfl) ⟨495179, by rfl⟩ : syracuseStep 660239 = 990359) B990359
theorem B660257 : Blo 291829 660257 := bstep (se 2 (by rfl) ⟨247596, by rfl⟩ : syracuseStep 660257 = 495193) B495193
theorem B660599 : Blo 291829 660599 := bstep (se 1 (by rfl) ⟨495449, by rfl⟩ : syracuseStep 660599 = 990899) B990899
theorem B496759 : Blo 291829 496759 := bstep (se 1 (by rfl) ⟨372569, by rfl⟩ : syracuseStep 496759 = 745139) B745139
theorem B988361 : Blo 291829 988361 := bstep (se 2 (by rfl) ⟨370635, by rfl⟩ : syracuseStep 988361 = 741271) B741271
theorem B660779 : Blo 291829 660779 := bstep (se 1 (by rfl) ⟨495584, by rfl⟩ : syracuseStep 660779 = 991169) B991169
theorem B496955 : Blo 291829 496955 := bstep (se 1 (by rfl) ⟨372716, by rfl⟩ : syracuseStep 496955 = 745433) B745433
theorem B1676861 : Blo 291829 1676861 := bstep (se 3 (by rfl) ⟨314411, by rfl⟩ : syracuseStep 1676861 = 628823) B628823
theorem B1873475 : Blo 291829 1873475 := bstep (se 1 (by rfl) ⟨1405106, by rfl⟩ : syracuseStep 1873475 = 2810213) B2810213
theorem B661139 : Blo 291829 661139 := bstep (se 1 (by rfl) ⟨495854, by rfl⟩ : syracuseStep 661139 = 991709) B991709
theorem B661193 : Blo 291829 661193 := bstep (se 2 (by rfl) ⟨247947, by rfl⟩ : syracuseStep 661193 = 495895) B495895
theorem B497353 : Blo 291829 497353 := bstep (se 2 (by rfl) ⟨186507, by rfl⟩ : syracuseStep 497353 = 373015) B373015
theorem B2496257 : Blo 291829 2496257 := bstep (se 2 (by rfl) ⟨936096, by rfl⟩ : syracuseStep 2496257 = 1872193) B1872193
theorem B1775495 : Blo 291829 1775495 := bstep (se 1 (by rfl) ⟨1331621, by rfl⟩ : syracuseStep 1775495 = 2663243) B2663243
theorem B989063 : Blo 291829 989063 := bstep (se 1 (by rfl) ⟨741797, by rfl⟩ : syracuseStep 989063 = 1483595) B1483595
theorem B890777 : Blo 291829 890777 := bstep (se 2 (by rfl) ⟨334041, by rfl⟩ : syracuseStep 890777 = 668083) B668083
theorem B2693017 : Blo 291829 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B1578973 : Blo 291829 1578973 := bstep (se 3 (by rfl) ⟨296057, by rfl⟩ : syracuseStep 1578973 = 592115) B592115
theorem B989441 : Blo 291829 989441 := bstep (se 2 (by rfl) ⟨371040, by rfl⟩ : syracuseStep 989441 = 742081) B742081
theorem B4233485 : Blo 291829 4233485 := bstep (se 3 (by rfl) ⟨793778, by rfl⟩ : syracuseStep 4233485 = 1587557) B1587557
theorem B530807 : Blo 291829 530807 := bstep (se 1 (by rfl) ⟨398105, by rfl⟩ : syracuseStep 530807 = 796211) B796211
theorem B661895 : Blo 291829 661895 := bstep (se 1 (by rfl) ⟨496421, by rfl⟩ : syracuseStep 661895 = 992843) B992843
theorem B498055 : Blo 291829 498055 := bstep (se 1 (by rfl) ⟨373541, by rfl⟩ : syracuseStep 498055 = 747083) B747083
theorem B662075 : Blo 291829 662075 := bstep (se 1 (by rfl) ⟨496556, by rfl⟩ : syracuseStep 662075 = 993113) B993113
theorem B662201 : Blo 291829 662201 := bstep (se 2 (by rfl) ⟨248325, by rfl⟩ : syracuseStep 662201 = 496651) B496651
theorem B629651 : Blo 291829 629651 := bstep (se 1 (by rfl) ⟨472238, by rfl⟩ : syracuseStep 629651 = 944477) B944477
theorem B662543 : Blo 291829 662543 := bstep (se 1 (by rfl) ⟨496907, by rfl⟩ : syracuseStep 662543 = 993815) B993815
theorem B498703 : Blo 291829 498703 := bstep (se 1 (by rfl) ⟨374027, by rfl⟩ : syracuseStep 498703 = 748055) B748055
theorem B1121309 : Blo 291829 1121309 := bstep (se 3 (by rfl) ⟨210245, by rfl⟩ : syracuseStep 1121309 = 420491) B420491
theorem B662561 : Blo 291829 662561 := bstep (se 2 (by rfl) ⟨248460, by rfl⟩ : syracuseStep 662561 = 496921) B496921
theorem B990251 : Blo 291829 990251 := bstep (se 1 (by rfl) ⟨742688, by rfl⟩ : syracuseStep 990251 = 1485377) B1485377
theorem B1121323 : Blo 291829 1121323 := bstep (se 1 (by rfl) ⟨840992, by rfl⟩ : syracuseStep 1121323 = 1681985) B1681985
theorem B662903 : Blo 291829 662903 := bstep (se 1 (by rfl) ⟨497177, by rfl⟩ : syracuseStep 662903 = 994355) B994355
theorem B1482137 : Blo 291829 1482137 := bstep (se 2 (by rfl) ⟨555801, by rfl⟩ : syracuseStep 1482137 = 1111603) B1111603
theorem B663083 : Blo 291829 663083 := bstep (se 1 (by rfl) ⟨497312, by rfl⟩ : syracuseStep 663083 = 994625) B994625
theorem B7118405 : Blo 291829 7118405 := bstep (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) B1334701
theorem B1056527 : Blo 291829 1056527 := bstep (se 1 (by rfl) ⟨792395, by rfl⟩ : syracuseStep 1056527 = 1584791) B1584791
theorem B5119793 : Blo 291829 5119793 := bstep (se 2 (by rfl) ⟨1919922, by rfl⟩ : syracuseStep 5119793 = 3839845) B3839845
theorem B1679251 : Blo 291829 1679251 := bstep (se 1 (by rfl) ⟨1259438, by rfl⟩ : syracuseStep 1679251 = 2518877) B2518877
theorem B663443 : Blo 291829 663443 := bstep (se 1 (by rfl) ⟨497582, by rfl⟩ : syracuseStep 663443 = 995165) B995165
theorem B794569 : Blo 291829 794569 := bstep (se 2 (by rfl) ⟨297963, by rfl⟩ : syracuseStep 794569 = 595927) B595927
theorem B663497 : Blo 291829 663497 := bstep (se 2 (by rfl) ⟨248811, by rfl⟩ : syracuseStep 663497 = 497623) B497623
theorem B2498647 : Blo 291829 2498647 := bstep (se 1 (by rfl) ⟨1873985, by rfl⟩ : syracuseStep 2498647 = 3747971) B3747971
theorem B893015 : Blo 291829 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B1187959 : Blo 291829 1187959 := bstep (se 1 (by rfl) ⟨890969, by rfl⟩ : syracuseStep 1187959 = 1781939) B1781939
theorem B1056887 : Blo 291829 1056887 := bstep (se 1 (by rfl) ⟨792665, by rfl⟩ : syracuseStep 1056887 = 1585331) B1585331
theorem B1417409 : Blo 291829 1417409 := bstep (se 2 (by rfl) ⟨531528, by rfl⟩ : syracuseStep 1417409 = 1063057) B1063057
theorem B565537 : Blo 291829 565537 := bstep (se 2 (by rfl) ⟨212076, by rfl⟩ : syracuseStep 565537 = 424153) B424153
theorem B991547 : Blo 291829 991547 := bstep (se 1 (by rfl) ⟨743660, by rfl⟩ : syracuseStep 991547 = 1487321) B1487321
theorem B1188413 : Blo 291829 1188413 := bstep (se 3 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 1188413 = 445655) B445655
theorem B893501 : Blo 291829 893501 := bstep (se 3 (by rfl) ⟨167531, by rfl⟩ : syracuseStep 893501 = 335063) B335063
theorem B664199 : Blo 291829 664199 := bstep (se 1 (by rfl) ⟨498149, by rfl⟩ : syracuseStep 664199 = 996299) B996299
theorem B992033 : Blo 291829 992033 := bstep (se 2 (by rfl) ⟨372012, by rfl⟩ : syracuseStep 992033 = 744025) B744025
theorem B369451 : Blo 291829 369451 := bstep (se 1 (by rfl) ⟨277088, by rfl⟩ : syracuseStep 369451 = 554177) B554177
theorem B664379 : Blo 291829 664379 := bstep (se 1 (by rfl) ⟨498284, by rfl⟩ : syracuseStep 664379 = 996569) B996569
theorem B467831 : Blo 291829 467831 := bstep (se 1 (by rfl) ⟨350873, by rfl⟩ : syracuseStep 467831 = 701747) B701747
theorem B664505 : Blo 291829 664505 := bstep (se 2 (by rfl) ⟨249189, by rfl⟩ : syracuseStep 664505 = 498379) B498379
theorem B533519 : Blo 291829 533519 := bstep (se 1 (by rfl) ⟨400139, by rfl⟩ : syracuseStep 533519 = 800279) B800279
theorem B369679 : Blo 291829 369679 := bstep (se 1 (by rfl) ⟨277259, by rfl⟩ : syracuseStep 369679 = 554519) B554519
theorem B1877165 : Blo 291829 1877165 := bstep (se 3 (by rfl) ⟨351968, by rfl⟩ : syracuseStep 1877165 = 703937) B703937
theorem B402617 : Blo 291829 402617 := bstep (se 2 (by rfl) ⟨150981, by rfl⟩ : syracuseStep 402617 = 301963) B301963
theorem B664847 : Blo 291829 664847 := bstep (se 1 (by rfl) ⟨498635, by rfl⟩ : syracuseStep 664847 = 997271) B997271
theorem B664865 : Blo 291829 664865 := bstep (se 2 (by rfl) ⟨249324, by rfl⟩ : syracuseStep 664865 = 498649) B498649
theorem B992627 : Blo 291829 992627 := bstep (se 1 (by rfl) ⟨744470, by rfl⟩ : syracuseStep 992627 = 1488941) B1488941
theorem B468343 : Blo 291829 468343 := bstep (se 1 (by rfl) ⟨351257, by rfl⟩ : syracuseStep 468343 = 702515) B702515
theorem B1254791 : Blo 291829 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B4072913 : Blo 291829 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B5678545 : Blo 291829 5678545 := bstep (se 2 (by rfl) ⟨2129454, by rfl⟩ : syracuseStep 5678545 = 4258909) B4258909
theorem B1418755 : Blo 291829 1418755 := bstep (se 1 (by rfl) ⟨1064066, by rfl⟩ : syracuseStep 1418755 = 2128133) B2128133
theorem B2238029 : Blo 291829 2238029 := bstep (se 3 (by rfl) ⟨419630, by rfl⟩ : syracuseStep 2238029 = 839261) B839261
theorem B1680983 : Blo 291829 1680983 := bstep (se 1 (by rfl) ⟨1260737, by rfl⟩ : syracuseStep 1680983 = 2521475) B2521475
theorem B468599 : Blo 291829 468599 := bstep (se 1 (by rfl) ⟨351449, by rfl⟩ : syracuseStep 468599 = 702899) B702899
theorem B665207 : Blo 291829 665207 := bstep (se 1 (by rfl) ⟨498905, by rfl⟩ : syracuseStep 665207 = 997811) B997811
theorem B370423 : Blo 291829 370423 := bstep (se 1 (by rfl) ⟨277817, by rfl⟩ : syracuseStep 370423 = 555635) B555635
theorem B4499201 : Blo 291829 4499201 := bstep (se 2 (by rfl) ⟨1687200, by rfl⟩ : syracuseStep 4499201 = 3374401) B3374401
theorem B567073 : Blo 291829 567073 := bstep (se 2 (by rfl) ⟨212652, by rfl⟩ : syracuseStep 567073 = 425305) B425305
theorem B665387 : Blo 291829 665387 := bstep (se 1 (by rfl) ⟨499040, by rfl⟩ : syracuseStep 665387 = 998081) B998081
theorem B1025939 : Blo 291829 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B1484729 : Blo 291829 1484729 := bstep (se 2 (by rfl) ⟨556773, by rfl⟩ : syracuseStep 1484729 = 1113547) B1113547
theorem B2500631 : Blo 291829 2500631 := bstep (se 1 (by rfl) ⟨1875473, by rfl⟩ : syracuseStep 2500631 = 3750947) B3750947
theorem B370747 : Blo 291829 370747 := bstep (se 1 (by rfl) ⟨278060, by rfl⟩ : syracuseStep 370747 = 556121) B556121
theorem B2664737 : Blo 291829 2664737 := bstep (se 2 (by rfl) ⟨999276, by rfl⟩ : syracuseStep 2664737 = 1998553) B1998553
theorem B1288601 : Blo 291829 1288601 := bstep (se 2 (by rfl) ⟨483225, by rfl⟩ : syracuseStep 1288601 = 966451) B966451
theorem B371243 : Blo 291829 371243 := bstep (se 1 (by rfl) ⟨278432, by rfl⟩ : syracuseStep 371243 = 556865) B556865
theorem B371719 : Blo 291829 371719 := bstep (se 1 (by rfl) ⟨278789, by rfl⟩ : syracuseStep 371719 = 557579) B557579
theorem B1486025 : Blo 291829 1486025 := bstep (se 2 (by rfl) ⟨557259, by rfl⟩ : syracuseStep 1486025 = 1114519) B1114519
theorem B1256705 : Blo 291829 1256705 := bstep (se 2 (by rfl) ⟨471264, by rfl⟩ : syracuseStep 1256705 = 942529) B942529
theorem B798137 : Blo 291829 798137 := bstep (se 2 (by rfl) ⟨299301, by rfl⟩ : syracuseStep 798137 = 598603) B598603
theorem B1420753 : Blo 291829 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B372215 : Blo 291829 372215 := bstep (se 1 (by rfl) ⟨279161, by rfl⟩ : syracuseStep 372215 = 558323) B558323
theorem B437819 : Blo 291829 437819 := bstep (se 1 (by rfl) ⟨328364, by rfl⟩ : syracuseStep 437819 = 656729) B656729
theorem B437879 : Blo 291829 437879 := bstep (se 1 (by rfl) ⟨328409, by rfl⟩ : syracuseStep 437879 = 656819) B656819
theorem B437903 : Blo 291829 437903 := bstep (se 1 (by rfl) ⟨328427, by rfl⟩ : syracuseStep 437903 = 656855) B656855
theorem B372367 : Blo 291829 372367 := bstep (se 1 (by rfl) ⟨279275, by rfl⟩ : syracuseStep 372367 = 558551) B558551
theorem B437945 : Blo 291829 437945 := bstep (se 2 (by rfl) ⟨164229, by rfl⟩ : syracuseStep 437945 = 328459) B328459
theorem B438023 : Blo 291829 438023 := bstep (se 1 (by rfl) ⟨328517, by rfl⟩ : syracuseStep 438023 = 657035) B657035
theorem B438059 : Blo 291829 438059 := bstep (se 1 (by rfl) ⟨328544, by rfl⟩ : syracuseStep 438059 = 657089) B657089
theorem B372539 : Blo 291829 372539 := bstep (se 1 (by rfl) ⟨279404, by rfl⟩ : syracuseStep 372539 = 558809) B558809
theorem B438089 : Blo 291829 438089 := bstep (se 2 (by rfl) ⟨164283, by rfl⟩ : syracuseStep 438089 = 328567) B328567
theorem B831379 : Blo 291829 831379 := bstep (se 1 (by rfl) ⟨623534, by rfl⟩ : syracuseStep 831379 = 1247069) B1247069
theorem B995219 : Blo 291829 995219 := bstep (se 1 (by rfl) ⟨746414, by rfl⟩ : syracuseStep 995219 = 1492829) B1492829
theorem B438203 : Blo 291829 438203 := bstep (se 1 (by rfl) ⟨328652, by rfl⟩ : syracuseStep 438203 = 657305) B657305
theorem B2240459 : Blo 291829 2240459 := bstep (se 1 (by rfl) ⟨1680344, by rfl⟩ : syracuseStep 2240459 = 3360689) B3360689
theorem B438263 : Blo 291829 438263 := bstep (se 1 (by rfl) ⟨328697, by rfl⟩ : syracuseStep 438263 = 657395) B657395
theorem B438287 : Blo 291829 438287 := bstep (se 1 (by rfl) ⟨328715, by rfl⟩ : syracuseStep 438287 = 657431) B657431
theorem B438329 : Blo 291829 438329 := bstep (se 2 (by rfl) ⟨164373, by rfl⟩ : syracuseStep 438329 = 328747) B328747
theorem B438407 : Blo 291829 438407 := bstep (se 1 (by rfl) ⟨328805, by rfl⟩ : syracuseStep 438407 = 657611) B657611
theorem B438443 : Blo 291829 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B438473 : Blo 291829 438473 := bstep (se 2 (by rfl) ⟨164427, by rfl⟩ : syracuseStep 438473 = 328855) B328855
theorem B438587 : Blo 291829 438587 := bstep (se 1 (by rfl) ⟨328940, by rfl⟩ : syracuseStep 438587 = 657881) B657881
theorem B438647 : Blo 291829 438647 := bstep (se 1 (by rfl) ⟨328985, by rfl⟩ : syracuseStep 438647 = 657971) B657971
theorem B438671 : Blo 291829 438671 := bstep (se 1 (by rfl) ⟨329003, by rfl⟩ : syracuseStep 438671 = 658007) B658007
theorem B438713 : Blo 291829 438713 := bstep (se 2 (by rfl) ⟨164517, by rfl⟩ : syracuseStep 438713 = 329035) B329035
theorem B438791 : Blo 291829 438791 := bstep (se 1 (by rfl) ⟨329093, by rfl⟩ : syracuseStep 438791 = 658187) B658187
theorem B438827 : Blo 291829 438827 := bstep (se 1 (by rfl) ⟨329120, by rfl⟩ : syracuseStep 438827 = 658241) B658241
theorem B3551809 : Blo 291829 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B3781187 : Blo 291829 3781187 := bstep (se 1 (by rfl) ⟨2835890, by rfl⟩ : syracuseStep 3781187 = 5671781) B5671781
theorem B438857 : Blo 291829 438857 := bstep (se 2 (by rfl) ⟨164571, by rfl⟩ : syracuseStep 438857 = 329143) B329143
theorem B438971 : Blo 291829 438971 := bstep (se 1 (by rfl) ⟨329228, by rfl⟩ : syracuseStep 438971 = 658457) B658457
theorem B439031 : Blo 291829 439031 := bstep (se 1 (by rfl) ⟨329273, by rfl⟩ : syracuseStep 439031 = 658547) B658547
theorem B373511 : Blo 291829 373511 := bstep (se 1 (by rfl) ⟨280133, by rfl⟩ : syracuseStep 373511 = 560267) B560267
theorem B439055 : Blo 291829 439055 := bstep (se 1 (by rfl) ⟨329291, by rfl⟩ : syracuseStep 439055 = 658583) B658583
theorem B439097 : Blo 291829 439097 := bstep (se 2 (by rfl) ⟨164661, by rfl⟩ : syracuseStep 439097 = 329323) B329323
theorem B439175 : Blo 291829 439175 := bstep (se 1 (by rfl) ⟨329381, by rfl⟩ : syracuseStep 439175 = 658763) B658763
theorem B439211 : Blo 291829 439211 := bstep (se 1 (by rfl) ⟨329408, by rfl⟩ : syracuseStep 439211 = 658817) B658817
theorem B439241 : Blo 291829 439241 := bstep (se 2 (by rfl) ⟨164715, by rfl⟩ : syracuseStep 439241 = 329431) B329431
theorem B439355 : Blo 291829 439355 := bstep (se 1 (by rfl) ⟨329516, by rfl⟩ : syracuseStep 439355 = 659033) B659033
theorem B439415 : Blo 291829 439415 := bstep (se 1 (by rfl) ⟨329561, by rfl⟩ : syracuseStep 439415 = 659123) B659123
theorem B439439 : Blo 291829 439439 := bstep (se 1 (by rfl) ⟨329579, by rfl⟩ : syracuseStep 439439 = 659159) B659159
theorem B439481 : Blo 291829 439481 := bstep (se 2 (by rfl) ⟨164805, by rfl⟩ : syracuseStep 439481 = 329611) B329611
theorem B439559 : Blo 291829 439559 := bstep (se 1 (by rfl) ⟨329669, by rfl⟩ : syracuseStep 439559 = 659339) B659339
theorem B996623 : Blo 291829 996623 := bstep (se 1 (by rfl) ⟨747467, by rfl⟩ : syracuseStep 996623 = 1494935) B1494935
theorem B439595 : Blo 291829 439595 := bstep (se 1 (by rfl) ⟨329696, by rfl⟩ : syracuseStep 439595 = 659393) B659393
theorem B439625 : Blo 291829 439625 := bstep (se 2 (by rfl) ⟨164859, by rfl⟩ : syracuseStep 439625 = 329719) B329719
theorem B374159 : Blo 291829 374159 := bstep (se 1 (by rfl) ⟨280619, by rfl⟩ : syracuseStep 374159 = 561239) B561239
theorem B5092793 : Blo 291829 5092793 := bstep (se 2 (by rfl) ⟨1909797, by rfl⟩ : syracuseStep 5092793 = 3819595) B3819595
theorem B439739 : Blo 291829 439739 := bstep (se 1 (by rfl) ⟨329804, by rfl⟩ : syracuseStep 439739 = 659609) B659609
theorem B439799 : Blo 291829 439799 := bstep (se 1 (by rfl) ⟨329849, by rfl⟩ : syracuseStep 439799 = 659699) B659699
theorem B439823 : Blo 291829 439823 := bstep (se 1 (by rfl) ⟨329867, by rfl⟩ : syracuseStep 439823 = 659735) B659735
theorem B996893 : Blo 291829 996893 := bstep (se 3 (by rfl) ⟨186917, by rfl⟩ : syracuseStep 996893 = 373835) B373835
theorem B439865 : Blo 291829 439865 := bstep (se 2 (by rfl) ⟨164949, by rfl⟩ : syracuseStep 439865 = 329899) B329899
theorem B833111 : Blo 291829 833111 := bstep (se 1 (by rfl) ⟨624833, by rfl⟩ : syracuseStep 833111 = 1249667) B1249667
theorem B439943 : Blo 291829 439943 := bstep (se 1 (by rfl) ⟨329957, by rfl⟩ : syracuseStep 439943 = 659915) B659915
theorem B439979 : Blo 291829 439979 := bstep (se 1 (by rfl) ⟨329984, by rfl⟩ : syracuseStep 439979 = 659969) B659969
theorem B440009 : Blo 291829 440009 := bstep (se 2 (by rfl) ⟨165003, by rfl⟩ : syracuseStep 440009 = 330007) B330007
theorem B440123 : Blo 291829 440123 := bstep (se 1 (by rfl) ⟨330092, by rfl⟩ : syracuseStep 440123 = 660185) B660185
theorem B1587059 : Blo 291829 1587059 := bstep (se 1 (by rfl) ⟨1190294, by rfl⟩ : syracuseStep 1587059 = 2380589) B2380589
theorem B440183 : Blo 291829 440183 := bstep (se 1 (by rfl) ⟨330137, by rfl⟩ : syracuseStep 440183 = 660275) B660275
theorem B440207 : Blo 291829 440207 := bstep (se 1 (by rfl) ⟨330155, by rfl⟩ : syracuseStep 440207 = 660311) B660311
theorem B702361 : Blo 291829 702361 := bstep (se 2 (by rfl) ⟨263385, by rfl⟩ : syracuseStep 702361 = 526771) B526771
theorem B440249 : Blo 291829 440249 := bstep (se 2 (by rfl) ⟨165093, by rfl⟩ : syracuseStep 440249 = 330187) B330187
theorem B440327 : Blo 291829 440327 := bstep (se 1 (by rfl) ⟨330245, by rfl⟩ : syracuseStep 440327 = 660491) B660491
theorem B440363 : Blo 291829 440363 := bstep (se 1 (by rfl) ⟨330272, by rfl⟩ : syracuseStep 440363 = 660545) B660545
theorem B440393 : Blo 291829 440393 := bstep (se 2 (by rfl) ⟨165147, by rfl⟩ : syracuseStep 440393 = 330295) B330295
theorem B440507 : Blo 291829 440507 := bstep (se 1 (by rfl) ⟨330380, by rfl⟩ : syracuseStep 440507 = 660761) B660761
theorem B440567 : Blo 291829 440567 := bstep (se 1 (by rfl) ⟨330425, by rfl⟩ : syracuseStep 440567 = 660851) B660851
theorem B440591 : Blo 291829 440591 := bstep (se 1 (by rfl) ⟨330443, by rfl⟩ : syracuseStep 440591 = 660887) B660887
theorem B440633 : Blo 291829 440633 := bstep (se 2 (by rfl) ⟨165237, by rfl⟩ : syracuseStep 440633 = 330475) B330475
theorem B440711 : Blo 291829 440711 := bstep (se 1 (by rfl) ⟨330533, by rfl⟩ : syracuseStep 440711 = 661067) B661067
theorem B440747 : Blo 291829 440747 := bstep (se 1 (by rfl) ⟨330560, by rfl⟩ : syracuseStep 440747 = 661121) B661121
theorem B440777 : Blo 291829 440777 := bstep (se 2 (by rfl) ⟨165291, by rfl⟩ : syracuseStep 440777 = 330583) B330583
theorem B375355 : Blo 291829 375355 := bstep (se 1 (by rfl) ⟨281516, by rfl⟩ : syracuseStep 375355 = 563033) B563033
theorem B440891 : Blo 291829 440891 := bstep (se 1 (by rfl) ⟨330668, by rfl⟩ : syracuseStep 440891 = 661337) B661337
theorem B440951 : Blo 291829 440951 := bstep (se 1 (by rfl) ⟨330713, by rfl⟩ : syracuseStep 440951 = 661427) B661427
theorem B440975 : Blo 291829 440975 := bstep (se 1 (by rfl) ⟨330731, by rfl⟩ : syracuseStep 440975 = 661463) B661463
theorem B441017 : Blo 291829 441017 := bstep (se 2 (by rfl) ⟨165381, by rfl⟩ : syracuseStep 441017 = 330763) B330763
theorem B441095 : Blo 291829 441095 := bstep (se 1 (by rfl) ⟨330821, by rfl⟩ : syracuseStep 441095 = 661643) B661643
theorem B441131 : Blo 291829 441131 := bstep (se 1 (by rfl) ⟨330848, by rfl⟩ : syracuseStep 441131 = 661697) B661697
theorem B441161 : Blo 291829 441161 := bstep (se 2 (by rfl) ⟨165435, by rfl⟩ : syracuseStep 441161 = 330871) B330871
theorem B998297 : Blo 291829 998297 := bstep (se 2 (by rfl) ⟨374361, by rfl⟩ : syracuseStep 998297 = 748723) B748723
theorem B441275 : Blo 291829 441275 := bstep (se 1 (by rfl) ⟨330956, by rfl⟩ : syracuseStep 441275 = 661913) B661913
theorem B441335 : Blo 291829 441335 := bstep (se 1 (by rfl) ⟨331001, by rfl⟩ : syracuseStep 441335 = 662003) B662003
theorem B441359 : Blo 291829 441359 := bstep (se 1 (by rfl) ⟨331019, by rfl⟩ : syracuseStep 441359 = 662039) B662039
theorem B441401 : Blo 291829 441401 := bstep (se 2 (by rfl) ⟨165525, by rfl⟩ : syracuseStep 441401 = 331051) B331051
theorem B834695 : Blo 291829 834695 := bstep (se 1 (by rfl) ⟨626021, by rfl⟩ : syracuseStep 834695 = 1252043) B1252043
theorem B441479 : Blo 291829 441479 := bstep (se 1 (by rfl) ⟨331109, by rfl⟩ : syracuseStep 441479 = 662219) B662219
theorem B441515 : Blo 291829 441515 := bstep (se 1 (by rfl) ⟨331136, by rfl⟩ : syracuseStep 441515 = 662273) B662273
theorem B441545 : Blo 291829 441545 := bstep (se 2 (by rfl) ⟨165579, by rfl⟩ : syracuseStep 441545 = 331159) B331159
theorem B703745 : Blo 291829 703745 := bstep (se 2 (by rfl) ⟨263904, by rfl⟩ : syracuseStep 703745 = 527809) B527809
theorem B441659 : Blo 291829 441659 := bstep (se 1 (by rfl) ⟨331244, by rfl⟩ : syracuseStep 441659 = 662489) B662489
theorem B441719 : Blo 291829 441719 := bstep (se 1 (by rfl) ⟨331289, by rfl⟩ : syracuseStep 441719 = 662579) B662579
theorem B441743 : Blo 291829 441743 := bstep (se 1 (by rfl) ⟨331307, by rfl⟩ : syracuseStep 441743 = 662615) B662615
theorem B441785 : Blo 291829 441785 := bstep (se 2 (by rfl) ⟨165669, by rfl⟩ : syracuseStep 441785 = 331339) B331339
theorem B441863 : Blo 291829 441863 := bstep (se 1 (by rfl) ⟨331397, by rfl⟩ : syracuseStep 441863 = 662795) B662795
theorem B441899 : Blo 291829 441899 := bstep (se 1 (by rfl) ⟨331424, by rfl⟩ : syracuseStep 441899 = 662849) B662849
theorem B441929 : Blo 291829 441929 := bstep (se 2 (by rfl) ⟨165723, by rfl⟩ : syracuseStep 441929 = 331447) B331447
theorem B442043 : Blo 291829 442043 := bstep (se 1 (by rfl) ⟨331532, by rfl⟩ : syracuseStep 442043 = 663065) B663065
theorem B442103 : Blo 291829 442103 := bstep (se 1 (by rfl) ⟨331577, by rfl⟩ : syracuseStep 442103 = 663155) B663155
theorem B3325697 : Blo 291829 3325697 := bstep (se 2 (by rfl) ⟨1247136, by rfl⟩ : syracuseStep 3325697 = 2494273) B2494273
theorem B835343 : Blo 291829 835343 := bstep (se 1 (by rfl) ⟨626507, by rfl⟩ : syracuseStep 835343 = 1253015) B1253015
theorem B442127 : Blo 291829 442127 := bstep (se 1 (by rfl) ⟨331595, by rfl⟩ : syracuseStep 442127 = 663191) B663191
theorem B442169 : Blo 291829 442169 := bstep (se 2 (by rfl) ⟨165813, by rfl⟩ : syracuseStep 442169 = 331627) B331627
theorem B442247 : Blo 291829 442247 := bstep (se 1 (by rfl) ⟨331685, by rfl⟩ : syracuseStep 442247 = 663371) B663371
theorem B442283 : Blo 291829 442283 := bstep (se 1 (by rfl) ⟨331712, by rfl⟩ : syracuseStep 442283 = 663425) B663425
theorem B442313 : Blo 291829 442313 := bstep (se 2 (by rfl) ⟨165867, by rfl⟩ : syracuseStep 442313 = 331735) B331735
theorem B10665931 : Blo 291829 10665931 := bstep (se 1 (by rfl) ⟨7999448, by rfl⟩ : syracuseStep 10665931 = 15998897) B15998897
theorem B442427 : Blo 291829 442427 := bstep (se 1 (by rfl) ⟨331820, by rfl⟩ : syracuseStep 442427 = 663641) B663641
theorem B442487 : Blo 291829 442487 := bstep (se 1 (by rfl) ⟨331865, by rfl⟩ : syracuseStep 442487 = 663731) B663731
theorem B442511 : Blo 291829 442511 := bstep (se 1 (by rfl) ⟨331883, by rfl⟩ : syracuseStep 442511 = 663767) B663767
theorem B704659 : Blo 291829 704659 := bstep (se 1 (by rfl) ⟨528494, by rfl⟩ : syracuseStep 704659 = 1056989) B1056989
theorem B3784877 : Blo 291829 3784877 := bstep (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) B1419329
theorem B442553 : Blo 291829 442553 := bstep (se 2 (by rfl) ⟨165957, by rfl⟩ : syracuseStep 442553 = 331915) B331915
theorem B442631 : Blo 291829 442631 := bstep (se 1 (by rfl) ⟨331973, by rfl⟩ : syracuseStep 442631 = 663947) B663947
theorem B442667 : Blo 291829 442667 := bstep (se 1 (by rfl) ⟨332000, by rfl⟩ : syracuseStep 442667 = 664001) B664001
theorem B442697 : Blo 291829 442697 := bstep (se 2 (by rfl) ⟨166011, by rfl⟩ : syracuseStep 442697 = 332023) B332023
theorem B442811 : Blo 291829 442811 := bstep (se 1 (by rfl) ⟨332108, by rfl⟩ : syracuseStep 442811 = 664217) B664217
theorem B442871 : Blo 291829 442871 := bstep (se 1 (by rfl) ⟨332153, by rfl⟩ : syracuseStep 442871 = 664307) B664307
theorem B442895 : Blo 291829 442895 := bstep (se 1 (by rfl) ⟨332171, by rfl⟩ : syracuseStep 442895 = 664343) B664343
theorem B442937 : Blo 291829 442937 := bstep (se 2 (by rfl) ⟨166101, by rfl⟩ : syracuseStep 442937 = 332203) B332203
theorem B1589827 : Blo 291829 1589827 := bstep (se 1 (by rfl) ⟨1192370, by rfl⟩ : syracuseStep 1589827 = 2384741) B2384741
theorem B443015 : Blo 291829 443015 := bstep (se 1 (by rfl) ⟨332261, by rfl⟩ : syracuseStep 443015 = 664523) B664523
theorem B443051 : Blo 291829 443051 := bstep (se 1 (by rfl) ⟨332288, by rfl⟩ : syracuseStep 443051 = 664577) B664577
theorem B443081 : Blo 291829 443081 := bstep (se 2 (by rfl) ⟨166155, by rfl⟩ : syracuseStep 443081 = 332311) B332311
theorem B607019 : Blo 291829 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B672571 : Blo 291829 672571 := bstep (se 1 (by rfl) ⟨504428, by rfl⟩ : syracuseStep 672571 = 1008857) B1008857
theorem B443195 : Blo 291829 443195 := bstep (se 1 (by rfl) ⟨332396, by rfl⟩ : syracuseStep 443195 = 664793) B664793
theorem B443255 : Blo 291829 443255 := bstep (se 1 (by rfl) ⟨332441, by rfl⟩ : syracuseStep 443255 = 664883) B664883
theorem B443279 : Blo 291829 443279 := bstep (se 1 (by rfl) ⟨332459, by rfl⟩ : syracuseStep 443279 = 664919) B664919
theorem B1491857 : Blo 291829 1491857 := bstep (se 2 (by rfl) ⟨559446, by rfl⟩ : syracuseStep 1491857 = 1118893) B1118893
theorem B443321 : Blo 291829 443321 := bstep (se 2 (by rfl) ⟨166245, by rfl⟩ : syracuseStep 443321 = 332491) B332491
theorem B443399 : Blo 291829 443399 := bstep (se 1 (by rfl) ⟨332549, by rfl⟩ : syracuseStep 443399 = 665099) B665099
theorem B443435 : Blo 291829 443435 := bstep (se 1 (by rfl) ⟨332576, by rfl⟩ : syracuseStep 443435 = 665153) B665153
theorem B443465 : Blo 291829 443465 := bstep (se 2 (by rfl) ⟨166299, by rfl⟩ : syracuseStep 443465 = 332599) B332599
theorem B5653637 : Blo 291829 5653637 := bstep (se 4 (by rfl) ⟨530028, by rfl⟩ : syracuseStep 5653637 = 1060057) B1060057
theorem B2245805 : Blo 291829 2245805 := bstep (se 3 (by rfl) ⟨421088, by rfl⟩ : syracuseStep 2245805 = 842177) B842177
theorem B443579 : Blo 291829 443579 := bstep (se 1 (by rfl) ⟨332684, by rfl⟩ : syracuseStep 443579 = 665369) B665369
theorem B443639 : Blo 291829 443639 := bstep (se 1 (by rfl) ⟨332729, by rfl⟩ : syracuseStep 443639 = 665459) B665459
theorem B443663 : Blo 291829 443663 := bstep (se 1 (by rfl) ⟨332747, by rfl⟩ : syracuseStep 443663 = 665495) B665495
theorem B443705 : Blo 291829 443705 := bstep (se 2 (by rfl) ⟨166389, by rfl⟩ : syracuseStep 443705 = 332779) B332779
theorem B836983 : Blo 291829 836983 := bstep (se 1 (by rfl) ⟨627737, by rfl⟩ : syracuseStep 836983 = 1255475) B1255475
theorem B2835971 : Blo 291829 2835971 := bstep (se 1 (by rfl) ⟨2126978, by rfl⟩ : syracuseStep 2835971 = 4253957) B4253957
theorem B739115 : Blo 291829 739115 := bstep (se 1 (by rfl) ⟨554336, by rfl⟩ : syracuseStep 739115 = 1108673) B1108673
theorem B444233 : Blo 291829 444233 := bstep (se 2 (by rfl) ⟨166587, by rfl⟩ : syracuseStep 444233 = 333175) B333175
theorem B1722391 : Blo 291829 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B2115821 : Blo 291829 2115821 := bstep (se 3 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 2115821 = 793433) B793433
theorem B2509379 : Blo 291829 2509379 := bstep (se 1 (by rfl) ⟨1882034, by rfl⟩ : syracuseStep 2509379 = 3764069) B3764069
theorem B3328613 : Blo 291829 3328613 := bstep (se 4 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 3328613 = 624115) B624115
theorem B739955 : Blo 291829 739955 := bstep (se 1 (by rfl) ⟨554966, by rfl⟩ : syracuseStep 739955 = 1109933) B1109933
theorem B838259 : Blo 291829 838259 := bstep (se 1 (by rfl) ⟨628694, by rfl⟩ : syracuseStep 838259 = 1257389) B1257389
theorem B674423 : Blo 291829 674423 := bstep (se 1 (by rfl) ⟨505817, by rfl⟩ : syracuseStep 674423 = 1011635) B1011635
theorem B739975 : Blo 291829 739975 := bstep (se 1 (by rfl) ⟨554981, by rfl⟩ : syracuseStep 739975 = 1109963) B1109963
theorem B1198793 : Blo 291829 1198793 := bstep (se 2 (by rfl) ⟨449547, by rfl⟩ : syracuseStep 1198793 = 899095) B899095
theorem B838487 : Blo 291829 838487 := bstep (se 1 (by rfl) ⟨628865, by rfl⟩ : syracuseStep 838487 = 1257731) B1257731
theorem B1133459 : Blo 291829 1133459 := bstep (se 1 (by rfl) ⟨850094, by rfl⟩ : syracuseStep 1133459 = 1700189) B1700189
theorem B740249 : Blo 291829 740249 := bstep (se 2 (by rfl) ⟨277593, by rfl⟩ : syracuseStep 740249 = 555187) B555187
theorem B1493963 : Blo 291829 1493963 := bstep (se 1 (by rfl) ⟨1120472, by rfl⟩ : syracuseStep 1493963 = 2240945) B2240945
theorem B740411 : Blo 291829 740411 := bstep (se 1 (by rfl) ⟨555308, by rfl⟩ : syracuseStep 740411 = 1110617) B1110617
theorem B740623 : Blo 291829 740623 := bstep (se 1 (by rfl) ⟨555467, by rfl⟩ : syracuseStep 740623 = 1110935) B1110935
theorem B904463 : Blo 291829 904463 := bstep (se 1 (by rfl) ⟨678347, by rfl⟩ : syracuseStep 904463 = 1356695) B1356695
theorem B1494287 : Blo 291829 1494287 := bstep (se 1 (by rfl) ⟨1120715, by rfl⟩ : syracuseStep 1494287 = 2241431) B2241431
theorem B1887623 : Blo 291829 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B2805137 : Blo 291829 2805137 := bstep (se 2 (by rfl) ⟨1051926, by rfl⟩ : syracuseStep 2805137 = 2103853) B2103853
theorem B1592855 : Blo 291829 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B740897 : Blo 291829 740897 := bstep (se 2 (by rfl) ⟨277836, by rfl⟩ : syracuseStep 740897 = 555673) B555673
theorem B708281 : Blo 291829 708281 := bstep (se 2 (by rfl) ⟨265605, by rfl⟩ : syracuseStep 708281 = 531211) B531211
theorem B3330071 : Blo 291829 3330071 := bstep (se 1 (by rfl) ⟨2497553, by rfl⟩ : syracuseStep 3330071 = 4995107) B4995107
theorem B708743 : Blo 291829 708743 := bstep (se 1 (by rfl) ⟨531557, by rfl⟩ : syracuseStep 708743 = 1063115) B1063115
theorem B840071 : Blo 291829 840071 := bstep (se 1 (by rfl) ⟨630053, by rfl⟩ : syracuseStep 840071 = 1260107) B1260107
theorem B741899 : Blo 291829 741899 := bstep (se 1 (by rfl) ⟨556424, by rfl⟩ : syracuseStep 741899 = 1112849) B1112849
theorem B938557 : Blo 291829 938557 := bstep (se 3 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 938557 = 351959) B351959
theorem B840253 : Blo 291829 840253 := bstep (se 3 (by rfl) ⟨157547, by rfl⟩ : syracuseStep 840253 = 315095) B315095
theorem B1495745 : Blo 291829 1495745 := bstep (se 2 (by rfl) ⟨560904, by rfl⟩ : syracuseStep 1495745 = 1121809) B1121809
theorem B2511769 : Blo 291829 2511769 := bstep (se 2 (by rfl) ⟨941913, by rfl⟩ : syracuseStep 2511769 = 1883827) B1883827
theorem B840719 : Blo 291829 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B5624963 : Blo 291829 5624963 := bstep (se 1 (by rfl) ⟨4218722, by rfl⟩ : syracuseStep 5624963 = 8437445) B8437445
theorem B742547 : Blo 291829 742547 := bstep (se 1 (by rfl) ⟨556910, by rfl⟩ : syracuseStep 742547 = 1113821) B1113821
theorem B710041 : Blo 291829 710041 := bstep (se 2 (by rfl) ⟨266265, by rfl⟩ : syracuseStep 710041 = 532531) B532531
theorem B742841 : Blo 291829 742841 := bstep (se 2 (by rfl) ⟨278565, by rfl⟩ : syracuseStep 742841 = 557131) B557131
theorem B710203 : Blo 291829 710203 := bstep (se 1 (by rfl) ⟨532652, by rfl⟩ : syracuseStep 710203 = 1065305) B1065305
theorem B3790795 : Blo 291829 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B1497041 : Blo 291829 1497041 := bstep (se 2 (by rfl) ⟨561390, by rfl⟩ : syracuseStep 1497041 = 1122781) B1122781
theorem B710657 : Blo 291829 710657 := bstep (se 2 (by rfl) ⟨266496, by rfl⟩ : syracuseStep 710657 = 532993) B532993
theorem B1792043 : Blo 291829 1792043 := bstep (se 1 (by rfl) ⟨1344032, by rfl⟩ : syracuseStep 1792043 = 2688065) B2688065
theorem B743539 : Blo 291829 743539 := bstep (se 1 (by rfl) ⟨557654, by rfl⟩ : syracuseStep 743539 = 1115309) B1115309
theorem B6379721 : Blo 291829 6379721 := bstep (se 2 (by rfl) ⟨2392395, by rfl⟩ : syracuseStep 6379721 = 4784791) B4784791
theorem B2840777 : Blo 291829 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B743681 : Blo 291829 743681 := bstep (se 2 (by rfl) ⟨278880, by rfl⟩ : syracuseStep 743681 = 557761) B557761
theorem B841985 : Blo 291829 841985 := bstep (se 2 (by rfl) ⟨315744, by rfl⟩ : syracuseStep 841985 = 631489) B631489
theorem B940403 : Blo 291829 940403 := bstep (se 1 (by rfl) ⟨705302, by rfl⟩ : syracuseStep 940403 = 1410605) B1410605
theorem B776633 : Blo 291829 776633 := bstep (se 2 (by rfl) ⟨291237, by rfl⟩ : syracuseStep 776633 = 582475) B582475
theorem B1432075 : Blo 291829 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B744137 : Blo 291829 744137 := bstep (se 2 (by rfl) ⟨279051, by rfl⟩ : syracuseStep 744137 = 558103) B558103
theorem B711467 : Blo 291829 711467 := bstep (se 1 (by rfl) ⟨533600, by rfl⟩ : syracuseStep 711467 = 1067201) B1067201
theorem B2513753 : Blo 291829 2513753 := bstep (se 2 (by rfl) ⟨942657, by rfl⟩ : syracuseStep 2513753 = 1885315) B1885315
theorem B1891187 : Blo 291829 1891187 := bstep (se 1 (by rfl) ⟨1418390, by rfl⟩ : syracuseStep 1891187 = 2836781) B2836781
theorem B416783 : Blo 291829 416783 := bstep (se 1 (by rfl) ⟨312587, by rfl⟩ : syracuseStep 416783 = 625175) B625175
theorem B744491 : Blo 291829 744491 := bstep (se 1 (by rfl) ⟨558368, by rfl⟩ : syracuseStep 744491 = 1116737) B1116737
theorem B2841733 : Blo 291829 2841733 := bstep (se 4 (by rfl) ⟨266412, by rfl⟩ : syracuseStep 2841733 = 532825) B532825
theorem B745483 : Blo 291829 745483 := bstep (se 1 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 745483 = 1118225) B1118225
theorem B1794059 : Blo 291829 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B647227 : Blo 291829 647227 := bstep (se 1 (by rfl) ⟨485420, by rfl⟩ : syracuseStep 647227 = 970841) B970841
theorem B745625 : Blo 291829 745625 := bstep (se 2 (by rfl) ⟨279609, by rfl⟩ : syracuseStep 745625 = 559219) B559219
theorem B1401025 : Blo 291829 1401025 := bstep (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) B1050769
theorem B1663213 : Blo 291829 1663213 := bstep (se 3 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 1663213 = 623705) B623705
theorem B745787 : Blo 291829 745787 := bstep (se 1 (by rfl) ⟨559340, by rfl⟩ : syracuseStep 745787 = 1118681) B1118681
theorem B1335869 : Blo 291829 1335869 := bstep (se 3 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 1335869 = 500951) B500951
theorem B2122307 : Blo 291829 2122307 := bstep (se 1 (by rfl) ⟨1591730, by rfl⟩ : syracuseStep 2122307 = 3183461) B3183461
theorem B746131 : Blo 291829 746131 := bstep (se 1 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 746131 = 1119197) B1119197
theorem B746273 : Blo 291829 746273 := bstep (se 2 (by rfl) ⟨279852, by rfl⟩ : syracuseStep 746273 = 559705) B559705
theorem B3629873 : Blo 291829 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B3171869 : Blo 291829 3171869 := bstep (se 3 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 3171869 = 1189451) B1189451
theorem B943645 : Blo 291829 943645 := bstep (se 3 (by rfl) ⟨176933, by rfl⟩ : syracuseStep 943645 = 353867) B353867
theorem B747265 : Blo 291829 747265 := bstep (se 2 (by rfl) ⟨280224, by rfl⟩ : syracuseStep 747265 = 560449) B560449
theorem B419899 : Blo 291829 419899 := bstep (se 1 (by rfl) ⟨314924, by rfl⟩ : syracuseStep 419899 = 629849) B629849
theorem B10152053 : Blo 291829 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B845959 : Blo 291829 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B1665197 : Blo 291829 1665197 := bstep (se 3 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 1665197 = 624449) B624449
theorem B747863 : Blo 291829 747863 := bstep (se 1 (by rfl) ⟨560897, by rfl⟩ : syracuseStep 747863 = 1121795) B1121795
theorem B846281 : Blo 291829 846281 := bstep (se 2 (by rfl) ⟨317355, by rfl⟩ : syracuseStep 846281 = 634711) B634711
theorem B3369437 : Blo 291829 3369437 := bstep (se 3 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 3369437 = 1263539) B1263539
theorem B748075 : Blo 291829 748075 := bstep (se 1 (by rfl) ⟨561056, by rfl⟩ : syracuseStep 748075 = 1122113) B1122113
theorem B748217 : Blo 291829 748217 := bstep (se 2 (by rfl) ⟨280581, by rfl⟩ : syracuseStep 748217 = 561163) B561163
theorem B420599 : Blo 291829 420599 := bstep (se 1 (by rfl) ⟨315449, by rfl⟩ : syracuseStep 420599 = 630899) B630899
theorem B4025123 : Blo 291829 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B2222963 : Blo 291829 2222963 := bstep (se 1 (by rfl) ⟨1667222, by rfl⟩ : syracuseStep 2222963 = 3334445) B3334445
theorem B5369753 : Blo 291829 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B2125997 : Blo 291829 2125997 := bstep (se 3 (by rfl) ⟨398624, by rfl⟩ : syracuseStep 2125997 = 797249) B797249
theorem B1110419 : Blo 291829 1110419 := bstep (se 1 (by rfl) ⟨832814, by rfl⟩ : syracuseStep 1110419 = 1665629) B1665629
theorem B2388371 : Blo 291829 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B946579 : Blo 291829 946579 := bstep (se 1 (by rfl) ⟨709934, by rfl⟩ : syracuseStep 946579 = 1419869) B1419869
theorem B7139825 : Blo 291829 7139825 := bstep (se 2 (by rfl) ⟨2677434, by rfl⟩ : syracuseStep 7139825 = 5354869) B5354869
theorem B1667587 : Blo 291829 1667587 := bstep (se 1 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 1667587 = 2501381) B2501381
theorem B3338819 : Blo 291829 3338819 := bstep (se 1 (by rfl) ⟨2504114, by rfl⟩ : syracuseStep 3338819 = 5008229) B5008229
theorem B5731033 : Blo 291829 5731033 := bstep (se 2 (by rfl) ⟨2149137, by rfl⟩ : syracuseStep 5731033 = 4298275) B4298275
theorem B12743513 : Blo 291829 12743513 := bstep (se 2 (by rfl) ⟨4778817, by rfl⟩ : syracuseStep 12743513 = 9557635) B9557635
theorem B291847 : Blo 291829 291847 := bstep (se 1 (by rfl) ⟨218885, by rfl⟩ : syracuseStep 291847 = 437771) B437771
theorem B291855 : Blo 291829 291855 := bstep (se 1 (by rfl) ⟨218891, by rfl⟩ : syracuseStep 291855 = 437783) B437783
theorem B291899 : Blo 291829 291899 := bstep (se 1 (by rfl) ⟨218924, by rfl⟩ : syracuseStep 291899 = 437849) B437849
theorem B291975 : Blo 291829 291975 := bstep (se 1 (by rfl) ⟨218981, by rfl⟩ : syracuseStep 291975 = 437963) B437963
theorem B291983 : Blo 291829 291983 := bstep (se 1 (by rfl) ⟨218987, by rfl⟩ : syracuseStep 291983 = 437975) B437975
theorem B554131 : Blo 291829 554131 := bstep (se 1 (by rfl) ⟨415598, by rfl⟩ : syracuseStep 554131 = 831197) B831197
theorem B292027 : Blo 291829 292027 := bstep (se 1 (by rfl) ⟨219020, by rfl⟩ : syracuseStep 292027 = 438041) B438041
theorem B292103 : Blo 291829 292103 := bstep (se 1 (by rfl) ⟨219077, by rfl⟩ : syracuseStep 292103 = 438155) B438155
theorem B292111 : Blo 291829 292111 := bstep (se 1 (by rfl) ⟨219083, by rfl⟩ : syracuseStep 292111 = 438167) B438167
theorem B292155 : Blo 291829 292155 := bstep (se 1 (by rfl) ⟨219116, by rfl⟩ : syracuseStep 292155 = 438233) B438233
theorem B554359 : Blo 291829 554359 := bstep (se 1 (by rfl) ⟨415769, by rfl⟩ : syracuseStep 554359 = 831539) B831539
theorem B292231 : Blo 291829 292231 := bstep (se 1 (by rfl) ⟨219173, by rfl⟩ : syracuseStep 292231 = 438347) B438347
theorem B292239 : Blo 291829 292239 := bstep (se 1 (by rfl) ⟨219179, by rfl⟩ : syracuseStep 292239 = 438359) B438359
theorem B292283 : Blo 291829 292283 := bstep (se 1 (by rfl) ⟨219212, by rfl⟩ : syracuseStep 292283 = 438425) B438425
theorem B292359 : Blo 291829 292359 := bstep (se 1 (by rfl) ⟨219269, by rfl⟩ : syracuseStep 292359 = 438539) B438539
theorem B292367 : Blo 291829 292367 := bstep (se 1 (by rfl) ⟨219275, by rfl⟩ : syracuseStep 292367 = 438551) B438551
theorem B292411 : Blo 291829 292411 := bstep (se 1 (by rfl) ⟨219308, by rfl⟩ : syracuseStep 292411 = 438617) B438617
theorem B292487 : Blo 291829 292487 := bstep (se 1 (by rfl) ⟨219365, by rfl⟩ : syracuseStep 292487 = 438731) B438731
theorem B292495 : Blo 291829 292495 := bstep (se 1 (by rfl) ⟨219371, by rfl⟩ : syracuseStep 292495 = 438743) B438743
theorem B292539 : Blo 291829 292539 := bstep (se 1 (by rfl) ⟨219404, by rfl⟩ : syracuseStep 292539 = 438809) B438809
theorem B292615 : Blo 291829 292615 := bstep (se 1 (by rfl) ⟨219461, by rfl⟩ : syracuseStep 292615 = 438923) B438923
theorem B292623 : Blo 291829 292623 := bstep (se 1 (by rfl) ⟨219467, by rfl⟩ : syracuseStep 292623 = 438935) B438935
theorem B292667 : Blo 291829 292667 := bstep (se 1 (by rfl) ⟨219500, by rfl⟩ : syracuseStep 292667 = 439001) B439001
theorem B292743 : Blo 291829 292743 := bstep (se 1 (by rfl) ⟨219557, by rfl⟩ : syracuseStep 292743 = 439115) B439115
theorem B292751 : Blo 291829 292751 := bstep (se 1 (by rfl) ⟨219563, by rfl⟩ : syracuseStep 292751 = 439127) B439127
theorem B292795 : Blo 291829 292795 := bstep (se 1 (by rfl) ⟨219596, by rfl⟩ : syracuseStep 292795 = 439193) B439193
theorem B292871 : Blo 291829 292871 := bstep (se 1 (by rfl) ⟨219653, by rfl⟩ : syracuseStep 292871 = 439307) B439307
theorem B1112075 : Blo 291829 1112075 := bstep (se 1 (by rfl) ⟨834056, by rfl⟩ : syracuseStep 1112075 = 1668113) B1668113
theorem B292879 : Blo 291829 292879 := bstep (se 1 (by rfl) ⟨219659, by rfl⟩ : syracuseStep 292879 = 439319) B439319
theorem B292923 : Blo 291829 292923 := bstep (se 1 (by rfl) ⟨219692, by rfl⟩ : syracuseStep 292923 = 439385) B439385
theorem B2422871 : Blo 291829 2422871 := bstep (se 1 (by rfl) ⟨1817153, by rfl⟩ : syracuseStep 2422871 = 3634307) B3634307
theorem B292999 : Blo 291829 292999 := bstep (se 1 (by rfl) ⟨219749, by rfl⟩ : syracuseStep 292999 = 439499) B439499
theorem B293007 : Blo 291829 293007 := bstep (se 1 (by rfl) ⟨219755, by rfl⟩ : syracuseStep 293007 = 439511) B439511
theorem B293051 : Blo 291829 293051 := bstep (se 1 (by rfl) ⟨219788, by rfl⟩ : syracuseStep 293051 = 439577) B439577
theorem B293127 : Blo 291829 293127 := bstep (se 1 (by rfl) ⟨219845, by rfl⟩ : syracuseStep 293127 = 439691) B439691
theorem B293135 : Blo 291829 293135 := bstep (se 1 (by rfl) ⟨219851, by rfl⟩ : syracuseStep 293135 = 439703) B439703
theorem B293179 : Blo 291829 293179 := bstep (se 1 (by rfl) ⟨219884, by rfl⟩ : syracuseStep 293179 = 439769) B439769
theorem B293255 : Blo 291829 293255 := bstep (se 1 (by rfl) ⟨219941, by rfl⟩ : syracuseStep 293255 = 439883) B439883
theorem B293263 : Blo 291829 293263 := bstep (se 1 (by rfl) ⟨219947, by rfl⟩ : syracuseStep 293263 = 439895) B439895
theorem B293307 : Blo 291829 293307 := bstep (se 1 (by rfl) ⟨219980, by rfl⟩ : syracuseStep 293307 = 439961) B439961
theorem B293383 : Blo 291829 293383 := bstep (se 1 (by rfl) ⟨220037, by rfl⟩ : syracuseStep 293383 = 440075) B440075
theorem B293391 : Blo 291829 293391 := bstep (se 1 (by rfl) ⟨220043, by rfl⟩ : syracuseStep 293391 = 440087) B440087
theorem B293435 : Blo 291829 293435 := bstep (se 1 (by rfl) ⟨220076, by rfl⟩ : syracuseStep 293435 = 440153) B440153
theorem B293511 : Blo 291829 293511 := bstep (se 1 (by rfl) ⟨220133, by rfl⟩ : syracuseStep 293511 = 440267) B440267
theorem B293519 : Blo 291829 293519 := bstep (se 1 (by rfl) ⟨220139, by rfl⟩ : syracuseStep 293519 = 440279) B440279
theorem B293563 : Blo 291829 293563 := bstep (se 1 (by rfl) ⟨220172, by rfl⟩ : syracuseStep 293563 = 440345) B440345
theorem B293639 : Blo 291829 293639 := bstep (se 1 (by rfl) ⟨220229, by rfl⟩ : syracuseStep 293639 = 440459) B440459
theorem B424711 : Blo 291829 424711 := bstep (se 1 (by rfl) ⟨318533, by rfl⟩ : syracuseStep 424711 = 637067) B637067
theorem B293647 : Blo 291829 293647 := bstep (se 1 (by rfl) ⟨220235, by rfl⟩ : syracuseStep 293647 = 440471) B440471
theorem B293691 : Blo 291829 293691 := bstep (se 1 (by rfl) ⟨220268, by rfl⟩ : syracuseStep 293691 = 440537) B440537
theorem B1670003 : Blo 291829 1670003 := bstep (se 1 (by rfl) ⟨1252502, by rfl⟩ : syracuseStep 1670003 = 2505005) B2505005
theorem B293767 : Blo 291829 293767 := bstep (se 1 (by rfl) ⟨220325, by rfl⟩ : syracuseStep 293767 = 440651) B440651
theorem B293775 : Blo 291829 293775 := bstep (se 1 (by rfl) ⟨220331, by rfl⟩ : syracuseStep 293775 = 440663) B440663
theorem B555923 : Blo 291829 555923 := bstep (se 1 (by rfl) ⟨416942, by rfl⟩ : syracuseStep 555923 = 833885) B833885
theorem B293819 : Blo 291829 293819 := bstep (se 1 (by rfl) ⟨220364, by rfl⟩ : syracuseStep 293819 = 440729) B440729
theorem B555977 : Blo 291829 555977 := bstep (se 2 (by rfl) ⟨208491, by rfl⟩ : syracuseStep 555977 = 416983) B416983
theorem B293895 : Blo 291829 293895 := bstep (se 1 (by rfl) ⟨220421, by rfl⟩ : syracuseStep 293895 = 440843) B440843
theorem B293903 : Blo 291829 293903 := bstep (se 1 (by rfl) ⟨220427, by rfl⟩ : syracuseStep 293903 = 440855) B440855
theorem B556075 : Blo 291829 556075 := bstep (se 1 (by rfl) ⟨417056, by rfl⟩ : syracuseStep 556075 = 834113) B834113
theorem B293947 : Blo 291829 293947 := bstep (se 1 (by rfl) ⟨220460, by rfl⟩ : syracuseStep 293947 = 440921) B440921
theorem B294023 : Blo 291829 294023 := bstep (se 1 (by rfl) ⟨220517, by rfl⟩ : syracuseStep 294023 = 441035) B441035
theorem B294031 : Blo 291829 294031 := bstep (se 1 (by rfl) ⟨220523, by rfl⟩ : syracuseStep 294031 = 441047) B441047
theorem B294075 : Blo 291829 294075 := bstep (se 1 (by rfl) ⟨220556, by rfl⟩ : syracuseStep 294075 = 441113) B441113
theorem B294151 : Blo 291829 294151 := bstep (se 1 (by rfl) ⟨220613, by rfl⟩ : syracuseStep 294151 = 441227) B441227
theorem B556303 : Blo 291829 556303 := bstep (se 1 (by rfl) ⟨417227, by rfl⟩ : syracuseStep 556303 = 834455) B834455
theorem B294159 : Blo 291829 294159 := bstep (se 1 (by rfl) ⟨220619, by rfl⟩ : syracuseStep 294159 = 441239) B441239
theorem B294203 : Blo 291829 294203 := bstep (se 1 (by rfl) ⟨220652, by rfl⟩ : syracuseStep 294203 = 441305) B441305
theorem B294279 : Blo 291829 294279 := bstep (se 1 (by rfl) ⟨220709, by rfl⟩ : syracuseStep 294279 = 441419) B441419
theorem B294287 : Blo 291829 294287 := bstep (se 1 (by rfl) ⟨220715, by rfl⟩ : syracuseStep 294287 = 441431) B441431
theorem B294331 : Blo 291829 294331 := bstep (se 1 (by rfl) ⟨220748, by rfl⟩ : syracuseStep 294331 = 441497) B441497
theorem B294407 : Blo 291829 294407 := bstep (se 1 (by rfl) ⟨220805, by rfl⟩ : syracuseStep 294407 = 441611) B441611
theorem B294415 : Blo 291829 294415 := bstep (se 1 (by rfl) ⟨220811, by rfl⟩ : syracuseStep 294415 = 441623) B441623
theorem B294459 : Blo 291829 294459 := bstep (se 1 (by rfl) ⟨220844, by rfl⟩ : syracuseStep 294459 = 441689) B441689
theorem B5144141 : Blo 291829 5144141 := bstep (se 3 (by rfl) ⟨964526, by rfl⟩ : syracuseStep 5144141 = 1929053) B1929053
theorem B294535 : Blo 291829 294535 := bstep (se 1 (by rfl) ⟨220901, by rfl⟩ : syracuseStep 294535 = 441803) B441803
theorem B294543 : Blo 291829 294543 := bstep (se 1 (by rfl) ⟨220907, by rfl⟩ : syracuseStep 294543 = 441815) B441815
theorem B294587 : Blo 291829 294587 := bstep (se 1 (by rfl) ⟨220940, by rfl⟩ : syracuseStep 294587 = 441881) B441881
theorem B3768065 : Blo 291829 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B294663 : Blo 291829 294663 := bstep (se 1 (by rfl) ⟨220997, by rfl⟩ : syracuseStep 294663 = 441995) B441995
theorem B294671 : Blo 291829 294671 := bstep (se 1 (by rfl) ⟨221003, by rfl⟩ : syracuseStep 294671 = 442007) B442007
theorem B2817827 : Blo 291829 2817827 := bstep (se 1 (by rfl) ⟨2113370, by rfl⟩ : syracuseStep 2817827 = 4226741) B4226741
theorem B425785 : Blo 291829 425785 := bstep (se 2 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 425785 = 319339) B319339
theorem B294715 : Blo 291829 294715 := bstep (se 1 (by rfl) ⟨221036, by rfl⟩ : syracuseStep 294715 = 442073) B442073
theorem B3374963 : Blo 291829 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B294791 : Blo 291829 294791 := bstep (se 1 (by rfl) ⟨221093, by rfl⟩ : syracuseStep 294791 = 442187) B442187
theorem B294799 : Blo 291829 294799 := bstep (se 1 (by rfl) ⟨221099, by rfl⟩ : syracuseStep 294799 = 442199) B442199
theorem B4751257 : Blo 291829 4751257 := bstep (se 2 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 4751257 = 3563443) B3563443
theorem B294843 : Blo 291829 294843 := bstep (se 1 (by rfl) ⟨221132, by rfl⟩ : syracuseStep 294843 = 442265) B442265
theorem B294951 : Blo 291829 294951 := bstep (se 1 (by rfl) ⟨221213, by rfl⟩ : syracuseStep 294951 = 442427) B442427
theorem B294991 : Blo 291829 294991 := bstep (se 1 (by rfl) ⟨221243, by rfl⟩ : syracuseStep 294991 = 442487) B442487
theorem B295007 : Blo 291829 295007 := bstep (se 1 (by rfl) ⟨221255, by rfl⟩ : syracuseStep 295007 = 442511) B442511
theorem B2523251 : Blo 291829 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B295035 : Blo 291829 295035 := bstep (se 1 (by rfl) ⟨221276, by rfl⟩ : syracuseStep 295035 = 442553) B442553
theorem B295087 : Blo 291829 295087 := bstep (se 1 (by rfl) ⟨221315, by rfl⟩ : syracuseStep 295087 = 442631) B442631
theorem B1114307 : Blo 291829 1114307 := bstep (se 1 (by rfl) ⟨835730, by rfl⟩ : syracuseStep 1114307 = 1671461) B1671461
theorem B295111 : Blo 291829 295111 := bstep (se 1 (by rfl) ⟨221333, by rfl⟩ : syracuseStep 295111 = 442667) B442667
theorem B295131 : Blo 291829 295131 := bstep (se 1 (by rfl) ⟨221348, by rfl⟩ : syracuseStep 295131 = 442697) B442697
theorem B1868033 : Blo 291829 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B295207 : Blo 291829 295207 := bstep (se 1 (by rfl) ⟨221405, by rfl⟩ : syracuseStep 295207 = 442811) B442811
theorem B295247 : Blo 291829 295247 := bstep (se 1 (by rfl) ⟨221435, by rfl⟩ : syracuseStep 295247 = 442871) B442871
theorem B295263 : Blo 291829 295263 := bstep (se 1 (by rfl) ⟨221447, by rfl⟩ : syracuseStep 295263 = 442895) B442895
theorem B295291 : Blo 291829 295291 := bstep (se 1 (by rfl) ⟨221468, by rfl⟩ : syracuseStep 295291 = 442937) B442937
theorem B754049 : Blo 291829 754049 := bstep (se 2 (by rfl) ⟨282768, by rfl⟩ : syracuseStep 754049 = 565537) B565537
theorem B295343 : Blo 291829 295343 := bstep (se 1 (by rfl) ⟨221507, by rfl⟩ : syracuseStep 295343 = 443015) B443015
theorem B295367 : Blo 291829 295367 := bstep (se 1 (by rfl) ⟨221525, by rfl⟩ : syracuseStep 295367 = 443051) B443051
theorem B295387 : Blo 291829 295387 := bstep (se 1 (by rfl) ⟨221540, by rfl⟩ : syracuseStep 295387 = 443081) B443081
theorem B295463 : Blo 291829 295463 := bstep (se 1 (by rfl) ⟨221597, by rfl⟩ : syracuseStep 295463 = 443195) B443195
theorem B2228795 : Blo 291829 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B295503 : Blo 291829 295503 := bstep (se 1 (by rfl) ⟨221627, by rfl⟩ : syracuseStep 295503 = 443255) B443255
theorem B295519 : Blo 291829 295519 := bstep (se 1 (by rfl) ⟨221639, by rfl⟩ : syracuseStep 295519 = 443279) B443279
theorem B328315 : Blo 291829 328315 := bstep (se 1 (by rfl) ⟨246236, by rfl⟩ : syracuseStep 328315 = 492473) B492473
theorem B295547 : Blo 291829 295547 := bstep (se 1 (by rfl) ⟨221660, by rfl⟩ : syracuseStep 295547 = 443321) B443321
theorem B295599 : Blo 291829 295599 := bstep (se 1 (by rfl) ⟨221699, by rfl⟩ : syracuseStep 295599 = 443399) B443399
theorem B1114823 : Blo 291829 1114823 := bstep (se 1 (by rfl) ⟨836117, by rfl⟩ : syracuseStep 1114823 = 1672235) B1672235
theorem B295623 : Blo 291829 295623 := bstep (se 1 (by rfl) ⟨221717, by rfl⟩ : syracuseStep 295623 = 443435) B443435
theorem B295643 : Blo 291829 295643 := bstep (se 1 (by rfl) ⟨221732, by rfl⟩ : syracuseStep 295643 = 443465) B443465
theorem B3769091 : Blo 291829 3769091 := bstep (se 1 (by rfl) ⟨2826818, by rfl⟩ : syracuseStep 3769091 = 5653637) B5653637
theorem B295719 : Blo 291829 295719 := bstep (se 1 (by rfl) ⟨221789, by rfl⟩ : syracuseStep 295719 = 443579) B443579
theorem B295759 : Blo 291829 295759 := bstep (se 1 (by rfl) ⟨221819, by rfl⟩ : syracuseStep 295759 = 443639) B443639
theorem B295775 : Blo 291829 295775 := bstep (se 1 (by rfl) ⟨221831, by rfl⟩ : syracuseStep 295775 = 443663) B443663
theorem B295803 : Blo 291829 295803 := bstep (se 1 (by rfl) ⟨221852, by rfl⟩ : syracuseStep 295803 = 443705) B443705
theorem B492601 : Blo 291829 492601 := bstep (se 2 (by rfl) ⟨184725, by rfl⟩ : syracuseStep 492601 = 369451) B369451
theorem B328783 : Blo 291829 328783 := bstep (se 1 (by rfl) ⟨246587, by rfl⟩ : syracuseStep 328783 = 493175) B493175
theorem B492743 : Blo 291829 492743 := bstep (se 1 (by rfl) ⟨369557, by rfl⟩ : syracuseStep 492743 = 739115) B739115
theorem B296155 : Blo 291829 296155 := bstep (se 1 (by rfl) ⟨222116, by rfl⟩ : syracuseStep 296155 = 444233) B444233
theorem B6391133 : Blo 291829 6391133 := bstep (se 3 (by rfl) ⟨1198337, by rfl⟩ : syracuseStep 6391133 = 2396675) B2396675
theorem B492905 : Blo 291829 492905 := bstep (se 2 (by rfl) ⟨184839, by rfl⟩ : syracuseStep 492905 = 369679) B369679
theorem B656783 : Blo 291829 656783 := bstep (se 1 (by rfl) ⟨492587, by rfl⟩ : syracuseStep 656783 = 985175) B985175
theorem B329179 : Blo 291829 329179 := bstep (se 1 (by rfl) ⟨246884, by rfl⟩ : syracuseStep 329179 = 493769) B493769
theorem B1410547 : Blo 291829 1410547 := bstep (se 1 (by rfl) ⟨1057910, by rfl⟩ : syracuseStep 1410547 = 2115821) B2115821
theorem B1115795 : Blo 291829 1115795 := bstep (se 1 (by rfl) ⟨836846, by rfl⟩ : syracuseStep 1115795 = 1673693) B1673693
theorem B657107 : Blo 291829 657107 := bstep (se 1 (by rfl) ⟨492830, by rfl⟩ : syracuseStep 657107 = 985661) B985661
theorem B1672919 : Blo 291829 1672919 := bstep (se 1 (by rfl) ⟨1254689, by rfl⟩ : syracuseStep 1672919 = 2509379) B2509379
theorem B493303 : Blo 291829 493303 := bstep (se 1 (by rfl) ⟨369977, by rfl⟩ : syracuseStep 493303 = 739955) B739955
theorem B558839 : Blo 291829 558839 := bstep (se 1 (by rfl) ⟨419129, by rfl⟩ : syracuseStep 558839 = 838259) B838259
theorem B624457 : Blo 291829 624457 := bstep (se 2 (by rfl) ⟨234171, by rfl⟩ : syracuseStep 624457 = 468343) B468343
theorem B1115977 : Blo 291829 1115977 := bstep (se 2 (by rfl) ⟨418491, by rfl⟩ : syracuseStep 1115977 = 836983) B836983
theorem B558991 : Blo 291829 558991 := bstep (se 1 (by rfl) ⟨419243, by rfl⟩ : syracuseStep 558991 = 838487) B838487
theorem B329647 : Blo 291829 329647 := bstep (se 1 (by rfl) ⟨247235, by rfl⟩ : syracuseStep 329647 = 494471) B494471
theorem B755639 : Blo 291829 755639 := bstep (se 1 (by rfl) ⟨566729, by rfl⟩ : syracuseStep 755639 = 1133459) B1133459
theorem B493499 : Blo 291829 493499 := bstep (se 1 (by rfl) ⟨370124, by rfl⟩ : syracuseStep 493499 = 740249) B740249
theorem B7571393 : Blo 291829 7571393 := bstep (se 2 (by rfl) ⟨2839272, by rfl⟩ : syracuseStep 7571393 = 5678545) B5678545
theorem B493607 : Blo 291829 493607 := bstep (se 1 (by rfl) ⟨370205, by rfl⟩ : syracuseStep 493607 = 740411) B740411
theorem B1870091 : Blo 291829 1870091 := bstep (se 1 (by rfl) ⟨1402568, by rfl⟩ : syracuseStep 1870091 = 2805137) B2805137
theorem B493897 : Blo 291829 493897 := bstep (se 2 (by rfl) ⟨185211, by rfl⟩ : syracuseStep 493897 = 370423) B370423
theorem B330079 : Blo 291829 330079 := bstep (se 1 (by rfl) ⟨247559, by rfl⟩ : syracuseStep 330079 = 495119) B495119
theorem B493931 : Blo 291829 493931 := bstep (se 1 (by rfl) ⟨370448, by rfl⟩ : syracuseStep 493931 = 740897) B740897
theorem B756097 : Blo 291829 756097 := bstep (se 2 (by rfl) ⟨283536, by rfl⟩ : syracuseStep 756097 = 567073) B567073
theorem B395695 : Blo 291829 395695 := bstep (se 1 (by rfl) ⟨296771, by rfl⟩ : syracuseStep 395695 = 593543) B593543
theorem B658043 : Blo 291829 658043 := bstep (se 1 (by rfl) ⟨493532, by rfl⟩ : syracuseStep 658043 = 987065) B987065
theorem B330439 : Blo 291829 330439 := bstep (se 1 (by rfl) ⟨247829, by rfl⟩ : syracuseStep 330439 = 495659) B495659
theorem B658169 : Blo 291829 658169 := bstep (se 2 (by rfl) ⟨246813, by rfl⟩ : syracuseStep 658169 = 493627) B493627
theorem B494329 : Blo 291829 494329 := bstep (se 2 (by rfl) ⟨185373, by rfl⟩ : syracuseStep 494329 = 370747) B370747
theorem B559865 : Blo 291829 559865 := bstep (se 2 (by rfl) ⟨209949, by rfl⟩ : syracuseStep 559865 = 419899) B419899
theorem B560047 : Blo 291829 560047 := bstep (se 1 (by rfl) ⟨420035, by rfl⟩ : syracuseStep 560047 = 840071) B840071
theorem B986039 : Blo 291829 986039 := bstep (se 1 (by rfl) ⟨739529, by rfl⟩ : syracuseStep 986039 = 1479059) B1479059
theorem B658439 : Blo 291829 658439 := bstep (se 1 (by rfl) ⟨493829, by rfl⟩ : syracuseStep 658439 = 987659) B987659
theorem B494599 : Blo 291829 494599 := bstep (se 1 (by rfl) ⟨370949, by rfl⟩ : syracuseStep 494599 = 741899) B741899
theorem B658511 : Blo 291829 658511 := bstep (se 1 (by rfl) ⟨493883, by rfl⟩ : syracuseStep 658511 = 987767) B987767
theorem B495031 : Blo 291829 495031 := bstep (se 1 (by rfl) ⟨371273, by rfl⟩ : syracuseStep 495031 = 742547) B742547
theorem B658907 : Blo 291829 658907 := bstep (se 1 (by rfl) ⟨494180, by rfl⟩ : syracuseStep 658907 = 988361) B988361
theorem B986633 : Blo 291829 986633 := bstep (se 2 (by rfl) ⟨369987, by rfl⟩ : syracuseStep 986633 = 739975) B739975
theorem B331303 : Blo 291829 331303 := bstep (se 1 (by rfl) ⟨248477, by rfl⟩ : syracuseStep 331303 = 496955) B496955
theorem B495227 : Blo 291829 495227 := bstep (se 1 (by rfl) ⟨371420, by rfl⟩ : syracuseStep 495227 = 742841) B742841
theorem B3346109 : Blo 291829 3346109 := bstep (se 3 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 3346109 = 1254791) B1254791
theorem B1117907 : Blo 291829 1117907 := bstep (se 1 (by rfl) ⟨838430, by rfl⟩ : syracuseStep 1117907 = 1676861) B1676861
theorem B1248983 : Blo 291829 1248983 := bstep (se 1 (by rfl) ⟨936737, by rfl⟩ : syracuseStep 1248983 = 1873475) B1873475
theorem B1183663 : Blo 291829 1183663 := bstep (se 1 (by rfl) ⟨887747, by rfl⟩ : syracuseStep 1183663 = 1775495) B1775495
theorem B659375 : Blo 291829 659375 := bstep (se 1 (by rfl) ⟨494531, by rfl⟩ : syracuseStep 659375 = 989063) B989063
theorem B593851 : Blo 291829 593851 := bstep (se 1 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 593851 = 890777) B890777
theorem B495625 : Blo 291829 495625 := bstep (se 2 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 495625 = 371719) B371719
theorem B659627 : Blo 291829 659627 := bstep (se 1 (by rfl) ⟨494720, by rfl⟩ : syracuseStep 659627 = 989441) B989441
theorem B495787 : Blo 291829 495787 := bstep (se 1 (by rfl) ⟨371840, by rfl⟩ : syracuseStep 495787 = 743681) B743681
theorem B561323 : Blo 291829 561323 := bstep (se 1 (by rfl) ⟨420992, by rfl⟩ : syracuseStep 561323 = 841985) B841985
theorem B2822323 : Blo 291829 2822323 := bstep (se 1 (by rfl) ⟨2116742, by rfl⟩ : syracuseStep 2822323 = 4233485) B4233485
theorem B626935 : Blo 291829 626935 := bstep (se 1 (by rfl) ⟨470201, by rfl⟩ : syracuseStep 626935 = 940403) B940403
theorem B1249597 : Blo 291829 1249597 := bstep (se 3 (by rfl) ⟨234299, by rfl⟩ : syracuseStep 1249597 = 468599) B468599
theorem B987497 : Blo 291829 987497 := bstep (se 2 (by rfl) ⟨370311, by rfl⟩ : syracuseStep 987497 = 740623) B740623
theorem B496091 : Blo 291829 496091 := bstep (se 1 (by rfl) ⟨372068, by rfl⟩ : syracuseStep 496091 = 744137) B744137
theorem B1675835 : Blo 291829 1675835 := bstep (se 1 (by rfl) ⟨1256876, by rfl⟩ : syracuseStep 1675835 = 2513753) B2513753
theorem B660167 : Blo 291829 660167 := bstep (se 1 (by rfl) ⟨495125, by rfl⟩ : syracuseStep 660167 = 990251) B990251
theorem B496327 : Blo 291829 496327 := bstep (se 1 (by rfl) ⟨372245, by rfl⟩ : syracuseStep 496327 = 744491) B744491
theorem B496489 : Blo 291829 496489 := bstep (se 2 (by rfl) ⟨186183, by rfl⟩ : syracuseStep 496489 = 372367) B372367
theorem B988091 : Blo 291829 988091 := bstep (se 1 (by rfl) ⟨741068, by rfl⟩ : syracuseStep 988091 = 1482137) B1482137
theorem B3413195 : Blo 291829 3413195 := bstep (se 1 (by rfl) ⟨2559896, by rfl⟩ : syracuseStep 3413195 = 5119793) B5119793
theorem B595343 : Blo 291829 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B497083 : Blo 291829 497083 := bstep (se 1 (by rfl) ⟨372812, by rfl⟩ : syracuseStep 497083 = 745625) B745625
theorem B661031 : Blo 291829 661031 := bstep (se 1 (by rfl) ⟨495773, by rfl⟩ : syracuseStep 661031 = 991547) B991547
theorem B497191 : Blo 291829 497191 := bstep (se 1 (by rfl) ⟨372893, by rfl⟩ : syracuseStep 497191 = 745787) B745787
theorem B890579 : Blo 291829 890579 := bstep (se 1 (by rfl) ⟨667934, by rfl⟩ : syracuseStep 890579 = 1335869) B1335869
theorem B792275 : Blo 291829 792275 := bstep (se 1 (by rfl) ⟨594206, by rfl⟩ : syracuseStep 792275 = 1188413) B1188413
theorem B595667 : Blo 291829 595667 := bstep (se 1 (by rfl) ⟨446750, by rfl⟩ : syracuseStep 595667 = 893501) B893501
theorem B1414871 : Blo 291829 1414871 := bstep (se 1 (by rfl) ⟨1061153, by rfl⟩ : syracuseStep 1414871 = 2122307) B2122307
theorem B661355 : Blo 291829 661355 := bstep (se 1 (by rfl) ⟨496016, by rfl⟩ : syracuseStep 661355 = 992033) B992033
theorem B497515 : Blo 291829 497515 := bstep (se 1 (by rfl) ⟨373136, by rfl⟩ : syracuseStep 497515 = 746273) B746273
theorem B661409 : Blo 291829 661409 := bstep (se 2 (by rfl) ⟨248028, by rfl⟩ : syracuseStep 661409 = 496057) B496057
theorem B1251409 : Blo 291829 1251409 := bstep (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) B938557
theorem B1120337 : Blo 291829 1120337 := bstep (se 2 (by rfl) ⟨420126, by rfl⟩ : syracuseStep 1120337 = 840253) B840253
theorem B1251443 : Blo 291829 1251443 := bstep (se 1 (by rfl) ⟨938582, by rfl⟩ : syracuseStep 1251443 = 1877165) B1877165
theorem B661751 : Blo 291829 661751 := bstep (se 1 (by rfl) ⟨496313, by rfl⟩ : syracuseStep 661751 = 992627) B992627
theorem B7641377 : Blo 291829 7641377 := bstep (se 2 (by rfl) ⟨2865516, by rfl⟩ : syracuseStep 7641377 = 5731033) B5731033
theorem B1415485 : Blo 291829 1415485 := bstep (se 3 (by rfl) ⟨265403, by rfl⟩ : syracuseStep 1415485 = 530807) B530807
theorem B1120655 : Blo 291829 1120655 := bstep (se 1 (by rfl) ⟨840491, by rfl⟩ : syracuseStep 1120655 = 1680983) B1680983
theorem B2071021 : Blo 291829 2071021 := bstep (se 3 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 2071021 = 776633) B776633
theorem B3349025 : Blo 291829 3349025 := bstep (se 2 (by rfl) ⟨1255884, by rfl⟩ : syracuseStep 3349025 = 2511769) B2511769
theorem B989819 : Blo 291829 989819 := bstep (se 1 (by rfl) ⟨742364, by rfl⟩ : syracuseStep 989819 = 1484729) B1484729
theorem B989981 : Blo 291829 989981 := bstep (se 3 (by rfl) ⟨185621, by rfl⟩ : syracuseStep 989981 = 371243) B371243
theorem B662345 : Blo 291829 662345 := bstep (se 2 (by rfl) ⟨248379, by rfl⟩ : syracuseStep 662345 = 496759) B496759
theorem B1776491 : Blo 291829 1776491 := bstep (se 1 (by rfl) ⟨1332368, by rfl⟩ : syracuseStep 1776491 = 2664737) B2664737
theorem B498575 : Blo 291829 498575 := bstep (se 1 (by rfl) ⟨373931, by rfl⟩ : syracuseStep 498575 = 747863) B747863
theorem B859067 : Blo 291829 859067 := bstep (se 1 (by rfl) ⟨644300, by rfl⟩ : syracuseStep 859067 = 1288601) B1288601
theorem B564187 : Blo 291829 564187 := bstep (se 1 (by rfl) ⟨423140, by rfl⟩ : syracuseStep 564187 = 846281) B846281
theorem B498811 : Blo 291829 498811 := bstep (se 1 (by rfl) ⟨374108, by rfl⟩ : syracuseStep 498811 = 748217) B748217
theorem B1481975 : Blo 291829 1481975 := bstep (se 1 (by rfl) ⟨1111481, by rfl⟩ : syracuseStep 1481975 = 2222963) B2222963
theorem B1121597 : Blo 291829 1121597 := bstep (se 3 (by rfl) ⟨210299, by rfl⟩ : syracuseStep 1121597 = 420599) B420599
theorem B990683 : Blo 291829 990683 := bstep (se 1 (by rfl) ⟨743012, by rfl⟩ : syracuseStep 990683 = 1486025) B1486025
theorem B663137 : Blo 291829 663137 := bstep (se 2 (by rfl) ⟨248676, by rfl⟩ : syracuseStep 663137 = 497353) B497353
theorem B532091 : Blo 291829 532091 := bstep (se 1 (by rfl) ⟨399068, by rfl⟩ : syracuseStep 532091 = 798137) B798137
theorem B1482461 : Blo 291829 1482461 := bstep (se 3 (by rfl) ⟨277961, by rfl⟩ : syracuseStep 1482461 = 555923) B555923
theorem B1679069 : Blo 291829 1679069 := bstep (se 3 (by rfl) ⟨314825, by rfl⟩ : syracuseStep 1679069 = 629651) B629651
theorem B663479 : Blo 291829 663479 := bstep (se 1 (by rfl) ⟨497609, by rfl⟩ : syracuseStep 663479 = 995219) B995219
theorem B5054393 : Blo 291829 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B3579835 : Blo 291829 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B2105297 : Blo 291829 2105297 := bstep (se 2 (by rfl) ⟨789486, by rfl⟩ : syracuseStep 2105297 = 1578973) B1578973
theorem B1417331 : Blo 291829 1417331 := bstep (se 1 (by rfl) ⟨1062998, by rfl⟩ : syracuseStep 1417331 = 2125997) B2125997
theorem B991385 : Blo 291829 991385 := bstep (se 2 (by rfl) ⟨371769, by rfl⟩ : syracuseStep 991385 = 743539) B743539
theorem B4759883 : Blo 291829 4759883 := bstep (se 1 (by rfl) ⟨3569912, by rfl⟩ : syracuseStep 4759883 = 7139825) B7139825
theorem B664073 : Blo 291829 664073 := bstep (se 2 (by rfl) ⟨249027, by rfl⟩ : syracuseStep 664073 = 498055) B498055
theorem B8495675 : Blo 291829 8495675 := bstep (se 1 (by rfl) ⟨6371756, by rfl⟩ : syracuseStep 8495675 = 12743513) B12743513
theorem B1909433 : Blo 291829 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B500473 : Blo 291829 500473 := bstep (se 2 (by rfl) ⟨187677, by rfl⟩ : syracuseStep 500473 = 375355) B375355
theorem B664415 : Blo 291829 664415 := bstep (se 1 (by rfl) ⟨498311, by rfl⟩ : syracuseStep 664415 = 996623) B996623
theorem B566281 : Blo 291829 566281 := bstep (se 2 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 566281 = 424711) B424711
theorem B664595 : Blo 291829 664595 := bstep (se 1 (by rfl) ⟨498446, by rfl⟩ : syracuseStep 664595 = 996893) B996893
theorem B1058039 : Blo 291829 1058039 := bstep (se 1 (by rfl) ⟨793529, by rfl⟩ : syracuseStep 1058039 = 1587059) B1587059
theorem B992573 : Blo 291829 992573 := bstep (se 3 (by rfl) ⟨186107, by rfl⟩ : syracuseStep 992573 = 372215) B372215
theorem B664937 : Blo 291829 664937 := bstep (se 2 (by rfl) ⟨249351, by rfl⟩ : syracuseStep 664937 = 498703) B498703
theorem B1615247 : Blo 291829 1615247 := bstep (se 1 (by rfl) ⟨1211435, by rfl⟩ : syracuseStep 1615247 = 2422871) B2422871
theorem B665531 : Blo 291829 665531 := bstep (se 1 (by rfl) ⟨499148, by rfl⟩ : syracuseStep 665531 = 998297) B998297
theorem B370651 : Blo 291829 370651 := bstep (se 1 (by rfl) ⟨277988, by rfl⟩ : syracuseStep 370651 = 555977) B555977
theorem B993437 : Blo 291829 993437 := bstep (se 3 (by rfl) ⟨186269, by rfl⟩ : syracuseStep 993437 = 372539) B372539
theorem B469163 : Blo 291829 469163 := bstep (se 1 (by rfl) ⟨351872, by rfl⟩ : syracuseStep 469163 = 703745) B703745
theorem B567713 : Blo 291829 567713 := bstep (se 2 (by rfl) ⟨212892, by rfl⟩ : syracuseStep 567713 = 425785) B425785
theorem B1878551 : Blo 291829 1878551 := bstep (se 1 (by rfl) ⟨1408913, by rfl⟩ : syracuseStep 1878551 = 2817827) B2817827
theorem B2239001 : Blo 291829 2239001 := bstep (se 2 (by rfl) ⟨839625, by rfl⟩ : syracuseStep 2239001 = 1679251) B1679251
theorem B6335009 : Blo 291829 6335009 := bstep (se 2 (by rfl) ⟨2375628, by rfl⟩ : syracuseStep 6335009 = 4751257) B4751257
theorem B1059425 : Blo 291829 1059425 := bstep (se 2 (by rfl) ⟨397284, by rfl⟩ : syracuseStep 1059425 = 794569) B794569
theorem B993977 : Blo 291829 993977 := bstep (se 2 (by rfl) ⟨372741, by rfl⟩ : syracuseStep 993977 = 745483) B745483
theorem B764615 : Blo 291829 764615 := bstep (se 1 (by rfl) ⟨573461, by rfl⟩ : syracuseStep 764615 = 1146923) B1146923
theorem B862969 : Blo 291829 862969 := bstep (se 2 (by rfl) ⟨323613, by rfl⟩ : syracuseStep 862969 = 647227) B647227
theorem B9186085 : Blo 291829 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B1583945 : Blo 291829 1583945 := bstep (se 2 (by rfl) ⟨593979, by rfl⟩ : syracuseStep 1583945 = 1187959) B1187959
theorem B994571 : Blo 291829 994571 := bstep (se 1 (by rfl) ⟨745928, by rfl⟩ : syracuseStep 994571 = 1491857) B1491857
theorem B994841 : Blo 291829 994841 := bstep (se 2 (by rfl) ⟨373065, by rfl⟩ : syracuseStep 994841 = 746131) B746131
theorem B6368989 : Blo 291829 6368989 := bstep (se 3 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 6368989 = 2388371) B2388371
theorem B896761 : Blo 291829 896761 := bstep (se 2 (by rfl) ⟨336285, by rfl⟩ : syracuseStep 896761 = 672571) B672571
theorem B438191 : Blo 291829 438191 := bstep (se 1 (by rfl) ⟨328643, by rfl⟩ : syracuseStep 438191 = 657287) B657287
theorem B438281 : Blo 291829 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B438311 : Blo 291829 438311 := bstep (se 1 (by rfl) ⟨328733, by rfl⟩ : syracuseStep 438311 = 657467) B657467
theorem B438395 : Blo 291829 438395 := bstep (se 1 (by rfl) ⟨328796, by rfl⟩ : syracuseStep 438395 = 657593) B657593
theorem B438521 : Blo 291829 438521 := bstep (se 2 (by rfl) ⟨164445, by rfl⟩ : syracuseStep 438521 = 328891) B328891
theorem B438623 : Blo 291829 438623 := bstep (se 1 (by rfl) ⟨328967, by rfl⟩ : syracuseStep 438623 = 657935) B657935
theorem B438635 : Blo 291829 438635 := bstep (se 1 (by rfl) ⟨328976, by rfl⟩ : syracuseStep 438635 = 657953) B657953
theorem B799195 : Blo 291829 799195 := bstep (se 1 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 799195 = 1198793) B1198793
theorem B438863 : Blo 291829 438863 := bstep (se 1 (by rfl) ⟨329147, by rfl⟩ : syracuseStep 438863 = 658295) B658295
theorem B995975 : Blo 291829 995975 := bstep (se 1 (by rfl) ⟨746981, by rfl⟩ : syracuseStep 995975 = 1493963) B1493963
theorem B996029 : Blo 291829 996029 := bstep (se 3 (by rfl) ⟨186755, by rfl⟩ : syracuseStep 996029 = 373511) B373511
theorem B438983 : Blo 291829 438983 := bstep (se 1 (by rfl) ⟨329237, by rfl⟩ : syracuseStep 438983 = 658475) B658475
theorem B1258193 : Blo 291829 1258193 := bstep (se 2 (by rfl) ⟨471822, by rfl⟩ : syracuseStep 1258193 = 943645) B943645
theorem B1487645 : Blo 291829 1487645 := bstep (se 3 (by rfl) ⟨278933, by rfl⟩ : syracuseStep 1487645 = 557867) B557867
theorem B1618717 : Blo 291829 1618717 := bstep (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) B607019
theorem B9679661 : Blo 291829 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B602975 : Blo 291829 602975 := bstep (se 1 (by rfl) ⟨452231, by rfl⟩ : syracuseStep 602975 = 904463) B904463
theorem B996191 : Blo 291829 996191 := bstep (se 1 (by rfl) ⟨747143, by rfl⟩ : syracuseStep 996191 = 1494287) B1494287
theorem B439145 : Blo 291829 439145 := bstep (se 2 (by rfl) ⟨164679, by rfl⟩ : syracuseStep 439145 = 329359) B329359
theorem B1258415 : Blo 291829 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B439223 : Blo 291829 439223 := bstep (se 1 (by rfl) ⟨329417, by rfl⟩ : syracuseStep 439223 = 658835) B658835
theorem B439259 : Blo 291829 439259 := bstep (se 1 (by rfl) ⟨329444, by rfl⟩ : syracuseStep 439259 = 658889) B658889
theorem B996353 : Blo 291829 996353 := bstep (se 2 (by rfl) ⟨373632, by rfl⟩ : syracuseStep 996353 = 747265) B747265
theorem B504839 : Blo 291829 504839 := bstep (se 1 (by rfl) ⟨378629, by rfl⟩ : syracuseStep 504839 = 757259) B757259
theorem B1061903 : Blo 291829 1061903 := bstep (se 1 (by rfl) ⟨796427, by rfl⟩ : syracuseStep 1061903 = 1592855) B1592855
theorem B472187 : Blo 291829 472187 := bstep (se 1 (by rfl) ⟨354140, by rfl⟩ : syracuseStep 472187 = 708281) B708281
theorem B2241917 : Blo 291829 2241917 := bstep (se 3 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 2241917 = 840719) B840719
theorem B439727 : Blo 291829 439727 := bstep (se 1 (by rfl) ⟨329795, by rfl⟩ : syracuseStep 439727 = 659591) B659591
theorem B472495 : Blo 291829 472495 := bstep (se 1 (by rfl) ⟨354371, by rfl⟩ : syracuseStep 472495 = 708743) B708743
theorem B701939 : Blo 291829 701939 := bstep (se 1 (by rfl) ⟨526454, by rfl⟩ : syracuseStep 701939 = 1052909) B1052909
theorem B1127945 : Blo 291829 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B439817 : Blo 291829 439817 := bstep (se 2 (by rfl) ⟨164931, by rfl⟩ : syracuseStep 439817 = 329863) B329863
theorem B439847 : Blo 291829 439847 := bstep (se 1 (by rfl) ⟨329885, by rfl⟩ : syracuseStep 439847 = 659771) B659771
theorem B374311 : Blo 291829 374311 := bstep (se 1 (by rfl) ⟨280733, by rfl⟩ : syracuseStep 374311 = 561467) B561467
theorem B2012759 : Blo 291829 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B1947223 : Blo 291829 1947223 := bstep (se 1 (by rfl) ⟨1460417, by rfl⟩ : syracuseStep 1947223 = 2920835) B2920835
theorem B439931 : Blo 291829 439931 := bstep (se 1 (by rfl) ⟨329948, by rfl⟩ : syracuseStep 439931 = 659897) B659897
theorem B440057 : Blo 291829 440057 := bstep (se 2 (by rfl) ⟨165021, by rfl⟩ : syracuseStep 440057 = 330043) B330043
theorem B997163 : Blo 291829 997163 := bstep (se 1 (by rfl) ⟨747872, by rfl⟩ : syracuseStep 997163 = 1495745) B1495745
theorem B440159 : Blo 291829 440159 := bstep (se 1 (by rfl) ⟨330119, by rfl⟩ : syracuseStep 440159 = 660239) B660239
theorem B440171 : Blo 291829 440171 := bstep (se 1 (by rfl) ⟨330128, by rfl⟩ : syracuseStep 440171 = 660257) B660257
theorem B997433 : Blo 291829 997433 := bstep (se 2 (by rfl) ⟨374037, by rfl⟩ : syracuseStep 997433 = 748075) B748075
theorem B440399 : Blo 291829 440399 := bstep (se 1 (by rfl) ⟨330299, by rfl⟩ : syracuseStep 440399 = 660599) B660599
theorem B3749975 : Blo 291829 3749975 := bstep (se 1 (by rfl) ⟨2812481, by rfl⟩ : syracuseStep 3749975 = 5624963) B5624963
theorem B440519 : Blo 291829 440519 := bstep (se 1 (by rfl) ⟨330389, by rfl⟩ : syracuseStep 440519 = 660779) B660779
theorem B36616493 : Blo 291829 36616493 := bstep (se 3 (by rfl) ⟨6865592, by rfl⟩ : syracuseStep 36616493 = 13731185) B13731185
theorem B440681 : Blo 291829 440681 := bstep (se 2 (by rfl) ⟨165255, by rfl⟩ : syracuseStep 440681 = 330511) B330511
theorem B997757 : Blo 291829 997757 := bstep (se 3 (by rfl) ⟨187079, by rfl⟩ : syracuseStep 997757 = 374159) B374159
theorem B440759 : Blo 291829 440759 := bstep (se 1 (by rfl) ⟨330569, by rfl⟩ : syracuseStep 440759 = 661139) B661139
theorem B440795 : Blo 291829 440795 := bstep (se 1 (by rfl) ⟨330596, by rfl⟩ : syracuseStep 440795 = 661193) B661193
theorem B998027 : Blo 291829 998027 := bstep (se 1 (by rfl) ⟨748520, by rfl⟩ : syracuseStep 998027 = 1497041) B1497041
theorem B473771 : Blo 291829 473771 := bstep (se 1 (by rfl) ⟨355328, by rfl⟩ : syracuseStep 473771 = 710657) B710657
theorem B7518905 : Blo 291829 7518905 := bstep (se 2 (by rfl) ⟨2819589, by rfl⟩ : syracuseStep 7518905 = 5639179) B5639179
theorem B1194695 : Blo 291829 1194695 := bstep (se 1 (by rfl) ⟨896021, by rfl⟩ : syracuseStep 1194695 = 1792043) B1792043
theorem B441263 : Blo 291829 441263 := bstep (se 1 (by rfl) ⟨330947, by rfl⟩ : syracuseStep 441263 = 661895) B661895
theorem B441353 : Blo 291829 441353 := bstep (se 2 (by rfl) ⟨165507, by rfl⟩ : syracuseStep 441353 = 331015) B331015
theorem B441383 : Blo 291829 441383 := bstep (se 1 (by rfl) ⟨331037, by rfl⟩ : syracuseStep 441383 = 662075) B662075
theorem B441467 : Blo 291829 441467 := bstep (se 1 (by rfl) ⟨331100, by rfl⟩ : syracuseStep 441467 = 662201) B662201
theorem B1260791 : Blo 291829 1260791 := bstep (se 1 (by rfl) ⟨945593, by rfl⟩ : syracuseStep 1260791 = 1891187) B1891187
theorem B441593 : Blo 291829 441593 := bstep (se 2 (by rfl) ⟨165597, by rfl⟩ : syracuseStep 441593 = 331195) B331195
theorem B441695 : Blo 291829 441695 := bstep (se 1 (by rfl) ⟨331271, by rfl⟩ : syracuseStep 441695 = 662543) B662543
theorem B441707 : Blo 291829 441707 := bstep (se 1 (by rfl) ⟨331280, by rfl⟩ : syracuseStep 441707 = 662561) B662561
theorem B441935 : Blo 291829 441935 := bstep (se 1 (by rfl) ⟨331451, by rfl⟩ : syracuseStep 441935 = 662903) B662903
theorem B442055 : Blo 291829 442055 := bstep (se 1 (by rfl) ⟨331541, by rfl⟩ : syracuseStep 442055 = 663083) B663083
theorem B704351 : Blo 291829 704351 := bstep (se 1 (by rfl) ⟨528263, by rfl⟩ : syracuseStep 704351 = 1056527) B1056527
theorem B442217 : Blo 291829 442217 := bstep (se 2 (by rfl) ⟨165831, by rfl⟩ : syracuseStep 442217 = 331663) B331663
theorem B442295 : Blo 291829 442295 := bstep (se 1 (by rfl) ⟨331721, by rfl⟩ : syracuseStep 442295 = 663443) B663443
theorem B442331 : Blo 291829 442331 := bstep (se 1 (by rfl) ⟨331748, by rfl⟩ : syracuseStep 442331 = 663497) B663497
theorem B1196039 : Blo 291829 1196039 := bstep (se 1 (by rfl) ⟨897029, by rfl⟩ : syracuseStep 1196039 = 1794059) B1794059
theorem B704591 : Blo 291829 704591 := bstep (se 1 (by rfl) ⟨528443, by rfl⟩ : syracuseStep 704591 = 1056887) B1056887
theorem B442799 : Blo 291829 442799 := bstep (se 1 (by rfl) ⟨332099, by rfl⟩ : syracuseStep 442799 = 664199) B664199
theorem B442889 : Blo 291829 442889 := bstep (se 2 (by rfl) ⟨166083, by rfl⟩ : syracuseStep 442889 = 332167) B332167
theorem B1262105 : Blo 291829 1262105 := bstep (se 2 (by rfl) ⟨473289, by rfl⟩ : syracuseStep 1262105 = 946579) B946579
theorem B442919 : Blo 291829 442919 := bstep (se 1 (by rfl) ⟨332189, by rfl⟩ : syracuseStep 442919 = 664379) B664379
theorem B311887 : Blo 291829 311887 := bstep (se 1 (by rfl) ⟨233915, by rfl⟩ : syracuseStep 311887 = 467831) B467831
theorem B443003 : Blo 291829 443003 := bstep (se 1 (by rfl) ⟨332252, by rfl⟩ : syracuseStep 443003 = 664505) B664505
theorem B836345 : Blo 291829 836345 := bstep (se 2 (by rfl) ⟨313629, by rfl⟩ : syracuseStep 836345 = 627259) B627259
theorem B443129 : Blo 291829 443129 := bstep (se 2 (by rfl) ⟨166173, by rfl⟩ : syracuseStep 443129 = 332347) B332347
theorem B4735745 : Blo 291829 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B443231 : Blo 291829 443231 := bstep (se 1 (by rfl) ⟨332423, by rfl⟩ : syracuseStep 443231 = 664847) B664847
theorem B443243 : Blo 291829 443243 := bstep (se 1 (by rfl) ⟨332432, by rfl⟩ : syracuseStep 443243 = 664865) B664865
theorem B2114579 : Blo 291829 2114579 := bstep (se 1 (by rfl) ⟨1585934, by rfl⟩ : syracuseStep 2114579 = 3171869) B3171869
theorem B1492019 : Blo 291829 1492019 := bstep (se 1 (by rfl) ⟨1119014, by rfl⟩ : syracuseStep 1492019 = 2238029) B2238029
theorem B443471 : Blo 291829 443471 := bstep (se 1 (by rfl) ⟨332603, by rfl⟩ : syracuseStep 443471 = 665207) B665207
theorem B2999467 : Blo 291829 2999467 := bstep (se 1 (by rfl) ⟨2249600, by rfl⟩ : syracuseStep 2999467 = 4499201) B4499201
theorem B443591 : Blo 291829 443591 := bstep (se 1 (by rfl) ⟨332693, by rfl⟩ : syracuseStep 443591 = 665387) B665387
theorem B6768035 : Blo 291829 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B738841 : Blo 291829 738841 := bstep (se 2 (by rfl) ⟨277065, by rfl⟩ : syracuseStep 738841 = 554131) B554131
theorem B2246291 : Blo 291829 2246291 := bstep (se 1 (by rfl) ⟨1684718, by rfl⟩ : syracuseStep 2246291 = 3369437) B3369437
theorem B739145 : Blo 291829 739145 := bstep (se 2 (by rfl) ⟨277179, by rfl⟩ : syracuseStep 739145 = 554359) B554359
theorem B837803 : Blo 291829 837803 := bstep (se 1 (by rfl) ⟨628352, by rfl⟩ : syracuseStep 837803 = 1256705) B1256705
theorem B936481 : Blo 291829 936481 := bstep (se 2 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 936481 = 702361) B702361
theorem B3590689 : Blo 291829 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B1493639 : Blo 291829 1493639 := bstep (se 1 (by rfl) ⟨1120229, by rfl⟩ : syracuseStep 1493639 = 2240459) B2240459
theorem B740279 : Blo 291829 740279 := bstep (se 1 (by rfl) ⟨555209, by rfl⟩ : syracuseStep 740279 = 1110419) B1110419
theorem B7588981 : Blo 291829 7588981 := bstep (se 5 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 7588981 = 711467) B711467
theorem B3395195 : Blo 291829 3395195 := bstep (se 1 (by rfl) ⟨2546396, by rfl⟩ : syracuseStep 3395195 = 5092793) B5092793
theorem B741383 : Blo 291829 741383 := bstep (se 1 (by rfl) ⟨556037, by rfl⟩ : syracuseStep 741383 = 1112075) B1112075
theorem B741433 : Blo 291829 741433 := bstep (se 2 (by rfl) ⟨278037, by rfl⟩ : syracuseStep 741433 = 556075) B556075
theorem B1495097 : Blo 291829 1495097 := bstep (se 2 (by rfl) ⟨560661, by rfl⟩ : syracuseStep 1495097 = 1121323) B1121323
theorem B3788977 : Blo 291829 3788977 := bstep (se 2 (by rfl) ⟨1420866, by rfl⟩ : syracuseStep 3788977 = 2841733) B2841733
theorem B741737 : Blo 291829 741737 := bstep (se 2 (by rfl) ⟨278151, by rfl⟩ : syracuseStep 741737 = 556303) B556303
theorem B3429427 : Blo 291829 3429427 := bstep (se 1 (by rfl) ⟨2572070, by rfl⟩ : syracuseStep 3429427 = 5144141) B5144141
theorem B2217131 : Blo 291829 2217131 := bstep (se 1 (by rfl) ⟨1662848, by rfl⟩ : syracuseStep 2217131 = 3325697) B3325697
theorem B2512043 : Blo 291829 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B2249975 : Blo 291829 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B3331529 : Blo 291829 3331529 := bstep (se 2 (by rfl) ⟨1249323, by rfl⟩ : syracuseStep 3331529 = 2498647) B2498647
theorem B939545 : Blo 291829 939545 := bstep (se 2 (by rfl) ⟨352329, by rfl⟩ : syracuseStep 939545 = 704659) B704659
theorem B2217617 : Blo 291829 2217617 := bstep (se 2 (by rfl) ⟨831606, by rfl⟩ : syracuseStep 2217617 = 1663213) B1663213
theorem B22763477 : Blo 291829 22763477 := bstep (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) B533519
theorem B2119769 : Blo 291829 2119769 := bstep (se 2 (by rfl) ⟨794913, by rfl⟩ : syracuseStep 2119769 = 1589827) B1589827
theorem B4216931 : Blo 291829 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B1497203 : Blo 291829 1497203 := bstep (se 1 (by rfl) ⟨1122902, by rfl⟩ : syracuseStep 1497203 = 2245805) B2245805
theorem B1890647 : Blo 291829 1890647 := bstep (se 1 (by rfl) ⟨1417985, by rfl⟩ : syracuseStep 1890647 = 2835971) B2835971
theorem B940531 : Blo 291829 940531 := bstep (se 1 (by rfl) ⟨705398, by rfl⟩ : syracuseStep 940531 = 1410797) B1410797
theorem B743975 : Blo 291829 743975 := bstep (se 1 (by rfl) ⟨557981, by rfl⟩ : syracuseStep 743975 = 1115963) B1115963
theorem B744299 : Blo 291829 744299 := bstep (se 1 (by rfl) ⟨558224, by rfl⟩ : syracuseStep 744299 = 1116449) B1116449
theorem B2219075 : Blo 291829 2219075 := bstep (se 1 (by rfl) ⟨1664306, by rfl⟩ : syracuseStep 2219075 = 3328613) B3328613
theorem B449615 : Blo 291829 449615 := bstep (se 1 (by rfl) ⟨337211, by rfl⟩ : syracuseStep 449615 = 674423) B674423
theorem B1891673 : Blo 291829 1891673 := bstep (se 2 (by rfl) ⟨709377, by rfl⟩ : syracuseStep 1891673 = 1418755) B1418755
theorem B744947 : Blo 291829 744947 := bstep (se 1 (by rfl) ⟨558710, by rfl⟩ : syracuseStep 744947 = 1117421) B1117421
theorem B745159 : Blo 291829 745159 := bstep (se 1 (by rfl) ⟨558869, by rfl⟩ : syracuseStep 745159 = 1117739) B1117739
theorem B1662713 : Blo 291829 1662713 := bstep (se 2 (by rfl) ⟨623517, by rfl⟩ : syracuseStep 1662713 = 1247035) B1247035
theorem B2220047 : Blo 291829 2220047 := bstep (se 1 (by rfl) ⟨1665035, by rfl⟩ : syracuseStep 2220047 = 3330071) B3330071
theorem B942479 : Blo 291829 942479 := bstep (se 1 (by rfl) ⟨706859, by rfl⟩ : syracuseStep 942479 = 1413719) B1413719
theorem B1073645 : Blo 291829 1073645 := bstep (se 3 (by rfl) ⟨201308, by rfl⟩ : syracuseStep 1073645 = 402617) B402617
theorem B746081 : Blo 291829 746081 := bstep (se 2 (by rfl) ⟨279780, by rfl⟩ : syracuseStep 746081 = 559561) B559561
theorem B1664171 : Blo 291829 1664171 := bstep (se 1 (by rfl) ⟨1248128, by rfl⟩ : syracuseStep 1664171 = 2496257) B2496257
theorem B4253147 : Blo 291829 4253147 := bstep (se 1 (by rfl) ⟨3189860, by rfl⟩ : syracuseStep 4253147 = 6379721) B6379721
theorem B1893851 : Blo 291829 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B1894337 : Blo 291829 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B747539 : Blo 291829 747539 := bstep (se 1 (by rfl) ⟨560654, by rfl⟩ : syracuseStep 747539 = 1121309) B1121309
theorem B4745603 : Blo 291829 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B1108505 : Blo 291829 1108505 := bstep (se 2 (by rfl) ⟨415689, by rfl⟩ : syracuseStep 1108505 = 831379) B831379
theorem B1796633 : Blo 291829 1796633 := bstep (se 2 (by rfl) ⟨673737, by rfl⟩ : syracuseStep 1796633 = 1347475) B1347475
theorem B3762733 : Blo 291829 3762733 := bstep (se 3 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 3762733 = 1411025) B1411025
theorem B944939 : Blo 291829 944939 := bstep (se 1 (by rfl) ⟨708704, by rfl⟩ : syracuseStep 944939 = 1417409) B1417409
theorem B2223449 : Blo 291829 2223449 := bstep (se 2 (by rfl) ⟨833793, by rfl⟩ : syracuseStep 2223449 = 1667587) B1667587
theorem B2715275 : Blo 291829 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B683959 : Blo 291829 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B1667087 : Blo 291829 1667087 := bstep (se 1 (by rfl) ⟨1250315, by rfl⟩ : syracuseStep 1667087 = 2500631) B2500631
theorem B1110131 : Blo 291829 1110131 := bstep (se 1 (by rfl) ⟨832598, by rfl⟩ : syracuseStep 1110131 = 1665197) B1665197
theorem B2683415 : Blo 291829 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B946721 : Blo 291829 946721 := bstep (se 2 (by rfl) ⟨355020, by rfl⟩ : syracuseStep 946721 = 710041) B710041
theorem B946937 : Blo 291829 946937 := bstep (se 2 (by rfl) ⟨355101, by rfl⟩ : syracuseStep 946937 = 710203) B710203
theorem B291879 : Blo 291829 291879 := bstep (se 1 (by rfl) ⟨218909, by rfl⟩ : syracuseStep 291879 = 437819) B437819
theorem B291919 : Blo 291829 291919 := bstep (se 1 (by rfl) ⟨218939, by rfl⟩ : syracuseStep 291919 = 437879) B437879
theorem B291935 : Blo 291829 291935 := bstep (se 1 (by rfl) ⟨218951, by rfl⟩ : syracuseStep 291935 = 437903) B437903
theorem B291963 : Blo 291829 291963 := bstep (se 1 (by rfl) ⟨218972, by rfl⟩ : syracuseStep 291963 = 437945) B437945
theorem B292015 : Blo 291829 292015 := bstep (se 1 (by rfl) ⟨219011, by rfl⟩ : syracuseStep 292015 = 438023) B438023
theorem B292039 : Blo 291829 292039 := bstep (se 1 (by rfl) ⟨219029, by rfl⟩ : syracuseStep 292039 = 438059) B438059
theorem B292059 : Blo 291829 292059 := bstep (se 1 (by rfl) ⟨219044, by rfl⟩ : syracuseStep 292059 = 438089) B438089
theorem B292135 : Blo 291829 292135 := bstep (se 1 (by rfl) ⟨219101, by rfl⟩ : syracuseStep 292135 = 438203) B438203
theorem B292175 : Blo 291829 292175 := bstep (se 1 (by rfl) ⟨219131, by rfl⟩ : syracuseStep 292175 = 438263) B438263
theorem B292191 : Blo 291829 292191 := bstep (se 1 (by rfl) ⟨219143, by rfl⟩ : syracuseStep 292191 = 438287) B438287
theorem B292219 : Blo 291829 292219 := bstep (se 1 (by rfl) ⟨219164, by rfl⟩ : syracuseStep 292219 = 438329) B438329
theorem B1111421 : Blo 291829 1111421 := bstep (se 3 (by rfl) ⟨208391, by rfl⟩ : syracuseStep 1111421 = 416783) B416783
theorem B292271 : Blo 291829 292271 := bstep (se 1 (by rfl) ⟨219203, by rfl⟩ : syracuseStep 292271 = 438407) B438407
theorem B292295 : Blo 291829 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B292315 : Blo 291829 292315 := bstep (se 1 (by rfl) ⟨219236, by rfl⟩ : syracuseStep 292315 = 438473) B438473
theorem B292391 : Blo 291829 292391 := bstep (se 1 (by rfl) ⟨219293, by rfl⟩ : syracuseStep 292391 = 438587) B438587
theorem B292431 : Blo 291829 292431 := bstep (se 1 (by rfl) ⟨219323, by rfl⟩ : syracuseStep 292431 = 438647) B438647
theorem B292447 : Blo 291829 292447 := bstep (se 1 (by rfl) ⟨219335, by rfl⟩ : syracuseStep 292447 = 438671) B438671
theorem B292475 : Blo 291829 292475 := bstep (se 1 (by rfl) ⟨219356, by rfl⟩ : syracuseStep 292475 = 438713) B438713
theorem B292527 : Blo 291829 292527 := bstep (se 1 (by rfl) ⟨219395, by rfl⟩ : syracuseStep 292527 = 438791) B438791
theorem B292551 : Blo 291829 292551 := bstep (se 1 (by rfl) ⟨219413, by rfl⟩ : syracuseStep 292551 = 438827) B438827
theorem B2225879 : Blo 291829 2225879 := bstep (se 1 (by rfl) ⟨1669409, by rfl⟩ : syracuseStep 2225879 = 3338819) B3338819
theorem B2520791 : Blo 291829 2520791 := bstep (se 1 (by rfl) ⟨1890593, by rfl⟩ : syracuseStep 2520791 = 3781187) B3781187
theorem B292571 : Blo 291829 292571 := bstep (se 1 (by rfl) ⟨219428, by rfl⟩ : syracuseStep 292571 = 438857) B438857
theorem B292647 : Blo 291829 292647 := bstep (se 1 (by rfl) ⟨219485, by rfl⟩ : syracuseStep 292647 = 438971) B438971
theorem B292687 : Blo 291829 292687 := bstep (se 1 (by rfl) ⟨219515, by rfl⟩ : syracuseStep 292687 = 439031) B439031
theorem B292703 : Blo 291829 292703 := bstep (se 1 (by rfl) ⟨219527, by rfl⟩ : syracuseStep 292703 = 439055) B439055
theorem B292731 : Blo 291829 292731 := bstep (se 1 (by rfl) ⟨219548, by rfl⟩ : syracuseStep 292731 = 439097) B439097
theorem B292783 : Blo 291829 292783 := bstep (se 1 (by rfl) ⟨219587, by rfl⟩ : syracuseStep 292783 = 439175) B439175
theorem B292807 : Blo 291829 292807 := bstep (se 1 (by rfl) ⟨219605, by rfl⟩ : syracuseStep 292807 = 439211) B439211
theorem B292827 : Blo 291829 292827 := bstep (se 1 (by rfl) ⟨219620, by rfl⟩ : syracuseStep 292827 = 439241) B439241
theorem B292903 : Blo 291829 292903 := bstep (se 1 (by rfl) ⟨219677, by rfl⟩ : syracuseStep 292903 = 439355) B439355
theorem B292943 : Blo 291829 292943 := bstep (se 1 (by rfl) ⟨219707, by rfl⟩ : syracuseStep 292943 = 439415) B439415
theorem B292959 : Blo 291829 292959 := bstep (se 1 (by rfl) ⟨219719, by rfl⟩ : syracuseStep 292959 = 439439) B439439
theorem B292987 : Blo 291829 292987 := bstep (se 1 (by rfl) ⟨219740, by rfl⟩ : syracuseStep 292987 = 439481) B439481
theorem B293039 : Blo 291829 293039 := bstep (se 1 (by rfl) ⟨219779, by rfl⟩ : syracuseStep 293039 = 439559) B439559
theorem B293063 : Blo 291829 293063 := bstep (se 1 (by rfl) ⟨219797, by rfl⟩ : syracuseStep 293063 = 439595) B439595
theorem B293083 : Blo 291829 293083 := bstep (se 1 (by rfl) ⟨219812, by rfl⟩ : syracuseStep 293083 = 439625) B439625
theorem B293159 : Blo 291829 293159 := bstep (se 1 (by rfl) ⟨219869, by rfl⟩ : syracuseStep 293159 = 439739) B439739
theorem B293199 : Blo 291829 293199 := bstep (se 1 (by rfl) ⟨219899, by rfl⟩ : syracuseStep 293199 = 439799) B439799
theorem B293215 : Blo 291829 293215 := bstep (se 1 (by rfl) ⟨219911, by rfl⟩ : syracuseStep 293215 = 439823) B439823
theorem B293243 : Blo 291829 293243 := bstep (se 1 (by rfl) ⟨219932, by rfl⟩ : syracuseStep 293243 = 439865) B439865
theorem B555407 : Blo 291829 555407 := bstep (se 1 (by rfl) ⟨416555, by rfl⟩ : syracuseStep 555407 = 833111) B833111
theorem B293295 : Blo 291829 293295 := bstep (se 1 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 293295 = 439943) B439943
theorem B293319 : Blo 291829 293319 := bstep (se 1 (by rfl) ⟨219989, by rfl⟩ : syracuseStep 293319 = 439979) B439979
theorem B293339 : Blo 291829 293339 := bstep (se 1 (by rfl) ⟨220004, by rfl⟩ : syracuseStep 293339 = 440009) B440009
theorem B293415 : Blo 291829 293415 := bstep (se 1 (by rfl) ⟨220061, by rfl⟩ : syracuseStep 293415 = 440123) B440123
theorem B293455 : Blo 291829 293455 := bstep (se 1 (by rfl) ⟨220091, by rfl⟩ : syracuseStep 293455 = 440183) B440183
theorem B293471 : Blo 291829 293471 := bstep (se 1 (by rfl) ⟨220103, by rfl⟩ : syracuseStep 293471 = 440207) B440207
theorem B293499 : Blo 291829 293499 := bstep (se 1 (by rfl) ⟨220124, by rfl⟩ : syracuseStep 293499 = 440249) B440249
theorem B293551 : Blo 291829 293551 := bstep (se 1 (by rfl) ⟨220163, by rfl⟩ : syracuseStep 293551 = 440327) B440327
theorem B293575 : Blo 291829 293575 := bstep (se 1 (by rfl) ⟨220181, by rfl⟩ : syracuseStep 293575 = 440363) B440363
theorem B293595 : Blo 291829 293595 := bstep (se 1 (by rfl) ⟨220196, by rfl⟩ : syracuseStep 293595 = 440393) B440393
theorem B293671 : Blo 291829 293671 := bstep (se 1 (by rfl) ⟨220253, by rfl⟩ : syracuseStep 293671 = 440507) B440507
theorem B293711 : Blo 291829 293711 := bstep (se 1 (by rfl) ⟨220283, by rfl⟩ : syracuseStep 293711 = 440567) B440567
theorem B293727 : Blo 291829 293727 := bstep (se 1 (by rfl) ⟨220295, by rfl⟩ : syracuseStep 293727 = 440591) B440591
theorem B293755 : Blo 291829 293755 := bstep (se 1 (by rfl) ⟨220316, by rfl⟩ : syracuseStep 293755 = 440633) B440633
theorem B293807 : Blo 291829 293807 := bstep (se 1 (by rfl) ⟨220355, by rfl⟩ : syracuseStep 293807 = 440711) B440711
theorem B293831 : Blo 291829 293831 := bstep (se 1 (by rfl) ⟨220373, by rfl⟩ : syracuseStep 293831 = 440747) B440747
theorem B293851 : Blo 291829 293851 := bstep (se 1 (by rfl) ⟨220388, by rfl⟩ : syracuseStep 293851 = 440777) B440777
theorem B293927 : Blo 291829 293927 := bstep (se 1 (by rfl) ⟨220445, by rfl⟩ : syracuseStep 293927 = 440891) B440891
theorem B293967 : Blo 291829 293967 := bstep (se 1 (by rfl) ⟨220475, by rfl⟩ : syracuseStep 293967 = 440951) B440951
theorem B293983 : Blo 291829 293983 := bstep (se 1 (by rfl) ⟨220487, by rfl⟩ : syracuseStep 293983 = 440975) B440975
theorem B294011 : Blo 291829 294011 := bstep (se 1 (by rfl) ⟨220508, by rfl⟩ : syracuseStep 294011 = 441017) B441017
theorem B294063 : Blo 291829 294063 := bstep (se 1 (by rfl) ⟨220547, by rfl⟩ : syracuseStep 294063 = 441095) B441095
theorem B294087 : Blo 291829 294087 := bstep (se 1 (by rfl) ⟨220565, by rfl⟩ : syracuseStep 294087 = 441131) B441131
theorem B294107 : Blo 291829 294107 := bstep (se 1 (by rfl) ⟨220580, by rfl⟩ : syracuseStep 294107 = 441161) B441161
theorem B1113335 : Blo 291829 1113335 := bstep (se 1 (by rfl) ⟨835001, by rfl⟩ : syracuseStep 1113335 = 1670003) B1670003
theorem B294183 : Blo 291829 294183 := bstep (se 1 (by rfl) ⟨220637, by rfl⟩ : syracuseStep 294183 = 441275) B441275
theorem B294223 : Blo 291829 294223 := bstep (se 1 (by rfl) ⟨220667, by rfl⟩ : syracuseStep 294223 = 441335) B441335
theorem B294239 : Blo 291829 294239 := bstep (se 1 (by rfl) ⟨220679, by rfl⟩ : syracuseStep 294239 = 441359) B441359
theorem B294267 : Blo 291829 294267 := bstep (se 1 (by rfl) ⟨220700, by rfl⟩ : syracuseStep 294267 = 441401) B441401
theorem B556463 : Blo 291829 556463 := bstep (se 1 (by rfl) ⟨417347, by rfl⟩ : syracuseStep 556463 = 834695) B834695
theorem B294319 : Blo 291829 294319 := bstep (se 1 (by rfl) ⟨220739, by rfl⟩ : syracuseStep 294319 = 441479) B441479
theorem B294343 : Blo 291829 294343 := bstep (se 1 (by rfl) ⟨220757, by rfl⟩ : syracuseStep 294343 = 441515) B441515
theorem B294363 : Blo 291829 294363 := bstep (se 1 (by rfl) ⟨220772, by rfl⟩ : syracuseStep 294363 = 441545) B441545
theorem B294439 : Blo 291829 294439 := bstep (se 1 (by rfl) ⟨220829, by rfl⟩ : syracuseStep 294439 = 441659) B441659
theorem B294479 : Blo 291829 294479 := bstep (se 1 (by rfl) ⟨220859, by rfl⟩ : syracuseStep 294479 = 441719) B441719
theorem B294495 : Blo 291829 294495 := bstep (se 1 (by rfl) ⟨220871, by rfl⟩ : syracuseStep 294495 = 441743) B441743
theorem B294523 : Blo 291829 294523 := bstep (se 1 (by rfl) ⟨220892, by rfl⟩ : syracuseStep 294523 = 441785) B441785
theorem B294575 : Blo 291829 294575 := bstep (se 1 (by rfl) ⟨220931, by rfl⟩ : syracuseStep 294575 = 441863) B441863
theorem B294599 : Blo 291829 294599 := bstep (se 1 (by rfl) ⟨220949, by rfl⟩ : syracuseStep 294599 = 441899) B441899
theorem B294619 : Blo 291829 294619 := bstep (se 1 (by rfl) ⟨220964, by rfl⟩ : syracuseStep 294619 = 441929) B441929
theorem B294695 : Blo 291829 294695 := bstep (se 1 (by rfl) ⟨221021, by rfl⟩ : syracuseStep 294695 = 442043) B442043
theorem B294735 : Blo 291829 294735 := bstep (se 1 (by rfl) ⟨221051, by rfl⟩ : syracuseStep 294735 = 442103) B442103
theorem B556895 : Blo 291829 556895 := bstep (se 1 (by rfl) ⟨417671, by rfl⟩ : syracuseStep 556895 = 835343) B835343
theorem B294751 : Blo 291829 294751 := bstep (se 1 (by rfl) ⟨221063, by rfl⟩ : syracuseStep 294751 = 442127) B442127
theorem B294779 : Blo 291829 294779 := bstep (se 1 (by rfl) ⟨221084, by rfl⟩ : syracuseStep 294779 = 442169) B442169
theorem B294831 : Blo 291829 294831 := bstep (se 1 (by rfl) ⟨221123, by rfl⟩ : syracuseStep 294831 = 442247) B442247
theorem B14221241 : Blo 291829 14221241 := bstep (se 2 (by rfl) ⟨5332965, by rfl⟩ : syracuseStep 14221241 = 10665931) B10665931
theorem B294855 : Blo 291829 294855 := bstep (se 1 (by rfl) ⟨221141, by rfl⟩ : syracuseStep 294855 = 442283) B442283
theorem B294875 : Blo 291829 294875 := bstep (se 1 (by rfl) ⟨221156, by rfl⟩ : syracuseStep 294875 = 442313) B442313
theorem B295199 : Blo 291829 295199 := bstep (se 1 (by rfl) ⟨221399, by rfl⟩ : syracuseStep 295199 = 442799) B442799
theorem B295259 : Blo 291829 295259 := bstep (se 1 (by rfl) ⟨221444, by rfl⟩ : syracuseStep 295259 = 442889) B442889
theorem B295279 : Blo 291829 295279 := bstep (se 1 (by rfl) ⟨221459, by rfl⟩ : syracuseStep 295279 = 442919) B442919
theorem B295335 : Blo 291829 295335 := bstep (se 1 (by rfl) ⟨221501, by rfl⟩ : syracuseStep 295335 = 443003) B443003
theorem B295419 : Blo 291829 295419 := bstep (se 1 (by rfl) ⟨221564, by rfl⟩ : syracuseStep 295419 = 443129) B443129
theorem B295487 : Blo 291829 295487 := bstep (se 1 (by rfl) ⟨221615, by rfl⟩ : syracuseStep 295487 = 443231) B443231
theorem B295495 : Blo 291829 295495 := bstep (se 1 (by rfl) ⟨221621, by rfl⟩ : syracuseStep 295495 = 443243) B443243
theorem B4981421 : Blo 291829 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B1409719 : Blo 291829 1409719 := bstep (se 1 (by rfl) ⟨1057289, by rfl⟩ : syracuseStep 1409719 = 2114579) B2114579
theorem B295647 : Blo 291829 295647 := bstep (se 1 (by rfl) ⟨221735, by rfl⟩ : syracuseStep 295647 = 443471) B443471
theorem B328495 : Blo 291829 328495 := bstep (se 1 (by rfl) ⟨246371, by rfl⟩ : syracuseStep 328495 = 492743) B492743
theorem B295727 : Blo 291829 295727 := bstep (se 1 (by rfl) ⟨221795, by rfl⟩ : syracuseStep 295727 = 443591) B443591
theorem B4260755 : Blo 291829 4260755 := bstep (se 1 (by rfl) ⟨3195566, by rfl⟩ : syracuseStep 4260755 = 6391133) B6391133
theorem B328603 : Blo 291829 328603 := bstep (se 1 (by rfl) ⟨246452, by rfl⟩ : syracuseStep 328603 = 492905) B492905
theorem B1115279 : Blo 291829 1115279 := bstep (se 1 (by rfl) ⟨836459, by rfl⟩ : syracuseStep 1115279 = 1672919) B1672919
theorem B492763 : Blo 291829 492763 := bstep (se 1 (by rfl) ⟨369572, by rfl⟩ : syracuseStep 492763 = 739145) B739145
theorem B328999 : Blo 291829 328999 := bstep (se 1 (by rfl) ⟨246749, by rfl⟩ : syracuseStep 328999 = 493499) B493499
theorem B5047595 : Blo 291829 5047595 := bstep (se 1 (by rfl) ⟨3785696, by rfl⟩ : syracuseStep 5047595 = 7571393) B7571393
theorem B329071 : Blo 291829 329071 := bstep (se 1 (by rfl) ⟨246803, by rfl⟩ : syracuseStep 329071 = 493607) B493607
theorem B656801 : Blo 291829 656801 := bstep (se 2 (by rfl) ⟨246300, by rfl⟩ : syracuseStep 656801 = 492601) B492601
theorem B1246727 : Blo 291829 1246727 := bstep (se 1 (by rfl) ⟨935045, by rfl⟩ : syracuseStep 1246727 = 1870091) B1870091
theorem B3999289 : Blo 291829 3999289 := bstep (se 2 (by rfl) ⟨1499733, by rfl⟩ : syracuseStep 3999289 = 2999467) B2999467
theorem B329287 : Blo 291829 329287 := bstep (se 1 (by rfl) ⟨246965, by rfl⟩ : syracuseStep 329287 = 493931) B493931
theorem B657359 : Blo 291829 657359 := bstep (se 1 (by rfl) ⟨493019, by rfl⟩ : syracuseStep 657359 = 986039) B986039
theorem B493519 : Blo 291829 493519 := bstep (se 1 (by rfl) ⟨370139, by rfl⟩ : syracuseStep 493519 = 740279) B740279
theorem B2230253 : Blo 291829 2230253 := bstep (se 3 (by rfl) ⟨418172, by rfl⟩ : syracuseStep 2230253 = 836345) B836345
theorem B2525165 : Blo 291829 2525165 := bstep (se 3 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 2525165 = 946937) B946937
theorem B4032517 : Blo 291829 4032517 := bstep (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) B756097
theorem B985121 : Blo 291829 985121 := bstep (se 2 (by rfl) ⟨369420, by rfl⟩ : syracuseStep 985121 = 738841) B738841
theorem B1607933 : Blo 291829 1607933 := bstep (se 3 (by rfl) ⟨301487, by rfl⟩ : syracuseStep 1607933 = 602975) B602975
theorem B657737 : Blo 291829 657737 := bstep (se 2 (by rfl) ⟨246651, by rfl⟩ : syracuseStep 657737 = 493303) B493303
theorem B657755 : Blo 291829 657755 := bstep (se 1 (by rfl) ⟨493316, by rfl⟩ : syracuseStep 657755 = 986633) B986633
theorem B330151 : Blo 291829 330151 := bstep (se 1 (by rfl) ⟨247613, by rfl⟩ : syracuseStep 330151 = 495227) B495227
theorem B2263463 : Blo 291829 2263463 := bstep (se 1 (by rfl) ⟨1697597, by rfl⟩ : syracuseStep 2263463 = 3395195) B3395195
theorem B2230739 : Blo 291829 2230739 := bstep (se 1 (by rfl) ⟨1673054, by rfl⟩ : syracuseStep 2230739 = 3346109) B3346109
theorem B494201 : Blo 291829 494201 := bstep (se 2 (by rfl) ⟨185325, by rfl⟩ : syracuseStep 494201 = 370651) B370651
theorem B494255 : Blo 291829 494255 := bstep (se 1 (by rfl) ⟨370691, by rfl⟩ : syracuseStep 494255 = 741383) B741383
theorem B658331 : Blo 291829 658331 := bstep (se 1 (by rfl) ⟨493748, by rfl⟩ : syracuseStep 658331 = 987497) B987497
theorem B494491 : Blo 291829 494491 := bstep (se 1 (by rfl) ⟨370868, by rfl⟩ : syracuseStep 494491 = 741737) B741737
theorem B330727 : Blo 291829 330727 := bstep (se 1 (by rfl) ⟨248045, by rfl⟩ : syracuseStep 330727 = 496091) B496091
theorem B1117223 : Blo 291829 1117223 := bstep (se 1 (by rfl) ⟨837917, by rfl⟩ : syracuseStep 1117223 = 1675835) B1675835
theorem B658529 : Blo 291829 658529 := bstep (se 2 (by rfl) ⟨246948, by rfl⟩ : syracuseStep 658529 = 493897) B493897
theorem B658727 : Blo 291829 658727 := bstep (se 1 (by rfl) ⟨494045, by rfl⟩ : syracuseStep 658727 = 988091) B988091
theorem B5999933 : Blo 291829 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B1248641 : Blo 291829 1248641 := bstep (se 2 (by rfl) ⟨468240, by rfl⟩ : syracuseStep 1248641 = 936481) B936481
theorem B4787585 : Blo 291829 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B5016977 : Blo 291829 5016977 := bstep (se 2 (by rfl) ⟨1881366, by rfl⟩ : syracuseStep 5016977 = 3762733) B3762733
theorem B1478087 : Blo 291829 1478087 := bstep (se 1 (by rfl) ⟨1108565, by rfl⟩ : syracuseStep 1478087 = 2217131) B2217131
theorem B1674695 : Blo 291829 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B396895 : Blo 291829 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B659105 : Blo 291829 659105 := bstep (se 2 (by rfl) ⟨247164, by rfl⟩ : syracuseStep 659105 = 494329) B494329
theorem B1150625 : Blo 291829 1150625 := bstep (se 2 (by rfl) ⟨431484, by rfl⟩ : syracuseStep 1150625 = 862969) B862969
theorem B626363 : Blo 291829 626363 := bstep (se 1 (by rfl) ⟨469772, by rfl⟩ : syracuseStep 626363 = 939545) B939545
theorem B1478411 : Blo 291829 1478411 := bstep (se 1 (by rfl) ⟨1108808, by rfl⟩ : syracuseStep 1478411 = 2217617) B2217617
theorem B397111 : Blo 291829 397111 := bstep (se 1 (by rfl) ⟨297833, by rfl⟩ : syracuseStep 397111 = 595667) B595667
theorem B659465 : Blo 291829 659465 := bstep (se 2 (by rfl) ⟨247299, by rfl⟩ : syracuseStep 659465 = 494599) B494599
theorem B1413179 : Blo 291829 1413179 := bstep (se 1 (by rfl) ⟨1059884, by rfl⟩ : syracuseStep 1413179 = 2119769) B2119769
theorem B2232683 : Blo 291829 2232683 := bstep (se 1 (by rfl) ⟨1674512, by rfl⟩ : syracuseStep 2232683 = 3349025) B3349025
theorem B495983 : Blo 291829 495983 := bstep (se 1 (by rfl) ⟨371987, by rfl⟩ : syracuseStep 495983 = 743975) B743975
theorem B659879 : Blo 291829 659879 := bstep (se 1 (by rfl) ⟨494909, by rfl⟩ : syracuseStep 659879 = 989819) B989819
theorem B659987 : Blo 291829 659987 := bstep (se 1 (by rfl) ⟨494990, by rfl⟩ : syracuseStep 659987 = 989981) B989981
theorem B1184327 : Blo 291829 1184327 := bstep (se 1 (by rfl) ⟨888245, by rfl⟩ : syracuseStep 1184327 = 1776491) B1776491
theorem B496199 : Blo 291829 496199 := bstep (se 1 (by rfl) ⟨372149, by rfl⟩ : syracuseStep 496199 = 744299) B744299
theorem B660041 : Blo 291829 660041 := bstep (se 2 (by rfl) ⟨247515, by rfl⟩ : syracuseStep 660041 = 495031) B495031
theorem B332383 : Blo 291829 332383 := bstep (se 1 (by rfl) ⟨249287, by rfl⟩ : syracuseStep 332383 = 498575) B498575
theorem B1479383 : Blo 291829 1479383 := bstep (se 1 (by rfl) ⟨1109537, by rfl⟩ : syracuseStep 1479383 = 2219075) B2219075
theorem B299743 : Blo 291829 299743 := bstep (se 1 (by rfl) ⟨224807, by rfl⟩ : syracuseStep 299743 = 449615) B449615
theorem B987983 : Blo 291829 987983 := bstep (se 1 (by rfl) ⟨740987, by rfl⟩ : syracuseStep 987983 = 1481975) B1481975
theorem B8491985 : Blo 291829 8491985 := bstep (se 2 (by rfl) ⟨3184494, by rfl⟩ : syracuseStep 8491985 = 6368989) B6368989
theorem B660455 : Blo 291829 660455 := bstep (se 1 (by rfl) ⟨495341, by rfl⟩ : syracuseStep 660455 = 990683) B990683
theorem B496631 : Blo 291829 496631 := bstep (se 1 (by rfl) ⟨372473, by rfl⟩ : syracuseStep 496631 = 744947) B744947
theorem B988307 : Blo 291829 988307 := bstep (se 1 (by rfl) ⟨741230, by rfl⟩ : syracuseStep 988307 = 1482461) B1482461
theorem B1119379 : Blo 291829 1119379 := bstep (se 1 (by rfl) ⟨839534, by rfl⟩ : syracuseStep 1119379 = 1679069) B1679069
theorem B1578217 : Blo 291829 1578217 := bstep (se 2 (by rfl) ⟨591831, by rfl⟩ : syracuseStep 1578217 = 1183663) B1183663
theorem B791801 : Blo 291829 791801 := bstep (se 2 (by rfl) ⟨296925, by rfl⟩ : syracuseStep 791801 = 593851) B593851
theorem B1480031 : Blo 291829 1480031 := bstep (se 1 (by rfl) ⟨1110023, by rfl⟩ : syracuseStep 1480031 = 2220047) B2220047
theorem B660833 : Blo 291829 660833 := bstep (se 2 (by rfl) ⟨247812, by rfl⟩ : syracuseStep 660833 = 495625) B495625
theorem B3020165 : Blo 291829 3020165 := bstep (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) B566281
theorem B988577 : Blo 291829 988577 := bstep (se 2 (by rfl) ⟨370716, by rfl⟩ : syracuseStep 988577 = 741433) B741433
theorem B660923 : Blo 291829 660923 := bstep (se 1 (by rfl) ⟨495692, by rfl⟩ : syracuseStep 660923 = 991385) B991385
theorem B661049 : Blo 291829 661049 := bstep (se 2 (by rfl) ⟨247893, by rfl⟩ : syracuseStep 661049 = 495787) B495787
theorem B5051969 : Blo 291829 5051969 := bstep (se 2 (by rfl) ⟨1894488, by rfl⟩ : syracuseStep 5051969 = 3788977) B3788977
theorem B628319 : Blo 291829 628319 := bstep (se 1 (by rfl) ⟨471239, by rfl⟩ : syracuseStep 628319 = 942479) B942479
theorem B497387 : Blo 291829 497387 := bstep (se 1 (by rfl) ⟨373040, by rfl⟩ : syracuseStep 497387 = 746081) B746081
theorem B1251101 : Blo 291829 1251101 := bstep (se 3 (by rfl) ⟨234581, by rfl⟩ : syracuseStep 1251101 = 469163) B469163
theorem B2234141 : Blo 291829 2234141 := bstep (se 3 (by rfl) ⟨418901, by rfl⟩ : syracuseStep 2234141 = 837803) B837803
theorem B661715 : Blo 291829 661715 := bstep (se 1 (by rfl) ⟨496286, by rfl⟩ : syracuseStep 661715 = 992573) B992573
theorem B661769 : Blo 291829 661769 := bstep (se 2 (by rfl) ⟨248163, by rfl⟩ : syracuseStep 661769 = 496327) B496327
theorem B661985 : Blo 291829 661985 := bstep (se 2 (by rfl) ⟨248244, by rfl⟩ : syracuseStep 661985 = 496489) B496489
theorem B1579493 : Blo 291829 1579493 := bstep (se 4 (by rfl) ⟨148077, by rfl⟩ : syracuseStep 1579493 = 296155) B296155
theorem B498359 : Blo 291829 498359 := bstep (se 1 (by rfl) ⟨373769, by rfl⟩ : syracuseStep 498359 = 747539) B747539
theorem B662291 : Blo 291829 662291 := bstep (se 1 (by rfl) ⟨496718, by rfl⟩ : syracuseStep 662291 = 993437) B993437
theorem B1252367 : Blo 291829 1252367 := bstep (se 1 (by rfl) ⟨939275, by rfl⟩ : syracuseStep 1252367 = 1878551) B1878551
theorem B662651 : Blo 291829 662651 := bstep (se 1 (by rfl) ⟨496988, by rfl⟩ : syracuseStep 662651 = 993977) B993977
theorem B629959 : Blo 291829 629959 := bstep (se 1 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 629959 = 944939) B944939
theorem B1055963 : Blo 291829 1055963 := bstep (se 1 (by rfl) ⟨791972, by rfl⟩ : syracuseStep 1055963 = 1583945) B1583945
theorem B629993 : Blo 291829 629993 := bstep (se 2 (by rfl) ⟨236247, by rfl⟩ : syracuseStep 629993 = 472495) B472495
theorem B662777 : Blo 291829 662777 := bstep (se 2 (by rfl) ⟨248541, by rfl⟩ : syracuseStep 662777 = 497083) B497083
theorem B662921 : Blo 291829 662921 := bstep (se 2 (by rfl) ⟨248595, by rfl⟩ : syracuseStep 662921 = 497191) B497191
theorem B499081 : Blo 291829 499081 := bstep (se 2 (by rfl) ⟨187155, by rfl⟩ : syracuseStep 499081 = 374311) B374311
theorem B663047 : Blo 291829 663047 := bstep (se 1 (by rfl) ⟨497285, by rfl⟩ : syracuseStep 663047 = 994571) B994571
theorem B1482299 : Blo 291829 1482299 := bstep (se 1 (by rfl) ⟨1111724, by rfl⟩ : syracuseStep 1482299 = 2223449) B2223449
theorem B663227 : Blo 291829 663227 := bstep (se 1 (by rfl) ⟨497420, by rfl⟩ : syracuseStep 663227 = 994841) B994841
theorem B1810183 : Blo 291829 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B663353 : Blo 291829 663353 := bstep (se 2 (by rfl) ⟨248757, by rfl⟩ : syracuseStep 663353 = 497515) B497515
theorem B631147 : Blo 291829 631147 := bstep (se 1 (by rfl) ⟨473360, by rfl⟩ : syracuseStep 631147 = 946721) B946721
theorem B663983 : Blo 291829 663983 := bstep (se 1 (by rfl) ⟨497987, by rfl⟩ : syracuseStep 663983 = 995975) B995975
theorem B664019 : Blo 291829 664019 := bstep (se 1 (by rfl) ⟨498014, by rfl⟩ : syracuseStep 664019 = 996029) B996029
theorem B991763 : Blo 291829 991763 := bstep (se 1 (by rfl) ⟨743822, by rfl⟩ : syracuseStep 991763 = 1487645) B1487645
theorem B664127 : Blo 291829 664127 := bstep (se 1 (by rfl) ⟨498095, by rfl⟩ : syracuseStep 664127 = 996191) B996191
theorem B2761361 : Blo 291829 2761361 := bstep (se 2 (by rfl) ⟨1035510, by rfl⟩ : syracuseStep 2761361 = 2071021) B2071021
theorem B1254041 : Blo 291829 1254041 := bstep (se 2 (by rfl) ⟨470265, by rfl⟩ : syracuseStep 1254041 = 940531) B940531
theorem B664235 : Blo 291829 664235 := bstep (se 1 (by rfl) ⟨498176, by rfl⟩ : syracuseStep 664235 = 996353) B996353
theorem B336559 : Blo 291829 336559 := bstep (se 1 (by rfl) ⟨252419, by rfl⟩ : syracuseStep 336559 = 504839) B504839
theorem B467959 : Blo 291829 467959 := bstep (se 1 (by rfl) ⟨350969, by rfl⟩ : syracuseStep 467959 = 701939) B701939
theorem B1483919 : Blo 291829 1483919 := bstep (se 1 (by rfl) ⟨1112939, by rfl⟩ : syracuseStep 1483919 = 2225879) B2225879
theorem B1680527 : Blo 291829 1680527 := bstep (se 1 (by rfl) ⟨1260395, by rfl⟩ : syracuseStep 1680527 = 2520791) B2520791
theorem B664775 : Blo 291829 664775 := bstep (se 1 (by rfl) ⟨498581, by rfl⟩ : syracuseStep 664775 = 997163) B997163
theorem B664955 : Blo 291829 664955 := bstep (se 1 (by rfl) ⟨498716, by rfl⟩ : syracuseStep 664955 = 997433) B997433
theorem B2499983 : Blo 291829 2499983 := bstep (se 1 (by rfl) ⟨1874987, by rfl⟩ : syracuseStep 2499983 = 3749975) B3749975
theorem B665081 : Blo 291829 665081 := bstep (se 2 (by rfl) ⟨249405, by rfl⟩ : syracuseStep 665081 = 498811) B498811
theorem B665171 : Blo 291829 665171 := bstep (se 1 (by rfl) ⟨498878, by rfl⟩ : syracuseStep 665171 = 997757) B997757
theorem B370271 : Blo 291829 370271 := bstep (se 1 (by rfl) ⟨277703, by rfl⟩ : syracuseStep 370271 = 555407) B555407
theorem B665351 : Blo 291829 665351 := bstep (se 1 (by rfl) ⟨499013, by rfl⟩ : syracuseStep 665351 = 998027) B998027
theorem B796463 : Blo 291829 796463 := bstep (se 1 (by rfl) ⟨597347, by rfl⟩ : syracuseStep 796463 = 1194695) B1194695
theorem B1485053 : Blo 291829 1485053 := bstep (se 3 (by rfl) ⟨278447, by rfl⟩ : syracuseStep 1485053 = 556895) B556895
theorem B993545 : Blo 291829 993545 := bstep (se 2 (by rfl) ⟨372579, by rfl⟩ : syracuseStep 993545 = 745159) B745159
theorem B370975 : Blo 291829 370975 := bstep (se 1 (by rfl) ⟨278231, by rfl⟩ : syracuseStep 370975 = 556463) B556463
theorem B469567 : Blo 291829 469567 := bstep (se 1 (by rfl) ⟨352175, by rfl⟩ : syracuseStep 469567 = 704351) B704351
theorem B9480827 : Blo 291829 9480827 := bstep (se 1 (by rfl) ⟨7110620, by rfl⟩ : syracuseStep 9480827 = 14221241) B14221241
theorem B797359 : Blo 291829 797359 := bstep (se 1 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 797359 = 1196039) B1196039
theorem B469727 : Blo 291829 469727 := bstep (se 1 (by rfl) ⟨352295, by rfl⟩ : syracuseStep 469727 = 704591) B704591
theorem B1682167 : Blo 291829 1682167 := bstep (se 1 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 1682167 = 2523251) B2523251
theorem B502699 : Blo 291829 502699 := bstep (se 1 (by rfl) ⟨377024, by rfl⟩ : syracuseStep 502699 = 754049) B754049
theorem B1485863 : Blo 291829 1485863 := bstep (se 1 (by rfl) ⟨1114397, by rfl⟩ : syracuseStep 1485863 = 2228795) B2228795
theorem B3157163 : Blo 291829 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B994679 : Blo 291829 994679 := bstep (se 1 (by rfl) ⟨746009, by rfl⟩ : syracuseStep 994679 = 1492019) B1492019
theorem B437753 : Blo 291829 437753 := bstep (se 2 (by rfl) ⟨164157, by rfl⟩ : syracuseStep 437753 = 328315) B328315
theorem B437855 : Blo 291829 437855 := bstep (se 1 (by rfl) ⟨328391, by rfl⟩ : syracuseStep 437855 = 656783) B656783
theorem B667297 : Blo 291829 667297 := bstep (se 2 (by rfl) ⟨250236, by rfl⟩ : syracuseStep 667297 = 500473) B500473
theorem B438071 : Blo 291829 438071 := bstep (se 1 (by rfl) ⟨328553, by rfl⟩ : syracuseStep 438071 = 657107) B657107
theorem B503759 : Blo 291829 503759 := bstep (se 1 (by rfl) ⟨377819, by rfl⟩ : syracuseStep 503759 = 755639) B755639
theorem B7155773 : Blo 291829 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B438377 : Blo 291829 438377 := bstep (se 2 (by rfl) ⟨164391, by rfl⟩ : syracuseStep 438377 = 328783) B328783
theorem B438695 : Blo 291829 438695 := bstep (se 1 (by rfl) ⟨329021, by rfl⟩ : syracuseStep 438695 = 658043) B658043
theorem B995759 : Blo 291829 995759 := bstep (se 1 (by rfl) ⟨746819, by rfl⟩ : syracuseStep 995759 = 1493639) B1493639
theorem B438779 : Blo 291829 438779 := bstep (se 1 (by rfl) ⟨329084, by rfl⟩ : syracuseStep 438779 = 658169) B658169
theorem B373243 : Blo 291829 373243 := bstep (se 1 (by rfl) ⟨279932, by rfl⟩ : syracuseStep 373243 = 559865) B559865
theorem B438905 : Blo 291829 438905 := bstep (se 2 (by rfl) ⟨164589, by rfl⟩ : syracuseStep 438905 = 329179) B329179
theorem B1880729 : Blo 291829 1880729 := bstep (se 2 (by rfl) ⟨705273, by rfl⟩ : syracuseStep 1880729 = 1410547) B1410547
theorem B438959 : Blo 291829 438959 := bstep (se 1 (by rfl) ⟨329219, by rfl⟩ : syracuseStep 438959 = 658439) B658439
theorem B439007 : Blo 291829 439007 := bstep (se 1 (by rfl) ⟨329255, by rfl⟩ : syracuseStep 439007 = 658511) B658511
theorem B2110373 : Blo 291829 2110373 := bstep (se 4 (by rfl) ⟨197847, by rfl⟩ : syracuseStep 2110373 = 395695) B395695
theorem B439271 : Blo 291829 439271 := bstep (se 1 (by rfl) ⟨329453, by rfl⟩ : syracuseStep 439271 = 658907) B658907
theorem B832609 : Blo 291829 832609 := bstep (se 2 (by rfl) ⟨312228, by rfl⟩ : syracuseStep 832609 = 624457) B624457
theorem B1487969 : Blo 291829 1487969 := bstep (se 2 (by rfl) ⟨557988, by rfl⟩ : syracuseStep 1487969 = 1115977) B1115977
theorem B832655 : Blo 291829 832655 := bstep (se 1 (by rfl) ⟨624491, by rfl⟩ : syracuseStep 832655 = 1248983) B1248983
theorem B439529 : Blo 291829 439529 := bstep (se 2 (by rfl) ⟨164823, by rfl⟩ : syracuseStep 439529 = 329647) B329647
theorem B439583 : Blo 291829 439583 := bstep (se 1 (by rfl) ⟨329687, by rfl⟩ : syracuseStep 439583 = 659375) B659375
theorem B996731 : Blo 291829 996731 := bstep (se 1 (by rfl) ⟨747548, by rfl⟩ : syracuseStep 996731 = 1495097) B1495097
theorem B439751 : Blo 291829 439751 := bstep (se 1 (by rfl) ⟨329813, by rfl⟩ : syracuseStep 439751 = 659627) B659627
theorem B374215 : Blo 291829 374215 := bstep (se 1 (by rfl) ⟨280661, by rfl⟩ : syracuseStep 374215 = 561323) B561323
theorem B1259165 : Blo 291829 1259165 := bstep (se 3 (by rfl) ⟨236093, by rfl⟩ : syracuseStep 1259165 = 472187) B472187
theorem B440105 : Blo 291829 440105 := bstep (se 2 (by rfl) ⟨165039, by rfl⟩ : syracuseStep 440105 = 330079) B330079
theorem B440111 : Blo 291829 440111 := bstep (se 1 (by rfl) ⟨330083, by rfl⟩ : syracuseStep 440111 = 660167) B660167
theorem B2275463 : Blo 291829 2275463 := bstep (se 1 (by rfl) ⟨1706597, by rfl⟩ : syracuseStep 2275463 = 3413195) B3413195
theorem B440585 : Blo 291829 440585 := bstep (se 2 (by rfl) ⟨165219, by rfl⟩ : syracuseStep 440585 = 330439) B330439
theorem B440687 : Blo 291829 440687 := bstep (se 1 (by rfl) ⟨330515, by rfl⟩ : syracuseStep 440687 = 661031) B661031
theorem B440903 : Blo 291829 440903 := bstep (se 1 (by rfl) ⟨330677, by rfl⟩ : syracuseStep 440903 = 661355) B661355
theorem B440939 : Blo 291829 440939 := bstep (se 1 (by rfl) ⟨330704, by rfl⟩ : syracuseStep 440939 = 661409) B661409
theorem B834295 : Blo 291829 834295 := bstep (se 1 (by rfl) ⟨625721, by rfl⟩ : syracuseStep 834295 = 1251443) B1251443
theorem B998135 : Blo 291829 998135 := bstep (se 1 (by rfl) ⟨748601, by rfl⟩ : syracuseStep 998135 = 1497203) B1497203
theorem B441167 : Blo 291829 441167 := bstep (se 1 (by rfl) ⟨330875, by rfl⟩ : syracuseStep 441167 = 661751) B661751
theorem B5094251 : Blo 291829 5094251 := bstep (se 1 (by rfl) ⟨3820688, by rfl⟩ : syracuseStep 5094251 = 7641377) B7641377
theorem B1260431 : Blo 291829 1260431 := bstep (se 1 (by rfl) ⟨945323, by rfl⟩ : syracuseStep 1260431 = 1890647) B1890647
theorem B441563 : Blo 291829 441563 := bstep (se 1 (by rfl) ⟨331172, by rfl⟩ : syracuseStep 441563 = 662345) B662345
theorem B2374877 : Blo 291829 2374877 := bstep (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) B890579
theorem B2112733 : Blo 291829 2112733 := bstep (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) B792275
theorem B572711 : Blo 291829 572711 := bstep (se 1 (by rfl) ⟨429533, by rfl⟩ : syracuseStep 572711 = 859067) B859067
theorem B1490237 : Blo 291829 1490237 := bstep (se 3 (by rfl) ⟨279419, by rfl⟩ : syracuseStep 1490237 = 558839) B558839
theorem B441737 : Blo 291829 441737 := bstep (se 2 (by rfl) ⟨165651, by rfl⟩ : syracuseStep 441737 = 331303) B331303
theorem B1261115 : Blo 291829 1261115 := bstep (se 1 (by rfl) ⟨945836, by rfl⟩ : syracuseStep 1261115 = 1891673) B1891673
theorem B1195681 : Blo 291829 1195681 := bstep (se 2 (by rfl) ⟨448380, by rfl⟩ : syracuseStep 1195681 = 896761) B896761
theorem B442091 : Blo 291829 442091 := bstep (se 1 (by rfl) ⟨331568, by rfl⟩ : syracuseStep 442091 = 663137) B663137
theorem B60702605 : Blo 291829 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B442319 : Blo 291829 442319 := bstep (se 1 (by rfl) ⟨331739, by rfl⟩ : syracuseStep 442319 = 663479) B663479
theorem B835913 : Blo 291829 835913 := bstep (se 2 (by rfl) ⟨313467, by rfl⟩ : syracuseStep 835913 = 626935) B626935
theorem B442715 : Blo 291829 442715 := bstep (se 1 (by rfl) ⟨332036, by rfl⟩ : syracuseStep 442715 = 664073) B664073
theorem B442943 : Blo 291829 442943 := bstep (se 1 (by rfl) ⟨332207, by rfl⟩ : syracuseStep 442943 = 664415) B664415
theorem B1065593 : Blo 291829 1065593 := bstep (se 2 (by rfl) ⟨399597, by rfl⟩ : syracuseStep 1065593 = 799195) B799195
theorem B443063 : Blo 291829 443063 := bstep (se 1 (by rfl) ⟨332297, by rfl⟩ : syracuseStep 443063 = 664595) B664595
theorem B705359 : Blo 291829 705359 := bstep (se 1 (by rfl) ⟨529019, by rfl⟩ : syracuseStep 705359 = 1058039) B1058039
theorem B443291 : Blo 291829 443291 := bstep (se 1 (by rfl) ⟨332468, by rfl⟩ : syracuseStep 443291 = 664937) B664937
theorem B2835431 : Blo 291829 2835431 := bstep (se 1 (by rfl) ⟨2126573, by rfl⟩ : syracuseStep 2835431 = 4253147) B4253147
theorem B1262567 : Blo 291829 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B443687 : Blo 291829 443687 := bstep (se 1 (by rfl) ⟨332765, by rfl⟩ : syracuseStep 443687 = 665531) B665531
theorem B1262891 : Blo 291829 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B4572569 : Blo 291829 4572569 := bstep (se 2 (by rfl) ⟨1714713, by rfl⟩ : syracuseStep 4572569 = 3429427) B3429427
theorem B3163735 : Blo 291829 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B378475 : Blo 291829 378475 := bstep (se 1 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 378475 = 567713) B567713
theorem B739003 : Blo 291829 739003 := bstep (se 1 (by rfl) ⟨554252, by rfl⟩ : syracuseStep 739003 = 1108505) B1108505
theorem B1492667 : Blo 291829 1492667 := bstep (se 1 (by rfl) ⟨1119500, by rfl⟩ : syracuseStep 1492667 = 2239001) B2239001
theorem B1197755 : Blo 291829 1197755 := bstep (se 1 (by rfl) ⟨898316, by rfl⟩ : syracuseStep 1197755 = 1796633) B1796633
theorem B706283 : Blo 291829 706283 := bstep (se 1 (by rfl) ⟨529712, by rfl⟩ : syracuseStep 706283 = 1059425) B1059425
theorem B509743 : Blo 291829 509743 := bstep (se 1 (by rfl) ⟨382307, by rfl⟩ : syracuseStep 509743 = 764615) B764615
theorem B740087 : Blo 291829 740087 := bstep (se 1 (by rfl) ⟨555065, by rfl⟩ : syracuseStep 740087 = 1110131) B1110131
theorem B1887313 : Blo 291829 1887313 := bstep (se 2 (by rfl) ⟨707742, by rfl⟩ : syracuseStep 1887313 = 1415485) B1415485
theorem B838795 : Blo 291829 838795 := bstep (se 1 (by rfl) ⟨629096, by rfl⟩ : syracuseStep 838795 = 1258193) B1258193
theorem B838943 : Blo 291829 838943 := bstep (se 1 (by rfl) ⟨629207, by rfl⟩ : syracuseStep 838943 = 1258415) B1258415
theorem B707935 : Blo 291829 707935 := bstep (se 1 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 707935 = 1061903) B1061903
theorem B740947 : Blo 291829 740947 := bstep (se 1 (by rfl) ⟨555710, by rfl⟩ : syracuseStep 740947 = 1111421) B1111421
theorem B1494611 : Blo 291829 1494611 := bstep (se 1 (by rfl) ⟨1120958, by rfl⟩ : syracuseStep 1494611 = 2241917) B2241917
theorem B315847 : Blo 291829 315847 := bstep (se 1 (by rfl) ⟨236885, by rfl⟩ : syracuseStep 315847 = 473771) B473771
theorem B742223 : Blo 291829 742223 := bstep (se 1 (by rfl) ⟨556667, by rfl⟩ : syracuseStep 742223 = 1113335) B1113335
theorem B840527 : Blo 291829 840527 := bstep (se 1 (by rfl) ⟨630395, by rfl⟩ : syracuseStep 840527 = 1260791) B1260791
theorem B4773113 : Blo 291829 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B742871 : Blo 291829 742871 := bstep (se 1 (by rfl) ⟨557153, by rfl⟩ : syracuseStep 742871 = 1114307) B1114307
theorem B841403 : Blo 291829 841403 := bstep (se 1 (by rfl) ⟨631052, by rfl⟩ : syracuseStep 841403 = 1262105) B1262105
theorem B743215 : Blo 291829 743215 := bstep (se 1 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 743215 = 1114823) B1114823
theorem B2512727 : Blo 291829 2512727 := bstep (se 1 (by rfl) ⟨1884545, by rfl⟩ : syracuseStep 2512727 = 3769091) B3769091
theorem B415849 : Blo 291829 415849 := bstep (se 2 (by rfl) ⟨155943, by rfl⟩ : syracuseStep 415849 = 311887) B311887
theorem B4512023 : Blo 291829 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B743863 : Blo 291829 743863 := bstep (se 1 (by rfl) ⟨557897, by rfl⟩ : syracuseStep 743863 = 1115795) B1115795
theorem B1497527 : Blo 291829 1497527 := bstep (se 1 (by rfl) ⟨1123145, by rfl⟩ : syracuseStep 1497527 = 2246291) B2246291
theorem B745271 : Blo 291829 745271 := bstep (se 1 (by rfl) ⟨558953, by rfl⟩ : syracuseStep 745271 = 1117907) B1117907
theorem B745321 : Blo 291829 745321 := bstep (se 2 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 745321 = 558991) B558991
theorem B2221019 : Blo 291829 2221019 := bstep (se 1 (by rfl) ⟨1665764, by rfl⟩ : syracuseStep 2221019 = 3331529) B3331529
theorem B12248113 : Blo 291829 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B943247 : Blo 291829 943247 := bstep (se 1 (by rfl) ⟨707435, by rfl⟩ : syracuseStep 943247 = 1414871) B1414871
theorem B746729 : Blo 291829 746729 := bstep (se 2 (by rfl) ⟨280023, by rfl⟩ : syracuseStep 746729 = 560047) B560047
theorem B3007853 : Blo 291829 3007853 := bstep (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) B1127945
theorem B746891 : Blo 291829 746891 := bstep (se 1 (by rfl) ⟨560168, by rfl⟩ : syracuseStep 746891 = 1120337) B1120337
theorem B2811287 : Blo 291829 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B10118641 : Blo 291829 10118641 := bstep (se 2 (by rfl) ⟨3794490, by rfl⟩ : syracuseStep 10118641 = 7588981) B7588981
theorem B747103 : Blo 291829 747103 := bstep (se 1 (by rfl) ⟨560327, by rfl⟩ : syracuseStep 747103 = 1120655) B1120655
theorem B747731 : Blo 291829 747731 := bstep (se 1 (by rfl) ⟨560798, by rfl⟩ : syracuseStep 747731 = 1121597) B1121597
theorem B354727 : Blo 291829 354727 := bstep (se 1 (by rfl) ⟨266045, by rfl⟩ : syracuseStep 354727 = 532091) B532091
theorem B1108475 : Blo 291829 1108475 := bstep (se 1 (by rfl) ⟨831356, by rfl⟩ : syracuseStep 1108475 = 1662713) B1662713
theorem B911945 : Blo 291829 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B3369595 : Blo 291829 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B1403531 : Blo 291829 1403531 := bstep (se 1 (by rfl) ⟨1052648, by rfl⟩ : syracuseStep 1403531 = 2105297) B2105297
theorem B944887 : Blo 291829 944887 := bstep (se 1 (by rfl) ⟨708665, by rfl⟩ : syracuseStep 944887 = 1417331) B1417331
theorem B3173255 : Blo 291829 3173255 := bstep (se 1 (by rfl) ⟨2379941, by rfl⟩ : syracuseStep 3173255 = 4759883) B4759883
theorem B3763097 : Blo 291829 3763097 := bstep (se 2 (by rfl) ⟨1411161, by rfl⟩ : syracuseStep 3763097 = 2822323) B2822323
theorem B715763 : Blo 291829 715763 := bstep (se 1 (by rfl) ⟨536822, by rfl⟩ : syracuseStep 715763 = 1073645) B1073645
theorem B5663783 : Blo 291829 5663783 := bstep (se 1 (by rfl) ⟨4247837, by rfl⟩ : syracuseStep 5663783 = 8495675) B8495675
theorem B1666129 : Blo 291829 1666129 := bstep (se 2 (by rfl) ⟨624798, by rfl⟩ : syracuseStep 1666129 = 1249597) B1249597
theorem B1272955 : Blo 291829 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B1109447 : Blo 291829 1109447 := bstep (se 1 (by rfl) ⟨832085, by rfl⟩ : syracuseStep 1109447 = 1664171) B1664171
theorem B97643981 : Blo 291829 97643981 := bstep (se 3 (by rfl) ⟨18308246, by rfl⟩ : syracuseStep 97643981 = 36616493) B36616493
theorem B1076831 : Blo 291829 1076831 := bstep (se 1 (by rfl) ⟨807623, by rfl⟩ : syracuseStep 1076831 = 1615247) B1615247
theorem B2158289 : Blo 291829 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B4223339 : Blo 291829 4223339 := bstep (se 1 (by rfl) ⟨3167504, by rfl⟩ : syracuseStep 4223339 = 6335009) B6335009
theorem B292127 : Blo 291829 292127 := bstep (se 1 (by rfl) ⟨219095, by rfl⟩ : syracuseStep 292127 = 438191) B438191
theorem B292187 : Blo 291829 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B1111391 : Blo 291829 1111391 := bstep (se 1 (by rfl) ⟨833543, by rfl⟩ : syracuseStep 1111391 = 1667087) B1667087
theorem B292207 : Blo 291829 292207 := bstep (se 1 (by rfl) ⟨219155, by rfl⟩ : syracuseStep 292207 = 438311) B438311
theorem B292263 : Blo 291829 292263 := bstep (se 1 (by rfl) ⟨219197, by rfl⟩ : syracuseStep 292263 = 438395) B438395
theorem B1668545 : Blo 291829 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B292347 : Blo 291829 292347 := bstep (se 1 (by rfl) ⟨219260, by rfl⟩ : syracuseStep 292347 = 438521) B438521
theorem B292415 : Blo 291829 292415 := bstep (se 1 (by rfl) ⟨219311, by rfl⟩ : syracuseStep 292415 = 438623) B438623
theorem B292423 : Blo 291829 292423 := bstep (se 1 (by rfl) ⟨219317, by rfl⟩ : syracuseStep 292423 = 438635) B438635
theorem B292575 : Blo 291829 292575 := bstep (se 1 (by rfl) ⟨219431, by rfl⟩ : syracuseStep 292575 = 438863) B438863
theorem B10385189 : Blo 291829 10385189 := bstep (se 4 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 10385189 = 1947223) B1947223
theorem B292655 : Blo 291829 292655 := bstep (se 1 (by rfl) ⟨219491, by rfl⟩ : syracuseStep 292655 = 438983) B438983
theorem B6453107 : Blo 291829 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B292763 : Blo 291829 292763 := bstep (se 1 (by rfl) ⟨219572, by rfl⟩ : syracuseStep 292763 = 439145) B439145
theorem B292815 : Blo 291829 292815 := bstep (se 1 (by rfl) ⟨219611, by rfl⟩ : syracuseStep 292815 = 439223) B439223
theorem B292839 : Blo 291829 292839 := bstep (se 1 (by rfl) ⟨219629, by rfl⟩ : syracuseStep 292839 = 439259) B439259
theorem B293151 : Blo 291829 293151 := bstep (se 1 (by rfl) ⟨219863, by rfl⟩ : syracuseStep 293151 = 439727) B439727
theorem B293211 : Blo 291829 293211 := bstep (se 1 (by rfl) ⟨219908, by rfl⟩ : syracuseStep 293211 = 439817) B439817
theorem B293231 : Blo 291829 293231 := bstep (se 1 (by rfl) ⟨219923, by rfl⟩ : syracuseStep 293231 = 439847) B439847
theorem B1341839 : Blo 291829 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B293287 : Blo 291829 293287 := bstep (se 1 (by rfl) ⟨219965, by rfl⟩ : syracuseStep 293287 = 439931) B439931
theorem B293371 : Blo 291829 293371 := bstep (se 1 (by rfl) ⟨220028, by rfl⟩ : syracuseStep 293371 = 440057) B440057
theorem B293439 : Blo 291829 293439 := bstep (se 1 (by rfl) ⟨220079, by rfl⟩ : syracuseStep 293439 = 440159) B440159
theorem B293447 : Blo 291829 293447 := bstep (se 1 (by rfl) ⟨220085, by rfl⟩ : syracuseStep 293447 = 440171) B440171
theorem B752249 : Blo 291829 752249 := bstep (se 2 (by rfl) ⟨282093, by rfl⟩ : syracuseStep 752249 = 564187) B564187
theorem B293599 : Blo 291829 293599 := bstep (se 1 (by rfl) ⟨220199, by rfl⟩ : syracuseStep 293599 = 440399) B440399
theorem B293679 : Blo 291829 293679 := bstep (se 1 (by rfl) ⟨220259, by rfl⟩ : syracuseStep 293679 = 440519) B440519
theorem B293787 : Blo 291829 293787 := bstep (se 1 (by rfl) ⟨220340, by rfl⟩ : syracuseStep 293787 = 440681) B440681
theorem B293839 : Blo 291829 293839 := bstep (se 1 (by rfl) ⟨220379, by rfl⟩ : syracuseStep 293839 = 440759) B440759
theorem B293863 : Blo 291829 293863 := bstep (se 1 (by rfl) ⟨220397, by rfl⟩ : syracuseStep 293863 = 440795) B440795
theorem B5012603 : Blo 291829 5012603 := bstep (se 1 (by rfl) ⟨3759452, by rfl⟩ : syracuseStep 5012603 = 7518905) B7518905
theorem B294175 : Blo 291829 294175 := bstep (se 1 (by rfl) ⟨220631, by rfl⟩ : syracuseStep 294175 = 441263) B441263
theorem B294235 : Blo 291829 294235 := bstep (se 1 (by rfl) ⟨220676, by rfl⟩ : syracuseStep 294235 = 441353) B441353
theorem B294255 : Blo 291829 294255 := bstep (se 1 (by rfl) ⟨220691, by rfl⟩ : syracuseStep 294255 = 441383) B441383
theorem B294311 : Blo 291829 294311 := bstep (se 1 (by rfl) ⟨220733, by rfl⟩ : syracuseStep 294311 = 441467) B441467
theorem B294395 : Blo 291829 294395 := bstep (se 1 (by rfl) ⟨220796, by rfl⟩ : syracuseStep 294395 = 441593) B441593
theorem B294463 : Blo 291829 294463 := bstep (se 1 (by rfl) ⟨220847, by rfl⟩ : syracuseStep 294463 = 441695) B441695
theorem B294471 : Blo 291829 294471 := bstep (se 1 (by rfl) ⟨220853, by rfl⟩ : syracuseStep 294471 = 441707) B441707
theorem B294623 : Blo 291829 294623 := bstep (se 1 (by rfl) ⟨220967, by rfl⟩ : syracuseStep 294623 = 441935) B441935
theorem B294703 : Blo 291829 294703 := bstep (se 1 (by rfl) ⟨221027, by rfl⟩ : syracuseStep 294703 = 442055) B442055
theorem B294811 : Blo 291829 294811 := bstep (se 1 (by rfl) ⟨221108, by rfl⟩ : syracuseStep 294811 = 442217) B442217
theorem B294863 : Blo 291829 294863 := bstep (se 1 (by rfl) ⟨221147, by rfl⟩ : syracuseStep 294863 = 442295) B442295
theorem B294887 : Blo 291829 294887 := bstep (se 1 (by rfl) ⟨221165, by rfl⟩ : syracuseStep 294887 = 442331) B442331
theorem B557275 : Blo 291829 557275 := bstep (se 1 (by rfl) ⟨417956, by rfl⟩ : syracuseStep 557275 = 835913) B835913
theorem B295143 : Blo 291829 295143 := bstep (se 1 (by rfl) ⟨221357, by rfl⟩ : syracuseStep 295143 = 442715) B442715
theorem B295295 : Blo 291829 295295 := bstep (se 1 (by rfl) ⟨221471, by rfl⟩ : syracuseStep 295295 = 442943) B442943
theorem B295375 : Blo 291829 295375 := bstep (se 1 (by rfl) ⟨221531, by rfl⟩ : syracuseStep 295375 = 443063) B443063
theorem B295527 : Blo 291829 295527 := bstep (se 1 (by rfl) ⟨221645, by rfl⟩ : syracuseStep 295527 = 443291) B443291
theorem B295791 : Blo 291829 295791 := bstep (se 1 (by rfl) ⟨221843, by rfl⟩ : syracuseStep 295791 = 443687) B443687
theorem B623945 : Blo 291829 623945 := bstep (se 2 (by rfl) ⟨233979, by rfl⟩ : syracuseStep 623945 = 467959) B467959
theorem B656747 : Blo 291829 656747 := bstep (se 1 (by rfl) ⟨492560, by rfl⟩ : syracuseStep 656747 = 985121) B985121
theorem B1508975 : Blo 291829 1508975 := bstep (se 1 (by rfl) ⟨1131731, by rfl⟩ : syracuseStep 1508975 = 2263463) B2263463
theorem B657017 : Blo 291829 657017 := bstep (se 2 (by rfl) ⟨246381, by rfl⟩ : syracuseStep 657017 = 492763) B492763
theorem B329467 : Blo 291829 329467 := bstep (se 1 (by rfl) ⟨247100, by rfl⟩ : syracuseStep 329467 = 494201) B494201
theorem B329503 : Blo 291829 329503 := bstep (se 1 (by rfl) ⟨247127, by rfl⟩ : syracuseStep 329503 = 494255) B494255
theorem B493391 : Blo 291829 493391 := bstep (se 1 (by rfl) ⟨370043, by rfl⟩ : syracuseStep 493391 = 740087) B740087
theorem B559295 : Blo 291829 559295 := bstep (se 1 (by rfl) ⟨419471, by rfl⟩ : syracuseStep 559295 = 838943) B838943
theorem B3999955 : Blo 291829 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B985337 : Blo 291829 985337 := bstep (se 2 (by rfl) ⟨369501, by rfl⟩ : syracuseStep 985337 = 739003) B739003
theorem B3344651 : Blo 291829 3344651 := bstep (se 1 (by rfl) ⟨2508488, by rfl⟩ : syracuseStep 3344651 = 5016977) B5016977
theorem B985391 : Blo 291829 985391 := bstep (se 1 (by rfl) ⟨739043, by rfl⟩ : syracuseStep 985391 = 1478087) B1478087
theorem B1116463 : Blo 291829 1116463 := bstep (se 1 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 1116463 = 1674695) B1674695
theorem B985607 : Blo 291829 985607 := bstep (se 1 (by rfl) ⟨739205, by rfl⟩ : syracuseStep 985607 = 1478411) B1478411
theorem B658025 : Blo 291829 658025 := bstep (se 2 (by rfl) ⟨246759, by rfl⟩ : syracuseStep 658025 = 493519) B493519
theorem B5376689 : Blo 291829 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B330655 : Blo 291829 330655 := bstep (se 1 (by rfl) ⟨247991, by rfl⟩ : syracuseStep 330655 = 495983) B495983
theorem B494633 : Blo 291829 494633 := bstep (se 2 (by rfl) ⟨185487, by rfl⟩ : syracuseStep 494633 = 370975) B370975
theorem B789551 : Blo 291829 789551 := bstep (se 1 (by rfl) ⟨592163, by rfl⟩ : syracuseStep 789551 = 1184327) B1184327
theorem B330799 : Blo 291829 330799 := bstep (se 1 (by rfl) ⟨248099, by rfl⟩ : syracuseStep 330799 = 496199) B496199
theorem B986255 : Blo 291829 986255 := bstep (se 1 (by rfl) ⟨739691, by rfl⟩ : syracuseStep 986255 = 1479383) B1479383
theorem B658655 : Blo 291829 658655 := bstep (se 1 (by rfl) ⟨493991, by rfl⟩ : syracuseStep 658655 = 987983) B987983
theorem B494815 : Blo 291829 494815 := bstep (se 1 (by rfl) ⟨371111, by rfl⟩ : syracuseStep 494815 = 742223) B742223
theorem B560351 : Blo 291829 560351 := bstep (se 1 (by rfl) ⟨420263, by rfl⟩ : syracuseStep 560351 = 840527) B840527
theorem B331087 : Blo 291829 331087 := bstep (se 1 (by rfl) ⟨248315, by rfl⟩ : syracuseStep 331087 = 496631) B496631
theorem B658871 : Blo 291829 658871 := bstep (se 1 (by rfl) ⟨494153, by rfl⟩ : syracuseStep 658871 = 988307) B988307
theorem B4492793 : Blo 291829 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B527867 : Blo 291829 527867 := bstep (se 1 (by rfl) ⟨395900, by rfl⟩ : syracuseStep 527867 = 791801) B791801
theorem B3182075 : Blo 291829 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B986687 : Blo 291829 986687 := bstep (se 1 (by rfl) ⟨740015, by rfl⟩ : syracuseStep 986687 = 1480031) B1480031
theorem B659051 : Blo 291829 659051 := bstep (se 1 (by rfl) ⟨494288, by rfl⟩ : syracuseStep 659051 = 988577) B988577
theorem B495247 : Blo 291829 495247 := bstep (se 1 (by rfl) ⟨371435, by rfl⟩ : syracuseStep 495247 = 742871) B742871
theorem B12193517 : Blo 291829 12193517 := bstep (se 3 (by rfl) ⟨2286284, by rfl⟩ : syracuseStep 12193517 = 4572569) B4572569
theorem B560935 : Blo 291829 560935 := bstep (se 1 (by rfl) ⟨420701, by rfl⟩ : syracuseStep 560935 = 841403) B841403
theorem B331591 : Blo 291829 331591 := bstep (se 1 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 331591 = 497387) B497387
theorem B659321 : Blo 291829 659321 := bstep (se 2 (by rfl) ⟨247245, by rfl⟩ : syracuseStep 659321 = 494491) B494491
theorem B1675151 : Blo 291829 1675151 := bstep (se 1 (by rfl) ⟨1256363, by rfl⟩ : syracuseStep 1675151 = 2512727) B2512727
theorem B1118393 : Blo 291829 1118393 := bstep (se 2 (by rfl) ⟨419397, by rfl⟩ : syracuseStep 1118393 = 838795) B838795
theorem B987389 : Blo 291829 987389 := bstep (se 3 (by rfl) ⟨185135, by rfl⟩ : syracuseStep 987389 = 370271) B370271
theorem B1052995 : Blo 291829 1052995 := bstep (se 1 (by rfl) ⟨789746, by rfl⟩ : syracuseStep 1052995 = 1579493) B1579493
theorem B332239 : Blo 291829 332239 := bstep (se 1 (by rfl) ⟨249179, by rfl⟩ : syracuseStep 332239 = 498359) B498359
theorem B987929 : Blo 291829 987929 := bstep (se 2 (by rfl) ⟨370473, by rfl⟩ : syracuseStep 987929 = 740947) B740947
theorem B529193 : Blo 291829 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B988199 : Blo 291829 988199 := bstep (se 1 (by rfl) ⟨741149, by rfl⟩ : syracuseStep 988199 = 1482299) B1482299
theorem B529481 : Blo 291829 529481 := bstep (se 2 (by rfl) ⟨198555, by rfl⟩ : syracuseStep 529481 = 397111) B397111
theorem B496847 : Blo 291829 496847 := bstep (se 1 (by rfl) ⟨372635, by rfl⟩ : syracuseStep 496847 = 745271) B745271
theorem B661175 : Blo 291829 661175 := bstep (se 1 (by rfl) ⟨495881, by rfl⟩ : syracuseStep 661175 = 991763) B991763
theorem B1840907 : Blo 291829 1840907 := bstep (se 1 (by rfl) ⟨1380680, by rfl⟩ : syracuseStep 1840907 = 2761361) B2761361
theorem B1480679 : Blo 291829 1480679 := bstep (se 1 (by rfl) ⟨1110509, by rfl⟩ : syracuseStep 1480679 = 2221019) B2221019
theorem B497657 : Blo 291829 497657 := bstep (se 2 (by rfl) ⟨186621, by rfl⟩ : syracuseStep 497657 = 373243) B373243
theorem B1120351 : Blo 291829 1120351 := bstep (se 1 (by rfl) ⟨840263, by rfl⟩ : syracuseStep 1120351 = 1680527) B1680527
theorem B989279 : Blo 291829 989279 := bstep (se 1 (by rfl) ⟨741959, by rfl⟩ : syracuseStep 989279 = 1483919) B1483919
theorem B628831 : Blo 291829 628831 := bstep (se 1 (by rfl) ⟨471623, by rfl⟩ : syracuseStep 628831 = 943247) B943247
theorem B497819 : Blo 291829 497819 := bstep (se 1 (by rfl) ⟨373364, by rfl⟩ : syracuseStep 497819 = 746729) B746729
theorem B2005235 : Blo 291829 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B497927 : Blo 291829 497927 := bstep (se 1 (by rfl) ⟨373445, by rfl⟩ : syracuseStep 497927 = 746891) B746891
theorem B1874191 : Blo 291829 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B530975 : Blo 291829 530975 := bstep (se 1 (by rfl) ⟨398231, by rfl⟩ : syracuseStep 530975 = 796463) B796463
theorem B498487 : Blo 291829 498487 := bstep (se 1 (by rfl) ⟨373865, by rfl⟩ : syracuseStep 498487 = 747731) B747731
theorem B990035 : Blo 291829 990035 := bstep (se 1 (by rfl) ⟨742526, by rfl⟩ : syracuseStep 990035 = 1485053) B1485053
theorem B662363 : Blo 291829 662363 := bstep (se 1 (by rfl) ⟨496772, by rfl⟩ : syracuseStep 662363 = 993545) B993545
theorem B2431853 : Blo 291829 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B2104289 : Blo 291829 2104289 := bstep (se 2 (by rfl) ⟨789108, by rfl⟩ : syracuseStep 2104289 = 1578217) B1578217
theorem B498953 : Blo 291829 498953 := bstep (se 2 (by rfl) ⟨187107, by rfl⟩ : syracuseStep 498953 = 374215) B374215
theorem B990575 : Blo 291829 990575 := bstep (se 1 (by rfl) ⟨742931, by rfl⟩ : syracuseStep 990575 = 1485863) B1485863
theorem B3775855 : Blo 291829 3775855 := bstep (se 1 (by rfl) ⟨2831891, by rfl⟩ : syracuseStep 3775855 = 5663783) B5663783
theorem B2104775 : Blo 291829 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B663119 : Blo 291829 663119 := bstep (se 1 (by rfl) ⟨497339, by rfl⟩ : syracuseStep 663119 = 994679) B994679
theorem B990953 : Blo 291829 990953 := bstep (se 2 (by rfl) ⟨371607, by rfl⟩ : syracuseStep 990953 = 743215) B743215
theorem B335839 : Blo 291829 335839 := bstep (se 1 (by rfl) ⟨251879, by rfl⟩ : syracuseStep 335839 = 503759) B503759
theorem B663839 : Blo 291829 663839 := bstep (se 1 (by rfl) ⟨497879, by rfl⟩ : syracuseStep 663839 = 995759) B995759
theorem B1253819 : Blo 291829 1253819 := bstep (se 1 (by rfl) ⟨940364, by rfl⟩ : syracuseStep 1253819 = 1880729) B1880729
theorem B991817 : Blo 291829 991817 := bstep (se 2 (by rfl) ⟨371931, by rfl⟩ : syracuseStep 991817 = 743863) B743863
theorem B6333005 : Blo 291829 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B991979 : Blo 291829 991979 := bstep (se 1 (by rfl) ⟨743984, by rfl⟩ : syracuseStep 991979 = 1487969) B1487969
theorem B664487 : Blo 291829 664487 := bstep (se 1 (by rfl) ⟨498365, by rfl⟩ : syracuseStep 664487 = 996731) B996731
theorem B6923459 : Blo 291829 6923459 := bstep (se 1 (by rfl) ⟨5192594, by rfl⟩ : syracuseStep 6923459 = 10385189) B10385189
theorem B4302071 : Blo 291829 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B1516975 : Blo 291829 1516975 := bstep (se 1 (by rfl) ⟨1137731, by rfl⟩ : syracuseStep 1516975 = 2275463) B2275463
theorem B894559 : Blo 291829 894559 := bstep (se 1 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 894559 = 1341839) B1341839
theorem B501499 : Blo 291829 501499 := bstep (se 1 (by rfl) ⟨376124, by rfl⟩ : syracuseStep 501499 = 752249) B752249
theorem B665423 : Blo 291829 665423 := bstep (se 1 (by rfl) ⟨499067, by rfl⟩ : syracuseStep 665423 = 998135) B998135
theorem B665441 : Blo 291829 665441 := bstep (se 2 (by rfl) ⟨249540, by rfl⟩ : syracuseStep 665441 = 499081) B499081
theorem B993491 : Blo 291829 993491 := bstep (se 1 (by rfl) ⟨745118, by rfl⟩ : syracuseStep 993491 = 1490237) B1490237
theorem B993761 : Blo 291829 993761 := bstep (se 2 (by rfl) ⟨372660, by rfl⟩ : syracuseStep 993761 = 745321) B745321
theorem B3320947 : Blo 291829 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B1879625 : Blo 291829 1879625 := bstep (se 2 (by rfl) ⟨704859, by rfl⟩ : syracuseStep 1879625 = 1409719) B1409719
theorem B437867 : Blo 291829 437867 := bstep (se 1 (by rfl) ⟨328400, by rfl⟩ : syracuseStep 437867 = 656801) B656801
theorem B831151 : Blo 291829 831151 := bstep (se 1 (by rfl) ⟨623363, by rfl⟩ : syracuseStep 831151 = 1246727) B1246727
theorem B437993 : Blo 291829 437993 := bstep (se 2 (by rfl) ⟨164247, by rfl⟩ : syracuseStep 437993 = 328495) B328495
theorem B995111 : Blo 291829 995111 := bstep (se 1 (by rfl) ⟨746333, by rfl⟩ : syracuseStep 995111 = 1492667) B1492667
theorem B798503 : Blo 291829 798503 := bstep (se 1 (by rfl) ⟨598877, by rfl⟩ : syracuseStep 798503 = 1197755) B1197755
theorem B470855 : Blo 291829 470855 := bstep (se 1 (by rfl) ⟨353141, by rfl⟩ : syracuseStep 470855 = 706283) B706283
theorem B438137 : Blo 291829 438137 := bstep (se 2 (by rfl) ⟨164301, by rfl⟩ : syracuseStep 438137 = 328603) B328603
theorem B438239 : Blo 291829 438239 := bstep (se 1 (by rfl) ⟨328679, by rfl⟩ : syracuseStep 438239 = 657359) B657359
theorem B1486835 : Blo 291829 1486835 := bstep (se 1 (by rfl) ⟨1115126, by rfl⟩ : syracuseStep 1486835 = 2230253) B2230253
theorem B1683443 : Blo 291829 1683443 := bstep (se 1 (by rfl) ⟨1262582, by rfl⟩ : syracuseStep 1683443 = 2525165) B2525165
theorem B16330817 : Blo 291829 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B438491 : Blo 291829 438491 := bstep (se 1 (by rfl) ⟨328868, by rfl⟩ : syracuseStep 438491 = 657737) B657737
theorem B438503 : Blo 291829 438503 := bstep (se 1 (by rfl) ⟨328877, by rfl⟩ : syracuseStep 438503 = 657755) B657755
theorem B1487159 : Blo 291829 1487159 := bstep (se 1 (by rfl) ⟨1115369, by rfl⟩ : syracuseStep 1487159 = 2230739) B2230739
theorem B438665 : Blo 291829 438665 := bstep (se 2 (by rfl) ⟨164499, by rfl⟩ : syracuseStep 438665 = 328999) B328999
theorem B438761 : Blo 291829 438761 := bstep (se 2 (by rfl) ⟨164535, by rfl⟩ : syracuseStep 438761 = 329071) B329071
theorem B438887 : Blo 291829 438887 := bstep (se 1 (by rfl) ⟨329165, by rfl⟩ : syracuseStep 438887 = 658331) B658331
theorem B439019 : Blo 291829 439019 := bstep (se 1 (by rfl) ⟨329264, by rfl⟩ : syracuseStep 439019 = 658529) B658529
theorem B439049 : Blo 291829 439049 := bstep (se 2 (by rfl) ⟨164643, by rfl⟩ : syracuseStep 439049 = 329287) B329287
theorem B996137 : Blo 291829 996137 := bstep (se 2 (by rfl) ⟨373551, by rfl⟩ : syracuseStep 996137 = 747103) B747103
theorem B439151 : Blo 291829 439151 := bstep (se 1 (by rfl) ⟨329363, by rfl⟩ : syracuseStep 439151 = 658727) B658727
theorem B1880957 : Blo 291829 1880957 := bstep (se 3 (by rfl) ⟨352679, by rfl⟩ : syracuseStep 1880957 = 705359) B705359
theorem B832427 : Blo 291829 832427 := bstep (se 1 (by rfl) ⟨624320, by rfl⟩ : syracuseStep 832427 = 1248641) B1248641
theorem B3191723 : Blo 291829 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B996407 : Blo 291829 996407 := bstep (se 1 (by rfl) ⟨747305, by rfl⟩ : syracuseStep 996407 = 1494611) B1494611
theorem B439403 : Blo 291829 439403 := bstep (se 1 (by rfl) ⟨329552, by rfl⟩ : syracuseStep 439403 = 659105) B659105
theorem B767083 : Blo 291829 767083 := bstep (se 1 (by rfl) ⟨575312, by rfl⟩ : syracuseStep 767083 = 1150625) B1150625
theorem B439643 : Blo 291829 439643 := bstep (se 1 (by rfl) ⟨329732, by rfl⟩ : syracuseStep 439643 = 659465) B659465
theorem B1488455 : Blo 291829 1488455 := bstep (se 1 (by rfl) ⟨1116341, by rfl⟩ : syracuseStep 1488455 = 2232683) B2232683
theorem B439919 : Blo 291829 439919 := bstep (se 1 (by rfl) ⟨329939, by rfl⟩ : syracuseStep 439919 = 659879) B659879
theorem B2504357 : Blo 291829 2504357 := bstep (se 4 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 2504357 = 469567) B469567
theorem B439991 : Blo 291829 439991 := bstep (se 1 (by rfl) ⟨329993, by rfl⟩ : syracuseStep 439991 = 659987) B659987
theorem B440027 : Blo 291829 440027 := bstep (se 1 (by rfl) ⟨330020, by rfl⟩ : syracuseStep 440027 = 660041) B660041
theorem B440201 : Blo 291829 440201 := bstep (se 2 (by rfl) ⟨165075, by rfl⟩ : syracuseStep 440201 = 330151) B330151
theorem B472969 : Blo 291829 472969 := bstep (se 2 (by rfl) ⟨177363, by rfl⟩ : syracuseStep 472969 = 354727) B354727
theorem B440303 : Blo 291829 440303 := bstep (se 1 (by rfl) ⟨330227, by rfl⟩ : syracuseStep 440303 = 660455) B660455
theorem B1063145 : Blo 291829 1063145 := bstep (se 2 (by rfl) ⟨398679, by rfl⟩ : syracuseStep 1063145 = 797359) B797359
theorem B440555 : Blo 291829 440555 := bstep (se 1 (by rfl) ⟨330416, by rfl⟩ : syracuseStep 440555 = 660833) B660833
theorem B2013443 : Blo 291829 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B440615 : Blo 291829 440615 := bstep (se 1 (by rfl) ⟨330461, by rfl⟩ : syracuseStep 440615 = 660923) B660923
theorem B1259849 : Blo 291829 1259849 := bstep (se 2 (by rfl) ⟨472443, by rfl⟩ : syracuseStep 1259849 = 944887) B944887
theorem B2242889 : Blo 291829 2242889 := bstep (se 2 (by rfl) ⟨841083, by rfl⟩ : syracuseStep 2242889 = 1682167) B1682167
theorem B440699 : Blo 291829 440699 := bstep (se 1 (by rfl) ⟨330524, by rfl⟩ : syracuseStep 440699 = 661049) B661049
theorem B834067 : Blo 291829 834067 := bstep (se 1 (by rfl) ⟨625550, by rfl⟩ : syracuseStep 834067 = 1251101) B1251101
theorem B1489427 : Blo 291829 1489427 := bstep (se 1 (by rfl) ⟨1117070, by rfl⟩ : syracuseStep 1489427 = 2234141) B2234141
theorem B670265 : Blo 291829 670265 := bstep (se 2 (by rfl) ⟨251349, by rfl⟩ : syracuseStep 670265 = 502699) B502699
theorem B440969 : Blo 291829 440969 := bstep (se 2 (by rfl) ⟨165363, by rfl⟩ : syracuseStep 440969 = 330727) B330727
theorem B441143 : Blo 291829 441143 := bstep (se 1 (by rfl) ⟨330857, by rfl⟩ : syracuseStep 441143 = 661715) B661715
theorem B441179 : Blo 291829 441179 := bstep (se 1 (by rfl) ⟨330884, by rfl⟩ : syracuseStep 441179 = 661769) B661769
theorem B998351 : Blo 291829 998351 := bstep (se 1 (by rfl) ⟨748763, by rfl⟩ : syracuseStep 998351 = 1497527) B1497527
theorem B441323 : Blo 291829 441323 := bstep (se 1 (by rfl) ⟨330992, by rfl⟩ : syracuseStep 441323 = 661985) B661985
theorem B3357773 : Blo 291829 3357773 := bstep (se 3 (by rfl) ⟨629582, by rfl⟩ : syracuseStep 3357773 = 1259165) B1259165
theorem B441527 : Blo 291829 441527 := bstep (se 1 (by rfl) ⟨331145, by rfl⟩ : syracuseStep 441527 = 662291) B662291
theorem B834911 : Blo 291829 834911 := bstep (se 1 (by rfl) ⟨626183, by rfl⟩ : syracuseStep 834911 = 1252367) B1252367
theorem B441767 : Blo 291829 441767 := bstep (se 1 (by rfl) ⟨331325, by rfl⟩ : syracuseStep 441767 = 662651) B662651
theorem B703975 : Blo 291829 703975 := bstep (se 1 (by rfl) ⟨527981, by rfl⟩ : syracuseStep 703975 = 1055963) B1055963
theorem B441851 : Blo 291829 441851 := bstep (se 1 (by rfl) ⟨331388, by rfl⟩ : syracuseStep 441851 = 662777) B662777
theorem B441947 : Blo 291829 441947 := bstep (se 1 (by rfl) ⟨331460, by rfl⟩ : syracuseStep 441947 = 662921) B662921
theorem B442031 : Blo 291829 442031 := bstep (se 1 (by rfl) ⟨331523, by rfl⟩ : syracuseStep 442031 = 663047) B663047
theorem B442151 : Blo 291829 442151 := bstep (se 1 (by rfl) ⟨331613, by rfl⟩ : syracuseStep 442151 = 663227) B663227
theorem B442235 : Blo 291829 442235 := bstep (se 1 (by rfl) ⟨331676, by rfl⟩ : syracuseStep 442235 = 663353) B663353
theorem B442655 : Blo 291829 442655 := bstep (se 1 (by rfl) ⟨331991, by rfl⟩ : syracuseStep 442655 = 663983) B663983
theorem B442679 : Blo 291829 442679 := bstep (se 1 (by rfl) ⟨332009, by rfl⟩ : syracuseStep 442679 = 664019) B664019
theorem B442751 : Blo 291829 442751 := bstep (se 1 (by rfl) ⟨332063, by rfl⟩ : syracuseStep 442751 = 664127) B664127
theorem B836027 : Blo 291829 836027 := bstep (se 1 (by rfl) ⟨627020, by rfl⟩ : syracuseStep 836027 = 1254041) B1254041
theorem B442823 : Blo 291829 442823 := bstep (se 1 (by rfl) ⟨332117, by rfl⟩ : syracuseStep 442823 = 664235) B664235
theorem B443177 : Blo 291829 443177 := bstep (se 2 (by rfl) ⟨166191, by rfl⟩ : syracuseStep 443177 = 332383) B332383
theorem B443183 : Blo 291829 443183 := bstep (se 1 (by rfl) ⟨332387, by rfl⟩ : syracuseStep 443183 = 664775) B664775
theorem B443303 : Blo 291829 443303 := bstep (se 1 (by rfl) ⟨332477, by rfl⟩ : syracuseStep 443303 = 664955) B664955
theorem B443387 : Blo 291829 443387 := bstep (se 1 (by rfl) ⟨332540, by rfl⟩ : syracuseStep 443387 = 665081) B665081
theorem B443447 : Blo 291829 443447 := bstep (se 1 (by rfl) ⟨332585, by rfl⟩ : syracuseStep 443447 = 665171) B665171
theorem B443567 : Blo 291829 443567 := bstep (se 1 (by rfl) ⟨332675, by rfl⟩ : syracuseStep 443567 = 665351) B665351
theorem B1492505 : Blo 291829 1492505 := bstep (se 2 (by rfl) ⟨559689, by rfl⟩ : syracuseStep 1492505 = 1119379) B1119379
theorem B738983 : Blo 291829 738983 := bstep (se 1 (by rfl) ⟨554237, by rfl⟩ : syracuseStep 738983 = 1108475) B1108475
theorem B935687 : Blo 291829 935687 := bstep (se 1 (by rfl) ⟨701765, by rfl⟩ : syracuseStep 935687 = 1403531) B1403531
theorem B313151 : Blo 291829 313151 := bstep (se 1 (by rfl) ⟨234863, by rfl⟩ : syracuseStep 313151 = 469727) B469727
theorem B2115503 : Blo 291829 2115503 := bstep (se 1 (by rfl) ⟨1586627, by rfl⟩ : syracuseStep 2115503 = 3173255) B3173255
theorem B2508731 : Blo 291829 2508731 := bstep (se 1 (by rfl) ⟨1881548, by rfl⟩ : syracuseStep 2508731 = 3763097) B3763097
theorem B477175 : Blo 291829 477175 := bstep (se 1 (by rfl) ⟨357881, by rfl⟩ : syracuseStep 477175 = 715763) B715763
theorem B739631 : Blo 291829 739631 := bstep (se 1 (by rfl) ⟨554723, by rfl⟩ : syracuseStep 739631 = 1109447) B1109447
theorem B65095987 : Blo 291829 65095987 := bstep (se 1 (by rfl) ⟨48821990, by rfl⟩ : syracuseStep 65095987 = 97643981) B97643981
theorem B4770515 : Blo 291829 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B2018533 : Blo 291829 2018533 := bstep (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) B378475
theorem B1527229 : Blo 291829 1527229 := bstep (se 3 (by rfl) ⟨286355, by rfl⟩ : syracuseStep 1527229 = 572711) B572711
theorem B3558917 : Blo 291829 3558917 := bstep (se 4 (by rfl) ⟨333648, by rfl⟩ : syracuseStep 3558917 = 667297) B667297
theorem B740927 : Blo 291829 740927 := bstep (se 1 (by rfl) ⟨555695, by rfl⟩ : syracuseStep 740927 = 1111391) B1111391
theorem B839945 : Blo 291829 839945 := bstep (se 2 (by rfl) ⟨314979, by rfl⟩ : syracuseStep 839945 = 629959) B629959
theorem B3396167 : Blo 291829 3396167 := bstep (se 1 (by rfl) ⟨2547125, by rfl⟩ : syracuseStep 3396167 = 5094251) B5094251
theorem B840287 : Blo 291829 840287 := bstep (se 1 (by rfl) ⟨630215, by rfl⟩ : syracuseStep 840287 = 1260431) B1260431
theorem B1594241 : Blo 291829 1594241 := bstep (se 2 (by rfl) ⟨597840, by rfl⟩ : syracuseStep 1594241 = 1195681) B1195681
theorem B2413577 : Blo 291829 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B840743 : Blo 291829 840743 := bstep (se 1 (by rfl) ⟨630557, by rfl⟩ : syracuseStep 840743 = 1261115) B1261115
theorem B841529 : Blo 291829 841529 := bstep (se 2 (by rfl) ⟨315573, by rfl⟩ : syracuseStep 841529 = 631147) B631147
theorem B2840503 : Blo 291829 2840503 := bstep (se 1 (by rfl) ⟨2130377, by rfl⟩ : syracuseStep 2840503 = 4260755) B4260755
theorem B1890287 : Blo 291829 1890287 := bstep (se 1 (by rfl) ⟨1417715, by rfl⟩ : syracuseStep 1890287 = 2835431) B2835431
theorem B841711 : Blo 291829 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B743519 : Blo 291829 743519 := bstep (se 1 (by rfl) ⟨557639, by rfl⟩ : syracuseStep 743519 = 1115279) B1115279
theorem B3365063 : Blo 291829 3365063 := bstep (se 1 (by rfl) ⟨2523797, by rfl⟩ : syracuseStep 3365063 = 5047595) B5047595
theorem B841927 : Blo 291829 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B448745 : Blo 291829 448745 := bstep (se 2 (by rfl) ⟨168279, by rfl⟩ : syracuseStep 448745 = 336559) B336559
theorem B1071955 : Blo 291829 1071955 := bstep (se 1 (by rfl) ⟨803966, by rfl⟩ : syracuseStep 1071955 = 1607933) B1607933
theorem B2841581 : Blo 291829 2841581 := bstep (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) B1065593
theorem B13491521 : Blo 291829 13491521 := bstep (se 2 (by rfl) ⟨5059320, by rfl⟩ : syracuseStep 13491521 = 10118641) B10118641
theorem B744815 : Blo 291829 744815 := bstep (se 1 (by rfl) ⟨558611, by rfl⟩ : syracuseStep 744815 = 1117223) B1117223
theorem B5332385 : Blo 291829 5332385 := bstep (se 2 (by rfl) ⟨1999644, by rfl⟩ : syracuseStep 5332385 = 3999289) B3999289
theorem B4218313 : Blo 291829 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B679657 : Blo 291829 679657 := bstep (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) B509743
theorem B417575 : Blo 291829 417575 := bstep (se 1 (by rfl) ⟨313181, by rfl⟩ : syracuseStep 417575 = 626363) B626363
theorem B942119 : Blo 291829 942119 := bstep (se 1 (by rfl) ⟨706589, by rfl⟩ : syracuseStep 942119 = 1413179) B1413179
theorem B5661323 : Blo 291829 5661323 := bstep (se 1 (by rfl) ⟨4245992, by rfl⟩ : syracuseStep 5661323 = 8491985) B8491985
theorem B3367979 : Blo 291829 3367979 := bstep (se 1 (by rfl) ⟨2525984, by rfl⟩ : syracuseStep 3367979 = 5051969) B5051969
theorem B418879 : Blo 291829 418879 := bstep (se 1 (by rfl) ⟨314159, by rfl⟩ : syracuseStep 418879 = 628319) B628319
theorem B1598629 : Blo 291829 1598629 := bstep (se 4 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 1598629 = 299743) B299743
theorem B2221505 : Blo 291829 2221505 := bstep (se 2 (by rfl) ⟨833064, by rfl⟩ : syracuseStep 2221505 = 1666129) B1666129
theorem B2516417 : Blo 291829 2516417 := bstep (se 2 (by rfl) ⟨943656, by rfl⟩ : syracuseStep 2516417 = 1887313) B1887313
theorem B1697273 : Blo 291829 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B3008015 : Blo 291829 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B943913 : Blo 291829 943913 := bstep (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) B707935
theorem B419995 : Blo 291829 419995 := bstep (se 1 (by rfl) ⟨314996, by rfl⟩ : syracuseStep 419995 = 629993) B629993
theorem B421129 : Blo 291829 421129 := bstep (se 2 (by rfl) ⟨157923, by rfl⟩ : syracuseStep 421129 = 315847) B315847
theorem B1666655 : Blo 291829 1666655 := bstep (se 1 (by rfl) ⟨1249991, by rfl⟩ : syracuseStep 1666655 = 2499983) B2499983
theorem B1110145 : Blo 291829 1110145 := bstep (se 2 (by rfl) ⟨416304, by rfl⟩ : syracuseStep 1110145 = 832609) B832609
theorem B6320551 : Blo 291829 6320551 := bstep (se 1 (by rfl) ⟨4740413, by rfl⟩ : syracuseStep 6320551 = 9480827) B9480827
theorem B291835 : Blo 291829 291835 := bstep (se 1 (by rfl) ⟨218876, by rfl⟩ : syracuseStep 291835 = 437753) B437753
theorem B291903 : Blo 291829 291903 := bstep (se 1 (by rfl) ⟨218927, by rfl⟩ : syracuseStep 291903 = 437855) B437855
theorem B717887 : Blo 291829 717887 := bstep (se 1 (by rfl) ⟨538415, by rfl⟩ : syracuseStep 717887 = 1076831) B1076831
theorem B1438859 : Blo 291829 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B292047 : Blo 291829 292047 := bstep (se 1 (by rfl) ⟨219035, by rfl⟩ : syracuseStep 292047 = 438071) B438071
theorem B292251 : Blo 291829 292251 := bstep (se 1 (by rfl) ⟨219188, by rfl⟩ : syracuseStep 292251 = 438377) B438377
theorem B554465 : Blo 291829 554465 := bstep (se 2 (by rfl) ⟨207924, by rfl⟩ : syracuseStep 554465 = 415849) B415849
theorem B2815559 : Blo 291829 2815559 := bstep (se 1 (by rfl) ⟨2111669, by rfl⟩ : syracuseStep 2815559 = 4223339) B4223339
theorem B292463 : Blo 291829 292463 := bstep (se 1 (by rfl) ⟨219347, by rfl⟩ : syracuseStep 292463 = 438695) B438695
theorem B292519 : Blo 291829 292519 := bstep (se 1 (by rfl) ⟨219389, by rfl⟩ : syracuseStep 292519 = 438779) B438779
theorem B292603 : Blo 291829 292603 := bstep (se 1 (by rfl) ⟨219452, by rfl⟩ : syracuseStep 292603 = 438905) B438905
theorem B292639 : Blo 291829 292639 := bstep (se 1 (by rfl) ⟨219479, by rfl⟩ : syracuseStep 292639 = 438959) B438959
theorem B292671 : Blo 291829 292671 := bstep (se 1 (by rfl) ⟨219503, by rfl⟩ : syracuseStep 292671 = 439007) B439007
theorem B1406915 : Blo 291829 1406915 := bstep (se 1 (by rfl) ⟨1055186, by rfl⟩ : syracuseStep 1406915 = 2110373) B2110373
theorem B292847 : Blo 291829 292847 := bstep (se 1 (by rfl) ⟨219635, by rfl⟩ : syracuseStep 292847 = 439271) B439271
theorem B555103 : Blo 291829 555103 := bstep (se 1 (by rfl) ⟨416327, by rfl⟩ : syracuseStep 555103 = 832655) B832655
theorem B293019 : Blo 291829 293019 := bstep (se 1 (by rfl) ⟨219764, by rfl⟩ : syracuseStep 293019 = 439529) B439529
theorem B293055 : Blo 291829 293055 := bstep (se 1 (by rfl) ⟨219791, by rfl⟩ : syracuseStep 293055 = 439583) B439583
theorem B1112363 : Blo 291829 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B293167 : Blo 291829 293167 := bstep (se 1 (by rfl) ⟨219875, by rfl⟩ : syracuseStep 293167 = 439751) B439751
theorem B1112393 : Blo 291829 1112393 := bstep (se 2 (by rfl) ⟨417147, by rfl⟩ : syracuseStep 1112393 = 834295) B834295
theorem B293403 : Blo 291829 293403 := bstep (se 1 (by rfl) ⟨220052, by rfl⟩ : syracuseStep 293403 = 440105) B440105
theorem B293407 : Blo 291829 293407 := bstep (se 1 (by rfl) ⟨220055, by rfl⟩ : syracuseStep 293407 = 440111) B440111
theorem B293723 : Blo 291829 293723 := bstep (se 1 (by rfl) ⟨220292, by rfl⟩ : syracuseStep 293723 = 440585) B440585
theorem B293791 : Blo 291829 293791 := bstep (se 1 (by rfl) ⟨220343, by rfl⟩ : syracuseStep 293791 = 440687) B440687
theorem B2816977 : Blo 291829 2816977 := bstep (se 2 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 2816977 = 2112733) B2112733
theorem B293935 : Blo 291829 293935 := bstep (se 1 (by rfl) ⟨220451, by rfl⟩ : syracuseStep 293935 = 440903) B440903
theorem B293959 : Blo 291829 293959 := bstep (se 1 (by rfl) ⟨220469, by rfl⟩ : syracuseStep 293959 = 440939) B440939
theorem B294111 : Blo 291829 294111 := bstep (se 1 (by rfl) ⟨220583, by rfl⟩ : syracuseStep 294111 = 441167) B441167
theorem B3341735 : Blo 291829 3341735 := bstep (se 1 (by rfl) ⟨2506301, by rfl⟩ : syracuseStep 3341735 = 5012603) B5012603
theorem B294375 : Blo 291829 294375 := bstep (se 1 (by rfl) ⟨220781, by rfl⟩ : syracuseStep 294375 = 441563) B441563
theorem B294491 : Blo 291829 294491 := bstep (se 1 (by rfl) ⟨220868, by rfl⟩ : syracuseStep 294491 = 441737) B441737
theorem B294727 : Blo 291829 294727 := bstep (se 1 (by rfl) ⟨221045, by rfl⟩ : syracuseStep 294727 = 442091) B442091
theorem B40468403 : Blo 291829 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B294879 : Blo 291829 294879 := bstep (se 1 (by rfl) ⟨221159, by rfl⟩ : syracuseStep 294879 = 442319) B442319
theorem B295103 : Blo 291829 295103 := bstep (se 1 (by rfl) ⟨221327, by rfl⟩ : syracuseStep 295103 = 442655) B442655
theorem B295119 : Blo 291829 295119 := bstep (se 1 (by rfl) ⟨221339, by rfl⟩ : syracuseStep 295119 = 442679) B442679
theorem B295167 : Blo 291829 295167 := bstep (se 1 (by rfl) ⟨221375, by rfl⟩ : syracuseStep 295167 = 442751) B442751
theorem B557351 : Blo 291829 557351 := bstep (se 1 (by rfl) ⟨418013, by rfl⟩ : syracuseStep 557351 = 836027) B836027
theorem B295215 : Blo 291829 295215 := bstep (se 1 (by rfl) ⟨221411, by rfl⟩ : syracuseStep 295215 = 442823) B442823
theorem B295451 : Blo 291829 295451 := bstep (se 1 (by rfl) ⟨221588, by rfl⟩ : syracuseStep 295451 = 443177) B443177
theorem B295455 : Blo 291829 295455 := bstep (se 1 (by rfl) ⟨221591, by rfl⟩ : syracuseStep 295455 = 443183) B443183
theorem B295535 : Blo 291829 295535 := bstep (se 1 (by rfl) ⟨221651, by rfl⟩ : syracuseStep 295535 = 443303) B443303
theorem B295591 : Blo 291829 295591 := bstep (se 1 (by rfl) ⟨221693, by rfl⟩ : syracuseStep 295591 = 443387) B443387
theorem B295631 : Blo 291829 295631 := bstep (se 1 (by rfl) ⟨221723, by rfl⟩ : syracuseStep 295631 = 443447) B443447
theorem B295711 : Blo 291829 295711 := bstep (se 1 (by rfl) ⟨221783, by rfl⟩ : syracuseStep 295711 = 443567) B443567
theorem B492655 : Blo 291829 492655 := bstep (se 1 (by rfl) ⟨369491, by rfl⟩ : syracuseStep 492655 = 738983) B738983
theorem B623791 : Blo 291829 623791 := bstep (se 1 (by rfl) ⟨467843, by rfl⟩ : syracuseStep 623791 = 935687) B935687
theorem B328927 : Blo 291829 328927 := bstep (se 1 (by rfl) ⟨246695, by rfl⟩ : syracuseStep 328927 = 493391) B493391
theorem B1410335 : Blo 291829 1410335 := bstep (se 1 (by rfl) ⟨1057751, by rfl⟩ : syracuseStep 1410335 = 2115503) B2115503
theorem B1672487 : Blo 291829 1672487 := bstep (se 1 (by rfl) ⟨1254365, by rfl⟩ : syracuseStep 1672487 = 2508731) B2508731
theorem B558505 : Blo 291829 558505 := bstep (se 2 (by rfl) ⟨209439, by rfl⟩ : syracuseStep 558505 = 418879) B418879
theorem B656891 : Blo 291829 656891 := bstep (se 1 (by rfl) ⟨492668, by rfl⟩ : syracuseStep 656891 = 985337) B985337
theorem B2229767 : Blo 291829 2229767 := bstep (se 1 (by rfl) ⟨1672325, by rfl⟩ : syracuseStep 2229767 = 3344651) B3344651
theorem B656927 : Blo 291829 656927 := bstep (se 1 (by rfl) ⟨492695, by rfl⟩ : syracuseStep 656927 = 985391) B985391
theorem B493087 : Blo 291829 493087 := bstep (se 1 (by rfl) ⟨369815, by rfl⟩ : syracuseStep 493087 = 739631) B739631
theorem B2131505 : Blo 291829 2131505 := bstep (se 2 (by rfl) ⟨799314, by rfl⟩ : syracuseStep 2131505 = 1598629) B1598629
theorem B657071 : Blo 291829 657071 := bstep (se 1 (by rfl) ⟨492803, by rfl⟩ : syracuseStep 657071 = 985607) B985607
theorem B3180343 : Blo 291829 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B329755 : Blo 291829 329755 := bstep (se 1 (by rfl) ⟨247316, by rfl⟩ : syracuseStep 329755 = 494633) B494633
theorem B526367 : Blo 291829 526367 := bstep (se 1 (by rfl) ⟨394775, by rfl⟩ : syracuseStep 526367 = 789551) B789551
theorem B657503 : Blo 291829 657503 := bstep (se 1 (by rfl) ⟨493127, by rfl⟩ : syracuseStep 657503 = 986255) B986255
theorem B1411181 : Blo 291829 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B657791 : Blo 291829 657791 := bstep (se 1 (by rfl) ⟨493343, by rfl⟩ : syracuseStep 657791 = 986687) B986687
theorem B493951 : Blo 291829 493951 := bstep (se 1 (by rfl) ⟨370463, by rfl⟩ : syracuseStep 493951 = 740927) B740927
theorem B4786613 : Blo 291829 4786613 := bstep (se 5 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 4786613 = 448745) B448745
theorem B8129011 : Blo 291829 8129011 := bstep (se 1 (by rfl) ⟨6096758, by rfl⟩ : syracuseStep 8129011 = 12193517) B12193517
theorem B1116767 : Blo 291829 1116767 := bstep (se 1 (by rfl) ⟨837575, by rfl⟩ : syracuseStep 1116767 = 1675151) B1675151
theorem B658259 : Blo 291829 658259 := bstep (se 1 (by rfl) ⟨493694, by rfl⟩ : syracuseStep 658259 = 987389) B987389
theorem B559963 : Blo 291829 559963 := bstep (se 1 (by rfl) ⟨419972, by rfl⟩ : syracuseStep 559963 = 839945) B839945
theorem B2264111 : Blo 291829 2264111 := bstep (se 1 (by rfl) ⟨1698083, by rfl⟩ : syracuseStep 2264111 = 3396167) B3396167
theorem B560191 : Blo 291829 560191 := bstep (se 1 (by rfl) ⟨420143, by rfl⟩ : syracuseStep 560191 = 840287) B840287
theorem B658619 : Blo 291829 658619 := bstep (se 1 (by rfl) ⟨493964, by rfl⟩ : syracuseStep 658619 = 987929) B987929
theorem B658799 : Blo 291829 658799 := bstep (se 1 (by rfl) ⟨494099, by rfl⟩ : syracuseStep 658799 = 988199) B988199
theorem B560495 : Blo 291829 560495 := bstep (se 1 (by rfl) ⟨420371, by rfl⟩ : syracuseStep 560495 = 840743) B840743
theorem B331231 : Blo 291829 331231 := bstep (se 1 (by rfl) ⟨248423, by rfl⟩ : syracuseStep 331231 = 496847) B496847
theorem B561019 : Blo 291829 561019 := bstep (se 1 (by rfl) ⟨420764, by rfl⟩ : syracuseStep 561019 = 841529) B841529
theorem B1478573 : Blo 291829 1478573 := bstep (se 3 (by rfl) ⟨277232, by rfl⟩ : syracuseStep 1478573 = 554465) B554465
theorem B987119 : Blo 291829 987119 := bstep (se 1 (by rfl) ⟨740339, by rfl⟩ : syracuseStep 987119 = 1480679) B1480679
theorem B331771 : Blo 291829 331771 := bstep (se 1 (by rfl) ⟨248828, by rfl⟩ : syracuseStep 331771 = 497657) B497657
theorem B659519 : Blo 291829 659519 := bstep (se 1 (by rfl) ⟨494639, by rfl⟩ : syracuseStep 659519 = 989279) B989279
theorem B495679 : Blo 291829 495679 := bstep (se 1 (by rfl) ⟨371759, by rfl⟩ : syracuseStep 495679 = 743519) B743519
theorem B331879 : Blo 291829 331879 := bstep (se 1 (by rfl) ⟨248909, by rfl⟩ : syracuseStep 331879 = 497819) B497819
theorem B4427929 : Blo 291829 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B331951 : Blo 291829 331951 := bstep (se 1 (by rfl) ⟨248963, by rfl⟩ : syracuseStep 331951 = 497927) B497927
theorem B659753 : Blo 291829 659753 := bstep (se 2 (by rfl) ⟨247407, by rfl⟩ : syracuseStep 659753 = 494815) B494815
theorem B2691377 : Blo 291829 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B561505 : Blo 291829 561505 := bstep (se 2 (by rfl) ⟨210564, by rfl⟩ : syracuseStep 561505 = 421129) B421129
theorem B660023 : Blo 291829 660023 := bstep (se 1 (by rfl) ⟨495017, by rfl⟩ : syracuseStep 660023 = 990035) B990035
theorem B2036305 : Blo 291829 2036305 := bstep (se 2 (by rfl) ⟨763614, by rfl⟩ : syracuseStep 2036305 = 1527229) B1527229
theorem B332635 : Blo 291829 332635 := bstep (se 1 (by rfl) ⟨249476, by rfl⟩ : syracuseStep 332635 = 498953) B498953
theorem B660329 : Blo 291829 660329 := bstep (se 2 (by rfl) ⟨247623, by rfl⟩ : syracuseStep 660329 = 495247) B495247
theorem B660383 : Blo 291829 660383 := bstep (se 1 (by rfl) ⟨495287, by rfl⟩ : syracuseStep 660383 = 990575) B990575
theorem B496543 : Blo 291829 496543 := bstep (se 1 (by rfl) ⟨372407, by rfl⟩ : syracuseStep 496543 = 744815) B744815
theorem B660635 : Blo 291829 660635 := bstep (se 1 (by rfl) ⟨495476, by rfl⟩ : syracuseStep 660635 = 990953) B990953
theorem B628079 : Blo 291829 628079 := bstep (se 1 (by rfl) ⟨471059, by rfl⟩ : syracuseStep 628079 = 942119) B942119
theorem B1480193 : Blo 291829 1480193 := bstep (se 2 (by rfl) ⟨555072, by rfl⟩ : syracuseStep 1480193 = 1110145) B1110145
theorem B661211 : Blo 291829 661211 := bstep (se 1 (by rfl) ⟨495908, by rfl⟩ : syracuseStep 661211 = 991817) B991817
theorem B3774215 : Blo 291829 3774215 := bstep (se 1 (by rfl) ⟨2830661, by rfl⟩ : syracuseStep 3774215 = 5661323) B5661323
theorem B661319 : Blo 291829 661319 := bstep (se 1 (by rfl) ⟨495989, by rfl⟩ : syracuseStep 661319 = 991979) B991979
theorem B8427401 : Blo 291829 8427401 := bstep (se 2 (by rfl) ⟨3160275, by rfl⟩ : syracuseStep 8427401 = 6320551) B6320551
theorem B1677611 : Blo 291829 1677611 := bstep (se 1 (by rfl) ⟨1258208, by rfl⟩ : syracuseStep 1677611 = 2516417) B2516417
theorem B1481003 : Blo 291829 1481003 := bstep (se 1 (by rfl) ⟨1110752, by rfl⟩ : syracuseStep 1481003 = 2221505) B2221505
theorem B2005343 : Blo 291829 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B662327 : Blo 291829 662327 := bstep (se 1 (by rfl) ⟨496745, by rfl⟩ : syracuseStep 662327 = 993491) B993491
theorem B1022777 : Blo 291829 1022777 := bstep (se 2 (by rfl) ⟨383541, by rfl⟩ : syracuseStep 1022777 = 767083) B767083
theorem B662507 : Blo 291829 662507 := bstep (se 1 (by rfl) ⟨496880, by rfl⟩ : syracuseStep 662507 = 993761) B993761
theorem B1253083 : Blo 291829 1253083 := bstep (se 1 (by rfl) ⟨939812, by rfl⟩ : syracuseStep 1253083 = 1879625) B1879625
theorem B663407 : Blo 291829 663407 := bstep (se 1 (by rfl) ⟨497555, by rfl⟩ : syracuseStep 663407 = 995111) B995111
theorem B1122281 : Blo 291829 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B991223 : Blo 291829 991223 := bstep (se 1 (by rfl) ⟨743417, by rfl⟩ : syracuseStep 991223 = 1486835) B1486835
theorem B1122295 : Blo 291829 1122295 := bstep (se 1 (by rfl) ⟨841721, by rfl⟩ : syracuseStep 1122295 = 1683443) B1683443
theorem B10887211 : Blo 291829 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B991439 : Blo 291829 991439 := bstep (se 1 (by rfl) ⟨743579, by rfl⟩ : syracuseStep 991439 = 1487159) B1487159
theorem B1122569 : Blo 291829 1122569 := bstep (se 2 (by rfl) ⟨420963, by rfl⟩ : syracuseStep 1122569 = 841927) B841927
theorem B2498921 : Blo 291829 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B664091 : Blo 291829 664091 := bstep (se 1 (by rfl) ⟨498068, by rfl⟩ : syracuseStep 664091 = 996137) B996137
theorem B1253971 : Blo 291829 1253971 := bstep (se 1 (by rfl) ⟨940478, by rfl⟩ : syracuseStep 1253971 = 1880957) B1880957
theorem B664271 : Blo 291829 664271 := bstep (se 1 (by rfl) ⟨498203, by rfl⟩ : syracuseStep 664271 = 996407) B996407
theorem B959239 : Blo 291829 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B1877039 : Blo 291829 1877039 := bstep (se 1 (by rfl) ⟨1407779, by rfl⟩ : syracuseStep 1877039 = 2815559) B2815559
theorem B992303 : Blo 291829 992303 := bstep (se 1 (by rfl) ⟨744227, by rfl⟩ : syracuseStep 992303 = 1488455) B1488455
theorem B664649 : Blo 291829 664649 := bstep (se 2 (by rfl) ⟨249243, by rfl⟩ : syracuseStep 664649 = 498487) B498487
theorem B992951 : Blo 291829 992951 := bstep (se 1 (by rfl) ⟨744713, by rfl⟩ : syracuseStep 992951 = 1489427) B1489427
theorem B665567 : Blo 291829 665567 := bstep (se 1 (by rfl) ⟨499175, by rfl⟩ : syracuseStep 665567 = 998351) B998351
theorem B2238515 : Blo 291829 2238515 := bstep (se 1 (by rfl) ⟨1678886, by rfl⟩ : syracuseStep 2238515 = 3357773) B3357773
theorem B26978935 : Blo 291829 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B2239973 : Blo 291829 2239973 := bstep (se 4 (by rfl) ⟨209997, by rfl⟩ : syracuseStep 2239973 = 419995) B419995
theorem B437831 : Blo 291829 437831 := bstep (se 1 (by rfl) ⟨328373, by rfl⟩ : syracuseStep 437831 = 656747) B656747
theorem B995003 : Blo 291829 995003 := bstep (se 1 (by rfl) ⟨746252, by rfl⟩ : syracuseStep 995003 = 1492505) B1492505
theorem B438011 : Blo 291829 438011 := bstep (se 1 (by rfl) ⟨328508, by rfl⟩ : syracuseStep 438011 = 657017) B657017
theorem B372863 : Blo 291829 372863 := bstep (se 1 (by rfl) ⟨279647, by rfl⟩ : syracuseStep 372863 = 559295) B559295
theorem B16888013 : Blo 291829 16888013 := bstep (se 3 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 16888013 = 6333005) B6333005
theorem B438683 : Blo 291829 438683 := bstep (se 1 (by rfl) ⟨329012, by rfl⟩ : syracuseStep 438683 = 658025) B658025
theorem B3584459 : Blo 291829 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B1192745 : Blo 291829 1192745 := bstep (se 2 (by rfl) ⟨447279, by rfl⟩ : syracuseStep 1192745 = 894559) B894559
theorem B439103 : Blo 291829 439103 := bstep (se 1 (by rfl) ⟨329327, by rfl⟩ : syracuseStep 439103 = 658655) B658655
theorem B373567 : Blo 291829 373567 := bstep (se 1 (by rfl) ⟨280175, by rfl⟩ : syracuseStep 373567 = 560351) B560351
theorem B439247 : Blo 291829 439247 := bstep (se 1 (by rfl) ⟨329435, by rfl⟩ : syracuseStep 439247 = 658871) B658871
theorem B439289 : Blo 291829 439289 := bstep (se 2 (by rfl) ⟨164733, by rfl⟩ : syracuseStep 439289 = 329467) B329467
theorem B668665 : Blo 291829 668665 := bstep (se 2 (by rfl) ⟨250749, by rfl⟩ : syracuseStep 668665 = 501499) B501499
theorem B2372611 : Blo 291829 2372611 := bstep (se 1 (by rfl) ⟨1779458, by rfl⟩ : syracuseStep 2372611 = 3558917) B3558917
theorem B439337 : Blo 291829 439337 := bstep (se 2 (by rfl) ⟨164751, by rfl⟩ : syracuseStep 439337 = 329503) B329503
theorem B439367 : Blo 291829 439367 := bstep (se 1 (by rfl) ⟨329525, by rfl⟩ : syracuseStep 439367 = 659051) B659051
theorem B439547 : Blo 291829 439547 := bstep (se 1 (by rfl) ⟨329660, by rfl⟩ : syracuseStep 439547 = 659321) B659321
theorem B636233 : Blo 291829 636233 := bstep (se 2 (by rfl) ⟨238587, by rfl⟩ : syracuseStep 636233 = 477175) B477175
theorem B6436205 : Blo 291829 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B1488617 : Blo 291829 1488617 := bstep (se 2 (by rfl) ⟨558231, by rfl⟩ : syracuseStep 1488617 = 1116463) B1116463
theorem B1062827 : Blo 291829 1062827 := bstep (se 1 (by rfl) ⟨797120, by rfl⟩ : syracuseStep 1062827 = 1594241) B1594241
theorem B440783 : Blo 291829 440783 := bstep (se 1 (by rfl) ⟨330587, by rfl⟩ : syracuseStep 440783 = 661175) B661175
theorem B1227271 : Blo 291829 1227271 := bstep (se 1 (by rfl) ⟨920453, by rfl⟩ : syracuseStep 1227271 = 1840907) B1840907
theorem B440873 : Blo 291829 440873 := bstep (se 2 (by rfl) ⟨165327, by rfl⟩ : syracuseStep 440873 = 330655) B330655
theorem B1260191 : Blo 291829 1260191 := bstep (se 1 (by rfl) ⟨945143, by rfl⟩ : syracuseStep 1260191 = 1890287) B1890287
theorem B441065 : Blo 291829 441065 := bstep (se 2 (by rfl) ⟨165399, by rfl⟩ : syracuseStep 441065 = 330799) B330799
theorem B2243375 : Blo 291829 2243375 := bstep (se 1 (by rfl) ⟨1682531, by rfl⟩ : syracuseStep 2243375 = 3365063) B3365063
theorem B441449 : Blo 291829 441449 := bstep (se 2 (by rfl) ⟨165543, by rfl⟩ : syracuseStep 441449 = 331087) B331087
theorem B441575 : Blo 291829 441575 := bstep (se 1 (by rfl) ⟨331181, by rfl⟩ : syracuseStep 441575 = 662363) B662363
theorem B1621235 : Blo 291829 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B8994347 : Blo 291829 8994347 := bstep (se 1 (by rfl) ⟨6745760, by rfl⟩ : syracuseStep 8994347 = 13491521) B13491521
theorem B3554923 : Blo 291829 3554923 := bstep (se 1 (by rfl) ⟨2666192, by rfl⟩ : syracuseStep 3554923 = 5332385) B5332385
theorem B442079 : Blo 291829 442079 := bstep (se 1 (by rfl) ⟨331559, by rfl⟩ : syracuseStep 442079 = 663119) B663119
theorem B442121 : Blo 291829 442121 := bstep (se 2 (by rfl) ⟨165795, by rfl⟩ : syracuseStep 442121 = 331591) B331591
theorem B442559 : Blo 291829 442559 := bstep (se 1 (by rfl) ⟨331919, by rfl⟩ : syracuseStep 442559 = 663839) B663839
theorem B835879 : Blo 291829 835879 := bstep (se 1 (by rfl) ⟨626909, by rfl⟩ : syracuseStep 835879 = 1253819) B1253819
theorem B442985 : Blo 291829 442985 := bstep (se 2 (by rfl) ⟨166119, by rfl⟩ : syracuseStep 442985 = 332239) B332239
theorem B442991 : Blo 291829 442991 := bstep (se 1 (by rfl) ⟨332243, by rfl⟩ : syracuseStep 442991 = 664487) B664487
theorem B2245319 : Blo 291829 2245319 := bstep (se 1 (by rfl) ⟨1683989, by rfl⟩ : syracuseStep 2245319 = 3367979) B3367979
theorem B2868047 : Blo 291829 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B1131515 : Blo 291829 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B443615 : Blo 291829 443615 := bstep (se 1 (by rfl) ⟨332711, by rfl⟩ : syracuseStep 443615 = 665423) B665423
theorem B443627 : Blo 291829 443627 := bstep (se 1 (by rfl) ⟨332720, by rfl⟩ : syracuseStep 443627 = 665441) B665441
theorem B313903 : Blo 291829 313903 := bstep (se 1 (by rfl) ⟨235427, by rfl⟩ : syracuseStep 313903 = 470855) B470855
theorem B3787337 : Blo 291829 3787337 := bstep (se 2 (by rfl) ⟨1420251, by rfl⟩ : syracuseStep 3787337 = 2840503) B2840503
theorem B740137 : Blo 291829 740137 := bstep (se 2 (by rfl) ⟨277551, by rfl⟩ : syracuseStep 740137 = 555103) B555103
theorem B838441 : Blo 291829 838441 := bstep (se 2 (by rfl) ⟨314415, by rfl⟩ : syracuseStep 838441 = 628831) B628831
theorem B1493801 : Blo 291829 1493801 := bstep (se 2 (by rfl) ⟨560175, by rfl⟩ : syracuseStep 1493801 = 1120351) B1120351
theorem B478591 : Blo 291829 478591 := bstep (se 1 (by rfl) ⟨358943, by rfl⟩ : syracuseStep 478591 = 717887) B717887
theorem B1429273 : Blo 291829 1429273 := bstep (se 2 (by rfl) ⟨535977, by rfl⟩ : syracuseStep 1429273 = 1071955) B1071955
theorem B3755969 : Blo 291829 3755969 := bstep (se 2 (by rfl) ⟨1408488, by rfl⟩ : syracuseStep 3755969 = 2816977) B2816977
theorem B937943 : Blo 291829 937943 := bstep (se 1 (by rfl) ⟨703457, by rfl⟩ : syracuseStep 937943 = 1406915) B1406915
theorem B11980781 : Blo 291829 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B708763 : Blo 291829 708763 := bstep (se 1 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 708763 = 1063145) B1063145
theorem B741575 : Blo 291829 741575 := bstep (se 1 (by rfl) ⟨556181, by rfl⟩ : syracuseStep 741575 = 1112363) B1112363
theorem B741595 : Blo 291829 741595 := bstep (se 1 (by rfl) ⟨556196, by rfl⟩ : syracuseStep 741595 = 1112393) B1112393
theorem B839899 : Blo 291829 839899 := bstep (se 1 (by rfl) ⟨629924, by rfl⟩ : syracuseStep 839899 = 1259849) B1259849
theorem B1495259 : Blo 291829 1495259 := bstep (se 1 (by rfl) ⟨1121444, by rfl⟩ : syracuseStep 1495259 = 2242889) B2242889
theorem B446843 : Blo 291829 446843 := bstep (se 1 (by rfl) ⟨335132, by rfl⟩ : syracuseStep 446843 = 670265) B670265
theorem B5034473 : Blo 291829 5034473 := bstep (se 2 (by rfl) ⟨1887927, by rfl⟩ : syracuseStep 5034473 = 3775855) B3775855
theorem B5624417 : Blo 291829 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B938633 : Blo 291829 938633 := bstep (se 2 (by rfl) ⟨351987, by rfl⟩ : syracuseStep 938633 = 703975) B703975
theorem B906209 : Blo 291829 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B447785 : Blo 291829 447785 := bstep (se 2 (by rfl) ⟨167919, by rfl⟩ : syracuseStep 447785 = 335839) B335839
theorem B743033 : Blo 291829 743033 := bstep (se 2 (by rfl) ⟨278637, by rfl⟩ : syracuseStep 743033 = 557275) B557275
theorem B415963 : Blo 291829 415963 := bstep (se 1 (by rfl) ⟨311972, by rfl⟩ : syracuseStep 415963 = 623945) B623945
theorem B1005983 : Blo 291829 1005983 := bstep (se 1 (by rfl) ⟨754487, by rfl⟩ : syracuseStep 1005983 = 1508975) B1508975
theorem B351911 : Blo 291829 351911 := bstep (se 1 (by rfl) ⟨263933, by rfl⟩ : syracuseStep 351911 = 527867) B527867
theorem B2121383 : Blo 291829 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B745595 : Blo 291829 745595 := bstep (se 1 (by rfl) ⟨559196, by rfl⟩ : syracuseStep 745595 = 1118393) B1118393
theorem B5333273 : Blo 291829 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B86794649 : Blo 291829 86794649 := bstep (se 2 (by rfl) ⟨32547993, by rfl⟩ : syracuseStep 86794649 = 65095987) B65095987
theorem B352987 : Blo 291829 352987 := bstep (se 1 (by rfl) ⟨264740, by rfl⟩ : syracuseStep 352987 = 529481) B529481
theorem B1336823 : Blo 291829 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B353983 : Blo 291829 353983 := bstep (se 1 (by rfl) ⟨265487, by rfl⟩ : syracuseStep 353983 = 530975) B530975
theorem B1402859 : Blo 291829 1402859 := bstep (se 1 (by rfl) ⟨1052144, by rfl⟩ : syracuseStep 1402859 = 2104289) B2104289
theorem B1894387 : Blo 291829 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B2517101 : Blo 291829 2517101 := bstep (se 3 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 2517101 = 943913) B943913
theorem B1108201 : Blo 291829 1108201 := bstep (se 2 (by rfl) ⟨415575, by rfl⟩ : syracuseStep 1108201 = 831151) B831151
theorem B1403183 : Blo 291829 1403183 := bstep (se 1 (by rfl) ⟨1052387, by rfl⟩ : syracuseStep 1403183 = 2104775) B2104775
theorem B747913 : Blo 291829 747913 := bstep (se 2 (by rfl) ⟨280467, by rfl⟩ : syracuseStep 747913 = 560935) B560935
theorem B1403993 : Blo 291829 1403993 := bstep (se 2 (by rfl) ⟨526497, by rfl⟩ : syracuseStep 1403993 = 1052995) B1052995
theorem B4615639 : Blo 291829 4615639 := bstep (se 1 (by rfl) ⟨3461729, by rfl⟩ : syracuseStep 4615639 = 6923459) B6923459
theorem B8090533 : Blo 291829 8090533 := bstep (se 4 (by rfl) ⟨758487, by rfl⟩ : syracuseStep 8090533 = 1516975) B1516975
theorem B1111103 : Blo 291829 1111103 := bstep (se 1 (by rfl) ⟨833327, by rfl⟩ : syracuseStep 1111103 = 1666655) B1666655
theorem B291911 : Blo 291829 291911 := bstep (se 1 (by rfl) ⟨218933, by rfl⟩ : syracuseStep 291911 = 437867) B437867
theorem B291995 : Blo 291829 291995 := bstep (se 1 (by rfl) ⟨218996, by rfl⟩ : syracuseStep 291995 = 437993) B437993
theorem B292091 : Blo 291829 292091 := bstep (se 1 (by rfl) ⟨219068, by rfl⟩ : syracuseStep 292091 = 438137) B438137
theorem B292159 : Blo 291829 292159 := bstep (se 1 (by rfl) ⟨219119, by rfl⟩ : syracuseStep 292159 = 438239) B438239
theorem B292327 : Blo 291829 292327 := bstep (se 1 (by rfl) ⟨219245, by rfl⟩ : syracuseStep 292327 = 438491) B438491
theorem B292335 : Blo 291829 292335 := bstep (se 1 (by rfl) ⟨219251, by rfl⟩ : syracuseStep 292335 = 438503) B438503
theorem B292443 : Blo 291829 292443 := bstep (se 1 (by rfl) ⟨219332, by rfl⟩ : syracuseStep 292443 = 438665) B438665
theorem B292507 : Blo 291829 292507 := bstep (se 1 (by rfl) ⟨219380, by rfl⟩ : syracuseStep 292507 = 438761) B438761
theorem B292591 : Blo 291829 292591 := bstep (se 1 (by rfl) ⟨219443, by rfl⟩ : syracuseStep 292591 = 438887) B438887
theorem B292679 : Blo 291829 292679 := bstep (se 1 (by rfl) ⟨219509, by rfl⟩ : syracuseStep 292679 = 439019) B439019
theorem B292699 : Blo 291829 292699 := bstep (se 1 (by rfl) ⟨219524, by rfl⟩ : syracuseStep 292699 = 439049) B439049
theorem B292767 : Blo 291829 292767 := bstep (se 1 (by rfl) ⟨219575, by rfl⟩ : syracuseStep 292767 = 439151) B439151
theorem B554951 : Blo 291829 554951 := bstep (se 1 (by rfl) ⟨416213, by rfl⟩ : syracuseStep 554951 = 832427) B832427
theorem B2127815 : Blo 291829 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B3340277 : Blo 291829 3340277 := bstep (se 5 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 3340277 = 313151) B313151
theorem B1112089 : Blo 291829 1112089 := bstep (se 2 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 1112089 = 834067) B834067
theorem B292935 : Blo 291829 292935 := bstep (se 1 (by rfl) ⟨219701, by rfl⟩ : syracuseStep 292935 = 439403) B439403
theorem B293095 : Blo 291829 293095 := bstep (se 1 (by rfl) ⟨219821, by rfl⟩ : syracuseStep 293095 = 439643) B439643
theorem B293279 : Blo 291829 293279 := bstep (se 1 (by rfl) ⟨219959, by rfl⟩ : syracuseStep 293279 = 439919) B439919
theorem B1669571 : Blo 291829 1669571 := bstep (se 1 (by rfl) ⟨1252178, by rfl⟩ : syracuseStep 1669571 = 2504357) B2504357
theorem B293327 : Blo 291829 293327 := bstep (se 1 (by rfl) ⟨219995, by rfl⟩ : syracuseStep 293327 = 439991) B439991
theorem B293351 : Blo 291829 293351 := bstep (se 1 (by rfl) ⟨220013, by rfl⟩ : syracuseStep 293351 = 440027) B440027
theorem B293467 : Blo 291829 293467 := bstep (se 1 (by rfl) ⟨220100, by rfl⟩ : syracuseStep 293467 = 440201) B440201
theorem B293535 : Blo 291829 293535 := bstep (se 1 (by rfl) ⟨220151, by rfl⟩ : syracuseStep 293535 = 440303) B440303
theorem B293703 : Blo 291829 293703 := bstep (se 1 (by rfl) ⟨220277, by rfl⟩ : syracuseStep 293703 = 440555) B440555
theorem B1342295 : Blo 291829 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B293743 : Blo 291829 293743 := bstep (se 1 (by rfl) ⟨220307, by rfl⟩ : syracuseStep 293743 = 440615) B440615
theorem B293799 : Blo 291829 293799 := bstep (se 1 (by rfl) ⟨220349, by rfl⟩ : syracuseStep 293799 = 440699) B440699
theorem B293979 : Blo 291829 293979 := bstep (se 1 (by rfl) ⟨220484, by rfl⟩ : syracuseStep 293979 = 440969) B440969
theorem B294095 : Blo 291829 294095 := bstep (se 1 (by rfl) ⟨220571, by rfl⟩ : syracuseStep 294095 = 441143) B441143
theorem B294119 : Blo 291829 294119 := bstep (se 1 (by rfl) ⟨220589, by rfl⟩ : syracuseStep 294119 = 441179) B441179
theorem B294215 : Blo 291829 294215 := bstep (se 1 (by rfl) ⟨220661, by rfl⟩ : syracuseStep 294215 = 441323) B441323
theorem B2522501 : Blo 291829 2522501 := bstep (se 4 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 2522501 = 472969) B472969
theorem B1113533 : Blo 291829 1113533 := bstep (se 3 (by rfl) ⟨208787, by rfl⟩ : syracuseStep 1113533 = 417575) B417575
theorem B2129341 : Blo 291829 2129341 := bstep (se 3 (by rfl) ⟨399251, by rfl⟩ : syracuseStep 2129341 = 798503) B798503
theorem B294351 : Blo 291829 294351 := bstep (se 1 (by rfl) ⟨220763, by rfl⟩ : syracuseStep 294351 = 441527) B441527
theorem B556607 : Blo 291829 556607 := bstep (se 1 (by rfl) ⟨417455, by rfl⟩ : syracuseStep 556607 = 834911) B834911
theorem B2227823 : Blo 291829 2227823 := bstep (se 1 (by rfl) ⟨1670867, by rfl⟩ : syracuseStep 2227823 = 3341735) B3341735
theorem B294511 : Blo 291829 294511 := bstep (se 1 (by rfl) ⟨220883, by rfl⟩ : syracuseStep 294511 = 441767) B441767
theorem B294567 : Blo 291829 294567 := bstep (se 1 (by rfl) ⟨220925, by rfl⟩ : syracuseStep 294567 = 441851) B441851
theorem B294631 : Blo 291829 294631 := bstep (se 1 (by rfl) ⟨220973, by rfl⟩ : syracuseStep 294631 = 441947) B441947
theorem B294687 : Blo 291829 294687 := bstep (se 1 (by rfl) ⟨221015, by rfl⟩ : syracuseStep 294687 = 442031) B442031
theorem B294767 : Blo 291829 294767 := bstep (se 1 (by rfl) ⟨221075, by rfl⟩ : syracuseStep 294767 = 442151) B442151
theorem B294823 : Blo 291829 294823 := bstep (se 1 (by rfl) ⟨221117, by rfl⟩ : syracuseStep 294823 = 442235) B442235
theorem B14516281 : Blo 291829 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B295039 : Blo 291829 295039 := bstep (se 1 (by rfl) ⟨221279, by rfl⟩ : syracuseStep 295039 = 442559) B442559
theorem B1114505 : Blo 291829 1114505 := bstep (se 2 (by rfl) ⟨417939, by rfl⟩ : syracuseStep 1114505 = 835879) B835879
theorem B295323 : Blo 291829 295323 := bstep (se 1 (by rfl) ⟨221492, by rfl⟩ : syracuseStep 295323 = 442985) B442985
theorem B295327 : Blo 291829 295327 := bstep (se 1 (by rfl) ⟨221495, by rfl⟩ : syracuseStep 295327 = 442991) B442991
theorem B754343 : Blo 291829 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B1671961 : Blo 291829 1671961 := bstep (se 2 (by rfl) ⟨626985, by rfl⟩ : syracuseStep 1671961 = 1253971) B1253971
theorem B295743 : Blo 291829 295743 := bstep (se 1 (by rfl) ⟨221807, by rfl⟩ : syracuseStep 295743 = 443615) B443615
theorem B295751 : Blo 291829 295751 := bstep (se 1 (by rfl) ⟨221813, by rfl⟩ : syracuseStep 295751 = 443627) B443627
theorem B1114991 : Blo 291829 1114991 := bstep (se 1 (by rfl) ⟨836243, by rfl⟩ : syracuseStep 1114991 = 1672487) B1672487
theorem B1278985 : Blo 291829 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B656873 : Blo 291829 656873 := bstep (se 2 (by rfl) ⟨246327, by rfl⟩ : syracuseStep 656873 = 492655) B492655
theorem B2524891 : Blo 291829 2524891 := bstep (se 1 (by rfl) ⟨1893668, by rfl⟩ : syracuseStep 2524891 = 3787337) B3787337
theorem B1509407 : Blo 291829 1509407 := bstep (se 1 (by rfl) ⟨1132055, by rfl⟩ : syracuseStep 1509407 = 2264111) B2264111
theorem B657449 : Blo 291829 657449 := bstep (se 2 (by rfl) ⟨246543, by rfl⟩ : syracuseStep 657449 = 493087) B493087
theorem B985715 : Blo 291829 985715 := bstep (se 1 (by rfl) ⟨739286, by rfl⟩ : syracuseStep 985715 = 1478573) B1478573
theorem B625295 : Blo 291829 625295 := bstep (se 1 (by rfl) ⟨468971, by rfl⟩ : syracuseStep 625295 = 937943) B937943
theorem B2525849 : Blo 291829 2525849 := bstep (se 2 (by rfl) ⟨947193, by rfl⟩ : syracuseStep 2525849 = 1894387) B1894387
theorem B658079 : Blo 291829 658079 := bstep (se 1 (by rfl) ⟨493559, by rfl⟩ : syracuseStep 658079 = 987119) B987119
theorem B494383 : Blo 291829 494383 := bstep (se 1 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 494383 = 741575) B741575
theorem B1477601 : Blo 291829 1477601 := bstep (se 2 (by rfl) ⟨554100, by rfl⟩ : syracuseStep 1477601 = 1108201) B1108201
theorem B658601 : Blo 291829 658601 := bstep (se 2 (by rfl) ⟨246975, by rfl⟩ : syracuseStep 658601 = 493951) B493951
theorem B298523 : Blo 291829 298523 := bstep (se 1 (by rfl) ⟨223892, by rfl⟩ : syracuseStep 298523 = 447785) B447785
theorem B1674877 : Blo 291829 1674877 := bstep (se 3 (by rfl) ⟨314039, by rfl⟩ : syracuseStep 1674877 = 628079) B628079
theorem B986795 : Blo 291829 986795 := bstep (se 1 (by rfl) ⟨740096, by rfl⟩ : syracuseStep 986795 = 1480193) B1480193
theorem B986849 : Blo 291829 986849 := bstep (se 2 (by rfl) ⟨370068, by rfl⟩ : syracuseStep 986849 = 740137) B740137
theorem B1117921 : Blo 291829 1117921 := bstep (se 2 (by rfl) ⟨419220, by rfl⟩ : syracuseStep 1117921 = 838441) B838441
theorem B495355 : Blo 291829 495355 := bstep (se 1 (by rfl) ⟨371516, by rfl⟩ : syracuseStep 495355 = 743033) B743033
theorem B987335 : Blo 291829 987335 := bstep (se 1 (by rfl) ⟨740501, by rfl⟩ : syracuseStep 987335 = 1481003) B1481003
theorem B1118407 : Blo 291829 1118407 := bstep (se 1 (by rfl) ⟨838805, by rfl⟩ : syracuseStep 1118407 = 1677611) B1677611
theorem B1905697 : Blo 291829 1905697 := bstep (se 2 (by rfl) ⟨714636, by rfl⟩ : syracuseStep 1905697 = 1429273) B1429273
theorem B1414255 : Blo 291829 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B1479869 : Blo 291829 1479869 := bstep (se 3 (by rfl) ⟨277475, by rfl⟩ : syracuseStep 1479869 = 554951) B554951
theorem B660815 : Blo 291829 660815 := bstep (se 1 (by rfl) ⟨495611, by rfl⟩ : syracuseStep 660815 = 991223) B991223
theorem B497063 : Blo 291829 497063 := bstep (se 1 (by rfl) ⟨372797, by rfl⟩ : syracuseStep 497063 = 745595) B745595
theorem B660905 : Blo 291829 660905 := bstep (se 2 (by rfl) ⟨247839, by rfl⟩ : syracuseStep 660905 = 495679) B495679
theorem B660959 : Blo 291829 660959 := bstep (se 1 (by rfl) ⟨495719, by rfl⟩ : syracuseStep 660959 = 991439) B991439
theorem B988793 : Blo 291829 988793 := bstep (se 2 (by rfl) ⟨370797, by rfl⟩ : syracuseStep 988793 = 741595) B741595
theorem B1119865 : Blo 291829 1119865 := bstep (se 2 (by rfl) ⟨419949, by rfl⟩ : syracuseStep 1119865 = 839899) B839899
theorem B1251359 : Blo 291829 1251359 := bstep (se 1 (by rfl) ⟨938519, by rfl⟩ : syracuseStep 1251359 = 1877039) B1877039
theorem B661535 : Blo 291829 661535 := bstep (se 1 (by rfl) ⟨496151, by rfl⟩ : syracuseStep 661535 = 992303) B992303
theorem B3741821 : Blo 291829 3741821 := bstep (se 3 (by rfl) ⟨701591, by rfl⟩ : syracuseStep 3741821 = 1403183) B1403183
theorem B891215 : Blo 291829 891215 := bstep (se 1 (by rfl) ⟨668411, by rfl⟩ : syracuseStep 891215 = 1336823) B1336823
theorem B498089 : Blo 291829 498089 := bstep (se 2 (by rfl) ⟨186783, by rfl⟩ : syracuseStep 498089 = 373567) B373567
theorem B661967 : Blo 291829 661967 := bstep (se 1 (by rfl) ⟨496475, by rfl⟩ : syracuseStep 661967 = 992951) B992951
theorem B662057 : Blo 291829 662057 := bstep (se 2 (by rfl) ⟨248271, by rfl⟩ : syracuseStep 662057 = 496543) B496543
theorem B10787377 : Blo 291829 10787377 := bstep (se 2 (by rfl) ⟨4045266, by rfl⟩ : syracuseStep 10787377 = 8090533) B8090533
theorem B1678067 : Blo 291829 1678067 := bstep (se 1 (by rfl) ⟨1258550, by rfl⟩ : syracuseStep 1678067 = 2517101) B2517101
theorem B663335 : Blo 291829 663335 := bstep (se 1 (by rfl) ⟨497501, by rfl⟩ : syracuseStep 663335 = 995003) B995003
theorem B1482785 : Blo 291829 1482785 := bstep (se 2 (by rfl) ⟨556044, by rfl⟩ : syracuseStep 1482785 = 1112089) B1112089
theorem B795163 : Blo 291829 795163 := bstep (se 1 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 795163 = 1192745) B1192745
theorem B992411 : Blo 291829 992411 := bstep (se 1 (by rfl) ⟨744308, by rfl⟩ : syracuseStep 992411 = 1488617) B1488617
theorem B1418543 : Blo 291829 1418543 := bstep (se 1 (by rfl) ⟨1063907, by rfl⟩ : syracuseStep 1418543 = 2127815) B2127815
theorem B894863 : Blo 291829 894863 := bstep (se 1 (by rfl) ⟨671147, by rfl⟩ : syracuseStep 894863 = 1342295) B1342295
theorem B1681667 : Blo 291829 1681667 := bstep (se 1 (by rfl) ⟨1261250, by rfl⟩ : syracuseStep 1681667 = 2522501) B2522501
theorem B371071 : Blo 291829 371071 := bstep (se 1 (by rfl) ⟨278303, by rfl⟩ : syracuseStep 371071 = 556607) B556607
theorem B1485215 : Blo 291829 1485215 := bstep (se 1 (by rfl) ⟨1113911, by rfl⟩ : syracuseStep 1485215 = 2227823) B2227823
theorem B371567 : Blo 291829 371567 := bstep (se 1 (by rfl) ⟨278675, by rfl⟩ : syracuseStep 371567 = 557351) B557351
theorem B994301 : Blo 291829 994301 := bstep (se 3 (by rfl) ⟨186431, by rfl⟩ : syracuseStep 994301 = 372863) B372863
theorem B1912031 : Blo 291829 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B1191581 : Blo 291829 1191581 := bstep (se 3 (by rfl) ⟨223421, by rfl⟩ : syracuseStep 1191581 = 446843) B446843
theorem B437927 : Blo 291829 437927 := bstep (se 1 (by rfl) ⟨328445, by rfl⟩ : syracuseStep 437927 = 656891) B656891
theorem B1486511 : Blo 291829 1486511 := bstep (se 1 (by rfl) ⟨1114883, by rfl⟩ : syracuseStep 1486511 = 2229767) B2229767
theorem B437951 : Blo 291829 437951 := bstep (se 1 (by rfl) ⟨328463, by rfl⟩ : syracuseStep 437951 = 656927) B656927
theorem B1421003 : Blo 291829 1421003 := bstep (se 1 (by rfl) ⟨1065752, by rfl⟩ : syracuseStep 1421003 = 2131505) B2131505
theorem B438047 : Blo 291829 438047 := bstep (se 1 (by rfl) ⟨328535, by rfl⟩ : syracuseStep 438047 = 657071) B657071
theorem B438335 : Blo 291829 438335 := bstep (se 1 (by rfl) ⟨328751, by rfl⟩ : syracuseStep 438335 = 657503) B657503
theorem B831721 : Blo 291829 831721 := bstep (se 2 (by rfl) ⟨311895, by rfl⟩ : syracuseStep 831721 = 623791) B623791
theorem B438527 : Blo 291829 438527 := bstep (se 1 (by rfl) ⟨328895, by rfl⟩ : syracuseStep 438527 = 657791) B657791
theorem B3191075 : Blo 291829 3191075 := bstep (se 1 (by rfl) ⟨2393306, by rfl⟩ : syracuseStep 3191075 = 4786613) B4786613
theorem B438569 : Blo 291829 438569 := bstep (se 2 (by rfl) ⟨164463, by rfl⟩ : syracuseStep 438569 = 328927) B328927
theorem B2503021 : Blo 291829 2503021 := bstep (se 3 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 2503021 = 938633) B938633
theorem B995867 : Blo 291829 995867 := bstep (se 1 (by rfl) ⟨746900, by rfl⟩ : syracuseStep 995867 = 1493801) B1493801
theorem B438839 : Blo 291829 438839 := bstep (se 1 (by rfl) ⟨329129, by rfl⟩ : syracuseStep 438839 = 658259) B658259
theorem B439079 : Blo 291829 439079 := bstep (se 1 (by rfl) ⟨329309, by rfl⟩ : syracuseStep 439079 = 658619) B658619
theorem B439199 : Blo 291829 439199 := bstep (se 1 (by rfl) ⟨329399, by rfl⟩ : syracuseStep 439199 = 658799) B658799
theorem B373663 : Blo 291829 373663 := bstep (se 1 (by rfl) ⟨280247, by rfl⟩ : syracuseStep 373663 = 560495) B560495
theorem B471977 : Blo 291829 471977 := bstep (se 2 (by rfl) ⟨176991, by rfl⟩ : syracuseStep 471977 = 353983) B353983
theorem B4240457 : Blo 291829 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B2503979 : Blo 291829 2503979 := bstep (se 1 (by rfl) ⟨1877984, by rfl⟩ : syracuseStep 2503979 = 3755969) B3755969
theorem B439673 : Blo 291829 439673 := bstep (se 2 (by rfl) ⟨164877, by rfl⟩ : syracuseStep 439673 = 329755) B329755
theorem B439679 : Blo 291829 439679 := bstep (se 1 (by rfl) ⟨329759, by rfl⟩ : syracuseStep 439679 = 659519) B659519
theorem B996839 : Blo 291829 996839 := bstep (se 1 (by rfl) ⟨747629, by rfl⟩ : syracuseStep 996839 = 1495259) B1495259
theorem B439835 : Blo 291829 439835 := bstep (se 1 (by rfl) ⟨329876, by rfl⟩ : syracuseStep 439835 = 659753) B659753
theorem B3356315 : Blo 291829 3356315 := bstep (se 1 (by rfl) ⟨2517236, by rfl⟩ : syracuseStep 3356315 = 5034473) B5034473
theorem B440015 : Blo 291829 440015 := bstep (se 1 (by rfl) ⟨330011, by rfl⟩ : syracuseStep 440015 = 660023) B660023
theorem B3749611 : Blo 291829 3749611 := bstep (se 1 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 3749611 = 5624417) B5624417
theorem B10860293 : Blo 291829 10860293 := bstep (se 4 (by rfl) ⟨1018152, by rfl⟩ : syracuseStep 10860293 = 2036305) B2036305
theorem B997217 : Blo 291829 997217 := bstep (se 2 (by rfl) ⟨373956, by rfl⟩ : syracuseStep 997217 = 747913) B747913
theorem B440219 : Blo 291829 440219 := bstep (se 1 (by rfl) ⟨330164, by rfl⟩ : syracuseStep 440219 = 660329) B660329
theorem B440255 : Blo 291829 440255 := bstep (se 1 (by rfl) ⟨330191, by rfl⟩ : syracuseStep 440255 = 660383) B660383
theorem B604139 : Blo 291829 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B440423 : Blo 291829 440423 := bstep (se 1 (by rfl) ⟨330317, by rfl⟩ : syracuseStep 440423 = 660635) B660635
theorem B1882597 : Blo 291829 1882597 := bstep (se 4 (by rfl) ⟨176493, by rfl⟩ : syracuseStep 1882597 = 352987) B352987
theorem B440807 : Blo 291829 440807 := bstep (se 1 (by rfl) ⟨330605, by rfl⟩ : syracuseStep 440807 = 661211) B661211
theorem B440879 : Blo 291829 440879 := bstep (se 1 (by rfl) ⟨330659, by rfl⟩ : syracuseStep 440879 = 661319) B661319
theorem B5618267 : Blo 291829 5618267 := bstep (se 1 (by rfl) ⟨4213700, by rfl⟩ : syracuseStep 5618267 = 8427401) B8427401
theorem B670655 : Blo 291829 670655 := bstep (se 1 (by rfl) ⟨502991, by rfl⟩ : syracuseStep 670655 = 1005983) B1005983
theorem B441551 : Blo 291829 441551 := bstep (se 1 (by rfl) ⟨331163, by rfl⟩ : syracuseStep 441551 = 662327) B662327
theorem B441641 : Blo 291829 441641 := bstep (se 2 (by rfl) ⟨165615, by rfl⟩ : syracuseStep 441641 = 331231) B331231
theorem B441671 : Blo 291829 441671 := bstep (se 1 (by rfl) ⟨331253, by rfl⟩ : syracuseStep 441671 = 662507) B662507
theorem B442271 : Blo 291829 442271 := bstep (se 1 (by rfl) ⟨331703, by rfl⟩ : syracuseStep 442271 = 663407) B663407
theorem B442361 : Blo 291829 442361 := bstep (se 2 (by rfl) ⟨165885, by rfl⟩ : syracuseStep 442361 = 331771) B331771
theorem B442505 : Blo 291829 442505 := bstep (se 2 (by rfl) ⟨165939, by rfl⟩ : syracuseStep 442505 = 331879) B331879
theorem B3555515 : Blo 291829 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B442601 : Blo 291829 442601 := bstep (se 2 (by rfl) ⟨165975, by rfl⟩ : syracuseStep 442601 = 331951) B331951
theorem B442727 : Blo 291829 442727 := bstep (se 1 (by rfl) ⟨332045, by rfl⟩ : syracuseStep 442727 = 664091) B664091
theorem B442847 : Blo 291829 442847 := bstep (se 1 (by rfl) ⟨332135, by rfl⟩ : syracuseStep 442847 = 664271) B664271
theorem B443099 : Blo 291829 443099 := bstep (se 1 (by rfl) ⟨332324, by rfl⟩ : syracuseStep 443099 = 664649) B664649
theorem B443513 : Blo 291829 443513 := bstep (se 2 (by rfl) ⟨166317, by rfl⟩ : syracuseStep 443513 = 332635) B332635
theorem B443711 : Blo 291829 443711 := bstep (se 1 (by rfl) ⟨332783, by rfl⟩ : syracuseStep 443711 = 665567) B665567
theorem B935239 : Blo 291829 935239 := bstep (se 1 (by rfl) ⟨701429, by rfl⟩ : syracuseStep 935239 = 1402859) B1402859
theorem B3163481 : Blo 291829 3163481 := bstep (se 2 (by rfl) ⟨1186305, by rfl⟩ : syracuseStep 3163481 = 2372611) B2372611
theorem B1492343 : Blo 291829 1492343 := bstep (se 1 (by rfl) ⟨1119257, by rfl⟩ : syracuseStep 1492343 = 2238515) B2238515
theorem B935995 : Blo 291829 935995 := bstep (se 1 (by rfl) ⟨701996, by rfl⟩ : syracuseStep 935995 = 1403993) B1403993
theorem B1493315 : Blo 291829 1493315 := bstep (se 1 (by rfl) ⟨1119986, by rfl⟩ : syracuseStep 1493315 = 2239973) B2239973
theorem B11258675 : Blo 291829 11258675 := bstep (se 1 (by rfl) ⟨8444006, by rfl⟩ : syracuseStep 11258675 = 16888013) B16888013
theorem B740735 : Blo 291829 740735 := bstep (se 1 (by rfl) ⟨555551, by rfl⟩ : syracuseStep 740735 = 1111103) B1111103
theorem B708551 : Blo 291829 708551 := bstep (se 1 (by rfl) ⟨531413, by rfl⟩ : syracuseStep 708551 = 1062827) B1062827
theorem B938429 : Blo 291829 938429 := bstep (se 3 (by rfl) ⟨175955, by rfl⟩ : syracuseStep 938429 = 351911) B351911
theorem B840127 : Blo 291829 840127 := bstep (se 1 (by rfl) ⟨630095, by rfl⟩ : syracuseStep 840127 = 1260191) B1260191
theorem B1495583 : Blo 291829 1495583 := bstep (se 1 (by rfl) ⟨1121687, by rfl⟩ : syracuseStep 1495583 = 2243375) B2243375
theorem B2839121 : Blo 291829 2839121 := bstep (se 2 (by rfl) ⟨1064670, by rfl⟩ : syracuseStep 2839121 = 2129341) B2129341
theorem B4739897 : Blo 291829 4739897 := bstep (se 2 (by rfl) ⟨1777461, by rfl⟩ : syracuseStep 4739897 = 3554923) B3554923
theorem B742355 : Blo 291829 742355 := bstep (se 1 (by rfl) ⟨556766, by rfl⟩ : syracuseStep 742355 = 1113533) B1113533
theorem B1496393 : Blo 291829 1496393 := bstep (se 2 (by rfl) ⟨561147, by rfl⟩ : syracuseStep 1496393 = 1122295) B1122295
theorem B1496879 : Blo 291829 1496879 := bstep (se 1 (by rfl) ⟨1122659, by rfl⟩ : syracuseStep 1496879 = 2245319) B2245319
theorem B23615621 : Blo 291829 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B940223 : Blo 291829 940223 := bstep (se 1 (by rfl) ⟨705167, by rfl⟩ : syracuseStep 940223 = 1410335) B1410335
theorem B9558557 : Blo 291829 9558557 := bstep (se 3 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 9558557 = 3584459) B3584459
theorem B350911 : Blo 291829 350911 := bstep (se 1 (by rfl) ⟨263183, by rfl⟩ : syracuseStep 350911 = 526367) B526367
theorem B940787 : Blo 291829 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B744511 : Blo 291829 744511 := bstep (se 1 (by rfl) ⟨558383, by rfl⟩ : syracuseStep 744511 = 1116767) B1116767
theorem B744673 : Blo 291829 744673 := bstep (se 2 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 744673 = 558505) B558505
theorem B7987187 : Blo 291829 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B1794251 : Blo 291829 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B10838681 : Blo 291829 10838681 := bstep (se 2 (by rfl) ⟨4064505, by rfl⟩ : syracuseStep 10838681 = 8129011) B8129011
theorem B418537 : Blo 291829 418537 := bstep (se 2 (by rfl) ⟨156951, by rfl⟩ : syracuseStep 418537 = 313903) B313903
theorem B35971913 : Blo 291829 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B1696621 : Blo 291829 1696621 := bstep (se 3 (by rfl) ⟨318116, by rfl⟩ : syracuseStep 1696621 = 636233) B636233
theorem B746617 : Blo 291829 746617 := bstep (se 2 (by rfl) ⟨279981, by rfl⟩ : syracuseStep 746617 = 559963) B559963
theorem B2516143 : Blo 291829 2516143 := bstep (se 1 (by rfl) ⟨1887107, by rfl⟩ : syracuseStep 2516143 = 3774215) B3774215
theorem B746921 : Blo 291829 746921 := bstep (se 2 (by rfl) ⟨280095, by rfl⟩ : syracuseStep 746921 = 560191) B560191
theorem B1336895 : Blo 291829 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B681851 : Blo 291829 681851 := bstep (se 1 (by rfl) ⟨511388, by rfl⟩ : syracuseStep 681851 = 1022777) B1022777
theorem B748025 : Blo 291829 748025 := bstep (se 2 (by rfl) ⟨280509, by rfl⟩ : syracuseStep 748025 = 561019) B561019
theorem B3566213 : Blo 291829 3566213 := bstep (se 4 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 3566213 = 668665) B668665
theorem B748187 : Blo 291829 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B748379 : Blo 291829 748379 := bstep (se 1 (by rfl) ⟨561284, by rfl⟩ : syracuseStep 748379 = 1122569) B1122569
theorem B945017 : Blo 291829 945017 := bstep (se 2 (by rfl) ⟨354381, by rfl⟩ : syracuseStep 945017 = 708763) B708763
theorem B1665947 : Blo 291829 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B57863099 : Blo 291829 57863099 := bstep (se 1 (by rfl) ⟨43397324, by rfl⟩ : syracuseStep 57863099 = 86794649) B86794649
theorem B748673 : Blo 291829 748673 := bstep (se 2 (by rfl) ⟨280752, by rfl⟩ : syracuseStep 748673 = 561505) B561505
theorem B2552485 : Blo 291829 2552485 := bstep (se 4 (by rfl) ⟨239295, by rfl⟩ : syracuseStep 2552485 = 478591) B478591
theorem B291887 : Blo 291829 291887 := bstep (se 1 (by rfl) ⟨218915, by rfl⟩ : syracuseStep 291887 = 437831) B437831
theorem B292007 : Blo 291829 292007 := bstep (se 1 (by rfl) ⟨219005, by rfl⟩ : syracuseStep 292007 = 438011) B438011
theorem B292455 : Blo 291829 292455 := bstep (se 1 (by rfl) ⟨219341, by rfl⟩ : syracuseStep 292455 = 438683) B438683
theorem B554617 : Blo 291829 554617 := bstep (se 2 (by rfl) ⟨207981, by rfl⟩ : syracuseStep 554617 = 415963) B415963
theorem B292735 : Blo 291829 292735 := bstep (se 1 (by rfl) ⟨219551, by rfl⟩ : syracuseStep 292735 = 439103) B439103
theorem B292831 : Blo 291829 292831 := bstep (se 1 (by rfl) ⟨219623, by rfl⟩ : syracuseStep 292831 = 439247) B439247
theorem B292859 : Blo 291829 292859 := bstep (se 1 (by rfl) ⟨219644, by rfl⟩ : syracuseStep 292859 = 439289) B439289
theorem B1636361 : Blo 291829 1636361 := bstep (se 2 (by rfl) ⟨613635, by rfl⟩ : syracuseStep 1636361 = 1227271) B1227271
theorem B292891 : Blo 291829 292891 := bstep (se 1 (by rfl) ⟨219668, by rfl⟩ : syracuseStep 292891 = 439337) B439337
theorem B292911 : Blo 291829 292911 := bstep (se 1 (by rfl) ⟨219683, by rfl⟩ : syracuseStep 292911 = 439367) B439367
theorem B293031 : Blo 291829 293031 := bstep (se 1 (by rfl) ⟨219773, by rfl⟩ : syracuseStep 293031 = 439547) B439547
theorem B4290803 : Blo 291829 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B2226851 : Blo 291829 2226851 := bstep (se 1 (by rfl) ⟨1670138, by rfl⟩ : syracuseStep 2226851 = 3340277) B3340277
theorem B1113047 : Blo 291829 1113047 := bstep (se 1 (by rfl) ⟨834785, by rfl⟩ : syracuseStep 1113047 = 1669571) B1669571
theorem B293855 : Blo 291829 293855 := bstep (se 1 (by rfl) ⟨220391, by rfl⟩ : syracuseStep 293855 = 440783) B440783
theorem B293915 : Blo 291829 293915 := bstep (se 1 (by rfl) ⟨220436, by rfl⟩ : syracuseStep 293915 = 440873) B440873
theorem B98466965 : Blo 291829 98466965 := bstep (se 6 (by rfl) ⟨2307819, by rfl⟩ : syracuseStep 98466965 = 4615639) B4615639
theorem B294043 : Blo 291829 294043 := bstep (se 1 (by rfl) ⟨220532, by rfl⟩ : syracuseStep 294043 = 441065) B441065
theorem B294299 : Blo 291829 294299 := bstep (se 1 (by rfl) ⟨220724, by rfl⟩ : syracuseStep 294299 = 441449) B441449
theorem B294383 : Blo 291829 294383 := bstep (se 1 (by rfl) ⟨220787, by rfl⟩ : syracuseStep 294383 = 441575) B441575
theorem B1080823 : Blo 291829 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B1670777 : Blo 291829 1670777 := bstep (se 2 (by rfl) ⟨626541, by rfl⟩ : syracuseStep 1670777 = 1253083) B1253083
theorem B5996231 : Blo 291829 5996231 := bstep (se 1 (by rfl) ⟨4497173, by rfl⟩ : syracuseStep 5996231 = 8994347) B8994347
theorem B294719 : Blo 291829 294719 := bstep (se 1 (by rfl) ⟨221039, by rfl⟩ : syracuseStep 294719 = 442079) B442079
theorem B294747 : Blo 291829 294747 := bstep (se 1 (by rfl) ⟨221060, by rfl⟩ : syracuseStep 294747 = 442121) B442121
theorem B295003 : Blo 291829 295003 := bstep (se 1 (by rfl) ⟨221252, by rfl⟩ : syracuseStep 295003 = 442505) B442505
theorem B295067 : Blo 291829 295067 := bstep (se 1 (by rfl) ⟨221300, by rfl⟩ : syracuseStep 295067 = 442601) B442601
theorem B295151 : Blo 291829 295151 := bstep (se 1 (by rfl) ⟨221363, by rfl⟩ : syracuseStep 295151 = 442727) B442727
theorem B295231 : Blo 291829 295231 := bstep (se 1 (by rfl) ⟨221423, by rfl⟩ : syracuseStep 295231 = 442847) B442847
theorem B295399 : Blo 291829 295399 := bstep (se 1 (by rfl) ⟨221549, by rfl⟩ : syracuseStep 295399 = 443099) B443099
theorem B295675 : Blo 291829 295675 := bstep (se 1 (by rfl) ⟨221756, by rfl⟩ : syracuseStep 295675 = 443513) B443513
theorem B295807 : Blo 291829 295807 := bstep (se 1 (by rfl) ⟨221855, by rfl⟩ : syracuseStep 295807 = 443711) B443711
theorem B2229281 : Blo 291829 2229281 := bstep (se 2 (by rfl) ⟨835980, by rfl⟩ : syracuseStep 2229281 = 1671961) B1671961
theorem B2262161 : Blo 291829 2262161 := bstep (se 2 (by rfl) ⟨848310, by rfl⟩ : syracuseStep 2262161 = 1696621) B1696621
theorem B1705313 : Blo 291829 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B657143 : Blo 291829 657143 := bstep (se 1 (by rfl) ⟨492857, by rfl⟩ : syracuseStep 657143 = 985715) B985715
theorem B1246985 : Blo 291829 1246985 := bstep (se 2 (by rfl) ⟨467619, by rfl⟩ : syracuseStep 1246985 = 935239) B935239
theorem B7505783 : Blo 291829 7505783 := bstep (se 1 (by rfl) ⟨5629337, by rfl⟩ : syracuseStep 7505783 = 11258675) B11258675
theorem B985067 : Blo 291829 985067 := bstep (se 1 (by rfl) ⟨738800, by rfl⟩ : syracuseStep 985067 = 1477601) B1477601
theorem B493823 : Blo 291829 493823 := bstep (se 1 (by rfl) ⟨370367, by rfl⟩ : syracuseStep 493823 = 740735) B740735
theorem B657863 : Blo 291829 657863 := bstep (se 1 (by rfl) ⟨493397, by rfl⟩ : syracuseStep 657863 = 986795) B986795
theorem B657899 : Blo 291829 657899 := bstep (se 1 (by rfl) ⟨493424, by rfl⟩ : syracuseStep 657899 = 986849) B986849
theorem B1247993 : Blo 291829 1247993 := bstep (se 2 (by rfl) ⟨467997, by rfl⟩ : syracuseStep 1247993 = 935995) B935995
theorem B658223 : Blo 291829 658223 := bstep (se 1 (by rfl) ⟨493667, by rfl⟩ : syracuseStep 658223 = 987335) B987335
theorem B625619 : Blo 291829 625619 := bstep (se 1 (by rfl) ⟨469214, by rfl⟩ : syracuseStep 625619 = 938429) B938429
theorem B494761 : Blo 291829 494761 := bstep (se 2 (by rfl) ⟨185535, by rfl⟩ : syracuseStep 494761 = 371071) B371071
theorem B494903 : Blo 291829 494903 := bstep (se 1 (by rfl) ⟨371177, by rfl⟩ : syracuseStep 494903 = 742355) B742355
theorem B986579 : Blo 291829 986579 := bstep (se 1 (by rfl) ⟨739934, by rfl⟩ : syracuseStep 986579 = 1479869) B1479869
theorem B331375 : Blo 291829 331375 := bstep (se 1 (by rfl) ⟨248531, by rfl⟩ : syracuseStep 331375 = 497063) B497063
theorem B1871525 : Blo 291829 1871525 := bstep (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) B350911
theorem B659177 : Blo 291829 659177 := bstep (se 2 (by rfl) ⟨247191, by rfl⟩ : syracuseStep 659177 = 494383) B494383
theorem B659195 : Blo 291829 659195 := bstep (se 1 (by rfl) ⟨494396, by rfl⟩ : syracuseStep 659195 = 988793) B988793
theorem B2232197 : Blo 291829 2232197 := bstep (se 4 (by rfl) ⟨209268, by rfl⟩ : syracuseStep 2232197 = 418537) B418537
theorem B2494547 : Blo 291829 2494547 := bstep (se 1 (by rfl) ⟨1870910, by rfl⟩ : syracuseStep 2494547 = 3741821) B3741821
theorem B626815 : Blo 291829 626815 := bstep (se 1 (by rfl) ⟨470111, by rfl⟩ : syracuseStep 626815 = 940223) B940223
theorem B594143 : Blo 291829 594143 := bstep (se 1 (by rfl) ⟨445607, by rfl⟩ : syracuseStep 594143 = 891215) B891215
theorem B332059 : Blo 291829 332059 := bstep (se 1 (by rfl) ⟨249044, by rfl⟩ : syracuseStep 332059 = 498089) B498089
theorem B627191 : Blo 291829 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B1118711 : Blo 291829 1118711 := bstep (se 1 (by rfl) ⟨839033, by rfl⟩ : syracuseStep 1118711 = 1678067) B1678067
theorem B2233169 : Blo 291829 2233169 := bstep (se 2 (by rfl) ⟨837438, by rfl⟩ : syracuseStep 2233169 = 1674877) B1674877
theorem B660473 : Blo 291829 660473 := bstep (se 2 (by rfl) ⟨247677, by rfl⟩ : syracuseStep 660473 = 495355) B495355
theorem B1611037 : Blo 291829 1611037 := bstep (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) B604139
theorem B988523 : Blo 291829 988523 := bstep (se 1 (by rfl) ⟨741392, by rfl⟩ : syracuseStep 988523 = 1482785) B1482785
theorem B1120169 : Blo 291829 1120169 := bstep (se 2 (by rfl) ⟨420063, by rfl⟩ : syracuseStep 1120169 = 840127) B840127
theorem B661607 : Blo 291829 661607 := bstep (se 1 (by rfl) ⟨496205, by rfl⟩ : syracuseStep 661607 = 992411) B992411
theorem B497947 : Blo 291829 497947 := bstep (se 1 (by rfl) ⟨373460, by rfl⟩ : syracuseStep 497947 = 746921) B746921
theorem B891263 : Blo 291829 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B498217 : Blo 291829 498217 := bstep (se 2 (by rfl) ⟨186831, by rfl⟩ : syracuseStep 498217 = 373663) B373663
theorem B596575 : Blo 291829 596575 := bstep (se 1 (by rfl) ⟨447431, by rfl⟩ : syracuseStep 596575 = 894863) B894863
theorem B1121111 : Blo 291829 1121111 := bstep (se 1 (by rfl) ⟨840833, by rfl⟩ : syracuseStep 1121111 = 1681667) B1681667
theorem B990143 : Blo 291829 990143 := bstep (se 1 (by rfl) ⟨742607, by rfl⟩ : syracuseStep 990143 = 1485215) B1485215
theorem B498683 : Blo 291829 498683 := bstep (se 1 (by rfl) ⟨374012, by rfl⟩ : syracuseStep 498683 = 748025) B748025
theorem B498791 : Blo 291829 498791 := bstep (se 1 (by rfl) ⟨374093, by rfl⟩ : syracuseStep 498791 = 748187) B748187
theorem B498919 : Blo 291829 498919 := bstep (se 1 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 498919 = 748379) B748379
theorem B630011 : Blo 291829 630011 := bstep (se 1 (by rfl) ⟨472508, by rfl⟩ : syracuseStep 630011 = 945017) B945017
theorem B38575399 : Blo 291829 38575399 := bstep (se 1 (by rfl) ⟨28931549, by rfl⟩ : syracuseStep 38575399 = 57863099) B57863099
theorem B662867 : Blo 291829 662867 := bstep (se 1 (by rfl) ⟨497150, by rfl⟩ : syracuseStep 662867 = 994301) B994301
theorem B499115 : Blo 291829 499115 := bstep (se 1 (by rfl) ⟨374336, by rfl⟩ : syracuseStep 499115 = 748673) B748673
theorem B990845 : Blo 291829 990845 := bstep (se 3 (by rfl) ⟨185783, by rfl⟩ : syracuseStep 990845 = 371567) B371567
theorem B794387 : Blo 291829 794387 := bstep (se 1 (by rfl) ⟨595790, by rfl⟩ : syracuseStep 794387 = 1191581) B1191581
theorem B991007 : Blo 291829 991007 := bstep (se 1 (by rfl) ⟨743255, by rfl⟩ : syracuseStep 991007 = 1486511) B1486511
theorem B663911 : Blo 291829 663911 := bstep (se 1 (by rfl) ⟨497933, by rfl⟩ : syracuseStep 663911 = 995867) B995867
theorem B2826971 : Blo 291829 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B664559 : Blo 291829 664559 := bstep (se 1 (by rfl) ⟨498419, by rfl⟩ : syracuseStep 664559 = 996839) B996839
theorem B2237543 : Blo 291829 2237543 := bstep (se 1 (by rfl) ⟨1678157, by rfl⟩ : syracuseStep 2237543 = 3356315) B3356315
theorem B664811 : Blo 291829 664811 := bstep (se 1 (by rfl) ⟨498608, by rfl⟩ : syracuseStep 664811 = 997217) B997217
theorem B1090907 : Blo 291829 1090907 := bstep (se 1 (by rfl) ⟨818180, by rfl⟩ : syracuseStep 1090907 = 1636361) B1636361
theorem B796061 : Blo 291829 796061 := bstep (se 3 (by rfl) ⟨149261, by rfl⟩ : syracuseStep 796061 = 298523) B298523
theorem B992681 : Blo 291829 992681 := bstep (se 2 (by rfl) ⟨372255, by rfl⟩ : syracuseStep 992681 = 744511) B744511
theorem B2860535 : Blo 291829 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B992897 : Blo 291829 992897 := bstep (se 2 (by rfl) ⟨372336, by rfl⟩ : syracuseStep 992897 = 744673) B744673
theorem B3745511 : Blo 291829 3745511 := bstep (se 1 (by rfl) ⟨2809133, by rfl⟩ : syracuseStep 3745511 = 5618267) B5618267
theorem B1484567 : Blo 291829 1484567 := bstep (se 1 (by rfl) ⟨1113425, by rfl⟩ : syracuseStep 1484567 = 2226851) B2226851
theorem B65644643 : Blo 291829 65644643 := bstep (se 1 (by rfl) ⟨49233482, by rfl⟩ : syracuseStep 65644643 = 98466965) B98466965
theorem B2370343 : Blo 291829 2370343 := bstep (se 1 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 2370343 = 3555515) B3555515
theorem B502895 : Blo 291829 502895 := bstep (se 1 (by rfl) ⟨377171, by rfl⟩ : syracuseStep 502895 = 754343) B754343
theorem B1060217 : Blo 291829 1060217 := bstep (se 2 (by rfl) ⟨397581, by rfl⟩ : syracuseStep 1060217 = 795163) B795163
theorem B2108987 : Blo 291829 2108987 := bstep (se 1 (by rfl) ⟨1581740, by rfl⟩ : syracuseStep 2108987 = 3163481) B3163481
theorem B994895 : Blo 291829 994895 := bstep (se 1 (by rfl) ⟨746171, by rfl⟩ : syracuseStep 994895 = 1492343) B1492343
theorem B437915 : Blo 291829 437915 := bstep (se 1 (by rfl) ⟨328436, by rfl⟩ : syracuseStep 437915 = 656873) B656873
theorem B438299 : Blo 291829 438299 := bstep (se 1 (by rfl) ⟨328724, by rfl⟩ : syracuseStep 438299 = 657449) B657449
theorem B995489 : Blo 291829 995489 := bstep (se 2 (by rfl) ⟨373308, by rfl⟩ : syracuseStep 995489 = 746617) B746617
theorem B995543 : Blo 291829 995543 := bstep (se 1 (by rfl) ⟨746657, by rfl⟩ : syracuseStep 995543 = 1493315) B1493315
theorem B3354857 : Blo 291829 3354857 := bstep (se 2 (by rfl) ⟨1258071, by rfl⟩ : syracuseStep 3354857 = 2516143) B2516143
theorem B1683899 : Blo 291829 1683899 := bstep (se 1 (by rfl) ⟨1262924, by rfl⟩ : syracuseStep 1683899 = 2525849) B2525849
theorem B438719 : Blo 291829 438719 := bstep (se 1 (by rfl) ⟨329039, by rfl⟩ : syracuseStep 438719 = 658079) B658079
theorem B439067 : Blo 291829 439067 := bstep (se 1 (by rfl) ⟨329300, by rfl⟩ : syracuseStep 439067 = 658601) B658601
theorem B472367 : Blo 291829 472367 := bstep (se 1 (by rfl) ⟨354275, by rfl⟩ : syracuseStep 472367 = 708551) B708551
theorem B997055 : Blo 291829 997055 := bstep (se 1 (by rfl) ⟨747791, by rfl⟩ : syracuseStep 997055 = 1495583) B1495583
theorem B3159931 : Blo 291829 3159931 := bstep (se 1 (by rfl) ⟨2369948, by rfl⟩ : syracuseStep 3159931 = 4739897) B4739897
theorem B997595 : Blo 291829 997595 := bstep (se 1 (by rfl) ⟨748196, by rfl⟩ : syracuseStep 997595 = 1496393) B1496393
theorem B440543 : Blo 291829 440543 := bstep (se 1 (by rfl) ⟨330407, by rfl⟩ : syracuseStep 440543 = 660815) B660815
theorem B440603 : Blo 291829 440603 := bstep (se 1 (by rfl) ⟨330452, by rfl⟩ : syracuseStep 440603 = 660905) B660905
theorem B440639 : Blo 291829 440639 := bstep (se 1 (by rfl) ⟨330479, by rfl⟩ : syracuseStep 440639 = 660959) B660959
theorem B997919 : Blo 291829 997919 := bstep (se 1 (by rfl) ⟨748439, by rfl⟩ : syracuseStep 997919 = 1496879) B1496879
theorem B834239 : Blo 291829 834239 := bstep (se 1 (by rfl) ⟨625679, by rfl⟩ : syracuseStep 834239 = 1251359) B1251359
theorem B441023 : Blo 291829 441023 := bstep (se 1 (by rfl) ⟨330767, by rfl⟩ : syracuseStep 441023 = 661535) B661535
theorem B15743747 : Blo 291829 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B441311 : Blo 291829 441311 := bstep (se 1 (by rfl) ⟨330983, by rfl⟩ : syracuseStep 441311 = 661967) B661967
theorem B6372371 : Blo 291829 6372371 := bstep (se 1 (by rfl) ⟨4779278, by rfl⟩ : syracuseStep 6372371 = 9558557) B9558557
theorem B441371 : Blo 291829 441371 := bstep (se 1 (by rfl) ⟨331028, by rfl⟩ : syracuseStep 441371 = 662057) B662057
theorem B1490561 : Blo 291829 1490561 := bstep (se 2 (by rfl) ⟨558960, by rfl⟩ : syracuseStep 1490561 = 1117921) B1117921
theorem B442223 : Blo 291829 442223 := bstep (se 1 (by rfl) ⟨331667, by rfl⟩ : syracuseStep 442223 = 663335) B663335
theorem B5324791 : Blo 291829 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B1196167 : Blo 291829 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B1491209 : Blo 291829 1491209 := bstep (se 2 (by rfl) ⟨559203, by rfl⟩ : syracuseStep 1491209 = 1118407) B1118407
theorem B7225787 : Blo 291829 7225787 := bstep (se 1 (by rfl) ⟨5419340, by rfl⟩ : syracuseStep 7225787 = 10838681) B10838681
theorem B2540929 : Blo 291829 2540929 := bstep (se 2 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 2540929 = 1905697) B1905697
theorem B1885673 : Blo 291829 1885673 := bstep (se 2 (by rfl) ⟨707127, by rfl⟩ : syracuseStep 1885673 = 1414255) B1414255
theorem B2377475 : Blo 291829 2377475 := bstep (se 1 (by rfl) ⟨1783106, by rfl⟩ : syracuseStep 2377475 = 3566213) B3566213
theorem B739489 : Blo 291829 739489 := bstep (se 2 (by rfl) ⟨277308, by rfl⟩ : syracuseStep 739489 = 554617) B554617
theorem B1493153 : Blo 291829 1493153 := bstep (se 2 (by rfl) ⟨559932, by rfl⟩ : syracuseStep 1493153 = 1119865) B1119865
theorem B4999481 : Blo 291829 4999481 := bstep (se 2 (by rfl) ⟨1874805, by rfl⟩ : syracuseStep 4999481 = 3749611) B3749611
theorem B314651 : Blo 291829 314651 := bstep (se 1 (by rfl) ⟨235988, by rfl⟩ : syracuseStep 314651 = 471977) B471977
theorem B2510129 : Blo 291829 2510129 := bstep (se 2 (by rfl) ⟨941298, by rfl⟩ : syracuseStep 2510129 = 1882597) B1882597
theorem B3789341 : Blo 291829 3789341 := bstep (se 3 (by rfl) ⟨710501, by rfl⟩ : syracuseStep 3789341 = 1421003) B1421003
theorem B447103 : Blo 291829 447103 := bstep (se 1 (by rfl) ⟨335327, by rfl⟩ : syracuseStep 447103 = 670655) B670655
theorem B742031 : Blo 291829 742031 := bstep (se 1 (by rfl) ⟨556523, by rfl⟩ : syracuseStep 742031 = 1113047) B1113047
theorem B19355041 : Blo 291829 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B743003 : Blo 291829 743003 := bstep (se 1 (by rfl) ⟨557252, by rfl⟩ : syracuseStep 743003 = 1114505) B1114505
theorem B743327 : Blo 291829 743327 := bstep (se 1 (by rfl) ⟨557495, by rfl⟩ : syracuseStep 743327 = 1114991) B1114991
theorem B1006271 : Blo 291829 1006271 := bstep (se 1 (by rfl) ⟨754703, by rfl⟩ : syracuseStep 1006271 = 1509407) B1509407
theorem B416863 : Blo 291829 416863 := bstep (se 1 (by rfl) ⟨312647, by rfl⟩ : syracuseStep 416863 = 625295) B625295
theorem B3366521 : Blo 291829 3366521 := bstep (se 2 (by rfl) ⟨1262445, by rfl⟩ : syracuseStep 3366521 = 2524891) B2524891
theorem B1892747 : Blo 291829 1892747 := bstep (se 1 (by rfl) ⟨1419560, by rfl⟩ : syracuseStep 1892747 = 2839121) B2839121
theorem B1108961 : Blo 291829 1108961 := bstep (se 2 (by rfl) ⟨415860, by rfl⟩ : syracuseStep 1108961 = 831721) B831721
theorem B3337361 : Blo 291829 3337361 := bstep (se 2 (by rfl) ⟨1251510, by rfl⟩ : syracuseStep 3337361 = 2503021) B2503021
theorem B23981275 : Blo 291829 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B945695 : Blo 291829 945695 := bstep (se 1 (by rfl) ⟨709271, by rfl⟩ : syracuseStep 945695 = 1418543) B1418543
theorem B3403313 : Blo 291829 3403313 := bstep (se 2 (by rfl) ⟨1276242, by rfl⟩ : syracuseStep 3403313 = 2552485) B2552485
theorem B454567 : Blo 291829 454567 := bstep (se 1 (by rfl) ⟨340925, by rfl⟩ : syracuseStep 454567 = 681851) B681851
theorem B1110631 : Blo 291829 1110631 := bstep (se 1 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 1110631 = 1665947) B1665947
theorem B1274687 : Blo 291829 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B291951 : Blo 291829 291951 := bstep (se 1 (by rfl) ⟨218963, by rfl⟩ : syracuseStep 291951 = 437927) B437927
theorem B291967 : Blo 291829 291967 := bstep (se 1 (by rfl) ⟨218975, by rfl⟩ : syracuseStep 291967 = 437951) B437951
theorem B292031 : Blo 291829 292031 := bstep (se 1 (by rfl) ⟨219023, by rfl⟩ : syracuseStep 292031 = 438047) B438047
theorem B292223 : Blo 291829 292223 := bstep (se 1 (by rfl) ⟨219167, by rfl⟩ : syracuseStep 292223 = 438335) B438335
theorem B292351 : Blo 291829 292351 := bstep (se 1 (by rfl) ⟨219263, by rfl⟩ : syracuseStep 292351 = 438527) B438527
theorem B2127383 : Blo 291829 2127383 := bstep (se 1 (by rfl) ⟨1595537, by rfl⟩ : syracuseStep 2127383 = 3191075) B3191075
theorem B292379 : Blo 291829 292379 := bstep (se 1 (by rfl) ⟨219284, by rfl⟩ : syracuseStep 292379 = 438569) B438569
theorem B292559 : Blo 291829 292559 := bstep (se 1 (by rfl) ⟨219419, by rfl⟩ : syracuseStep 292559 = 438839) B438839
theorem B292719 : Blo 291829 292719 := bstep (se 1 (by rfl) ⟨219539, by rfl⟩ : syracuseStep 292719 = 439079) B439079
theorem B292799 : Blo 291829 292799 := bstep (se 1 (by rfl) ⟨219599, by rfl⟩ : syracuseStep 292799 = 439199) B439199
theorem B14383169 : Blo 291829 14383169 := bstep (se 2 (by rfl) ⟨5393688, by rfl⟩ : syracuseStep 14383169 = 10787377) B10787377
theorem B1669319 : Blo 291829 1669319 := bstep (se 1 (by rfl) ⟨1251989, by rfl⟩ : syracuseStep 1669319 = 2503979) B2503979
theorem B293115 : Blo 291829 293115 := bstep (se 1 (by rfl) ⟨219836, by rfl⟩ : syracuseStep 293115 = 439673) B439673
theorem B293119 : Blo 291829 293119 := bstep (se 1 (by rfl) ⟨219839, by rfl⟩ : syracuseStep 293119 = 439679) B439679
theorem B293223 : Blo 291829 293223 := bstep (se 1 (by rfl) ⟨219917, by rfl⟩ : syracuseStep 293223 = 439835) B439835
theorem B293343 : Blo 291829 293343 := bstep (se 1 (by rfl) ⟨220007, by rfl⟩ : syracuseStep 293343 = 440015) B440015
theorem B7240195 : Blo 291829 7240195 := bstep (se 1 (by rfl) ⟨5430146, by rfl⟩ : syracuseStep 7240195 = 10860293) B10860293
theorem B293479 : Blo 291829 293479 := bstep (se 1 (by rfl) ⟨220109, by rfl⟩ : syracuseStep 293479 = 440219) B440219
theorem B293503 : Blo 291829 293503 := bstep (se 1 (by rfl) ⟨220127, by rfl⟩ : syracuseStep 293503 = 440255) B440255
theorem B293615 : Blo 291829 293615 := bstep (se 1 (by rfl) ⟨220211, by rfl⟩ : syracuseStep 293615 = 440423) B440423
theorem B293871 : Blo 291829 293871 := bstep (se 1 (by rfl) ⟨220403, by rfl⟩ : syracuseStep 293871 = 440807) B440807
theorem B293919 : Blo 291829 293919 := bstep (se 1 (by rfl) ⟨220439, by rfl⟩ : syracuseStep 293919 = 440879) B440879
theorem B1441097 : Blo 291829 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B294367 : Blo 291829 294367 := bstep (se 1 (by rfl) ⟨220775, by rfl⟩ : syracuseStep 294367 = 441551) B441551
theorem B294427 : Blo 291829 294427 := bstep (se 1 (by rfl) ⟨220820, by rfl⟩ : syracuseStep 294427 = 441641) B441641
theorem B294447 : Blo 291829 294447 := bstep (se 1 (by rfl) ⟨220835, by rfl⟩ : syracuseStep 294447 = 441671) B441671
theorem B1113851 : Blo 291829 1113851 := bstep (se 1 (by rfl) ⟨835388, by rfl⟩ : syracuseStep 1113851 = 1670777) B1670777
theorem B3997487 : Blo 291829 3997487 := bstep (se 1 (by rfl) ⟨2998115, by rfl⟩ : syracuseStep 3997487 = 5996231) B5996231
theorem B294847 : Blo 291829 294847 := bstep (se 1 (by rfl) ⟨221135, by rfl⟩ : syracuseStep 294847 = 442271) B442271
theorem B294907 : Blo 291829 294907 := bstep (se 1 (by rfl) ⟨221180, by rfl⟩ : syracuseStep 294907 = 442361) B442361
theorem B4817191 : Blo 291829 4817191 := bstep (se 1 (by rfl) ⟨3612893, by rfl⟩ : syracuseStep 4817191 = 7225787) B7225787
theorem B1508107 : Blo 291829 1508107 := bstep (se 1 (by rfl) ⟨1131080, by rfl⟩ : syracuseStep 1508107 = 2262161) B2262161
theorem B656711 : Blo 291829 656711 := bstep (se 1 (by rfl) ⟨492533, by rfl⟩ : syracuseStep 656711 = 985067) B985067
theorem B329215 : Blo 291829 329215 := bstep (se 1 (by rfl) ⟨246911, by rfl⟩ : syracuseStep 329215 = 493823) B493823
theorem B1673419 : Blo 291829 1673419 := bstep (se 1 (by rfl) ⟨1255064, by rfl⟩ : syracuseStep 1673419 = 2510129) B2510129
theorem B329935 : Blo 291829 329935 := bstep (se 1 (by rfl) ⟨247451, by rfl⟩ : syracuseStep 329935 = 494903) B494903
theorem B657719 : Blo 291829 657719 := bstep (se 1 (by rfl) ⟨493289, by rfl⟩ : syracuseStep 657719 = 986579) B986579
theorem B396095 : Blo 291829 396095 := bstep (se 1 (by rfl) ⟨297071, by rfl⟩ : syracuseStep 396095 = 594143) B594143
theorem B985985 : Blo 291829 985985 := bstep (se 2 (by rfl) ⟨369744, by rfl⟩ : syracuseStep 985985 = 739489) B739489
theorem B2526227 : Blo 291829 2526227 := bstep (se 1 (by rfl) ⟨1894670, by rfl⟩ : syracuseStep 2526227 = 3789341) B3789341
theorem B494687 : Blo 291829 494687 := bstep (se 1 (by rfl) ⟨371015, by rfl⟩ : syracuseStep 494687 = 742031) B742031
theorem B659015 : Blo 291829 659015 := bstep (se 1 (by rfl) ⟨494261, by rfl⟩ : syracuseStep 659015 = 988523) B988523
theorem B495335 : Blo 291829 495335 := bstep (se 1 (by rfl) ⟨371501, by rfl⟩ : syracuseStep 495335 = 743003) B743003
theorem B495551 : Blo 291829 495551 := bstep (se 1 (by rfl) ⟨371663, by rfl⟩ : syracuseStep 495551 = 743327) B743327
theorem B659681 : Blo 291829 659681 := bstep (se 2 (by rfl) ⟨247380, by rfl⟩ : syracuseStep 659681 = 494761) B494761
theorem B660095 : Blo 291829 660095 := bstep (se 1 (by rfl) ⟨495071, by rfl⟩ : syracuseStep 660095 = 990143) B990143
theorem B332455 : Blo 291829 332455 := bstep (se 1 (by rfl) ⟨249341, by rfl⟩ : syracuseStep 332455 = 498683) B498683
theorem B332527 : Blo 291829 332527 := bstep (se 1 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 332527 = 498791) B498791
theorem B332743 : Blo 291829 332743 := bstep (se 1 (by rfl) ⟨249557, by rfl⟩ : syracuseStep 332743 = 499115) B499115
theorem B660563 : Blo 291829 660563 := bstep (se 1 (by rfl) ⟨495422, by rfl⟩ : syracuseStep 660563 = 990845) B990845
theorem B529591 : Blo 291829 529591 := bstep (se 1 (by rfl) ⟨397193, by rfl⟩ : syracuseStep 529591 = 794387) B794387
theorem B660671 : Blo 291829 660671 := bstep (se 1 (by rfl) ⟨495503, by rfl⟩ : syracuseStep 660671 = 991007) B991007
theorem B1480841 : Blo 291829 1480841 := bstep (se 2 (by rfl) ⟨555315, by rfl⟩ : syracuseStep 1480841 = 1110631) B1110631
theorem B727271 : Blo 291829 727271 := bstep (se 1 (by rfl) ⟨545453, by rfl⟩ : syracuseStep 727271 = 1090907) B1090907
theorem B530707 : Blo 291829 530707 := bstep (se 1 (by rfl) ⟨398030, by rfl⟩ : syracuseStep 530707 = 796061) B796061
theorem B661787 : Blo 291829 661787 := bstep (se 1 (by rfl) ⟨496340, by rfl⟩ : syracuseStep 661787 = 992681) B992681
theorem B1907023 : Blo 291829 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B661931 : Blo 291829 661931 := bstep (se 1 (by rfl) ⟨496448, by rfl⟩ : syracuseStep 661931 = 992897) B992897
theorem B2497007 : Blo 291829 2497007 := bstep (se 1 (by rfl) ⟨1872755, by rfl⟩ : syracuseStep 2497007 = 3745511) B3745511
theorem B989711 : Blo 291829 989711 := bstep (se 1 (by rfl) ⟨742283, by rfl⟩ : syracuseStep 989711 = 1484567) B1484567
theorem B2268875 : Blo 291829 2268875 := bstep (se 1 (by rfl) ⟨1701656, by rfl⟩ : syracuseStep 2268875 = 3403313) B3403313
theorem B663263 : Blo 291829 663263 := bstep (se 1 (by rfl) ⟨497447, by rfl⟩ : syracuseStep 663263 = 994895) B994895
theorem B663659 : Blo 291829 663659 := bstep (se 1 (by rfl) ⟨497744, by rfl⟩ : syracuseStep 663659 = 995489) B995489
theorem B663695 : Blo 291829 663695 := bstep (se 1 (by rfl) ⟨497771, by rfl⟩ : syracuseStep 663695 = 995543) B995543
theorem B2236571 : Blo 291829 2236571 := bstep (se 1 (by rfl) ⟨1677428, by rfl⟩ : syracuseStep 2236571 = 3354857) B3354857
theorem B1122599 : Blo 291829 1122599 := bstep (se 1 (by rfl) ⟨841949, by rfl⟩ : syracuseStep 1122599 = 1683899) B1683899
theorem B663929 : Blo 291829 663929 := bstep (se 2 (by rfl) ⟨248973, by rfl⟩ : syracuseStep 663929 = 497947) B497947
theorem B664289 : Blo 291829 664289 := bstep (se 2 (by rfl) ⟨249108, by rfl⟩ : syracuseStep 664289 = 498217) B498217
theorem B795433 : Blo 291829 795433 := bstep (se 2 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 795433 = 596575) B596575
theorem B1418255 : Blo 291829 1418255 := bstep (se 1 (by rfl) ⟨1063691, by rfl⟩ : syracuseStep 1418255 = 2127383) B2127383
theorem B664703 : Blo 291829 664703 := bstep (se 1 (by rfl) ⟨498527, by rfl⟩ : syracuseStep 664703 = 997055) B997055
theorem B665063 : Blo 291829 665063 := bstep (se 1 (by rfl) ⟨498797, by rfl⟩ : syracuseStep 665063 = 997595) B997595
theorem B665225 : Blo 291829 665225 := bstep (se 2 (by rfl) ⟨249459, by rfl⟩ : syracuseStep 665225 = 498919) B498919
theorem B665279 : Blo 291829 665279 := bstep (se 1 (by rfl) ⟨498959, by rfl⟩ : syracuseStep 665279 = 997919) B997919
theorem B4990733 : Blo 291829 4990733 := bstep (se 3 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 4990733 = 1871525) B1871525
theorem B10495831 : Blo 291829 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B960731 : Blo 291829 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B993707 : Blo 291829 993707 := bstep (se 1 (by rfl) ⟨745280, by rfl⟩ : syracuseStep 993707 = 1490561) B1490561
theorem B2664991 : Blo 291829 2664991 := bstep (se 1 (by rfl) ⟨1998743, by rfl⟩ : syracuseStep 2664991 = 3997487) B3997487
theorem B994139 : Blo 291829 994139 := bstep (se 1 (by rfl) ⟨745604, by rfl⟩ : syracuseStep 994139 = 1491209) B1491209
theorem B1486187 : Blo 291829 1486187 := bstep (se 1 (by rfl) ⟨1114640, by rfl⟩ : syracuseStep 1486187 = 2229281) B2229281
theorem B1257115 : Blo 291829 1257115 := bstep (se 1 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 1257115 = 1885673) B1885673
theorem B438095 : Blo 291829 438095 := bstep (se 1 (by rfl) ⟨328571, by rfl⟩ : syracuseStep 438095 = 657143) B657143
theorem B1584983 : Blo 291829 1584983 := bstep (se 1 (by rfl) ⟨1188737, by rfl⟩ : syracuseStep 1584983 = 2377475) B2377475
theorem B831323 : Blo 291829 831323 := bstep (se 1 (by rfl) ⟨623492, by rfl⟩ : syracuseStep 831323 = 1246985) B1246985
theorem B995435 : Blo 291829 995435 := bstep (se 1 (by rfl) ⟨746576, by rfl⟩ : syracuseStep 995435 = 1493153) B1493153
theorem B438575 : Blo 291829 438575 := bstep (se 1 (by rfl) ⟨328931, by rfl⟩ : syracuseStep 438575 = 657863) B657863
theorem B438599 : Blo 291829 438599 := bstep (se 1 (by rfl) ⟨328949, by rfl⟩ : syracuseStep 438599 = 657899) B657899
theorem B831995 : Blo 291829 831995 := bstep (se 1 (by rfl) ⟨623996, by rfl⟩ : syracuseStep 831995 = 1247993) B1247993
theorem B3387905 : Blo 291829 3387905 := bstep (se 2 (by rfl) ⟨1270464, by rfl⟩ : syracuseStep 3387905 = 2540929) B2540929
theorem B438815 : Blo 291829 438815 := bstep (se 1 (by rfl) ⟨329111, by rfl⟩ : syracuseStep 438815 = 658223) B658223
theorem B439451 : Blo 291829 439451 := bstep (se 1 (by rfl) ⟨329588, by rfl⟩ : syracuseStep 439451 = 659177) B659177
theorem B439463 : Blo 291829 439463 := bstep (se 1 (by rfl) ⟨329597, by rfl⟩ : syracuseStep 439463 = 659195) B659195
theorem B1488131 : Blo 291829 1488131 := bstep (se 1 (by rfl) ⟨1116098, by rfl⟩ : syracuseStep 1488131 = 2232197) B2232197
theorem B1488779 : Blo 291829 1488779 := bstep (se 1 (by rfl) ⟨1116584, by rfl⟩ : syracuseStep 1488779 = 2233169) B2233169
theorem B440315 : Blo 291829 440315 := bstep (se 1 (by rfl) ⟨330236, by rfl⟩ : syracuseStep 440315 = 660473) B660473
theorem B3160457 : Blo 291829 3160457 := bstep (se 2 (by rfl) ⟨1185171, by rfl⟩ : syracuseStep 3160457 = 2370343) B2370343
theorem B441071 : Blo 291829 441071 := bstep (se 1 (by rfl) ⟨330803, by rfl⟩ : syracuseStep 441071 = 661607) B661607
theorem B670847 : Blo 291829 670847 := bstep (se 1 (by rfl) ⟨503135, by rfl⟩ : syracuseStep 670847 = 1006271) B1006271
theorem B441833 : Blo 291829 441833 := bstep (se 2 (by rfl) ⟨165687, by rfl⟩ : syracuseStep 441833 = 331375) B331375
theorem B441911 : Blo 291829 441911 := bstep (se 1 (by rfl) ⟨331433, by rfl⟩ : syracuseStep 441911 = 662867) B662867
theorem B2244347 : Blo 291829 2244347 := bstep (se 1 (by rfl) ⟨1683260, by rfl⟩ : syracuseStep 2244347 = 3366521) B3366521
theorem B606089 : Blo 291829 606089 := bstep (se 2 (by rfl) ⟨227283, by rfl⟩ : syracuseStep 606089 = 454567) B454567
theorem B835753 : Blo 291829 835753 := bstep (se 2 (by rfl) ⟨313407, by rfl⟩ : syracuseStep 835753 = 626815) B626815
theorem B442607 : Blo 291829 442607 := bstep (se 1 (by rfl) ⟨331955, by rfl⟩ : syracuseStep 442607 = 663911) B663911
theorem B1261831 : Blo 291829 1261831 := bstep (se 1 (by rfl) ⟨946373, by rfl⟩ : syracuseStep 1261831 = 1892747) B1892747
theorem B442745 : Blo 291829 442745 := bstep (se 2 (by rfl) ⟨166029, by rfl⟩ : syracuseStep 442745 = 332059) B332059
theorem B1884647 : Blo 291829 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B443039 : Blo 291829 443039 := bstep (se 1 (by rfl) ⟨332279, by rfl⟩ : syracuseStep 443039 = 664559) B664559
theorem B1491695 : Blo 291829 1491695 := bstep (se 1 (by rfl) ⟨1118771, by rfl⟩ : syracuseStep 1491695 = 2237543) B2237543
theorem B443207 : Blo 291829 443207 := bstep (se 1 (by rfl) ⟨332405, by rfl⟩ : syracuseStep 443207 = 664811) B664811
theorem B2376701 : Blo 291829 2376701 := bstep (se 3 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 2376701 = 891263) B891263
theorem B43763095 : Blo 291829 43763095 := bstep (se 1 (by rfl) ⟨32822321, by rfl⟩ : syracuseStep 43763095 = 65644643) B65644643
theorem B2148049 : Blo 291829 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B25806721 : Blo 291829 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B739307 : Blo 291829 739307 := bstep (se 1 (by rfl) ⟨554480, by rfl⟩ : syracuseStep 739307 = 1108961) B1108961
theorem B706811 : Blo 291829 706811 := bstep (se 1 (by rfl) ⟨530108, by rfl⟩ : syracuseStep 706811 = 1060217) B1060217
theorem B4213241 : Blo 291829 4213241 := bstep (se 2 (by rfl) ⟨1579965, by rfl⟩ : syracuseStep 4213241 = 3159931) B3159931
theorem B9653593 : Blo 291829 9653593 := bstep (se 2 (by rfl) ⟨3620097, by rfl⟩ : syracuseStep 9653593 = 7240195) B7240195
theorem B839069 : Blo 291829 839069 := bstep (se 3 (by rfl) ⟨157325, by rfl⟩ : syracuseStep 839069 = 314651) B314651
theorem B314911 : Blo 291829 314911 := bstep (se 1 (by rfl) ⟨236183, by rfl⟩ : syracuseStep 314911 = 472367) B472367
theorem B9588779 : Blo 291829 9588779 := bstep (se 1 (by rfl) ⟨7191584, by rfl⟩ : syracuseStep 9588779 = 14383169) B14383169
theorem B51433865 : Blo 291829 51433865 := bstep (se 2 (by rfl) ⟨19287699, by rfl⟩ : syracuseStep 51433865 = 38575399) B38575399
theorem B4248247 : Blo 291829 4248247 := bstep (se 1 (by rfl) ⟨3186185, by rfl⟩ : syracuseStep 4248247 = 6372371) B6372371
theorem B742567 : Blo 291829 742567 := bstep (se 1 (by rfl) ⟨556925, by rfl⟩ : syracuseStep 742567 = 1113851) B1113851
theorem B7099721 : Blo 291829 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B1594889 : Blo 291829 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B1136875 : Blo 291829 1136875 := bstep (se 1 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 1136875 = 1705313) B1705313
theorem B5003855 : Blo 291829 5003855 := bstep (se 1 (by rfl) ⟨3752891, by rfl⟩ : syracuseStep 5003855 = 7505783) B7505783
theorem B3332987 : Blo 291829 3332987 := bstep (se 1 (by rfl) ⟨2499740, by rfl⟩ : syracuseStep 3332987 = 4999481) B4999481
theorem B417079 : Blo 291829 417079 := bstep (se 1 (by rfl) ⟨312809, by rfl⟩ : syracuseStep 417079 = 625619) B625619
theorem B1663031 : Blo 291829 1663031 := bstep (se 1 (by rfl) ⟨1247273, by rfl⟩ : syracuseStep 1663031 = 2494547) B2494547
theorem B418127 : Blo 291829 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B745807 : Blo 291829 745807 := bstep (se 1 (by rfl) ⟨559355, by rfl⟩ : syracuseStep 745807 = 1118711) B1118711
theorem B2384549 : Blo 291829 2384549 := bstep (se 4 (by rfl) ⟨223551, by rfl⟩ : syracuseStep 2384549 = 447103) B447103
theorem B746779 : Blo 291829 746779 := bstep (se 1 (by rfl) ⟨560084, by rfl⟩ : syracuseStep 746779 = 1120169) B1120169
theorem B31975033 : Blo 291829 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B747407 : Blo 291829 747407 := bstep (se 1 (by rfl) ⟨560555, by rfl⟩ : syracuseStep 747407 = 1121111) B1121111
theorem B420007 : Blo 291829 420007 := bstep (se 1 (by rfl) ⟨315005, by rfl⟩ : syracuseStep 420007 = 630011) B630011
theorem B2224907 : Blo 291829 2224907 := bstep (se 1 (by rfl) ⟨1668680, by rfl⟩ : syracuseStep 2224907 = 3337361) B3337361
theorem B1405991 : Blo 291829 1405991 := bstep (se 1 (by rfl) ⟨1054493, by rfl⟩ : syracuseStep 1405991 = 2108987) B2108987
theorem B291943 : Blo 291829 291943 := bstep (se 1 (by rfl) ⟨218957, by rfl⟩ : syracuseStep 291943 = 437915) B437915
theorem B292199 : Blo 291829 292199 := bstep (se 1 (by rfl) ⟨219149, by rfl⟩ : syracuseStep 292199 = 438299) B438299
theorem B1341053 : Blo 291829 1341053 := bstep (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) B502895
theorem B292479 : Blo 291829 292479 := bstep (se 1 (by rfl) ⟨219359, by rfl⟩ : syracuseStep 292479 = 438719) B438719
theorem B292711 : Blo 291829 292711 := bstep (se 1 (by rfl) ⟨219533, by rfl⟩ : syracuseStep 292711 = 439067) B439067
theorem B849791 : Blo 291829 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B2521853 : Blo 291829 2521853 := bstep (se 3 (by rfl) ⟨472847, by rfl⟩ : syracuseStep 2521853 = 945695) B945695
theorem B555817 : Blo 291829 555817 := bstep (se 2 (by rfl) ⟨208431, by rfl⟩ : syracuseStep 555817 = 416863) B416863
theorem B1112879 : Blo 291829 1112879 := bstep (se 1 (by rfl) ⟨834659, by rfl⟩ : syracuseStep 1112879 = 1669319) B1669319
theorem B293695 : Blo 291829 293695 := bstep (se 1 (by rfl) ⟨220271, by rfl⟩ : syracuseStep 293695 = 440543) B440543
theorem B293735 : Blo 291829 293735 := bstep (se 1 (by rfl) ⟨220301, by rfl⟩ : syracuseStep 293735 = 440603) B440603
theorem B293759 : Blo 291829 293759 := bstep (se 1 (by rfl) ⟨220319, by rfl⟩ : syracuseStep 293759 = 440639) B440639
theorem B556159 : Blo 291829 556159 := bstep (se 1 (by rfl) ⟨417119, by rfl⟩ : syracuseStep 556159 = 834239) B834239
theorem B294015 : Blo 291829 294015 := bstep (se 1 (by rfl) ⟨220511, by rfl⟩ : syracuseStep 294015 = 441023) B441023
theorem B294207 : Blo 291829 294207 := bstep (se 1 (by rfl) ⟨220655, by rfl⟩ : syracuseStep 294207 = 441311) B441311
theorem B294247 : Blo 291829 294247 := bstep (se 1 (by rfl) ⟨220685, by rfl⟩ : syracuseStep 294247 = 441371) B441371
theorem B294815 : Blo 291829 294815 := bstep (se 1 (by rfl) ⟨221111, by rfl⟩ : syracuseStep 294815 = 442223) B442223
theorem B295071 : Blo 291829 295071 := bstep (se 1 (by rfl) ⟨221303, by rfl⟩ : syracuseStep 295071 = 442607) B442607
theorem B1114337 : Blo 291829 1114337 := bstep (se 2 (by rfl) ⟨417876, by rfl⟩ : syracuseStep 1114337 = 835753) B835753
theorem B295163 : Blo 291829 295163 := bstep (se 1 (by rfl) ⟨221372, by rfl⟩ : syracuseStep 295163 = 442745) B442745
theorem B6422921 : Blo 291829 6422921 := bstep (se 2 (by rfl) ⟨2408595, by rfl⟩ : syracuseStep 6422921 = 4817191) B4817191
theorem B295359 : Blo 291829 295359 := bstep (se 1 (by rfl) ⟨221519, by rfl⟩ : syracuseStep 295359 = 443039) B443039
theorem B295471 : Blo 291829 295471 := bstep (se 1 (by rfl) ⟨221603, by rfl⟩ : syracuseStep 295471 = 443207) B443207
theorem B1115005 : Blo 291829 1115005 := bstep (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) B418127
theorem B492871 : Blo 291829 492871 := bstep (se 1 (by rfl) ⟨369653, by rfl⟩ : syracuseStep 492871 = 739307) B739307
theorem B657323 : Blo 291829 657323 := bstep (se 1 (by rfl) ⟨492992, by rfl⟩ : syracuseStep 657323 = 985985) B985985
theorem B329791 : Blo 291829 329791 := bstep (se 1 (by rfl) ⟨247343, by rfl⟩ : syracuseStep 329791 = 494687) B494687
theorem B42633377 : Blo 291829 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B559379 : Blo 291829 559379 := bstep (se 1 (by rfl) ⟨419534, by rfl⟩ : syracuseStep 559379 = 839069) B839069
theorem B13994441 : Blo 291829 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B330223 : Blo 291829 330223 := bstep (se 1 (by rfl) ⟨247667, by rfl⟩ : syracuseStep 330223 = 495335) B495335
theorem B34408961 : Blo 291829 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B330367 : Blo 291829 330367 := bstep (se 1 (by rfl) ⟨247775, by rfl⟩ : syracuseStep 330367 = 495551) B495551
theorem B6392519 : Blo 291829 6392519 := bstep (se 1 (by rfl) ⟨4794389, by rfl⟩ : syracuseStep 6392519 = 9588779) B9588779
theorem B560009 : Blo 291829 560009 := bstep (se 2 (by rfl) ⟨210003, by rfl⟩ : syracuseStep 560009 = 420007) B420007
theorem B2231225 : Blo 291829 2231225 := bstep (se 2 (by rfl) ⟨836709, by rfl⟩ : syracuseStep 2231225 = 1673419) B1673419
theorem B987227 : Blo 291829 987227 := bstep (se 1 (by rfl) ⟨740420, by rfl⟩ : syracuseStep 987227 = 1480841) B1480841
theorem B659807 : Blo 291829 659807 := bstep (se 1 (by rfl) ⟨494855, by rfl⟩ : syracuseStep 659807 = 989711) B989711
theorem B1676153 : Blo 291829 1676153 := bstep (se 2 (by rfl) ⟨628557, by rfl⟩ : syracuseStep 1676153 = 1257115) B1257115
theorem B1512583 : Blo 291829 1512583 := bstep (se 1 (by rfl) ⟨1134437, by rfl⟩ : syracuseStep 1512583 = 2268875) B2268875
theorem B498271 : Blo 291829 498271 := bstep (se 1 (by rfl) ⟨373703, by rfl⟩ : syracuseStep 498271 = 747407) B747407
theorem B990089 : Blo 291829 990089 := bstep (se 2 (by rfl) ⟨371283, by rfl⟩ : syracuseStep 990089 = 742567) B742567
theorem B662471 : Blo 291829 662471 := bstep (se 1 (by rfl) ⟨496853, by rfl⟩ : syracuseStep 662471 = 993707) B993707
theorem B662759 : Blo 291829 662759 := bstep (se 1 (by rfl) ⟨497069, by rfl⟩ : syracuseStep 662759 = 994139) B994139
theorem B1056253 : Blo 291829 1056253 := bstep (se 3 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 1056253 = 396095) B396095
theorem B990791 : Blo 291829 990791 := bstep (se 1 (by rfl) ⟨743093, by rfl⟩ : syracuseStep 990791 = 1486187) B1486187
theorem B1056655 : Blo 291829 1056655 := bstep (se 1 (by rfl) ⟨792491, by rfl⟩ : syracuseStep 1056655 = 1584983) B1584983
theorem B663623 : Blo 291829 663623 := bstep (se 1 (by rfl) ⟨497717, by rfl⟩ : syracuseStep 663623 = 995435) B995435
theorem B1679525 : Blo 291829 1679525 := bstep (se 4 (by rfl) ⟨157455, by rfl⟩ : syracuseStep 1679525 = 314911) B314911
theorem B1515833 : Blo 291829 1515833 := bstep (se 2 (by rfl) ⟨568437, by rfl⟩ : syracuseStep 1515833 = 1136875) B1136875
theorem B1483271 : Blo 291829 1483271 := bstep (se 1 (by rfl) ⟨1112453, by rfl⟩ : syracuseStep 1483271 = 2224907) B2224907
theorem B992087 : Blo 291829 992087 := bstep (se 1 (by rfl) ⟨744065, by rfl⟩ : syracuseStep 992087 = 1488131) B1488131
theorem B894035 : Blo 291829 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B566527 : Blo 291829 566527 := bstep (se 1 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 566527 = 849791) B849791
theorem B992519 : Blo 291829 992519 := bstep (se 1 (by rfl) ⟨744389, by rfl⟩ : syracuseStep 992519 = 1488779) B1488779
theorem B2106971 : Blo 291829 2106971 := bstep (se 1 (by rfl) ⟨1580228, by rfl⟩ : syracuseStep 2106971 = 3160457) B3160457
theorem B1681235 : Blo 291829 1681235 := bstep (se 1 (by rfl) ⟨1260926, by rfl⟩ : syracuseStep 1681235 = 2521853) B2521853
theorem B1616237 : Blo 291829 1616237 := bstep (se 3 (by rfl) ⟨303044, by rfl⟩ : syracuseStep 1616237 = 606089) B606089
theorem B1682441 : Blo 291829 1682441 := bstep (se 2 (by rfl) ⟨630915, by rfl⟩ : syracuseStep 1682441 = 1261831) B1261831
theorem B994409 : Blo 291829 994409 := bstep (se 2 (by rfl) ⟨372903, by rfl⟩ : syracuseStep 994409 = 745807) B745807
theorem B994463 : Blo 291829 994463 := bstep (se 1 (by rfl) ⟨745847, by rfl⟩ : syracuseStep 994463 = 1491695) B1491695
theorem B1584467 : Blo 291829 1584467 := bstep (se 1 (by rfl) ⟨1188350, by rfl⟩ : syracuseStep 1584467 = 2376701) B2376701
theorem B437807 : Blo 291829 437807 := bstep (se 1 (by rfl) ⟨328355, by rfl⟩ : syracuseStep 437807 = 656711) B656711
theorem B2010809 : Blo 291829 2010809 := bstep (se 2 (by rfl) ⟨754053, by rfl⟩ : syracuseStep 2010809 = 1508107) B1508107
theorem B1060577 : Blo 291829 1060577 := bstep (se 2 (by rfl) ⟨397716, by rfl⟩ : syracuseStep 1060577 = 795433) B795433
theorem B5025725 : Blo 291829 5025725 := bstep (se 3 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 5025725 = 1884647) B1884647
theorem B438479 : Blo 291829 438479 := bstep (se 1 (by rfl) ⟨328859, by rfl⟩ : syracuseStep 438479 = 657719) B657719
theorem B995705 : Blo 291829 995705 := bstep (se 2 (by rfl) ⟨373389, by rfl⟩ : syracuseStep 995705 = 746779) B746779
theorem B438953 : Blo 291829 438953 := bstep (se 2 (by rfl) ⟨164607, by rfl⟩ : syracuseStep 438953 = 329215) B329215
theorem B1684151 : Blo 291829 1684151 := bstep (se 1 (by rfl) ⟨1263113, by rfl⟩ : syracuseStep 1684151 = 2526227) B2526227
theorem B2864065 : Blo 291829 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B439343 : Blo 291829 439343 := bstep (se 1 (by rfl) ⟨329507, by rfl⟩ : syracuseStep 439343 = 659015) B659015
theorem B439787 : Blo 291829 439787 := bstep (se 1 (by rfl) ⟨329840, by rfl⟩ : syracuseStep 439787 = 659681) B659681
theorem B34289243 : Blo 291829 34289243 := bstep (se 1 (by rfl) ⟨25716932, by rfl⟩ : syracuseStep 34289243 = 51433865) B51433865
theorem B439913 : Blo 291829 439913 := bstep (se 2 (by rfl) ⟨164967, by rfl⟩ : syracuseStep 439913 = 329935) B329935
theorem B440063 : Blo 291829 440063 := bstep (se 1 (by rfl) ⟨330047, by rfl⟩ : syracuseStep 440063 = 660095) B660095
theorem B3553321 : Blo 291829 3553321 := bstep (se 2 (by rfl) ⟨1332495, by rfl⟩ : syracuseStep 3553321 = 2664991) B2664991
theorem B440375 : Blo 291829 440375 := bstep (se 1 (by rfl) ⟨330281, by rfl⟩ : syracuseStep 440375 = 660563) B660563
theorem B440447 : Blo 291829 440447 := bstep (se 1 (by rfl) ⟨330335, by rfl⟩ : syracuseStep 440447 = 660671) B660671
theorem B4733147 : Blo 291829 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B1063259 : Blo 291829 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B441191 : Blo 291829 441191 := bstep (se 1 (by rfl) ⟨330893, by rfl⟩ : syracuseStep 441191 = 661787) B661787
theorem B441287 : Blo 291829 441287 := bstep (se 1 (by rfl) ⟨330965, by rfl⟩ : syracuseStep 441287 = 661931) B661931
theorem B442175 : Blo 291829 442175 := bstep (se 1 (by rfl) ⟨331631, by rfl⟩ : syracuseStep 442175 = 663263) B663263
theorem B442439 : Blo 291829 442439 := bstep (se 1 (by rfl) ⟨331829, by rfl⟩ : syracuseStep 442439 = 663659) B663659
theorem B442463 : Blo 291829 442463 := bstep (se 1 (by rfl) ⟨331847, by rfl⟩ : syracuseStep 442463 = 663695) B663695
theorem B1491047 : Blo 291829 1491047 := bstep (se 1 (by rfl) ⟨1118285, by rfl⟩ : syracuseStep 1491047 = 2236571) B2236571
theorem B442619 : Blo 291829 442619 := bstep (se 1 (by rfl) ⟨331964, by rfl⟩ : syracuseStep 442619 = 663929) B663929
theorem B1589699 : Blo 291829 1589699 := bstep (se 1 (by rfl) ⟨1192274, by rfl⟩ : syracuseStep 1589699 = 2384549) B2384549
theorem B442859 : Blo 291829 442859 := bstep (se 1 (by rfl) ⟨332144, by rfl⟩ : syracuseStep 442859 = 664289) B664289
theorem B1884829 : Blo 291829 1884829 := bstep (se 3 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 1884829 = 706811) B706811
theorem B443135 : Blo 291829 443135 := bstep (se 1 (by rfl) ⟨332351, by rfl⟩ : syracuseStep 443135 = 664703) B664703
theorem B443273 : Blo 291829 443273 := bstep (se 2 (by rfl) ⟨166227, by rfl⟩ : syracuseStep 443273 = 332455) B332455
theorem B443369 : Blo 291829 443369 := bstep (se 2 (by rfl) ⟨166263, by rfl⟩ : syracuseStep 443369 = 332527) B332527
theorem B443375 : Blo 291829 443375 := bstep (se 1 (by rfl) ⟨332531, by rfl⟩ : syracuseStep 443375 = 665063) B665063
theorem B443483 : Blo 291829 443483 := bstep (se 1 (by rfl) ⟨332612, by rfl⟩ : syracuseStep 443483 = 665225) B665225
theorem B443519 : Blo 291829 443519 := bstep (se 1 (by rfl) ⟨332639, by rfl⟩ : syracuseStep 443519 = 665279) B665279
theorem B3327155 : Blo 291829 3327155 := bstep (se 1 (by rfl) ⟨2495366, by rfl⟩ : syracuseStep 3327155 = 4990733) B4990733
theorem B443657 : Blo 291829 443657 := bstep (se 2 (by rfl) ⟨166371, by rfl⟩ : syracuseStep 443657 = 332743) B332743
theorem B640487 : Blo 291829 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B706121 : Blo 291829 706121 := bstep (se 2 (by rfl) ⟨264795, by rfl⟩ : syracuseStep 706121 = 529591) B529591
theorem B1788925 : Blo 291829 1788925 := bstep (se 3 (by rfl) ⟨335423, by rfl⟩ : syracuseStep 1788925 = 670847) B670847
theorem B707609 : Blo 291829 707609 := bstep (se 2 (by rfl) ⟨265353, by rfl⟩ : syracuseStep 707609 = 530707) B530707
theorem B2542697 : Blo 291829 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B937327 : Blo 291829 937327 := bstep (se 1 (by rfl) ⟨702995, by rfl⟩ : syracuseStep 937327 = 1405991) B1405991
theorem B741089 : Blo 291829 741089 := bstep (se 2 (by rfl) ⟨277908, by rfl⟩ : syracuseStep 741089 = 555817) B555817
theorem B741545 : Blo 291829 741545 := bstep (se 2 (by rfl) ⟨278079, by rfl⟩ : syracuseStep 741545 = 556159) B556159
theorem B741919 : Blo 291829 741919 := bstep (se 1 (by rfl) ⟨556439, by rfl⟩ : syracuseStep 741919 = 1112879) B1112879
theorem B1496231 : Blo 291829 1496231 := bstep (se 1 (by rfl) ⟨1122173, by rfl⟩ : syracuseStep 1496231 = 2244347) B2244347
theorem B2808827 : Blo 291829 2808827 := bstep (se 1 (by rfl) ⟨2106620, by rfl⟩ : syracuseStep 2808827 = 4213241) B4213241
theorem B58350793 : Blo 291829 58350793 := bstep (se 2 (by rfl) ⟨21881547, by rfl⟩ : syracuseStep 58350793 = 43763095) B43763095
theorem B484847 : Blo 291829 484847 := bstep (se 1 (by rfl) ⟨363635, by rfl⟩ : syracuseStep 484847 = 727271) B727271
theorem B1664671 : Blo 291829 1664671 := bstep (se 1 (by rfl) ⟨1248503, by rfl⟩ : syracuseStep 1664671 = 2497007) B2497007
theorem B3335903 : Blo 291829 3335903 := bstep (se 1 (by rfl) ⟨2501927, by rfl⟩ : syracuseStep 3335903 = 5003855) B5003855
theorem B12871457 : Blo 291829 12871457 := bstep (se 2 (by rfl) ⟨4826796, by rfl⟩ : syracuseStep 12871457 = 9653593) B9653593
theorem B2221991 : Blo 291829 2221991 := bstep (se 1 (by rfl) ⟨1666493, by rfl⟩ : syracuseStep 2221991 = 3332987) B3332987
theorem B1108687 : Blo 291829 1108687 := bstep (se 1 (by rfl) ⟨831515, by rfl⟩ : syracuseStep 1108687 = 1663031) B1663031
theorem B748399 : Blo 291829 748399 := bstep (se 1 (by rfl) ⟨561299, by rfl⟩ : syracuseStep 748399 = 1122599) B1122599
theorem B945503 : Blo 291829 945503 := bstep (se 1 (by rfl) ⟨709127, by rfl⟩ : syracuseStep 945503 = 1418255) B1418255
theorem B5664329 : Blo 291829 5664329 := bstep (se 2 (by rfl) ⟨2124123, by rfl⟩ : syracuseStep 5664329 = 4248247) B4248247
theorem B2224421 : Blo 291829 2224421 := bstep (se 4 (by rfl) ⟨208539, by rfl⟩ : syracuseStep 2224421 = 417079) B417079
theorem B292063 : Blo 291829 292063 := bstep (se 1 (by rfl) ⟨219047, by rfl⟩ : syracuseStep 292063 = 438095) B438095
theorem B554215 : Blo 291829 554215 := bstep (se 1 (by rfl) ⟨415661, by rfl⟩ : syracuseStep 554215 = 831323) B831323
theorem B292383 : Blo 291829 292383 := bstep (se 1 (by rfl) ⟨219287, by rfl⟩ : syracuseStep 292383 = 438575) B438575
theorem B292399 : Blo 291829 292399 := bstep (se 1 (by rfl) ⟨219299, by rfl⟩ : syracuseStep 292399 = 438599) B438599
theorem B554663 : Blo 291829 554663 := bstep (se 1 (by rfl) ⟨415997, by rfl⟩ : syracuseStep 554663 = 831995) B831995
theorem B2258603 : Blo 291829 2258603 := bstep (se 1 (by rfl) ⟨1693952, by rfl⟩ : syracuseStep 2258603 = 3387905) B3387905
theorem B292543 : Blo 291829 292543 := bstep (se 1 (by rfl) ⟨219407, by rfl⟩ : syracuseStep 292543 = 438815) B438815
theorem B292967 : Blo 291829 292967 := bstep (se 1 (by rfl) ⟨219725, by rfl⟩ : syracuseStep 292967 = 439451) B439451
theorem B292975 : Blo 291829 292975 := bstep (se 1 (by rfl) ⟨219731, by rfl⟩ : syracuseStep 292975 = 439463) B439463
theorem B293543 : Blo 291829 293543 := bstep (se 1 (by rfl) ⟨220157, by rfl⟩ : syracuseStep 293543 = 440315) B440315
theorem B294047 : Blo 291829 294047 := bstep (se 1 (by rfl) ⟨220535, by rfl⟩ : syracuseStep 294047 = 441071) B441071
theorem B294555 : Blo 291829 294555 := bstep (se 1 (by rfl) ⟨220916, by rfl⟩ : syracuseStep 294555 = 441833) B441833
theorem B294607 : Blo 291829 294607 := bstep (se 1 (by rfl) ⟨220955, by rfl⟩ : syracuseStep 294607 = 441911) B441911
theorem B294959 : Blo 291829 294959 := bstep (se 1 (by rfl) ⟨221219, by rfl⟩ : syracuseStep 294959 = 442439) B442439
theorem B294975 : Blo 291829 294975 := bstep (se 1 (by rfl) ⟨221231, by rfl⟩ : syracuseStep 294975 = 442463) B442463
theorem B295079 : Blo 291829 295079 := bstep (se 1 (by rfl) ⟨221309, by rfl⟩ : syracuseStep 295079 = 442619) B442619
theorem B295239 : Blo 291829 295239 := bstep (se 1 (by rfl) ⟨221429, by rfl⟩ : syracuseStep 295239 = 442859) B442859
theorem B295423 : Blo 291829 295423 := bstep (se 1 (by rfl) ⟨221567, by rfl⟩ : syracuseStep 295423 = 443135) B443135
theorem B295515 : Blo 291829 295515 := bstep (se 1 (by rfl) ⟨221636, by rfl⟩ : syracuseStep 295515 = 443273) B443273
theorem B295579 : Blo 291829 295579 := bstep (se 1 (by rfl) ⟨221684, by rfl⟩ : syracuseStep 295579 = 443369) B443369
theorem B295583 : Blo 291829 295583 := bstep (se 1 (by rfl) ⟨221687, by rfl⟩ : syracuseStep 295583 = 443375) B443375
theorem B295655 : Blo 291829 295655 := bstep (se 1 (by rfl) ⟨221741, by rfl⟩ : syracuseStep 295655 = 443483) B443483
theorem B295679 : Blo 291829 295679 := bstep (se 1 (by rfl) ⟨221759, by rfl⟩ : syracuseStep 295679 = 443519) B443519
theorem B295771 : Blo 291829 295771 := bstep (se 1 (by rfl) ⟨221828, by rfl⟩ : syracuseStep 295771 = 443657) B443657
theorem B755369 : Blo 291829 755369 := bstep (se 2 (by rfl) ⟨283263, by rfl⟩ : syracuseStep 755369 = 566527) B566527
theorem B22939307 : Blo 291829 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B657161 : Blo 291829 657161 := bstep (se 2 (by rfl) ⟨246435, by rfl⟩ : syracuseStep 657161 = 492871) B492871
theorem B4261679 : Blo 291829 4261679 := bstep (se 1 (by rfl) ⟨3196259, by rfl⟩ : syracuseStep 4261679 = 6392519) B6392519
theorem B494059 : Blo 291829 494059 := bstep (se 1 (by rfl) ⟨370544, by rfl⟩ : syracuseStep 494059 = 741089) B741089
theorem B658151 : Blo 291829 658151 := bstep (se 1 (by rfl) ⟨493613, by rfl⟩ : syracuseStep 658151 = 987227) B987227
theorem B494363 : Blo 291829 494363 := bstep (se 1 (by rfl) ⟨370772, by rfl⟩ : syracuseStep 494363 = 741545) B741545
theorem B1117435 : Blo 291829 1117435 := bstep (se 1 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 1117435 = 1676153) B1676153
theorem B1478249 : Blo 291829 1478249 := bstep (se 2 (by rfl) ⟨554343, by rfl⟩ : syracuseStep 1478249 = 1108687) B1108687
theorem B1707965 : Blo 291829 1707965 := bstep (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) B640487
theorem B1249769 : Blo 291829 1249769 := bstep (se 2 (by rfl) ⟨468663, by rfl⟩ : syracuseStep 1249769 = 937327) B937327
theorem B660059 : Blo 291829 660059 := bstep (se 1 (by rfl) ⟨495044, by rfl⟩ : syracuseStep 660059 = 990089) B990089
theorem B1872551 : Blo 291829 1872551 := bstep (se 1 (by rfl) ⟨1404413, by rfl⟩ : syracuseStep 1872551 = 2808827) B2808827
theorem B660527 : Blo 291829 660527 := bstep (se 1 (by rfl) ⟨495395, by rfl⟩ : syracuseStep 660527 = 990791) B990791
theorem B1119683 : Blo 291829 1119683 := bstep (se 1 (by rfl) ⟨839762, by rfl⟩ : syracuseStep 1119683 = 1679525) B1679525
theorem B988847 : Blo 291829 988847 := bstep (se 1 (by rfl) ⟨741635, by rfl⟩ : syracuseStep 988847 = 1483271) B1483271
theorem B661391 : Blo 291829 661391 := bstep (se 1 (by rfl) ⟨496043, by rfl⟩ : syracuseStep 661391 = 992087) B992087
theorem B8067109 : Blo 291829 8067109 := bstep (se 4 (by rfl) ⟨756291, by rfl⟩ : syracuseStep 8067109 = 1512583) B1512583
theorem B989225 : Blo 291829 989225 := bstep (se 2 (by rfl) ⟨370959, by rfl⟩ : syracuseStep 989225 = 741919) B741919
theorem B661679 : Blo 291829 661679 := bstep (se 1 (by rfl) ⟨496259, by rfl⟩ : syracuseStep 661679 = 992519) B992519
theorem B1120823 : Blo 291829 1120823 := bstep (se 1 (by rfl) ⟨840617, by rfl⟩ : syracuseStep 1120823 = 1681235) B1681235
theorem B1481327 : Blo 291829 1481327 := bstep (se 1 (by rfl) ⟨1110995, by rfl⟩ : syracuseStep 1481327 = 2221991) B2221991
theorem B1121627 : Blo 291829 1121627 := bstep (se 1 (by rfl) ⟨841220, by rfl⟩ : syracuseStep 1121627 = 1682441) B1682441
theorem B662939 : Blo 291829 662939 := bstep (se 1 (by rfl) ⟨497204, by rfl⟩ : syracuseStep 662939 = 994409) B994409
theorem B662975 : Blo 291829 662975 := bstep (se 1 (by rfl) ⟨497231, by rfl⟩ : syracuseStep 662975 = 994463) B994463
theorem B1056311 : Blo 291829 1056311 := bstep (se 1 (by rfl) ⟨792233, by rfl⟩ : syracuseStep 1056311 = 1584467) B1584467
theorem B630335 : Blo 291829 630335 := bstep (se 1 (by rfl) ⟨472751, by rfl⟩ : syracuseStep 630335 = 945503) B945503
theorem B3776219 : Blo 291829 3776219 := bstep (se 1 (by rfl) ⟨2832164, by rfl⟩ : syracuseStep 3776219 = 5664329) B5664329
theorem B3350483 : Blo 291829 3350483 := bstep (se 1 (by rfl) ⟨2512862, by rfl⟩ : syracuseStep 3350483 = 5025725) B5025725
theorem B1482947 : Blo 291829 1482947 := bstep (se 1 (by rfl) ⟨1112210, by rfl⟩ : syracuseStep 1482947 = 2224421) B2224421
theorem B663803 : Blo 291829 663803 := bstep (se 1 (by rfl) ⟨497852, by rfl⟩ : syracuseStep 663803 = 995705) B995705
theorem B1122767 : Blo 291829 1122767 := bstep (se 1 (by rfl) ⟨842075, by rfl⟩ : syracuseStep 1122767 = 1684151) B1684151
theorem B664361 : Blo 291829 664361 := bstep (se 2 (by rfl) ⟨249135, by rfl⟩ : syracuseStep 664361 = 498271) B498271
theorem B369775 : Blo 291829 369775 := bstep (se 1 (by rfl) ⟨277331, by rfl⟩ : syracuseStep 369775 = 554663) B554663
theorem B3155431 : Blo 291829 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B77801057 : Blo 291829 77801057 := bstep (se 2 (by rfl) ⟨29175396, by rfl⟩ : syracuseStep 77801057 = 58350793) B58350793
theorem B994031 : Blo 291829 994031 := bstep (se 1 (by rfl) ⟨745523, by rfl⟩ : syracuseStep 994031 = 1491047) B1491047
theorem B1059799 : Blo 291829 1059799 := bstep (se 1 (by rfl) ⟨794849, by rfl⟩ : syracuseStep 1059799 = 1589699) B1589699
theorem B470747 : Blo 291829 470747 := bstep (se 1 (by rfl) ⟨353060, by rfl⟩ : syracuseStep 470747 = 706121) B706121
theorem B1486673 : Blo 291829 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B438215 : Blo 291829 438215 := bstep (se 1 (by rfl) ⟨328661, by rfl⟩ : syracuseStep 438215 = 657323) B657323
theorem B28422251 : Blo 291829 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B372919 : Blo 291829 372919 := bstep (se 1 (by rfl) ⟨279689, by rfl⟩ : syracuseStep 372919 = 559379) B559379
theorem B373339 : Blo 291829 373339 := bstep (se 1 (by rfl) ⟨280004, by rfl⟩ : syracuseStep 373339 = 560009) B560009
theorem B1487483 : Blo 291829 1487483 := bstep (se 1 (by rfl) ⟨1115612, by rfl⟩ : syracuseStep 1487483 = 2231225) B2231225
theorem B471739 : Blo 291829 471739 := bstep (se 1 (by rfl) ⟨353804, by rfl⟩ : syracuseStep 471739 = 707609) B707609
theorem B439721 : Blo 291829 439721 := bstep (se 2 (by rfl) ⟨164895, by rfl⟩ : syracuseStep 439721 = 329791) B329791
theorem B439871 : Blo 291829 439871 := bstep (se 1 (by rfl) ⟨329903, by rfl⟩ : syracuseStep 439871 = 659807) B659807
theorem B440297 : Blo 291829 440297 := bstep (se 2 (by rfl) ⟨165111, by rfl⟩ : syracuseStep 440297 = 330223) B330223
theorem B997487 : Blo 291829 997487 := bstep (se 1 (by rfl) ⟨748115, by rfl⟩ : syracuseStep 997487 = 1496231) B1496231
theorem B440489 : Blo 291829 440489 := bstep (se 2 (by rfl) ⟨165183, by rfl⟩ : syracuseStep 440489 = 330367) B330367
theorem B997865 : Blo 291829 997865 := bstep (se 2 (by rfl) ⟨374199, by rfl⟩ : syracuseStep 997865 = 748399) B748399
theorem B441647 : Blo 291829 441647 := bstep (se 1 (by rfl) ⟨331235, by rfl⟩ : syracuseStep 441647 = 662471) B662471
theorem B441839 : Blo 291829 441839 := bstep (se 1 (by rfl) ⟨331379, by rfl⟩ : syracuseStep 441839 = 662759) B662759
theorem B442415 : Blo 291829 442415 := bstep (se 1 (by rfl) ⟨331811, by rfl⟩ : syracuseStep 442415 = 663623) B663623
theorem B3818753 : Blo 291829 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B738953 : Blo 291829 738953 := bstep (se 2 (by rfl) ⟨277107, by rfl⟩ : syracuseStep 738953 = 554215) B554215
theorem B707051 : Blo 291829 707051 := bstep (se 1 (by rfl) ⟨530288, by rfl⟩ : syracuseStep 707051 = 1060577) B1060577
theorem B4737761 : Blo 291829 4737761 := bstep (se 2 (by rfl) ⟨1776660, by rfl⟩ : syracuseStep 4737761 = 3553321) B3553321
theorem B22859495 : Blo 291829 22859495 := bstep (se 1 (by rfl) ⟨17144621, by rfl⟩ : syracuseStep 22859495 = 34289243) B34289243
theorem B708839 : Blo 291829 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B5362157 : Blo 291829 5362157 := bstep (se 3 (by rfl) ⟨1005404, by rfl⟩ : syracuseStep 5362157 = 2010809) B2010809
theorem B742891 : Blo 291829 742891 := bstep (se 1 (by rfl) ⟨557168, by rfl⟩ : syracuseStep 742891 = 1114337) B1114337
theorem B4281947 : Blo 291829 4281947 := bstep (se 1 (by rfl) ⟨3211460, by rfl⟩ : syracuseStep 4281947 = 6422921) B6422921
theorem B2218103 : Blo 291829 2218103 := bstep (se 1 (by rfl) ⟨1663577, by rfl⟩ : syracuseStep 2218103 = 3327155) B3327155
theorem B2513105 : Blo 291829 2513105 := bstep (se 2 (by rfl) ⟨942414, by rfl⟩ : syracuseStep 2513105 = 1884829) B1884829
theorem B9329627 : Blo 291829 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B1695131 : Blo 291829 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B2219561 : Blo 291829 2219561 := bstep (se 2 (by rfl) ⟨832335, by rfl⟩ : syracuseStep 2219561 = 1664671) B1664671
theorem B2384093 : Blo 291829 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B2385233 : Blo 291829 2385233 := bstep (se 2 (by rfl) ⟨894462, by rfl⟩ : syracuseStep 2385233 = 1788925) B1788925
theorem B1010555 : Blo 291829 1010555 := bstep (se 1 (by rfl) ⟨757916, by rfl⟩ : syracuseStep 1010555 = 1515833) B1515833
theorem B323231 : Blo 291829 323231 := bstep (se 1 (by rfl) ⟨242423, by rfl⟩ : syracuseStep 323231 = 484847) B484847
theorem B1404647 : Blo 291829 1404647 := bstep (se 1 (by rfl) ⟨1053485, by rfl⟩ : syracuseStep 1404647 = 2106971) B2106971
theorem B2223935 : Blo 291829 2223935 := bstep (se 1 (by rfl) ⟨1667951, by rfl⟩ : syracuseStep 2223935 = 3335903) B3335903
theorem B8580971 : Blo 291829 8580971 := bstep (se 1 (by rfl) ⟨6435728, by rfl⟩ : syracuseStep 8580971 = 12871457) B12871457
theorem B1077491 : Blo 291829 1077491 := bstep (se 1 (by rfl) ⟨808118, by rfl⟩ : syracuseStep 1077491 = 1616237) B1616237
theorem B291871 : Blo 291829 291871 := bstep (se 1 (by rfl) ⟨218903, by rfl⟩ : syracuseStep 291871 = 437807) B437807
theorem B292319 : Blo 291829 292319 := bstep (se 1 (by rfl) ⟨219239, by rfl⟩ : syracuseStep 292319 = 438479) B438479
theorem B292635 : Blo 291829 292635 := bstep (se 1 (by rfl) ⟨219476, by rfl⟩ : syracuseStep 292635 = 438953) B438953
theorem B292895 : Blo 291829 292895 := bstep (se 1 (by rfl) ⟨219671, by rfl⟩ : syracuseStep 292895 = 439343) B439343
theorem B293191 : Blo 291829 293191 := bstep (se 1 (by rfl) ⟨219893, by rfl⟩ : syracuseStep 293191 = 439787) B439787
theorem B293275 : Blo 291829 293275 := bstep (se 1 (by rfl) ⟨219956, by rfl⟩ : syracuseStep 293275 = 439913) B439913
theorem B1505735 : Blo 291829 1505735 := bstep (se 1 (by rfl) ⟨1129301, by rfl⟩ : syracuseStep 1505735 = 2258603) B2258603
theorem B293375 : Blo 291829 293375 := bstep (se 1 (by rfl) ⟨220031, by rfl⟩ : syracuseStep 293375 = 440063) B440063
theorem B293583 : Blo 291829 293583 := bstep (se 1 (by rfl) ⟨220187, by rfl⟩ : syracuseStep 293583 = 440375) B440375
theorem B293631 : Blo 291829 293631 := bstep (se 1 (by rfl) ⟨220223, by rfl⟩ : syracuseStep 293631 = 440447) B440447
theorem B294127 : Blo 291829 294127 := bstep (se 1 (by rfl) ⟨220595, by rfl⟩ : syracuseStep 294127 = 441191) B441191
theorem B294191 : Blo 291829 294191 := bstep (se 1 (by rfl) ⟨220643, by rfl⟩ : syracuseStep 294191 = 441287) B441287
theorem B1408337 : Blo 291829 1408337 := bstep (se 2 (by rfl) ⟨528126, by rfl⟩ : syracuseStep 1408337 = 1056253) B1056253
theorem B1408873 : Blo 291829 1408873 := bstep (se 2 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 1408873 = 1056655) B1056655
theorem B294783 : Blo 291829 294783 := bstep (se 1 (by rfl) ⟨221087, by rfl⟩ : syracuseStep 294783 = 442175) B442175
theorem B294943 : Blo 291829 294943 := bstep (se 1 (by rfl) ⟨221207, by rfl⟩ : syracuseStep 294943 = 442415) B442415
theorem B492635 : Blo 291829 492635 := bstep (se 1 (by rfl) ⟨369476, by rfl⟩ : syracuseStep 492635 = 738953) B738953
theorem B493033 : Blo 291829 493033 := bstep (se 2 (by rfl) ⟨184887, by rfl⟩ : syracuseStep 493033 = 369775) B369775
theorem B329575 : Blo 291829 329575 := bstep (se 1 (by rfl) ⟨247181, by rfl⟩ : syracuseStep 329575 = 494363) B494363
theorem B985499 : Blo 291829 985499 := bstep (se 1 (by rfl) ⟨739124, by rfl⟩ : syracuseStep 985499 = 1478249) B1478249
theorem B15239663 : Blo 291829 15239663 := bstep (se 1 (by rfl) ⟨11429747, by rfl⟩ : syracuseStep 15239663 = 22859495) B22859495
theorem B1248367 : Blo 291829 1248367 := bstep (se 1 (by rfl) ⟨936275, by rfl⟩ : syracuseStep 1248367 = 1872551) B1872551
theorem B658745 : Blo 291829 658745 := bstep (se 2 (by rfl) ⟨247029, by rfl⟩ : syracuseStep 658745 = 494059) B494059
theorem B2854631 : Blo 291829 2854631 := bstep (se 1 (by rfl) ⟨2140973, by rfl⟩ : syracuseStep 2854631 = 4281947) B4281947
theorem B659231 : Blo 291829 659231 := bstep (se 1 (by rfl) ⟨494423, by rfl⟩ : syracuseStep 659231 = 988847) B988847
theorem B1413065 : Blo 291829 1413065 := bstep (se 2 (by rfl) ⟨529899, by rfl⟩ : syracuseStep 1413065 = 1059799) B1059799
theorem B659483 : Blo 291829 659483 := bstep (se 1 (by rfl) ⟨494612, by rfl⟩ : syracuseStep 659483 = 989225) B989225
theorem B1478735 : Blo 291829 1478735 := bstep (se 1 (by rfl) ⟨1109051, by rfl⟩ : syracuseStep 1478735 = 2218103) B2218103
theorem B1675403 : Blo 291829 1675403 := bstep (se 1 (by rfl) ⟨1256552, by rfl⟩ : syracuseStep 1675403 = 2513105) B2513105
theorem B987551 : Blo 291829 987551 := bstep (se 1 (by rfl) ⟨740663, by rfl⟩ : syracuseStep 987551 = 1481327) B1481327
theorem B1479707 : Blo 291829 1479707 := bstep (se 1 (by rfl) ⟨1109780, by rfl⟩ : syracuseStep 1479707 = 2219561) B2219561
theorem B2233655 : Blo 291829 2233655 := bstep (se 1 (by rfl) ⟨1675241, by rfl⟩ : syracuseStep 2233655 = 3350483) B3350483
theorem B988631 : Blo 291829 988631 := bstep (se 1 (by rfl) ⟨741473, by rfl⟩ : syracuseStep 988631 = 1482947) B1482947
theorem B497225 : Blo 291829 497225 := bstep (se 2 (by rfl) ⟨186459, by rfl⟩ : syracuseStep 497225 = 372919) B372919
theorem B497785 : Blo 291829 497785 := bstep (se 2 (by rfl) ⟨186669, by rfl⟩ : syracuseStep 497785 = 373339) B373339
theorem B628985 : Blo 291829 628985 := bstep (se 2 (by rfl) ⟨235869, by rfl⟩ : syracuseStep 628985 = 471739) B471739
theorem B662687 : Blo 291829 662687 := bstep (se 1 (by rfl) ⟨497015, by rfl⟩ : syracuseStep 662687 = 994031) B994031
theorem B990521 : Blo 291829 990521 := bstep (se 2 (by rfl) ⟨371445, by rfl⟩ : syracuseStep 990521 = 742891) B742891
theorem B1482623 : Blo 291829 1482623 := bstep (se 1 (by rfl) ⟨1111967, by rfl⟩ : syracuseStep 1482623 = 2223935) B2223935
theorem B991115 : Blo 291829 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B24879005 : Blo 291829 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B10756145 : Blo 291829 10756145 := bstep (se 2 (by rfl) ⟨4033554, by rfl⟩ : syracuseStep 10756145 = 8067109) B8067109
theorem B18948167 : Blo 291829 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B991655 : Blo 291829 991655 := bstep (se 1 (by rfl) ⟨743741, by rfl⟩ : syracuseStep 991655 = 1487483) B1487483
theorem B664991 : Blo 291829 664991 := bstep (se 1 (by rfl) ⟨498743, by rfl⟩ : syracuseStep 664991 = 997487) B997487
theorem B665243 : Blo 291829 665243 := bstep (se 1 (by rfl) ⟨498932, by rfl⟩ : syracuseStep 665243 = 997865) B997865
theorem B861949 : Blo 291829 861949 := bstep (se 3 (by rfl) ⟨161615, by rfl⟩ : syracuseStep 861949 = 323231) B323231
theorem B1878497 : Blo 291829 1878497 := bstep (se 2 (by rfl) ⟨704436, by rfl⟩ : syracuseStep 1878497 = 1408873) B1408873
theorem B503579 : Blo 291829 503579 := bstep (se 1 (by rfl) ⟨377684, by rfl⟩ : syracuseStep 503579 = 755369) B755369
theorem B438107 : Blo 291829 438107 := bstep (se 1 (by rfl) ⟨328580, by rfl⟩ : syracuseStep 438107 = 657161) B657161
theorem B14299085 : Blo 291829 14299085 := bstep (se 3 (by rfl) ⟨2681078, by rfl⟩ : syracuseStep 14299085 = 5362157) B5362157
theorem B471367 : Blo 291829 471367 := bstep (se 1 (by rfl) ⟨353525, by rfl⟩ : syracuseStep 471367 = 707051) B707051
theorem B3158507 : Blo 291829 3158507 := bstep (se 1 (by rfl) ⟨2368880, by rfl⟩ : syracuseStep 3158507 = 4737761) B4737761
theorem B438767 : Blo 291829 438767 := bstep (se 1 (by rfl) ⟨329075, by rfl⟩ : syracuseStep 438767 = 658151) B658151
theorem B4207241 : Blo 291829 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B472559 : Blo 291829 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B833179 : Blo 291829 833179 := bstep (se 1 (by rfl) ⟨624884, by rfl⟩ : syracuseStep 833179 = 1249769) B1249769
theorem B440039 : Blo 291829 440039 := bstep (se 1 (by rfl) ⟨330029, by rfl⟩ : syracuseStep 440039 = 660059) B660059
theorem B440351 : Blo 291829 440351 := bstep (se 1 (by rfl) ⟨330263, by rfl⟩ : syracuseStep 440351 = 660527) B660527
theorem B440927 : Blo 291829 440927 := bstep (se 1 (by rfl) ⟨330695, by rfl⟩ : syracuseStep 440927 = 661391) B661391
theorem B441119 : Blo 291829 441119 := bstep (se 1 (by rfl) ⟨330839, by rfl⟩ : syracuseStep 441119 = 661679) B661679
theorem B1489913 : Blo 291829 1489913 := bstep (se 2 (by rfl) ⟨558717, by rfl⟩ : syracuseStep 1489913 = 1117435) B1117435
theorem B1130087 : Blo 291829 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B441959 : Blo 291829 441959 := bstep (se 1 (by rfl) ⟨331469, by rfl⟩ : syracuseStep 441959 = 662939) B662939
theorem B441983 : Blo 291829 441983 := bstep (se 1 (by rfl) ⟨331487, by rfl⟩ : syracuseStep 441983 = 662975) B662975
theorem B704207 : Blo 291829 704207 := bstep (se 1 (by rfl) ⟨528155, by rfl⟩ : syracuseStep 704207 = 1056311) B1056311
theorem B1589395 : Blo 291829 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B442535 : Blo 291829 442535 := bstep (se 1 (by rfl) ⟨331901, by rfl⟩ : syracuseStep 442535 = 663803) B663803
theorem B442907 : Blo 291829 442907 := bstep (se 1 (by rfl) ⟨332180, by rfl⟩ : syracuseStep 442907 = 664361) B664361
theorem B1590155 : Blo 291829 1590155 := bstep (se 1 (by rfl) ⟨1192616, by rfl⟩ : syracuseStep 1590155 = 2385233) B2385233
theorem B673703 : Blo 291829 673703 := bstep (se 1 (by rfl) ⟨505277, by rfl⟩ : syracuseStep 673703 = 1010555) B1010555
theorem B313831 : Blo 291829 313831 := bstep (se 1 (by rfl) ⟨235373, by rfl⟩ : syracuseStep 313831 = 470747) B470747
theorem B936431 : Blo 291829 936431 := bstep (se 1 (by rfl) ⟨702323, by rfl⟩ : syracuseStep 936431 = 1404647) B1404647
theorem B5720647 : Blo 291829 5720647 := bstep (se 1 (by rfl) ⟨4290485, by rfl⟩ : syracuseStep 5720647 = 8580971) B8580971
theorem B1003823 : Blo 291829 1003823 := bstep (se 1 (by rfl) ⟨752867, by rfl⟩ : syracuseStep 1003823 = 1505735) B1505735
theorem B938891 : Blo 291829 938891 := bstep (se 1 (by rfl) ⟨704168, by rfl⟩ : syracuseStep 938891 = 1408337) B1408337
theorem B2545835 : Blo 291829 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B15292871 : Blo 291829 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B2841119 : Blo 291829 2841119 := bstep (se 1 (by rfl) ⟨2130839, by rfl⟩ : syracuseStep 2841119 = 4261679) B4261679
theorem B1138643 : Blo 291829 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B746455 : Blo 291829 746455 := bstep (se 1 (by rfl) ⟨559841, by rfl⟩ : syracuseStep 746455 = 1119683) B1119683
theorem B747215 : Blo 291829 747215 := bstep (se 1 (by rfl) ⟨560411, by rfl⟩ : syracuseStep 747215 = 1120823) B1120823
theorem B747751 : Blo 291829 747751 := bstep (se 1 (by rfl) ⟨560813, by rfl⟩ : syracuseStep 747751 = 1121627) B1121627
theorem B420223 : Blo 291829 420223 := bstep (se 1 (by rfl) ⟨315167, by rfl⟩ : syracuseStep 420223 = 630335) B630335
theorem B2517479 : Blo 291829 2517479 := bstep (se 1 (by rfl) ⟨1888109, by rfl⟩ : syracuseStep 2517479 = 3776219) B3776219
theorem B748511 : Blo 291829 748511 := bstep (se 1 (by rfl) ⟨561383, by rfl⟩ : syracuseStep 748511 = 1122767) B1122767
theorem B51867371 : Blo 291829 51867371 := bstep (se 1 (by rfl) ⟨38900528, by rfl⟩ : syracuseStep 51867371 = 77801057) B77801057
theorem B292143 : Blo 291829 292143 := bstep (se 1 (by rfl) ⟨219107, by rfl⟩ : syracuseStep 292143 = 438215) B438215
theorem B718327 : Blo 291829 718327 := bstep (se 1 (by rfl) ⟨538745, by rfl⟩ : syracuseStep 718327 = 1077491) B1077491
theorem B293147 : Blo 291829 293147 := bstep (se 1 (by rfl) ⟨219860, by rfl⟩ : syracuseStep 293147 = 439721) B439721
theorem B293247 : Blo 291829 293247 := bstep (se 1 (by rfl) ⟨219935, by rfl⟩ : syracuseStep 293247 = 439871) B439871
theorem B293531 : Blo 291829 293531 := bstep (se 1 (by rfl) ⟨220148, by rfl⟩ : syracuseStep 293531 = 440297) B440297
theorem B293659 : Blo 291829 293659 := bstep (se 1 (by rfl) ⟨220244, by rfl⟩ : syracuseStep 293659 = 440489) B440489
theorem B294431 : Blo 291829 294431 := bstep (se 1 (by rfl) ⟨220823, by rfl⟩ : syracuseStep 294431 = 441647) B441647
theorem B294559 : Blo 291829 294559 := bstep (se 1 (by rfl) ⟨220919, by rfl⟩ : syracuseStep 294559 = 441839) B441839
theorem B295023 : Blo 291829 295023 := bstep (se 1 (by rfl) ⟨221267, by rfl⟩ : syracuseStep 295023 = 442535) B442535
theorem B295271 : Blo 291829 295271 := bstep (se 1 (by rfl) ⟨221453, by rfl⟩ : syracuseStep 295271 = 442907) B442907
theorem B328423 : Blo 291829 328423 := bstep (se 1 (by rfl) ⟨246317, by rfl⟩ : syracuseStep 328423 = 492635) B492635
theorem B656999 : Blo 291829 656999 := bstep (se 1 (by rfl) ⟨492749, by rfl⟩ : syracuseStep 656999 = 985499) B985499
theorem B624287 : Blo 291829 624287 := bstep (se 1 (by rfl) ⟨468215, by rfl⟩ : syracuseStep 624287 = 936431) B936431
theorem B10159775 : Blo 291829 10159775 := bstep (se 1 (by rfl) ⟨7619831, by rfl⟩ : syracuseStep 10159775 = 15239663) B15239663
theorem B657377 : Blo 291829 657377 := bstep (se 2 (by rfl) ⟨246516, by rfl⟩ : syracuseStep 657377 = 493033) B493033
theorem B1149265 : Blo 291829 1149265 := bstep (se 2 (by rfl) ⟨430974, by rfl⟩ : syracuseStep 1149265 = 861949) B861949
theorem B1903087 : Blo 291829 1903087 := bstep (se 1 (by rfl) ⟨1427315, by rfl⟩ : syracuseStep 1903087 = 2854631) B2854631
theorem B985823 : Blo 291829 985823 := bstep (se 1 (by rfl) ⟨739367, by rfl⟩ : syracuseStep 985823 = 1478735) B1478735
theorem B1116935 : Blo 291829 1116935 := bstep (se 1 (by rfl) ⟨837701, by rfl⟩ : syracuseStep 1116935 = 1675403) B1675403
theorem B658367 : Blo 291829 658367 := bstep (se 1 (by rfl) ⟨493775, by rfl⟩ : syracuseStep 658367 = 987551) B987551
theorem B560297 : Blo 291829 560297 := bstep (se 2 (by rfl) ⟨210111, by rfl⟩ : syracuseStep 560297 = 420223) B420223
theorem B625927 : Blo 291829 625927 := bstep (se 1 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 625927 = 938891) B938891
theorem B986471 : Blo 291829 986471 := bstep (se 1 (by rfl) ⟨739853, by rfl⟩ : syracuseStep 986471 = 1479707) B1479707
theorem B659087 : Blo 291829 659087 := bstep (se 1 (by rfl) ⟨494315, by rfl⟩ : syracuseStep 659087 = 988631) B988631
theorem B331483 : Blo 291829 331483 := bstep (se 1 (by rfl) ⟨248612, by rfl⟩ : syracuseStep 331483 = 497225) B497225
theorem B10195247 : Blo 291829 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B660347 : Blo 291829 660347 := bstep (se 1 (by rfl) ⟨495260, by rfl⟩ : syracuseStep 660347 = 990521) B990521
theorem B988415 : Blo 291829 988415 := bstep (se 1 (by rfl) ⟨741311, by rfl⟩ : syracuseStep 988415 = 1482623) B1482623
theorem B660743 : Blo 291829 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B16586003 : Blo 291829 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B759095 : Blo 291829 759095 := bstep (se 1 (by rfl) ⟨569321, by rfl⟩ : syracuseStep 759095 = 1138643) B1138643
theorem B661103 : Blo 291829 661103 := bstep (se 1 (by rfl) ⟨495827, by rfl⟩ : syracuseStep 661103 = 991655) B991655
theorem B628489 : Blo 291829 628489 := bstep (se 2 (by rfl) ⟨235683, by rfl⟩ : syracuseStep 628489 = 471367) B471367
theorem B6788893 : Blo 291829 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B1677293 : Blo 291829 1677293 := bstep (se 3 (by rfl) ⟨314492, by rfl⟩ : syracuseStep 1677293 = 628985) B628985
theorem B498143 : Blo 291829 498143 := bstep (se 1 (by rfl) ⟨373607, by rfl⟩ : syracuseStep 498143 = 747215) B747215
theorem B1252331 : Blo 291829 1252331 := bstep (se 1 (by rfl) ⟨939248, by rfl⟩ : syracuseStep 1252331 = 1878497) B1878497
theorem B1678319 : Blo 291829 1678319 := bstep (se 1 (by rfl) ⟨1258739, by rfl⟩ : syracuseStep 1678319 = 2517479) B2517479
theorem B499007 : Blo 291829 499007 := bstep (se 1 (by rfl) ⟨374255, by rfl⟩ : syracuseStep 499007 = 748511) B748511
theorem B34578247 : Blo 291829 34578247 := bstep (se 1 (by rfl) ⟨25933685, by rfl⟩ : syracuseStep 34578247 = 51867371) B51867371
theorem B335719 : Blo 291829 335719 := bstep (se 1 (by rfl) ⟨251789, by rfl⟩ : syracuseStep 335719 = 503579) B503579
theorem B663713 : Blo 291829 663713 := bstep (se 2 (by rfl) ⟨248892, by rfl⟩ : syracuseStep 663713 = 497785) B497785
theorem B2105671 : Blo 291829 2105671 := bstep (se 1 (by rfl) ⟨1579253, by rfl⟩ : syracuseStep 2105671 = 3158507) B3158507
theorem B993275 : Blo 291829 993275 := bstep (se 1 (by rfl) ⟨744956, by rfl⟩ : syracuseStep 993275 = 1489913) B1489913
theorem B469471 : Blo 291829 469471 := bstep (se 1 (by rfl) ⟨352103, by rfl⟩ : syracuseStep 469471 = 704207) B704207
theorem B1060103 : Blo 291829 1060103 := bstep (se 1 (by rfl) ⟨795077, by rfl⟩ : syracuseStep 1060103 = 1590155) B1590155
theorem B995273 : Blo 291829 995273 := bstep (se 2 (by rfl) ⟨373227, by rfl⟩ : syracuseStep 995273 = 746455) B746455
theorem B11219309 : Blo 291829 11219309 := bstep (se 3 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 11219309 = 4207241) B4207241
theorem B439163 : Blo 291829 439163 := bstep (se 1 (by rfl) ⟨329372, by rfl⟩ : syracuseStep 439163 = 658745) B658745
theorem B439433 : Blo 291829 439433 := bstep (se 2 (by rfl) ⟨164787, by rfl⟩ : syracuseStep 439433 = 329575) B329575
theorem B439487 : Blo 291829 439487 := bstep (se 1 (by rfl) ⟨329615, by rfl⟩ : syracuseStep 439487 = 659231) B659231
theorem B439655 : Blo 291829 439655 := bstep (se 1 (by rfl) ⟨329741, by rfl⟩ : syracuseStep 439655 = 659483) B659483
theorem B669215 : Blo 291829 669215 := bstep (se 1 (by rfl) ⟨501911, by rfl⟩ : syracuseStep 669215 = 1003823) B1003823
theorem B997001 : Blo 291829 997001 := bstep (se 2 (by rfl) ⟨373875, by rfl⟩ : syracuseStep 997001 = 747751) B747751
theorem B1489103 : Blo 291829 1489103 := bstep (se 1 (by rfl) ⟨1116827, by rfl⟩ : syracuseStep 1489103 = 2233655) B2233655
theorem B1260157 : Blo 291829 1260157 := bstep (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) B472559
theorem B441791 : Blo 291829 441791 := bstep (se 1 (by rfl) ⟨331343, by rfl⟩ : syracuseStep 441791 = 662687) B662687
theorem B12632111 : Blo 291829 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B443327 : Blo 291829 443327 := bstep (se 1 (by rfl) ⟨332495, by rfl⟩ : syracuseStep 443327 = 664991) B664991
theorem B443495 : Blo 291829 443495 := bstep (se 1 (by rfl) ⟨332621, by rfl⟩ : syracuseStep 443495 = 665243) B665243
theorem B2119193 : Blo 291829 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B449135 : Blo 291829 449135 := bstep (se 1 (by rfl) ⟨336851, by rfl⟩ : syracuseStep 449135 = 673703) B673703
theorem B942043 : Blo 291829 942043 := bstep (se 1 (by rfl) ⟨706532, by rfl⟩ : syracuseStep 942043 = 1413065) B1413065
theorem B418441 : Blo 291829 418441 := bstep (se 2 (by rfl) ⟨156915, by rfl⟩ : syracuseStep 418441 = 313831) B313831
theorem B7627529 : Blo 291829 7627529 := bstep (se 2 (by rfl) ⟨2860323, by rfl⟩ : syracuseStep 7627529 = 5720647) B5720647
theorem B1664489 : Blo 291829 1664489 := bstep (se 2 (by rfl) ⟨624183, by rfl⟩ : syracuseStep 1664489 = 1248367) B1248367
theorem B1894079 : Blo 291829 1894079 := bstep (se 1 (by rfl) ⟨1420559, by rfl⟩ : syracuseStep 1894079 = 2841119) B2841119
theorem B7170763 : Blo 291829 7170763 := bstep (se 1 (by rfl) ⟨5378072, by rfl⟩ : syracuseStep 7170763 = 10756145) B10756145
theorem B1110905 : Blo 291829 1110905 := bstep (se 2 (by rfl) ⟨416589, by rfl⟩ : syracuseStep 1110905 = 833179) B833179
theorem B292071 : Blo 291829 292071 := bstep (se 1 (by rfl) ⟨219053, by rfl⟩ : syracuseStep 292071 = 438107) B438107
theorem B3831077 : Blo 291829 3831077 := bstep (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) B718327
theorem B9532723 : Blo 291829 9532723 := bstep (se 1 (by rfl) ⟨7149542, by rfl⟩ : syracuseStep 9532723 = 14299085) B14299085
theorem B292511 : Blo 291829 292511 := bstep (se 1 (by rfl) ⟨219383, by rfl⟩ : syracuseStep 292511 = 438767) B438767
theorem B293359 : Blo 291829 293359 := bstep (se 1 (by rfl) ⟨220019, by rfl⟩ : syracuseStep 293359 = 440039) B440039
theorem B293567 : Blo 291829 293567 := bstep (se 1 (by rfl) ⟨220175, by rfl⟩ : syracuseStep 293567 = 440351) B440351
theorem B293951 : Blo 291829 293951 := bstep (se 1 (by rfl) ⟨220463, by rfl⟩ : syracuseStep 293951 = 440927) B440927
theorem B294079 : Blo 291829 294079 := bstep (se 1 (by rfl) ⟨220559, by rfl⟩ : syracuseStep 294079 = 441119) B441119
theorem B753391 : Blo 291829 753391 := bstep (se 1 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 753391 = 1130087) B1130087
theorem B294639 : Blo 291829 294639 := bstep (se 1 (by rfl) ⟨220979, by rfl⟩ : syracuseStep 294639 = 441959) B441959
theorem B294655 : Blo 291829 294655 := bstep (se 1 (by rfl) ⟨220991, by rfl⟩ : syracuseStep 294655 = 441983) B441983
theorem B8421407 : Blo 291829 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B295551 : Blo 291829 295551 := bstep (se 1 (by rfl) ⟨221663, by rfl⟩ : syracuseStep 295551 = 443327) B443327
theorem B295663 : Blo 291829 295663 := bstep (se 1 (by rfl) ⟨221747, by rfl⟩ : syracuseStep 295663 = 443495) B443495
theorem B557921 : Blo 291829 557921 := bstep (se 2 (by rfl) ⟨209220, by rfl⟩ : syracuseStep 557921 = 418441) B418441
theorem B657215 : Blo 291829 657215 := bstep (se 1 (by rfl) ⟨492911, by rfl⟩ : syracuseStep 657215 = 985823) B985823
theorem B657647 : Blo 291829 657647 := bstep (se 1 (by rfl) ⟨493235, by rfl⟩ : syracuseStep 657647 = 986471) B986471
theorem B625961 : Blo 291829 625961 := bstep (se 2 (by rfl) ⟨234735, by rfl⟩ : syracuseStep 625961 = 469471) B469471
theorem B658943 : Blo 291829 658943 := bstep (se 1 (by rfl) ⟨494207, by rfl⟩ : syracuseStep 658943 = 988415) B988415
theorem B1412795 : Blo 291829 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B1118195 : Blo 291829 1118195 := bstep (se 1 (by rfl) ⟨838646, by rfl⟩ : syracuseStep 1118195 = 1677293) B1677293
theorem B332095 : Blo 291829 332095 := bstep (se 1 (by rfl) ⟨249071, by rfl⟩ : syracuseStep 332095 = 498143) B498143
theorem B299423 : Blo 291829 299423 := bstep (se 1 (by rfl) ⟨224567, by rfl⟩ : syracuseStep 299423 = 449135) B449135
theorem B1118879 : Blo 291829 1118879 := bstep (se 1 (by rfl) ⟨839159, by rfl⟩ : syracuseStep 1118879 = 1678319) B1678319
theorem B332671 : Blo 291829 332671 := bstep (se 1 (by rfl) ⟨249503, by rfl⟩ : syracuseStep 332671 = 499007) B499007
theorem B5085019 : Blo 291829 5085019 := bstep (se 1 (by rfl) ⟨3813764, by rfl⟩ : syracuseStep 5085019 = 7627529) B7627529
theorem B662183 : Blo 291829 662183 := bstep (se 1 (by rfl) ⟨496637, by rfl⟩ : syracuseStep 662183 = 993275) B993275
theorem B9051857 : Blo 291829 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B663515 : Blo 291829 663515 := bstep (se 1 (by rfl) ⟨497636, by rfl⟩ : syracuseStep 663515 = 995273) B995273
theorem B7479539 : Blo 291829 7479539 := bstep (se 1 (by rfl) ⟨5609654, by rfl⟩ : syracuseStep 7479539 = 11219309) B11219309
theorem B1680209 : Blo 291829 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B664667 : Blo 291829 664667 := bstep (se 1 (by rfl) ⟨498500, by rfl⟩ : syracuseStep 664667 = 997001) B997001
theorem B3351941 : Blo 291829 3351941 := bstep (se 4 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 3351941 = 628489) B628489
theorem B992735 : Blo 291829 992735 := bstep (se 1 (by rfl) ⟨744551, by rfl⟩ : syracuseStep 992735 = 1489103) B1489103
theorem B1256057 : Blo 291829 1256057 := bstep (se 2 (by rfl) ⟨471021, by rfl⟩ : syracuseStep 1256057 = 942043) B942043
theorem B437897 : Blo 291829 437897 := bstep (se 2 (by rfl) ⟨164211, by rfl⟩ : syracuseStep 437897 = 328423) B328423
theorem B437999 : Blo 291829 437999 := bstep (se 1 (by rfl) ⟨328499, by rfl⟩ : syracuseStep 437999 = 656999) B656999
theorem B438251 : Blo 291829 438251 := bstep (se 1 (by rfl) ⟨328688, by rfl⟩ : syracuseStep 438251 = 657377) B657377
theorem B438911 : Blo 291829 438911 := bstep (se 1 (by rfl) ⟨329183, by rfl⟩ : syracuseStep 438911 = 658367) B658367
theorem B439391 : Blo 291829 439391 := bstep (se 1 (by rfl) ⟨329543, by rfl⟩ : syracuseStep 439391 = 659087) B659087
theorem B6796831 : Blo 291829 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B440231 : Blo 291829 440231 := bstep (se 1 (by rfl) ⟨330173, by rfl⟩ : syracuseStep 440231 = 660347) B660347
theorem B440495 : Blo 291829 440495 := bstep (se 1 (by rfl) ⟨330371, by rfl⟩ : syracuseStep 440495 = 660743) B660743
theorem B506063 : Blo 291829 506063 := bstep (se 1 (by rfl) ⟨379547, by rfl⟩ : syracuseStep 506063 = 759095) B759095
theorem B440735 : Blo 291829 440735 := bstep (se 1 (by rfl) ⟨330551, by rfl⟩ : syracuseStep 440735 = 661103) B661103
theorem B834569 : Blo 291829 834569 := bstep (se 2 (by rfl) ⟨312963, by rfl⟩ : syracuseStep 834569 = 625927) B625927
theorem B834887 : Blo 291829 834887 := bstep (se 1 (by rfl) ⟨626165, by rfl⟩ : syracuseStep 834887 = 1252331) B1252331
theorem B441977 : Blo 291829 441977 := bstep (se 2 (by rfl) ⟨165741, by rfl⟩ : syracuseStep 441977 = 331483) B331483
theorem B442475 : Blo 291829 442475 := bstep (se 1 (by rfl) ⟨331856, by rfl⟩ : syracuseStep 442475 = 663713) B663713
theorem B1262719 : Blo 291829 1262719 := bstep (se 1 (by rfl) ⟨947039, by rfl⟩ : syracuseStep 1262719 = 1894079) B1894079
theorem B706735 : Blo 291829 706735 := bstep (se 1 (by rfl) ⟨530051, by rfl⟩ : syracuseStep 706735 = 1060103) B1060103
theorem B1494125 : Blo 291829 1494125 := bstep (se 3 (by rfl) ⟨280148, by rfl⟩ : syracuseStep 1494125 = 560297) B560297
theorem B740603 : Blo 291829 740603 := bstep (se 1 (by rfl) ⟨555452, by rfl⟩ : syracuseStep 740603 = 1110905) B1110905
theorem B446143 : Blo 291829 446143 := bstep (se 1 (by rfl) ⟨334607, by rfl⟩ : syracuseStep 446143 = 669215) B669215
theorem B1004521 : Blo 291829 1004521 := bstep (se 2 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 1004521 = 753391) B753391
theorem B447625 : Blo 291829 447625 := bstep (se 2 (by rfl) ⟨167859, by rfl⟩ : syracuseStep 447625 = 335719) B335719
theorem B2807561 : Blo 291829 2807561 := bstep (se 2 (by rfl) ⟨1052835, by rfl⟩ : syracuseStep 2807561 = 2105671) B2105671
theorem B416191 : Blo 291829 416191 := bstep (se 1 (by rfl) ⟨312143, by rfl⟩ : syracuseStep 416191 = 624287) B624287
theorem B6773183 : Blo 291829 6773183 := bstep (se 1 (by rfl) ⟨5079887, by rfl⟩ : syracuseStep 6773183 = 10159775) B10159775
theorem B744623 : Blo 291829 744623 := bstep (se 1 (by rfl) ⟨558467, by rfl⟩ : syracuseStep 744623 = 1116935) B1116935
theorem B10149797 : Blo 291829 10149797 := bstep (se 4 (by rfl) ⟨951543, by rfl⟩ : syracuseStep 10149797 = 1903087) B1903087
theorem B1532353 : Blo 291829 1532353 := bstep (se 2 (by rfl) ⟨574632, by rfl⟩ : syracuseStep 1532353 = 1149265) B1149265
theorem B44229341 : Blo 291829 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B9561017 : Blo 291829 9561017 := bstep (se 2 (by rfl) ⟨3585381, by rfl⟩ : syracuseStep 9561017 = 7170763) B7170763
theorem B1109659 : Blo 291829 1109659 := bstep (se 1 (by rfl) ⟨832244, by rfl⟩ : syracuseStep 1109659 = 1664489) B1664489
theorem B12710297 : Blo 291829 12710297 := bstep (se 2 (by rfl) ⟨4766361, by rfl⟩ : syracuseStep 12710297 = 9532723) B9532723
theorem B292775 : Blo 291829 292775 := bstep (se 1 (by rfl) ⟨219581, by rfl⟩ : syracuseStep 292775 = 439163) B439163
theorem B292955 : Blo 291829 292955 := bstep (se 1 (by rfl) ⟨219716, by rfl⟩ : syracuseStep 292955 = 439433) B439433
theorem B292991 : Blo 291829 292991 := bstep (se 1 (by rfl) ⟨219743, by rfl⟩ : syracuseStep 292991 = 439487) B439487
theorem B2554051 : Blo 291829 2554051 := bstep (se 1 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 2554051 = 3831077) B3831077
theorem B293103 : Blo 291829 293103 := bstep (se 1 (by rfl) ⟨219827, by rfl⟩ : syracuseStep 293103 = 439655) B439655
theorem B294527 : Blo 291829 294527 := bstep (se 1 (by rfl) ⟨220895, by rfl⟩ : syracuseStep 294527 = 441791) B441791
theorem B46104329 : Blo 291829 46104329 := bstep (se 2 (by rfl) ⟨17289123, by rfl⟩ : syracuseStep 46104329 = 34578247) B34578247
theorem B294983 : Blo 291829 294983 := bstep (se 1 (by rfl) ⟨221237, by rfl⟩ : syracuseStep 294983 = 442475) B442475
theorem B493735 : Blo 291829 493735 := bstep (se 1 (by rfl) ⟨370301, by rfl⟩ : syracuseStep 493735 = 740603) B740603
theorem B1871707 : Blo 291829 1871707 := bstep (se 1 (by rfl) ⟨1403780, by rfl⟩ : syracuseStep 1871707 = 2807561) B2807561
theorem B496415 : Blo 291829 496415 := bstep (se 1 (by rfl) ⟨372311, by rfl⟩ : syracuseStep 496415 = 744623) B744623
theorem B1479545 : Blo 291829 1479545 := bstep (se 2 (by rfl) ⟨554829, by rfl⟩ : syracuseStep 1479545 = 1109659) B1109659
theorem B594857 : Blo 291829 594857 := bstep (se 2 (by rfl) ⟨223071, by rfl⟩ : syracuseStep 594857 = 446143) B446143
theorem B6034571 : Blo 291829 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B4986359 : Blo 291829 4986359 := bstep (se 1 (by rfl) ⟨3739769, by rfl⟩ : syracuseStep 4986359 = 7479539) B7479539
theorem B1120139 : Blo 291829 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B2234627 : Blo 291829 2234627 := bstep (se 1 (by rfl) ⟨1675970, by rfl⟩ : syracuseStep 2234627 = 3351941) B3351941
theorem B661823 : Blo 291829 661823 := bstep (se 1 (by rfl) ⟨496367, by rfl⟩ : syracuseStep 661823 = 992735) B992735
theorem B337375 : Blo 291829 337375 := bstep (se 1 (by rfl) ⟨253031, by rfl⟩ : syracuseStep 337375 = 506063) B506063
theorem B5614271 : Blo 291829 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B371947 : Blo 291829 371947 := bstep (se 1 (by rfl) ⟨278960, by rfl⟩ : syracuseStep 371947 = 557921) B557921
theorem B2043137 : Blo 291829 2043137 := bstep (se 2 (by rfl) ⟨766176, by rfl⟩ : syracuseStep 2043137 = 1532353) B1532353
theorem B798461 : Blo 291829 798461 := bstep (se 3 (by rfl) ⟨149711, by rfl⟩ : syracuseStep 798461 = 299423) B299423
theorem B438143 : Blo 291829 438143 := bstep (se 1 (by rfl) ⟨328607, by rfl⟩ : syracuseStep 438143 = 657215) B657215
theorem B438431 : Blo 291829 438431 := bstep (se 1 (by rfl) ⟨328823, by rfl⟩ : syracuseStep 438431 = 657647) B657647
theorem B1683625 : Blo 291829 1683625 := bstep (se 2 (by rfl) ⟨631359, by rfl⟩ : syracuseStep 1683625 = 1262719) B1262719
theorem B996083 : Blo 291829 996083 := bstep (se 1 (by rfl) ⟨747062, by rfl⟩ : syracuseStep 996083 = 1494125) B1494125
theorem B439295 : Blo 291829 439295 := bstep (se 1 (by rfl) ⟨329471, by rfl⟩ : syracuseStep 439295 = 658943) B658943
theorem B441455 : Blo 291829 441455 := bstep (se 1 (by rfl) ⟨331091, by rfl⟩ : syracuseStep 441455 = 662183) B662183
theorem B442343 : Blo 291829 442343 := bstep (se 1 (by rfl) ⟨331757, by rfl⟩ : syracuseStep 442343 = 663515) B663515
theorem B442793 : Blo 291829 442793 := bstep (se 2 (by rfl) ⟨166047, by rfl⟩ : syracuseStep 442793 = 332095) B332095
theorem B6374011 : Blo 291829 6374011 := bstep (se 1 (by rfl) ⟨4780508, by rfl⟩ : syracuseStep 6374011 = 9561017) B9561017
theorem B443111 : Blo 291829 443111 := bstep (se 1 (by rfl) ⟨332333, by rfl⟩ : syracuseStep 443111 = 664667) B664667
theorem B443561 : Blo 291829 443561 := bstep (se 2 (by rfl) ⟨166335, by rfl⟩ : syracuseStep 443561 = 332671) B332671
theorem B837371 : Blo 291829 837371 := bstep (se 1 (by rfl) ⟨628028, by rfl⟩ : syracuseStep 837371 = 1256057) B1256057
theorem B9062441 : Blo 291829 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B8473531 : Blo 291829 8473531 := bstep (se 1 (by rfl) ⟨6355148, by rfl⟩ : syracuseStep 8473531 = 12710297) B12710297
theorem B417307 : Blo 291829 417307 := bstep (se 1 (by rfl) ⟨312980, by rfl⟩ : syracuseStep 417307 = 625961) B625961
theorem B941863 : Blo 291829 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B745463 : Blo 291829 745463 := bstep (se 1 (by rfl) ⟨559097, by rfl⟩ : syracuseStep 745463 = 1118195) B1118195
theorem B942313 : Blo 291829 942313 := bstep (se 2 (by rfl) ⟨353367, by rfl⟩ : syracuseStep 942313 = 706735) B706735
theorem B745919 : Blo 291829 745919 := bstep (se 1 (by rfl) ⟨559439, by rfl⟩ : syracuseStep 745919 = 1118879) B1118879
theorem B4515455 : Blo 291829 4515455 := bstep (se 1 (by rfl) ⟨3386591, by rfl⟩ : syracuseStep 4515455 = 6773183) B6773183
theorem B29486227 : Blo 291829 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B2387333 : Blo 291829 2387333 := bstep (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) B447625
theorem B1339361 : Blo 291829 1339361 := bstep (se 2 (by rfl) ⟨502260, by rfl⟩ : syracuseStep 1339361 = 1004521) B1004521
theorem B291931 : Blo 291829 291931 := bstep (se 1 (by rfl) ⟨218948, by rfl⟩ : syracuseStep 291931 = 437897) B437897
theorem B6780025 : Blo 291829 6780025 := bstep (se 2 (by rfl) ⟨2542509, by rfl⟩ : syracuseStep 6780025 = 5085019) B5085019
theorem B291999 : Blo 291829 291999 := bstep (se 1 (by rfl) ⟨218999, by rfl⟩ : syracuseStep 291999 = 437999) B437999
theorem B292167 : Blo 291829 292167 := bstep (se 1 (by rfl) ⟨219125, by rfl⟩ : syracuseStep 292167 = 438251) B438251
theorem B3405401 : Blo 291829 3405401 := bstep (se 2 (by rfl) ⟨1277025, by rfl⟩ : syracuseStep 3405401 = 2554051) B2554051
theorem B292607 : Blo 291829 292607 := bstep (se 1 (by rfl) ⟨219455, by rfl⟩ : syracuseStep 292607 = 438911) B438911
theorem B554921 : Blo 291829 554921 := bstep (se 2 (by rfl) ⟨208095, by rfl⟩ : syracuseStep 554921 = 416191) B416191
theorem B292927 : Blo 291829 292927 := bstep (se 1 (by rfl) ⟨219695, by rfl⟩ : syracuseStep 292927 = 439391) B439391
theorem B2226365 : Blo 291829 2226365 := bstep (se 3 (by rfl) ⟨417443, by rfl⟩ : syracuseStep 2226365 = 834887) B834887
theorem B293487 : Blo 291829 293487 := bstep (se 1 (by rfl) ⟨220115, by rfl⟩ : syracuseStep 293487 = 440231) B440231
theorem B293663 : Blo 291829 293663 := bstep (se 1 (by rfl) ⟨220247, by rfl⟩ : syracuseStep 293663 = 440495) B440495
theorem B293823 : Blo 291829 293823 := bstep (se 1 (by rfl) ⟨220367, by rfl⟩ : syracuseStep 293823 = 440735) B440735
theorem B556379 : Blo 291829 556379 := bstep (se 1 (by rfl) ⟨417284, by rfl⟩ : syracuseStep 556379 = 834569) B834569
theorem B294651 : Blo 291829 294651 := bstep (se 1 (by rfl) ⟨220988, by rfl⟩ : syracuseStep 294651 = 441977) B441977
theorem B27066125 : Blo 291829 27066125 := bstep (se 3 (by rfl) ⟨5074898, by rfl⟩ : syracuseStep 27066125 = 10149797) B10149797
theorem B30736219 : Blo 291829 30736219 := bstep (se 1 (by rfl) ⟨23052164, by rfl⟩ : syracuseStep 30736219 = 46104329) B46104329
theorem B295195 : Blo 291829 295195 := bstep (se 1 (by rfl) ⟨221396, by rfl⟩ : syracuseStep 295195 = 442793) B442793
theorem B295407 : Blo 291829 295407 := bstep (se 1 (by rfl) ⟨221555, by rfl⟩ : syracuseStep 295407 = 443111) B443111
theorem B295707 : Blo 291829 295707 := bstep (se 1 (by rfl) ⟨221780, by rfl⟩ : syracuseStep 295707 = 443561) B443561
theorem B558247 : Blo 291829 558247 := bstep (se 1 (by rfl) ⟨418685, by rfl⟩ : syracuseStep 558247 = 837371) B837371
theorem B658313 : Blo 291829 658313 := bstep (se 2 (by rfl) ⟨246867, by rfl⟩ : syracuseStep 658313 = 493735) B493735
theorem B330943 : Blo 291829 330943 := bstep (se 1 (by rfl) ⟨248207, by rfl⟩ : syracuseStep 330943 = 496415) B496415
theorem B986363 : Blo 291829 986363 := bstep (se 1 (by rfl) ⟨739772, by rfl⟩ : syracuseStep 986363 = 1479545) B1479545
theorem B396571 : Blo 291829 396571 := bstep (se 1 (by rfl) ⟨297428, by rfl⟩ : syracuseStep 396571 = 594857) B594857
theorem B495929 : Blo 291829 495929 := bstep (se 2 (by rfl) ⟨185973, by rfl⟩ : syracuseStep 495929 = 371947) B371947
theorem B2495609 : Blo 291829 2495609 := bstep (se 2 (by rfl) ⟨935853, by rfl⟩ : syracuseStep 2495609 = 1871707) B1871707
theorem B496975 : Blo 291829 496975 := bstep (se 1 (by rfl) ⟨372731, by rfl⟩ : syracuseStep 496975 = 745463) B745463
theorem B497279 : Blo 291829 497279 := bstep (se 1 (by rfl) ⟨372959, by rfl⟩ : syracuseStep 497279 = 745919) B745919
theorem B3742847 : Blo 291829 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B532307 : Blo 291829 532307 := bstep (se 1 (by rfl) ⟨399230, by rfl⟩ : syracuseStep 532307 = 798461) B798461
theorem B892907 : Blo 291829 892907 := bstep (se 1 (by rfl) ⟨669680, by rfl⟩ : syracuseStep 892907 = 1339361) B1339361
theorem B664055 : Blo 291829 664055 := bstep (se 1 (by rfl) ⟨498041, by rfl⟩ : syracuseStep 664055 = 996083) B996083
theorem B6366221 : Blo 291829 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B2270267 : Blo 291829 2270267 := bstep (se 1 (by rfl) ⟨1702700, by rfl⟩ : syracuseStep 2270267 = 3405401) B3405401
theorem B369947 : Blo 291829 369947 := bstep (se 1 (by rfl) ⟨277460, by rfl⟩ : syracuseStep 369947 = 554921) B554921
theorem B1484243 : Blo 291829 1484243 := bstep (se 1 (by rfl) ⟨1113182, by rfl⟩ : syracuseStep 1484243 = 2226365) B2226365
theorem B370919 : Blo 291829 370919 := bstep (se 1 (by rfl) ⟨278189, by rfl⟩ : syracuseStep 370919 = 556379) B556379
theorem B1255817 : Blo 291829 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B1256417 : Blo 291829 1256417 := bstep (se 2 (by rfl) ⟨471156, by rfl⟩ : syracuseStep 1256417 = 942313) B942313
theorem B8498681 : Blo 291829 8498681 := bstep (se 2 (by rfl) ⟨3187005, by rfl⟩ : syracuseStep 8498681 = 6374011) B6374011
theorem B6041627 : Blo 291829 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B3324239 : Blo 291829 3324239 := bstep (se 1 (by rfl) ⟨2493179, by rfl⟩ : syracuseStep 3324239 = 4986359) B4986359
theorem B1489751 : Blo 291829 1489751 := bstep (se 1 (by rfl) ⟨1117313, by rfl⟩ : syracuseStep 1489751 = 2234627) B2234627
theorem B441215 : Blo 291829 441215 := bstep (se 1 (by rfl) ⟨330911, by rfl⟩ : syracuseStep 441215 = 661823) B661823
theorem B2244833 : Blo 291829 2244833 := bstep (se 2 (by rfl) ⟨841812, by rfl⟩ : syracuseStep 2244833 = 1683625) B1683625
theorem B1362091 : Blo 291829 1362091 := bstep (se 1 (by rfl) ⟨1021568, by rfl⟩ : syracuseStep 1362091 = 2043137) B2043137
theorem B40981625 : Blo 291829 40981625 := bstep (se 2 (by rfl) ⟨15368109, by rfl⟩ : syracuseStep 40981625 = 30736219) B30736219
theorem B18044083 : Blo 291829 18044083 := bstep (se 1 (by rfl) ⟨13533062, by rfl⟩ : syracuseStep 18044083 = 27066125) B27066125
theorem B4023047 : Blo 291829 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B11298041 : Blo 291829 11298041 := bstep (se 2 (by rfl) ⟨4236765, by rfl⟩ : syracuseStep 11298041 = 8473531) B8473531
theorem B746759 : Blo 291829 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B39314969 : Blo 291829 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B3010303 : Blo 291829 3010303 := bstep (se 1 (by rfl) ⟨2257727, by rfl⟩ : syracuseStep 3010303 = 4515455) B4515455
theorem B9040033 : Blo 291829 9040033 := bstep (se 2 (by rfl) ⟨3390012, by rfl⟩ : syracuseStep 9040033 = 6780025) B6780025
theorem B1799333 : Blo 291829 1799333 := bstep (se 4 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 1799333 = 337375) B337375
theorem B292095 : Blo 291829 292095 := bstep (se 1 (by rfl) ⟨219071, by rfl⟩ : syracuseStep 292095 = 438143) B438143
theorem B292287 : Blo 291829 292287 := bstep (se 1 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 292287 = 438431) B438431
theorem B292863 : Blo 291829 292863 := bstep (se 1 (by rfl) ⟨219647, by rfl⟩ : syracuseStep 292863 = 439295) B439295
theorem B556409 : Blo 291829 556409 := bstep (se 2 (by rfl) ⟨208653, by rfl⟩ : syracuseStep 556409 = 417307) B417307
theorem B294303 : Blo 291829 294303 := bstep (se 1 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 294303 = 441455) B441455
theorem B294895 : Blo 291829 294895 := bstep (se 1 (by rfl) ⟨221171, by rfl⟩ : syracuseStep 294895 = 442343) B442343
theorem B657575 : Blo 291829 657575 := bstep (se 1 (by rfl) ⟨493181, by rfl⟩ : syracuseStep 657575 = 986363) B986363
theorem B330619 : Blo 291829 330619 := bstep (se 1 (by rfl) ⟨247964, by rfl⟩ : syracuseStep 330619 = 495929) B495929
theorem B986525 : Blo 291829 986525 := bstep (se 3 (by rfl) ⟨184973, by rfl⟩ : syracuseStep 986525 = 369947) B369947
theorem B331519 : Blo 291829 331519 := bstep (se 1 (by rfl) ⟨248639, by rfl⟩ : syracuseStep 331519 = 497279) B497279
theorem B528761 : Blo 291829 528761 := bstep (se 2 (by rfl) ⟨198285, by rfl⟩ : syracuseStep 528761 = 396571) B396571
theorem B2495231 : Blo 291829 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B595271 : Blo 291829 595271 := bstep (se 1 (by rfl) ⟨446453, by rfl⟩ : syracuseStep 595271 = 892907) B892907
theorem B989117 : Blo 291829 989117 := bstep (se 3 (by rfl) ⟨185459, by rfl⟩ : syracuseStep 989117 = 370919) B370919
theorem B1513511 : Blo 291829 1513511 := bstep (se 1 (by rfl) ⟨1135133, by rfl⟩ : syracuseStep 1513511 = 2270267) B2270267
theorem B497839 : Blo 291829 497839 := bstep (se 1 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 497839 = 746759) B746759
theorem B989495 : Blo 291829 989495 := bstep (se 1 (by rfl) ⟨742121, by rfl⟩ : syracuseStep 989495 = 1484243) B1484243
theorem B24058777 : Blo 291829 24058777 := bstep (se 2 (by rfl) ⟨9022041, by rfl⟩ : syracuseStep 24058777 = 18044083) B18044083
theorem B662633 : Blo 291829 662633 := bstep (se 2 (by rfl) ⟨248487, by rfl⟩ : syracuseStep 662633 = 496975) B496975
theorem B1483757 : Blo 291829 1483757 := bstep (se 3 (by rfl) ⟨278204, by rfl⟩ : syracuseStep 1483757 = 556409) B556409
theorem B993167 : Blo 291829 993167 := bstep (se 1 (by rfl) ⟨744875, by rfl⟩ : syracuseStep 993167 = 1489751) B1489751
theorem B438875 : Blo 291829 438875 := bstep (se 1 (by rfl) ⟨329156, by rfl⟩ : syracuseStep 438875 = 658313) B658313
theorem B10728125 : Blo 291829 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B1816121 : Blo 291829 1816121 := bstep (se 2 (by rfl) ⟨681045, by rfl⟩ : syracuseStep 1816121 = 1362091) B1362091
theorem B441257 : Blo 291829 441257 := bstep (se 2 (by rfl) ⟨165471, by rfl⟩ : syracuseStep 441257 = 330943) B330943
theorem B442703 : Blo 291829 442703 := bstep (se 1 (by rfl) ⟨332027, by rfl⟩ : syracuseStep 442703 = 664055) B664055
theorem B4244147 : Blo 291829 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B837211 : Blo 291829 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B837611 : Blo 291829 837611 := bstep (se 1 (by rfl) ⟨628208, by rfl⟩ : syracuseStep 837611 = 1256417) B1256417
theorem B1199555 : Blo 291829 1199555 := bstep (se 1 (by rfl) ⟨899666, by rfl⟩ : syracuseStep 1199555 = 1799333) B1799333
theorem B2216159 : Blo 291829 2216159 := bstep (se 1 (by rfl) ⟨1662119, by rfl⟩ : syracuseStep 2216159 = 3324239) B3324239
theorem B1496555 : Blo 291829 1496555 := bstep (se 1 (by rfl) ⟨1122416, by rfl⟩ : syracuseStep 1496555 = 2244833) B2244833
theorem B744329 : Blo 291829 744329 := bstep (se 2 (by rfl) ⟨279123, by rfl⟩ : syracuseStep 744329 = 558247) B558247
theorem B1663739 : Blo 291829 1663739 := bstep (se 1 (by rfl) ⟨1247804, by rfl⟩ : syracuseStep 1663739 = 2495609) B2495609
theorem B27321083 : Blo 291829 27321083 := bstep (se 1 (by rfl) ⟨20490812, by rfl⟩ : syracuseStep 27321083 = 40981625) B40981625
theorem B354871 : Blo 291829 354871 := bstep (se 1 (by rfl) ⟨266153, by rfl⟩ : syracuseStep 354871 = 532307) B532307
theorem B12053377 : Blo 291829 12053377 := bstep (se 2 (by rfl) ⟨4520016, by rfl⟩ : syracuseStep 12053377 = 9040033) B9040033
theorem B7532027 : Blo 291829 7532027 := bstep (se 1 (by rfl) ⟨5649020, by rfl⟩ : syracuseStep 7532027 = 11298041) B11298041
theorem B26209979 : Blo 291829 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B5665787 : Blo 291829 5665787 := bstep (se 1 (by rfl) ⟨4249340, by rfl⟩ : syracuseStep 5665787 = 8498681) B8498681
theorem B4027751 : Blo 291829 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B16054949 : Blo 291829 16054949 := bstep (se 4 (by rfl) ⟨1505151, by rfl⟩ : syracuseStep 16054949 = 3010303) B3010303
theorem B294143 : Blo 291829 294143 := bstep (se 1 (by rfl) ⟨220607, by rfl⟩ : syracuseStep 294143 = 441215) B441215
theorem B295135 : Blo 291829 295135 := bstep (se 1 (by rfl) ⟨221351, by rfl⟩ : syracuseStep 295135 = 442703) B442703
theorem B558407 : Blo 291829 558407 := bstep (se 1 (by rfl) ⟨418805, by rfl⟩ : syracuseStep 558407 = 837611) B837611
theorem B1116281 : Blo 291829 1116281 := bstep (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) B837211
theorem B657683 : Blo 291829 657683 := bstep (se 1 (by rfl) ⟨493262, by rfl⟩ : syracuseStep 657683 = 986525) B986525
theorem B1477439 : Blo 291829 1477439 := bstep (se 1 (by rfl) ⟨1108079, by rfl⟩ : syracuseStep 1477439 = 2216159) B2216159
theorem B396847 : Blo 291829 396847 := bstep (se 1 (by rfl) ⟨297635, by rfl⟩ : syracuseStep 396847 = 595271) B595271
theorem B659411 : Blo 291829 659411 := bstep (se 1 (by rfl) ⟨494558, by rfl⟩ : syracuseStep 659411 = 989117) B989117
theorem B659663 : Blo 291829 659663 := bstep (se 1 (by rfl) ⟨494747, by rfl⟩ : syracuseStep 659663 = 989495) B989495
theorem B496219 : Blo 291829 496219 := bstep (se 1 (by rfl) ⟨372164, by rfl⟩ : syracuseStep 496219 = 744329) B744329
theorem B989171 : Blo 291829 989171 := bstep (se 1 (by rfl) ⟨741878, by rfl⟩ : syracuseStep 989171 = 1483757) B1483757
theorem B662111 : Blo 291829 662111 := bstep (se 1 (by rfl) ⟨496583, by rfl⟩ : syracuseStep 662111 = 993167) B993167
theorem B5021351 : Blo 291829 5021351 := bstep (se 1 (by rfl) ⟨3766013, by rfl⟩ : syracuseStep 5021351 = 7532027) B7532027
theorem B17473319 : Blo 291829 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B663785 : Blo 291829 663785 := bstep (se 2 (by rfl) ⟨248919, by rfl⟩ : syracuseStep 663785 = 497839) B497839
theorem B7152083 : Blo 291829 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B3777191 : Blo 291829 3777191 := bstep (se 1 (by rfl) ⟨2832893, by rfl⟩ : syracuseStep 3777191 = 5665787) B5665787
theorem B2829431 : Blo 291829 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B438383 : Blo 291829 438383 := bstep (se 1 (by rfl) ⟨328787, by rfl⟩ : syracuseStep 438383 = 657575) B657575
theorem B799703 : Blo 291829 799703 := bstep (se 1 (by rfl) ⟨599777, by rfl⟩ : syracuseStep 799703 = 1199555) B1199555
theorem B997703 : Blo 291829 997703 := bstep (se 1 (by rfl) ⟨748277, by rfl⟩ : syracuseStep 997703 = 1496555) B1496555
theorem B440825 : Blo 291829 440825 := bstep (se 2 (by rfl) ⟨165309, by rfl⟩ : syracuseStep 440825 = 330619) B330619
theorem B16071169 : Blo 291829 16071169 := bstep (se 2 (by rfl) ⟨6026688, by rfl⟩ : syracuseStep 16071169 = 12053377) B12053377
theorem B441755 : Blo 291829 441755 := bstep (se 1 (by rfl) ⟨331316, by rfl⟩ : syracuseStep 441755 = 662633) B662633
theorem B442025 : Blo 291829 442025 := bstep (se 2 (by rfl) ⟨165759, by rfl⟩ : syracuseStep 442025 = 331519) B331519
theorem B10703299 : Blo 291829 10703299 := bstep (se 1 (by rfl) ⟨8027474, by rfl⟩ : syracuseStep 10703299 = 16054949) B16054949
theorem B352507 : Blo 291829 352507 := bstep (se 1 (by rfl) ⟨264380, by rfl⟩ : syracuseStep 352507 = 528761) B528761
theorem B1892645 : Blo 291829 1892645 := bstep (se 4 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 1892645 = 354871) B354871
theorem B1663487 : Blo 291829 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B1009007 : Blo 291829 1009007 := bstep (se 1 (by rfl) ⟨756755, by rfl⟩ : syracuseStep 1009007 = 1513511) B1513511
theorem B1109159 : Blo 291829 1109159 := bstep (se 1 (by rfl) ⟨831869, by rfl⟩ : syracuseStep 1109159 = 1663739) B1663739
theorem B18214055 : Blo 291829 18214055 := bstep (se 1 (by rfl) ⟨13660541, by rfl⟩ : syracuseStep 18214055 = 27321083) B27321083
theorem B292583 : Blo 291829 292583 := bstep (se 1 (by rfl) ⟨219437, by rfl⟩ : syracuseStep 292583 = 438875) B438875
theorem B2685167 : Blo 291829 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B1210747 : Blo 291829 1210747 := bstep (se 1 (by rfl) ⟨908060, by rfl⟩ : syracuseStep 1210747 = 1816121) B1816121
theorem B32078369 : Blo 291829 32078369 := bstep (se 2 (by rfl) ⟨12029388, by rfl⟩ : syracuseStep 32078369 = 24058777) B24058777
theorem B294171 : Blo 291829 294171 := bstep (se 1 (by rfl) ⟨220628, by rfl⟩ : syracuseStep 294171 = 441257) B441257
theorem B984959 : Blo 291829 984959 := bstep (se 1 (by rfl) ⟨738719, by rfl⟩ : syracuseStep 984959 = 1477439) B1477439
theorem B659447 : Blo 291829 659447 := bstep (se 1 (by rfl) ⟨494585, by rfl⟩ : syracuseStep 659447 = 989171) B989171
theorem B529129 : Blo 291829 529129 := bstep (se 2 (by rfl) ⟨198423, by rfl⟩ : syracuseStep 529129 = 396847) B396847
theorem B3347567 : Blo 291829 3347567 := bstep (se 1 (by rfl) ⟨2510675, by rfl⟩ : syracuseStep 3347567 = 5021351) B5021351
theorem B661625 : Blo 291829 661625 := bstep (se 2 (by rfl) ⟨248109, by rfl⟩ : syracuseStep 661625 = 496219) B496219
theorem B7545149 : Blo 291829 7545149 := bstep (se 3 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 7545149 = 2829431) B2829431
theorem B1614329 : Blo 291829 1614329 := bstep (se 2 (by rfl) ⟨605373, by rfl⟩ : syracuseStep 1614329 = 1210747) B1210747
theorem B533135 : Blo 291829 533135 := bstep (se 1 (by rfl) ⟨399851, by rfl⟩ : syracuseStep 533135 = 799703) B799703
theorem B665135 : Blo 291829 665135 := bstep (se 1 (by rfl) ⟨498851, by rfl⟩ : syracuseStep 665135 = 997703) B997703
theorem B470009 : Blo 291829 470009 := bstep (se 2 (by rfl) ⟨176253, by rfl⟩ : syracuseStep 470009 = 352507) B352507
theorem B372271 : Blo 291829 372271 := bstep (se 1 (by rfl) ⟨279203, by rfl⟩ : syracuseStep 372271 = 558407) B558407
theorem B438455 : Blo 291829 438455 := bstep (se 1 (by rfl) ⟨328841, by rfl⟩ : syracuseStep 438455 = 657683) B657683
theorem B439607 : Blo 291829 439607 := bstep (se 1 (by rfl) ⟨329705, by rfl⟩ : syracuseStep 439607 = 659411) B659411
theorem B439775 : Blo 291829 439775 := bstep (se 1 (by rfl) ⟨329831, by rfl⟩ : syracuseStep 439775 = 659663) B659663
theorem B441407 : Blo 291829 441407 := bstep (se 1 (by rfl) ⟨331055, by rfl⟩ : syracuseStep 441407 = 662111) B662111
theorem B11648879 : Blo 291829 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B442523 : Blo 291829 442523 := bstep (se 1 (by rfl) ⟨331892, by rfl⟩ : syracuseStep 442523 = 663785) B663785
theorem B1261763 : Blo 291829 1261763 := bstep (se 1 (by rfl) ⟨946322, by rfl⟩ : syracuseStep 1261763 = 1892645) B1892645
theorem B4768055 : Blo 291829 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B14271065 : Blo 291829 14271065 := bstep (se 2 (by rfl) ⟨5351649, by rfl⟩ : syracuseStep 14271065 = 10703299) B10703299
theorem B672671 : Blo 291829 672671 := bstep (se 1 (by rfl) ⟨504503, by rfl⟩ : syracuseStep 672671 = 1009007) B1009007
theorem B739439 : Blo 291829 739439 := bstep (se 1 (by rfl) ⟨554579, by rfl⟩ : syracuseStep 739439 = 1109159) B1109159
theorem B12142703 : Blo 291829 12142703 := bstep (se 1 (by rfl) ⟨9107027, by rfl⟩ : syracuseStep 12142703 = 18214055) B18214055
theorem B1790111 : Blo 291829 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B21385579 : Blo 291829 21385579 := bstep (se 1 (by rfl) ⟨16039184, by rfl⟩ : syracuseStep 21385579 = 32078369) B32078369
theorem B744187 : Blo 291829 744187 := bstep (se 1 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 744187 = 1116281) B1116281
theorem B1108991 : Blo 291829 1108991 := bstep (se 1 (by rfl) ⟨831743, by rfl⟩ : syracuseStep 1108991 = 1663487) B1663487
theorem B2518127 : Blo 291829 2518127 := bstep (se 1 (by rfl) ⟨1888595, by rfl⟩ : syracuseStep 2518127 = 3777191) B3777191
theorem B292255 : Blo 291829 292255 := bstep (se 1 (by rfl) ⟨219191, by rfl⟩ : syracuseStep 292255 = 438383) B438383
theorem B21428225 : Blo 291829 21428225 := bstep (se 2 (by rfl) ⟨8035584, by rfl⟩ : syracuseStep 21428225 = 16071169) B16071169
theorem B293883 : Blo 291829 293883 := bstep (se 1 (by rfl) ⟨220412, by rfl⟩ : syracuseStep 293883 = 440825) B440825
theorem B294503 : Blo 291829 294503 := bstep (se 1 (by rfl) ⟨220877, by rfl⟩ : syracuseStep 294503 = 441755) B441755
theorem B294683 : Blo 291829 294683 := bstep (se 1 (by rfl) ⟨221012, by rfl⟩ : syracuseStep 294683 = 442025) B442025
theorem B295015 : Blo 291829 295015 := bstep (se 1 (by rfl) ⟨221261, by rfl⟩ : syracuseStep 295015 = 442523) B442523
theorem B3178703 : Blo 291829 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B656639 : Blo 291829 656639 := bstep (se 1 (by rfl) ⟨492479, by rfl⟩ : syracuseStep 656639 = 984959) B984959
theorem B492959 : Blo 291829 492959 := bstep (se 1 (by rfl) ⟨369719, by rfl⟩ : syracuseStep 492959 = 739439) B739439
theorem B8095135 : Blo 291829 8095135 := bstep (se 1 (by rfl) ⟨6071351, by rfl⟩ : syracuseStep 8095135 = 12142703) B12142703
theorem B2231711 : Blo 291829 2231711 := bstep (se 1 (by rfl) ⟨1673783, by rfl⟩ : syracuseStep 2231711 = 3347567) B3347567
theorem B496361 : Blo 291829 496361 := bstep (se 2 (by rfl) ⟨186135, by rfl⟩ : syracuseStep 496361 = 372271) B372271
theorem B28514105 : Blo 291829 28514105 := bstep (se 2 (by rfl) ⟨10692789, by rfl⟩ : syracuseStep 28514105 = 21385579) B21385579
theorem B1678751 : Blo 291829 1678751 := bstep (se 1 (by rfl) ⟨1259063, by rfl⟩ : syracuseStep 1678751 = 2518127) B2518127
theorem B1253357 : Blo 291829 1253357 := bstep (se 3 (by rfl) ⟨235004, by rfl⟩ : syracuseStep 1253357 = 470009) B470009
theorem B992249 : Blo 291829 992249 := bstep (se 2 (by rfl) ⟨372093, by rfl⟩ : syracuseStep 992249 = 744187) B744187
theorem B9514043 : Blo 291829 9514043 := bstep (se 1 (by rfl) ⟨7135532, by rfl⟩ : syracuseStep 9514043 = 14271065) B14271065
theorem B439631 : Blo 291829 439631 := bstep (se 1 (by rfl) ⟨329723, by rfl⟩ : syracuseStep 439631 = 659447) B659447
theorem B441083 : Blo 291829 441083 := bstep (se 1 (by rfl) ⟨330812, by rfl⟩ : syracuseStep 441083 = 661625) B661625
theorem B5030099 : Blo 291829 5030099 := bstep (se 1 (by rfl) ⟨3772574, by rfl⟩ : syracuseStep 5030099 = 7545149) B7545149
theorem B705505 : Blo 291829 705505 := bstep (se 2 (by rfl) ⟨264564, by rfl⟩ : syracuseStep 705505 = 529129) B529129
theorem B443423 : Blo 291829 443423 := bstep (se 1 (by rfl) ⟨332567, by rfl⟩ : syracuseStep 443423 = 665135) B665135
theorem B739327 : Blo 291829 739327 := bstep (se 1 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 739327 = 1108991) B1108991
theorem B841175 : Blo 291829 841175 := bstep (se 1 (by rfl) ⟨630881, by rfl⟩ : syracuseStep 841175 = 1261763) B1261763
theorem B4773629 : Blo 291829 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B1793789 : Blo 291829 1793789 := bstep (se 3 (by rfl) ⟨336335, by rfl⟩ : syracuseStep 1793789 = 672671) B672671
theorem B1076219 : Blo 291829 1076219 := bstep (se 1 (by rfl) ⟨807164, by rfl⟩ : syracuseStep 1076219 = 1614329) B1614329
theorem B355423 : Blo 291829 355423 := bstep (se 1 (by rfl) ⟨266567, by rfl⟩ : syracuseStep 355423 = 533135) B533135
theorem B292303 : Blo 291829 292303 := bstep (se 1 (by rfl) ⟨219227, by rfl⟩ : syracuseStep 292303 = 438455) B438455
theorem B293071 : Blo 291829 293071 := bstep (se 1 (by rfl) ⟨219803, by rfl⟩ : syracuseStep 293071 = 439607) B439607
theorem B293183 : Blo 291829 293183 := bstep (se 1 (by rfl) ⟨219887, by rfl⟩ : syracuseStep 293183 = 439775) B439775
theorem B14285483 : Blo 291829 14285483 := bstep (se 1 (by rfl) ⟨10714112, by rfl⟩ : syracuseStep 14285483 = 21428225) B21428225
theorem B294271 : Blo 291829 294271 := bstep (se 1 (by rfl) ⟨220703, by rfl⟩ : syracuseStep 294271 = 441407) B441407
theorem B7765919 : Blo 291829 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B295615 : Blo 291829 295615 := bstep (se 1 (by rfl) ⟨221711, by rfl⟩ : syracuseStep 295615 = 443423) B443423
theorem B328639 : Blo 291829 328639 := bstep (se 1 (by rfl) ⟨246479, by rfl⟩ : syracuseStep 328639 = 492959) B492959
theorem B985769 : Blo 291829 985769 := bstep (se 2 (by rfl) ⟨369663, by rfl⟩ : syracuseStep 985769 = 739327) B739327
theorem B330907 : Blo 291829 330907 := bstep (se 1 (by rfl) ⟨248180, by rfl⟩ : syracuseStep 330907 = 496361) B496361
theorem B560783 : Blo 291829 560783 := bstep (se 1 (by rfl) ⟨420587, by rfl⟩ : syracuseStep 560783 = 841175) B841175
theorem B3182419 : Blo 291829 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B19009403 : Blo 291829 19009403 := bstep (se 1 (by rfl) ⟨14257052, by rfl⟩ : syracuseStep 19009403 = 28514105) B28514105
theorem B1119167 : Blo 291829 1119167 := bstep (se 1 (by rfl) ⟨839375, by rfl⟩ : syracuseStep 1119167 = 1678751) B1678751
theorem B661499 : Blo 291829 661499 := bstep (se 1 (by rfl) ⟨496124, by rfl⟩ : syracuseStep 661499 = 992249) B992249
theorem B3353399 : Blo 291829 3353399 := bstep (se 1 (by rfl) ⟨2515049, by rfl⟩ : syracuseStep 3353399 = 5030099) B5030099
theorem B437759 : Blo 291829 437759 := bstep (se 1 (by rfl) ⟨328319, by rfl⟩ : syracuseStep 437759 = 656639) B656639
theorem B10793513 : Blo 291829 10793513 := bstep (se 2 (by rfl) ⟨4047567, by rfl⟩ : syracuseStep 10793513 = 8095135) B8095135
theorem B1487807 : Blo 291829 1487807 := bstep (se 1 (by rfl) ⟨1115855, by rfl⟩ : syracuseStep 1487807 = 2231711) B2231711
theorem B473897 : Blo 291829 473897 := bstep (se 2 (by rfl) ⟨177711, by rfl⟩ : syracuseStep 473897 = 355423) B355423
theorem B1195859 : Blo 291829 1195859 := bstep (se 1 (by rfl) ⟨896894, by rfl⟩ : syracuseStep 1195859 = 1793789) B1793789
theorem B835571 : Blo 291829 835571 := bstep (se 1 (by rfl) ⟨626678, by rfl⟩ : syracuseStep 835571 = 1253357) B1253357
theorem B6342695 : Blo 291829 6342695 := bstep (se 1 (by rfl) ⟨4757021, by rfl⟩ : syracuseStep 6342695 = 9514043) B9514043
theorem B9523655 : Blo 291829 9523655 := bstep (se 1 (by rfl) ⟨7142741, by rfl⟩ : syracuseStep 9523655 = 14285483) B14285483
theorem B2119135 : Blo 291829 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B940673 : Blo 291829 940673 := bstep (se 2 (by rfl) ⟨352752, by rfl⟩ : syracuseStep 940673 = 705505) B705505
theorem B717479 : Blo 291829 717479 := bstep (se 1 (by rfl) ⟨538109, by rfl⟩ : syracuseStep 717479 = 1076219) B1076219
theorem B293087 : Blo 291829 293087 := bstep (se 1 (by rfl) ⟨219815, by rfl⟩ : syracuseStep 293087 = 439631) B439631
theorem B294055 : Blo 291829 294055 := bstep (se 1 (by rfl) ⟨220541, by rfl⟩ : syracuseStep 294055 = 441083) B441083
theorem B5177279 : Blo 291829 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B4228463 : Blo 291829 4228463 := bstep (se 1 (by rfl) ⟨3171347, by rfl⟩ : syracuseStep 4228463 = 6342695) B6342695
theorem B657179 : Blo 291829 657179 := bstep (se 1 (by rfl) ⟨492884, by rfl⟩ : syracuseStep 657179 = 985769) B985769
theorem B627115 : Blo 291829 627115 := bstep (se 1 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 627115 = 940673) B940673
theorem B2235599 : Blo 291829 2235599 := bstep (se 1 (by rfl) ⟨1676699, by rfl⟩ : syracuseStep 2235599 = 3353399) B3353399
theorem B2825513 : Blo 291829 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B991871 : Blo 291829 991871 := bstep (se 1 (by rfl) ⟨743903, by rfl⟩ : syracuseStep 991871 = 1487807) B1487807
theorem B13806077 : Blo 291829 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B797239 : Blo 291829 797239 := bstep (se 1 (by rfl) ⟨597929, by rfl⟩ : syracuseStep 797239 = 1195859) B1195859
theorem B438185 : Blo 291829 438185 := bstep (se 2 (by rfl) ⟨164319, by rfl⟩ : syracuseStep 438185 = 328639) B328639
theorem B440999 : Blo 291829 440999 := bstep (se 1 (by rfl) ⟨330749, by rfl⟩ : syracuseStep 440999 = 661499) B661499
theorem B441209 : Blo 291829 441209 := bstep (se 2 (by rfl) ⟨165453, by rfl⟩ : syracuseStep 441209 = 330907) B330907
theorem B4243225 : Blo 291829 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B1263725 : Blo 291829 1263725 := bstep (se 3 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 1263725 = 473897) B473897
theorem B7195675 : Blo 291829 7195675 := bstep (se 1 (by rfl) ⟨5396756, by rfl⟩ : syracuseStep 7195675 = 10793513) B10793513
theorem B478319 : Blo 291829 478319 := bstep (se 1 (by rfl) ⟨358739, by rfl⟩ : syracuseStep 478319 = 717479) B717479
theorem B1495421 : Blo 291829 1495421 := bstep (se 3 (by rfl) ⟨280391, by rfl⟩ : syracuseStep 1495421 = 560783) B560783
theorem B12672935 : Blo 291829 12672935 := bstep (se 1 (by rfl) ⟨9504701, by rfl⟩ : syracuseStep 12672935 = 19009403) B19009403
theorem B6349103 : Blo 291829 6349103 := bstep (se 1 (by rfl) ⟨4761827, by rfl⟩ : syracuseStep 6349103 = 9523655) B9523655
theorem B746111 : Blo 291829 746111 := bstep (se 1 (by rfl) ⟨559583, by rfl⟩ : syracuseStep 746111 = 1119167) B1119167
theorem B291839 : Blo 291829 291839 := bstep (se 1 (by rfl) ⟨218879, by rfl⟩ : syracuseStep 291839 = 437759) B437759
theorem B557047 : Blo 291829 557047 := bstep (se 1 (by rfl) ⟨417785, by rfl⟩ : syracuseStep 557047 = 835571) B835571
theorem B2818975 : Blo 291829 2818975 := bstep (se 1 (by rfl) ⟨2114231, by rfl⟩ : syracuseStep 2818975 = 4228463) B4228463
theorem B4232735 : Blo 291829 4232735 := bstep (se 1 (by rfl) ⟨3174551, by rfl⟩ : syracuseStep 4232735 = 6349103) B6349103
theorem B497407 : Blo 291829 497407 := bstep (se 1 (by rfl) ⟨373055, by rfl⟩ : syracuseStep 497407 = 746111) B746111
theorem B661247 : Blo 291829 661247 := bstep (se 1 (by rfl) ⟨495935, by rfl⟩ : syracuseStep 661247 = 991871) B991871
theorem B438119 : Blo 291829 438119 := bstep (se 1 (by rfl) ⟨328589, by rfl⟩ : syracuseStep 438119 = 657179) B657179
theorem B996947 : Blo 291829 996947 := bstep (se 1 (by rfl) ⟨747710, by rfl⟩ : syracuseStep 996947 = 1495421) B1495421
theorem B1062985 : Blo 291829 1062985 := bstep (se 2 (by rfl) ⟨398619, by rfl⟩ : syracuseStep 1062985 = 797239) B797239
theorem B1490399 : Blo 291829 1490399 := bstep (se 1 (by rfl) ⟨1117799, by rfl⟩ : syracuseStep 1490399 = 2235599) B2235599
theorem B1883675 : Blo 291829 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B836153 : Blo 291829 836153 := bstep (se 2 (by rfl) ⟨313557, by rfl⟩ : syracuseStep 836153 = 627115) B627115
theorem B36816205 : Blo 291829 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B5657633 : Blo 291829 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B742729 : Blo 291829 742729 := bstep (se 2 (by rfl) ⟨278523, by rfl⟩ : syracuseStep 742729 = 557047) B557047
theorem B842483 : Blo 291829 842483 := bstep (se 1 (by rfl) ⟨631862, by rfl⟩ : syracuseStep 842483 = 1263725) B1263725
theorem B9594233 : Blo 291829 9594233 := bstep (se 2 (by rfl) ⟨3597837, by rfl⟩ : syracuseStep 9594233 = 7195675) B7195675
theorem B8448623 : Blo 291829 8448623 := bstep (se 1 (by rfl) ⟨6336467, by rfl⟩ : syracuseStep 8448623 = 12672935) B12672935
theorem B292123 : Blo 291829 292123 := bstep (se 1 (by rfl) ⟨219092, by rfl⟩ : syracuseStep 292123 = 438185) B438185
theorem B1275517 : Blo 291829 1275517 := bstep (se 3 (by rfl) ⟨239159, by rfl⟩ : syracuseStep 1275517 = 478319) B478319
theorem B293999 : Blo 291829 293999 := bstep (se 1 (by rfl) ⟨220499, by rfl⟩ : syracuseStep 293999 = 440999) B440999
theorem B294139 : Blo 291829 294139 := bstep (se 1 (by rfl) ⟨220604, by rfl⟩ : syracuseStep 294139 = 441209) B441209
theorem B557435 : Blo 291829 557435 := bstep (se 1 (by rfl) ⟨418076, by rfl⟩ : syracuseStep 557435 = 836153) B836153
theorem B49088273 : Blo 291829 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B3771755 : Blo 291829 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B2821823 : Blo 291829 2821823 := bstep (se 1 (by rfl) ⟨2116367, by rfl⟩ : syracuseStep 2821823 = 4232735) B4232735
theorem B561655 : Blo 291829 561655 := bstep (se 1 (by rfl) ⟨421241, by rfl⟩ : syracuseStep 561655 = 842483) B842483
theorem B6396155 : Blo 291829 6396155 := bstep (se 1 (by rfl) ⟨4797116, by rfl⟩ : syracuseStep 6396155 = 9594233) B9594233
theorem B990305 : Blo 291829 990305 := bstep (se 2 (by rfl) ⟨371364, by rfl⟩ : syracuseStep 990305 = 742729) B742729
theorem B663209 : Blo 291829 663209 := bstep (se 2 (by rfl) ⟨248703, by rfl⟩ : syracuseStep 663209 = 497407) B497407
theorem B1417313 : Blo 291829 1417313 := bstep (se 2 (by rfl) ⟨531492, by rfl⟩ : syracuseStep 1417313 = 1062985) B1062985
theorem B664631 : Blo 291829 664631 := bstep (se 1 (by rfl) ⟨498473, by rfl⟩ : syracuseStep 664631 = 996947) B996947
theorem B993599 : Blo 291829 993599 := bstep (se 1 (by rfl) ⟨745199, by rfl⟩ : syracuseStep 993599 = 1490399) B1490399
theorem B1255783 : Blo 291829 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B440831 : Blo 291829 440831 := bstep (se 1 (by rfl) ⟨330623, by rfl⟩ : syracuseStep 440831 = 661247) B661247
theorem B3758633 : Blo 291829 3758633 := bstep (se 2 (by rfl) ⟨1409487, by rfl⟩ : syracuseStep 3758633 = 2818975) B2818975
theorem B5632415 : Blo 291829 5632415 := bstep (se 1 (by rfl) ⟨4224311, by rfl⟩ : syracuseStep 5632415 = 8448623) B8448623
theorem B1700689 : Blo 291829 1700689 := bstep (se 2 (by rfl) ⟨637758, by rfl⟩ : syracuseStep 1700689 = 1275517) B1275517
theorem B292079 : Blo 291829 292079 := bstep (se 1 (by rfl) ⟨219059, by rfl⟩ : syracuseStep 292079 = 438119) B438119
theorem B1674377 : Blo 291829 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B4264103 : Blo 291829 4264103 := bstep (se 1 (by rfl) ⟨3198077, by rfl⟩ : syracuseStep 4264103 = 6396155) B6396155
theorem B660203 : Blo 291829 660203 := bstep (se 1 (by rfl) ⟨495152, by rfl⟩ : syracuseStep 660203 = 990305) B990305
theorem B2267585 : Blo 291829 2267585 := bstep (se 2 (by rfl) ⟨850344, by rfl⟩ : syracuseStep 2267585 = 1700689) B1700689
theorem B662399 : Blo 291829 662399 := bstep (se 1 (by rfl) ⟨496799, by rfl⟩ : syracuseStep 662399 = 993599) B993599
theorem B523608245 : Blo 291829 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B371623 : Blo 291829 371623 := bstep (se 1 (by rfl) ⟨278717, by rfl⟩ : syracuseStep 371623 = 557435) B557435
theorem B1881215 : Blo 291829 1881215 := bstep (se 1 (by rfl) ⟨1410911, by rfl⟩ : syracuseStep 1881215 = 2821823) B2821823
theorem B2505755 : Blo 291829 2505755 := bstep (se 1 (by rfl) ⟨1879316, by rfl⟩ : syracuseStep 2505755 = 3758633) B3758633
theorem B442139 : Blo 291829 442139 := bstep (se 1 (by rfl) ⟨331604, by rfl⟩ : syracuseStep 442139 = 663209) B663209
theorem B443087 : Blo 291829 443087 := bstep (se 1 (by rfl) ⟨332315, by rfl⟩ : syracuseStep 443087 = 664631) B664631
theorem B3754943 : Blo 291829 3754943 := bstep (se 1 (by rfl) ⟨2816207, by rfl⟩ : syracuseStep 3754943 = 5632415) B5632415
theorem B2514503 : Blo 291829 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B944875 : Blo 291829 944875 := bstep (se 1 (by rfl) ⟨708656, by rfl⟩ : syracuseStep 944875 = 1417313) B1417313
theorem B748873 : Blo 291829 748873 := bstep (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) B561655
theorem B293887 : Blo 291829 293887 := bstep (se 1 (by rfl) ⟨220415, by rfl⟩ : syracuseStep 293887 = 440831) B440831
theorem B295391 : Blo 291829 295391 := bstep (se 1 (by rfl) ⟨221543, by rfl⟩ : syracuseStep 295391 = 443087) B443087
theorem B1116251 : Blo 291829 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B495497 : Blo 291829 495497 := bstep (se 2 (by rfl) ⟨185811, by rfl⟩ : syracuseStep 495497 = 371623) B371623
theorem B1511723 : Blo 291829 1511723 := bstep (se 1 (by rfl) ⟨1133792, by rfl⟩ : syracuseStep 1511723 = 2267585) B2267585
theorem B1676335 : Blo 291829 1676335 := bstep (se 1 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 1676335 = 2514503) B2514503
theorem B1254143 : Blo 291829 1254143 := bstep (se 1 (by rfl) ⟨940607, by rfl⟩ : syracuseStep 1254143 = 1881215) B1881215
theorem B2503295 : Blo 291829 2503295 := bstep (se 1 (by rfl) ⟨1877471, by rfl⟩ : syracuseStep 2503295 = 3754943) B3754943
theorem B440135 : Blo 291829 440135 := bstep (se 1 (by rfl) ⟨330101, by rfl⟩ : syracuseStep 440135 = 660203) B660203
theorem B1259833 : Blo 291829 1259833 := bstep (se 2 (by rfl) ⟨472437, by rfl⟩ : syracuseStep 1259833 = 944875) B944875
theorem B998497 : Blo 291829 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B441599 : Blo 291829 441599 := bstep (se 1 (by rfl) ⟨331199, by rfl⟩ : syracuseStep 441599 = 662399) B662399
theorem B2842735 : Blo 291829 2842735 := bstep (se 1 (by rfl) ⟨2132051, by rfl⟩ : syracuseStep 2842735 = 4264103) B4264103
theorem B349072163 : Blo 291829 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B1670503 : Blo 291829 1670503 := bstep (se 1 (by rfl) ⟨1252877, by rfl⟩ : syracuseStep 1670503 = 2505755) B2505755
theorem B294759 : Blo 291829 294759 := bstep (se 1 (by rfl) ⟨221069, by rfl⟩ : syracuseStep 294759 = 442139) B442139
theorem B330331 : Blo 291829 330331 := bstep (se 1 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 330331 = 495497) B495497
theorem B2235113 : Blo 291829 2235113 := bstep (se 2 (by rfl) ⟨838167, by rfl⟩ : syracuseStep 2235113 = 1676335) B1676335
theorem B1679777 : Blo 291829 1679777 := bstep (se 2 (by rfl) ⟨629916, by rfl⟩ : syracuseStep 1679777 = 1259833) B1259833
theorem B836095 : Blo 291829 836095 := bstep (se 1 (by rfl) ⟨627071, by rfl⟩ : syracuseStep 836095 = 1254143) B1254143
theorem B1331329 : Blo 291829 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B3790313 : Blo 291829 3790313 := bstep (se 2 (by rfl) ⟨1421367, by rfl⟩ : syracuseStep 3790313 = 2842735) B2842735
theorem B744167 : Blo 291829 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B1007815 : Blo 291829 1007815 := bstep (se 1 (by rfl) ⟨755861, by rfl⟩ : syracuseStep 1007815 = 1511723) B1511723
theorem B232714775 : Blo 291829 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B1668863 : Blo 291829 1668863 := bstep (se 1 (by rfl) ⟨1251647, by rfl⟩ : syracuseStep 1668863 = 2503295) B2503295
theorem B293423 : Blo 291829 293423 := bstep (se 1 (by rfl) ⟨220067, by rfl⟩ : syracuseStep 293423 = 440135) B440135
theorem B2227337 : Blo 291829 2227337 := bstep (se 2 (by rfl) ⟨835251, by rfl⟩ : syracuseStep 2227337 = 1670503) B1670503
theorem B294399 : Blo 291829 294399 := bstep (se 1 (by rfl) ⟨220799, by rfl⟩ : syracuseStep 294399 = 441599) B441599
theorem B1343753 : Blo 291829 1343753 := bstep (se 2 (by rfl) ⟨503907, by rfl⟩ : syracuseStep 1343753 = 1007815) B1007815
theorem B1114793 : Blo 291829 1114793 := bstep (se 2 (by rfl) ⟨418047, by rfl⟩ : syracuseStep 1114793 = 836095) B836095
theorem B2526875 : Blo 291829 2526875 := bstep (se 1 (by rfl) ⟨1895156, by rfl⟩ : syracuseStep 2526875 = 3790313) B3790313
theorem B496111 : Blo 291829 496111 := bstep (se 1 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 496111 = 744167) B744167
theorem B1775105 : Blo 291829 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B1119851 : Blo 291829 1119851 := bstep (se 1 (by rfl) ⟨839888, by rfl⟩ : syracuseStep 1119851 = 1679777) B1679777
theorem B1484891 : Blo 291829 1484891 := bstep (se 1 (by rfl) ⟨1113668, by rfl⟩ : syracuseStep 1484891 = 2227337) B2227337
theorem B440441 : Blo 291829 440441 := bstep (se 2 (by rfl) ⟨165165, by rfl⟩ : syracuseStep 440441 = 330331) B330331
theorem B1490075 : Blo 291829 1490075 := bstep (se 1 (by rfl) ⟨1117556, by rfl⟩ : syracuseStep 1490075 = 2235113) B2235113
theorem B155143183 : Blo 291829 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B1112575 : Blo 291829 1112575 := bstep (se 1 (by rfl) ⟨834431, by rfl⟩ : syracuseStep 1112575 = 1668863) B1668863
theorem B1183403 : Blo 291829 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B661481 : Blo 291829 661481 := bstep (se 2 (by rfl) ⟨248055, by rfl⟩ : syracuseStep 661481 = 496111) B496111
theorem B989927 : Blo 291829 989927 := bstep (se 1 (by rfl) ⟨742445, by rfl⟩ : syracuseStep 989927 = 1484891) B1484891
theorem B1483433 : Blo 291829 1483433 := bstep (se 2 (by rfl) ⟨556287, by rfl⟩ : syracuseStep 1483433 = 1112575) B1112575
theorem B993383 : Blo 291829 993383 := bstep (se 1 (by rfl) ⟨745037, by rfl⟩ : syracuseStep 993383 = 1490075) B1490075
theorem B895835 : Blo 291829 895835 := bstep (se 1 (by rfl) ⟨671876, by rfl⟩ : syracuseStep 895835 = 1343753) B1343753
theorem B1684583 : Blo 291829 1684583 := bstep (se 1 (by rfl) ⟨1263437, by rfl⟩ : syracuseStep 1684583 = 2526875) B2526875
theorem B743195 : Blo 291829 743195 := bstep (se 1 (by rfl) ⟨557396, by rfl⟩ : syracuseStep 743195 = 1114793) B1114793
theorem B746567 : Blo 291829 746567 := bstep (se 1 (by rfl) ⟨559925, by rfl⟩ : syracuseStep 746567 = 1119851) B1119851
theorem B206857577 : Blo 291829 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B293627 : Blo 291829 293627 := bstep (se 1 (by rfl) ⟨220220, by rfl⟩ : syracuseStep 293627 = 440441) B440441
theorem B788935 : Blo 291829 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B495463 : Blo 291829 495463 := bstep (se 1 (by rfl) ⟨371597, by rfl⟩ : syracuseStep 495463 = 743195) B743195
theorem B659951 : Blo 291829 659951 := bstep (se 1 (by rfl) ⟨494963, by rfl⟩ : syracuseStep 659951 = 989927) B989927
theorem B988955 : Blo 291829 988955 := bstep (se 1 (by rfl) ⟨741716, by rfl⟩ : syracuseStep 988955 = 1483433) B1483433
theorem B497711 : Blo 291829 497711 := bstep (se 1 (by rfl) ⟨373283, by rfl⟩ : syracuseStep 497711 = 746567) B746567
theorem B662255 : Blo 291829 662255 := bstep (se 1 (by rfl) ⟨496691, by rfl⟩ : syracuseStep 662255 = 993383) B993383
theorem B597223 : Blo 291829 597223 := bstep (se 1 (by rfl) ⟨447917, by rfl⟩ : syracuseStep 597223 = 895835) B895835
theorem B1123055 : Blo 291829 1123055 := bstep (se 1 (by rfl) ⟨842291, by rfl⟩ : syracuseStep 1123055 = 1684583) B1684583
theorem B440987 : Blo 291829 440987 := bstep (se 1 (by rfl) ⟨330740, by rfl⟩ : syracuseStep 440987 = 661481) B661481
theorem B137905051 : Blo 291829 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B1051913 : Blo 291829 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B659303 : Blo 291829 659303 := bstep (se 1 (by rfl) ⟨494477, by rfl⟩ : syracuseStep 659303 = 988955) B988955
theorem B331807 : Blo 291829 331807 := bstep (se 1 (by rfl) ⟨248855, by rfl⟩ : syracuseStep 331807 = 497711) B497711
theorem B660617 : Blo 291829 660617 := bstep (se 2 (by rfl) ⟨247731, by rfl⟩ : syracuseStep 660617 = 495463) B495463
theorem B3185189 : Blo 291829 3185189 := bstep (se 4 (by rfl) ⟨298611, by rfl⟩ : syracuseStep 3185189 = 597223) B597223
theorem B183873401 : Blo 291829 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B439967 : Blo 291829 439967 := bstep (se 1 (by rfl) ⟨329975, by rfl⟩ : syracuseStep 439967 = 659951) B659951
theorem B441503 : Blo 291829 441503 := bstep (se 1 (by rfl) ⟨331127, by rfl⟩ : syracuseStep 441503 = 662255) B662255
theorem B748703 : Blo 291829 748703 := bstep (se 1 (by rfl) ⟨561527, by rfl⟩ : syracuseStep 748703 = 1123055) B1123055
theorem B293991 : Blo 291829 293991 := bstep (se 1 (by rfl) ⟨220493, by rfl⟩ : syracuseStep 293991 = 440987) B440987
theorem B499135 : Blo 291829 499135 := bstep (se 1 (by rfl) ⟨374351, by rfl⟩ : syracuseStep 499135 = 748703) B748703
theorem B439535 : Blo 291829 439535 := bstep (se 1 (by rfl) ⟨329651, by rfl⟩ : syracuseStep 439535 = 659303) B659303
theorem B440411 : Blo 291829 440411 := bstep (se 1 (by rfl) ⟨330308, by rfl⟩ : syracuseStep 440411 = 660617) B660617
theorem B442409 : Blo 291829 442409 := bstep (se 2 (by rfl) ⟨165903, by rfl⟩ : syracuseStep 442409 = 331807) B331807
theorem B2805101 : Blo 291829 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B2123459 : Blo 291829 2123459 := bstep (se 1 (by rfl) ⟨1592594, by rfl⟩ : syracuseStep 2123459 = 3185189) B3185189
theorem B122582267 : Blo 291829 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B293311 : Blo 291829 293311 := bstep (se 1 (by rfl) ⟨219983, by rfl⟩ : syracuseStep 293311 = 439967) B439967
theorem B294335 : Blo 291829 294335 := bstep (se 1 (by rfl) ⟨220751, by rfl⟩ : syracuseStep 294335 = 441503) B441503
theorem B294939 : Blo 291829 294939 := bstep (se 1 (by rfl) ⟨221204, by rfl⟩ : syracuseStep 294939 = 442409) B442409
theorem B1870067 : Blo 291829 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B1415639 : Blo 291829 1415639 := bstep (se 1 (by rfl) ⟨1061729, by rfl⟩ : syracuseStep 1415639 = 2123459) B2123459
theorem B665513 : Blo 291829 665513 := bstep (se 2 (by rfl) ⟨249567, by rfl⟩ : syracuseStep 665513 = 499135) B499135
theorem B293023 : Blo 291829 293023 := bstep (se 1 (by rfl) ⟨219767, by rfl⟩ : syracuseStep 293023 = 439535) B439535
theorem B81721511 : Blo 291829 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B293607 : Blo 291829 293607 := bstep (se 1 (by rfl) ⟨220205, by rfl⟩ : syracuseStep 293607 = 440411) B440411
theorem B1246711 : Blo 291829 1246711 := bstep (se 1 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 1246711 = 1870067) B1870067
theorem B443675 : Blo 291829 443675 := bstep (se 1 (by rfl) ⟨332756, by rfl⟩ : syracuseStep 443675 = 665513) B665513
theorem B54481007 : Blo 291829 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B943759 : Blo 291829 943759 := bstep (se 1 (by rfl) ⟨707819, by rfl⟩ : syracuseStep 943759 = 1415639) B1415639
theorem B295783 : Blo 291829 295783 := bstep (se 1 (by rfl) ⟨221837, by rfl⟩ : syracuseStep 295783 = 443675) B443675
theorem B1258345 : Blo 291829 1258345 := bstep (se 2 (by rfl) ⟨471879, by rfl⟩ : syracuseStep 1258345 = 943759) B943759
theorem B36320671 : Blo 291829 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B1662281 : Blo 291829 1662281 := bstep (se 2 (by rfl) ⟨623355, by rfl⟩ : syracuseStep 1662281 = 1246711) B1246711
theorem B1677793 : Blo 291829 1677793 := bstep (se 2 (by rfl) ⟨629172, by rfl⟩ : syracuseStep 1677793 = 1258345) B1258345
theorem B1108187 : Blo 291829 1108187 := bstep (se 1 (by rfl) ⟨831140, by rfl⟩ : syracuseStep 1108187 = 1662281) B1662281
theorem B48427561 : Blo 291829 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B2237057 : Blo 291829 2237057 := bstep (se 2 (by rfl) ⟨838896, by rfl⟩ : syracuseStep 2237057 = 1677793) B1677793
theorem B64570081 : Blo 291829 64570081 := bstep (se 2 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 64570081 = 48427561) B48427561
theorem B738791 : Blo 291829 738791 := bstep (se 1 (by rfl) ⟨554093, by rfl⟩ : syracuseStep 738791 = 1108187) B1108187
theorem B492527 : Blo 291829 492527 := bstep (se 1 (by rfl) ⟨369395, by rfl⟩ : syracuseStep 492527 = 738791) B738791
theorem B86093441 : Blo 291829 86093441 := bstep (se 2 (by rfl) ⟨32285040, by rfl⟩ : syracuseStep 86093441 = 64570081) B64570081
theorem B1491371 : Blo 291829 1491371 := bstep (se 1 (by rfl) ⟨1118528, by rfl⟩ : syracuseStep 1491371 = 2237057) B2237057
theorem B328351 : Blo 291829 328351 := bstep (se 1 (by rfl) ⟨246263, by rfl⟩ : syracuseStep 328351 = 492527) B492527
theorem B994247 : Blo 291829 994247 := bstep (se 1 (by rfl) ⟨745685, by rfl⟩ : syracuseStep 994247 = 1491371) B1491371
theorem B57395627 : Blo 291829 57395627 := bstep (se 1 (by rfl) ⟨43046720, by rfl⟩ : syracuseStep 57395627 = 86093441) B86093441
theorem B662831 : Blo 291829 662831 := bstep (se 1 (by rfl) ⟨497123, by rfl⟩ : syracuseStep 662831 = 994247) B994247
theorem B437801 : Blo 291829 437801 := bstep (se 2 (by rfl) ⟨164175, by rfl⟩ : syracuseStep 437801 = 328351) B328351
theorem B38263751 : Blo 291829 38263751 := bstep (se 1 (by rfl) ⟨28697813, by rfl⟩ : syracuseStep 38263751 = 57395627) B57395627
theorem B25509167 : Blo 291829 25509167 := bstep (se 1 (by rfl) ⟨19131875, by rfl⟩ : syracuseStep 25509167 = 38263751) B38263751
theorem B441887 : Blo 291829 441887 := bstep (se 1 (by rfl) ⟨331415, by rfl⟩ : syracuseStep 441887 = 662831) B662831
theorem B291867 : Blo 291829 291867 := bstep (se 1 (by rfl) ⟨218900, by rfl⟩ : syracuseStep 291867 = 437801) B437801
theorem B17006111 : Blo 291829 17006111 := bstep (se 1 (by rfl) ⟨12754583, by rfl⟩ : syracuseStep 17006111 = 25509167) B25509167
theorem B294591 : Blo 291829 294591 := bstep (se 1 (by rfl) ⟨220943, by rfl⟩ : syracuseStep 294591 = 441887) B441887
theorem B11337407 : Blo 291829 11337407 := bstep (se 1 (by rfl) ⟨8503055, by rfl⟩ : syracuseStep 11337407 = 17006111) B17006111
theorem B7558271 : Blo 291829 7558271 := bstep (se 1 (by rfl) ⟨5668703, by rfl⟩ : syracuseStep 7558271 = 11337407) B11337407
theorem B5038847 : Blo 291829 5038847 := bstep (se 1 (by rfl) ⟨3779135, by rfl⟩ : syracuseStep 5038847 = 7558271) B7558271
theorem B3359231 : Blo 291829 3359231 := bstep (se 1 (by rfl) ⟨2519423, by rfl⟩ : syracuseStep 3359231 = 5038847) B5038847
theorem B2239487 : Blo 291829 2239487 := bstep (se 1 (by rfl) ⟨1679615, by rfl⟩ : syracuseStep 2239487 = 3359231) B3359231
theorem B1492991 : Blo 291829 1492991 := bstep (se 1 (by rfl) ⟨1119743, by rfl⟩ : syracuseStep 1492991 = 2239487) B2239487
theorem B995327 : Blo 291829 995327 := bstep (se 1 (by rfl) ⟨746495, by rfl⟩ : syracuseStep 995327 = 1492991) B1492991
theorem B663551 : Blo 291829 663551 := bstep (se 1 (by rfl) ⟨497663, by rfl⟩ : syracuseStep 663551 = 995327) B995327
theorem B442367 : Blo 291829 442367 := bstep (se 1 (by rfl) ⟨331775, by rfl⟩ : syracuseStep 442367 = 663551) B663551
theorem B294911 : Blo 291829 294911 := bstep (se 1 (by rfl) ⟨221183, by rfl⟩ : syracuseStep 294911 = 442367) B442367

theorem C0 (j : ℕ) (h1 : 72957 ≤ j) (h2 : j ≤ 73656) : Blo 291829 (4 * j + 3) := by
  interval_cases j
  · exact B291831
  · exact B291835
  · exact B291839
  · exact B291843
  · exact B291847
  · exact B291851
  · exact B291855
  · exact B291859
  · exact B291863
  · exact B291867
  · exact B291871
  · exact B291875
  · exact B291879
  · exact B291883
  · exact B291887
  · exact B291891
  · exact B291895
  · exact B291899
  · exact B291903
  · exact B291907
  · exact B291911
  · exact B291915
  · exact B291919
  · exact B291923
  · exact B291927
  · exact B291931
  · exact B291935
  · exact B291939
  · exact B291943
  · exact B291947
  · exact B291951
  · exact B291955
  · exact B291959
  · exact B291963
  · exact B291967
  · exact B291971
  · exact B291975
  · exact B291979
  · exact B291983
  · exact B291987
  · exact B291991
  · exact B291995
  · exact B291999
  · exact B292003
  · exact B292007
  · exact B292011
  · exact B292015
  · exact B292019
  · exact B292023
  · exact B292027
  · exact B292031
  · exact B292035
  · exact B292039
  · exact B292043
  · exact B292047
  · exact B292051
  · exact B292055
  · exact B292059
  · exact B292063
  · exact B292067
  · exact B292071
  · exact B292075
  · exact B292079
  · exact B292083
  · exact B292087
  · exact B292091
  · exact B292095
  · exact B292099
  · exact B292103
  · exact B292107
  · exact B292111
  · exact B292115
  · exact B292119
  · exact B292123
  · exact B292127
  · exact B292131
  · exact B292135
  · exact B292139
  · exact B292143
  · exact B292147
  · exact B292151
  · exact B292155
  · exact B292159
  · exact B292163
  · exact B292167
  · exact B292171
  · exact B292175
  · exact B292179
  · exact B292183
  · exact B292187
  · exact B292191
  · exact B292195
  · exact B292199
  · exact B292203
  · exact B292207
  · exact B292211
  · exact B292215
  · exact B292219
  · exact B292223
  · exact B292227
  · exact B292231
  · exact B292235
  · exact B292239
  · exact B292243
  · exact B292247
  · exact B292251
  · exact B292255
  · exact B292259
  · exact B292263
  · exact B292267
  · exact B292271
  · exact B292275
  · exact B292279
  · exact B292283
  · exact B292287
  · exact B292291
  · exact B292295
  · exact B292299
  · exact B292303
  · exact B292307
  · exact B292311
  · exact B292315
  · exact B292319
  · exact B292323
  · exact B292327
  · exact B292331
  · exact B292335
  · exact B292339
  · exact B292343
  · exact B292347
  · exact B292351
  · exact B292355
  · exact B292359
  · exact B292363
  · exact B292367
  · exact B292371
  · exact B292375
  · exact B292379
  · exact B292383
  · exact B292387
  · exact B292391
  · exact B292395
  · exact B292399
  · exact B292403
  · exact B292407
  · exact B292411
  · exact B292415
  · exact B292419
  · exact B292423
  · exact B292427
  · exact B292431
  · exact B292435
  · exact B292439
  · exact B292443
  · exact B292447
  · exact B292451
  · exact B292455
  · exact B292459
  · exact B292463
  · exact B292467
  · exact B292471
  · exact B292475
  · exact B292479
  · exact B292483
  · exact B292487
  · exact B292491
  · exact B292495
  · exact B292499
  · exact B292503
  · exact B292507
  · exact B292511
  · exact B292515
  · exact B292519
  · exact B292523
  · exact B292527
  · exact B292531
  · exact B292535
  · exact B292539
  · exact B292543
  · exact B292547
  · exact B292551
  · exact B292555
  · exact B292559
  · exact B292563
  · exact B292567
  · exact B292571
  · exact B292575
  · exact B292579
  · exact B292583
  · exact B292587
  · exact B292591
  · exact B292595
  · exact B292599
  · exact B292603
  · exact B292607
  · exact B292611
  · exact B292615
  · exact B292619
  · exact B292623
  · exact B292627
  · exact B292631
  · exact B292635
  · exact B292639
  · exact B292643
  · exact B292647
  · exact B292651
  · exact B292655
  · exact B292659
  · exact B292663
  · exact B292667
  · exact B292671
  · exact B292675
  · exact B292679
  · exact B292683
  · exact B292687
  · exact B292691
  · exact B292695
  · exact B292699
  · exact B292703
  · exact B292707
  · exact B292711
  · exact B292715
  · exact B292719
  · exact B292723
  · exact B292727
  · exact B292731
  · exact B292735
  · exact B292739
  · exact B292743
  · exact B292747
  · exact B292751
  · exact B292755
  · exact B292759
  · exact B292763
  · exact B292767
  · exact B292771
  · exact B292775
  · exact B292779
  · exact B292783
  · exact B292787
  · exact B292791
  · exact B292795
  · exact B292799
  · exact B292803
  · exact B292807
  · exact B292811
  · exact B292815
  · exact B292819
  · exact B292823
  · exact B292827
  · exact B292831
  · exact B292835
  · exact B292839
  · exact B292843
  · exact B292847
  · exact B292851
  · exact B292855
  · exact B292859
  · exact B292863
  · exact B292867
  · exact B292871
  · exact B292875
  · exact B292879
  · exact B292883
  · exact B292887
  · exact B292891
  · exact B292895
  · exact B292899
  · exact B292903
  · exact B292907
  · exact B292911
  · exact B292915
  · exact B292919
  · exact B292923
  · exact B292927
  · exact B292931
  · exact B292935
  · exact B292939
  · exact B292943
  · exact B292947
  · exact B292951
  · exact B292955
  · exact B292959
  · exact B292963
  · exact B292967
  · exact B292971
  · exact B292975
  · exact B292979
  · exact B292983
  · exact B292987
  · exact B292991
  · exact B292995
  · exact B292999
  · exact B293003
  · exact B293007
  · exact B293011
  · exact B293015
  · exact B293019
  · exact B293023
  · exact B293027
  · exact B293031
  · exact B293035
  · exact B293039
  · exact B293043
  · exact B293047
  · exact B293051
  · exact B293055
  · exact B293059
  · exact B293063
  · exact B293067
  · exact B293071
  · exact B293075
  · exact B293079
  · exact B293083
  · exact B293087
  · exact B293091
  · exact B293095
  · exact B293099
  · exact B293103
  · exact B293107
  · exact B293111
  · exact B293115
  · exact B293119
  · exact B293123
  · exact B293127
  · exact B293131
  · exact B293135
  · exact B293139
  · exact B293143
  · exact B293147
  · exact B293151
  · exact B293155
  · exact B293159
  · exact B293163
  · exact B293167
  · exact B293171
  · exact B293175
  · exact B293179
  · exact B293183
  · exact B293187
  · exact B293191
  · exact B293195
  · exact B293199
  · exact B293203
  · exact B293207
  · exact B293211
  · exact B293215
  · exact B293219
  · exact B293223
  · exact B293227
  · exact B293231
  · exact B293235
  · exact B293239
  · exact B293243
  · exact B293247
  · exact B293251
  · exact B293255
  · exact B293259
  · exact B293263
  · exact B293267
  · exact B293271
  · exact B293275
  · exact B293279
  · exact B293283
  · exact B293287
  · exact B293291
  · exact B293295
  · exact B293299
  · exact B293303
  · exact B293307
  · exact B293311
  · exact B293315
  · exact B293319
  · exact B293323
  · exact B293327
  · exact B293331
  · exact B293335
  · exact B293339
  · exact B293343
  · exact B293347
  · exact B293351
  · exact B293355
  · exact B293359
  · exact B293363
  · exact B293367
  · exact B293371
  · exact B293375
  · exact B293379
  · exact B293383
  · exact B293387
  · exact B293391
  · exact B293395
  · exact B293399
  · exact B293403
  · exact B293407
  · exact B293411
  · exact B293415
  · exact B293419
  · exact B293423
  · exact B293427
  · exact B293431
  · exact B293435
  · exact B293439
  · exact B293443
  · exact B293447
  · exact B293451
  · exact B293455
  · exact B293459
  · exact B293463
  · exact B293467
  · exact B293471
  · exact B293475
  · exact B293479
  · exact B293483
  · exact B293487
  · exact B293491
  · exact B293495
  · exact B293499
  · exact B293503
  · exact B293507
  · exact B293511
  · exact B293515
  · exact B293519
  · exact B293523
  · exact B293527
  · exact B293531
  · exact B293535
  · exact B293539
  · exact B293543
  · exact B293547
  · exact B293551
  · exact B293555
  · exact B293559
  · exact B293563
  · exact B293567
  · exact B293571
  · exact B293575
  · exact B293579
  · exact B293583
  · exact B293587
  · exact B293591
  · exact B293595
  · exact B293599
  · exact B293603
  · exact B293607
  · exact B293611
  · exact B293615
  · exact B293619
  · exact B293623
  · exact B293627
  · exact B293631
  · exact B293635
  · exact B293639
  · exact B293643
  · exact B293647
  · exact B293651
  · exact B293655
  · exact B293659
  · exact B293663
  · exact B293667
  · exact B293671
  · exact B293675
  · exact B293679
  · exact B293683
  · exact B293687
  · exact B293691
  · exact B293695
  · exact B293699
  · exact B293703
  · exact B293707
  · exact B293711
  · exact B293715
  · exact B293719
  · exact B293723
  · exact B293727
  · exact B293731
  · exact B293735
  · exact B293739
  · exact B293743
  · exact B293747
  · exact B293751
  · exact B293755
  · exact B293759
  · exact B293763
  · exact B293767
  · exact B293771
  · exact B293775
  · exact B293779
  · exact B293783
  · exact B293787
  · exact B293791
  · exact B293795
  · exact B293799
  · exact B293803
  · exact B293807
  · exact B293811
  · exact B293815
  · exact B293819
  · exact B293823
  · exact B293827
  · exact B293831
  · exact B293835
  · exact B293839
  · exact B293843
  · exact B293847
  · exact B293851
  · exact B293855
  · exact B293859
  · exact B293863
  · exact B293867
  · exact B293871
  · exact B293875
  · exact B293879
  · exact B293883
  · exact B293887
  · exact B293891
  · exact B293895
  · exact B293899
  · exact B293903
  · exact B293907
  · exact B293911
  · exact B293915
  · exact B293919
  · exact B293923
  · exact B293927
  · exact B293931
  · exact B293935
  · exact B293939
  · exact B293943
  · exact B293947
  · exact B293951
  · exact B293955
  · exact B293959
  · exact B293963
  · exact B293967
  · exact B293971
  · exact B293975
  · exact B293979
  · exact B293983
  · exact B293987
  · exact B293991
  · exact B293995
  · exact B293999
  · exact B294003
  · exact B294007
  · exact B294011
  · exact B294015
  · exact B294019
  · exact B294023
  · exact B294027
  · exact B294031
  · exact B294035
  · exact B294039
  · exact B294043
  · exact B294047
  · exact B294051
  · exact B294055
  · exact B294059
  · exact B294063
  · exact B294067
  · exact B294071
  · exact B294075
  · exact B294079
  · exact B294083
  · exact B294087
  · exact B294091
  · exact B294095
  · exact B294099
  · exact B294103
  · exact B294107
  · exact B294111
  · exact B294115
  · exact B294119
  · exact B294123
  · exact B294127
  · exact B294131
  · exact B294135
  · exact B294139
  · exact B294143
  · exact B294147
  · exact B294151
  · exact B294155
  · exact B294159
  · exact B294163
  · exact B294167
  · exact B294171
  · exact B294175
  · exact B294179
  · exact B294183
  · exact B294187
  · exact B294191
  · exact B294195
  · exact B294199
  · exact B294203
  · exact B294207
  · exact B294211
  · exact B294215
  · exact B294219
  · exact B294223
  · exact B294227
  · exact B294231
  · exact B294235
  · exact B294239
  · exact B294243
  · exact B294247
  · exact B294251
  · exact B294255
  · exact B294259
  · exact B294263
  · exact B294267
  · exact B294271
  · exact B294275
  · exact B294279
  · exact B294283
  · exact B294287
  · exact B294291
  · exact B294295
  · exact B294299
  · exact B294303
  · exact B294307
  · exact B294311
  · exact B294315
  · exact B294319
  · exact B294323
  · exact B294327
  · exact B294331
  · exact B294335
  · exact B294339
  · exact B294343
  · exact B294347
  · exact B294351
  · exact B294355
  · exact B294359
  · exact B294363
  · exact B294367
  · exact B294371
  · exact B294375
  · exact B294379
  · exact B294383
  · exact B294387
  · exact B294391
  · exact B294395
  · exact B294399
  · exact B294403
  · exact B294407
  · exact B294411
  · exact B294415
  · exact B294419
  · exact B294423
  · exact B294427
  · exact B294431
  · exact B294435
  · exact B294439
  · exact B294443
  · exact B294447
  · exact B294451
  · exact B294455
  · exact B294459
  · exact B294463
  · exact B294467
  · exact B294471
  · exact B294475
  · exact B294479
  · exact B294483
  · exact B294487
  · exact B294491
  · exact B294495
  · exact B294499
  · exact B294503
  · exact B294507
  · exact B294511
  · exact B294515
  · exact B294519
  · exact B294523
  · exact B294527
  · exact B294531
  · exact B294535
  · exact B294539
  · exact B294543
  · exact B294547
  · exact B294551
  · exact B294555
  · exact B294559
  · exact B294563
  · exact B294567
  · exact B294571
  · exact B294575
  · exact B294579
  · exact B294583
  · exact B294587
  · exact B294591
  · exact B294595
  · exact B294599
  · exact B294603
  · exact B294607
  · exact B294611
  · exact B294615
  · exact B294619
  · exact B294623
  · exact B294627

theorem C1 (j : ℕ) (h1 : 73657 ≤ j) (h2 : j ≤ 73956) : Blo 291829 (4 * j + 3) := by
  interval_cases j
  · exact B294631
  · exact B294635
  · exact B294639
  · exact B294643
  · exact B294647
  · exact B294651
  · exact B294655
  · exact B294659
  · exact B294663
  · exact B294667
  · exact B294671
  · exact B294675
  · exact B294679
  · exact B294683
  · exact B294687
  · exact B294691
  · exact B294695
  · exact B294699
  · exact B294703
  · exact B294707
  · exact B294711
  · exact B294715
  · exact B294719
  · exact B294723
  · exact B294727
  · exact B294731
  · exact B294735
  · exact B294739
  · exact B294743
  · exact B294747
  · exact B294751
  · exact B294755
  · exact B294759
  · exact B294763
  · exact B294767
  · exact B294771
  · exact B294775
  · exact B294779
  · exact B294783
  · exact B294787
  · exact B294791
  · exact B294795
  · exact B294799
  · exact B294803
  · exact B294807
  · exact B294811
  · exact B294815
  · exact B294819
  · exact B294823
  · exact B294827
  · exact B294831
  · exact B294835
  · exact B294839
  · exact B294843
  · exact B294847
  · exact B294851
  · exact B294855
  · exact B294859
  · exact B294863
  · exact B294867
  · exact B294871
  · exact B294875
  · exact B294879
  · exact B294883
  · exact B294887
  · exact B294891
  · exact B294895
  · exact B294899
  · exact B294903
  · exact B294907
  · exact B294911
  · exact B294915
  · exact B294919
  · exact B294923
  · exact B294927
  · exact B294931
  · exact B294935
  · exact B294939
  · exact B294943
  · exact B294947
  · exact B294951
  · exact B294955
  · exact B294959
  · exact B294963
  · exact B294967
  · exact B294971
  · exact B294975
  · exact B294979
  · exact B294983
  · exact B294987
  · exact B294991
  · exact B294995
  · exact B294999
  · exact B295003
  · exact B295007
  · exact B295011
  · exact B295015
  · exact B295019
  · exact B295023
  · exact B295027
  · exact B295031
  · exact B295035
  · exact B295039
  · exact B295043
  · exact B295047
  · exact B295051
  · exact B295055
  · exact B295059
  · exact B295063
  · exact B295067
  · exact B295071
  · exact B295075
  · exact B295079
  · exact B295083
  · exact B295087
  · exact B295091
  · exact B295095
  · exact B295099
  · exact B295103
  · exact B295107
  · exact B295111
  · exact B295115
  · exact B295119
  · exact B295123
  · exact B295127
  · exact B295131
  · exact B295135
  · exact B295139
  · exact B295143
  · exact B295147
  · exact B295151
  · exact B295155
  · exact B295159
  · exact B295163
  · exact B295167
  · exact B295171
  · exact B295175
  · exact B295179
  · exact B295183
  · exact B295187
  · exact B295191
  · exact B295195
  · exact B295199
  · exact B295203
  · exact B295207
  · exact B295211
  · exact B295215
  · exact B295219
  · exact B295223
  · exact B295227
  · exact B295231
  · exact B295235
  · exact B295239
  · exact B295243
  · exact B295247
  · exact B295251
  · exact B295255
  · exact B295259
  · exact B295263
  · exact B295267
  · exact B295271
  · exact B295275
  · exact B295279
  · exact B295283
  · exact B295287
  · exact B295291
  · exact B295295
  · exact B295299
  · exact B295303
  · exact B295307
  · exact B295311
  · exact B295315
  · exact B295319
  · exact B295323
  · exact B295327
  · exact B295331
  · exact B295335
  · exact B295339
  · exact B295343
  · exact B295347
  · exact B295351
  · exact B295355
  · exact B295359
  · exact B295363
  · exact B295367
  · exact B295371
  · exact B295375
  · exact B295379
  · exact B295383
  · exact B295387
  · exact B295391
  · exact B295395
  · exact B295399
  · exact B295403
  · exact B295407
  · exact B295411
  · exact B295415
  · exact B295419
  · exact B295423
  · exact B295427
  · exact B295431
  · exact B295435
  · exact B295439
  · exact B295443
  · exact B295447
  · exact B295451
  · exact B295455
  · exact B295459
  · exact B295463
  · exact B295467
  · exact B295471
  · exact B295475
  · exact B295479
  · exact B295483
  · exact B295487
  · exact B295491
  · exact B295495
  · exact B295499
  · exact B295503
  · exact B295507
  · exact B295511
  · exact B295515
  · exact B295519
  · exact B295523
  · exact B295527
  · exact B295531
  · exact B295535
  · exact B295539
  · exact B295543
  · exact B295547
  · exact B295551
  · exact B295555
  · exact B295559
  · exact B295563
  · exact B295567
  · exact B295571
  · exact B295575
  · exact B295579
  · exact B295583
  · exact B295587
  · exact B295591
  · exact B295595
  · exact B295599
  · exact B295603
  · exact B295607
  · exact B295611
  · exact B295615
  · exact B295619
  · exact B295623
  · exact B295627
  · exact B295631
  · exact B295635
  · exact B295639
  · exact B295643
  · exact B295647
  · exact B295651
  · exact B295655
  · exact B295659
  · exact B295663
  · exact B295667
  · exact B295671
  · exact B295675
  · exact B295679
  · exact B295683
  · exact B295687
  · exact B295691
  · exact B295695
  · exact B295699
  · exact B295703
  · exact B295707
  · exact B295711
  · exact B295715
  · exact B295719
  · exact B295723
  · exact B295727
  · exact B295731
  · exact B295735
  · exact B295739
  · exact B295743
  · exact B295747
  · exact B295751
  · exact B295755
  · exact B295759
  · exact B295763
  · exact B295767
  · exact B295771
  · exact B295775
  · exact B295779
  · exact B295783
  · exact B295787
  · exact B295791
  · exact B295795
  · exact B295799
  · exact B295803
  · exact B295807
  · exact B295811
  · exact B295815
  · exact B295819
  · exact B295823
  · exact B295827

theorem solution (m : ℕ) (hlo : 291829 ≤ m) (hhi : m ≤ 295829) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 72957 ≤ j := by omega
    have hj2 : j ≤ 73956 := by omega
    have hb : Blo 291829 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 73657 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
