-- Prove2me | solution 1 for syracuse_descends_range_467785_471785
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:03.428409+00:00
-- url     : https://prove2.me/submissions/90a4f26e-d929-4169-9b23-a561c9996aba

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


theorem B1507493 : Blo 467785 1507493 := bbase (se 4 (by rfl) ⟨141327, by rfl⟩ : syracuseStep 1507493 = 282655) (by norm_num)
theorem B753965 : Blo 467785 753965 := bbase (se 3 (by rfl) ⟨141368, by rfl⟩ : syracuseStep 753965 = 282737) (by norm_num)
theorem B2261317 : Blo 467785 2261317 := bbase (se 4 (by rfl) ⟨211998, by rfl⟩ : syracuseStep 2261317 = 423997) (by norm_num)
theorem B754157 : Blo 467785 754157 := bbase (se 3 (by rfl) ⟨141404, by rfl⟩ : syracuseStep 754157 = 282809) (by norm_num)
theorem B1901045 : Blo 467785 1901045 := bbase (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) (by norm_num)
theorem B1999397 : Blo 467785 1999397 := bbase (se 4 (by rfl) ⟨187443, by rfl⟩ : syracuseStep 1999397 = 374887) (by norm_num)
theorem B754285 : Blo 467785 754285 := bbase (se 3 (by rfl) ⟨141428, by rfl⟩ : syracuseStep 754285 = 282857) (by norm_num)
theorem B1508005 : Blo 467785 1508005 := bbase (se 4 (by rfl) ⟨141375, by rfl⟩ : syracuseStep 1508005 = 282751) (by norm_num)
theorem B1999637 : Blo 467785 1999637 := bbase (se 6 (by rfl) ⟨46866, by rfl⟩ : syracuseStep 1999637 = 93733) (by norm_num)
theorem B951205 : Blo 467785 951205 := bbase (se 4 (by rfl) ⟨89175, by rfl⟩ : syracuseStep 951205 = 178351) (by norm_num)
theorem B951301 : Blo 467785 951301 := bbase (se 4 (by rfl) ⟨89184, by rfl⟩ : syracuseStep 951301 = 178369) (by norm_num)
theorem B754925 : Blo 467785 754925 := bbase (se 3 (by rfl) ⟨141548, by rfl⟩ : syracuseStep 754925 = 283097) (by norm_num)
theorem B951725 : Blo 467785 951725 := bbase (se 3 (by rfl) ⟨178448, by rfl⟩ : syracuseStep 951725 = 356897) (by norm_num)
theorem B755381 : Blo 467785 755381 := bbase (se 5 (by rfl) ⟨35408, by rfl⟩ : syracuseStep 755381 = 70817) (by norm_num)
theorem B3573557 : Blo 467785 3573557 := bbase (se 5 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 3573557 = 335021) (by norm_num)
theorem B1148773 : Blo 467785 1148773 := bbase (se 4 (by rfl) ⟨107697, by rfl⟩ : syracuseStep 1148773 = 215395) (by norm_num)
theorem B755605 : Blo 467785 755605 := bbase (se 6 (by rfl) ⟨17709, by rfl⟩ : syracuseStep 755605 = 35419) (by norm_num)
theorem B526261 : Blo 467785 526261 := bbase (se 5 (by rfl) ⟨24668, by rfl⟩ : syracuseStep 526261 = 49337) (by norm_num)
theorem B3213269 : Blo 467785 3213269 := bbase (se 7 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 3213269 = 75311) (by norm_num)
theorem B755669 : Blo 467785 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B526297 : Blo 467785 526297 := bbase (se 2 (by rfl) ⟨197361, by rfl⟩ : syracuseStep 526297 = 394723) (by norm_num)
theorem B526333 : Blo 467785 526333 := bbase (se 3 (by rfl) ⟨98687, by rfl⟩ : syracuseStep 526333 = 197375) (by norm_num)
theorem B9635861 : Blo 467785 9635861 := bbase (se 6 (by rfl) ⟨225840, by rfl⟩ : syracuseStep 9635861 = 451681) (by norm_num)
theorem B526369 : Blo 467785 526369 := bbase (se 2 (by rfl) ⟨197388, by rfl⟩ : syracuseStep 526369 = 394777) (by norm_num)
theorem B526405 : Blo 467785 526405 := bbase (se 4 (by rfl) ⟨49350, by rfl⟩ : syracuseStep 526405 = 98701) (by norm_num)
theorem B526441 : Blo 467785 526441 := bbase (se 2 (by rfl) ⟨197415, by rfl⟩ : syracuseStep 526441 = 394831) (by norm_num)
theorem B2852981 : Blo 467785 2852981 := bbase (se 5 (by rfl) ⟨133733, by rfl⟩ : syracuseStep 2852981 = 267467) (by norm_num)
theorem B526477 : Blo 467785 526477 := bbase (se 3 (by rfl) ⟨98714, by rfl⟩ : syracuseStep 526477 = 197429) (by norm_num)
theorem B592049 : Blo 467785 592049 := bbase (se 2 (by rfl) ⟨222018, by rfl⟩ : syracuseStep 592049 = 444037) (by norm_num)
theorem B526513 : Blo 467785 526513 := bbase (se 2 (by rfl) ⟨197442, by rfl⟩ : syracuseStep 526513 = 394885) (by norm_num)
theorem B526549 : Blo 467785 526549 := bbase (se 7 (by rfl) ⟨6170, by rfl⟩ : syracuseStep 526549 = 12341) (by norm_num)
theorem B5998805 : Blo 467785 5998805 := bbase (se 7 (by rfl) ⟨70298, by rfl⟩ : syracuseStep 5998805 = 140597) (by norm_num)
theorem B592105 : Blo 467785 592105 := bbase (se 2 (by rfl) ⟨222039, by rfl⟩ : syracuseStep 592105 = 444079) (by norm_num)
theorem B526585 : Blo 467785 526585 := bbase (se 2 (by rfl) ⟨197469, by rfl⟩ : syracuseStep 526585 = 394939) (by norm_num)
theorem B526621 : Blo 467785 526621 := bbase (se 3 (by rfl) ⟨98741, by rfl⟩ : syracuseStep 526621 = 197483) (by norm_num)
theorem B526657 : Blo 467785 526657 := bbase (se 2 (by rfl) ⟨197496, by rfl⟩ : syracuseStep 526657 = 394993) (by norm_num)
theorem B592201 : Blo 467785 592201 := bbase (se 2 (by rfl) ⟨222075, by rfl⟩ : syracuseStep 592201 = 444151) (by norm_num)
theorem B526693 : Blo 467785 526693 := bbase (se 4 (by rfl) ⟨49377, by rfl⟩ : syracuseStep 526693 = 98755) (by norm_num)
theorem B1509749 : Blo 467785 1509749 := bbase (se 5 (by rfl) ⟨70769, by rfl⟩ : syracuseStep 1509749 = 141539) (by norm_num)
theorem B526729 : Blo 467785 526729 := bbase (se 2 (by rfl) ⟨197523, by rfl⟩ : syracuseStep 526729 = 395047) (by norm_num)
theorem B526765 : Blo 467785 526765 := bbase (se 3 (by rfl) ⟨98768, by rfl⟩ : syracuseStep 526765 = 197537) (by norm_num)
theorem B526801 : Blo 467785 526801 := bbase (se 2 (by rfl) ⟨197550, by rfl⟩ : syracuseStep 526801 = 395101) (by norm_num)
theorem B592373 : Blo 467785 592373 := bbase (se 5 (by rfl) ⟨27767, by rfl⟩ : syracuseStep 592373 = 55535) (by norm_num)
theorem B526837 : Blo 467785 526837 := bbase (se 5 (by rfl) ⟨24695, by rfl⟩ : syracuseStep 526837 = 49391) (by norm_num)
theorem B526873 : Blo 467785 526873 := bbase (se 2 (by rfl) ⟨197577, by rfl⟩ : syracuseStep 526873 = 395155) (by norm_num)
theorem B592429 : Blo 467785 592429 := bbase (se 3 (by rfl) ⟨111080, by rfl⟩ : syracuseStep 592429 = 222161) (by norm_num)
theorem B2034229 : Blo 467785 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B1509941 : Blo 467785 1509941 := bbase (se 5 (by rfl) ⟨70778, by rfl⟩ : syracuseStep 1509941 = 141557) (by norm_num)
theorem B526909 : Blo 467785 526909 := bbase (se 3 (by rfl) ⟨98795, by rfl⟩ : syracuseStep 526909 = 197591) (by norm_num)
theorem B526945 : Blo 467785 526945 := bbase (se 2 (by rfl) ⟨197604, by rfl⟩ : syracuseStep 526945 = 395209) (by norm_num)
theorem B526981 : Blo 467785 526981 := bbase (se 4 (by rfl) ⟨49404, by rfl⟩ : syracuseStep 526981 = 98809) (by norm_num)
theorem B592525 : Blo 467785 592525 := bbase (se 3 (by rfl) ⟨111098, by rfl⟩ : syracuseStep 592525 = 222197) (by norm_num)
theorem B527017 : Blo 467785 527017 := bbase (se 2 (by rfl) ⟨197631, by rfl⟩ : syracuseStep 527017 = 395263) (by norm_num)
theorem B527053 : Blo 467785 527053 := bbase (se 3 (by rfl) ⟨98822, by rfl⟩ : syracuseStep 527053 = 197645) (by norm_num)
theorem B527089 : Blo 467785 527089 := bbase (se 2 (by rfl) ⟨197658, by rfl⟩ : syracuseStep 527089 = 395317) (by norm_num)
theorem B527125 : Blo 467785 527125 := bbase (se 6 (by rfl) ⟨12354, by rfl⟩ : syracuseStep 527125 = 24709) (by norm_num)
theorem B592697 : Blo 467785 592697 := bbase (se 2 (by rfl) ⟨222261, by rfl⟩ : syracuseStep 592697 = 444523) (by norm_num)
theorem B527161 : Blo 467785 527161 := bbase (se 2 (by rfl) ⟨197685, by rfl⟩ : syracuseStep 527161 = 395371) (by norm_num)
theorem B527197 : Blo 467785 527197 := bbase (se 3 (by rfl) ⟨98849, by rfl⟩ : syracuseStep 527197 = 197699) (by norm_num)
theorem B592753 : Blo 467785 592753 := bbase (se 2 (by rfl) ⟨222282, by rfl⟩ : syracuseStep 592753 = 444565) (by norm_num)
theorem B527233 : Blo 467785 527233 := bbase (se 2 (by rfl) ⟨197712, by rfl⟩ : syracuseStep 527233 = 395425) (by norm_num)
theorem B527269 : Blo 467785 527269 := bbase (se 4 (by rfl) ⟨49431, by rfl⟩ : syracuseStep 527269 = 98863) (by norm_num)
theorem B723901 : Blo 467785 723901 := bbase (se 3 (by rfl) ⟨135731, by rfl⟩ : syracuseStep 723901 = 271463) (by norm_num)
theorem B527305 : Blo 467785 527305 := bbase (se 2 (by rfl) ⟨197739, by rfl⟩ : syracuseStep 527305 = 395479) (by norm_num)
theorem B592849 : Blo 467785 592849 := bbase (se 2 (by rfl) ⟨222318, by rfl⟩ : syracuseStep 592849 = 444637) (by norm_num)
theorem B527341 : Blo 467785 527341 := bbase (se 3 (by rfl) ⟨98876, by rfl⟩ : syracuseStep 527341 = 197753) (by norm_num)
theorem B789493 : Blo 467785 789493 := bbase (se 5 (by rfl) ⟨37007, by rfl⟩ : syracuseStep 789493 = 74015) (by norm_num)
theorem B2001925 : Blo 467785 2001925 := bbase (se 4 (by rfl) ⟨187680, by rfl⟩ : syracuseStep 2001925 = 375361) (by norm_num)
theorem B527377 : Blo 467785 527377 := bbase (se 2 (by rfl) ⟨197766, by rfl⟩ : syracuseStep 527377 = 395533) (by norm_num)
theorem B527413 : Blo 467785 527413 := bbase (se 5 (by rfl) ⟨24722, by rfl⟩ : syracuseStep 527413 = 49445) (by norm_num)
theorem B789581 : Blo 467785 789581 := bbase (se 3 (by rfl) ⟨148046, by rfl⟩ : syracuseStep 789581 = 296093) (by norm_num)
theorem B527449 : Blo 467785 527449 := bbase (se 2 (by rfl) ⟨197793, by rfl⟩ : syracuseStep 527449 = 395587) (by norm_num)
theorem B593021 : Blo 467785 593021 := bbase (se 3 (by rfl) ⟨111191, by rfl⟩ : syracuseStep 593021 = 222383) (by norm_num)
theorem B527485 : Blo 467785 527485 := bbase (se 3 (by rfl) ⟨98903, by rfl⟩ : syracuseStep 527485 = 197807) (by norm_num)
theorem B527521 : Blo 467785 527521 := bbase (se 2 (by rfl) ⟨197820, by rfl⟩ : syracuseStep 527521 = 395641) (by norm_num)
theorem B593077 : Blo 467785 593077 := bbase (se 5 (by rfl) ⟨27800, by rfl⟩ : syracuseStep 593077 = 55601) (by norm_num)
theorem B953525 : Blo 467785 953525 := bbase (se 5 (by rfl) ⟨44696, by rfl⟩ : syracuseStep 953525 = 89393) (by norm_num)
theorem B527557 : Blo 467785 527557 := bbase (se 4 (by rfl) ⟨49458, by rfl⟩ : syracuseStep 527557 = 98917) (by norm_num)
theorem B789709 : Blo 467785 789709 := bbase (se 3 (by rfl) ⟨148070, by rfl⟩ : syracuseStep 789709 = 296141) (by norm_num)
theorem B527593 : Blo 467785 527593 := bbase (se 2 (by rfl) ⟨197847, by rfl⟩ : syracuseStep 527593 = 395695) (by norm_num)
theorem B527629 : Blo 467785 527629 := bbase (se 3 (by rfl) ⟨98930, by rfl⟩ : syracuseStep 527629 = 197861) (by norm_num)
theorem B593173 : Blo 467785 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B789797 : Blo 467785 789797 := bbase (se 4 (by rfl) ⟨74043, by rfl⟩ : syracuseStep 789797 = 148087) (by norm_num)
theorem B527665 : Blo 467785 527665 := bbase (se 2 (by rfl) ⟨197874, by rfl⟩ : syracuseStep 527665 = 395749) (by norm_num)
theorem B527701 : Blo 467785 527701 := bbase (se 11 (by rfl) ⟨386, by rfl⟩ : syracuseStep 527701 = 773) (by norm_num)
theorem B527737 : Blo 467785 527737 := bbase (se 2 (by rfl) ⟨197901, by rfl⟩ : syracuseStep 527737 = 395803) (by norm_num)
theorem B527773 : Blo 467785 527773 := bbase (se 3 (by rfl) ⟨98957, by rfl⟩ : syracuseStep 527773 = 197915) (by norm_num)
theorem B789925 : Blo 467785 789925 := bbase (se 4 (by rfl) ⟨74055, by rfl⟩ : syracuseStep 789925 = 148111) (by norm_num)
theorem B593345 : Blo 467785 593345 := bbase (se 2 (by rfl) ⟨222504, by rfl⟩ : syracuseStep 593345 = 445009) (by norm_num)
theorem B527809 : Blo 467785 527809 := bbase (se 2 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 527809 = 395857) (by norm_num)
theorem B527845 : Blo 467785 527845 := bbase (se 4 (by rfl) ⟨49485, by rfl⟩ : syracuseStep 527845 = 98971) (by norm_num)
theorem B593401 : Blo 467785 593401 := bbase (se 2 (by rfl) ⟨222525, by rfl⟩ : syracuseStep 593401 = 445051) (by norm_num)
theorem B888317 : Blo 467785 888317 := bbase (se 3 (by rfl) ⟨166559, by rfl⟩ : syracuseStep 888317 = 333119) (by norm_num)
theorem B790013 : Blo 467785 790013 := bbase (se 3 (by rfl) ⟨148127, by rfl⟩ : syracuseStep 790013 = 296255) (by norm_num)
theorem B527881 : Blo 467785 527881 := bbase (se 2 (by rfl) ⟨197955, by rfl⟩ : syracuseStep 527881 = 395911) (by norm_num)
theorem B527917 : Blo 467785 527917 := bbase (se 3 (by rfl) ⟨98984, by rfl⟩ : syracuseStep 527917 = 197969) (by norm_num)
theorem B2068021 : Blo 467785 2068021 := bbase (se 5 (by rfl) ⟨96938, by rfl⟩ : syracuseStep 2068021 = 193877) (by norm_num)
theorem B527953 : Blo 467785 527953 := bbase (se 2 (by rfl) ⟨197982, by rfl⟩ : syracuseStep 527953 = 395965) (by norm_num)
theorem B593497 : Blo 467785 593497 := bbase (se 2 (by rfl) ⟨222561, by rfl⟩ : syracuseStep 593497 = 445123) (by norm_num)
theorem B527989 : Blo 467785 527989 := bbase (se 5 (by rfl) ⟨24749, by rfl⟩ : syracuseStep 527989 = 49499) (by norm_num)
theorem B790141 : Blo 467785 790141 := bbase (se 3 (by rfl) ⟨148151, by rfl⟩ : syracuseStep 790141 = 296303) (by norm_num)
theorem B528025 : Blo 467785 528025 := bbase (se 2 (by rfl) ⟨198009, by rfl⟩ : syracuseStep 528025 = 396019) (by norm_num)
theorem B528061 : Blo 467785 528061 := bbase (se 3 (by rfl) ⟨99011, by rfl⟩ : syracuseStep 528061 = 198023) (by norm_num)
theorem B790229 : Blo 467785 790229 := bbase (se 7 (by rfl) ⟨9260, by rfl⟩ : syracuseStep 790229 = 18521) (by norm_num)
theorem B528097 : Blo 467785 528097 := bbase (se 2 (by rfl) ⟨198036, by rfl⟩ : syracuseStep 528097 = 396073) (by norm_num)
theorem B593669 : Blo 467785 593669 := bbase (se 4 (by rfl) ⟨55656, by rfl⟩ : syracuseStep 593669 = 111313) (by norm_num)
theorem B528133 : Blo 467785 528133 := bbase (se 4 (by rfl) ⟨49512, by rfl⟩ : syracuseStep 528133 = 99025) (by norm_num)
theorem B528169 : Blo 467785 528169 := bbase (se 2 (by rfl) ⟨198063, by rfl⟩ : syracuseStep 528169 = 396127) (by norm_num)
theorem B593725 : Blo 467785 593725 := bbase (se 3 (by rfl) ⟨111323, by rfl⟩ : syracuseStep 593725 = 222647) (by norm_num)
theorem B528205 : Blo 467785 528205 := bbase (se 3 (by rfl) ⟨99038, by rfl⟩ : syracuseStep 528205 = 198077) (by norm_num)
theorem B790357 : Blo 467785 790357 := bbase (se 9 (by rfl) ⟨2315, by rfl⟩ : syracuseStep 790357 = 4631) (by norm_num)
theorem B1740629 : Blo 467785 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B1904485 : Blo 467785 1904485 := bbase (se 4 (by rfl) ⟨178545, by rfl⟩ : syracuseStep 1904485 = 357091) (by norm_num)
theorem B528241 : Blo 467785 528241 := bbase (se 2 (by rfl) ⟨198090, by rfl⟩ : syracuseStep 528241 = 396181) (by norm_num)
theorem B1052549 : Blo 467785 1052549 := bbase (se 4 (by rfl) ⟨98676, by rfl⟩ : syracuseStep 1052549 = 197353) (by norm_num)
theorem B528277 : Blo 467785 528277 := bbase (se 6 (by rfl) ⟨12381, by rfl⟩ : syracuseStep 528277 = 24763) (by norm_num)
theorem B593821 : Blo 467785 593821 := bbase (se 3 (by rfl) ⟨111341, by rfl⟩ : syracuseStep 593821 = 222683) (by norm_num)
theorem B790445 : Blo 467785 790445 := bbase (se 3 (by rfl) ⟨148208, by rfl⟩ : syracuseStep 790445 = 296417) (by norm_num)
theorem B528313 : Blo 467785 528313 := bbase (se 2 (by rfl) ⟨198117, by rfl⟩ : syracuseStep 528313 = 396235) (by norm_num)
theorem B1904581 : Blo 467785 1904581 := bbase (se 4 (by rfl) ⟨178554, by rfl⟩ : syracuseStep 1904581 = 357109) (by norm_num)
theorem B1052621 : Blo 467785 1052621 := bbase (se 3 (by rfl) ⟨197366, by rfl⟩ : syracuseStep 1052621 = 394733) (by norm_num)
theorem B528349 : Blo 467785 528349 := bbase (se 3 (by rfl) ⟨99065, by rfl⟩ : syracuseStep 528349 = 198131) (by norm_num)
theorem B528385 : Blo 467785 528385 := bbase (se 2 (by rfl) ⟨198144, by rfl⟩ : syracuseStep 528385 = 396289) (by norm_num)
theorem B1052693 : Blo 467785 1052693 := bbase (se 6 (by rfl) ⟨24672, by rfl⟩ : syracuseStep 1052693 = 49345) (by norm_num)
theorem B528421 : Blo 467785 528421 := bbase (se 4 (by rfl) ⟨49539, by rfl⟩ : syracuseStep 528421 = 99079) (by norm_num)
theorem B790573 : Blo 467785 790573 := bbase (se 3 (by rfl) ⟨148232, by rfl⟩ : syracuseStep 790573 = 296465) (by norm_num)
theorem B593993 : Blo 467785 593993 := bbase (se 2 (by rfl) ⟨222747, by rfl⟩ : syracuseStep 593993 = 445495) (by norm_num)
theorem B528457 : Blo 467785 528457 := bbase (se 2 (by rfl) ⟨198171, by rfl⟩ : syracuseStep 528457 = 396343) (by norm_num)
theorem B1019989 : Blo 467785 1019989 := bbase (se 8 (by rfl) ⟨5976, by rfl⟩ : syracuseStep 1019989 = 11953) (by norm_num)
theorem B1052765 : Blo 467785 1052765 := bbase (se 3 (by rfl) ⟨197393, by rfl⟩ : syracuseStep 1052765 = 394787) (by norm_num)
theorem B528493 : Blo 467785 528493 := bbase (se 3 (by rfl) ⟨99092, by rfl⟩ : syracuseStep 528493 = 198185) (by norm_num)
theorem B594049 : Blo 467785 594049 := bbase (se 2 (by rfl) ⟨222768, by rfl⟩ : syracuseStep 594049 = 445537) (by norm_num)
theorem B790661 : Blo 467785 790661 := bbase (se 4 (by rfl) ⟨74124, by rfl⟩ : syracuseStep 790661 = 148249) (by norm_num)
theorem B528529 : Blo 467785 528529 := bbase (se 2 (by rfl) ⟨198198, by rfl⟩ : syracuseStep 528529 = 396397) (by norm_num)
theorem B1052837 : Blo 467785 1052837 := bbase (se 4 (by rfl) ⟨98703, by rfl⟩ : syracuseStep 1052837 = 197407) (by norm_num)
theorem B528565 : Blo 467785 528565 := bbase (se 5 (by rfl) ⟨24776, by rfl⟩ : syracuseStep 528565 = 49553) (by norm_num)
theorem B528601 : Blo 467785 528601 := bbase (se 2 (by rfl) ⟨198225, by rfl⟩ : syracuseStep 528601 = 396451) (by norm_num)
theorem B594145 : Blo 467785 594145 := bbase (se 2 (by rfl) ⟨222804, by rfl⟩ : syracuseStep 594145 = 445609) (by norm_num)
theorem B1052909 : Blo 467785 1052909 := bbase (se 3 (by rfl) ⟨197420, by rfl⟩ : syracuseStep 1052909 = 394841) (by norm_num)
theorem B889069 : Blo 467785 889069 := bbase (se 3 (by rfl) ⟨166700, by rfl⟩ : syracuseStep 889069 = 333401) (by norm_num)
theorem B528637 : Blo 467785 528637 := bbase (se 3 (by rfl) ⟨99119, by rfl⟩ : syracuseStep 528637 = 198239) (by norm_num)
theorem B790789 : Blo 467785 790789 := bbase (se 4 (by rfl) ⟨74136, by rfl⟩ : syracuseStep 790789 = 148273) (by norm_num)
theorem B528673 : Blo 467785 528673 := bbase (se 2 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 528673 = 396505) (by norm_num)
theorem B1052981 : Blo 467785 1052981 := bbase (se 5 (by rfl) ⟨49358, by rfl⟩ : syracuseStep 1052981 = 98717) (by norm_num)
theorem B528709 : Blo 467785 528709 := bbase (se 4 (by rfl) ⟨49566, by rfl⟩ : syracuseStep 528709 = 99133) (by norm_num)
theorem B790877 : Blo 467785 790877 := bbase (se 3 (by rfl) ⟨148289, by rfl⟩ : syracuseStep 790877 = 296579) (by norm_num)
theorem B528745 : Blo 467785 528745 := bbase (se 2 (by rfl) ⟨198279, by rfl⟩ : syracuseStep 528745 = 396559) (by norm_num)
theorem B1053053 : Blo 467785 1053053 := bbase (se 3 (by rfl) ⟨197447, by rfl⟩ : syracuseStep 1053053 = 394895) (by norm_num)
theorem B889213 : Blo 467785 889213 := bbase (se 3 (by rfl) ⟨166727, by rfl⟩ : syracuseStep 889213 = 333455) (by norm_num)
theorem B954757 : Blo 467785 954757 := bbase (se 4 (by rfl) ⟨89508, by rfl⟩ : syracuseStep 954757 = 179017) (by norm_num)
theorem B594317 : Blo 467785 594317 := bbase (se 3 (by rfl) ⟨111434, by rfl⟩ : syracuseStep 594317 = 222869) (by norm_num)
theorem B528781 : Blo 467785 528781 := bbase (se 3 (by rfl) ⟨99146, by rfl⟩ : syracuseStep 528781 = 198293) (by norm_num)
theorem B528817 : Blo 467785 528817 := bbase (se 2 (by rfl) ⟨198306, by rfl⟩ : syracuseStep 528817 = 396613) (by norm_num)
theorem B1053125 : Blo 467785 1053125 := bbase (se 4 (by rfl) ⟨98730, by rfl⟩ : syracuseStep 1053125 = 197461) (by norm_num)
theorem B594373 : Blo 467785 594373 := bbase (se 4 (by rfl) ⟨55722, by rfl⟩ : syracuseStep 594373 = 111445) (by norm_num)
theorem B2003413 : Blo 467785 2003413 := bbase (se 7 (by rfl) ⟨23477, by rfl⟩ : syracuseStep 2003413 = 46955) (by norm_num)
theorem B528853 : Blo 467785 528853 := bbase (se 7 (by rfl) ⟨6197, by rfl⟩ : syracuseStep 528853 = 12395) (by norm_num)
theorem B791005 : Blo 467785 791005 := bbase (se 3 (by rfl) ⟨148313, by rfl⟩ : syracuseStep 791005 = 296627) (by norm_num)
theorem B2003429 : Blo 467785 2003429 := bbase (se 4 (by rfl) ⟨187821, by rfl⟩ : syracuseStep 2003429 = 375643) (by norm_num)
theorem B528889 : Blo 467785 528889 := bbase (se 2 (by rfl) ⟨198333, by rfl⟩ : syracuseStep 528889 = 396667) (by norm_num)
theorem B1053197 : Blo 467785 1053197 := bbase (se 3 (by rfl) ⟨197474, by rfl⟩ : syracuseStep 1053197 = 394949) (by norm_num)
theorem B889373 : Blo 467785 889373 := bbase (se 3 (by rfl) ⟨166757, by rfl⟩ : syracuseStep 889373 = 333515) (by norm_num)
theorem B528925 : Blo 467785 528925 := bbase (se 3 (by rfl) ⟨99173, by rfl⟩ : syracuseStep 528925 = 198347) (by norm_num)
theorem B594469 : Blo 467785 594469 := bbase (se 4 (by rfl) ⟨55731, by rfl⟩ : syracuseStep 594469 = 111463) (by norm_num)
theorem B791093 : Blo 467785 791093 := bbase (se 5 (by rfl) ⟨37082, by rfl⟩ : syracuseStep 791093 = 74165) (by norm_num)
theorem B528961 : Blo 467785 528961 := bbase (se 2 (by rfl) ⟨198360, by rfl⟩ : syracuseStep 528961 = 396721) (by norm_num)
theorem B1184341 : Blo 467785 1184341 := bbase (se 8 (by rfl) ⟨6939, by rfl⟩ : syracuseStep 1184341 = 13879) (by norm_num)
theorem B1053269 : Blo 467785 1053269 := bbase (se 8 (by rfl) ⟨6171, by rfl⟩ : syracuseStep 1053269 = 12343) (by norm_num)
theorem B528997 : Blo 467785 528997 := bbase (se 4 (by rfl) ⟨49593, by rfl⟩ : syracuseStep 528997 = 99187) (by norm_num)
theorem B529033 : Blo 467785 529033 := bbase (se 2 (by rfl) ⟨198387, by rfl⟩ : syracuseStep 529033 = 396775) (by norm_num)
theorem B1217173 : Blo 467785 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B1053341 : Blo 467785 1053341 := bbase (se 3 (by rfl) ⟨197501, by rfl⟩ : syracuseStep 1053341 = 395003) (by norm_num)
theorem B889517 : Blo 467785 889517 := bbase (se 3 (by rfl) ⟨166784, by rfl⟩ : syracuseStep 889517 = 333569) (by norm_num)
theorem B529069 : Blo 467785 529069 := bbase (se 3 (by rfl) ⟨99200, by rfl⟩ : syracuseStep 529069 = 198401) (by norm_num)
theorem B791221 : Blo 467785 791221 := bbase (se 5 (by rfl) ⟨37088, by rfl⟩ : syracuseStep 791221 = 74177) (by norm_num)
theorem B3609269 : Blo 467785 3609269 := bbase (se 5 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 3609269 = 338369) (by norm_num)
theorem B1184453 : Blo 467785 1184453 := bbase (se 4 (by rfl) ⟨111042, by rfl⟩ : syracuseStep 1184453 = 222085) (by norm_num)
theorem B594641 : Blo 467785 594641 := bbase (se 2 (by rfl) ⟨222990, by rfl⟩ : syracuseStep 594641 = 445981) (by norm_num)
theorem B529105 : Blo 467785 529105 := bbase (se 2 (by rfl) ⟨198414, by rfl⟩ : syracuseStep 529105 = 396829) (by norm_num)
theorem B2888405 : Blo 467785 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B1053413 : Blo 467785 1053413 := bbase (se 4 (by rfl) ⟨98757, by rfl⟩ : syracuseStep 1053413 = 197515) (by norm_num)
theorem B529141 : Blo 467785 529141 := bbase (se 5 (by rfl) ⟨24803, by rfl⟩ : syracuseStep 529141 = 49607) (by norm_num)
theorem B594697 : Blo 467785 594697 := bbase (se 2 (by rfl) ⟨223011, by rfl⟩ : syracuseStep 594697 = 446023) (by norm_num)
theorem B791309 : Blo 467785 791309 := bbase (se 3 (by rfl) ⟨148370, by rfl⟩ : syracuseStep 791309 = 296741) (by norm_num)
theorem B529177 : Blo 467785 529177 := bbase (se 2 (by rfl) ⟨198441, by rfl⟩ : syracuseStep 529177 = 396883) (by norm_num)
theorem B2265893 : Blo 467785 2265893 := bbase (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) (by norm_num)
theorem B1053485 : Blo 467785 1053485 := bbase (se 3 (by rfl) ⟨197528, by rfl⟩ : syracuseStep 1053485 = 395057) (by norm_num)
theorem B529213 : Blo 467785 529213 := bbase (se 3 (by rfl) ⟨99227, by rfl⟩ : syracuseStep 529213 = 198455) (by norm_num)
theorem B529249 : Blo 467785 529249 := bbase (se 2 (by rfl) ⟨198468, by rfl⟩ : syracuseStep 529249 = 396937) (by norm_num)
theorem B594793 : Blo 467785 594793 := bbase (se 2 (by rfl) ⟨223047, by rfl⟩ : syracuseStep 594793 = 446095) (by norm_num)
theorem B1053557 : Blo 467785 1053557 := bbase (se 5 (by rfl) ⟨49385, by rfl⟩ : syracuseStep 1053557 = 98771) (by norm_num)
theorem B1184645 : Blo 467785 1184645 := bbase (se 4 (by rfl) ⟨111060, by rfl⟩ : syracuseStep 1184645 = 222121) (by norm_num)
theorem B529285 : Blo 467785 529285 := bbase (se 4 (by rfl) ⟨49620, by rfl⟩ : syracuseStep 529285 = 99241) (by norm_num)
theorem B791437 : Blo 467785 791437 := bbase (se 3 (by rfl) ⟨148394, by rfl⟩ : syracuseStep 791437 = 296789) (by norm_num)
theorem B562081 : Blo 467785 562081 := bbase (se 2 (by rfl) ⟨210780, by rfl⟩ : syracuseStep 562081 = 421561) (by norm_num)
theorem B529321 : Blo 467785 529321 := bbase (se 2 (by rfl) ⟨198495, by rfl⟩ : syracuseStep 529321 = 396991) (by norm_num)
theorem B1053629 : Blo 467785 1053629 := bbase (se 3 (by rfl) ⟨197555, by rfl⟩ : syracuseStep 1053629 = 395111) (by norm_num)
theorem B889805 : Blo 467785 889805 := bbase (se 3 (by rfl) ⟨166838, by rfl⟩ : syracuseStep 889805 = 333677) (by norm_num)
theorem B529357 : Blo 467785 529357 := bbase (se 3 (by rfl) ⟨99254, by rfl⟩ : syracuseStep 529357 = 198509) (by norm_num)
theorem B791525 : Blo 467785 791525 := bbase (se 4 (by rfl) ⟨74205, by rfl⟩ : syracuseStep 791525 = 148411) (by norm_num)
theorem B529393 : Blo 467785 529393 := bbase (se 2 (by rfl) ⟨198522, by rfl⟩ : syracuseStep 529393 = 397045) (by norm_num)
theorem B562177 : Blo 467785 562177 := bbase (se 2 (by rfl) ⟨210816, by rfl⟩ : syracuseStep 562177 = 421633) (by norm_num)
theorem B1053701 : Blo 467785 1053701 := bbase (se 4 (by rfl) ⟨98784, by rfl⟩ : syracuseStep 1053701 = 197569) (by norm_num)
theorem B594965 : Blo 467785 594965 := bbase (se 6 (by rfl) ⟨13944, by rfl⟩ : syracuseStep 594965 = 27889) (by norm_num)
theorem B529429 : Blo 467785 529429 := bbase (se 6 (by rfl) ⟨12408, by rfl⟩ : syracuseStep 529429 = 24817) (by norm_num)
theorem B529465 : Blo 467785 529465 := bbase (se 2 (by rfl) ⟨198549, by rfl⟩ : syracuseStep 529465 = 397099) (by norm_num)
theorem B1053773 : Blo 467785 1053773 := bbase (se 3 (by rfl) ⟨197582, by rfl⟩ : syracuseStep 1053773 = 395165) (by norm_num)
theorem B595021 : Blo 467785 595021 := bbase (se 3 (by rfl) ⟨111566, by rfl⟩ : syracuseStep 595021 = 223133) (by norm_num)
theorem B529501 : Blo 467785 529501 := bbase (se 3 (by rfl) ⟨99281, by rfl⟩ : syracuseStep 529501 = 198563) (by norm_num)
theorem B889957 : Blo 467785 889957 := bbase (se 4 (by rfl) ⟨83433, by rfl⟩ : syracuseStep 889957 = 166867) (by norm_num)
theorem B791653 : Blo 467785 791653 := bbase (se 4 (by rfl) ⟨74217, by rfl⟩ : syracuseStep 791653 = 148435) (by norm_num)
theorem B529537 : Blo 467785 529537 := bbase (se 2 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 529537 = 397153) (by norm_num)
theorem B2135173 : Blo 467785 2135173 := bbase (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) (by norm_num)
theorem B562321 : Blo 467785 562321 := bbase (se 2 (by rfl) ⟨210870, by rfl⟩ : syracuseStep 562321 = 421741) (by norm_num)
theorem B1053845 : Blo 467785 1053845 := bbase (se 6 (by rfl) ⟨24699, by rfl⟩ : syracuseStep 1053845 = 49399) (by norm_num)
theorem B529573 : Blo 467785 529573 := bbase (se 4 (by rfl) ⟨49647, by rfl⟩ : syracuseStep 529573 = 99295) (by norm_num)
theorem B595117 : Blo 467785 595117 := bbase (se 3 (by rfl) ⟨111584, by rfl⟩ : syracuseStep 595117 = 223169) (by norm_num)
theorem B791741 : Blo 467785 791741 := bbase (se 3 (by rfl) ⟨148451, by rfl⟩ : syracuseStep 791741 = 296903) (by norm_num)
theorem B529609 : Blo 467785 529609 := bbase (se 2 (by rfl) ⟨198603, by rfl⟩ : syracuseStep 529609 = 397207) (by norm_num)
theorem B1184989 : Blo 467785 1184989 := bbase (se 3 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 1184989 = 444371) (by norm_num)
theorem B1053917 : Blo 467785 1053917 := bbase (se 3 (by rfl) ⟨197609, by rfl⟩ : syracuseStep 1053917 = 395219) (by norm_num)
theorem B529645 : Blo 467785 529645 := bbase (se 3 (by rfl) ⟨99308, by rfl⟩ : syracuseStep 529645 = 198617) (by norm_num)
theorem B529681 : Blo 467785 529681 := bbase (se 2 (by rfl) ⟨198630, by rfl⟩ : syracuseStep 529681 = 397261) (by norm_num)
theorem B1053989 : Blo 467785 1053989 := bbase (se 4 (by rfl) ⟨98811, by rfl⟩ : syracuseStep 1053989 = 197623) (by norm_num)
theorem B529717 : Blo 467785 529717 := bbase (se 5 (by rfl) ⟨24830, by rfl⟩ : syracuseStep 529717 = 49661) (by norm_num)
theorem B791869 : Blo 467785 791869 := bbase (se 3 (by rfl) ⟨148475, by rfl⟩ : syracuseStep 791869 = 296951) (by norm_num)
theorem B1185101 : Blo 467785 1185101 := bbase (se 3 (by rfl) ⟨222206, by rfl⟩ : syracuseStep 1185101 = 444413) (by norm_num)
theorem B595289 : Blo 467785 595289 := bbase (se 2 (by rfl) ⟨223233, by rfl⟩ : syracuseStep 595289 = 446467) (by norm_num)
theorem B529753 : Blo 467785 529753 := bbase (se 2 (by rfl) ⟨198657, by rfl⟩ : syracuseStep 529753 = 397315) (by norm_num)
theorem B1054061 : Blo 467785 1054061 := bbase (se 3 (by rfl) ⟨197636, by rfl⟩ : syracuseStep 1054061 = 395273) (by norm_num)
theorem B529789 : Blo 467785 529789 := bbase (se 3 (by rfl) ⟨99335, by rfl⟩ : syracuseStep 529789 = 198671) (by norm_num)
theorem B595345 : Blo 467785 595345 := bbase (se 2 (by rfl) ⟨223254, by rfl⟩ : syracuseStep 595345 = 446509) (by norm_num)
theorem B890261 : Blo 467785 890261 := bbase (se 6 (by rfl) ⟨20865, by rfl⟩ : syracuseStep 890261 = 41731) (by norm_num)
theorem B791957 : Blo 467785 791957 := bbase (se 6 (by rfl) ⟨18561, by rfl⟩ : syracuseStep 791957 = 37123) (by norm_num)
theorem B529825 : Blo 467785 529825 := bbase (se 2 (by rfl) ⟨198684, by rfl⟩ : syracuseStep 529825 = 397369) (by norm_num)
theorem B1054133 : Blo 467785 1054133 := bbase (se 5 (by rfl) ⟨49412, by rfl⟩ : syracuseStep 1054133 = 98825) (by norm_num)
theorem B529861 : Blo 467785 529861 := bbase (se 4 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 529861 = 99349) (by norm_num)
theorem B529897 : Blo 467785 529897 := bbase (se 2 (by rfl) ⟨198711, by rfl⟩ : syracuseStep 529897 = 397423) (by norm_num)
theorem B595441 : Blo 467785 595441 := bbase (se 2 (by rfl) ⟨223290, by rfl⟩ : syracuseStep 595441 = 446581) (by norm_num)
theorem B1054205 : Blo 467785 1054205 := bbase (se 3 (by rfl) ⟨197663, by rfl⟩ : syracuseStep 1054205 = 395327) (by norm_num)
theorem B1185293 : Blo 467785 1185293 := bbase (se 3 (by rfl) ⟨222242, by rfl⟩ : syracuseStep 1185293 = 444485) (by norm_num)
theorem B529933 : Blo 467785 529933 := bbase (se 3 (by rfl) ⟨99362, by rfl⟩ : syracuseStep 529933 = 198725) (by norm_num)
theorem B792085 : Blo 467785 792085 := bbase (se 6 (by rfl) ⟨18564, by rfl⟩ : syracuseStep 792085 = 37129) (by norm_num)
theorem B529969 : Blo 467785 529969 := bbase (se 2 (by rfl) ⟨198738, by rfl⟩ : syracuseStep 529969 = 397477) (by norm_num)
theorem B1054277 : Blo 467785 1054277 := bbase (se 4 (by rfl) ⟨98838, by rfl⟩ : syracuseStep 1054277 = 197677) (by norm_num)
theorem B530005 : Blo 467785 530005 := bbase (se 8 (by rfl) ⟨3105, by rfl⟩ : syracuseStep 530005 = 6211) (by norm_num)
theorem B792173 : Blo 467785 792173 := bbase (se 3 (by rfl) ⟨148532, by rfl⟩ : syracuseStep 792173 = 297065) (by norm_num)
theorem B530041 : Blo 467785 530041 := bbase (se 2 (by rfl) ⟨198765, by rfl⟩ : syracuseStep 530041 = 397531) (by norm_num)
theorem B1054349 : Blo 467785 1054349 := bbase (se 3 (by rfl) ⟨197690, by rfl⟩ : syracuseStep 1054349 = 395381) (by norm_num)
theorem B595613 : Blo 467785 595613 := bbase (se 3 (by rfl) ⟨111677, by rfl⟩ : syracuseStep 595613 = 223355) (by norm_num)
theorem B530077 : Blo 467785 530077 := bbase (se 3 (by rfl) ⟨99389, by rfl⟩ : syracuseStep 530077 = 198779) (by norm_num)
theorem B530113 : Blo 467785 530113 := bbase (se 2 (by rfl) ⟨198792, by rfl⟩ : syracuseStep 530113 = 397585) (by norm_num)
theorem B1054421 : Blo 467785 1054421 := bbase (se 7 (by rfl) ⟨12356, by rfl⟩ : syracuseStep 1054421 = 24713) (by norm_num)
theorem B595669 : Blo 467785 595669 := bbase (se 7 (by rfl) ⟨6980, by rfl⟩ : syracuseStep 595669 = 13961) (by norm_num)
theorem B530149 : Blo 467785 530149 := bbase (se 4 (by rfl) ⟨49701, by rfl⟩ : syracuseStep 530149 = 99403) (by norm_num)
theorem B792301 : Blo 467785 792301 := bbase (se 3 (by rfl) ⟨148556, by rfl⟩ : syracuseStep 792301 = 297113) (by norm_num)
theorem B530185 : Blo 467785 530185 := bbase (se 2 (by rfl) ⟨198819, by rfl⟩ : syracuseStep 530185 = 397639) (by norm_num)
theorem B1054493 : Blo 467785 1054493 := bbase (se 3 (by rfl) ⟨197717, by rfl⟩ : syracuseStep 1054493 = 395435) (by norm_num)
theorem B530221 : Blo 467785 530221 := bbase (se 3 (by rfl) ⟨99416, by rfl⟩ : syracuseStep 530221 = 198833) (by norm_num)
theorem B595765 : Blo 467785 595765 := bbase (se 5 (by rfl) ⟨27926, by rfl⟩ : syracuseStep 595765 = 55853) (by norm_num)
theorem B792389 : Blo 467785 792389 := bbase (se 4 (by rfl) ⟨74286, by rfl⟩ : syracuseStep 792389 = 148573) (by norm_num)
theorem B530257 : Blo 467785 530257 := bbase (se 2 (by rfl) ⟨198846, by rfl⟩ : syracuseStep 530257 = 397693) (by norm_num)
theorem B1185637 : Blo 467785 1185637 := bbase (se 4 (by rfl) ⟨111153, by rfl⟩ : syracuseStep 1185637 = 222307) (by norm_num)
theorem B1054565 : Blo 467785 1054565 := bbase (se 4 (by rfl) ⟨98865, by rfl⟩ : syracuseStep 1054565 = 197731) (by norm_num)
theorem B530293 : Blo 467785 530293 := bbase (se 5 (by rfl) ⟨24857, by rfl⟩ : syracuseStep 530293 = 49715) (by norm_num)
theorem B530329 : Blo 467785 530329 := bbase (se 2 (by rfl) ⟨198873, by rfl⟩ : syracuseStep 530329 = 397747) (by norm_num)
theorem B1054637 : Blo 467785 1054637 := bbase (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) (by norm_num)
theorem B1611701 : Blo 467785 1611701 := bbase (se 5 (by rfl) ⟨75548, by rfl⟩ : syracuseStep 1611701 = 151097) (by norm_num)
theorem B530365 : Blo 467785 530365 := bbase (se 3 (by rfl) ⟨99443, by rfl⟩ : syracuseStep 530365 = 198887) (by norm_num)
theorem B792517 : Blo 467785 792517 := bbase (se 4 (by rfl) ⟨74298, by rfl⟩ : syracuseStep 792517 = 148597) (by norm_num)
theorem B1185749 : Blo 467785 1185749 := bbase (se 7 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 1185749 = 27791) (by norm_num)
theorem B595937 : Blo 467785 595937 := bbase (se 2 (by rfl) ⟨223476, by rfl⟩ : syracuseStep 595937 = 446953) (by norm_num)
theorem B530401 : Blo 467785 530401 := bbase (se 2 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 530401 = 397801) (by norm_num)
theorem B1054709 : Blo 467785 1054709 := bbase (se 5 (by rfl) ⟨49439, by rfl⟩ : syracuseStep 1054709 = 98879) (by norm_num)
theorem B1579013 : Blo 467785 1579013 := bbase (se 4 (by rfl) ⟨148032, by rfl⟩ : syracuseStep 1579013 = 296065) (by norm_num)
theorem B530437 : Blo 467785 530437 := bbase (se 4 (by rfl) ⟨49728, by rfl⟩ : syracuseStep 530437 = 99457) (by norm_num)
theorem B595993 : Blo 467785 595993 := bbase (se 2 (by rfl) ⟨223497, by rfl⟩ : syracuseStep 595993 = 446995) (by norm_num)
theorem B792605 : Blo 467785 792605 := bbase (se 3 (by rfl) ⟨148613, by rfl⟩ : syracuseStep 792605 = 297227) (by norm_num)
theorem B530473 : Blo 467785 530473 := bbase (se 2 (by rfl) ⟨198927, by rfl⟩ : syracuseStep 530473 = 397855) (by norm_num)
theorem B759869 : Blo 467785 759869 := bbase (se 3 (by rfl) ⟨142475, by rfl⟩ : syracuseStep 759869 = 284951) (by norm_num)
theorem B1054781 : Blo 467785 1054781 := bbase (se 3 (by rfl) ⟨197771, by rfl⟩ : syracuseStep 1054781 = 395543) (by norm_num)
theorem B530509 : Blo 467785 530509 := bbase (se 3 (by rfl) ⟨99470, by rfl⟩ : syracuseStep 530509 = 198941) (by norm_num)
theorem B530545 : Blo 467785 530545 := bbase (se 2 (by rfl) ⟨198954, by rfl⟩ : syracuseStep 530545 = 397909) (by norm_num)
theorem B3381365 : Blo 467785 3381365 := bbase (se 5 (by rfl) ⟨158501, by rfl⟩ : syracuseStep 3381365 = 317003) (by norm_num)
theorem B563321 : Blo 467785 563321 := bbase (se 2 (by rfl) ⟨211245, by rfl⟩ : syracuseStep 563321 = 422491) (by norm_num)
theorem B596089 : Blo 467785 596089 := bbase (se 2 (by rfl) ⟨223533, by rfl⟩ : syracuseStep 596089 = 447067) (by norm_num)
theorem B1054853 : Blo 467785 1054853 := bbase (se 4 (by rfl) ⟨98892, by rfl⟩ : syracuseStep 1054853 = 197785) (by norm_num)
theorem B891013 : Blo 467785 891013 := bbase (se 4 (by rfl) ⟨83532, by rfl⟩ : syracuseStep 891013 = 167065) (by norm_num)
theorem B1185941 : Blo 467785 1185941 := bbase (se 6 (by rfl) ⟨27795, by rfl⟩ : syracuseStep 1185941 = 55591) (by norm_num)
theorem B530581 : Blo 467785 530581 := bbase (se 6 (by rfl) ⟨12435, by rfl⟩ : syracuseStep 530581 = 24871) (by norm_num)
theorem B792733 : Blo 467785 792733 := bbase (se 3 (by rfl) ⟨148637, by rfl⟩ : syracuseStep 792733 = 297275) (by norm_num)
theorem B530617 : Blo 467785 530617 := bbase (se 2 (by rfl) ⟨198981, by rfl⟩ : syracuseStep 530617 = 397963) (by norm_num)
theorem B1054925 : Blo 467785 1054925 := bbase (se 3 (by rfl) ⟨197798, by rfl⟩ : syracuseStep 1054925 = 395597) (by norm_num)
theorem B530653 : Blo 467785 530653 := bbase (se 3 (by rfl) ⟨99497, by rfl⟩ : syracuseStep 530653 = 198995) (by norm_num)
theorem B792821 : Blo 467785 792821 := bbase (se 5 (by rfl) ⟨37163, by rfl⟩ : syracuseStep 792821 = 74327) (by norm_num)
theorem B530689 : Blo 467785 530689 := bbase (se 2 (by rfl) ⟨199008, by rfl⟩ : syracuseStep 530689 = 398017) (by norm_num)
theorem B1054997 : Blo 467785 1054997 := bbase (se 6 (by rfl) ⟨24726, by rfl⟩ : syracuseStep 1054997 = 49453) (by norm_num)
theorem B891157 : Blo 467785 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B596261 : Blo 467785 596261 := bbase (se 4 (by rfl) ⟨55899, by rfl⟩ : syracuseStep 596261 = 111799) (by norm_num)
theorem B530725 : Blo 467785 530725 := bbase (se 4 (by rfl) ⟨49755, by rfl⟩ : syracuseStep 530725 = 99511) (by norm_num)
theorem B1055069 : Blo 467785 1055069 := bbase (se 3 (by rfl) ⟨197825, by rfl⟩ : syracuseStep 1055069 = 395651) (by norm_num)
theorem B596317 : Blo 467785 596317 := bbase (se 3 (by rfl) ⟨111809, by rfl⟩ : syracuseStep 596317 = 223619) (by norm_num)
theorem B792949 : Blo 467785 792949 := bbase (se 5 (by rfl) ⟨37169, by rfl⟩ : syracuseStep 792949 = 74339) (by norm_num)
theorem B1055141 : Blo 467785 1055141 := bbase (se 4 (by rfl) ⟨98919, by rfl⟩ : syracuseStep 1055141 = 197839) (by norm_num)
theorem B1579445 : Blo 467785 1579445 := bbase (se 5 (by rfl) ⟨74036, by rfl⟩ : syracuseStep 1579445 = 148073) (by norm_num)
theorem B891317 : Blo 467785 891317 := bbase (se 5 (by rfl) ⟨41780, by rfl⟩ : syracuseStep 891317 = 83561) (by norm_num)
theorem B596413 : Blo 467785 596413 := bbase (se 3 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 596413 = 223655) (by norm_num)
theorem B793037 : Blo 467785 793037 := bbase (se 3 (by rfl) ⟨148694, by rfl⟩ : syracuseStep 793037 = 297389) (by norm_num)
theorem B1186285 : Blo 467785 1186285 := bbase (se 3 (by rfl) ⟨222428, by rfl⟩ : syracuseStep 1186285 = 444857) (by norm_num)
theorem B1055213 : Blo 467785 1055213 := bbase (se 3 (by rfl) ⟨197852, by rfl⟩ : syracuseStep 1055213 = 395705) (by norm_num)
theorem B1055285 : Blo 467785 1055285 := bbase (se 5 (by rfl) ⟨49466, by rfl⟩ : syracuseStep 1055285 = 98933) (by norm_num)
theorem B891461 : Blo 467785 891461 := bbase (se 4 (by rfl) ⟨83574, by rfl⟩ : syracuseStep 891461 = 167149) (by norm_num)
theorem B793165 : Blo 467785 793165 := bbase (se 3 (by rfl) ⟨148718, by rfl⟩ : syracuseStep 793165 = 297437) (by norm_num)
theorem B1186397 : Blo 467785 1186397 := bbase (se 3 (by rfl) ⟨222449, by rfl⟩ : syracuseStep 1186397 = 444899) (by norm_num)
theorem B596585 : Blo 467785 596585 := bbase (se 2 (by rfl) ⟨223719, by rfl⟩ : syracuseStep 596585 = 447439) (by norm_num)
theorem B1055357 : Blo 467785 1055357 := bbase (se 3 (by rfl) ⟨197879, by rfl⟩ : syracuseStep 1055357 = 395759) (by norm_num)
theorem B3054229 : Blo 467785 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B596641 : Blo 467785 596641 := bbase (se 2 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 596641 = 447481) (by norm_num)
theorem B793253 : Blo 467785 793253 := bbase (se 4 (by rfl) ⟨74367, by rfl⟩ : syracuseStep 793253 = 148735) (by norm_num)
theorem B2005685 : Blo 467785 2005685 := bbase (se 5 (by rfl) ⟨94016, by rfl⟩ : syracuseStep 2005685 = 188033) (by norm_num)
theorem B1055429 : Blo 467785 1055429 := bbase (se 4 (by rfl) ⟨98946, by rfl⟩ : syracuseStep 1055429 = 197893) (by norm_num)
theorem B596737 : Blo 467785 596737 := bbase (se 2 (by rfl) ⟨223776, by rfl⟩ : syracuseStep 596737 = 447553) (by norm_num)
theorem B1055501 : Blo 467785 1055501 := bbase (se 3 (by rfl) ⟨197906, by rfl⟩ : syracuseStep 1055501 = 395813) (by norm_num)
theorem B1186589 : Blo 467785 1186589 := bbase (se 3 (by rfl) ⟨222485, by rfl⟩ : syracuseStep 1186589 = 444971) (by norm_num)
theorem B793381 : Blo 467785 793381 := bbase (se 4 (by rfl) ⟨74379, by rfl⟩ : syracuseStep 793381 = 148759) (by norm_num)
theorem B564013 : Blo 467785 564013 := bbase (se 3 (by rfl) ⟨105752, by rfl⟩ : syracuseStep 564013 = 211505) (by norm_num)
theorem B1776437 : Blo 467785 1776437 := bbase (se 5 (by rfl) ⟨83270, by rfl⟩ : syracuseStep 1776437 = 166541) (by norm_num)
theorem B1055573 : Blo 467785 1055573 := bbase (se 9 (by rfl) ⟨3092, by rfl⟩ : syracuseStep 1055573 = 6185) (by norm_num)
theorem B1579877 : Blo 467785 1579877 := bbase (se 4 (by rfl) ⟨148113, by rfl⟩ : syracuseStep 1579877 = 296227) (by norm_num)
theorem B891749 : Blo 467785 891749 := bbase (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) (by norm_num)
theorem B793469 : Blo 467785 793469 := bbase (se 3 (by rfl) ⟨148775, by rfl⟩ : syracuseStep 793469 = 297551) (by norm_num)
theorem B1055645 : Blo 467785 1055645 := bbase (se 3 (by rfl) ⟨197933, by rfl⟩ : syracuseStep 1055645 = 395867) (by norm_num)
theorem B596909 : Blo 467785 596909 := bbase (se 3 (by rfl) ⟨111920, by rfl⟩ : syracuseStep 596909 = 223841) (by norm_num)
theorem B1055717 : Blo 467785 1055717 := bbase (se 4 (by rfl) ⟨98973, by rfl⟩ : syracuseStep 1055717 = 197947) (by norm_num)
theorem B596965 : Blo 467785 596965 := bbase (se 4 (by rfl) ⟨55965, by rfl⟩ : syracuseStep 596965 = 111931) (by norm_num)
theorem B891901 : Blo 467785 891901 := bbase (se 3 (by rfl) ⟨167231, by rfl⟩ : syracuseStep 891901 = 334463) (by norm_num)
theorem B793597 : Blo 467785 793597 := bbase (se 3 (by rfl) ⟨148799, by rfl⟩ : syracuseStep 793597 = 297599) (by norm_num)
theorem B564229 : Blo 467785 564229 := bbase (se 4 (by rfl) ⟨52896, by rfl⟩ : syracuseStep 564229 = 105793) (by norm_num)
theorem B1055789 : Blo 467785 1055789 := bbase (se 3 (by rfl) ⟨197960, by rfl⟩ : syracuseStep 1055789 = 395921) (by norm_num)
theorem B597061 : Blo 467785 597061 := bbase (se 4 (by rfl) ⟨55974, by rfl⟩ : syracuseStep 597061 = 111949) (by norm_num)
theorem B1776725 : Blo 467785 1776725 := bbase (se 8 (by rfl) ⟨10410, by rfl⟩ : syracuseStep 1776725 = 20821) (by norm_num)
theorem B793685 : Blo 467785 793685 := bbase (se 8 (by rfl) ⟨4650, by rfl⟩ : syracuseStep 793685 = 9301) (by norm_num)
theorem B1055861 : Blo 467785 1055861 := bbase (se 5 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 1055861 = 98987) (by norm_num)
theorem B1186933 : Blo 467785 1186933 := bbase (se 5 (by rfl) ⟨55637, by rfl⟩ : syracuseStep 1186933 = 111275) (by norm_num)
theorem B1055933 : Blo 467785 1055933 := bbase (se 3 (by rfl) ⟨197987, by rfl⟩ : syracuseStep 1055933 = 395975) (by norm_num)
theorem B793813 : Blo 467785 793813 := bbase (se 7 (by rfl) ⟨9302, by rfl⟩ : syracuseStep 793813 = 18605) (by norm_num)
theorem B1187045 : Blo 467785 1187045 := bbase (se 4 (by rfl) ⟨111285, by rfl⟩ : syracuseStep 1187045 = 222571) (by norm_num)
theorem B1056005 : Blo 467785 1056005 := bbase (se 4 (by rfl) ⟨99000, by rfl⟩ : syracuseStep 1056005 = 198001) (by norm_num)
theorem B1580309 : Blo 467785 1580309 := bbase (se 6 (by rfl) ⟨37038, by rfl⟩ : syracuseStep 1580309 = 74077) (by norm_num)
theorem B892205 : Blo 467785 892205 := bbase (se 3 (by rfl) ⟨167288, by rfl⟩ : syracuseStep 892205 = 334577) (by norm_num)
theorem B793901 : Blo 467785 793901 := bbase (se 3 (by rfl) ⟨148856, by rfl⟩ : syracuseStep 793901 = 297713) (by norm_num)
theorem B1056077 : Blo 467785 1056077 := bbase (se 3 (by rfl) ⟨198014, by rfl⟩ : syracuseStep 1056077 = 396029) (by norm_num)
theorem B1056149 : Blo 467785 1056149 := bbase (se 6 (by rfl) ⟨24753, by rfl⟩ : syracuseStep 1056149 = 49507) (by norm_num)
theorem B1187237 : Blo 467785 1187237 := bbase (se 4 (by rfl) ⟨111303, by rfl⟩ : syracuseStep 1187237 = 222607) (by norm_num)
theorem B794029 : Blo 467785 794029 := bbase (se 3 (by rfl) ⟨148880, by rfl⟩ : syracuseStep 794029 = 297761) (by norm_num)
theorem B1056221 : Blo 467785 1056221 := bbase (se 3 (by rfl) ⟨198041, by rfl⟩ : syracuseStep 1056221 = 396083) (by norm_num)
theorem B794117 : Blo 467785 794117 := bbase (se 4 (by rfl) ⟨74448, by rfl⟩ : syracuseStep 794117 = 148897) (by norm_num)
theorem B1056293 : Blo 467785 1056293 := bbase (se 4 (by rfl) ⟨99027, by rfl⟩ : syracuseStep 1056293 = 198055) (by norm_num)
theorem B1056365 : Blo 467785 1056365 := bbase (se 3 (by rfl) ⟨198068, by rfl⟩ : syracuseStep 1056365 = 396137) (by norm_num)
theorem B794245 : Blo 467785 794245 := bbase (se 4 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 794245 = 148921) (by norm_num)
theorem B1056437 : Blo 467785 1056437 := bbase (se 5 (by rfl) ⟨49520, by rfl⟩ : syracuseStep 1056437 = 99041) (by norm_num)
theorem B1580741 : Blo 467785 1580741 := bbase (se 4 (by rfl) ⟨148194, by rfl⟩ : syracuseStep 1580741 = 296389) (by norm_num)
theorem B3776213 : Blo 467785 3776213 := bbase (se 7 (by rfl) ⟨44252, by rfl⟩ : syracuseStep 3776213 = 88505) (by norm_num)
theorem B794333 : Blo 467785 794333 := bbase (se 3 (by rfl) ⟨148937, by rfl⟩ : syracuseStep 794333 = 297875) (by norm_num)
theorem B1187581 : Blo 467785 1187581 := bbase (se 3 (by rfl) ⟨222671, by rfl⟩ : syracuseStep 1187581 = 445343) (by norm_num)
theorem B1056509 : Blo 467785 1056509 := bbase (se 3 (by rfl) ⟨198095, by rfl⟩ : syracuseStep 1056509 = 396191) (by norm_num)
theorem B1056581 : Blo 467785 1056581 := bbase (se 4 (by rfl) ⟨99054, by rfl⟩ : syracuseStep 1056581 = 198109) (by norm_num)
theorem B794461 : Blo 467785 794461 := bbase (se 3 (by rfl) ⟨148961, by rfl⟩ : syracuseStep 794461 = 297923) (by norm_num)
theorem B1187693 : Blo 467785 1187693 := bbase (se 3 (by rfl) ⟨222692, by rfl⟩ : syracuseStep 1187693 = 445385) (by norm_num)
theorem B1056653 : Blo 467785 1056653 := bbase (se 3 (by rfl) ⟨198122, by rfl⟩ : syracuseStep 1056653 = 396245) (by norm_num)
theorem B2138021 : Blo 467785 2138021 := bbase (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) (by norm_num)
theorem B794549 : Blo 467785 794549 := bbase (se 5 (by rfl) ⟨37244, by rfl⟩ : syracuseStep 794549 = 74489) (by norm_num)
theorem B1056725 : Blo 467785 1056725 := bbase (se 7 (by rfl) ⟨12383, by rfl⟩ : syracuseStep 1056725 = 24767) (by norm_num)
theorem B1056797 : Blo 467785 1056797 := bbase (se 3 (by rfl) ⟨198149, by rfl⟩ : syracuseStep 1056797 = 396299) (by norm_num)
theorem B892957 : Blo 467785 892957 := bbase (se 3 (by rfl) ⟨167429, by rfl⟩ : syracuseStep 892957 = 334859) (by norm_num)
theorem B1187885 : Blo 467785 1187885 := bbase (se 3 (by rfl) ⟨222728, by rfl⟩ : syracuseStep 1187885 = 445457) (by norm_num)
theorem B794677 : Blo 467785 794677 := bbase (se 5 (by rfl) ⟨37250, by rfl⟩ : syracuseStep 794677 = 74501) (by norm_num)
theorem B499781 : Blo 467785 499781 := bbase (se 4 (by rfl) ⟨46854, by rfl⟩ : syracuseStep 499781 = 93709) (by norm_num)
theorem B1056869 : Blo 467785 1056869 := bbase (se 4 (by rfl) ⟨99081, by rfl⟩ : syracuseStep 1056869 = 198163) (by norm_num)
theorem B1581173 : Blo 467785 1581173 := bbase (se 5 (by rfl) ⟨74117, by rfl⟩ : syracuseStep 1581173 = 148235) (by norm_num)
theorem B794765 : Blo 467785 794765 := bbase (se 3 (by rfl) ⟨149018, by rfl⟩ : syracuseStep 794765 = 298037) (by norm_num)
theorem B4006037 : Blo 467785 4006037 := bbase (se 6 (by rfl) ⟨93891, by rfl⟩ : syracuseStep 4006037 = 187783) (by norm_num)
theorem B1056941 : Blo 467785 1056941 := bbase (se 3 (by rfl) ⟨198176, by rfl⟩ : syracuseStep 1056941 = 396353) (by norm_num)
theorem B893101 : Blo 467785 893101 := bbase (se 3 (by rfl) ⟨167456, by rfl⟩ : syracuseStep 893101 = 334913) (by norm_num)
theorem B1777909 : Blo 467785 1777909 := bbase (se 5 (by rfl) ⟨83339, by rfl⟩ : syracuseStep 1777909 = 166679) (by norm_num)
theorem B1057013 : Blo 467785 1057013 := bbase (se 5 (by rfl) ⟨49547, by rfl⟩ : syracuseStep 1057013 = 99095) (by norm_num)
theorem B499969 : Blo 467785 499969 := bbase (se 2 (by rfl) ⟨187488, by rfl⟩ : syracuseStep 499969 = 374977) (by norm_num)
theorem B794893 : Blo 467785 794893 := bbase (se 3 (by rfl) ⟨149042, by rfl⟩ : syracuseStep 794893 = 298085) (by norm_num)
theorem B1057085 : Blo 467785 1057085 := bbase (se 3 (by rfl) ⟨198203, by rfl⟩ : syracuseStep 1057085 = 396407) (by norm_num)
theorem B893261 : Blo 467785 893261 := bbase (se 3 (by rfl) ⟨167486, by rfl⟩ : syracuseStep 893261 = 334973) (by norm_num)
theorem B794981 : Blo 467785 794981 := bbase (se 4 (by rfl) ⟨74529, by rfl⟩ : syracuseStep 794981 = 149059) (by norm_num)
theorem B1188229 : Blo 467785 1188229 := bbase (se 4 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 1188229 = 222793) (by norm_num)
theorem B1057157 : Blo 467785 1057157 := bbase (se 4 (by rfl) ⟨99108, by rfl⟩ : syracuseStep 1057157 = 198217) (by norm_num)
theorem B1057229 : Blo 467785 1057229 := bbase (se 3 (by rfl) ⟨198230, by rfl⟩ : syracuseStep 1057229 = 396461) (by norm_num)
theorem B893405 : Blo 467785 893405 := bbase (se 3 (by rfl) ⟨167513, by rfl⟩ : syracuseStep 893405 = 335027) (by norm_num)
theorem B795109 : Blo 467785 795109 := bbase (se 4 (by rfl) ⟨74541, by rfl⟩ : syracuseStep 795109 = 149083) (by norm_num)
theorem B1188341 : Blo 467785 1188341 := bbase (se 5 (by rfl) ⟨55703, by rfl⟩ : syracuseStep 1188341 = 111407) (by norm_num)
theorem B1057301 : Blo 467785 1057301 := bbase (se 6 (by rfl) ⟨24780, by rfl⟩ : syracuseStep 1057301 = 49561) (by norm_num)
theorem B1778213 : Blo 467785 1778213 := bbase (se 4 (by rfl) ⟨166707, by rfl⟩ : syracuseStep 1778213 = 333415) (by norm_num)
theorem B1581605 : Blo 467785 1581605 := bbase (se 4 (by rfl) ⟨148275, by rfl⟩ : syracuseStep 1581605 = 296551) (by norm_num)
theorem B795197 : Blo 467785 795197 := bbase (se 3 (by rfl) ⟨149099, by rfl⟩ : syracuseStep 795197 = 298199) (by norm_num)
theorem B1057373 : Blo 467785 1057373 := bbase (se 3 (by rfl) ⟨198257, by rfl⟩ : syracuseStep 1057373 = 396515) (by norm_num)
theorem B1057445 : Blo 467785 1057445 := bbase (se 4 (by rfl) ⟨99135, by rfl⟩ : syracuseStep 1057445 = 198271) (by norm_num)
theorem B565925 : Blo 467785 565925 := bbase (se 4 (by rfl) ⟨53055, by rfl⟩ : syracuseStep 565925 = 106111) (by norm_num)
theorem B1188533 : Blo 467785 1188533 := bbase (se 5 (by rfl) ⟨55712, by rfl⟩ : syracuseStep 1188533 = 111425) (by norm_num)
theorem B795325 : Blo 467785 795325 := bbase (se 3 (by rfl) ⟨149123, by rfl⟩ : syracuseStep 795325 = 298247) (by norm_num)
theorem B1057517 : Blo 467785 1057517 := bbase (se 3 (by rfl) ⟨198284, by rfl⟩ : syracuseStep 1057517 = 396569) (by norm_num)
theorem B893693 : Blo 467785 893693 := bbase (se 3 (by rfl) ⟨167567, by rfl⟩ : syracuseStep 893693 = 335135) (by norm_num)
theorem B2368277 : Blo 467785 2368277 := bbase (se 6 (by rfl) ⟨55506, by rfl⟩ : syracuseStep 2368277 = 111013) (by norm_num)
theorem B795413 : Blo 467785 795413 := bbase (se 6 (by rfl) ⟨18642, by rfl⟩ : syracuseStep 795413 = 37285) (by norm_num)
theorem B1057589 : Blo 467785 1057589 := bbase (se 5 (by rfl) ⟨49574, by rfl⟩ : syracuseStep 1057589 = 99149) (by norm_num)
theorem B566137 : Blo 467785 566137 := bbase (se 2 (by rfl) ⟨212301, by rfl⟩ : syracuseStep 566137 = 424603) (by norm_num)
theorem B1057661 : Blo 467785 1057661 := bbase (se 3 (by rfl) ⟨198311, by rfl⟩ : syracuseStep 1057661 = 396623) (by norm_num)
theorem B893845 : Blo 467785 893845 := bbase (se 6 (by rfl) ⟨20949, by rfl⟩ : syracuseStep 893845 = 41899) (by norm_num)
theorem B795541 : Blo 467785 795541 := bbase (se 6 (by rfl) ⟨18645, by rfl⟩ : syracuseStep 795541 = 37291) (by norm_num)
theorem B1057733 : Blo 467785 1057733 := bbase (se 4 (by rfl) ⟨99162, by rfl⟩ : syracuseStep 1057733 = 198325) (by norm_num)
theorem B1582037 : Blo 467785 1582037 := bbase (se 7 (by rfl) ⟨18539, by rfl⟩ : syracuseStep 1582037 = 37079) (by norm_num)
theorem B795629 : Blo 467785 795629 := bbase (se 3 (by rfl) ⟨149180, by rfl⟩ : syracuseStep 795629 = 298361) (by norm_num)
theorem B566281 : Blo 467785 566281 := bbase (se 2 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 566281 = 424711) (by norm_num)
theorem B1188877 : Blo 467785 1188877 := bbase (se 3 (by rfl) ⟨222914, by rfl⟩ : syracuseStep 1188877 = 445829) (by norm_num)
theorem B1057805 : Blo 467785 1057805 := bbase (se 3 (by rfl) ⟨198338, by rfl⟩ : syracuseStep 1057805 = 396677) (by norm_num)
theorem B500789 : Blo 467785 500789 := bbase (se 5 (by rfl) ⟨23474, by rfl⟩ : syracuseStep 500789 = 46949) (by norm_num)
theorem B1057877 : Blo 467785 1057877 := bbase (se 8 (by rfl) ⟨6198, by rfl⟩ : syracuseStep 1057877 = 12397) (by norm_num)
theorem B795757 : Blo 467785 795757 := bbase (se 3 (by rfl) ⟨149204, by rfl⟩ : syracuseStep 795757 = 298409) (by norm_num)
theorem B1188989 : Blo 467785 1188989 := bbase (se 3 (by rfl) ⟨222935, by rfl⟩ : syracuseStep 1188989 = 445871) (by norm_num)
theorem B1057949 : Blo 467785 1057949 := bbase (se 3 (by rfl) ⟨198365, by rfl⟩ : syracuseStep 1057949 = 396731) (by norm_num)
theorem B894149 : Blo 467785 894149 := bbase (se 4 (by rfl) ⟨83826, by rfl⟩ : syracuseStep 894149 = 167653) (by norm_num)
theorem B795845 : Blo 467785 795845 := bbase (se 4 (by rfl) ⟨74610, by rfl⟩ : syracuseStep 795845 = 149221) (by norm_num)
theorem B1058021 : Blo 467785 1058021 := bbase (se 4 (by rfl) ⟨99189, by rfl⟩ : syracuseStep 1058021 = 198379) (by norm_num)
theorem B2172149 : Blo 467785 2172149 := bbase (se 5 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 2172149 = 203639) (by norm_num)
theorem B1058093 : Blo 467785 1058093 := bbase (se 3 (by rfl) ⟨198392, by rfl⟩ : syracuseStep 1058093 = 396785) (by norm_num)
theorem B1189181 : Blo 467785 1189181 := bbase (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) (by norm_num)
theorem B795973 : Blo 467785 795973 := bbase (se 4 (by rfl) ⟨74622, by rfl⟩ : syracuseStep 795973 = 149245) (by norm_num)
theorem B1058165 : Blo 467785 1058165 := bbase (se 5 (by rfl) ⟨49601, by rfl⟩ : syracuseStep 1058165 = 99203) (by norm_num)
theorem B1582469 : Blo 467785 1582469 := bbase (se 4 (by rfl) ⟨148356, by rfl⟩ : syracuseStep 1582469 = 296713) (by norm_num)
theorem B3581333 : Blo 467785 3581333 := bbase (se 6 (by rfl) ⟨83937, by rfl⟩ : syracuseStep 3581333 = 167875) (by norm_num)
theorem B796061 : Blo 467785 796061 := bbase (se 3 (by rfl) ⟨149261, by rfl⟩ : syracuseStep 796061 = 298523) (by norm_num)
theorem B1058237 : Blo 467785 1058237 := bbase (se 3 (by rfl) ⟨198419, by rfl⟩ : syracuseStep 1058237 = 396839) (by norm_num)
theorem B501233 : Blo 467785 501233 := bbase (se 2 (by rfl) ⟨187962, by rfl⟩ : syracuseStep 501233 = 375925) (by norm_num)
theorem B1058309 : Blo 467785 1058309 := bbase (se 4 (by rfl) ⟨99216, by rfl⟩ : syracuseStep 1058309 = 198433) (by norm_num)
theorem B1058381 : Blo 467785 1058381 := bbase (se 3 (by rfl) ⟨198446, by rfl⟩ : syracuseStep 1058381 = 396893) (by norm_num)
theorem B1189525 : Blo 467785 1189525 := bbase (se 6 (by rfl) ⟨27879, by rfl⟩ : syracuseStep 1189525 = 55759) (by norm_num)
theorem B1058453 : Blo 467785 1058453 := bbase (se 6 (by rfl) ⟨24807, by rfl⟩ : syracuseStep 1058453 = 49615) (by norm_num)
theorem B534205 : Blo 467785 534205 := bbase (se 3 (by rfl) ⟨100163, by rfl⟩ : syracuseStep 534205 = 200327) (by norm_num)
theorem B1287893 : Blo 467785 1287893 := bbase (se 7 (by rfl) ⟨15092, by rfl⟩ : syracuseStep 1287893 = 30185) (by norm_num)
theorem B1058525 : Blo 467785 1058525 := bbase (se 3 (by rfl) ⟨198473, by rfl⟩ : syracuseStep 1058525 = 396947) (by norm_num)
theorem B501481 : Blo 467785 501481 := bbase (se 2 (by rfl) ⟨188055, by rfl⟩ : syracuseStep 501481 = 376111) (by norm_num)
theorem B1189637 : Blo 467785 1189637 := bbase (se 4 (by rfl) ⟨111528, by rfl⟩ : syracuseStep 1189637 = 223057) (by norm_num)
theorem B4073237 : Blo 467785 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B1058597 : Blo 467785 1058597 := bbase (se 4 (by rfl) ⟨99243, by rfl⟩ : syracuseStep 1058597 = 198487) (by norm_num)
theorem B1582901 : Blo 467785 1582901 := bbase (se 5 (by rfl) ⟨74198, by rfl⟩ : syracuseStep 1582901 = 148397) (by norm_num)
theorem B1058669 : Blo 467785 1058669 := bbase (se 3 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 1058669 = 397001) (by norm_num)
theorem B1058741 : Blo 467785 1058741 := bbase (se 5 (by rfl) ⟨49628, by rfl⟩ : syracuseStep 1058741 = 99257) (by norm_num)
theorem B894901 : Blo 467785 894901 := bbase (se 5 (by rfl) ⟨41948, by rfl⟩ : syracuseStep 894901 = 83897) (by norm_num)
theorem B1189829 : Blo 467785 1189829 := bbase (se 4 (by rfl) ⟨111546, by rfl⟩ : syracuseStep 1189829 = 223093) (by norm_num)
theorem B1058813 : Blo 467785 1058813 := bbase (se 3 (by rfl) ⟨198527, by rfl⟩ : syracuseStep 1058813 = 397055) (by norm_num)
theorem B2369573 : Blo 467785 2369573 := bbase (se 4 (by rfl) ⟨222147, by rfl⟩ : syracuseStep 2369573 = 444295) (by norm_num)
theorem B1058885 : Blo 467785 1058885 := bbase (se 4 (by rfl) ⟨99270, by rfl⟩ : syracuseStep 1058885 = 198541) (by norm_num)
theorem B895045 : Blo 467785 895045 := bbase (se 4 (by rfl) ⟨83910, by rfl⟩ : syracuseStep 895045 = 167821) (by norm_num)
theorem B1058957 : Blo 467785 1058957 := bbase (se 3 (by rfl) ⟨198554, by rfl⟩ : syracuseStep 1058957 = 397109) (by norm_num)
theorem B501913 : Blo 467785 501913 := bbase (se 2 (by rfl) ⟨188217, by rfl⟩ : syracuseStep 501913 = 376435) (by norm_num)
theorem B1059029 : Blo 467785 1059029 := bbase (se 7 (by rfl) ⟨12410, by rfl⟩ : syracuseStep 1059029 = 24821) (by norm_num)
theorem B501985 : Blo 467785 501985 := bbase (se 2 (by rfl) ⟨188244, by rfl⟩ : syracuseStep 501985 = 376489) (by norm_num)
theorem B1583333 : Blo 467785 1583333 := bbase (se 4 (by rfl) ⟨148437, by rfl⟩ : syracuseStep 1583333 = 296875) (by norm_num)
theorem B895205 : Blo 467785 895205 := bbase (se 4 (by rfl) ⟨83925, by rfl⟩ : syracuseStep 895205 = 167851) (by norm_num)
theorem B600313 : Blo 467785 600313 := bbase (se 2 (by rfl) ⟨225117, by rfl⟩ : syracuseStep 600313 = 450235) (by norm_num)
theorem B1190173 : Blo 467785 1190173 := bbase (se 3 (by rfl) ⟨223157, by rfl⟩ : syracuseStep 1190173 = 446315) (by norm_num)
theorem B1059101 : Blo 467785 1059101 := bbase (se 3 (by rfl) ⟨198581, by rfl⟩ : syracuseStep 1059101 = 397163) (by norm_num)
theorem B1059173 : Blo 467785 1059173 := bbase (se 4 (by rfl) ⟨99297, by rfl⟩ : syracuseStep 1059173 = 198595) (by norm_num)
theorem B895349 : Blo 467785 895349 := bbase (se 5 (by rfl) ⟨41969, by rfl⟩ : syracuseStep 895349 = 83939) (by norm_num)
theorem B1190285 : Blo 467785 1190285 := bbase (se 3 (by rfl) ⟨223178, by rfl⟩ : syracuseStep 1190285 = 446357) (by norm_num)
theorem B1059245 : Blo 467785 1059245 := bbase (se 3 (by rfl) ⟨198608, by rfl⟩ : syracuseStep 1059245 = 397217) (by norm_num)
theorem B666101 : Blo 467785 666101 := bbase (se 5 (by rfl) ⟨31223, by rfl⟩ : syracuseStep 666101 = 62447) (by norm_num)
theorem B1059317 : Blo 467785 1059317 := bbase (se 5 (by rfl) ⟨49655, by rfl⟩ : syracuseStep 1059317 = 99311) (by norm_num)
theorem B535081 : Blo 467785 535081 := bbase (se 2 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 535081 = 401311) (by norm_num)
theorem B1059389 : Blo 467785 1059389 := bbase (se 3 (by rfl) ⟨198635, by rfl⟩ : syracuseStep 1059389 = 397271) (by norm_num)
theorem B666181 : Blo 467785 666181 := bbase (se 4 (by rfl) ⟨62454, by rfl⟩ : syracuseStep 666181 = 124909) (by norm_num)
theorem B1190477 : Blo 467785 1190477 := bbase (se 3 (by rfl) ⟨223214, by rfl⟩ : syracuseStep 1190477 = 446429) (by norm_num)
theorem B600661 : Blo 467785 600661 := bbase (se 8 (by rfl) ⟨3519, by rfl⟩ : syracuseStep 600661 = 7039) (by norm_num)
theorem B502357 : Blo 467785 502357 := bbase (se 8 (by rfl) ⟨2943, by rfl⟩ : syracuseStep 502357 = 5887) (by norm_num)
theorem B1780325 : Blo 467785 1780325 := bbase (se 4 (by rfl) ⟨166905, by rfl⟩ : syracuseStep 1780325 = 333811) (by norm_num)
theorem B2009717 : Blo 467785 2009717 := bbase (se 5 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 2009717 = 188411) (by norm_num)
theorem B1059461 : Blo 467785 1059461 := bbase (se 4 (by rfl) ⟨99324, by rfl⟩ : syracuseStep 1059461 = 198649) (by norm_num)
theorem B1583765 : Blo 467785 1583765 := bbase (se 6 (by rfl) ⟨37119, by rfl⟩ : syracuseStep 1583765 = 74239) (by norm_num)
theorem B895637 : Blo 467785 895637 := bbase (se 6 (by rfl) ⟨20991, by rfl⟩ : syracuseStep 895637 = 41983) (by norm_num)
theorem B666301 : Blo 467785 666301 := bbase (se 3 (by rfl) ⟨124931, by rfl⟩ : syracuseStep 666301 = 249863) (by norm_num)
theorem B1059533 : Blo 467785 1059533 := bbase (se 3 (by rfl) ⟨198662, by rfl⟩ : syracuseStep 1059533 = 397325) (by norm_num)
theorem B3386069 : Blo 467785 3386069 := bbase (se 7 (by rfl) ⟨39680, by rfl⟩ : syracuseStep 3386069 = 79361) (by norm_num)
theorem B1059605 : Blo 467785 1059605 := bbase (se 6 (by rfl) ⟨24834, by rfl⟩ : syracuseStep 1059605 = 49669) (by norm_num)
theorem B666397 : Blo 467785 666397 := bbase (se 3 (by rfl) ⟨124949, by rfl⟩ : syracuseStep 666397 = 249899) (by norm_num)
theorem B1125181 : Blo 467785 1125181 := bbase (se 3 (by rfl) ⟨210971, by rfl⟩ : syracuseStep 1125181 = 421943) (by norm_num)
theorem B1059677 : Blo 467785 1059677 := bbase (se 3 (by rfl) ⟨198689, by rfl⟩ : syracuseStep 1059677 = 397379) (by norm_num)
theorem B1780613 : Blo 467785 1780613 := bbase (se 4 (by rfl) ⟨166932, by rfl⟩ : syracuseStep 1780613 = 333865) (by norm_num)
theorem B1190821 : Blo 467785 1190821 := bbase (se 4 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 1190821 = 223279) (by norm_num)
theorem B1059749 : Blo 467785 1059749 := bbase (se 4 (by rfl) ⟨99351, by rfl⟩ : syracuseStep 1059749 = 198703) (by norm_num)
theorem B502733 : Blo 467785 502733 := bbase (se 3 (by rfl) ⟨94262, by rfl⟩ : syracuseStep 502733 = 188525) (by norm_num)
theorem B1059821 : Blo 467785 1059821 := bbase (se 3 (by rfl) ⟨198716, by rfl⟩ : syracuseStep 1059821 = 397433) (by norm_num)
theorem B1190933 : Blo 467785 1190933 := bbase (se 6 (by rfl) ⟨27912, by rfl⟩ : syracuseStep 1190933 = 55825) (by norm_num)
theorem B502805 : Blo 467785 502805 := bbase (se 6 (by rfl) ⟨11784, by rfl⟩ : syracuseStep 502805 = 23569) (by norm_num)
theorem B4009013 : Blo 467785 4009013 := bbase (se 5 (by rfl) ⟨187922, by rfl⟩ : syracuseStep 4009013 = 375845) (by norm_num)
theorem B1059893 : Blo 467785 1059893 := bbase (se 5 (by rfl) ⟨49682, by rfl⟩ : syracuseStep 1059893 = 99365) (by norm_num)
theorem B1584197 : Blo 467785 1584197 := bbase (se 4 (by rfl) ⟨148518, by rfl⟩ : syracuseStep 1584197 = 297037) (by norm_num)
theorem B535673 : Blo 467785 535673 := bbase (se 2 (by rfl) ⟨200877, by rfl⟩ : syracuseStep 535673 = 401755) (by norm_num)
theorem B1059965 : Blo 467785 1059965 := bbase (se 3 (by rfl) ⟨198743, by rfl⟩ : syracuseStep 1059965 = 397487) (by norm_num)
theorem B1060037 : Blo 467785 1060037 := bbase (se 4 (by rfl) ⟨99378, by rfl⟩ : syracuseStep 1060037 = 198757) (by norm_num)
theorem B502993 : Blo 467785 502993 := bbase (se 2 (by rfl) ⟨188622, by rfl⟩ : syracuseStep 502993 = 377245) (by norm_num)
theorem B1191125 : Blo 467785 1191125 := bbase (se 7 (by rfl) ⟨13958, by rfl⟩ : syracuseStep 1191125 = 27917) (by norm_num)
theorem B666893 : Blo 467785 666893 := bbase (se 3 (by rfl) ⟨125042, by rfl⟩ : syracuseStep 666893 = 250085) (by norm_num)
theorem B1060109 : Blo 467785 1060109 := bbase (se 3 (by rfl) ⟨198770, by rfl⟩ : syracuseStep 1060109 = 397541) (by norm_num)
theorem B535837 : Blo 467785 535837 := bbase (se 3 (by rfl) ⟨100469, by rfl⟩ : syracuseStep 535837 = 200939) (by norm_num)
theorem B2370869 : Blo 467785 2370869 := bbase (se 5 (by rfl) ⟨111134, by rfl⟩ : syracuseStep 2370869 = 222269) (by norm_num)
theorem B1060181 : Blo 467785 1060181 := bbase (se 11 (by rfl) ⟨776, by rfl⟩ : syracuseStep 1060181 = 1553) (by norm_num)
theorem B503177 : Blo 467785 503177 := bbase (se 2 (by rfl) ⟨188691, by rfl⟩ : syracuseStep 503177 = 377383) (by norm_num)
theorem B1060253 : Blo 467785 1060253 := bbase (se 3 (by rfl) ⟨198797, by rfl⟩ : syracuseStep 1060253 = 397595) (by norm_num)
theorem B1125845 : Blo 467785 1125845 := bbase (se 7 (by rfl) ⟨13193, by rfl⟩ : syracuseStep 1125845 = 26387) (by norm_num)
theorem B1060325 : Blo 467785 1060325 := bbase (se 4 (by rfl) ⟨99405, by rfl⟩ : syracuseStep 1060325 = 198811) (by norm_num)
theorem B1584629 : Blo 467785 1584629 := bbase (se 5 (by rfl) ⟨74279, by rfl⟩ : syracuseStep 1584629 = 148559) (by norm_num)
theorem B1191469 : Blo 467785 1191469 := bbase (se 3 (by rfl) ⟨223400, by rfl⟩ : syracuseStep 1191469 = 446801) (by norm_num)
theorem B1060397 : Blo 467785 1060397 := bbase (se 3 (by rfl) ⟨198824, by rfl⟩ : syracuseStep 1060397 = 397649) (by norm_num)
theorem B1060469 : Blo 467785 1060469 := bbase (se 5 (by rfl) ⟨49709, by rfl⟩ : syracuseStep 1060469 = 99419) (by norm_num)
theorem B1191581 : Blo 467785 1191581 := bbase (se 3 (by rfl) ⟨223421, by rfl⟩ : syracuseStep 1191581 = 446843) (by norm_num)
theorem B1060541 : Blo 467785 1060541 := bbase (se 3 (by rfl) ⟨198851, by rfl⟩ : syracuseStep 1060541 = 397703) (by norm_num)
theorem B1060613 : Blo 467785 1060613 := bbase (se 4 (by rfl) ⟨99432, by rfl⟩ : syracuseStep 1060613 = 198865) (by norm_num)
theorem B667445 : Blo 467785 667445 := bbase (se 5 (by rfl) ⟨31286, by rfl⟩ : syracuseStep 667445 = 62573) (by norm_num)
theorem B1060685 : Blo 467785 1060685 := bbase (se 3 (by rfl) ⟨198878, by rfl⟩ : syracuseStep 1060685 = 397757) (by norm_num)
theorem B1191773 : Blo 467785 1191773 := bbase (se 3 (by rfl) ⟨223457, by rfl⟩ : syracuseStep 1191773 = 446915) (by norm_num)
theorem B1060757 : Blo 467785 1060757 := bbase (se 6 (by rfl) ⟨24861, by rfl⟩ : syracuseStep 1060757 = 49723) (by norm_num)
theorem B1585061 : Blo 467785 1585061 := bbase (se 4 (by rfl) ⟨148599, by rfl⟩ : syracuseStep 1585061 = 297199) (by norm_num)
theorem B1355717 : Blo 467785 1355717 := bbase (se 4 (by rfl) ⟨127098, by rfl⟩ : syracuseStep 1355717 = 254197) (by norm_num)
theorem B1060829 : Blo 467785 1060829 := bbase (se 3 (by rfl) ⟨198905, by rfl⟩ : syracuseStep 1060829 = 397811) (by norm_num)
theorem B1781797 : Blo 467785 1781797 := bbase (se 4 (by rfl) ⟨167043, by rfl⟩ : syracuseStep 1781797 = 334087) (by norm_num)
theorem B1060901 : Blo 467785 1060901 := bbase (se 4 (by rfl) ⟨99459, by rfl⟩ : syracuseStep 1060901 = 198919) (by norm_num)
theorem B1060973 : Blo 467785 1060973 := bbase (se 3 (by rfl) ⟨198932, by rfl⟩ : syracuseStep 1060973 = 397865) (by norm_num)
theorem B536749 : Blo 467785 536749 := bbase (se 3 (by rfl) ⟨100640, by rfl⟩ : syracuseStep 536749 = 201281) (by norm_num)
theorem B1192117 : Blo 467785 1192117 := bbase (se 5 (by rfl) ⟨55880, by rfl⟩ : syracuseStep 1192117 = 111761) (by norm_num)
theorem B1061045 : Blo 467785 1061045 := bbase (se 5 (by rfl) ⟨49736, by rfl⟩ : syracuseStep 1061045 = 99473) (by norm_num)
theorem B1061117 : Blo 467785 1061117 := bbase (se 3 (by rfl) ⟨198959, by rfl⟩ : syracuseStep 1061117 = 397919) (by norm_num)
theorem B1192229 : Blo 467785 1192229 := bbase (se 4 (by rfl) ⟨111771, by rfl⟩ : syracuseStep 1192229 = 223543) (by norm_num)
theorem B1061189 : Blo 467785 1061189 := bbase (se 4 (by rfl) ⟨99486, by rfl⟩ : syracuseStep 1061189 = 198973) (by norm_num)
theorem B1782101 : Blo 467785 1782101 := bbase (se 10 (by rfl) ⟨2610, by rfl⟩ : syracuseStep 1782101 = 5221) (by norm_num)
theorem B1585493 : Blo 467785 1585493 := bbase (se 10 (by rfl) ⟨2322, by rfl⟩ : syracuseStep 1585493 = 4645) (by norm_num)
theorem B2011493 : Blo 467785 2011493 := bbase (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) (by norm_num)
theorem B1061261 : Blo 467785 1061261 := bbase (se 3 (by rfl) ⟨198986, by rfl⟩ : syracuseStep 1061261 = 397973) (by norm_num)
theorem B1061333 : Blo 467785 1061333 := bbase (se 7 (by rfl) ⟨12437, by rfl⟩ : syracuseStep 1061333 = 24875) (by norm_num)
theorem B1192421 : Blo 467785 1192421 := bbase (se 4 (by rfl) ⟨111789, by rfl⟩ : syracuseStep 1192421 = 223579) (by norm_num)
theorem B602653 : Blo 467785 602653 := bbase (se 3 (by rfl) ⟨112997, by rfl⟩ : syracuseStep 602653 = 225995) (by norm_num)
theorem B1061405 : Blo 467785 1061405 := bbase (se 3 (by rfl) ⟨199013, by rfl⟩ : syracuseStep 1061405 = 398027) (by norm_num)
theorem B668197 : Blo 467785 668197 := bbase (se 4 (by rfl) ⟨62643, by rfl⟩ : syracuseStep 668197 = 125287) (by norm_num)
theorem B2372165 : Blo 467785 2372165 := bbase (se 4 (by rfl) ⟨222390, by rfl⟩ : syracuseStep 2372165 = 444781) (by norm_num)
theorem B1061477 : Blo 467785 1061477 := bbase (se 4 (by rfl) ⟨99513, by rfl⟩ : syracuseStep 1061477 = 199027) (by norm_num)
theorem B1585925 : Blo 467785 1585925 := bbase (se 4 (by rfl) ⟨148680, by rfl⟩ : syracuseStep 1585925 = 297361) (by norm_num)
theorem B1192765 : Blo 467785 1192765 := bbase (se 3 (by rfl) ⟨223643, by rfl⟩ : syracuseStep 1192765 = 447287) (by norm_num)
theorem B1192877 : Blo 467785 1192877 := bbase (se 3 (by rfl) ⟨223664, by rfl⟩ : syracuseStep 1192877 = 447329) (by norm_num)
theorem B635909 : Blo 467785 635909 := bbase (se 4 (by rfl) ⟨59616, by rfl⟩ : syracuseStep 635909 = 119233) (by norm_num)
theorem B537625 : Blo 467785 537625 := bbase (se 2 (by rfl) ⟨201609, by rfl⟩ : syracuseStep 537625 = 403219) (by norm_num)
theorem B3224629 : Blo 467785 3224629 := bbase (se 5 (by rfl) ⟨151154, by rfl⟩ : syracuseStep 3224629 = 302309) (by norm_num)
theorem B1193069 : Blo 467785 1193069 := bbase (se 3 (by rfl) ⟨223700, by rfl⟩ : syracuseStep 1193069 = 447401) (by norm_num)
theorem B1586357 : Blo 467785 1586357 := bbase (se 5 (by rfl) ⟨74360, by rfl⟩ : syracuseStep 1586357 = 148721) (by norm_num)
theorem B1127621 : Blo 467785 1127621 := bbase (se 4 (by rfl) ⟨105714, by rfl⟩ : syracuseStep 1127621 = 211429) (by norm_num)
theorem B701693 : Blo 467785 701693 := bbase (se 3 (by rfl) ⟨131567, by rfl⟩ : syracuseStep 701693 = 263135) (by norm_num)
theorem B701717 : Blo 467785 701717 := bbase (se 6 (by rfl) ⟨16446, by rfl⟩ : syracuseStep 701717 = 32893) (by norm_num)
theorem B701741 : Blo 467785 701741 := bbase (se 3 (by rfl) ⟨131576, by rfl⟩ : syracuseStep 701741 = 263153) (by norm_num)
theorem B668989 : Blo 467785 668989 := bbase (se 3 (by rfl) ⟨125435, by rfl⟩ : syracuseStep 668989 = 250871) (by norm_num)
theorem B701765 : Blo 467785 701765 := bbase (se 4 (by rfl) ⟨65790, by rfl⟩ : syracuseStep 701765 = 131581) (by norm_num)
theorem B2012485 : Blo 467785 2012485 := bbase (se 4 (by rfl) ⟨188670, by rfl⟩ : syracuseStep 2012485 = 377341) (by norm_num)
theorem B701789 : Blo 467785 701789 := bbase (se 3 (by rfl) ⟨131585, by rfl⟩ : syracuseStep 701789 = 263171) (by norm_num)
theorem B537953 : Blo 467785 537953 := bbase (se 2 (by rfl) ⟨201732, by rfl⟩ : syracuseStep 537953 = 403465) (by norm_num)
theorem B701813 : Blo 467785 701813 := bbase (se 5 (by rfl) ⟨32897, by rfl⟩ : syracuseStep 701813 = 65795) (by norm_num)
theorem B701837 : Blo 467785 701837 := bbase (se 3 (by rfl) ⟨131594, by rfl⟩ : syracuseStep 701837 = 263189) (by norm_num)
theorem B701861 : Blo 467785 701861 := bbase (se 4 (by rfl) ⟨65799, by rfl⟩ : syracuseStep 701861 = 131599) (by norm_num)
theorem B701885 : Blo 467785 701885 := bbase (se 3 (by rfl) ⟨131603, by rfl⟩ : syracuseStep 701885 = 263207) (by norm_num)
theorem B1193413 : Blo 467785 1193413 := bbase (se 4 (by rfl) ⟨111882, by rfl⟩ : syracuseStep 1193413 = 223765) (by norm_num)
theorem B701909 : Blo 467785 701909 := bbase (se 7 (by rfl) ⟨8225, by rfl⟩ : syracuseStep 701909 = 16451) (by norm_num)
theorem B701933 : Blo 467785 701933 := bbase (se 3 (by rfl) ⟨131612, by rfl⟩ : syracuseStep 701933 = 263225) (by norm_num)
theorem B701957 : Blo 467785 701957 := bbase (se 4 (by rfl) ⟨65808, by rfl⟩ : syracuseStep 701957 = 131617) (by norm_num)
theorem B701981 : Blo 467785 701981 := bbase (se 3 (by rfl) ⟨131621, by rfl⟩ : syracuseStep 701981 = 263243) (by norm_num)
theorem B702005 : Blo 467785 702005 := bbase (se 5 (by rfl) ⟨32906, by rfl⟩ : syracuseStep 702005 = 65813) (by norm_num)
theorem B1193525 : Blo 467785 1193525 := bbase (se 5 (by rfl) ⟨55946, by rfl⟩ : syracuseStep 1193525 = 111893) (by norm_num)
theorem B702029 : Blo 467785 702029 := bbase (se 3 (by rfl) ⟨131630, by rfl⟩ : syracuseStep 702029 = 263261) (by norm_num)
theorem B636493 : Blo 467785 636493 := bbase (se 3 (by rfl) ⟨119342, by rfl⟩ : syracuseStep 636493 = 238685) (by norm_num)
theorem B702053 : Blo 467785 702053 := bbase (se 4 (by rfl) ⟨65817, by rfl⟩ : syracuseStep 702053 = 131635) (by norm_num)
theorem B1586789 : Blo 467785 1586789 := bbase (se 4 (by rfl) ⟨148761, by rfl⟩ : syracuseStep 1586789 = 297523) (by norm_num)
theorem B702077 : Blo 467785 702077 := bbase (se 3 (by rfl) ⟨131639, by rfl⟩ : syracuseStep 702077 = 263279) (by norm_num)
theorem B669325 : Blo 467785 669325 := bbase (se 3 (by rfl) ⟨125498, by rfl⟩ : syracuseStep 669325 = 250997) (by norm_num)
theorem B702101 : Blo 467785 702101 := bbase (se 6 (by rfl) ⟨16455, by rfl⟩ : syracuseStep 702101 = 32911) (by norm_num)
theorem B702125 : Blo 467785 702125 := bbase (se 3 (by rfl) ⟨131648, by rfl⟩ : syracuseStep 702125 = 263297) (by norm_num)
theorem B702149 : Blo 467785 702149 := bbase (se 4 (by rfl) ⟨65826, by rfl⟩ : syracuseStep 702149 = 131653) (by norm_num)
theorem B702173 : Blo 467785 702173 := bbase (se 3 (by rfl) ⟨131657, by rfl⟩ : syracuseStep 702173 = 263315) (by norm_num)
theorem B702197 : Blo 467785 702197 := bbase (se 5 (by rfl) ⟨32915, by rfl⟩ : syracuseStep 702197 = 65831) (by norm_num)
theorem B636661 : Blo 467785 636661 := bbase (se 5 (by rfl) ⟨29843, by rfl⟩ : syracuseStep 636661 = 59687) (by norm_num)
theorem B1193717 : Blo 467785 1193717 := bbase (se 5 (by rfl) ⟨55955, by rfl⟩ : syracuseStep 1193717 = 111911) (by norm_num)
theorem B702221 : Blo 467785 702221 := bbase (se 3 (by rfl) ⟨131666, by rfl⟩ : syracuseStep 702221 = 263333) (by norm_num)
theorem B702245 : Blo 467785 702245 := bbase (se 4 (by rfl) ⟨65835, by rfl⟩ : syracuseStep 702245 = 131671) (by norm_num)
theorem B702269 : Blo 467785 702269 := bbase (se 3 (by rfl) ⟨131675, by rfl⟩ : syracuseStep 702269 = 263351) (by norm_num)
theorem B800597 : Blo 467785 800597 := bbase (se 9 (by rfl) ⟨2345, by rfl⟩ : syracuseStep 800597 = 4691) (by norm_num)
theorem B702293 : Blo 467785 702293 := bbase (se 9 (by rfl) ⟨2057, by rfl⟩ : syracuseStep 702293 = 4115) (by norm_num)
theorem B2373461 : Blo 467785 2373461 := bbase (se 9 (by rfl) ⟨6953, by rfl⟩ : syracuseStep 2373461 = 13907) (by norm_num)
theorem B669541 : Blo 467785 669541 := bbase (se 4 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 669541 = 125539) (by norm_num)
theorem B702317 : Blo 467785 702317 := bbase (se 3 (by rfl) ⟨131684, by rfl⟩ : syracuseStep 702317 = 263369) (by norm_num)
theorem B702341 : Blo 467785 702341 := bbase (se 4 (by rfl) ⟨65844, by rfl⟩ : syracuseStep 702341 = 131689) (by norm_num)
theorem B2537365 : Blo 467785 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B702365 : Blo 467785 702365 := bbase (se 3 (by rfl) ⟨131693, by rfl⟩ : syracuseStep 702365 = 263387) (by norm_num)
theorem B702389 : Blo 467785 702389 := bbase (se 5 (by rfl) ⟨32924, by rfl⟩ : syracuseStep 702389 = 65849) (by norm_num)
theorem B702413 : Blo 467785 702413 := bbase (se 3 (by rfl) ⟨131702, by rfl⟩ : syracuseStep 702413 = 263405) (by norm_num)
theorem B702437 : Blo 467785 702437 := bbase (se 4 (by rfl) ⟨65853, by rfl⟩ : syracuseStep 702437 = 131707) (by norm_num)
theorem B702461 : Blo 467785 702461 := bbase (se 3 (by rfl) ⟨131711, by rfl⟩ : syracuseStep 702461 = 263423) (by norm_num)
theorem B702485 : Blo 467785 702485 := bbase (se 6 (by rfl) ⟨16464, by rfl⟩ : syracuseStep 702485 = 32929) (by norm_num)
theorem B1587221 : Blo 467785 1587221 := bbase (se 6 (by rfl) ⟨37200, by rfl⟩ : syracuseStep 1587221 = 74401) (by norm_num)
theorem B702509 : Blo 467785 702509 := bbase (se 3 (by rfl) ⟨131720, by rfl⟩ : syracuseStep 702509 = 263441) (by norm_num)
theorem B702533 : Blo 467785 702533 := bbase (se 4 (by rfl) ⟨65862, by rfl⟩ : syracuseStep 702533 = 131725) (by norm_num)
theorem B1194061 : Blo 467785 1194061 := bbase (se 3 (by rfl) ⟨223886, by rfl⟩ : syracuseStep 1194061 = 447773) (by norm_num)
theorem B702557 : Blo 467785 702557 := bbase (se 3 (by rfl) ⟨131729, by rfl⟩ : syracuseStep 702557 = 263459) (by norm_num)
theorem B702581 : Blo 467785 702581 := bbase (se 5 (by rfl) ⟨32933, by rfl⟩ : syracuseStep 702581 = 65867) (by norm_num)
theorem B702605 : Blo 467785 702605 := bbase (se 3 (by rfl) ⟨131738, by rfl⟩ : syracuseStep 702605 = 263477) (by norm_num)
theorem B9615509 : Blo 467785 9615509 := bbase (se 6 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 9615509 = 450727) (by norm_num)
theorem B2144405 : Blo 467785 2144405 := bbase (se 6 (by rfl) ⟨50259, by rfl⟩ : syracuseStep 2144405 = 100519) (by norm_num)
theorem B702629 : Blo 467785 702629 := bbase (se 4 (by rfl) ⟨65871, by rfl⟩ : syracuseStep 702629 = 131743) (by norm_num)
theorem B702653 : Blo 467785 702653 := bbase (se 3 (by rfl) ⟨131747, by rfl⟩ : syracuseStep 702653 = 263495) (by norm_num)
theorem B1194173 : Blo 467785 1194173 := bbase (se 3 (by rfl) ⟨223907, by rfl⟩ : syracuseStep 1194173 = 447815) (by norm_num)
theorem B702677 : Blo 467785 702677 := bbase (se 7 (by rfl) ⟨8234, by rfl⟩ : syracuseStep 702677 = 16469) (by norm_num)
theorem B2865365 : Blo 467785 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B669917 : Blo 467785 669917 := bbase (se 3 (by rfl) ⟨125609, by rfl⟩ : syracuseStep 669917 = 251219) (by norm_num)
theorem B702701 : Blo 467785 702701 := bbase (se 3 (by rfl) ⟨131756, by rfl⟩ : syracuseStep 702701 = 263513) (by norm_num)
theorem B702725 : Blo 467785 702725 := bbase (se 4 (by rfl) ⟨65880, by rfl⟩ : syracuseStep 702725 = 131761) (by norm_num)
theorem B702749 : Blo 467785 702749 := bbase (se 3 (by rfl) ⟨131765, by rfl⟩ : syracuseStep 702749 = 263531) (by norm_num)
theorem B702773 : Blo 467785 702773 := bbase (se 5 (by rfl) ⟨32942, by rfl⟩ : syracuseStep 702773 = 65885) (by norm_num)
theorem B702797 : Blo 467785 702797 := bbase (se 3 (by rfl) ⟨131774, by rfl⟩ : syracuseStep 702797 = 263549) (by norm_num)
theorem B702821 : Blo 467785 702821 := bbase (se 4 (by rfl) ⟨65889, by rfl⟩ : syracuseStep 702821 = 131779) (by norm_num)
theorem B702845 : Blo 467785 702845 := bbase (se 3 (by rfl) ⟨131783, by rfl⟩ : syracuseStep 702845 = 263567) (by norm_num)
theorem B702869 : Blo 467785 702869 := bbase (se 6 (by rfl) ⟨16473, by rfl⟩ : syracuseStep 702869 = 32947) (by norm_num)
theorem B1784213 : Blo 467785 1784213 := bbase (se 6 (by rfl) ⟨41817, by rfl⟩ : syracuseStep 1784213 = 83635) (by norm_num)
theorem B702893 : Blo 467785 702893 := bbase (se 3 (by rfl) ⟨131792, by rfl⟩ : syracuseStep 702893 = 263585) (by norm_num)
theorem B702917 : Blo 467785 702917 := bbase (se 4 (by rfl) ⟨65898, by rfl⟩ : syracuseStep 702917 = 131797) (by norm_num)
theorem B1587653 : Blo 467785 1587653 := bbase (se 4 (by rfl) ⟨148842, by rfl⟩ : syracuseStep 1587653 = 297685) (by norm_num)
theorem B702941 : Blo 467785 702941 := bbase (se 3 (by rfl) ⟨131801, by rfl⟩ : syracuseStep 702941 = 263603) (by norm_num)
theorem B702965 : Blo 467785 702965 := bbase (se 5 (by rfl) ⟨32951, by rfl⟩ : syracuseStep 702965 = 65903) (by norm_num)
theorem B702989 : Blo 467785 702989 := bbase (se 3 (by rfl) ⟨131810, by rfl⟩ : syracuseStep 702989 = 263621) (by norm_num)
theorem B703013 : Blo 467785 703013 := bbase (se 4 (by rfl) ⟨65907, by rfl⟩ : syracuseStep 703013 = 131815) (by norm_num)
theorem B1522229 : Blo 467785 1522229 := bbase (se 5 (by rfl) ⟨71354, by rfl⟩ : syracuseStep 1522229 = 142709) (by norm_num)
theorem B703037 : Blo 467785 703037 := bbase (se 3 (by rfl) ⟨131819, by rfl⟩ : syracuseStep 703037 = 263639) (by norm_num)
theorem B703061 : Blo 467785 703061 := bbase (se 8 (by rfl) ⟨4119, by rfl⟩ : syracuseStep 703061 = 8239) (by norm_num)
theorem B703085 : Blo 467785 703085 := bbase (se 3 (by rfl) ⟨131828, by rfl⟩ : syracuseStep 703085 = 263657) (by norm_num)
theorem B703109 : Blo 467785 703109 := bbase (se 4 (by rfl) ⟨65916, by rfl⟩ : syracuseStep 703109 = 131833) (by norm_num)
theorem B703133 : Blo 467785 703133 := bbase (se 3 (by rfl) ⟨131837, by rfl⟩ : syracuseStep 703133 = 263675) (by norm_num)
theorem B703157 : Blo 467785 703157 := bbase (se 5 (by rfl) ⟨32960, by rfl⟩ : syracuseStep 703157 = 65921) (by norm_num)
theorem B1784501 : Blo 467785 1784501 := bbase (se 5 (by rfl) ⟨83648, by rfl⟩ : syracuseStep 1784501 = 167297) (by norm_num)
theorem B703181 : Blo 467785 703181 := bbase (se 3 (by rfl) ⟨131846, by rfl⟩ : syracuseStep 703181 = 263693) (by norm_num)
theorem B703205 : Blo 467785 703205 := bbase (se 4 (by rfl) ⟨65925, by rfl⟩ : syracuseStep 703205 = 131851) (by norm_num)
theorem B2407141 : Blo 467785 2407141 := bbase (se 4 (by rfl) ⟨225669, by rfl⟩ : syracuseStep 2407141 = 451339) (by norm_num)
theorem B703229 : Blo 467785 703229 := bbase (se 3 (by rfl) ⟨131855, by rfl⟩ : syracuseStep 703229 = 263711) (by norm_num)
theorem B703253 : Blo 467785 703253 := bbase (se 6 (by rfl) ⟨16482, by rfl⟩ : syracuseStep 703253 = 32965) (by norm_num)
theorem B801565 : Blo 467785 801565 := bbase (se 3 (by rfl) ⟨150293, by rfl⟩ : syracuseStep 801565 = 300587) (by norm_num)
theorem B703277 : Blo 467785 703277 := bbase (se 3 (by rfl) ⟨131864, by rfl⟩ : syracuseStep 703277 = 263729) (by norm_num)
theorem B703301 : Blo 467785 703301 := bbase (se 4 (by rfl) ⟨65934, by rfl⟩ : syracuseStep 703301 = 131869) (by norm_num)
theorem B703325 : Blo 467785 703325 := bbase (se 3 (by rfl) ⟨131873, by rfl⟩ : syracuseStep 703325 = 263747) (by norm_num)
theorem B703349 : Blo 467785 703349 := bbase (se 5 (by rfl) ⟨32969, by rfl⟩ : syracuseStep 703349 = 65939) (by norm_num)
theorem B1588085 : Blo 467785 1588085 := bbase (se 5 (by rfl) ⟨74441, by rfl⟩ : syracuseStep 1588085 = 148883) (by norm_num)
theorem B703373 : Blo 467785 703373 := bbase (se 3 (by rfl) ⟨131882, by rfl⟩ : syracuseStep 703373 = 263765) (by norm_num)
theorem B703397 : Blo 467785 703397 := bbase (se 4 (by rfl) ⟨65943, by rfl⟩ : syracuseStep 703397 = 131887) (by norm_num)
theorem B703421 : Blo 467785 703421 := bbase (se 3 (by rfl) ⟨131891, by rfl⟩ : syracuseStep 703421 = 263783) (by norm_num)
theorem B703445 : Blo 467785 703445 := bbase (se 7 (by rfl) ⟨8243, by rfl⟩ : syracuseStep 703445 = 16487) (by norm_num)
theorem B703469 : Blo 467785 703469 := bbase (se 3 (by rfl) ⟨131900, by rfl⟩ : syracuseStep 703469 = 263801) (by norm_num)
theorem B703493 : Blo 467785 703493 := bbase (se 4 (by rfl) ⟨65952, by rfl⟩ : syracuseStep 703493 = 131905) (by norm_num)
theorem B703517 : Blo 467785 703517 := bbase (se 3 (by rfl) ⟨131909, by rfl⟩ : syracuseStep 703517 = 263819) (by norm_num)
theorem B703541 : Blo 467785 703541 := bbase (se 5 (by rfl) ⟨32978, by rfl⟩ : syracuseStep 703541 = 65957) (by norm_num)
theorem B703565 : Blo 467785 703565 := bbase (se 3 (by rfl) ⟨131918, by rfl⟩ : syracuseStep 703565 = 263837) (by norm_num)
theorem B2866261 : Blo 467785 2866261 := bbase (se 8 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 2866261 = 33589) (by norm_num)
theorem B703589 : Blo 467785 703589 := bbase (se 4 (by rfl) ⟨65961, by rfl⟩ : syracuseStep 703589 = 131923) (by norm_num)
theorem B2374757 : Blo 467785 2374757 := bbase (se 4 (by rfl) ⟨222633, by rfl⟩ : syracuseStep 2374757 = 445267) (by norm_num)
theorem B703613 : Blo 467785 703613 := bbase (se 3 (by rfl) ⟨131927, by rfl⟩ : syracuseStep 703613 = 263855) (by norm_num)
theorem B703637 : Blo 467785 703637 := bbase (se 6 (by rfl) ⟨16491, by rfl⟩ : syracuseStep 703637 = 32983) (by norm_num)
theorem B703661 : Blo 467785 703661 := bbase (se 3 (by rfl) ⟨131936, by rfl⟩ : syracuseStep 703661 = 263873) (by norm_num)
theorem B703685 : Blo 467785 703685 := bbase (se 4 (by rfl) ⟨65970, by rfl⟩ : syracuseStep 703685 = 131941) (by norm_num)
theorem B703709 : Blo 467785 703709 := bbase (se 3 (by rfl) ⟨131945, by rfl⟩ : syracuseStep 703709 = 263891) (by norm_num)
theorem B572653 : Blo 467785 572653 := bbase (se 3 (by rfl) ⟨107372, by rfl⟩ : syracuseStep 572653 = 214745) (by norm_num)
theorem B703733 : Blo 467785 703733 := bbase (se 5 (by rfl) ⟨32987, by rfl⟩ : syracuseStep 703733 = 65975) (by norm_num)
theorem B1129717 : Blo 467785 1129717 := bbase (se 5 (by rfl) ⟨52955, by rfl⟩ : syracuseStep 1129717 = 105911) (by norm_num)
theorem B703757 : Blo 467785 703757 := bbase (se 3 (by rfl) ⟨131954, by rfl⟩ : syracuseStep 703757 = 263909) (by norm_num)
theorem B703781 : Blo 467785 703781 := bbase (se 4 (by rfl) ⟨65979, by rfl⟩ : syracuseStep 703781 = 131959) (by norm_num)
theorem B1588517 : Blo 467785 1588517 := bbase (se 4 (by rfl) ⟨148923, by rfl⟩ : syracuseStep 1588517 = 297847) (by norm_num)
theorem B2997557 : Blo 467785 2997557 := bbase (se 5 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 2997557 = 281021) (by norm_num)
theorem B703805 : Blo 467785 703805 := bbase (se 3 (by rfl) ⟨131963, by rfl⟩ : syracuseStep 703805 = 263927) (by norm_num)
theorem B703829 : Blo 467785 703829 := bbase (se 11 (by rfl) ⟨515, by rfl⟩ : syracuseStep 703829 = 1031) (by norm_num)
theorem B703853 : Blo 467785 703853 := bbase (se 3 (by rfl) ⟨131972, by rfl⟩ : syracuseStep 703853 = 263945) (by norm_num)
theorem B703877 : Blo 467785 703877 := bbase (se 4 (by rfl) ⟨65988, by rfl⟩ : syracuseStep 703877 = 131977) (by norm_num)
theorem B703901 : Blo 467785 703901 := bbase (se 3 (by rfl) ⟨131981, by rfl⟩ : syracuseStep 703901 = 263963) (by norm_num)
theorem B703925 : Blo 467785 703925 := bbase (se 5 (by rfl) ⟨32996, by rfl⟩ : syracuseStep 703925 = 65993) (by norm_num)
theorem B703949 : Blo 467785 703949 := bbase (se 3 (by rfl) ⟨131990, by rfl⟩ : syracuseStep 703949 = 263981) (by norm_num)
theorem B474589 : Blo 467785 474589 := bbase (se 3 (by rfl) ⟨88985, by rfl⟩ : syracuseStep 474589 = 177971) (by norm_num)
theorem B703973 : Blo 467785 703973 := bbase (se 4 (by rfl) ⟨65997, by rfl⟩ : syracuseStep 703973 = 131995) (by norm_num)
theorem B703997 : Blo 467785 703997 := bbase (se 3 (by rfl) ⟨131999, by rfl⟩ : syracuseStep 703997 = 263999) (by norm_num)
theorem B474641 : Blo 467785 474641 := bbase (se 2 (by rfl) ⟨177990, by rfl⟩ : syracuseStep 474641 = 355981) (by norm_num)
theorem B704021 : Blo 467785 704021 := bbase (se 6 (by rfl) ⟨16500, by rfl⟩ : syracuseStep 704021 = 33001) (by norm_num)
theorem B802333 : Blo 467785 802333 := bbase (se 3 (by rfl) ⟨150437, by rfl⟩ : syracuseStep 802333 = 300875) (by norm_num)
theorem B704045 : Blo 467785 704045 := bbase (se 3 (by rfl) ⟨132008, by rfl⟩ : syracuseStep 704045 = 264017) (by norm_num)
theorem B704069 : Blo 467785 704069 := bbase (se 4 (by rfl) ⟨66006, by rfl⟩ : syracuseStep 704069 = 132013) (by norm_num)
theorem B704093 : Blo 467785 704093 := bbase (se 3 (by rfl) ⟨132017, by rfl⟩ : syracuseStep 704093 = 264035) (by norm_num)
theorem B671341 : Blo 467785 671341 := bbase (se 3 (by rfl) ⟨125876, by rfl⟩ : syracuseStep 671341 = 251753) (by norm_num)
theorem B704117 : Blo 467785 704117 := bbase (se 5 (by rfl) ⟨33005, by rfl⟩ : syracuseStep 704117 = 66011) (by norm_num)
theorem B704141 : Blo 467785 704141 := bbase (se 3 (by rfl) ⟨132026, by rfl⟩ : syracuseStep 704141 = 264053) (by norm_num)
theorem B704165 : Blo 467785 704165 := bbase (se 4 (by rfl) ⟨66015, by rfl⟩ : syracuseStep 704165 = 132031) (by norm_num)
theorem B704189 : Blo 467785 704189 := bbase (se 3 (by rfl) ⟨132035, by rfl⟩ : syracuseStep 704189 = 264071) (by norm_num)
theorem B704213 : Blo 467785 704213 := bbase (se 7 (by rfl) ⟨8252, by rfl⟩ : syracuseStep 704213 = 16505) (by norm_num)
theorem B1588949 : Blo 467785 1588949 := bbase (se 7 (by rfl) ⟨18620, by rfl⟩ : syracuseStep 1588949 = 37241) (by norm_num)
theorem B704237 : Blo 467785 704237 := bbase (se 3 (by rfl) ⟨132044, by rfl⟩ : syracuseStep 704237 = 264089) (by norm_num)
theorem B704261 : Blo 467785 704261 := bbase (se 4 (by rfl) ⟨66024, by rfl⟩ : syracuseStep 704261 = 132049) (by norm_num)
theorem B704285 : Blo 467785 704285 := bbase (se 3 (by rfl) ⟨132053, by rfl⟩ : syracuseStep 704285 = 264107) (by norm_num)
theorem B704309 : Blo 467785 704309 := bbase (se 5 (by rfl) ⟨33014, by rfl⟩ : syracuseStep 704309 = 66029) (by norm_num)
theorem B704333 : Blo 467785 704333 := bbase (se 3 (by rfl) ⟨132062, by rfl⟩ : syracuseStep 704333 = 264125) (by norm_num)
theorem B1785685 : Blo 467785 1785685 := bbase (se 9 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 1785685 = 10463) (by norm_num)
theorem B704357 : Blo 467785 704357 := bbase (se 4 (by rfl) ⟨66033, by rfl⟩ : syracuseStep 704357 = 132067) (by norm_num)
theorem B704381 : Blo 467785 704381 := bbase (se 3 (by rfl) ⟨132071, by rfl⟩ : syracuseStep 704381 = 264143) (by norm_num)
theorem B704405 : Blo 467785 704405 := bbase (se 6 (by rfl) ⟨16509, by rfl⟩ : syracuseStep 704405 = 33019) (by norm_num)
theorem B704429 : Blo 467785 704429 := bbase (se 3 (by rfl) ⟨132080, by rfl⟩ : syracuseStep 704429 = 264161) (by norm_num)
theorem B1130429 : Blo 467785 1130429 := bbase (se 3 (by rfl) ⟨211955, by rfl⟩ : syracuseStep 1130429 = 423911) (by norm_num)
theorem B704453 : Blo 467785 704453 := bbase (se 4 (by rfl) ⟨66042, by rfl⟩ : syracuseStep 704453 = 132085) (by norm_num)
theorem B704477 : Blo 467785 704477 := bbase (se 3 (by rfl) ⟨132089, by rfl⟩ : syracuseStep 704477 = 264179) (by norm_num)
theorem B573409 : Blo 467785 573409 := bbase (se 2 (by rfl) ⟨215028, by rfl⟩ : syracuseStep 573409 = 430057) (by norm_num)
theorem B704501 : Blo 467785 704501 := bbase (se 5 (by rfl) ⟨33023, by rfl⟩ : syracuseStep 704501 = 66047) (by norm_num)
theorem B507917 : Blo 467785 507917 := bbase (se 3 (by rfl) ⟨95234, by rfl⟩ : syracuseStep 507917 = 190469) (by norm_num)
theorem B704525 : Blo 467785 704525 := bbase (se 3 (by rfl) ⟨132098, by rfl⟩ : syracuseStep 704525 = 264197) (by norm_num)
theorem B704549 : Blo 467785 704549 := bbase (se 4 (by rfl) ⟨66051, by rfl⟩ : syracuseStep 704549 = 132103) (by norm_num)
theorem B704573 : Blo 467785 704573 := bbase (se 3 (by rfl) ⟨132107, by rfl⟩ : syracuseStep 704573 = 264215) (by norm_num)
theorem B704597 : Blo 467785 704597 := bbase (se 8 (by rfl) ⟨4128, by rfl⟩ : syracuseStep 704597 = 8257) (by norm_num)
theorem B704621 : Blo 467785 704621 := bbase (se 3 (by rfl) ⟨132116, by rfl⟩ : syracuseStep 704621 = 264233) (by norm_num)
theorem B704645 : Blo 467785 704645 := bbase (se 4 (by rfl) ⟨66060, by rfl⟩ : syracuseStep 704645 = 132121) (by norm_num)
theorem B1785989 : Blo 467785 1785989 := bbase (se 4 (by rfl) ⟨167436, by rfl⟩ : syracuseStep 1785989 = 334873) (by norm_num)
theorem B1589381 : Blo 467785 1589381 := bbase (se 4 (by rfl) ⟨149004, by rfl⟩ : syracuseStep 1589381 = 298009) (by norm_num)
theorem B704669 : Blo 467785 704669 := bbase (se 3 (by rfl) ⟨132125, by rfl⟩ : syracuseStep 704669 = 264251) (by norm_num)
theorem B704693 : Blo 467785 704693 := bbase (se 5 (by rfl) ⟨33032, by rfl⟩ : syracuseStep 704693 = 66065) (by norm_num)
theorem B704717 : Blo 467785 704717 := bbase (se 3 (by rfl) ⟨132134, by rfl⟩ : syracuseStep 704717 = 264269) (by norm_num)
theorem B704741 : Blo 467785 704741 := bbase (se 4 (by rfl) ⟨66069, by rfl⟩ : syracuseStep 704741 = 132139) (by norm_num)
theorem B704765 : Blo 467785 704765 := bbase (se 3 (by rfl) ⟨132143, by rfl⟩ : syracuseStep 704765 = 264287) (by norm_num)
theorem B704789 : Blo 467785 704789 := bbase (se 6 (by rfl) ⟨16518, by rfl⟩ : syracuseStep 704789 = 33037) (by norm_num)
theorem B704813 : Blo 467785 704813 := bbase (se 3 (by rfl) ⟨132152, by rfl⟩ : syracuseStep 704813 = 264305) (by norm_num)
theorem B1130813 : Blo 467785 1130813 := bbase (se 3 (by rfl) ⟨212027, by rfl⟩ : syracuseStep 1130813 = 424055) (by norm_num)
theorem B704837 : Blo 467785 704837 := bbase (se 4 (by rfl) ⟨66078, by rfl⟩ : syracuseStep 704837 = 132157) (by norm_num)
theorem B475465 : Blo 467785 475465 := bbase (se 2 (by rfl) ⟨178299, by rfl⟩ : syracuseStep 475465 = 356599) (by norm_num)
theorem B704861 : Blo 467785 704861 := bbase (se 3 (by rfl) ⟨132161, by rfl⟩ : syracuseStep 704861 = 264323) (by norm_num)
theorem B2670965 : Blo 467785 2670965 := bbase (se 5 (by rfl) ⟨125201, by rfl⟩ : syracuseStep 2670965 = 250403) (by norm_num)
theorem B2376053 : Blo 467785 2376053 := bbase (se 5 (by rfl) ⟨111377, by rfl⟩ : syracuseStep 2376053 = 222755) (by norm_num)
theorem B704885 : Blo 467785 704885 := bbase (se 5 (by rfl) ⟨33041, by rfl⟩ : syracuseStep 704885 = 66083) (by norm_num)
theorem B704909 : Blo 467785 704909 := bbase (se 3 (by rfl) ⟨132170, by rfl⟩ : syracuseStep 704909 = 264341) (by norm_num)
theorem B475553 : Blo 467785 475553 := bbase (se 2 (by rfl) ⟨178332, by rfl⟩ : syracuseStep 475553 = 356665) (by norm_num)
theorem B704933 : Blo 467785 704933 := bbase (se 4 (by rfl) ⟨66087, by rfl⟩ : syracuseStep 704933 = 132175) (by norm_num)
theorem B999869 : Blo 467785 999869 := bbase (se 3 (by rfl) ⟨187475, by rfl⟩ : syracuseStep 999869 = 374951) (by norm_num)
theorem B704957 : Blo 467785 704957 := bbase (se 3 (by rfl) ⟨132179, by rfl⟩ : syracuseStep 704957 = 264359) (by norm_num)
theorem B704981 : Blo 467785 704981 := bbase (se 7 (by rfl) ⟨8261, by rfl⟩ : syracuseStep 704981 = 16523) (by norm_num)
theorem B705005 : Blo 467785 705005 := bbase (se 3 (by rfl) ⟨132188, by rfl⟩ : syracuseStep 705005 = 264377) (by norm_num)
theorem B705029 : Blo 467785 705029 := bbase (se 4 (by rfl) ⟨66096, by rfl⟩ : syracuseStep 705029 = 132193) (by norm_num)
theorem B705053 : Blo 467785 705053 := bbase (se 3 (by rfl) ⟨132197, by rfl⟩ : syracuseStep 705053 = 264395) (by norm_num)
theorem B541225 : Blo 467785 541225 := bbase (se 2 (by rfl) ⟨202959, by rfl⟩ : syracuseStep 541225 = 405919) (by norm_num)
theorem B705077 : Blo 467785 705077 := bbase (se 5 (by rfl) ⟨33050, by rfl⟩ : syracuseStep 705077 = 66101) (by norm_num)
theorem B1589813 : Blo 467785 1589813 := bbase (se 5 (by rfl) ⟨74522, by rfl⟩ : syracuseStep 1589813 = 149045) (by norm_num)
theorem B705101 : Blo 467785 705101 := bbase (se 3 (by rfl) ⟨132206, by rfl⟩ : syracuseStep 705101 = 264413) (by norm_num)
theorem B1131101 : Blo 467785 1131101 := bbase (se 3 (by rfl) ⟨212081, by rfl⟩ : syracuseStep 1131101 = 424163) (by norm_num)
theorem B705125 : Blo 467785 705125 := bbase (se 4 (by rfl) ⟨66105, by rfl⟩ : syracuseStep 705125 = 132211) (by norm_num)
theorem B705149 : Blo 467785 705149 := bbase (se 3 (by rfl) ⟨132215, by rfl⟩ : syracuseStep 705149 = 264431) (by norm_num)
theorem B705173 : Blo 467785 705173 := bbase (se 6 (by rfl) ⟨16527, by rfl⟩ : syracuseStep 705173 = 33055) (by norm_num)
theorem B541345 : Blo 467785 541345 := bbase (se 2 (by rfl) ⟨203004, by rfl⟩ : syracuseStep 541345 = 406009) (by norm_num)
theorem B1000109 : Blo 467785 1000109 := bbase (se 3 (by rfl) ⟨187520, by rfl⟩ : syracuseStep 1000109 = 375041) (by norm_num)
theorem B705197 : Blo 467785 705197 := bbase (se 3 (by rfl) ⟨132224, by rfl⟩ : syracuseStep 705197 = 264449) (by norm_num)
theorem B705221 : Blo 467785 705221 := bbase (se 4 (by rfl) ⟨66114, by rfl⟩ : syracuseStep 705221 = 132229) (by norm_num)
theorem B705245 : Blo 467785 705245 := bbase (se 3 (by rfl) ⟨132233, by rfl⟩ : syracuseStep 705245 = 264467) (by norm_num)
theorem B705269 : Blo 467785 705269 := bbase (se 5 (by rfl) ⟨33059, by rfl⟩ : syracuseStep 705269 = 66119) (by norm_num)
theorem B705293 : Blo 467785 705293 := bbase (se 3 (by rfl) ⟨132242, by rfl⟩ : syracuseStep 705293 = 264485) (by norm_num)
theorem B705317 : Blo 467785 705317 := bbase (se 4 (by rfl) ⟨66123, by rfl⟩ : syracuseStep 705317 = 132247) (by norm_num)
theorem B705341 : Blo 467785 705341 := bbase (se 3 (by rfl) ⟨132251, by rfl⟩ : syracuseStep 705341 = 264503) (by norm_num)
theorem B705365 : Blo 467785 705365 := bbase (se 9 (by rfl) ⟨2066, by rfl⟩ : syracuseStep 705365 = 4133) (by norm_num)
theorem B705389 : Blo 467785 705389 := bbase (se 3 (by rfl) ⟨132260, by rfl⟩ : syracuseStep 705389 = 264521) (by norm_num)
theorem B705413 : Blo 467785 705413 := bbase (se 4 (by rfl) ⟨66132, by rfl⟩ : syracuseStep 705413 = 132265) (by norm_num)
theorem B705437 : Blo 467785 705437 := bbase (se 3 (by rfl) ⟨132269, by rfl⟩ : syracuseStep 705437 = 264539) (by norm_num)
theorem B705461 : Blo 467785 705461 := bbase (se 5 (by rfl) ⟨33068, by rfl⟩ : syracuseStep 705461 = 66137) (by norm_num)
theorem B705485 : Blo 467785 705485 := bbase (se 3 (by rfl) ⟨132278, by rfl⟩ : syracuseStep 705485 = 264557) (by norm_num)
theorem B705509 : Blo 467785 705509 := bbase (se 4 (by rfl) ⟨66141, by rfl⟩ : syracuseStep 705509 = 132283) (by norm_num)
theorem B1590245 : Blo 467785 1590245 := bbase (se 4 (by rfl) ⟨149085, by rfl⟩ : syracuseStep 1590245 = 298171) (by norm_num)
theorem B705533 : Blo 467785 705533 := bbase (se 3 (by rfl) ⟨132287, by rfl⟩ : syracuseStep 705533 = 264575) (by norm_num)
theorem B705557 : Blo 467785 705557 := bbase (se 6 (by rfl) ⟨16536, by rfl⟩ : syracuseStep 705557 = 33073) (by norm_num)
theorem B705581 : Blo 467785 705581 := bbase (se 3 (by rfl) ⟨132296, by rfl⟩ : syracuseStep 705581 = 264593) (by norm_num)
theorem B705605 : Blo 467785 705605 := bbase (se 4 (by rfl) ⟨66150, by rfl⟩ : syracuseStep 705605 = 132301) (by norm_num)
theorem B705629 : Blo 467785 705629 := bbase (se 3 (by rfl) ⟨132305, by rfl⟩ : syracuseStep 705629 = 264611) (by norm_num)
theorem B705653 : Blo 467785 705653 := bbase (se 5 (by rfl) ⟨33077, by rfl⟩ : syracuseStep 705653 = 66155) (by norm_num)
theorem B705677 : Blo 467785 705677 := bbase (se 3 (by rfl) ⟨132314, by rfl⟩ : syracuseStep 705677 = 264629) (by norm_num)
theorem B1000613 : Blo 467785 1000613 := bbase (se 4 (by rfl) ⟨93807, by rfl⟩ : syracuseStep 1000613 = 187615) (by norm_num)
theorem B705701 : Blo 467785 705701 := bbase (se 4 (by rfl) ⟨66159, by rfl⟩ : syracuseStep 705701 = 132319) (by norm_num)
theorem B1000621 : Blo 467785 1000621 := bbase (se 3 (by rfl) ⟨187616, by rfl⟩ : syracuseStep 1000621 = 375233) (by norm_num)
theorem B705725 : Blo 467785 705725 := bbase (se 3 (by rfl) ⟨132323, by rfl⟩ : syracuseStep 705725 = 264647) (by norm_num)
theorem B705749 : Blo 467785 705749 := bbase (se 7 (by rfl) ⟨8270, by rfl⟩ : syracuseStep 705749 = 16541) (by norm_num)
theorem B705773 : Blo 467785 705773 := bbase (se 3 (by rfl) ⟨132332, by rfl⟩ : syracuseStep 705773 = 264665) (by norm_num)
theorem B705797 : Blo 467785 705797 := bbase (se 4 (by rfl) ⟨66168, by rfl⟩ : syracuseStep 705797 = 132337) (by norm_num)
theorem B705821 : Blo 467785 705821 := bbase (se 3 (by rfl) ⟨132341, by rfl⟩ : syracuseStep 705821 = 264683) (by norm_num)
theorem B705845 : Blo 467785 705845 := bbase (se 5 (by rfl) ⟨33086, by rfl⟩ : syracuseStep 705845 = 66173) (by norm_num)
theorem B705869 : Blo 467785 705869 := bbase (se 3 (by rfl) ⟨132350, by rfl⟩ : syracuseStep 705869 = 264701) (by norm_num)
theorem B705893 : Blo 467785 705893 := bbase (se 4 (by rfl) ⟨66177, by rfl⟩ : syracuseStep 705893 = 132355) (by norm_num)
theorem B705917 : Blo 467785 705917 := bbase (se 3 (by rfl) ⟨132359, by rfl⟩ : syracuseStep 705917 = 264719) (by norm_num)
theorem B705941 : Blo 467785 705941 := bbase (se 6 (by rfl) ⟨16545, by rfl⟩ : syracuseStep 705941 = 33091) (by norm_num)
theorem B1590677 : Blo 467785 1590677 := bbase (se 6 (by rfl) ⟨37281, by rfl⟩ : syracuseStep 1590677 = 74563) (by norm_num)
theorem B705965 : Blo 467785 705965 := bbase (se 3 (by rfl) ⟨132368, by rfl⟩ : syracuseStep 705965 = 264737) (by norm_num)
theorem B705989 : Blo 467785 705989 := bbase (se 4 (by rfl) ⟨66186, by rfl⟩ : syracuseStep 705989 = 132373) (by norm_num)
theorem B706013 : Blo 467785 706013 := bbase (se 3 (by rfl) ⟨132377, by rfl⟩ : syracuseStep 706013 = 264755) (by norm_num)
theorem B476641 : Blo 467785 476641 := bbase (se 2 (by rfl) ⟨178740, by rfl⟩ : syracuseStep 476641 = 357481) (by norm_num)
theorem B706037 : Blo 467785 706037 := bbase (se 5 (by rfl) ⟨33095, by rfl⟩ : syracuseStep 706037 = 66191) (by norm_num)
theorem B706061 : Blo 467785 706061 := bbase (se 3 (by rfl) ⟨132386, by rfl⟩ : syracuseStep 706061 = 264773) (by norm_num)
theorem B2672149 : Blo 467785 2672149 := bbase (se 6 (by rfl) ⟨62628, by rfl⟩ : syracuseStep 2672149 = 125257) (by norm_num)
theorem B706085 : Blo 467785 706085 := bbase (se 4 (by rfl) ⟨66195, by rfl⟩ : syracuseStep 706085 = 132391) (by norm_num)
theorem B476717 : Blo 467785 476717 := bbase (se 3 (by rfl) ⟨89384, by rfl⟩ : syracuseStep 476717 = 178769) (by norm_num)
theorem B706109 : Blo 467785 706109 := bbase (se 3 (by rfl) ⟨132395, by rfl⟩ : syracuseStep 706109 = 264791) (by norm_num)
theorem B706133 : Blo 467785 706133 := bbase (se 8 (by rfl) ⟨4137, by rfl⟩ : syracuseStep 706133 = 8275) (by norm_num)
theorem B706157 : Blo 467785 706157 := bbase (se 3 (by rfl) ⟨132404, by rfl⟩ : syracuseStep 706157 = 264809) (by norm_num)
theorem B2377349 : Blo 467785 2377349 := bbase (se 4 (by rfl) ⟨222876, by rfl⟩ : syracuseStep 2377349 = 445753) (by norm_num)
theorem B706181 : Blo 467785 706181 := bbase (se 4 (by rfl) ⟨66204, by rfl⟩ : syracuseStep 706181 = 132409) (by norm_num)
theorem B706205 : Blo 467785 706205 := bbase (se 3 (by rfl) ⟨132413, by rfl⟩ : syracuseStep 706205 = 264827) (by norm_num)
theorem B706229 : Blo 467785 706229 := bbase (se 5 (by rfl) ⟨33104, by rfl⟩ : syracuseStep 706229 = 66209) (by norm_num)
theorem B706253 : Blo 467785 706253 := bbase (se 3 (by rfl) ⟨132422, by rfl⟩ : syracuseStep 706253 = 264845) (by norm_num)
theorem B706277 : Blo 467785 706277 := bbase (se 4 (by rfl) ⟨66213, by rfl⟩ : syracuseStep 706277 = 132427) (by norm_num)
theorem B706301 : Blo 467785 706301 := bbase (se 3 (by rfl) ⟨132431, by rfl⟩ : syracuseStep 706301 = 264863) (by norm_num)
theorem B706325 : Blo 467785 706325 := bbase (se 6 (by rfl) ⟨16554, by rfl⟩ : syracuseStep 706325 = 33109) (by norm_num)
theorem B706349 : Blo 467785 706349 := bbase (se 3 (by rfl) ⟨132440, by rfl⟩ : syracuseStep 706349 = 264881) (by norm_num)
theorem B476977 : Blo 467785 476977 := bbase (se 2 (by rfl) ⟨178866, by rfl⟩ : syracuseStep 476977 = 357733) (by norm_num)
theorem B706373 : Blo 467785 706373 := bbase (se 4 (by rfl) ⟨66222, by rfl⟩ : syracuseStep 706373 = 132445) (by norm_num)
theorem B1591109 : Blo 467785 1591109 := bbase (se 4 (by rfl) ⟨149166, by rfl⟩ : syracuseStep 1591109 = 298333) (by norm_num)
theorem B706397 : Blo 467785 706397 := bbase (se 3 (by rfl) ⟨132449, by rfl⟩ : syracuseStep 706397 = 264899) (by norm_num)
theorem B706421 : Blo 467785 706421 := bbase (se 5 (by rfl) ⟨33113, by rfl⟩ : syracuseStep 706421 = 66227) (by norm_num)
theorem B706445 : Blo 467785 706445 := bbase (se 3 (by rfl) ⟨132458, by rfl⟩ : syracuseStep 706445 = 264917) (by norm_num)
theorem B706469 : Blo 467785 706469 := bbase (se 4 (by rfl) ⟨66231, by rfl⟩ : syracuseStep 706469 = 132463) (by norm_num)
theorem B706493 : Blo 467785 706493 := bbase (se 3 (by rfl) ⟨132467, by rfl⟩ : syracuseStep 706493 = 264935) (by norm_num)
theorem B706517 : Blo 467785 706517 := bbase (se 7 (by rfl) ⟨8279, by rfl⟩ : syracuseStep 706517 = 16559) (by norm_num)
theorem B706541 : Blo 467785 706541 := bbase (se 3 (by rfl) ⟨132476, by rfl⟩ : syracuseStep 706541 = 264953) (by norm_num)
theorem B706565 : Blo 467785 706565 := bbase (se 4 (by rfl) ⟨66240, by rfl⟩ : syracuseStep 706565 = 132481) (by norm_num)
theorem B706589 : Blo 467785 706589 := bbase (se 3 (by rfl) ⟨132485, by rfl⟩ : syracuseStep 706589 = 264971) (by norm_num)
theorem B706613 : Blo 467785 706613 := bbase (se 5 (by rfl) ⟨33122, by rfl⟩ : syracuseStep 706613 = 66245) (by norm_num)
theorem B706637 : Blo 467785 706637 := bbase (se 3 (by rfl) ⟨132494, by rfl⟩ : syracuseStep 706637 = 264989) (by norm_num)
theorem B12863573 : Blo 467785 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B706661 : Blo 467785 706661 := bbase (se 4 (by rfl) ⟨66249, by rfl⟩ : syracuseStep 706661 = 132499) (by norm_num)
theorem B706685 : Blo 467785 706685 := bbase (se 3 (by rfl) ⟨132503, by rfl⟩ : syracuseStep 706685 = 265007) (by norm_num)
theorem B706709 : Blo 467785 706709 := bbase (se 6 (by rfl) ⟨16563, by rfl⟩ : syracuseStep 706709 = 33127) (by norm_num)
theorem B706733 : Blo 467785 706733 := bbase (se 3 (by rfl) ⟨132512, by rfl⟩ : syracuseStep 706733 = 265025) (by norm_num)
theorem B1788101 : Blo 467785 1788101 := bbase (se 4 (by rfl) ⟨167634, by rfl⟩ : syracuseStep 1788101 = 335269) (by norm_num)
theorem B706757 : Blo 467785 706757 := bbase (se 4 (by rfl) ⟨66258, by rfl⟩ : syracuseStep 706757 = 132517) (by norm_num)
theorem B706781 : Blo 467785 706781 := bbase (se 3 (by rfl) ⟨132521, by rfl⟩ : syracuseStep 706781 = 265043) (by norm_num)
theorem B706805 : Blo 467785 706805 := bbase (se 5 (by rfl) ⟨33131, by rfl⟩ : syracuseStep 706805 = 66263) (by norm_num)
theorem B1591541 : Blo 467785 1591541 := bbase (se 5 (by rfl) ⟨74603, by rfl⟩ : syracuseStep 1591541 = 149207) (by norm_num)
theorem B706829 : Blo 467785 706829 := bbase (se 3 (by rfl) ⟨132530, by rfl⟩ : syracuseStep 706829 = 265061) (by norm_num)
theorem B1001749 : Blo 467785 1001749 := bbase (se 6 (by rfl) ⟨23478, by rfl⟩ : syracuseStep 1001749 = 46957) (by norm_num)
theorem B706853 : Blo 467785 706853 := bbase (se 4 (by rfl) ⟨66267, by rfl⟩ : syracuseStep 706853 = 132535) (by norm_num)
theorem B903485 : Blo 467785 903485 := bbase (se 3 (by rfl) ⟨169403, by rfl⟩ : syracuseStep 903485 = 338807) (by norm_num)
theorem B706877 : Blo 467785 706877 := bbase (se 3 (by rfl) ⟨132539, by rfl⟩ : syracuseStep 706877 = 265079) (by norm_num)
theorem B706901 : Blo 467785 706901 := bbase (se 10 (by rfl) ⟨1035, by rfl⟩ : syracuseStep 706901 = 2071) (by norm_num)
theorem B706925 : Blo 467785 706925 := bbase (se 3 (by rfl) ⟨132548, by rfl⟩ : syracuseStep 706925 = 265097) (by norm_num)
theorem B706949 : Blo 467785 706949 := bbase (se 4 (by rfl) ⟨66276, by rfl⟩ : syracuseStep 706949 = 132553) (by norm_num)
theorem B706973 : Blo 467785 706973 := bbase (se 3 (by rfl) ⟨132557, by rfl⟩ : syracuseStep 706973 = 265115) (by norm_num)
theorem B706997 : Blo 467785 706997 := bbase (se 5 (by rfl) ⟨33140, by rfl⟩ : syracuseStep 706997 = 66281) (by norm_num)
theorem B707021 : Blo 467785 707021 := bbase (se 3 (by rfl) ⟨132566, by rfl⟩ : syracuseStep 707021 = 265133) (by norm_num)
theorem B1788389 : Blo 467785 1788389 := bbase (se 4 (by rfl) ⟨167661, by rfl⟩ : syracuseStep 1788389 = 335323) (by norm_num)
theorem B707045 : Blo 467785 707045 := bbase (se 4 (by rfl) ⟨66285, by rfl⟩ : syracuseStep 707045 = 132571) (by norm_num)
theorem B707069 : Blo 467785 707069 := bbase (se 3 (by rfl) ⟨132575, by rfl⟩ : syracuseStep 707069 = 265151) (by norm_num)
theorem B707093 : Blo 467785 707093 := bbase (se 6 (by rfl) ⟨16572, by rfl⟩ : syracuseStep 707093 = 33145) (by norm_num)
theorem B707117 : Blo 467785 707117 := bbase (se 3 (by rfl) ⟨132584, by rfl⟩ : syracuseStep 707117 = 265169) (by norm_num)
theorem B707141 : Blo 467785 707141 := bbase (se 4 (by rfl) ⟨66294, by rfl⟩ : syracuseStep 707141 = 132589) (by norm_num)
theorem B707165 : Blo 467785 707165 := bbase (se 3 (by rfl) ⟨132593, by rfl⟩ : syracuseStep 707165 = 265187) (by norm_num)
theorem B3558005 : Blo 467785 3558005 := bbase (se 5 (by rfl) ⟨166781, by rfl⟩ : syracuseStep 3558005 = 333563) (by norm_num)
theorem B707189 : Blo 467785 707189 := bbase (se 5 (by rfl) ⟨33149, by rfl⟩ : syracuseStep 707189 = 66299) (by norm_num)
theorem B1002125 : Blo 467785 1002125 := bbase (se 3 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 1002125 = 375797) (by norm_num)
theorem B707213 : Blo 467785 707213 := bbase (se 3 (by rfl) ⟨132602, by rfl⟩ : syracuseStep 707213 = 265205) (by norm_num)
theorem B707237 : Blo 467785 707237 := bbase (se 4 (by rfl) ⟨66303, by rfl⟩ : syracuseStep 707237 = 132607) (by norm_num)
theorem B1591973 : Blo 467785 1591973 := bbase (se 4 (by rfl) ⟨149247, by rfl⟩ : syracuseStep 1591973 = 298495) (by norm_num)
theorem B707261 : Blo 467785 707261 := bbase (se 3 (by rfl) ⟨132611, by rfl⟩ : syracuseStep 707261 = 265223) (by norm_num)
theorem B707285 : Blo 467785 707285 := bbase (se 7 (by rfl) ⟨8288, by rfl⟩ : syracuseStep 707285 = 16577) (by norm_num)
theorem B707309 : Blo 467785 707309 := bbase (se 3 (by rfl) ⟨132620, by rfl⟩ : syracuseStep 707309 = 265241) (by norm_num)
theorem B707333 : Blo 467785 707333 := bbase (se 4 (by rfl) ⟨66312, by rfl⟩ : syracuseStep 707333 = 132625) (by norm_num)
theorem B707357 : Blo 467785 707357 := bbase (se 3 (by rfl) ⟨132629, by rfl⟩ : syracuseStep 707357 = 265259) (by norm_num)
theorem B707381 : Blo 467785 707381 := bbase (se 5 (by rfl) ⟨33158, by rfl⟩ : syracuseStep 707381 = 66317) (by norm_num)
theorem B1526597 : Blo 467785 1526597 := bbase (se 4 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 1526597 = 286237) (by norm_num)
theorem B707405 : Blo 467785 707405 := bbase (se 3 (by rfl) ⟨132638, by rfl⟩ : syracuseStep 707405 = 265277) (by norm_num)
theorem B707429 : Blo 467785 707429 := bbase (se 4 (by rfl) ⟨66321, by rfl⟩ : syracuseStep 707429 = 132643) (by norm_num)
theorem B707453 : Blo 467785 707453 := bbase (se 3 (by rfl) ⟨132647, by rfl⟩ : syracuseStep 707453 = 265295) (by norm_num)
theorem B2378645 : Blo 467785 2378645 := bbase (se 6 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 2378645 = 111499) (by norm_num)
theorem B707477 : Blo 467785 707477 := bbase (se 6 (by rfl) ⟨16581, by rfl⟩ : syracuseStep 707477 = 33163) (by norm_num)
theorem B707501 : Blo 467785 707501 := bbase (se 3 (by rfl) ⟨132656, by rfl⟩ : syracuseStep 707501 = 265313) (by norm_num)
theorem B707525 : Blo 467785 707525 := bbase (se 4 (by rfl) ⟨66330, by rfl⟩ : syracuseStep 707525 = 132661) (by norm_num)
theorem B2411477 : Blo 467785 2411477 := bbase (se 7 (by rfl) ⟨28259, by rfl⟩ : syracuseStep 2411477 = 56519) (by norm_num)
theorem B8604629 : Blo 467785 8604629 := bbase (se 7 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 8604629 = 201671) (by norm_num)
theorem B707549 : Blo 467785 707549 := bbase (se 3 (by rfl) ⟨132665, by rfl⟩ : syracuseStep 707549 = 265331) (by norm_num)
theorem B707573 : Blo 467785 707573 := bbase (se 5 (by rfl) ⟨33167, by rfl⟩ : syracuseStep 707573 = 66335) (by norm_num)
theorem B707597 : Blo 467785 707597 := bbase (se 3 (by rfl) ⟨132674, by rfl⟩ : syracuseStep 707597 = 265349) (by norm_num)
theorem B707621 : Blo 467785 707621 := bbase (se 4 (by rfl) ⟨66339, by rfl⟩ : syracuseStep 707621 = 132679) (by norm_num)
theorem B707645 : Blo 467785 707645 := bbase (se 3 (by rfl) ⟨132683, by rfl⟩ : syracuseStep 707645 = 265367) (by norm_num)
theorem B707669 : Blo 467785 707669 := bbase (se 8 (by rfl) ⟨4146, by rfl⟩ : syracuseStep 707669 = 8293) (by norm_num)
theorem B1690885 : Blo 467785 1690885 := bbase (se 4 (by rfl) ⟨158520, by rfl⟩ : syracuseStep 1690885 = 317041) (by norm_num)
theorem B2674133 : Blo 467785 2674133 := bbase (se 7 (by rfl) ⟨31337, by rfl⟩ : syracuseStep 2674133 = 62675) (by norm_num)
theorem B904717 : Blo 467785 904717 := bbase (se 3 (by rfl) ⟨169634, by rfl⟩ : syracuseStep 904717 = 339269) (by norm_num)
theorem B1691189 : Blo 467785 1691189 := bbase (se 5 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 1691189 = 158549) (by norm_num)
theorem B9064021 : Blo 467785 9064021 := bbase (se 8 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 9064021 = 106219) (by norm_num)
theorem B1789573 : Blo 467785 1789573 := bbase (se 4 (by rfl) ⟨167772, by rfl⟩ : syracuseStep 1789573 = 335545) (by norm_num)
theorem B1068821 : Blo 467785 1068821 := bbase (se 6 (by rfl) ⟨25050, by rfl⟩ : syracuseStep 1068821 = 50101) (by norm_num)
theorem B1396565 : Blo 467785 1396565 := bbase (se 9 (by rfl) ⟨4091, by rfl⟩ : syracuseStep 1396565 = 8183) (by norm_num)
theorem B2576245 : Blo 467785 2576245 := bbase (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) (by norm_num)
theorem B1789877 : Blo 467785 1789877 := bbase (se 5 (by rfl) ⟨83900, by rfl⟩ : syracuseStep 1789877 = 167801) (by norm_num)
theorem B806869 : Blo 467785 806869 := bbase (se 7 (by rfl) ⟨9455, by rfl⟩ : syracuseStep 806869 = 18911) (by norm_num)
theorem B8572949 : Blo 467785 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B2379941 : Blo 467785 2379941 := bbase (se 4 (by rfl) ⟨223119, by rfl⟩ : syracuseStep 2379941 = 446239) (by norm_num)
theorem B1626325 : Blo 467785 1626325 := bbase (se 7 (by rfl) ⟨19058, by rfl⟩ : syracuseStep 1626325 = 38117) (by norm_num)
theorem B1003765 : Blo 467785 1003765 := bbase (se 5 (by rfl) ⟨47051, by rfl⟩ : syracuseStep 1003765 = 94103) (by norm_num)
theorem B5067029 : Blo 467785 5067029 := bbase (se 6 (by rfl) ⟨118758, by rfl⟩ : syracuseStep 5067029 = 237517) (by norm_num)
theorem B708949 : Blo 467785 708949 := bbase (se 10 (by rfl) ⟨1038, by rfl⟩ : syracuseStep 708949 = 2077) (by norm_num)
theorem B545341 : Blo 467785 545341 := bbase (se 3 (by rfl) ⟨102251, by rfl⟩ : syracuseStep 545341 = 204503) (by norm_num)
theorem B5100245 : Blo 467785 5100245 := bbase (se 7 (by rfl) ⟨59768, by rfl⟩ : syracuseStep 5100245 = 119537) (by norm_num)
theorem B1430261 : Blo 467785 1430261 := bbase (se 5 (by rfl) ⟨67043, by rfl⟩ : syracuseStep 1430261 = 134087) (by norm_num)
theorem B676669 : Blo 467785 676669 := bbase (se 3 (by rfl) ⟨126875, by rfl⟩ : syracuseStep 676669 = 253751) (by norm_num)
theorem B1004653 : Blo 467785 1004653 := bbase (se 3 (by rfl) ⟨188372, by rfl⟩ : syracuseStep 1004653 = 376745) (by norm_num)
theorem B2315621 : Blo 467785 2315621 := bbase (se 4 (by rfl) ⟨217089, by rfl⟩ : syracuseStep 2315621 = 434179) (by norm_num)
theorem B513389 : Blo 467785 513389 := bbase (se 3 (by rfl) ⟨96260, by rfl⟩ : syracuseStep 513389 = 192521) (by norm_num)
theorem B2381237 : Blo 467785 2381237 := bbase (se 5 (by rfl) ⟨111620, by rfl⟩ : syracuseStep 2381237 = 223241) (by norm_num)
theorem B1005149 : Blo 467785 1005149 := bbase (se 3 (by rfl) ⟨188465, by rfl⟩ : syracuseStep 1005149 = 376931) (by norm_num)
theorem B2676341 : Blo 467785 2676341 := bbase (se 5 (by rfl) ⟨125453, by rfl⟩ : syracuseStep 2676341 = 250907) (by norm_num)
theorem B1070725 : Blo 467785 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B2250629 : Blo 467785 2250629 := bbase (se 4 (by rfl) ⟨210996, by rfl⟩ : syracuseStep 2250629 = 421993) (by norm_num)
theorem B1333205 : Blo 467785 1333205 := bbase (se 7 (by rfl) ⟨15623, by rfl⟩ : syracuseStep 1333205 = 31247) (by norm_num)
theorem B2414549 : Blo 467785 2414549 := bbase (se 7 (by rfl) ⟨28295, by rfl⟩ : syracuseStep 2414549 = 56591) (by norm_num)
theorem B1006013 : Blo 467785 1006013 := bbase (se 3 (by rfl) ⟨188627, by rfl⟩ : syracuseStep 1006013 = 377255) (by norm_num)
theorem B1006157 : Blo 467785 1006157 := bbase (se 3 (by rfl) ⟨188654, by rfl⟩ : syracuseStep 1006157 = 377309) (by norm_num)
theorem B2382533 : Blo 467785 2382533 := bbase (se 4 (by rfl) ⟨223362, by rfl⟩ : syracuseStep 2382533 = 446725) (by norm_num)
theorem B1694533 : Blo 467785 1694533 := bbase (se 4 (by rfl) ⟨158862, by rfl⟩ : syracuseStep 1694533 = 317725) (by norm_num)
theorem B1268597 : Blo 467785 1268597 := bbase (se 5 (by rfl) ⟨59465, by rfl⟩ : syracuseStep 1268597 = 118931) (by norm_num)
theorem B1334389 : Blo 467785 1334389 := bbase (se 5 (by rfl) ⟨62549, by rfl⟩ : syracuseStep 1334389 = 125099) (by norm_num)
theorem B2415781 : Blo 467785 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B1334549 : Blo 467785 1334549 := bbase (se 6 (by rfl) ⟨31278, by rfl⟩ : syracuseStep 1334549 = 62557) (by norm_num)
theorem B1006901 : Blo 467785 1006901 := bbase (se 5 (by rfl) ⟨47198, by rfl⟩ : syracuseStep 1006901 = 94397) (by norm_num)
theorem B1072549 : Blo 467785 1072549 := bbase (se 4 (by rfl) ⟨100551, by rfl⟩ : syracuseStep 1072549 = 201103) (by norm_num)
theorem B2252245 : Blo 467785 2252245 := bbase (se 7 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 2252245 = 52787) (by norm_num)
theorem B1334789 : Blo 467785 1334789 := bbase (se 4 (by rfl) ⟨125136, by rfl⟩ : syracuseStep 1334789 = 250273) (by norm_num)
theorem B843461 : Blo 467785 843461 := bbase (se 4 (by rfl) ⟨79074, by rfl⟩ : syracuseStep 843461 = 158149) (by norm_num)
theorem B1334981 : Blo 467785 1334981 := bbase (se 4 (by rfl) ⟨125154, by rfl⟩ : syracuseStep 1334981 = 250309) (by norm_num)
theorem B2383829 : Blo 467785 2383829 := bbase (se 7 (by rfl) ⟨27935, by rfl⟩ : syracuseStep 2383829 = 55871) (by norm_num)
theorem B1925141 : Blo 467785 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B5726485 : Blo 467785 5726485 := bbase (se 6 (by rfl) ⟨134214, by rfl⟩ : syracuseStep 5726485 = 268429) (by norm_num)
theorem B1433909 : Blo 467785 1433909 := bbase (se 5 (by rfl) ⟨67214, by rfl⟩ : syracuseStep 1433909 = 134429) (by norm_num)
theorem B680293 : Blo 467785 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B1335973 : Blo 467785 1335973 := bbase (se 4 (by rfl) ⟨125247, by rfl⟩ : syracuseStep 1335973 = 250495) (by norm_num)
theorem B1696565 : Blo 467785 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B1270997 : Blo 467785 1270997 := bbase (se 7 (by rfl) ⟨14894, by rfl⟩ : syracuseStep 1270997 = 29789) (by norm_num)
theorem B2385125 : Blo 467785 2385125 := bbase (se 4 (by rfl) ⟨223605, by rfl⟩ : syracuseStep 2385125 = 447211) (by norm_num)
theorem B4515061 : Blo 467785 4515061 := bbase (se 5 (by rfl) ⟨211643, by rfl⟩ : syracuseStep 4515061 = 423287) (by norm_num)
theorem B30532949 : Blo 467785 30532949 := bbase (se 12 (by rfl) ⟨11181, by rfl⟩ : syracuseStep 30532949 = 22363) (by norm_num)
theorem B714109 : Blo 467785 714109 := bbase (se 3 (by rfl) ⟨133895, by rfl⟩ : syracuseStep 714109 = 267791) (by norm_num)
theorem B1500677 : Blo 467785 1500677 := bbase (se 4 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 1500677 = 281377) (by norm_num)
theorem B3008117 : Blo 467785 3008117 := bbase (se 5 (by rfl) ⟨141005, by rfl⟩ : syracuseStep 3008117 = 282011) (by norm_num)
theorem B1697429 : Blo 467785 1697429 := bbase (se 6 (by rfl) ⟨39783, by rfl⟩ : syracuseStep 1697429 = 79567) (by norm_num)
theorem B1337077 : Blo 467785 1337077 := bbase (se 5 (by rfl) ⟨62675, by rfl⟩ : syracuseStep 1337077 = 125351) (by norm_num)
theorem B1206373 : Blo 467785 1206373 := bbase (se 4 (by rfl) ⟨113097, by rfl⟩ : syracuseStep 1206373 = 226195) (by norm_num)
theorem B3565781 : Blo 467785 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B714997 : Blo 467785 714997 := bbase (se 5 (by rfl) ⟨33515, by rfl⟩ : syracuseStep 714997 = 67031) (by norm_num)
theorem B1501573 : Blo 467785 1501573 := bbase (se 4 (by rfl) ⟨140772, by rfl⟩ : syracuseStep 1501573 = 281545) (by norm_num)
theorem B846229 : Blo 467785 846229 := bbase (se 6 (by rfl) ⟨19833, by rfl⟩ : syracuseStep 846229 = 39667) (by norm_num)
theorem B2386421 : Blo 467785 2386421 := bbase (se 5 (by rfl) ⟨111863, by rfl⟩ : syracuseStep 2386421 = 223727) (by norm_num)
theorem B1272629 : Blo 467785 1272629 := bbase (se 5 (by rfl) ⟨59654, by rfl⟩ : syracuseStep 1272629 = 119309) (by norm_num)
theorem B4025173 : Blo 467785 4025173 := bbase (se 9 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 4025173 = 23585) (by norm_num)
theorem B3206101 : Blo 467785 3206101 := bbase (se 7 (by rfl) ⟨37571, by rfl⟩ : syracuseStep 3206101 = 75143) (by norm_num)
theorem B846869 : Blo 467785 846869 := bbase (se 6 (by rfl) ⟨19848, by rfl⟩ : syracuseStep 846869 = 39697) (by norm_num)
theorem B1338581 : Blo 467785 1338581 := bbase (se 7 (by rfl) ⟨15686, by rfl⟩ : syracuseStep 1338581 = 31373) (by norm_num)
theorem B3042613 : Blo 467785 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B2387717 : Blo 467785 2387717 := bbase (se 4 (by rfl) ⟨223848, by rfl⟩ : syracuseStep 2387717 = 447697) (by norm_num)
theorem B749333 : Blo 467785 749333 := bbase (se 6 (by rfl) ⟨17562, by rfl⟩ : syracuseStep 749333 = 35125) (by norm_num)
theorem B1273765 : Blo 467785 1273765 := bbase (se 4 (by rfl) ⟨119415, by rfl⟩ : syracuseStep 1273765 = 238831) (by norm_num)
theorem B5369813 : Blo 467785 5369813 := bbase (se 7 (by rfl) ⟨62927, by rfl⟩ : syracuseStep 5369813 = 125855) (by norm_num)
theorem B1929205 : Blo 467785 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B1274069 : Blo 467785 1274069 := bbase (se 7 (by rfl) ⟨14930, by rfl⟩ : syracuseStep 1274069 = 29861) (by norm_num)
theorem B717029 : Blo 467785 717029 := bbase (se 4 (by rfl) ⟨67221, by rfl⟩ : syracuseStep 717029 = 134443) (by norm_num)
theorem B749845 : Blo 467785 749845 := bbase (se 6 (by rfl) ⟨17574, by rfl⟩ : syracuseStep 749845 = 35149) (by norm_num)
theorem B848189 : Blo 467785 848189 := bbase (se 3 (by rfl) ⟨159035, by rfl⟩ : syracuseStep 848189 = 318071) (by norm_num)
theorem B3600949 : Blo 467785 3600949 := bbase (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) (by norm_num)
theorem B1340165 : Blo 467785 1340165 := bbase (se 4 (by rfl) ⟨125640, by rfl⟩ : syracuseStep 1340165 = 251281) (by norm_num)
theorem B4027157 : Blo 467785 4027157 := bbase (se 6 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 4027157 = 188773) (by norm_num)
theorem B750389 : Blo 467785 750389 := bbase (se 5 (by rfl) ⟨35174, by rfl⟩ : syracuseStep 750389 = 70349) (by norm_num)
theorem B848917 : Blo 467785 848917 := bbase (se 6 (by rfl) ⟨19896, by rfl⟩ : syracuseStep 848917 = 39793) (by norm_num)
theorem B1274933 : Blo 467785 1274933 := bbase (se 5 (by rfl) ⟨59762, by rfl⟩ : syracuseStep 1274933 = 119525) (by norm_num)
theorem B521321 : Blo 467785 521321 := bbase (se 2 (by rfl) ⟨195495, by rfl⟩ : syracuseStep 521321 = 390991) (by norm_num)
theorem B3798197 : Blo 467785 3798197 := bbase (se 5 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 3798197 = 356081) (by norm_num)
theorem B1504469 : Blo 467785 1504469 := bbase (se 7 (by rfl) ⟨17630, by rfl⟩ : syracuseStep 1504469 = 35261) (by norm_num)
theorem B849133 : Blo 467785 849133 := bbase (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) (by norm_num)
theorem B750941 : Blo 467785 750941 := bbase (se 3 (by rfl) ⟨140801, by rfl⟩ : syracuseStep 750941 = 281603) (by norm_num)
theorem B750973 : Blo 467785 750973 := bbase (se 3 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 750973 = 281615) (by norm_num)
theorem B1340837 : Blo 467785 1340837 := bbase (se 4 (by rfl) ⟨125703, by rfl⟩ : syracuseStep 1340837 = 251407) (by norm_num)
theorem B1209821 : Blo 467785 1209821 := bbase (se 3 (by rfl) ⟨226841, by rfl⟩ : syracuseStep 1209821 = 453683) (by norm_num)
theorem B2258549 : Blo 467785 2258549 := bbase (se 5 (by rfl) ⟨105869, by rfl⟩ : syracuseStep 2258549 = 211739) (by norm_num)
theorem B849637 : Blo 467785 849637 := bbase (se 4 (by rfl) ⟨79653, by rfl⟩ : syracuseStep 849637 = 159307) (by norm_num)
theorem B1341269 : Blo 467785 1341269 := bbase (se 9 (by rfl) ⟨3929, by rfl⟩ : syracuseStep 1341269 = 7859) (by norm_num)
theorem B1898437 : Blo 467785 1898437 := bbase (se 4 (by rfl) ⟨177978, by rfl⟩ : syracuseStep 1898437 = 355957) (by norm_num)
theorem B9140309 : Blo 467785 9140309 := bbase (se 8 (by rfl) ⟨53556, by rfl⟩ : syracuseStep 9140309 = 107113) (by norm_num)
theorem B751901 : Blo 467785 751901 := bbase (se 3 (by rfl) ⟨140981, by rfl⟩ : syracuseStep 751901 = 281963) (by norm_num)
theorem B1603925 : Blo 467785 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B1342021 : Blo 467785 1342021 := bbase (se 4 (by rfl) ⟨125814, by rfl⟩ : syracuseStep 1342021 = 251629) (by norm_num)
theorem B8583893 : Blo 467785 8583893 := bbase (se 7 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 8583893 = 201185) (by norm_num)
theorem B1801061 : Blo 467785 1801061 := bbase (se 4 (by rfl) ⟨168849, by rfl⟩ : syracuseStep 1801061 = 337699) (by norm_num)
theorem B752581 : Blo 467785 752581 := bbase (se 4 (by rfl) ⟨70554, by rfl⟩ : syracuseStep 752581 = 141109) (by norm_num)
theorem B752645 : Blo 467785 752645 := bbase (se 4 (by rfl) ⟨70560, by rfl⟩ : syracuseStep 752645 = 141121) (by norm_num)
theorem B2686229 : Blo 467785 2686229 := bbase (se 6 (by rfl) ⟨62958, by rfl⟩ : syracuseStep 2686229 = 125917) (by norm_num)
theorem B1506725 : Blo 467785 1506725 := bbase (se 4 (by rfl) ⟨141255, by rfl⟩ : syracuseStep 1506725 = 282511) (by norm_num)
theorem B3014165 : Blo 467785 3014165 := bbase (se 6 (by rfl) ⟨70644, by rfl⟩ : syracuseStep 3014165 = 141289) (by norm_num)
theorem B753875 : Blo 467785 753875 := bstep (se 1 (by rfl) ⟨565406, by rfl⟩ : syracuseStep 753875 = 1130813) B1130813
theorem B7635313 : Blo 467785 7635313 := bstep (se 2 (by rfl) ⟨2863242, by rfl⟩ : syracuseStep 7635313 = 5726485) B5726485
theorem B754067 : Blo 467785 754067 := bstep (se 1 (by rfl) ⟨565550, by rfl⟩ : syracuseStep 754067 = 1131101) B1131101
theorem B3015089 : Blo 467785 3015089 := bstep (se 2 (by rfl) ⟨1130658, by rfl⟩ : syracuseStep 3015089 = 2261317) B2261317
theorem B5439941 : Blo 467785 5439941 := bstep (se 4 (by rfl) ⟨509994, by rfl⟩ : syracuseStep 5439941 = 1019989) B1019989
theorem B2261837 : Blo 467785 2261837 := bstep (se 3 (by rfl) ⟨424094, by rfl⟩ : syracuseStep 2261837 = 848189) B848189
theorem B754849 : Blo 467785 754849 := bstep (se 2 (by rfl) ⟨283068, by rfl⟩ : syracuseStep 754849 = 566137) B566137
theorem B6423907 : Blo 467785 6423907 := bstep (se 1 (by rfl) ⟨4817930, by rfl⟩ : syracuseStep 6423907 = 9635861) B9635861
theorem B1901987 : Blo 467785 1901987 := bstep (se 1 (by rfl) ⟨1426490, by rfl⟩ : syracuseStep 1901987 = 2852981) B2852981
theorem B3999203 : Blo 467785 3999203 := bstep (se 1 (by rfl) ⟨2999402, by rfl⟩ : syracuseStep 3999203 = 5998805) B5998805
theorem B1509133 : Blo 467785 1509133 := bstep (se 3 (by rfl) ⟨282962, by rfl⟩ : syracuseStep 1509133 = 565925) B565925
theorem B952145 : Blo 467785 952145 := bstep (se 2 (by rfl) ⟨357054, by rfl⟩ : syracuseStep 952145 = 714109) B714109
theorem B1017731 : Blo 467785 1017731 := bstep (se 1 (by rfl) ⟨763298, by rfl⟩ : syracuseStep 1017731 = 1526597) B1526597
theorem B1607651 : Blo 467785 1607651 := bstep (se 1 (by rfl) ⟨1205738, by rfl⟩ : syracuseStep 1607651 = 2411477) B2411477
theorem B5736419 : Blo 467785 5736419 := bstep (se 1 (by rfl) ⟨4302314, by rfl⟩ : syracuseStep 5736419 = 8604629) B8604629
theorem B526387 : Blo 467785 526387 := bstep (se 1 (by rfl) ⟨394790, by rfl⟩ : syracuseStep 526387 = 789581) B789581
theorem B2001037 : Blo 467785 2001037 := bstep (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) B750389
theorem B4524173 : Blo 467785 4524173 := bstep (se 3 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 4524173 = 1696565) B1696565
theorem B526531 : Blo 467785 526531 := bstep (se 1 (by rfl) ⟨394898, by rfl⟩ : syracuseStep 526531 = 789797) B789797
theorem B592211 : Blo 467785 592211 := bstep (se 1 (by rfl) ⟨444158, by rfl⟩ : syracuseStep 592211 = 888317) B888317
theorem B526675 : Blo 467785 526675 := bstep (se 1 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 526675 = 790013) B790013
theorem B526819 : Blo 467785 526819 := bstep (se 1 (by rfl) ⟨395114, by rfl⟩ : syracuseStep 526819 = 790229) B790229
theorem B526963 : Blo 467785 526963 := bstep (se 1 (by rfl) ⟨395222, by rfl⟩ : syracuseStep 526963 = 790445) B790445
theorem B527107 : Blo 467785 527107 := bstep (se 1 (by rfl) ⟨395330, by rfl⟩ : syracuseStep 527107 = 790661) B790661
theorem B1608497 : Blo 467785 1608497 := bstep (se 2 (by rfl) ⟨603186, by rfl⟩ : syracuseStep 1608497 = 1206373) B1206373
theorem B3378019 : Blo 467785 3378019 := bstep (se 1 (by rfl) ⟨2533514, by rfl⟩ : syracuseStep 3378019 = 5067029) B5067029
theorem B2886533 : Blo 467785 2886533 := bstep (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) B541225
theorem B527251 : Blo 467785 527251 := bstep (se 1 (by rfl) ⟨395438, by rfl⟩ : syracuseStep 527251 = 790877) B790877
theorem B789473 : Blo 467785 789473 := bstep (se 2 (by rfl) ⟨296052, by rfl⟩ : syracuseStep 789473 = 592105) B592105
theorem B592915 : Blo 467785 592915 := bstep (se 1 (by rfl) ⟨444686, by rfl⟩ : syracuseStep 592915 = 889373) B889373
theorem B527395 : Blo 467785 527395 := bstep (se 1 (by rfl) ⟨395546, by rfl⟩ : syracuseStep 527395 = 791093) B791093
theorem B789601 : Blo 467785 789601 := bstep (se 2 (by rfl) ⟨296100, by rfl⟩ : syracuseStep 789601 = 592201) B592201
theorem B593011 : Blo 467785 593011 := bstep (se 1 (by rfl) ⟨444758, by rfl⟩ : syracuseStep 593011 = 889517) B889517
theorem B789635 : Blo 467785 789635 := bstep (se 1 (by rfl) ⟨592226, by rfl⟩ : syracuseStep 789635 = 1184453) B1184453
theorem B953507 : Blo 467785 953507 := bstep (se 1 (by rfl) ⟨715130, by rfl⟩ : syracuseStep 953507 = 1430261) B1430261
theorem B2002097 : Blo 467785 2002097 := bstep (se 2 (by rfl) ⟨750786, by rfl⟩ : syracuseStep 2002097 = 1501573) B1501573
theorem B527539 : Blo 467785 527539 := bstep (se 1 (by rfl) ⟨395654, by rfl⟩ : syracuseStep 527539 = 791309) B791309
theorem B1510595 : Blo 467785 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B789763 : Blo 467785 789763 := bstep (se 1 (by rfl) ⟨592322, by rfl⟩ : syracuseStep 789763 = 1184645) B1184645
theorem B527683 : Blo 467785 527683 := bstep (se 1 (by rfl) ⟨395762, by rfl⟩ : syracuseStep 527683 = 791525) B791525
theorem B789905 : Blo 467785 789905 := bstep (se 2 (by rfl) ⟨296214, by rfl⟩ : syracuseStep 789905 = 592429) B592429
theorem B888241 : Blo 467785 888241 := bstep (se 2 (by rfl) ⟨333090, by rfl⟩ : syracuseStep 888241 = 666181) B666181
theorem B16289221 : Blo 467785 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B527827 : Blo 467785 527827 := bstep (se 1 (by rfl) ⟨395870, by rfl⟩ : syracuseStep 527827 = 791741) B791741
theorem B790033 : Blo 467785 790033 := bstep (se 2 (by rfl) ⟨296262, by rfl⟩ : syracuseStep 790033 = 592525) B592525
theorem B790067 : Blo 467785 790067 := bstep (se 1 (by rfl) ⟨592550, by rfl⟩ : syracuseStep 790067 = 1185101) B1185101
theorem B1543747 : Blo 467785 1543747 := bstep (se 1 (by rfl) ⟨1157810, by rfl⟩ : syracuseStep 1543747 = 2315621) B2315621
theorem B888401 : Blo 467785 888401 := bstep (se 2 (by rfl) ⟨333150, by rfl⟩ : syracuseStep 888401 = 666301) B666301
theorem B593507 : Blo 467785 593507 := bstep (se 1 (by rfl) ⟨445130, by rfl⟩ : syracuseStep 593507 = 890261) B890261
theorem B527971 : Blo 467785 527971 := bstep (se 1 (by rfl) ⟨395978, by rfl⟩ : syracuseStep 527971 = 791957) B791957
theorem B790195 : Blo 467785 790195 := bstep (se 1 (by rfl) ⟨592646, by rfl⟩ : syracuseStep 790195 = 1185293) B1185293
theorem B5738165 : Blo 467785 5738165 := bstep (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) B537953
theorem B528115 : Blo 467785 528115 := bstep (se 1 (by rfl) ⟨396086, by rfl⟩ : syracuseStep 528115 = 792173) B792173
theorem B790337 : Blo 467785 790337 := bstep (se 2 (by rfl) ⟨296376, by rfl⟩ : syracuseStep 790337 = 592753) B592753
theorem B528259 : Blo 467785 528259 := bstep (se 1 (by rfl) ⟨396194, by rfl⟩ : syracuseStep 528259 = 792389) B792389
theorem B790465 : Blo 467785 790465 := bstep (se 2 (by rfl) ⟨296424, by rfl⟩ : syracuseStep 790465 = 592849) B592849
theorem B888803 : Blo 467785 888803 := bstep (se 1 (by rfl) ⟨666602, by rfl⟩ : syracuseStep 888803 = 1333205) B1333205
theorem B790499 : Blo 467785 790499 := bstep (se 1 (by rfl) ⟨592874, by rfl⟩ : syracuseStep 790499 = 1185749) B1185749
theorem B1609699 : Blo 467785 1609699 := bstep (se 1 (by rfl) ⟨1207274, by rfl⟩ : syracuseStep 1609699 = 2414549) B2414549
theorem B1052657 : Blo 467785 1052657 := bstep (se 2 (by rfl) ⟨394746, by rfl⟩ : syracuseStep 1052657 = 789493) B789493
theorem B1052675 : Blo 467785 1052675 := bstep (se 1 (by rfl) ⟨789506, by rfl⟩ : syracuseStep 1052675 = 1579013) B1579013
theorem B528403 : Blo 467785 528403 := bstep (se 1 (by rfl) ⟨396302, by rfl⟩ : syracuseStep 528403 = 792605) B792605
theorem B790627 : Blo 467785 790627 := bstep (se 1 (by rfl) ⟨592970, by rfl⟩ : syracuseStep 790627 = 1185941) B1185941
theorem B528547 : Blo 467785 528547 := bstep (se 1 (by rfl) ⟨396410, by rfl⟩ : syracuseStep 528547 = 792821) B792821
theorem B790769 : Blo 467785 790769 := bstep (se 2 (by rfl) ⟨296538, by rfl⟩ : syracuseStep 790769 = 593077) B593077
theorem B1052945 : Blo 467785 1052945 := bstep (se 2 (by rfl) ⟨394854, by rfl⟩ : syracuseStep 1052945 = 789709) B789709
theorem B1052963 : Blo 467785 1052963 := bstep (se 1 (by rfl) ⟨789722, by rfl⟩ : syracuseStep 1052963 = 1579445) B1579445
theorem B594211 : Blo 467785 594211 := bstep (se 1 (by rfl) ⟨445658, by rfl⟩ : syracuseStep 594211 = 891317) B891317
theorem B528691 : Blo 467785 528691 := bstep (se 1 (by rfl) ⟨396518, by rfl⟩ : syracuseStep 528691 = 793037) B793037
theorem B790897 : Blo 467785 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B594307 : Blo 467785 594307 := bstep (se 1 (by rfl) ⟨445730, by rfl⟩ : syracuseStep 594307 = 891461) B891461
theorem B790931 : Blo 467785 790931 := bstep (se 1 (by rfl) ⟨593198, by rfl⟩ : syracuseStep 790931 = 1186397) B1186397
theorem B528835 : Blo 467785 528835 := bstep (se 1 (by rfl) ⟨396626, by rfl⟩ : syracuseStep 528835 = 793253) B793253
theorem B791059 : Blo 467785 791059 := bstep (se 1 (by rfl) ⟨593294, by rfl⟩ : syracuseStep 791059 = 1186589) B1186589
theorem B1184291 : Blo 467785 1184291 := bstep (se 1 (by rfl) ⟨888218, by rfl⟩ : syracuseStep 1184291 = 1776437) B1776437
theorem B1053233 : Blo 467785 1053233 := bstep (se 2 (by rfl) ⟨394962, by rfl⟩ : syracuseStep 1053233 = 789925) B789925
theorem B1053251 : Blo 467785 1053251 := bstep (se 1 (by rfl) ⟨789938, by rfl⟩ : syracuseStep 1053251 = 1579877) B1579877
theorem B528979 : Blo 467785 528979 := bstep (se 1 (by rfl) ⟨396734, by rfl⟩ : syracuseStep 528979 = 793469) B793469
theorem B791201 : Blo 467785 791201 := bstep (se 2 (by rfl) ⟨296700, by rfl⟩ : syracuseStep 791201 = 593401) B593401
theorem B1184483 : Blo 467785 1184483 := bstep (se 1 (by rfl) ⟨888362, by rfl⟩ : syracuseStep 1184483 = 1776725) B1776725
theorem B529123 : Blo 467785 529123 := bstep (se 1 (by rfl) ⟨396842, by rfl⟩ : syracuseStep 529123 = 793685) B793685
theorem B2757361 : Blo 467785 2757361 := bstep (se 2 (by rfl) ⟨1034010, by rfl⟩ : syracuseStep 2757361 = 2068021) B2068021
theorem B791329 : Blo 467785 791329 := bstep (se 2 (by rfl) ⟨296748, by rfl⟩ : syracuseStep 791329 = 593497) B593497
theorem B791363 : Blo 467785 791363 := bstep (se 1 (by rfl) ⟨593522, by rfl⟩ : syracuseStep 791363 = 1187045) B1187045
theorem B1053521 : Blo 467785 1053521 := bstep (se 2 (by rfl) ⟨395070, by rfl⟩ : syracuseStep 1053521 = 790141) B790141
theorem B1053539 : Blo 467785 1053539 := bstep (se 1 (by rfl) ⟨790154, by rfl⟩ : syracuseStep 1053539 = 1580309) B1580309
theorem B889699 : Blo 467785 889699 := bstep (se 1 (by rfl) ⟨667274, by rfl⟩ : syracuseStep 889699 = 1334549) B1334549
theorem B594803 : Blo 467785 594803 := bstep (se 1 (by rfl) ⟨446102, by rfl⟩ : syracuseStep 594803 = 892205) B892205
theorem B529267 : Blo 467785 529267 := bstep (se 1 (by rfl) ⟨396950, by rfl⟩ : syracuseStep 529267 = 793901) B793901
theorem B791491 : Blo 467785 791491 := bstep (se 1 (by rfl) ⟨593618, by rfl⟩ : syracuseStep 791491 = 1187237) B1187237
theorem B889859 : Blo 467785 889859 := bstep (se 1 (by rfl) ⟨667394, by rfl⟩ : syracuseStep 889859 = 1334789) B1334789
theorem B529411 : Blo 467785 529411 := bstep (se 1 (by rfl) ⟨397058, by rfl⟩ : syracuseStep 529411 = 794117) B794117
theorem B791633 : Blo 467785 791633 := bstep (se 2 (by rfl) ⟨296862, by rfl⟩ : syracuseStep 791633 = 593725) B593725
theorem B1053809 : Blo 467785 1053809 := bstep (se 2 (by rfl) ⟨395178, by rfl⟩ : syracuseStep 1053809 = 790357) B790357
theorem B562307 : Blo 467785 562307 := bstep (se 1 (by rfl) ⟨421730, by rfl⟩ : syracuseStep 562307 = 843461) B843461
theorem B1053827 : Blo 467785 1053827 := bstep (se 1 (by rfl) ⟨790370, by rfl⟩ : syracuseStep 1053827 = 1580741) B1580741
theorem B529555 : Blo 467785 529555 := bstep (se 1 (by rfl) ⟨397166, by rfl⟩ : syracuseStep 529555 = 794333) B794333
theorem B5346485 : Blo 467785 5346485 := bstep (se 5 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 5346485 = 501233) B501233
theorem B791761 : Blo 467785 791761 := bstep (se 2 (by rfl) ⟨296910, by rfl⟩ : syracuseStep 791761 = 593821) B593821
theorem B791795 : Blo 467785 791795 := bstep (se 1 (by rfl) ⟨593846, by rfl⟩ : syracuseStep 791795 = 1187693) B1187693
theorem B529699 : Blo 467785 529699 := bstep (se 1 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 529699 = 794549) B794549
theorem B791923 : Blo 467785 791923 := bstep (se 1 (by rfl) ⟨593942, by rfl⟩ : syracuseStep 791923 = 1187885) B1187885
theorem B3020165 : Blo 467785 3020165 := bstep (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) B566281
theorem B1054097 : Blo 467785 1054097 := bstep (se 2 (by rfl) ⟨395286, by rfl⟩ : syracuseStep 1054097 = 790573) B790573
theorem B1054115 : Blo 467785 1054115 := bstep (se 1 (by rfl) ⟨790586, by rfl⟩ : syracuseStep 1054115 = 1581173) B1581173
theorem B529843 : Blo 467785 529843 := bstep (se 1 (by rfl) ⟨397382, by rfl⟩ : syracuseStep 529843 = 794765) B794765
theorem B792065 : Blo 467785 792065 := bstep (se 2 (by rfl) ⟨297024, by rfl⟩ : syracuseStep 792065 = 594049) B594049
theorem B595507 : Blo 467785 595507 := bstep (se 1 (by rfl) ⟨446630, by rfl⟩ : syracuseStep 595507 = 893261) B893261
theorem B529987 : Blo 467785 529987 := bstep (se 1 (by rfl) ⟨397490, by rfl⟩ : syracuseStep 529987 = 794981) B794981
theorem B792193 : Blo 467785 792193 := bstep (se 2 (by rfl) ⟨297072, by rfl⟩ : syracuseStep 792193 = 594145) B594145
theorem B1185425 : Blo 467785 1185425 := bstep (se 2 (by rfl) ⟨444534, by rfl⟩ : syracuseStep 1185425 = 889069) B889069
theorem B595603 : Blo 467785 595603 := bstep (se 1 (by rfl) ⟨446702, by rfl⟩ : syracuseStep 595603 = 893405) B893405
theorem B792227 : Blo 467785 792227 := bstep (se 1 (by rfl) ⟨594170, by rfl⟩ : syracuseStep 792227 = 1188341) B1188341
theorem B1054385 : Blo 467785 1054385 := bstep (se 2 (by rfl) ⟨395394, by rfl⟩ : syracuseStep 1054385 = 790789) B790789
theorem B1185475 : Blo 467785 1185475 := bstep (se 1 (by rfl) ⟨889106, by rfl⟩ : syracuseStep 1185475 = 1778213) B1778213
theorem B1054403 : Blo 467785 1054403 := bstep (se 1 (by rfl) ⟨790802, by rfl⟩ : syracuseStep 1054403 = 1581605) B1581605
theorem B530131 : Blo 467785 530131 := bstep (se 1 (by rfl) ⟨397598, by rfl⟩ : syracuseStep 530131 = 795197) B795197
theorem B792355 : Blo 467785 792355 := bstep (se 1 (by rfl) ⟨594266, by rfl⟩ : syracuseStep 792355 = 1188533) B1188533
theorem B1578797 : Blo 467785 1578797 := bstep (se 3 (by rfl) ⟨296024, by rfl⟩ : syracuseStep 1578797 = 592049) B592049
theorem B5084981 : Blo 467785 5084981 := bstep (se 5 (by rfl) ⟨238358, by rfl⟩ : syracuseStep 5084981 = 476717) B476717
theorem B1185617 : Blo 467785 1185617 := bstep (se 2 (by rfl) ⟨444606, by rfl⟩ : syracuseStep 1185617 = 889213) B889213
theorem B1578851 : Blo 467785 1578851 := bstep (se 1 (by rfl) ⟨1184138, by rfl⟩ : syracuseStep 1578851 = 2368277) B2368277
theorem B530275 : Blo 467785 530275 := bstep (se 1 (by rfl) ⟨397706, by rfl⟩ : syracuseStep 530275 = 795413) B795413
theorem B792497 : Blo 467785 792497 := bstep (se 2 (by rfl) ⟨297186, by rfl⟩ : syracuseStep 792497 = 594373) B594373
theorem B1054673 : Blo 467785 1054673 := bstep (se 2 (by rfl) ⟨395502, by rfl⟩ : syracuseStep 1054673 = 791005) B791005
theorem B1054691 : Blo 467785 1054691 := bstep (se 1 (by rfl) ⟨791018, by rfl⟩ : syracuseStep 1054691 = 1582037) B1582037
theorem B530419 : Blo 467785 530419 := bstep (se 1 (by rfl) ⟨397814, by rfl⟩ : syracuseStep 530419 = 795629) B795629
theorem B890929 : Blo 467785 890929 := bstep (se 2 (by rfl) ⟨334098, by rfl⟩ : syracuseStep 890929 = 668197) B668197
theorem B792625 : Blo 467785 792625 := bstep (se 2 (by rfl) ⟨297234, by rfl⟩ : syracuseStep 792625 = 594469) B594469
theorem B2005069 : Blo 467785 2005069 := bstep (se 3 (by rfl) ⟨375950, by rfl⟩ : syracuseStep 2005069 = 751901) B751901
theorem B727121 : Blo 467785 727121 := bstep (se 2 (by rfl) ⟨272670, by rfl⟩ : syracuseStep 727121 = 545341) B545341
theorem B792659 : Blo 467785 792659 := bstep (se 1 (by rfl) ⟨594494, by rfl⟩ : syracuseStep 792659 = 1188989) B1188989
theorem B1579121 : Blo 467785 1579121 := bstep (se 2 (by rfl) ⟨592170, by rfl⟩ : syracuseStep 1579121 = 1184341) B1184341
theorem B596099 : Blo 467785 596099 := bstep (se 1 (by rfl) ⟨447074, by rfl⟩ : syracuseStep 596099 = 894149) B894149
theorem B530563 : Blo 467785 530563 := bstep (se 1 (by rfl) ⟨397922, by rfl⟩ : syracuseStep 530563 = 795845) B795845
theorem B1448099 : Blo 467785 1448099 := bstep (se 1 (by rfl) ⟨1086074, by rfl⟩ : syracuseStep 1448099 = 2172149) B2172149
theorem B792787 : Blo 467785 792787 := bstep (se 1 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 792787 = 1189181) B1189181
theorem B20355299 : Blo 467785 20355299 := bstep (se 1 (by rfl) ⟨15266474, by rfl⟩ : syracuseStep 20355299 = 30532949) B30532949
theorem B1054961 : Blo 467785 1054961 := bstep (se 2 (by rfl) ⟨395610, by rfl⟩ : syracuseStep 1054961 = 791221) B791221
theorem B1054979 : Blo 467785 1054979 := bstep (se 1 (by rfl) ⟨791234, by rfl⟩ : syracuseStep 1054979 = 1582469) B1582469
theorem B530707 : Blo 467785 530707 := bstep (se 1 (by rfl) ⟨398030, by rfl⟩ : syracuseStep 530707 = 796061) B796061
theorem B792929 : Blo 467785 792929 := bstep (se 2 (by rfl) ⟨297348, by rfl⟩ : syracuseStep 792929 = 594697) B594697
theorem B2005411 : Blo 467785 2005411 := bstep (se 1 (by rfl) ⟨1504058, by rfl⟩ : syracuseStep 2005411 = 3008117) B3008117
theorem B793057 : Blo 467785 793057 := bstep (se 2 (by rfl) ⟨297396, by rfl⟩ : syracuseStep 793057 = 594793) B594793
theorem B858595 : Blo 467785 858595 := bstep (se 1 (by rfl) ⟨643946, by rfl⟩ : syracuseStep 858595 = 1287893) B1287893
theorem B793091 : Blo 467785 793091 := bstep (se 1 (by rfl) ⟨594818, by rfl⟩ : syracuseStep 793091 = 1189637) B1189637
theorem B1055249 : Blo 467785 1055249 := bstep (se 2 (by rfl) ⟨395718, by rfl⟩ : syracuseStep 1055249 = 791437) B791437
theorem B1055267 : Blo 467785 1055267 := bstep (se 1 (by rfl) ⟨791450, by rfl⟩ : syracuseStep 1055267 = 1582901) B1582901
theorem B4528709 : Blo 467785 4528709 := bstep (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) B849133
theorem B793219 : Blo 467785 793219 := bstep (se 1 (by rfl) ⟨594914, by rfl⟩ : syracuseStep 793219 = 1189829) B1189829
theorem B1776269 : Blo 467785 1776269 := bstep (se 3 (by rfl) ⟨333050, by rfl⟩ : syracuseStep 1776269 = 666101) B666101
theorem B1579661 : Blo 467785 1579661 := bstep (se 3 (by rfl) ⟨296186, by rfl⟩ : syracuseStep 1579661 = 592373) B592373
theorem B1579715 : Blo 467785 1579715 := bstep (se 1 (by rfl) ⟨1184786, by rfl⟩ : syracuseStep 1579715 = 2369573) B2369573
theorem B793361 : Blo 467785 793361 := bstep (se 2 (by rfl) ⟨297510, by rfl⟩ : syracuseStep 793361 = 595021) B595021
theorem B1186609 : Blo 467785 1186609 := bstep (se 2 (by rfl) ⟨444978, by rfl⟩ : syracuseStep 1186609 = 889957) B889957
theorem B1055537 : Blo 467785 1055537 := bstep (se 2 (by rfl) ⟨395826, by rfl⟩ : syracuseStep 1055537 = 791653) B791653
theorem B1055555 : Blo 467785 1055555 := bstep (se 1 (by rfl) ⟨791666, by rfl⟩ : syracuseStep 1055555 = 1583333) B1583333
theorem B596803 : Blo 467785 596803 := bstep (se 1 (by rfl) ⟨447602, by rfl⟩ : syracuseStep 596803 = 895205) B895205
theorem B793489 : Blo 467785 793489 := bstep (se 2 (by rfl) ⟨297558, by rfl⟩ : syracuseStep 793489 = 595117) B595117
theorem B596899 : Blo 467785 596899 := bstep (se 1 (by rfl) ⟨447674, by rfl⟩ : syracuseStep 596899 = 895349) B895349
theorem B793523 : Blo 467785 793523 := bstep (se 1 (by rfl) ⟨595142, by rfl⟩ : syracuseStep 793523 = 1190285) B1190285
theorem B1579985 : Blo 467785 1579985 := bstep (se 2 (by rfl) ⟨592494, by rfl⟩ : syracuseStep 1579985 = 1184989) B1184989
theorem B793651 : Blo 467785 793651 := bstep (se 1 (by rfl) ⟨595238, by rfl⟩ : syracuseStep 793651 = 1190477) B1190477
theorem B1186883 : Blo 467785 1186883 := bstep (se 1 (by rfl) ⟨890162, by rfl⟩ : syracuseStep 1186883 = 1780325) B1780325
theorem B1055825 : Blo 467785 1055825 := bstep (se 2 (by rfl) ⟨395934, by rfl⟩ : syracuseStep 1055825 = 791869) B791869
theorem B891985 : Blo 467785 891985 := bstep (se 2 (by rfl) ⟨334494, by rfl⟩ : syracuseStep 891985 = 668989) B668989
theorem B1055843 : Blo 467785 1055843 := bstep (se 1 (by rfl) ⟨791882, by rfl⟩ : syracuseStep 1055843 = 1583765) B1583765
theorem B793793 : Blo 467785 793793 := bstep (se 2 (by rfl) ⟨297672, by rfl⟩ : syracuseStep 793793 = 595345) B595345
theorem B1187075 : Blo 467785 1187075 := bstep (se 1 (by rfl) ⟨890306, by rfl⟩ : syracuseStep 1187075 = 1780613) B1780613
theorem B793921 : Blo 467785 793921 := bstep (se 2 (by rfl) ⟨297720, by rfl⟩ : syracuseStep 793921 = 595441) B595441
theorem B793955 : Blo 467785 793955 := bstep (se 1 (by rfl) ⟨595466, by rfl⟩ : syracuseStep 793955 = 1190933) B1190933
theorem B1056113 : Blo 467785 1056113 := bstep (se 2 (by rfl) ⟨396042, by rfl⟩ : syracuseStep 1056113 = 792085) B792085
theorem B1056131 : Blo 467785 1056131 := bstep (se 1 (by rfl) ⟨792098, by rfl⟩ : syracuseStep 1056131 = 1584197) B1584197
theorem B892387 : Blo 467785 892387 := bstep (se 1 (by rfl) ⟨669290, by rfl⟩ : syracuseStep 892387 = 1338581) B1338581
theorem B794083 : Blo 467785 794083 := bstep (se 1 (by rfl) ⟨595562, by rfl⟩ : syracuseStep 794083 = 1191125) B1191125
theorem B1580525 : Blo 467785 1580525 := bstep (se 3 (by rfl) ⟨296348, by rfl⟩ : syracuseStep 1580525 = 592697) B592697
theorem B892433 : Blo 467785 892433 := bstep (se 2 (by rfl) ⟨334662, by rfl⟩ : syracuseStep 892433 = 669325) B669325
theorem B1580579 : Blo 467785 1580579 := bstep (se 1 (by rfl) ⟨1185434, by rfl⟩ : syracuseStep 1580579 = 2370869) B2370869
theorem B794225 : Blo 467785 794225 := bstep (se 2 (by rfl) ⟨297834, by rfl⟩ : syracuseStep 794225 = 595669) B595669
theorem B1056401 : Blo 467785 1056401 := bstep (se 2 (by rfl) ⟨396150, by rfl⟩ : syracuseStep 1056401 = 792301) B792301
theorem B1056419 : Blo 467785 1056419 := bstep (se 1 (by rfl) ⟨792314, by rfl⟩ : syracuseStep 1056419 = 1584629) B1584629
theorem B794353 : Blo 467785 794353 := bstep (se 2 (by rfl) ⟨297882, by rfl⟩ : syracuseStep 794353 = 595765) B595765
theorem B794387 : Blo 467785 794387 := bstep (se 1 (by rfl) ⟨595790, by rfl⟩ : syracuseStep 794387 = 1191581) B1191581
theorem B1580849 : Blo 467785 1580849 := bstep (se 2 (by rfl) ⟨592818, by rfl⟩ : syracuseStep 1580849 = 1185637) B1185637
theorem B892721 : Blo 467785 892721 := bstep (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) B669541
theorem B499555 : Blo 467785 499555 := bstep (se 1 (by rfl) ⟨374666, by rfl⟩ : syracuseStep 499555 = 749333) B749333
theorem B3383153 : Blo 467785 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B794515 : Blo 467785 794515 := bstep (se 1 (by rfl) ⟨595886, by rfl⟩ : syracuseStep 794515 = 1191773) B1191773
theorem B2531249 : Blo 467785 2531249 := bstep (se 2 (by rfl) ⟨949218, by rfl⟩ : syracuseStep 2531249 = 1898437) B1898437
theorem B1056689 : Blo 467785 1056689 := bstep (se 2 (by rfl) ⟨396258, by rfl⟩ : syracuseStep 1056689 = 792517) B792517
theorem B1056707 : Blo 467785 1056707 := bstep (se 1 (by rfl) ⟨792530, by rfl⟩ : syracuseStep 1056707 = 1585061) B1585061
theorem B3579875 : Blo 467785 3579875 := bstep (se 1 (by rfl) ⟨2684906, by rfl⟩ : syracuseStep 3579875 = 5369813) B5369813
theorem B794657 : Blo 467785 794657 := bstep (se 2 (by rfl) ⟨297996, by rfl⟩ : syracuseStep 794657 = 595993) B595993
theorem B794785 : Blo 467785 794785 := bstep (se 2 (by rfl) ⟨298044, by rfl⟩ : syracuseStep 794785 = 596089) B596089
theorem B1188017 : Blo 467785 1188017 := bstep (se 2 (by rfl) ⟨445506, by rfl⟩ : syracuseStep 1188017 = 891013) B891013
theorem B794819 : Blo 467785 794819 := bstep (se 1 (by rfl) ⟨596114, by rfl⟩ : syracuseStep 794819 = 1192229) B1192229
theorem B1056977 : Blo 467785 1056977 := bstep (se 2 (by rfl) ⟨396366, by rfl⟩ : syracuseStep 1056977 = 792733) B792733
theorem B1188067 : Blo 467785 1188067 := bstep (se 1 (by rfl) ⟨891050, by rfl⟩ : syracuseStep 1188067 = 1782101) B1782101
theorem B1056995 : Blo 467785 1056995 := bstep (se 1 (by rfl) ⟨792746, by rfl⟩ : syracuseStep 1056995 = 1585493) B1585493
theorem B794947 : Blo 467785 794947 := bstep (se 1 (by rfl) ⟨596210, by rfl⟩ : syracuseStep 794947 = 1192421) B1192421
theorem B1581389 : Blo 467785 1581389 := bstep (se 3 (by rfl) ⟨296510, by rfl⟩ : syracuseStep 1581389 = 593021) B593021
theorem B1188209 : Blo 467785 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B1581443 : Blo 467785 1581443 := bstep (se 1 (by rfl) ⟨1186082, by rfl⟩ : syracuseStep 1581443 = 2372165) B2372165
theorem B795089 : Blo 467785 795089 := bstep (se 2 (by rfl) ⟨298158, by rfl⟩ : syracuseStep 795089 = 596317) B596317
theorem B1057265 : Blo 467785 1057265 := bstep (se 2 (by rfl) ⟨396474, by rfl⟩ : syracuseStep 1057265 = 792949) B792949
theorem B1057283 : Blo 467785 1057283 := bstep (se 1 (by rfl) ⟨792962, by rfl⟩ : syracuseStep 1057283 = 1585925) B1585925
theorem B893443 : Blo 467785 893443 := bstep (se 1 (by rfl) ⟨670082, by rfl⟩ : syracuseStep 893443 = 1340165) B1340165
theorem B795217 : Blo 467785 795217 := bstep (se 2 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 795217 = 596413) B596413
theorem B795251 : Blo 467785 795251 := bstep (se 1 (by rfl) ⟨596438, by rfl⟩ : syracuseStep 795251 = 1192877) B1192877
theorem B1581713 : Blo 467785 1581713 := bstep (se 2 (by rfl) ⟨593142, by rfl⟩ : syracuseStep 1581713 = 1186285) B1186285
theorem B1778381 : Blo 467785 1778381 := bstep (se 3 (by rfl) ⟨333446, by rfl⟩ : syracuseStep 1778381 = 666893) B666893
theorem B795379 : Blo 467785 795379 := bstep (se 1 (by rfl) ⟨596534, by rfl⟩ : syracuseStep 795379 = 1193069) B1193069
theorem B1057553 : Blo 467785 1057553 := bstep (se 2 (by rfl) ⟨396582, by rfl⟩ : syracuseStep 1057553 = 793165) B793165
theorem B2532131 : Blo 467785 2532131 := bstep (se 1 (by rfl) ⟨1899098, by rfl⟩ : syracuseStep 2532131 = 3798197) B3798197
theorem B1057571 : Blo 467785 1057571 := bstep (se 1 (by rfl) ⟨793178, by rfl⟩ : syracuseStep 1057571 = 1586357) B1586357
theorem B467795 : Blo 467785 467795 := bstep (se 1 (by rfl) ⟨350846, by rfl⟩ : syracuseStep 467795 = 701693) B701693
theorem B467811 : Blo 467785 467811 := bstep (se 1 (by rfl) ⟨350858, by rfl⟩ : syracuseStep 467811 = 701717) B701717
theorem B467827 : Blo 467785 467827 := bstep (se 1 (by rfl) ⟨350870, by rfl⟩ : syracuseStep 467827 = 701741) B701741
theorem B795521 : Blo 467785 795521 := bstep (se 2 (by rfl) ⟨298320, by rfl⟩ : syracuseStep 795521 = 596641) B596641
theorem B467843 : Blo 467785 467843 := bstep (se 1 (by rfl) ⟨350882, by rfl⟩ : syracuseStep 467843 = 701765) B701765
theorem B467859 : Blo 467785 467859 := bstep (se 1 (by rfl) ⟨350894, by rfl⟩ : syracuseStep 467859 = 701789) B701789
theorem B500627 : Blo 467785 500627 := bstep (se 1 (by rfl) ⟨375470, by rfl⟩ : syracuseStep 500627 = 750941) B750941
theorem B467875 : Blo 467785 467875 := bstep (se 1 (by rfl) ⟨350906, by rfl⟩ : syracuseStep 467875 = 701813) B701813
theorem B467891 : Blo 467785 467891 := bstep (se 1 (by rfl) ⟨350918, by rfl⟩ : syracuseStep 467891 = 701837) B701837
theorem B467907 : Blo 467785 467907 := bstep (se 1 (by rfl) ⟨350930, by rfl⟩ : syracuseStep 467907 = 701861) B701861
theorem B893891 : Blo 467785 893891 := bstep (se 1 (by rfl) ⟨670418, by rfl⟩ : syracuseStep 893891 = 1340837) B1340837
theorem B467923 : Blo 467785 467923 := bstep (se 1 (by rfl) ⟨350942, by rfl⟩ : syracuseStep 467923 = 701885) B701885
theorem B467939 : Blo 467785 467939 := bstep (se 1 (by rfl) ⟨350954, by rfl⟩ : syracuseStep 467939 = 701909) B701909
theorem B467955 : Blo 467785 467955 := bstep (se 1 (by rfl) ⟨350966, by rfl⟩ : syracuseStep 467955 = 701933) B701933
theorem B795649 : Blo 467785 795649 := bstep (se 2 (by rfl) ⟨298368, by rfl⟩ : syracuseStep 795649 = 596737) B596737
theorem B467971 : Blo 467785 467971 := bstep (se 1 (by rfl) ⟨350978, by rfl⟩ : syracuseStep 467971 = 701957) B701957
theorem B467987 : Blo 467785 467987 := bstep (se 1 (by rfl) ⟨350990, by rfl⟩ : syracuseStep 467987 = 701981) B701981
theorem B468003 : Blo 467785 468003 := bstep (se 1 (by rfl) ⟨351002, by rfl⟩ : syracuseStep 468003 = 702005) B702005
theorem B795683 : Blo 467785 795683 := bstep (se 1 (by rfl) ⟨596762, by rfl⟩ : syracuseStep 795683 = 1193525) B1193525
theorem B1057841 : Blo 467785 1057841 := bstep (se 2 (by rfl) ⟨396690, by rfl⟩ : syracuseStep 1057841 = 793381) B793381
theorem B468019 : Blo 467785 468019 := bstep (se 1 (by rfl) ⟨351014, by rfl⟩ : syracuseStep 468019 = 702029) B702029
theorem B468035 : Blo 467785 468035 := bstep (se 1 (by rfl) ⟨351026, by rfl⟩ : syracuseStep 468035 = 702053) B702053
theorem B1057859 : Blo 467785 1057859 := bstep (se 1 (by rfl) ⟨793394, by rfl⟩ : syracuseStep 1057859 = 1586789) B1586789
theorem B468051 : Blo 467785 468051 := bstep (se 1 (by rfl) ⟨351038, by rfl⟩ : syracuseStep 468051 = 702077) B702077
theorem B468067 : Blo 467785 468067 := bstep (se 1 (by rfl) ⟨351050, by rfl⟩ : syracuseStep 468067 = 702101) B702101
theorem B468083 : Blo 467785 468083 := bstep (se 1 (by rfl) ⟨351062, by rfl⟩ : syracuseStep 468083 = 702125) B702125
theorem B468099 : Blo 467785 468099 := bstep (se 1 (by rfl) ⟨351074, by rfl⟩ : syracuseStep 468099 = 702149) B702149
theorem B468115 : Blo 467785 468115 := bstep (se 1 (by rfl) ⟨351086, by rfl⟩ : syracuseStep 468115 = 702173) B702173
theorem B468131 : Blo 467785 468131 := bstep (se 1 (by rfl) ⟨351098, by rfl⟩ : syracuseStep 468131 = 702197) B702197
theorem B795811 : Blo 467785 795811 := bstep (se 1 (by rfl) ⟨596858, by rfl⟩ : syracuseStep 795811 = 1193717) B1193717
theorem B1582253 : Blo 467785 1582253 := bstep (se 3 (by rfl) ⟨296672, by rfl⟩ : syracuseStep 1582253 = 593345) B593345
theorem B468147 : Blo 467785 468147 := bstep (se 1 (by rfl) ⟨351110, by rfl⟩ : syracuseStep 468147 = 702221) B702221
theorem B468163 : Blo 467785 468163 := bstep (se 1 (by rfl) ⟨351122, by rfl⟩ : syracuseStep 468163 = 702245) B702245
theorem B468179 : Blo 467785 468179 := bstep (se 1 (by rfl) ⟨351134, by rfl⟩ : syracuseStep 468179 = 702269) B702269
theorem B533731 : Blo 467785 533731 := bstep (se 1 (by rfl) ⟨400298, by rfl⟩ : syracuseStep 533731 = 800597) B800597
theorem B468195 : Blo 467785 468195 := bstep (se 1 (by rfl) ⟨351146, by rfl⟩ : syracuseStep 468195 = 702293) B702293
theorem B1582307 : Blo 467785 1582307 := bstep (se 1 (by rfl) ⟨1186730, by rfl⟩ : syracuseStep 1582307 = 2373461) B2373461
theorem B894179 : Blo 467785 894179 := bstep (se 1 (by rfl) ⟨670634, by rfl⟩ : syracuseStep 894179 = 1341269) B1341269
theorem B468211 : Blo 467785 468211 := bstep (se 1 (by rfl) ⟨351158, by rfl⟩ : syracuseStep 468211 = 702317) B702317
theorem B468227 : Blo 467785 468227 := bstep (se 1 (by rfl) ⟨351170, by rfl⟩ : syracuseStep 468227 = 702341) B702341
theorem B468243 : Blo 467785 468243 := bstep (se 1 (by rfl) ⟨351182, by rfl⟩ : syracuseStep 468243 = 702365) B702365
theorem B468259 : Blo 467785 468259 := bstep (se 1 (by rfl) ⟨351194, by rfl⟩ : syracuseStep 468259 = 702389) B702389
theorem B795953 : Blo 467785 795953 := bstep (se 2 (by rfl) ⟨298482, by rfl⟩ : syracuseStep 795953 = 596965) B596965
theorem B468275 : Blo 467785 468275 := bstep (se 1 (by rfl) ⟨351206, by rfl⟩ : syracuseStep 468275 = 702413) B702413
theorem B468291 : Blo 467785 468291 := bstep (se 1 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 468291 = 702437) B702437
theorem B1189201 : Blo 467785 1189201 := bstep (se 2 (by rfl) ⟨445950, by rfl⟩ : syracuseStep 1189201 = 891901) B891901
theorem B468307 : Blo 467785 468307 := bstep (se 1 (by rfl) ⟨351230, by rfl⟩ : syracuseStep 468307 = 702461) B702461
theorem B1058129 : Blo 467785 1058129 := bstep (se 2 (by rfl) ⟨396798, by rfl⟩ : syracuseStep 1058129 = 793597) B793597
theorem B468323 : Blo 467785 468323 := bstep (se 1 (by rfl) ⟨351242, by rfl⟩ : syracuseStep 468323 = 702485) B702485
theorem B1058147 : Blo 467785 1058147 := bstep (se 1 (by rfl) ⟨793610, by rfl⟩ : syracuseStep 1058147 = 1587221) B1587221
theorem B468339 : Blo 467785 468339 := bstep (se 1 (by rfl) ⟨351254, by rfl⟩ : syracuseStep 468339 = 702509) B702509
theorem B468355 : Blo 467785 468355 := bstep (se 1 (by rfl) ⟨351266, by rfl⟩ : syracuseStep 468355 = 702533) B702533
theorem B468371 : Blo 467785 468371 := bstep (se 1 (by rfl) ⟨351278, by rfl⟩ : syracuseStep 468371 = 702557) B702557
theorem B468387 : Blo 467785 468387 := bstep (se 1 (by rfl) ⟨351290, by rfl⟩ : syracuseStep 468387 = 702581) B702581
theorem B796081 : Blo 467785 796081 := bstep (se 2 (by rfl) ⟨298530, by rfl⟩ : syracuseStep 796081 = 597061) B597061
theorem B468403 : Blo 467785 468403 := bstep (se 1 (by rfl) ⟨351302, by rfl⟩ : syracuseStep 468403 = 702605) B702605
theorem B468419 : Blo 467785 468419 := bstep (se 1 (by rfl) ⟨351314, by rfl⟩ : syracuseStep 468419 = 702629) B702629
theorem B468435 : Blo 467785 468435 := bstep (se 1 (by rfl) ⟨351326, by rfl⟩ : syracuseStep 468435 = 702653) B702653
theorem B796115 : Blo 467785 796115 := bstep (se 1 (by rfl) ⟨597086, by rfl⟩ : syracuseStep 796115 = 1194173) B1194173
theorem B468451 : Blo 467785 468451 := bstep (se 1 (by rfl) ⟨351338, by rfl⟩ : syracuseStep 468451 = 702677) B702677
theorem B1910243 : Blo 467785 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B1779185 : Blo 467785 1779185 := bstep (se 2 (by rfl) ⟨667194, by rfl⟩ : syracuseStep 1779185 = 1334389) B1334389
theorem B1582577 : Blo 467785 1582577 := bstep (se 2 (by rfl) ⟨593466, by rfl⟩ : syracuseStep 1582577 = 1186933) B1186933
theorem B468467 : Blo 467785 468467 := bstep (se 1 (by rfl) ⟨351350, by rfl⟩ : syracuseStep 468467 = 702701) B702701
theorem B468483 : Blo 467785 468483 := bstep (se 1 (by rfl) ⟨351362, by rfl⟩ : syracuseStep 468483 = 702725) B702725
theorem B468499 : Blo 467785 468499 := bstep (se 1 (by rfl) ⟨351374, by rfl⟩ : syracuseStep 468499 = 702749) B702749
theorem B468515 : Blo 467785 468515 := bstep (se 1 (by rfl) ⟨351386, by rfl⟩ : syracuseStep 468515 = 702773) B702773
theorem B3221041 : Blo 467785 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B468531 : Blo 467785 468531 := bstep (se 1 (by rfl) ⟨351398, by rfl⟩ : syracuseStep 468531 = 702797) B702797
theorem B468547 : Blo 467785 468547 := bstep (se 1 (by rfl) ⟨351410, by rfl⟩ : syracuseStep 468547 = 702821) B702821
theorem B468563 : Blo 467785 468563 := bstep (se 1 (by rfl) ⟨351422, by rfl⟩ : syracuseStep 468563 = 702845) B702845
theorem B468579 : Blo 467785 468579 := bstep (se 1 (by rfl) ⟨351434, by rfl⟩ : syracuseStep 468579 = 702869) B702869
theorem B1189475 : Blo 467785 1189475 := bstep (se 1 (by rfl) ⟨892106, by rfl⟩ : syracuseStep 1189475 = 1784213) B1784213
theorem B1058417 : Blo 467785 1058417 := bstep (se 2 (by rfl) ⟨396906, by rfl⟩ : syracuseStep 1058417 = 793813) B793813
theorem B468595 : Blo 467785 468595 := bstep (se 1 (by rfl) ⟨351446, by rfl⟩ : syracuseStep 468595 = 702893) B702893
theorem B468611 : Blo 467785 468611 := bstep (se 1 (by rfl) ⟨351458, by rfl⟩ : syracuseStep 468611 = 702917) B702917
theorem B1058435 : Blo 467785 1058435 := bstep (se 1 (by rfl) ⟨793826, by rfl⟩ : syracuseStep 1058435 = 1587653) B1587653
theorem B763537 : Blo 467785 763537 := bstep (se 2 (by rfl) ⟨286326, by rfl⟩ : syracuseStep 763537 = 572653) B572653
theorem B468627 : Blo 467785 468627 := bstep (se 1 (by rfl) ⟨351470, by rfl⟩ : syracuseStep 468627 = 702941) B702941
theorem B468643 : Blo 467785 468643 := bstep (se 1 (by rfl) ⟨351482, by rfl⟩ : syracuseStep 468643 = 702965) B702965
theorem B468659 : Blo 467785 468659 := bstep (se 1 (by rfl) ⟨351494, by rfl⟩ : syracuseStep 468659 = 702989) B702989
theorem B468675 : Blo 467785 468675 := bstep (se 1 (by rfl) ⟨351506, by rfl⟩ : syracuseStep 468675 = 703013) B703013
theorem B468691 : Blo 467785 468691 := bstep (se 1 (by rfl) ⟨351518, by rfl⟩ : syracuseStep 468691 = 703037) B703037
theorem B468707 : Blo 467785 468707 := bstep (se 1 (by rfl) ⟨351530, by rfl⟩ : syracuseStep 468707 = 703061) B703061
theorem B468723 : Blo 467785 468723 := bstep (se 1 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 468723 = 703085) B703085
theorem B468739 : Blo 467785 468739 := bstep (se 1 (by rfl) ⟨351554, by rfl⟩ : syracuseStep 468739 = 703109) B703109
theorem B468755 : Blo 467785 468755 := bstep (se 1 (by rfl) ⟨351566, by rfl⟩ : syracuseStep 468755 = 703133) B703133
theorem B468771 : Blo 467785 468771 := bstep (se 1 (by rfl) ⟨351578, by rfl⟩ : syracuseStep 468771 = 703157) B703157
theorem B1189667 : Blo 467785 1189667 := bstep (se 1 (by rfl) ⟨892250, by rfl⟩ : syracuseStep 1189667 = 1784501) B1784501
theorem B468787 : Blo 467785 468787 := bstep (se 1 (by rfl) ⟨351590, by rfl⟩ : syracuseStep 468787 = 703181) B703181
theorem B468803 : Blo 467785 468803 := bstep (se 1 (by rfl) ⟨351602, by rfl⟩ : syracuseStep 468803 = 703205) B703205
theorem B468819 : Blo 467785 468819 := bstep (se 1 (by rfl) ⟨351614, by rfl⟩ : syracuseStep 468819 = 703229) B703229
theorem B468835 : Blo 467785 468835 := bstep (se 1 (by rfl) ⟨351626, by rfl⟩ : syracuseStep 468835 = 703253) B703253
theorem B468851 : Blo 467785 468851 := bstep (se 1 (by rfl) ⟨351638, by rfl⟩ : syracuseStep 468851 = 703277) B703277
theorem B468867 : Blo 467785 468867 := bstep (se 1 (by rfl) ⟨351650, by rfl⟩ : syracuseStep 468867 = 703301) B703301
theorem B1058705 : Blo 467785 1058705 := bstep (se 2 (by rfl) ⟨397014, by rfl⟩ : syracuseStep 1058705 = 794029) B794029
theorem B468883 : Blo 467785 468883 := bstep (se 1 (by rfl) ⟨351662, by rfl⟩ : syracuseStep 468883 = 703325) B703325
theorem B468899 : Blo 467785 468899 := bstep (se 1 (by rfl) ⟨351674, by rfl⟩ : syracuseStep 468899 = 703349) B703349
theorem B1058723 : Blo 467785 1058723 := bstep (se 1 (by rfl) ⟨794042, by rfl⟩ : syracuseStep 1058723 = 1588085) B1588085
theorem B468915 : Blo 467785 468915 := bstep (se 1 (by rfl) ⟨351686, by rfl⟩ : syracuseStep 468915 = 703373) B703373
theorem B468931 : Blo 467785 468931 := bstep (se 1 (by rfl) ⟨351698, by rfl⟩ : syracuseStep 468931 = 703397) B703397
theorem B632785 : Blo 467785 632785 := bstep (se 2 (by rfl) ⟨237294, by rfl⟩ : syracuseStep 632785 = 474589) B474589
theorem B468947 : Blo 467785 468947 := bstep (se 1 (by rfl) ⟨351710, by rfl⟩ : syracuseStep 468947 = 703421) B703421
theorem B468963 : Blo 467785 468963 := bstep (se 1 (by rfl) ⟨351722, by rfl⟩ : syracuseStep 468963 = 703445) B703445
theorem B468979 : Blo 467785 468979 := bstep (se 1 (by rfl) ⟨351734, by rfl⟩ : syracuseStep 468979 = 703469) B703469
theorem B468995 : Blo 467785 468995 := bstep (se 1 (by rfl) ⟨351746, by rfl⟩ : syracuseStep 468995 = 703493) B703493
theorem B501763 : Blo 467785 501763 := bstep (se 1 (by rfl) ⟨376322, by rfl⟩ : syracuseStep 501763 = 752645) B752645
theorem B1583117 : Blo 467785 1583117 := bstep (se 3 (by rfl) ⟨296834, by rfl⟩ : syracuseStep 1583117 = 593669) B593669
theorem B469011 : Blo 467785 469011 := bstep (se 1 (by rfl) ⟨351758, by rfl⟩ : syracuseStep 469011 = 703517) B703517
theorem B469027 : Blo 467785 469027 := bstep (se 1 (by rfl) ⟨351770, by rfl⟩ : syracuseStep 469027 = 703541) B703541
theorem B469043 : Blo 467785 469043 := bstep (se 1 (by rfl) ⟨351782, by rfl⟩ : syracuseStep 469043 = 703565) B703565
theorem B469059 : Blo 467785 469059 := bstep (se 1 (by rfl) ⟨351794, by rfl⟩ : syracuseStep 469059 = 703589) B703589
theorem B1583171 : Blo 467785 1583171 := bstep (se 1 (by rfl) ⟨1187378, by rfl⟩ : syracuseStep 1583171 = 2374757) B2374757
theorem B469075 : Blo 467785 469075 := bstep (se 1 (by rfl) ⟨351806, by rfl⟩ : syracuseStep 469075 = 703613) B703613
theorem B469091 : Blo 467785 469091 := bstep (se 1 (by rfl) ⟨351818, by rfl⟩ : syracuseStep 469091 = 703637) B703637
theorem B469107 : Blo 467785 469107 := bstep (se 1 (by rfl) ⟨351830, by rfl⟩ : syracuseStep 469107 = 703661) B703661
theorem B469123 : Blo 467785 469123 := bstep (se 1 (by rfl) ⟨351842, by rfl⟩ : syracuseStep 469123 = 703685) B703685
theorem B1779853 : Blo 467785 1779853 := bstep (se 3 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 1779853 = 667445) B667445
theorem B895121 : Blo 467785 895121 := bstep (se 2 (by rfl) ⟨335670, by rfl⟩ : syracuseStep 895121 = 671341) B671341
theorem B469139 : Blo 467785 469139 := bstep (se 1 (by rfl) ⟨351854, by rfl⟩ : syracuseStep 469139 = 703709) B703709
theorem B469155 : Blo 467785 469155 := bstep (se 1 (by rfl) ⟨351866, by rfl⟩ : syracuseStep 469155 = 703733) B703733
theorem B1058993 : Blo 467785 1058993 := bstep (se 2 (by rfl) ⟨397122, by rfl⟩ : syracuseStep 1058993 = 794245) B794245
theorem B469171 : Blo 467785 469171 := bstep (se 1 (by rfl) ⟨351878, by rfl⟩ : syracuseStep 469171 = 703757) B703757
theorem B469187 : Blo 467785 469187 := bstep (se 1 (by rfl) ⟨351890, by rfl⟩ : syracuseStep 469187 = 703781) B703781
theorem B1059011 : Blo 467785 1059011 := bstep (se 1 (by rfl) ⟨794258, by rfl⟩ : syracuseStep 1059011 = 1588517) B1588517
theorem B469203 : Blo 467785 469203 := bstep (se 1 (by rfl) ⟨351902, by rfl⟩ : syracuseStep 469203 = 703805) B703805
theorem B469219 : Blo 467785 469219 := bstep (se 1 (by rfl) ⟨351914, by rfl⟩ : syracuseStep 469219 = 703829) B703829
theorem B469235 : Blo 467785 469235 := bstep (se 1 (by rfl) ⟨351926, by rfl⟩ : syracuseStep 469235 = 703853) B703853
theorem B469251 : Blo 467785 469251 := bstep (se 1 (by rfl) ⟨351938, by rfl⟩ : syracuseStep 469251 = 703877) B703877
theorem B469267 : Blo 467785 469267 := bstep (se 1 (by rfl) ⟨351950, by rfl⟩ : syracuseStep 469267 = 703901) B703901
theorem B469283 : Blo 467785 469283 := bstep (se 1 (by rfl) ⟨351962, by rfl⟩ : syracuseStep 469283 = 703925) B703925
theorem B469299 : Blo 467785 469299 := bstep (se 1 (by rfl) ⟨351974, by rfl⟩ : syracuseStep 469299 = 703949) B703949
theorem B469315 : Blo 467785 469315 := bstep (se 1 (by rfl) ⟨351986, by rfl⟩ : syracuseStep 469315 = 703973) B703973
theorem B1583441 : Blo 467785 1583441 := bstep (se 2 (by rfl) ⟨593790, by rfl⟩ : syracuseStep 1583441 = 1187581) B1187581
theorem B469331 : Blo 467785 469331 := bstep (se 1 (by rfl) ⟨351998, by rfl⟩ : syracuseStep 469331 = 703997) B703997
theorem B469347 : Blo 467785 469347 := bstep (se 1 (by rfl) ⟨352010, by rfl⟩ : syracuseStep 469347 = 704021) B704021
theorem B2009443 : Blo 467785 2009443 := bstep (se 1 (by rfl) ⟨1507082, by rfl⟩ : syracuseStep 2009443 = 3014165) B3014165
theorem B469363 : Blo 467785 469363 := bstep (se 1 (by rfl) ⟨352022, by rfl⟩ : syracuseStep 469363 = 704045) B704045
theorem B469379 : Blo 467785 469379 := bstep (se 1 (by rfl) ⟨352034, by rfl⟩ : syracuseStep 469379 = 704069) B704069
theorem B469395 : Blo 467785 469395 := bstep (se 1 (by rfl) ⟨352046, by rfl⟩ : syracuseStep 469395 = 704093) B704093
theorem B469411 : Blo 467785 469411 := bstep (se 1 (by rfl) ⟨352058, by rfl⟩ : syracuseStep 469411 = 704117) B704117
theorem B469427 : Blo 467785 469427 := bstep (se 1 (by rfl) ⟨352070, by rfl⟩ : syracuseStep 469427 = 704141) B704141
theorem B469443 : Blo 467785 469443 := bstep (se 1 (by rfl) ⟨352082, by rfl⟩ : syracuseStep 469443 = 704165) B704165
theorem B1059281 : Blo 467785 1059281 := bstep (se 2 (by rfl) ⟨397230, by rfl⟩ : syracuseStep 1059281 = 794461) B794461
theorem B469459 : Blo 467785 469459 := bstep (se 1 (by rfl) ⟨352094, by rfl⟩ : syracuseStep 469459 = 704189) B704189
theorem B469475 : Blo 467785 469475 := bstep (se 1 (by rfl) ⟨352106, by rfl⟩ : syracuseStep 469475 = 704213) B704213
theorem B1059299 : Blo 467785 1059299 := bstep (se 1 (by rfl) ⟨794474, by rfl⟩ : syracuseStep 1059299 = 1588949) B1588949
theorem B469491 : Blo 467785 469491 := bstep (se 1 (by rfl) ⟨352118, by rfl⟩ : syracuseStep 469491 = 704237) B704237
theorem B469507 : Blo 467785 469507 := bstep (se 1 (by rfl) ⟨352130, by rfl⟩ : syracuseStep 469507 = 704261) B704261
theorem B3058181 : Blo 467785 3058181 := bstep (se 4 (by rfl) ⟨286704, by rfl⟩ : syracuseStep 3058181 = 573409) B573409
theorem B469523 : Blo 467785 469523 := bstep (se 1 (by rfl) ⟨352142, by rfl⟩ : syracuseStep 469523 = 704285) B704285
theorem B469539 : Blo 467785 469539 := bstep (se 1 (by rfl) ⟨352154, by rfl⟩ : syracuseStep 469539 = 704309) B704309
theorem B469555 : Blo 467785 469555 := bstep (se 1 (by rfl) ⟨352166, by rfl⟩ : syracuseStep 469555 = 704333) B704333
theorem B469571 : Blo 467785 469571 := bstep (se 1 (by rfl) ⟨352178, by rfl⟩ : syracuseStep 469571 = 704357) B704357
theorem B469587 : Blo 467785 469587 := bstep (se 1 (by rfl) ⟨352190, by rfl⟩ : syracuseStep 469587 = 704381) B704381
theorem B469603 : Blo 467785 469603 := bstep (se 1 (by rfl) ⟨352202, by rfl⟩ : syracuseStep 469603 = 704405) B704405
theorem B469619 : Blo 467785 469619 := bstep (se 1 (by rfl) ⟨352214, by rfl⟩ : syracuseStep 469619 = 704429) B704429
theorem B469635 : Blo 467785 469635 := bstep (se 1 (by rfl) ⟨352226, by rfl⟩ : syracuseStep 469635 = 704453) B704453
theorem B469651 : Blo 467785 469651 := bstep (se 1 (by rfl) ⟨352238, by rfl⟩ : syracuseStep 469651 = 704477) B704477
theorem B469667 : Blo 467785 469667 := bstep (se 1 (by rfl) ⟨352250, by rfl⟩ : syracuseStep 469667 = 704501) B704501
theorem B469683 : Blo 467785 469683 := bstep (se 1 (by rfl) ⟨352262, by rfl⟩ : syracuseStep 469683 = 704525) B704525
theorem B469699 : Blo 467785 469699 := bstep (se 1 (by rfl) ⟨352274, by rfl⟩ : syracuseStep 469699 = 704549) B704549
theorem B1354445 : Blo 467785 1354445 := bstep (se 3 (by rfl) ⟨253958, by rfl⟩ : syracuseStep 1354445 = 507917) B507917
theorem B1190609 : Blo 467785 1190609 := bstep (se 2 (by rfl) ⟨446478, by rfl⟩ : syracuseStep 1190609 = 892957) B892957
theorem B469715 : Blo 467785 469715 := bstep (se 1 (by rfl) ⟨352286, by rfl⟩ : syracuseStep 469715 = 704573) B704573
theorem B469731 : Blo 467785 469731 := bstep (se 1 (by rfl) ⟨352298, by rfl⟩ : syracuseStep 469731 = 704597) B704597
theorem B1059569 : Blo 467785 1059569 := bstep (se 2 (by rfl) ⟨397338, by rfl⟩ : syracuseStep 1059569 = 794677) B794677
theorem B469747 : Blo 467785 469747 := bstep (se 1 (by rfl) ⟨352310, by rfl⟩ : syracuseStep 469747 = 704621) B704621
theorem B469763 : Blo 467785 469763 := bstep (se 1 (by rfl) ⟨352322, by rfl⟩ : syracuseStep 469763 = 704645) B704645
theorem B1190659 : Blo 467785 1190659 := bstep (se 1 (by rfl) ⟨892994, by rfl⟩ : syracuseStep 1190659 = 1785989) B1785989
theorem B1059587 : Blo 467785 1059587 := bstep (se 1 (by rfl) ⟨794690, by rfl⟩ : syracuseStep 1059587 = 1589381) B1589381
theorem B469779 : Blo 467785 469779 := bstep (se 1 (by rfl) ⟨352334, by rfl⟩ : syracuseStep 469779 = 704669) B704669
theorem B469795 : Blo 467785 469795 := bstep (se 1 (by rfl) ⟨352346, by rfl⟩ : syracuseStep 469795 = 704693) B704693
theorem B469811 : Blo 467785 469811 := bstep (se 1 (by rfl) ⟨352358, by rfl⟩ : syracuseStep 469811 = 704717) B704717
theorem B469827 : Blo 467785 469827 := bstep (se 1 (by rfl) ⟨352370, by rfl⟩ : syracuseStep 469827 = 704741) B704741
theorem B469843 : Blo 467785 469843 := bstep (se 1 (by rfl) ⟨352382, by rfl⟩ : syracuseStep 469843 = 704765) B704765
theorem B469859 : Blo 467785 469859 := bstep (se 1 (by rfl) ⟨352394, by rfl⟩ : syracuseStep 469859 = 704789) B704789
theorem B1583981 : Blo 467785 1583981 := bstep (se 3 (by rfl) ⟨296996, by rfl⟩ : syracuseStep 1583981 = 593993) B593993
theorem B469875 : Blo 467785 469875 := bstep (se 1 (by rfl) ⟨352406, by rfl⟩ : syracuseStep 469875 = 704813) B704813
theorem B502643 : Blo 467785 502643 := bstep (se 1 (by rfl) ⟨376982, by rfl⟩ : syracuseStep 502643 = 753965) B753965
theorem B469891 : Blo 467785 469891 := bstep (se 1 (by rfl) ⟨352418, by rfl⟩ : syracuseStep 469891 = 704837) B704837
theorem B1190801 : Blo 467785 1190801 := bstep (se 2 (by rfl) ⟨446550, by rfl⟩ : syracuseStep 1190801 = 893101) B893101
theorem B469907 : Blo 467785 469907 := bstep (se 1 (by rfl) ⟨352430, by rfl⟩ : syracuseStep 469907 = 704861) B704861
theorem B1780643 : Blo 467785 1780643 := bstep (se 1 (by rfl) ⟨1335482, by rfl⟩ : syracuseStep 1780643 = 2670965) B2670965
theorem B1584035 : Blo 467785 1584035 := bstep (se 1 (by rfl) ⟨1188026, by rfl⟩ : syracuseStep 1584035 = 2376053) B2376053
theorem B469923 : Blo 467785 469923 := bstep (se 1 (by rfl) ⟨352442, by rfl⟩ : syracuseStep 469923 = 704885) B704885
theorem B469939 : Blo 467785 469939 := bstep (se 1 (by rfl) ⟨352454, by rfl⟩ : syracuseStep 469939 = 704909) B704909
theorem B469955 : Blo 467785 469955 := bstep (se 1 (by rfl) ⟨352466, by rfl⟩ : syracuseStep 469955 = 704933) B704933
theorem B469971 : Blo 467785 469971 := bstep (se 1 (by rfl) ⟨352478, by rfl⟩ : syracuseStep 469971 = 704957) B704957
theorem B469987 : Blo 467785 469987 := bstep (se 1 (by rfl) ⟨352490, by rfl⟩ : syracuseStep 469987 = 704981) B704981
theorem B2370545 : Blo 467785 2370545 := bstep (se 2 (by rfl) ⟨888954, by rfl⟩ : syracuseStep 2370545 = 1777909) B1777909
theorem B470003 : Blo 467785 470003 := bstep (se 1 (by rfl) ⟨352502, by rfl⟩ : syracuseStep 470003 = 705005) B705005
theorem B502771 : Blo 467785 502771 := bstep (se 1 (by rfl) ⟨377078, by rfl⟩ : syracuseStep 502771 = 754157) B754157
theorem B666625 : Blo 467785 666625 := bstep (se 2 (by rfl) ⟨249984, by rfl⟩ : syracuseStep 666625 = 499969) B499969
theorem B470019 : Blo 467785 470019 := bstep (se 1 (by rfl) ⟨352514, by rfl⟩ : syracuseStep 470019 = 705029) B705029
theorem B1059857 : Blo 467785 1059857 := bstep (se 2 (by rfl) ⟨397446, by rfl⟩ : syracuseStep 1059857 = 794893) B794893
theorem B470035 : Blo 467785 470035 := bstep (se 1 (by rfl) ⟨352526, by rfl⟩ : syracuseStep 470035 = 705053) B705053
theorem B470051 : Blo 467785 470051 := bstep (se 1 (by rfl) ⟨352538, by rfl⟩ : syracuseStep 470051 = 705077) B705077
theorem B1059875 : Blo 467785 1059875 := bstep (se 1 (by rfl) ⟨794906, by rfl⟩ : syracuseStep 1059875 = 1589813) B1589813
theorem B470067 : Blo 467785 470067 := bstep (se 1 (by rfl) ⟨352550, by rfl⟩ : syracuseStep 470067 = 705101) B705101
theorem B470083 : Blo 467785 470083 := bstep (se 1 (by rfl) ⟨352562, by rfl⟩ : syracuseStep 470083 = 705125) B705125
theorem B470099 : Blo 467785 470099 := bstep (se 1 (by rfl) ⟨352574, by rfl⟩ : syracuseStep 470099 = 705149) B705149
theorem B633953 : Blo 467785 633953 := bstep (se 2 (by rfl) ⟨237732, by rfl⟩ : syracuseStep 633953 = 475465) B475465
theorem B470115 : Blo 467785 470115 := bstep (se 1 (by rfl) ⟨352586, by rfl⟩ : syracuseStep 470115 = 705173) B705173
theorem B666739 : Blo 467785 666739 := bstep (se 1 (by rfl) ⟨500054, by rfl⟩ : syracuseStep 666739 = 1000109) B1000109
theorem B470131 : Blo 467785 470131 := bstep (se 1 (by rfl) ⟨352598, by rfl⟩ : syracuseStep 470131 = 705197) B705197
theorem B470147 : Blo 467785 470147 := bstep (se 1 (by rfl) ⟨352610, by rfl⟩ : syracuseStep 470147 = 705221) B705221
theorem B470163 : Blo 467785 470163 := bstep (se 1 (by rfl) ⟨352622, by rfl⟩ : syracuseStep 470163 = 705245) B705245
theorem B470179 : Blo 467785 470179 := bstep (se 1 (by rfl) ⟨352634, by rfl⟩ : syracuseStep 470179 = 705269) B705269
theorem B1584305 : Blo 467785 1584305 := bstep (se 2 (by rfl) ⟨594114, by rfl⟩ : syracuseStep 1584305 = 1188229) B1188229
theorem B470195 : Blo 467785 470195 := bstep (se 1 (by rfl) ⟨352646, by rfl⟩ : syracuseStep 470195 = 705293) B705293
theorem B470211 : Blo 467785 470211 := bstep (se 1 (by rfl) ⟨352658, by rfl⟩ : syracuseStep 470211 = 705317) B705317
theorem B470227 : Blo 467785 470227 := bstep (se 1 (by rfl) ⟨352670, by rfl⟩ : syracuseStep 470227 = 705341) B705341
theorem B470243 : Blo 467785 470243 := bstep (se 1 (by rfl) ⟨352682, by rfl⟩ : syracuseStep 470243 = 705365) B705365
theorem B470259 : Blo 467785 470259 := bstep (se 1 (by rfl) ⟨352694, by rfl⟩ : syracuseStep 470259 = 705389) B705389
theorem B470275 : Blo 467785 470275 := bstep (se 1 (by rfl) ⟨352706, by rfl⟩ : syracuseStep 470275 = 705413) B705413
theorem B470291 : Blo 467785 470291 := bstep (se 1 (by rfl) ⟨352718, by rfl⟩ : syracuseStep 470291 = 705437) B705437
theorem B470307 : Blo 467785 470307 := bstep (se 1 (by rfl) ⟨352730, by rfl⟩ : syracuseStep 470307 = 705461) B705461
theorem B1060145 : Blo 467785 1060145 := bstep (se 2 (by rfl) ⟨397554, by rfl⟩ : syracuseStep 1060145 = 795109) B795109
theorem B470323 : Blo 467785 470323 := bstep (se 1 (by rfl) ⟨352742, by rfl⟩ : syracuseStep 470323 = 705485) B705485
theorem B470339 : Blo 467785 470339 := bstep (se 1 (by rfl) ⟨352754, by rfl⟩ : syracuseStep 470339 = 705509) B705509
theorem B1060163 : Blo 467785 1060163 := bstep (se 1 (by rfl) ⟨795122, by rfl⟩ : syracuseStep 1060163 = 1590245) B1590245
theorem B470355 : Blo 467785 470355 := bstep (se 1 (by rfl) ⟨352766, by rfl⟩ : syracuseStep 470355 = 705533) B705533
theorem B470371 : Blo 467785 470371 := bstep (se 1 (by rfl) ⟨352778, by rfl⟩ : syracuseStep 470371 = 705557) B705557
theorem B470387 : Blo 467785 470387 := bstep (se 1 (by rfl) ⟨352790, by rfl⟩ : syracuseStep 470387 = 705581) B705581
theorem B470403 : Blo 467785 470403 := bstep (se 1 (by rfl) ⟨352802, by rfl⟩ : syracuseStep 470403 = 705605) B705605
theorem B470419 : Blo 467785 470419 := bstep (se 1 (by rfl) ⟨352814, by rfl⟩ : syracuseStep 470419 = 705629) B705629
theorem B470435 : Blo 467785 470435 := bstep (se 1 (by rfl) ⟨352826, by rfl⟩ : syracuseStep 470435 = 705653) B705653
theorem B470451 : Blo 467785 470451 := bstep (se 1 (by rfl) ⟨352838, by rfl⟩ : syracuseStep 470451 = 705677) B705677
theorem B470467 : Blo 467785 470467 := bstep (se 1 (by rfl) ⟨352850, by rfl⟩ : syracuseStep 470467 = 705701) B705701
theorem B470483 : Blo 467785 470483 := bstep (se 1 (by rfl) ⟨352862, by rfl⟩ : syracuseStep 470483 = 705725) B705725
theorem B470499 : Blo 467785 470499 := bstep (se 1 (by rfl) ⟨352874, by rfl⟩ : syracuseStep 470499 = 705749) B705749
theorem B470515 : Blo 467785 470515 := bstep (se 1 (by rfl) ⟨352886, by rfl⟩ : syracuseStep 470515 = 705773) B705773
theorem B470531 : Blo 467785 470531 := bstep (se 1 (by rfl) ⟨352898, by rfl⟩ : syracuseStep 470531 = 705797) B705797
theorem B470547 : Blo 467785 470547 := bstep (se 1 (by rfl) ⟨352910, by rfl⟩ : syracuseStep 470547 = 705821) B705821
theorem B470563 : Blo 467785 470563 := bstep (se 1 (by rfl) ⟨352922, by rfl⟩ : syracuseStep 470563 = 705845) B705845
theorem B1781297 : Blo 467785 1781297 := bstep (se 2 (by rfl) ⟨667986, by rfl⟩ : syracuseStep 1781297 = 1335973) B1335973
theorem B2010673 : Blo 467785 2010673 := bstep (se 2 (by rfl) ⟨754002, by rfl⟩ : syracuseStep 2010673 = 1508005) B1508005
theorem B470579 : Blo 467785 470579 := bstep (se 1 (by rfl) ⟨352934, by rfl⟩ : syracuseStep 470579 = 705869) B705869
theorem B470595 : Blo 467785 470595 := bstep (se 1 (by rfl) ⟨352946, by rfl⟩ : syracuseStep 470595 = 705893) B705893
theorem B2862661 : Blo 467785 2862661 := bstep (se 4 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 2862661 = 536749) B536749
theorem B1060433 : Blo 467785 1060433 := bstep (se 2 (by rfl) ⟨397662, by rfl⟩ : syracuseStep 1060433 = 795325) B795325
theorem B470611 : Blo 467785 470611 := bstep (se 1 (by rfl) ⟨352958, by rfl⟩ : syracuseStep 470611 = 705917) B705917
theorem B470627 : Blo 467785 470627 := bstep (se 1 (by rfl) ⟨352970, by rfl⟩ : syracuseStep 470627 = 705941) B705941
theorem B1060451 : Blo 467785 1060451 := bstep (se 1 (by rfl) ⟨795338, by rfl⟩ : syracuseStep 1060451 = 1590677) B1590677
theorem B634483 : Blo 467785 634483 := bstep (se 1 (by rfl) ⟨475862, by rfl⟩ : syracuseStep 634483 = 951725) B951725
theorem B470643 : Blo 467785 470643 := bstep (se 1 (by rfl) ⟨352982, by rfl⟩ : syracuseStep 470643 = 705965) B705965
theorem B470659 : Blo 467785 470659 := bstep (se 1 (by rfl) ⟨352994, by rfl⟩ : syracuseStep 470659 = 705989) B705989
theorem B470675 : Blo 467785 470675 := bstep (se 1 (by rfl) ⟨353006, by rfl⟩ : syracuseStep 470675 = 706013) B706013
theorem B470691 : Blo 467785 470691 := bstep (se 1 (by rfl) ⟨353018, by rfl⟩ : syracuseStep 470691 = 706037) B706037
theorem B470707 : Blo 467785 470707 := bstep (se 1 (by rfl) ⟨353030, by rfl⟩ : syracuseStep 470707 = 706061) B706061
theorem B470723 : Blo 467785 470723 := bstep (se 1 (by rfl) ⟨353042, by rfl⟩ : syracuseStep 470723 = 706085) B706085
theorem B1584845 : Blo 467785 1584845 := bstep (se 3 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 1584845 = 594317) B594317
theorem B470739 : Blo 467785 470739 := bstep (se 1 (by rfl) ⟨353054, by rfl⟩ : syracuseStep 470739 = 706109) B706109
theorem B470755 : Blo 467785 470755 := bstep (se 1 (by rfl) ⟨353066, by rfl⟩ : syracuseStep 470755 = 706133) B706133
theorem B470771 : Blo 467785 470771 := bstep (se 1 (by rfl) ⟨353078, by rfl⟩ : syracuseStep 470771 = 706157) B706157
theorem B1584899 : Blo 467785 1584899 := bstep (se 1 (by rfl) ⟨1188674, by rfl⟩ : syracuseStep 1584899 = 2377349) B2377349
theorem B470787 : Blo 467785 470787 := bstep (se 1 (by rfl) ⟨353090, by rfl⟩ : syracuseStep 470787 = 706181) B706181
theorem B470803 : Blo 467785 470803 := bstep (se 1 (by rfl) ⟨353102, by rfl⟩ : syracuseStep 470803 = 706205) B706205
theorem B470819 : Blo 467785 470819 := bstep (se 1 (by rfl) ⟨353114, by rfl⟩ : syracuseStep 470819 = 706229) B706229
theorem B503587 : Blo 467785 503587 := bstep (se 1 (by rfl) ⟨377690, by rfl⟩ : syracuseStep 503587 = 755381) B755381
theorem B470835 : Blo 467785 470835 := bstep (se 1 (by rfl) ⟨353126, by rfl⟩ : syracuseStep 470835 = 706253) B706253
theorem B470851 : Blo 467785 470851 := bstep (se 1 (by rfl) ⟨353138, by rfl⟩ : syracuseStep 470851 = 706277) B706277
theorem B2666317 : Blo 467785 2666317 := bstep (se 3 (by rfl) ⟨499934, by rfl⟩ : syracuseStep 2666317 = 999869) B999869
theorem B470867 : Blo 467785 470867 := bstep (se 1 (by rfl) ⟨353150, by rfl⟩ : syracuseStep 470867 = 706301) B706301
theorem B470883 : Blo 467785 470883 := bstep (se 1 (by rfl) ⟨353162, by rfl⟩ : syracuseStep 470883 = 706325) B706325
theorem B1191793 : Blo 467785 1191793 := bstep (se 2 (by rfl) ⟨446922, by rfl⟩ : syracuseStep 1191793 = 893845) B893845
theorem B470899 : Blo 467785 470899 := bstep (se 1 (by rfl) ⟨353174, by rfl⟩ : syracuseStep 470899 = 706349) B706349
theorem B1060721 : Blo 467785 1060721 := bstep (se 2 (by rfl) ⟨397770, by rfl⟩ : syracuseStep 1060721 = 795541) B795541
theorem B470915 : Blo 467785 470915 := bstep (se 1 (by rfl) ⟨353186, by rfl⟩ : syracuseStep 470915 = 706373) B706373
theorem B1060739 : Blo 467785 1060739 := bstep (se 1 (by rfl) ⟨795554, by rfl⟩ : syracuseStep 1060739 = 1591109) B1591109
theorem B470931 : Blo 467785 470931 := bstep (se 1 (by rfl) ⟨353198, by rfl⟩ : syracuseStep 470931 = 706397) B706397
theorem B470947 : Blo 467785 470947 := bstep (se 1 (by rfl) ⟨353210, by rfl⟩ : syracuseStep 470947 = 706421) B706421
theorem B470963 : Blo 467785 470963 := bstep (se 1 (by rfl) ⟨353222, by rfl⟩ : syracuseStep 470963 = 706445) B706445
theorem B470979 : Blo 467785 470979 := bstep (se 1 (by rfl) ⟨353234, by rfl⟩ : syracuseStep 470979 = 706469) B706469
theorem B3813317 : Blo 467785 3813317 := bstep (se 4 (by rfl) ⟨357498, by rfl⟩ : syracuseStep 3813317 = 714997) B714997
theorem B470995 : Blo 467785 470995 := bstep (se 1 (by rfl) ⟨353246, by rfl⟩ : syracuseStep 470995 = 706493) B706493
theorem B2142179 : Blo 467785 2142179 := bstep (se 1 (by rfl) ⟨1606634, by rfl⟩ : syracuseStep 2142179 = 3213269) B3213269
theorem B471011 : Blo 467785 471011 := bstep (se 1 (by rfl) ⟨353258, by rfl⟩ : syracuseStep 471011 = 706517) B706517
theorem B471027 : Blo 467785 471027 := bstep (se 1 (by rfl) ⟨353270, by rfl⟩ : syracuseStep 471027 = 706541) B706541
theorem B471043 : Blo 467785 471043 := bstep (se 1 (by rfl) ⟨353282, by rfl⟩ : syracuseStep 471043 = 706565) B706565
theorem B1585169 : Blo 467785 1585169 := bstep (se 2 (by rfl) ⟨594438, by rfl⟩ : syracuseStep 1585169 = 1188877) B1188877
theorem B471059 : Blo 467785 471059 := bstep (se 1 (by rfl) ⟨353294, by rfl⟩ : syracuseStep 471059 = 706589) B706589
theorem B471075 : Blo 467785 471075 := bstep (se 1 (by rfl) ⟨353306, by rfl⟩ : syracuseStep 471075 = 706613) B706613
theorem B471091 : Blo 467785 471091 := bstep (se 1 (by rfl) ⟨353318, by rfl⟩ : syracuseStep 471091 = 706637) B706637
theorem B471107 : Blo 467785 471107 := bstep (se 1 (by rfl) ⟨353330, by rfl⟩ : syracuseStep 471107 = 706661) B706661
theorem B471123 : Blo 467785 471123 := bstep (se 1 (by rfl) ⟨353342, by rfl⟩ : syracuseStep 471123 = 706685) B706685
theorem B471139 : Blo 467785 471139 := bstep (se 1 (by rfl) ⟨353354, by rfl⟩ : syracuseStep 471139 = 706709) B706709
theorem B471155 : Blo 467785 471155 := bstep (se 1 (by rfl) ⟨353366, by rfl⟩ : syracuseStep 471155 = 706733) B706733
theorem B1192067 : Blo 467785 1192067 := bstep (se 1 (by rfl) ⟨894050, by rfl⟩ : syracuseStep 1192067 = 1788101) B1788101
theorem B471171 : Blo 467785 471171 := bstep (se 1 (by rfl) ⟨353378, by rfl⟩ : syracuseStep 471171 = 706757) B706757
theorem B1061009 : Blo 467785 1061009 := bstep (se 2 (by rfl) ⟨397878, by rfl⟩ : syracuseStep 1061009 = 795757) B795757
theorem B471187 : Blo 467785 471187 := bstep (se 1 (by rfl) ⟨353390, by rfl⟩ : syracuseStep 471187 = 706781) B706781
theorem B471203 : Blo 467785 471203 := bstep (se 1 (by rfl) ⟨353402, by rfl⟩ : syracuseStep 471203 = 706805) B706805
theorem B1061027 : Blo 467785 1061027 := bstep (se 1 (by rfl) ⟨795770, by rfl⟩ : syracuseStep 1061027 = 1591541) B1591541
theorem B471219 : Blo 467785 471219 := bstep (se 1 (by rfl) ⟨353414, by rfl⟩ : syracuseStep 471219 = 706829) B706829
theorem B471235 : Blo 467785 471235 := bstep (se 1 (by rfl) ⟨353426, by rfl⟩ : syracuseStep 471235 = 706853) B706853
theorem B471251 : Blo 467785 471251 := bstep (se 1 (by rfl) ⟨353438, by rfl⟩ : syracuseStep 471251 = 706877) B706877
theorem B471267 : Blo 467785 471267 := bstep (se 1 (by rfl) ⟨353450, by rfl⟩ : syracuseStep 471267 = 706901) B706901
theorem B471283 : Blo 467785 471283 := bstep (se 1 (by rfl) ⟨353462, by rfl⟩ : syracuseStep 471283 = 706925) B706925
theorem B471299 : Blo 467785 471299 := bstep (se 1 (by rfl) ⟨353474, by rfl⟩ : syracuseStep 471299 = 706949) B706949
theorem B471315 : Blo 467785 471315 := bstep (se 1 (by rfl) ⟨353486, by rfl⟩ : syracuseStep 471315 = 706973) B706973
theorem B471331 : Blo 467785 471331 := bstep (se 1 (by rfl) ⟨353498, by rfl⟩ : syracuseStep 471331 = 706997) B706997
theorem B471347 : Blo 467785 471347 := bstep (se 1 (by rfl) ⟨353510, by rfl⟩ : syracuseStep 471347 = 707021) B707021
theorem B1192259 : Blo 467785 1192259 := bstep (se 1 (by rfl) ⟨894194, by rfl⟩ : syracuseStep 1192259 = 1788389) B1788389
theorem B471363 : Blo 467785 471363 := bstep (se 1 (by rfl) ⟨353522, by rfl⟩ : syracuseStep 471363 = 707045) B707045
theorem B471379 : Blo 467785 471379 := bstep (se 1 (by rfl) ⟨353534, by rfl⟩ : syracuseStep 471379 = 707069) B707069
theorem B471395 : Blo 467785 471395 := bstep (se 1 (by rfl) ⟨353546, by rfl⟩ : syracuseStep 471395 = 707093) B707093
theorem B471411 : Blo 467785 471411 := bstep (se 1 (by rfl) ⟨353558, by rfl⟩ : syracuseStep 471411 = 707117) B707117
theorem B471427 : Blo 467785 471427 := bstep (se 1 (by rfl) ⟨353570, by rfl⟩ : syracuseStep 471427 = 707141) B707141
theorem B471443 : Blo 467785 471443 := bstep (se 1 (by rfl) ⟨353582, by rfl⟩ : syracuseStep 471443 = 707165) B707165
theorem B2372003 : Blo 467785 2372003 := bstep (se 1 (by rfl) ⟨1779002, by rfl⟩ : syracuseStep 2372003 = 3558005) B3558005
theorem B471459 : Blo 467785 471459 := bstep (se 1 (by rfl) ⟨353594, by rfl⟩ : syracuseStep 471459 = 707189) B707189
theorem B1061297 : Blo 467785 1061297 := bstep (se 2 (by rfl) ⟨397986, by rfl⟩ : syracuseStep 1061297 = 795973) B795973
theorem B668083 : Blo 467785 668083 := bstep (se 1 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 668083 = 1002125) B1002125
theorem B471475 : Blo 467785 471475 := bstep (se 1 (by rfl) ⟨353606, by rfl⟩ : syracuseStep 471475 = 707213) B707213
theorem B471491 : Blo 467785 471491 := bstep (se 1 (by rfl) ⟨353618, by rfl⟩ : syracuseStep 471491 = 707237) B707237
theorem B1061315 : Blo 467785 1061315 := bstep (se 1 (by rfl) ⟨795986, by rfl⟩ : syracuseStep 1061315 = 1591973) B1591973
theorem B471507 : Blo 467785 471507 := bstep (se 1 (by rfl) ⟨353630, by rfl⟩ : syracuseStep 471507 = 707261) B707261
theorem B471523 : Blo 467785 471523 := bstep (se 1 (by rfl) ⟨353642, by rfl⟩ : syracuseStep 471523 = 707285) B707285
theorem B471539 : Blo 467785 471539 := bstep (se 1 (by rfl) ⟨353654, by rfl⟩ : syracuseStep 471539 = 707309) B707309
theorem B471555 : Blo 467785 471555 := bstep (se 1 (by rfl) ⟨353666, by rfl⟩ : syracuseStep 471555 = 707333) B707333
theorem B471571 : Blo 467785 471571 := bstep (se 1 (by rfl) ⟨353678, by rfl⟩ : syracuseStep 471571 = 707357) B707357
theorem B471587 : Blo 467785 471587 := bstep (se 1 (by rfl) ⟨353690, by rfl⟩ : syracuseStep 471587 = 707381) B707381
theorem B1585709 : Blo 467785 1585709 := bstep (se 3 (by rfl) ⟨297320, by rfl⟩ : syracuseStep 1585709 = 594641) B594641
theorem B471603 : Blo 467785 471603 := bstep (se 1 (by rfl) ⟨353702, by rfl⟩ : syracuseStep 471603 = 707405) B707405
theorem B471619 : Blo 467785 471619 := bstep (se 1 (by rfl) ⟨353714, by rfl⟩ : syracuseStep 471619 = 707429) B707429
theorem B471635 : Blo 467785 471635 := bstep (se 1 (by rfl) ⟨353726, by rfl⟩ : syracuseStep 471635 = 707453) B707453
theorem B1585763 : Blo 467785 1585763 := bstep (se 1 (by rfl) ⟨1189322, by rfl⟩ : syracuseStep 1585763 = 2378645) B2378645
theorem B471651 : Blo 467785 471651 := bstep (se 1 (by rfl) ⟨353738, by rfl⟩ : syracuseStep 471651 = 707477) B707477
theorem B471667 : Blo 467785 471667 := bstep (se 1 (by rfl) ⟨353750, by rfl⟩ : syracuseStep 471667 = 707501) B707501
theorem B635521 : Blo 467785 635521 := bstep (se 2 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 635521 = 476641) B476641
theorem B471683 : Blo 467785 471683 := bstep (se 1 (by rfl) ⟨353762, by rfl⟩ : syracuseStep 471683 = 707525) B707525
theorem B471699 : Blo 467785 471699 := bstep (se 1 (by rfl) ⟨353774, by rfl⟩ : syracuseStep 471699 = 707549) B707549
theorem B471715 : Blo 467785 471715 := bstep (se 1 (by rfl) ⟨353786, by rfl⟩ : syracuseStep 471715 = 707573) B707573
theorem B471731 : Blo 467785 471731 := bstep (se 1 (by rfl) ⟨353798, by rfl⟩ : syracuseStep 471731 = 707597) B707597
theorem B471747 : Blo 467785 471747 := bstep (se 1 (by rfl) ⟨353810, by rfl⟩ : syracuseStep 471747 = 707621) B707621
theorem B471763 : Blo 467785 471763 := bstep (se 1 (by rfl) ⟨353822, by rfl⟩ : syracuseStep 471763 = 707645) B707645
theorem B471779 : Blo 467785 471779 := bstep (se 1 (by rfl) ⟨353834, by rfl⟩ : syracuseStep 471779 = 707669) B707669
theorem B635683 : Blo 467785 635683 := bstep (se 1 (by rfl) ⟨476762, by rfl⟩ : syracuseStep 635683 = 953525) B953525
theorem B1586033 : Blo 467785 1586033 := bstep (se 2 (by rfl) ⟨594762, by rfl⟩ : syracuseStep 1586033 = 1189525) B1189525
theorem B1782755 : Blo 467785 1782755 := bstep (se 1 (by rfl) ⟨1337066, by rfl⟩ : syracuseStep 1782755 = 2674133) B2674133
theorem B1782769 : Blo 467785 1782769 := bstep (se 2 (by rfl) ⟨668538, by rfl⟩ : syracuseStep 1782769 = 1337077) B1337077
theorem B1127459 : Blo 467785 1127459 := bstep (se 1 (by rfl) ⟨845594, by rfl⟩ : syracuseStep 1127459 = 1691189) B1691189
theorem B635969 : Blo 467785 635969 := bstep (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) B476977
theorem B2372813 : Blo 467785 2372813 := bstep (se 3 (by rfl) ⟨444902, by rfl⟩ : syracuseStep 2372813 = 889805) B889805
theorem B931043 : Blo 467785 931043 := bstep (se 1 (by rfl) ⟨698282, by rfl⟩ : syracuseStep 931043 = 1396565) B1396565
theorem B701681 : Blo 467785 701681 := bstep (se 2 (by rfl) ⟨263130, by rfl⟩ : syracuseStep 701681 = 526261) B526261
theorem B1193201 : Blo 467785 1193201 := bstep (se 2 (by rfl) ⟨447450, by rfl⟩ : syracuseStep 1193201 = 894901) B894901
theorem B701699 : Blo 467785 701699 := bstep (se 1 (by rfl) ⟨526274, by rfl⟩ : syracuseStep 701699 = 1052549) B1052549
theorem B701729 : Blo 467785 701729 := bstep (se 2 (by rfl) ⟨263148, by rfl⟩ : syracuseStep 701729 = 526297) B526297
theorem B1193251 : Blo 467785 1193251 := bstep (se 1 (by rfl) ⟨894938, by rfl⟩ : syracuseStep 1193251 = 1789877) B1789877
theorem B701747 : Blo 467785 701747 := bstep (se 1 (by rfl) ⟨526310, by rfl⟩ : syracuseStep 701747 = 1052621) B1052621
theorem B701777 : Blo 467785 701777 := bstep (se 2 (by rfl) ⟨263166, by rfl⟩ : syracuseStep 701777 = 526333) B526333
theorem B701795 : Blo 467785 701795 := bstep (se 1 (by rfl) ⟨526346, by rfl⟩ : syracuseStep 701795 = 1052693) B1052693
theorem B5715299 : Blo 467785 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B701825 : Blo 467785 701825 := bstep (se 2 (by rfl) ⟨263184, by rfl⟩ : syracuseStep 701825 = 526369) B526369
theorem B1586573 : Blo 467785 1586573 := bstep (se 3 (by rfl) ⟨297482, by rfl⟩ : syracuseStep 1586573 = 594965) B594965
theorem B701843 : Blo 467785 701843 := bstep (se 1 (by rfl) ⟨526382, by rfl⟩ : syracuseStep 701843 = 1052765) B1052765
theorem B701873 : Blo 467785 701873 := bstep (se 2 (by rfl) ⟨263202, by rfl⟩ : syracuseStep 701873 = 526405) B526405
theorem B1193393 : Blo 467785 1193393 := bstep (se 2 (by rfl) ⟨447522, by rfl⟩ : syracuseStep 1193393 = 895045) B895045
theorem B701891 : Blo 467785 701891 := bstep (se 1 (by rfl) ⟨526418, by rfl⟩ : syracuseStep 701891 = 1052837) B1052837
theorem B1586627 : Blo 467785 1586627 := bstep (se 1 (by rfl) ⟨1189970, by rfl⟩ : syracuseStep 1586627 = 2379941) B2379941
theorem B701921 : Blo 467785 701921 := bstep (se 2 (by rfl) ⟨263220, by rfl⟩ : syracuseStep 701921 = 526441) B526441
theorem B701939 : Blo 467785 701939 := bstep (se 1 (by rfl) ⟨526454, by rfl⟩ : syracuseStep 701939 = 1052909) B1052909
theorem B701969 : Blo 467785 701969 := bstep (se 2 (by rfl) ⟨263238, by rfl⟩ : syracuseStep 701969 = 526477) B526477
theorem B669217 : Blo 467785 669217 := bstep (se 2 (by rfl) ⟨250956, by rfl⟩ : syracuseStep 669217 = 501913) B501913
theorem B701987 : Blo 467785 701987 := bstep (se 1 (by rfl) ⟨526490, by rfl⟩ : syracuseStep 701987 = 1052981) B1052981
theorem B702017 : Blo 467785 702017 := bstep (se 2 (by rfl) ⟨263256, by rfl⟩ : syracuseStep 702017 = 526513) B526513
theorem B702035 : Blo 467785 702035 := bstep (se 1 (by rfl) ⟨526526, by rfl⟩ : syracuseStep 702035 = 1053053) B1053053
theorem B1390189 : Blo 467785 1390189 := bstep (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) B521321
theorem B702065 : Blo 467785 702065 := bstep (se 2 (by rfl) ⟨263274, by rfl⟩ : syracuseStep 702065 = 526549) B526549
theorem B669313 : Blo 467785 669313 := bstep (se 2 (by rfl) ⟨250992, by rfl⟩ : syracuseStep 669313 = 501985) B501985
theorem B702083 : Blo 467785 702083 := bstep (se 1 (by rfl) ⟨526562, by rfl⟩ : syracuseStep 702083 = 1053125) B1053125
theorem B800417 : Blo 467785 800417 := bstep (se 2 (by rfl) ⟨300156, by rfl⟩ : syracuseStep 800417 = 600313) B600313
theorem B702113 : Blo 467785 702113 := bstep (se 2 (by rfl) ⟨263292, by rfl⟩ : syracuseStep 702113 = 526585) B526585
theorem B702131 : Blo 467785 702131 := bstep (se 1 (by rfl) ⟨526598, by rfl⟩ : syracuseStep 702131 = 1053197) B1053197
theorem B702161 : Blo 467785 702161 := bstep (se 2 (by rfl) ⟨263310, by rfl⟩ : syracuseStep 702161 = 526621) B526621
theorem B1586897 : Blo 467785 1586897 := bstep (se 2 (by rfl) ⟨595086, by rfl⟩ : syracuseStep 1586897 = 1190173) B1190173
theorem B702179 : Blo 467785 702179 := bstep (se 1 (by rfl) ⟨526634, by rfl⟩ : syracuseStep 702179 = 1053269) B1053269
theorem B702209 : Blo 467785 702209 := bstep (se 2 (by rfl) ⟨263328, by rfl⟩ : syracuseStep 702209 = 526657) B526657
theorem B2668301 : Blo 467785 2668301 := bstep (se 3 (by rfl) ⟨500306, by rfl⟩ : syracuseStep 2668301 = 1000613) B1000613
theorem B702227 : Blo 467785 702227 := bstep (se 1 (by rfl) ⟨526670, by rfl⟩ : syracuseStep 702227 = 1053341) B1053341
theorem B2406179 : Blo 467785 2406179 := bstep (se 1 (by rfl) ⟨1804634, by rfl⟩ : syracuseStep 2406179 = 3609269) B3609269
theorem B702257 : Blo 467785 702257 := bstep (se 2 (by rfl) ⟨263346, by rfl⟩ : syracuseStep 702257 = 526693) B526693
theorem B702275 : Blo 467785 702275 := bstep (se 1 (by rfl) ⟨526706, by rfl⟩ : syracuseStep 702275 = 1053413) B1053413
theorem B702305 : Blo 467785 702305 := bstep (se 2 (by rfl) ⟨263364, by rfl⟩ : syracuseStep 702305 = 526729) B526729
theorem B1128305 : Blo 467785 1128305 := bstep (se 2 (by rfl) ⟨423114, by rfl⟩ : syracuseStep 1128305 = 846229) B846229
theorem B702323 : Blo 467785 702323 := bstep (se 1 (by rfl) ⟨526742, by rfl⟩ : syracuseStep 702323 = 1053485) B1053485
theorem B702353 : Blo 467785 702353 := bstep (se 2 (by rfl) ⟨263382, by rfl⟩ : syracuseStep 702353 = 526765) B526765
theorem B702371 : Blo 467785 702371 := bstep (se 1 (by rfl) ⟨526778, by rfl⟩ : syracuseStep 702371 = 1053557) B1053557
theorem B702401 : Blo 467785 702401 := bstep (se 2 (by rfl) ⟨263400, by rfl⟩ : syracuseStep 702401 = 526801) B526801
theorem B702419 : Blo 467785 702419 := bstep (se 1 (by rfl) ⟨526814, by rfl⟩ : syracuseStep 702419 = 1053629) B1053629
theorem B702449 : Blo 467785 702449 := bstep (se 2 (by rfl) ⟨263418, by rfl⟩ : syracuseStep 702449 = 526837) B526837
theorem B702467 : Blo 467785 702467 := bstep (se 1 (by rfl) ⟨526850, by rfl⟩ : syracuseStep 702467 = 1053701) B1053701
theorem B11548693 : Blo 467785 11548693 := bstep (se 6 (by rfl) ⟨270672, by rfl⟩ : syracuseStep 11548693 = 541345) B541345
theorem B702497 : Blo 467785 702497 := bstep (se 2 (by rfl) ⟨263436, by rfl⟩ : syracuseStep 702497 = 526873) B526873
theorem B702515 : Blo 467785 702515 := bstep (se 1 (by rfl) ⟨526886, by rfl⟩ : syracuseStep 702515 = 1053773) B1053773
theorem B702545 : Blo 467785 702545 := bstep (se 2 (by rfl) ⟨263454, by rfl⟩ : syracuseStep 702545 = 526909) B526909
theorem B702563 : Blo 467785 702563 := bstep (se 1 (by rfl) ⟨526922, by rfl⟩ : syracuseStep 702563 = 1053845) B1053845
theorem B669809 : Blo 467785 669809 := bstep (se 2 (by rfl) ⟨251178, by rfl⟩ : syracuseStep 669809 = 502357) B502357
theorem B702593 : Blo 467785 702593 := bstep (se 2 (by rfl) ⟨263472, by rfl⟩ : syracuseStep 702593 = 526945) B526945
theorem B702611 : Blo 467785 702611 := bstep (se 1 (by rfl) ⟨526958, by rfl⟩ : syracuseStep 702611 = 1053917) B1053917
theorem B702641 : Blo 467785 702641 := bstep (se 2 (by rfl) ⟨263490, by rfl⟩ : syracuseStep 702641 = 526981) B526981
theorem B702659 : Blo 467785 702659 := bstep (se 1 (by rfl) ⟨526994, by rfl⟩ : syracuseStep 702659 = 1053989) B1053989
theorem B702689 : Blo 467785 702689 := bstep (se 2 (by rfl) ⟨263508, by rfl⟩ : syracuseStep 702689 = 527017) B527017
theorem B1587437 : Blo 467785 1587437 := bstep (se 3 (by rfl) ⟨297644, by rfl⟩ : syracuseStep 1587437 = 595289) B595289
theorem B702707 : Blo 467785 702707 := bstep (se 1 (by rfl) ⟨527030, by rfl⟩ : syracuseStep 702707 = 1054061) B1054061
theorem B702737 : Blo 467785 702737 := bstep (se 2 (by rfl) ⟨263526, by rfl⟩ : syracuseStep 702737 = 527053) B527053
theorem B702755 : Blo 467785 702755 := bstep (se 1 (by rfl) ⟨527066, by rfl⟩ : syracuseStep 702755 = 1054133) B1054133
theorem B1587491 : Blo 467785 1587491 := bstep (se 1 (by rfl) ⟨1190618, by rfl⟩ : syracuseStep 1587491 = 2381237) B2381237
theorem B702785 : Blo 467785 702785 := bstep (se 2 (by rfl) ⟨263544, by rfl⟩ : syracuseStep 702785 = 527089) B527089
theorem B702803 : Blo 467785 702803 := bstep (se 1 (by rfl) ⟨527102, by rfl⟩ : syracuseStep 702803 = 1054205) B1054205
theorem B702833 : Blo 467785 702833 := bstep (se 2 (by rfl) ⟨263562, by rfl⟩ : syracuseStep 702833 = 527125) B527125
theorem B702851 : Blo 467785 702851 := bstep (se 1 (by rfl) ⟨527138, by rfl⟩ : syracuseStep 702851 = 1054277) B1054277
theorem B702881 : Blo 467785 702881 := bstep (se 2 (by rfl) ⟨263580, by rfl⟩ : syracuseStep 702881 = 527161) B527161
theorem B1784227 : Blo 467785 1784227 := bstep (se 1 (by rfl) ⟨1338170, by rfl⟩ : syracuseStep 1784227 = 2676341) B2676341
theorem B702899 : Blo 467785 702899 := bstep (se 1 (by rfl) ⟨527174, by rfl⟩ : syracuseStep 702899 = 1054349) B1054349
theorem B702929 : Blo 467785 702929 := bstep (se 2 (by rfl) ⟨263598, by rfl⟩ : syracuseStep 702929 = 527197) B527197
theorem B702947 : Blo 467785 702947 := bstep (se 1 (by rfl) ⟨527210, by rfl⟩ : syracuseStep 702947 = 1054421) B1054421
theorem B702977 : Blo 467785 702977 := bstep (se 2 (by rfl) ⟨263616, by rfl⟩ : syracuseStep 702977 = 527233) B527233
theorem B702995 : Blo 467785 702995 := bstep (se 1 (by rfl) ⟨527246, by rfl⟩ : syracuseStep 702995 = 1054493) B1054493
theorem B703025 : Blo 467785 703025 := bstep (se 2 (by rfl) ⟨263634, by rfl⟩ : syracuseStep 703025 = 527269) B527269
theorem B1587761 : Blo 467785 1587761 := bstep (se 2 (by rfl) ⟨595410, by rfl⟩ : syracuseStep 1587761 = 1190821) B1190821
theorem B703043 : Blo 467785 703043 := bstep (se 1 (by rfl) ⟨527282, by rfl⟩ : syracuseStep 703043 = 1054565) B1054565
theorem B3226189 : Blo 467785 3226189 := bstep (se 3 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 3226189 = 1209821) B1209821
theorem B965201 : Blo 467785 965201 := bstep (se 2 (by rfl) ⟨361950, by rfl⟩ : syracuseStep 965201 = 723901) B723901
theorem B703073 : Blo 467785 703073 := bstep (se 2 (by rfl) ⟨263652, by rfl⟩ : syracuseStep 703073 = 527305) B527305
theorem B4274801 : Blo 467785 4274801 := bstep (se 2 (by rfl) ⟨1603050, by rfl⟩ : syracuseStep 4274801 = 3206101) B3206101
theorem B703091 : Blo 467785 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B703121 : Blo 467785 703121 := bstep (se 2 (by rfl) ⟨263670, by rfl⟩ : syracuseStep 703121 = 527341) B527341
theorem B703139 : Blo 467785 703139 := bstep (se 1 (by rfl) ⟨527354, by rfl⟩ : syracuseStep 703139 = 1054709) B1054709
theorem B2669233 : Blo 467785 2669233 := bstep (se 2 (by rfl) ⟨1000962, by rfl⟩ : syracuseStep 2669233 = 2001925) B2001925
theorem B703169 : Blo 467785 703169 := bstep (se 2 (by rfl) ⟨263688, by rfl⟩ : syracuseStep 703169 = 527377) B527377
theorem B506579 : Blo 467785 506579 := bstep (se 1 (by rfl) ⟨379934, by rfl⟩ : syracuseStep 506579 = 759869) B759869
theorem B703187 : Blo 467785 703187 := bstep (se 1 (by rfl) ⟨527390, by rfl⟩ : syracuseStep 703187 = 1054781) B1054781
theorem B703217 : Blo 467785 703217 := bstep (se 2 (by rfl) ⟨263706, by rfl⟩ : syracuseStep 703217 = 527413) B527413
theorem B703235 : Blo 467785 703235 := bstep (se 1 (by rfl) ⟨527426, by rfl⟩ : syracuseStep 703235 = 1054853) B1054853
theorem B703265 : Blo 467785 703265 := bstep (se 2 (by rfl) ⟨263724, by rfl⟩ : syracuseStep 703265 = 527449) B527449
theorem B703283 : Blo 467785 703283 := bstep (se 1 (by rfl) ⟨527462, by rfl⟩ : syracuseStep 703283 = 1054925) B1054925
theorem B3554117 : Blo 467785 3554117 := bstep (se 4 (by rfl) ⟨333198, by rfl⟩ : syracuseStep 3554117 = 666397) B666397
theorem B4275013 : Blo 467785 4275013 := bstep (se 4 (by rfl) ⟨400782, by rfl⟩ : syracuseStep 4275013 = 801565) B801565
theorem B703313 : Blo 467785 703313 := bstep (se 2 (by rfl) ⟨263742, by rfl⟩ : syracuseStep 703313 = 527485) B527485
theorem B703331 : Blo 467785 703331 := bstep (se 1 (by rfl) ⟨527498, by rfl⟩ : syracuseStep 703331 = 1054997) B1054997
theorem B703361 : Blo 467785 703361 := bstep (se 2 (by rfl) ⟨263760, by rfl⟩ : syracuseStep 703361 = 527521) B527521
theorem B703379 : Blo 467785 703379 := bstep (se 1 (by rfl) ⟨527534, by rfl⟩ : syracuseStep 703379 = 1055069) B1055069
theorem B703409 : Blo 467785 703409 := bstep (se 2 (by rfl) ⟨263778, by rfl⟩ : syracuseStep 703409 = 527557) B527557
theorem B703427 : Blo 467785 703427 := bstep (se 1 (by rfl) ⟨527570, by rfl⟩ : syracuseStep 703427 = 1055141) B1055141
theorem B670675 : Blo 467785 670675 := bstep (se 1 (by rfl) ⟨503006, by rfl⟩ : syracuseStep 670675 = 1006013) B1006013
theorem B703457 : Blo 467785 703457 := bstep (se 2 (by rfl) ⟨263796, by rfl⟩ : syracuseStep 703457 = 527593) B527593
theorem B703475 : Blo 467785 703475 := bstep (se 1 (by rfl) ⟨527606, by rfl⟩ : syracuseStep 703475 = 1055213) B1055213
theorem B703505 : Blo 467785 703505 := bstep (se 2 (by rfl) ⟨263814, by rfl⟩ : syracuseStep 703505 = 527629) B527629
theorem B703523 : Blo 467785 703523 := bstep (se 1 (by rfl) ⟨527642, by rfl⟩ : syracuseStep 703523 = 1055285) B1055285
theorem B670771 : Blo 467785 670771 := bstep (se 1 (by rfl) ⟨503078, by rfl⟩ : syracuseStep 670771 = 1006157) B1006157
theorem B703553 : Blo 467785 703553 := bstep (se 2 (by rfl) ⟨263832, by rfl⟩ : syracuseStep 703553 = 527665) B527665
theorem B1588301 : Blo 467785 1588301 := bstep (se 3 (by rfl) ⟨297806, by rfl⟩ : syracuseStep 1588301 = 595613) B595613
theorem B703571 : Blo 467785 703571 := bstep (se 1 (by rfl) ⟨527678, by rfl⟩ : syracuseStep 703571 = 1055357) B1055357
theorem B703601 : Blo 467785 703601 := bstep (se 2 (by rfl) ⟨263850, by rfl⟩ : syracuseStep 703601 = 527701) B527701
theorem B703619 : Blo 467785 703619 := bstep (se 1 (by rfl) ⟨527714, by rfl⟩ : syracuseStep 703619 = 1055429) B1055429
theorem B1588355 : Blo 467785 1588355 := bstep (se 1 (by rfl) ⟨1191266, by rfl⟩ : syracuseStep 1588355 = 2382533) B2382533
theorem B703649 : Blo 467785 703649 := bstep (se 2 (by rfl) ⟨263868, by rfl⟩ : syracuseStep 703649 = 527737) B527737
theorem B703667 : Blo 467785 703667 := bstep (se 1 (by rfl) ⟨527750, by rfl⟩ : syracuseStep 703667 = 1055501) B1055501
theorem B703697 : Blo 467785 703697 := bstep (se 2 (by rfl) ⟨263886, by rfl⟩ : syracuseStep 703697 = 527773) B527773
theorem B703715 : Blo 467785 703715 := bstep (se 1 (by rfl) ⟨527786, by rfl⟩ : syracuseStep 703715 = 1055573) B1055573
theorem B703745 : Blo 467785 703745 := bstep (se 2 (by rfl) ⟨263904, by rfl⟩ : syracuseStep 703745 = 527809) B527809
theorem B703763 : Blo 467785 703763 := bstep (se 1 (by rfl) ⟨527822, by rfl⟩ : syracuseStep 703763 = 1055645) B1055645
theorem B703793 : Blo 467785 703793 := bstep (se 2 (by rfl) ⟨263922, by rfl⟩ : syracuseStep 703793 = 527845) B527845
theorem B703811 : Blo 467785 703811 := bstep (se 1 (by rfl) ⟨527858, by rfl⟩ : syracuseStep 703811 = 1055717) B1055717
theorem B703841 : Blo 467785 703841 := bstep (se 2 (by rfl) ⟨263940, by rfl⟩ : syracuseStep 703841 = 527881) B527881
theorem B703859 : Blo 467785 703859 := bstep (se 1 (by rfl) ⟨527894, by rfl⟩ : syracuseStep 703859 = 1055789) B1055789
theorem B703889 : Blo 467785 703889 := bstep (se 2 (by rfl) ⟨263958, by rfl⟩ : syracuseStep 703889 = 527917) B527917
theorem B1588625 : Blo 467785 1588625 := bstep (se 2 (by rfl) ⟨595734, by rfl⟩ : syracuseStep 1588625 = 1191469) B1191469
theorem B703907 : Blo 467785 703907 := bstep (se 1 (by rfl) ⟨527930, by rfl⟩ : syracuseStep 703907 = 1055861) B1055861
theorem B703937 : Blo 467785 703937 := bstep (se 2 (by rfl) ⟨263976, by rfl⟩ : syracuseStep 703937 = 527953) B527953
theorem B703955 : Blo 467785 703955 := bstep (se 1 (by rfl) ⟨527966, by rfl⟩ : syracuseStep 703955 = 1055933) B1055933
theorem B703985 : Blo 467785 703985 := bstep (se 2 (by rfl) ⟨263994, by rfl⟩ : syracuseStep 703985 = 527989) B527989
theorem B704003 : Blo 467785 704003 := bstep (se 1 (by rfl) ⟨528002, by rfl⟩ : syracuseStep 704003 = 1056005) B1056005
theorem B704033 : Blo 467785 704033 := bstep (se 2 (by rfl) ⟨264012, by rfl⟩ : syracuseStep 704033 = 528025) B528025
theorem B671267 : Blo 467785 671267 := bstep (se 1 (by rfl) ⟨503450, by rfl⟩ : syracuseStep 671267 = 1006901) B1006901
theorem B704051 : Blo 467785 704051 := bstep (se 1 (by rfl) ⟨528038, by rfl⟩ : syracuseStep 704051 = 1056077) B1056077
theorem B704081 : Blo 467785 704081 := bstep (se 2 (by rfl) ⟨264030, by rfl⟩ : syracuseStep 704081 = 528061) B528061
theorem B704099 : Blo 467785 704099 := bstep (se 1 (by rfl) ⟨528074, by rfl⟩ : syracuseStep 704099 = 1056149) B1056149
theorem B704129 : Blo 467785 704129 := bstep (se 2 (by rfl) ⟨264048, by rfl⟩ : syracuseStep 704129 = 528097) B528097
theorem B704147 : Blo 467785 704147 := bstep (se 1 (by rfl) ⟨528110, by rfl⟩ : syracuseStep 704147 = 1056221) B1056221
theorem B704177 : Blo 467785 704177 := bstep (se 2 (by rfl) ⟨264066, by rfl⟩ : syracuseStep 704177 = 528133) B528133
theorem B704195 : Blo 467785 704195 := bstep (se 1 (by rfl) ⟨528146, by rfl⟩ : syracuseStep 704195 = 1056293) B1056293
theorem B704225 : Blo 467785 704225 := bstep (se 2 (by rfl) ⟨264084, by rfl⟩ : syracuseStep 704225 = 528169) B528169
theorem B704243 : Blo 467785 704243 := bstep (se 1 (by rfl) ⟨528182, by rfl⟩ : syracuseStep 704243 = 1056365) B1056365
theorem B704273 : Blo 467785 704273 := bstep (se 2 (by rfl) ⟨264102, by rfl⟩ : syracuseStep 704273 = 528205) B528205
theorem B704291 : Blo 467785 704291 := bstep (se 1 (by rfl) ⟨528218, by rfl⟩ : syracuseStep 704291 = 1056437) B1056437
theorem B2539313 : Blo 467785 2539313 := bstep (se 2 (by rfl) ⟨952242, by rfl⟩ : syracuseStep 2539313 = 1904485) B1904485
theorem B704321 : Blo 467785 704321 := bstep (se 2 (by rfl) ⟨264120, by rfl⟩ : syracuseStep 704321 = 528241) B528241
theorem B704339 : Blo 467785 704339 := bstep (se 1 (by rfl) ⟨528254, by rfl⟩ : syracuseStep 704339 = 1056509) B1056509
theorem B704369 : Blo 467785 704369 := bstep (se 2 (by rfl) ⟨264138, by rfl⟩ : syracuseStep 704369 = 528277) B528277
theorem B704387 : Blo 467785 704387 := bstep (se 1 (by rfl) ⟨528290, by rfl⟩ : syracuseStep 704387 = 1056581) B1056581
theorem B2015117 : Blo 467785 2015117 := bstep (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) B755669
theorem B704417 : Blo 467785 704417 := bstep (se 2 (by rfl) ⟨264156, by rfl⟩ : syracuseStep 704417 = 528313) B528313
theorem B1589165 : Blo 467785 1589165 := bstep (se 3 (by rfl) ⟨297968, by rfl⟩ : syracuseStep 1589165 = 595937) B595937
theorem B2539441 : Blo 467785 2539441 := bstep (se 2 (by rfl) ⟨952290, by rfl⟩ : syracuseStep 2539441 = 1904581) B1904581
theorem B704435 : Blo 467785 704435 := bstep (se 1 (by rfl) ⟨528326, by rfl⟩ : syracuseStep 704435 = 1056653) B1056653
theorem B1425347 : Blo 467785 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B704465 : Blo 467785 704465 := bstep (se 2 (by rfl) ⟨264174, by rfl⟩ : syracuseStep 704465 = 528349) B528349
theorem B704483 : Blo 467785 704483 := bstep (se 1 (by rfl) ⟨528362, by rfl⟩ : syracuseStep 704483 = 1056725) B1056725
theorem B1589219 : Blo 467785 1589219 := bstep (se 1 (by rfl) ⟨1191914, by rfl⟩ : syracuseStep 1589219 = 2383829) B2383829
theorem B2572273 : Blo 467785 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B704513 : Blo 467785 704513 := bstep (se 2 (by rfl) ⟨264192, by rfl⟩ : syracuseStep 704513 = 528385) B528385
theorem B704531 : Blo 467785 704531 := bstep (se 1 (by rfl) ⟨528398, by rfl⟩ : syracuseStep 704531 = 1056797) B1056797
theorem B2375729 : Blo 467785 2375729 := bstep (se 2 (by rfl) ⟨890898, by rfl⟩ : syracuseStep 2375729 = 1781797) B1781797
theorem B704561 : Blo 467785 704561 := bstep (se 2 (by rfl) ⟨264210, by rfl⟩ : syracuseStep 704561 = 528421) B528421
theorem B704579 : Blo 467785 704579 := bstep (se 1 (by rfl) ⟨528434, by rfl⟩ : syracuseStep 704579 = 1056869) B1056869
theorem B704609 : Blo 467785 704609 := bstep (se 2 (by rfl) ⟨264228, by rfl⟩ : syracuseStep 704609 = 528457) B528457
theorem B2670691 : Blo 467785 2670691 := bstep (se 1 (by rfl) ⟨2003018, by rfl⟩ : syracuseStep 2670691 = 4006037) B4006037
theorem B704627 : Blo 467785 704627 := bstep (se 1 (by rfl) ⟨528470, by rfl⟩ : syracuseStep 704627 = 1056941) B1056941
theorem B704657 : Blo 467785 704657 := bstep (se 2 (by rfl) ⟨264246, by rfl⟩ : syracuseStep 704657 = 528493) B528493
theorem B704675 : Blo 467785 704675 := bstep (se 1 (by rfl) ⟨528506, by rfl⟩ : syracuseStep 704675 = 1057013) B1057013
theorem B5062837 : Blo 467785 5062837 := bstep (se 5 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 5062837 = 474641) B474641
theorem B704705 : Blo 467785 704705 := bstep (se 2 (by rfl) ⟨264264, by rfl⟩ : syracuseStep 704705 = 528529) B528529
theorem B704723 : Blo 467785 704723 := bstep (se 1 (by rfl) ⟨528542, by rfl⟩ : syracuseStep 704723 = 1057085) B1057085
theorem B704753 : Blo 467785 704753 := bstep (se 2 (by rfl) ⟨264282, by rfl⟩ : syracuseStep 704753 = 528565) B528565
theorem B1589489 : Blo 467785 1589489 := bstep (se 2 (by rfl) ⟨596058, by rfl⟩ : syracuseStep 1589489 = 1192117) B1192117
theorem B704771 : Blo 467785 704771 := bstep (se 1 (by rfl) ⟨528578, by rfl⟩ : syracuseStep 704771 = 1057157) B1057157
theorem B704801 : Blo 467785 704801 := bstep (se 2 (by rfl) ⟨264300, by rfl⟩ : syracuseStep 704801 = 528601) B528601
theorem B704819 : Blo 467785 704819 := bstep (se 1 (by rfl) ⟨528614, by rfl⟩ : syracuseStep 704819 = 1057229) B1057229
theorem B704849 : Blo 467785 704849 := bstep (se 2 (by rfl) ⟨264318, by rfl⟩ : syracuseStep 704849 = 528637) B528637
theorem B704867 : Blo 467785 704867 := bstep (se 1 (by rfl) ⟨528650, by rfl⟩ : syracuseStep 704867 = 1057301) B1057301
theorem B999793 : Blo 467785 999793 := bstep (se 2 (by rfl) ⟨374922, by rfl⟩ : syracuseStep 999793 = 749845) B749845
theorem B704897 : Blo 467785 704897 := bstep (se 2 (by rfl) ⟨264336, by rfl⟩ : syracuseStep 704897 = 528673) B528673
theorem B5718413 : Blo 467785 5718413 := bstep (se 3 (by rfl) ⟨1072202, by rfl⟩ : syracuseStep 5718413 = 2144405) B2144405
theorem B704915 : Blo 467785 704915 := bstep (se 1 (by rfl) ⟨528686, by rfl⟩ : syracuseStep 704915 = 1057373) B1057373
theorem B704945 : Blo 467785 704945 := bstep (se 2 (by rfl) ⟨264354, by rfl⟩ : syracuseStep 704945 = 528709) B528709
theorem B704963 : Blo 467785 704963 := bstep (se 1 (by rfl) ⟨528722, by rfl⟩ : syracuseStep 704963 = 1057445) B1057445
theorem B704993 : Blo 467785 704993 := bstep (se 2 (by rfl) ⟨264372, by rfl⟩ : syracuseStep 704993 = 528745) B528745
theorem B705011 : Blo 467785 705011 := bstep (se 1 (by rfl) ⟨528758, by rfl⟩ : syracuseStep 705011 = 1057517) B1057517
theorem B705041 : Blo 467785 705041 := bstep (se 2 (by rfl) ⟨264390, by rfl⟩ : syracuseStep 705041 = 528781) B528781
theorem B705059 : Blo 467785 705059 := bstep (se 1 (by rfl) ⟨528794, by rfl⟩ : syracuseStep 705059 = 1057589) B1057589
theorem B705089 : Blo 467785 705089 := bstep (se 2 (by rfl) ⟨264408, by rfl⟩ : syracuseStep 705089 = 528817) B528817
theorem B5358149 : Blo 467785 5358149 := bstep (se 4 (by rfl) ⟨502326, by rfl⟩ : syracuseStep 5358149 = 1004653) B1004653
theorem B1786445 : Blo 467785 1786445 := bstep (se 3 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 1786445 = 669917) B669917
theorem B705107 : Blo 467785 705107 := bstep (se 1 (by rfl) ⟨528830, by rfl⟩ : syracuseStep 705107 = 1057661) B1057661
theorem B2671217 : Blo 467785 2671217 := bstep (se 2 (by rfl) ⟨1001706, by rfl⟩ : syracuseStep 2671217 = 2003413) B2003413
theorem B705137 : Blo 467785 705137 := bstep (se 2 (by rfl) ⟨264426, by rfl⟩ : syracuseStep 705137 = 528853) B528853
theorem B705155 : Blo 467785 705155 := bstep (se 1 (by rfl) ⟨528866, by rfl⟩ : syracuseStep 705155 = 1057733) B1057733
theorem B705185 : Blo 467785 705185 := bstep (se 2 (by rfl) ⟨264444, by rfl⟩ : syracuseStep 705185 = 528889) B528889
theorem B705203 : Blo 467785 705203 := bstep (se 1 (by rfl) ⟨528902, by rfl⟩ : syracuseStep 705203 = 1057805) B1057805
theorem B803537 : Blo 467785 803537 := bstep (se 2 (by rfl) ⟨301326, by rfl⟩ : syracuseStep 803537 = 602653) B602653
theorem B705233 : Blo 467785 705233 := bstep (se 2 (by rfl) ⟨264462, by rfl⟩ : syracuseStep 705233 = 528925) B528925
theorem B705251 : Blo 467785 705251 := bstep (se 1 (by rfl) ⟨528938, by rfl⟩ : syracuseStep 705251 = 1057877) B1057877
theorem B4801265 : Blo 467785 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B705281 : Blo 467785 705281 := bstep (se 2 (by rfl) ⟨264480, by rfl⟩ : syracuseStep 705281 = 528961) B528961
theorem B2999045 : Blo 467785 2999045 := bstep (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) B562321
theorem B1590029 : Blo 467785 1590029 := bstep (se 3 (by rfl) ⟨298130, by rfl⟩ : syracuseStep 1590029 = 596261) B596261
theorem B705299 : Blo 467785 705299 := bstep (se 1 (by rfl) ⟨528974, by rfl⟩ : syracuseStep 705299 = 1057949) B1057949
theorem B705329 : Blo 467785 705329 := bstep (se 2 (by rfl) ⟨264498, by rfl⟩ : syracuseStep 705329 = 528997) B528997
theorem B705347 : Blo 467785 705347 := bstep (se 1 (by rfl) ⟨529010, by rfl⟩ : syracuseStep 705347 = 1058021) B1058021
theorem B1590083 : Blo 467785 1590083 := bstep (se 1 (by rfl) ⟨1192562, by rfl⟩ : syracuseStep 1590083 = 2385125) B2385125
theorem B2409293 : Blo 467785 2409293 := bstep (se 3 (by rfl) ⟨451742, by rfl⟩ : syracuseStep 2409293 = 903485) B903485
theorem B705377 : Blo 467785 705377 := bstep (se 2 (by rfl) ⟨264516, by rfl⟩ : syracuseStep 705377 = 529033) B529033
theorem B1622897 : Blo 467785 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B705395 : Blo 467785 705395 := bstep (se 1 (by rfl) ⟨529046, by rfl⟩ : syracuseStep 705395 = 1058093) B1058093
theorem B705425 : Blo 467785 705425 := bstep (se 2 (by rfl) ⟨264534, by rfl⟩ : syracuseStep 705425 = 529069) B529069
theorem B705443 : Blo 467785 705443 := bstep (se 1 (by rfl) ⟨529082, by rfl⟩ : syracuseStep 705443 = 1058165) B1058165
theorem B705473 : Blo 467785 705473 := bstep (se 2 (by rfl) ⟨264552, by rfl⟩ : syracuseStep 705473 = 529105) B529105
theorem B705491 : Blo 467785 705491 := bstep (se 1 (by rfl) ⟨529118, by rfl⟩ : syracuseStep 705491 = 1058237) B1058237
theorem B705521 : Blo 467785 705521 := bstep (se 2 (by rfl) ⟨264570, by rfl⟩ : syracuseStep 705521 = 529141) B529141
theorem B1000451 : Blo 467785 1000451 := bstep (se 1 (by rfl) ⟨750338, by rfl⟩ : syracuseStep 1000451 = 1500677) B1500677
theorem B705539 : Blo 467785 705539 := bstep (se 1 (by rfl) ⟨529154, by rfl⟩ : syracuseStep 705539 = 1058309) B1058309
theorem B705569 : Blo 467785 705569 := bstep (se 2 (by rfl) ⟨264588, by rfl⟩ : syracuseStep 705569 = 529177) B529177
theorem B705587 : Blo 467785 705587 := bstep (se 1 (by rfl) ⟨529190, by rfl⟩ : syracuseStep 705587 = 1058381) B1058381
theorem B902225 : Blo 467785 902225 := bstep (se 2 (by rfl) ⟨338334, by rfl⟩ : syracuseStep 902225 = 676669) B676669
theorem B705617 : Blo 467785 705617 := bstep (se 2 (by rfl) ⟨264606, by rfl⟩ : syracuseStep 705617 = 529213) B529213
theorem B1590353 : Blo 467785 1590353 := bstep (se 2 (by rfl) ⟨596382, by rfl⟩ : syracuseStep 1590353 = 1192765) B1192765
theorem B705635 : Blo 467785 705635 := bstep (se 1 (by rfl) ⟨529226, by rfl⟩ : syracuseStep 705635 = 1058453) B1058453
theorem B1131619 : Blo 467785 1131619 := bstep (se 1 (by rfl) ⟨848714, by rfl⟩ : syracuseStep 1131619 = 1697429) B1697429
theorem B705665 : Blo 467785 705665 := bstep (se 2 (by rfl) ⟨264624, by rfl⟩ : syracuseStep 705665 = 529249) B529249
theorem B705683 : Blo 467785 705683 := bstep (se 1 (by rfl) ⟨529262, by rfl⟩ : syracuseStep 705683 = 1058525) B1058525
theorem B705713 : Blo 467785 705713 := bstep (se 2 (by rfl) ⟨264642, by rfl⟩ : syracuseStep 705713 = 529285) B529285
theorem B705731 : Blo 467785 705731 := bstep (se 1 (by rfl) ⟨529298, by rfl⟩ : syracuseStep 705731 = 1058597) B1058597
theorem B705761 : Blo 467785 705761 := bstep (se 2 (by rfl) ⟨264660, by rfl⟩ : syracuseStep 705761 = 529321) B529321
theorem B705779 : Blo 467785 705779 := bstep (se 1 (by rfl) ⟨529334, by rfl⟩ : syracuseStep 705779 = 1058669) B1058669
theorem B705809 : Blo 467785 705809 := bstep (se 2 (by rfl) ⟨264678, by rfl⟩ : syracuseStep 705809 = 529357) B529357
theorem B705827 : Blo 467785 705827 := bstep (se 1 (by rfl) ⟨529370, by rfl⟩ : syracuseStep 705827 = 1058741) B1058741
theorem B705857 : Blo 467785 705857 := bstep (se 2 (by rfl) ⟨264696, by rfl⟩ : syracuseStep 705857 = 529393) B529393
theorem B705875 : Blo 467785 705875 := bstep (se 1 (by rfl) ⟨529406, by rfl⟩ : syracuseStep 705875 = 1058813) B1058813
theorem B705905 : Blo 467785 705905 := bstep (se 2 (by rfl) ⟨264714, by rfl⟩ : syracuseStep 705905 = 529429) B529429
theorem B1131889 : Blo 467785 1131889 := bstep (se 2 (by rfl) ⟨424458, by rfl⟩ : syracuseStep 1131889 = 848917) B848917
theorem B705923 : Blo 467785 705923 := bstep (se 1 (by rfl) ⟨529442, by rfl⟩ : syracuseStep 705923 = 1058885) B1058885
theorem B705953 : Blo 467785 705953 := bstep (se 2 (by rfl) ⟨264732, by rfl⟩ : syracuseStep 705953 = 529465) B529465
theorem B705971 : Blo 467785 705971 := bstep (se 1 (by rfl) ⟨529478, by rfl⟩ : syracuseStep 705971 = 1058957) B1058957
theorem B706001 : Blo 467785 706001 := bstep (se 2 (by rfl) ⟨264750, by rfl⟩ : syracuseStep 706001 = 529501) B529501
theorem B2377187 : Blo 467785 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B706019 : Blo 467785 706019 := bstep (se 1 (by rfl) ⟨529514, by rfl⟩ : syracuseStep 706019 = 1059029) B1059029
theorem B706049 : Blo 467785 706049 := bstep (se 2 (by rfl) ⟨264768, by rfl⟩ : syracuseStep 706049 = 529537) B529537
theorem B706067 : Blo 467785 706067 := bstep (se 1 (by rfl) ⟨529550, by rfl⟩ : syracuseStep 706067 = 1059101) B1059101
theorem B706097 : Blo 467785 706097 := bstep (se 2 (by rfl) ⟨264786, by rfl⟩ : syracuseStep 706097 = 529573) B529573
theorem B706115 : Blo 467785 706115 := bstep (se 1 (by rfl) ⟨529586, by rfl⟩ : syracuseStep 706115 = 1059173) B1059173
theorem B706145 : Blo 467785 706145 := bstep (se 2 (by rfl) ⟨264804, by rfl⟩ : syracuseStep 706145 = 529609) B529609
theorem B1590893 : Blo 467785 1590893 := bstep (se 3 (by rfl) ⟨298292, by rfl⟩ : syracuseStep 1590893 = 596585) B596585
theorem B706163 : Blo 467785 706163 := bstep (se 1 (by rfl) ⟨529622, by rfl⟩ : syracuseStep 706163 = 1059245) B1059245
theorem B706193 : Blo 467785 706193 := bstep (se 2 (by rfl) ⟨264822, by rfl⟩ : syracuseStep 706193 = 529645) B529645
theorem B706211 : Blo 467785 706211 := bstep (se 1 (by rfl) ⟨529658, by rfl⟩ : syracuseStep 706211 = 1059317) B1059317
theorem B1590947 : Blo 467785 1590947 := bstep (se 1 (by rfl) ⟨1193210, by rfl⟩ : syracuseStep 1590947 = 2386421) B2386421
theorem B706241 : Blo 467785 706241 := bstep (se 2 (by rfl) ⟨264840, by rfl⟩ : syracuseStep 706241 = 529681) B529681
theorem B706259 : Blo 467785 706259 := bstep (se 1 (by rfl) ⟨529694, by rfl⟩ : syracuseStep 706259 = 1059389) B1059389
theorem B706289 : Blo 467785 706289 := bstep (se 2 (by rfl) ⟨264858, by rfl⟩ : syracuseStep 706289 = 529717) B529717
theorem B706307 : Blo 467785 706307 := bstep (se 1 (by rfl) ⟨529730, by rfl⟩ : syracuseStep 706307 = 1059461) B1059461
theorem B706337 : Blo 467785 706337 := bstep (se 2 (by rfl) ⟨264876, by rfl⟩ : syracuseStep 706337 = 529753) B529753
theorem B706355 : Blo 467785 706355 := bstep (se 1 (by rfl) ⟨529766, by rfl⟩ : syracuseStep 706355 = 1059533) B1059533
theorem B1001297 : Blo 467785 1001297 := bstep (se 2 (by rfl) ⟨375486, by rfl⟩ : syracuseStep 1001297 = 750973) B750973
theorem B706385 : Blo 467785 706385 := bstep (se 2 (by rfl) ⟨264894, by rfl⟩ : syracuseStep 706385 = 529789) B529789
theorem B706403 : Blo 467785 706403 := bstep (se 1 (by rfl) ⟨529802, by rfl⟩ : syracuseStep 706403 = 1059605) B1059605
theorem B706433 : Blo 467785 706433 := bstep (se 2 (by rfl) ⟨264912, by rfl⟩ : syracuseStep 706433 = 529825) B529825
theorem B706451 : Blo 467785 706451 := bstep (se 1 (by rfl) ⟨529838, by rfl⟩ : syracuseStep 706451 = 1059677) B1059677
theorem B706481 : Blo 467785 706481 := bstep (se 2 (by rfl) ⟨264930, by rfl⟩ : syracuseStep 706481 = 529861) B529861
theorem B1591217 : Blo 467785 1591217 := bstep (se 2 (by rfl) ⟨596706, by rfl⟩ : syracuseStep 1591217 = 1193413) B1193413
theorem B706499 : Blo 467785 706499 := bstep (se 1 (by rfl) ⟨529874, by rfl⟩ : syracuseStep 706499 = 1059749) B1059749
theorem B706529 : Blo 467785 706529 := bstep (se 2 (by rfl) ⟨264948, by rfl⟩ : syracuseStep 706529 = 529897) B529897
theorem B706547 : Blo 467785 706547 := bstep (se 1 (by rfl) ⟨529910, by rfl⟩ : syracuseStep 706547 = 1059821) B1059821
theorem B706577 : Blo 467785 706577 := bstep (se 2 (by rfl) ⟨264966, by rfl⟩ : syracuseStep 706577 = 529933) B529933
theorem B2672675 : Blo 467785 2672675 := bstep (se 1 (by rfl) ⟨2004506, by rfl⟩ : syracuseStep 2672675 = 4009013) B4009013
theorem B706595 : Blo 467785 706595 := bstep (se 1 (by rfl) ⟨529946, by rfl⟩ : syracuseStep 706595 = 1059893) B1059893
theorem B706625 : Blo 467785 706625 := bstep (se 2 (by rfl) ⟨264984, by rfl⟩ : syracuseStep 706625 = 529969) B529969
theorem B706643 : Blo 467785 706643 := bstep (se 1 (by rfl) ⟨529982, by rfl⟩ : syracuseStep 706643 = 1059965) B1059965
theorem B706673 : Blo 467785 706673 := bstep (se 2 (by rfl) ⟨265002, by rfl⟩ : syracuseStep 706673 = 530005) B530005
theorem B706691 : Blo 467785 706691 := bstep (se 1 (by rfl) ⟨530018, by rfl⟩ : syracuseStep 706691 = 1060037) B1060037
theorem B3393677 : Blo 467785 3393677 := bstep (se 3 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 3393677 = 1272629) B1272629
theorem B706721 : Blo 467785 706721 := bstep (se 2 (by rfl) ⟨265020, by rfl⟩ : syracuseStep 706721 = 530041) B530041
theorem B1427633 : Blo 467785 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B706739 : Blo 467785 706739 := bstep (se 1 (by rfl) ⟨530054, by rfl⟩ : syracuseStep 706739 = 1060109) B1060109
theorem B706769 : Blo 467785 706769 := bstep (se 2 (by rfl) ⟨265038, by rfl⟩ : syracuseStep 706769 = 530077) B530077
theorem B706787 : Blo 467785 706787 := bstep (se 1 (by rfl) ⟨530090, by rfl⟩ : syracuseStep 706787 = 1060181) B1060181
theorem B706817 : Blo 467785 706817 := bstep (se 2 (by rfl) ⟨265056, by rfl⟩ : syracuseStep 706817 = 530113) B530113
theorem B2377997 : Blo 467785 2377997 := bstep (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) B891749
theorem B706835 : Blo 467785 706835 := bstep (se 1 (by rfl) ⟨530126, by rfl⟩ : syracuseStep 706835 = 1060253) B1060253
theorem B706865 : Blo 467785 706865 := bstep (se 2 (by rfl) ⟨265074, by rfl⟩ : syracuseStep 706865 = 530149) B530149
theorem B1132849 : Blo 467785 1132849 := bstep (se 2 (by rfl) ⟨424818, by rfl⟩ : syracuseStep 1132849 = 849637) B849637
theorem B706883 : Blo 467785 706883 := bstep (se 1 (by rfl) ⟨530162, by rfl⟩ : syracuseStep 706883 = 1060325) B1060325
theorem B706913 : Blo 467785 706913 := bstep (se 2 (by rfl) ⟨265092, by rfl⟩ : syracuseStep 706913 = 530185) B530185
theorem B706931 : Blo 467785 706931 := bstep (se 1 (by rfl) ⟨530198, by rfl⟩ : syracuseStep 706931 = 1060397) B1060397
theorem B706961 : Blo 467785 706961 := bstep (se 2 (by rfl) ⟨265110, by rfl⟩ : syracuseStep 706961 = 530221) B530221
theorem B706979 : Blo 467785 706979 := bstep (se 1 (by rfl) ⟨530234, by rfl⟩ : syracuseStep 706979 = 1060469) B1060469
theorem B707009 : Blo 467785 707009 := bstep (se 2 (by rfl) ⟨265128, by rfl⟩ : syracuseStep 707009 = 530257) B530257
theorem B1591757 : Blo 467785 1591757 := bstep (se 3 (by rfl) ⟨298454, by rfl⟩ : syracuseStep 1591757 = 596909) B596909
theorem B707027 : Blo 467785 707027 := bstep (se 1 (by rfl) ⟨530270, by rfl⟩ : syracuseStep 707027 = 1060541) B1060541
theorem B707057 : Blo 467785 707057 := bstep (se 2 (by rfl) ⟨265146, by rfl⟩ : syracuseStep 707057 = 530293) B530293
theorem B707075 : Blo 467785 707075 := bstep (se 1 (by rfl) ⟨530306, by rfl⟩ : syracuseStep 707075 = 1060613) B1060613
theorem B1591811 : Blo 467785 1591811 := bstep (se 1 (by rfl) ⟨1193858, by rfl⟩ : syracuseStep 1591811 = 2387717) B2387717
theorem B707105 : Blo 467785 707105 := bstep (se 2 (by rfl) ⟨265164, by rfl⟩ : syracuseStep 707105 = 530329) B530329
theorem B707123 : Blo 467785 707123 := bstep (se 1 (by rfl) ⟨530342, by rfl⟩ : syracuseStep 707123 = 1060685) B1060685
theorem B707153 : Blo 467785 707153 := bstep (se 2 (by rfl) ⟨265182, by rfl⟩ : syracuseStep 707153 = 530365) B530365
theorem B707171 : Blo 467785 707171 := bstep (se 1 (by rfl) ⟨530378, by rfl⟩ : syracuseStep 707171 = 1060757) B1060757
theorem B707201 : Blo 467785 707201 := bstep (se 2 (by rfl) ⟨265200, by rfl⟩ : syracuseStep 707201 = 530401) B530401
theorem B903811 : Blo 467785 903811 := bstep (se 1 (by rfl) ⟨677858, by rfl⟩ : syracuseStep 903811 = 1355717) B1355717
theorem B707219 : Blo 467785 707219 := bstep (se 1 (by rfl) ⟨530414, by rfl⟩ : syracuseStep 707219 = 1060829) B1060829
theorem B707249 : Blo 467785 707249 := bstep (se 2 (by rfl) ⟨265218, by rfl⟩ : syracuseStep 707249 = 530437) B530437
theorem B707267 : Blo 467785 707267 := bstep (se 1 (by rfl) ⟨530450, by rfl⟩ : syracuseStep 707267 = 1060901) B1060901
theorem B707297 : Blo 467785 707297 := bstep (se 2 (by rfl) ⟨265236, by rfl⟩ : syracuseStep 707297 = 530473) B530473
theorem B707315 : Blo 467785 707315 := bstep (se 1 (by rfl) ⟨530486, by rfl⟩ : syracuseStep 707315 = 1060973) B1060973
theorem B707345 : Blo 467785 707345 := bstep (se 2 (by rfl) ⟨265254, by rfl⟩ : syracuseStep 707345 = 530509) B530509
theorem B1592081 : Blo 467785 1592081 := bstep (se 2 (by rfl) ⟨597030, by rfl⟩ : syracuseStep 1592081 = 1194061) B1194061
theorem B707363 : Blo 467785 707363 := bstep (se 1 (by rfl) ⟨530522, by rfl⟩ : syracuseStep 707363 = 1061045) B1061045
theorem B707393 : Blo 467785 707393 := bstep (se 2 (by rfl) ⟨265272, by rfl⟩ : syracuseStep 707393 = 530545) B530545
theorem B478019 : Blo 467785 478019 := bstep (se 1 (by rfl) ⟨358514, by rfl⟩ : syracuseStep 478019 = 717029) B717029
theorem B707411 : Blo 467785 707411 := bstep (se 1 (by rfl) ⟨530558, by rfl⟩ : syracuseStep 707411 = 1061117) B1061117
theorem B707441 : Blo 467785 707441 := bstep (se 2 (by rfl) ⟨265290, by rfl⟩ : syracuseStep 707441 = 530581) B530581
theorem B707459 : Blo 467785 707459 := bstep (se 1 (by rfl) ⟨530594, by rfl⟩ : syracuseStep 707459 = 1061189) B1061189
theorem B707489 : Blo 467785 707489 := bstep (se 2 (by rfl) ⟨265308, by rfl⟩ : syracuseStep 707489 = 530617) B530617
theorem B707507 : Blo 467785 707507 := bstep (se 1 (by rfl) ⟨530630, by rfl⟩ : syracuseStep 707507 = 1061261) B1061261
theorem B707537 : Blo 467785 707537 := bstep (se 2 (by rfl) ⟨265326, by rfl⟩ : syracuseStep 707537 = 530653) B530653
theorem B707555 : Blo 467785 707555 := bstep (se 1 (by rfl) ⟨530666, by rfl⟩ : syracuseStep 707555 = 1061333) B1061333
theorem B1428461 : Blo 467785 1428461 := bstep (se 3 (by rfl) ⟨267836, by rfl⟩ : syracuseStep 1428461 = 535673) B535673
theorem B707585 : Blo 467785 707585 := bstep (se 2 (by rfl) ⟨265344, by rfl⟩ : syracuseStep 707585 = 530689) B530689
theorem B707603 : Blo 467785 707603 := bstep (se 1 (by rfl) ⟨530702, by rfl⟩ : syracuseStep 707603 = 1061405) B1061405
theorem B707633 : Blo 467785 707633 := bstep (se 2 (by rfl) ⟨265362, by rfl⟩ : syracuseStep 707633 = 530725) B530725
theorem B707651 : Blo 467785 707651 := bstep (se 1 (by rfl) ⟨530738, by rfl⟩ : syracuseStep 707651 = 1061477) B1061477
theorem B1789361 : Blo 467785 1789361 := bstep (se 2 (by rfl) ⟨671010, by rfl⟩ : syracuseStep 1789361 = 1342021) B1342021
theorem B1002979 : Blo 467785 1002979 := bstep (se 1 (by rfl) ⟨752234, by rfl⟩ : syracuseStep 1002979 = 1504469) B1504469
theorem B2674565 : Blo 467785 2674565 := bstep (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) B501481
theorem B1003441 : Blo 467785 1003441 := bstep (se 2 (by rfl) ⟨376290, by rfl⟩ : syracuseStep 1003441 = 752581) B752581
theorem B6410339 : Blo 467785 6410339 := bstep (se 1 (by rfl) ⟨4807754, by rfl⟩ : syracuseStep 6410339 = 9615509) B9615509
theorem B3821681 : Blo 467785 3821681 := bstep (se 2 (by rfl) ⟨1433130, by rfl⟩ : syracuseStep 3821681 = 2866261) B2866261
theorem B1069283 : Blo 467785 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B5722595 : Blo 467785 5722595 := bstep (se 1 (by rfl) ⟨4291946, by rfl⟩ : syracuseStep 5722595 = 8583893) B8583893
theorem B3559949 : Blo 467785 3559949 := bstep (se 3 (by rfl) ⟨667490, by rfl⟩ : syracuseStep 3559949 = 1334981) B1334981
theorem B1430065 : Blo 467785 1430065 := bstep (se 2 (by rfl) ⟨536274, by rfl⟩ : syracuseStep 1430065 = 1072549) B1072549
theorem B1200707 : Blo 467785 1200707 := bstep (se 1 (by rfl) ⟨900530, by rfl⟩ : syracuseStep 1200707 = 1801061) B1801061
theorem B3002993 : Blo 467785 3002993 := bstep (se 2 (by rfl) ⟨1126122, by rfl⟩ : syracuseStep 3002993 = 2252245) B2252245
theorem B1069777 : Blo 467785 1069777 := bstep (se 2 (by rfl) ⟨401166, by rfl⟩ : syracuseStep 1069777 = 802333) B802333
theorem B1790819 : Blo 467785 1790819 := bstep (se 1 (by rfl) ⟨1343114, by rfl⟩ : syracuseStep 1790819 = 2686229) B2686229
theorem B4641677 : Blo 467785 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B1004483 : Blo 467785 1004483 := bstep (se 1 (by rfl) ⟨753362, by rfl⟩ : syracuseStep 1004483 = 1506725) B1506725
theorem B2380913 : Blo 467785 2380913 := bstep (se 2 (by rfl) ⟨892842, by rfl⟩ : syracuseStep 2380913 = 1785685) B1785685
theorem B5133709 : Blo 467785 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B1004995 : Blo 467785 1004995 := bstep (se 1 (by rfl) ⟨753746, by rfl⟩ : syracuseStep 1004995 = 1507493) B1507493
theorem B1332749 : Blo 467785 1332749 := bstep (se 3 (by rfl) ⟨249890, by rfl⟩ : syracuseStep 1332749 = 499781) B499781
theorem B1267363 : Blo 467785 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B1332931 : Blo 467785 1332931 := bstep (se 1 (by rfl) ⟨999698, by rfl⟩ : syracuseStep 1332931 = 1999397) B1999397
theorem B907057 : Blo 467785 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B1333091 : Blo 467785 1333091 := bstep (se 1 (by rfl) ⟨999818, by rfl⟩ : syracuseStep 1333091 = 1999637) B1999637
theorem B3823757 : Blo 467785 3823757 := bstep (se 3 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 3823757 = 1433909) B1433909
theorem B1005713 : Blo 467785 1005713 := bstep (se 2 (by rfl) ⟨377142, by rfl⟩ : syracuseStep 1005713 = 754285) B754285
theorem B5363981 : Blo 467785 5363981 := bstep (se 3 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 5363981 = 2011493) B2011493
theorem B1268141 : Blo 467785 1268141 := bstep (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) B475553
theorem B8673733 : Blo 467785 8673733 := bstep (se 4 (by rfl) ⟨813162, by rfl⟩ : syracuseStep 8673733 = 1626325) B1626325
theorem B2382371 : Blo 467785 2382371 := bstep (se 1 (by rfl) ⟨1786778, by rfl⟩ : syracuseStep 2382371 = 3573557) B3573557
theorem B1268273 : Blo 467785 1268273 := bstep (se 2 (by rfl) ⟨475602, by rfl⟩ : syracuseStep 1268273 = 951205) B951205
theorem B1268401 : Blo 467785 1268401 := bstep (se 2 (by rfl) ⟨475650, by rfl⟩ : syracuseStep 1268401 = 951301) B951301
theorem B8575715 : Blo 467785 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B1334161 : Blo 467785 1334161 := bstep (se 2 (by rfl) ⟨500310, by rfl⟩ : syracuseStep 1334161 = 1000621) B1000621
theorem B1006499 : Blo 467785 1006499 := bstep (se 1 (by rfl) ⟨754874, by rfl⟩ : syracuseStep 1006499 = 1509749) B1509749
theorem B6020081 : Blo 467785 6020081 := bstep (se 2 (by rfl) ⟨2257530, by rfl⟩ : syracuseStep 6020081 = 4515061) B4515061
theorem B2383181 : Blo 467785 2383181 := bstep (se 3 (by rfl) ⟨446846, by rfl⟩ : syracuseStep 2383181 = 893693) B893693
theorem B3562865 : Blo 467785 3562865 := bstep (se 2 (by rfl) ⟨1336074, by rfl⟩ : syracuseStep 3562865 = 2672149) B2672149
theorem B8052533 : Blo 467785 8052533 := bstep (se 5 (by rfl) ⟨377462, by rfl⟩ : syracuseStep 8052533 = 754925) B754925
theorem B712547 : Blo 467785 712547 := bstep (se 1 (by rfl) ⟨534410, by rfl⟩ : syracuseStep 712547 = 1068821) B1068821
theorem B1007473 : Blo 467785 1007473 := bstep (se 2 (by rfl) ⟨377802, by rfl⟩ : syracuseStep 1007473 = 755605) B755605
theorem B1695757 : Blo 467785 1695757 := bstep (se 3 (by rfl) ⟨317954, by rfl⟩ : syracuseStep 1695757 = 635909) B635909
theorem B1335437 : Blo 467785 1335437 := bstep (se 3 (by rfl) ⟨250394, by rfl⟩ : syracuseStep 1335437 = 500789) B500789
theorem B1335619 : Blo 467785 1335619 := bstep (se 1 (by rfl) ⟨1001714, by rfl⟩ : syracuseStep 1335619 = 2003429) B2003429
theorem B1335665 : Blo 467785 1335665 := bstep (se 2 (by rfl) ⟨500874, by rfl⟩ : syracuseStep 1335665 = 1001749) B1001749
theorem B3203525 : Blo 467785 3203525 := bstep (se 4 (by rfl) ⟨300330, by rfl⟩ : syracuseStep 3203525 = 600661) B600661
theorem B1925603 : Blo 467785 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B3400163 : Blo 467785 3400163 := bstep (se 1 (by rfl) ⟨2550122, by rfl⟩ : syracuseStep 3400163 = 5100245) B5100245
theorem B3006989 : Blo 467785 3006989 := bstep (se 3 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 3006989 = 1127621) B1127621
theorem B713441 : Blo 467785 713441 := bstep (se 2 (by rfl) ⟨267540, by rfl⟩ : syracuseStep 713441 = 535081) B535081
theorem B2712305 : Blo 467785 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B1369037 : Blo 467785 1369037 := bstep (se 3 (by rfl) ⟨256694, by rfl⟩ : syracuseStep 1369037 = 513389) B513389
theorem B1500241 : Blo 467785 1500241 := bstep (se 2 (by rfl) ⟨562590, by rfl⟩ : syracuseStep 1500241 = 1125181) B1125181
theorem B5366897 : Blo 467785 5366897 := bstep (se 2 (by rfl) ⟨2012586, by rfl⟩ : syracuseStep 5366897 = 4025173) B4025173
theorem B12838085 : Blo 467785 12838085 := bstep (se 4 (by rfl) ⟨1203570, by rfl⟩ : syracuseStep 12838085 = 2407141) B2407141
theorem B1500419 : Blo 467785 1500419 := bstep (se 1 (by rfl) ⟨1125314, by rfl⟩ : syracuseStep 1500419 = 2250629) B2250629
theorem B1074467 : Blo 467785 1074467 := bstep (se 1 (by rfl) ⟨805850, by rfl⟩ : syracuseStep 1074467 = 1611701) B1611701
theorem B2254243 : Blo 467785 2254243 := bstep (se 1 (by rfl) ⟨1690682, by rfl⟩ : syracuseStep 2254243 = 3381365) B3381365
theorem B2680397 : Blo 467785 2680397 := bstep (se 3 (by rfl) ⟨502574, by rfl⟩ : syracuseStep 2680397 = 1005149) B1005149
theorem B2254513 : Blo 467785 2254513 := bstep (se 2 (by rfl) ⟨845442, by rfl⟩ : syracuseStep 2254513 = 1690885) B1690885
theorem B714449 : Blo 467785 714449 := bstep (se 2 (by rfl) ⟨267918, by rfl⟩ : syracuseStep 714449 = 535837) B535837
theorem B4056817 : Blo 467785 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B1337123 : Blo 467785 1337123 := bstep (se 1 (by rfl) ⟨1002842, by rfl⟩ : syracuseStep 1337123 = 2005685) B2005685
theorem B845731 : Blo 467785 845731 := bstep (se 1 (by rfl) ⟨634298, by rfl⟩ : syracuseStep 845731 = 1268597) B1268597
theorem B1206289 : Blo 467785 1206289 := bstep (se 2 (by rfl) ⟨452358, by rfl⟩ : syracuseStep 1206289 = 904717) B904717
theorem B12085361 : Blo 467785 12085361 := bstep (se 2 (by rfl) ⟨4532010, by rfl⟩ : syracuseStep 12085361 = 9064021) B9064021
theorem B2386097 : Blo 467785 2386097 := bstep (se 2 (by rfl) ⟨894786, by rfl⟩ : syracuseStep 2386097 = 1789573) B1789573
theorem B2517475 : Blo 467785 2517475 := bstep (se 1 (by rfl) ⟨1888106, by rfl⟩ : syracuseStep 2517475 = 3776213) B3776213
theorem B3434993 : Blo 467785 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B1698353 : Blo 467785 1698353 := bstep (se 2 (by rfl) ⟨636882, by rfl⟩ : syracuseStep 1698353 = 1273765) B1273765
theorem B1075825 : Blo 467785 1075825 := bstep (se 2 (by rfl) ⟨403434, by rfl⟩ : syracuseStep 1075825 = 806869) B806869
theorem B3009221 : Blo 467785 3009221 := bstep (se 4 (by rfl) ⟨282114, by rfl⟩ : syracuseStep 3009221 = 564229) B564229
theorem B17198021 : Blo 467785 17198021 := bstep (se 4 (by rfl) ⟨1612314, by rfl⟩ : syracuseStep 17198021 = 3224629) B3224629
theorem B1502189 : Blo 467785 1502189 := bstep (se 3 (by rfl) ⟨281660, by rfl⟩ : syracuseStep 1502189 = 563321) B563321
theorem B1338353 : Blo 467785 1338353 := bstep (se 2 (by rfl) ⟨501882, by rfl⟩ : syracuseStep 1338353 = 1003765) B1003765
theorem B945265 : Blo 467785 945265 := bstep (se 2 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 945265 = 708949) B708949
theorem B1273009 : Blo 467785 1273009 := bstep (se 2 (by rfl) ⟨477378, by rfl⟩ : syracuseStep 1273009 = 954757) B954757
theorem B847331 : Blo 467785 847331 := bstep (se 1 (by rfl) ⟨635498, by rfl⟩ : syracuseStep 847331 = 1270997) B1270997
theorem B2387555 : Blo 467785 2387555 := bstep (se 1 (by rfl) ⟨1790666, by rfl⟩ : syracuseStep 2387555 = 3581333) B3581333
theorem B2682629 : Blo 467785 2682629 := bstep (se 4 (by rfl) ⟨251496, by rfl⟩ : syracuseStep 2682629 = 502993) B502993
theorem B2715491 : Blo 467785 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B749441 : Blo 467785 749441 := bstep (se 2 (by rfl) ⟨281040, by rfl⟩ : syracuseStep 749441 = 562081) B562081
theorem B749569 : Blo 467785 749569 := bstep (se 2 (by rfl) ⟨281088, by rfl⟩ : syracuseStep 749569 = 562177) B562177
theorem B716833 : Blo 467785 716833 := bstep (se 2 (by rfl) ⟨268812, by rfl⟩ : syracuseStep 716833 = 537625) B537625
theorem B4059277 : Blo 467785 4059277 := bstep (se 3 (by rfl) ⟨761114, by rfl⟩ : syracuseStep 4059277 = 1522229) B1522229
theorem B4026509 : Blo 467785 4026509 := bstep (se 3 (by rfl) ⟨754970, by rfl⟩ : syracuseStep 4026509 = 1509941) B1509941
theorem B2846897 : Blo 467785 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B2388365 : Blo 467785 2388365 := bstep (se 3 (by rfl) ⟨447818, by rfl⟩ : syracuseStep 2388365 = 895637) B895637
theorem B1339811 : Blo 467785 1339811 := bstep (se 1 (by rfl) ⟨1004858, by rfl⟩ : syracuseStep 1339811 = 2009717) B2009717
theorem B2683313 : Blo 467785 2683313 := bstep (se 2 (by rfl) ⟨1006242, by rfl⟩ : syracuseStep 2683313 = 2012485) B2012485
theorem B2257379 : Blo 467785 2257379 := bstep (se 1 (by rfl) ⟨1693034, by rfl⟩ : syracuseStep 2257379 = 3386069) B3386069
theorem B848657 : Blo 467785 848657 := bstep (se 2 (by rfl) ⟨318246, by rfl⟩ : syracuseStep 848657 = 636493) B636493
theorem B24507157 : Blo 467785 24507157 := bstep (se 6 (by rfl) ⟨574386, by rfl⟩ : syracuseStep 24507157 = 1148773) B1148773
theorem B750563 : Blo 467785 750563 := bstep (se 1 (by rfl) ⟨562922, by rfl⟩ : syracuseStep 750563 = 1125845) B1125845
theorem B848881 : Blo 467785 848881 := bstep (se 2 (by rfl) ⟨318330, by rfl⟩ : syracuseStep 848881 = 636661) B636661
theorem B1340621 : Blo 467785 1340621 := bstep (se 3 (by rfl) ⟨251366, by rfl⟩ : syracuseStep 1340621 = 502733) B502733
theorem B1340813 : Blo 467785 1340813 := bstep (se 3 (by rfl) ⟨251402, by rfl⟩ : syracuseStep 1340813 = 502805) B502805
theorem B2258317 : Blo 467785 2258317 := bstep (se 3 (by rfl) ⟨423434, by rfl⟩ : syracuseStep 2258317 = 846869) B846869
theorem B849379 : Blo 467785 849379 := bstep (se 1 (by rfl) ⟨637034, by rfl⟩ : syracuseStep 849379 = 1274069) B1274069
theorem B2684771 : Blo 467785 2684771 := bstep (se 1 (by rfl) ⟨2013578, by rfl⟩ : syracuseStep 2684771 = 4027157) B4027157
theorem B849955 : Blo 467785 849955 := bstep (se 1 (by rfl) ⟨637466, by rfl⟩ : syracuseStep 849955 = 1274933) B1274933
theorem B2849093 : Blo 467785 2849093 := bstep (se 4 (by rfl) ⟨267102, by rfl⟩ : syracuseStep 2849093 = 534205) B534205
theorem B1341805 : Blo 467785 1341805 := bstep (se 3 (by rfl) ⟨251588, by rfl⟩ : syracuseStep 1341805 = 503177) B503177
theorem B752017 : Blo 467785 752017 := bstep (se 2 (by rfl) ⟨282006, by rfl⟩ : syracuseStep 752017 = 564013) B564013
theorem B1505699 : Blo 467785 1505699 := bstep (se 1 (by rfl) ⟨1129274, by rfl⟩ : syracuseStep 1505699 = 2258549) B2258549
theorem B2259377 : Blo 467785 2259377 := bstep (se 2 (by rfl) ⟨847266, by rfl⟩ : syracuseStep 2259377 = 1694533) B1694533
theorem B6093539 : Blo 467785 6093539 := bstep (se 1 (by rfl) ⟨4570154, by rfl⟩ : syracuseStep 6093539 = 9140309) B9140309
theorem B1506289 : Blo 467785 1506289 := bstep (se 2 (by rfl) ⟨564858, by rfl⟩ : syracuseStep 1506289 = 1129717) B1129717
theorem B1998371 : Blo 467785 1998371 := bstep (se 1 (by rfl) ⟨1498778, by rfl⟩ : syracuseStep 1998371 = 2997557) B2997557
theorem B753619 : Blo 467785 753619 := bstep (se 1 (by rfl) ⟨565214, by rfl⟩ : syracuseStep 753619 = 1130429) B1130429
theorem B2261009 : Blo 467785 2261009 := bstep (se 2 (by rfl) ⟨847878, by rfl⟩ : syracuseStep 2261009 = 1695757) B1695757
theorem B6750449 : Blo 467785 6750449 := bstep (se 2 (by rfl) ⟨2531418, by rfl⟩ : syracuseStep 6750449 = 5062837) B5062837
theorem B3572099 : Blo 467785 3572099 := bstep (se 1 (by rfl) ⟨2679074, by rfl⟩ : syracuseStep 3572099 = 5358149) B5358149
theorem B1999363 : Blo 467785 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B1606195 : Blo 467785 1606195 := bstep (se 1 (by rfl) ⟨1204646, by rfl⟩ : syracuseStep 1606195 = 2409293) B2409293
theorem B1507891 : Blo 467785 1507891 := bstep (se 1 (by rfl) ⟨1130918, by rfl⟩ : syracuseStep 1507891 = 2261837) B2261837
theorem B1081931 : Blo 467785 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B2851421 : Blo 467785 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B3016115 : Blo 467785 3016115 := bstep (se 1 (by rfl) ⟨2262086, by rfl⟩ : syracuseStep 3016115 = 4524173) B4524173
theorem B2000321 : Blo 467785 2000321 := bstep (se 2 (by rfl) ⟨750120, by rfl⟩ : syracuseStep 2000321 = 1500241) B1500241
theorem B951755 : Blo 467785 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B1508825 : Blo 467785 1508825 := bstep (se 2 (by rfl) ⟨565809, by rfl⟩ : syracuseStep 1508825 = 1131619) B1131619
theorem B1509185 : Blo 467785 1509185 := bstep (se 2 (by rfl) ⟨565944, by rfl⟩ : syracuseStep 1509185 = 1131889) B1131889
theorem B526315 : Blo 467785 526315 := bstep (se 1 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 526315 = 789473) B789473
theorem B952307 : Blo 467785 952307 := bstep (se 1 (by rfl) ⟨714230, by rfl⟩ : syracuseStep 952307 = 1428461) B1428461
theorem B2263085 : Blo 467785 2263085 := bstep (se 3 (by rfl) ⟨424328, by rfl⟩ : syracuseStep 2263085 = 848657) B848657
theorem B4294721 : Blo 467785 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B526423 : Blo 467785 526423 := bstep (se 1 (by rfl) ⟨394817, by rfl⟩ : syracuseStep 526423 = 789635) B789635
theorem B1018049 : Blo 467785 1018049 := bstep (se 2 (by rfl) ⟨381768, by rfl⟩ : syracuseStep 1018049 = 763537) B763537
theorem B526603 : Blo 467785 526603 := bstep (se 1 (by rfl) ⟨394952, by rfl⟩ : syracuseStep 526603 = 789905) B789905
theorem B5409089 : Blo 467785 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B526711 : Blo 467785 526711 := bstep (se 1 (by rfl) ⟨395033, by rfl⟩ : syracuseStep 526711 = 790067) B790067
theorem B592267 : Blo 467785 592267 := bstep (se 1 (by rfl) ⟨444200, by rfl⟩ : syracuseStep 592267 = 888401) B888401
theorem B526891 : Blo 467785 526891 := bstep (se 1 (by rfl) ⟨395168, by rfl⟩ : syracuseStep 526891 = 790337) B790337
theorem B592535 : Blo 467785 592535 := bstep (se 1 (by rfl) ⟨444401, by rfl⟩ : syracuseStep 592535 = 888803) B888803
theorem B526999 : Blo 467785 526999 := bstep (se 1 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 526999 = 790499) B790499
theorem B1608385 : Blo 467785 1608385 := bstep (se 2 (by rfl) ⟨603144, by rfl⟩ : syracuseStep 1608385 = 1206289) B1206289
theorem B527179 : Blo 467785 527179 := bstep (se 1 (by rfl) ⟨395384, by rfl⟩ : syracuseStep 527179 = 790769) B790769
theorem B527287 : Blo 467785 527287 := bstep (se 1 (by rfl) ⟨395465, by rfl⟩ : syracuseStep 527287 = 790931) B790931
theorem B789527 : Blo 467785 789527 := bstep (se 1 (by rfl) ⟨592145, by rfl⟩ : syracuseStep 789527 = 1184291) B1184291
theorem B2001995 : Blo 467785 2001995 := bstep (se 1 (by rfl) ⟨1501496, by rfl⟩ : syracuseStep 2001995 = 3002993) B3002993
theorem B527467 : Blo 467785 527467 := bstep (se 1 (by rfl) ⟨395600, by rfl⟩ : syracuseStep 527467 = 791201) B791201
theorem B789655 : Blo 467785 789655 := bstep (se 1 (by rfl) ⟨592241, by rfl⟩ : syracuseStep 789655 = 1184483) B1184483
theorem B527575 : Blo 467785 527575 := bstep (se 1 (by rfl) ⟨395681, by rfl⟩ : syracuseStep 527575 = 791363) B791363
theorem B593239 : Blo 467785 593239 := bstep (se 1 (by rfl) ⟨444929, by rfl⟩ : syracuseStep 593239 = 889859) B889859
theorem B527755 : Blo 467785 527755 := bstep (se 1 (by rfl) ⟨395816, by rfl⟩ : syracuseStep 527755 = 791633) B791633
theorem B527863 : Blo 467785 527863 := bstep (se 1 (by rfl) ⟨395897, by rfl⟩ : syracuseStep 527863 = 791795) B791795
theorem B528043 : Blo 467785 528043 := bstep (se 1 (by rfl) ⟨396032, by rfl⟩ : syracuseStep 528043 = 792065) B792065
theorem B888499 : Blo 467785 888499 := bstep (se 1 (by rfl) ⟨666374, by rfl⟩ : syracuseStep 888499 = 1332749) B1332749
theorem B3575501 : Blo 467785 3575501 := bstep (se 3 (by rfl) ⟨670406, by rfl⟩ : syracuseStep 3575501 = 1340813) B1340813
theorem B790283 : Blo 467785 790283 := bstep (se 1 (by rfl) ⟨592712, by rfl⟩ : syracuseStep 790283 = 1185425) B1185425
theorem B528151 : Blo 467785 528151 := bstep (se 1 (by rfl) ⟨396113, by rfl⟩ : syracuseStep 528151 = 792227) B792227
theorem B1052531 : Blo 467785 1052531 := bstep (se 1 (by rfl) ⟨789398, by rfl⟩ : syracuseStep 1052531 = 1578797) B1578797
theorem B790411 : Blo 467785 790411 := bstep (se 1 (by rfl) ⟨592808, by rfl⟩ : syracuseStep 790411 = 1185617) B1185617
theorem B1052567 : Blo 467785 1052567 := bstep (se 1 (by rfl) ⟨789425, by rfl⟩ : syracuseStep 1052567 = 1578851) B1578851
theorem B888727 : Blo 467785 888727 := bstep (se 1 (by rfl) ⟨666545, by rfl⟩ : syracuseStep 888727 = 1333091) B1333091
theorem B528331 : Blo 467785 528331 := bstep (se 1 (by rfl) ⟨396248, by rfl⟩ : syracuseStep 528331 = 792497) B792497
theorem B888833 : Blo 467785 888833 := bstep (se 2 (by rfl) ⟨333312, by rfl⟩ : syracuseStep 888833 = 666625) B666625
theorem B790553 : Blo 467785 790553 := bstep (se 2 (by rfl) ⟨296457, by rfl⟩ : syracuseStep 790553 = 592915) B592915
theorem B528439 : Blo 467785 528439 := bstep (se 1 (by rfl) ⟨396329, by rfl⟩ : syracuseStep 528439 = 792659) B792659
theorem B1052747 : Blo 467785 1052747 := bstep (se 1 (by rfl) ⟨789560, by rfl⟩ : syracuseStep 1052747 = 1579121) B1579121
theorem B1052801 : Blo 467785 1052801 := bstep (se 2 (by rfl) ⟨394800, by rfl⟩ : syracuseStep 1052801 = 789601) B789601
theorem B13570199 : Blo 467785 13570199 := bstep (se 1 (by rfl) ⟨10177649, by rfl⟩ : syracuseStep 13570199 = 20355299) B20355299
theorem B888985 : Blo 467785 888985 := bstep (se 2 (by rfl) ⟨333369, by rfl⟩ : syracuseStep 888985 = 666739) B666739
theorem B790681 : Blo 467785 790681 := bstep (se 2 (by rfl) ⟨296505, by rfl⟩ : syracuseStep 790681 = 593011) B593011
theorem B3575987 : Blo 467785 3575987 := bstep (se 1 (by rfl) ⟨2681990, by rfl⟩ : syracuseStep 3575987 = 5363981) B5363981
theorem B528619 : Blo 467785 528619 := bstep (se 1 (by rfl) ⟨396464, by rfl⟩ : syracuseStep 528619 = 792929) B792929
theorem B528727 : Blo 467785 528727 := bstep (se 1 (by rfl) ⟨396545, by rfl⟩ : syracuseStep 528727 = 793091) B793091
theorem B1053017 : Blo 467785 1053017 := bstep (se 2 (by rfl) ⟨394881, by rfl⟩ : syracuseStep 1053017 = 789763) B789763
theorem B3019139 : Blo 467785 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B1184179 : Blo 467785 1184179 := bstep (se 1 (by rfl) ⟨888134, by rfl⟩ : syracuseStep 1184179 = 1776269) B1776269
theorem B1053107 : Blo 467785 1053107 := bstep (se 1 (by rfl) ⟨789830, by rfl⟩ : syracuseStep 1053107 = 1579661) B1579661
theorem B1053143 : Blo 467785 1053143 := bstep (se 1 (by rfl) ⟨789857, by rfl⟩ : syracuseStep 1053143 = 1579715) B1579715
theorem B528907 : Blo 467785 528907 := bstep (se 1 (by rfl) ⟨396680, by rfl⟩ : syracuseStep 528907 = 793361) B793361
theorem B1184321 : Blo 467785 1184321 := bstep (se 2 (by rfl) ⟨444120, by rfl⟩ : syracuseStep 1184321 = 888241) B888241
theorem B529015 : Blo 467785 529015 := bstep (se 1 (by rfl) ⟨396761, by rfl⟩ : syracuseStep 529015 = 793523) B793523
theorem B1053323 : Blo 467785 1053323 := bstep (se 1 (by rfl) ⟨789992, by rfl⟩ : syracuseStep 1053323 = 1579985) B1579985
theorem B1053377 : Blo 467785 1053377 := bstep (se 2 (by rfl) ⟨395016, by rfl⟩ : syracuseStep 1053377 = 790033) B790033
theorem B791255 : Blo 467785 791255 := bstep (se 1 (by rfl) ⟨593441, by rfl⟩ : syracuseStep 791255 = 1186883) B1186883
theorem B529195 : Blo 467785 529195 := bstep (se 1 (by rfl) ⟨396896, by rfl⟩ : syracuseStep 529195 = 793793) B793793
theorem B791383 : Blo 467785 791383 := bstep (se 1 (by rfl) ⟨593537, by rfl⟩ : syracuseStep 791383 = 1187075) B1187075
theorem B529303 : Blo 467785 529303 := bstep (se 1 (by rfl) ⟨396977, by rfl⟩ : syracuseStep 529303 = 793955) B793955
theorem B1053593 : Blo 467785 1053593 := bstep (se 2 (by rfl) ⟨395097, by rfl⟩ : syracuseStep 1053593 = 790195) B790195
theorem B1053683 : Blo 467785 1053683 := bstep (se 1 (by rfl) ⟨790262, by rfl⟩ : syracuseStep 1053683 = 1580525) B1580525
theorem B594955 : Blo 467785 594955 := bstep (se 1 (by rfl) ⟨446216, by rfl⟩ : syracuseStep 594955 = 892433) B892433
theorem B1053719 : Blo 467785 1053719 := bstep (se 1 (by rfl) ⟨790289, by rfl⟩ : syracuseStep 1053719 = 1580579) B1580579
theorem B529483 : Blo 467785 529483 := bstep (se 1 (by rfl) ⟨397112, by rfl⟩ : syracuseStep 529483 = 794225) B794225
theorem B529591 : Blo 467785 529591 := bstep (se 1 (by rfl) ⟨397193, by rfl⟩ : syracuseStep 529591 = 794387) B794387
theorem B1053899 : Blo 467785 1053899 := bstep (se 1 (by rfl) ⟨790424, by rfl⟩ : syracuseStep 1053899 = 1580849) B1580849
theorem B1053953 : Blo 467785 1053953 := bstep (se 2 (by rfl) ⟨395232, by rfl⟩ : syracuseStep 1053953 = 790465) B790465
theorem B529771 : Blo 467785 529771 := bstep (se 1 (by rfl) ⟨397328, by rfl⟩ : syracuseStep 529771 = 794657) B794657
theorem B890291 : Blo 467785 890291 := bstep (se 1 (by rfl) ⟨667718, by rfl⟩ : syracuseStep 890291 = 1335437) B1335437
theorem B792011 : Blo 467785 792011 := bstep (se 1 (by rfl) ⟨594008, by rfl⟩ : syracuseStep 792011 = 1188017) B1188017
theorem B529879 : Blo 467785 529879 := bstep (se 1 (by rfl) ⟨397409, by rfl⟩ : syracuseStep 529879 = 794819) B794819
theorem B1054169 : Blo 467785 1054169 := bstep (se 2 (by rfl) ⟨395313, by rfl⟩ : syracuseStep 1054169 = 790627) B790627
theorem B1054259 : Blo 467785 1054259 := bstep (se 1 (by rfl) ⟨790694, by rfl⟩ : syracuseStep 1054259 = 1581389) B1581389
theorem B890443 : Blo 467785 890443 := bstep (se 1 (by rfl) ⟨667832, by rfl⟩ : syracuseStep 890443 = 1335665) B1335665
theorem B792139 : Blo 467785 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B1054295 : Blo 467785 1054295 := bstep (se 1 (by rfl) ⟨790721, by rfl⟩ : syracuseStep 1054295 = 1581443) B1581443
theorem B3577445 : Blo 467785 3577445 := bstep (se 4 (by rfl) ⟨335385, by rfl⟩ : syracuseStep 3577445 = 670771) B670771
theorem B2135683 : Blo 467785 2135683 := bstep (se 1 (by rfl) ⟨1601762, by rfl⟩ : syracuseStep 2135683 = 3203525) B3203525
theorem B530059 : Blo 467785 530059 := bstep (se 1 (by rfl) ⟨397544, by rfl⟩ : syracuseStep 530059 = 795089) B795089
theorem B1283735 : Blo 467785 1283735 := bstep (se 1 (by rfl) ⟨962801, by rfl⟩ : syracuseStep 1283735 = 1925603) B1925603
theorem B2266775 : Blo 467785 2266775 := bstep (se 1 (by rfl) ⟨1700081, by rfl⟩ : syracuseStep 2266775 = 3400163) B3400163
theorem B2004659 : Blo 467785 2004659 := bstep (se 1 (by rfl) ⟨1503494, by rfl⟩ : syracuseStep 2004659 = 3006989) B3006989
theorem B9049805 : Blo 467785 9049805 := bstep (se 3 (by rfl) ⟨1696838, by rfl⟩ : syracuseStep 9049805 = 3393677) B3393677
theorem B792281 : Blo 467785 792281 := bstep (se 2 (by rfl) ⟨297105, by rfl⟩ : syracuseStep 792281 = 594211) B594211
theorem B530167 : Blo 467785 530167 := bstep (se 1 (by rfl) ⟨397625, by rfl⟩ : syracuseStep 530167 = 795251) B795251
theorem B1054475 : Blo 467785 1054475 := bstep (se 1 (by rfl) ⟨790856, by rfl⟩ : syracuseStep 1054475 = 1581713) B1581713
theorem B1185587 : Blo 467785 1185587 := bstep (se 1 (by rfl) ⟨889190, by rfl⟩ : syracuseStep 1185587 = 1778381) B1778381
theorem B1054529 : Blo 467785 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B792409 : Blo 467785 792409 := bstep (se 2 (by rfl) ⟨297153, by rfl⟩ : syracuseStep 792409 = 594307) B594307
theorem B890777 : Blo 467785 890777 := bstep (se 2 (by rfl) ⟨334041, by rfl⟩ : syracuseStep 890777 = 668083) B668083
theorem B530347 : Blo 467785 530347 := bstep (se 1 (by rfl) ⟨397760, by rfl⟩ : syracuseStep 530347 = 795521) B795521
theorem B595927 : Blo 467785 595927 := bstep (se 1 (by rfl) ⟨446945, by rfl⟩ : syracuseStep 595927 = 893891) B893891
theorem B530455 : Blo 467785 530455 := bstep (se 1 (by rfl) ⟨397841, by rfl⟩ : syracuseStep 530455 = 795683) B795683
theorem B1054745 : Blo 467785 1054745 := bstep (se 2 (by rfl) ⟨395529, by rfl⟩ : syracuseStep 1054745 = 791059) B791059
theorem B1906753 : Blo 467785 1906753 := bstep (se 2 (by rfl) ⟨715032, by rfl⟩ : syracuseStep 1906753 = 1430065) B1430065
theorem B3577931 : Blo 467785 3577931 := bstep (se 1 (by rfl) ⟨2683448, by rfl⟩ : syracuseStep 3577931 = 5366897) B5366897
theorem B1054835 : Blo 467785 1054835 := bstep (se 1 (by rfl) ⟨791126, by rfl⟩ : syracuseStep 1054835 = 1582253) B1582253
theorem B8558723 : Blo 467785 8558723 := bstep (se 1 (by rfl) ⟨6419042, by rfl⟩ : syracuseStep 8558723 = 12838085) B12838085
theorem B1054871 : Blo 467785 1054871 := bstep (se 1 (by rfl) ⟨791153, by rfl⟩ : syracuseStep 1054871 = 1582307) B1582307
theorem B530635 : Blo 467785 530635 := bstep (se 1 (by rfl) ⟨397976, by rfl⟩ : syracuseStep 530635 = 795953) B795953
theorem B1579229 : Blo 467785 1579229 := bstep (se 3 (by rfl) ⟨296105, by rfl⟩ : syracuseStep 1579229 = 592211) B592211
theorem B530743 : Blo 467785 530743 := bstep (se 1 (by rfl) ⟨398057, by rfl⟩ : syracuseStep 530743 = 796115) B796115
theorem B3676481 : Blo 467785 3676481 := bstep (se 2 (by rfl) ⟨1378680, by rfl⟩ : syracuseStep 3676481 = 2757361) B2757361
theorem B1186123 : Blo 467785 1186123 := bstep (se 1 (by rfl) ⟨889592, by rfl⟩ : syracuseStep 1186123 = 1779185) B1779185
theorem B1055051 : Blo 467785 1055051 := bstep (se 1 (by rfl) ⟨791288, by rfl⟩ : syracuseStep 1055051 = 1582577) B1582577
theorem B32676209 : Blo 467785 32676209 := bstep (se 2 (by rfl) ⟨12253578, by rfl⟩ : syracuseStep 32676209 = 24507157) B24507157
theorem B1055105 : Blo 467785 1055105 := bstep (se 2 (by rfl) ⟨395664, by rfl⟩ : syracuseStep 1055105 = 791329) B791329
theorem B792983 : Blo 467785 792983 := bstep (se 1 (by rfl) ⟨594737, by rfl⟩ : syracuseStep 792983 = 1189475) B1189475
theorem B1186265 : Blo 467785 1186265 := bstep (se 2 (by rfl) ⟨444849, by rfl⟩ : syracuseStep 1186265 = 889699) B889699
theorem B891415 : Blo 467785 891415 := bstep (se 1 (by rfl) ⟨668561, by rfl⟩ : syracuseStep 891415 = 1337123) B1337123
theorem B793111 : Blo 467785 793111 := bstep (se 1 (by rfl) ⟨594833, by rfl⟩ : syracuseStep 793111 = 1189667) B1189667
theorem B1055321 : Blo 467785 1055321 := bstep (se 2 (by rfl) ⟨395745, by rfl⟩ : syracuseStep 1055321 = 791491) B791491
theorem B1055411 : Blo 467785 1055411 := bstep (se 1 (by rfl) ⟨791558, by rfl⟩ : syracuseStep 1055411 = 1583117) B1583117
theorem B1055447 : Blo 467785 1055447 := bstep (se 1 (by rfl) ⟨791585, by rfl⟩ : syracuseStep 1055447 = 1583171) B1583171
theorem B596747 : Blo 467785 596747 := bstep (se 1 (by rfl) ⟨447560, by rfl⟩ : syracuseStep 596747 = 895121) B895121
theorem B1055627 : Blo 467785 1055627 := bstep (se 1 (by rfl) ⟨791720, by rfl⟩ : syracuseStep 1055627 = 1583441) B1583441
theorem B1055681 : Blo 467785 1055681 := bstep (se 2 (by rfl) ⟨395880, by rfl⟩ : syracuseStep 1055681 = 791761) B791761
theorem B2038787 : Blo 467785 2038787 := bstep (se 1 (by rfl) ⟨1529090, by rfl⟩ : syracuseStep 2038787 = 3058181) B3058181
theorem B2006147 : Blo 467785 2006147 := bstep (se 1 (by rfl) ⟨1504610, by rfl⟩ : syracuseStep 2006147 = 3009221) B3009221
theorem B793739 : Blo 467785 793739 := bstep (se 1 (by rfl) ⟨595304, by rfl⟩ : syracuseStep 793739 = 1190609) B1190609
theorem B1055897 : Blo 467785 1055897 := bstep (se 2 (by rfl) ⟨395961, by rfl⟩ : syracuseStep 1055897 = 791923) B791923
theorem B1350877 : Blo 467785 1350877 := bstep (se 3 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 1350877 = 506579) B506579
theorem B1055987 : Blo 467785 1055987 := bstep (se 1 (by rfl) ⟨791990, by rfl⟩ : syracuseStep 1055987 = 1583981) B1583981
theorem B793867 : Blo 467785 793867 := bstep (se 1 (by rfl) ⟨595400, by rfl⟩ : syracuseStep 793867 = 1190801) B1190801
theorem B1187095 : Blo 467785 1187095 := bstep (se 1 (by rfl) ⟨890321, by rfl⟩ : syracuseStep 1187095 = 1780643) B1780643
theorem B1056023 : Blo 467785 1056023 := bstep (se 1 (by rfl) ⟨792017, by rfl⟩ : syracuseStep 1056023 = 1584035) B1584035
theorem B1580363 : Blo 467785 1580363 := bstep (se 1 (by rfl) ⟨1185272, by rfl⟩ : syracuseStep 1580363 = 2370545) B2370545
theorem B892235 : Blo 467785 892235 := bstep (se 1 (by rfl) ⟨669176, by rfl⟩ : syracuseStep 892235 = 1338353) B1338353
theorem B892289 : Blo 467785 892289 := bstep (se 2 (by rfl) ⟨334608, by rfl⟩ : syracuseStep 892289 = 669217) B669217
theorem B794009 : Blo 467785 794009 := bstep (se 2 (by rfl) ⟨297753, by rfl⟩ : syracuseStep 794009 = 595507) B595507
theorem B1056203 : Blo 467785 1056203 := bstep (se 1 (by rfl) ⟨792152, by rfl⟩ : syracuseStep 1056203 = 1584305) B1584305
theorem B1056257 : Blo 467785 1056257 := bstep (se 2 (by rfl) ⟨396096, by rfl⟩ : syracuseStep 1056257 = 792193) B792193
theorem B794137 : Blo 467785 794137 := bstep (se 2 (by rfl) ⟨297801, by rfl⟩ : syracuseStep 794137 = 595603) B595603
theorem B1777241 : Blo 467785 1777241 := bstep (se 2 (by rfl) ⟨666465, by rfl⟩ : syracuseStep 1777241 = 1332931) B1332931
theorem B1580633 : Blo 467785 1580633 := bstep (se 2 (by rfl) ⟨592737, by rfl⟩ : syracuseStep 1580633 = 1185475) B1185475
theorem B564887 : Blo 467785 564887 := bstep (se 1 (by rfl) ⟨423665, by rfl⟩ : syracuseStep 564887 = 847331) B847331
theorem B1187531 : Blo 467785 1187531 := bstep (se 1 (by rfl) ⟨890648, by rfl⟩ : syracuseStep 1187531 = 1781297) B1781297
theorem B1056473 : Blo 467785 1056473 := bstep (se 2 (by rfl) ⟨396177, by rfl⟩ : syracuseStep 1056473 = 792355) B792355
theorem B1056563 : Blo 467785 1056563 := bstep (se 1 (by rfl) ⟨792422, by rfl⟩ : syracuseStep 1056563 = 1584845) B1584845
theorem B1056599 : Blo 467785 1056599 := bstep (se 1 (by rfl) ⟨792449, by rfl⟩ : syracuseStep 1056599 = 1584899) B1584899
theorem B499627 : Blo 467785 499627 := bstep (se 1 (by rfl) ⟨374720, by rfl⟩ : syracuseStep 499627 = 749441) B749441
theorem B1056779 : Blo 467785 1056779 := bstep (se 1 (by rfl) ⟨792584, by rfl⟩ : syracuseStep 1056779 = 1585169) B1585169
theorem B1187905 : Blo 467785 1187905 := bstep (se 2 (by rfl) ⟨445464, by rfl⟩ : syracuseStep 1187905 = 890929) B890929
theorem B1056833 : Blo 467785 1056833 := bstep (se 2 (by rfl) ⟨396312, by rfl⟩ : syracuseStep 1056833 = 792625) B792625
theorem B794711 : Blo 467785 794711 := bstep (se 1 (by rfl) ⟨596033, by rfl⟩ : syracuseStep 794711 = 1192067) B1192067
theorem B794839 : Blo 467785 794839 := bstep (se 1 (by rfl) ⟨596129, by rfl⟩ : syracuseStep 794839 = 1192259) B1192259
theorem B1581335 : Blo 467785 1581335 := bstep (se 1 (by rfl) ⟨1186001, by rfl⟩ : syracuseStep 1581335 = 2372003) B2372003
theorem B893207 : Blo 467785 893207 := bstep (se 1 (by rfl) ⟨669905, by rfl⟩ : syracuseStep 893207 = 1339811) B1339811
theorem B1057049 : Blo 467785 1057049 := bstep (se 2 (by rfl) ⟨396393, by rfl⟩ : syracuseStep 1057049 = 792787) B792787
theorem B1057139 : Blo 467785 1057139 := bstep (se 1 (by rfl) ⟨792854, by rfl⟩ : syracuseStep 1057139 = 1585709) B1585709
theorem B1057175 : Blo 467785 1057175 := bstep (se 1 (by rfl) ⟨792881, by rfl⟩ : syracuseStep 1057175 = 1585763) B1585763
theorem B1057355 : Blo 467785 1057355 := bstep (se 1 (by rfl) ⟨793016, by rfl⟩ : syracuseStep 1057355 = 1586033) B1586033
theorem B1057409 : Blo 467785 1057409 := bstep (se 2 (by rfl) ⟨396528, by rfl⟩ : syracuseStep 1057409 = 793057) B793057
theorem B500375 : Blo 467785 500375 := bstep (se 1 (by rfl) ⟨375281, by rfl⟩ : syracuseStep 500375 = 750563) B750563
theorem B1188503 : Blo 467785 1188503 := bstep (se 1 (by rfl) ⟨891377, by rfl⟩ : syracuseStep 1188503 = 1782755) B1782755
theorem B4301585 : Blo 467785 4301585 := bstep (se 2 (by rfl) ⟨1613094, by rfl⟩ : syracuseStep 4301585 = 3226189) B3226189
theorem B1581875 : Blo 467785 1581875 := bstep (se 1 (by rfl) ⟨1186406, by rfl⟩ : syracuseStep 1581875 = 2372813) B2372813
theorem B893747 : Blo 467785 893747 := bstep (se 1 (by rfl) ⟨670310, by rfl⟩ : syracuseStep 893747 = 1340621) B1340621
theorem B467787 : Blo 467785 467787 := bstep (se 1 (by rfl) ⟨350840, by rfl⟩ : syracuseStep 467787 = 701681) B701681
theorem B795467 : Blo 467785 795467 := bstep (se 1 (by rfl) ⟨596600, by rfl⟩ : syracuseStep 795467 = 1193201) B1193201
theorem B467799 : Blo 467785 467799 := bstep (se 1 (by rfl) ⟨350849, by rfl⟩ : syracuseStep 467799 = 701699) B701699
theorem B1057625 : Blo 467785 1057625 := bstep (se 2 (by rfl) ⟨396609, by rfl⟩ : syracuseStep 1057625 = 793219) B793219
theorem B467819 : Blo 467785 467819 := bstep (se 1 (by rfl) ⟨350864, by rfl⟩ : syracuseStep 467819 = 701729) B701729
theorem B467831 : Blo 467785 467831 := bstep (se 1 (by rfl) ⟨350873, by rfl⟩ : syracuseStep 467831 = 701747) B701747
theorem B467851 : Blo 467785 467851 := bstep (se 1 (by rfl) ⟨350888, by rfl⟩ : syracuseStep 467851 = 701777) B701777
theorem B467863 : Blo 467785 467863 := bstep (se 1 (by rfl) ⟨350897, by rfl⟩ : syracuseStep 467863 = 701795) B701795
theorem B3810199 : Blo 467785 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B467883 : Blo 467785 467883 := bstep (se 1 (by rfl) ⟨350912, by rfl⟩ : syracuseStep 467883 = 701825) B701825
theorem B1057715 : Blo 467785 1057715 := bstep (se 1 (by rfl) ⟨793286, by rfl⟩ : syracuseStep 1057715 = 1586573) B1586573
theorem B467895 : Blo 467785 467895 := bstep (se 1 (by rfl) ⟨350921, by rfl⟩ : syracuseStep 467895 = 701843) B701843
theorem B467915 : Blo 467785 467915 := bstep (se 1 (by rfl) ⟨350936, by rfl⟩ : syracuseStep 467915 = 701873) B701873
theorem B795595 : Blo 467785 795595 := bstep (se 1 (by rfl) ⟨596696, by rfl⟩ : syracuseStep 795595 = 1193393) B1193393
theorem B467927 : Blo 467785 467927 := bstep (se 1 (by rfl) ⟨350945, by rfl⟩ : syracuseStep 467927 = 701891) B701891
theorem B1057751 : Blo 467785 1057751 := bstep (se 1 (by rfl) ⟨793313, by rfl⟩ : syracuseStep 1057751 = 1586627) B1586627
theorem B467947 : Blo 467785 467947 := bstep (se 1 (by rfl) ⟨350960, by rfl⟩ : syracuseStep 467947 = 701921) B701921
theorem B467959 : Blo 467785 467959 := bstep (se 1 (by rfl) ⟨350969, by rfl⟩ : syracuseStep 467959 = 701939) B701939
theorem B467979 : Blo 467785 467979 := bstep (se 1 (by rfl) ⟨350984, by rfl⟩ : syracuseStep 467979 = 701969) B701969
theorem B467991 : Blo 467785 467991 := bstep (se 1 (by rfl) ⟨350993, by rfl⟩ : syracuseStep 467991 = 701987) B701987
theorem B468011 : Blo 467785 468011 := bstep (se 1 (by rfl) ⟨351008, by rfl⟩ : syracuseStep 468011 = 702017) B702017
theorem B468023 : Blo 467785 468023 := bstep (se 1 (by rfl) ⟨351017, by rfl⟩ : syracuseStep 468023 = 702035) B702035
theorem B1582145 : Blo 467785 1582145 := bstep (se 2 (by rfl) ⟨593304, by rfl⟩ : syracuseStep 1582145 = 1186609) B1186609
theorem B468043 : Blo 467785 468043 := bstep (se 1 (by rfl) ⟨351032, by rfl⟩ : syracuseStep 468043 = 702065) B702065
theorem B468055 : Blo 467785 468055 := bstep (se 1 (by rfl) ⟨351041, by rfl⟩ : syracuseStep 468055 = 702083) B702083
theorem B795737 : Blo 467785 795737 := bstep (se 2 (by rfl) ⟨298401, by rfl⟩ : syracuseStep 795737 = 596803) B596803
theorem B533611 : Blo 467785 533611 := bstep (se 1 (by rfl) ⟨400208, by rfl⟩ : syracuseStep 533611 = 800417) B800417
theorem B468075 : Blo 467785 468075 := bstep (se 1 (by rfl) ⟨351056, by rfl⟩ : syracuseStep 468075 = 702113) B702113
theorem B468087 : Blo 467785 468087 := bstep (se 1 (by rfl) ⟨351065, by rfl⟩ : syracuseStep 468087 = 702131) B702131
theorem B468107 : Blo 467785 468107 := bstep (se 1 (by rfl) ⟨351080, by rfl⟩ : syracuseStep 468107 = 702161) B702161
theorem B1057931 : Blo 467785 1057931 := bstep (se 1 (by rfl) ⟨793448, by rfl⟩ : syracuseStep 1057931 = 1586897) B1586897
theorem B468119 : Blo 467785 468119 := bstep (se 1 (by rfl) ⟨351089, by rfl⟩ : syracuseStep 468119 = 702179) B702179
theorem B468139 : Blo 467785 468139 := bstep (se 1 (by rfl) ⟨351104, by rfl⟩ : syracuseStep 468139 = 702209) B702209
theorem B1778867 : Blo 467785 1778867 := bstep (se 1 (by rfl) ⟨1334150, by rfl⟩ : syracuseStep 1778867 = 2668301) B2668301
theorem B468151 : Blo 467785 468151 := bstep (se 1 (by rfl) ⟨351113, by rfl⟩ : syracuseStep 468151 = 702227) B702227
theorem B1778881 : Blo 467785 1778881 := bstep (se 2 (by rfl) ⟨667080, by rfl⟩ : syracuseStep 1778881 = 1334161) B1334161
theorem B1057985 : Blo 467785 1057985 := bstep (se 2 (by rfl) ⟨396744, by rfl⟩ : syracuseStep 1057985 = 793489) B793489
theorem B468171 : Blo 467785 468171 := bstep (se 1 (by rfl) ⟨351128, by rfl⟩ : syracuseStep 468171 = 702257) B702257
theorem B468183 : Blo 467785 468183 := bstep (se 1 (by rfl) ⟨351137, by rfl⟩ : syracuseStep 468183 = 702275) B702275
theorem B795865 : Blo 467785 795865 := bstep (se 2 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 795865 = 596899) B596899
theorem B468203 : Blo 467785 468203 := bstep (se 1 (by rfl) ⟨351152, by rfl⟩ : syracuseStep 468203 = 702305) B702305
theorem B468215 : Blo 467785 468215 := bstep (se 1 (by rfl) ⟨351161, by rfl⟩ : syracuseStep 468215 = 702323) B702323
theorem B468235 : Blo 467785 468235 := bstep (se 1 (by rfl) ⟨351176, by rfl⟩ : syracuseStep 468235 = 702353) B702353
theorem B468247 : Blo 467785 468247 := bstep (se 1 (by rfl) ⟨351185, by rfl⟩ : syracuseStep 468247 = 702371) B702371
theorem B894233 : Blo 467785 894233 := bstep (se 2 (by rfl) ⟨335337, by rfl⟩ : syracuseStep 894233 = 670675) B670675
theorem B468267 : Blo 467785 468267 := bstep (se 1 (by rfl) ⟨351200, by rfl⟩ : syracuseStep 468267 = 702401) B702401
theorem B468279 : Blo 467785 468279 := bstep (se 1 (by rfl) ⟨351209, by rfl⟩ : syracuseStep 468279 = 702419) B702419
theorem B2008385 : Blo 467785 2008385 := bstep (se 2 (by rfl) ⟨753144, by rfl⟩ : syracuseStep 2008385 = 1506289) B1506289
theorem B468299 : Blo 467785 468299 := bstep (se 1 (by rfl) ⟨351224, by rfl⟩ : syracuseStep 468299 = 702449) B702449
theorem B468311 : Blo 467785 468311 := bstep (se 1 (by rfl) ⟨351233, by rfl⟩ : syracuseStep 468311 = 702467) B702467
theorem B468331 : Blo 467785 468331 := bstep (se 1 (by rfl) ⟨351248, by rfl⟩ : syracuseStep 468331 = 702497) B702497
theorem B468343 : Blo 467785 468343 := bstep (se 1 (by rfl) ⟨351257, by rfl⟩ : syracuseStep 468343 = 702515) B702515
theorem B468363 : Blo 467785 468363 := bstep (se 1 (by rfl) ⟨351272, by rfl⟩ : syracuseStep 468363 = 702545) B702545
theorem B468375 : Blo 467785 468375 := bstep (se 1 (by rfl) ⟨351281, by rfl⟩ : syracuseStep 468375 = 702563) B702563
theorem B1058201 : Blo 467785 1058201 := bstep (se 2 (by rfl) ⟨396825, by rfl⟩ : syracuseStep 1058201 = 793651) B793651
theorem B468395 : Blo 467785 468395 := bstep (se 1 (by rfl) ⟨351296, by rfl⟩ : syracuseStep 468395 = 702593) B702593
theorem B468407 : Blo 467785 468407 := bstep (se 1 (by rfl) ⟨351305, by rfl⟩ : syracuseStep 468407 = 702611) B702611
theorem B1189313 : Blo 467785 1189313 := bstep (se 2 (by rfl) ⟨445992, by rfl⟩ : syracuseStep 1189313 = 891985) B891985
theorem B468427 : Blo 467785 468427 := bstep (se 1 (by rfl) ⟨351320, by rfl⟩ : syracuseStep 468427 = 702641) B702641
theorem B468439 : Blo 467785 468439 := bstep (se 1 (by rfl) ⟨351329, by rfl⟩ : syracuseStep 468439 = 702659) B702659
theorem B468459 : Blo 467785 468459 := bstep (se 1 (by rfl) ⟨351344, by rfl⟩ : syracuseStep 468459 = 702689) B702689
theorem B1058291 : Blo 467785 1058291 := bstep (se 1 (by rfl) ⟨793718, by rfl⟩ : syracuseStep 1058291 = 1587437) B1587437
theorem B468471 : Blo 467785 468471 := bstep (se 1 (by rfl) ⟨351353, by rfl⟩ : syracuseStep 468471 = 702707) B702707
theorem B468491 : Blo 467785 468491 := bstep (se 1 (by rfl) ⟨351368, by rfl⟩ : syracuseStep 468491 = 702737) B702737
theorem B468503 : Blo 467785 468503 := bstep (se 1 (by rfl) ⟨351377, by rfl⟩ : syracuseStep 468503 = 702755) B702755
theorem B1058327 : Blo 467785 1058327 := bstep (se 1 (by rfl) ⟨793745, by rfl⟩ : syracuseStep 1058327 = 1587491) B1587491
theorem B468523 : Blo 467785 468523 := bstep (se 1 (by rfl) ⟨351392, by rfl⟩ : syracuseStep 468523 = 702785) B702785
theorem B468535 : Blo 467785 468535 := bstep (se 1 (by rfl) ⟨351401, by rfl⟩ : syracuseStep 468535 = 702803) B702803
theorem B468555 : Blo 467785 468555 := bstep (se 1 (by rfl) ⟨351416, by rfl⟩ : syracuseStep 468555 = 702833) B702833
theorem B468567 : Blo 467785 468567 := bstep (se 1 (by rfl) ⟨351425, by rfl⟩ : syracuseStep 468567 = 702851) B702851
theorem B1582685 : Blo 467785 1582685 := bstep (se 3 (by rfl) ⟨296753, by rfl⟩ : syracuseStep 1582685 = 593507) B593507
theorem B468587 : Blo 467785 468587 := bstep (se 1 (by rfl) ⟨351440, by rfl⟩ : syracuseStep 468587 = 702881) B702881
theorem B468599 : Blo 467785 468599 := bstep (se 1 (by rfl) ⟨351449, by rfl⟩ : syracuseStep 468599 = 702899) B702899
theorem B468619 : Blo 467785 468619 := bstep (se 1 (by rfl) ⟨351464, by rfl⟩ : syracuseStep 468619 = 702929) B702929
theorem B468631 : Blo 467785 468631 := bstep (se 1 (by rfl) ⟨351473, by rfl⟩ : syracuseStep 468631 = 702947) B702947
theorem B468651 : Blo 467785 468651 := bstep (se 1 (by rfl) ⟨351488, by rfl⟩ : syracuseStep 468651 = 702977) B702977
theorem B468663 : Blo 467785 468663 := bstep (se 1 (by rfl) ⟨351497, by rfl⟩ : syracuseStep 468663 = 702995) B702995
theorem B468683 : Blo 467785 468683 := bstep (se 1 (by rfl) ⟨351512, by rfl⟩ : syracuseStep 468683 = 703025) B703025
theorem B1058507 : Blo 467785 1058507 := bstep (se 1 (by rfl) ⟨793880, by rfl⟩ : syracuseStep 1058507 = 1587761) B1587761
theorem B468695 : Blo 467785 468695 := bstep (se 1 (by rfl) ⟨351521, by rfl⟩ : syracuseStep 468695 = 703043) B703043
theorem B468715 : Blo 467785 468715 := bstep (se 1 (by rfl) ⟨351536, by rfl⟩ : syracuseStep 468715 = 703073) B703073
theorem B468727 : Blo 467785 468727 := bstep (se 1 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 468727 = 703091) B703091
theorem B1058561 : Blo 467785 1058561 := bstep (se 2 (by rfl) ⟨396960, by rfl⟩ : syracuseStep 1058561 = 793921) B793921
theorem B468747 : Blo 467785 468747 := bstep (se 1 (by rfl) ⟨351560, by rfl⟩ : syracuseStep 468747 = 703121) B703121
theorem B468759 : Blo 467785 468759 := bstep (se 1 (by rfl) ⟨351569, by rfl⟩ : syracuseStep 468759 = 703139) B703139
theorem B468779 : Blo 467785 468779 := bstep (se 1 (by rfl) ⟨351584, by rfl⟩ : syracuseStep 468779 = 703169) B703169
theorem B468791 : Blo 467785 468791 := bstep (se 1 (by rfl) ⟨351593, by rfl⟩ : syracuseStep 468791 = 703187) B703187
theorem B468811 : Blo 467785 468811 := bstep (se 1 (by rfl) ⟨351608, by rfl⟩ : syracuseStep 468811 = 703217) B703217
theorem B468823 : Blo 467785 468823 := bstep (se 1 (by rfl) ⟨351617, by rfl⟩ : syracuseStep 468823 = 703235) B703235
theorem B468843 : Blo 467785 468843 := bstep (se 1 (by rfl) ⟨351632, by rfl⟩ : syracuseStep 468843 = 703265) B703265
theorem B468855 : Blo 467785 468855 := bstep (se 1 (by rfl) ⟨351641, by rfl⟩ : syracuseStep 468855 = 703283) B703283
theorem B2369411 : Blo 467785 2369411 := bstep (se 1 (by rfl) ⟨1777058, by rfl⟩ : syracuseStep 2369411 = 3554117) B3554117
theorem B468875 : Blo 467785 468875 := bstep (se 1 (by rfl) ⟨351656, by rfl⟩ : syracuseStep 468875 = 703313) B703313
theorem B468887 : Blo 467785 468887 := bstep (se 1 (by rfl) ⟨351665, by rfl⟩ : syracuseStep 468887 = 703331) B703331
theorem B468907 : Blo 467785 468907 := bstep (se 1 (by rfl) ⟨351680, by rfl⟩ : syracuseStep 468907 = 703361) B703361
theorem B468919 : Blo 467785 468919 := bstep (se 1 (by rfl) ⟨351689, by rfl⟩ : syracuseStep 468919 = 703379) B703379
theorem B468939 : Blo 467785 468939 := bstep (se 1 (by rfl) ⟨351704, by rfl⟩ : syracuseStep 468939 = 703409) B703409
theorem B468951 : Blo 467785 468951 := bstep (se 1 (by rfl) ⟨351713, by rfl⟩ : syracuseStep 468951 = 703427) B703427
theorem B1189849 : Blo 467785 1189849 := bstep (se 2 (by rfl) ⟨446193, by rfl⟩ : syracuseStep 1189849 = 892387) B892387
theorem B1058777 : Blo 467785 1058777 := bstep (se 2 (by rfl) ⟨397041, by rfl⟩ : syracuseStep 1058777 = 794083) B794083
theorem B468971 : Blo 467785 468971 := bstep (se 1 (by rfl) ⟨351728, by rfl⟩ : syracuseStep 468971 = 703457) B703457
theorem B468983 : Blo 467785 468983 := bstep (se 1 (by rfl) ⟨351737, by rfl⟩ : syracuseStep 468983 = 703475) B703475
theorem B469003 : Blo 467785 469003 := bstep (se 1 (by rfl) ⟨351752, by rfl⟩ : syracuseStep 469003 = 703505) B703505
theorem B469015 : Blo 467785 469015 := bstep (se 1 (by rfl) ⟨351761, by rfl⟩ : syracuseStep 469015 = 703523) B703523
theorem B469035 : Blo 467785 469035 := bstep (se 1 (by rfl) ⟨351776, by rfl⟩ : syracuseStep 469035 = 703553) B703553
theorem B1058867 : Blo 467785 1058867 := bstep (se 1 (by rfl) ⟨794150, by rfl⟩ : syracuseStep 1058867 = 1588301) B1588301
theorem B469047 : Blo 467785 469047 := bstep (se 1 (by rfl) ⟨351785, by rfl⟩ : syracuseStep 469047 = 703571) B703571
theorem B469067 : Blo 467785 469067 := bstep (se 1 (by rfl) ⟨351800, by rfl⟩ : syracuseStep 469067 = 703601) B703601
theorem B469079 : Blo 467785 469079 := bstep (se 1 (by rfl) ⟨351809, by rfl⟩ : syracuseStep 469079 = 703619) B703619
theorem B1058903 : Blo 467785 1058903 := bstep (se 1 (by rfl) ⟨794177, by rfl⟩ : syracuseStep 1058903 = 1588355) B1588355
theorem B469099 : Blo 467785 469099 := bstep (se 1 (by rfl) ⟨351824, by rfl⟩ : syracuseStep 469099 = 703649) B703649
theorem B469111 : Blo 467785 469111 := bstep (se 1 (by rfl) ⟨351833, by rfl⟩ : syracuseStep 469111 = 703667) B703667
theorem B469131 : Blo 467785 469131 := bstep (se 1 (by rfl) ⟨351848, by rfl⟩ : syracuseStep 469131 = 703697) B703697
theorem B469143 : Blo 467785 469143 := bstep (se 1 (by rfl) ⟨351857, by rfl⟩ : syracuseStep 469143 = 703715) B703715
theorem B469163 : Blo 467785 469163 := bstep (se 1 (by rfl) ⟨351872, by rfl⟩ : syracuseStep 469163 = 703745) B703745
theorem B469175 : Blo 467785 469175 := bstep (se 1 (by rfl) ⟨351881, by rfl⟩ : syracuseStep 469175 = 703763) B703763
theorem B469195 : Blo 467785 469195 := bstep (se 1 (by rfl) ⟨351896, by rfl⟩ : syracuseStep 469195 = 703793) B703793
theorem B469207 : Blo 467785 469207 := bstep (se 1 (by rfl) ⟨351905, by rfl⟩ : syracuseStep 469207 = 703811) B703811
theorem B469227 : Blo 467785 469227 := bstep (se 1 (by rfl) ⟨351920, by rfl⟩ : syracuseStep 469227 = 703841) B703841
theorem B469239 : Blo 467785 469239 := bstep (se 1 (by rfl) ⟨351929, by rfl⟩ : syracuseStep 469239 = 703859) B703859
theorem B469259 : Blo 467785 469259 := bstep (se 1 (by rfl) ⟨351944, by rfl⟩ : syracuseStep 469259 = 703889) B703889
theorem B1059083 : Blo 467785 1059083 := bstep (se 1 (by rfl) ⟨794312, by rfl⟩ : syracuseStep 1059083 = 1588625) B1588625
theorem B469271 : Blo 467785 469271 := bstep (se 1 (by rfl) ⟨351953, by rfl⟩ : syracuseStep 469271 = 703907) B703907
theorem B469291 : Blo 467785 469291 := bstep (se 1 (by rfl) ⟨351968, by rfl⟩ : syracuseStep 469291 = 703937) B703937
theorem B469303 : Blo 467785 469303 := bstep (se 1 (by rfl) ⟨351977, by rfl⟩ : syracuseStep 469303 = 703955) B703955
theorem B1059137 : Blo 467785 1059137 := bstep (se 2 (by rfl) ⟨397176, by rfl⟩ : syracuseStep 1059137 = 794353) B794353
theorem B469323 : Blo 467785 469323 := bstep (se 1 (by rfl) ⟨351992, by rfl⟩ : syracuseStep 469323 = 703985) B703985
theorem B469335 : Blo 467785 469335 := bstep (se 1 (by rfl) ⟨352001, by rfl⟩ : syracuseStep 469335 = 704003) B704003
theorem B469355 : Blo 467785 469355 := bstep (se 1 (by rfl) ⟨352016, by rfl⟩ : syracuseStep 469355 = 704033) B704033
theorem B469367 : Blo 467785 469367 := bstep (se 1 (by rfl) ⟨352025, by rfl⟩ : syracuseStep 469367 = 704051) B704051
theorem B469387 : Blo 467785 469387 := bstep (se 1 (by rfl) ⟨352040, by rfl⟩ : syracuseStep 469387 = 704081) B704081
theorem B469399 : Blo 467785 469399 := bstep (se 1 (by rfl) ⟨352049, by rfl⟩ : syracuseStep 469399 = 704099) B704099
theorem B469419 : Blo 467785 469419 := bstep (se 1 (by rfl) ⟨352064, by rfl⟩ : syracuseStep 469419 = 704129) B704129
theorem B469431 : Blo 467785 469431 := bstep (se 1 (by rfl) ⟨352073, by rfl⟩ : syracuseStep 469431 = 704147) B704147
theorem B469451 : Blo 467785 469451 := bstep (se 1 (by rfl) ⟨352088, by rfl⟩ : syracuseStep 469451 = 704177) B704177
theorem B469463 : Blo 467785 469463 := bstep (se 1 (by rfl) ⟨352097, by rfl⟩ : syracuseStep 469463 = 704195) B704195
theorem B666073 : Blo 467785 666073 := bstep (se 2 (by rfl) ⟨249777, by rfl⟩ : syracuseStep 666073 = 499555) B499555
theorem B469483 : Blo 467785 469483 := bstep (se 1 (by rfl) ⟨352112, by rfl⟩ : syracuseStep 469483 = 704225) B704225
theorem B469495 : Blo 467785 469495 := bstep (se 1 (by rfl) ⟨352121, by rfl⟩ : syracuseStep 469495 = 704243) B704243
theorem B469515 : Blo 467785 469515 := bstep (se 1 (by rfl) ⟨352136, by rfl⟩ : syracuseStep 469515 = 704273) B704273
theorem B469527 : Blo 467785 469527 := bstep (se 1 (by rfl) ⟨352145, by rfl⟩ : syracuseStep 469527 = 704291) B704291
theorem B1059353 : Blo 467785 1059353 := bstep (se 2 (by rfl) ⟨397257, by rfl⟩ : syracuseStep 1059353 = 794515) B794515
theorem B469547 : Blo 467785 469547 := bstep (se 1 (by rfl) ⟨352160, by rfl⟩ : syracuseStep 469547 = 704321) B704321
theorem B469559 : Blo 467785 469559 := bstep (se 1 (by rfl) ⟨352169, by rfl⟩ : syracuseStep 469559 = 704339) B704339
theorem B3385921 : Blo 467785 3385921 := bstep (se 2 (by rfl) ⟨1269720, by rfl⟩ : syracuseStep 3385921 = 2539441) B2539441
theorem B469579 : Blo 467785 469579 := bstep (se 1 (by rfl) ⟨352184, by rfl⟩ : syracuseStep 469579 = 704369) B704369
theorem B469591 : Blo 467785 469591 := bstep (se 1 (by rfl) ⟨352193, by rfl⟩ : syracuseStep 469591 = 704387) B704387
theorem B469611 : Blo 467785 469611 := bstep (se 1 (by rfl) ⟨352208, by rfl⟩ : syracuseStep 469611 = 704417) B704417
theorem B1059443 : Blo 467785 1059443 := bstep (se 1 (by rfl) ⟨794582, by rfl⟩ : syracuseStep 1059443 = 1589165) B1589165
theorem B469623 : Blo 467785 469623 := bstep (se 1 (by rfl) ⟨352217, by rfl⟩ : syracuseStep 469623 = 704435) B704435
theorem B469643 : Blo 467785 469643 := bstep (se 1 (by rfl) ⟨352232, by rfl⟩ : syracuseStep 469643 = 704465) B704465
theorem B469655 : Blo 467785 469655 := bstep (se 1 (by rfl) ⟨352241, by rfl⟩ : syracuseStep 469655 = 704483) B704483
theorem B1059479 : Blo 467785 1059479 := bstep (se 1 (by rfl) ⟨794609, by rfl⟩ : syracuseStep 1059479 = 1589219) B1589219
theorem B469675 : Blo 467785 469675 := bstep (se 1 (by rfl) ⟨352256, by rfl⟩ : syracuseStep 469675 = 704513) B704513
theorem B469687 : Blo 467785 469687 := bstep (se 1 (by rfl) ⟨352265, by rfl⟩ : syracuseStep 469687 = 704531) B704531
theorem B1583819 : Blo 467785 1583819 := bstep (se 1 (by rfl) ⟨1187864, by rfl⟩ : syracuseStep 1583819 = 2375729) B2375729
theorem B469707 : Blo 467785 469707 := bstep (se 1 (by rfl) ⟨352280, by rfl⟩ : syracuseStep 469707 = 704561) B704561
theorem B469719 : Blo 467785 469719 := bstep (se 1 (by rfl) ⟨352289, by rfl⟩ : syracuseStep 469719 = 704579) B704579
theorem B469739 : Blo 467785 469739 := bstep (se 1 (by rfl) ⟨352304, by rfl⟩ : syracuseStep 469739 = 704609) B704609
theorem B469751 : Blo 467785 469751 := bstep (se 1 (by rfl) ⟨352313, by rfl⟩ : syracuseStep 469751 = 704627) B704627
theorem B469771 : Blo 467785 469771 := bstep (se 1 (by rfl) ⟨352328, by rfl⟩ : syracuseStep 469771 = 704657) B704657
theorem B469783 : Blo 467785 469783 := bstep (se 1 (by rfl) ⟨352337, by rfl⟩ : syracuseStep 469783 = 704675) B704675
theorem B469803 : Blo 467785 469803 := bstep (se 1 (by rfl) ⟨352352, by rfl⟩ : syracuseStep 469803 = 704705) B704705
theorem B469815 : Blo 467785 469815 := bstep (se 1 (by rfl) ⟨352361, by rfl⟩ : syracuseStep 469815 = 704723) B704723
theorem B502583 : Blo 467785 502583 := bstep (se 1 (by rfl) ⟨376937, by rfl⟩ : syracuseStep 502583 = 753875) B753875
theorem B469835 : Blo 467785 469835 := bstep (se 1 (by rfl) ⟨352376, by rfl⟩ : syracuseStep 469835 = 704753) B704753
theorem B1059659 : Blo 467785 1059659 := bstep (se 1 (by rfl) ⟨794744, by rfl⟩ : syracuseStep 1059659 = 1589489) B1589489
theorem B469847 : Blo 467785 469847 := bstep (se 1 (by rfl) ⟨352385, by rfl⟩ : syracuseStep 469847 = 704771) B704771
theorem B469867 : Blo 467785 469867 := bstep (se 1 (by rfl) ⟨352400, by rfl⟩ : syracuseStep 469867 = 704801) B704801
theorem B469879 : Blo 467785 469879 := bstep (se 1 (by rfl) ⟨352409, by rfl⟩ : syracuseStep 469879 = 704819) B704819
theorem B1059713 : Blo 467785 1059713 := bstep (se 2 (by rfl) ⟨397392, by rfl⟩ : syracuseStep 1059713 = 794785) B794785
theorem B469899 : Blo 467785 469899 := bstep (se 1 (by rfl) ⟨352424, by rfl⟩ : syracuseStep 469899 = 704849) B704849
theorem B469911 : Blo 467785 469911 := bstep (se 1 (by rfl) ⟨352433, by rfl⟩ : syracuseStep 469911 = 704867) B704867
theorem B469931 : Blo 467785 469931 := bstep (se 1 (by rfl) ⟨352448, by rfl⟩ : syracuseStep 469931 = 704897) B704897
theorem B3812275 : Blo 467785 3812275 := bstep (se 1 (by rfl) ⟨2859206, by rfl⟩ : syracuseStep 3812275 = 5718413) B5718413
theorem B469943 : Blo 467785 469943 := bstep (se 1 (by rfl) ⟨352457, by rfl⟩ : syracuseStep 469943 = 704915) B704915
theorem B469963 : Blo 467785 469963 := bstep (se 1 (by rfl) ⟨352472, by rfl⟩ : syracuseStep 469963 = 704945) B704945
theorem B2010059 : Blo 467785 2010059 := bstep (se 1 (by rfl) ⟨1507544, by rfl⟩ : syracuseStep 2010059 = 3015089) B3015089
theorem B469975 : Blo 467785 469975 := bstep (se 1 (by rfl) ⟨352481, by rfl⟩ : syracuseStep 469975 = 704963) B704963
theorem B1584089 : Blo 467785 1584089 := bstep (se 2 (by rfl) ⟨594033, by rfl⟩ : syracuseStep 1584089 = 1188067) B1188067
theorem B469995 : Blo 467785 469995 := bstep (se 1 (by rfl) ⟨352496, by rfl⟩ : syracuseStep 469995 = 704993) B704993
theorem B470007 : Blo 467785 470007 := bstep (se 1 (by rfl) ⟨352505, by rfl⟩ : syracuseStep 470007 = 705011) B705011
theorem B470027 : Blo 467785 470027 := bstep (se 1 (by rfl) ⟨352520, by rfl⟩ : syracuseStep 470027 = 705041) B705041
theorem B470039 : Blo 467785 470039 := bstep (se 1 (by rfl) ⟨352529, by rfl⟩ : syracuseStep 470039 = 705059) B705059
theorem B470059 : Blo 467785 470059 := bstep (se 1 (by rfl) ⟨352544, by rfl⟩ : syracuseStep 470059 = 705089) B705089
theorem B1190963 : Blo 467785 1190963 := bstep (se 1 (by rfl) ⟨893222, by rfl⟩ : syracuseStep 1190963 = 1786445) B1786445
theorem B470071 : Blo 467785 470071 := bstep (se 1 (by rfl) ⟨352553, by rfl⟩ : syracuseStep 470071 = 705107) B705107
theorem B1780811 : Blo 467785 1780811 := bstep (se 1 (by rfl) ⟨1335608, by rfl⟩ : syracuseStep 1780811 = 2671217) B2671217
theorem B470091 : Blo 467785 470091 := bstep (se 1 (by rfl) ⟨352568, by rfl⟩ : syracuseStep 470091 = 705137) B705137
theorem B470103 : Blo 467785 470103 := bstep (se 1 (by rfl) ⟨352577, by rfl⟩ : syracuseStep 470103 = 705155) B705155
theorem B1780825 : Blo 467785 1780825 := bstep (se 2 (by rfl) ⟨667809, by rfl⟩ : syracuseStep 1780825 = 1335619) B1335619
theorem B1059929 : Blo 467785 1059929 := bstep (se 2 (by rfl) ⟨397473, by rfl⟩ : syracuseStep 1059929 = 794947) B794947
theorem B470123 : Blo 467785 470123 := bstep (se 1 (by rfl) ⟨352592, by rfl⟩ : syracuseStep 470123 = 705185) B705185
theorem B470135 : Blo 467785 470135 := bstep (se 1 (by rfl) ⟨352601, by rfl⟩ : syracuseStep 470135 = 705203) B705203
theorem B535691 : Blo 467785 535691 := bstep (se 1 (by rfl) ⟨401768, by rfl⟩ : syracuseStep 535691 = 803537) B803537
theorem B470155 : Blo 467785 470155 := bstep (se 1 (by rfl) ⟨352616, by rfl⟩ : syracuseStep 470155 = 705233) B705233
theorem B470167 : Blo 467785 470167 := bstep (se 1 (by rfl) ⟨352625, by rfl⟩ : syracuseStep 470167 = 705251) B705251
theorem B470187 : Blo 467785 470187 := bstep (se 1 (by rfl) ⟨352640, by rfl⟩ : syracuseStep 470187 = 705281) B705281
theorem B1060019 : Blo 467785 1060019 := bstep (se 1 (by rfl) ⟨795014, by rfl⟩ : syracuseStep 1060019 = 1590029) B1590029
theorem B470199 : Blo 467785 470199 := bstep (se 1 (by rfl) ⟨352649, by rfl⟩ : syracuseStep 470199 = 705299) B705299
theorem B470219 : Blo 467785 470219 := bstep (se 1 (by rfl) ⟨352664, by rfl⟩ : syracuseStep 470219 = 705329) B705329
theorem B470231 : Blo 467785 470231 := bstep (se 1 (by rfl) ⟨352673, by rfl⟩ : syracuseStep 470231 = 705347) B705347
theorem B1060055 : Blo 467785 1060055 := bstep (se 1 (by rfl) ⟨795041, by rfl⟩ : syracuseStep 1060055 = 1590083) B1590083
theorem B470251 : Blo 467785 470251 := bstep (se 1 (by rfl) ⟨352688, by rfl⟩ : syracuseStep 470251 = 705377) B705377
theorem B470263 : Blo 467785 470263 := bstep (se 1 (by rfl) ⟨352697, by rfl⟩ : syracuseStep 470263 = 705395) B705395
theorem B470283 : Blo 467785 470283 := bstep (se 1 (by rfl) ⟨352712, by rfl⟩ : syracuseStep 470283 = 705425) B705425
theorem B470295 : Blo 467785 470295 := bstep (se 1 (by rfl) ⟨352721, by rfl⟩ : syracuseStep 470295 = 705443) B705443
theorem B470315 : Blo 467785 470315 := bstep (se 1 (by rfl) ⟨352736, by rfl⟩ : syracuseStep 470315 = 705473) B705473
theorem B470327 : Blo 467785 470327 := bstep (se 1 (by rfl) ⟨352745, by rfl⟩ : syracuseStep 470327 = 705491) B705491
theorem B470347 : Blo 467785 470347 := bstep (se 1 (by rfl) ⟨352760, by rfl⟩ : syracuseStep 470347 = 705521) B705521
theorem B666967 : Blo 467785 666967 := bstep (se 1 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 666967 = 1000451) B1000451
theorem B470359 : Blo 467785 470359 := bstep (se 1 (by rfl) ⟨352769, by rfl⟩ : syracuseStep 470359 = 705539) B705539
theorem B1191257 : Blo 467785 1191257 := bstep (se 2 (by rfl) ⟨446721, by rfl⟩ : syracuseStep 1191257 = 893443) B893443
theorem B470379 : Blo 467785 470379 := bstep (se 1 (by rfl) ⟨352784, by rfl⟩ : syracuseStep 470379 = 705569) B705569
theorem B470391 : Blo 467785 470391 := bstep (se 1 (by rfl) ⟨352793, by rfl⟩ : syracuseStep 470391 = 705587) B705587
theorem B470411 : Blo 467785 470411 := bstep (se 1 (by rfl) ⟨352808, by rfl⟩ : syracuseStep 470411 = 705617) B705617
theorem B1060235 : Blo 467785 1060235 := bstep (se 1 (by rfl) ⟨795176, by rfl⟩ : syracuseStep 1060235 = 1590353) B1590353
theorem B470423 : Blo 467785 470423 := bstep (se 1 (by rfl) ⟨352817, by rfl⟩ : syracuseStep 470423 = 705635) B705635
theorem B470443 : Blo 467785 470443 := bstep (se 1 (by rfl) ⟨352832, by rfl⟩ : syracuseStep 470443 = 705665) B705665
theorem B470455 : Blo 467785 470455 := bstep (se 1 (by rfl) ⟨352841, by rfl⟩ : syracuseStep 470455 = 705683) B705683
theorem B1060289 : Blo 467785 1060289 := bstep (se 2 (by rfl) ⟨397608, by rfl⟩ : syracuseStep 1060289 = 795217) B795217
theorem B470475 : Blo 467785 470475 := bstep (se 1 (by rfl) ⟨352856, by rfl⟩ : syracuseStep 470475 = 705713) B705713
theorem B470487 : Blo 467785 470487 := bstep (se 1 (by rfl) ⟨352865, by rfl⟩ : syracuseStep 470487 = 705731) B705731
theorem B470507 : Blo 467785 470507 := bstep (se 1 (by rfl) ⟨352880, by rfl⟩ : syracuseStep 470507 = 705761) B705761
theorem B470519 : Blo 467785 470519 := bstep (se 1 (by rfl) ⟨352889, by rfl⟩ : syracuseStep 470519 = 705779) B705779
theorem B470539 : Blo 467785 470539 := bstep (se 1 (by rfl) ⟨352904, by rfl⟩ : syracuseStep 470539 = 705809) B705809
theorem B470551 : Blo 467785 470551 := bstep (se 1 (by rfl) ⟨352913, by rfl⟩ : syracuseStep 470551 = 705827) B705827
theorem B470571 : Blo 467785 470571 := bstep (se 1 (by rfl) ⟨352928, by rfl⟩ : syracuseStep 470571 = 705857) B705857
theorem B470583 : Blo 467785 470583 := bstep (se 1 (by rfl) ⟨352937, by rfl⟩ : syracuseStep 470583 = 705875) B705875
theorem B470603 : Blo 467785 470603 := bstep (se 1 (by rfl) ⟨352952, by rfl⟩ : syracuseStep 470603 = 705905) B705905
theorem B470615 : Blo 467785 470615 := bstep (se 1 (by rfl) ⟨352961, by rfl⟩ : syracuseStep 470615 = 705923) B705923
theorem B470635 : Blo 467785 470635 := bstep (se 1 (by rfl) ⟨352976, by rfl⟩ : syracuseStep 470635 = 705953) B705953
theorem B470647 : Blo 467785 470647 := bstep (se 1 (by rfl) ⟨352985, by rfl⟩ : syracuseStep 470647 = 705971) B705971
theorem B470667 : Blo 467785 470667 := bstep (se 1 (by rfl) ⟨353000, by rfl⟩ : syracuseStep 470667 = 706001) B706001
theorem B2666135 : Blo 467785 2666135 := bstep (se 1 (by rfl) ⟨1999601, by rfl⟩ : syracuseStep 2666135 = 3999203) B3999203
theorem B1584791 : Blo 467785 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B470679 : Blo 467785 470679 := bstep (se 1 (by rfl) ⟨353009, by rfl⟩ : syracuseStep 470679 = 706019) B706019
theorem B1060505 : Blo 467785 1060505 := bstep (se 2 (by rfl) ⟨397689, by rfl⟩ : syracuseStep 1060505 = 795379) B795379
theorem B470699 : Blo 467785 470699 := bstep (se 1 (by rfl) ⟨353024, by rfl⟩ : syracuseStep 470699 = 706049) B706049
theorem B470711 : Blo 467785 470711 := bstep (se 1 (by rfl) ⟨353033, by rfl⟩ : syracuseStep 470711 = 706067) B706067
theorem B470731 : Blo 467785 470731 := bstep (se 1 (by rfl) ⟨353048, by rfl⟩ : syracuseStep 470731 = 706097) B706097
theorem B470743 : Blo 467785 470743 := bstep (se 1 (by rfl) ⟨353057, by rfl⟩ : syracuseStep 470743 = 706115) B706115
theorem B2010845 : Blo 467785 2010845 := bstep (se 3 (by rfl) ⟨377033, by rfl⟩ : syracuseStep 2010845 = 754067) B754067
theorem B470763 : Blo 467785 470763 := bstep (se 1 (by rfl) ⟨353072, by rfl⟩ : syracuseStep 470763 = 706145) B706145
theorem B1060595 : Blo 467785 1060595 := bstep (se 1 (by rfl) ⟨795446, by rfl⟩ : syracuseStep 1060595 = 1590893) B1590893
theorem B470775 : Blo 467785 470775 := bstep (se 1 (by rfl) ⟨353081, by rfl⟩ : syracuseStep 470775 = 706163) B706163
theorem B470795 : Blo 467785 470795 := bstep (se 1 (by rfl) ⟨353096, by rfl⟩ : syracuseStep 470795 = 706193) B706193
theorem B470807 : Blo 467785 470807 := bstep (se 1 (by rfl) ⟨353105, by rfl⟩ : syracuseStep 470807 = 706211) B706211
theorem B1060631 : Blo 467785 1060631 := bstep (se 1 (by rfl) ⟨795473, by rfl⟩ : syracuseStep 1060631 = 1590947) B1590947
theorem B470827 : Blo 467785 470827 := bstep (se 1 (by rfl) ⟨353120, by rfl⟩ : syracuseStep 470827 = 706241) B706241
theorem B470839 : Blo 467785 470839 := bstep (se 1 (by rfl) ⟨353129, by rfl⟩ : syracuseStep 470839 = 706259) B706259
theorem B470859 : Blo 467785 470859 := bstep (se 1 (by rfl) ⟨353144, by rfl⟩ : syracuseStep 470859 = 706289) B706289
theorem B470871 : Blo 467785 470871 := bstep (se 1 (by rfl) ⟨353153, by rfl⟩ : syracuseStep 470871 = 706307) B706307
theorem B470891 : Blo 467785 470891 := bstep (se 1 (by rfl) ⟨353168, by rfl⟩ : syracuseStep 470891 = 706337) B706337
theorem B470903 : Blo 467785 470903 := bstep (se 1 (by rfl) ⟨353177, by rfl⟩ : syracuseStep 470903 = 706355) B706355
theorem B667531 : Blo 467785 667531 := bstep (se 1 (by rfl) ⟨500648, by rfl⟩ : syracuseStep 667531 = 1001297) B1001297
theorem B634763 : Blo 467785 634763 := bstep (se 1 (by rfl) ⟨476072, by rfl⟩ : syracuseStep 634763 = 952145) B952145
theorem B470923 : Blo 467785 470923 := bstep (se 1 (by rfl) ⟨353192, by rfl⟩ : syracuseStep 470923 = 706385) B706385
theorem B470935 : Blo 467785 470935 := bstep (se 1 (by rfl) ⟨353201, by rfl⟩ : syracuseStep 470935 = 706403) B706403
theorem B470955 : Blo 467785 470955 := bstep (se 1 (by rfl) ⟨353216, by rfl⟩ : syracuseStep 470955 = 706433) B706433
theorem B470967 : Blo 467785 470967 := bstep (se 1 (by rfl) ⟨353225, by rfl⟩ : syracuseStep 470967 = 706451) B706451
theorem B470987 : Blo 467785 470987 := bstep (se 1 (by rfl) ⟨353240, by rfl⟩ : syracuseStep 470987 = 706481) B706481
theorem B1060811 : Blo 467785 1060811 := bstep (se 1 (by rfl) ⟨795608, by rfl⟩ : syracuseStep 1060811 = 1591217) B1591217
theorem B470999 : Blo 467785 470999 := bstep (se 1 (by rfl) ⟨353249, by rfl⟩ : syracuseStep 470999 = 706499) B706499
theorem B471019 : Blo 467785 471019 := bstep (se 1 (by rfl) ⟨353264, by rfl⟩ : syracuseStep 471019 = 706529) B706529
theorem B471031 : Blo 467785 471031 := bstep (se 1 (by rfl) ⟨353273, by rfl⟩ : syracuseStep 471031 = 706547) B706547
theorem B1060865 : Blo 467785 1060865 := bstep (se 2 (by rfl) ⟨397824, by rfl⟩ : syracuseStep 1060865 = 795649) B795649
theorem B471051 : Blo 467785 471051 := bstep (se 1 (by rfl) ⟨353288, by rfl⟩ : syracuseStep 471051 = 706577) B706577
theorem B1781783 : Blo 467785 1781783 := bstep (se 1 (by rfl) ⟨1336337, by rfl⟩ : syracuseStep 1781783 = 2672675) B2672675
theorem B471063 : Blo 467785 471063 := bstep (se 1 (by rfl) ⟨353297, by rfl⟩ : syracuseStep 471063 = 706595) B706595
theorem B471083 : Blo 467785 471083 := bstep (se 1 (by rfl) ⟨353312, by rfl⟩ : syracuseStep 471083 = 706625) B706625
theorem B471095 : Blo 467785 471095 := bstep (se 1 (by rfl) ⟨353321, by rfl⟩ : syracuseStep 471095 = 706643) B706643
theorem B471115 : Blo 467785 471115 := bstep (se 1 (by rfl) ⟨353336, by rfl⟩ : syracuseStep 471115 = 706673) B706673
theorem B471127 : Blo 467785 471127 := bstep (se 1 (by rfl) ⟨353345, by rfl⟩ : syracuseStep 471127 = 706691) B706691
theorem B471147 : Blo 467785 471147 := bstep (se 1 (by rfl) ⟨353360, by rfl⟩ : syracuseStep 471147 = 706721) B706721
theorem B471159 : Blo 467785 471159 := bstep (se 1 (by rfl) ⟨353369, by rfl⟩ : syracuseStep 471159 = 706739) B706739
theorem B471179 : Blo 467785 471179 := bstep (se 1 (by rfl) ⟨353384, by rfl⟩ : syracuseStep 471179 = 706769) B706769
theorem B471191 : Blo 467785 471191 := bstep (se 1 (by rfl) ⟨353393, by rfl⟩ : syracuseStep 471191 = 706787) B706787
theorem B471211 : Blo 467785 471211 := bstep (se 1 (by rfl) ⟨353408, by rfl⟩ : syracuseStep 471211 = 706817) B706817
theorem B1585331 : Blo 467785 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B471223 : Blo 467785 471223 := bstep (se 1 (by rfl) ⟨353417, by rfl⟩ : syracuseStep 471223 = 706835) B706835
theorem B471243 : Blo 467785 471243 := bstep (se 1 (by rfl) ⟨353432, by rfl⟩ : syracuseStep 471243 = 706865) B706865
theorem B471255 : Blo 467785 471255 := bstep (se 1 (by rfl) ⟨353441, by rfl⟩ : syracuseStep 471255 = 706883) B706883
theorem B1061081 : Blo 467785 1061081 := bstep (se 2 (by rfl) ⟨397905, by rfl⟩ : syracuseStep 1061081 = 795811) B795811
theorem B471275 : Blo 467785 471275 := bstep (se 1 (by rfl) ⟨353456, by rfl⟩ : syracuseStep 471275 = 706913) B706913
theorem B471287 : Blo 467785 471287 := bstep (se 1 (by rfl) ⟨353465, by rfl⟩ : syracuseStep 471287 = 706931) B706931
theorem B6041861 : Blo 467785 6041861 := bstep (se 4 (by rfl) ⟨566424, by rfl⟩ : syracuseStep 6041861 = 1132849) B1132849
theorem B471307 : Blo 467785 471307 := bstep (se 1 (by rfl) ⟨353480, by rfl⟩ : syracuseStep 471307 = 706961) B706961
theorem B471319 : Blo 467785 471319 := bstep (se 1 (by rfl) ⟨353489, by rfl⟩ : syracuseStep 471319 = 706979) B706979
theorem B471339 : Blo 467785 471339 := bstep (se 1 (by rfl) ⟨353504, by rfl⟩ : syracuseStep 471339 = 707009) B707009
theorem B1061171 : Blo 467785 1061171 := bstep (se 1 (by rfl) ⟨795878, by rfl⟩ : syracuseStep 1061171 = 1591757) B1591757
theorem B471351 : Blo 467785 471351 := bstep (se 1 (by rfl) ⟨353513, by rfl⟩ : syracuseStep 471351 = 707027) B707027
theorem B471371 : Blo 467785 471371 := bstep (se 1 (by rfl) ⟨353528, by rfl⟩ : syracuseStep 471371 = 707057) B707057
theorem B471383 : Blo 467785 471383 := bstep (se 1 (by rfl) ⟨353537, by rfl⟩ : syracuseStep 471383 = 707075) B707075
theorem B1061207 : Blo 467785 1061207 := bstep (se 1 (by rfl) ⟨795905, by rfl⟩ : syracuseStep 1061207 = 1591811) B1591811
theorem B471403 : Blo 467785 471403 := bstep (se 1 (by rfl) ⟨353552, by rfl⟩ : syracuseStep 471403 = 707105) B707105
theorem B15446389 : Blo 467785 15446389 := bstep (se 5 (by rfl) ⟨724049, by rfl⟩ : syracuseStep 15446389 = 1448099) B1448099
theorem B471415 : Blo 467785 471415 := bstep (se 1 (by rfl) ⟨353561, by rfl⟩ : syracuseStep 471415 = 707123) B707123
theorem B471435 : Blo 467785 471435 := bstep (se 1 (by rfl) ⟨353576, by rfl⟩ : syracuseStep 471435 = 707153) B707153
theorem B471447 : Blo 467785 471447 := bstep (se 1 (by rfl) ⟨353585, by rfl⟩ : syracuseStep 471447 = 707171) B707171
theorem B471467 : Blo 467785 471467 := bstep (se 1 (by rfl) ⟨353600, by rfl⟩ : syracuseStep 471467 = 707201) B707201
theorem B471479 : Blo 467785 471479 := bstep (se 1 (by rfl) ⟨353609, by rfl⟩ : syracuseStep 471479 = 707219) B707219
theorem B1585601 : Blo 467785 1585601 := bstep (se 2 (by rfl) ⟨594600, by rfl⟩ : syracuseStep 1585601 = 1189201) B1189201
theorem B471499 : Blo 467785 471499 := bstep (se 1 (by rfl) ⟨353624, by rfl⟩ : syracuseStep 471499 = 707249) B707249
theorem B471511 : Blo 467785 471511 := bstep (se 1 (by rfl) ⟨353633, by rfl⟩ : syracuseStep 471511 = 707267) B707267
theorem B8565209 : Blo 467785 8565209 := bstep (se 2 (by rfl) ⟨3211953, by rfl⟩ : syracuseStep 8565209 = 6423907) B6423907
theorem B471531 : Blo 467785 471531 := bstep (se 1 (by rfl) ⟨353648, by rfl⟩ : syracuseStep 471531 = 707297) B707297
theorem B471543 : Blo 467785 471543 := bstep (se 1 (by rfl) ⟨353657, by rfl⟩ : syracuseStep 471543 = 707315) B707315
theorem B471563 : Blo 467785 471563 := bstep (se 1 (by rfl) ⟨353672, by rfl⟩ : syracuseStep 471563 = 707345) B707345
theorem B1061387 : Blo 467785 1061387 := bstep (se 1 (by rfl) ⟨796040, by rfl⟩ : syracuseStep 1061387 = 1592081) B1592081
theorem B471575 : Blo 467785 471575 := bstep (se 1 (by rfl) ⟨353681, by rfl⟩ : syracuseStep 471575 = 707363) B707363
theorem B471595 : Blo 467785 471595 := bstep (se 1 (by rfl) ⟨353696, by rfl⟩ : syracuseStep 471595 = 707393) B707393
theorem B471607 : Blo 467785 471607 := bstep (se 1 (by rfl) ⟨353705, by rfl⟩ : syracuseStep 471607 = 707411) B707411
theorem B1061441 : Blo 467785 1061441 := bstep (se 2 (by rfl) ⟨398040, by rfl⟩ : syracuseStep 1061441 = 796081) B796081
theorem B471627 : Blo 467785 471627 := bstep (se 1 (by rfl) ⟨353720, by rfl⟩ : syracuseStep 471627 = 707441) B707441
theorem B471639 : Blo 467785 471639 := bstep (se 1 (by rfl) ⟨353729, by rfl⟩ : syracuseStep 471639 = 707459) B707459
theorem B471659 : Blo 467785 471659 := bstep (se 1 (by rfl) ⟨353744, by rfl⟩ : syracuseStep 471659 = 707489) B707489
theorem B471671 : Blo 467785 471671 := bstep (se 1 (by rfl) ⟨353753, by rfl⟩ : syracuseStep 471671 = 707507) B707507
theorem B471691 : Blo 467785 471691 := bstep (se 1 (by rfl) ⟨353768, by rfl⟩ : syracuseStep 471691 = 707537) B707537
theorem B471703 : Blo 467785 471703 := bstep (se 1 (by rfl) ⟨353777, by rfl⟩ : syracuseStep 471703 = 707555) B707555
theorem B471723 : Blo 467785 471723 := bstep (se 1 (by rfl) ⟨353792, by rfl⟩ : syracuseStep 471723 = 707585) B707585
theorem B471735 : Blo 467785 471735 := bstep (se 1 (by rfl) ⟨353801, by rfl⟩ : syracuseStep 471735 = 707603) B707603
theorem B471755 : Blo 467785 471755 := bstep (se 1 (by rfl) ⟨353816, by rfl⟩ : syracuseStep 471755 = 707633) B707633
theorem B471767 : Blo 467785 471767 := bstep (se 1 (by rfl) ⟨353825, by rfl⟩ : syracuseStep 471767 = 707651) B707651
theorem B635671 : Blo 467785 635671 := bstep (se 1 (by rfl) ⟨476753, by rfl⟩ : syracuseStep 635671 = 953507) B953507
theorem B1192907 : Blo 467785 1192907 := bstep (se 1 (by rfl) ⟨894680, by rfl⟩ : syracuseStep 1192907 = 1789361) B1789361
theorem B1586141 : Blo 467785 1586141 := bstep (se 3 (by rfl) ⟨297401, by rfl⟩ : syracuseStep 1586141 = 594803) B594803
theorem B2012177 : Blo 467785 2012177 := bstep (se 2 (by rfl) ⟨754566, by rfl⟩ : syracuseStep 2012177 = 1509133) B1509133
theorem B1783043 : Blo 467785 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B701771 : Blo 467785 701771 := bstep (se 1 (by rfl) ⟨526328, by rfl⟩ : syracuseStep 701771 = 1052657) B1052657
theorem B701783 : Blo 467785 701783 := bstep (se 1 (by rfl) ⟨526337, by rfl⟩ : syracuseStep 701783 = 1052675) B1052675
theorem B669017 : Blo 467785 669017 := bstep (se 2 (by rfl) ⟨250881, by rfl⟩ : syracuseStep 669017 = 501763) B501763
theorem B4273559 : Blo 467785 4273559 := bstep (se 1 (by rfl) ⟨3205169, by rfl⟩ : syracuseStep 4273559 = 6410339) B6410339
theorem B701849 : Blo 467785 701849 := bstep (se 2 (by rfl) ⟨263193, by rfl⟩ : syracuseStep 701849 = 526387) B526387
theorem B701963 : Blo 467785 701963 := bstep (se 1 (by rfl) ⟨526472, by rfl⟩ : syracuseStep 701963 = 1052945) B1052945
theorem B2668049 : Blo 467785 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B2373137 : Blo 467785 2373137 := bstep (se 2 (by rfl) ⟨889926, by rfl⟩ : syracuseStep 2373137 = 1779853) B1779853
theorem B701975 : Blo 467785 701975 := bstep (se 1 (by rfl) ⟨526481, by rfl⟩ : syracuseStep 701975 = 1052963) B1052963
theorem B2405933 : Blo 467785 2405933 := bstep (se 3 (by rfl) ⟨451112, by rfl⟩ : syracuseStep 2405933 = 902225) B902225
theorem B702041 : Blo 467785 702041 := bstep (se 2 (by rfl) ⟨263265, by rfl⟩ : syracuseStep 702041 = 526531) B526531
theorem B3815063 : Blo 467785 3815063 := bstep (se 1 (by rfl) ⟨2861297, by rfl⟩ : syracuseStep 3815063 = 5722595) B5722595
theorem B2373299 : Blo 467785 2373299 := bstep (se 1 (by rfl) ⟨1779974, by rfl⟩ : syracuseStep 2373299 = 3559949) B3559949
theorem B702155 : Blo 467785 702155 := bstep (se 1 (by rfl) ⟨526616, by rfl⟩ : syracuseStep 702155 = 1053233) B1053233
theorem B800471 : Blo 467785 800471 := bstep (se 1 (by rfl) ⟨600353, by rfl⟩ : syracuseStep 800471 = 1200707) B1200707
theorem B702167 : Blo 467785 702167 := bstep (se 1 (by rfl) ⟨526625, by rfl⟩ : syracuseStep 702167 = 1053251) B1053251
theorem B702233 : Blo 467785 702233 := bstep (se 2 (by rfl) ⟨263337, by rfl⟩ : syracuseStep 702233 = 526675) B526675
theorem B702347 : Blo 467785 702347 := bstep (se 1 (by rfl) ⟨526760, by rfl⟩ : syracuseStep 702347 = 1053521) B1053521
theorem B702359 : Blo 467785 702359 := bstep (se 1 (by rfl) ⟨526769, by rfl⟩ : syracuseStep 702359 = 1053539) B1053539
theorem B1193879 : Blo 467785 1193879 := bstep (se 1 (by rfl) ⟨895409, by rfl⟩ : syracuseStep 1193879 = 1790819) B1790819
theorem B3094451 : Blo 467785 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B669655 : Blo 467785 669655 := bstep (se 1 (by rfl) ⟨502241, by rfl⟩ : syracuseStep 669655 = 1004483) B1004483
theorem B702425 : Blo 467785 702425 := bstep (se 2 (by rfl) ⟨263409, by rfl⟩ : syracuseStep 702425 = 526819) B526819
theorem B3356633 : Blo 467785 3356633 := bstep (se 2 (by rfl) ⟨1258737, by rfl⟩ : syracuseStep 3356633 = 2517475) B2517475
theorem B702539 : Blo 467785 702539 := bstep (se 1 (by rfl) ⟨526904, by rfl⟩ : syracuseStep 702539 = 1053809) B1053809
theorem B1587275 : Blo 467785 1587275 := bstep (se 1 (by rfl) ⟨1190456, by rfl⟩ : syracuseStep 1587275 = 2380913) B2380913
theorem B702551 : Blo 467785 702551 := bstep (se 1 (by rfl) ⟨526913, by rfl⟩ : syracuseStep 702551 = 1053827) B1053827
theorem B702617 : Blo 467785 702617 := bstep (se 2 (by rfl) ⟨263481, by rfl⟩ : syracuseStep 702617 = 526963) B526963
theorem B2013443 : Blo 467785 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B702731 : Blo 467785 702731 := bstep (se 1 (by rfl) ⟨527048, by rfl⟩ : syracuseStep 702731 = 1054097) B1054097
theorem B702743 : Blo 467785 702743 := bstep (se 1 (by rfl) ⟨527057, by rfl⟩ : syracuseStep 702743 = 1054115) B1054115
theorem B702809 : Blo 467785 702809 := bstep (se 2 (by rfl) ⟨263553, by rfl⟩ : syracuseStep 702809 = 527107) B527107
theorem B1587545 : Blo 467785 1587545 := bstep (se 2 (by rfl) ⟨595329, by rfl⟩ : syracuseStep 1587545 = 1190659) B1190659
theorem B702923 : Blo 467785 702923 := bstep (se 1 (by rfl) ⟨527192, by rfl⟩ : syracuseStep 702923 = 1054385) B1054385
theorem B702935 : Blo 467785 702935 := bstep (se 1 (by rfl) ⟨527201, by rfl⟩ : syracuseStep 702935 = 1054403) B1054403
theorem B4504025 : Blo 467785 4504025 := bstep (se 2 (by rfl) ⟨1689009, by rfl⟩ : syracuseStep 4504025 = 3378019) B3378019
theorem B703001 : Blo 467785 703001 := bstep (se 2 (by rfl) ⟨263625, by rfl⟩ : syracuseStep 703001 = 527251) B527251
theorem B3389987 : Blo 467785 3389987 := bstep (se 1 (by rfl) ⟨2542490, by rfl⟩ : syracuseStep 3389987 = 5084981) B5084981
theorem B703115 : Blo 467785 703115 := bstep (se 1 (by rfl) ⟨527336, by rfl⟩ : syracuseStep 703115 = 1054673) B1054673
theorem B703127 : Blo 467785 703127 := bstep (se 1 (by rfl) ⟨527345, by rfl⟩ : syracuseStep 703127 = 1054691) B1054691
theorem B670361 : Blo 467785 670361 := bstep (se 2 (by rfl) ⟨251385, by rfl⟩ : syracuseStep 670361 = 502771) B502771
theorem B703193 : Blo 467785 703193 := bstep (se 2 (by rfl) ⟨263697, by rfl⟩ : syracuseStep 703193 = 527395) B527395
theorem B670475 : Blo 467785 670475 := bstep (se 1 (by rfl) ⟨502856, by rfl⟩ : syracuseStep 670475 = 1005713) B1005713
theorem B1260353 : Blo 467785 1260353 := bstep (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) B945265
theorem B703307 : Blo 467785 703307 := bstep (se 1 (by rfl) ⟨527480, by rfl⟩ : syracuseStep 703307 = 1054961) B1054961
theorem B703319 : Blo 467785 703319 := bstep (se 1 (by rfl) ⟨527489, by rfl⟩ : syracuseStep 703319 = 1054979) B1054979
theorem B703385 : Blo 467785 703385 := bstep (se 2 (by rfl) ⟨263769, by rfl⟩ : syracuseStep 703385 = 527539) B527539
theorem B703499 : Blo 467785 703499 := bstep (se 1 (by rfl) ⟨527624, by rfl⟩ : syracuseStep 703499 = 1055249) B1055249
theorem B703511 : Blo 467785 703511 := bstep (se 1 (by rfl) ⟨527633, by rfl⟩ : syracuseStep 703511 = 1055267) B1055267
theorem B1588247 : Blo 467785 1588247 := bstep (se 1 (by rfl) ⟨1191185, by rfl⟩ : syracuseStep 1588247 = 2382371) B2382371
theorem B703577 : Blo 467785 703577 := bstep (se 2 (by rfl) ⟨263841, by rfl⟩ : syracuseStep 703577 = 527683) B527683
theorem B5717143 : Blo 467785 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B703691 : Blo 467785 703691 := bstep (se 1 (by rfl) ⟨527768, by rfl⟩ : syracuseStep 703691 = 1055537) B1055537
theorem B703703 : Blo 467785 703703 := bstep (se 1 (by rfl) ⟨527777, by rfl⟩ : syracuseStep 703703 = 1055555) B1055555
theorem B670999 : Blo 467785 670999 := bstep (se 1 (by rfl) ⟨503249, by rfl⟩ : syracuseStep 670999 = 1006499) B1006499
theorem B703769 : Blo 467785 703769 := bstep (se 2 (by rfl) ⟨263913, by rfl⟩ : syracuseStep 703769 = 527827) B527827
theorem B4013387 : Blo 467785 4013387 := bstep (se 1 (by rfl) ⟨3010040, by rfl⟩ : syracuseStep 4013387 = 6020081) B6020081
theorem B703883 : Blo 467785 703883 := bstep (se 1 (by rfl) ⟨527912, by rfl⟩ : syracuseStep 703883 = 1055825) B1055825
theorem B703895 : Blo 467785 703895 := bstep (se 1 (by rfl) ⟨527921, by rfl⟩ : syracuseStep 703895 = 1055843) B1055843
theorem B3816881 : Blo 467785 3816881 := bstep (se 2 (by rfl) ⟨1431330, by rfl⟩ : syracuseStep 3816881 = 2862661) B2862661
theorem B703961 : Blo 467785 703961 := bstep (se 2 (by rfl) ⟨263985, by rfl⟩ : syracuseStep 703961 = 527971) B527971
theorem B1588787 : Blo 467785 1588787 := bstep (se 1 (by rfl) ⟨1191590, by rfl⟩ : syracuseStep 1588787 = 2383181) B2383181
theorem B2375243 : Blo 467785 2375243 := bstep (se 1 (by rfl) ⟨1781432, by rfl⟩ : syracuseStep 2375243 = 3562865) B3562865
theorem B704075 : Blo 467785 704075 := bstep (se 1 (by rfl) ⟨528056, by rfl⟩ : syracuseStep 704075 = 1056113) B1056113
theorem B704087 : Blo 467785 704087 := bstep (se 1 (by rfl) ⟨528065, by rfl⟩ : syracuseStep 704087 = 1056131) B1056131
theorem B704153 : Blo 467785 704153 := bstep (se 2 (by rfl) ⟨264057, by rfl⟩ : syracuseStep 704153 = 528115) B528115
theorem B704267 : Blo 467785 704267 := bstep (se 1 (by rfl) ⟨528200, by rfl⟩ : syracuseStep 704267 = 1056401) B1056401
theorem B3555089 : Blo 467785 3555089 := bstep (se 2 (by rfl) ⟨1333158, by rfl⟩ : syracuseStep 3555089 = 2666317) B2666317
theorem B704279 : Blo 467785 704279 := bstep (se 1 (by rfl) ⟨528209, by rfl⟩ : syracuseStep 704279 = 1056419) B1056419
theorem B1589057 : Blo 467785 1589057 := bstep (se 2 (by rfl) ⟨595896, by rfl⟩ : syracuseStep 1589057 = 1191793) B1191793
theorem B704345 : Blo 467785 704345 := bstep (se 2 (by rfl) ⟨264129, by rfl⟩ : syracuseStep 704345 = 528259) B528259
theorem B475031 : Blo 467785 475031 := bstep (se 1 (by rfl) ⟨356273, by rfl⟩ : syracuseStep 475031 = 712547) B712547
theorem B1687499 : Blo 467785 1687499 := bstep (se 1 (by rfl) ⟨1265624, by rfl⟩ : syracuseStep 1687499 = 2531249) B2531249
theorem B704459 : Blo 467785 704459 := bstep (se 1 (by rfl) ⟨528344, by rfl⟩ : syracuseStep 704459 = 1056689) B1056689
theorem B704471 : Blo 467785 704471 := bstep (se 1 (by rfl) ⟨528353, by rfl⟩ : syracuseStep 704471 = 1056707) B1056707
theorem B2146265 : Blo 467785 2146265 := bstep (se 2 (by rfl) ⟨804849, by rfl⟩ : syracuseStep 2146265 = 1609699) B1609699
theorem B999425 : Blo 467785 999425 := bstep (se 2 (by rfl) ⟨374784, by rfl⟩ : syracuseStep 999425 = 749569) B749569
theorem B704537 : Blo 467785 704537 := bstep (se 2 (by rfl) ⟨264201, by rfl⟩ : syracuseStep 704537 = 528403) B528403
theorem B704651 : Blo 467785 704651 := bstep (se 1 (by rfl) ⟨528488, by rfl⟩ : syracuseStep 704651 = 1056977) B1056977
theorem B704663 : Blo 467785 704663 := bstep (se 1 (by rfl) ⟨528497, by rfl⟩ : syracuseStep 704663 = 1056995) B1056995
theorem B704729 : Blo 467785 704729 := bstep (se 2 (by rfl) ⟨264273, by rfl⟩ : syracuseStep 704729 = 528547) B528547
theorem B1786157 : Blo 467785 1786157 := bstep (se 3 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 1786157 = 669809) B669809
theorem B704843 : Blo 467785 704843 := bstep (se 1 (by rfl) ⟨528632, by rfl⟩ : syracuseStep 704843 = 1057265) B1057265
theorem B704855 : Blo 467785 704855 := bstep (se 1 (by rfl) ⟨528641, by rfl⟩ : syracuseStep 704855 = 1057283) B1057283
theorem B1589597 : Blo 467785 1589597 := bstep (se 3 (by rfl) ⟨298049, by rfl⟩ : syracuseStep 1589597 = 596099) B596099
theorem B704921 : Blo 467785 704921 := bstep (se 2 (by rfl) ⟨264345, by rfl⟩ : syracuseStep 704921 = 528691) B528691
theorem B475627 : Blo 467785 475627 := bstep (se 1 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 475627 = 713441) B713441
theorem B705035 : Blo 467785 705035 := bstep (se 1 (by rfl) ⟨528776, by rfl⟩ : syracuseStep 705035 = 1057553) B1057553
theorem B1688087 : Blo 467785 1688087 := bstep (se 1 (by rfl) ⟨1266065, by rfl⟩ : syracuseStep 1688087 = 2532131) B2532131
theorem B705047 : Blo 467785 705047 := bstep (se 1 (by rfl) ⟨528785, by rfl⟩ : syracuseStep 705047 = 1057571) B1057571
theorem B705113 : Blo 467785 705113 := bstep (se 2 (by rfl) ⟨264417, by rfl⟩ : syracuseStep 705113 = 528835) B528835
theorem B705227 : Blo 467785 705227 := bstep (se 1 (by rfl) ⟨528920, by rfl⟩ : syracuseStep 705227 = 1057841) B1057841
theorem B705239 : Blo 467785 705239 := bstep (se 1 (by rfl) ⟨528929, by rfl⟩ : syracuseStep 705239 = 1057859) B1057859
theorem B705305 : Blo 467785 705305 := bstep (se 2 (by rfl) ⟨264489, by rfl⟩ : syracuseStep 705305 = 528979) B528979
theorem B1000279 : Blo 467785 1000279 := bstep (se 1 (by rfl) ⟨750209, by rfl⟩ : syracuseStep 1000279 = 1500419) B1500419
theorem B705419 : Blo 467785 705419 := bstep (se 1 (by rfl) ⟨529064, by rfl⟩ : syracuseStep 705419 = 1058129) B1058129
theorem B705431 : Blo 467785 705431 := bstep (se 1 (by rfl) ⟨529073, by rfl⟩ : syracuseStep 705431 = 1058147) B1058147
theorem B1426369 : Blo 467785 1426369 := bstep (se 2 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 1426369 = 1069777) B1069777
theorem B705497 : Blo 467785 705497 := bstep (se 2 (by rfl) ⟨264561, by rfl⟩ : syracuseStep 705497 = 529123) B529123
theorem B1786931 : Blo 467785 1786931 := bstep (se 1 (by rfl) ⟨1340198, by rfl⟩ : syracuseStep 1786931 = 2680397) B2680397
theorem B705611 : Blo 467785 705611 := bstep (se 1 (by rfl) ⟨529208, by rfl⟩ : syracuseStep 705611 = 1058417) B1058417
theorem B705623 : Blo 467785 705623 := bstep (se 1 (by rfl) ⟨529217, by rfl⟩ : syracuseStep 705623 = 1058435) B1058435
theorem B476299 : Blo 467785 476299 := bstep (se 1 (by rfl) ⟨357224, by rfl⟩ : syracuseStep 476299 = 714449) B714449
theorem B705689 : Blo 467785 705689 := bstep (se 2 (by rfl) ⟨264633, by rfl⟩ : syracuseStep 705689 = 529267) B529267
theorem B705803 : Blo 467785 705803 := bstep (se 1 (by rfl) ⟨529352, by rfl⟩ : syracuseStep 705803 = 1058705) B1058705
theorem B705815 : Blo 467785 705815 := bstep (se 1 (by rfl) ⟨529361, by rfl⟩ : syracuseStep 705815 = 1058723) B1058723
theorem B2377025 : Blo 467785 2377025 := bstep (se 2 (by rfl) ⟨891384, by rfl⟩ : syracuseStep 2377025 = 1782769) B1782769
theorem B1131841 : Blo 467785 1131841 := bstep (se 2 (by rfl) ⟨424440, by rfl⟩ : syracuseStep 1131841 = 848881) B848881
theorem B705881 : Blo 467785 705881 := bstep (se 2 (by rfl) ⟨264705, by rfl⟩ : syracuseStep 705881 = 529411) B529411
theorem B705995 : Blo 467785 705995 := bstep (se 1 (by rfl) ⟨529496, by rfl⟩ : syracuseStep 705995 = 1058993) B1058993
theorem B1590731 : Blo 467785 1590731 := bstep (se 1 (by rfl) ⟨1193048, by rfl⟩ : syracuseStep 1590731 = 2386097) B2386097
theorem B706007 : Blo 467785 706007 := bstep (se 1 (by rfl) ⟨529505, by rfl⟩ : syracuseStep 706007 = 1059011) B1059011
theorem B706073 : Blo 467785 706073 := bstep (se 2 (by rfl) ⟨264777, by rfl⟩ : syracuseStep 706073 = 529555) B529555
theorem B2573869 : Blo 467785 2573869 := bstep (se 3 (by rfl) ⟨482600, by rfl⟩ : syracuseStep 2573869 = 965201) B965201
theorem B706187 : Blo 467785 706187 := bstep (se 1 (by rfl) ⟨529640, by rfl⟩ : syracuseStep 706187 = 1059281) B1059281
theorem B706199 : Blo 467785 706199 := bstep (se 1 (by rfl) ⟨529649, by rfl⟩ : syracuseStep 706199 = 1059299) B1059299
theorem B1132235 : Blo 467785 1132235 := bstep (se 1 (by rfl) ⟨849176, by rfl⟩ : syracuseStep 1132235 = 1698353) B1698353
theorem B706265 : Blo 467785 706265 := bstep (se 2 (by rfl) ⟨264849, by rfl⟩ : syracuseStep 706265 = 529699) B529699
theorem B1591001 : Blo 467785 1591001 := bstep (se 2 (by rfl) ⟨596625, by rfl⟩ : syracuseStep 1591001 = 1193251) B1193251
theorem B902963 : Blo 467785 902963 := bstep (se 1 (by rfl) ⟨677222, by rfl⟩ : syracuseStep 902963 = 1354445) B1354445
theorem B706379 : Blo 467785 706379 := bstep (se 1 (by rfl) ⟨529784, by rfl⟩ : syracuseStep 706379 = 1059569) B1059569
theorem B706391 : Blo 467785 706391 := bstep (se 1 (by rfl) ⟨529793, by rfl⟩ : syracuseStep 706391 = 1059587) B1059587
theorem B706457 : Blo 467785 706457 := bstep (se 2 (by rfl) ⟨264921, by rfl⟩ : syracuseStep 706457 = 529843) B529843
theorem B1132505 : Blo 467785 1132505 := bstep (se 2 (by rfl) ⟨424689, by rfl⟩ : syracuseStep 1132505 = 849379) B849379
theorem B1001459 : Blo 467785 1001459 := bstep (se 1 (by rfl) ⟨751094, by rfl⟩ : syracuseStep 1001459 = 1502189) B1502189
theorem B706571 : Blo 467785 706571 := bstep (se 1 (by rfl) ⟨529928, by rfl⟩ : syracuseStep 706571 = 1059857) B1059857
theorem B706583 : Blo 467785 706583 := bstep (se 1 (by rfl) ⟨529937, by rfl⟩ : syracuseStep 706583 = 1059875) B1059875
theorem B706649 : Blo 467785 706649 := bstep (se 2 (by rfl) ⟨264993, by rfl⟩ : syracuseStep 706649 = 529987) B529987
theorem B1853585 : Blo 467785 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B706763 : Blo 467785 706763 := bstep (se 1 (by rfl) ⟨530072, by rfl⟩ : syracuseStep 706763 = 1060145) B1060145
theorem B706775 : Blo 467785 706775 := bstep (se 1 (by rfl) ⟨530081, by rfl⟩ : syracuseStep 706775 = 1060163) B1060163
theorem B1689817 : Blo 467785 1689817 := bstep (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) B1267363
theorem B706841 : Blo 467785 706841 := bstep (se 2 (by rfl) ⟨265065, by rfl⟩ : syracuseStep 706841 = 530131) B530131
theorem B706955 : Blo 467785 706955 := bstep (se 1 (by rfl) ⟨530216, by rfl⟩ : syracuseStep 706955 = 1060433) B1060433
theorem B706967 : Blo 467785 706967 := bstep (se 1 (by rfl) ⟨530225, by rfl⟩ : syracuseStep 706967 = 1060451) B1060451
theorem B1591703 : Blo 467785 1591703 := bstep (se 1 (by rfl) ⟨1193777, by rfl⟩ : syracuseStep 1591703 = 2387555) B2387555
theorem B707033 : Blo 467785 707033 := bstep (se 2 (by rfl) ⟨265137, by rfl⟩ : syracuseStep 707033 = 530275) B530275
theorem B1788419 : Blo 467785 1788419 := bstep (se 1 (by rfl) ⟨1341314, by rfl⟩ : syracuseStep 1788419 = 2682629) B2682629
theorem B707147 : Blo 467785 707147 := bstep (se 1 (by rfl) ⟨530360, by rfl⟩ : syracuseStep 707147 = 1060721) B1060721
theorem B707159 : Blo 467785 707159 := bstep (se 1 (by rfl) ⟨530369, by rfl⟩ : syracuseStep 707159 = 1060739) B1060739
theorem B2542211 : Blo 467785 2542211 := bstep (se 1 (by rfl) ⟨1906658, by rfl⟩ : syracuseStep 2542211 = 3813317) B3813317
theorem B1428119 : Blo 467785 1428119 := bstep (se 1 (by rfl) ⟨1071089, by rfl⟩ : syracuseStep 1428119 = 2142179) B2142179
theorem B707225 : Blo 467785 707225 := bstep (se 2 (by rfl) ⟨265209, by rfl⟩ : syracuseStep 707225 = 530419) B530419
theorem B1133273 : Blo 467785 1133273 := bstep (se 2 (by rfl) ⟨424977, by rfl⟩ : syracuseStep 1133273 = 849955) B849955
theorem B707339 : Blo 467785 707339 := bstep (se 1 (by rfl) ⟨530504, by rfl⟩ : syracuseStep 707339 = 1061009) B1061009
theorem B2673425 : Blo 467785 2673425 := bstep (se 2 (by rfl) ⟨1002534, by rfl⟩ : syracuseStep 2673425 = 2005069) B2005069
theorem B707351 : Blo 467785 707351 := bstep (se 1 (by rfl) ⟨530513, by rfl⟩ : syracuseStep 707351 = 1061027) B1061027
theorem B707417 : Blo 467785 707417 := bstep (se 2 (by rfl) ⟨265281, by rfl⟩ : syracuseStep 707417 = 530563) B530563
theorem B1690541 : Blo 467785 1690541 := bstep (se 3 (by rfl) ⟨316976, by rfl⟩ : syracuseStep 1690541 = 633953) B633953
theorem B1592243 : Blo 467785 1592243 := bstep (se 1 (by rfl) ⟨1194182, by rfl⟩ : syracuseStep 1592243 = 2388365) B2388365
theorem B1788875 : Blo 467785 1788875 := bstep (se 1 (by rfl) ⟨1341656, by rfl⟩ : syracuseStep 1788875 = 2683313) B2683313
theorem B707531 : Blo 467785 707531 := bstep (se 1 (by rfl) ⟨530648, by rfl⟩ : syracuseStep 707531 = 1061297) B1061297
theorem B707543 : Blo 467785 707543 := bstep (se 1 (by rfl) ⟨530657, by rfl⟩ : syracuseStep 707543 = 1061315) B1061315
theorem B707609 : Blo 467785 707609 := bstep (se 2 (by rfl) ⟨265353, by rfl⟩ : syracuseStep 707609 = 530707) B530707
theorem B1789073 : Blo 467785 1789073 := bstep (se 2 (by rfl) ⟨670902, by rfl⟩ : syracuseStep 1789073 = 1341805) B1341805
theorem B1002689 : Blo 467785 1002689 := bstep (se 2 (by rfl) ⟨376008, by rfl⟩ : syracuseStep 1002689 = 752017) B752017
theorem B2673881 : Blo 467785 2673881 := bstep (se 2 (by rfl) ⟨1002705, by rfl⟩ : syracuseStep 2673881 = 2005411) B2005411
theorem B2378969 : Blo 467785 2378969 := bstep (se 2 (by rfl) ⟨892113, by rfl⟩ : syracuseStep 2378969 = 1784227) B1784227
theorem B3558977 : Blo 467785 3558977 := bstep (se 2 (by rfl) ⟨1334616, by rfl⟩ : syracuseStep 3558977 = 2669233) B2669233
theorem B1691201 : Blo 467785 1691201 := bstep (se 2 (by rfl) ⟨634200, by rfl⟩ : syracuseStep 1691201 = 1268401) B1268401
theorem B1789847 : Blo 467785 1789847 := bstep (se 1 (by rfl) ⟨1342385, by rfl⟩ : syracuseStep 1789847 = 2684771) B2684771
theorem B5328989 : Blo 467785 5328989 := bstep (se 3 (by rfl) ⟨999185, by rfl⟩ : syracuseStep 5328989 = 1998371) B1998371
theorem B1790045 : Blo 467785 1790045 := bstep (se 3 (by rfl) ⟨335633, by rfl⟩ : syracuseStep 1790045 = 671267) B671267
theorem B4837637 : Blo 467785 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B1003799 : Blo 467785 1003799 := bstep (se 1 (by rfl) ⟨752849, by rfl⟩ : syracuseStep 1003799 = 1505699) B1505699
theorem B2380589 : Blo 467785 2380589 := bstep (se 3 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 2380589 = 892721) B892721
theorem B4510565 : Blo 467785 4510565 := bstep (se 4 (by rfl) ⟨422865, by rfl⟩ : syracuseStep 4510565 = 845731) B845731
theorem B1692875 : Blo 467785 1692875 := bstep (se 1 (by rfl) ⟨1269656, by rfl⟩ : syracuseStep 1692875 = 2539313) B2539313
theorem B1004825 : Blo 467785 1004825 := bstep (se 2 (by rfl) ⟨376809, by rfl⟩ : syracuseStep 1004825 = 753619) B753619
theorem B3429697 : Blo 467785 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B3560921 : Blo 467785 3560921 := bstep (se 2 (by rfl) ⟨1335345, by rfl⟩ : syracuseStep 3560921 = 2670691) B2670691
theorem B3823109 : Blo 467785 3823109 := bstep (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) B716833
theorem B3626627 : Blo 467785 3626627 := bstep (se 1 (by rfl) ⟨2719970, by rfl⟩ : syracuseStep 3626627 = 5439941) B5439941
theorem B1333057 : Blo 467785 1333057 := bstep (se 2 (by rfl) ⟨499896, by rfl⟩ : syracuseStep 1333057 = 999793) B999793
theorem B10180417 : Blo 467785 10180417 := bstep (se 2 (by rfl) ⟨3817656, by rfl⟩ : syracuseStep 10180417 = 7635313) B7635313
theorem B3200843 : Blo 467785 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B21649477 : Blo 467785 21649477 := bstep (se 4 (by rfl) ⟨2029638, by rfl⟩ : syracuseStep 21649477 = 4059277) B4059277
theorem B1267991 : Blo 467785 1267991 := bstep (se 1 (by rfl) ⟨950993, by rfl⟩ : syracuseStep 1267991 = 1901987) B1901987
theorem B1071767 : Blo 467785 1071767 := bstep (se 1 (by rfl) ⟨803825, by rfl⟩ : syracuseStep 1071767 = 1607651) B1607651
theorem B3824279 : Blo 467785 3824279 := bstep (se 1 (by rfl) ⟨2868209, by rfl⟩ : syracuseStep 3824279 = 5736419) B5736419
theorem B1006465 : Blo 467785 1006465 := bstep (se 2 (by rfl) ⟨377424, by rfl⟩ : syracuseStep 1006465 = 754849) B754849
theorem B711641 : Blo 467785 711641 := bstep (se 2 (by rfl) ⟨266865, by rfl⟩ : syracuseStep 711641 = 533731) B533731
theorem B1072331 : Blo 467785 1072331 := bstep (se 1 (by rfl) ⟨804248, by rfl⟩ : syracuseStep 1072331 = 1608497) B1608497
theorem B3005657 : Blo 467785 3005657 := bstep (se 2 (by rfl) ⟨1127121, by rfl⟩ : syracuseStep 3005657 = 2254243) B2254243
theorem B1924355 : Blo 467785 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B7232813 : Blo 467785 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B1334731 : Blo 467785 1334731 := bstep (se 1 (by rfl) ⟨1001048, by rfl⟩ : syracuseStep 1334731 = 2002097) B2002097
theorem B1007063 : Blo 467785 1007063 := bstep (se 1 (by rfl) ⟨755297, by rfl⟩ : syracuseStep 1007063 = 1510595) B1510595
theorem B3006017 : Blo 467785 3006017 := bstep (se 2 (by rfl) ⟨1127256, by rfl⟩ : syracuseStep 3006017 = 2254513) B2254513
theorem B1335005 : Blo 467785 1335005 := bstep (se 3 (by rfl) ⟨250313, by rfl⟩ : syracuseStep 1335005 = 500627) B500627
theorem B3825443 : Blo 467785 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B843713 : Blo 467785 843713 := bstep (se 2 (by rfl) ⟨316392, by rfl⟩ : syracuseStep 843713 = 632785) B632785
theorem B2547787 : Blo 467785 2547787 := bstep (se 1 (by rfl) ⟨1910840, by rfl⟩ : syracuseStep 2547787 = 3821681) B3821681
theorem B3006557 : Blo 467785 3006557 := bstep (se 3 (by rfl) ⟨563729, by rfl⟩ : syracuseStep 3006557 = 1127459) B1127459
theorem B1695917 : Blo 467785 1695917 := bstep (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) B635969
theorem B1499485 : Blo 467785 1499485 := bstep (se 3 (by rfl) ⟨281153, by rfl⟩ : syracuseStep 1499485 = 562307) B562307
theorem B2679257 : Blo 467785 2679257 := bstep (se 2 (by rfl) ⟨1004721, by rfl⟩ : syracuseStep 2679257 = 2009443) B2009443
theorem B2482781 : Blo 467785 2482781 := bstep (se 3 (by rfl) ⟨465521, by rfl⟩ : syracuseStep 2482781 = 931043) B931043
theorem B2384477 : Blo 467785 2384477 := bstep (se 3 (by rfl) ⟨447089, by rfl⟩ : syracuseStep 2384477 = 894179) B894179
theorem B3564323 : Blo 467785 3564323 := bstep (se 1 (by rfl) ⟨2673242, by rfl⟩ : syracuseStep 3564323 = 5346485) B5346485
theorem B1434433 : Blo 467785 1434433 := bstep (se 2 (by rfl) ⟨537912, by rfl⟩ : syracuseStep 1434433 = 1075825) B1075825
theorem B1205081 : Blo 467785 1205081 := bstep (se 2 (by rfl) ⟨451905, by rfl⟩ : syracuseStep 1205081 = 903811) B903811
theorem B484747 : Blo 467785 484747 := bstep (se 1 (by rfl) ⟨363560, by rfl⟩ : syracuseStep 484747 = 727121) B727121
theorem B2549171 : Blo 467785 2549171 := bstep (se 1 (by rfl) ⟨1911878, by rfl⟩ : syracuseStep 2549171 = 3823757) B3823757
theorem B1697345 : Blo 467785 1697345 := bstep (se 2 (by rfl) ⟨636504, by rfl⟩ : syracuseStep 1697345 = 1273009) B1273009
theorem B845515 : Blo 467785 845515 := bstep (se 1 (by rfl) ⟨634136, by rfl⟩ : syracuseStep 845515 = 1268273) B1268273
theorem B13526837 : Blo 467785 13526837 := bstep (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) B1268141
theorem B21718961 : Blo 467785 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B1337305 : Blo 467785 1337305 := bstep (se 2 (by rfl) ⟨501489, by rfl⟩ : syracuseStep 1337305 = 1002979) B1002979
theorem B2680897 : Blo 467785 2680897 := bstep (se 2 (by rfl) ⟨1005336, by rfl⟩ : syracuseStep 2680897 = 2010673) B2010673
theorem B2058329 : Blo 467785 2058329 := bstep (se 2 (by rfl) ⟨771873, by rfl⟩ : syracuseStep 2058329 = 1543747) B1543747
theorem B845977 : Blo 467785 845977 := bstep (se 2 (by rfl) ⟨317241, by rfl⟩ : syracuseStep 845977 = 634483) B634483
theorem B2713949 : Blo 467785 2713949 := bstep (se 3 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 2713949 = 1017731) B1017731
theorem B5368355 : Blo 467785 5368355 := bstep (se 1 (by rfl) ⟨4026266, by rfl⟩ : syracuseStep 5368355 = 8052533) B8052533
theorem B1337921 : Blo 467785 1337921 := bstep (se 2 (by rfl) ⟨501720, by rfl⟩ : syracuseStep 1337921 = 1003441) B1003441
theorem B2255435 : Blo 467785 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B2386583 : Blo 467785 2386583 := bstep (se 1 (by rfl) ⟨1789937, by rfl⟩ : syracuseStep 2386583 = 3579875) B3579875
theorem B912691 : Blo 467785 912691 := bstep (se 1 (by rfl) ⟨684518, by rfl⟩ : syracuseStep 912691 = 1369037) B1369037
theorem B847361 : Blo 467785 847361 := bstep (se 2 (by rfl) ⟨317760, by rfl⟩ : syracuseStep 847361 = 635521) B635521
theorem B716311 : Blo 467785 716311 := bstep (se 1 (by rfl) ⟨537233, by rfl⟩ : syracuseStep 716311 = 1074467) B1074467
theorem B1273495 : Blo 467785 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B847577 : Blo 467785 847577 := bstep (se 2 (by rfl) ⟨317841, by rfl⟩ : syracuseStep 847577 = 635683) B635683
theorem B8056907 : Blo 467785 8056907 := bstep (se 1 (by rfl) ⟨6042680, by rfl⟩ : syracuseStep 8056907 = 12085361) B12085361
theorem B2289995 : Blo 467785 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B6844945 : Blo 467785 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B3011089 : Blo 467785 3011089 := bstep (se 2 (by rfl) ⟨1129158, by rfl⟩ : syracuseStep 3011089 = 2258317) B2258317
theorem B1339993 : Blo 467785 1339993 := bstep (se 2 (by rfl) ⟨502497, by rfl⟩ : syracuseStep 1339993 = 1004995) B1004995
theorem B11465347 : Blo 467785 11465347 := bstep (se 1 (by rfl) ⟨8599010, by rfl⟩ : syracuseStep 11465347 = 17198021) B17198021
theorem B1274717 : Blo 467785 1274717 := bstep (se 3 (by rfl) ⟨239009, by rfl⟩ : syracuseStep 1274717 = 478019) B478019
theorem B1340381 : Blo 467785 1340381 := bstep (se 3 (by rfl) ⟨251321, by rfl⟩ : syracuseStep 1340381 = 502643) B502643
theorem B15398257 : Blo 467785 15398257 := bstep (se 2 (by rfl) ⟨5774346, by rfl⟩ : syracuseStep 15398257 = 11548693) B11548693
theorem B2684339 : Blo 467785 2684339 := bstep (se 1 (by rfl) ⟨2013254, by rfl⟩ : syracuseStep 2684339 = 4026509) B4026509
theorem B1897931 : Blo 467785 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B1504919 : Blo 467785 1504919 := bstep (se 1 (by rfl) ⟨1128689, by rfl⟩ : syracuseStep 1504919 = 2257379) B2257379
theorem B11564977 : Blo 467785 11564977 := bstep (se 2 (by rfl) ⟨4336866, by rfl⟩ : syracuseStep 11564977 = 8673733) B8673733
theorem B1144793 : Blo 467785 1144793 := bstep (se 2 (by rfl) ⟨429297, by rfl⟩ : syracuseStep 1144793 = 858595) B858595
theorem B3569669 : Blo 467785 3569669 := bstep (se 4 (by rfl) ⟨334656, by rfl⟩ : syracuseStep 3569669 = 669313) B669313
theorem B5700017 : Blo 467785 5700017 := bstep (se 2 (by rfl) ⟨2137506, by rfl⟩ : syracuseStep 5700017 = 4275013) B4275013
theorem B1604119 : Blo 467785 1604119 := bstep (se 1 (by rfl) ⟨1203089, by rfl⟩ : syracuseStep 1604119 = 2406179) B2406179
theorem B752203 : Blo 467785 752203 := bstep (se 1 (by rfl) ⟨564152, by rfl⟩ : syracuseStep 752203 = 1128305) B1128305
theorem B2685797 : Blo 467785 2685797 := bstep (se 4 (by rfl) ⟨251793, by rfl⟩ : syracuseStep 2685797 = 503587) B503587
theorem B1899395 : Blo 467785 1899395 := bstep (se 1 (by rfl) ⟨1424546, by rfl⟩ : syracuseStep 1899395 = 2849093) B2849093
theorem B1506251 : Blo 467785 1506251 := bstep (se 1 (by rfl) ⟨1129688, by rfl⟩ : syracuseStep 1506251 = 2259377) B2259377
theorem B2849867 : Blo 467785 2849867 := bstep (se 1 (by rfl) ⟨2137400, by rfl⟩ : syracuseStep 2849867 = 4274801) B4274801
theorem B4062359 : Blo 467785 4062359 := bstep (se 1 (by rfl) ⟨3046769, by rfl⟩ : syracuseStep 4062359 = 6093539) B6093539
theorem B7241309 : Blo 467785 7241309 := bstep (se 3 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 7241309 = 2715491) B2715491
theorem B1343297 : Blo 467785 1343297 := bstep (se 2 (by rfl) ⟨503736, by rfl⟩ : syracuseStep 1343297 = 1007473) B1007473
theorem B1343411 : Blo 467785 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B950231 : Blo 467785 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B1507339 : Blo 467785 1507339 := bstep (se 1 (by rfl) ⟨1130504, by rfl⟩ : syracuseStep 1507339 = 2261009) B2261009
theorem B1999313 : Blo 467785 1999313 := bstep (se 2 (by rfl) ⟨749742, by rfl⟩ : syracuseStep 1999313 = 1499485) B1499485
theorem B754823 : Blo 467785 754823 := bstep (se 1 (by rfl) ⟨566117, by rfl⟩ : syracuseStep 754823 = 1132235) B1132235
theorem B5080265 : Blo 467785 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B1901825 : Blo 467785 1901825 := bstep (se 2 (by rfl) ⟨713184, by rfl⟩ : syracuseStep 1901825 = 1426369) B1426369
theorem B755003 : Blo 467785 755003 := bstep (se 1 (by rfl) ⟨566252, by rfl⟩ : syracuseStep 755003 = 1132505) B1132505
theorem B1508723 : Blo 467785 1508723 := bstep (se 1 (by rfl) ⟨1131542, by rfl⟩ : syracuseStep 1508723 = 2263085) B2263085
theorem B2885149 : Blo 467785 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B3606059 : Blo 467785 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B7603789 : Blo 467785 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B1509121 : Blo 467785 1509121 := bstep (se 2 (by rfl) ⟨565920, by rfl⟩ : syracuseStep 1509121 = 1131841) B1131841
theorem B952079 : Blo 467785 952079 := bstep (se 1 (by rfl) ⟨714059, by rfl⟩ : syracuseStep 952079 = 1428119) B1428119
theorem B755515 : Blo 467785 755515 := bstep (se 1 (by rfl) ⟨566636, by rfl⟩ : syracuseStep 755515 = 1133273) B1133273
theorem B526351 : Blo 467785 526351 := bstep (se 1 (by rfl) ⟨394763, by rfl⟩ : syracuseStep 526351 = 789527) B789527
theorem B526855 : Blo 467785 526855 := bstep (se 1 (by rfl) ⟨395141, by rfl⟩ : syracuseStep 526855 = 790283) B790283
theorem B527035 : Blo 467785 527035 := bstep (se 1 (by rfl) ⟨395276, by rfl⟩ : syracuseStep 527035 = 790553) B790553
theorem B3574529 : Blo 467785 3574529 := bstep (se 2 (by rfl) ⟨1340448, by rfl⟩ : syracuseStep 3574529 = 2680897) B2680897
theorem B9046799 : Blo 467785 9046799 := bstep (se 1 (by rfl) ⟨6785099, by rfl⟩ : syracuseStep 9046799 = 13570199) B13570199
theorem B789547 : Blo 467785 789547 := bstep (se 1 (by rfl) ⟨592160, by rfl⟩ : syracuseStep 789547 = 1184321) B1184321
theorem B527503 : Blo 467785 527503 := bstep (se 1 (by rfl) ⟨395627, by rfl⟩ : syracuseStep 527503 = 791255) B791255
theorem B789689 : Blo 467785 789689 := bstep (se 2 (by rfl) ⟨296133, by rfl⟩ : syracuseStep 789689 = 592267) B592267
theorem B888097 : Blo 467785 888097 := bstep (se 2 (by rfl) ⟨333036, by rfl⟩ : syracuseStep 888097 = 666073) B666073
theorem B528007 : Blo 467785 528007 := bstep (se 1 (by rfl) ⟨396005, by rfl⟩ : syracuseStep 528007 = 792011) B792011
theorem B1511183 : Blo 467785 1511183 := bstep (se 1 (by rfl) ⟨1133387, by rfl⟩ : syracuseStep 1511183 = 2266775) B2266775
theorem B6033203 : Blo 467785 6033203 := bstep (se 1 (by rfl) ⟨4524902, by rfl⟩ : syracuseStep 6033203 = 9049805) B9049805
theorem B528187 : Blo 467785 528187 := bstep (se 1 (by rfl) ⟨396140, by rfl⟩ : syracuseStep 528187 = 792281) B792281
theorem B790391 : Blo 467785 790391 := bstep (se 1 (by rfl) ⟨592793, by rfl⟩ : syracuseStep 790391 = 1185587) B1185587
theorem B5083033 : Blo 467785 5083033 := bstep (se 2 (by rfl) ⟨1906137, by rfl⟩ : syracuseStep 5083033 = 3812275) B3812275
theorem B5705815 : Blo 467785 5705815 := bstep (se 1 (by rfl) ⟨4279361, by rfl⟩ : syracuseStep 5705815 = 8558723) B8558723
theorem B1052819 : Blo 467785 1052819 := bstep (se 1 (by rfl) ⟨789614, by rfl⟩ : syracuseStep 1052819 = 1579229) B1579229
theorem B1052873 : Blo 467785 1052873 := bstep (se 2 (by rfl) ⟨394827, by rfl⟩ : syracuseStep 1052873 = 789655) B789655
theorem B528655 : Blo 467785 528655 := bstep (se 1 (by rfl) ⟨396491, by rfl⟩ : syracuseStep 528655 = 792983) B792983
theorem B790843 : Blo 467785 790843 := bstep (se 1 (by rfl) ⟨593132, by rfl⟩ : syracuseStep 790843 = 1186265) B1186265
theorem B9671005 : Blo 467785 9671005 := bstep (se 3 (by rfl) ⟨1813313, by rfl⟩ : syracuseStep 9671005 = 3626627) B3626627
theorem B1216921 : Blo 467785 1216921 := bstep (se 2 (by rfl) ⟨456345, by rfl⟩ : syracuseStep 1216921 = 912691) B912691
theorem B889289 : Blo 467785 889289 := bstep (se 2 (by rfl) ⟨333483, by rfl⟩ : syracuseStep 889289 = 666967) B666967
theorem B790985 : Blo 467785 790985 := bstep (se 2 (by rfl) ⟨296619, by rfl⟩ : syracuseStep 790985 = 593239) B593239
theorem B955081 : Blo 467785 955081 := bstep (se 2 (by rfl) ⟨358155, by rfl⟩ : syracuseStep 955081 = 716311) B716311
theorem B529159 : Blo 467785 529159 := bstep (se 1 (by rfl) ⟨396869, by rfl⟩ : syracuseStep 529159 = 793739) B793739
theorem B2003771 : Blo 467785 2003771 := bstep (se 1 (by rfl) ⟨1502828, by rfl⟩ : syracuseStep 2003771 = 3005657) B3005657
theorem B4821875 : Blo 467785 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B1053575 : Blo 467785 1053575 := bstep (se 1 (by rfl) ⟨790181, by rfl⟩ : syracuseStep 1053575 = 1580363) B1580363
theorem B1184665 : Blo 467785 1184665 := bstep (se 2 (by rfl) ⟨444249, by rfl⟩ : syracuseStep 1184665 = 888499) B888499
theorem B594859 : Blo 467785 594859 := bstep (se 1 (by rfl) ⟨446144, by rfl⟩ : syracuseStep 594859 = 892289) B892289
theorem B529339 : Blo 467785 529339 := bstep (se 1 (by rfl) ⟨397004, by rfl⟩ : syracuseStep 529339 = 794009) B794009
theorem B2004011 : Blo 467785 2004011 := bstep (se 1 (by rfl) ⟨1503008, by rfl⟩ : syracuseStep 2004011 = 3006017) B3006017
theorem B1184827 : Blo 467785 1184827 := bstep (se 1 (by rfl) ⟨888620, by rfl⟩ : syracuseStep 1184827 = 1777241) B1777241
theorem B1053755 : Blo 467785 1053755 := bstep (se 1 (by rfl) ⟨790316, by rfl⟩ : syracuseStep 1053755 = 1580633) B1580633
theorem B791687 : Blo 467785 791687 := bstep (se 1 (by rfl) ⟨593765, by rfl⟩ : syracuseStep 791687 = 1187531) B1187531
theorem B890003 : Blo 467785 890003 := bstep (se 1 (by rfl) ⟨667502, by rfl⟩ : syracuseStep 890003 = 1335005) B1335005
theorem B1053881 : Blo 467785 1053881 := bstep (se 2 (by rfl) ⟨395205, by rfl⟩ : syracuseStep 1053881 = 790411) B790411
theorem B890041 : Blo 467785 890041 := bstep (se 2 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 890041 = 667531) B667531
theorem B1184969 : Blo 467785 1184969 := bstep (se 2 (by rfl) ⟨444363, by rfl⟩ : syracuseStep 1184969 = 888727) B888727
theorem B562475 : Blo 467785 562475 := bstep (se 1 (by rfl) ⟨421856, by rfl⟩ : syracuseStep 562475 = 843713) B843713
theorem B529807 : Blo 467785 529807 := bstep (se 1 (by rfl) ⟨397355, by rfl⟩ : syracuseStep 529807 = 794711) B794711
theorem B2004371 : Blo 467785 2004371 := bstep (se 1 (by rfl) ⟨1503278, by rfl⟩ : syracuseStep 2004371 = 3006557) B3006557
theorem B1054223 : Blo 467785 1054223 := bstep (se 1 (by rfl) ⟨790667, by rfl⟩ : syracuseStep 1054223 = 1581335) B1581335
theorem B1185313 : Blo 467785 1185313 := bstep (se 2 (by rfl) ⟨444492, by rfl⟩ : syracuseStep 1185313 = 888985) B888985
theorem B1054241 : Blo 467785 1054241 := bstep (se 2 (by rfl) ⟨395340, by rfl⟩ : syracuseStep 1054241 = 790681) B790681
theorem B792335 : Blo 467785 792335 := bstep (se 1 (by rfl) ⟨594251, by rfl⟩ : syracuseStep 792335 = 1188503) B1188503
theorem B1054583 : Blo 467785 1054583 := bstep (se 1 (by rfl) ⟨790937, by rfl⟩ : syracuseStep 1054583 = 1581875) B1581875
theorem B595831 : Blo 467785 595831 := bstep (se 1 (by rfl) ⟨446873, by rfl⟩ : syracuseStep 595831 = 893747) B893747
theorem B530311 : Blo 467785 530311 := bstep (se 1 (by rfl) ⟨397733, by rfl⟩ : syracuseStep 530311 = 795467) B795467
theorem B1578905 : Blo 467785 1578905 := bstep (se 2 (by rfl) ⟨592089, by rfl⟩ : syracuseStep 1578905 = 1184179) B1184179
theorem B1054763 : Blo 467785 1054763 := bstep (se 1 (by rfl) ⟨791072, by rfl⟩ : syracuseStep 1054763 = 1582145) B1582145
theorem B530491 : Blo 467785 530491 := bstep (se 1 (by rfl) ⟨397868, by rfl⟩ : syracuseStep 530491 = 795737) B795737
theorem B1251389 : Blo 467785 1251389 := bstep (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) B469271
theorem B1185911 : Blo 467785 1185911 := bstep (se 1 (by rfl) ⟨889433, by rfl⟩ : syracuseStep 1185911 = 1778867) B1778867
theorem B596155 : Blo 467785 596155 := bstep (se 1 (by rfl) ⟨447116, by rfl⟩ : syracuseStep 596155 = 894233) B894233
theorem B792875 : Blo 467785 792875 := bstep (se 1 (by rfl) ⟨594656, by rfl⟩ : syracuseStep 792875 = 1189313) B1189313
theorem B26482997 : Blo 467785 26482997 := bstep (se 5 (by rfl) ⟨1241390, by rfl⟩ : syracuseStep 26482997 = 2482781) B2482781
theorem B1055123 : Blo 467785 1055123 := bstep (se 1 (by rfl) ⟨791342, by rfl⟩ : syracuseStep 1055123 = 1582685) B1582685
theorem B1055177 : Blo 467785 1055177 := bstep (se 2 (by rfl) ⟨395691, by rfl⟩ : syracuseStep 1055177 = 791383) B791383
theorem B9017891 : Blo 467785 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B1579607 : Blo 467785 1579607 := bstep (se 1 (by rfl) ⟨1184705, by rfl⟩ : syracuseStep 1579607 = 2369411) B2369411
theorem B793273 : Blo 467785 793273 := bstep (se 2 (by rfl) ⟨297477, by rfl⟩ : syracuseStep 793273 = 594955) B594955
theorem B1809299 : Blo 467785 1809299 := bstep (se 1 (by rfl) ⟨1356974, by rfl⟩ : syracuseStep 1809299 = 2713949) B2713949
theorem B3578903 : Blo 467785 3578903 := bstep (se 1 (by rfl) ⟨2684177, by rfl⟩ : syracuseStep 3578903 = 5368355) B5368355
theorem B891947 : Blo 467785 891947 := bstep (se 1 (by rfl) ⟨668960, by rfl⟩ : syracuseStep 891947 = 1337921) B1337921
theorem B1580093 : Blo 467785 1580093 := bstep (se 3 (by rfl) ⟨296267, by rfl⟩ : syracuseStep 1580093 = 592535) B592535
theorem B1055879 : Blo 467785 1055879 := bstep (se 1 (by rfl) ⟨791909, by rfl⟩ : syracuseStep 1055879 = 1583819) B1583819
theorem B1056059 : Blo 467785 1056059 := bstep (se 1 (by rfl) ⟨792044, by rfl⟩ : syracuseStep 1056059 = 1584089) B1584089
theorem B793975 : Blo 467785 793975 := bstep (se 1 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 793975 = 1190963) B1190963
theorem B1187207 : Blo 467785 1187207 := bstep (se 1 (by rfl) ⟨890405, by rfl⟩ : syracuseStep 1187207 = 1780811) B1780811
theorem B1187257 : Blo 467785 1187257 := bstep (se 2 (by rfl) ⟨445221, by rfl⟩ : syracuseStep 1187257 = 890443) B890443
theorem B1056185 : Blo 467785 1056185 := bstep (se 2 (by rfl) ⟨396069, by rfl⟩ : syracuseStep 1056185 = 792139) B792139
theorem B794171 : Blo 467785 794171 := bstep (se 1 (by rfl) ⟨595628, by rfl⟩ : syracuseStep 794171 = 1191257) B1191257
theorem B564907 : Blo 467785 564907 := bstep (se 1 (by rfl) ⟨423680, by rfl⟩ : syracuseStep 564907 = 847361) B847361
theorem B1777409 : Blo 467785 1777409 := bstep (se 2 (by rfl) ⟨666528, by rfl⟩ : syracuseStep 1777409 = 1333057) B1333057
theorem B13573889 : Blo 467785 13573889 := bstep (se 2 (by rfl) ⟨5090208, by rfl⟩ : syracuseStep 13573889 = 10180417) B10180417
theorem B1777423 : Blo 467785 1777423 := bstep (se 1 (by rfl) ⟨1333067, by rfl⟩ : syracuseStep 1777423 = 2666135) B2666135
theorem B1056527 : Blo 467785 1056527 := bstep (se 1 (by rfl) ⟨792395, by rfl⟩ : syracuseStep 1056527 = 1584791) B1584791
theorem B1056545 : Blo 467785 1056545 := bstep (se 2 (by rfl) ⟨396204, by rfl⟩ : syracuseStep 1056545 = 792409) B792409
theorem B565051 : Blo 467785 565051 := bstep (se 1 (by rfl) ⟨423788, by rfl⟩ : syracuseStep 565051 = 847577) B847577
theorem B892873 : Blo 467785 892873 := bstep (se 2 (by rfl) ⟨334827, by rfl⟩ : syracuseStep 892873 = 669655) B669655
theorem B794569 : Blo 467785 794569 := bstep (se 2 (by rfl) ⟨297963, by rfl⟩ : syracuseStep 794569 = 595927) B595927
theorem B1187855 : Blo 467785 1187855 := bstep (se 1 (by rfl) ⟨890891, by rfl⟩ : syracuseStep 1187855 = 1781783) B1781783
theorem B1056887 : Blo 467785 1056887 := bstep (se 1 (by rfl) ⟨792665, by rfl⟩ : syracuseStep 1056887 = 1585331) B1585331
theorem B1057067 : Blo 467785 1057067 := bstep (se 1 (by rfl) ⟨792800, by rfl⟩ : syracuseStep 1057067 = 1585601) B1585601
theorem B5710139 : Blo 467785 5710139 := bstep (se 1 (by rfl) ⟨4282604, by rfl⟩ : syracuseStep 5710139 = 8565209) B8565209
theorem B1581497 : Blo 467785 1581497 := bstep (se 2 (by rfl) ⟨593061, by rfl⟩ : syracuseStep 1581497 = 1186123) B1186123
theorem B795271 : Blo 467785 795271 := bstep (se 1 (by rfl) ⟨596453, by rfl⟩ : syracuseStep 795271 = 1192907) B1192907
theorem B1057427 : Blo 467785 1057427 := bstep (se 1 (by rfl) ⟨793070, by rfl⟩ : syracuseStep 1057427 = 1586141) B1586141
theorem B893587 : Blo 467785 893587 := bstep (se 1 (by rfl) ⟨670190, by rfl⟩ : syracuseStep 893587 = 1340381) B1340381
theorem B2138825 : Blo 467785 2138825 := bstep (se 2 (by rfl) ⟨802059, by rfl⟩ : syracuseStep 2138825 = 1604119) B1604119
theorem B1188553 : Blo 467785 1188553 := bstep (se 2 (by rfl) ⟨445707, by rfl⟩ : syracuseStep 1188553 = 891415) B891415
theorem B1057481 : Blo 467785 1057481 := bstep (se 2 (by rfl) ⟨396555, by rfl⟩ : syracuseStep 1057481 = 793111) B793111
theorem B1188695 : Blo 467785 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B467847 : Blo 467785 467847 := bstep (se 1 (by rfl) ⟨350885, by rfl⟩ : syracuseStep 467847 = 701771) B701771
theorem B467855 : Blo 467785 467855 := bstep (se 1 (by rfl) ⟨350891, by rfl⟩ : syracuseStep 467855 = 701783) B701783
theorem B467899 : Blo 467785 467899 := bstep (se 1 (by rfl) ⟨350924, by rfl⟩ : syracuseStep 467899 = 701849) B701849
theorem B467975 : Blo 467785 467975 := bstep (se 1 (by rfl) ⟨350981, by rfl⟩ : syracuseStep 467975 = 701963) B701963
theorem B1778699 : Blo 467785 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B1582091 : Blo 467785 1582091 := bstep (se 1 (by rfl) ⟨1186568, by rfl⟩ : syracuseStep 1582091 = 2373137) B2373137
theorem B467983 : Blo 467785 467983 := bstep (se 1 (by rfl) ⟨350987, by rfl⟩ : syracuseStep 467983 = 701975) B701975
theorem B468027 : Blo 467785 468027 := bstep (se 1 (by rfl) ⟨351020, by rfl⟩ : syracuseStep 468027 = 702041) B702041
theorem B1582199 : Blo 467785 1582199 := bstep (se 1 (by rfl) ⟨1186649, by rfl⟩ : syracuseStep 1582199 = 2373299) B2373299
theorem B468103 : Blo 467785 468103 := bstep (se 1 (by rfl) ⟨351077, by rfl⟩ : syracuseStep 468103 = 702155) B702155
theorem B533647 : Blo 467785 533647 := bstep (se 1 (by rfl) ⟨400235, by rfl⟩ : syracuseStep 533647 = 800471) B800471
theorem B468111 : Blo 467785 468111 := bstep (se 1 (by rfl) ⟨351083, by rfl⟩ : syracuseStep 468111 = 702167) B702167
theorem B468155 : Blo 467785 468155 := bstep (se 1 (by rfl) ⟨351116, by rfl⟩ : syracuseStep 468155 = 702233) B702233
theorem B468231 : Blo 467785 468231 := bstep (se 1 (by rfl) ⟨351173, by rfl⟩ : syracuseStep 468231 = 702347) B702347
theorem B468239 : Blo 467785 468239 := bstep (se 1 (by rfl) ⟨351179, by rfl⟩ : syracuseStep 468239 = 702359) B702359
theorem B795919 : Blo 467785 795919 := bstep (se 1 (by rfl) ⟨596939, by rfl⟩ : syracuseStep 795919 = 1193879) B1193879
theorem B468283 : Blo 467785 468283 := bstep (se 1 (by rfl) ⟨351212, by rfl⟩ : syracuseStep 468283 = 702425) B702425
theorem B763195 : Blo 467785 763195 := bstep (se 1 (by rfl) ⟨572396, by rfl⟩ : syracuseStep 763195 = 1144793) B1144793
theorem B2237755 : Blo 467785 2237755 := bstep (se 1 (by rfl) ⟨1678316, by rfl⟩ : syracuseStep 2237755 = 3356633) B3356633
theorem B468359 : Blo 467785 468359 := bstep (se 1 (by rfl) ⟨351269, by rfl⟩ : syracuseStep 468359 = 702539) B702539
theorem B1058183 : Blo 467785 1058183 := bstep (se 1 (by rfl) ⟨793637, by rfl⟩ : syracuseStep 1058183 = 1587275) B1587275
theorem B468367 : Blo 467785 468367 := bstep (se 1 (by rfl) ⟨351275, by rfl⟩ : syracuseStep 468367 = 702551) B702551
theorem B468411 : Blo 467785 468411 := bstep (se 1 (by rfl) ⟨351308, by rfl⟩ : syracuseStep 468411 = 702617) B702617
theorem B468487 : Blo 467785 468487 := bstep (se 1 (by rfl) ⟨351365, by rfl⟩ : syracuseStep 468487 = 702731) B702731
theorem B468495 : Blo 467785 468495 := bstep (se 1 (by rfl) ⟨351371, by rfl⟩ : syracuseStep 468495 = 702743) B702743
theorem B468539 : Blo 467785 468539 := bstep (se 1 (by rfl) ⟨351404, by rfl⟩ : syracuseStep 468539 = 702809) B702809
theorem B1058363 : Blo 467785 1058363 := bstep (se 1 (by rfl) ⟨793772, by rfl⟩ : syracuseStep 1058363 = 1587545) B1587545
theorem B468615 : Blo 467785 468615 := bstep (se 1 (by rfl) ⟨351461, by rfl⟩ : syracuseStep 468615 = 702923) B702923
theorem B468623 : Blo 467785 468623 := bstep (se 1 (by rfl) ⟨351467, by rfl⟩ : syracuseStep 468623 = 702935) B702935
theorem B1058489 : Blo 467785 1058489 := bstep (se 2 (by rfl) ⟨396933, by rfl⟩ : syracuseStep 1058489 = 793867) B793867
theorem B468667 : Blo 467785 468667 := bstep (se 1 (by rfl) ⟨351500, by rfl⟩ : syracuseStep 468667 = 703001) B703001
theorem B1582793 : Blo 467785 1582793 := bstep (se 2 (by rfl) ⟨593547, by rfl⟩ : syracuseStep 1582793 = 1187095) B1187095
theorem B894665 : Blo 467785 894665 := bstep (se 2 (by rfl) ⟨335499, by rfl⟩ : syracuseStep 894665 = 670999) B670999
theorem B468743 : Blo 467785 468743 := bstep (se 1 (by rfl) ⟨351557, by rfl⟩ : syracuseStep 468743 = 703115) B703115
theorem B468751 : Blo 467785 468751 := bstep (se 1 (by rfl) ⟨351563, by rfl⟩ : syracuseStep 468751 = 703127) B703127
theorem B468795 : Blo 467785 468795 := bstep (se 1 (by rfl) ⟨351596, by rfl⟩ : syracuseStep 468795 = 703193) B703193
theorem B468871 : Blo 467785 468871 := bstep (se 1 (by rfl) ⟨351653, by rfl⟩ : syracuseStep 468871 = 703307) B703307
theorem B468879 : Blo 467785 468879 := bstep (se 1 (by rfl) ⟨351659, by rfl⟩ : syracuseStep 468879 = 703319) B703319
theorem B1779641 : Blo 467785 1779641 := bstep (se 2 (by rfl) ⟨667365, by rfl⟩ : syracuseStep 1779641 = 1334731) B1334731
theorem B468923 : Blo 467785 468923 := bstep (se 1 (by rfl) ⟨351692, by rfl⟩ : syracuseStep 468923 = 703385) B703385
theorem B468999 : Blo 467785 468999 := bstep (se 1 (by rfl) ⟨351749, by rfl⟩ : syracuseStep 468999 = 703499) B703499
theorem B469007 : Blo 467785 469007 := bstep (se 1 (by rfl) ⟨351755, by rfl⟩ : syracuseStep 469007 = 703511) B703511
theorem B1058831 : Blo 467785 1058831 := bstep (se 1 (by rfl) ⟨794123, by rfl⟩ : syracuseStep 1058831 = 1588247) B1588247
theorem B1058849 : Blo 467785 1058849 := bstep (se 2 (by rfl) ⟨397068, by rfl⟩ : syracuseStep 1058849 = 794137) B794137
theorem B469051 : Blo 467785 469051 := bstep (se 1 (by rfl) ⟨351788, by rfl⟩ : syracuseStep 469051 = 703577) B703577
theorem B469127 : Blo 467785 469127 := bstep (se 1 (by rfl) ⟨351845, by rfl⟩ : syracuseStep 469127 = 703691) B703691
theorem B469135 : Blo 467785 469135 := bstep (se 1 (by rfl) ⟨351851, by rfl⟩ : syracuseStep 469135 = 703703) B703703
theorem B469179 : Blo 467785 469179 := bstep (se 1 (by rfl) ⟨351884, by rfl⟩ : syracuseStep 469179 = 703769) B703769
theorem B2664677 : Blo 467785 2664677 := bstep (se 4 (by rfl) ⟨249813, by rfl⟩ : syracuseStep 2664677 = 499627) B499627
theorem B469255 : Blo 467785 469255 := bstep (se 1 (by rfl) ⟨351941, by rfl⟩ : syracuseStep 469255 = 703883) B703883
theorem B469263 : Blo 467785 469263 := bstep (se 1 (by rfl) ⟨351947, by rfl⟩ : syracuseStep 469263 = 703895) B703895
theorem B469307 : Blo 467785 469307 := bstep (se 1 (by rfl) ⟨351980, by rfl⟩ : syracuseStep 469307 = 703961) B703961
theorem B1059191 : Blo 467785 1059191 := bstep (se 1 (by rfl) ⟨794393, by rfl⟩ : syracuseStep 1059191 = 1588787) B1588787
theorem B1583495 : Blo 467785 1583495 := bstep (se 1 (by rfl) ⟨1187621, by rfl⟩ : syracuseStep 1583495 = 2375243) B2375243
theorem B469383 : Blo 467785 469383 := bstep (se 1 (by rfl) ⟨352037, by rfl⟩ : syracuseStep 469383 = 704075) B704075
theorem B469391 : Blo 467785 469391 := bstep (se 1 (by rfl) ⟨352043, by rfl⟩ : syracuseStep 469391 = 704087) B704087
theorem B4827539 : Blo 467785 4827539 := bstep (se 1 (by rfl) ⟨3620654, by rfl⟩ : syracuseStep 4827539 = 7241309) B7241309
theorem B469435 : Blo 467785 469435 := bstep (se 1 (by rfl) ⟨352076, by rfl⟩ : syracuseStep 469435 = 704153) B704153
theorem B469511 : Blo 467785 469511 := bstep (se 1 (by rfl) ⟨352133, by rfl⟩ : syracuseStep 469511 = 704267) B704267
theorem B2370059 : Blo 467785 2370059 := bstep (se 1 (by rfl) ⟨1777544, by rfl⟩ : syracuseStep 2370059 = 3555089) B3555089
theorem B469519 : Blo 467785 469519 := bstep (se 1 (by rfl) ⟨352139, by rfl⟩ : syracuseStep 469519 = 704279) B704279
theorem B1059371 : Blo 467785 1059371 := bstep (se 1 (by rfl) ⟨794528, by rfl⟩ : syracuseStep 1059371 = 1589057) B1589057
theorem B895531 : Blo 467785 895531 := bstep (se 1 (by rfl) ⟨671648, by rfl⟩ : syracuseStep 895531 = 1343297) B1343297
theorem B469563 : Blo 467785 469563 := bstep (se 1 (by rfl) ⟨352172, by rfl⟩ : syracuseStep 469563 = 704345) B704345
theorem B2533949 : Blo 467785 2533949 := bstep (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) B950231
theorem B895607 : Blo 467785 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B1124999 : Blo 467785 1124999 := bstep (se 1 (by rfl) ⟨843749, by rfl⟩ : syracuseStep 1124999 = 1687499) B1687499
theorem B469639 : Blo 467785 469639 := bstep (se 1 (by rfl) ⟨352229, by rfl⟩ : syracuseStep 469639 = 704459) B704459
theorem B469647 : Blo 467785 469647 := bstep (se 1 (by rfl) ⟨352235, by rfl⟩ : syracuseStep 469647 = 704471) B704471
theorem B2665133 : Blo 467785 2665133 := bstep (se 3 (by rfl) ⟨499712, by rfl⟩ : syracuseStep 2665133 = 999425) B999425
theorem B2370221 : Blo 467785 2370221 := bstep (se 3 (by rfl) ⟨444416, by rfl⟩ : syracuseStep 2370221 = 888833) B888833
theorem B469691 : Blo 467785 469691 := bstep (se 1 (by rfl) ⟨352268, by rfl⟩ : syracuseStep 469691 = 704537) B704537
theorem B1583873 : Blo 467785 1583873 := bstep (se 2 (by rfl) ⟨593952, by rfl⟩ : syracuseStep 1583873 = 1187905) B1187905
theorem B469767 : Blo 467785 469767 := bstep (se 1 (by rfl) ⟨352325, by rfl⟩ : syracuseStep 469767 = 704651) B704651
theorem B469775 : Blo 467785 469775 := bstep (se 1 (by rfl) ⟨352331, by rfl⟩ : syracuseStep 469775 = 704663) B704663
theorem B469819 : Blo 467785 469819 := bstep (se 1 (by rfl) ⟨352364, by rfl⟩ : syracuseStep 469819 = 704729) B704729
theorem B4500299 : Blo 467785 4500299 := bstep (se 1 (by rfl) ⟨3375224, by rfl⟩ : syracuseStep 4500299 = 6750449) B6750449
theorem B1190771 : Blo 467785 1190771 := bstep (se 1 (by rfl) ⟨893078, by rfl⟩ : syracuseStep 1190771 = 1786157) B1786157
theorem B469895 : Blo 467785 469895 := bstep (se 1 (by rfl) ⟨352421, by rfl⟩ : syracuseStep 469895 = 704843) B704843
theorem B469903 : Blo 467785 469903 := bstep (se 1 (by rfl) ⟨352427, by rfl⟩ : syracuseStep 469903 = 704855) B704855
theorem B1059731 : Blo 467785 1059731 := bstep (se 1 (by rfl) ⟨794798, by rfl⟩ : syracuseStep 1059731 = 1589597) B1589597
theorem B469947 : Blo 467785 469947 := bstep (se 1 (by rfl) ⟨352460, by rfl⟩ : syracuseStep 469947 = 704921) B704921
theorem B1059785 : Blo 467785 1059785 := bstep (se 2 (by rfl) ⟨397419, by rfl⟩ : syracuseStep 1059785 = 794839) B794839
theorem B470023 : Blo 467785 470023 := bstep (se 1 (by rfl) ⟨352517, by rfl⟩ : syracuseStep 470023 = 705035) B705035
theorem B470031 : Blo 467785 470031 := bstep (se 1 (by rfl) ⟨352523, by rfl⟩ : syracuseStep 470031 = 705047) B705047
theorem B470075 : Blo 467785 470075 := bstep (se 1 (by rfl) ⟨352556, by rfl⟩ : syracuseStep 470075 = 705113) B705113
theorem B470151 : Blo 467785 470151 := bstep (se 1 (by rfl) ⟨352613, by rfl⟩ : syracuseStep 470151 = 705227) B705227
theorem B470159 : Blo 467785 470159 := bstep (se 1 (by rfl) ⟨352619, by rfl⟩ : syracuseStep 470159 = 705239) B705239
theorem B470203 : Blo 467785 470203 := bstep (se 1 (by rfl) ⟨352652, by rfl⟩ : syracuseStep 470203 = 705305) B705305
theorem B470279 : Blo 467785 470279 := bstep (se 1 (by rfl) ⟨352709, by rfl⟩ : syracuseStep 470279 = 705419) B705419
theorem B470287 : Blo 467785 470287 := bstep (se 1 (by rfl) ⟨352715, by rfl⟩ : syracuseStep 470287 = 705431) B705431
theorem B634169 : Blo 467785 634169 := bstep (se 2 (by rfl) ⟨237813, by rfl⟩ : syracuseStep 634169 = 475627) B475627
theorem B470331 : Blo 467785 470331 := bstep (se 1 (by rfl) ⟨352748, by rfl⟩ : syracuseStep 470331 = 705497) B705497
theorem B2665817 : Blo 467785 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B1191287 : Blo 467785 1191287 := bstep (se 1 (by rfl) ⟨893465, by rfl⟩ : syracuseStep 1191287 = 1786931) B1786931
theorem B470407 : Blo 467785 470407 := bstep (se 1 (by rfl) ⟨352805, by rfl⟩ : syracuseStep 470407 = 705611) B705611
theorem B470415 : Blo 467785 470415 := bstep (se 1 (by rfl) ⟨352811, by rfl⟩ : syracuseStep 470415 = 705623) B705623
theorem B2010521 : Blo 467785 2010521 := bstep (se 2 (by rfl) ⟨753945, by rfl⟩ : syracuseStep 2010521 = 1507891) B1507891
theorem B470459 : Blo 467785 470459 := bstep (se 1 (by rfl) ⟨352844, by rfl⟩ : syracuseStep 470459 = 705689) B705689
theorem B470535 : Blo 467785 470535 := bstep (se 1 (by rfl) ⟨352901, by rfl⟩ : syracuseStep 470535 = 705803) B705803
theorem B470543 : Blo 467785 470543 := bstep (se 1 (by rfl) ⟨352907, by rfl⟩ : syracuseStep 470543 = 705815) B705815
theorem B1584683 : Blo 467785 1584683 := bstep (se 1 (by rfl) ⟨1188512, by rfl⟩ : syracuseStep 1584683 = 2377025) B2377025
theorem B470587 : Blo 467785 470587 := bstep (se 1 (by rfl) ⟨352940, by rfl⟩ : syracuseStep 470587 = 705881) B705881
theorem B2010743 : Blo 467785 2010743 := bstep (se 1 (by rfl) ⟨1508057, by rfl⟩ : syracuseStep 2010743 = 3016115) B3016115
theorem B470663 : Blo 467785 470663 := bstep (se 1 (by rfl) ⟨352997, by rfl⟩ : syracuseStep 470663 = 705995) B705995
theorem B1060487 : Blo 467785 1060487 := bstep (se 1 (by rfl) ⟨795365, by rfl⟩ : syracuseStep 1060487 = 1590731) B1590731
theorem B470671 : Blo 467785 470671 := bstep (se 1 (by rfl) ⟨353003, by rfl⟩ : syracuseStep 470671 = 706007) B706007
theorem B470715 : Blo 467785 470715 := bstep (se 1 (by rfl) ⟨353036, by rfl⟩ : syracuseStep 470715 = 706073) B706073
theorem B1912577 : Blo 467785 1912577 := bstep (se 2 (by rfl) ⟨717216, by rfl⟩ : syracuseStep 1912577 = 1434433) B1434433
theorem B470791 : Blo 467785 470791 := bstep (se 1 (by rfl) ⟨353093, by rfl⟩ : syracuseStep 470791 = 706187) B706187
theorem B470799 : Blo 467785 470799 := bstep (se 1 (by rfl) ⟨353099, by rfl⟩ : syracuseStep 470799 = 706199) B706199
theorem B470843 : Blo 467785 470843 := bstep (se 1 (by rfl) ⟨353132, by rfl⟩ : syracuseStep 470843 = 706265) B706265
theorem B1060667 : Blo 467785 1060667 := bstep (se 1 (by rfl) ⟨795500, by rfl⟩ : syracuseStep 1060667 = 1591001) B1591001
theorem B601975 : Blo 467785 601975 := bstep (se 1 (by rfl) ⟨451481, by rfl⟩ : syracuseStep 601975 = 902963) B902963
theorem B470919 : Blo 467785 470919 := bstep (se 1 (by rfl) ⟨353189, by rfl⟩ : syracuseStep 470919 = 706379) B706379
theorem B470927 : Blo 467785 470927 := bstep (se 1 (by rfl) ⟨353195, by rfl⟩ : syracuseStep 470927 = 706391) B706391
theorem B1060793 : Blo 467785 1060793 := bstep (se 2 (by rfl) ⟨397797, by rfl⟩ : syracuseStep 1060793 = 795595) B795595
theorem B470971 : Blo 467785 470971 := bstep (se 1 (by rfl) ⟨353228, by rfl⟩ : syracuseStep 470971 = 706457) B706457
theorem B667639 : Blo 467785 667639 := bstep (se 1 (by rfl) ⟨500729, by rfl⟩ : syracuseStep 667639 = 1001459) B1001459
theorem B634871 : Blo 467785 634871 := bstep (se 1 (by rfl) ⟨476153, by rfl⟩ : syracuseStep 634871 = 952307) B952307
theorem B471047 : Blo 467785 471047 := bstep (se 1 (by rfl) ⟨353285, by rfl⟩ : syracuseStep 471047 = 706571) B706571
theorem B471055 : Blo 467785 471055 := bstep (se 1 (by rfl) ⟨353291, by rfl⟩ : syracuseStep 471055 = 706583) B706583
theorem B471099 : Blo 467785 471099 := bstep (se 1 (by rfl) ⟨353324, by rfl⟩ : syracuseStep 471099 = 706649) B706649
theorem B4501565 : Blo 467785 4501565 := bstep (se 3 (by rfl) ⟨844043, by rfl⟩ : syracuseStep 4501565 = 1688087) B1688087
theorem B471175 : Blo 467785 471175 := bstep (se 1 (by rfl) ⟨353381, by rfl⟩ : syracuseStep 471175 = 706763) B706763
theorem B471183 : Blo 467785 471183 := bstep (se 1 (by rfl) ⟨353387, by rfl⟩ : syracuseStep 471183 = 706775) B706775
theorem B471227 : Blo 467785 471227 := bstep (se 1 (by rfl) ⟨353420, by rfl⟩ : syracuseStep 471227 = 706841) B706841
theorem B2371841 : Blo 467785 2371841 := bstep (se 2 (by rfl) ⟨889440, by rfl⟩ : syracuseStep 2371841 = 1778881) B1778881
theorem B471303 : Blo 467785 471303 := bstep (se 1 (by rfl) ⟨353477, by rfl⟩ : syracuseStep 471303 = 706955) B706955
theorem B471311 : Blo 467785 471311 := bstep (se 1 (by rfl) ⟨353483, by rfl⟩ : syracuseStep 471311 = 706967) B706967
theorem B1061135 : Blo 467785 1061135 := bstep (se 1 (by rfl) ⟨795851, by rfl⟩ : syracuseStep 1061135 = 1591703) B1591703
theorem B1061153 : Blo 467785 1061153 := bstep (se 2 (by rfl) ⟨397932, by rfl⟩ : syracuseStep 1061153 = 795865) B795865
theorem B471355 : Blo 467785 471355 := bstep (se 1 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 471355 = 707033) B707033
theorem B1192279 : Blo 467785 1192279 := bstep (se 1 (by rfl) ⟨894209, by rfl⟩ : syracuseStep 1192279 = 1788419) B1788419
theorem B471431 : Blo 467785 471431 := bstep (se 1 (by rfl) ⟨353573, by rfl⟩ : syracuseStep 471431 = 707147) B707147
theorem B471439 : Blo 467785 471439 := bstep (se 1 (by rfl) ⟨353579, by rfl⟩ : syracuseStep 471439 = 707159) B707159
theorem B471483 : Blo 467785 471483 := bstep (se 1 (by rfl) ⟨353612, by rfl⟩ : syracuseStep 471483 = 707225) B707225
theorem B471559 : Blo 467785 471559 := bstep (se 1 (by rfl) ⟨353669, by rfl⟩ : syracuseStep 471559 = 707339) B707339
theorem B1782283 : Blo 467785 1782283 := bstep (se 1 (by rfl) ⟨1336712, by rfl⟩ : syracuseStep 1782283 = 2673425) B2673425
theorem B471567 : Blo 467785 471567 := bstep (se 1 (by rfl) ⟨353675, by rfl⟩ : syracuseStep 471567 = 707351) B707351
theorem B471611 : Blo 467785 471611 := bstep (se 1 (by rfl) ⟨353708, by rfl⟩ : syracuseStep 471611 = 707417) B707417
theorem B1127027 : Blo 467785 1127027 := bstep (se 1 (by rfl) ⟨845270, by rfl⟩ : syracuseStep 1127027 = 1690541) B1690541
theorem B1061495 : Blo 467785 1061495 := bstep (se 1 (by rfl) ⟨796121, by rfl⟩ : syracuseStep 1061495 = 1592243) B1592243
theorem B1192583 : Blo 467785 1192583 := bstep (se 1 (by rfl) ⟨894437, by rfl⟩ : syracuseStep 1192583 = 1788875) B1788875
theorem B471687 : Blo 467785 471687 := bstep (se 1 (by rfl) ⟨353765, by rfl⟩ : syracuseStep 471687 = 707531) B707531
theorem B471695 : Blo 467785 471695 := bstep (se 1 (by rfl) ⟨353771, by rfl⟩ : syracuseStep 471695 = 707543) B707543
theorem B471739 : Blo 467785 471739 := bstep (se 1 (by rfl) ⟨353804, by rfl⟩ : syracuseStep 471739 = 707609) B707609
theorem B1192715 : Blo 467785 1192715 := bstep (se 1 (by rfl) ⟨894536, by rfl⟩ : syracuseStep 1192715 = 1789073) B1789073
theorem B668459 : Blo 467785 668459 := bstep (se 1 (by rfl) ⟨501344, by rfl⟩ : syracuseStep 668459 = 1002689) B1002689
theorem B1782587 : Blo 467785 1782587 := bstep (se 1 (by rfl) ⟨1336940, by rfl⟩ : syracuseStep 1782587 = 2673881) B2673881
theorem B1585979 : Blo 467785 1585979 := bstep (se 1 (by rfl) ⟨1189484, by rfl⟩ : syracuseStep 1585979 = 2378969) B2378969
theorem B1127353 : Blo 467785 1127353 := bstep (se 2 (by rfl) ⟨422757, by rfl⟩ : syracuseStep 1127353 = 845515) B845515
theorem B2372651 : Blo 467785 2372651 := bstep (se 1 (by rfl) ⟨1779488, by rfl⟩ : syracuseStep 2372651 = 3558977) B3558977
theorem B1127467 : Blo 467785 1127467 := bstep (se 1 (by rfl) ⟨845600, by rfl⟩ : syracuseStep 1127467 = 1691201) B1691201
theorem B701687 : Blo 467785 701687 := bstep (se 1 (by rfl) ⟨526265, by rfl⟩ : syracuseStep 701687 = 1052531) B1052531
theorem B701711 : Blo 467785 701711 := bstep (se 1 (by rfl) ⟨526283, by rfl⟩ : syracuseStep 701711 = 1052567) B1052567
theorem B1193231 : Blo 467785 1193231 := bstep (se 1 (by rfl) ⟨894923, by rfl⟩ : syracuseStep 1193231 = 1789847) B1789847
theorem B1783073 : Blo 467785 1783073 := bstep (se 2 (by rfl) ⟨668652, by rfl⟩ : syracuseStep 1783073 = 1337305) B1337305
theorem B1586465 : Blo 467785 1586465 := bstep (se 2 (by rfl) ⟨594924, by rfl⟩ : syracuseStep 1586465 = 1189849) B1189849
theorem B701753 : Blo 467785 701753 := bstep (se 2 (by rfl) ⟨263157, by rfl⟩ : syracuseStep 701753 = 526315) B526315
theorem B701831 : Blo 467785 701831 := bstep (se 1 (by rfl) ⟨526373, by rfl⟩ : syracuseStep 701831 = 1052747) B1052747
theorem B3552659 : Blo 467785 3552659 := bstep (se 1 (by rfl) ⟨2664494, by rfl⟩ : syracuseStep 3552659 = 5328989) B5328989
theorem B1193363 : Blo 467785 1193363 := bstep (se 1 (by rfl) ⟨895022, by rfl⟩ : syracuseStep 1193363 = 1790045) B1790045
theorem B701867 : Blo 467785 701867 := bstep (se 1 (by rfl) ⟨526400, by rfl⟩ : syracuseStep 701867 = 1052801) B1052801
theorem B701897 : Blo 467785 701897 := bstep (se 2 (by rfl) ⟨263211, by rfl⟩ : syracuseStep 701897 = 526423) B526423
theorem B3225091 : Blo 467785 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B1127969 : Blo 467785 1127969 := bstep (se 2 (by rfl) ⟨422988, by rfl⟩ : syracuseStep 1127969 = 845977) B845977
theorem B702011 : Blo 467785 702011 := bstep (se 1 (by rfl) ⟨526508, by rfl⟩ : syracuseStep 702011 = 1053017) B1053017
theorem B2012759 : Blo 467785 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B8566373 : Blo 467785 8566373 := bstep (se 4 (by rfl) ⟨803097, by rfl⟩ : syracuseStep 8566373 = 1606195) B1606195
theorem B702071 : Blo 467785 702071 := bstep (se 1 (by rfl) ⟨526553, by rfl⟩ : syracuseStep 702071 = 1053107) B1053107
theorem B702095 : Blo 467785 702095 := bstep (se 1 (by rfl) ⟨526571, by rfl⟩ : syracuseStep 702095 = 1053143) B1053143
theorem B702137 : Blo 467785 702137 := bstep (se 2 (by rfl) ⟨263301, by rfl⟩ : syracuseStep 702137 = 526603) B526603
theorem B702215 : Blo 467785 702215 := bstep (se 1 (by rfl) ⟨526661, by rfl⟩ : syracuseStep 702215 = 1053323) B1053323
theorem B702251 : Blo 467785 702251 := bstep (se 1 (by rfl) ⟨526688, by rfl⟩ : syracuseStep 702251 = 1053377) B1053377
theorem B702281 : Blo 467785 702281 := bstep (se 2 (by rfl) ⟨263355, by rfl⟩ : syracuseStep 702281 = 526711) B526711
theorem B1587059 : Blo 467785 1587059 := bstep (se 1 (by rfl) ⟨1190294, by rfl⟩ : syracuseStep 1587059 = 2380589) B2380589
theorem B702395 : Blo 467785 702395 := bstep (se 1 (by rfl) ⟨526796, by rfl⟩ : syracuseStep 702395 = 1053593) B1053593
theorem B702455 : Blo 467785 702455 := bstep (se 1 (by rfl) ⟨526841, by rfl⟩ : syracuseStep 702455 = 1053683) B1053683
theorem B702479 : Blo 467785 702479 := bstep (se 1 (by rfl) ⟨526859, by rfl⟩ : syracuseStep 702479 = 1053719) B1053719
theorem B702521 : Blo 467785 702521 := bstep (se 2 (by rfl) ⟨263445, by rfl⟩ : syracuseStep 702521 = 526891) B526891
theorem B702599 : Blo 467785 702599 := bstep (se 1 (by rfl) ⟨526949, by rfl⟩ : syracuseStep 702599 = 1053899) B1053899
theorem B1128583 : Blo 467785 1128583 := bstep (se 1 (by rfl) ⟨846437, by rfl⟩ : syracuseStep 1128583 = 1692875) B1692875
theorem B702635 : Blo 467785 702635 := bstep (se 1 (by rfl) ⟨526976, by rfl⟩ : syracuseStep 702635 = 1053953) B1053953
theorem B669883 : Blo 467785 669883 := bstep (se 1 (by rfl) ⟨502412, by rfl⟩ : syracuseStep 669883 = 1004825) B1004825
theorem B702665 : Blo 467785 702665 := bstep (se 2 (by rfl) ⟨263499, by rfl⟩ : syracuseStep 702665 = 526999) B526999
theorem B1784045 : Blo 467785 1784045 := bstep (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) B669017
theorem B2144513 : Blo 467785 2144513 := bstep (se 2 (by rfl) ⟨804192, by rfl⟩ : syracuseStep 2144513 = 1608385) B1608385
theorem B702779 : Blo 467785 702779 := bstep (se 1 (by rfl) ⟨527084, by rfl⟩ : syracuseStep 702779 = 1054169) B1054169
theorem B2373947 : Blo 467785 2373947 := bstep (se 1 (by rfl) ⟨1780460, by rfl⟩ : syracuseStep 2373947 = 3560921) B3560921
theorem B702839 : Blo 467785 702839 := bstep (se 1 (by rfl) ⟨527129, by rfl⟩ : syracuseStep 702839 = 1054259) B1054259
theorem B702863 : Blo 467785 702863 := bstep (se 1 (by rfl) ⟨527147, by rfl⟩ : syracuseStep 702863 = 1054295) B1054295
theorem B702905 : Blo 467785 702905 := bstep (se 2 (by rfl) ⟨263589, by rfl⟩ : syracuseStep 702905 = 527179) B527179
theorem B2374109 : Blo 467785 2374109 := bstep (se 3 (by rfl) ⟨445145, by rfl⟩ : syracuseStep 2374109 = 890291) B890291
theorem B6797789 : Blo 467785 6797789 := bstep (se 3 (by rfl) ⟨1274585, by rfl⟩ : syracuseStep 6797789 = 2549171) B2549171
theorem B702983 : Blo 467785 702983 := bstep (se 1 (by rfl) ⟨527237, by rfl⟩ : syracuseStep 702983 = 1054475) B1054475
theorem B703019 : Blo 467785 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B703049 : Blo 467785 703049 := bstep (se 2 (by rfl) ⟨263643, by rfl⟩ : syracuseStep 703049 = 527287) B527287
theorem B703163 : Blo 467785 703163 := bstep (se 1 (by rfl) ⟨527372, by rfl⟩ : syracuseStep 703163 = 1054745) B1054745
theorem B703223 : Blo 467785 703223 := bstep (se 1 (by rfl) ⟨527417, by rfl⟩ : syracuseStep 703223 = 1054835) B1054835
theorem B703247 : Blo 467785 703247 := bstep (se 1 (by rfl) ⟨527435, by rfl⟩ : syracuseStep 703247 = 1054871) B1054871
theorem B2374433 : Blo 467785 2374433 := bstep (se 2 (by rfl) ⟨890412, by rfl⟩ : syracuseStep 2374433 = 1780825) B1780825
theorem B3390245 : Blo 467785 3390245 := bstep (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) B635671
theorem B703289 : Blo 467785 703289 := bstep (se 2 (by rfl) ⟨263733, by rfl⟩ : syracuseStep 703289 = 527467) B527467
theorem B703367 : Blo 467785 703367 := bstep (se 1 (by rfl) ⟨527525, by rfl⟩ : syracuseStep 703367 = 1055051) B1055051
theorem B703403 : Blo 467785 703403 := bstep (se 1 (by rfl) ⟨527552, by rfl⟩ : syracuseStep 703403 = 1055105) B1055105
theorem B703433 : Blo 467785 703433 := bstep (se 2 (by rfl) ⟨263787, by rfl⟩ : syracuseStep 703433 = 527575) B527575
theorem B703547 : Blo 467785 703547 := bstep (se 1 (by rfl) ⟨527660, by rfl⟩ : syracuseStep 703547 = 1055321) B1055321
theorem B3423293 : Blo 467785 3423293 := bstep (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) B1283735
theorem B703607 : Blo 467785 703607 := bstep (se 1 (by rfl) ⟨527705, by rfl⟩ : syracuseStep 703607 = 1055411) B1055411
theorem B703631 : Blo 467785 703631 := bstep (se 1 (by rfl) ⟨527723, by rfl⟩ : syracuseStep 703631 = 1055447) B1055447
theorem B703673 : Blo 467785 703673 := bstep (se 2 (by rfl) ⟨263877, by rfl⟩ : syracuseStep 703673 = 527755) B527755
theorem B703751 : Blo 467785 703751 := bstep (se 1 (by rfl) ⟨527813, by rfl⟩ : syracuseStep 703751 = 1055627) B1055627
theorem B703787 : Blo 467785 703787 := bstep (se 1 (by rfl) ⟨527840, by rfl⟩ : syracuseStep 703787 = 1055681) B1055681
theorem B474427 : Blo 467785 474427 := bstep (se 1 (by rfl) ⟨355820, by rfl⟩ : syracuseStep 474427 = 711641) B711641
theorem B703817 : Blo 467785 703817 := bstep (se 2 (by rfl) ⟨263931, by rfl⟩ : syracuseStep 703817 = 527863) B527863
theorem B1359191 : Blo 467785 1359191 := bstep (se 1 (by rfl) ⟨1019393, by rfl⟩ : syracuseStep 1359191 = 2038787) B2038787
theorem B703931 : Blo 467785 703931 := bstep (se 1 (by rfl) ⟨527948, by rfl⟩ : syracuseStep 703931 = 1055897) B1055897
theorem B703991 : Blo 467785 703991 := bstep (se 1 (by rfl) ⟨527993, by rfl⟩ : syracuseStep 703991 = 1055987) B1055987
theorem B704015 : Blo 467785 704015 := bstep (se 1 (by rfl) ⟨528011, by rfl⟩ : syracuseStep 704015 = 1056023) B1056023
theorem B8535581 : Blo 467785 8535581 := bstep (se 3 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 8535581 = 3200843) B3200843
theorem B704057 : Blo 467785 704057 := bstep (se 2 (by rfl) ⟨264021, by rfl⟩ : syracuseStep 704057 = 528043) B528043
theorem B704135 : Blo 467785 704135 := bstep (se 1 (by rfl) ⟨528101, by rfl⟩ : syracuseStep 704135 = 1056203) B1056203
theorem B671375 : Blo 467785 671375 := bstep (se 1 (by rfl) ⟨503531, by rfl⟩ : syracuseStep 671375 = 1007063) B1007063
theorem B704171 : Blo 467785 704171 := bstep (se 1 (by rfl) ⟨528128, by rfl⟩ : syracuseStep 704171 = 1056257) B1056257
theorem B704201 : Blo 467785 704201 := bstep (se 2 (by rfl) ⟨264075, by rfl⟩ : syracuseStep 704201 = 528151) B528151
theorem B2375405 : Blo 467785 2375405 := bstep (se 3 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 2375405 = 890777) B890777
theorem B704315 : Blo 467785 704315 := bstep (se 1 (by rfl) ⟨528236, by rfl⟩ : syracuseStep 704315 = 1056473) B1056473
theorem B704375 : Blo 467785 704375 := bstep (se 1 (by rfl) ⟨528281, by rfl⟩ : syracuseStep 704375 = 1056563) B1056563
theorem B704399 : Blo 467785 704399 := bstep (se 1 (by rfl) ⟨528299, by rfl⟩ : syracuseStep 704399 = 1056599) B1056599
theorem B704441 : Blo 467785 704441 := bstep (se 2 (by rfl) ⟨264165, by rfl⟩ : syracuseStep 704441 = 528331) B528331
theorem B704519 : Blo 467785 704519 := bstep (se 1 (by rfl) ⟨528389, by rfl⟩ : syracuseStep 704519 = 1056779) B1056779
theorem B704555 : Blo 467785 704555 := bstep (se 1 (by rfl) ⟨528416, by rfl⟩ : syracuseStep 704555 = 1056833) B1056833
theorem B704585 : Blo 467785 704585 := bstep (se 2 (by rfl) ⟨264219, by rfl⟩ : syracuseStep 704585 = 528439) B528439
theorem B1130611 : Blo 467785 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B11452589 : Blo 467785 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B704699 : Blo 467785 704699 := bstep (se 1 (by rfl) ⟨528524, by rfl⟩ : syracuseStep 704699 = 1057049) B1057049
theorem B5488877 : Blo 467785 5488877 := bstep (se 3 (by rfl) ⟨1029164, by rfl⟩ : syracuseStep 5488877 = 2058329) B2058329
theorem B704759 : Blo 467785 704759 := bstep (se 1 (by rfl) ⟨528569, by rfl⟩ : syracuseStep 704759 = 1057139) B1057139
theorem B704783 : Blo 467785 704783 := bstep (se 1 (by rfl) ⟨528587, by rfl⟩ : syracuseStep 704783 = 1057175) B1057175
theorem B704825 : Blo 467785 704825 := bstep (se 2 (by rfl) ⟨264309, by rfl⟩ : syracuseStep 704825 = 528619) B528619
theorem B1786171 : Blo 467785 1786171 := bstep (se 1 (by rfl) ⟨1339628, by rfl⟩ : syracuseStep 1786171 = 2679257) B2679257
theorem B704903 : Blo 467785 704903 := bstep (se 1 (by rfl) ⟨528677, by rfl⟩ : syracuseStep 704903 = 1057355) B1057355
theorem B1589651 : Blo 467785 1589651 := bstep (se 1 (by rfl) ⟨1192238, by rfl⟩ : syracuseStep 1589651 = 2384477) B2384477
theorem B704939 : Blo 467785 704939 := bstep (se 1 (by rfl) ⟨528704, by rfl⟩ : syracuseStep 704939 = 1057409) B1057409
theorem B704969 : Blo 467785 704969 := bstep (se 2 (by rfl) ⟨264363, by rfl⟩ : syracuseStep 704969 = 528727) B528727
theorem B20595185 : Blo 467785 20595185 := bstep (se 2 (by rfl) ⟨7723194, by rfl⟩ : syracuseStep 20595185 = 15446389) B15446389
theorem B2867723 : Blo 467785 2867723 := bstep (se 1 (by rfl) ⟨2150792, by rfl⟩ : syracuseStep 2867723 = 4301585) B4301585
theorem B2376215 : Blo 467785 2376215 := bstep (se 1 (by rfl) ⟨1782161, by rfl⟩ : syracuseStep 2376215 = 3564323) B3564323
theorem B803387 : Blo 467785 803387 := bstep (se 1 (by rfl) ⟨602540, by rfl⟩ : syracuseStep 803387 = 1205081) B1205081
theorem B705083 : Blo 467785 705083 := bstep (se 1 (by rfl) ⟨528812, by rfl⟩ : syracuseStep 705083 = 1057625) B1057625
theorem B705143 : Blo 467785 705143 := bstep (se 1 (by rfl) ⟨528857, by rfl⟩ : syracuseStep 705143 = 1057715) B1057715
theorem B705167 : Blo 467785 705167 := bstep (se 1 (by rfl) ⟨528875, by rfl⟩ : syracuseStep 705167 = 1057751) B1057751
theorem B705209 : Blo 467785 705209 := bstep (se 2 (by rfl) ⟨264453, by rfl⟩ : syracuseStep 705209 = 528907) B528907
theorem B9126593 : Blo 467785 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B4014785 : Blo 467785 4014785 := bstep (se 2 (by rfl) ⟨1505544, by rfl⟩ : syracuseStep 4014785 = 3011089) B3011089
theorem B79086293 : Blo 467785 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B2540261 : Blo 467785 2540261 := bstep (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) B476299
theorem B705287 : Blo 467785 705287 := bstep (se 1 (by rfl) ⟨528965, by rfl⟩ : syracuseStep 705287 = 1057931) B1057931
theorem B1786657 : Blo 467785 1786657 := bstep (se 2 (by rfl) ⟨669996, by rfl⟩ : syracuseStep 1786657 = 1339993) B1339993
theorem B705323 : Blo 467785 705323 := bstep (se 1 (by rfl) ⟨528992, by rfl⟩ : syracuseStep 705323 = 1057985) B1057985
theorem B705353 : Blo 467785 705353 := bstep (se 2 (by rfl) ⟨264507, by rfl⟩ : syracuseStep 705353 = 529015) B529015
theorem B15287129 : Blo 467785 15287129 := bstep (se 2 (by rfl) ⟨5732673, by rfl⟩ : syracuseStep 15287129 = 11465347) B11465347
theorem B705467 : Blo 467785 705467 := bstep (se 1 (by rfl) ⟨529100, by rfl⟩ : syracuseStep 705467 = 1058201) B1058201
theorem B705527 : Blo 467785 705527 := bstep (se 1 (by rfl) ⟨529145, by rfl⟩ : syracuseStep 705527 = 1058291) B1058291
theorem B705551 : Blo 467785 705551 := bstep (se 1 (by rfl) ⟨529163, by rfl⟩ : syracuseStep 705551 = 1058327) B1058327
theorem B1131563 : Blo 467785 1131563 := bstep (se 1 (by rfl) ⟨848672, by rfl⟩ : syracuseStep 1131563 = 1697345) B1697345
theorem B705593 : Blo 467785 705593 := bstep (se 2 (by rfl) ⟨264597, by rfl⟩ : syracuseStep 705593 = 529195) B529195
theorem B705671 : Blo 467785 705671 := bstep (se 1 (by rfl) ⟨529253, by rfl⟩ : syracuseStep 705671 = 1058507) B1058507
theorem B705707 : Blo 467785 705707 := bstep (se 1 (by rfl) ⟨529280, by rfl⟩ : syracuseStep 705707 = 1058561) B1058561
theorem B705737 : Blo 467785 705737 := bstep (se 2 (by rfl) ⟨264651, by rfl⟩ : syracuseStep 705737 = 529303) B529303
theorem B705851 : Blo 467785 705851 := bstep (se 1 (by rfl) ⟨529388, by rfl⟩ : syracuseStep 705851 = 1058777) B1058777
theorem B705911 : Blo 467785 705911 := bstep (se 1 (by rfl) ⟨529433, by rfl⟩ : syracuseStep 705911 = 1058867) B1058867
theorem B705935 : Blo 467785 705935 := bstep (se 1 (by rfl) ⟨529451, by rfl⟩ : syracuseStep 705935 = 1058903) B1058903
theorem B705977 : Blo 467785 705977 := bstep (se 2 (by rfl) ⟨264741, by rfl⟩ : syracuseStep 705977 = 529483) B529483
theorem B706055 : Blo 467785 706055 := bstep (se 1 (by rfl) ⟨529541, by rfl⟩ : syracuseStep 706055 = 1059083) B1059083
theorem B706091 : Blo 467785 706091 := bstep (se 1 (by rfl) ⟨529568, by rfl⟩ : syracuseStep 706091 = 1059137) B1059137
theorem B706121 : Blo 467785 706121 := bstep (se 2 (by rfl) ⟨264795, by rfl⟩ : syracuseStep 706121 = 529591) B529591
theorem B706235 : Blo 467785 706235 := bstep (se 1 (by rfl) ⟨529676, by rfl⟩ : syracuseStep 706235 = 1059353) B1059353
theorem B1787629 : Blo 467785 1787629 := bstep (se 3 (by rfl) ⟨335180, by rfl⟩ : syracuseStep 1787629 = 670361) B670361
theorem B706295 : Blo 467785 706295 := bstep (se 1 (by rfl) ⟨529721, by rfl⟩ : syracuseStep 706295 = 1059443) B1059443
theorem B4572929 : Blo 467785 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B706319 : Blo 467785 706319 := bstep (se 1 (by rfl) ⟨529739, by rfl⟩ : syracuseStep 706319 = 1059479) B1059479
theorem B1591055 : Blo 467785 1591055 := bstep (se 1 (by rfl) ⟨1193291, by rfl⟩ : syracuseStep 1591055 = 2386583) B2386583
theorem B706361 : Blo 467785 706361 := bstep (se 2 (by rfl) ⟨264885, by rfl⟩ : syracuseStep 706361 = 529771) B529771
theorem B20531009 : Blo 467785 20531009 := bstep (se 2 (by rfl) ⟨7699128, by rfl⟩ : syracuseStep 20531009 = 15398257) B15398257
theorem B706439 : Blo 467785 706439 := bstep (se 1 (by rfl) ⟨529829, by rfl⟩ : syracuseStep 706439 = 1059659) B1059659
theorem B706475 : Blo 467785 706475 := bstep (se 1 (by rfl) ⟨529856, by rfl⟩ : syracuseStep 706475 = 1059713) B1059713
theorem B706505 : Blo 467785 706505 := bstep (se 2 (by rfl) ⟨264939, by rfl⟩ : syracuseStep 706505 = 529879) B529879
theorem B1787933 : Blo 467785 1787933 := bstep (se 3 (by rfl) ⟨335237, by rfl⟩ : syracuseStep 1787933 = 670475) B670475
theorem B1591325 : Blo 467785 1591325 := bstep (se 3 (by rfl) ⟨298373, by rfl⟩ : syracuseStep 1591325 = 596747) B596747
theorem B706619 : Blo 467785 706619 := bstep (se 1 (by rfl) ⟨529964, by rfl⟩ : syracuseStep 706619 = 1059929) B1059929
theorem B706679 : Blo 467785 706679 := bstep (se 1 (by rfl) ⟨530009, by rfl⟩ : syracuseStep 706679 = 1060019) B1060019
theorem B706703 : Blo 467785 706703 := bstep (se 1 (by rfl) ⟨530027, by rfl⟩ : syracuseStep 706703 = 1060055) B1060055
theorem B3360941 : Blo 467785 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B706745 : Blo 467785 706745 := bstep (se 2 (by rfl) ⟨265029, by rfl⟩ : syracuseStep 706745 = 530059) B530059
theorem B706823 : Blo 467785 706823 := bstep (se 1 (by rfl) ⟨530117, by rfl⟩ : syracuseStep 706823 = 1060235) B1060235
theorem B706859 : Blo 467785 706859 := bstep (se 1 (by rfl) ⟨530144, by rfl⟩ : syracuseStep 706859 = 1060289) B1060289
theorem B706889 : Blo 467785 706889 := bstep (se 2 (by rfl) ⟨265083, by rfl⟩ : syracuseStep 706889 = 530167) B530167
theorem B707003 : Blo 467785 707003 := bstep (se 1 (by rfl) ⟨530252, by rfl⟩ : syracuseStep 707003 = 1060505) B1060505
theorem B707063 : Blo 467785 707063 := bstep (se 1 (by rfl) ⟨530297, by rfl⟩ : syracuseStep 707063 = 1060595) B1060595
theorem B707087 : Blo 467785 707087 := bstep (se 1 (by rfl) ⟨530315, by rfl⟩ : syracuseStep 707087 = 1060631) B1060631
theorem B707129 : Blo 467785 707129 := bstep (se 2 (by rfl) ⟨265173, by rfl⟩ : syracuseStep 707129 = 530347) B530347
theorem B15419969 : Blo 467785 15419969 := bstep (se 2 (by rfl) ⟨5782488, by rfl⟩ : syracuseStep 15419969 = 11564977) B11564977
theorem B707207 : Blo 467785 707207 := bstep (se 1 (by rfl) ⟨530405, by rfl⟩ : syracuseStep 707207 = 1060811) B1060811
theorem B707243 : Blo 467785 707243 := bstep (se 1 (by rfl) ⟨530432, by rfl⟩ : syracuseStep 707243 = 1060865) B1060865
theorem B707273 : Blo 467785 707273 := bstep (se 2 (by rfl) ⟨265227, by rfl⟩ : syracuseStep 707273 = 530455) B530455
theorem B2542337 : Blo 467785 2542337 := bstep (se 2 (by rfl) ⟨953376, by rfl⟩ : syracuseStep 2542337 = 1906753) B1906753
theorem B707387 : Blo 467785 707387 := bstep (se 1 (by rfl) ⟨530540, by rfl⟩ : syracuseStep 707387 = 1061081) B1061081
theorem B707447 : Blo 467785 707447 := bstep (se 1 (by rfl) ⟨530585, by rfl⟩ : syracuseStep 707447 = 1061171) B1061171
theorem B1526663 : Blo 467785 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B707471 : Blo 467785 707471 := bstep (se 1 (by rfl) ⟨530603, by rfl⟩ : syracuseStep 707471 = 1061207) B1061207
theorem B707513 : Blo 467785 707513 := bstep (se 2 (by rfl) ⟨265317, by rfl⟩ : syracuseStep 707513 = 530635) B530635
theorem B707591 : Blo 467785 707591 := bstep (se 1 (by rfl) ⟨530693, by rfl⟩ : syracuseStep 707591 = 1061387) B1061387
theorem B1428509 : Blo 467785 1428509 := bstep (se 3 (by rfl) ⟨267845, by rfl⟩ : syracuseStep 1428509 = 535691) B535691
theorem B707627 : Blo 467785 707627 := bstep (se 1 (by rfl) ⟨530720, by rfl⟩ : syracuseStep 707627 = 1061441) B1061441
theorem B707657 : Blo 467785 707657 := bstep (se 2 (by rfl) ⟨265371, by rfl⟩ : syracuseStep 707657 = 530743) B530743
theorem B5131613 : Blo 467785 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B1002937 : Blo 467785 1002937 := bstep (se 2 (by rfl) ⟨376101, by rfl⟩ : syracuseStep 1002937 = 752203) B752203
theorem B2379293 : Blo 467785 2379293 := bstep (se 3 (by rfl) ⟨446117, by rfl⟩ : syracuseStep 2379293 = 892235) B892235
theorem B1789559 : Blo 467785 1789559 := bstep (se 1 (by rfl) ⟨1342169, by rfl⟩ : syracuseStep 1789559 = 2684339) B2684339
theorem B1265287 : Blo 467785 1265287 := bstep (se 1 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 1265287 = 1897931) B1897931
theorem B1003279 : Blo 467785 1003279 := bstep (se 1 (by rfl) ⟨752459, by rfl⟩ : syracuseStep 1003279 = 1504919) B1504919
theorem B2543375 : Blo 467785 2543375 := bstep (se 1 (by rfl) ⟨1907531, by rfl⟩ : syracuseStep 2543375 = 3815063) B3815063
theorem B2379779 : Blo 467785 2379779 := bstep (se 1 (by rfl) ⟨1784834, by rfl⟩ : syracuseStep 2379779 = 3569669) B3569669
theorem B7622857 : Blo 467785 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B3002683 : Blo 467785 3002683 := bstep (se 1 (by rfl) ⟨2252012, by rfl⟩ : syracuseStep 3002683 = 4504025) B4504025
theorem B1790531 : Blo 467785 1790531 := bstep (se 1 (by rfl) ⟨1342898, by rfl⟩ : syracuseStep 1790531 = 2685797) B2685797
theorem B1266263 : Blo 467785 1266263 := bstep (se 1 (by rfl) ⟨949697, by rfl⟩ : syracuseStep 1266263 = 1899395) B1899395
theorem B1004167 : Blo 467785 1004167 := bstep (se 1 (by rfl) ⟨753125, by rfl⟩ : syracuseStep 1004167 = 1506251) B1506251
theorem B2708239 : Blo 467785 2708239 := bstep (se 1 (by rfl) ⟨2031179, by rfl⟩ : syracuseStep 2708239 = 4062359) B4062359
theorem B2675591 : Blo 467785 2675591 := bstep (se 1 (by rfl) ⟨2006693, by rfl⟩ : syracuseStep 2675591 = 4013387) B4013387
theorem B2544587 : Blo 467785 2544587 := bstep (se 1 (by rfl) ⟨1908440, by rfl⟩ : syracuseStep 2544587 = 3816881) B3816881
theorem B1692701 : Blo 467785 1692701 := bstep (se 3 (by rfl) ⟨317381, by rfl⟩ : syracuseStep 1692701 = 634763) B634763
theorem B1266749 : Blo 467785 1266749 := bstep (se 3 (by rfl) ⟨237515, by rfl⟩ : syracuseStep 1266749 = 475031) B475031
theorem B1430843 : Blo 467785 1430843 := bstep (se 1 (by rfl) ⟨1073132, by rfl⟩ : syracuseStep 1430843 = 2146265) B2146265
theorem B3397049 : Blo 467785 3397049 := bstep (se 2 (by rfl) ⟨1273893, by rfl⟩ : syracuseStep 3397049 = 2547787) B2547787
theorem B2381399 : Blo 467785 2381399 := bstep (se 1 (by rfl) ⟨1786049, by rfl⟩ : syracuseStep 2381399 = 3572099) B3572099
theorem B2676797 : Blo 467785 2676797 := bstep (se 3 (by rfl) ⟨501899, by rfl⟩ : syracuseStep 2676797 = 1003799) B1003799
theorem B2381885 : Blo 467785 2381885 := bstep (se 3 (by rfl) ⟨446603, by rfl⟩ : syracuseStep 2381885 = 893207) B893207
theorem B1333547 : Blo 467785 1333547 := bstep (se 1 (by rfl) ⟨1000160, by rfl⟩ : syracuseStep 1333547 = 2000321) B2000321
theorem B1006123 : Blo 467785 1006123 := bstep (se 1 (by rfl) ⟨754592, by rfl⟩ : syracuseStep 1006123 = 1509185) B1509185
theorem B1334333 : Blo 467785 1334333 := bstep (se 3 (by rfl) ⟨250187, by rfl⟩ : syracuseStep 1334333 = 500375) B500375
theorem B1694807 : Blo 467785 1694807 := bstep (se 1 (by rfl) ⟨1271105, by rfl⟩ : syracuseStep 1694807 = 2542211) B2542211
theorem B1334663 : Blo 467785 1334663 := bstep (se 1 (by rfl) ⟨1000997, by rfl⟩ : syracuseStep 1334663 = 2001995) B2001995
theorem B3431825 : Blo 467785 3431825 := bstep (se 2 (by rfl) ⟨1286934, by rfl⟩ : syracuseStep 3431825 = 2573869) B2573869
theorem B2383667 : Blo 467785 2383667 := bstep (se 1 (by rfl) ⟨1787750, by rfl⟩ : syracuseStep 2383667 = 3575501) B3575501
theorem B2383991 : Blo 467785 2383991 := bstep (se 1 (by rfl) ⟨1787993, by rfl⟩ : syracuseStep 2383991 = 3575987) B3575987
theorem B2253089 : Blo 467785 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B3007043 : Blo 467785 3007043 := bstep (se 1 (by rfl) ⟨2255282, by rfl⟩ : syracuseStep 3007043 = 4510565) B4510565
theorem B4514561 : Blo 467785 4514561 := bstep (se 2 (by rfl) ⟨1692960, by rfl⟩ : syracuseStep 4514561 = 3385921) B3385921
theorem B2548739 : Blo 467785 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B2384963 : Blo 467785 2384963 := bstep (se 1 (by rfl) ⟨1788722, by rfl⟩ : syracuseStep 2384963 = 3577445) B3577445
theorem B1336439 : Blo 467785 1336439 := bstep (se 1 (by rfl) ⟨1002329, by rfl⟩ : syracuseStep 1336439 = 2004659) B2004659
theorem B4023533 : Blo 467785 4023533 := bstep (se 3 (by rfl) ⟨754412, by rfl⟩ : syracuseStep 4023533 = 1508825) B1508825
theorem B2385287 : Blo 467785 2385287 := bstep (se 1 (by rfl) ⟨1788965, by rfl⟩ : syracuseStep 2385287 = 3577931) B3577931
theorem B845327 : Blo 467785 845327 := bstep (se 1 (by rfl) ⟨633995, by rfl⟩ : syracuseStep 845327 = 1267991) B1267991
theorem B2450987 : Blo 467785 2450987 := bstep (se 1 (by rfl) ⟨1838240, by rfl⟩ : syracuseStep 2450987 = 3676481) B3676481
theorem B21784139 : Blo 467785 21784139 := bstep (se 1 (by rfl) ⟨16338104, by rfl⟩ : syracuseStep 21784139 = 32676209) B32676209
theorem B714511 : Blo 467785 714511 := bstep (se 1 (by rfl) ⟨535883, by rfl⟩ : syracuseStep 714511 = 1071767) B1071767
theorem B2549519 : Blo 467785 2549519 := bstep (se 1 (by rfl) ⟨1912139, by rfl⟩ : syracuseStep 2549519 = 3824279) B3824279
theorem B5334821 : Blo 467785 5334821 := bstep (se 4 (by rfl) ⟨500139, by rfl⟩ : syracuseStep 5334821 = 1000279) B1000279
theorem B1337431 : Blo 467785 1337431 := bstep (se 1 (by rfl) ⟨1003073, by rfl⟩ : syracuseStep 1337431 = 2006147) B2006147
theorem B10152053 : Blo 467785 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B714887 : Blo 467785 714887 := bstep (se 1 (by rfl) ⟨536165, by rfl⟩ : syracuseStep 714887 = 1072331) B1072331
theorem B1697993 : Blo 467785 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B2550295 : Blo 467785 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B2714797 : Blo 467785 2714797 := bstep (se 3 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 2714797 = 1018049) B1018049
theorem B2845925 : Blo 467785 2845925 := bstep (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) B533611
theorem B1338923 : Blo 467785 1338923 := bstep (se 1 (by rfl) ⟨1004192, by rfl⟩ : syracuseStep 1338923 = 2008385) B2008385
theorem B15200045 : Blo 467785 15200045 := bstep (se 3 (by rfl) ⟨2850008, by rfl⟩ : syracuseStep 15200045 = 5700017) B5700017
theorem B14479307 : Blo 467785 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B1503623 : Blo 467785 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B1340039 : Blo 467785 1340039 := bstep (se 1 (by rfl) ⟨1005029, by rfl⟩ : syracuseStep 1340039 = 2010059) B2010059
theorem B2585317 : Blo 467785 2585317 := bstep (se 4 (by rfl) ⟨242373, by rfl⟩ : syracuseStep 2585317 = 484747) B484747
theorem B1340221 : Blo 467785 1340221 := bstep (se 3 (by rfl) ⟨251291, by rfl⟩ : syracuseStep 1340221 = 502583) B502583
theorem B2847577 : Blo 467785 2847577 := bstep (se 2 (by rfl) ⟨1067841, by rfl⟩ : syracuseStep 2847577 = 2135683) B2135683
theorem B1340563 : Blo 467785 1340563 := bstep (se 1 (by rfl) ⟨1005422, by rfl⟩ : syracuseStep 1340563 = 2010845) B2010845
theorem B5371271 : Blo 467785 5371271 := bstep (se 1 (by rfl) ⟨4028453, by rfl⟩ : syracuseStep 5371271 = 8056907) B8056907
theorem B28865969 : Blo 467785 28865969 := bstep (se 2 (by rfl) ⟨10824738, by rfl⟩ : syracuseStep 28865969 = 21649477) B21649477
theorem B4027907 : Blo 467785 4027907 := bstep (se 1 (by rfl) ⟨3020930, by rfl⟩ : syracuseStep 4027907 = 6041861) B6041861
theorem B849811 : Blo 467785 849811 := bstep (se 1 (by rfl) ⟨637358, by rfl⟩ : syracuseStep 849811 = 1274717) B1274717
theorem B1341451 : Blo 467785 1341451 := bstep (se 1 (by rfl) ⟨1006088, by rfl⟩ : syracuseStep 1341451 = 2012177) B2012177
theorem B2849039 : Blo 467785 2849039 := bstep (se 1 (by rfl) ⟨2136779, by rfl⟩ : syracuseStep 2849039 = 4273559) B4273559
theorem B1603955 : Blo 467785 1603955 := bstep (se 1 (by rfl) ⟨1202966, by rfl⟩ : syracuseStep 1603955 = 2405933) B2405933
theorem B1341953 : Blo 467785 1341953 := bstep (se 2 (by rfl) ⟨503232, by rfl⟩ : syracuseStep 1341953 = 1006465) B1006465
theorem B2062967 : Blo 467785 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B1342295 : Blo 467785 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B1801169 : Blo 467785 1801169 := bstep (se 2 (by rfl) ⟨675438, by rfl⟩ : syracuseStep 1801169 = 1350877) B1350877
theorem B2259991 : Blo 467785 2259991 := bstep (se 1 (by rfl) ⟨1694993, by rfl⟩ : syracuseStep 2259991 = 3389987) B3389987
theorem B1506365 : Blo 467785 1506365 := bstep (se 3 (by rfl) ⟨282443, by rfl⟩ : syracuseStep 1506365 = 564887) B564887
theorem B1899911 : Blo 467785 1899911 := bstep (se 1 (by rfl) ⟨1424933, by rfl⟩ : syracuseStep 1899911 = 2849867) B2849867
theorem B7635059 : Blo 467785 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B1507481 : Blo 467785 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B13730123 : Blo 467785 13730123 := bstep (se 1 (by rfl) ⟨10297592, by rfl⟩ : syracuseStep 13730123 = 20595185) B20595185
theorem B52724195 : Blo 467785 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B10191419 : Blo 467785 10191419 := bstep (se 1 (by rfl) ⟨7643564, by rfl⟩ : syracuseStep 10191419 = 15287129) B15287129
theorem B754375 : Blo 467785 754375 := bstep (se 1 (by rfl) ⟨565781, by rfl⟩ : syracuseStep 754375 = 1131563) B1131563
theorem B3048619 : Blo 467785 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B1017593 : Blo 467785 1017593 := bstep (se 2 (by rfl) ⟨381597, by rfl⟩ : syracuseStep 1017593 = 763195) B763195
theorem B2983673 : Blo 467785 2983673 := bstep (se 2 (by rfl) ⟨1118877, by rfl⟩ : syracuseStep 2983673 = 2237755) B2237755
theorem B6031199 : Blo 467785 6031199 := bstep (se 1 (by rfl) ⟨4523399, by rfl⟩ : syracuseStep 6031199 = 9046799) B9046799
theorem B1017775 : Blo 467785 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B952339 : Blo 467785 952339 := bstep (se 1 (by rfl) ⟨714254, by rfl⟩ : syracuseStep 952339 = 1428509) B1428509
theorem B526459 : Blo 467785 526459 := bstep (se 1 (by rfl) ⟨394844, by rfl⟩ : syracuseStep 526459 = 789689) B789689
theorem B526927 : Blo 467785 526927 := bstep (se 1 (by rfl) ⟨395195, by rfl⟩ : syracuseStep 526927 = 790391) B790391
theorem B592859 : Blo 467785 592859 := bstep (se 1 (by rfl) ⟨444644, by rfl⟩ : syracuseStep 592859 = 889289) B889289
theorem B527323 : Blo 467785 527323 := bstep (se 1 (by rfl) ⟨395492, by rfl⟩ : syracuseStep 527323 = 790985) B790985
theorem B3214583 : Blo 467785 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B527791 : Blo 467785 527791 := bstep (se 1 (by rfl) ⟨395843, by rfl⟩ : syracuseStep 527791 = 791687) B791687
theorem B593335 : Blo 467785 593335 := bstep (se 1 (by rfl) ⟨445001, by rfl⟩ : syracuseStep 593335 = 890003) B890003
theorem B789979 : Blo 467785 789979 := bstep (se 1 (by rfl) ⟨592484, by rfl⟩ : syracuseStep 789979 = 1184969) B1184969
theorem B2264699 : Blo 467785 2264699 := bstep (se 1 (by rfl) ⟨1698524, by rfl⟩ : syracuseStep 2264699 = 3397049) B3397049
theorem B528223 : Blo 467785 528223 := bstep (se 1 (by rfl) ⟨396167, by rfl⟩ : syracuseStep 528223 = 792335) B792335
theorem B1052603 : Blo 467785 1052603 := bstep (se 1 (by rfl) ⟨789452, by rfl⟩ : syracuseStep 1052603 = 1578905) B1578905
theorem B1052729 : Blo 467785 1052729 := bstep (se 2 (by rfl) ⟨394773, by rfl⟩ : syracuseStep 1052729 = 789547) B789547
theorem B790607 : Blo 467785 790607 := bstep (se 1 (by rfl) ⟨592955, by rfl⟩ : syracuseStep 790607 = 1185911) B1185911
theorem B889031 : Blo 467785 889031 := bstep (se 1 (by rfl) ⟨666773, by rfl⟩ : syracuseStep 889031 = 1333547) B1333547
theorem B528583 : Blo 467785 528583 := bstep (se 1 (by rfl) ⟨396437, by rfl⟩ : syracuseStep 528583 = 792875) B792875
theorem B1184129 : Blo 467785 1184129 := bstep (se 2 (by rfl) ⟨444048, by rfl⟩ : syracuseStep 1184129 = 888097) B888097
theorem B1053071 : Blo 467785 1053071 := bstep (se 1 (by rfl) ⟨789803, by rfl⟩ : syracuseStep 1053071 = 1579607) B1579607
theorem B594631 : Blo 467785 594631 := bstep (se 1 (by rfl) ⟨445973, by rfl⟩ : syracuseStep 594631 = 891947) B891947
theorem B1053395 : Blo 467785 1053395 := bstep (se 1 (by rfl) ⟨790046, by rfl⟩ : syracuseStep 1053395 = 1580093) B1580093
theorem B889555 : Blo 467785 889555 := bstep (se 1 (by rfl) ⟨667166, by rfl⟩ : syracuseStep 889555 = 1334333) B1334333
theorem B889775 : Blo 467785 889775 := bstep (se 1 (by rfl) ⟨667331, by rfl⟩ : syracuseStep 889775 = 1334663) B1334663
theorem B791471 : Blo 467785 791471 := bstep (se 1 (by rfl) ⟨593603, by rfl⟩ : syracuseStep 791471 = 1187207) B1187207
theorem B529447 : Blo 467785 529447 := bstep (se 1 (by rfl) ⟨397085, by rfl⟩ : syracuseStep 529447 = 794171) B794171
theorem B1184939 : Blo 467785 1184939 := bstep (se 1 (by rfl) ⟨888704, by rfl⟩ : syracuseStep 1184939 = 1777409) B1777409
theorem B9049259 : Blo 467785 9049259 := bstep (se 1 (by rfl) ⟨6786944, by rfl⟩ : syracuseStep 9049259 = 13573889) B13573889
theorem B890185 : Blo 467785 890185 := bstep (se 2 (by rfl) ⟨333819, by rfl⟩ : syracuseStep 890185 = 667639) B667639
theorem B791903 : Blo 467785 791903 := bstep (se 1 (by rfl) ⟨593927, by rfl⟩ : syracuseStep 791903 = 1187855) B1187855
theorem B7607753 : Blo 467785 7607753 := bstep (se 2 (by rfl) ⟨2852907, by rfl⟩ : syracuseStep 7607753 = 5705815) B5705815
theorem B3806759 : Blo 467785 3806759 := bstep (se 1 (by rfl) ⟨2855069, by rfl⟩ : syracuseStep 3806759 = 5710139) B5710139
theorem B10163809 : Blo 467785 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B1054331 : Blo 467785 1054331 := bstep (se 1 (by rfl) ⟨790748, by rfl⟩ : syracuseStep 1054331 = 1581497) B1581497
theorem B2004695 : Blo 467785 2004695 := bstep (se 1 (by rfl) ⟨1503521, by rfl⟩ : syracuseStep 2004695 = 3007043) B3007043
theorem B4003577 : Blo 467785 4003577 := bstep (se 2 (by rfl) ⟨1501341, by rfl⟩ : syracuseStep 4003577 = 3002683) B3002683
theorem B1054457 : Blo 467785 1054457 := bstep (se 2 (by rfl) ⟨395421, by rfl⟩ : syracuseStep 1054457 = 790843) B790843
theorem B792463 : Blo 467785 792463 := bstep (se 1 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 792463 = 1188695) B1188695
theorem B1185799 : Blo 467785 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B1054727 : Blo 467785 1054727 := bstep (se 1 (by rfl) ⟨791045, by rfl⟩ : syracuseStep 1054727 = 1582091) B1582091
theorem B1054799 : Blo 467785 1054799 := bstep (se 1 (by rfl) ⟨791099, by rfl⟩ : syracuseStep 1054799 = 1582199) B1582199
theorem B3447089 : Blo 467785 3447089 := bstep (se 2 (by rfl) ⟨1292658, by rfl⟩ : syracuseStep 3447089 = 2585317) B2585317
theorem B3610985 : Blo 467785 3610985 := bstep (se 2 (by rfl) ⟨1354119, by rfl⟩ : syracuseStep 3610985 = 2708239) B2708239
theorem B14522759 : Blo 467785 14522759 := bstep (se 1 (by rfl) ⟨10892069, by rfl⟩ : syracuseStep 14522759 = 21784139) B21784139
theorem B1055195 : Blo 467785 1055195 := bstep (se 1 (by rfl) ⟨791396, by rfl⟩ : syracuseStep 1055195 = 1582793) B1582793
theorem B1579553 : Blo 467785 1579553 := bstep (se 2 (by rfl) ⟨592332, by rfl⟩ : syracuseStep 1579553 = 1184665) B1184665
theorem B793145 : Blo 467785 793145 := bstep (se 2 (by rfl) ⟨297429, by rfl⟩ : syracuseStep 793145 = 594859) B594859
theorem B1186427 : Blo 467785 1186427 := bstep (se 1 (by rfl) ⟨889820, by rfl⟩ : syracuseStep 1186427 = 1779641) B1779641
theorem B1579769 : Blo 467785 1579769 := bstep (se 2 (by rfl) ⟨592413, by rfl⟩ : syracuseStep 1579769 = 1184827) B1184827
theorem B1776451 : Blo 467785 1776451 := bstep (se 1 (by rfl) ⟨1332338, by rfl⟩ : syracuseStep 1776451 = 2664677) B2664677
theorem B1186721 : Blo 467785 1186721 := bstep (se 2 (by rfl) ⟨445020, by rfl⟩ : syracuseStep 1186721 = 890041) B890041
theorem B1055663 : Blo 467785 1055663 := bstep (se 1 (by rfl) ⟨791747, by rfl⟩ : syracuseStep 1055663 = 1583495) B1583495
theorem B3218359 : Blo 467785 3218359 := bstep (se 1 (by rfl) ⟨2413769, by rfl⟩ : syracuseStep 3218359 = 4827539) B4827539
theorem B2530277 : Blo 467785 2530277 := bstep (se 4 (by rfl) ⟨237213, by rfl⟩ : syracuseStep 2530277 = 474427) B474427
theorem B1580039 : Blo 467785 1580039 := bstep (se 1 (by rfl) ⟨1185029, by rfl⟩ : syracuseStep 1580039 = 2370059) B2370059
theorem B597071 : Blo 467785 597071 := bstep (se 1 (by rfl) ⟨447803, by rfl⟩ : syracuseStep 597071 = 895607) B895607
theorem B1776755 : Blo 467785 1776755 := bstep (se 1 (by rfl) ⟨1332566, by rfl⟩ : syracuseStep 1776755 = 2665133) B2665133
theorem B1580147 : Blo 467785 1580147 := bstep (se 1 (by rfl) ⟨1185110, by rfl⟩ : syracuseStep 1580147 = 2370221) B2370221
theorem B1055915 : Blo 467785 1055915 := bstep (se 1 (by rfl) ⟨791936, by rfl⟩ : syracuseStep 1055915 = 1583873) B1583873
theorem B793847 : Blo 467785 793847 := bstep (se 1 (by rfl) ⟨595385, by rfl⟩ : syracuseStep 793847 = 1190771) B1190771
theorem B4300121 : Blo 467785 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B1580417 : Blo 467785 1580417 := bstep (se 2 (by rfl) ⟨592656, by rfl⟩ : syracuseStep 1580417 = 1185313) B1185313
theorem B1777211 : Blo 467785 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B794191 : Blo 467785 794191 := bstep (se 1 (by rfl) ⟨595643, by rfl⟩ : syracuseStep 794191 = 1191287) B1191287
theorem B1056455 : Blo 467785 1056455 := bstep (se 1 (by rfl) ⟨792341, by rfl⟩ : syracuseStep 1056455 = 1584683) B1584683
theorem B892615 : Blo 467785 892615 := bstep (se 1 (by rfl) ⟨669461, by rfl⟩ : syracuseStep 892615 = 1338923) B1338923
theorem B794441 : Blo 467785 794441 := bstep (se 2 (by rfl) ⟨297915, by rfl⟩ : syracuseStep 794441 = 595831) B595831
theorem B10133363 : Blo 467785 10133363 := bstep (se 1 (by rfl) ⟨7600022, by rfl⟩ : syracuseStep 10133363 = 15200045) B15200045
theorem B1581227 : Blo 467785 1581227 := bstep (se 1 (by rfl) ⟨1185920, by rfl⟩ : syracuseStep 1581227 = 2371841) B2371841
theorem B893177 : Blo 467785 893177 := bstep (se 2 (by rfl) ⟨334941, by rfl⟩ : syracuseStep 893177 = 669883) B669883
theorem B794873 : Blo 467785 794873 := bstep (se 2 (by rfl) ⟨298077, by rfl⟩ : syracuseStep 794873 = 596155) B596155
theorem B893359 : Blo 467785 893359 := bstep (se 1 (by rfl) ⟨670019, by rfl⟩ : syracuseStep 893359 = 1340039) B1340039
theorem B795055 : Blo 467785 795055 := bstep (se 1 (by rfl) ⟨596291, by rfl⟩ : syracuseStep 795055 = 1192583) B1192583
theorem B795143 : Blo 467785 795143 := bstep (se 1 (by rfl) ⟨596357, by rfl⟩ : syracuseStep 795143 = 1192715) B1192715
theorem B25960981 : Blo 467785 25960981 := bstep (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) B1216921
theorem B1188391 : Blo 467785 1188391 := bstep (se 1 (by rfl) ⟨891293, by rfl⟩ : syracuseStep 1188391 = 1782587) B1782587
theorem B1057319 : Blo 467785 1057319 := bstep (se 1 (by rfl) ⟨792989, by rfl⟩ : syracuseStep 1057319 = 1585979) B1585979
theorem B1581767 : Blo 467785 1581767 := bstep (se 1 (by rfl) ⟨1186325, by rfl⟩ : syracuseStep 1581767 = 2372651) B2372651
theorem B467791 : Blo 467785 467791 := bstep (se 1 (by rfl) ⟨350843, by rfl⟩ : syracuseStep 467791 = 701687) B701687
theorem B467807 : Blo 467785 467807 := bstep (se 1 (by rfl) ⟨350855, by rfl⟩ : syracuseStep 467807 = 701711) B701711
theorem B795487 : Blo 467785 795487 := bstep (se 1 (by rfl) ⟨596615, by rfl⟩ : syracuseStep 795487 = 1193231) B1193231
theorem B1188715 : Blo 467785 1188715 := bstep (se 1 (by rfl) ⟨891536, by rfl⟩ : syracuseStep 1188715 = 1783073) B1783073
theorem B1057643 : Blo 467785 1057643 := bstep (se 1 (by rfl) ⟨793232, by rfl⟩ : syracuseStep 1057643 = 1586465) B1586465
theorem B467835 : Blo 467785 467835 := bstep (se 1 (by rfl) ⟨350876, by rfl⟩ : syracuseStep 467835 = 701753) B701753
theorem B1057697 : Blo 467785 1057697 := bstep (se 2 (by rfl) ⟨396636, by rfl⟩ : syracuseStep 1057697 = 793273) B793273
theorem B467887 : Blo 467785 467887 := bstep (se 1 (by rfl) ⟨350915, by rfl⟩ : syracuseStep 467887 = 701831) B701831
theorem B3580847 : Blo 467785 3580847 := bstep (se 1 (by rfl) ⟨2685635, by rfl⟩ : syracuseStep 3580847 = 5371271) B5371271
theorem B2368439 : Blo 467785 2368439 := bstep (se 1 (by rfl) ⟨1776329, by rfl⟩ : syracuseStep 2368439 = 3552659) B3552659
theorem B795575 : Blo 467785 795575 := bstep (se 1 (by rfl) ⟨596681, by rfl⟩ : syracuseStep 795575 = 1193363) B1193363
theorem B467911 : Blo 467785 467911 := bstep (se 1 (by rfl) ⟨350933, by rfl⟩ : syracuseStep 467911 = 701867) B701867
theorem B19243979 : Blo 467785 19243979 := bstep (se 1 (by rfl) ⟨14432984, by rfl⟩ : syracuseStep 19243979 = 28865969) B28865969
theorem B467931 : Blo 467785 467931 := bstep (se 1 (by rfl) ⟨350948, by rfl⟩ : syracuseStep 467931 = 701897) B701897
theorem B468007 : Blo 467785 468007 := bstep (se 1 (by rfl) ⟨351005, by rfl⟩ : syracuseStep 468007 = 702011) B702011
theorem B5710915 : Blo 467785 5710915 := bstep (se 1 (by rfl) ⟨4283186, by rfl⟩ : syracuseStep 5710915 = 8566373) B8566373
theorem B468047 : Blo 467785 468047 := bstep (se 1 (by rfl) ⟨351035, by rfl⟩ : syracuseStep 468047 = 702071) B702071
theorem B468063 : Blo 467785 468063 := bstep (se 1 (by rfl) ⟨351047, by rfl⟩ : syracuseStep 468063 = 702095) B702095
theorem B468091 : Blo 467785 468091 := bstep (se 1 (by rfl) ⟨351068, by rfl⟩ : syracuseStep 468091 = 702137) B702137
theorem B468143 : Blo 467785 468143 := bstep (se 1 (by rfl) ⟨351107, by rfl⟩ : syracuseStep 468143 = 702215) B702215
theorem B468167 : Blo 467785 468167 := bstep (se 1 (by rfl) ⟨351125, by rfl⟩ : syracuseStep 468167 = 702251) B702251
theorem B468187 : Blo 467785 468187 := bstep (se 1 (by rfl) ⟨351140, by rfl⟩ : syracuseStep 468187 = 702281) B702281
theorem B1058039 : Blo 467785 1058039 := bstep (se 1 (by rfl) ⟨793529, by rfl⟩ : syracuseStep 1058039 = 1587059) B1587059
theorem B468263 : Blo 467785 468263 := bstep (se 1 (by rfl) ⟨351197, by rfl⟩ : syracuseStep 468263 = 702395) B702395
theorem B468303 : Blo 467785 468303 := bstep (se 1 (by rfl) ⟨351227, by rfl⟩ : syracuseStep 468303 = 702455) B702455
theorem B468319 : Blo 467785 468319 := bstep (se 1 (by rfl) ⟨351239, by rfl⟩ : syracuseStep 468319 = 702479) B702479
theorem B468347 : Blo 467785 468347 := bstep (se 1 (by rfl) ⟨351260, by rfl⟩ : syracuseStep 468347 = 702521) B702521
theorem B3810725 : Blo 467785 3810725 := bstep (se 4 (by rfl) ⟨357255, by rfl⟩ : syracuseStep 3810725 = 714511) B714511
theorem B468399 : Blo 467785 468399 := bstep (se 1 (by rfl) ⟨351299, by rfl⟩ : syracuseStep 468399 = 702599) B702599
theorem B468423 : Blo 467785 468423 := bstep (se 1 (by rfl) ⟨351317, by rfl⟩ : syracuseStep 468423 = 702635) B702635
theorem B468443 : Blo 467785 468443 := bstep (se 1 (by rfl) ⟨351332, by rfl⟩ : syracuseStep 468443 = 702665) B702665
theorem B1189363 : Blo 467785 1189363 := bstep (se 1 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 1189363 = 1784045) B1784045
theorem B468519 : Blo 467785 468519 := bstep (se 1 (by rfl) ⟨351389, by rfl⟩ : syracuseStep 468519 = 702779) B702779
theorem B1582631 : Blo 467785 1582631 := bstep (se 1 (by rfl) ⟨1186973, by rfl⟩ : syracuseStep 1582631 = 2373947) B2373947
theorem B468559 : Blo 467785 468559 := bstep (se 1 (by rfl) ⟨351419, by rfl⟩ : syracuseStep 468559 = 702839) B702839
theorem B468575 : Blo 467785 468575 := bstep (se 1 (by rfl) ⟨351431, by rfl⟩ : syracuseStep 468575 = 702863) B702863
theorem B468603 : Blo 467785 468603 := bstep (se 1 (by rfl) ⟨351452, by rfl⟩ : syracuseStep 468603 = 702905) B702905
theorem B1582739 : Blo 467785 1582739 := bstep (se 1 (by rfl) ⟨1187054, by rfl⟩ : syracuseStep 1582739 = 2374109) B2374109
theorem B4531859 : Blo 467785 4531859 := bstep (se 1 (by rfl) ⟨3398894, by rfl⟩ : syracuseStep 4531859 = 6797789) B6797789
theorem B894635 : Blo 467785 894635 := bstep (se 1 (by rfl) ⟨670976, by rfl⟩ : syracuseStep 894635 = 1341953) B1341953
theorem B468655 : Blo 467785 468655 := bstep (se 1 (by rfl) ⟨351491, by rfl⟩ : syracuseStep 468655 = 702983) B702983
theorem B468679 : Blo 467785 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B468699 : Blo 467785 468699 := bstep (se 1 (by rfl) ⟨351524, by rfl⟩ : syracuseStep 468699 = 703049) B703049
theorem B468775 : Blo 467785 468775 := bstep (se 1 (by rfl) ⟨351581, by rfl⟩ : syracuseStep 468775 = 703163) B703163
theorem B1058633 : Blo 467785 1058633 := bstep (se 2 (by rfl) ⟨396987, by rfl⟩ : syracuseStep 1058633 = 793975) B793975
theorem B468815 : Blo 467785 468815 := bstep (se 1 (by rfl) ⟨351611, by rfl⟩ : syracuseStep 468815 = 703223) B703223
theorem B468831 : Blo 467785 468831 := bstep (se 1 (by rfl) ⟨351623, by rfl⟩ : syracuseStep 468831 = 703247) B703247
theorem B1582955 : Blo 467785 1582955 := bstep (se 1 (by rfl) ⟨1187216, by rfl⟩ : syracuseStep 1582955 = 2374433) B2374433
theorem B468859 : Blo 467785 468859 := bstep (se 1 (by rfl) ⟨351644, by rfl⟩ : syracuseStep 468859 = 703289) B703289
theorem B894863 : Blo 467785 894863 := bstep (se 1 (by rfl) ⟨671147, by rfl⟩ : syracuseStep 894863 = 1342295) B1342295
theorem B1583009 : Blo 467785 1583009 := bstep (se 2 (by rfl) ⟨593628, by rfl⟩ : syracuseStep 1583009 = 1187257) B1187257
theorem B468911 : Blo 467785 468911 := bstep (se 1 (by rfl) ⟨351683, by rfl⟩ : syracuseStep 468911 = 703367) B703367
theorem B468935 : Blo 467785 468935 := bstep (se 1 (by rfl) ⟨351701, by rfl⟩ : syracuseStep 468935 = 703403) B703403
theorem B468955 : Blo 467785 468955 := bstep (se 1 (by rfl) ⟨351716, by rfl⟩ : syracuseStep 468955 = 703433) B703433
theorem B469031 : Blo 467785 469031 := bstep (se 1 (by rfl) ⟨351773, by rfl⟩ : syracuseStep 469031 = 703547) B703547
theorem B469071 : Blo 467785 469071 := bstep (se 1 (by rfl) ⟨351803, by rfl⟩ : syracuseStep 469071 = 703607) B703607
theorem B469087 : Blo 467785 469087 := bstep (se 1 (by rfl) ⟨351815, by rfl⟩ : syracuseStep 469087 = 703631) B703631
theorem B469115 : Blo 467785 469115 := bstep (se 1 (by rfl) ⟨351836, by rfl⟩ : syracuseStep 469115 = 703673) B703673
theorem B469167 : Blo 467785 469167 := bstep (se 1 (by rfl) ⟨351875, by rfl⟩ : syracuseStep 469167 = 703751) B703751
theorem B469191 : Blo 467785 469191 := bstep (se 1 (by rfl) ⟨351893, by rfl⟩ : syracuseStep 469191 = 703787) B703787
theorem B469211 : Blo 467785 469211 := bstep (se 1 (by rfl) ⟨351908, by rfl⟩ : syracuseStep 469211 = 703817) B703817
theorem B469287 : Blo 467785 469287 := bstep (se 1 (by rfl) ⟨351965, by rfl⟩ : syracuseStep 469287 = 703931) B703931
theorem B469327 : Blo 467785 469327 := bstep (se 1 (by rfl) ⟨351995, by rfl⟩ : syracuseStep 469327 = 703991) B703991
theorem B469343 : Blo 467785 469343 := bstep (se 1 (by rfl) ⟨352007, by rfl⟩ : syracuseStep 469343 = 704015) B704015
theorem B2369897 : Blo 467785 2369897 := bstep (se 2 (by rfl) ⟨888711, by rfl⟩ : syracuseStep 2369897 = 1777423) B1777423
theorem B469371 : Blo 467785 469371 := bstep (se 1 (by rfl) ⟨352028, by rfl⟩ : syracuseStep 469371 = 704057) B704057
theorem B469423 : Blo 467785 469423 := bstep (se 1 (by rfl) ⟨352067, by rfl⟩ : syracuseStep 469423 = 704135) B704135
theorem B469447 : Blo 467785 469447 := bstep (se 1 (by rfl) ⟨352085, by rfl⟩ : syracuseStep 469447 = 704171) B704171
theorem B469467 : Blo 467785 469467 := bstep (se 1 (by rfl) ⟨352100, by rfl⟩ : syracuseStep 469467 = 704201) B704201
theorem B1583603 : Blo 467785 1583603 := bstep (se 1 (by rfl) ⟨1187702, by rfl⟩ : syracuseStep 1583603 = 2375405) B2375405
theorem B469543 : Blo 467785 469543 := bstep (se 1 (by rfl) ⟨352157, by rfl⟩ : syracuseStep 469543 = 704315) B704315
theorem B469583 : Blo 467785 469583 := bstep (se 1 (by rfl) ⟨352187, by rfl⟩ : syracuseStep 469583 = 704375) B704375
theorem B469599 : Blo 467785 469599 := bstep (se 1 (by rfl) ⟨352199, by rfl⟩ : syracuseStep 469599 = 704399) B704399
theorem B1190497 : Blo 467785 1190497 := bstep (se 2 (by rfl) ⟨446436, by rfl⟩ : syracuseStep 1190497 = 892873) B892873
theorem B1059425 : Blo 467785 1059425 := bstep (se 2 (by rfl) ⟨397284, by rfl⟩ : syracuseStep 1059425 = 794569) B794569
theorem B469627 : Blo 467785 469627 := bstep (se 1 (by rfl) ⟨352220, by rfl⟩ : syracuseStep 469627 = 704441) B704441
theorem B469679 : Blo 467785 469679 := bstep (se 1 (by rfl) ⟨352259, by rfl⟩ : syracuseStep 469679 = 704519) B704519
theorem B2009785 : Blo 467785 2009785 := bstep (se 2 (by rfl) ⟨753669, by rfl⟩ : syracuseStep 2009785 = 1507339) B1507339
theorem B469703 : Blo 467785 469703 := bstep (se 1 (by rfl) ⟨352277, by rfl⟩ : syracuseStep 469703 = 704555) B704555
theorem B469723 : Blo 467785 469723 := bstep (se 1 (by rfl) ⟨352292, by rfl⟩ : syracuseStep 469723 = 704585) B704585
theorem B469799 : Blo 467785 469799 := bstep (se 1 (by rfl) ⟨352349, by rfl⟩ : syracuseStep 469799 = 704699) B704699
theorem B469839 : Blo 467785 469839 := bstep (se 1 (by rfl) ⟨352379, by rfl⟩ : syracuseStep 469839 = 704759) B704759
theorem B469855 : Blo 467785 469855 := bstep (se 1 (by rfl) ⟨352391, by rfl⟩ : syracuseStep 469855 = 704783) B704783
theorem B469883 : Blo 467785 469883 := bstep (se 1 (by rfl) ⟨352412, by rfl⟩ : syracuseStep 469883 = 704825) B704825
theorem B469935 : Blo 467785 469935 := bstep (se 1 (by rfl) ⟨352451, by rfl⟩ : syracuseStep 469935 = 704903) B704903
theorem B1059767 : Blo 467785 1059767 := bstep (se 1 (by rfl) ⟨794825, by rfl⟩ : syracuseStep 1059767 = 1589651) B1589651
theorem B469959 : Blo 467785 469959 := bstep (se 1 (by rfl) ⟨352469, by rfl⟩ : syracuseStep 469959 = 704939) B704939
theorem B469979 : Blo 467785 469979 := bstep (se 1 (by rfl) ⟨352484, by rfl⟩ : syracuseStep 469979 = 704969) B704969
theorem B1911815 : Blo 467785 1911815 := bstep (se 1 (by rfl) ⟨1433861, by rfl⟩ : syracuseStep 1911815 = 2867723) B2867723
theorem B1584143 : Blo 467785 1584143 := bstep (se 1 (by rfl) ⟨1188107, by rfl⟩ : syracuseStep 1584143 = 2376215) B2376215
theorem B535591 : Blo 467785 535591 := bstep (se 1 (by rfl) ⟨401693, by rfl⟩ : syracuseStep 535591 = 803387) B803387
theorem B470055 : Blo 467785 470055 := bstep (se 1 (by rfl) ⟨352541, by rfl⟩ : syracuseStep 470055 = 705083) B705083
theorem B470095 : Blo 467785 470095 := bstep (se 1 (by rfl) ⟨352571, by rfl⟩ : syracuseStep 470095 = 705143) B705143
theorem B470111 : Blo 467785 470111 := bstep (se 1 (by rfl) ⟨352583, by rfl⟩ : syracuseStep 470111 = 705167) B705167
theorem B470139 : Blo 467785 470139 := bstep (se 1 (by rfl) ⟨352604, by rfl⟩ : syracuseStep 470139 = 705209) B705209
theorem B470191 : Blo 467785 470191 := bstep (se 1 (by rfl) ⟨352643, by rfl⟩ : syracuseStep 470191 = 705287) B705287
theorem B470215 : Blo 467785 470215 := bstep (se 1 (by rfl) ⟨352661, by rfl⟩ : syracuseStep 470215 = 705323) B705323
theorem B470235 : Blo 467785 470235 := bstep (se 1 (by rfl) ⟨352676, by rfl⟩ : syracuseStep 470235 = 705353) B705353
theorem B470311 : Blo 467785 470311 := bstep (se 1 (by rfl) ⟨352733, by rfl⟩ : syracuseStep 470311 = 705467) B705467
theorem B470351 : Blo 467785 470351 := bstep (se 1 (by rfl) ⟨352763, by rfl⟩ : syracuseStep 470351 = 705527) B705527
theorem B470367 : Blo 467785 470367 := bstep (se 1 (by rfl) ⟨352775, by rfl⟩ : syracuseStep 470367 = 705551) B705551
theorem B470395 : Blo 467785 470395 := bstep (se 1 (by rfl) ⟨352796, by rfl⟩ : syracuseStep 470395 = 705593) B705593
theorem B470447 : Blo 467785 470447 := bstep (se 1 (by rfl) ⟨352835, by rfl⟩ : syracuseStep 470447 = 705671) B705671
theorem B503215 : Blo 467785 503215 := bstep (se 1 (by rfl) ⟨377411, by rfl⟩ : syracuseStep 503215 = 754823) B754823
theorem B470471 : Blo 467785 470471 := bstep (se 1 (by rfl) ⟨352853, by rfl⟩ : syracuseStep 470471 = 705707) B705707
theorem B3386843 : Blo 467785 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B470491 : Blo 467785 470491 := bstep (se 1 (by rfl) ⟨352868, by rfl⟩ : syracuseStep 470491 = 705737) B705737
theorem B1060361 : Blo 467785 1060361 := bstep (se 2 (by rfl) ⟨397635, by rfl⟩ : syracuseStep 1060361 = 795271) B795271
theorem B1191449 : Blo 467785 1191449 := bstep (se 2 (by rfl) ⟨446793, by rfl⟩ : syracuseStep 1191449 = 893587) B893587
theorem B470567 : Blo 467785 470567 := bstep (se 1 (by rfl) ⟨352925, by rfl⟩ : syracuseStep 470567 = 705851) B705851
theorem B503335 : Blo 467785 503335 := bstep (se 1 (by rfl) ⟨377501, by rfl⟩ : syracuseStep 503335 = 755003) B755003
theorem B470607 : Blo 467785 470607 := bstep (se 1 (by rfl) ⟨352955, by rfl⟩ : syracuseStep 470607 = 705911) B705911
theorem B470623 : Blo 467785 470623 := bstep (se 1 (by rfl) ⟨352967, by rfl⟩ : syracuseStep 470623 = 705935) B705935
theorem B1584737 : Blo 467785 1584737 := bstep (se 2 (by rfl) ⟨594276, by rfl⟩ : syracuseStep 1584737 = 1188553) B1188553
theorem B470651 : Blo 467785 470651 := bstep (se 1 (by rfl) ⟨352988, by rfl⟩ : syracuseStep 470651 = 705977) B705977
theorem B470703 : Blo 467785 470703 := bstep (se 1 (by rfl) ⟨353027, by rfl⟩ : syracuseStep 470703 = 706055) B706055
theorem B4009661 : Blo 467785 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B470727 : Blo 467785 470727 := bstep (se 1 (by rfl) ⟨353045, by rfl⟩ : syracuseStep 470727 = 706091) B706091
theorem B470747 : Blo 467785 470747 := bstep (se 1 (by rfl) ⟨353060, by rfl⟩ : syracuseStep 470747 = 706121) B706121
theorem B470823 : Blo 467785 470823 := bstep (se 1 (by rfl) ⟨353117, by rfl⟩ : syracuseStep 470823 = 706235) B706235
theorem B470863 : Blo 467785 470863 := bstep (se 1 (by rfl) ⟨353147, by rfl⟩ : syracuseStep 470863 = 706295) B706295
theorem B470879 : Blo 467785 470879 := bstep (se 1 (by rfl) ⟨353159, by rfl⟩ : syracuseStep 470879 = 706319) B706319
theorem B1060703 : Blo 467785 1060703 := bstep (se 1 (by rfl) ⟨795527, by rfl⟩ : syracuseStep 1060703 = 1591055) B1591055
theorem B470907 : Blo 467785 470907 := bstep (se 1 (by rfl) ⟨353180, by rfl⟩ : syracuseStep 470907 = 706361) B706361
theorem B470959 : Blo 467785 470959 := bstep (se 1 (by rfl) ⟨353219, by rfl⟩ : syracuseStep 470959 = 706439) B706439
theorem B470983 : Blo 467785 470983 := bstep (se 1 (by rfl) ⟨353237, by rfl⟩ : syracuseStep 470983 = 706475) B706475
theorem B471003 : Blo 467785 471003 := bstep (se 1 (by rfl) ⟨353252, by rfl⟩ : syracuseStep 471003 = 706505) B706505
theorem B1191955 : Blo 467785 1191955 := bstep (se 1 (by rfl) ⟨893966, by rfl⟩ : syracuseStep 1191955 = 1787933) B1787933
theorem B1060883 : Blo 467785 1060883 := bstep (se 1 (by rfl) ⟨795662, by rfl⟩ : syracuseStep 1060883 = 1591325) B1591325
theorem B471079 : Blo 467785 471079 := bstep (se 1 (by rfl) ⟨353309, by rfl⟩ : syracuseStep 471079 = 706619) B706619
theorem B471119 : Blo 467785 471119 := bstep (se 1 (by rfl) ⟨353339, by rfl⟩ : syracuseStep 471119 = 706679) B706679
theorem B471135 : Blo 467785 471135 := bstep (se 1 (by rfl) ⟨353351, by rfl⟩ : syracuseStep 471135 = 706703) B706703
theorem B2240627 : Blo 467785 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B471163 : Blo 467785 471163 := bstep (se 1 (by rfl) ⟨353372, by rfl⟩ : syracuseStep 471163 = 706745) B706745
theorem B471215 : Blo 467785 471215 := bstep (se 1 (by rfl) ⟨353411, by rfl⟩ : syracuseStep 471215 = 706823) B706823
theorem B471239 : Blo 467785 471239 := bstep (se 1 (by rfl) ⟨353429, by rfl⟩ : syracuseStep 471239 = 706859) B706859
theorem B471259 : Blo 467785 471259 := bstep (se 1 (by rfl) ⟨353444, by rfl⟩ : syracuseStep 471259 = 706889) B706889
theorem B471335 : Blo 467785 471335 := bstep (se 1 (by rfl) ⟨353501, by rfl⟩ : syracuseStep 471335 = 707003) B707003
theorem B471375 : Blo 467785 471375 := bstep (se 1 (by rfl) ⟨353531, by rfl⟩ : syracuseStep 471375 = 707063) B707063
theorem B471391 : Blo 467785 471391 := bstep (se 1 (by rfl) ⟨353543, by rfl⟩ : syracuseStep 471391 = 707087) B707087
theorem B1061225 : Blo 467785 1061225 := bstep (se 2 (by rfl) ⟨397959, by rfl⟩ : syracuseStep 1061225 = 795919) B795919
theorem B471419 : Blo 467785 471419 := bstep (se 1 (by rfl) ⟨353564, by rfl⟩ : syracuseStep 471419 = 707129) B707129
theorem B471471 : Blo 467785 471471 := bstep (se 1 (by rfl) ⟨353603, by rfl⟩ : syracuseStep 471471 = 707207) B707207
theorem B471495 : Blo 467785 471495 := bstep (se 1 (by rfl) ⟨353621, by rfl⟩ : syracuseStep 471495 = 707243) B707243
theorem B471515 : Blo 467785 471515 := bstep (se 1 (by rfl) ⟨353636, by rfl⟩ : syracuseStep 471515 = 707273) B707273
theorem B471591 : Blo 467785 471591 := bstep (se 1 (by rfl) ⟨353693, by rfl⟩ : syracuseStep 471591 = 707387) B707387
theorem B471631 : Blo 467785 471631 := bstep (se 1 (by rfl) ⟨353723, by rfl⟩ : syracuseStep 471631 = 707447) B707447
theorem B471647 : Blo 467785 471647 := bstep (se 1 (by rfl) ⟨353735, by rfl⟩ : syracuseStep 471647 = 707471) B707471
theorem B471675 : Blo 467785 471675 := bstep (se 1 (by rfl) ⟨353756, by rfl⟩ : syracuseStep 471675 = 707513) B707513
theorem B471727 : Blo 467785 471727 := bstep (se 1 (by rfl) ⟨353795, by rfl⟩ : syracuseStep 471727 = 707591) B707591
theorem B471751 : Blo 467785 471751 := bstep (se 1 (by rfl) ⟨353813, by rfl⟩ : syracuseStep 471751 = 707627) B707627
theorem B3846865 : Blo 467785 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B471771 : Blo 467785 471771 := bstep (se 1 (by rfl) ⟨353828, by rfl⟩ : syracuseStep 471771 = 707657) B707657
theorem B10138385 : Blo 467785 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B1782557 : Blo 467785 1782557 := bstep (se 3 (by rfl) ⟨334229, by rfl⟩ : syracuseStep 1782557 = 668459) B668459
theorem B2012161 : Blo 467785 2012161 := bstep (se 2 (by rfl) ⟨754560, by rfl⟩ : syracuseStep 2012161 = 1509121) B1509121
theorem B1586195 : Blo 467785 1586195 := bstep (se 1 (by rfl) ⟨1189646, by rfl⟩ : syracuseStep 1586195 = 2379293) B2379293
theorem B1193039 : Blo 467785 1193039 := bstep (se 1 (by rfl) ⟨894779, by rfl⟩ : syracuseStep 1193039 = 1789559) B1789559
theorem B1586519 : Blo 467785 1586519 := bstep (se 1 (by rfl) ⟨1189889, by rfl⟩ : syracuseStep 1586519 = 2379779) B2379779
theorem B701801 : Blo 467785 701801 := bstep (se 2 (by rfl) ⟨263175, by rfl⟩ : syracuseStep 701801 = 526351) B526351
theorem B701879 : Blo 467785 701879 := bstep (se 1 (by rfl) ⟨526409, by rfl⟩ : syracuseStep 701879 = 1052819) B1052819
theorem B1783241 : Blo 467785 1783241 := bstep (se 2 (by rfl) ⟨668715, by rfl⟩ : syracuseStep 1783241 = 1337431) B1337431
theorem B701915 : Blo 467785 701915 := bstep (se 1 (by rfl) ⟨526436, by rfl⟩ : syracuseStep 701915 = 1052873) B1052873
theorem B1193687 : Blo 467785 1193687 := bstep (se 1 (by rfl) ⟨895265, by rfl⟩ : syracuseStep 1193687 = 1790531) B1790531
theorem B702383 : Blo 467785 702383 := bstep (se 1 (by rfl) ⟨526787, by rfl⟩ : syracuseStep 702383 = 1053575) B1053575
theorem B1783727 : Blo 467785 1783727 := bstep (se 1 (by rfl) ⟨1337795, by rfl⟩ : syracuseStep 1783727 = 2675591) B2675591
theorem B702473 : Blo 467785 702473 := bstep (se 2 (by rfl) ⟨263427, by rfl⟩ : syracuseStep 702473 = 526855) B526855
theorem B1128467 : Blo 467785 1128467 := bstep (se 1 (by rfl) ⟨846350, by rfl⟩ : syracuseStep 1128467 = 1692701) B1692701
theorem B702503 : Blo 467785 702503 := bstep (se 1 (by rfl) ⟨526877, by rfl⟩ : syracuseStep 702503 = 1053755) B1053755
theorem B1194041 : Blo 467785 1194041 := bstep (se 2 (by rfl) ⟨447765, by rfl⟩ : syracuseStep 1194041 = 895531) B895531
theorem B702587 : Blo 467785 702587 := bstep (se 1 (by rfl) ⟨526940, by rfl⟩ : syracuseStep 702587 = 1053881) B1053881
theorem B3815581 : Blo 467785 3815581 := bstep (se 3 (by rfl) ⟨715421, by rfl⟩ : syracuseStep 3815581 = 1430843) B1430843
theorem B702713 : Blo 467785 702713 := bstep (se 2 (by rfl) ⟨263517, by rfl⟩ : syracuseStep 702713 = 527035) B527035
theorem B702815 : Blo 467785 702815 := bstep (se 1 (by rfl) ⟨527111, by rfl⟩ : syracuseStep 702815 = 1054223) B1054223
theorem B702827 : Blo 467785 702827 := bstep (se 1 (by rfl) ⟨527120, by rfl⟩ : syracuseStep 702827 = 1054241) B1054241
theorem B5093765 : Blo 467785 5093765 := bstep (se 4 (by rfl) ⟨477540, by rfl⟩ : syracuseStep 5093765 = 955081) B955081
theorem B1587599 : Blo 467785 1587599 := bstep (se 1 (by rfl) ⟨1190699, by rfl⟩ : syracuseStep 1587599 = 2381399) B2381399
theorem B703055 : Blo 467785 703055 := bstep (se 1 (by rfl) ⟨527291, by rfl⟩ : syracuseStep 703055 = 1054583) B1054583
theorem B703175 : Blo 467785 703175 := bstep (se 1 (by rfl) ⟨527381, by rfl⟩ : syracuseStep 703175 = 1054763) B1054763
theorem B1784531 : Blo 467785 1784531 := bstep (se 1 (by rfl) ⟨1338398, by rfl⟩ : syracuseStep 1784531 = 2676797) B2676797
theorem B1587923 : Blo 467785 1587923 := bstep (se 1 (by rfl) ⟨1190942, by rfl⟩ : syracuseStep 1587923 = 2381885) B2381885
theorem B9616157 : Blo 467785 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B703337 : Blo 467785 703337 := bstep (se 2 (by rfl) ⟨263751, by rfl⟩ : syracuseStep 703337 = 527503) B527503
theorem B3619729 : Blo 467785 3619729 := bstep (se 2 (by rfl) ⟨1357398, by rfl⟩ : syracuseStep 3619729 = 2714797) B2714797
theorem B703415 : Blo 467785 703415 := bstep (se 1 (by rfl) ⟨527561, by rfl⟩ : syracuseStep 703415 = 1055123) B1055123
theorem B703451 : Blo 467785 703451 := bstep (se 1 (by rfl) ⟨527588, by rfl⟩ : syracuseStep 703451 = 1055177) B1055177
theorem B6011927 : Blo 467785 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B2538877 : Blo 467785 2538877 := bstep (se 3 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 2538877 = 952079) B952079
theorem B1129871 : Blo 467785 1129871 := bstep (se 1 (by rfl) ⟨847403, by rfl⟩ : syracuseStep 1129871 = 1694807) B1694807
theorem B703919 : Blo 467785 703919 := bstep (se 1 (by rfl) ⟨527939, by rfl⟩ : syracuseStep 703919 = 1055879) B1055879
theorem B1687049 : Blo 467785 1687049 := bstep (se 2 (by rfl) ⟨632643, by rfl⟩ : syracuseStep 1687049 = 1265287) B1265287
theorem B704009 : Blo 467785 704009 := bstep (se 2 (by rfl) ⟨264003, by rfl⟩ : syracuseStep 704009 = 528007) B528007
theorem B704039 : Blo 467785 704039 := bstep (se 1 (by rfl) ⟨528029, by rfl⟩ : syracuseStep 704039 = 1056059) B1056059
theorem B704123 : Blo 467785 704123 := bstep (se 1 (by rfl) ⟨528092, by rfl⟩ : syracuseStep 704123 = 1056185) B1056185
theorem B704249 : Blo 467785 704249 := bstep (se 2 (by rfl) ⟨264093, by rfl⟩ : syracuseStep 704249 = 528187) B528187
theorem B802633 : Blo 467785 802633 := bstep (se 2 (by rfl) ⟨300987, by rfl⟩ : syracuseStep 802633 = 601975) B601975
theorem B704351 : Blo 467785 704351 := bstep (se 1 (by rfl) ⟨528263, by rfl⟩ : syracuseStep 704351 = 1056527) B1056527
theorem B704363 : Blo 467785 704363 := bstep (se 1 (by rfl) ⟨528272, by rfl⟩ : syracuseStep 704363 = 1056545) B1056545
theorem B1589111 : Blo 467785 1589111 := bstep (se 1 (by rfl) ⟨1191833, by rfl⟩ : syracuseStep 1589111 = 2383667) B2383667
theorem B704591 : Blo 467785 704591 := bstep (se 1 (by rfl) ⟨528443, by rfl⟩ : syracuseStep 704591 = 1056887) B1056887
theorem B1589327 : Blo 467785 1589327 := bstep (se 1 (by rfl) ⟨1191995, by rfl⟩ : syracuseStep 1589327 = 2383991) B2383991
theorem B704711 : Blo 467785 704711 := bstep (se 1 (by rfl) ⟨528533, by rfl⟩ : syracuseStep 704711 = 1057067) B1057067
theorem B704873 : Blo 467785 704873 := bstep (se 2 (by rfl) ⟨264327, by rfl⟩ : syracuseStep 704873 = 528655) B528655
theorem B704951 : Blo 467785 704951 := bstep (se 1 (by rfl) ⟨528713, by rfl⟩ : syracuseStep 704951 = 1057427) B1057427
theorem B1589705 : Blo 467785 1589705 := bstep (se 2 (by rfl) ⟨596139, by rfl⟩ : syracuseStep 1589705 = 1192279) B1192279
theorem B12894673 : Blo 467785 12894673 := bstep (se 2 (by rfl) ⟨4835502, by rfl⟩ : syracuseStep 12894673 = 9671005) B9671005
theorem B1425883 : Blo 467785 1425883 := bstep (se 1 (by rfl) ⟨1069412, by rfl⟩ : syracuseStep 1425883 = 2138825) B2138825
theorem B704987 : Blo 467785 704987 := bstep (se 1 (by rfl) ⟨528740, by rfl⟩ : syracuseStep 704987 = 1057481) B1057481
theorem B5718701 : Blo 467785 5718701 := bstep (se 3 (by rfl) ⟨1072256, by rfl⟩ : syracuseStep 5718701 = 2144513) B2144513
theorem B2376377 : Blo 467785 2376377 := bstep (se 2 (by rfl) ⟨891141, by rfl⟩ : syracuseStep 2376377 = 1782283) B1782283
theorem B1589975 : Blo 467785 1589975 := bstep (se 1 (by rfl) ⟨1192481, by rfl⟩ : syracuseStep 1589975 = 2384963) B2384963
theorem B705455 : Blo 467785 705455 := bstep (se 1 (by rfl) ⟨529091, by rfl⟩ : syracuseStep 705455 = 1058183) B1058183
theorem B1590191 : Blo 467785 1590191 := bstep (se 1 (by rfl) ⟨1192643, by rfl⟩ : syracuseStep 1590191 = 2385287) B2385287
theorem B705545 : Blo 467785 705545 := bstep (se 2 (by rfl) ⟨264579, by rfl⟩ : syracuseStep 705545 = 529159) B529159
theorem B705575 : Blo 467785 705575 := bstep (se 1 (by rfl) ⟨529181, by rfl⟩ : syracuseStep 705575 = 1058363) B1058363
theorem B1786961 : Blo 467785 1786961 := bstep (se 2 (by rfl) ⟨670110, by rfl⟩ : syracuseStep 1786961 = 1340221) B1340221
theorem B705659 : Blo 467785 705659 := bstep (se 1 (by rfl) ⟨529244, by rfl⟩ : syracuseStep 705659 = 1058489) B1058489
theorem B3556547 : Blo 467785 3556547 := bstep (se 1 (by rfl) ⟨2667410, by rfl⟩ : syracuseStep 3556547 = 5334821) B5334821
theorem B705785 : Blo 467785 705785 := bstep (se 2 (by rfl) ⟨264669, by rfl⟩ : syracuseStep 705785 = 529339) B529339
theorem B705887 : Blo 467785 705887 := bstep (se 1 (by rfl) ⟨529415, by rfl⟩ : syracuseStep 705887 = 1058831) B1058831
theorem B705899 : Blo 467785 705899 := bstep (se 1 (by rfl) ⟨529424, by rfl⟩ : syracuseStep 705899 = 1058849) B1058849
theorem B6768035 : Blo 467785 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B476591 : Blo 467785 476591 := bstep (se 1 (by rfl) ⟨357443, by rfl⟩ : syracuseStep 476591 = 714887) B714887
theorem B1131995 : Blo 467785 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B1787417 : Blo 467785 1787417 := bstep (se 2 (by rfl) ⟨670281, by rfl⟩ : syracuseStep 1787417 = 1340563) B1340563
theorem B706127 : Blo 467785 706127 := bstep (se 1 (by rfl) ⟨529595, by rfl⟩ : syracuseStep 706127 = 1059191) B1059191
theorem B706247 : Blo 467785 706247 := bstep (se 1 (by rfl) ⟨529685, by rfl⟩ : syracuseStep 706247 = 1059371) B1059371
theorem B1689299 : Blo 467785 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B706409 : Blo 467785 706409 := bstep (se 2 (by rfl) ⟨264903, by rfl⟩ : syracuseStep 706409 = 529807) B529807
theorem B3000199 : Blo 467785 3000199 := bstep (se 1 (by rfl) ⟨2250149, by rfl⟩ : syracuseStep 3000199 = 4500299) B4500299
theorem B706487 : Blo 467785 706487 := bstep (se 1 (by rfl) ⟨529865, by rfl⟩ : syracuseStep 706487 = 1059731) B1059731
theorem B706523 : Blo 467785 706523 := bstep (se 1 (by rfl) ⟨529892, by rfl⟩ : syracuseStep 706523 = 1059785) B1059785
theorem B706991 : Blo 467785 706991 := bstep (se 1 (by rfl) ⟨530243, by rfl⟩ : syracuseStep 706991 = 1060487) B1060487
theorem B707081 : Blo 467785 707081 := bstep (se 2 (by rfl) ⟨265155, by rfl⟩ : syracuseStep 707081 = 530311) B530311
theorem B1133081 : Blo 467785 1133081 := bstep (se 2 (by rfl) ⟨424905, by rfl⟩ : syracuseStep 1133081 = 849811) B849811
theorem B707111 : Blo 467785 707111 := bstep (se 1 (by rfl) ⟨530333, by rfl⟩ : syracuseStep 707111 = 1060667) B1060667
theorem B707195 : Blo 467785 707195 := bstep (se 1 (by rfl) ⟨530396, by rfl⟩ : syracuseStep 707195 = 1060793) B1060793
theorem B9652871 : Blo 467785 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B1788601 : Blo 467785 1788601 := bstep (se 2 (by rfl) ⟨670725, by rfl⟩ : syracuseStep 1788601 = 1341451) B1341451
theorem B3001043 : Blo 467785 3001043 := bstep (se 1 (by rfl) ⟨2250782, by rfl⟩ : syracuseStep 3001043 = 4501565) B4501565
theorem B707321 : Blo 467785 707321 := bstep (se 2 (by rfl) ⟨265245, by rfl⟩ : syracuseStep 707321 = 530491) B530491
theorem B707423 : Blo 467785 707423 := bstep (se 1 (by rfl) ⟨530567, by rfl⟩ : syracuseStep 707423 = 1061135) B1061135
theorem B707435 : Blo 467785 707435 := bstep (se 1 (by rfl) ⟨530576, by rfl⟩ : syracuseStep 707435 = 1061153) B1061153
theorem B707663 : Blo 467785 707663 := bstep (se 1 (by rfl) ⟨530747, by rfl⟩ : syracuseStep 707663 = 1061495) B1061495
theorem B1691117 : Blo 467785 1691117 := bstep (se 3 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 1691117 = 634169) B634169
theorem B3624509 : Blo 467785 3624509 := bstep (se 3 (by rfl) ⟨679595, by rfl⟩ : syracuseStep 3624509 = 1359191) B1359191
theorem B13684301 : Blo 467785 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B1069303 : Blo 467785 1069303 := bstep (se 1 (by rfl) ⟨801977, by rfl⟩ : syracuseStep 1069303 = 1603955) B1603955
theorem B1790333 : Blo 467785 1790333 := bstep (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) B671375
theorem B1200779 : Blo 467785 1200779 := bstep (se 1 (by rfl) ⟨900584, by rfl⟩ : syracuseStep 1200779 = 1801169) B1801169
theorem B5100205 : Blo 467785 5100205 := bstep (se 3 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 5100205 = 1912577) B1912577
theorem B2282195 : Blo 467785 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B1004243 : Blo 467785 1004243 := bstep (se 1 (by rfl) ⟨753182, by rfl⟩ : syracuseStep 1004243 = 1506365) B1506365
theorem B1266607 : Blo 467785 1266607 := bstep (se 1 (by rfl) ⟨949955, by rfl⟩ : syracuseStep 1266607 = 1899911) B1899911
theorem B5690387 : Blo 467785 5690387 := bstep (se 1 (by rfl) ⟨4267790, by rfl⟩ : syracuseStep 5690387 = 8535581) B8535581
theorem B1692989 : Blo 467785 1692989 := bstep (se 3 (by rfl) ⟨317435, by rfl⟩ : syracuseStep 1692989 = 634871) B634871
theorem B3659251 : Blo 467785 3659251 := bstep (se 1 (by rfl) ⟨2744438, by rfl⟩ : syracuseStep 3659251 = 5488877) B5488877
theorem B1332875 : Blo 467785 1332875 := bstep (se 1 (by rfl) ⟨999656, by rfl⟩ : syracuseStep 1332875 = 1999313) B1999313
theorem B2381561 : Blo 467785 2381561 := bstep (se 2 (by rfl) ⟨893085, by rfl⟩ : syracuseStep 2381561 = 1786171) B1786171
theorem B6084395 : Blo 467785 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B2676523 : Blo 467785 2676523 := bstep (se 1 (by rfl) ⟨2007392, by rfl⟩ : syracuseStep 2676523 = 4014785) B4014785
theorem B1267883 : Blo 467785 1267883 := bstep (se 1 (by rfl) ⟨950912, by rfl⟩ : syracuseStep 1267883 = 1901825) B1901825
theorem B1005815 : Blo 467785 1005815 := bstep (se 1 (by rfl) ⟨754361, by rfl⟩ : syracuseStep 1005815 = 1508723) B1508723
theorem B2382209 : Blo 467785 2382209 := bstep (se 2 (by rfl) ⟨893328, by rfl⟩ : syracuseStep 2382209 = 1786657) B1786657
theorem B13687339 : Blo 467785 13687339 := bstep (se 1 (by rfl) ⟨10265504, by rfl⟩ : syracuseStep 13687339 = 20531009) B20531009
theorem B10279979 : Blo 467785 10279979 := bstep (se 1 (by rfl) ⟨7709984, by rfl⟩ : syracuseStep 10279979 = 15419969) B15419969
theorem B1694891 : Blo 467785 1694891 := bstep (se 1 (by rfl) ⟨1271168, by rfl⟩ : syracuseStep 1694891 = 2542337) B2542337
theorem B2383019 : Blo 467785 2383019 := bstep (se 1 (by rfl) ⟨1787264, by rfl⟩ : syracuseStep 2383019 = 3574529) B3574529
theorem B6774029 : Blo 467785 6774029 := bstep (se 3 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 6774029 = 2540261) B2540261
theorem B2383505 : Blo 467785 2383505 := bstep (se 2 (by rfl) ⟨893814, by rfl⟩ : syracuseStep 2383505 = 1787629) B1787629
theorem B1007353 : Blo 467785 1007353 := bstep (se 2 (by rfl) ⟨377757, by rfl⟩ : syracuseStep 1007353 = 755515) B755515
theorem B1695583 : Blo 467785 1695583 := bstep (se 1 (by rfl) ⟨1271687, by rfl⟩ : syracuseStep 1695583 = 2543375) B2543375
theorem B4022135 : Blo 467785 4022135 := bstep (se 1 (by rfl) ⟨3016601, by rfl⟩ : syracuseStep 4022135 = 6033203) B6033203
theorem B3563837 : Blo 467785 3563837 := bstep (se 3 (by rfl) ⟨668219, by rfl⟩ : syracuseStep 3563837 = 1336439) B1336439
theorem B844175 : Blo 467785 844175 := bstep (se 1 (by rfl) ⟨633131, by rfl⟩ : syracuseStep 844175 = 1266263) B1266263
theorem B1335847 : Blo 467785 1335847 := bstep (se 1 (by rfl) ⟨1001885, by rfl⟩ : syracuseStep 1335847 = 2003771) B2003771
theorem B1696391 : Blo 467785 1696391 := bstep (se 1 (by rfl) ⟨1272293, by rfl⟩ : syracuseStep 1696391 = 2544587) B2544587
theorem B1336007 : Blo 467785 1336007 := bstep (se 1 (by rfl) ⟨1002005, by rfl⟩ : syracuseStep 1336007 = 2004011) B2004011
theorem B3400393 : Blo 467785 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B844499 : Blo 467785 844499 := bstep (se 1 (by rfl) ⟨633374, by rfl⟩ : syracuseStep 844499 = 1266749) B1266749
theorem B1499933 : Blo 467785 1499933 := bstep (se 3 (by rfl) ⟨281237, by rfl⟩ : syracuseStep 1499933 = 562475) B562475
theorem B1336247 : Blo 467785 1336247 := bstep (se 1 (by rfl) ⟨1002185, by rfl⟩ : syracuseStep 1336247 = 2004371) B2004371
theorem B2254205 : Blo 467785 2254205 := bstep (se 3 (by rfl) ⟨422663, by rfl⟩ : syracuseStep 2254205 = 845327) B845327
theorem B17655331 : Blo 467785 17655331 := bstep (se 1 (by rfl) ⟨13241498, by rfl⟩ : syracuseStep 17655331 = 26482997) B26482997
theorem B2385773 : Blo 467785 2385773 := bstep (se 3 (by rfl) ⟨447332, by rfl⟩ : syracuseStep 2385773 = 894665) B894665
theorem B1337249 : Blo 467785 1337249 := bstep (se 2 (by rfl) ⟨501468, by rfl⟩ : syracuseStep 1337249 = 1002937) B1002937
theorem B1206199 : Blo 467785 1206199 := bstep (se 1 (by rfl) ⟨904649, by rfl⟩ : syracuseStep 1206199 = 1809299) B1809299
theorem B2385935 : Blo 467785 2385935 := bstep (se 1 (by rfl) ⟨1789451, by rfl⟩ : syracuseStep 2385935 = 3578903) B3578903
theorem B2287883 : Blo 467785 2287883 := bstep (se 1 (by rfl) ⟨1715912, by rfl⟩ : syracuseStep 2287883 = 3431825) B3431825
theorem B1337705 : Blo 467785 1337705 := bstep (se 2 (by rfl) ⟨501639, by rfl⟩ : syracuseStep 1337705 = 1003279) B1003279
theorem B6777377 : Blo 467785 6777377 := bstep (se 2 (by rfl) ⟨2541516, by rfl⟩ : syracuseStep 6777377 = 5083033) B5083033
theorem B3337037 : Blo 467785 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B1502059 : Blo 467785 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B3009707 : Blo 467785 3009707 := bstep (se 1 (by rfl) ⟨2257280, by rfl⟩ : syracuseStep 3009707 = 4514561) B4514561
theorem B1699159 : Blo 467785 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B2846117 : Blo 467785 2846117 := bstep (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) B533647
theorem B2682355 : Blo 467785 2682355 := bstep (se 1 (by rfl) ⟨2011766, by rfl⟩ : syracuseStep 2682355 = 4023533) B4023533
theorem B1338889 : Blo 467785 1338889 := bstep (se 2 (by rfl) ⟨502083, by rfl⟩ : syracuseStep 1338889 = 1004167) B1004167
theorem B1633991 : Blo 467785 1633991 := bstep (se 1 (by rfl) ⟨1225493, by rfl⟩ : syracuseStep 1633991 = 2450987) B2450987
theorem B3796769 : Blo 467785 3796769 := bstep (se 2 (by rfl) ⟨1423788, by rfl⟩ : syracuseStep 3796769 = 2847577) B2847577
theorem B1699679 : Blo 467785 1699679 := bstep (se 1 (by rfl) ⟨1274759, by rfl⟩ : syracuseStep 1699679 = 2549519) B2549519
theorem B1503137 : Blo 467785 1503137 := bstep (se 2 (by rfl) ⟨563676, by rfl⟩ : syracuseStep 1503137 = 1127353) B1127353
theorem B1503289 : Blo 467785 1503289 := bstep (se 2 (by rfl) ⟨563733, by rfl⟩ : syracuseStep 1503289 = 1127467) B1127467
theorem B5501245 : Blo 467785 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B749999 : Blo 467785 749999 := bstep (se 1 (by rfl) ⟨562499, by rfl⟩ : syracuseStep 749999 = 1124999) B1124999
theorem B1897283 : Blo 467785 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B1340347 : Blo 467785 1340347 := bstep (se 1 (by rfl) ⟨1005260, by rfl⟩ : syracuseStep 1340347 = 2010521) B2010521
theorem B1340495 : Blo 467785 1340495 := bstep (se 1 (by rfl) ⟨1005371, by rfl⟩ : syracuseStep 1340495 = 2010743) B2010743
theorem B1504777 : Blo 467785 1504777 := bstep (se 2 (by rfl) ⟨564291, by rfl⟩ : syracuseStep 1504777 = 1128583) B1128583
theorem B751351 : Blo 467785 751351 := bstep (se 1 (by rfl) ⟨563513, by rfl⟩ : syracuseStep 751351 = 1127027) B1127027
theorem B1341497 : Blo 467785 1341497 := bstep (se 2 (by rfl) ⟨503061, by rfl⟩ : syracuseStep 1341497 = 1006123) B1006123
theorem B2685271 : Blo 467785 2685271 := bstep (se 1 (by rfl) ⟨2013953, by rfl⟩ : syracuseStep 2685271 = 4027907) B4027907
theorem B751979 : Blo 467785 751979 := bstep (se 1 (by rfl) ⟨563984, by rfl⟩ : syracuseStep 751979 = 1127969) B1127969
theorem B1341839 : Blo 467785 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B3013321 : Blo 467785 3013321 := bstep (se 2 (by rfl) ⟨1129995, by rfl⟩ : syracuseStep 3013321 = 2259991) B2259991
theorem B1899359 : Blo 467785 1899359 := bstep (se 1 (by rfl) ⟨1424519, by rfl⟩ : syracuseStep 1899359 = 2849039) B2849039
theorem B2260163 : Blo 467785 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B4029821 : Blo 467785 4029821 := bstep (se 3 (by rfl) ⟨755591, by rfl⟩ : syracuseStep 4029821 = 1511183) B1511183
theorem B753209 : Blo 467785 753209 := bstep (se 2 (by rfl) ⟨282453, by rfl⟩ : syracuseStep 753209 = 564907) B564907
theorem B753401 : Blo 467785 753401 := bstep (se 2 (by rfl) ⟨282525, by rfl⟩ : syracuseStep 753401 = 565051) B565051
theorem B1901177 : Blo 467785 1901177 := bstep (se 2 (by rfl) ⟨712941, by rfl⟩ : syracuseStep 1901177 = 1425883) B1425883
theorem B1999997 : Blo 467785 1999997 := bstep (se 3 (by rfl) ⟨374999, by rfl⟩ : syracuseStep 1999997 = 749999) B749999
theorem B4064825 : Blo 467785 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B755387 : Blo 467785 755387 := bstep (se 1 (by rfl) ⟨566540, by rfl⟩ : syracuseStep 755387 = 1133081) B1133081
theorem B2000695 : Blo 467785 2000695 := bstep (se 1 (by rfl) ⟨1500521, by rfl⟩ : syracuseStep 2000695 = 3001043) B3001043
theorem B4000265 : Blo 467785 4000265 := bstep (se 2 (by rfl) ⟨1500099, by rfl⟩ : syracuseStep 4000265 = 3000199) B3000199
theorem B1608265 : Blo 467785 1608265 := bstep (se 2 (by rfl) ⟨603099, by rfl⟩ : syracuseStep 1608265 = 1206199) B1206199
theorem B527071 : Blo 467785 527071 := bstep (se 1 (by rfl) ⟨395303, by rfl⟩ : syracuseStep 527071 = 790607) B790607
theorem B592687 : Blo 467785 592687 := bstep (se 1 (by rfl) ⟨444515, by rfl⟩ : syracuseStep 592687 = 889031) B889031
theorem B789419 : Blo 467785 789419 := bstep (se 1 (by rfl) ⟨592064, by rfl⟩ : syracuseStep 789419 = 1184129) B1184129
theorem B593183 : Blo 467785 593183 := bstep (se 1 (by rfl) ⟨444887, by rfl⟩ : syracuseStep 593183 = 889775) B889775
theorem B527647 : Blo 467785 527647 := bstep (se 1 (by rfl) ⟨395735, by rfl⟩ : syracuseStep 527647 = 791471) B791471
theorem B789959 : Blo 467785 789959 := bstep (se 1 (by rfl) ⟨592469, by rfl⟩ : syracuseStep 789959 = 1184939) B1184939
theorem B6032839 : Blo 467785 6032839 := bstep (se 1 (by rfl) ⟨4524629, by rfl⟩ : syracuseStep 6032839 = 9049259) B9049259
theorem B527935 : Blo 467785 527935 := bstep (se 1 (by rfl) ⟨395951, by rfl⟩ : syracuseStep 527935 = 791903) B791903
theorem B888583 : Blo 467785 888583 := bstep (se 1 (by rfl) ⟨666437, by rfl⟩ : syracuseStep 888583 = 1332875) B1332875
theorem B2002745 : Blo 467785 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B3018653 : Blo 467785 3018653 := bstep (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) B1131995
theorem B2298059 : Blo 467785 2298059 := bstep (se 1 (by rfl) ⟨1723544, by rfl⟩ : syracuseStep 2298059 = 3447089) B3447089
theorem B1053035 : Blo 467785 1053035 := bstep (se 1 (by rfl) ⟨789776, by rfl⟩ : syracuseStep 1053035 = 1579553) B1579553
theorem B528763 : Blo 467785 528763 := bstep (se 1 (by rfl) ⟨396572, by rfl⟩ : syracuseStep 528763 = 793145) B793145
theorem B790951 : Blo 467785 790951 := bstep (se 1 (by rfl) ⟨593213, by rfl⟩ : syracuseStep 790951 = 1186427) B1186427
theorem B2265545 : Blo 467785 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B1053179 : Blo 467785 1053179 := bstep (se 1 (by rfl) ⟨789884, by rfl⟩ : syracuseStep 1053179 = 1579769) B1579769
theorem B791113 : Blo 467785 791113 := bstep (se 2 (by rfl) ⟨296667, by rfl⟩ : syracuseStep 791113 = 593335) B593335
theorem B791147 : Blo 467785 791147 := bstep (se 1 (by rfl) ⟨593360, by rfl⟩ : syracuseStep 791147 = 1186721) B1186721
theorem B1053305 : Blo 467785 1053305 := bstep (se 2 (by rfl) ⟨394989, by rfl⟩ : syracuseStep 1053305 = 789979) B789979
theorem B3576473 : Blo 467785 3576473 := bstep (se 2 (by rfl) ⟨1341177, by rfl⟩ : syracuseStep 3576473 = 2682355) B2682355
theorem B1053359 : Blo 467785 1053359 := bstep (se 1 (by rfl) ⟨790019, by rfl⟩ : syracuseStep 1053359 = 1580039) B1580039
theorem B6853319 : Blo 467785 6853319 := bstep (se 1 (by rfl) ⟨5139989, by rfl⟩ : syracuseStep 6853319 = 10279979) B10279979
theorem B1184503 : Blo 467785 1184503 := bstep (se 1 (by rfl) ⟨888377, by rfl⟩ : syracuseStep 1184503 = 1776755) B1776755
theorem B1053431 : Blo 467785 1053431 := bstep (se 1 (by rfl) ⟨790073, by rfl⟩ : syracuseStep 1053431 = 1580147) B1580147
theorem B529231 : Blo 467785 529231 := bstep (se 1 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 529231 = 793847) B793847
theorem B1053611 : Blo 467785 1053611 := bstep (se 1 (by rfl) ⟨790208, by rfl⟩ : syracuseStep 1053611 = 1580417) B1580417
theorem B1184807 : Blo 467785 1184807 := bstep (se 1 (by rfl) ⟨888605, by rfl⟩ : syracuseStep 1184807 = 1777211) B1777211
theorem B529627 : Blo 467785 529627 := bstep (se 1 (by rfl) ⟨397220, by rfl⟩ : syracuseStep 529627 = 794441) B794441
theorem B6755575 : Blo 467785 6755575 := bstep (se 1 (by rfl) ⟨5066681, by rfl⟩ : syracuseStep 6755575 = 10133363) B10133363
theorem B1054151 : Blo 467785 1054151 := bstep (se 1 (by rfl) ⟨790613, by rfl⟩ : syracuseStep 1054151 = 1581227) B1581227
theorem B595451 : Blo 467785 595451 := bstep (se 1 (by rfl) ⟨446588, by rfl⟩ : syracuseStep 595451 = 893177) B893177
theorem B529915 : Blo 467785 529915 := bstep (se 1 (by rfl) ⟨397436, by rfl⟩ : syracuseStep 529915 = 794873) B794873
theorem B2856485 : Blo 467785 2856485 := bstep (se 4 (by rfl) ⟨267795, by rfl⟩ : syracuseStep 2856485 = 535591) B535591
theorem B562783 : Blo 467785 562783 := bstep (se 1 (by rfl) ⟨422087, by rfl⟩ : syracuseStep 562783 = 844175) B844175
theorem B530095 : Blo 467785 530095 := bstep (se 1 (by rfl) ⟨397571, by rfl⟩ : syracuseStep 530095 = 795143) B795143
theorem B1054511 : Blo 467785 1054511 := bstep (se 1 (by rfl) ⟨790883, by rfl⟩ : syracuseStep 1054511 = 1581767) B1581767
theorem B890671 : Blo 467785 890671 := bstep (se 1 (by rfl) ⟨668003, by rfl⟩ : syracuseStep 890671 = 1336007) B1336007
theorem B562999 : Blo 467785 562999 := bstep (se 1 (by rfl) ⟨422249, by rfl⟩ : syracuseStep 562999 = 844499) B844499
theorem B1578959 : Blo 467785 1578959 := bstep (se 1 (by rfl) ⟨1184219, by rfl⟩ : syracuseStep 1578959 = 2368439) B2368439
theorem B890831 : Blo 467785 890831 := bstep (se 1 (by rfl) ⟨668123, by rfl⟩ : syracuseStep 890831 = 1336247) B1336247
theorem B530383 : Blo 467785 530383 := bstep (se 1 (by rfl) ⟨397787, by rfl⟩ : syracuseStep 530383 = 795575) B795575
theorem B6101021 : Blo 467785 6101021 := bstep (se 3 (by rfl) ⟨1143941, by rfl⟩ : syracuseStep 6101021 = 2287883) B2287883
theorem B792841 : Blo 467785 792841 := bstep (se 2 (by rfl) ⟨297315, by rfl⟩ : syracuseStep 792841 = 594631) B594631
theorem B1186073 : Blo 467785 1186073 := bstep (se 2 (by rfl) ⟨444777, by rfl⟩ : syracuseStep 1186073 = 889555) B889555
theorem B1055087 : Blo 467785 1055087 := bstep (se 1 (by rfl) ⟨791315, by rfl⟩ : syracuseStep 1055087 = 1582631) B1582631
theorem B1055159 : Blo 467785 1055159 := bstep (se 1 (by rfl) ⟨791369, by rfl⟩ : syracuseStep 1055159 = 1582739) B1582739
theorem B3021239 : Blo 467785 3021239 := bstep (se 1 (by rfl) ⟨2265929, by rfl⟩ : syracuseStep 3021239 = 4531859) B4531859
theorem B596423 : Blo 467785 596423 := bstep (se 1 (by rfl) ⟨447317, by rfl⟩ : syracuseStep 596423 = 894635) B894635
theorem B1055303 : Blo 467785 1055303 := bstep (se 1 (by rfl) ⟨791477, by rfl⟩ : syracuseStep 1055303 = 1582955) B1582955
theorem B596575 : Blo 467785 596575 := bstep (se 1 (by rfl) ⟨447431, by rfl⟩ : syracuseStep 596575 = 894863) B894863
theorem B1055339 : Blo 467785 1055339 := bstep (se 1 (by rfl) ⟨791504, by rfl⟩ : syracuseStep 1055339 = 1583009) B1583009
theorem B891499 : Blo 467785 891499 := bstep (se 1 (by rfl) ⟨668624, by rfl⟩ : syracuseStep 891499 = 1337249) B1337249
theorem B1579931 : Blo 467785 1579931 := bstep (se 1 (by rfl) ⟨1184948, by rfl⟩ : syracuseStep 1579931 = 2369897) B2369897
theorem B891803 : Blo 467785 891803 := bstep (se 1 (by rfl) ⟨668852, by rfl⟩ : syracuseStep 891803 = 1337705) B1337705
theorem B1055735 : Blo 467785 1055735 := bstep (se 1 (by rfl) ⟨791801, by rfl⟩ : syracuseStep 1055735 = 1583603) B1583603
theorem B1186913 : Blo 467785 1186913 := bstep (se 2 (by rfl) ⟨445092, by rfl⟩ : syracuseStep 1186913 = 890185) B890185
theorem B1056095 : Blo 467785 1056095 := bstep (se 1 (by rfl) ⟨792071, by rfl⟩ : syracuseStep 1056095 = 1584143) B1584143
theorem B2006369 : Blo 467785 2006369 := bstep (se 2 (by rfl) ⟨752388, by rfl⟩ : syracuseStep 2006369 = 1504777) B1504777
theorem B2006471 : Blo 467785 2006471 := bstep (se 1 (by rfl) ⟨1504853, by rfl⟩ : syracuseStep 2006471 = 3009707) B3009707
theorem B794299 : Blo 467785 794299 := bstep (se 1 (by rfl) ⟨595724, by rfl⟩ : syracuseStep 794299 = 1191449) B1191449
theorem B1056491 : Blo 467785 1056491 := bstep (se 1 (by rfl) ⟨792368, by rfl⟩ : syracuseStep 1056491 = 1584737) B1584737
theorem B1056617 : Blo 467785 1056617 := bstep (se 2 (by rfl) ⟨396231, by rfl⟩ : syracuseStep 1056617 = 792463) B792463
theorem B2531179 : Blo 467785 2531179 := bstep (se 1 (by rfl) ⟨1898384, by rfl⟩ : syracuseStep 2531179 = 3796769) B3796769
theorem B1580957 : Blo 467785 1580957 := bstep (se 3 (by rfl) ⟨296429, by rfl⟩ : syracuseStep 1580957 = 592859) B592859
theorem B1581065 : Blo 467785 1581065 := bstep (se 2 (by rfl) ⟨592899, by rfl⟩ : syracuseStep 1581065 = 1185799) B1185799
theorem B5087441 : Blo 467785 5087441 := bstep (se 2 (by rfl) ⟨1907790, by rfl⟩ : syracuseStep 5087441 = 3815581) B3815581
theorem B3580361 : Blo 467785 3580361 := bstep (se 2 (by rfl) ⟨1342635, by rfl⟩ : syracuseStep 3580361 = 2685271) B2685271
theorem B6758923 : Blo 467785 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B1188371 : Blo 467785 1188371 := bstep (se 1 (by rfl) ⟨891278, by rfl⟩ : syracuseStep 1188371 = 1782557) B1782557
theorem B1057463 : Blo 467785 1057463 := bstep (se 1 (by rfl) ⟨793097, by rfl⟩ : syracuseStep 1057463 = 1586195) B1586195
theorem B893663 : Blo 467785 893663 := bstep (se 1 (by rfl) ⟨670247, by rfl⟩ : syracuseStep 893663 = 1340495) B1340495
theorem B795359 : Blo 467785 795359 := bstep (se 1 (by rfl) ⟨596519, by rfl⟩ : syracuseStep 795359 = 1193039) B1193039
theorem B1057679 : Blo 467785 1057679 := bstep (se 1 (by rfl) ⟨793259, by rfl⟩ : syracuseStep 1057679 = 1586519) B1586519
theorem B467867 : Blo 467785 467867 := bstep (se 1 (by rfl) ⟨350900, by rfl⟩ : syracuseStep 467867 = 701801) B701801
theorem B467919 : Blo 467785 467919 := bstep (se 1 (by rfl) ⟨350939, by rfl⟩ : syracuseStep 467919 = 701879) B701879
theorem B1188827 : Blo 467785 1188827 := bstep (se 1 (by rfl) ⟨891620, by rfl⟩ : syracuseStep 1188827 = 1783241) B1783241
theorem B467943 : Blo 467785 467943 := bstep (se 1 (by rfl) ⟨350957, by rfl⟩ : syracuseStep 467943 = 701915) B701915
theorem B2368601 : Blo 467785 2368601 := bstep (se 2 (by rfl) ⟨888225, by rfl⟩ : syracuseStep 2368601 = 1776451) B1776451
theorem B795791 : Blo 467785 795791 := bstep (se 1 (by rfl) ⟨596843, by rfl⟩ : syracuseStep 795791 = 1193687) B1193687
theorem B4826305 : Blo 467785 4826305 := bstep (se 2 (by rfl) ⟨1809864, by rfl⟩ : syracuseStep 4826305 = 3619729) B3619729
theorem B468255 : Blo 467785 468255 := bstep (se 1 (by rfl) ⟨351191, by rfl⟩ : syracuseStep 468255 = 702383) B702383
theorem B1189151 : Blo 467785 1189151 := bstep (se 1 (by rfl) ⟨891863, by rfl⟩ : syracuseStep 1189151 = 1783727) B1783727
theorem B468315 : Blo 467785 468315 := bstep (se 1 (by rfl) ⟨351236, by rfl⟩ : syracuseStep 468315 = 702473) B702473
theorem B468335 : Blo 467785 468335 := bstep (se 1 (by rfl) ⟨351251, by rfl⟩ : syracuseStep 468335 = 702503) B702503
theorem B894331 : Blo 467785 894331 := bstep (se 1 (by rfl) ⟨670748, by rfl⟩ : syracuseStep 894331 = 1341497) B1341497
theorem B796027 : Blo 467785 796027 := bstep (se 1 (by rfl) ⟨597020, by rfl⟩ : syracuseStep 796027 = 1194041) B1194041
theorem B468391 : Blo 467785 468391 := bstep (se 1 (by rfl) ⟨351293, by rfl⟩ : syracuseStep 468391 = 702587) B702587
theorem B468475 : Blo 467785 468475 := bstep (se 1 (by rfl) ⟨351356, by rfl⟩ : syracuseStep 468475 = 702713) B702713
theorem B468543 : Blo 467785 468543 := bstep (se 1 (by rfl) ⟨351407, by rfl⟩ : syracuseStep 468543 = 702815) B702815
theorem B468551 : Blo 467785 468551 := bstep (se 1 (by rfl) ⟨351413, by rfl⟩ : syracuseStep 468551 = 702827) B702827
theorem B501319 : Blo 467785 501319 := bstep (se 1 (by rfl) ⟨375989, by rfl⟩ : syracuseStep 501319 = 751979) B751979
theorem B1058399 : Blo 467785 1058399 := bstep (se 1 (by rfl) ⟨793799, by rfl⟩ : syracuseStep 1058399 = 1587599) B1587599
theorem B894559 : Blo 467785 894559 := bstep (se 1 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 894559 = 1341839) B1341839
theorem B6039197 : Blo 467785 6039197 := bstep (se 3 (by rfl) ⟨1132349, by rfl⟩ : syracuseStep 6039197 = 2264699) B2264699
theorem B468703 : Blo 467785 468703 := bstep (se 1 (by rfl) ⟨351527, by rfl⟩ : syracuseStep 468703 = 703055) B703055
theorem B468783 : Blo 467785 468783 := bstep (se 1 (by rfl) ⟨351587, by rfl⟩ : syracuseStep 468783 = 703175) B703175
theorem B1189687 : Blo 467785 1189687 := bstep (se 1 (by rfl) ⟨892265, by rfl⟩ : syracuseStep 1189687 = 1784531) B1784531
theorem B1058615 : Blo 467785 1058615 := bstep (se 1 (by rfl) ⟨793961, by rfl⟩ : syracuseStep 1058615 = 1587923) B1587923
theorem B3385169 : Blo 467785 3385169 := bstep (se 2 (by rfl) ⟨1269438, by rfl⟩ : syracuseStep 3385169 = 2538877) B2538877
theorem B468891 : Blo 467785 468891 := bstep (se 1 (by rfl) ⟨351668, by rfl⟩ : syracuseStep 468891 = 703337) B703337
theorem B468943 : Blo 467785 468943 := bstep (se 1 (by rfl) ⟨351707, by rfl⟩ : syracuseStep 468943 = 703415) B703415
theorem B468967 : Blo 467785 468967 := bstep (se 1 (by rfl) ⟨351725, by rfl⟩ : syracuseStep 468967 = 703451) B703451
theorem B2009069 : Blo 467785 2009069 := bstep (se 3 (by rfl) ⟨376700, by rfl⟩ : syracuseStep 2009069 = 753401) B753401
theorem B4007951 : Blo 467785 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B1058921 : Blo 467785 1058921 := bstep (se 2 (by rfl) ⟨397095, by rfl⟩ : syracuseStep 1058921 = 794191) B794191
theorem B1190153 : Blo 467785 1190153 := bstep (se 2 (by rfl) ⟨446307, by rfl⟩ : syracuseStep 1190153 = 892615) B892615
theorem B469279 : Blo 467785 469279 := bstep (se 1 (by rfl) ⟨351959, by rfl⟩ : syracuseStep 469279 = 703919) B703919
theorem B1124699 : Blo 467785 1124699 := bstep (se 1 (by rfl) ⟨843524, by rfl⟩ : syracuseStep 1124699 = 1687049) B1687049
theorem B469339 : Blo 467785 469339 := bstep (se 1 (by rfl) ⟨352004, by rfl⟩ : syracuseStep 469339 = 704009) B704009
theorem B469359 : Blo 467785 469359 := bstep (se 1 (by rfl) ⟨352019, by rfl⟩ : syracuseStep 469359 = 704039) B704039
theorem B502139 : Blo 467785 502139 := bstep (se 1 (by rfl) ⟨376604, by rfl⟩ : syracuseStep 502139 = 753209) B753209
theorem B469415 : Blo 467785 469415 := bstep (se 1 (by rfl) ⟨352061, by rfl⟩ : syracuseStep 469415 = 704123) B704123
theorem B469499 : Blo 467785 469499 := bstep (se 1 (by rfl) ⟨352124, by rfl⟩ : syracuseStep 469499 = 704249) B704249
theorem B469567 : Blo 467785 469567 := bstep (se 1 (by rfl) ⟨352175, by rfl⟩ : syracuseStep 469567 = 704351) B704351
theorem B469575 : Blo 467785 469575 := bstep (se 1 (by rfl) ⟨352181, by rfl⟩ : syracuseStep 469575 = 704363) B704363
theorem B1059407 : Blo 467785 1059407 := bstep (se 1 (by rfl) ⟨794555, by rfl⟩ : syracuseStep 1059407 = 1589111) B1589111
theorem B469727 : Blo 467785 469727 := bstep (se 1 (by rfl) ⟨352295, by rfl⟩ : syracuseStep 469727 = 704591) B704591
theorem B1059551 : Blo 467785 1059551 := bstep (se 1 (by rfl) ⟨794663, by rfl⟩ : syracuseStep 1059551 = 1589327) B1589327
theorem B5090039 : Blo 467785 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B469807 : Blo 467785 469807 := bstep (se 1 (by rfl) ⟨352355, by rfl⟩ : syracuseStep 469807 = 704711) B704711
theorem B9153415 : Blo 467785 9153415 := bstep (se 1 (by rfl) ⟨6865061, by rfl⟩ : syracuseStep 9153415 = 13730123) B13730123
theorem B469915 : Blo 467785 469915 := bstep (se 1 (by rfl) ⟨352436, by rfl⟩ : syracuseStep 469915 = 704873) B704873
theorem B469967 : Blo 467785 469967 := bstep (se 1 (by rfl) ⟨352475, by rfl⟩ : syracuseStep 469967 = 704951) B704951
theorem B1059803 : Blo 467785 1059803 := bstep (se 1 (by rfl) ⟨794852, by rfl⟩ : syracuseStep 1059803 = 1589705) B1589705
theorem B5975005 : Blo 467785 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B469991 : Blo 467785 469991 := bstep (se 1 (by rfl) ⟨352493, by rfl⟩ : syracuseStep 469991 = 704987) B704987
theorem B6794279 : Blo 467785 6794279 := bstep (se 1 (by rfl) ⟨5095709, by rfl⟩ : syracuseStep 6794279 = 10191419) B10191419
theorem B1584251 : Blo 467785 1584251 := bstep (se 1 (by rfl) ⟨1188188, by rfl⟩ : syracuseStep 1584251 = 2376377) B2376377
theorem B1059983 : Blo 467785 1059983 := bstep (se 1 (by rfl) ⟨794987, by rfl⟩ : syracuseStep 1059983 = 1589975) B1589975
theorem B1191145 : Blo 467785 1191145 := bstep (se 2 (by rfl) ⟨446679, by rfl⟩ : syracuseStep 1191145 = 893359) B893359
theorem B1060073 : Blo 467785 1060073 := bstep (se 2 (by rfl) ⟨397527, by rfl⟩ : syracuseStep 1060073 = 795055) B795055
theorem B470303 : Blo 467785 470303 := bstep (se 1 (by rfl) ⟨352727, by rfl⟩ : syracuseStep 470303 = 705455) B705455
theorem B1060127 : Blo 467785 1060127 := bstep (se 1 (by rfl) ⟨795095, by rfl⟩ : syracuseStep 1060127 = 1590191) B1590191
theorem B470363 : Blo 467785 470363 := bstep (se 1 (by rfl) ⟨352772, by rfl⟩ : syracuseStep 470363 = 705545) B705545
theorem B470383 : Blo 467785 470383 := bstep (se 1 (by rfl) ⟨352787, by rfl⟩ : syracuseStep 470383 = 705575) B705575
theorem B34614641 : Blo 467785 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B1781129 : Blo 467785 1781129 := bstep (se 2 (by rfl) ⟨667923, by rfl⟩ : syracuseStep 1781129 = 1335847) B1335847
theorem B1584521 : Blo 467785 1584521 := bstep (se 2 (by rfl) ⟨594195, by rfl⟩ : syracuseStep 1584521 = 1188391) B1188391
theorem B1191307 : Blo 467785 1191307 := bstep (se 1 (by rfl) ⟨893480, by rfl⟩ : syracuseStep 1191307 = 1786961) B1786961
theorem B470439 : Blo 467785 470439 := bstep (se 1 (by rfl) ⟨352829, by rfl⟩ : syracuseStep 470439 = 705659) B705659
theorem B2371031 : Blo 467785 2371031 := bstep (se 1 (by rfl) ⟨1778273, by rfl⟩ : syracuseStep 2371031 = 3556547) B3556547
theorem B470523 : Blo 467785 470523 := bstep (se 1 (by rfl) ⟨352892, by rfl⟩ : syracuseStep 470523 = 705785) B705785
theorem B470591 : Blo 467785 470591 := bstep (se 1 (by rfl) ⟨352943, by rfl⟩ : syracuseStep 470591 = 705887) B705887
theorem B470599 : Blo 467785 470599 := bstep (se 1 (by rfl) ⟨352949, by rfl⟩ : syracuseStep 470599 = 705899) B705899
theorem B4533857 : Blo 467785 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B1191611 : Blo 467785 1191611 := bstep (se 1 (by rfl) ⟨893708, by rfl⟩ : syracuseStep 1191611 = 1787417) B1787417
theorem B470751 : Blo 467785 470751 := bstep (se 1 (by rfl) ⟨353063, by rfl⟩ : syracuseStep 470751 = 706127) B706127
theorem B1060649 : Blo 467785 1060649 := bstep (se 2 (by rfl) ⟨397743, by rfl⟩ : syracuseStep 1060649 = 795487) B795487
theorem B470831 : Blo 467785 470831 := bstep (se 1 (by rfl) ⟨353123, by rfl⟩ : syracuseStep 470831 = 706247) B706247
theorem B1126199 : Blo 467785 1126199 := bstep (se 1 (by rfl) ⟨844649, by rfl⟩ : syracuseStep 1126199 = 1689299) B1689299
theorem B1584953 : Blo 467785 1584953 := bstep (se 2 (by rfl) ⟨594357, by rfl⟩ : syracuseStep 1584953 = 1188715) B1188715
theorem B470939 : Blo 467785 470939 := bstep (se 1 (by rfl) ⟨353204, by rfl⟩ : syracuseStep 470939 = 706409) B706409
theorem B470991 : Blo 467785 470991 := bstep (se 1 (by rfl) ⟨353243, by rfl⟩ : syracuseStep 470991 = 706487) B706487
theorem B471015 : Blo 467785 471015 := bstep (se 1 (by rfl) ⟨353261, by rfl⟩ : syracuseStep 471015 = 706523) B706523
theorem B471327 : Blo 467785 471327 := bstep (se 1 (by rfl) ⟨353495, by rfl⟩ : syracuseStep 471327 = 706991) B706991
theorem B471387 : Blo 467785 471387 := bstep (se 1 (by rfl) ⟨353540, by rfl⟩ : syracuseStep 471387 = 707081) B707081
theorem B471407 : Blo 467785 471407 := bstep (se 1 (by rfl) ⟨353555, by rfl⟩ : syracuseStep 471407 = 707111) B707111
theorem B471463 : Blo 467785 471463 := bstep (se 1 (by rfl) ⟨353597, by rfl⟩ : syracuseStep 471463 = 707195) B707195
theorem B15249869 : Blo 467785 15249869 := bstep (se 3 (by rfl) ⟨2859350, by rfl⟩ : syracuseStep 15249869 = 5718701) B5718701
theorem B471547 : Blo 467785 471547 := bstep (se 1 (by rfl) ⟨353660, by rfl⟩ : syracuseStep 471547 = 707321) B707321
theorem B471615 : Blo 467785 471615 := bstep (se 1 (by rfl) ⟨353711, by rfl⟩ : syracuseStep 471615 = 707423) B707423
theorem B471623 : Blo 467785 471623 := bstep (se 1 (by rfl) ⟨353717, by rfl⟩ : syracuseStep 471623 = 707435) B707435
theorem B1585817 : Blo 467785 1585817 := bstep (se 2 (by rfl) ⟨594681, by rfl⟩ : syracuseStep 1585817 = 1189363) B1189363
theorem B23540441 : Blo 467785 23540441 := bstep (se 2 (by rfl) ⟨8827665, by rfl⟩ : syracuseStep 23540441 = 17655331) B17655331
theorem B471775 : Blo 467785 471775 := bstep (se 1 (by rfl) ⟨353831, by rfl⟩ : syracuseStep 471775 = 707663) B707663
theorem B2143055 : Blo 467785 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B5059421 : Blo 467785 5059421 := bstep (se 3 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 5059421 = 1897283) B1897283
theorem B1127411 : Blo 467785 1127411 := bstep (se 1 (by rfl) ⟨845558, by rfl⟩ : syracuseStep 1127411 = 1691117) B1691117
theorem B9122867 : Blo 467785 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B701735 : Blo 467785 701735 := bstep (se 1 (by rfl) ⟨526301, by rfl⟩ : syracuseStep 701735 = 1052603) B1052603
theorem B701819 : Blo 467785 701819 := bstep (se 1 (by rfl) ⟨526364, by rfl⟩ : syracuseStep 701819 = 1052729) B1052729
theorem B701945 : Blo 467785 701945 := bstep (se 2 (by rfl) ⟨263229, by rfl⟩ : syracuseStep 701945 = 526459) B526459
theorem B1193555 : Blo 467785 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B702047 : Blo 467785 702047 := bstep (se 1 (by rfl) ⟨526535, by rfl⟩ : syracuseStep 702047 = 1053071) B1053071
theorem B800519 : Blo 467785 800519 := bstep (se 1 (by rfl) ⟨600389, by rfl⟩ : syracuseStep 800519 = 1200779) B1200779
theorem B702263 : Blo 467785 702263 := bstep (se 1 (by rfl) ⟨526697, by rfl⟩ : syracuseStep 702263 = 1053395) B1053395
theorem B702569 : Blo 467785 702569 := bstep (se 2 (by rfl) ⟨263463, by rfl⟩ : syracuseStep 702569 = 526927) B526927
theorem B1587329 : Blo 467785 1587329 := bstep (se 2 (by rfl) ⟨595248, by rfl⟩ : syracuseStep 1587329 = 1190497) B1190497
theorem B1128659 : Blo 467785 1128659 := bstep (se 1 (by rfl) ⟨846494, by rfl⟩ : syracuseStep 1128659 = 1692989) B1692989
theorem B2537839 : Blo 467785 2537839 := bstep (se 1 (by rfl) ⟨1903379, by rfl⟩ : syracuseStep 2537839 = 3806759) B3806759
theorem B702887 : Blo 467785 702887 := bstep (se 1 (by rfl) ⟨527165, by rfl⟩ : syracuseStep 702887 = 1054331) B1054331
theorem B2669051 : Blo 467785 2669051 := bstep (se 1 (by rfl) ⟨2001788, by rfl⟩ : syracuseStep 2669051 = 4003577) B4003577
theorem B702971 : Blo 467785 702971 := bstep (se 1 (by rfl) ⟨527228, by rfl⟩ : syracuseStep 702971 = 1054457) B1054457
theorem B1587707 : Blo 467785 1587707 := bstep (se 1 (by rfl) ⟨1190780, by rfl⟩ : syracuseStep 1587707 = 2381561) B2381561
theorem B703097 : Blo 467785 703097 := bstep (se 2 (by rfl) ⟨263661, by rfl⟩ : syracuseStep 703097 = 527323) B527323
theorem B703151 : Blo 467785 703151 := bstep (se 1 (by rfl) ⟨527363, by rfl⟩ : syracuseStep 703151 = 1054727) B1054727
theorem B703199 : Blo 467785 703199 := bstep (se 1 (by rfl) ⟨527399, by rfl⟩ : syracuseStep 703199 = 1054799) B1054799
theorem B1588139 : Blo 467785 1588139 := bstep (se 1 (by rfl) ⟨1191104, by rfl⟩ : syracuseStep 1588139 = 2382209) B2382209
theorem B9681839 : Blo 467785 9681839 := bstep (se 1 (by rfl) ⟨7261379, by rfl⟩ : syracuseStep 9681839 = 14522759) B14522759
theorem B703463 : Blo 467785 703463 := bstep (se 1 (by rfl) ⟨527597, by rfl⟩ : syracuseStep 703463 = 1055195) B1055195
theorem B703721 : Blo 467785 703721 := bstep (se 2 (by rfl) ⟨263895, by rfl⟩ : syracuseStep 703721 = 527791) B527791
theorem B703775 : Blo 467785 703775 := bstep (se 1 (by rfl) ⟨527831, by rfl⟩ : syracuseStep 703775 = 1055663) B1055663
theorem B1686851 : Blo 467785 1686851 := bstep (se 1 (by rfl) ⟨1265138, by rfl⟩ : syracuseStep 1686851 = 2530277) B2530277
theorem B1785185 : Blo 467785 1785185 := bstep (se 2 (by rfl) ⟨669444, by rfl⟩ : syracuseStep 1785185 = 1338889) B1338889
theorem B671113 : Blo 467785 671113 := bstep (se 2 (by rfl) ⟨251667, by rfl⟩ : syracuseStep 671113 = 503335) B503335
theorem B703943 : Blo 467785 703943 := bstep (se 1 (by rfl) ⟨527957, by rfl⟩ : syracuseStep 703943 = 1055915) B1055915
theorem B1588679 : Blo 467785 1588679 := bstep (se 1 (by rfl) ⟨1191509, by rfl⟩ : syracuseStep 1588679 = 2383019) B2383019
theorem B2866747 : Blo 467785 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B1589003 : Blo 467785 1589003 := bstep (se 1 (by rfl) ⟨1191752, by rfl⟩ : syracuseStep 1589003 = 2383505) B2383505
theorem B704297 : Blo 467785 704297 := bstep (se 2 (by rfl) ⟨264111, by rfl⟩ : syracuseStep 704297 = 528223) B528223
theorem B704303 : Blo 467785 704303 := bstep (se 1 (by rfl) ⟨528227, by rfl⟩ : syracuseStep 704303 = 1056455) B1056455
theorem B1589273 : Blo 467785 1589273 := bstep (se 2 (by rfl) ⟨595977, by rfl⟩ : syracuseStep 1589273 = 1191955) B1191955
theorem B2375891 : Blo 467785 2375891 := bstep (se 1 (by rfl) ⟨1781918, by rfl⟩ : syracuseStep 2375891 = 3563837) B3563837
theorem B704777 : Blo 467785 704777 := bstep (se 2 (by rfl) ⟨264291, by rfl⟩ : syracuseStep 704777 = 528583) B528583
theorem B1425737 : Blo 467785 1425737 := bstep (se 2 (by rfl) ⟨534651, by rfl⟩ : syracuseStep 1425737 = 1069303) B1069303
theorem B30458213 : Blo 467785 30458213 := bstep (se 4 (by rfl) ⟨2855457, by rfl⟩ : syracuseStep 30458213 = 5710915) B5710915
theorem B704879 : Blo 467785 704879 := bstep (se 1 (by rfl) ⟨528659, by rfl⟩ : syracuseStep 704879 = 1057319) B1057319
theorem B1130927 : Blo 467785 1130927 := bstep (se 1 (by rfl) ⟨848195, by rfl⟩ : syracuseStep 1130927 = 1696391) B1696391
theorem B999955 : Blo 467785 999955 := bstep (se 1 (by rfl) ⟨749966, by rfl⟩ : syracuseStep 999955 = 1499933) B1499933
theorem B705095 : Blo 467785 705095 := bstep (se 1 (by rfl) ⟨528821, by rfl⟩ : syracuseStep 705095 = 1057643) B1057643
theorem B705131 : Blo 467785 705131 := bstep (se 1 (by rfl) ⟨528848, by rfl⟩ : syracuseStep 705131 = 1057697) B1057697
theorem B12829319 : Blo 467785 12829319 := bstep (se 1 (by rfl) ⟨9621989, by rfl⟩ : syracuseStep 12829319 = 19243979) B19243979
theorem B705359 : Blo 467785 705359 := bstep (se 1 (by rfl) ⟨529019, by rfl⟩ : syracuseStep 705359 = 1058039) B1058039
theorem B6800273 : Blo 467785 6800273 := bstep (se 2 (by rfl) ⟨2550102, by rfl⟩ : syracuseStep 6800273 = 5100205) B5100205
theorem B5129153 : Blo 467785 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B2540483 : Blo 467785 2540483 := bstep (se 1 (by rfl) ⟨1905362, by rfl⟩ : syracuseStep 2540483 = 3810725) B3810725
theorem B705755 : Blo 467785 705755 := bstep (se 1 (by rfl) ⟨529316, by rfl⟩ : syracuseStep 705755 = 1058633) B1058633
theorem B1688809 : Blo 467785 1688809 := bstep (se 2 (by rfl) ⟨633303, by rfl⟩ : syracuseStep 1688809 = 1266607) B1266607
theorem B1590515 : Blo 467785 1590515 := bstep (se 1 (by rfl) ⟨1192886, by rfl⟩ : syracuseStep 1590515 = 2385773) B2385773
theorem B1787129 : Blo 467785 1787129 := bstep (se 2 (by rfl) ⟨670173, by rfl⟩ : syracuseStep 1787129 = 1340347) B1340347
theorem B1590623 : Blo 467785 1590623 := bstep (se 1 (by rfl) ⟨1192967, by rfl⟩ : syracuseStep 1590623 = 2385935) B2385935
theorem B705929 : Blo 467785 705929 := bstep (se 2 (by rfl) ⟨264723, by rfl⟩ : syracuseStep 705929 = 529447) B529447
theorem B25740989 : Blo 467785 25740989 := bstep (se 3 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 25740989 = 9652871) B9652871
theorem B706283 : Blo 467785 706283 := bstep (se 1 (by rfl) ⟨529712, by rfl⟩ : syracuseStep 706283 = 1059425) B1059425
theorem B706511 : Blo 467785 706511 := bstep (se 1 (by rfl) ⟨529883, by rfl⟩ : syracuseStep 706511 = 1059767) B1059767
theorem B13551745 : Blo 467785 13551745 := bstep (se 2 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 13551745 = 10163809) B10163809
theorem B1001801 : Blo 467785 1001801 := bstep (se 2 (by rfl) ⟨375675, by rfl⟩ : syracuseStep 1001801 = 751351) B751351
theorem B706907 : Blo 467785 706907 := bstep (se 1 (by rfl) ⟨530180, by rfl⟩ : syracuseStep 706907 = 1060361) B1060361
theorem B2673107 : Blo 467785 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B707135 : Blo 467785 707135 := bstep (se 1 (by rfl) ⟨530351, by rfl⟩ : syracuseStep 707135 = 1060703) B1060703
theorem B1133119 : Blo 467785 1133119 := bstep (se 1 (by rfl) ⟨849839, by rfl⟩ : syracuseStep 1133119 = 1699679) B1699679
theorem B1002091 : Blo 467785 1002091 := bstep (se 1 (by rfl) ⟨751568, by rfl⟩ : syracuseStep 1002091 = 1503137) B1503137
theorem B707255 : Blo 467785 707255 := bstep (se 1 (by rfl) ⟨530441, by rfl⟩ : syracuseStep 707255 = 1060883) B1060883
theorem B1592189 : Blo 467785 1592189 := bstep (se 3 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 1592189 = 597071) B597071
theorem B707483 : Blo 467785 707483 := bstep (se 1 (by rfl) ⟨530612, by rfl⟩ : syracuseStep 707483 = 1061225) B1061225
theorem B4017761 : Blo 467785 4017761 := bstep (se 2 (by rfl) ⟨1506660, by rfl⟩ : syracuseStep 4017761 = 3013321) B3013321
theorem B3395843 : Blo 467785 3395843 := bstep (se 1 (by rfl) ⟨2546882, by rfl⟩ : syracuseStep 3395843 = 5093765) B5093765
theorem B6410771 : Blo 467785 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B1266239 : Blo 467785 1266239 := bstep (se 1 (by rfl) ⟨949679, by rfl⟩ : syracuseStep 1266239 = 1899359) B1899359
theorem B5428133 : Blo 467785 5428133 := bstep (se 4 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 5428133 = 1017775) B1017775
theorem B1070177 : Blo 467785 1070177 := bstep (se 2 (by rfl) ⟨401316, by rfl⟩ : syracuseStep 1070177 = 802633) B802633
theorem B1004987 : Blo 467785 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B8017541 : Blo 467785 8017541 := bstep (se 4 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 8017541 = 1503289) B1503289
theorem B35149463 : Blo 467785 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B17192897 : Blo 467785 17192897 := bstep (se 2 (by rfl) ⟨6447336, by rfl⟩ : syracuseStep 17192897 = 12894673) B12894673
theorem B1005833 : Blo 467785 1005833 := bstep (se 2 (by rfl) ⟨377187, by rfl⟩ : syracuseStep 1005833 = 754375) B754375
theorem B4512023 : Blo 467785 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B678395 : Blo 467785 678395 := bstep (se 1 (by rfl) ⟨508796, by rfl⟩ : syracuseStep 678395 = 1017593) B1017593
theorem B4020799 : Blo 467785 4020799 := bstep (se 1 (by rfl) ⟨3015599, by rfl⟩ : syracuseStep 4020799 = 6031199) B6031199
theorem B6085853 : Blo 467785 6085853 := bstep (se 3 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 6085853 = 2282195) B2282195
theorem B2677981 : Blo 467785 2677981 := bstep (se 3 (by rfl) ⟨502121, by rfl⟩ : syracuseStep 2677981 = 1004243) B1004243
theorem B2416339 : Blo 467785 2416339 := bstep (se 1 (by rfl) ⟨1812254, by rfl⟩ : syracuseStep 2416339 = 3624509) B3624509
theorem B1269785 : Blo 467785 1269785 := bstep (se 2 (by rfl) ⟨476169, by rfl⟩ : syracuseStep 1269785 = 952339) B952339
theorem B3793591 : Blo 467785 3793591 := bstep (se 1 (by rfl) ⟨2845193, by rfl⟩ : syracuseStep 3793591 = 5690387) B5690387
theorem B2679713 : Blo 467785 2679713 := bstep (se 2 (by rfl) ⟨1004892, by rfl⟩ : syracuseStep 2679713 = 2009785) B2009785
theorem B2384801 : Blo 467785 2384801 := bstep (se 2 (by rfl) ⟨894300, by rfl⟩ : syracuseStep 2384801 = 1788601) B1788601
theorem B5071835 : Blo 467785 5071835 := bstep (se 1 (by rfl) ⟨3803876, by rfl⟩ : syracuseStep 5071835 = 7607753) B7607753
theorem B1270909 : Blo 467785 1270909 := bstep (se 3 (by rfl) ⟨238295, by rfl⟩ : syracuseStep 1270909 = 476591) B476591
theorem B1336463 : Blo 467785 1336463 := bstep (se 1 (by rfl) ⟨1002347, by rfl⟩ : syracuseStep 1336463 = 2004695) B2004695
theorem B4056263 : Blo 467785 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B845255 : Blo 467785 845255 := bstep (se 1 (by rfl) ⟨633941, by rfl⟩ : syracuseStep 845255 = 1267883) B1267883
theorem B7956461 : Blo 467785 7956461 := bstep (se 3 (by rfl) ⟨1491836, by rfl⟩ : syracuseStep 7956461 = 2983673) B2983673
theorem B4516019 : Blo 467785 4516019 := bstep (se 1 (by rfl) ⟨3387014, by rfl⟩ : syracuseStep 4516019 = 6774029) B6774029
theorem B2681423 : Blo 467785 2681423 := bstep (se 1 (by rfl) ⟨2011067, by rfl⟩ : syracuseStep 2681423 = 4022135) B4022135
theorem B7334993 : Blo 467785 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B2387231 : Blo 467785 2387231 := bstep (se 1 (by rfl) ⟨1790423, by rfl⟩ : syracuseStep 2387231 = 3580847) B3580847
theorem B2682173 : Blo 467785 2682173 := bstep (se 3 (by rfl) ⟨502907, by rfl⟩ : syracuseStep 2682173 = 1005815) B1005815
theorem B1502803 : Blo 467785 1502803 := bstep (se 1 (by rfl) ⟨1127102, by rfl⟩ : syracuseStep 1502803 = 2254205) B2254205
theorem B9629293 : Blo 467785 9629293 := bstep (se 3 (by rfl) ⟨1805492, by rfl⟩ : syracuseStep 9629293 = 3610985) B3610985
theorem B2682881 : Blo 467785 2682881 := bstep (se 2 (by rfl) ⟨1006080, by rfl⟩ : syracuseStep 2682881 = 2012161) B2012161
theorem B4518251 : Blo 467785 4518251 := bstep (se 1 (by rfl) ⟨3388688, by rfl⟩ : syracuseStep 4518251 = 6777377) B6777377
theorem B2224691 : Blo 467785 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B4879001 : Blo 467785 4879001 := bstep (se 2 (by rfl) ⟨1829625, by rfl⟩ : syracuseStep 4879001 = 3659251) B3659251
theorem B1274543 : Blo 467785 1274543 := bstep (se 1 (by rfl) ⟨955907, by rfl⟩ : syracuseStep 1274543 = 1911815) B1911815
theorem B2683813 : Blo 467785 2683813 := bstep (se 4 (by rfl) ⟨251607, by rfl⟩ : syracuseStep 2683813 = 503215) B503215
theorem B1897411 : Blo 467785 1897411 := bstep (se 1 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 1897411 = 2846117) B2846117
theorem B2257895 : Blo 467785 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B3568697 : Blo 467785 3568697 := bstep (se 2 (by rfl) ⟨1338261, by rfl⟩ : syracuseStep 3568697 = 2676523) B2676523
theorem B4519709 : Blo 467785 4519709 := bstep (se 3 (by rfl) ⟨847445, by rfl⟩ : syracuseStep 4519709 = 1694891) B1694891
theorem B18249785 : Blo 467785 18249785 := bstep (se 2 (by rfl) ⟨6843669, by rfl⟩ : syracuseStep 18249785 = 13687339) B13687339
theorem B4291145 : Blo 467785 4291145 := bstep (se 2 (by rfl) ⟨1609179, by rfl⟩ : syracuseStep 4291145 = 3218359) B3218359
theorem B752311 : Blo 467785 752311 := bstep (se 1 (by rfl) ⟨564233, by rfl⟩ : syracuseStep 752311 = 1128467) B1128467
theorem B9043109 : Blo 467785 9043109 := bstep (se 4 (by rfl) ⟨847791, by rfl⟩ : syracuseStep 9043109 = 1695583) B1695583
theorem B4357309 : Blo 467785 4357309 := bstep (se 3 (by rfl) ⟨816995, by rfl⟩ : syracuseStep 4357309 = 1633991) B1633991
theorem B1506775 : Blo 467785 1506775 := bstep (se 1 (by rfl) ⟨1130081, by rfl⟩ : syracuseStep 1506775 = 2260163) B2260163
theorem B2686547 : Blo 467785 2686547 := bstep (se 1 (by rfl) ⟨2014910, by rfl⟩ : syracuseStep 2686547 = 4029821) B4029821
theorem B753247 : Blo 467785 753247 := bstep (se 1 (by rfl) ⟨564935, by rfl⟩ : syracuseStep 753247 = 1129871) B1129871
theorem B1343137 : Blo 467785 1343137 := bstep (se 2 (by rfl) ⟨503676, by rfl⟩ : syracuseStep 1343137 = 1007353) B1007353
theorem B950491 : Blo 467785 950491 := bstep (se 1 (by rfl) ⟨712868, by rfl⟩ : syracuseStep 950491 = 1425737) B1425737
theorem B8552879 : Blo 467785 8552879 := bstep (se 1 (by rfl) ⟨6414659, by rfl⟩ : syracuseStep 8552879 = 12829319) B12829319
theorem B9011897 : Blo 467785 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B3015805 : Blo 467785 3015805 := bstep (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) B1130927
theorem B3376637 : Blo 467785 3376637 := bstep (se 3 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 3376637 = 1266239) B1266239
theorem B526279 : Blo 467785 526279 := bstep (se 1 (by rfl) ⟨394709, by rfl⟩ : syracuseStep 526279 = 789419) B789419
theorem B526639 : Blo 467785 526639 := bstep (se 1 (by rfl) ⟨394979, by rfl⟩ : syracuseStep 526639 = 789959) B789959
theorem B2263895 : Blo 467785 2263895 := bstep (se 1 (by rfl) ⟨1697921, by rfl⟩ : syracuseStep 2263895 = 3395843) B3395843
theorem B2853805 : Blo 467785 2853805 := bstep (se 3 (by rfl) ⟨535088, by rfl⟩ : syracuseStep 2853805 = 1070177) B1070177
theorem B1510363 : Blo 467785 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B527431 : Blo 467785 527431 := bstep (se 1 (by rfl) ⟨395573, by rfl⟩ : syracuseStep 527431 = 791147) B791147
theorem B789871 : Blo 467785 789871 := bstep (se 1 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 789871 = 1184807) B1184807
theorem B1510825 : Blo 467785 1510825 := bstep (se 2 (by rfl) ⟨566559, by rfl⟩ : syracuseStep 1510825 = 1133119) B1133119
theorem B1904323 : Blo 467785 1904323 := bstep (se 1 (by rfl) ⟨1428242, by rfl⟩ : syracuseStep 1904323 = 2856485) B2856485
theorem B790249 : Blo 467785 790249 := bstep (se 2 (by rfl) ⟨296343, by rfl⟩ : syracuseStep 790249 = 592687) B592687
theorem B5345027 : Blo 467785 5345027 := bstep (se 1 (by rfl) ⟨4008770, by rfl⟩ : syracuseStep 5345027 = 8017541) B8017541
theorem B23432975 : Blo 467785 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B7966673 : Blo 467785 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B1052639 : Blo 467785 1052639 := bstep (se 1 (by rfl) ⟨789479, by rfl⟩ : syracuseStep 1052639 = 1578959) B1578959
theorem B593887 : Blo 467785 593887 := bstep (se 1 (by rfl) ⟨445415, by rfl⟩ : syracuseStep 593887 = 890831) B890831
theorem B4067347 : Blo 467785 4067347 := bstep (se 1 (by rfl) ⟨3050510, by rfl⟩ : syracuseStep 4067347 = 6101021) B6101021
theorem B790715 : Blo 467785 790715 := bstep (se 1 (by rfl) ⟨593036, by rfl⟩ : syracuseStep 790715 = 1186073) B1186073
theorem B1053287 : Blo 467785 1053287 := bstep (se 1 (by rfl) ⟨789965, by rfl⟩ : syracuseStep 1053287 = 1579931) B1579931
theorem B594535 : Blo 467785 594535 := bstep (se 1 (by rfl) ⟨445901, by rfl⟩ : syracuseStep 594535 = 891803) B891803
theorem B2134717 : Blo 467785 2134717 := bstep (se 3 (by rfl) ⟨400259, by rfl⟩ : syracuseStep 2134717 = 800519) B800519
theorem B791275 : Blo 467785 791275 := bstep (se 1 (by rfl) ⟨593456, by rfl⟩ : syracuseStep 791275 = 1186913) B1186913
theorem B2003737 : Blo 467785 2003737 := bstep (se 2 (by rfl) ⟨751401, by rfl⟩ : syracuseStep 2003737 = 1502803) B1502803
theorem B1184777 : Blo 467785 1184777 := bstep (se 2 (by rfl) ⟨444291, by rfl⟩ : syracuseStep 1184777 = 888583) B888583
theorem B1053971 : Blo 467785 1053971 := bstep (se 1 (by rfl) ⟨790478, by rfl⟩ : syracuseStep 1053971 = 1580957) B1580957
theorem B1054043 : Blo 467785 1054043 := bstep (se 1 (by rfl) ⟨790532, by rfl⟩ : syracuseStep 1054043 = 1581065) B1581065
theorem B792247 : Blo 467785 792247 := bstep (se 1 (by rfl) ⟨594185, by rfl⟩ : syracuseStep 792247 = 1188371) B1188371
theorem B595775 : Blo 467785 595775 := bstep (se 1 (by rfl) ⟨446831, by rfl⟩ : syracuseStep 595775 = 893663) B893663
theorem B530239 : Blo 467785 530239 := bstep (se 1 (by rfl) ⟨397679, by rfl⟩ : syracuseStep 530239 = 795359) B795359
theorem B1054601 : Blo 467785 1054601 := bstep (se 2 (by rfl) ⟨395475, by rfl⟩ : syracuseStep 1054601 = 790951) B790951
theorem B3381223 : Blo 467785 3381223 := bstep (se 1 (by rfl) ⟨2535917, by rfl⟩ : syracuseStep 3381223 = 5071835) B5071835
theorem B792551 : Blo 467785 792551 := bstep (se 1 (by rfl) ⟨594413, by rfl⟩ : syracuseStep 792551 = 1188827) B1188827
theorem B1579067 : Blo 467785 1579067 := bstep (se 1 (by rfl) ⟨1184300, by rfl⟩ : syracuseStep 1579067 = 2368601) B2368601
theorem B890975 : Blo 467785 890975 := bstep (se 1 (by rfl) ⟨668231, by rfl⟩ : syracuseStep 890975 = 1336463) B1336463
theorem B530527 : Blo 467785 530527 := bstep (se 1 (by rfl) ⟨397895, by rfl⟩ : syracuseStep 530527 = 795791) B795791
theorem B1054817 : Blo 467785 1054817 := bstep (se 2 (by rfl) ⟨395556, by rfl⟩ : syracuseStep 1054817 = 791113) B791113
theorem B792767 : Blo 467785 792767 := bstep (se 1 (by rfl) ⟨594575, by rfl⟩ : syracuseStep 792767 = 1189151) B1189151
theorem B1579337 : Blo 467785 1579337 := bstep (se 2 (by rfl) ⟨592251, by rfl⟩ : syracuseStep 1579337 = 1184503) B1184503
theorem B3578417 : Blo 467785 3578417 := bstep (se 2 (by rfl) ⟨1341906, by rfl⟩ : syracuseStep 3578417 = 2683813) B2683813
theorem B2529881 : Blo 467785 2529881 := bstep (se 2 (by rfl) ⟨948705, by rfl⟩ : syracuseStep 2529881 = 1897411) B1897411
theorem B1809053 : Blo 467785 1809053 := bstep (se 3 (by rfl) ⟨339197, by rfl⟩ : syracuseStep 1809053 = 678395) B678395
theorem B793435 : Blo 467785 793435 := bstep (se 1 (by rfl) ⟨595076, by rfl⟩ : syracuseStep 793435 = 1190153) B1190153
theorem B4529519 : Blo 467785 4529519 := bstep (se 1 (by rfl) ⟨3397139, by rfl⟩ : syracuseStep 4529519 = 6794279) B6794279
theorem B1056167 : Blo 467785 1056167 := bstep (se 1 (by rfl) ⟨792125, by rfl⟩ : syracuseStep 1056167 = 1584251) B1584251
theorem B23076427 : Blo 467785 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B1187419 : Blo 467785 1187419 := bstep (se 1 (by rfl) ⟨890564, by rfl⟩ : syracuseStep 1187419 = 1781129) B1781129
theorem B1056347 : Blo 467785 1056347 := bstep (se 1 (by rfl) ⟨792260, by rfl⟩ : syracuseStep 1056347 = 1584521) B1584521
theorem B1580687 : Blo 467785 1580687 := bstep (se 1 (by rfl) ⟨1185515, by rfl⟩ : syracuseStep 1580687 = 2371031) B2371031
theorem B1187561 : Blo 467785 1187561 := bstep (se 2 (by rfl) ⟨445335, by rfl⟩ : syracuseStep 1187561 = 890671) B890671
theorem B3022571 : Blo 467785 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B794407 : Blo 467785 794407 := bstep (se 1 (by rfl) ⟨595805, by rfl⟩ : syracuseStep 794407 = 1191611) B1191611
theorem B1056635 : Blo 467785 1056635 := bstep (se 1 (by rfl) ⟨792476, by rfl⟩ : syracuseStep 1056635 = 1584953) B1584953
theorem B10166579 : Blo 467785 10166579 := bstep (se 1 (by rfl) ⟨7624934, by rfl⟩ : syracuseStep 10166579 = 15249869) B15249869
theorem B1057121 : Blo 467785 1057121 := bstep (se 2 (by rfl) ⟨396420, by rfl⟩ : syracuseStep 1057121 = 792841) B792841
theorem B1483127 : Blo 467785 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B3252667 : Blo 467785 3252667 := bstep (se 1 (by rfl) ⟨2439500, by rfl⟩ : syracuseStep 3252667 = 4879001) B4879001
theorem B1057211 : Blo 467785 1057211 := bstep (se 1 (by rfl) ⟨792908, by rfl⟩ : syracuseStep 1057211 = 1585817) B1585817
theorem B3383785 : Blo 467785 3383785 := bstep (se 2 (by rfl) ⟨1268919, by rfl⟩ : syracuseStep 3383785 = 2537839) B2537839
theorem B1581821 : Blo 467785 1581821 := bstep (se 3 (by rfl) ⟨296591, by rfl⟩ : syracuseStep 1581821 = 593183) B593183
theorem B795433 : Blo 467785 795433 := bstep (se 2 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 795433 = 596575) B596575
theorem B1188665 : Blo 467785 1188665 := bstep (se 2 (by rfl) ⟨445749, by rfl⟩ : syracuseStep 1188665 = 891499) B891499
theorem B467823 : Blo 467785 467823 := bstep (se 1 (by rfl) ⟨350867, by rfl⟩ : syracuseStep 467823 = 701735) B701735
theorem B467879 : Blo 467785 467879 := bstep (se 1 (by rfl) ⟨350909, by rfl⟩ : syracuseStep 467879 = 701819) B701819
theorem B467963 : Blo 467785 467963 := bstep (se 1 (by rfl) ⟨350972, by rfl⟩ : syracuseStep 467963 = 701945) B701945
theorem B795703 : Blo 467785 795703 := bstep (se 1 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 795703 = 1193555) B1193555
theorem B468031 : Blo 467785 468031 := bstep (se 1 (by rfl) ⟨351023, by rfl⟩ : syracuseStep 468031 = 702047) B702047
theorem B468175 : Blo 467785 468175 := bstep (se 1 (by rfl) ⟨351131, by rfl⟩ : syracuseStep 468175 = 702263) B702263
theorem B12166523 : Blo 467785 12166523 := bstep (se 1 (by rfl) ⟨9124892, by rfl⟩ : syracuseStep 12166523 = 18249785) B18249785
theorem B468379 : Blo 467785 468379 := bstep (se 1 (by rfl) ⟨351284, by rfl⟩ : syracuseStep 468379 = 702569) B702569
theorem B1058219 : Blo 467785 1058219 := bstep (se 1 (by rfl) ⟨793664, by rfl⟩ : syracuseStep 1058219 = 1587329) B1587329
theorem B5809745 : Blo 467785 5809745 := bstep (se 2 (by rfl) ⟨2178654, by rfl⟩ : syracuseStep 5809745 = 4357309) B4357309
theorem B468591 : Blo 467785 468591 := bstep (se 1 (by rfl) ⟨351443, by rfl⟩ : syracuseStep 468591 = 702887) B702887
theorem B1779367 : Blo 467785 1779367 := bstep (se 1 (by rfl) ⟨1334525, by rfl⟩ : syracuseStep 1779367 = 2669051) B2669051
theorem B468647 : Blo 467785 468647 := bstep (se 1 (by rfl) ⟨351485, by rfl⟩ : syracuseStep 468647 = 702971) B702971
theorem B1058471 : Blo 467785 1058471 := bstep (se 1 (by rfl) ⟨793853, by rfl⟩ : syracuseStep 1058471 = 1587707) B1587707
theorem B2860763 : Blo 467785 2860763 := bstep (se 1 (by rfl) ⟨2145572, by rfl⟩ : syracuseStep 2860763 = 4291145) B4291145
theorem B468731 : Blo 467785 468731 := bstep (se 1 (by rfl) ⟨351548, by rfl⟩ : syracuseStep 468731 = 703097) B703097
theorem B468767 : Blo 467785 468767 := bstep (se 1 (by rfl) ⟨351575, by rfl⟩ : syracuseStep 468767 = 703151) B703151
theorem B468799 : Blo 467785 468799 := bstep (se 1 (by rfl) ⟨351599, by rfl⟩ : syracuseStep 468799 = 703199) B703199
theorem B894817 : Blo 467785 894817 := bstep (se 2 (by rfl) ⟨335556, by rfl⟩ : syracuseStep 894817 = 671113) B671113
theorem B1058759 : Blo 467785 1058759 := bstep (se 1 (by rfl) ⟨794069, by rfl⟩ : syracuseStep 1058759 = 1588139) B1588139
theorem B2009033 : Blo 467785 2009033 := bstep (se 2 (by rfl) ⟨753387, by rfl⟩ : syracuseStep 2009033 = 1506775) B1506775
theorem B468975 : Blo 467785 468975 := bstep (se 1 (by rfl) ⟨351731, by rfl⟩ : syracuseStep 468975 = 703463) B703463
theorem B469147 : Blo 467785 469147 := bstep (se 1 (by rfl) ⟨351860, by rfl⟩ : syracuseStep 469147 = 703721) B703721
theorem B469183 : Blo 467785 469183 := bstep (se 1 (by rfl) ⟨351887, by rfl⟩ : syracuseStep 469183 = 703775) B703775
theorem B1124567 : Blo 467785 1124567 := bstep (se 1 (by rfl) ⟨843425, by rfl⟩ : syracuseStep 1124567 = 1686851) B1686851
theorem B1190123 : Blo 467785 1190123 := bstep (se 1 (by rfl) ⟨892592, by rfl⟩ : syracuseStep 1190123 = 1785185) B1785185
theorem B1059065 : Blo 467785 1059065 := bstep (se 2 (by rfl) ⟨397149, by rfl⟩ : syracuseStep 1059065 = 794299) B794299
theorem B3221785 : Blo 467785 3221785 := bstep (se 2 (by rfl) ⟨1208169, by rfl⟩ : syracuseStep 3221785 = 2416339) B2416339
theorem B469295 : Blo 467785 469295 := bstep (se 1 (by rfl) ⟨351971, by rfl⟩ : syracuseStep 469295 = 703943) B703943
theorem B1059119 : Blo 467785 1059119 := bstep (se 1 (by rfl) ⟨794339, by rfl⟩ : syracuseStep 1059119 = 1588679) B1588679
theorem B1059335 : Blo 467785 1059335 := bstep (se 1 (by rfl) ⟨794501, by rfl⟩ : syracuseStep 1059335 = 1589003) B1589003
theorem B469531 : Blo 467785 469531 := bstep (se 1 (by rfl) ⟨352148, by rfl⟩ : syracuseStep 469531 = 704297) B704297
theorem B469535 : Blo 467785 469535 := bstep (se 1 (by rfl) ⟨352151, by rfl⟩ : syracuseStep 469535 = 704303) B704303
theorem B1059515 : Blo 467785 1059515 := bstep (se 1 (by rfl) ⟨794636, by rfl⟩ : syracuseStep 1059515 = 1589273) B1589273
theorem B1583927 : Blo 467785 1583927 := bstep (se 1 (by rfl) ⟨1187945, by rfl⟩ : syracuseStep 1583927 = 2375891) B2375891
theorem B469851 : Blo 467785 469851 := bstep (se 1 (by rfl) ⟨352388, by rfl⟩ : syracuseStep 469851 = 704777) B704777
theorem B469919 : Blo 467785 469919 := bstep (se 1 (by rfl) ⟨352439, by rfl⟩ : syracuseStep 469919 = 704879) B704879
theorem B470063 : Blo 467785 470063 := bstep (se 1 (by rfl) ⟨352547, by rfl⟩ : syracuseStep 470063 = 705095) B705095
theorem B470087 : Blo 467785 470087 := bstep (se 1 (by rfl) ⟨352565, by rfl⟩ : syracuseStep 470087 = 705131) B705131
theorem B470239 : Blo 467785 470239 := bstep (se 1 (by rfl) ⟨352679, by rfl⟩ : syracuseStep 470239 = 705359) B705359
theorem B4533515 : Blo 467785 4533515 := bstep (se 1 (by rfl) ⟨3400136, by rfl⟩ : syracuseStep 4533515 = 6800273) B6800273
theorem B3419435 : Blo 467785 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B470503 : Blo 467785 470503 := bstep (se 1 (by rfl) ⟨352877, by rfl⟩ : syracuseStep 470503 = 705755) B705755
theorem B1060343 : Blo 467785 1060343 := bstep (se 1 (by rfl) ⟨795257, by rfl⟩ : syracuseStep 1060343 = 1590515) B1590515
theorem B1191419 : Blo 467785 1191419 := bstep (se 1 (by rfl) ⟨893564, by rfl⟩ : syracuseStep 1191419 = 1787129) B1787129
theorem B1060415 : Blo 467785 1060415 := bstep (se 1 (by rfl) ⟨795311, by rfl⟩ : syracuseStep 1060415 = 1590623) B1590623
theorem B5058121 : Blo 467785 5058121 := bstep (se 2 (by rfl) ⟨1896795, by rfl⟩ : syracuseStep 5058121 = 3793591) B3793591
theorem B470619 : Blo 467785 470619 := bstep (se 1 (by rfl) ⟨352964, by rfl⟩ : syracuseStep 470619 = 705929) B705929
theorem B503591 : Blo 467785 503591 := bstep (se 1 (by rfl) ⟨377693, by rfl⟩ : syracuseStep 503591 = 755387) B755387
theorem B470855 : Blo 467785 470855 := bstep (se 1 (by rfl) ⟨353141, by rfl⟩ : syracuseStep 470855 = 706283) B706283
theorem B471007 : Blo 467785 471007 := bstep (se 1 (by rfl) ⟨353255, by rfl⟩ : syracuseStep 471007 = 706511) B706511
theorem B667867 : Blo 467785 667867 := bstep (se 1 (by rfl) ⟨500900, by rfl⟩ : syracuseStep 667867 = 1001801) B1001801
theorem B471271 : Blo 467785 471271 := bstep (se 1 (by rfl) ⟨353453, by rfl⟩ : syracuseStep 471271 = 706907) B706907
theorem B6435073 : Blo 467785 6435073 := bstep (se 2 (by rfl) ⟨2413152, by rfl⟩ : syracuseStep 6435073 = 4826305) B4826305
theorem B1782071 : Blo 467785 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B2666843 : Blo 467785 2666843 := bstep (se 1 (by rfl) ⟨2000132, by rfl⟩ : syracuseStep 2666843 = 4000265) B4000265
theorem B471423 : Blo 467785 471423 := bstep (se 1 (by rfl) ⟨353567, by rfl⟩ : syracuseStep 471423 = 707135) B707135
theorem B471503 : Blo 467785 471503 := bstep (se 1 (by rfl) ⟨353627, by rfl⟩ : syracuseStep 471503 = 707255) B707255
theorem B1192441 : Blo 467785 1192441 := bstep (se 2 (by rfl) ⟨447165, by rfl⟩ : syracuseStep 1192441 = 894331) B894331
theorem B1061369 : Blo 467785 1061369 := bstep (se 2 (by rfl) ⟨398013, by rfl⟩ : syracuseStep 1061369 = 796027) B796027
theorem B1061459 : Blo 467785 1061459 := bstep (se 1 (by rfl) ⟨796094, by rfl⟩ : syracuseStep 1061459 = 1592189) B1592189
theorem B471655 : Blo 467785 471655 := bstep (se 1 (by rfl) ⟨353741, by rfl⟩ : syracuseStep 471655 = 707483) B707483
theorem B668425 : Blo 467785 668425 := bstep (se 2 (by rfl) ⟨250659, by rfl⟩ : syracuseStep 668425 = 501319) B501319
theorem B1192745 : Blo 467785 1192745 := bstep (se 2 (by rfl) ⟨447279, by rfl⟩ : syracuseStep 1192745 = 894559) B894559
theorem B5714813 : Blo 467785 5714813 := bstep (se 3 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 5714813 = 2143055) B2143055
theorem B2667593 : Blo 467785 2667593 := bstep (se 2 (by rfl) ⟨1000347, by rfl⟩ : syracuseStep 2667593 = 2000695) B2000695
theorem B1586249 : Blo 467785 1586249 := bstep (se 2 (by rfl) ⟨594843, by rfl⟩ : syracuseStep 1586249 = 1189687) B1189687
theorem B2012435 : Blo 467785 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B18068993 : Blo 467785 18068993 := bstep (se 2 (by rfl) ⟨6775872, by rfl⟩ : syracuseStep 18068993 = 13551745) B13551745
theorem B702023 : Blo 467785 702023 := bstep (se 1 (by rfl) ⟨526517, by rfl⟩ : syracuseStep 702023 = 1053035) B1053035
theorem B702119 : Blo 467785 702119 := bstep (se 1 (by rfl) ⟨526589, by rfl⟩ : syracuseStep 702119 = 1053179) B1053179
theorem B4273847 : Blo 467785 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B702203 : Blo 467785 702203 := bstep (se 1 (by rfl) ⟨526652, by rfl⟩ : syracuseStep 702203 = 1053305) B1053305
theorem B702239 : Blo 467785 702239 := bstep (se 1 (by rfl) ⟨526679, by rfl⟩ : syracuseStep 702239 = 1053359) B1053359
theorem B4568879 : Blo 467785 4568879 := bstep (se 1 (by rfl) ⟨3426659, by rfl⟩ : syracuseStep 4568879 = 6853319) B6853319
theorem B702287 : Blo 467785 702287 := bstep (se 1 (by rfl) ⟨526715, by rfl⟩ : syracuseStep 702287 = 1053431) B1053431
theorem B3618755 : Blo 467785 3618755 := bstep (se 1 (by rfl) ⟨2714066, by rfl⟩ : syracuseStep 3618755 = 5428133) B5428133
theorem B702407 : Blo 467785 702407 := bstep (se 1 (by rfl) ⟨526805, by rfl⟩ : syracuseStep 702407 = 1053611) B1053611
theorem B4012325 : Blo 467785 4012325 := bstep (se 4 (by rfl) ⟨376155, by rfl⟩ : syracuseStep 4012325 = 752311) B752311
theorem B702761 : Blo 467785 702761 := bstep (se 2 (by rfl) ⟨263535, by rfl⟩ : syracuseStep 702761 = 527071) B527071
theorem B702767 : Blo 467785 702767 := bstep (se 1 (by rfl) ⟨527075, by rfl⟩ : syracuseStep 702767 = 1054151) B1054151
theorem B12204553 : Blo 467785 12204553 := bstep (se 2 (by rfl) ⟨4576707, by rfl⟩ : syracuseStep 12204553 = 9153415) B9153415
theorem B703007 : Blo 467785 703007 := bstep (se 1 (by rfl) ⟨527255, by rfl⟩ : syracuseStep 703007 = 1054511) B1054511
theorem B1587869 : Blo 467785 1587869 := bstep (se 3 (by rfl) ⟨297725, by rfl⟩ : syracuseStep 1587869 = 595451) B595451
theorem B670555 : Blo 467785 670555 := bstep (se 1 (by rfl) ⟨502916, by rfl⟩ : syracuseStep 670555 = 1005833) B1005833
theorem B703391 : Blo 467785 703391 := bstep (se 1 (by rfl) ⟨527543, by rfl⟩ : syracuseStep 703391 = 1055087) B1055087
theorem B703439 : Blo 467785 703439 := bstep (se 1 (by rfl) ⟨527579, by rfl⟩ : syracuseStep 703439 = 1055159) B1055159
theorem B2014159 : Blo 467785 2014159 := bstep (se 1 (by rfl) ⟨1510619, by rfl⟩ : syracuseStep 2014159 = 3021239) B3021239
theorem B1588193 : Blo 467785 1588193 := bstep (se 2 (by rfl) ⟨595572, by rfl⟩ : syracuseStep 1588193 = 1191145) B1191145
theorem B703529 : Blo 467785 703529 := bstep (se 2 (by rfl) ⟨263823, by rfl⟩ : syracuseStep 703529 = 527647) B527647
theorem B703535 : Blo 467785 703535 := bstep (se 1 (by rfl) ⟨527651, by rfl⟩ : syracuseStep 703535 = 1055303) B1055303
theorem B703559 : Blo 467785 703559 := bstep (se 1 (by rfl) ⟨527669, by rfl⟩ : syracuseStep 703559 = 1055339) B1055339
theorem B1588409 : Blo 467785 1588409 := bstep (se 2 (by rfl) ⟨595653, by rfl⟩ : syracuseStep 1588409 = 1191307) B1191307
theorem B8043785 : Blo 467785 8043785 := bstep (se 2 (by rfl) ⟨3016419, by rfl⟩ : syracuseStep 8043785 = 6032839) B6032839
theorem B703823 : Blo 467785 703823 := bstep (se 1 (by rfl) ⟨527867, by rfl⟩ : syracuseStep 703823 = 1055735) B1055735
theorem B703913 : Blo 467785 703913 := bstep (se 2 (by rfl) ⟨263967, by rfl⟩ : syracuseStep 703913 = 527935) B527935
theorem B704063 : Blo 467785 704063 := bstep (se 1 (by rfl) ⟨528047, by rfl⟩ : syracuseStep 704063 = 1056095) B1056095
theorem B704327 : Blo 467785 704327 := bstep (se 1 (by rfl) ⟨528245, by rfl⟩ : syracuseStep 704327 = 1056491) B1056491
theorem B704411 : Blo 467785 704411 := bstep (se 1 (by rfl) ⟨528308, by rfl⟩ : syracuseStep 704411 = 1056617) B1056617
theorem B3391627 : Blo 467785 3391627 := bstep (se 1 (by rfl) ⟨2543720, by rfl⟩ : syracuseStep 3391627 = 5087441) B5087441
theorem B704975 : Blo 467785 704975 := bstep (se 1 (by rfl) ⟨528731, by rfl⟩ : syracuseStep 704975 = 1057463) B1057463
theorem B705017 : Blo 467785 705017 := bstep (se 2 (by rfl) ⟨264381, by rfl⟩ : syracuseStep 705017 = 528763) B528763
theorem B705119 : Blo 467785 705119 := bstep (se 1 (by rfl) ⟨528839, by rfl⟩ : syracuseStep 705119 = 1057679) B1057679
theorem B1786475 : Blo 467785 1786475 := bstep (se 1 (by rfl) ⟨1339856, by rfl⟩ : syracuseStep 1786475 = 2679713) B2679713
theorem B1589867 : Blo 467785 1589867 := bstep (se 1 (by rfl) ⟨1192400, by rfl⟩ : syracuseStep 1589867 = 2384801) B2384801
theorem B2704175 : Blo 467785 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B2999197 : Blo 467785 2999197 := bstep (se 3 (by rfl) ⟨562349, by rfl⟩ : syracuseStep 2999197 = 1124699) B1124699
theorem B705599 : Blo 467785 705599 := bstep (se 1 (by rfl) ⟨529199, by rfl⟩ : syracuseStep 705599 = 1058399) B1058399
theorem B705641 : Blo 467785 705641 := bstep (se 2 (by rfl) ⟨264615, by rfl⟩ : syracuseStep 705641 = 529231) B529231
theorem B1590461 : Blo 467785 1590461 := bstep (se 3 (by rfl) ⟨298211, by rfl⟩ : syracuseStep 1590461 = 596423) B596423
theorem B705743 : Blo 467785 705743 := bstep (se 1 (by rfl) ⟨529307, by rfl⟩ : syracuseStep 705743 = 1058615) B1058615
theorem B2671967 : Blo 467785 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B705947 : Blo 467785 705947 := bstep (se 1 (by rfl) ⟨529460, by rfl⟩ : syracuseStep 705947 = 1058921) B1058921
theorem B706169 : Blo 467785 706169 := bstep (se 2 (by rfl) ⟨264813, by rfl⟩ : syracuseStep 706169 = 529627) B529627
theorem B1787615 : Blo 467785 1787615 := bstep (se 1 (by rfl) ⟨1340711, by rfl⟩ : syracuseStep 1787615 = 2681423) B2681423
theorem B706271 : Blo 467785 706271 := bstep (se 1 (by rfl) ⟨529703, by rfl⟩ : syracuseStep 706271 = 1059407) B1059407
theorem B706367 : Blo 467785 706367 := bstep (se 1 (by rfl) ⟨529775, by rfl⟩ : syracuseStep 706367 = 1059551) B1059551
theorem B3393359 : Blo 467785 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B706535 : Blo 467785 706535 := bstep (se 1 (by rfl) ⟨529901, by rfl⟩ : syracuseStep 706535 = 1059803) B1059803
theorem B706553 : Blo 467785 706553 := bstep (se 2 (by rfl) ⟨264957, by rfl⟩ : syracuseStep 706553 = 529915) B529915
theorem B706655 : Blo 467785 706655 := bstep (se 1 (by rfl) ⟨529991, by rfl⟩ : syracuseStep 706655 = 1059983) B1059983
theorem B706715 : Blo 467785 706715 := bstep (se 1 (by rfl) ⟨530036, by rfl⟩ : syracuseStep 706715 = 1060073) B1060073
theorem B706751 : Blo 467785 706751 := bstep (se 1 (by rfl) ⟨530063, by rfl⟩ : syracuseStep 706751 = 1060127) B1060127
theorem B1591487 : Blo 467785 1591487 := bstep (se 1 (by rfl) ⟨1193615, by rfl⟩ : syracuseStep 1591487 = 2387231) B2387231
theorem B1788115 : Blo 467785 1788115 := bstep (se 1 (by rfl) ⟨1341086, by rfl⟩ : syracuseStep 1788115 = 2682173) B2682173
theorem B706793 : Blo 467785 706793 := bstep (se 2 (by rfl) ⟨265047, by rfl⟩ : syracuseStep 706793 = 530095) B530095
theorem B707099 : Blo 467785 707099 := bstep (se 1 (by rfl) ⟨530324, by rfl⟩ : syracuseStep 707099 = 1060649) B1060649
theorem B707177 : Blo 467785 707177 := bstep (se 2 (by rfl) ⟨265191, by rfl⟩ : syracuseStep 707177 = 530383) B530383
theorem B1788587 : Blo 467785 1788587 := bstep (se 1 (by rfl) ⟨1341440, by rfl⟩ : syracuseStep 1788587 = 2682881) B2682881
theorem B6081911 : Blo 467785 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B2379131 : Blo 467785 2379131 := bstep (se 1 (by rfl) ⟨1784348, by rfl⟩ : syracuseStep 2379131 = 3568697) B3568697
theorem B5361065 : Blo 467785 5361065 := bstep (se 2 (by rfl) ⟨2010399, by rfl⟩ : syracuseStep 5361065 = 4020799) B4020799
theorem B3822329 : Blo 467785 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B1004329 : Blo 467785 1004329 := bstep (se 2 (by rfl) ⟨376623, by rfl⟩ : syracuseStep 1004329 = 753247) B753247
theorem B1790849 : Blo 467785 1790849 := bstep (se 2 (by rfl) ⟨671568, by rfl⟩ : syracuseStep 1790849 = 1343137) B1343137
theorem B1791031 : Blo 467785 1791031 := bstep (se 1 (by rfl) ⟨1343273, by rfl⟩ : syracuseStep 1791031 = 2686547) B2686547
theorem B20305475 : Blo 467785 20305475 := bstep (se 1 (by rfl) ⟨15229106, by rfl⟩ : syracuseStep 20305475 = 30458213) B30458213
theorem B1267451 : Blo 467785 1267451 := bstep (se 1 (by rfl) ⟨950588, by rfl⟩ : syracuseStep 1267451 = 1901177) B1901177
theorem B1693655 : Blo 467785 1693655 := bstep (se 1 (by rfl) ⟨1270241, by rfl⟩ : syracuseStep 1693655 = 2540483) B2540483
theorem B1333273 : Blo 467785 1333273 := bstep (se 2 (by rfl) ⟨499977, by rfl⟩ : syracuseStep 1333273 = 999955) B999955
theorem B1333331 : Blo 467785 1333331 := bstep (se 1 (by rfl) ⟨999998, by rfl⟩ : syracuseStep 1333331 = 1999997) B1999997
theorem B2709883 : Blo 467785 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B17160659 : Blo 467785 17160659 := bstep (se 1 (by rfl) ⟨12870494, by rfl⟩ : syracuseStep 17160659 = 25740989) B25740989
theorem B2251745 : Blo 467785 2251745 := bstep (se 2 (by rfl) ⟨844404, by rfl⟩ : syracuseStep 2251745 = 1688809) B1688809
theorem B62774509 : Blo 467785 62774509 := bstep (se 3 (by rfl) ⟨11770220, by rfl⟩ : syracuseStep 62774509 = 23540441) B23540441
theorem B2678507 : Blo 467785 2678507 := bstep (se 1 (by rfl) ⟨2008880, by rfl⟩ : syracuseStep 2678507 = 4017761) B4017761
theorem B6021053 : Blo 467785 6021053 := bstep (se 3 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 6021053 = 2257895) B2257895
theorem B1532039 : Blo 467785 1532039 := bstep (se 1 (by rfl) ⟨1149029, by rfl⟩ : syracuseStep 1532039 = 2298059) B2298059
theorem B8577413 : Blo 467785 8577413 := bstep (se 4 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 8577413 = 1608265) B1608265
theorem B2384315 : Blo 467785 2384315 := bstep (se 1 (by rfl) ⟨1788236, by rfl⟩ : syracuseStep 2384315 = 3576473) B3576473
theorem B1336121 : Blo 467785 1336121 := bstep (se 2 (by rfl) ⟨501045, by rfl⟩ : syracuseStep 1336121 = 1002091) B1002091
theorem B2679965 : Blo 467785 2679965 := bstep (se 3 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 2679965 = 1004987) B1004987
theorem B2254013 : Blo 467785 2254013 := bstep (se 3 (by rfl) ⟨422627, by rfl⟩ : syracuseStep 2254013 = 845255) B845255
theorem B11461931 : Blo 467785 11461931 := bstep (se 1 (by rfl) ⟨8596448, by rfl⟩ : syracuseStep 11461931 = 17192897) B17192897
theorem B3008015 : Blo 467785 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B12839057 : Blo 467785 12839057 := bstep (se 2 (by rfl) ⟨4814646, by rfl⟩ : syracuseStep 12839057 = 9629293) B9629293
theorem B4057235 : Blo 467785 4057235 := bstep (se 1 (by rfl) ⟨3042926, by rfl⟩ : syracuseStep 4057235 = 6085853) B6085853
theorem B1337579 : Blo 467785 1337579 := bstep (se 1 (by rfl) ⟨1003184, by rfl⟩ : syracuseStep 1337579 = 2006369) B2006369
theorem B1337647 : Blo 467785 1337647 := bstep (se 1 (by rfl) ⟨1003235, by rfl⟩ : syracuseStep 1337647 = 2006471) B2006471
theorem B846523 : Blo 467785 846523 := bstep (se 1 (by rfl) ⟨634892, by rfl⟩ : syracuseStep 846523 = 1269785) B1269785
theorem B2386907 : Blo 467785 2386907 := bstep (se 1 (by rfl) ⟨1790180, by rfl⟩ : syracuseStep 2386907 = 3580361) B3580361
theorem B3009757 : Blo 467785 3009757 := bstep (se 3 (by rfl) ⟨564329, by rfl⟩ : syracuseStep 3009757 = 1128659) B1128659
theorem B6778181 : Blo 467785 6778181 := bstep (se 4 (by rfl) ⟨635454, by rfl⟩ : syracuseStep 6778181 = 1270909) B1270909
theorem B1339037 : Blo 467785 1339037 := bstep (se 3 (by rfl) ⟨251069, by rfl⟩ : syracuseStep 1339037 = 502139) B502139
theorem B4026131 : Blo 467785 4026131 := bstep (se 1 (by rfl) ⟨3019598, by rfl⟩ : syracuseStep 4026131 = 6039197) B6039197
theorem B2256779 : Blo 467785 2256779 := bstep (se 1 (by rfl) ⟨1692584, by rfl⟩ : syracuseStep 2256779 = 3385169) B3385169
theorem B1339379 : Blo 467785 1339379 := bstep (se 1 (by rfl) ⟨1004534, by rfl⟩ : syracuseStep 1339379 = 2009069) B2009069
theorem B5304307 : Blo 467785 5304307 := bstep (se 1 (by rfl) ⟨3978230, by rfl⟩ : syracuseStep 5304307 = 7956461) B7956461
theorem B3010679 : Blo 467785 3010679 := bstep (se 1 (by rfl) ⟨2258009, by rfl⟩ : syracuseStep 3010679 = 4516019) B4516019
theorem B9007433 : Blo 467785 9007433 := bstep (se 2 (by rfl) ⟨3377787, by rfl⟩ : syracuseStep 9007433 = 6755575) B6755575
theorem B750377 : Blo 467785 750377 := bstep (se 2 (by rfl) ⟨281391, by rfl⟩ : syracuseStep 750377 = 562783) B562783
theorem B750665 : Blo 467785 750665 := bstep (se 2 (by rfl) ⟨281499, by rfl⟩ : syracuseStep 750665 = 562999) B562999
theorem B750799 : Blo 467785 750799 := bstep (se 1 (by rfl) ⟨563099, by rfl⟩ : syracuseStep 750799 = 1126199) B1126199
theorem B19559981 : Blo 467785 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B3012167 : Blo 467785 3012167 := bstep (se 1 (by rfl) ⟨2259125, by rfl⟩ : syracuseStep 3012167 = 4518251) B4518251
theorem B849695 : Blo 467785 849695 := bstep (se 1 (by rfl) ⟨637271, by rfl⟩ : syracuseStep 849695 = 1274543) B1274543
theorem B3372947 : Blo 467785 3372947 := bstep (se 1 (by rfl) ⟨2529710, by rfl⟩ : syracuseStep 3372947 = 5059421) B5059421
theorem B751607 : Blo 467785 751607 := bstep (se 1 (by rfl) ⟨563705, by rfl⟩ : syracuseStep 751607 = 1127411) B1127411
theorem B3013139 : Blo 467785 3013139 := bstep (se 1 (by rfl) ⟨2259854, by rfl⟩ : syracuseStep 3013139 = 4519709) B4519709
theorem B3570641 : Blo 467785 3570641 := bstep (se 2 (by rfl) ⟨1338990, by rfl⟩ : syracuseStep 3570641 = 2677981) B2677981
theorem B13499621 : Blo 467785 13499621 := bstep (se 4 (by rfl) ⟨1265589, by rfl⟩ : syracuseStep 13499621 = 2531179) B2531179
theorem B6454559 : Blo 467785 6454559 := bstep (se 1 (by rfl) ⟨4840919, by rfl⟩ : syracuseStep 6454559 = 9681839) B9681839
theorem B6028739 : Blo 467785 6028739 := bstep (se 1 (by rfl) ⟨4521554, by rfl⟩ : syracuseStep 6028739 = 9043109) B9043109
theorem B5340653 : Blo 467785 5340653 := bstep (se 3 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 5340653 = 2002745) B2002745
theorem B4522169 : Blo 467785 4522169 := bstep (se 2 (by rfl) ⟨1695813, by rfl⟩ : syracuseStep 4522169 = 3391627) B3391627
theorem B5701919 : Blo 467785 5701919 := bstep (se 1 (by rfl) ⟨4276439, by rfl⟩ : syracuseStep 5701919 = 8552879) B8552879
theorem B1802783 : Blo 467785 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B3998929 : Blo 467785 3998929 := bstep (se 2 (by rfl) ⟨1499598, by rfl⟩ : syracuseStep 3998929 = 2999197) B2999197
theorem B2262239 : Blo 467785 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B1509263 : Blo 467785 1509263 := bstep (se 1 (by rfl) ⟨1131947, by rfl⟩ : syracuseStep 1509263 = 2263895) B2263895
theorem B10192877 : Blo 467785 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B3574043 : Blo 467785 3574043 := bstep (se 1 (by rfl) ⟨2680532, by rfl⟩ : syracuseStep 3574043 = 5361065) B5361065
theorem B5311115 : Blo 467785 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B527143 : Blo 467785 527143 := bstep (se 1 (by rfl) ⟨395357, by rfl⟩ : syracuseStep 527143 = 790715) B790715
theorem B2001773 : Blo 467785 2001773 := bstep (se 3 (by rfl) ⟨375332, by rfl⟩ : syracuseStep 2001773 = 750665) B750665
theorem B4295713 : Blo 467785 4295713 := bstep (se 2 (by rfl) ⟨1610892, by rfl⟩ : syracuseStep 4295713 = 3221785) B3221785
theorem B789851 : Blo 467785 789851 := bstep (se 1 (by rfl) ⟨592388, by rfl⟩ : syracuseStep 789851 = 1184777) B1184777
theorem B13536983 : Blo 467785 13536983 := bstep (se 1 (by rfl) ⟨10152737, by rfl⟩ : syracuseStep 13536983 = 20305475) B20305475
theorem B3805073 : Blo 467785 3805073 := bstep (se 2 (by rfl) ⟨1426902, by rfl⟩ : syracuseStep 3805073 = 2853805) B2853805
theorem B528367 : Blo 467785 528367 := bstep (se 1 (by rfl) ⟨396275, by rfl⟩ : syracuseStep 528367 = 792551) B792551
theorem B1052711 : Blo 467785 1052711 := bstep (se 1 (by rfl) ⟨789533, by rfl⟩ : syracuseStep 1052711 = 1579067) B1579067
theorem B888887 : Blo 467785 888887 := bstep (se 1 (by rfl) ⟨666665, by rfl⟩ : syracuseStep 888887 = 1333331) B1333331
theorem B593983 : Blo 467785 593983 := bstep (se 1 (by rfl) ⟨445487, by rfl⟩ : syracuseStep 593983 = 890975) B890975
theorem B528511 : Blo 467785 528511 := bstep (se 1 (by rfl) ⟨396383, by rfl⟩ : syracuseStep 528511 = 792767) B792767
theorem B1052891 : Blo 467785 1052891 := bstep (se 1 (by rfl) ⟨789668, by rfl⟩ : syracuseStep 1052891 = 1579337) B1579337
theorem B11440439 : Blo 467785 11440439 := bstep (se 1 (by rfl) ⟨8580329, by rfl⟩ : syracuseStep 11440439 = 17160659) B17160659
theorem B1053161 : Blo 467785 1053161 := bstep (se 2 (by rfl) ⟨394935, by rfl⟩ : syracuseStep 1053161 = 789871) B789871
theorem B2265853 : Blo 467785 2265853 := bstep (se 3 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 2265853 = 849695) B849695
theorem B3019679 : Blo 467785 3019679 := bstep (se 1 (by rfl) ⟨2264759, by rfl⟩ : syracuseStep 3019679 = 4529519) B4529519
theorem B1053665 : Blo 467785 1053665 := bstep (se 2 (by rfl) ⟨395124, by rfl⟩ : syracuseStep 1053665 = 790249) B790249
theorem B1053791 : Blo 467785 1053791 := bstep (se 1 (by rfl) ⟨790343, by rfl⟩ : syracuseStep 1053791 = 1580687) B1580687
theorem B791707 : Blo 467785 791707 := bstep (se 1 (by rfl) ⟨593780, by rfl⟩ : syracuseStep 791707 = 1187561) B1187561
theorem B791849 : Blo 467785 791849 := bstep (se 2 (by rfl) ⟨296943, by rfl⟩ : syracuseStep 791849 = 593887) B593887
theorem B988751 : Blo 467785 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B890489 : Blo 467785 890489 := bstep (se 2 (by rfl) ⟨333933, by rfl⟩ : syracuseStep 890489 = 667867) B667867
theorem B1054547 : Blo 467785 1054547 := bstep (se 1 (by rfl) ⟨790910, by rfl⟩ : syracuseStep 1054547 = 1581821) B1581821
theorem B890747 : Blo 467785 890747 := bstep (se 1 (by rfl) ⟨668060, by rfl⟩ : syracuseStep 890747 = 1336121) B1336121
theorem B792443 : Blo 467785 792443 := bstep (se 1 (by rfl) ⟨594332, by rfl⟩ : syracuseStep 792443 = 1188665) B1188665
theorem B792713 : Blo 467785 792713 := bstep (se 2 (by rfl) ⟨297267, by rfl⟩ : syracuseStep 792713 = 594535) B594535
theorem B7641287 : Blo 467785 7641287 := bstep (se 1 (by rfl) ⟨5730965, by rfl⟩ : syracuseStep 7641287 = 11461931) B11461931
theorem B1055033 : Blo 467785 1055033 := bstep (se 2 (by rfl) ⟨395637, by rfl⟩ : syracuseStep 1055033 = 791275) B791275
theorem B2005343 : Blo 467785 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B891233 : Blo 467785 891233 := bstep (se 2 (by rfl) ⟨334212, by rfl⟩ : syracuseStep 891233 = 668425) B668425
theorem B4004261 : Blo 467785 4004261 := bstep (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) B750799
theorem B8035037 : Blo 467785 8035037 := bstep (se 3 (by rfl) ⟨1506569, by rfl⟩ : syracuseStep 8035037 = 3013139) B3013139
theorem B8559371 : Blo 467785 8559371 := bstep (se 1 (by rfl) ⟨6419528, by rfl⟩ : syracuseStep 8559371 = 12839057) B12839057
theorem B891719 : Blo 467785 891719 := bstep (se 1 (by rfl) ⟨668789, by rfl⟩ : syracuseStep 891719 = 1337579) B1337579
theorem B793415 : Blo 467785 793415 := bstep (se 1 (by rfl) ⟨595061, by rfl⟩ : syracuseStep 793415 = 1190123) B1190123
theorem B1055951 : Blo 467785 1055951 := bstep (se 1 (by rfl) ⟨791963, by rfl⟩ : syracuseStep 1055951 = 1583927) B1583927
theorem B3022343 : Blo 467785 3022343 := bstep (se 1 (by rfl) ⟨2266757, by rfl⟩ : syracuseStep 3022343 = 4533515) B4533515
theorem B1056329 : Blo 467785 1056329 := bstep (se 2 (by rfl) ⟨396123, by rfl⟩ : syracuseStep 1056329 = 792247) B792247
theorem B794279 : Blo 467785 794279 := bstep (se 1 (by rfl) ⟨595709, by rfl⟩ : syracuseStep 794279 = 1191419) B1191419
theorem B892691 : Blo 467785 892691 := bstep (se 1 (by rfl) ⟨669518, by rfl⟩ : syracuseStep 892691 = 1339037) B1339037
theorem B892919 : Blo 467785 892919 := bstep (se 1 (by rfl) ⟨669689, by rfl⟩ : syracuseStep 892919 = 1339379) B1339379
theorem B1777697 : Blo 467785 1777697 := bstep (se 2 (by rfl) ⟨666636, by rfl⟩ : syracuseStep 1777697 = 1333273) B1333273
theorem B2007119 : Blo 467785 2007119 := bstep (se 1 (by rfl) ⟨1505339, by rfl⟩ : syracuseStep 2007119 = 3010679) B3010679
theorem B1188047 : Blo 467785 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B6004955 : Blo 467785 6004955 := bstep (se 1 (by rfl) ⟨4503716, by rfl⟩ : syracuseStep 6004955 = 9007433) B9007433
theorem B1777895 : Blo 467785 1777895 := bstep (se 1 (by rfl) ⟨1333421, by rfl⟩ : syracuseStep 1777895 = 2666843) B2666843
theorem B3613177 : Blo 467785 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B500251 : Blo 467785 500251 := bstep (se 1 (by rfl) ⟨375188, by rfl⟩ : syracuseStep 500251 = 750377) B750377
theorem B795163 : Blo 467785 795163 := bstep (se 1 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 795163 = 1192745) B1192745
theorem B3809875 : Blo 467785 3809875 := bstep (se 1 (by rfl) ⟨2857406, by rfl⟩ : syracuseStep 3809875 = 5714813) B5714813
theorem B1778395 : Blo 467785 1778395 := bstep (se 1 (by rfl) ⟨1333796, by rfl⟩ : syracuseStep 1778395 = 2667593) B2667593
theorem B1057499 : Blo 467785 1057499 := bstep (se 1 (by rfl) ⟨793124, by rfl⟩ : syracuseStep 1057499 = 1586249) B1586249
theorem B9118493 : Blo 467785 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B468015 : Blo 467785 468015 := bstep (se 1 (by rfl) ⟨351011, by rfl⟩ : syracuseStep 468015 = 702023) B702023
theorem B2008111 : Blo 467785 2008111 := bstep (se 1 (by rfl) ⟨1506083, by rfl⟩ : syracuseStep 2008111 = 3012167) B3012167
theorem B468079 : Blo 467785 468079 := bstep (se 1 (by rfl) ⟨351059, by rfl⟩ : syracuseStep 468079 = 702119) B702119
theorem B894073 : Blo 467785 894073 := bstep (se 2 (by rfl) ⟨335277, by rfl⟩ : syracuseStep 894073 = 670555) B670555
theorem B1057913 : Blo 467785 1057913 := bstep (se 2 (by rfl) ⟨396717, by rfl⟩ : syracuseStep 1057913 = 793435) B793435
theorem B468135 : Blo 467785 468135 := bstep (se 1 (by rfl) ⟨351101, by rfl⟩ : syracuseStep 468135 = 702203) B702203
theorem B468159 : Blo 467785 468159 := bstep (se 1 (by rfl) ⟨351119, by rfl⟩ : syracuseStep 468159 = 702239) B702239
theorem B468191 : Blo 467785 468191 := bstep (se 1 (by rfl) ⟨351143, by rfl⟩ : syracuseStep 468191 = 702287) B702287
theorem B468271 : Blo 467785 468271 := bstep (se 1 (by rfl) ⟨351203, by rfl⟩ : syracuseStep 468271 = 702407) B702407
theorem B501071 : Blo 467785 501071 := bstep (se 1 (by rfl) ⟨375803, by rfl⟩ : syracuseStep 501071 = 751607) B751607
theorem B468507 : Blo 467785 468507 := bstep (se 1 (by rfl) ⟨351380, by rfl⟩ : syracuseStep 468507 = 702761) B702761
theorem B468511 : Blo 467785 468511 := bstep (se 1 (by rfl) ⟨351383, by rfl⟩ : syracuseStep 468511 = 702767) B702767
theorem B83699345 : Blo 467785 83699345 := bstep (se 2 (by rfl) ⟨31387254, by rfl⟩ : syracuseStep 83699345 = 62774509) B62774509
theorem B468671 : Blo 467785 468671 := bstep (se 1 (by rfl) ⟨351503, by rfl⟩ : syracuseStep 468671 = 703007) B703007
theorem B1058579 : Blo 467785 1058579 := bstep (se 1 (by rfl) ⟨793934, by rfl⟩ : syracuseStep 1058579 = 1587869) B1587869
theorem B468927 : Blo 467785 468927 := bstep (se 1 (by rfl) ⟨351695, by rfl⟩ : syracuseStep 468927 = 703391) B703391
theorem B468959 : Blo 467785 468959 := bstep (se 1 (by rfl) ⟨351719, by rfl⟩ : syracuseStep 468959 = 703439) B703439
theorem B1058795 : Blo 467785 1058795 := bstep (se 1 (by rfl) ⟨794096, by rfl⟩ : syracuseStep 1058795 = 1588193) B1588193
theorem B469019 : Blo 467785 469019 := bstep (se 1 (by rfl) ⟨351764, by rfl⟩ : syracuseStep 469019 = 703529) B703529
theorem B469023 : Blo 467785 469023 := bstep (se 1 (by rfl) ⟨351767, by rfl⟩ : syracuseStep 469023 = 703535) B703535
theorem B469039 : Blo 467785 469039 := bstep (se 1 (by rfl) ⟨351779, by rfl⟩ : syracuseStep 469039 = 703559) B703559
theorem B1583225 : Blo 467785 1583225 := bstep (se 2 (by rfl) ⟨593709, by rfl⟩ : syracuseStep 1583225 = 1187419) B1187419
theorem B1058939 : Blo 467785 1058939 := bstep (se 1 (by rfl) ⟨794204, by rfl⟩ : syracuseStep 1058939 = 1588409) B1588409
theorem B4303039 : Blo 467785 4303039 := bstep (se 1 (by rfl) ⟨3227279, by rfl⟩ : syracuseStep 4303039 = 6454559) B6454559
theorem B469215 : Blo 467785 469215 := bstep (se 1 (by rfl) ⟨351911, by rfl⟩ : syracuseStep 469215 = 703823) B703823
theorem B469275 : Blo 467785 469275 := bstep (se 1 (by rfl) ⟨351956, by rfl⟩ : syracuseStep 469275 = 703913) B703913
theorem B469375 : Blo 467785 469375 := bstep (se 1 (by rfl) ⟨352031, by rfl⟩ : syracuseStep 469375 = 704063) B704063
theorem B1059209 : Blo 467785 1059209 := bstep (se 2 (by rfl) ⟨397203, by rfl⟩ : syracuseStep 1059209 = 794407) B794407
theorem B469551 : Blo 467785 469551 := bstep (se 1 (by rfl) ⟨352163, by rfl⟩ : syracuseStep 469551 = 704327) B704327
theorem B469607 : Blo 467785 469607 := bstep (se 1 (by rfl) ⟨352205, by rfl⟩ : syracuseStep 469607 = 704411) B704411
theorem B469983 : Blo 467785 469983 := bstep (se 1 (by rfl) ⟨352487, by rfl⟩ : syracuseStep 469983 = 704975) B704975
theorem B470011 : Blo 467785 470011 := bstep (se 1 (by rfl) ⟨352508, by rfl⟩ : syracuseStep 470011 = 705017) B705017
theorem B470079 : Blo 467785 470079 := bstep (se 1 (by rfl) ⟨352559, by rfl⟩ : syracuseStep 470079 = 705119) B705119
theorem B1190983 : Blo 467785 1190983 := bstep (se 1 (by rfl) ⟨893237, by rfl⟩ : syracuseStep 1190983 = 1786475) B1786475
theorem B1059911 : Blo 467785 1059911 := bstep (se 1 (by rfl) ⟨794933, by rfl⟩ : syracuseStep 1059911 = 1589867) B1589867
theorem B6007931 : Blo 467785 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B470399 : Blo 467785 470399 := bstep (se 1 (by rfl) ⟨352799, by rfl⟩ : syracuseStep 470399 = 705599) B705599
theorem B470427 : Blo 467785 470427 := bstep (se 1 (by rfl) ⟨352820, by rfl⟩ : syracuseStep 470427 = 705641) B705641
theorem B1060307 : Blo 467785 1060307 := bstep (se 1 (by rfl) ⟨795230, by rfl⟩ : syracuseStep 1060307 = 1590461) B1590461
theorem B470495 : Blo 467785 470495 := bstep (se 1 (by rfl) ⟨352871, by rfl⟩ : syracuseStep 470495 = 705743) B705743
theorem B1781311 : Blo 467785 1781311 := bstep (se 1 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 1781311 = 2671967) B2671967
theorem B470631 : Blo 467785 470631 := bstep (se 1 (by rfl) ⟨352973, by rfl⟩ : syracuseStep 470631 = 705947) B705947
theorem B1060577 : Blo 467785 1060577 := bstep (se 2 (by rfl) ⟨397716, by rfl⟩ : syracuseStep 1060577 = 795433) B795433
theorem B470779 : Blo 467785 470779 := bstep (se 1 (by rfl) ⟨353084, by rfl⟩ : syracuseStep 470779 = 706169) B706169
theorem B1191743 : Blo 467785 1191743 := bstep (se 1 (by rfl) ⟨893807, by rfl⟩ : syracuseStep 1191743 = 1787615) B1787615
theorem B470847 : Blo 467785 470847 := bstep (se 1 (by rfl) ⟨353135, by rfl⟩ : syracuseStep 470847 = 706271) B706271
theorem B470911 : Blo 467785 470911 := bstep (se 1 (by rfl) ⟨353183, by rfl⟩ : syracuseStep 470911 = 706367) B706367
theorem B471023 : Blo 467785 471023 := bstep (se 1 (by rfl) ⟨353267, by rfl⟩ : syracuseStep 471023 = 706535) B706535
theorem B471035 : Blo 467785 471035 := bstep (se 1 (by rfl) ⟨353276, by rfl⟩ : syracuseStep 471035 = 706553) B706553
theorem B471103 : Blo 467785 471103 := bstep (se 1 (by rfl) ⟨353327, by rfl⟩ : syracuseStep 471103 = 706655) B706655
theorem B1060937 : Blo 467785 1060937 := bstep (se 2 (by rfl) ⟨397851, by rfl⟩ : syracuseStep 1060937 = 795703) B795703
theorem B471143 : Blo 467785 471143 := bstep (se 1 (by rfl) ⟨353357, by rfl⟩ : syracuseStep 471143 = 706715) B706715
theorem B471167 : Blo 467785 471167 := bstep (se 1 (by rfl) ⟨353375, by rfl⟩ : syracuseStep 471167 = 706751) B706751
theorem B1060991 : Blo 467785 1060991 := bstep (se 1 (by rfl) ⟨795743, by rfl⟩ : syracuseStep 1060991 = 1591487) B1591487
theorem B471195 : Blo 467785 471195 := bstep (se 1 (by rfl) ⟨353396, by rfl⟩ : syracuseStep 471195 = 706793) B706793
theorem B471399 : Blo 467785 471399 := bstep (se 1 (by rfl) ⟨353549, by rfl⟩ : syracuseStep 471399 = 707099) B707099
theorem B471451 : Blo 467785 471451 := bstep (se 1 (by rfl) ⟨353588, by rfl⟩ : syracuseStep 471451 = 707177) B707177
theorem B1192391 : Blo 467785 1192391 := bstep (se 1 (by rfl) ⟨894293, by rfl⟩ : syracuseStep 1192391 = 1788587) B1788587
theorem B2372489 : Blo 467785 2372489 := bstep (se 2 (by rfl) ⟨889683, by rfl⟩ : syracuseStep 2372489 = 1779367) B1779367
theorem B1586087 : Blo 467785 1586087 := bstep (se 1 (by rfl) ⟨1189565, by rfl⟩ : syracuseStep 1586087 = 2379131) B2379131
theorem B1193089 : Blo 467785 1193089 := bstep (se 2 (by rfl) ⟨447408, by rfl⟩ : syracuseStep 1193089 = 894817) B894817
theorem B701705 : Blo 467785 701705 := bstep (se 2 (by rfl) ⟨263139, by rfl⟩ : syracuseStep 701705 = 526279) B526279
theorem B701759 : Blo 467785 701759 := bstep (se 1 (by rfl) ⟨526319, by rfl⟩ : syracuseStep 701759 = 1052639) B1052639
theorem B702185 : Blo 467785 702185 := bstep (se 2 (by rfl) ⟨263319, by rfl⟩ : syracuseStep 702185 = 526639) B526639
theorem B1783529 : Blo 467785 1783529 := bstep (se 2 (by rfl) ⟨668823, by rfl⟩ : syracuseStep 1783529 = 1337647) B1337647
theorem B702191 : Blo 467785 702191 := bstep (se 1 (by rfl) ⟨526643, by rfl⟩ : syracuseStep 702191 = 1053287) B1053287
theorem B1193899 : Blo 467785 1193899 := bstep (se 1 (by rfl) ⟨895424, by rfl⟩ : syracuseStep 1193899 = 1790849) B1790849
theorem B702647 : Blo 467785 702647 := bstep (se 1 (by rfl) ⟨526985, by rfl⟩ : syracuseStep 702647 = 1053971) B1053971
theorem B702695 : Blo 467785 702695 := bstep (se 1 (by rfl) ⟨527021, by rfl⟩ : syracuseStep 702695 = 1054043) B1054043
theorem B1128697 : Blo 467785 1128697 := bstep (se 2 (by rfl) ⟨423261, by rfl⟩ : syracuseStep 1128697 = 846523) B846523
theorem B11385157 : Blo 467785 11385157 := bstep (se 4 (by rfl) ⟨1067358, by rfl⟩ : syracuseStep 11385157 = 2134717) B2134717
theorem B703067 : Blo 467785 703067 := bstep (se 1 (by rfl) ⟨527300, by rfl⟩ : syracuseStep 703067 = 1054601) B1054601
theorem B2013817 : Blo 467785 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B1129103 : Blo 467785 1129103 := bstep (se 1 (by rfl) ⟨846827, by rfl⟩ : syracuseStep 1129103 = 1693655) B1693655
theorem B703211 : Blo 467785 703211 := bstep (se 1 (by rfl) ⟨527408, by rfl⟩ : syracuseStep 703211 = 1054817) B1054817
theorem B703241 : Blo 467785 703241 := bstep (se 2 (by rfl) ⟨263715, by rfl⟩ : syracuseStep 703241 = 527431) B527431
theorem B4013009 : Blo 467785 4013009 := bstep (se 2 (by rfl) ⟨1504878, by rfl⟩ : syracuseStep 4013009 = 3009757) B3009757
theorem B1686587 : Blo 467785 1686587 := bstep (se 1 (by rfl) ⟨1264940, by rfl⟩ : syracuseStep 1686587 = 2529881) B2529881
theorem B2014433 : Blo 467785 2014433 := bstep (se 2 (by rfl) ⟨755412, by rfl⟩ : syracuseStep 2014433 = 1510825) B1510825
theorem B1588733 : Blo 467785 1588733 := bstep (se 3 (by rfl) ⟨297887, by rfl⟩ : syracuseStep 1588733 = 595775) B595775
theorem B2539097 : Blo 467785 2539097 := bstep (se 2 (by rfl) ⟨952161, by rfl⟩ : syracuseStep 2539097 = 1904323) B1904323
theorem B704111 : Blo 467785 704111 := bstep (se 1 (by rfl) ⟨528083, by rfl⟩ : syracuseStep 704111 = 1056167) B1056167
theorem B704231 : Blo 467785 704231 := bstep (se 1 (by rfl) ⟨528173, by rfl⟩ : syracuseStep 704231 = 1056347) B1056347
theorem B1785671 : Blo 467785 1785671 := bstep (se 1 (by rfl) ⟨1339253, by rfl⟩ : syracuseStep 1785671 = 2678507) B2678507
theorem B2015047 : Blo 467785 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B704423 : Blo 467785 704423 := bstep (se 1 (by rfl) ⟨528317, by rfl⟩ : syracuseStep 704423 = 1056635) B1056635
theorem B4014035 : Blo 467785 4014035 := bstep (se 1 (by rfl) ⟨3010526, by rfl⟩ : syracuseStep 4014035 = 6021053) B6021053
theorem B5423129 : Blo 467785 5423129 := bstep (se 2 (by rfl) ⟨2033673, by rfl⟩ : syracuseStep 5423129 = 4067347) B4067347
theorem B704747 : Blo 467785 704747 := bstep (se 1 (by rfl) ⟨528560, by rfl⟩ : syracuseStep 704747 = 1057121) B1057121
theorem B5718275 : Blo 467785 5718275 := bstep (se 1 (by rfl) ⟨4288706, by rfl⟩ : syracuseStep 5718275 = 8577413) B8577413
theorem B704807 : Blo 467785 704807 := bstep (se 1 (by rfl) ⟨528605, by rfl⟩ : syracuseStep 704807 = 1057211) B1057211
theorem B1589543 : Blo 467785 1589543 := bstep (se 1 (by rfl) ⟨1192157, by rfl⟩ : syracuseStep 1589543 = 2384315) B2384315
theorem B1589921 : Blo 467785 1589921 := bstep (se 2 (by rfl) ⟨596220, by rfl⟩ : syracuseStep 1589921 = 1192441) B1192441
theorem B1786643 : Blo 467785 1786643 := bstep (se 1 (by rfl) ⟨1339982, by rfl⟩ : syracuseStep 1786643 = 2679965) B2679965
theorem B8111015 : Blo 467785 8111015 := bstep (se 1 (by rfl) ⟨6083261, by rfl⟩ : syracuseStep 8111015 = 12166523) B12166523
theorem B705479 : Blo 467785 705479 := bstep (se 1 (by rfl) ⟨529109, by rfl⟩ : syracuseStep 705479 = 1058219) B1058219
theorem B2671649 : Blo 467785 2671649 := bstep (se 2 (by rfl) ⟨1001868, by rfl⟩ : syracuseStep 2671649 = 2003737) B2003737
theorem B705647 : Blo 467785 705647 := bstep (se 1 (by rfl) ⟨529235, by rfl⟩ : syracuseStep 705647 = 1058471) B1058471
theorem B705839 : Blo 467785 705839 := bstep (se 1 (by rfl) ⟨529379, by rfl⟩ : syracuseStep 705839 = 1058759) B1058759
theorem B2704823 : Blo 467785 2704823 := bstep (se 1 (by rfl) ⟨2028617, by rfl⟩ : syracuseStep 2704823 = 4057235) B4057235
theorem B706043 : Blo 467785 706043 := bstep (se 1 (by rfl) ⟨529532, by rfl⟩ : syracuseStep 706043 = 1059065) B1059065
theorem B706079 : Blo 467785 706079 := bstep (se 1 (by rfl) ⟨529559, by rfl⟩ : syracuseStep 706079 = 1059119) B1059119
theorem B706223 : Blo 467785 706223 := bstep (se 1 (by rfl) ⟨529667, by rfl⟩ : syracuseStep 706223 = 1059335) B1059335
theorem B706343 : Blo 467785 706343 := bstep (se 1 (by rfl) ⟨529757, by rfl⟩ : syracuseStep 706343 = 1059515) B1059515
theorem B1591271 : Blo 467785 1591271 := bstep (se 1 (by rfl) ⟨1193453, by rfl⟩ : syracuseStep 1591271 = 2386907) B2386907
theorem B706895 : Blo 467785 706895 := bstep (se 1 (by rfl) ⟨530171, by rfl⟩ : syracuseStep 706895 = 1060343) B1060343
theorem B706943 : Blo 467785 706943 := bstep (se 1 (by rfl) ⟨530207, by rfl⟩ : syracuseStep 706943 = 1060415) B1060415
theorem B706985 : Blo 467785 706985 := bstep (se 2 (by rfl) ⟨265119, by rfl⟩ : syracuseStep 706985 = 530239) B530239
theorem B4508297 : Blo 467785 4508297 := bstep (se 2 (by rfl) ⟨1690611, by rfl⟩ : syracuseStep 4508297 = 3381223) B3381223
theorem B707369 : Blo 467785 707369 := bstep (se 2 (by rfl) ⟨265263, by rfl⟩ : syracuseStep 707369 = 530527) B530527
theorem B707579 : Blo 467785 707579 := bstep (se 1 (by rfl) ⟨530684, by rfl⟩ : syracuseStep 707579 = 1061369) B1061369
theorem B707639 : Blo 467785 707639 := bstep (se 1 (by rfl) ⟨530729, by rfl⟩ : syracuseStep 707639 = 1061459) B1061459
theorem B16272737 : Blo 467785 16272737 := bstep (se 2 (by rfl) ⟨6102276, by rfl⟩ : syracuseStep 16272737 = 12204553) B12204553
theorem B12045995 : Blo 467785 12045995 := bstep (se 1 (by rfl) ⟨9034496, by rfl⟩ : syracuseStep 12045995 = 18068993) B18068993
theorem B69390229 : Blo 467785 69390229 := bstep (se 6 (by rfl) ⟨1626333, by rfl⟩ : syracuseStep 69390229 = 3252667) B3252667
theorem B2248631 : Blo 467785 2248631 := bstep (se 1 (by rfl) ⟨1686473, by rfl⟩ : syracuseStep 2248631 = 3372947) B3372947
theorem B2412503 : Blo 467785 2412503 := bstep (se 1 (by rfl) ⟨1809377, by rfl⟩ : syracuseStep 2412503 = 3618755) B3618755
theorem B2674883 : Blo 467785 2674883 := bstep (se 1 (by rfl) ⟨2006162, by rfl⟩ : syracuseStep 2674883 = 4012325) B4012325
theorem B2380427 : Blo 467785 2380427 := bstep (se 1 (by rfl) ⟨1785320, by rfl⟩ : syracuseStep 2380427 = 3570641) B3570641
theorem B8999747 : Blo 467785 8999747 := bstep (se 1 (by rfl) ⟨6749810, by rfl⟩ : syracuseStep 8999747 = 13499621) B13499621
theorem B5362523 : Blo 467785 5362523 := bstep (se 1 (by rfl) ⟨4021892, by rfl⟩ : syracuseStep 5362523 = 8043785) B8043785
theorem B4019159 : Blo 467785 4019159 := bstep (se 1 (by rfl) ⟨3014369, by rfl⟩ : syracuseStep 4019159 = 6028739) B6028739
theorem B3560435 : Blo 467785 3560435 := bstep (se 1 (by rfl) ⟨2670326, by rfl⟩ : syracuseStep 3560435 = 5340653) B5340653
theorem B6018077 : Blo 467785 6018077 := bstep (se 3 (by rfl) ⟨1128389, by rfl⟩ : syracuseStep 6018077 = 2256779) B2256779
theorem B1267321 : Blo 467785 1267321 := bstep (se 2 (by rfl) ⟨475245, by rfl⟩ : syracuseStep 1267321 = 950491) B950491
theorem B4085437 : Blo 467785 4085437 := bstep (se 3 (by rfl) ⟨766019, by rfl⟩ : syracuseStep 4085437 = 1532039) B1532039
theorem B4511713 : Blo 467785 4511713 := bstep (se 2 (by rfl) ⟨1691892, by rfl⟩ : syracuseStep 4511713 = 3383785) B3383785
theorem B2251091 : Blo 467785 2251091 := bstep (se 1 (by rfl) ⟨1688318, by rfl⟩ : syracuseStep 2251091 = 3376637) B3376637
theorem B4021073 : Blo 467785 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B4054607 : Blo 467785 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B3563351 : Blo 467785 3563351 := bstep (se 1 (by rfl) ⟨2672513, by rfl⟩ : syracuseStep 3563351 = 5345027) B5345027
theorem B15621983 : Blo 467785 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B2384153 : Blo 467785 2384153 := bstep (se 2 (by rfl) ⟨894057, by rfl⟩ : syracuseStep 2384153 = 1788115) B1788115
theorem B844967 : Blo 467785 844967 := bstep (se 1 (by rfl) ⟨633725, by rfl⟩ : syracuseStep 844967 = 1267451) B1267451
theorem B52159949 : Blo 467785 52159949 := bstep (se 3 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 52159949 = 19559981) B19559981
theorem B15492653 : Blo 467785 15492653 := bstep (se 3 (by rfl) ⟨2904872, by rfl⟩ : syracuseStep 15492653 = 5809745) B5809745
theorem B2385611 : Blo 467785 2385611 := bstep (se 1 (by rfl) ⟨1789208, by rfl⟩ : syracuseStep 2385611 = 3578417) B3578417
theorem B1206035 : Blo 467785 1206035 := bstep (se 1 (by rfl) ⟨904526, by rfl⟩ : syracuseStep 1206035 = 1809053) B1809053
theorem B7628701 : Blo 467785 7628701 := bstep (se 3 (by rfl) ⟨1430381, by rfl⟩ : syracuseStep 7628701 = 2860763) B2860763
theorem B1501163 : Blo 467785 1501163 := bstep (se 1 (by rfl) ⟨1125872, by rfl⟩ : syracuseStep 1501163 = 2251745) B2251745
theorem B6744161 : Blo 467785 6744161 := bstep (se 2 (by rfl) ⟨2529060, by rfl⟩ : syracuseStep 6744161 = 5058121) B5058121
theorem B7072409 : Blo 467785 7072409 := bstep (se 2 (by rfl) ⟨2652153, by rfl⟩ : syracuseStep 7072409 = 5304307) B5304307
theorem B6777719 : Blo 467785 6777719 := bstep (se 1 (by rfl) ⟨5083289, by rfl⟩ : syracuseStep 6777719 = 10166579) B10166579
theorem B8580097 : Blo 467785 8580097 := bstep (se 2 (by rfl) ⟨3217536, by rfl⟩ : syracuseStep 8580097 = 6435073) B6435073
theorem B1502675 : Blo 467785 1502675 := bstep (se 1 (by rfl) ⟨1127006, by rfl⟩ : syracuseStep 1502675 = 2254013) B2254013
theorem B1339105 : Blo 467785 1339105 := bstep (se 2 (by rfl) ⟨502164, by rfl⟩ : syracuseStep 1339105 = 1004329) B1004329
theorem B1339355 : Blo 467785 1339355 := bstep (se 1 (by rfl) ⟨1004516, by rfl⟩ : syracuseStep 1339355 = 2009033) B2009033
theorem B2388041 : Blo 467785 2388041 := bstep (se 2 (by rfl) ⟨895515, by rfl⟩ : syracuseStep 2388041 = 1791031) B1791031
theorem B749711 : Blo 467785 749711 := bstep (se 1 (by rfl) ⟨562283, by rfl⟩ : syracuseStep 749711 = 1124567) B1124567
theorem B4518787 : Blo 467785 4518787 := bstep (se 1 (by rfl) ⟨3389090, by rfl⟩ : syracuseStep 4518787 = 6778181) B6778181
theorem B2684087 : Blo 467785 2684087 := bstep (se 1 (by rfl) ⟨2013065, by rfl⟩ : syracuseStep 2684087 = 4026131) B4026131
theorem B1341623 : Blo 467785 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B2849231 : Blo 467785 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B3045919 : Blo 467785 3045919 := bstep (se 1 (by rfl) ⟨2284439, by rfl⟩ : syracuseStep 3045919 = 4568879) B4568879
theorem B2685545 : Blo 467785 2685545 := bstep (se 2 (by rfl) ⟨1007079, by rfl⟩ : syracuseStep 2685545 = 2014159) B2014159
theorem B30768569 : Blo 467785 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B1342909 : Blo 467785 1342909 := bstep (se 3 (by rfl) ⟨251795, by rfl⟩ : syracuseStep 1342909 = 503591) B503591
theorem B12059117 : Blo 467785 12059117 := bstep (se 3 (by rfl) ⟨2261084, by rfl⟩ : syracuseStep 12059117 = 4522169) B4522169
theorem B5407343 : Blo 467785 5407343 := bstep (se 1 (by rfl) ⟨4055507, by rfl⟩ : syracuseStep 5407343 = 8111015) B8111015
theorem B17990261 : Blo 467785 17990261 := bstep (se 5 (by rfl) ⟨843293, by rfl⟩ : syracuseStep 17990261 = 1686587) B1686587
theorem B4817569 : Blo 467785 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B15205117 : Blo 467785 15205117 := bstep (se 3 (by rfl) ⟨2850959, by rfl⟩ : syracuseStep 15205117 = 5701919) B5701919
theorem B5079833 : Blo 467785 5079833 := bstep (se 2 (by rfl) ⟨1904937, by rfl⟩ : syracuseStep 5079833 = 3809875) B3809875
theorem B1508159 : Blo 467785 1508159 := bstep (se 1 (by rfl) ⟨1131119, by rfl⟩ : syracuseStep 1508159 = 2262239) B2262239
theorem B1803215 : Blo 467785 1803215 := bstep (se 1 (by rfl) ⟨1352411, by rfl⟩ : syracuseStep 1803215 = 2704823) B2704823
theorem B3540743 : Blo 467785 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B526567 : Blo 467785 526567 := bstep (se 1 (by rfl) ⟨394925, by rfl⟩ : syracuseStep 526567 = 789851) B789851
theorem B10848491 : Blo 467785 10848491 := bstep (se 1 (by rfl) ⟨8136368, by rfl⟩ : syracuseStep 10848491 = 16272737) B16272737
theorem B8030663 : Blo 467785 8030663 := bstep (se 1 (by rfl) ⟨6022997, by rfl⟩ : syracuseStep 8030663 = 12045995) B12045995
theorem B1608335 : Blo 467785 1608335 := bstep (se 1 (by rfl) ⟨1206251, by rfl⟩ : syracuseStep 1608335 = 2412503) B2412503
theorem B592591 : Blo 467785 592591 := bstep (se 1 (by rfl) ⟨444443, by rfl⟩ : syracuseStep 592591 = 888887) B888887
theorem B5737385 : Blo 467785 5737385 := bstep (se 2 (by rfl) ⟨2151519, by rfl⟩ : syracuseStep 5737385 = 4303039) B4303039
theorem B5999831 : Blo 467785 5999831 := bstep (se 1 (by rfl) ⟨4499873, by rfl⟩ : syracuseStep 5999831 = 8999747) B8999747
theorem B3575015 : Blo 467785 3575015 := bstep (se 1 (by rfl) ⟨2681261, by rfl⟩ : syracuseStep 3575015 = 5362523) B5362523
theorem B527899 : Blo 467785 527899 := bstep (se 1 (by rfl) ⟨395924, by rfl⟩ : syracuseStep 527899 = 791849) B791849
theorem B659167 : Blo 467785 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B593659 : Blo 467785 593659 := bstep (se 1 (by rfl) ⟨445244, by rfl⟩ : syracuseStep 593659 = 890489) B890489
theorem B593831 : Blo 467785 593831 := bstep (se 1 (by rfl) ⟨445373, by rfl⟩ : syracuseStep 593831 = 890747) B890747
theorem B528295 : Blo 467785 528295 := bstep (se 1 (by rfl) ⟨396221, by rfl⟩ : syracuseStep 528295 = 792443) B792443
theorem B11440129 : Blo 467785 11440129 := bstep (se 2 (by rfl) ⟨4290048, by rfl⟩ : syracuseStep 11440129 = 8580097) B8580097
theorem B528475 : Blo 467785 528475 := bstep (se 1 (by rfl) ⟨396356, by rfl⟩ : syracuseStep 528475 = 792713) B792713
theorem B594155 : Blo 467785 594155 := bstep (se 1 (by rfl) ⟨445616, by rfl⟩ : syracuseStep 594155 = 891233) B891233
theorem B5706247 : Blo 467785 5706247 := bstep (se 1 (by rfl) ⟨4279685, by rfl⟩ : syracuseStep 5706247 = 8559371) B8559371
theorem B594479 : Blo 467785 594479 := bstep (se 1 (by rfl) ⟨445859, by rfl⟩ : syracuseStep 594479 = 891719) B891719
theorem B528943 : Blo 467785 528943 := bstep (se 1 (by rfl) ⟨396707, by rfl⟩ : syracuseStep 528943 = 793415) B793415
theorem B529519 : Blo 467785 529519 := bstep (se 1 (by rfl) ⟨397139, by rfl⟩ : syracuseStep 529519 = 794279) B794279
theorem B595127 : Blo 467785 595127 := bstep (se 1 (by rfl) ⟨446345, by rfl⟩ : syracuseStep 595127 = 892691) B892691
theorem B595279 : Blo 467785 595279 := bstep (se 1 (by rfl) ⟨446459, by rfl⟩ : syracuseStep 595279 = 892919) B892919
theorem B1185131 : Blo 467785 1185131 := bstep (se 1 (by rfl) ⟨888848, by rfl⟩ : syracuseStep 1185131 = 1777697) B1777697
theorem B791977 : Blo 467785 791977 := bstep (se 2 (by rfl) ⟨296991, by rfl⟩ : syracuseStep 791977 = 593983) B593983
theorem B792031 : Blo 467785 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B4003303 : Blo 467785 4003303 := bstep (se 1 (by rfl) ⟨3002477, by rfl⟩ : syracuseStep 4003303 = 6004955) B6004955
theorem B1185263 : Blo 467785 1185263 := bstep (se 1 (by rfl) ⟨888947, by rfl⟩ : syracuseStep 1185263 = 1777895) B1777895
theorem B563311 : Blo 467785 563311 := bstep (se 1 (by rfl) ⟨422483, by rfl⟩ : syracuseStep 563311 = 844967) B844967
theorem B34773299 : Blo 467785 34773299 := bstep (se 1 (by rfl) ⟨26079974, by rfl⟩ : syracuseStep 34773299 = 52159949) B52159949
theorem B3021137 : Blo 467785 3021137 := bstep (se 2 (by rfl) ⟨1132926, by rfl⟩ : syracuseStep 3021137 = 2265853) B2265853
theorem B10328435 : Blo 467785 10328435 := bstep (se 1 (by rfl) ⟨7746326, by rfl⟩ : syracuseStep 10328435 = 15492653) B15492653
theorem B4496107 : Blo 467785 4496107 := bstep (se 1 (by rfl) ⟨3372080, by rfl⟩ : syracuseStep 4496107 = 6744161) B6744161
theorem B1055483 : Blo 467785 1055483 := bstep (se 1 (by rfl) ⟨791612, by rfl⟩ : syracuseStep 1055483 = 1583225) B1583225
theorem B1055609 : Blo 467785 1055609 := bstep (se 2 (by rfl) ⟨395853, by rfl⟩ : syracuseStep 1055609 = 791707) B791707
theorem B4005287 : Blo 467785 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B5447249 : Blo 467785 5447249 := bstep (se 2 (by rfl) ⟨2042718, by rfl⟩ : syracuseStep 5447249 = 4085437) B4085437
theorem B794495 : Blo 467785 794495 := bstep (se 1 (by rfl) ⟨595871, by rfl⟩ : syracuseStep 794495 = 1191743) B1191743
theorem B499807 : Blo 467785 499807 := bstep (se 1 (by rfl) ⟨374855, by rfl⟩ : syracuseStep 499807 = 749711) B749711
theorem B794927 : Blo 467785 794927 := bstep (se 1 (by rfl) ⟨596195, by rfl⟩ : syracuseStep 794927 = 1192391) B1192391
theorem B15180209 : Blo 467785 15180209 := bstep (se 2 (by rfl) ⟨5692578, by rfl⟩ : syracuseStep 15180209 = 11385157) B11385157
theorem B1581659 : Blo 467785 1581659 := bstep (se 1 (by rfl) ⟨1186244, by rfl⟩ : syracuseStep 1581659 = 2372489) B2372489
theorem B1057391 : Blo 467785 1057391 := bstep (se 1 (by rfl) ⟨793043, by rfl⟩ : syracuseStep 1057391 = 1586087) B1586087
theorem B467803 : Blo 467785 467803 := bstep (se 1 (by rfl) ⟨350852, by rfl⟩ : syracuseStep 467803 = 701705) B701705
theorem B467839 : Blo 467785 467839 := bstep (se 1 (by rfl) ⟨350879, by rfl⟩ : syracuseStep 467839 = 701759) B701759
theorem B468123 : Blo 467785 468123 := bstep (se 1 (by rfl) ⟨351092, by rfl⟩ : syracuseStep 468123 = 702185) B702185
theorem B1189019 : Blo 467785 1189019 := bstep (se 1 (by rfl) ⟨891764, by rfl⟩ : syracuseStep 1189019 = 1783529) B1783529
theorem B468127 : Blo 467785 468127 := bstep (se 1 (by rfl) ⟨351095, by rfl⟩ : syracuseStep 468127 = 702191) B702191
theorem B468431 : Blo 467785 468431 := bstep (se 1 (by rfl) ⟨351323, by rfl⟩ : syracuseStep 468431 = 702647) B702647
theorem B894415 : Blo 467785 894415 := bstep (se 1 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 894415 = 1341623) B1341623
theorem B468463 : Blo 467785 468463 := bstep (se 1 (by rfl) ⟨351347, by rfl⟩ : syracuseStep 468463 = 702695) B702695
theorem B468711 : Blo 467785 468711 := bstep (se 1 (by rfl) ⟨351533, by rfl⟩ : syracuseStep 468711 = 703067) B703067
theorem B468807 : Blo 467785 468807 := bstep (se 1 (by rfl) ⟨351605, by rfl⟩ : syracuseStep 468807 = 703211) B703211
theorem B468827 : Blo 467785 468827 := bstep (se 1 (by rfl) ⟨351620, by rfl⟩ : syracuseStep 468827 = 703241) B703241
theorem B1059155 : Blo 467785 1059155 := bstep (se 1 (by rfl) ⟨794366, by rfl⟩ : syracuseStep 1059155 = 1588733) B1588733
theorem B469407 : Blo 467785 469407 := bstep (se 1 (by rfl) ⟨352055, by rfl⟩ : syracuseStep 469407 = 704111) B704111
theorem B469487 : Blo 467785 469487 := bstep (se 1 (by rfl) ⟨352115, by rfl⟩ : syracuseStep 469487 = 704231) B704231
theorem B1190447 : Blo 467785 1190447 := bstep (se 1 (by rfl) ⟨892835, by rfl⟩ : syracuseStep 1190447 = 1785671) B1785671
theorem B469615 : Blo 467785 469615 := bstep (se 1 (by rfl) ⟨352211, by rfl⟩ : syracuseStep 469615 = 704423) B704423
theorem B3615419 : Blo 467785 3615419 := bstep (se 1 (by rfl) ⟨2711564, by rfl⟩ : syracuseStep 3615419 = 5423129) B5423129
theorem B469831 : Blo 467785 469831 := bstep (se 1 (by rfl) ⟨352373, by rfl⟩ : syracuseStep 469831 = 704747) B704747
theorem B3812183 : Blo 467785 3812183 := bstep (se 1 (by rfl) ⟨2859137, by rfl⟩ : syracuseStep 3812183 = 5718275) B5718275
theorem B469871 : Blo 467785 469871 := bstep (se 1 (by rfl) ⟨352403, by rfl⟩ : syracuseStep 469871 = 704807) B704807
theorem B1059695 : Blo 467785 1059695 := bstep (se 1 (by rfl) ⟨794771, by rfl⟩ : syracuseStep 1059695 = 1589543) B1589543
theorem B5352317 : Blo 467785 5352317 := bstep (se 3 (by rfl) ⟨1003559, by rfl⟩ : syracuseStep 5352317 = 2007119) B2007119
theorem B1059947 : Blo 467785 1059947 := bstep (se 1 (by rfl) ⟨794960, by rfl⟩ : syracuseStep 1059947 = 1589921) B1589921
theorem B1191095 : Blo 467785 1191095 := bstep (se 1 (by rfl) ⟨893321, by rfl⟩ : syracuseStep 1191095 = 1786643) B1786643
theorem B470319 : Blo 467785 470319 := bstep (se 1 (by rfl) ⟨352739, by rfl⟩ : syracuseStep 470319 = 705479) B705479
theorem B1781099 : Blo 467785 1781099 := bstep (se 1 (by rfl) ⟨1335824, by rfl⟩ : syracuseStep 1781099 = 2671649) B2671649
theorem B667001 : Blo 467785 667001 := bstep (se 2 (by rfl) ⟨250125, by rfl⟩ : syracuseStep 667001 = 500251) B500251
theorem B1060217 : Blo 467785 1060217 := bstep (se 2 (by rfl) ⟨397581, by rfl⟩ : syracuseStep 1060217 = 795163) B795163
theorem B470431 : Blo 467785 470431 := bstep (se 1 (by rfl) ⟨352823, by rfl⟩ : syracuseStep 470431 = 705647) B705647
theorem B470559 : Blo 467785 470559 := bstep (se 1 (by rfl) ⟨352919, by rfl⟩ : syracuseStep 470559 = 705839) B705839
theorem B2371193 : Blo 467785 2371193 := bstep (se 2 (by rfl) ⟨889197, by rfl⟩ : syracuseStep 2371193 = 1778395) B1778395
theorem B470695 : Blo 467785 470695 := bstep (se 1 (by rfl) ⟨353021, by rfl⟩ : syracuseStep 470695 = 706043) B706043
theorem B470719 : Blo 467785 470719 := bstep (se 1 (by rfl) ⟨353039, by rfl⟩ : syracuseStep 470719 = 706079) B706079
theorem B470815 : Blo 467785 470815 := bstep (se 1 (by rfl) ⟨353111, by rfl⟩ : syracuseStep 470815 = 706223) B706223
theorem B470895 : Blo 467785 470895 := bstep (se 1 (by rfl) ⟨353171, by rfl⟩ : syracuseStep 470895 = 706343) B706343
theorem B1060847 : Blo 467785 1060847 := bstep (se 1 (by rfl) ⟨795635, by rfl⟩ : syracuseStep 1060847 = 1591271) B1591271
theorem B6795251 : Blo 467785 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B1192097 : Blo 467785 1192097 := bstep (se 2 (by rfl) ⟨447036, by rfl⟩ : syracuseStep 1192097 = 894073) B894073
theorem B471263 : Blo 467785 471263 := bstep (se 1 (by rfl) ⟨353447, by rfl⟩ : syracuseStep 471263 = 706895) B706895
theorem B471295 : Blo 467785 471295 := bstep (se 1 (by rfl) ⟨353471, by rfl⟩ : syracuseStep 471295 = 706943) B706943
theorem B471323 : Blo 467785 471323 := bstep (se 1 (by rfl) ⟨353492, by rfl⟩ : syracuseStep 471323 = 706985) B706985
theorem B471579 : Blo 467785 471579 := bstep (se 1 (by rfl) ⟨353684, by rfl⟩ : syracuseStep 471579 = 707369) B707369
theorem B471719 : Blo 467785 471719 := bstep (se 1 (by rfl) ⟨353789, by rfl⟩ : syracuseStep 471719 = 707579) B707579
theorem B471759 : Blo 467785 471759 := bstep (se 1 (by rfl) ⟨353819, by rfl⟩ : syracuseStep 471759 = 707639) B707639
theorem B9024655 : Blo 467785 9024655 := bstep (se 1 (by rfl) ⟨6768491, by rfl⟩ : syracuseStep 9024655 = 13536983) B13536983
theorem B10171601 : Blo 467785 10171601 := bstep (se 2 (by rfl) ⟨3814350, by rfl⟩ : syracuseStep 10171601 = 7628701) B7628701
theorem B2536715 : Blo 467785 2536715 := bstep (se 1 (by rfl) ⟨1902536, by rfl⟩ : syracuseStep 2536715 = 3805073) B3805073
theorem B701807 : Blo 467785 701807 := bstep (se 1 (by rfl) ⟨526355, by rfl⟩ : syracuseStep 701807 = 1052711) B1052711
theorem B1783255 : Blo 467785 1783255 := bstep (se 1 (by rfl) ⟨1337441, by rfl⟩ : syracuseStep 1783255 = 2674883) B2674883
theorem B701927 : Blo 467785 701927 := bstep (se 1 (by rfl) ⟨526445, by rfl⟩ : syracuseStep 701927 = 1052891) B1052891
theorem B702107 : Blo 467785 702107 := bstep (se 1 (by rfl) ⟨526580, by rfl⟩ : syracuseStep 702107 = 1053161) B1053161
theorem B1586951 : Blo 467785 1586951 := bstep (se 1 (by rfl) ⟨1190213, by rfl⟩ : syracuseStep 1586951 = 2380427) B2380427
theorem B2013119 : Blo 467785 2013119 := bstep (se 1 (by rfl) ⟨1509839, by rfl⟩ : syracuseStep 2013119 = 3019679) B3019679
theorem B702443 : Blo 467785 702443 := bstep (se 1 (by rfl) ⟨526832, by rfl⟩ : syracuseStep 702443 = 1053665) B1053665
theorem B2373623 : Blo 467785 2373623 := bstep (se 1 (by rfl) ⟨1780217, by rfl⟩ : syracuseStep 2373623 = 3560435) B3560435
theorem B4012051 : Blo 467785 4012051 := bstep (se 1 (by rfl) ⟨3009038, by rfl⟩ : syracuseStep 4012051 = 6018077) B6018077
theorem B702527 : Blo 467785 702527 := bstep (se 1 (by rfl) ⟨526895, by rfl⟩ : syracuseStep 702527 = 1053791) B1053791
theorem B702857 : Blo 467785 702857 := bstep (se 2 (by rfl) ⟨263571, by rfl⟩ : syracuseStep 702857 = 527143) B527143
theorem B703031 : Blo 467785 703031 := bstep (se 1 (by rfl) ⟨527273, by rfl⟩ : syracuseStep 703031 = 1054547) B1054547
theorem B1587977 : Blo 467785 1587977 := bstep (se 2 (by rfl) ⟨595491, by rfl⟩ : syracuseStep 1587977 = 1190983) B1190983
theorem B5094191 : Blo 467785 5094191 := bstep (se 1 (by rfl) ⟨3820643, by rfl⟩ : syracuseStep 5094191 = 7641287) B7641287
theorem B703355 : Blo 467785 703355 := bstep (se 1 (by rfl) ⟨527516, by rfl⟩ : syracuseStep 703355 = 1055033) B1055033
theorem B2669507 : Blo 467785 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B5356691 : Blo 467785 5356691 := bstep (se 1 (by rfl) ⟨4017518, by rfl⟩ : syracuseStep 5356691 = 8035037) B8035037
theorem B2375081 : Blo 467785 2375081 := bstep (se 2 (by rfl) ⟨890655, by rfl⟩ : syracuseStep 2375081 = 1781311) B1781311
theorem B703967 : Blo 467785 703967 := bstep (se 1 (by rfl) ⟨527975, by rfl⟩ : syracuseStep 703967 = 1055951) B1055951
theorem B1785473 : Blo 467785 1785473 := bstep (se 2 (by rfl) ⟨669552, by rfl⟩ : syracuseStep 1785473 = 1339105) B1339105
theorem B2014895 : Blo 467785 2014895 := bstep (se 1 (by rfl) ⟨1511171, by rfl⟩ : syracuseStep 2014895 = 3022343) B3022343
theorem B704219 : Blo 467785 704219 := bstep (se 1 (by rfl) ⟨528164, by rfl⟩ : syracuseStep 704219 = 1056329) B1056329
theorem B2703071 : Blo 467785 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B92520305 : Blo 467785 92520305 := bstep (se 2 (by rfl) ⟨34695114, by rfl⟩ : syracuseStep 92520305 = 69390229) B69390229
theorem B2375567 : Blo 467785 2375567 := bstep (se 1 (by rfl) ⟨1781675, by rfl⟩ : syracuseStep 2375567 = 3563351) B3563351
theorem B704489 : Blo 467785 704489 := bstep (se 2 (by rfl) ⟨264183, by rfl⟩ : syracuseStep 704489 = 528367) B528367
theorem B704681 : Blo 467785 704681 := bstep (se 2 (by rfl) ⟨264255, by rfl⟩ : syracuseStep 704681 = 528511) B528511
theorem B1589435 : Blo 467785 1589435 := bstep (se 1 (by rfl) ⟨1192076, by rfl⟩ : syracuseStep 1589435 = 2384153) B2384153
theorem B704999 : Blo 467785 704999 := bstep (se 1 (by rfl) ⟨528749, by rfl⟩ : syracuseStep 704999 = 1057499) B1057499
theorem B6078995 : Blo 467785 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B705275 : Blo 467785 705275 := bstep (se 1 (by rfl) ⟨528956, by rfl⟩ : syracuseStep 705275 = 1057913) B1057913
theorem B1590407 : Blo 467785 1590407 := bstep (se 1 (by rfl) ⟨1192805, by rfl⟩ : syracuseStep 1590407 = 2385611) B2385611
theorem B804023 : Blo 467785 804023 := bstep (se 1 (by rfl) ⟨603017, by rfl⟩ : syracuseStep 804023 = 1206035) B1206035
theorem B705719 : Blo 467785 705719 := bstep (se 1 (by rfl) ⟨529289, by rfl⟩ : syracuseStep 705719 = 1058579) B1058579
theorem B1000775 : Blo 467785 1000775 := bstep (se 1 (by rfl) ⟨750581, by rfl⟩ : syracuseStep 1000775 = 1501163) B1501163
theorem B705863 : Blo 467785 705863 := bstep (se 1 (by rfl) ⟨529397, by rfl⟩ : syracuseStep 705863 = 1058795) B1058795
theorem B705959 : Blo 467785 705959 := bstep (se 1 (by rfl) ⟨529469, by rfl⟩ : syracuseStep 705959 = 1058939) B1058939
theorem B1590785 : Blo 467785 1590785 := bstep (se 2 (by rfl) ⟨596544, by rfl⟩ : syracuseStep 1590785 = 1193089) B1193089
theorem B706139 : Blo 467785 706139 := bstep (se 1 (by rfl) ⟨529604, by rfl⟩ : syracuseStep 706139 = 1059209) B1059209
theorem B706607 : Blo 467785 706607 := bstep (se 1 (by rfl) ⟨529955, by rfl⟩ : syracuseStep 706607 = 1059911) B1059911
theorem B1689761 : Blo 467785 1689761 := bstep (se 2 (by rfl) ⟨633660, by rfl⟩ : syracuseStep 1689761 = 1267321) B1267321
theorem B1001783 : Blo 467785 1001783 := bstep (se 1 (by rfl) ⟨751337, by rfl⟩ : syracuseStep 1001783 = 1502675) B1502675
theorem B706871 : Blo 467785 706871 := bstep (se 1 (by rfl) ⟨530153, by rfl⟩ : syracuseStep 706871 = 1060307) B1060307
theorem B707051 : Blo 467785 707051 := bstep (se 1 (by rfl) ⟨530288, by rfl⟩ : syracuseStep 707051 = 1060577) B1060577
theorem B1591865 : Blo 467785 1591865 := bstep (se 2 (by rfl) ⟨596949, by rfl⟩ : syracuseStep 1591865 = 1193899) B1193899
theorem B6015617 : Blo 467785 6015617 := bstep (se 2 (by rfl) ⟨2255856, by rfl⟩ : syracuseStep 6015617 = 4511713) B4511713
theorem B707291 : Blo 467785 707291 := bstep (se 1 (by rfl) ⟨530468, by rfl⟩ : syracuseStep 707291 = 1060937) B1060937
theorem B1592027 : Blo 467785 1592027 := bstep (se 1 (by rfl) ⟨1194020, by rfl⟩ : syracuseStep 1592027 = 2388041) B2388041
theorem B707327 : Blo 467785 707327 := bstep (se 1 (by rfl) ⟨530495, by rfl⟩ : syracuseStep 707327 = 1060991) B1060991
theorem B1789391 : Blo 467785 1789391 := bstep (se 1 (by rfl) ⟨1342043, by rfl⟩ : syracuseStep 1789391 = 2684087) B2684087
theorem B1790363 : Blo 467785 1790363 := bstep (se 1 (by rfl) ⟨1342772, by rfl⟩ : syracuseStep 1790363 = 2685545) B2685545
theorem B1790545 : Blo 467785 1790545 := bstep (se 2 (by rfl) ⟨671454, by rfl⟩ : syracuseStep 1790545 = 1342909) B1342909
theorem B2675339 : Blo 467785 2675339 := bstep (se 1 (by rfl) ⟨2006504, by rfl⟩ : syracuseStep 2675339 = 4013009) B4013009
theorem B1692731 : Blo 467785 1692731 := bstep (se 1 (by rfl) ⟨1269548, by rfl⟩ : syracuseStep 1692731 = 2539097) B2539097
theorem B2676023 : Blo 467785 2676023 := bstep (se 1 (by rfl) ⟨2007017, by rfl⟩ : syracuseStep 2676023 = 4014035) B4014035
theorem B1201855 : Blo 467785 1201855 := bstep (se 1 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 1201855 = 1802783) B1802783
theorem B1006175 : Blo 467785 1006175 := bstep (se 1 (by rfl) ⟨754631, by rfl⟩ : syracuseStep 1006175 = 1509263) B1509263
theorem B6019717 : Blo 467785 6019717 := bstep (se 4 (by rfl) ⟨564348, by rfl⟩ : syracuseStep 6019717 = 1128697) B1128697
theorem B2677481 : Blo 467785 2677481 := bstep (se 2 (by rfl) ⟨1004055, by rfl⟩ : syracuseStep 2677481 = 2008111) B2008111
theorem B2382695 : Blo 467785 2382695 := bstep (se 1 (by rfl) ⟨1787021, by rfl⟩ : syracuseStep 2382695 = 3574043) B3574043
theorem B5331905 : Blo 467785 5331905 := bstep (se 2 (by rfl) ⟨1999464, by rfl⟩ : syracuseStep 5331905 = 3998929) B3998929
theorem B3005531 : Blo 467785 3005531 := bstep (se 1 (by rfl) ⟨2254148, by rfl⟩ : syracuseStep 3005531 = 4508297) B4508297
theorem B1334515 : Blo 467785 1334515 := bstep (se 1 (by rfl) ⟨1000886, by rfl⟩ : syracuseStep 1334515 = 2001773) B2001773
theorem B1499087 : Blo 467785 1499087 := bstep (se 1 (by rfl) ⟨1124315, by rfl⟩ : syracuseStep 1499087 = 2248631) B2248631
theorem B7626959 : Blo 467785 7626959 := bstep (se 1 (by rfl) ⟨5720219, by rfl⟩ : syracuseStep 7626959 = 11440439) B11440439
theorem B2679439 : Blo 467785 2679439 := bstep (se 1 (by rfl) ⟨2009579, by rfl⟩ : syracuseStep 2679439 = 4019159) B4019159
theorem B1336189 : Blo 467785 1336189 := bstep (se 3 (by rfl) ⟨250535, by rfl⟩ : syracuseStep 1336189 = 501071) B501071
theorem B5727617 : Blo 467785 5727617 := bstep (se 2 (by rfl) ⟨2147856, by rfl⟩ : syracuseStep 5727617 = 4295713) B4295713
theorem B1500727 : Blo 467785 1500727 := bstep (se 1 (by rfl) ⟨1125545, by rfl⟩ : syracuseStep 1500727 = 2251091) B2251091
theorem B1336895 : Blo 467785 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B2680715 : Blo 467785 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B10414655 : Blo 467785 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B55799563 : Blo 467785 55799563 := bstep (se 1 (by rfl) ⟨41849672, by rfl⟩ : syracuseStep 55799563 = 83699345) B83699345
theorem B6025049 : Blo 467785 6025049 := bstep (se 2 (by rfl) ⟨2259393, by rfl⟩ : syracuseStep 6025049 = 4518787) B4518787
theorem B4714939 : Blo 467785 4714939 := bstep (se 1 (by rfl) ⟨3536204, by rfl⟩ : syracuseStep 4714939 = 7072409) B7072409
theorem B4518479 : Blo 467785 4518479 := bstep (se 1 (by rfl) ⟨3388859, by rfl⟩ : syracuseStep 4518479 = 6777719) B6777719
theorem B4061225 : Blo 467785 4061225 := bstep (se 2 (by rfl) ⟨1522959, by rfl⟩ : syracuseStep 4061225 = 3045919) B3045919
theorem B2685089 : Blo 467785 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B1899487 : Blo 467785 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B752735 : Blo 467785 752735 := bstep (se 1 (by rfl) ⟨564551, by rfl⟩ : syracuseStep 752735 = 1129103) B1129103
theorem B1342955 : Blo 467785 1342955 := bstep (se 1 (by rfl) ⟨1007216, by rfl⟩ : syracuseStep 1342955 = 2014433) B2014433
theorem B20512379 : Blo 467785 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B2686729 : Blo 467785 2686729 := bstep (se 2 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 2686729 = 2015047) B2015047
theorem B3571613 : Blo 467785 3571613 := bstep (se 3 (by rfl) ⟨669677, by rfl⟩ : syracuseStep 3571613 = 1339355) B1339355
theorem B3604895 : Blo 467785 3604895 := bstep (se 1 (by rfl) ⟨2703671, by rfl⟩ : syracuseStep 3604895 = 5407343) B5407343
theorem B11993507 : Blo 467785 11993507 := bstep (se 1 (by rfl) ⟨8995130, by rfl⟩ : syracuseStep 11993507 = 17990261) B17990261
theorem B3572585 : Blo 467785 3572585 := bstep (se 2 (by rfl) ⟨1339719, by rfl⟩ : syracuseStep 3572585 = 2679439) B2679439
theorem B6423425 : Blo 467785 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B2360495 : Blo 467785 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B2000969 : Blo 467785 2000969 := bstep (se 2 (by rfl) ⟨750363, by rfl⟩ : syracuseStep 2000969 = 1500727) B1500727
theorem B3999887 : Blo 467785 3999887 := bstep (se 1 (by rfl) ⟨2999915, by rfl⟩ : syracuseStep 3999887 = 5999831) B5999831
theorem B790087 : Blo 467785 790087 := bstep (se 1 (by rfl) ⟨592565, by rfl⟩ : syracuseStep 790087 = 1185131) B1185131
theorem B790121 : Blo 467785 790121 := bstep (se 2 (by rfl) ⟨296295, by rfl⟩ : syracuseStep 790121 = 592591) B592591
theorem B790175 : Blo 467785 790175 := bstep (se 1 (by rfl) ⟨592631, by rfl⟩ : syracuseStep 790175 = 1185263) B1185263
theorem B6885623 : Blo 467785 6885623 := bstep (se 1 (by rfl) ⟨5164217, by rfl⟩ : syracuseStep 6885623 = 10328435) B10328435
theorem B2003687 : Blo 467785 2003687 := bstep (se 1 (by rfl) ⟨1502765, by rfl⟩ : syracuseStep 2003687 = 3005531) B3005531
theorem B791545 : Blo 467785 791545 := bstep (se 2 (by rfl) ⟨296829, by rfl⟩ : syracuseStep 791545 = 593659) B593659
theorem B529663 : Blo 467785 529663 := bstep (se 1 (by rfl) ⟨397247, by rfl⟩ : syracuseStep 529663 = 794495) B794495
theorem B5084639 : Blo 467785 5084639 := bstep (se 1 (by rfl) ⟨3813479, by rfl⟩ : syracuseStep 5084639 = 7626959) B7626959
theorem B529951 : Blo 467785 529951 := bstep (se 1 (by rfl) ⟨397463, by rfl⟩ : syracuseStep 529951 = 794927) B794927
theorem B1054439 : Blo 467785 1054439 := bstep (se 1 (by rfl) ⟨790829, by rfl⟩ : syracuseStep 1054439 = 1581659) B1581659
theorem B7608329 : Blo 467785 7608329 := bstep (se 2 (by rfl) ⟨2853123, by rfl⟩ : syracuseStep 7608329 = 5706247) B5706247
theorem B792679 : Blo 467785 792679 := bstep (se 1 (by rfl) ⟨594509, by rfl⟩ : syracuseStep 792679 = 1189019) B1189019
theorem B891263 : Blo 467785 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B12032873 : Blo 467785 12032873 := bstep (se 2 (by rfl) ⟨4512327, by rfl⟩ : syracuseStep 12032873 = 9024655) B9024655
theorem B793631 : Blo 467785 793631 := bstep (se 1 (by rfl) ⟨595223, by rfl⟩ : syracuseStep 793631 = 1190447) B1190447
theorem B793705 : Blo 467785 793705 := bstep (se 2 (by rfl) ⟨297639, by rfl⟩ : syracuseStep 793705 = 595279) B595279
theorem B1055969 : Blo 467785 1055969 := bstep (se 2 (by rfl) ⟨395988, by rfl⟩ : syracuseStep 1055969 = 791977) B791977
theorem B1056041 : Blo 467785 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B794063 : Blo 467785 794063 := bstep (se 1 (by rfl) ⟨595547, by rfl⟩ : syracuseStep 794063 = 1191095) B1191095
theorem B1187399 : Blo 467785 1187399 := bstep (se 1 (by rfl) ⟨890549, by rfl⟩ : syracuseStep 1187399 = 1781099) B1781099
theorem B1580795 : Blo 467785 1580795 := bstep (se 1 (by rfl) ⟨1185596, by rfl⟩ : syracuseStep 1580795 = 2371193) B2371193
theorem B4530167 : Blo 467785 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B5349401 : Blo 467785 5349401 := bstep (se 2 (by rfl) ⟨2006025, by rfl⟩ : syracuseStep 5349401 = 4012051) B4012051
theorem B794731 : Blo 467785 794731 := bstep (se 1 (by rfl) ⟨596048, by rfl⟩ : syracuseStep 794731 = 1192097) B1192097
theorem B467871 : Blo 467785 467871 := bstep (se 1 (by rfl) ⟨350903, by rfl⟩ : syracuseStep 467871 = 701807) B701807
theorem B1778669 : Blo 467785 1778669 := bstep (se 3 (by rfl) ⟨333500, by rfl⟩ : syracuseStep 1778669 = 667001) B667001
theorem B467951 : Blo 467785 467951 := bstep (se 1 (by rfl) ⟨350963, by rfl⟩ : syracuseStep 467951 = 701927) B701927
theorem B468071 : Blo 467785 468071 := bstep (se 1 (by rfl) ⟨351053, by rfl⟩ : syracuseStep 468071 = 702107) B702107
theorem B3515557 : Blo 467785 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B1057967 : Blo 467785 1057967 := bstep (se 1 (by rfl) ⟨793475, by rfl⟩ : syracuseStep 1057967 = 1586951) B1586951
theorem B2532649 : Blo 467785 2532649 := bstep (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) B1899487
theorem B468295 : Blo 467785 468295 := bstep (se 1 (by rfl) ⟨351221, by rfl⟩ : syracuseStep 468295 = 702443) B702443
theorem B1582415 : Blo 467785 1582415 := bstep (se 1 (by rfl) ⟨1186811, by rfl⟩ : syracuseStep 1582415 = 2373623) B2373623
theorem B468351 : Blo 467785 468351 := bstep (se 1 (by rfl) ⟨351263, by rfl⟩ : syracuseStep 468351 = 702527) B702527
theorem B468571 : Blo 467785 468571 := bstep (se 1 (by rfl) ⟨351428, by rfl⟩ : syracuseStep 468571 = 702857) B702857
theorem B1779353 : Blo 467785 1779353 := bstep (se 2 (by rfl) ⟨667257, by rfl⟩ : syracuseStep 1779353 = 1334515) B1334515
theorem B468687 : Blo 467785 468687 := bstep (se 1 (by rfl) ⟨351515, by rfl⟩ : syracuseStep 468687 = 703031) B703031
theorem B1058651 : Blo 467785 1058651 := bstep (se 1 (by rfl) ⟨793988, by rfl⟩ : syracuseStep 1058651 = 1587977) B1587977
theorem B468903 : Blo 467785 468903 := bstep (se 1 (by rfl) ⟨351677, by rfl⟩ : syracuseStep 468903 = 703355) B703355
theorem B1779671 : Blo 467785 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B501823 : Blo 467785 501823 := bstep (se 1 (by rfl) ⟨376367, by rfl⟩ : syracuseStep 501823 = 752735) B752735
theorem B1583387 : Blo 467785 1583387 := bstep (se 1 (by rfl) ⟨1187540, by rfl⟩ : syracuseStep 1583387 = 2375081) B2375081
theorem B469311 : Blo 467785 469311 := bstep (se 1 (by rfl) ⟨351983, by rfl⟩ : syracuseStep 469311 = 703967) B703967
theorem B895303 : Blo 467785 895303 := bstep (se 1 (by rfl) ⟨671477, by rfl⟩ : syracuseStep 895303 = 1342955) B1342955
theorem B3582305 : Blo 467785 3582305 := bstep (se 2 (by rfl) ⟨1343364, by rfl⟩ : syracuseStep 3582305 = 2686729) B2686729
theorem B13674919 : Blo 467785 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B1190315 : Blo 467785 1190315 := bstep (se 1 (by rfl) ⟨892736, by rfl⟩ : syracuseStep 1190315 = 1785473) B1785473
theorem B1583549 : Blo 467785 1583549 := bstep (se 3 (by rfl) ⟨296915, by rfl⟩ : syracuseStep 1583549 = 593831) B593831
theorem B469479 : Blo 467785 469479 := bstep (se 1 (by rfl) ⟨352109, by rfl⟩ : syracuseStep 469479 = 704219) B704219
theorem B61680203 : Blo 467785 61680203 := bstep (se 1 (by rfl) ⟨46260152, by rfl⟩ : syracuseStep 61680203 = 92520305) B92520305
theorem B1583711 : Blo 467785 1583711 := bstep (se 1 (by rfl) ⟨1187783, by rfl⟩ : syracuseStep 1583711 = 2375567) B2375567
theorem B469659 : Blo 467785 469659 := bstep (se 1 (by rfl) ⟨352244, by rfl⟩ : syracuseStep 469659 = 704489) B704489
theorem B469787 : Blo 467785 469787 := bstep (se 1 (by rfl) ⟨352340, by rfl⟩ : syracuseStep 469787 = 704681) B704681
theorem B1059623 : Blo 467785 1059623 := bstep (se 1 (by rfl) ⟨794717, by rfl⟩ : syracuseStep 1059623 = 1589435) B1589435
theorem B666409 : Blo 467785 666409 := bstep (se 2 (by rfl) ⟨249903, by rfl⟩ : syracuseStep 666409 = 499807) B499807
theorem B469999 : Blo 467785 469999 := bstep (se 1 (by rfl) ⟨352499, by rfl⟩ : syracuseStep 469999 = 704999) B704999
theorem B8039411 : Blo 467785 8039411 := bstep (se 1 (by rfl) ⟨6029558, by rfl⟩ : syracuseStep 8039411 = 12059117) B12059117
theorem B470183 : Blo 467785 470183 := bstep (se 1 (by rfl) ⟨352637, by rfl⟩ : syracuseStep 470183 = 705275) B705275
theorem B3386555 : Blo 467785 3386555 := bstep (se 1 (by rfl) ⟨2539916, by rfl⟩ : syracuseStep 3386555 = 5079833) B5079833
theorem B1584413 : Blo 467785 1584413 := bstep (se 3 (by rfl) ⟨297077, by rfl⟩ : syracuseStep 1584413 = 594155) B594155
theorem B1060271 : Blo 467785 1060271 := bstep (se 1 (by rfl) ⟨795203, by rfl⟩ : syracuseStep 1060271 = 1590407) B1590407
theorem B536015 : Blo 467785 536015 := bstep (se 1 (by rfl) ⟨402011, by rfl⟩ : syracuseStep 536015 = 804023) B804023
theorem B470479 : Blo 467785 470479 := bstep (se 1 (by rfl) ⟨352859, by rfl⟩ : syracuseStep 470479 = 705719) B705719
theorem B470575 : Blo 467785 470575 := bstep (se 1 (by rfl) ⟨352931, by rfl⟩ : syracuseStep 470575 = 705863) B705863
theorem B470639 : Blo 467785 470639 := bstep (se 1 (by rfl) ⟨352979, by rfl⟩ : syracuseStep 470639 = 705959) B705959
theorem B1060523 : Blo 467785 1060523 := bstep (se 1 (by rfl) ⟨795392, by rfl⟩ : syracuseStep 1060523 = 1590785) B1590785
theorem B470759 : Blo 467785 470759 := bstep (se 1 (by rfl) ⟨353069, by rfl⟩ : syracuseStep 470759 = 706139) B706139
theorem B1781585 : Blo 467785 1781585 := bstep (se 2 (by rfl) ⟨668094, by rfl⟩ : syracuseStep 1781585 = 1336189) B1336189
theorem B471071 : Blo 467785 471071 := bstep (se 1 (by rfl) ⟨353303, by rfl⟩ : syracuseStep 471071 = 706607) B706607
theorem B1126507 : Blo 467785 1126507 := bstep (se 1 (by rfl) ⟨844880, by rfl⟩ : syracuseStep 1126507 = 1689761) B1689761
theorem B1585277 : Blo 467785 1585277 := bstep (se 3 (by rfl) ⟨297239, by rfl⟩ : syracuseStep 1585277 = 594479) B594479
theorem B667855 : Blo 467785 667855 := bstep (se 1 (by rfl) ⟨500891, by rfl⟩ : syracuseStep 667855 = 1001783) B1001783
theorem B471247 : Blo 467785 471247 := bstep (se 1 (by rfl) ⟨353435, by rfl⟩ : syracuseStep 471247 = 706871) B706871
theorem B5353775 : Blo 467785 5353775 := bstep (se 1 (by rfl) ⟨4015331, by rfl⟩ : syracuseStep 5353775 = 8030663) B8030663
theorem B471367 : Blo 467785 471367 := bstep (se 1 (by rfl) ⟨353525, by rfl⟩ : syracuseStep 471367 = 707051) B707051
theorem B1061243 : Blo 467785 1061243 := bstep (se 1 (by rfl) ⟨795932, by rfl⟩ : syracuseStep 1061243 = 1591865) B1591865
theorem B4010411 : Blo 467785 4010411 := bstep (se 1 (by rfl) ⟨3007808, by rfl⟩ : syracuseStep 4010411 = 6015617) B6015617
theorem B471527 : Blo 467785 471527 := bstep (se 1 (by rfl) ⟨353645, by rfl⟩ : syracuseStep 471527 = 707291) B707291
theorem B1061351 : Blo 467785 1061351 := bstep (se 1 (by rfl) ⟨796013, by rfl⟩ : syracuseStep 1061351 = 1592027) B1592027
theorem B471551 : Blo 467785 471551 := bstep (se 1 (by rfl) ⟨353663, by rfl⟩ : syracuseStep 471551 = 707327) B707327
theorem B1192553 : Blo 467785 1192553 := bstep (se 2 (by rfl) ⟨447207, by rfl⟩ : syracuseStep 1192553 = 894415) B894415
theorem B1192927 : Blo 467785 1192927 := bstep (se 1 (by rfl) ⟨894695, by rfl⟩ : syracuseStep 1192927 = 1789391) B1789391
theorem B1193575 : Blo 467785 1193575 := bstep (se 1 (by rfl) ⟨895181, by rfl⟩ : syracuseStep 1193575 = 1790363) B1790363
theorem B702089 : Blo 467785 702089 := bstep (se 2 (by rfl) ⟨263283, by rfl⟩ : syracuseStep 702089 = 526567) B526567
theorem B1783559 : Blo 467785 1783559 := bstep (se 1 (by rfl) ⟨1337669, by rfl⟩ : syracuseStep 1783559 = 2675339) B2675339
theorem B1587005 : Blo 467785 1587005 := bstep (se 3 (by rfl) ⟨297563, by rfl⟩ : syracuseStep 1587005 = 595127) B595127
theorem B6764573 : Blo 467785 6764573 := bstep (se 3 (by rfl) ⟨1268357, by rfl⟩ : syracuseStep 6764573 = 2536715) B2536715
theorem B1128487 : Blo 467785 1128487 := bstep (se 1 (by rfl) ⟨846365, by rfl⟩ : syracuseStep 1128487 = 1692731) B1692731
theorem B2668733 : Blo 467785 2668733 := bstep (se 3 (by rfl) ⟨500387, by rfl⟩ : syracuseStep 2668733 = 1000775) B1000775
theorem B1784015 : Blo 467785 1784015 := bstep (se 1 (by rfl) ⟨1338011, by rfl⟩ : syracuseStep 1784015 = 2676023) B2676023
theorem B23182199 : Blo 467785 23182199 := bstep (se 1 (by rfl) ⟨17386649, by rfl⟩ : syracuseStep 23182199 = 34773299) B34773299
theorem B2014091 : Blo 467785 2014091 := bstep (se 1 (by rfl) ⟨1510568, by rfl⟩ : syracuseStep 2014091 = 3021137) B3021137
theorem B670783 : Blo 467785 670783 := bstep (se 1 (by rfl) ⟨503087, by rfl⟩ : syracuseStep 670783 = 1006175) B1006175
theorem B1784987 : Blo 467785 1784987 := bstep (se 1 (by rfl) ⟨1338740, by rfl⟩ : syracuseStep 1784987 = 2677481) B2677481
theorem B703655 : Blo 467785 703655 := bstep (se 1 (by rfl) ⟨527741, by rfl⟩ : syracuseStep 703655 = 1055483) B1055483
theorem B1588463 : Blo 467785 1588463 := bstep (se 1 (by rfl) ⟨1191347, by rfl⟩ : syracuseStep 1588463 = 2382695) B2382695
theorem B703739 : Blo 467785 703739 := bstep (se 1 (by rfl) ⟨527804, by rfl⟩ : syracuseStep 703739 = 1055609) B1055609
theorem B3554603 : Blo 467785 3554603 := bstep (se 1 (by rfl) ⟨2665952, by rfl⟩ : syracuseStep 3554603 = 5331905) B5331905
theorem B703865 : Blo 467785 703865 := bstep (se 2 (by rfl) ⟨263949, by rfl⟩ : syracuseStep 703865 = 527899) B527899
theorem B2670191 : Blo 467785 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B74399417 : Blo 467785 74399417 := bstep (se 2 (by rfl) ⟨27899781, by rfl⟩ : syracuseStep 74399417 = 55799563) B55799563
theorem B704393 : Blo 467785 704393 := bstep (se 2 (by rfl) ⟨264147, by rfl⟩ : syracuseStep 704393 = 528295) B528295
theorem B999391 : Blo 467785 999391 := bstep (se 1 (by rfl) ⟨749543, by rfl⟩ : syracuseStep 999391 = 1499087) B1499087
theorem B15253505 : Blo 467785 15253505 := bstep (se 2 (by rfl) ⟨5720064, by rfl⟩ : syracuseStep 15253505 = 11440129) B11440129
theorem B10829933 : Blo 467785 10829933 := bstep (se 3 (by rfl) ⟨2030612, by rfl⟩ : syracuseStep 10829933 = 4061225) B4061225
theorem B704633 : Blo 467785 704633 := bstep (se 2 (by rfl) ⟨264237, by rfl⟩ : syracuseStep 704633 = 528475) B528475
theorem B704927 : Blo 467785 704927 := bstep (se 1 (by rfl) ⟨528695, by rfl⟩ : syracuseStep 704927 = 1057391) B1057391
theorem B705257 : Blo 467785 705257 := bstep (se 2 (by rfl) ⟨264471, by rfl⟩ : syracuseStep 705257 = 528943) B528943
theorem B3818411 : Blo 467785 3818411 := bstep (se 1 (by rfl) ⟨2863808, by rfl⟩ : syracuseStep 3818411 = 5727617) B5727617
theorem B1787143 : Blo 467785 1787143 := bstep (se 1 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 1787143 = 2680715) B2680715
theorem B706025 : Blo 467785 706025 := bstep (se 2 (by rfl) ⟨264759, by rfl⟩ : syracuseStep 706025 = 529519) B529519
theorem B706103 : Blo 467785 706103 := bstep (se 1 (by rfl) ⟨529577, by rfl⟩ : syracuseStep 706103 = 1059155) B1059155
theorem B2410279 : Blo 467785 2410279 := bstep (se 1 (by rfl) ⟨1807709, by rfl⟩ : syracuseStep 2410279 = 3615419) B3615419
theorem B2541455 : Blo 467785 2541455 := bstep (se 1 (by rfl) ⟨1906091, by rfl⟩ : syracuseStep 2541455 = 3812183) B3812183
theorem B706463 : Blo 467785 706463 := bstep (se 1 (by rfl) ⟨529847, by rfl⟩ : syracuseStep 706463 = 1059695) B1059695
theorem B2377673 : Blo 467785 2377673 := bstep (se 2 (by rfl) ⟨891627, by rfl⟩ : syracuseStep 2377673 = 1783255) B1783255
theorem B706631 : Blo 467785 706631 := bstep (se 1 (by rfl) ⟨529973, by rfl⟩ : syracuseStep 706631 = 1059947) B1059947
theorem B706811 : Blo 467785 706811 := bstep (se 1 (by rfl) ⟨530108, by rfl⟩ : syracuseStep 706811 = 1060217) B1060217
theorem B4016699 : Blo 467785 4016699 := bstep (se 1 (by rfl) ⟨3012524, by rfl⟩ : syracuseStep 4016699 = 6025049) B6025049
theorem B707231 : Blo 467785 707231 := bstep (se 1 (by rfl) ⟨530423, by rfl⟩ : syracuseStep 707231 = 1060847) B1060847
theorem B1790059 : Blo 467785 1790059 := bstep (se 1 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 1790059 = 2685089) B2685089
theorem B3396127 : Blo 467785 3396127 := bstep (se 1 (by rfl) ⟨2547095, by rfl⟩ : syracuseStep 3396127 = 5094191) B5094191
theorem B2381075 : Blo 467785 2381075 := bstep (se 1 (by rfl) ⟨1785806, by rfl⟩ : syracuseStep 2381075 = 3571613) B3571613
theorem B4052663 : Blo 467785 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B20273489 : Blo 467785 20273489 := bstep (se 2 (by rfl) ⟨7602558, by rfl⟩ : syracuseStep 20273489 = 15205117) B15205117
theorem B7232327 : Blo 467785 7232327 := bstep (se 1 (by rfl) ⟨5424245, by rfl⟩ : syracuseStep 7232327 = 10848491) B10848491
theorem B1072223 : Blo 467785 1072223 := bstep (se 1 (by rfl) ⟨804167, by rfl⟩ : syracuseStep 1072223 = 1608335) B1608335
theorem B3824923 : Blo 467785 3824923 := bstep (se 1 (by rfl) ⟨2868692, by rfl⟩ : syracuseStep 3824923 = 5737385) B5737385
theorem B2383343 : Blo 467785 2383343 := bstep (se 1 (by rfl) ⟨1787507, by rfl⟩ : syracuseStep 2383343 = 3575015) B3575015
theorem B4021757 : Blo 467785 4021757 := bstep (se 3 (by rfl) ⟨754079, by rfl⟩ : syracuseStep 4021757 = 1508159) B1508159
theorem B4808573 : Blo 467785 4808573 := bstep (se 3 (by rfl) ⟨901607, by rfl⟩ : syracuseStep 4808573 = 1803215) B1803215
theorem B3631499 : Blo 467785 3631499 := bstep (se 1 (by rfl) ⟨2723624, by rfl⟩ : syracuseStep 3631499 = 5447249) B5447249
theorem B10120139 : Blo 467785 10120139 := bstep (se 1 (by rfl) ⟨7590104, by rfl⟩ : syracuseStep 10120139 = 15180209) B15180209
theorem B6286585 : Blo 467785 6286585 := bstep (se 2 (by rfl) ⟨2357469, by rfl⟩ : syracuseStep 6286585 = 4714939) B4714939
theorem B2387393 : Blo 467785 2387393 := bstep (se 2 (by rfl) ⟨895272, by rfl⟩ : syracuseStep 2387393 = 1790545) B1790545
theorem B6943103 : Blo 467785 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B3568211 : Blo 467785 3568211 := bstep (se 1 (by rfl) ⟨2676158, by rfl⟩ : syracuseStep 3568211 = 5352317) B5352317
theorem B5337737 : Blo 467785 5337737 := bstep (se 2 (by rfl) ⟨2001651, by rfl⟩ : syracuseStep 5337737 = 4003303) B4003303
theorem B1602473 : Blo 467785 1602473 := bstep (se 2 (by rfl) ⟨600927, by rfl⟩ : syracuseStep 1602473 = 1201855) B1201855
theorem B751081 : Blo 467785 751081 := bstep (se 2 (by rfl) ⟨281655, by rfl⟩ : syracuseStep 751081 = 563311) B563311
theorem B3012319 : Blo 467785 3012319 := bstep (se 1 (by rfl) ⟨2259239, by rfl⟩ : syracuseStep 3012319 = 4518479) B4518479
theorem B6781067 : Blo 467785 6781067 := bstep (se 1 (by rfl) ⟨5085800, by rfl⟩ : syracuseStep 6781067 = 10171601) B10171601
theorem B8026289 : Blo 467785 8026289 := bstep (se 2 (by rfl) ⟨3009858, by rfl⟩ : syracuseStep 8026289 = 6019717) B6019717
theorem B5994809 : Blo 467785 5994809 := bstep (se 2 (by rfl) ⟨2248053, by rfl⟩ : syracuseStep 5994809 = 4496107) B4496107
theorem B1342079 : Blo 467785 1342079 := bstep (se 1 (by rfl) ⟨1006559, by rfl⟩ : syracuseStep 1342079 = 2013119) B2013119
theorem B3571127 : Blo 467785 3571127 := bstep (se 1 (by rfl) ⟨2678345, by rfl⟩ : syracuseStep 3571127 = 5356691) B5356691
theorem B1343263 : Blo 467785 1343263 := bstep (se 1 (by rfl) ⟨1007447, by rfl⟩ : syracuseStep 1343263 = 2014895) B2014895
theorem B1802047 : Blo 467785 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B7995671 : Blo 467785 7995671 := bstep (se 1 (by rfl) ⟨5996753, by rfl⟩ : syracuseStep 7995671 = 11993507) B11993507
theorem B1573663 : Blo 467785 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B4687409 : Blo 467785 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B3376865 : Blo 467785 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B526747 : Blo 467785 526747 := bstep (se 1 (by rfl) ⟨395060, by rfl⟩ : syracuseStep 526747 = 790121) B790121
theorem B526783 : Blo 467785 526783 := bstep (se 1 (by rfl) ⟨395087, by rfl⟩ : syracuseStep 526783 = 790175) B790175
theorem B4590415 : Blo 467785 4590415 := bstep (se 1 (by rfl) ⟨3442811, by rfl⟩ : syracuseStep 4590415 = 6885623) B6885623
theorem B888545 : Blo 467785 888545 := bstep (se 2 (by rfl) ⟨333204, by rfl⟩ : syracuseStep 888545 = 666409) B666409
theorem B4821551 : Blo 467785 4821551 := bstep (se 1 (by rfl) ⟨3616163, by rfl⟩ : syracuseStep 4821551 = 7232327) B7232327
theorem B529087 : Blo 467785 529087 := bstep (se 1 (by rfl) ⟨396815, by rfl⟩ : syracuseStep 529087 = 793631) B793631
theorem B1053449 : Blo 467785 1053449 := bstep (se 2 (by rfl) ⟨395043, by rfl⟩ : syracuseStep 1053449 = 790087) B790087
theorem B529375 : Blo 467785 529375 := bstep (se 1 (by rfl) ⟨397031, by rfl⟩ : syracuseStep 529375 = 794063) B794063
theorem B791599 : Blo 467785 791599 := bstep (se 1 (by rfl) ⟨593699, by rfl⟩ : syracuseStep 791599 = 1187399) B1187399
theorem B1053863 : Blo 467785 1053863 := bstep (se 1 (by rfl) ⟨790397, by rfl⟩ : syracuseStep 1053863 = 1580795) B1580795
theorem B3020111 : Blo 467785 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B1185779 : Blo 467785 1185779 := bstep (se 1 (by rfl) ⟨889334, by rfl⟩ : syracuseStep 1185779 = 1778669) B1778669
theorem B4528169 : Blo 467785 4528169 := bstep (se 2 (by rfl) ⟨1698063, by rfl⟩ : syracuseStep 4528169 = 3396127) B3396127
theorem B1054943 : Blo 467785 1054943 := bstep (se 1 (by rfl) ⟨791207, by rfl⟩ : syracuseStep 1054943 = 1582415) B1582415
theorem B1186235 : Blo 467785 1186235 := bstep (se 1 (by rfl) ⟨889676, by rfl⟩ : syracuseStep 1186235 = 1779353) B1779353
theorem B1186447 : Blo 467785 1186447 := bstep (se 1 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 1186447 = 1779671) B1779671
theorem B1055393 : Blo 467785 1055393 := bstep (se 2 (by rfl) ⟨395772, by rfl⟩ : syracuseStep 1055393 = 791545) B791545
theorem B1055591 : Blo 467785 1055591 := bstep (se 1 (by rfl) ⟨791693, by rfl⟩ : syracuseStep 1055591 = 1583387) B1583387
theorem B793543 : Blo 467785 793543 := bstep (se 1 (by rfl) ⟨595157, by rfl⟩ : syracuseStep 793543 = 1190315) B1190315
theorem B1055699 : Blo 467785 1055699 := bstep (se 1 (by rfl) ⟨791774, by rfl⟩ : syracuseStep 1055699 = 1583549) B1583549
theorem B1055807 : Blo 467785 1055807 := bstep (se 1 (by rfl) ⟨791855, by rfl⟩ : syracuseStep 1055807 = 1583711) B1583711
theorem B1056275 : Blo 467785 1056275 := bstep (se 1 (by rfl) ⟨792206, by rfl⟩ : syracuseStep 1056275 = 1584413) B1584413
theorem B1187723 : Blo 467785 1187723 := bstep (se 1 (by rfl) ⟨890792, by rfl⟩ : syracuseStep 1187723 = 1781585) B1781585
theorem B1056851 : Blo 467785 1056851 := bstep (se 1 (by rfl) ⟨792638, by rfl⟩ : syracuseStep 1056851 = 1585277) B1585277
theorem B1056905 : Blo 467785 1056905 := bstep (se 2 (by rfl) ⟨396339, by rfl⟩ : syracuseStep 1056905 = 792679) B792679
theorem B4628735 : Blo 467785 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B795035 : Blo 467785 795035 := bstep (se 1 (by rfl) ⟨596276, by rfl⟩ : syracuseStep 795035 = 1192553) B1192553
theorem B468059 : Blo 467785 468059 := bstep (se 1 (by rfl) ⟨351044, by rfl⟩ : syracuseStep 468059 = 702089) B702089
theorem B1189039 : Blo 467785 1189039 := bstep (se 1 (by rfl) ⟨891779, by rfl⟩ : syracuseStep 1189039 = 1783559) B1783559
theorem B1058003 : Blo 467785 1058003 := bstep (se 1 (by rfl) ⟨793502, by rfl⟩ : syracuseStep 1058003 = 1587005) B1587005
theorem B894377 : Blo 467785 894377 := bstep (se 2 (by rfl) ⟨335391, by rfl⟩ : syracuseStep 894377 = 670783) B670783
theorem B5350859 : Blo 467785 5350859 := bstep (se 1 (by rfl) ⟨4013144, by rfl⟩ : syracuseStep 5350859 = 8026289) B8026289
theorem B1779155 : Blo 467785 1779155 := bstep (se 1 (by rfl) ⟨1334366, by rfl⟩ : syracuseStep 1779155 = 2668733) B2668733
theorem B1189343 : Blo 467785 1189343 := bstep (se 1 (by rfl) ⟨892007, by rfl⟩ : syracuseStep 1189343 = 1784015) B1784015
theorem B1058273 : Blo 467785 1058273 := bstep (se 2 (by rfl) ⟨396852, by rfl⟩ : syracuseStep 1058273 = 793705) B793705
theorem B12854821 : Blo 467785 12854821 := bstep (se 4 (by rfl) ⟨1205139, by rfl⟩ : syracuseStep 12854821 = 2410279) B2410279
theorem B894719 : Blo 467785 894719 := bstep (se 1 (by rfl) ⟨671039, by rfl⟩ : syracuseStep 894719 = 1342079) B1342079
theorem B1189991 : Blo 467785 1189991 := bstep (se 1 (by rfl) ⟨892493, by rfl⟩ : syracuseStep 1189991 = 1784987) B1784987
theorem B469103 : Blo 467785 469103 := bstep (se 1 (by rfl) ⟨351827, by rfl⟩ : syracuseStep 469103 = 703655) B703655
theorem B1058975 : Blo 467785 1058975 := bstep (se 1 (by rfl) ⟨794231, by rfl⟩ : syracuseStep 1058975 = 1588463) B1588463
theorem B469159 : Blo 467785 469159 := bstep (se 1 (by rfl) ⟨351869, by rfl⟩ : syracuseStep 469159 = 703739) B703739
theorem B2369735 : Blo 467785 2369735 := bstep (se 1 (by rfl) ⟨1777301, by rfl⟩ : syracuseStep 2369735 = 3554603) B3554603
theorem B469243 : Blo 467785 469243 := bstep (se 1 (by rfl) ⟨351932, by rfl⟩ : syracuseStep 469243 = 703865) B703865
theorem B1780127 : Blo 467785 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B2402729 : Blo 467785 2402729 := bstep (se 2 (by rfl) ⟨901023, by rfl⟩ : syracuseStep 2402729 = 1802047) B1802047
theorem B469595 : Blo 467785 469595 := bstep (se 1 (by rfl) ⟨352196, by rfl⟩ : syracuseStep 469595 = 704393) B704393
theorem B10169003 : Blo 467785 10169003 := bstep (se 1 (by rfl) ⟨7626752, by rfl⟩ : syracuseStep 10169003 = 15253505) B15253505
theorem B7219955 : Blo 467785 7219955 := bstep (se 1 (by rfl) ⟨5414966, by rfl⟩ : syracuseStep 7219955 = 10829933) B10829933
theorem B469755 : Blo 467785 469755 := bstep (se 1 (by rfl) ⟨352316, by rfl⟩ : syracuseStep 469755 = 704633) B704633
theorem B1059641 : Blo 467785 1059641 := bstep (se 2 (by rfl) ⟨397365, by rfl⟩ : syracuseStep 1059641 = 794731) B794731
theorem B2403263 : Blo 467785 2403263 := bstep (se 1 (by rfl) ⟨1802447, by rfl⟩ : syracuseStep 2403263 = 3604895) B3604895
theorem B469951 : Blo 467785 469951 := bstep (se 1 (by rfl) ⟨352463, by rfl⟩ : syracuseStep 469951 = 704927) B704927
theorem B470171 : Blo 467785 470171 := bstep (se 1 (by rfl) ⟨352628, by rfl⟩ : syracuseStep 470171 = 705257) B705257
theorem B470683 : Blo 467785 470683 := bstep (se 1 (by rfl) ⟨353012, by rfl⟩ : syracuseStep 470683 = 706025) B706025
theorem B470735 : Blo 467785 470735 := bstep (se 1 (by rfl) ⟨353051, by rfl⟩ : syracuseStep 470735 = 706103) B706103
theorem B470975 : Blo 467785 470975 := bstep (se 1 (by rfl) ⟨353231, by rfl⟩ : syracuseStep 470975 = 706463) B706463
theorem B1585115 : Blo 467785 1585115 := bstep (se 1 (by rfl) ⟨1188836, by rfl⟩ : syracuseStep 1585115 = 2377673) B2377673
theorem B471087 : Blo 467785 471087 := bstep (se 1 (by rfl) ⟨353315, by rfl⟩ : syracuseStep 471087 = 706631) B706631
theorem B2666591 : Blo 467785 2666591 := bstep (se 1 (by rfl) ⟨1999943, by rfl⟩ : syracuseStep 2666591 = 3999887) B3999887
theorem B471207 : Blo 467785 471207 := bstep (se 1 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 471207 = 706811) B706811
theorem B471487 : Blo 467785 471487 := bstep (se 1 (by rfl) ⟨353615, by rfl⟩ : syracuseStep 471487 = 707231) B707231
theorem B669097 : Blo 467785 669097 := bstep (se 2 (by rfl) ⟨250911, by rfl⟩ : syracuseStep 669097 = 501823) B501823
theorem B1193737 : Blo 467785 1193737 := bstep (se 2 (by rfl) ⟨447651, by rfl⟩ : syracuseStep 1193737 = 895303) B895303
theorem B18233225 : Blo 467785 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B1587383 : Blo 467785 1587383 := bstep (se 1 (by rfl) ⟨1190537, by rfl⟩ : syracuseStep 1587383 = 2381075) B2381075
theorem B3389759 : Blo 467785 3389759 := bstep (se 1 (by rfl) ⟨2542319, by rfl⟩ : syracuseStep 3389759 = 5084639) B5084639
theorem B2701775 : Blo 467785 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B702959 : Blo 467785 702959 := bstep (se 1 (by rfl) ⟨527219, by rfl⟩ : syracuseStep 702959 = 1054439) B1054439
theorem B13515659 : Blo 467785 13515659 := bstep (se 1 (by rfl) ⟨10136744, by rfl⟩ : syracuseStep 13515659 = 20273489) B20273489
theorem B703979 : Blo 467785 703979 := bstep (se 1 (by rfl) ⟨527984, by rfl⟩ : syracuseStep 703979 = 1055969) B1055969
theorem B704027 : Blo 467785 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B1588895 : Blo 467785 1588895 := bstep (se 1 (by rfl) ⟨1191671, by rfl⟩ : syracuseStep 1588895 = 2383343) B2383343
theorem B705311 : Blo 467785 705311 := bstep (se 1 (by rfl) ⟨528983, by rfl⟩ : syracuseStep 705311 = 1057967) B1057967
theorem B2376701 : Blo 467785 2376701 := bstep (se 3 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 2376701 = 891263) B891263
theorem B705767 : Blo 467785 705767 := bstep (se 1 (by rfl) ⟨529325, by rfl⟩ : syracuseStep 705767 = 1058651) B1058651
theorem B1590569 : Blo 467785 1590569 := bstep (se 2 (by rfl) ⟨596463, by rfl⟩ : syracuseStep 1590569 = 1192927) B1192927
theorem B706217 : Blo 467785 706217 := bstep (se 2 (by rfl) ⟨264831, by rfl⟩ : syracuseStep 706217 = 529663) B529663
theorem B706415 : Blo 467785 706415 := bstep (se 1 (by rfl) ⟨529811, by rfl⟩ : syracuseStep 706415 = 1059623) B1059623
theorem B1001441 : Blo 467785 1001441 := bstep (se 2 (by rfl) ⟨375540, by rfl⟩ : syracuseStep 1001441 = 751081) B751081
theorem B5359607 : Blo 467785 5359607 := bstep (se 1 (by rfl) ⟨4019705, by rfl⟩ : syracuseStep 5359607 = 8039411) B8039411
theorem B706601 : Blo 467785 706601 := bstep (se 2 (by rfl) ⟨264975, by rfl⟩ : syracuseStep 706601 = 529951) B529951
theorem B1591433 : Blo 467785 1591433 := bstep (se 2 (by rfl) ⟨596787, by rfl⟩ : syracuseStep 1591433 = 1193575) B1193575
theorem B706847 : Blo 467785 706847 := bstep (se 1 (by rfl) ⟨530135, by rfl⟩ : syracuseStep 706847 = 1060271) B1060271
theorem B4016425 : Blo 467785 4016425 := bstep (se 2 (by rfl) ⟨1506159, by rfl⟩ : syracuseStep 4016425 = 3012319) B3012319
theorem B1591595 : Blo 467785 1591595 := bstep (se 1 (by rfl) ⟨1193696, by rfl⟩ : syracuseStep 1591595 = 2387393) B2387393
theorem B707015 : Blo 467785 707015 := bstep (se 1 (by rfl) ⟨530261, by rfl⟩ : syracuseStep 707015 = 1060523) B1060523
theorem B707495 : Blo 467785 707495 := bstep (se 1 (by rfl) ⟨530621, by rfl⟩ : syracuseStep 707495 = 1061243) B1061243
theorem B2673607 : Blo 467785 2673607 := bstep (se 1 (by rfl) ⟨2005205, by rfl⟩ : syracuseStep 2673607 = 4010411) B4010411
theorem B707567 : Blo 467785 707567 := bstep (se 1 (by rfl) ⟨530675, by rfl⟩ : syracuseStep 707567 = 1061351) B1061351
theorem B2378807 : Blo 467785 2378807 := bstep (se 1 (by rfl) ⟨1784105, by rfl⟩ : syracuseStep 2378807 = 3568211) B3568211
theorem B3558491 : Blo 467785 3558491 := bstep (se 1 (by rfl) ⟨2668868, by rfl⟩ : syracuseStep 3558491 = 5337737) B5337737
theorem B1429373 : Blo 467785 1429373 := bstep (se 3 (by rfl) ⟨268007, by rfl⟩ : syracuseStep 1429373 = 536015) B536015
theorem B4509715 : Blo 467785 4509715 := bstep (se 1 (by rfl) ⟨3382286, by rfl⟩ : syracuseStep 4509715 = 6764573) B6764573
theorem B5099897 : Blo 467785 5099897 := bstep (se 2 (by rfl) ⟨1912461, by rfl⟩ : syracuseStep 5099897 = 3824923) B3824923
theorem B17093045 : Blo 467785 17093045 := bstep (se 5 (by rfl) ⟨801236, by rfl⟩ : syracuseStep 17093045 = 1602473) B1602473
theorem B15454799 : Blo 467785 15454799 := bstep (se 1 (by rfl) ⟨11591099, by rfl⟩ : syracuseStep 15454799 = 23182199) B23182199
theorem B2380751 : Blo 467785 2380751 := bstep (se 1 (by rfl) ⟨1785563, by rfl⟩ : syracuseStep 2380751 = 3571127) B3571127
theorem B1791017 : Blo 467785 1791017 := bstep (se 2 (by rfl) ⟨671631, by rfl⟩ : syracuseStep 1791017 = 1343263) B1343263
theorem B49599611 : Blo 467785 49599611 := bstep (se 1 (by rfl) ⟨37199708, by rfl⟩ : syracuseStep 49599611 = 74399417) B74399417
theorem B1332521 : Blo 467785 1332521 := bstep (se 2 (by rfl) ⟨499695, by rfl⟩ : syracuseStep 1332521 = 999391) B999391
theorem B2381723 : Blo 467785 2381723 := bstep (se 1 (by rfl) ⟨1786292, by rfl⟩ : syracuseStep 2381723 = 3572585) B3572585
theorem B4282283 : Blo 467785 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B2545607 : Blo 467785 2545607 := bstep (se 1 (by rfl) ⟨1909205, by rfl⟩ : syracuseStep 2545607 = 3818411) B3818411
theorem B3561893 : Blo 467785 3561893 := bstep (se 4 (by rfl) ⟨333927, by rfl⟩ : syracuseStep 3561893 = 667855) B667855
theorem B1694303 : Blo 467785 1694303 := bstep (se 1 (by rfl) ⟨1270727, by rfl⟩ : syracuseStep 1694303 = 2541455) B2541455
theorem B1333979 : Blo 467785 1333979 := bstep (se 1 (by rfl) ⟨1000484, by rfl⟩ : syracuseStep 1333979 = 2000969) B2000969
theorem B2382857 : Blo 467785 2382857 := bstep (se 2 (by rfl) ⟨893571, by rfl⟩ : syracuseStep 2382857 = 1787143) B1787143
theorem B2677799 : Blo 467785 2677799 := bstep (se 1 (by rfl) ⟨2008349, by rfl⟩ : syracuseStep 2677799 = 4016699) B4016699
theorem B1335791 : Blo 467785 1335791 := bstep (se 1 (by rfl) ⟨1001843, by rfl⟩ : syracuseStep 1335791 = 2003687) B2003687
theorem B5072219 : Blo 467785 5072219 := bstep (se 1 (by rfl) ⟨3804164, by rfl⟩ : syracuseStep 5072219 = 7608329) B7608329
theorem B8382113 : Blo 467785 8382113 := bstep (se 2 (by rfl) ⟨3143292, by rfl⟩ : syracuseStep 8382113 = 6286585) B6286585
theorem B8021915 : Blo 467785 8021915 := bstep (se 1 (by rfl) ⟨6016436, by rfl⟩ : syracuseStep 8021915 = 12032873) B12032873
theorem B714815 : Blo 467785 714815 := bstep (se 1 (by rfl) ⟨536111, by rfl⟩ : syracuseStep 714815 = 1072223) B1072223
theorem B2681171 : Blo 467785 2681171 := bstep (se 1 (by rfl) ⟨2010878, by rfl⟩ : syracuseStep 2681171 = 4021757) B4021757
theorem B3205715 : Blo 467785 3205715 := bstep (se 1 (by rfl) ⟨2404286, by rfl⟩ : syracuseStep 3205715 = 4808573) B4808573
theorem B3566267 : Blo 467785 3566267 := bstep (se 1 (by rfl) ⟨2674700, by rfl⟩ : syracuseStep 3566267 = 5349401) B5349401
theorem B1502009 : Blo 467785 1502009 := bstep (se 2 (by rfl) ⟨563253, by rfl⟩ : syracuseStep 1502009 = 1126507) B1126507
theorem B2386745 : Blo 467785 2386745 := bstep (se 2 (by rfl) ⟨895029, by rfl⟩ : syracuseStep 2386745 = 1790059) B1790059
theorem B2388203 : Blo 467785 2388203 := bstep (se 1 (by rfl) ⟨1791152, by rfl⟩ : syracuseStep 2388203 = 3582305) B3582305
theorem B2420999 : Blo 467785 2420999 := bstep (se 1 (by rfl) ⟨1815749, by rfl⟩ : syracuseStep 2420999 = 3631499) B3631499
theorem B41120135 : Blo 467785 41120135 := bstep (se 1 (by rfl) ⟨30840101, by rfl⟩ : syracuseStep 41120135 = 61680203) B61680203
theorem B6746759 : Blo 467785 6746759 := bstep (se 1 (by rfl) ⟨5060069, by rfl⟩ : syracuseStep 6746759 = 10120139) B10120139
theorem B2257703 : Blo 467785 2257703 := bstep (se 1 (by rfl) ⟨1693277, by rfl⟩ : syracuseStep 2257703 = 3386555) B3386555
theorem B1504649 : Blo 467785 1504649 := bstep (se 2 (by rfl) ⟨564243, by rfl⟩ : syracuseStep 1504649 = 1128487) B1128487
theorem B3569183 : Blo 467785 3569183 := bstep (se 1 (by rfl) ⟨2676887, by rfl⟩ : syracuseStep 3569183 = 5353775) B5353775
theorem B4520711 : Blo 467785 4520711 := bstep (se 1 (by rfl) ⟨3390533, by rfl⟩ : syracuseStep 4520711 = 6781067) B6781067
theorem B3996539 : Blo 467785 3996539 := bstep (se 1 (by rfl) ⟨2997404, by rfl⟩ : syracuseStep 3996539 = 5994809) B5994809
theorem B1342727 : Blo 467785 1342727 := bstep (se 1 (by rfl) ⟨1007045, by rfl⟩ : syracuseStep 1342727 = 2014091) B2014091
theorem B2098217 : Blo 467785 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B45581453 : Blo 467785 45581453 := bstep (se 3 (by rfl) ⟨8546522, by rfl⟩ : syracuseStep 45581453 = 17093045) B17093045
theorem B3573071 : Blo 467785 3573071 := bstep (se 1 (by rfl) ⟨2679803, by rfl⟩ : syracuseStep 3573071 = 5359607) B5359607
theorem B17139761 : Blo 467785 17139761 := bstep (se 2 (by rfl) ⟨6427410, by rfl⟩ : syracuseStep 17139761 = 12854821) B12854821
theorem B592363 : Blo 467785 592363 := bstep (se 1 (by rfl) ⟨444272, by rfl⟩ : syracuseStep 592363 = 888545) B888545
theorem B3214367 : Blo 467785 3214367 := bstep (se 1 (by rfl) ⟨2410775, by rfl⟩ : syracuseStep 3214367 = 4821551) B4821551
theorem B33066407 : Blo 467785 33066407 := bstep (se 1 (by rfl) ⟨24799805, by rfl⟩ : syracuseStep 33066407 = 49599611) B49599611
theorem B888347 : Blo 467785 888347 := bstep (se 1 (by rfl) ⟨666260, by rfl⟩ : syracuseStep 888347 = 1332521) B1332521
theorem B2854855 : Blo 467785 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B790519 : Blo 467785 790519 := bstep (se 1 (by rfl) ⟨592889, by rfl⟩ : syracuseStep 790519 = 1185779) B1185779
theorem B3018779 : Blo 467785 3018779 := bstep (se 1 (by rfl) ⟨2264084, by rfl⟩ : syracuseStep 3018779 = 4528169) B4528169
theorem B790823 : Blo 467785 790823 := bstep (se 1 (by rfl) ⟨593117, by rfl⟩ : syracuseStep 790823 = 1186235) B1186235
theorem B24482213 : Blo 467785 24482213 := bstep (se 4 (by rfl) ⟨2295207, by rfl⟩ : syracuseStep 24482213 = 4590415) B4590415
theorem B889319 : Blo 467785 889319 := bstep (se 1 (by rfl) ⟨666989, by rfl⟩ : syracuseStep 889319 = 1333979) B1333979
theorem B791815 : Blo 467785 791815 := bstep (se 1 (by rfl) ⟨593861, by rfl⟩ : syracuseStep 791815 = 1187723) B1187723
theorem B3085823 : Blo 467785 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B530023 : Blo 467785 530023 := bstep (se 1 (by rfl) ⟨397517, by rfl⟩ : syracuseStep 530023 = 795035) B795035
theorem B890527 : Blo 467785 890527 := bstep (se 1 (by rfl) ⟨667895, by rfl⟩ : syracuseStep 890527 = 1335791) B1335791
theorem B3381479 : Blo 467785 3381479 := bstep (se 1 (by rfl) ⟨2536109, by rfl⟩ : syracuseStep 3381479 = 5072219) B5072219
theorem B596251 : Blo 467785 596251 := bstep (se 1 (by rfl) ⟨447188, by rfl⟩ : syracuseStep 596251 = 894377) B894377
theorem B1186103 : Blo 467785 1186103 := bstep (se 1 (by rfl) ⟨889577, by rfl⟩ : syracuseStep 1186103 = 1779155) B1779155
theorem B792895 : Blo 467785 792895 := bstep (se 1 (by rfl) ⟨594671, by rfl⟩ : syracuseStep 792895 = 1189343) B1189343
theorem B596479 : Blo 467785 596479 := bstep (se 1 (by rfl) ⟨447359, by rfl⟩ : syracuseStep 596479 = 894719) B894719
theorem B5347943 : Blo 467785 5347943 := bstep (se 1 (by rfl) ⟨4010957, by rfl⟩ : syracuseStep 5347943 = 8021915) B8021915
theorem B1055465 : Blo 467785 1055465 := bstep (se 2 (by rfl) ⟨395799, by rfl⟩ : syracuseStep 1055465 = 791599) B791599
theorem B793327 : Blo 467785 793327 := bstep (se 1 (by rfl) ⟨594995, by rfl⟩ : syracuseStep 793327 = 1189991) B1189991
theorem B1579823 : Blo 467785 1579823 := bstep (se 1 (by rfl) ⟨1184867, by rfl⟩ : syracuseStep 1579823 = 2369735) B2369735
theorem B1186751 : Blo 467785 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B892129 : Blo 467785 892129 := bstep (se 2 (by rfl) ⟨334548, by rfl⟩ : syracuseStep 892129 = 669097) B669097
theorem B1056743 : Blo 467785 1056743 := bstep (se 1 (by rfl) ⟨792557, by rfl⟩ : syracuseStep 1056743 = 1585115) B1585115
theorem B1777727 : Blo 467785 1777727 := bstep (se 1 (by rfl) ⟨1333295, by rfl⟩ : syracuseStep 1777727 = 2666591) B2666591
theorem B1613999 : Blo 467785 1613999 := bstep (se 1 (by rfl) ⟨1210499, by rfl⟩ : syracuseStep 1613999 = 2420999) B2420999
theorem B4497839 : Blo 467785 4497839 := bstep (se 1 (by rfl) ⟨3373379, by rfl⟩ : syracuseStep 4497839 = 6746759) B6746759
theorem B1581929 : Blo 467785 1581929 := bstep (se 2 (by rfl) ⟨593223, by rfl⟩ : syracuseStep 1581929 = 1186447) B1186447
theorem B1058057 : Blo 467785 1058057 := bstep (se 2 (by rfl) ⟨396771, by rfl⟩ : syracuseStep 1058057 = 793543) B793543
theorem B1058255 : Blo 467785 1058255 := bstep (se 1 (by rfl) ⟨793691, by rfl⟩ : syracuseStep 1058255 = 1587383) B1587383
theorem B468639 : Blo 467785 468639 := bstep (se 1 (by rfl) ⟨351479, by rfl⟩ : syracuseStep 468639 = 702959) B702959
theorem B2664359 : Blo 467785 2664359 := bstep (se 1 (by rfl) ⟨1998269, by rfl⟩ : syracuseStep 2664359 = 3996539) B3996539
theorem B895151 : Blo 467785 895151 := bstep (se 1 (by rfl) ⟨671363, by rfl⟩ : syracuseStep 895151 = 1342727) B1342727
theorem B469319 : Blo 467785 469319 := bstep (se 1 (by rfl) ⟨351989, by rfl⟩ : syracuseStep 469319 = 703979) B703979
theorem B3811661 : Blo 467785 3811661 := bstep (se 3 (by rfl) ⟨714686, by rfl⟩ : syracuseStep 3811661 = 1429373) B1429373
theorem B469351 : Blo 467785 469351 := bstep (se 1 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 469351 = 704027) B704027
theorem B1059263 : Blo 467785 1059263 := bstep (se 1 (by rfl) ⟨794447, by rfl⟩ : syracuseStep 1059263 = 1588895) B1588895
theorem B470207 : Blo 467785 470207 := bstep (se 1 (by rfl) ⟨352655, by rfl⟩ : syracuseStep 470207 = 705311) B705311
theorem B1584467 : Blo 467785 1584467 := bstep (se 1 (by rfl) ⟨1188350, by rfl⟩ : syracuseStep 1584467 = 2376701) B2376701
theorem B470511 : Blo 467785 470511 := bstep (se 1 (by rfl) ⟨352883, by rfl⟩ : syracuseStep 470511 = 705767) B705767
theorem B1060379 : Blo 467785 1060379 := bstep (se 1 (by rfl) ⟨795284, by rfl⟩ : syracuseStep 1060379 = 1590569) B1590569
theorem B3124939 : Blo 467785 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B470811 : Blo 467785 470811 := bstep (se 1 (by rfl) ⟨353108, by rfl⟩ : syracuseStep 470811 = 706217) B706217
theorem B470943 : Blo 467785 470943 := bstep (se 1 (by rfl) ⟨353207, by rfl⟩ : syracuseStep 470943 = 706415) B706415
theorem B471067 : Blo 467785 471067 := bstep (se 1 (by rfl) ⟨353300, by rfl⟩ : syracuseStep 471067 = 706601) B706601
theorem B1060955 : Blo 467785 1060955 := bstep (se 1 (by rfl) ⟨795716, by rfl⟩ : syracuseStep 1060955 = 1591433) B1591433
theorem B471231 : Blo 467785 471231 := bstep (se 1 (by rfl) ⟨353423, by rfl⟩ : syracuseStep 471231 = 706847) B706847
theorem B1061063 : Blo 467785 1061063 := bstep (se 1 (by rfl) ⟨795797, by rfl⟩ : syracuseStep 1061063 = 1591595) B1591595
theorem B1585385 : Blo 467785 1585385 := bstep (se 2 (by rfl) ⟨594519, by rfl⟩ : syracuseStep 1585385 = 1189039) B1189039
theorem B471343 : Blo 467785 471343 := bstep (se 1 (by rfl) ⟨353507, by rfl⟩ : syracuseStep 471343 = 707015) B707015
theorem B471663 : Blo 467785 471663 := bstep (se 1 (by rfl) ⟨353747, by rfl⟩ : syracuseStep 471663 = 707495) B707495
theorem B471711 : Blo 467785 471711 := bstep (se 1 (by rfl) ⟨353783, by rfl⟩ : syracuseStep 471711 = 707567) B707567
theorem B1585871 : Blo 467785 1585871 := bstep (se 1 (by rfl) ⟨1189403, by rfl⟩ : syracuseStep 1585871 = 2378807) B2378807
theorem B2372327 : Blo 467785 2372327 := bstep (se 1 (by rfl) ⟨1779245, by rfl⟩ : syracuseStep 2372327 = 3558491) B3558491
theorem B10303199 : Blo 467785 10303199 := bstep (se 1 (by rfl) ⟨7727399, by rfl⟩ : syracuseStep 10303199 = 15454799) B15454799
theorem B5355233 : Blo 467785 5355233 := bstep (se 2 (by rfl) ⟨2008212, by rfl⟩ : syracuseStep 5355233 = 4016425) B4016425
theorem B702299 : Blo 467785 702299 := bstep (se 1 (by rfl) ⟨526724, by rfl⟩ : syracuseStep 702299 = 1053449) B1053449
theorem B702329 : Blo 467785 702329 := bstep (se 2 (by rfl) ⟨263373, by rfl⟩ : syracuseStep 702329 = 526747) B526747
theorem B702377 : Blo 467785 702377 := bstep (se 2 (by rfl) ⟨263391, by rfl⟩ : syracuseStep 702377 = 526783) B526783
theorem B1587167 : Blo 467785 1587167 := bstep (se 1 (by rfl) ⟨1190375, by rfl⟩ : syracuseStep 1587167 = 2380751) B2380751
theorem B1194011 : Blo 467785 1194011 := bstep (se 1 (by rfl) ⟨895508, by rfl⟩ : syracuseStep 1194011 = 1791017) B1791017
theorem B702575 : Blo 467785 702575 := bstep (se 1 (by rfl) ⟨526931, by rfl⟩ : syracuseStep 702575 = 1053863) B1053863
theorem B2013407 : Blo 467785 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B1587815 : Blo 467785 1587815 := bstep (se 1 (by rfl) ⟨1190861, by rfl⟩ : syracuseStep 1587815 = 2381723) B2381723
theorem B703295 : Blo 467785 703295 := bstep (se 1 (by rfl) ⟨527471, by rfl⟩ : syracuseStep 703295 = 1054943) B1054943
theorem B2374595 : Blo 467785 2374595 := bstep (se 1 (by rfl) ⟨1780946, by rfl⟩ : syracuseStep 2374595 = 3561893) B3561893
theorem B1129535 : Blo 467785 1129535 := bstep (se 1 (by rfl) ⟨847151, by rfl⟩ : syracuseStep 1129535 = 1694303) B1694303
theorem B703595 : Blo 467785 703595 := bstep (se 1 (by rfl) ⟨527696, by rfl⟩ : syracuseStep 703595 = 1055393) B1055393
theorem B703727 : Blo 467785 703727 := bstep (se 1 (by rfl) ⟨527795, by rfl⟩ : syracuseStep 703727 = 1055591) B1055591
theorem B703799 : Blo 467785 703799 := bstep (se 1 (by rfl) ⟨527849, by rfl⟩ : syracuseStep 703799 = 1055699) B1055699
theorem B1588571 : Blo 467785 1588571 := bstep (se 1 (by rfl) ⟨1191428, by rfl⟩ : syracuseStep 1588571 = 2382857) B2382857
theorem B1785199 : Blo 467785 1785199 := bstep (se 1 (by rfl) ⟨1338899, by rfl⟩ : syracuseStep 1785199 = 2677799) B2677799
theorem B703871 : Blo 467785 703871 := bstep (se 1 (by rfl) ⟨527903, by rfl⟩ : syracuseStep 703871 = 1055807) B1055807
theorem B704183 : Blo 467785 704183 := bstep (se 1 (by rfl) ⟨528137, by rfl⟩ : syracuseStep 704183 = 1056275) B1056275
theorem B2670509 : Blo 467785 2670509 := bstep (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) B1001441
theorem B6012953 : Blo 467785 6012953 := bstep (se 2 (by rfl) ⟨2254857, by rfl⟩ : syracuseStep 6012953 = 4509715) B4509715
theorem B704567 : Blo 467785 704567 := bstep (se 1 (by rfl) ⟨528425, by rfl⟩ : syracuseStep 704567 = 1056851) B1056851
theorem B704603 : Blo 467785 704603 := bstep (se 1 (by rfl) ⟨528452, by rfl⟩ : syracuseStep 704603 = 1056905) B1056905
theorem B705335 : Blo 467785 705335 := bstep (se 1 (by rfl) ⟨529001, by rfl⟩ : syracuseStep 705335 = 1058003) B1058003
theorem B705449 : Blo 467785 705449 := bstep (se 2 (by rfl) ⟨264543, by rfl⟩ : syracuseStep 705449 = 529087) B529087
theorem B705515 : Blo 467785 705515 := bstep (se 1 (by rfl) ⟨529136, by rfl⟩ : syracuseStep 705515 = 1058273) B1058273
theorem B5588075 : Blo 467785 5588075 := bstep (se 1 (by rfl) ⟨4191056, by rfl⟩ : syracuseStep 5588075 = 8382113) B8382113
theorem B705833 : Blo 467785 705833 := bstep (se 2 (by rfl) ⟨264687, by rfl⟩ : syracuseStep 705833 = 529375) B529375
theorem B476543 : Blo 467785 476543 := bstep (se 1 (by rfl) ⟨357407, by rfl⟩ : syracuseStep 476543 = 714815) B714815
theorem B705983 : Blo 467785 705983 := bstep (se 1 (by rfl) ⟨529487, by rfl⟩ : syracuseStep 705983 = 1058975) B1058975
theorem B1787447 : Blo 467785 1787447 := bstep (se 1 (by rfl) ⟨1340585, by rfl⟩ : syracuseStep 1787447 = 2681171) B2681171
theorem B2377511 : Blo 467785 2377511 := bstep (se 1 (by rfl) ⟨1783133, by rfl⟩ : syracuseStep 2377511 = 3566267) B3566267
theorem B1001339 : Blo 467785 1001339 := bstep (se 1 (by rfl) ⟨751004, by rfl⟩ : syracuseStep 1001339 = 1502009) B1502009
theorem B706427 : Blo 467785 706427 := bstep (se 1 (by rfl) ⟨529820, by rfl⟩ : syracuseStep 706427 = 1059641) B1059641
theorem B1591163 : Blo 467785 1591163 := bstep (se 1 (by rfl) ⟨1193372, by rfl⟩ : syracuseStep 1591163 = 2386745) B2386745
theorem B1591649 : Blo 467785 1591649 := bstep (se 2 (by rfl) ⟨596868, by rfl⟩ : syracuseStep 1591649 = 1193737) B1193737
theorem B1592135 : Blo 467785 1592135 := bstep (se 1 (by rfl) ⟨1194101, by rfl⟩ : syracuseStep 1592135 = 2388203) B2388203
theorem B27413423 : Blo 467785 27413423 := bstep (se 1 (by rfl) ⟨20560067, by rfl⟩ : syracuseStep 27413423 = 41120135) B41120135
theorem B1003099 : Blo 467785 1003099 := bstep (se 1 (by rfl) ⟨752324, by rfl⟩ : syracuseStep 1003099 = 1504649) B1504649
theorem B2379455 : Blo 467785 2379455 := bstep (se 1 (by rfl) ⟨1784591, by rfl⟩ : syracuseStep 2379455 = 3569183) B3569183
theorem B5330447 : Blo 467785 5330447 := bstep (se 1 (by rfl) ⟨3997835, by rfl⟩ : syracuseStep 5330447 = 7995671) B7995671
theorem B2251243 : Blo 467785 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B3399931 : Blo 467785 3399931 := bstep (se 1 (by rfl) ⟨2549948, by rfl⟩ : syracuseStep 3399931 = 5099897) B5099897
theorem B3564809 : Blo 467785 3564809 := bstep (se 2 (by rfl) ⟨1336803, by rfl⟩ : syracuseStep 3564809 = 2673607) B2673607
theorem B1697071 : Blo 467785 1697071 := bstep (se 1 (by rfl) ⟨1272803, by rfl⟩ : syracuseStep 1697071 = 2545607) B2545607
theorem B3567239 : Blo 467785 3567239 := bstep (se 1 (by rfl) ⟨2675429, by rfl⟩ : syracuseStep 3567239 = 5350859) B5350859
theorem B8548573 : Blo 467785 8548573 := bstep (se 3 (by rfl) ⟨1602857, by rfl⟩ : syracuseStep 8548573 = 3205715) B3205715
theorem B1601819 : Blo 467785 1601819 := bstep (se 1 (by rfl) ⟨1201364, by rfl⟩ : syracuseStep 1601819 = 2402729) B2402729
theorem B6779335 : Blo 467785 6779335 := bstep (se 1 (by rfl) ⟨5084501, by rfl⟩ : syracuseStep 6779335 = 10169003) B10169003
theorem B4813303 : Blo 467785 4813303 := bstep (se 1 (by rfl) ⟨3609977, by rfl⟩ : syracuseStep 4813303 = 7219955) B7219955
theorem B1602175 : Blo 467785 1602175 := bstep (se 1 (by rfl) ⟨1201631, by rfl⟩ : syracuseStep 1602175 = 2403263) B2403263
theorem B1505135 : Blo 467785 1505135 := bstep (se 1 (by rfl) ⟨1128851, by rfl⟩ : syracuseStep 1505135 = 2257703) B2257703
theorem B12155483 : Blo 467785 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B2259839 : Blo 467785 2259839 := bstep (se 1 (by rfl) ⟨1694879, by rfl⟩ : syracuseStep 2259839 = 3389759) B3389759
theorem B1801183 : Blo 467785 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B3013807 : Blo 467785 3013807 := bstep (se 1 (by rfl) ⟨2260355, by rfl⟩ : syracuseStep 3013807 = 4520711) B4520711
theorem B9010439 : Blo 467785 9010439 := bstep (se 1 (by rfl) ⟨6757829, by rfl⟩ : syracuseStep 9010439 = 13515659) B13515659
theorem B2262761 : Blo 467785 2262761 := bstep (se 2 (by rfl) ⟨848535, by rfl⟩ : syracuseStep 2262761 = 1697071) B1697071
theorem B527215 : Blo 467785 527215 := bstep (se 1 (by rfl) ⟨395411, by rfl⟩ : syracuseStep 527215 = 790823) B790823
theorem B16321475 : Blo 467785 16321475 := bstep (se 1 (by rfl) ⟨12241106, by rfl⟩ : syracuseStep 16321475 = 24482213) B24482213
theorem B789817 : Blo 467785 789817 := bstep (se 2 (by rfl) ⟨296181, by rfl⟩ : syracuseStep 789817 = 592363) B592363
theorem B8228861 : Blo 467785 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B790735 : Blo 467785 790735 := bstep (se 1 (by rfl) ⟨593051, by rfl⟩ : syracuseStep 790735 = 1186103) B1186103
theorem B1053215 : Blo 467785 1053215 := bstep (se 1 (by rfl) ⟨789911, by rfl⟩ : syracuseStep 1053215 = 1579823) B1579823
theorem B791167 : Blo 467785 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B4166585 : Blo 467785 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B3806473 : Blo 467785 3806473 := bstep (se 2 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 3806473 = 2854855) B2854855
theorem B1054025 : Blo 467785 1054025 := bstep (se 2 (by rfl) ⟨395259, by rfl⟩ : syracuseStep 1054025 = 790519) B790519
theorem B1185151 : Blo 467785 1185151 := bstep (se 1 (by rfl) ⟨888863, by rfl⟩ : syracuseStep 1185151 = 1777727) B1777727
theorem B1054619 : Blo 467785 1054619 := bstep (se 1 (by rfl) ⟨790964, by rfl⟩ : syracuseStep 1054619 = 1581929) B1581929
theorem B2136233 : Blo 467785 2136233 := bstep (se 2 (by rfl) ⟨801087, by rfl⟩ : syracuseStep 2136233 = 1602175) B1602175
theorem B1776239 : Blo 467785 1776239 := bstep (se 1 (by rfl) ⟨1332179, by rfl⟩ : syracuseStep 1776239 = 2664359) B2664359
theorem B1055753 : Blo 467785 1055753 := bstep (se 2 (by rfl) ⟨395907, by rfl⟩ : syracuseStep 1055753 = 791815) B791815
theorem B1187369 : Blo 467785 1187369 := bstep (se 2 (by rfl) ⟨445263, by rfl⟩ : syracuseStep 1187369 = 890527) B890527
theorem B1056311 : Blo 467785 1056311 := bstep (se 1 (by rfl) ⟨792233, by rfl⟩ : syracuseStep 1056311 = 1584467) B1584467
theorem B1056923 : Blo 467785 1056923 := bstep (se 1 (by rfl) ⟨792692, by rfl⟩ : syracuseStep 1056923 = 1585385) B1585385
theorem B795001 : Blo 467785 795001 := bstep (se 2 (by rfl) ⟨298125, by rfl⟩ : syracuseStep 795001 = 596251) B596251
theorem B1057193 : Blo 467785 1057193 := bstep (se 2 (by rfl) ⟨396447, by rfl⟩ : syracuseStep 1057193 = 792895) B792895
theorem B1057247 : Blo 467785 1057247 := bstep (se 1 (by rfl) ⟨792935, by rfl⟩ : syracuseStep 1057247 = 1585871) B1585871
theorem B1581551 : Blo 467785 1581551 := bstep (se 1 (by rfl) ⟨1186163, by rfl⟩ : syracuseStep 1581551 = 2372327) B2372327
theorem B795305 : Blo 467785 795305 := bstep (se 2 (by rfl) ⟨298239, by rfl⟩ : syracuseStep 795305 = 596479) B596479
theorem B1057769 : Blo 467785 1057769 := bstep (se 2 (by rfl) ⟨396663, by rfl⟩ : syracuseStep 1057769 = 793327) B793327
theorem B468199 : Blo 467785 468199 := bstep (se 1 (by rfl) ⟨351149, by rfl⟩ : syracuseStep 468199 = 702299) B702299
theorem B468219 : Blo 467785 468219 := bstep (se 1 (by rfl) ⟨351164, by rfl⟩ : syracuseStep 468219 = 702329) B702329
theorem B468251 : Blo 467785 468251 := bstep (se 1 (by rfl) ⟨351188, by rfl⟩ : syracuseStep 468251 = 702377) B702377
theorem B2401577 : Blo 467785 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B1058111 : Blo 467785 1058111 := bstep (se 1 (by rfl) ⟨793583, by rfl⟩ : syracuseStep 1058111 = 1587167) B1587167
theorem B796007 : Blo 467785 796007 := bstep (se 1 (by rfl) ⟨597005, by rfl⟩ : syracuseStep 796007 = 1194011) B1194011
theorem B2368925 : Blo 467785 2368925 := bstep (se 3 (by rfl) ⟨444173, by rfl⟩ : syracuseStep 2368925 = 888347) B888347
theorem B468383 : Blo 467785 468383 := bstep (se 1 (by rfl) ⟨351287, by rfl⟩ : syracuseStep 468383 = 702575) B702575
theorem B1189505 : Blo 467785 1189505 := bstep (se 2 (by rfl) ⟨446064, by rfl⟩ : syracuseStep 1189505 = 892129) B892129
theorem B8103655 : Blo 467785 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B1058543 : Blo 467785 1058543 := bstep (se 1 (by rfl) ⟨793907, by rfl⟩ : syracuseStep 1058543 = 1587815) B1587815
theorem B468863 : Blo 467785 468863 := bstep (se 1 (by rfl) ⟨351647, by rfl⟩ : syracuseStep 468863 = 703295) B703295
theorem B1583063 : Blo 467785 1583063 := bstep (se 1 (by rfl) ⟨1187297, by rfl⟩ : syracuseStep 1583063 = 2374595) B2374595
theorem B469063 : Blo 467785 469063 := bstep (se 1 (by rfl) ⟨351797, by rfl⟩ : syracuseStep 469063 = 703595) B703595
theorem B469151 : Blo 467785 469151 := bstep (se 1 (by rfl) ⟨351863, by rfl⟩ : syracuseStep 469151 = 703727) B703727
theorem B6006959 : Blo 467785 6006959 := bstep (se 1 (by rfl) ⟨4505219, by rfl⟩ : syracuseStep 6006959 = 9010439) B9010439
theorem B469199 : Blo 467785 469199 := bstep (se 1 (by rfl) ⟨351899, by rfl⟩ : syracuseStep 469199 = 703799) B703799
theorem B1059047 : Blo 467785 1059047 := bstep (se 1 (by rfl) ⟨794285, by rfl⟩ : syracuseStep 1059047 = 1588571) B1588571
theorem B469247 : Blo 467785 469247 := bstep (se 1 (by rfl) ⟨351935, by rfl⟩ : syracuseStep 469247 = 703871) B703871
theorem B469455 : Blo 467785 469455 := bstep (se 1 (by rfl) ⟨352091, by rfl⟩ : syracuseStep 469455 = 704183) B704183
theorem B1780339 : Blo 467785 1780339 := bstep (se 1 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 1780339 = 2670509) B2670509
theorem B4008635 : Blo 467785 4008635 := bstep (se 1 (by rfl) ⟨3006476, by rfl⟩ : syracuseStep 4008635 = 6012953) B6012953
theorem B469711 : Blo 467785 469711 := bstep (se 1 (by rfl) ⟨352283, by rfl⟩ : syracuseStep 469711 = 704567) B704567
theorem B469735 : Blo 467785 469735 := bstep (se 1 (by rfl) ⟨352301, by rfl⟩ : syracuseStep 469735 = 704603) B704603
theorem B4533241 : Blo 467785 4533241 := bstep (se 2 (by rfl) ⟨1699965, by rfl⟩ : syracuseStep 4533241 = 3399931) B3399931
theorem B470223 : Blo 467785 470223 := bstep (se 1 (by rfl) ⟨352667, by rfl⟩ : syracuseStep 470223 = 705335) B705335
theorem B470299 : Blo 467785 470299 := bstep (se 1 (by rfl) ⟨352724, by rfl⟩ : syracuseStep 470299 = 705449) B705449
theorem B470343 : Blo 467785 470343 := bstep (se 1 (by rfl) ⟨352757, by rfl⟩ : syracuseStep 470343 = 705515) B705515
theorem B30387635 : Blo 467785 30387635 := bstep (se 1 (by rfl) ⟨22790726, by rfl⟩ : syracuseStep 30387635 = 45581453) B45581453
theorem B470555 : Blo 467785 470555 := bstep (se 1 (by rfl) ⟨352916, by rfl⟩ : syracuseStep 470555 = 705833) B705833
theorem B470655 : Blo 467785 470655 := bstep (se 1 (by rfl) ⟨352991, by rfl⟩ : syracuseStep 470655 = 705983) B705983
theorem B1191631 : Blo 467785 1191631 := bstep (se 1 (by rfl) ⟨893723, by rfl⟩ : syracuseStep 1191631 = 1787447) B1787447
theorem B1585007 : Blo 467785 1585007 := bstep (se 1 (by rfl) ⟨1188755, by rfl⟩ : syracuseStep 1585007 = 2377511) B2377511
theorem B667559 : Blo 467785 667559 := bstep (se 1 (by rfl) ⟨500669, by rfl⟩ : syracuseStep 667559 = 1001339) B1001339
theorem B470951 : Blo 467785 470951 := bstep (se 1 (by rfl) ⟨353213, by rfl⟩ : syracuseStep 470951 = 706427) B706427
theorem B1060775 : Blo 467785 1060775 := bstep (se 1 (by rfl) ⟨795581, by rfl⟩ : syracuseStep 1060775 = 1591163) B1591163
theorem B2371517 : Blo 467785 2371517 := bstep (se 3 (by rfl) ⟨444659, by rfl⟩ : syracuseStep 2371517 = 889319) B889319
theorem B1061099 : Blo 467785 1061099 := bstep (se 1 (by rfl) ⟨795824, by rfl⟩ : syracuseStep 1061099 = 1591649) B1591649
theorem B1061423 : Blo 467785 1061423 := bstep (se 1 (by rfl) ⟨796067, by rfl⟩ : syracuseStep 1061423 = 1592135) B1592135
theorem B2142911 : Blo 467785 2142911 := bstep (se 1 (by rfl) ⟨1607183, by rfl⟩ : syracuseStep 2142911 = 3214367) B3214367
theorem B1586303 : Blo 467785 1586303 := bstep (se 1 (by rfl) ⟨1189727, by rfl⟩ : syracuseStep 1586303 = 2379455) B2379455
theorem B12006629 : Blo 467785 12006629 := bstep (se 4 (by rfl) ⟨1125621, by rfl⟩ : syracuseStep 12006629 = 2251243) B2251243
theorem B2012519 : Blo 467785 2012519 := bstep (se 1 (by rfl) ⟨1509389, by rfl⟩ : syracuseStep 2012519 = 3018779) B3018779
theorem B3553631 : Blo 467785 3553631 := bstep (se 1 (by rfl) ⟨2665223, by rfl⟩ : syracuseStep 3553631 = 5330447) B5330447
theorem B703643 : Blo 467785 703643 := bstep (se 1 (by rfl) ⟨527732, by rfl⟩ : syracuseStep 703643 = 1055465) B1055465
theorem B704495 : Blo 467785 704495 := bstep (se 1 (by rfl) ⟨528371, by rfl⟩ : syracuseStep 704495 = 1056743) B1056743
theorem B2998559 : Blo 467785 2998559 := bstep (se 1 (by rfl) ⟨2248919, by rfl⟩ : syracuseStep 2998559 = 4497839) B4497839
theorem B2376539 : Blo 467785 2376539 := bstep (se 1 (by rfl) ⟨1782404, by rfl⟩ : syracuseStep 2376539 = 3564809) B3564809
theorem B705371 : Blo 467785 705371 := bstep (se 1 (by rfl) ⟨529028, by rfl⟩ : syracuseStep 705371 = 1058057) B1058057
theorem B705503 : Blo 467785 705503 := bstep (se 1 (by rfl) ⟨529127, by rfl⟩ : syracuseStep 705503 = 1058255) B1058255
theorem B2541107 : Blo 467785 2541107 := bstep (se 1 (by rfl) ⟨1905830, by rfl⟩ : syracuseStep 2541107 = 3811661) B3811661
theorem B706175 : Blo 467785 706175 := bstep (se 1 (by rfl) ⟨529631, by rfl⟩ : syracuseStep 706175 = 1059263) B1059263
theorem B706697 : Blo 467785 706697 := bstep (se 2 (by rfl) ⟨265011, by rfl⟩ : syracuseStep 706697 = 530023) B530023
theorem B706919 : Blo 467785 706919 := bstep (se 1 (by rfl) ⟨530189, by rfl⟩ : syracuseStep 706919 = 1060379) B1060379
theorem B2378159 : Blo 467785 2378159 := bstep (se 1 (by rfl) ⟨1783619, by rfl⟩ : syracuseStep 2378159 = 3567239) B3567239
theorem B707303 : Blo 467785 707303 := bstep (se 1 (by rfl) ⟨530477, by rfl⟩ : syracuseStep 707303 = 1060955) B1060955
theorem B707375 : Blo 467785 707375 := bstep (se 1 (by rfl) ⟨530531, by rfl⟩ : syracuseStep 707375 = 1061063) B1061063
theorem B1067879 : Blo 467785 1067879 := bstep (se 1 (by rfl) ⟨800909, by rfl⟩ : syracuseStep 1067879 = 1601819) B1601819
theorem B6868799 : Blo 467785 6868799 := bstep (se 1 (by rfl) ⟨5151599, by rfl⟩ : syracuseStep 6868799 = 10303199) B10303199
theorem B1003423 : Blo 467785 1003423 := bstep (se 1 (by rfl) ⟨752567, by rfl⟩ : syracuseStep 1003423 = 1505135) B1505135
theorem B4018409 : Blo 467785 4018409 := bstep (se 2 (by rfl) ⟨1506903, by rfl⟩ : syracuseStep 4018409 = 3013807) B3013807
theorem B2380265 : Blo 467785 2380265 := bstep (se 2 (by rfl) ⟨892599, by rfl⟩ : syracuseStep 2380265 = 1785199) B1785199
theorem B1398811 : Blo 467785 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B3725383 : Blo 467785 3725383 := bstep (se 1 (by rfl) ⟨2794037, by rfl⟩ : syracuseStep 3725383 = 5588075) B5588075
theorem B2382047 : Blo 467785 2382047 := bstep (se 1 (by rfl) ⟨1786535, by rfl⟩ : syracuseStep 2382047 = 3573071) B3573071
theorem B11426507 : Blo 467785 11426507 := bstep (se 1 (by rfl) ⟨8569880, by rfl⟩ : syracuseStep 11426507 = 17139761) B17139761
theorem B18275615 : Blo 467785 18275615 := bstep (se 1 (by rfl) ⟨13706711, by rfl⟩ : syracuseStep 18275615 = 27413423) B27413423
theorem B1270781 : Blo 467785 1270781 := bstep (se 3 (by rfl) ⟨238271, by rfl⟩ : syracuseStep 1270781 = 476543) B476543
theorem B2254319 : Blo 467785 2254319 := bstep (se 1 (by rfl) ⟨1690739, by rfl⟩ : syracuseStep 2254319 = 3381479) B3381479
theorem B3565295 : Blo 467785 3565295 := bstep (se 1 (by rfl) ⟨2673971, by rfl⟩ : syracuseStep 3565295 = 5347943) B5347943
theorem B1337465 : Blo 467785 1337465 := bstep (se 2 (by rfl) ⟨501549, by rfl⟩ : syracuseStep 1337465 = 1003099) B1003099
theorem B1075999 : Blo 467785 1075999 := bstep (se 1 (by rfl) ⟨806999, by rfl⟩ : syracuseStep 1075999 = 1613999) B1613999
theorem B11398097 : Blo 467785 11398097 := bstep (se 2 (by rfl) ⟨4274286, by rfl⟩ : syracuseStep 11398097 = 8548573) B8548573
theorem B2387069 : Blo 467785 2387069 := bstep (se 3 (by rfl) ⟨447575, by rfl⟩ : syracuseStep 2387069 = 895151) B895151
theorem B9039113 : Blo 467785 9039113 := bstep (se 2 (by rfl) ⟨3389667, by rfl⟩ : syracuseStep 9039113 = 6779335) B6779335
theorem B6417737 : Blo 467785 6417737 := bstep (se 2 (by rfl) ⟨2406651, by rfl⟩ : syracuseStep 6417737 = 4813303) B4813303
theorem B88177085 : Blo 467785 88177085 := bstep (se 3 (by rfl) ⟨16533203, by rfl⟩ : syracuseStep 88177085 = 33066407) B33066407
theorem B3570155 : Blo 467785 3570155 := bstep (se 1 (by rfl) ⟨2677616, by rfl⟩ : syracuseStep 3570155 = 5355233) B5355233
theorem B1342271 : Blo 467785 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B1506559 : Blo 467785 1506559 := bstep (se 1 (by rfl) ⟨1129919, by rfl⟩ : syracuseStep 1506559 = 2259839) B2259839
theorem B753023 : Blo 467785 753023 := bstep (se 1 (by rfl) ⟨564767, by rfl⟩ : syracuseStep 753023 = 1129535) B1129535
theorem B1999039 : Blo 467785 1999039 := bstep (se 1 (by rfl) ⟨1499279, by rfl⟩ : syracuseStep 1999039 = 2998559) B2998559
theorem B1508507 : Blo 467785 1508507 := bstep (se 1 (by rfl) ⟨1131380, by rfl⟩ : syracuseStep 1508507 = 2262761) B2262761
theorem B10880983 : Blo 467785 10880983 := bstep (se 1 (by rfl) ⟨8160737, by rfl⟩ : syracuseStep 10880983 = 16321475) B16321475
theorem B1184159 : Blo 467785 1184159 := bstep (se 1 (by rfl) ⟨888119, by rfl⟩ : syracuseStep 1184159 = 1776239) B1776239
theorem B1053089 : Blo 467785 1053089 := bstep (se 2 (by rfl) ⟨394908, by rfl⟩ : syracuseStep 1053089 = 789817) B789817
theorem B791579 : Blo 467785 791579 := bstep (se 1 (by rfl) ⟨593684, by rfl⟩ : syracuseStep 791579 = 1187369) B1187369
theorem B1054313 : Blo 467785 1054313 := bstep (se 2 (by rfl) ⟨395367, by rfl⟩ : syracuseStep 1054313 = 790735) B790735
theorem B1054367 : Blo 467785 1054367 := bstep (se 1 (by rfl) ⟨790775, by rfl⟩ : syracuseStep 1054367 = 1581551) B1581551
theorem B530203 : Blo 467785 530203 := bstep (se 1 (by rfl) ⟨397652, by rfl⟩ : syracuseStep 530203 = 795305) B795305
theorem B1054889 : Blo 467785 1054889 := bstep (se 2 (by rfl) ⟨395583, by rfl⟩ : syracuseStep 1054889 = 791167) B791167
theorem B530671 : Blo 467785 530671 := bstep (se 1 (by rfl) ⟨398003, by rfl⟩ : syracuseStep 530671 = 796007) B796007
theorem B1579283 : Blo 467785 1579283 := bstep (se 1 (by rfl) ⟨1184462, by rfl⟩ : syracuseStep 1579283 = 2368925) B2368925
theorem B793003 : Blo 467785 793003 := bstep (se 1 (by rfl) ⟨594752, by rfl⟩ : syracuseStep 793003 = 1189505) B1189505
theorem B1055375 : Blo 467785 1055375 := bstep (se 1 (by rfl) ⟨791531, by rfl⟩ : syracuseStep 1055375 = 1583063) B1583063
theorem B891643 : Blo 467785 891643 := bstep (se 1 (by rfl) ⟨668732, by rfl⟩ : syracuseStep 891643 = 1337465) B1337465
theorem B4004639 : Blo 467785 4004639 := bstep (se 1 (by rfl) ⟨3003479, by rfl⟩ : syracuseStep 4004639 = 6006959) B6006959
theorem B1580201 : Blo 467785 1580201 := bstep (se 2 (by rfl) ⟨592575, by rfl⟩ : syracuseStep 1580201 = 1185151) B1185151
theorem B3579389 : Blo 467785 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B20258423 : Blo 467785 20258423 := bstep (se 1 (by rfl) ⟨15193817, by rfl⟩ : syracuseStep 20258423 = 30387635) B30387635
theorem B1056671 : Blo 467785 1056671 := bstep (se 1 (by rfl) ⟨792503, by rfl⟩ : syracuseStep 1056671 = 1585007) B1585007
theorem B1581011 : Blo 467785 1581011 := bstep (se 1 (by rfl) ⟨1185758, by rfl⟩ : syracuseStep 1581011 = 2371517) B2371517
theorem B1057535 : Blo 467785 1057535 := bstep (se 1 (by rfl) ⟨793151, by rfl⟩ : syracuseStep 1057535 = 1586303) B1586303
theorem B8004419 : Blo 467785 8004419 := bstep (se 1 (by rfl) ⟨6003314, by rfl⟩ : syracuseStep 8004419 = 12006629) B12006629
theorem B2008061 : Blo 467785 2008061 := bstep (se 3 (by rfl) ⟨376511, by rfl⟩ : syracuseStep 2008061 = 753023) B753023
theorem B2369087 : Blo 467785 2369087 := bstep (se 1 (by rfl) ⟨1776815, by rfl⟩ : syracuseStep 2369087 = 3553631) B3553631
theorem B2008745 : Blo 467785 2008745 := bstep (se 2 (by rfl) ⟨753279, by rfl⟩ : syracuseStep 2008745 = 1506559) B1506559
theorem B469095 : Blo 467785 469095 := bstep (se 1 (by rfl) ⟨351821, by rfl⟩ : syracuseStep 469095 = 703643) B703643
theorem B1780157 : Blo 467785 1780157 := bstep (se 3 (by rfl) ⟨333779, by rfl⟩ : syracuseStep 1780157 = 667559) B667559
theorem B469663 : Blo 467785 469663 := bstep (se 1 (by rfl) ⟨352247, by rfl⟩ : syracuseStep 469663 = 704495) B704495
theorem B1060001 : Blo 467785 1060001 := bstep (se 2 (by rfl) ⟨397500, by rfl⟩ : syracuseStep 1060001 = 795001) B795001
theorem B1584359 : Blo 467785 1584359 := bstep (se 1 (by rfl) ⟨1188269, by rfl⟩ : syracuseStep 1584359 = 2376539) B2376539
theorem B470247 : Blo 467785 470247 := bstep (se 1 (by rfl) ⟨352685, by rfl⟩ : syracuseStep 470247 = 705371) B705371
theorem B470335 : Blo 467785 470335 := bstep (se 1 (by rfl) ⟨352751, by rfl⟩ : syracuseStep 470335 = 705503) B705503
theorem B470783 : Blo 467785 470783 := bstep (se 1 (by rfl) ⟨353087, by rfl⟩ : syracuseStep 470783 = 706175) B706175
theorem B471131 : Blo 467785 471131 := bstep (se 1 (by rfl) ⟨353348, by rfl⟩ : syracuseStep 471131 = 706697) B706697
theorem B471279 : Blo 467785 471279 := bstep (se 1 (by rfl) ⟨353459, by rfl⟩ : syracuseStep 471279 = 706919) B706919
theorem B1585439 : Blo 467785 1585439 := bstep (se 1 (by rfl) ⟨1189079, by rfl⟩ : syracuseStep 1585439 = 2378159) B2378159
theorem B471535 : Blo 467785 471535 := bstep (se 1 (by rfl) ⟨353651, by rfl⟩ : syracuseStep 471535 = 707303) B707303
theorem B471583 : Blo 467785 471583 := bstep (se 1 (by rfl) ⟨353687, by rfl⟩ : syracuseStep 471583 = 707375) B707375
theorem B5485907 : Blo 467785 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B1586843 : Blo 467785 1586843 := bstep (se 1 (by rfl) ⟨1190132, by rfl⟩ : syracuseStep 1586843 = 2380265) B2380265
theorem B702143 : Blo 467785 702143 := bstep (se 1 (by rfl) ⟨526607, by rfl⟩ : syracuseStep 702143 = 1053215) B1053215
theorem B2373785 : Blo 467785 2373785 := bstep (se 2 (by rfl) ⟨890169, by rfl⟩ : syracuseStep 2373785 = 1780339) B1780339
theorem B702683 : Blo 467785 702683 := bstep (se 1 (by rfl) ⟨527012, by rfl⟩ : syracuseStep 702683 = 1054025) B1054025
theorem B702953 : Blo 467785 702953 := bstep (se 2 (by rfl) ⟨263607, by rfl⟩ : syracuseStep 702953 = 527215) B527215
theorem B703079 : Blo 467785 703079 := bstep (se 1 (by rfl) ⟨527309, by rfl⟩ : syracuseStep 703079 = 1054619) B1054619
theorem B6044321 : Blo 467785 6044321 := bstep (se 2 (by rfl) ⟨2266620, by rfl⟩ : syracuseStep 6044321 = 4533241) B4533241
theorem B1424155 : Blo 467785 1424155 := bstep (se 1 (by rfl) ⟨1068116, by rfl⟩ : syracuseStep 1424155 = 2136233) B2136233
theorem B1588031 : Blo 467785 1588031 := bstep (se 1 (by rfl) ⟨1191023, by rfl⟩ : syracuseStep 1588031 = 2382047) B2382047
theorem B7617671 : Blo 467785 7617671 := bstep (se 1 (by rfl) ⟨5713253, by rfl⟩ : syracuseStep 7617671 = 11426507) B11426507
theorem B703835 : Blo 467785 703835 := bstep (se 1 (by rfl) ⟨527876, by rfl⟩ : syracuseStep 703835 = 1055753) B1055753
theorem B1588841 : Blo 467785 1588841 := bstep (se 2 (by rfl) ⟨595815, by rfl⟩ : syracuseStep 1588841 = 1191631) B1191631
theorem B704207 : Blo 467785 704207 := bstep (se 1 (by rfl) ⟨528155, by rfl⟩ : syracuseStep 704207 = 1056311) B1056311
theorem B704615 : Blo 467785 704615 := bstep (se 1 (by rfl) ⟨528461, by rfl⟩ : syracuseStep 704615 = 1056923) B1056923
theorem B704795 : Blo 467785 704795 := bstep (se 1 (by rfl) ⟨528596, by rfl⟩ : syracuseStep 704795 = 1057193) B1057193
theorem B704831 : Blo 467785 704831 := bstep (se 1 (by rfl) ⟨528623, by rfl⟩ : syracuseStep 704831 = 1057247) B1057247
theorem B705179 : Blo 467785 705179 := bstep (se 1 (by rfl) ⟨528884, by rfl⟩ : syracuseStep 705179 = 1057769) B1057769
theorem B705407 : Blo 467785 705407 := bstep (se 1 (by rfl) ⟨529055, by rfl⟩ : syracuseStep 705407 = 1058111) B1058111
theorem B2376863 : Blo 467785 2376863 := bstep (se 1 (by rfl) ⟨1782647, by rfl⟩ : syracuseStep 2376863 = 3565295) B3565295
theorem B705695 : Blo 467785 705695 := bstep (se 1 (by rfl) ⟨529271, by rfl⟩ : syracuseStep 705695 = 1058543) B1058543
theorem B706031 : Blo 467785 706031 := bstep (se 1 (by rfl) ⟨529523, by rfl⟩ : syracuseStep 706031 = 1059047) B1059047
theorem B2672423 : Blo 467785 2672423 := bstep (se 1 (by rfl) ⟨2004317, by rfl⟩ : syracuseStep 2672423 = 4008635) B4008635
theorem B1591379 : Blo 467785 1591379 := bstep (se 1 (by rfl) ⟨1193534, by rfl⟩ : syracuseStep 1591379 = 2387069) B2387069
theorem B4278491 : Blo 467785 4278491 := bstep (se 1 (by rfl) ⟨3208868, by rfl⟩ : syracuseStep 4278491 = 6417737) B6417737
theorem B707183 : Blo 467785 707183 := bstep (se 1 (by rfl) ⟨530387, by rfl⟩ : syracuseStep 707183 = 1060775) B1060775
theorem B4967177 : Blo 467785 4967177 := bstep (se 2 (by rfl) ⟨1862691, by rfl⟩ : syracuseStep 4967177 = 3725383) B3725383
theorem B707399 : Blo 467785 707399 := bstep (se 1 (by rfl) ⟨530549, by rfl⟩ : syracuseStep 707399 = 1061099) B1061099
theorem B707615 : Blo 467785 707615 := bstep (se 1 (by rfl) ⟨530711, by rfl⟩ : syracuseStep 707615 = 1061423) B1061423
theorem B1428607 : Blo 467785 1428607 := bstep (se 1 (by rfl) ⟨1071455, by rfl⟩ : syracuseStep 1428607 = 2142911) B2142911
theorem B2380103 : Blo 467785 2380103 := bstep (se 1 (by rfl) ⟨1785077, by rfl⟩ : syracuseStep 2380103 = 3570155) B3570155
theorem B1694071 : Blo 467785 1694071 := bstep (se 1 (by rfl) ⟨1270553, by rfl⟩ : syracuseStep 1694071 = 2541107) B2541107
theorem B711919 : Blo 467785 711919 := bstep (se 1 (by rfl) ⟨533939, by rfl⟩ : syracuseStep 711919 = 1067879) B1067879
theorem B4579199 : Blo 467785 4579199 := bstep (se 1 (by rfl) ⟨3434399, by rfl⟩ : syracuseStep 4579199 = 6868799) B6868799
theorem B2678939 : Blo 467785 2678939 := bstep (se 1 (by rfl) ⟨2009204, by rfl⟩ : syracuseStep 2678939 = 4018409) B4018409
theorem B2777723 : Blo 467785 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B1434665 : Blo 467785 1434665 := bstep (se 2 (by rfl) ⟨537999, by rfl⟩ : syracuseStep 1434665 = 1075999) B1075999
theorem B12183743 : Blo 467785 12183743 := bstep (se 1 (by rfl) ⟨9137807, by rfl⟩ : syracuseStep 12183743 = 18275615) B18275615
theorem B1337897 : Blo 467785 1337897 := bstep (se 2 (by rfl) ⟨501711, by rfl⟩ : syracuseStep 1337897 = 1003423) B1003423
theorem B847187 : Blo 467785 847187 := bstep (se 1 (by rfl) ⟨635390, by rfl⟩ : syracuseStep 847187 = 1270781) B1270781
theorem B1601051 : Blo 467785 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B1502879 : Blo 467785 1502879 := bstep (se 1 (by rfl) ⟨1127159, by rfl⟩ : syracuseStep 1502879 = 2254319) B2254319
theorem B5075297 : Blo 467785 5075297 := bstep (se 2 (by rfl) ⟨1903236, by rfl⟩ : syracuseStep 5075297 = 3806473) B3806473
theorem B7598731 : Blo 467785 7598731 := bstep (se 1 (by rfl) ⟨5699048, by rfl⟩ : syracuseStep 7598731 = 11398097) B11398097
theorem B6026075 : Blo 467785 6026075 := bstep (se 1 (by rfl) ⟨4519556, by rfl⟩ : syracuseStep 6026075 = 9039113) B9039113
theorem B1865081 : Blo 467785 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B1341679 : Blo 467785 1341679 := bstep (se 1 (by rfl) ⟨1006259, by rfl⟩ : syracuseStep 1341679 = 2012519) B2012519
theorem B43219493 : Blo 467785 43219493 := bstep (se 4 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 43219493 = 8103655) B8103655
theorem B58784723 : Blo 467785 58784723 := bstep (se 1 (by rfl) ⟨44088542, by rfl⟩ : syracuseStep 58784723 = 88177085) B88177085
theorem B2852327 : Blo 467785 2852327 := bstep (se 1 (by rfl) ⟨2139245, by rfl⟩ : syracuseStep 2852327 = 4278491) B4278491
theorem B789439 : Blo 467785 789439 := bstep (se 1 (by rfl) ⟨592079, by rfl⟩ : syracuseStep 789439 = 1184159) B1184159
theorem B527719 : Blo 467785 527719 := bstep (se 1 (by rfl) ⟨395789, by rfl⟩ : syracuseStep 527719 = 791579) B791579
theorem B1904809 : Blo 467785 1904809 := bstep (se 2 (by rfl) ⟨714303, by rfl⟩ : syracuseStep 1904809 = 1428607) B1428607
theorem B1052855 : Blo 467785 1052855 := bstep (se 1 (by rfl) ⟨789641, by rfl⟩ : syracuseStep 1052855 = 1579283) B1579283
theorem B1053467 : Blo 467785 1053467 := bstep (se 1 (by rfl) ⟨790100, by rfl⟩ : syracuseStep 1053467 = 1580201) B1580201
theorem B13505615 : Blo 467785 13505615 := bstep (se 1 (by rfl) ⟨10129211, by rfl⟩ : syracuseStep 13505615 = 20258423) B20258423
theorem B3052799 : Blo 467785 3052799 := bstep (se 1 (by rfl) ⟨2289599, by rfl⟩ : syracuseStep 3052799 = 4579199) B4579199
theorem B1054007 : Blo 467785 1054007 := bstep (se 1 (by rfl) ⟨790505, by rfl⟩ : syracuseStep 1054007 = 1581011) B1581011
theorem B956443 : Blo 467785 956443 := bstep (se 1 (by rfl) ⟨717332, by rfl⟩ : syracuseStep 956443 = 1434665) B1434665
theorem B10131641 : Blo 467785 10131641 := bstep (se 2 (by rfl) ⟨3799365, by rfl⟩ : syracuseStep 10131641 = 7598731) B7598731
theorem B1579391 : Blo 467785 1579391 := bstep (se 1 (by rfl) ⟨1184543, by rfl⟩ : syracuseStep 1579391 = 2369087) B2369087
theorem B1186771 : Blo 467785 1186771 := bstep (se 1 (by rfl) ⟨890078, by rfl⟩ : syracuseStep 1186771 = 1780157) B1780157
theorem B13245805 : Blo 467785 13245805 := bstep (se 3 (by rfl) ⟨2483588, by rfl⟩ : syracuseStep 13245805 = 4967177) B4967177
theorem B1056239 : Blo 467785 1056239 := bstep (se 1 (by rfl) ⟨792179, by rfl⟩ : syracuseStep 1056239 = 1584359) B1584359
theorem B564791 : Blo 467785 564791 := bstep (se 1 (by rfl) ⟨423593, by rfl⟩ : syracuseStep 564791 = 847187) B847187
theorem B1056959 : Blo 467785 1056959 := bstep (se 1 (by rfl) ⟨792719, by rfl⟩ : syracuseStep 1056959 = 1585439) B1585439
theorem B3383531 : Blo 467785 3383531 := bstep (se 1 (by rfl) ⟨2537648, by rfl⟩ : syracuseStep 3383531 = 5075297) B5075297
theorem B1057337 : Blo 467785 1057337 := bstep (se 2 (by rfl) ⟨396501, by rfl⟩ : syracuseStep 1057337 = 793003) B793003
theorem B1188857 : Blo 467785 1188857 := bstep (se 2 (by rfl) ⟨445821, by rfl⟩ : syracuseStep 1188857 = 891643) B891643
theorem B1057895 : Blo 467785 1057895 := bstep (se 1 (by rfl) ⟨793421, by rfl⟩ : syracuseStep 1057895 = 1586843) B1586843
theorem B468095 : Blo 467785 468095 := bstep (se 1 (by rfl) ⟨351071, by rfl⟩ : syracuseStep 468095 = 702143) B702143
theorem B4269469 : Blo 467785 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B1582523 : Blo 467785 1582523 := bstep (se 1 (by rfl) ⟨1186892, by rfl⟩ : syracuseStep 1582523 = 2373785) B2373785
theorem B468455 : Blo 467785 468455 := bstep (se 1 (by rfl) ⟨351341, by rfl⟩ : syracuseStep 468455 = 702683) B702683
theorem B468635 : Blo 467785 468635 := bstep (se 1 (by rfl) ⟨351476, by rfl⟩ : syracuseStep 468635 = 702953) B702953
theorem B28812995 : Blo 467785 28812995 := bstep (se 1 (by rfl) ⟨21609746, by rfl⟩ : syracuseStep 28812995 = 43219493) B43219493
theorem B468719 : Blo 467785 468719 := bstep (se 1 (by rfl) ⟨351539, by rfl⟩ : syracuseStep 468719 = 703079) B703079
theorem B4007677 : Blo 467785 4007677 := bstep (se 3 (by rfl) ⟨751439, by rfl⟩ : syracuseStep 4007677 = 1502879) B1502879
theorem B1058687 : Blo 467785 1058687 := bstep (se 1 (by rfl) ⟨794015, by rfl⟩ : syracuseStep 1058687 = 1588031) B1588031
theorem B469223 : Blo 467785 469223 := bstep (se 1 (by rfl) ⟨351917, by rfl⟩ : syracuseStep 469223 = 703835) B703835
theorem B1059227 : Blo 467785 1059227 := bstep (se 1 (by rfl) ⟨794420, by rfl⟩ : syracuseStep 1059227 = 1588841) B1588841
theorem B469471 : Blo 467785 469471 := bstep (se 1 (by rfl) ⟨352103, by rfl⟩ : syracuseStep 469471 = 704207) B704207
theorem B469743 : Blo 467785 469743 := bstep (se 1 (by rfl) ⟨352307, by rfl⟩ : syracuseStep 469743 = 704615) B704615
theorem B469863 : Blo 467785 469863 := bstep (se 1 (by rfl) ⟨352397, by rfl⟩ : syracuseStep 469863 = 704795) B704795
theorem B469887 : Blo 467785 469887 := bstep (se 1 (by rfl) ⟨352415, by rfl⟩ : syracuseStep 469887 = 704831) B704831
theorem B2665385 : Blo 467785 2665385 := bstep (se 2 (by rfl) ⟨999519, by rfl⟩ : syracuseStep 2665385 = 1999039) B1999039
theorem B470119 : Blo 467785 470119 := bstep (se 1 (by rfl) ⟨352589, by rfl⟩ : syracuseStep 470119 = 705179) B705179
theorem B470271 : Blo 467785 470271 := bstep (se 1 (by rfl) ⟨352703, by rfl⟩ : syracuseStep 470271 = 705407) B705407
theorem B1584575 : Blo 467785 1584575 := bstep (se 1 (by rfl) ⟨1188431, by rfl⟩ : syracuseStep 1584575 = 2376863) B2376863
theorem B470463 : Blo 467785 470463 := bstep (se 1 (by rfl) ⟨352847, by rfl⟩ : syracuseStep 470463 = 705695) B705695
theorem B470687 : Blo 467785 470687 := bstep (se 1 (by rfl) ⟨353015, by rfl⟩ : syracuseStep 470687 = 706031) B706031
theorem B1781615 : Blo 467785 1781615 := bstep (se 1 (by rfl) ⟨1336211, by rfl⟩ : syracuseStep 1781615 = 2672423) B2672423
theorem B1060919 : Blo 467785 1060919 := bstep (se 1 (by rfl) ⟨795689, by rfl⟩ : syracuseStep 1060919 = 1591379) B1591379
theorem B471455 : Blo 467785 471455 := bstep (se 1 (by rfl) ⟨353591, by rfl⟩ : syracuseStep 471455 = 707183) B707183
theorem B471599 : Blo 467785 471599 := bstep (se 1 (by rfl) ⟨353699, by rfl⟩ : syracuseStep 471599 = 707399) B707399
theorem B471743 : Blo 467785 471743 := bstep (se 1 (by rfl) ⟨353807, by rfl⟩ : syracuseStep 471743 = 707615) B707615
theorem B1586735 : Blo 467785 1586735 := bstep (se 1 (by rfl) ⟨1190051, by rfl⟩ : syracuseStep 1586735 = 2380103) B2380103
theorem B702059 : Blo 467785 702059 := bstep (se 1 (by rfl) ⟨526544, by rfl⟩ : syracuseStep 702059 = 1053089) B1053089
theorem B14629085 : Blo 467785 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B702875 : Blo 467785 702875 := bstep (se 1 (by rfl) ⟨527156, by rfl⟩ : syracuseStep 702875 = 1054313) B1054313
theorem B702911 : Blo 467785 702911 := bstep (se 1 (by rfl) ⟨527183, by rfl⟩ : syracuseStep 702911 = 1054367) B1054367
theorem B703259 : Blo 467785 703259 := bstep (se 1 (by rfl) ⟨527444, by rfl⟩ : syracuseStep 703259 = 1054889) B1054889
theorem B703583 : Blo 467785 703583 := bstep (se 1 (by rfl) ⟨527687, by rfl⟩ : syracuseStep 703583 = 1055375) B1055375
theorem B2669759 : Blo 467785 2669759 := bstep (se 1 (by rfl) ⟨2002319, by rfl⟩ : syracuseStep 2669759 = 4004639) B4004639
theorem B704447 : Blo 467785 704447 := bstep (se 1 (by rfl) ⟨528335, by rfl⟩ : syracuseStep 704447 = 1056671) B1056671
theorem B1785959 : Blo 467785 1785959 := bstep (se 1 (by rfl) ⟨1339469, by rfl⟩ : syracuseStep 1785959 = 2678939) B2678939
theorem B1851815 : Blo 467785 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B32489981 : Blo 467785 32489981 := bstep (se 3 (by rfl) ⟨6091871, by rfl⟩ : syracuseStep 32489981 = 12183743) B12183743
theorem B705023 : Blo 467785 705023 := bstep (se 1 (by rfl) ⟨528767, by rfl⟩ : syracuseStep 705023 = 1057535) B1057535
theorem B706667 : Blo 467785 706667 := bstep (se 1 (by rfl) ⟨530000, by rfl⟩ : syracuseStep 706667 = 1060001) B1060001
theorem B706937 : Blo 467785 706937 := bstep (se 2 (by rfl) ⟨265101, by rfl⟩ : syracuseStep 706937 = 530203) B530203
theorem B1788905 : Blo 467785 1788905 := bstep (se 2 (by rfl) ⟨670839, by rfl⟩ : syracuseStep 1788905 = 1341679) B1341679
theorem B707561 : Blo 467785 707561 := bstep (se 2 (by rfl) ⟨265335, by rfl⟩ : syracuseStep 707561 = 530671) B530671
theorem B4017383 : Blo 467785 4017383 := bstep (se 1 (by rfl) ⟨3013037, by rfl⟩ : syracuseStep 4017383 = 6026075) B6026075
theorem B1005671 : Blo 467785 1005671 := bstep (se 1 (by rfl) ⟨754253, by rfl⟩ : syracuseStep 1005671 = 1508507) B1508507
theorem B2386259 : Blo 467785 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B5336279 : Blo 467785 5336279 := bstep (se 1 (by rfl) ⟨4002209, by rfl⟩ : syracuseStep 5336279 = 8004419) B8004419
theorem B1338707 : Blo 467785 1338707 := bstep (se 1 (by rfl) ⟨1004030, by rfl⟩ : syracuseStep 1338707 = 2008061) B2008061
theorem B1339163 : Blo 467785 1339163 := bstep (se 1 (by rfl) ⟨1004372, by rfl⟩ : syracuseStep 1339163 = 2008745) B2008745
theorem B3567725 : Blo 467785 3567725 := bstep (se 3 (by rfl) ⟨668948, by rfl⟩ : syracuseStep 3567725 = 1337897) B1337897
theorem B2258761 : Blo 467785 2258761 := bstep (se 2 (by rfl) ⟨847035, by rfl⟩ : syracuseStep 2258761 = 1694071) B1694071
theorem B1243387 : Blo 467785 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B1898873 : Blo 467785 1898873 := bstep (se 2 (by rfl) ⟨712077, by rfl⟩ : syracuseStep 1898873 = 1424155) B1424155
theorem B949225 : Blo 467785 949225 := bstep (se 2 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 949225 = 711919) B711919
theorem B4029547 : Blo 467785 4029547 := bstep (se 1 (by rfl) ⟨3022160, by rfl⟩ : syracuseStep 4029547 = 6044321) B6044321
theorem B39189815 : Blo 467785 39189815 := bstep (se 1 (by rfl) ⟨29392361, by rfl⟩ : syracuseStep 39189815 = 58784723) B58784723
theorem B5078447 : Blo 467785 5078447 := bstep (se 1 (by rfl) ⟨3808835, by rfl⟩ : syracuseStep 5078447 = 7617671) B7617671
theorem B58031909 : Blo 467785 58031909 := bstep (se 4 (by rfl) ⟨5440491, by rfl⟩ : syracuseStep 58031909 = 10880983) B10880983
theorem B21659987 : Blo 467785 21659987 := bstep (se 1 (by rfl) ⟨16244990, by rfl⟩ : syracuseStep 21659987 = 32489981) B32489981
theorem B1901551 : Blo 467785 1901551 := bstep (se 1 (by rfl) ⟨1426163, by rfl⟩ : syracuseStep 1901551 = 2852327) B2852327
theorem B5343569 : Blo 467785 5343569 := bstep (se 2 (by rfl) ⟨2003838, by rfl⟩ : syracuseStep 5343569 = 4007677) B4007677
theorem B2035199 : Blo 467785 2035199 := bstep (se 1 (by rfl) ⟨1526399, by rfl⟩ : syracuseStep 2035199 = 3052799) B3052799
theorem B1052585 : Blo 467785 1052585 := bstep (se 2 (by rfl) ⟨394719, by rfl⟩ : syracuseStep 1052585 = 789439) B789439
theorem B6754427 : Blo 467785 6754427 := bstep (se 1 (by rfl) ⟨5065820, by rfl⟩ : syracuseStep 6754427 = 10131641) B10131641
theorem B1052927 : Blo 467785 1052927 := bstep (se 1 (by rfl) ⟨789695, by rfl⟩ : syracuseStep 1052927 = 1579391) B1579391
theorem B792571 : Blo 467785 792571 := bstep (se 1 (by rfl) ⟨594428, by rfl⟩ : syracuseStep 792571 = 1188857) B1188857
theorem B1055015 : Blo 467785 1055015 := bstep (se 1 (by rfl) ⟨791261, by rfl⟩ : syracuseStep 1055015 = 1582523) B1582523
theorem B19208663 : Blo 467785 19208663 := bstep (se 1 (by rfl) ⟨14406497, by rfl⟩ : syracuseStep 19208663 = 28812995) B28812995
theorem B1776923 : Blo 467785 1776923 := bstep (se 1 (by rfl) ⟨1332692, by rfl⟩ : syracuseStep 1776923 = 2665385) B2665385
theorem B892471 : Blo 467785 892471 := bstep (se 1 (by rfl) ⟨669353, by rfl⟩ : syracuseStep 892471 = 1338707) B1338707
theorem B1056383 : Blo 467785 1056383 := bstep (se 1 (by rfl) ⟨792287, by rfl⟩ : syracuseStep 1056383 = 1584575) B1584575
theorem B892775 : Blo 467785 892775 := bstep (se 1 (by rfl) ⟨669581, by rfl⟩ : syracuseStep 892775 = 1339163) B1339163
theorem B1187743 : Blo 467785 1187743 := bstep (se 1 (by rfl) ⟨890807, by rfl⟩ : syracuseStep 1187743 = 1781615) B1781615
theorem B1057823 : Blo 467785 1057823 := bstep (se 1 (by rfl) ⟨793367, by rfl⟩ : syracuseStep 1057823 = 1586735) B1586735
theorem B468039 : Blo 467785 468039 := bstep (se 1 (by rfl) ⟨351029, by rfl⟩ : syracuseStep 468039 = 702059) B702059
theorem B1582361 : Blo 467785 1582361 := bstep (se 2 (by rfl) ⟨593385, by rfl⟩ : syracuseStep 1582361 = 1186771) B1186771
theorem B468583 : Blo 467785 468583 := bstep (se 1 (by rfl) ⟨351437, by rfl⟩ : syracuseStep 468583 = 702875) B702875
theorem B468607 : Blo 467785 468607 := bstep (se 1 (by rfl) ⟨351455, by rfl⟩ : syracuseStep 468607 = 702911) B702911
theorem B468839 : Blo 467785 468839 := bstep (se 1 (by rfl) ⟨351629, by rfl⟩ : syracuseStep 468839 = 703259) B703259
theorem B469055 : Blo 467785 469055 := bstep (se 1 (by rfl) ⟨351791, by rfl⟩ : syracuseStep 469055 = 703583) B703583
theorem B1779839 : Blo 467785 1779839 := bstep (se 1 (by rfl) ⟨1334879, by rfl⟩ : syracuseStep 1779839 = 2669759) B2669759
theorem B26126543 : Blo 467785 26126543 := bstep (se 1 (by rfl) ⟨19594907, by rfl⟩ : syracuseStep 26126543 = 39189815) B39189815
theorem B3385631 : Blo 467785 3385631 := bstep (se 1 (by rfl) ⟨2539223, by rfl⟩ : syracuseStep 3385631 = 5078447) B5078447
theorem B469631 : Blo 467785 469631 := bstep (se 1 (by rfl) ⟨352223, by rfl⟩ : syracuseStep 469631 = 704447) B704447
theorem B1190639 : Blo 467785 1190639 := bstep (se 1 (by rfl) ⟨892979, by rfl⟩ : syracuseStep 1190639 = 1785959) B1785959
theorem B470015 : Blo 467785 470015 := bstep (se 1 (by rfl) ⟨352511, by rfl⟩ : syracuseStep 470015 = 705023) B705023
theorem B471111 : Blo 467785 471111 := bstep (se 1 (by rfl) ⟨353333, by rfl⟩ : syracuseStep 471111 = 706667) B706667
theorem B471291 : Blo 467785 471291 := bstep (se 1 (by rfl) ⟨353468, by rfl⟩ : syracuseStep 471291 = 706937) B706937
theorem B1192603 : Blo 467785 1192603 := bstep (se 1 (by rfl) ⟨894452, by rfl⟩ : syracuseStep 1192603 = 1788905) B1788905
theorem B471707 : Blo 467785 471707 := bstep (se 1 (by rfl) ⟨353780, by rfl⟩ : syracuseStep 471707 = 707561) B707561
theorem B701903 : Blo 467785 701903 := bstep (se 1 (by rfl) ⟨526427, by rfl⟩ : syracuseStep 701903 = 1052855) B1052855
theorem B702311 : Blo 467785 702311 := bstep (se 1 (by rfl) ⟨526733, by rfl⟩ : syracuseStep 702311 = 1053467) B1053467
theorem B702671 : Blo 467785 702671 := bstep (se 1 (by rfl) ⟨527003, by rfl⟩ : syracuseStep 702671 = 1054007) B1054007
theorem B670447 : Blo 467785 670447 := bstep (se 1 (by rfl) ⟨502835, by rfl⟩ : syracuseStep 670447 = 1005671) B1005671
theorem B703625 : Blo 467785 703625 := bstep (se 2 (by rfl) ⟨263859, by rfl⟩ : syracuseStep 703625 = 527719) B527719
theorem B704159 : Blo 467785 704159 := bstep (se 1 (by rfl) ⟨528119, by rfl⟩ : syracuseStep 704159 = 1056239) B1056239
theorem B704639 : Blo 467785 704639 := bstep (se 1 (by rfl) ⟨528479, by rfl⟩ : syracuseStep 704639 = 1056959) B1056959
theorem B2539745 : Blo 467785 2539745 := bstep (se 2 (by rfl) ⟨952404, by rfl⟩ : syracuseStep 2539745 = 1904809) B1904809
theorem B704891 : Blo 467785 704891 := bstep (se 1 (by rfl) ⟨528668, by rfl⟩ : syracuseStep 704891 = 1057337) B1057337
theorem B705263 : Blo 467785 705263 := bstep (se 1 (by rfl) ⟨528947, by rfl⟩ : syracuseStep 705263 = 1057895) B1057895
theorem B705791 : Blo 467785 705791 := bstep (se 1 (by rfl) ⟨529343, by rfl⟩ : syracuseStep 705791 = 1058687) B1058687
theorem B1590839 : Blo 467785 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B706151 : Blo 467785 706151 := bstep (se 1 (by rfl) ⟨529613, by rfl⟩ : syracuseStep 706151 = 1059227) B1059227
theorem B3557519 : Blo 467785 3557519 := bstep (se 1 (by rfl) ⟨2668139, by rfl⟩ : syracuseStep 3557519 = 5336279) B5336279
theorem B707279 : Blo 467785 707279 := bstep (se 1 (by rfl) ⟨530459, by rfl⟩ : syracuseStep 707279 = 1060919) B1060919
theorem B2378483 : Blo 467785 2378483 := bstep (se 1 (by rfl) ⟨1783862, by rfl⟩ : syracuseStep 2378483 = 3567725) B3567725
theorem B1657849 : Blo 467785 1657849 := bstep (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) B1243387
theorem B1265633 : Blo 467785 1265633 := bstep (se 2 (by rfl) ⟨474612, by rfl⟩ : syracuseStep 1265633 = 949225) B949225
theorem B9752723 : Blo 467785 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B1265915 : Blo 467785 1265915 := bstep (se 1 (by rfl) ⟨949436, by rfl⟩ : syracuseStep 1265915 = 1898873) B1898873
theorem B38687939 : Blo 467785 38687939 := bstep (se 1 (by rfl) ⟨29015954, by rfl⟩ : syracuseStep 38687939 = 58031909) B58031909
theorem B1234543 : Blo 467785 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B5692625 : Blo 467785 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B2678255 : Blo 467785 2678255 := bstep (se 1 (by rfl) ⟨2008691, by rfl⟩ : syracuseStep 2678255 = 4017383) B4017383
theorem B9003743 : Blo 467785 9003743 := bstep (se 1 (by rfl) ⟨6752807, by rfl⟩ : syracuseStep 9003743 = 13505615) B13505615
theorem B2255687 : Blo 467785 2255687 := bstep (se 1 (by rfl) ⟨1691765, by rfl⟩ : syracuseStep 2255687 = 3383531) B3383531
theorem B3011681 : Blo 467785 3011681 := bstep (se 2 (by rfl) ⟨1129380, by rfl⟩ : syracuseStep 3011681 = 2258761) B2258761
theorem B1275257 : Blo 467785 1275257 := bstep (se 2 (by rfl) ⟨478221, by rfl⟩ : syracuseStep 1275257 = 956443) B956443
theorem B5372729 : Blo 467785 5372729 := bstep (se 2 (by rfl) ⟨2014773, by rfl⟩ : syracuseStep 5372729 = 4029547) B4029547
theorem B1506109 : Blo 467785 1506109 := bstep (se 3 (by rfl) ⟨282395, by rfl⟩ : syracuseStep 1506109 = 564791) B564791
theorem B17661073 : Blo 467785 17661073 := bstep (se 2 (by rfl) ⟨6622902, by rfl⟩ : syracuseStep 17661073 = 13245805) B13245805
theorem B25791959 : Blo 467785 25791959 := bstep (se 1 (by rfl) ⟨19343969, by rfl⟩ : syracuseStep 25791959 = 38687939) B38687939
theorem B1184615 : Blo 467785 1184615 := bstep (se 1 (by rfl) ⟨888461, by rfl⟩ : syracuseStep 1184615 = 1776923) B1776923
theorem B595183 : Blo 467785 595183 := bstep (se 1 (by rfl) ⟨446387, by rfl⟩ : syracuseStep 595183 = 892775) B892775
theorem B6002495 : Blo 467785 6002495 := bstep (se 1 (by rfl) ⟨4501871, by rfl⟩ : syracuseStep 6002495 = 9003743) B9003743
theorem B69670781 : Blo 467785 69670781 := bstep (se 3 (by rfl) ⟨13063271, by rfl⟩ : syracuseStep 69670781 = 26126543) B26126543
theorem B1054907 : Blo 467785 1054907 := bstep (se 1 (by rfl) ⟨791180, by rfl⟩ : syracuseStep 1054907 = 1582361) B1582361
theorem B1186559 : Blo 467785 1186559 := bstep (se 1 (by rfl) ⟨889919, by rfl⟩ : syracuseStep 1186559 = 1779839) B1779839
theorem B793759 : Blo 467785 793759 := bstep (se 1 (by rfl) ⟨595319, by rfl⟩ : syracuseStep 793759 = 1190639) B1190639
theorem B1646057 : Blo 467785 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B1056761 : Blo 467785 1056761 := bstep (se 2 (by rfl) ⟨396285, by rfl⟩ : syracuseStep 1056761 = 792571) B792571
theorem B2007787 : Blo 467785 2007787 := bstep (se 1 (by rfl) ⟨1505840, by rfl⟩ : syracuseStep 2007787 = 3011681) B3011681
theorem B467935 : Blo 467785 467935 := bstep (se 1 (by rfl) ⟨350951, by rfl⟩ : syracuseStep 467935 = 701903) B701903
theorem B893929 : Blo 467785 893929 := bstep (se 2 (by rfl) ⟨335223, by rfl⟩ : syracuseStep 893929 = 670447) B670447
theorem B2008145 : Blo 467785 2008145 := bstep (se 2 (by rfl) ⟨753054, by rfl⟩ : syracuseStep 2008145 = 1506109) B1506109
theorem B468207 : Blo 467785 468207 := bstep (se 1 (by rfl) ⟨351155, by rfl⟩ : syracuseStep 468207 = 702311) B702311
theorem B468447 : Blo 467785 468447 := bstep (se 1 (by rfl) ⟨351335, by rfl⟩ : syracuseStep 468447 = 702671) B702671
theorem B3581819 : Blo 467785 3581819 := bstep (se 1 (by rfl) ⟨2686364, by rfl⟩ : syracuseStep 3581819 = 5372729) B5372729
theorem B1189961 : Blo 467785 1189961 := bstep (se 2 (by rfl) ⟨446235, by rfl⟩ : syracuseStep 1189961 = 892471) B892471
theorem B469083 : Blo 467785 469083 := bstep (se 1 (by rfl) ⟨351812, by rfl⟩ : syracuseStep 469083 = 703625) B703625
theorem B469439 : Blo 467785 469439 := bstep (se 1 (by rfl) ⟨352079, by rfl⟩ : syracuseStep 469439 = 704159) B704159
theorem B1583657 : Blo 467785 1583657 := bstep (se 2 (by rfl) ⟨593871, by rfl⟩ : syracuseStep 1583657 = 1187743) B1187743
theorem B469759 : Blo 467785 469759 := bstep (se 1 (by rfl) ⟨352319, by rfl⟩ : syracuseStep 469759 = 704639) B704639
theorem B469927 : Blo 467785 469927 := bstep (se 1 (by rfl) ⟨352445, by rfl⟩ : syracuseStep 469927 = 704891) B704891
theorem B470175 : Blo 467785 470175 := bstep (se 1 (by rfl) ⟨352631, by rfl⟩ : syracuseStep 470175 = 705263) B705263
theorem B470527 : Blo 467785 470527 := bstep (se 1 (by rfl) ⟨352895, by rfl⟩ : syracuseStep 470527 = 705791) B705791
theorem B1060559 : Blo 467785 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B470767 : Blo 467785 470767 := bstep (se 1 (by rfl) ⟨353075, by rfl⟩ : syracuseStep 470767 = 706151) B706151
theorem B2535401 : Blo 467785 2535401 := bstep (se 2 (by rfl) ⟨950775, by rfl⟩ : syracuseStep 2535401 = 1901551) B1901551
theorem B2371679 : Blo 467785 2371679 := bstep (se 1 (by rfl) ⟨1778759, by rfl⟩ : syracuseStep 2371679 = 3557519) B3557519
theorem B471519 : Blo 467785 471519 := bstep (se 1 (by rfl) ⟨353639, by rfl⟩ : syracuseStep 471519 = 707279) B707279
theorem B1585655 : Blo 467785 1585655 := bstep (se 1 (by rfl) ⟨1189241, by rfl⟩ : syracuseStep 1585655 = 2378483) B2378483
theorem B1356799 : Blo 467785 1356799 := bstep (se 1 (by rfl) ⟨1017599, by rfl⟩ : syracuseStep 1356799 = 2035199) B2035199
theorem B701723 : Blo 467785 701723 := bstep (se 1 (by rfl) ⟨526292, by rfl⟩ : syracuseStep 701723 = 1052585) B1052585
theorem B4502951 : Blo 467785 4502951 := bstep (se 1 (by rfl) ⟨3377213, by rfl⟩ : syracuseStep 4502951 = 6754427) B6754427
theorem B6501815 : Blo 467785 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B701951 : Blo 467785 701951 := bstep (se 1 (by rfl) ⟨526463, by rfl⟩ : syracuseStep 701951 = 1052927) B1052927
theorem B2210465 : Blo 467785 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B703343 : Blo 467785 703343 := bstep (se 1 (by rfl) ⟨527507, by rfl⟩ : syracuseStep 703343 = 1055015) B1055015
theorem B1785503 : Blo 467785 1785503 := bstep (se 1 (by rfl) ⟨1339127, by rfl⟩ : syracuseStep 1785503 = 2678255) B2678255
theorem B704255 : Blo 467785 704255 := bstep (se 1 (by rfl) ⟨528191, by rfl⟩ : syracuseStep 704255 = 1056383) B1056383
theorem B705215 : Blo 467785 705215 := bstep (se 1 (by rfl) ⟨528911, by rfl⟩ : syracuseStep 705215 = 1057823) B1057823
theorem B1590137 : Blo 467785 1590137 := bstep (se 2 (by rfl) ⟨596301, by rfl⟩ : syracuseStep 1590137 = 1192603) B1192603
theorem B23548097 : Blo 467785 23548097 := bstep (se 2 (by rfl) ⟨8830536, by rfl⟩ : syracuseStep 23548097 = 17661073) B17661073
theorem B1693163 : Blo 467785 1693163 := bstep (se 1 (by rfl) ⟨1269872, by rfl⟩ : syracuseStep 1693163 = 2539745) B2539745
theorem B14439991 : Blo 467785 14439991 := bstep (se 1 (by rfl) ⟨10829993, by rfl⟩ : syracuseStep 14439991 = 21659987) B21659987
theorem B3562379 : Blo 467785 3562379 := bstep (se 1 (by rfl) ⟨2671784, by rfl⟩ : syracuseStep 3562379 = 5343569) B5343569
theorem B843755 : Blo 467785 843755 := bstep (se 1 (by rfl) ⟨632816, by rfl⟩ : syracuseStep 843755 = 1265633) B1265633
theorem B843943 : Blo 467785 843943 := bstep (se 1 (by rfl) ⟨632957, by rfl⟩ : syracuseStep 843943 = 1265915) B1265915
theorem B12805775 : Blo 467785 12805775 := bstep (se 1 (by rfl) ⟨9604331, by rfl⟩ : syracuseStep 12805775 = 19208663) B19208663
theorem B3795083 : Blo 467785 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B2257087 : Blo 467785 2257087 := bstep (se 1 (by rfl) ⟨1692815, by rfl⟩ : syracuseStep 2257087 = 3385631) B3385631
theorem B1503791 : Blo 467785 1503791 := bstep (se 1 (by rfl) ⟨1127843, by rfl⟩ : syracuseStep 1503791 = 2255687) B2255687
theorem B850171 : Blo 467785 850171 := bstep (se 1 (by rfl) ⟨637628, by rfl⟩ : syracuseStep 850171 = 1275257) B1275257
theorem B15698731 : Blo 467785 15698731 := bstep (se 1 (by rfl) ⟨11774048, by rfl⟩ : syracuseStep 15698731 = 23548097) B23548097
theorem B789743 : Blo 467785 789743 := bstep (se 1 (by rfl) ⟨592307, by rfl⟩ : syracuseStep 789743 = 1184615) B1184615
theorem B4001663 : Blo 467785 4001663 := bstep (se 1 (by rfl) ⟨3001247, by rfl⟩ : syracuseStep 4001663 = 6002495) B6002495
theorem B791039 : Blo 467785 791039 := bstep (se 1 (by rfl) ⟨593279, by rfl⟩ : syracuseStep 791039 = 1186559) B1186559
theorem B1809065 : Blo 467785 1809065 := bstep (se 2 (by rfl) ⟨678399, by rfl⟩ : syracuseStep 1809065 = 1356799) B1356799
theorem B793307 : Blo 467785 793307 := bstep (se 1 (by rfl) ⟨594980, by rfl⟩ : syracuseStep 793307 = 1189961) B1189961
theorem B2530055 : Blo 467785 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B793577 : Blo 467785 793577 := bstep (se 2 (by rfl) ⟨297591, by rfl⟩ : syracuseStep 793577 = 595183) B595183
theorem B1055771 : Blo 467785 1055771 := bstep (se 1 (by rfl) ⟨791828, by rfl⟩ : syracuseStep 1055771 = 1583657) B1583657
theorem B1581119 : Blo 467785 1581119 := bstep (se 1 (by rfl) ⟨1185839, by rfl⟩ : syracuseStep 1581119 = 2371679) B2371679
theorem B1057103 : Blo 467785 1057103 := bstep (se 1 (by rfl) ⟨792827, by rfl⟩ : syracuseStep 1057103 = 1585655) B1585655
theorem B467815 : Blo 467785 467815 := bstep (se 1 (by rfl) ⟨350861, by rfl⟩ : syracuseStep 467815 = 701723) B701723
theorem B4334543 : Blo 467785 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B467967 : Blo 467785 467967 := bstep (se 1 (by rfl) ⟨350975, by rfl⟩ : syracuseStep 467967 = 701951) B701951
theorem B1058345 : Blo 467785 1058345 := bstep (se 2 (by rfl) ⟨396879, by rfl⟩ : syracuseStep 1058345 = 793759) B793759
theorem B468895 : Blo 467785 468895 := bstep (se 1 (by rfl) ⟨351671, by rfl⟩ : syracuseStep 468895 = 703343) B703343
theorem B1190335 : Blo 467785 1190335 := bstep (se 1 (by rfl) ⟨892751, by rfl⟩ : syracuseStep 1190335 = 1785503) B1785503
theorem B469503 : Blo 467785 469503 := bstep (se 1 (by rfl) ⟨352127, by rfl⟩ : syracuseStep 469503 = 704255) B704255
theorem B1125257 : Blo 467785 1125257 := bstep (se 2 (by rfl) ⟨421971, by rfl⟩ : syracuseStep 1125257 = 843943) B843943
theorem B470143 : Blo 467785 470143 := bstep (se 1 (by rfl) ⟨352607, by rfl⟩ : syracuseStep 470143 = 705215) B705215
theorem B1060091 : Blo 467785 1060091 := bstep (se 1 (by rfl) ⟨795068, by rfl⟩ : syracuseStep 1060091 = 1590137) B1590137
theorem B1191905 : Blo 467785 1191905 := bstep (se 2 (by rfl) ⟨446964, by rfl⟩ : syracuseStep 1191905 = 893929) B893929
theorem B1128775 : Blo 467785 1128775 := bstep (se 1 (by rfl) ⟨846581, by rfl⟩ : syracuseStep 1128775 = 1693163) B1693163
theorem B46447187 : Blo 467785 46447187 := bstep (se 1 (by rfl) ⟨34835390, by rfl⟩ : syracuseStep 46447187 = 69670781) B69670781
theorem B703271 : Blo 467785 703271 := bstep (se 1 (by rfl) ⟨527453, by rfl⟩ : syracuseStep 703271 = 1054907) B1054907
theorem B2374919 : Blo 467785 2374919 := bstep (se 1 (by rfl) ⟨1781189, by rfl⟩ : syracuseStep 2374919 = 3562379) B3562379
theorem B1097371 : Blo 467785 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B704507 : Blo 467785 704507 := bstep (se 1 (by rfl) ⟨528380, by rfl⟩ : syracuseStep 704507 = 1056761) B1056761
theorem B8537183 : Blo 467785 8537183 := bstep (se 1 (by rfl) ⟨6402887, by rfl⟩ : syracuseStep 8537183 = 12805775) B12805775
theorem B19253321 : Blo 467785 19253321 := bstep (se 2 (by rfl) ⟨7219995, by rfl⟩ : syracuseStep 19253321 = 14439991) B14439991
theorem B707039 : Blo 467785 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B1690267 : Blo 467785 1690267 := bstep (se 1 (by rfl) ⟨1267700, by rfl⟩ : syracuseStep 1690267 = 2535401) B2535401
theorem B1133561 : Blo 467785 1133561 := bstep (se 2 (by rfl) ⟨425085, by rfl⟩ : syracuseStep 1133561 = 850171) B850171
theorem B1002527 : Blo 467785 1002527 := bstep (se 1 (by rfl) ⟨751895, by rfl⟩ : syracuseStep 1002527 = 1503791) B1503791
theorem B3001967 : Blo 467785 3001967 := bstep (se 1 (by rfl) ⟨2251475, by rfl⟩ : syracuseStep 3001967 = 4502951) B4502951
theorem B2250013 : Blo 467785 2250013 := bstep (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) B843755
theorem B2677049 : Blo 467785 2677049 := bstep (se 2 (by rfl) ⟨1003893, by rfl⟩ : syracuseStep 2677049 = 2007787) B2007787
theorem B17194639 : Blo 467785 17194639 := bstep (se 1 (by rfl) ⟨12895979, by rfl⟩ : syracuseStep 17194639 = 25791959) B25791959
theorem B3009449 : Blo 467785 3009449 := bstep (se 2 (by rfl) ⟨1128543, by rfl⟩ : syracuseStep 3009449 = 2257087) B2257087
theorem B1338763 : Blo 467785 1338763 := bstep (se 1 (by rfl) ⟨1004072, by rfl⟩ : syracuseStep 1338763 = 2008145) B2008145
theorem B2387879 : Blo 467785 2387879 := bstep (se 1 (by rfl) ⟨1790909, by rfl⟩ : syracuseStep 2387879 = 3581819) B3581819
theorem B1473643 : Blo 467785 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B526495 : Blo 467785 526495 := bstep (se 1 (by rfl) ⟨394871, by rfl⟩ : syracuseStep 526495 = 789743) B789743
theorem B2001311 : Blo 467785 2001311 := bstep (se 1 (by rfl) ⟨1500983, by rfl⟩ : syracuseStep 2001311 = 3001967) B3001967
theorem B527359 : Blo 467785 527359 := bstep (se 1 (by rfl) ⟨395519, by rfl⟩ : syracuseStep 527359 = 791039) B791039
theorem B528871 : Blo 467785 528871 := bstep (se 1 (by rfl) ⟨396653, by rfl⟩ : syracuseStep 528871 = 793307) B793307
theorem B529051 : Blo 467785 529051 := bstep (se 1 (by rfl) ⟨396788, by rfl⟩ : syracuseStep 529051 = 793577) B793577
theorem B1054079 : Blo 467785 1054079 := bstep (se 1 (by rfl) ⟨790559, by rfl⟩ : syracuseStep 1054079 = 1581119) B1581119
theorem B2889695 : Blo 467785 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B4824173 : Blo 467785 4824173 := bstep (se 3 (by rfl) ⟨904532, by rfl⟩ : syracuseStep 4824173 = 1809065) B1809065
theorem B2006299 : Blo 467785 2006299 := bstep (se 1 (by rfl) ⟨1504724, by rfl⟩ : syracuseStep 2006299 = 3009449) B3009449
theorem B794603 : Blo 467785 794603 := bstep (se 1 (by rfl) ⟨595952, by rfl⟩ : syracuseStep 794603 = 1191905) B1191905
theorem B3022829 : Blo 467785 3022829 := bstep (se 3 (by rfl) ⟨566780, by rfl⟩ : syracuseStep 3022829 = 1133561) B1133561
theorem B468847 : Blo 467785 468847 := bstep (se 1 (by rfl) ⟨351635, by rfl⟩ : syracuseStep 468847 = 703271) B703271
theorem B1583279 : Blo 467785 1583279 := bstep (se 1 (by rfl) ⟨1187459, by rfl⟩ : syracuseStep 1583279 = 2374919) B2374919
theorem B469671 : Blo 467785 469671 := bstep (se 1 (by rfl) ⟨352253, by rfl⟩ : syracuseStep 469671 = 704507) B704507
theorem B471359 : Blo 467785 471359 := bstep (se 1 (by rfl) ⟨353519, by rfl⟩ : syracuseStep 471359 = 707039) B707039
theorem B668351 : Blo 467785 668351 := bstep (se 1 (by rfl) ⟨501263, by rfl⟩ : syracuseStep 668351 = 1002527) B1002527
theorem B2667775 : Blo 467785 2667775 := bstep (se 1 (by rfl) ⟨2000831, by rfl⟩ : syracuseStep 2667775 = 4001663) B4001663
theorem B1587113 : Blo 467785 1587113 := bstep (se 2 (by rfl) ⟨595167, by rfl⟩ : syracuseStep 1587113 = 1190335) B1190335
theorem B1784699 : Blo 467785 1784699 := bstep (se 1 (by rfl) ⟨1338524, by rfl⟩ : syracuseStep 1784699 = 2677049) B2677049
theorem B1785017 : Blo 467785 1785017 := bstep (se 2 (by rfl) ⟨669381, by rfl⟩ : syracuseStep 1785017 = 1338763) B1338763
theorem B703847 : Blo 467785 703847 := bstep (se 1 (by rfl) ⟨527885, by rfl⟩ : syracuseStep 703847 = 1055771) B1055771
theorem B704735 : Blo 467785 704735 := bstep (se 1 (by rfl) ⟨528551, by rfl⟩ : syracuseStep 704735 = 1057103) B1057103
theorem B495436661 : Blo 467785 495436661 := bstep (se 5 (by rfl) ⟨23223593, by rfl⟩ : syracuseStep 495436661 = 46447187) B46447187
theorem B705563 : Blo 467785 705563 := bstep (se 1 (by rfl) ⟨529172, by rfl⟩ : syracuseStep 705563 = 1058345) B1058345
theorem B3000017 : Blo 467785 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B706727 : Blo 467785 706727 := bstep (se 1 (by rfl) ⟨530045, by rfl⟩ : syracuseStep 706727 = 1060091) B1060091
theorem B3000685 : Blo 467785 3000685 := bstep (se 3 (by rfl) ⟨562628, by rfl⟩ : syracuseStep 3000685 = 1125257) B1125257
theorem B1591919 : Blo 467785 1591919 := bstep (se 1 (by rfl) ⟨1193939, by rfl⟩ : syracuseStep 1591919 = 2387879) B2387879
theorem B5852645 : Blo 467785 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B22926185 : Blo 467785 22926185 := bstep (se 2 (by rfl) ⟨8597319, by rfl⟩ : syracuseStep 22926185 = 17194639) B17194639
theorem B5691455 : Blo 467785 5691455 := bstep (se 1 (by rfl) ⟨4268591, by rfl⟩ : syracuseStep 5691455 = 8537183) B8537183
theorem B12835547 : Blo 467785 12835547 := bstep (se 1 (by rfl) ⟨9626660, by rfl⟩ : syracuseStep 12835547 = 19253321) B19253321
theorem B2253689 : Blo 467785 2253689 := bstep (se 2 (by rfl) ⟨845133, by rfl⟩ : syracuseStep 2253689 = 1690267) B1690267
theorem B20931641 : Blo 467785 20931641 := bstep (se 2 (by rfl) ⟨7849365, by rfl⟩ : syracuseStep 20931641 = 15698731) B15698731
theorem B7859429 : Blo 467785 7859429 := bstep (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) B1473643
theorem B6746813 : Blo 467785 6746813 := bstep (se 3 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 6746813 = 2530055) B2530055
theorem B1505033 : Blo 467785 1505033 := bstep (se 2 (by rfl) ⟨564387, by rfl⟩ : syracuseStep 1505033 = 1128775) B1128775
theorem B3901763 : Blo 467785 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B4000913 : Blo 467785 4000913 := bstep (se 2 (by rfl) ⟨1500342, by rfl⟩ : syracuseStep 4000913 = 3000685) B3000685
theorem B8557031 : Blo 467785 8557031 := bstep (se 1 (by rfl) ⟨6417773, by rfl⟩ : syracuseStep 8557031 = 12835547) B12835547
theorem B8000045 : Blo 467785 8000045 := bstep (se 3 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 8000045 = 3000017) B3000017
theorem B3216115 : Blo 467785 3216115 := bstep (se 1 (by rfl) ⟨2412086, by rfl⟩ : syracuseStep 3216115 = 4824173) B4824173
theorem B529735 : Blo 467785 529735 := bstep (se 1 (by rfl) ⟨397301, by rfl⟩ : syracuseStep 529735 = 794603) B794603
theorem B1055519 : Blo 467785 1055519 := bstep (se 1 (by rfl) ⟨791639, by rfl⟩ : syracuseStep 1055519 = 1583279) B1583279
theorem B4497875 : Blo 467785 4497875 := bstep (se 1 (by rfl) ⟨3373406, by rfl⟩ : syracuseStep 4497875 = 6746813) B6746813
theorem B1058075 : Blo 467785 1058075 := bstep (se 1 (by rfl) ⟨793556, by rfl⟩ : syracuseStep 1058075 = 1587113) B1587113
theorem B1189799 : Blo 467785 1189799 := bstep (se 1 (by rfl) ⟨892349, by rfl⟩ : syracuseStep 1189799 = 1784699) B1784699
theorem B1190011 : Blo 467785 1190011 := bstep (se 1 (by rfl) ⟨892508, by rfl⟩ : syracuseStep 1190011 = 1785017) B1785017
theorem B469231 : Blo 467785 469231 := bstep (se 1 (by rfl) ⟨351923, by rfl⟩ : syracuseStep 469231 = 703847) B703847
theorem B469823 : Blo 467785 469823 := bstep (se 1 (by rfl) ⟨352367, by rfl⟩ : syracuseStep 469823 = 704735) B704735
theorem B470375 : Blo 467785 470375 := bstep (se 1 (by rfl) ⟨352781, by rfl⟩ : syracuseStep 470375 = 705563) B705563
theorem B471151 : Blo 467785 471151 := bstep (se 1 (by rfl) ⟨353363, by rfl⟩ : syracuseStep 471151 = 706727) B706727
theorem B1061279 : Blo 467785 1061279 := bstep (se 1 (by rfl) ⟨795959, by rfl⟩ : syracuseStep 1061279 = 1591919) B1591919
theorem B1782269 : Blo 467785 1782269 := bstep (se 3 (by rfl) ⟨334175, by rfl⟩ : syracuseStep 1782269 = 668351) B668351
theorem B701993 : Blo 467785 701993 := bstep (se 2 (by rfl) ⟨263247, by rfl⟩ : syracuseStep 701993 = 526495) B526495
theorem B15284123 : Blo 467785 15284123 := bstep (se 1 (by rfl) ⟨11463092, by rfl⟩ : syracuseStep 15284123 = 22926185) B22926185
theorem B702719 : Blo 467785 702719 := bstep (se 1 (by rfl) ⟨527039, by rfl⟩ : syracuseStep 702719 = 1054079) B1054079
theorem B703145 : Blo 467785 703145 := bstep (se 2 (by rfl) ⟨263679, by rfl⟩ : syracuseStep 703145 = 527359) B527359
theorem B2015219 : Blo 467785 2015219 := bstep (se 1 (by rfl) ⟨1511414, by rfl⟩ : syracuseStep 2015219 = 3022829) B3022829
theorem B705161 : Blo 467785 705161 := bstep (se 2 (by rfl) ⟨264435, by rfl⟩ : syracuseStep 705161 = 528871) B528871
theorem B705401 : Blo 467785 705401 := bstep (se 2 (by rfl) ⟨264525, by rfl⟩ : syracuseStep 705401 = 529051) B529051
theorem B3557033 : Blo 467785 3557033 := bstep (se 2 (by rfl) ⟨1333887, by rfl⟩ : syracuseStep 3557033 = 2667775) B2667775
theorem B1003355 : Blo 467785 1003355 := bstep (se 1 (by rfl) ⟨752516, by rfl⟩ : syracuseStep 1003355 = 1505033) B1505033
theorem B2675065 : Blo 467785 2675065 := bstep (se 2 (by rfl) ⟨1003149, by rfl⟩ : syracuseStep 2675065 = 2006299) B2006299
theorem B330291107 : Blo 467785 330291107 := bstep (se 1 (by rfl) ⟨247718330, by rfl⟩ : syracuseStep 330291107 = 495436661) B495436661
theorem B1334207 : Blo 467785 1334207 := bstep (se 1 (by rfl) ⟨1000655, by rfl⟩ : syracuseStep 1334207 = 2001311) B2001311
theorem B1926463 : Blo 467785 1926463 := bstep (se 1 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 1926463 = 2889695) B2889695
theorem B3794303 : Blo 467785 3794303 := bstep (se 1 (by rfl) ⟨2845727, by rfl⟩ : syracuseStep 3794303 = 5691455) B5691455
theorem B1502459 : Blo 467785 1502459 := bstep (se 1 (by rfl) ⟨1126844, by rfl⟩ : syracuseStep 1502459 = 2253689) B2253689
theorem B13954427 : Blo 467785 13954427 := bstep (se 1 (by rfl) ⟨10465820, by rfl⟩ : syracuseStep 13954427 = 20931641) B20931641
theorem B5239619 : Blo 467785 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B5704687 : Blo 467785 5704687 := bstep (se 1 (by rfl) ⟨4278515, by rfl⟩ : syracuseStep 5704687 = 8557031) B8557031
theorem B889471 : Blo 467785 889471 := bstep (se 1 (by rfl) ⟨667103, by rfl⟩ : syracuseStep 889471 = 1334207) B1334207
theorem B793199 : Blo 467785 793199 := bstep (se 1 (by rfl) ⟨594899, by rfl⟩ : syracuseStep 793199 = 1189799) B1189799
theorem B1188179 : Blo 467785 1188179 := bstep (se 1 (by rfl) ⟨891134, by rfl⟩ : syracuseStep 1188179 = 1782269) B1782269
theorem B467995 : Blo 467785 467995 := bstep (se 1 (by rfl) ⟨350996, by rfl⟩ : syracuseStep 467995 = 701993) B701993
theorem B468479 : Blo 467785 468479 := bstep (se 1 (by rfl) ⟨351359, by rfl⟩ : syracuseStep 468479 = 702719) B702719
theorem B468763 : Blo 467785 468763 := bstep (se 1 (by rfl) ⟨351572, by rfl⟩ : syracuseStep 468763 = 703145) B703145
theorem B470107 : Blo 467785 470107 := bstep (se 1 (by rfl) ⟨352580, by rfl⟩ : syracuseStep 470107 = 705161) B705161
theorem B470267 : Blo 467785 470267 := bstep (se 1 (by rfl) ⟨352700, by rfl⟩ : syracuseStep 470267 = 705401) B705401
theorem B2371355 : Blo 467785 2371355 := bstep (se 1 (by rfl) ⟨1778516, by rfl⟩ : syracuseStep 2371355 = 3557033) B3557033
theorem B2601175 : Blo 467785 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B2568617 : Blo 467785 2568617 := bstep (se 2 (by rfl) ⟨963231, by rfl⟩ : syracuseStep 2568617 = 1926463) B1926463
theorem B2667275 : Blo 467785 2667275 := bstep (se 1 (by rfl) ⟨2000456, by rfl⟩ : syracuseStep 2667275 = 4000913) B4000913
theorem B668903 : Blo 467785 668903 := bstep (se 1 (by rfl) ⟨501677, by rfl⟩ : syracuseStep 668903 = 1003355) B1003355
theorem B1586681 : Blo 467785 1586681 := bstep (se 2 (by rfl) ⟨595005, by rfl⟩ : syracuseStep 1586681 = 1190011) B1190011
theorem B703679 : Blo 467785 703679 := bstep (se 1 (by rfl) ⟨527759, by rfl⟩ : syracuseStep 703679 = 1055519) B1055519
theorem B2998583 : Blo 467785 2998583 := bstep (se 1 (by rfl) ⟨2248937, by rfl⟩ : syracuseStep 2998583 = 4497875) B4497875
theorem B705383 : Blo 467785 705383 := bstep (se 1 (by rfl) ⟨529037, by rfl⟩ : syracuseStep 705383 = 1058075) B1058075
theorem B706313 : Blo 467785 706313 := bstep (se 2 (by rfl) ⟨264867, by rfl⟩ : syracuseStep 706313 = 529735) B529735
theorem B1001639 : Blo 467785 1001639 := bstep (se 1 (by rfl) ⟨751229, by rfl⟩ : syracuseStep 1001639 = 1502459) B1502459
theorem B707519 : Blo 467785 707519 := bstep (se 1 (by rfl) ⟨530639, by rfl⟩ : syracuseStep 707519 = 1061279) B1061279
theorem B3493079 : Blo 467785 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B5333363 : Blo 467785 5333363 := bstep (se 1 (by rfl) ⟨4000022, by rfl⟩ : syracuseStep 5333363 = 8000045) B8000045
theorem B10118141 : Blo 467785 10118141 := bstep (se 3 (by rfl) ⟨1897151, by rfl⟩ : syracuseStep 10118141 = 3794303) B3794303
theorem B220194071 : Blo 467785 220194071 := bstep (se 1 (by rfl) ⟨165145553, by rfl⟩ : syracuseStep 220194071 = 330291107) B330291107
theorem B3566753 : Blo 467785 3566753 := bstep (se 2 (by rfl) ⟨1337532, by rfl⟩ : syracuseStep 3566753 = 2675065) B2675065
theorem B4288153 : Blo 467785 4288153 := bstep (se 2 (by rfl) ⟨1608057, by rfl⟩ : syracuseStep 4288153 = 3216115) B3216115
theorem B9302951 : Blo 467785 9302951 := bstep (se 1 (by rfl) ⟨6977213, by rfl⟩ : syracuseStep 9302951 = 13954427) B13954427
theorem B10189415 : Blo 467785 10189415 := bstep (se 1 (by rfl) ⟨7642061, by rfl⟩ : syracuseStep 10189415 = 15284123) B15284123
theorem B1343479 : Blo 467785 1343479 := bstep (se 1 (by rfl) ⟨1007609, by rfl⟩ : syracuseStep 1343479 = 2015219) B2015219
theorem B1999055 : Blo 467785 1999055 := bstep (se 1 (by rfl) ⟨1499291, by rfl⟩ : syracuseStep 1999055 = 2998583) B2998583
theorem B37259509 : Blo 467785 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B528799 : Blo 467785 528799 := bstep (se 1 (by rfl) ⟨396599, by rfl⟩ : syracuseStep 528799 = 793199) B793199
theorem B792119 : Blo 467785 792119 := bstep (se 1 (by rfl) ⟨594089, by rfl⟩ : syracuseStep 792119 = 1188179) B1188179
theorem B1185961 : Blo 467785 1185961 := bstep (se 2 (by rfl) ⟨444735, by rfl⟩ : syracuseStep 1185961 = 889471) B889471
theorem B1580903 : Blo 467785 1580903 := bstep (se 1 (by rfl) ⟨1185677, by rfl⟩ : syracuseStep 1580903 = 2371355) B2371355
theorem B1712411 : Blo 467785 1712411 := bstep (se 1 (by rfl) ⟨1284308, by rfl⟩ : syracuseStep 1712411 = 2568617) B2568617
theorem B1778183 : Blo 467785 1778183 := bstep (se 1 (by rfl) ⟨1333637, by rfl⟩ : syracuseStep 1778183 = 2667275) B2667275
theorem B6201967 : Blo 467785 6201967 := bstep (se 1 (by rfl) ⟨4651475, by rfl⟩ : syracuseStep 6201967 = 9302951) B9302951
theorem B1057787 : Blo 467785 1057787 := bstep (se 1 (by rfl) ⟨793340, by rfl⟩ : syracuseStep 1057787 = 1586681) B1586681
theorem B6792943 : Blo 467785 6792943 := bstep (se 1 (by rfl) ⟨5094707, by rfl⟩ : syracuseStep 6792943 = 10189415) B10189415
theorem B469119 : Blo 467785 469119 := bstep (se 1 (by rfl) ⟨351839, by rfl⟩ : syracuseStep 469119 = 703679) B703679
theorem B470255 : Blo 467785 470255 := bstep (se 1 (by rfl) ⟨352691, by rfl⟩ : syracuseStep 470255 = 705383) B705383
theorem B470875 : Blo 467785 470875 := bstep (se 1 (by rfl) ⟨353156, by rfl⟩ : syracuseStep 470875 = 706313) B706313
theorem B667759 : Blo 467785 667759 := bstep (se 1 (by rfl) ⟨500819, by rfl⟩ : syracuseStep 667759 = 1001639) B1001639
theorem B471679 : Blo 467785 471679 := bstep (se 1 (by rfl) ⟨353759, by rfl⟩ : syracuseStep 471679 = 707519) B707519
theorem B1783741 : Blo 467785 1783741 := bstep (se 3 (by rfl) ⟨334451, by rfl⟩ : syracuseStep 1783741 = 668903) B668903
theorem B5717537 : Blo 467785 5717537 := bstep (se 2 (by rfl) ⟨2144076, by rfl⟩ : syracuseStep 5717537 = 4288153) B4288153
theorem B30424997 : Blo 467785 30424997 := bstep (se 4 (by rfl) ⟨2852343, by rfl⟩ : syracuseStep 30424997 = 5704687) B5704687
theorem B3555575 : Blo 467785 3555575 := bstep (se 1 (by rfl) ⟨2666681, by rfl⟩ : syracuseStep 3555575 = 5333363) B5333363
theorem B2377835 : Blo 467785 2377835 := bstep (se 1 (by rfl) ⟨1783376, by rfl⟩ : syracuseStep 2377835 = 3566753) B3566753
theorem B1791305 : Blo 467785 1791305 := bstep (se 2 (by rfl) ⟨671739, by rfl⟩ : syracuseStep 1791305 = 1343479) B1343479
theorem B3468233 : Blo 467785 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B6745427 : Blo 467785 6745427 := bstep (se 1 (by rfl) ⟨5059070, by rfl⟩ : syracuseStep 6745427 = 10118141) B10118141
theorem B146796047 : Blo 467785 146796047 := bstep (se 1 (by rfl) ⟨110097035, by rfl⟩ : syracuseStep 146796047 = 220194071) B220194071
theorem B49679345 : Blo 467785 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B528079 : Blo 467785 528079 := bstep (se 1 (by rfl) ⟨396059, by rfl⟩ : syracuseStep 528079 = 792119) B792119
theorem B1053935 : Blo 467785 1053935 := bstep (se 1 (by rfl) ⟨790451, by rfl⟩ : syracuseStep 1053935 = 1580903) B1580903
theorem B890345 : Blo 467785 890345 := bstep (se 2 (by rfl) ⟨333879, by rfl⟩ : syracuseStep 890345 = 667759) B667759
theorem B1185455 : Blo 467785 1185455 := bstep (se 1 (by rfl) ⟨889091, by rfl⟩ : syracuseStep 1185455 = 1778183) B1778183
theorem B4496951 : Blo 467785 4496951 := bstep (se 1 (by rfl) ⟨3372713, by rfl⟩ : syracuseStep 4496951 = 6745427) B6745427
theorem B1581281 : Blo 467785 1581281 := bstep (se 2 (by rfl) ⟨592980, by rfl⟩ : syracuseStep 1581281 = 1185961) B1185961
theorem B3811691 : Blo 467785 3811691 := bstep (se 1 (by rfl) ⟨2858768, by rfl⟩ : syracuseStep 3811691 = 5717537) B5717537
theorem B2370383 : Blo 467785 2370383 := bstep (se 1 (by rfl) ⟨1777787, by rfl⟩ : syracuseStep 2370383 = 3555575) B3555575
theorem B8269289 : Blo 467785 8269289 := bstep (se 2 (by rfl) ⟨3100983, by rfl⟩ : syracuseStep 8269289 = 6201967) B6201967
theorem B1585223 : Blo 467785 1585223 := bstep (se 1 (by rfl) ⟨1188917, by rfl⟩ : syracuseStep 1585223 = 2377835) B2377835
theorem B9057257 : Blo 467785 9057257 := bstep (se 2 (by rfl) ⟨3396471, by rfl⟩ : syracuseStep 9057257 = 6792943) B6792943
theorem B1194203 : Blo 467785 1194203 := bstep (se 1 (by rfl) ⟨895652, by rfl⟩ : syracuseStep 1194203 = 1791305) B1791305
theorem B705065 : Blo 467785 705065 := bstep (se 2 (by rfl) ⟨264399, by rfl⟩ : syracuseStep 705065 = 528799) B528799
theorem B705191 : Blo 467785 705191 := bstep (se 1 (by rfl) ⟨528893, by rfl⟩ : syracuseStep 705191 = 1057787) B1057787
theorem B2312155 : Blo 467785 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B97864031 : Blo 467785 97864031 := bstep (se 1 (by rfl) ⟨73398023, by rfl⟩ : syracuseStep 97864031 = 146796047) B146796047
theorem B2378321 : Blo 467785 2378321 := bstep (se 2 (by rfl) ⟨891870, by rfl⟩ : syracuseStep 2378321 = 1783741) B1783741
theorem B1332703 : Blo 467785 1332703 := bstep (se 1 (by rfl) ⟨999527, by rfl⟩ : syracuseStep 1332703 = 1999055) B1999055
theorem B1141607 : Blo 467785 1141607 := bstep (se 1 (by rfl) ⟨856205, by rfl⟩ : syracuseStep 1141607 = 1712411) B1712411
theorem B20283331 : Blo 467785 20283331 := bstep (se 1 (by rfl) ⟨15212498, by rfl⟩ : syracuseStep 20283331 = 30424997) B30424997
theorem B65242687 : Blo 467785 65242687 := bstep (se 1 (by rfl) ⟨48932015, by rfl⟩ : syracuseStep 65242687 = 97864031) B97864031
theorem B3082873 : Blo 467785 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B593563 : Blo 467785 593563 := bstep (se 1 (by rfl) ⟨445172, by rfl⟩ : syracuseStep 593563 = 890345) B890345
theorem B790303 : Blo 467785 790303 := bstep (se 1 (by rfl) ⟨592727, by rfl⟩ : syracuseStep 790303 = 1185455) B1185455
theorem B1054187 : Blo 467785 1054187 := bstep (se 1 (by rfl) ⟨790640, by rfl⟩ : syracuseStep 1054187 = 1581281) B1581281
theorem B1580255 : Blo 467785 1580255 := bstep (se 1 (by rfl) ⟨1185191, by rfl⟩ : syracuseStep 1580255 = 2370383) B2370383
theorem B761071 : Blo 467785 761071 := bstep (se 1 (by rfl) ⟨570803, by rfl⟩ : syracuseStep 761071 = 1141607) B1141607
theorem B1776937 : Blo 467785 1776937 := bstep (se 2 (by rfl) ⟨666351, by rfl⟩ : syracuseStep 1776937 = 1332703) B1332703
theorem B5512859 : Blo 467785 5512859 := bstep (se 1 (by rfl) ⟨4134644, by rfl⟩ : syracuseStep 5512859 = 8269289) B8269289
theorem B1056815 : Blo 467785 1056815 := bstep (se 1 (by rfl) ⟨792611, by rfl⟩ : syracuseStep 1056815 = 1585223) B1585223
theorem B6038171 : Blo 467785 6038171 := bstep (se 1 (by rfl) ⟨4528628, by rfl⟩ : syracuseStep 6038171 = 9057257) B9057257
theorem B796135 : Blo 467785 796135 := bstep (se 1 (by rfl) ⟨597101, by rfl⟩ : syracuseStep 796135 = 1194203) B1194203
theorem B27044441 : Blo 467785 27044441 := bstep (se 2 (by rfl) ⟨10141665, by rfl⟩ : syracuseStep 27044441 = 20283331) B20283331
theorem B470043 : Blo 467785 470043 := bstep (se 1 (by rfl) ⟨352532, by rfl⟩ : syracuseStep 470043 = 705065) B705065
theorem B470127 : Blo 467785 470127 := bstep (se 1 (by rfl) ⟨352595, by rfl⟩ : syracuseStep 470127 = 705191) B705191
theorem B1585547 : Blo 467785 1585547 := bstep (se 1 (by rfl) ⟨1189160, by rfl⟩ : syracuseStep 1585547 = 2378321) B2378321
theorem B702623 : Blo 467785 702623 := bstep (se 1 (by rfl) ⟨526967, by rfl⟩ : syracuseStep 702623 = 1053935) B1053935
theorem B704105 : Blo 467785 704105 := bstep (se 2 (by rfl) ⟨264039, by rfl⟩ : syracuseStep 704105 = 528079) B528079
theorem B2997967 : Blo 467785 2997967 := bstep (se 1 (by rfl) ⟨2248475, by rfl⟩ : syracuseStep 2997967 = 4496951) B4496951
theorem B2541127 : Blo 467785 2541127 := bstep (se 1 (by rfl) ⟨1905845, by rfl⟩ : syracuseStep 2541127 = 3811691) B3811691
theorem B33119563 : Blo 467785 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B1053503 : Blo 467785 1053503 := bstep (se 1 (by rfl) ⟨790127, by rfl⟩ : syracuseStep 1053503 = 1580255) B1580255
theorem B791417 : Blo 467785 791417 := bstep (se 2 (by rfl) ⟨296781, by rfl⟩ : syracuseStep 791417 = 593563) B593563
theorem B1053737 : Blo 467785 1053737 := bstep (se 2 (by rfl) ⟨395151, by rfl⟩ : syracuseStep 1053737 = 790303) B790303
theorem B3675239 : Blo 467785 3675239 := bstep (se 1 (by rfl) ⟨2756429, by rfl⟩ : syracuseStep 3675239 = 5512859) B5512859
theorem B18029627 : Blo 467785 18029627 := bstep (se 1 (by rfl) ⟨13522220, by rfl⟩ : syracuseStep 18029627 = 27044441) B27044441
theorem B1057031 : Blo 467785 1057031 := bstep (se 1 (by rfl) ⟨792773, by rfl⟩ : syracuseStep 1057031 = 1585547) B1585547
theorem B468415 : Blo 467785 468415 := bstep (se 1 (by rfl) ⟨351311, by rfl⟩ : syracuseStep 468415 = 702623) B702623
theorem B2369249 : Blo 467785 2369249 := bstep (se 2 (by rfl) ⟨888468, by rfl⟩ : syracuseStep 2369249 = 1776937) B1776937
theorem B469403 : Blo 467785 469403 := bstep (se 1 (by rfl) ⟨352052, by rfl⟩ : syracuseStep 469403 = 704105) B704105
theorem B1061513 : Blo 467785 1061513 := bstep (se 2 (by rfl) ⟨398067, by rfl⟩ : syracuseStep 1061513 = 796135) B796135
theorem B3388169 : Blo 467785 3388169 := bstep (se 2 (by rfl) ⟨1270563, by rfl⟩ : syracuseStep 3388169 = 2541127) B2541127
theorem B4110497 : Blo 467785 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B702791 : Blo 467785 702791 := bstep (se 1 (by rfl) ⟨527093, by rfl⟩ : syracuseStep 702791 = 1054187) B1054187
theorem B704543 : Blo 467785 704543 := bstep (se 1 (by rfl) ⟨528407, by rfl⟩ : syracuseStep 704543 = 1056815) B1056815
theorem B44159417 : Blo 467785 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B86990249 : Blo 467785 86990249 := bstep (se 2 (by rfl) ⟨32621343, by rfl⟩ : syracuseStep 86990249 = 65242687) B65242687
theorem B4025447 : Blo 467785 4025447 := bstep (se 1 (by rfl) ⟨3019085, by rfl⟩ : syracuseStep 4025447 = 6038171) B6038171
theorem B1014761 : Blo 467785 1014761 := bstep (se 2 (by rfl) ⟨380535, by rfl⟩ : syracuseStep 1014761 = 761071) B761071
theorem B3997289 : Blo 467785 3997289 := bstep (se 2 (by rfl) ⟨1498983, by rfl⟩ : syracuseStep 3997289 = 2997967) B2997967
theorem B527611 : Blo 467785 527611 := bstep (se 1 (by rfl) ⟨395708, by rfl⟩ : syracuseStep 527611 = 791417) B791417
theorem B1579499 : Blo 467785 1579499 := bstep (se 1 (by rfl) ⟨1184624, by rfl⟩ : syracuseStep 1579499 = 2369249) B2369249
theorem B468527 : Blo 467785 468527 := bstep (se 1 (by rfl) ⟨351395, by rfl⟩ : syracuseStep 468527 = 702791) B702791
theorem B2664859 : Blo 467785 2664859 := bstep (se 1 (by rfl) ⟨1998644, by rfl⟩ : syracuseStep 2664859 = 3997289) B3997289
theorem B469695 : Blo 467785 469695 := bstep (se 1 (by rfl) ⟨352271, by rfl⟩ : syracuseStep 469695 = 704543) B704543
theorem B29439611 : Blo 467785 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B702335 : Blo 467785 702335 := bstep (se 1 (by rfl) ⟨526751, by rfl⟩ : syracuseStep 702335 = 1053503) B1053503
theorem B702491 : Blo 467785 702491 := bstep (se 1 (by rfl) ⟨526868, by rfl⟩ : syracuseStep 702491 = 1053737) B1053737
theorem B704687 : Blo 467785 704687 := bstep (se 1 (by rfl) ⟨528515, by rfl⟩ : syracuseStep 704687 = 1057031) B1057031
theorem B707675 : Blo 467785 707675 := bstep (se 1 (by rfl) ⟨530756, by rfl⟩ : syracuseStep 707675 = 1061513) B1061513
theorem B2740331 : Blo 467785 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B676507 : Blo 467785 676507 := bstep (se 1 (by rfl) ⟨507380, by rfl⟩ : syracuseStep 676507 = 1014761) B1014761
theorem B2450159 : Blo 467785 2450159 := bstep (se 1 (by rfl) ⟨1837619, by rfl⟩ : syracuseStep 2450159 = 3675239) B3675239
theorem B12019751 : Blo 467785 12019751 := bstep (se 1 (by rfl) ⟨9014813, by rfl⟩ : syracuseStep 12019751 = 18029627) B18029627
theorem B57993499 : Blo 467785 57993499 := bstep (se 1 (by rfl) ⟨43495124, by rfl⟩ : syracuseStep 57993499 = 86990249) B86990249
theorem B2683631 : Blo 467785 2683631 := bstep (se 1 (by rfl) ⟨2012723, by rfl⟩ : syracuseStep 2683631 = 4025447) B4025447
theorem B2258779 : Blo 467785 2258779 := bstep (se 1 (by rfl) ⟨1694084, by rfl⟩ : syracuseStep 2258779 = 3388169) B3388169
theorem B1052999 : Blo 467785 1052999 := bstep (se 1 (by rfl) ⟨789749, by rfl⟩ : syracuseStep 1052999 = 1579499) B1579499
theorem B468223 : Blo 467785 468223 := bstep (se 1 (by rfl) ⟨351167, by rfl⟩ : syracuseStep 468223 = 702335) B702335
theorem B468327 : Blo 467785 468327 := bstep (se 1 (by rfl) ⟨351245, by rfl⟩ : syracuseStep 468327 = 702491) B702491
theorem B469791 : Blo 467785 469791 := bstep (se 1 (by rfl) ⟨352343, by rfl⟩ : syracuseStep 469791 = 704687) B704687
theorem B471783 : Blo 467785 471783 := bstep (se 1 (by rfl) ⟨353837, by rfl⟩ : syracuseStep 471783 = 707675) B707675
theorem B3553145 : Blo 467785 3553145 := bstep (se 2 (by rfl) ⟨1332429, by rfl⟩ : syracuseStep 3553145 = 2664859) B2664859
theorem B703481 : Blo 467785 703481 := bstep (se 2 (by rfl) ⟨263805, by rfl⟩ : syracuseStep 703481 = 527611) B527611
theorem B902009 : Blo 467785 902009 := bstep (se 2 (by rfl) ⟨338253, by rfl⟩ : syracuseStep 902009 = 676507) B676507
theorem B8013167 : Blo 467785 8013167 := bstep (se 1 (by rfl) ⟨6009875, by rfl⟩ : syracuseStep 8013167 = 12019751) B12019751
theorem B1789087 : Blo 467785 1789087 := bstep (se 1 (by rfl) ⟨1341815, by rfl⟩ : syracuseStep 1789087 = 2683631) B2683631
theorem B1826887 : Blo 467785 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B77324665 : Blo 467785 77324665 := bstep (se 2 (by rfl) ⟨28996749, by rfl⟩ : syracuseStep 77324665 = 57993499) B57993499
theorem B1633439 : Blo 467785 1633439 := bstep (se 1 (by rfl) ⟨1225079, by rfl⟩ : syracuseStep 1633439 = 2450159) B2450159
theorem B3011705 : Blo 467785 3011705 := bstep (se 2 (by rfl) ⟨1129389, by rfl⟩ : syracuseStep 3011705 = 2258779) B2258779
theorem B19626407 : Blo 467785 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B5342111 : Blo 467785 5342111 := bstep (se 1 (by rfl) ⟨4006583, by rfl⟩ : syracuseStep 5342111 = 8013167) B8013167
theorem B1088959 : Blo 467785 1088959 := bstep (se 1 (by rfl) ⟨816719, by rfl⟩ : syracuseStep 1088959 = 1633439) B1633439
theorem B2007803 : Blo 467785 2007803 := bstep (se 1 (by rfl) ⟨1505852, by rfl⟩ : syracuseStep 2007803 = 3011705) B3011705
theorem B2368763 : Blo 467785 2368763 := bstep (se 1 (by rfl) ⟨1776572, by rfl⟩ : syracuseStep 2368763 = 3553145) B3553145
theorem B13084271 : Blo 467785 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B468987 : Blo 467785 468987 := bstep (se 1 (by rfl) ⟨351740, by rfl⟩ : syracuseStep 468987 = 703481) B703481
theorem B2435849 : Blo 467785 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B103099553 : Blo 467785 103099553 := bstep (se 2 (by rfl) ⟨38662332, by rfl⟩ : syracuseStep 103099553 = 77324665) B77324665
theorem B601339 : Blo 467785 601339 := bstep (se 1 (by rfl) ⟨451004, by rfl⟩ : syracuseStep 601339 = 902009) B902009
theorem B701999 : Blo 467785 701999 := bstep (se 1 (by rfl) ⟨526499, by rfl⟩ : syracuseStep 701999 = 1052999) B1052999
theorem B2385449 : Blo 467785 2385449 := bstep (se 2 (by rfl) ⟨894543, by rfl⟩ : syracuseStep 2385449 = 1789087) B1789087
theorem B1579175 : Blo 467785 1579175 := bstep (se 1 (by rfl) ⟨1184381, by rfl⟩ : syracuseStep 1579175 = 2368763) B2368763
theorem B8722847 : Blo 467785 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B467999 : Blo 467785 467999 := bstep (se 1 (by rfl) ⟨350999, by rfl⟩ : syracuseStep 467999 = 701999) B701999
theorem B1451945 : Blo 467785 1451945 := bstep (se 2 (by rfl) ⟨544479, by rfl⟩ : syracuseStep 1451945 = 1088959) B1088959
theorem B801785 : Blo 467785 801785 := bstep (se 2 (by rfl) ⟨300669, by rfl⟩ : syracuseStep 801785 = 601339) B601339
theorem B1590299 : Blo 467785 1590299 := bstep (se 1 (by rfl) ⟨1192724, by rfl⟩ : syracuseStep 1590299 = 2385449) B2385449
theorem B1623899 : Blo 467785 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B68733035 : Blo 467785 68733035 := bstep (se 1 (by rfl) ⟨51549776, by rfl⟩ : syracuseStep 68733035 = 103099553) B103099553
theorem B3561407 : Blo 467785 3561407 := bstep (se 1 (by rfl) ⟨2671055, by rfl⟩ : syracuseStep 3561407 = 5342111) B5342111
theorem B1338535 : Blo 467785 1338535 := bstep (se 1 (by rfl) ⟨1003901, by rfl⟩ : syracuseStep 1338535 = 2007803) B2007803
theorem B1052783 : Blo 467785 1052783 := bstep (se 1 (by rfl) ⟨789587, by rfl⟩ : syracuseStep 1052783 = 1579175) B1579175
theorem B4330397 : Blo 467785 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B534523 : Blo 467785 534523 := bstep (se 1 (by rfl) ⟨400892, by rfl⟩ : syracuseStep 534523 = 801785) B801785
theorem B1060199 : Blo 467785 1060199 := bstep (se 1 (by rfl) ⟨795149, by rfl⟩ : syracuseStep 1060199 = 1590299) B1590299
theorem B45822023 : Blo 467785 45822023 := bstep (se 1 (by rfl) ⟨34366517, by rfl⟩ : syracuseStep 45822023 = 68733035) B68733035
theorem B2374271 : Blo 467785 2374271 := bstep (se 1 (by rfl) ⟨1780703, by rfl⟩ : syracuseStep 2374271 = 3561407) B3561407
theorem B1784713 : Blo 467785 1784713 := bstep (se 2 (by rfl) ⟨669267, by rfl⟩ : syracuseStep 1784713 = 1338535) B1338535
theorem B967963 : Blo 467785 967963 := bstep (se 1 (by rfl) ⟨725972, by rfl⟩ : syracuseStep 967963 = 1451945) B1451945
theorem B23260925 : Blo 467785 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B2886931 : Blo 467785 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B15507283 : Blo 467785 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B30548015 : Blo 467785 30548015 := bstep (se 1 (by rfl) ⟨22911011, by rfl⟩ : syracuseStep 30548015 = 45822023) B45822023
theorem B1582847 : Blo 467785 1582847 := bstep (se 1 (by rfl) ⟨1187135, by rfl⟩ : syracuseStep 1582847 = 2374271) B2374271
theorem B1290617 : Blo 467785 1290617 := bstep (se 2 (by rfl) ⟨483981, by rfl⟩ : syracuseStep 1290617 = 967963) B967963
theorem B701855 : Blo 467785 701855 := bstep (se 1 (by rfl) ⟨526391, by rfl⟩ : syracuseStep 701855 = 1052783) B1052783
theorem B706799 : Blo 467785 706799 := bstep (se 1 (by rfl) ⟨530099, by rfl⟩ : syracuseStep 706799 = 1060199) B1060199
theorem B2379617 : Blo 467785 2379617 := bstep (se 2 (by rfl) ⟨892356, by rfl⟩ : syracuseStep 2379617 = 1784713) B1784713
theorem B712697 : Blo 467785 712697 := bstep (se 2 (by rfl) ⟨267261, by rfl⟩ : syracuseStep 712697 = 534523) B534523
theorem B1055231 : Blo 467785 1055231 := bstep (se 1 (by rfl) ⟨791423, by rfl⟩ : syracuseStep 1055231 = 1582847) B1582847
theorem B860411 : Blo 467785 860411 := bstep (se 1 (by rfl) ⟨645308, by rfl⟩ : syracuseStep 860411 = 1290617) B1290617
theorem B467903 : Blo 467785 467903 := bstep (se 1 (by rfl) ⟨350927, by rfl⟩ : syracuseStep 467903 = 701855) B701855
theorem B471199 : Blo 467785 471199 := bstep (se 1 (by rfl) ⟨353399, by rfl⟩ : syracuseStep 471199 = 706799) B706799
theorem B1586411 : Blo 467785 1586411 := bstep (se 1 (by rfl) ⟨1189808, by rfl⟩ : syracuseStep 1586411 = 2379617) B2379617
theorem B3849241 : Blo 467785 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B20365343 : Blo 467785 20365343 := bstep (se 1 (by rfl) ⟨15274007, by rfl⟩ : syracuseStep 20365343 = 30548015) B30548015
theorem B20676377 : Blo 467785 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B1900525 : Blo 467785 1900525 := bstep (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) B712697
theorem B1057607 : Blo 467785 1057607 := bstep (se 1 (by rfl) ⟨793205, by rfl⟩ : syracuseStep 1057607 = 1586411) B1586411
theorem B2534033 : Blo 467785 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B13576895 : Blo 467785 13576895 := bstep (se 1 (by rfl) ⟨10182671, by rfl⟩ : syracuseStep 13576895 = 20365343) B20365343
theorem B703487 : Blo 467785 703487 := bstep (se 1 (by rfl) ⟨527615, by rfl⟩ : syracuseStep 703487 = 1055231) B1055231
theorem B573607 : Blo 467785 573607 := bstep (se 1 (by rfl) ⟨430205, by rfl⟩ : syracuseStep 573607 = 860411) B860411
theorem B5132321 : Blo 467785 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B13784251 : Blo 467785 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B9051263 : Blo 467785 9051263 := bstep (se 1 (by rfl) ⟨6788447, by rfl⟩ : syracuseStep 9051263 = 13576895) B13576895
theorem B468991 : Blo 467785 468991 := bstep (se 1 (by rfl) ⟨351743, by rfl⟩ : syracuseStep 468991 = 703487) B703487
theorem B3059237 : Blo 467785 3059237 := bstep (se 4 (by rfl) ⟨286803, by rfl⟩ : syracuseStep 3059237 = 573607) B573607
theorem B3421547 : Blo 467785 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B705071 : Blo 467785 705071 := bstep (se 1 (by rfl) ⟨528803, by rfl⟩ : syracuseStep 705071 = 1057607) B1057607
theorem B1689355 : Blo 467785 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B18379001 : Blo 467785 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B6034175 : Blo 467785 6034175 := bstep (se 1 (by rfl) ⟨4525631, by rfl⟩ : syracuseStep 6034175 = 9051263) B9051263
theorem B2039491 : Blo 467785 2039491 := bstep (se 1 (by rfl) ⟨1529618, by rfl⟩ : syracuseStep 2039491 = 3059237) B3059237
theorem B470047 : Blo 467785 470047 := bstep (se 1 (by rfl) ⟨352535, by rfl⟩ : syracuseStep 470047 = 705071) B705071
theorem B2281031 : Blo 467785 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B49010669 : Blo 467785 49010669 := bstep (se 3 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 49010669 = 18379001) B18379001
theorem B9009893 : Blo 467785 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B32673779 : Blo 467785 32673779 := bstep (se 1 (by rfl) ⟨24505334, by rfl⟩ : syracuseStep 32673779 = 49010669) B49010669
theorem B6006595 : Blo 467785 6006595 := bstep (se 1 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 6006595 = 9009893) B9009893
theorem B1520687 : Blo 467785 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B4022783 : Blo 467785 4022783 := bstep (se 1 (by rfl) ⟨3017087, by rfl⟩ : syracuseStep 4022783 = 6034175) B6034175
theorem B10877285 : Blo 467785 10877285 := bstep (se 4 (by rfl) ⟨1019745, by rfl⟩ : syracuseStep 10877285 = 2039491) B2039491
theorem B29006093 : Blo 467785 29006093 := bstep (se 3 (by rfl) ⟨5438642, by rfl⟩ : syracuseStep 29006093 = 10877285) B10877285
theorem B8008793 : Blo 467785 8008793 := bstep (se 2 (by rfl) ⟨3003297, by rfl⟩ : syracuseStep 8008793 = 6006595) B6006595
theorem B21782519 : Blo 467785 21782519 := bstep (se 1 (by rfl) ⟨16336889, by rfl⟩ : syracuseStep 21782519 = 32673779) B32673779
theorem B2681855 : Blo 467785 2681855 := bstep (se 1 (by rfl) ⟨2011391, by rfl⟩ : syracuseStep 2681855 = 4022783) B4022783
theorem B1013791 : Blo 467785 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B19337395 : Blo 467785 19337395 := bstep (se 1 (by rfl) ⟨14503046, by rfl⟩ : syracuseStep 19337395 = 29006093) B29006093
theorem B14521679 : Blo 467785 14521679 := bstep (se 1 (by rfl) ⟨10891259, by rfl⟩ : syracuseStep 14521679 = 21782519) B21782519
theorem B1351721 : Blo 467785 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B1787903 : Blo 467785 1787903 := bstep (se 1 (by rfl) ⟨1340927, by rfl⟩ : syracuseStep 1787903 = 2681855) B2681855
theorem B5339195 : Blo 467785 5339195 := bstep (se 1 (by rfl) ⟨4004396, by rfl⟩ : syracuseStep 5339195 = 8008793) B8008793
theorem B1191935 : Blo 467785 1191935 := bstep (se 1 (by rfl) ⟨893951, by rfl⟩ : syracuseStep 1191935 = 1787903) B1787903
theorem B9681119 : Blo 467785 9681119 := bstep (se 1 (by rfl) ⟨7260839, by rfl⟩ : syracuseStep 9681119 = 14521679) B14521679
theorem B901147 : Blo 467785 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B3559463 : Blo 467785 3559463 := bstep (se 1 (by rfl) ⟨2669597, by rfl⟩ : syracuseStep 3559463 = 5339195) B5339195
theorem B25783193 : Blo 467785 25783193 := bstep (se 2 (by rfl) ⟨9668697, by rfl⟩ : syracuseStep 25783193 = 19337395) B19337395
theorem B794623 : Blo 467785 794623 := bstep (se 1 (by rfl) ⟨595967, by rfl⟩ : syracuseStep 794623 = 1191935) B1191935
theorem B2372975 : Blo 467785 2372975 := bstep (se 1 (by rfl) ⟨1779731, by rfl⟩ : syracuseStep 2372975 = 3559463) B3559463
theorem B17188795 : Blo 467785 17188795 := bstep (se 1 (by rfl) ⟨12891596, by rfl⟩ : syracuseStep 17188795 = 25783193) B25783193
theorem B1201529 : Blo 467785 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B6454079 : Blo 467785 6454079 := bstep (se 1 (by rfl) ⟨4840559, by rfl⟩ : syracuseStep 6454079 = 9681119) B9681119
theorem B1581983 : Blo 467785 1581983 := bstep (se 1 (by rfl) ⟨1186487, by rfl⟩ : syracuseStep 1581983 = 2372975) B2372975
theorem B4302719 : Blo 467785 4302719 := bstep (se 1 (by rfl) ⟨3227039, by rfl⟩ : syracuseStep 4302719 = 6454079) B6454079
theorem B1059497 : Blo 467785 1059497 := bstep (se 2 (by rfl) ⟨397311, by rfl⟩ : syracuseStep 1059497 = 794623) B794623
theorem B22918393 : Blo 467785 22918393 := bstep (se 2 (by rfl) ⟨8594397, by rfl⟩ : syracuseStep 22918393 = 17188795) B17188795
theorem B801019 : Blo 467785 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B1054655 : Blo 467785 1054655 := bstep (se 1 (by rfl) ⟨790991, by rfl⟩ : syracuseStep 1054655 = 1581983) B1581983
theorem B4272101 : Blo 467785 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B2868479 : Blo 467785 2868479 := bstep (se 1 (by rfl) ⟨2151359, by rfl⟩ : syracuseStep 2868479 = 4302719) B4302719
theorem B30557857 : Blo 467785 30557857 := bstep (se 2 (by rfl) ⟨11459196, by rfl⟩ : syracuseStep 30557857 = 22918393) B22918393
theorem B706331 : Blo 467785 706331 := bstep (se 1 (by rfl) ⟨529748, by rfl⟩ : syracuseStep 706331 = 1059497) B1059497
theorem B1912319 : Blo 467785 1912319 := bstep (se 1 (by rfl) ⟨1434239, by rfl⟩ : syracuseStep 1912319 = 2868479) B2868479
theorem B470887 : Blo 467785 470887 := bstep (se 1 (by rfl) ⟨353165, by rfl⟩ : syracuseStep 470887 = 706331) B706331
theorem B40743809 : Blo 467785 40743809 := bstep (se 2 (by rfl) ⟨15278928, by rfl⟩ : syracuseStep 40743809 = 30557857) B30557857
theorem B703103 : Blo 467785 703103 := bstep (se 1 (by rfl) ⟨527327, by rfl⟩ : syracuseStep 703103 = 1054655) B1054655
theorem B2848067 : Blo 467785 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B468735 : Blo 467785 468735 := bstep (se 1 (by rfl) ⟨351551, by rfl⟩ : syracuseStep 468735 = 703103) B703103
theorem B1274879 : Blo 467785 1274879 := bstep (se 1 (by rfl) ⟨956159, by rfl⟩ : syracuseStep 1274879 = 1912319) B1912319
theorem B27162539 : Blo 467785 27162539 := bstep (se 1 (by rfl) ⟨20371904, by rfl⟩ : syracuseStep 27162539 = 40743809) B40743809
theorem B1898711 : Blo 467785 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B18108359 : Blo 467785 18108359 := bstep (se 1 (by rfl) ⟨13581269, by rfl⟩ : syracuseStep 18108359 = 27162539) B27162539
theorem B1265807 : Blo 467785 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B3399677 : Blo 467785 3399677 := bstep (se 3 (by rfl) ⟨637439, by rfl⟩ : syracuseStep 3399677 = 1274879) B1274879
theorem B2266451 : Blo 467785 2266451 := bstep (se 1 (by rfl) ⟨1699838, by rfl⟩ : syracuseStep 2266451 = 3399677) B3399677
theorem B12072239 : Blo 467785 12072239 := bstep (se 1 (by rfl) ⟨9054179, by rfl⟩ : syracuseStep 12072239 = 18108359) B18108359
theorem B843871 : Blo 467785 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B1510967 : Blo 467785 1510967 := bstep (se 1 (by rfl) ⟨1133225, by rfl⟩ : syracuseStep 1510967 = 2266451) B2266451
theorem B1125161 : Blo 467785 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B8048159 : Blo 467785 8048159 := bstep (se 1 (by rfl) ⟨6036119, by rfl⟩ : syracuseStep 8048159 = 12072239) B12072239
theorem B5365439 : Blo 467785 5365439 := bstep (se 1 (by rfl) ⟨4024079, by rfl⟩ : syracuseStep 5365439 = 8048159) B8048159
theorem B1007311 : Blo 467785 1007311 := bstep (se 1 (by rfl) ⟨755483, by rfl⟩ : syracuseStep 1007311 = 1510967) B1510967
theorem B750107 : Blo 467785 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B2000285 : Blo 467785 2000285 := bstep (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) B750107
theorem B3576959 : Blo 467785 3576959 := bstep (se 1 (by rfl) ⟨2682719, by rfl⟩ : syracuseStep 3576959 = 5365439) B5365439
theorem B1343081 : Blo 467785 1343081 := bstep (se 2 (by rfl) ⟨503655, by rfl⟩ : syracuseStep 1343081 = 1007311) B1007311
theorem B895387 : Blo 467785 895387 := bstep (se 1 (by rfl) ⟨671540, by rfl⟩ : syracuseStep 895387 = 1343081) B1343081
theorem B1333523 : Blo 467785 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B2384639 : Blo 467785 2384639 := bstep (se 1 (by rfl) ⟨1788479, by rfl⟩ : syracuseStep 2384639 = 3576959) B3576959
theorem B1193849 : Blo 467785 1193849 := bstep (se 2 (by rfl) ⟨447693, by rfl⟩ : syracuseStep 1193849 = 895387) B895387
theorem B1589759 : Blo 467785 1589759 := bstep (se 1 (by rfl) ⟨1192319, by rfl⟩ : syracuseStep 1589759 = 2384639) B2384639
theorem B3556061 : Blo 467785 3556061 := bstep (se 3 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 3556061 = 1333523) B1333523
theorem B795899 : Blo 467785 795899 := bstep (se 1 (by rfl) ⟨596924, by rfl⟩ : syracuseStep 795899 = 1193849) B1193849
theorem B1059839 : Blo 467785 1059839 := bstep (se 1 (by rfl) ⟨794879, by rfl⟩ : syracuseStep 1059839 = 1589759) B1589759
theorem B2370707 : Blo 467785 2370707 := bstep (se 1 (by rfl) ⟨1778030, by rfl⟩ : syracuseStep 2370707 = 3556061) B3556061
theorem B530599 : Blo 467785 530599 := bstep (se 1 (by rfl) ⟨397949, by rfl⟩ : syracuseStep 530599 = 795899) B795899
theorem B1580471 : Blo 467785 1580471 := bstep (se 1 (by rfl) ⟨1185353, by rfl⟩ : syracuseStep 1580471 = 2370707) B2370707
theorem B706559 : Blo 467785 706559 := bstep (se 1 (by rfl) ⟨529919, by rfl⟩ : syracuseStep 706559 = 1059839) B1059839
theorem B1053647 : Blo 467785 1053647 := bstep (se 1 (by rfl) ⟨790235, by rfl⟩ : syracuseStep 1053647 = 1580471) B1580471
theorem B471039 : Blo 467785 471039 := bstep (se 1 (by rfl) ⟨353279, by rfl⟩ : syracuseStep 471039 = 706559) B706559
theorem B707465 : Blo 467785 707465 := bstep (se 2 (by rfl) ⟨265299, by rfl⟩ : syracuseStep 707465 = 530599) B530599
theorem B471643 : Blo 467785 471643 := bstep (se 1 (by rfl) ⟨353732, by rfl⟩ : syracuseStep 471643 = 707465) B707465
theorem B702431 : Blo 467785 702431 := bstep (se 1 (by rfl) ⟨526823, by rfl⟩ : syracuseStep 702431 = 1053647) B1053647
theorem B468287 : Blo 467785 468287 := bstep (se 1 (by rfl) ⟨351215, by rfl⟩ : syracuseStep 468287 = 702431) B702431

theorem C0 (j : ℕ) (h1 : 116946 ≤ j) (h2 : j ≤ 117645) : Blo 467785 (4 * j + 3) := by
  interval_cases j
  · exact B467787
  · exact B467791
  · exact B467795
  · exact B467799
  · exact B467803
  · exact B467807
  · exact B467811
  · exact B467815
  · exact B467819
  · exact B467823
  · exact B467827
  · exact B467831
  · exact B467835
  · exact B467839
  · exact B467843
  · exact B467847
  · exact B467851
  · exact B467855
  · exact B467859
  · exact B467863
  · exact B467867
  · exact B467871
  · exact B467875
  · exact B467879
  · exact B467883
  · exact B467887
  · exact B467891
  · exact B467895
  · exact B467899
  · exact B467903
  · exact B467907
  · exact B467911
  · exact B467915
  · exact B467919
  · exact B467923
  · exact B467927
  · exact B467931
  · exact B467935
  · exact B467939
  · exact B467943
  · exact B467947
  · exact B467951
  · exact B467955
  · exact B467959
  · exact B467963
  · exact B467967
  · exact B467971
  · exact B467975
  · exact B467979
  · exact B467983
  · exact B467987
  · exact B467991
  · exact B467995
  · exact B467999
  · exact B468003
  · exact B468007
  · exact B468011
  · exact B468015
  · exact B468019
  · exact B468023
  · exact B468027
  · exact B468031
  · exact B468035
  · exact B468039
  · exact B468043
  · exact B468047
  · exact B468051
  · exact B468055
  · exact B468059
  · exact B468063
  · exact B468067
  · exact B468071
  · exact B468075
  · exact B468079
  · exact B468083
  · exact B468087
  · exact B468091
  · exact B468095
  · exact B468099
  · exact B468103
  · exact B468107
  · exact B468111
  · exact B468115
  · exact B468119
  · exact B468123
  · exact B468127
  · exact B468131
  · exact B468135
  · exact B468139
  · exact B468143
  · exact B468147
  · exact B468151
  · exact B468155
  · exact B468159
  · exact B468163
  · exact B468167
  · exact B468171
  · exact B468175
  · exact B468179
  · exact B468183
  · exact B468187
  · exact B468191
  · exact B468195
  · exact B468199
  · exact B468203
  · exact B468207
  · exact B468211
  · exact B468215
  · exact B468219
  · exact B468223
  · exact B468227
  · exact B468231
  · exact B468235
  · exact B468239
  · exact B468243
  · exact B468247
  · exact B468251
  · exact B468255
  · exact B468259
  · exact B468263
  · exact B468267
  · exact B468271
  · exact B468275
  · exact B468279
  · exact B468283
  · exact B468287
  · exact B468291
  · exact B468295
  · exact B468299
  · exact B468303
  · exact B468307
  · exact B468311
  · exact B468315
  · exact B468319
  · exact B468323
  · exact B468327
  · exact B468331
  · exact B468335
  · exact B468339
  · exact B468343
  · exact B468347
  · exact B468351
  · exact B468355
  · exact B468359
  · exact B468363
  · exact B468367
  · exact B468371
  · exact B468375
  · exact B468379
  · exact B468383
  · exact B468387
  · exact B468391
  · exact B468395
  · exact B468399
  · exact B468403
  · exact B468407
  · exact B468411
  · exact B468415
  · exact B468419
  · exact B468423
  · exact B468427
  · exact B468431
  · exact B468435
  · exact B468439
  · exact B468443
  · exact B468447
  · exact B468451
  · exact B468455
  · exact B468459
  · exact B468463
  · exact B468467
  · exact B468471
  · exact B468475
  · exact B468479
  · exact B468483
  · exact B468487
  · exact B468491
  · exact B468495
  · exact B468499
  · exact B468503
  · exact B468507
  · exact B468511
  · exact B468515
  · exact B468519
  · exact B468523
  · exact B468527
  · exact B468531
  · exact B468535
  · exact B468539
  · exact B468543
  · exact B468547
  · exact B468551
  · exact B468555
  · exact B468559
  · exact B468563
  · exact B468567
  · exact B468571
  · exact B468575
  · exact B468579
  · exact B468583
  · exact B468587
  · exact B468591
  · exact B468595
  · exact B468599
  · exact B468603
  · exact B468607
  · exact B468611
  · exact B468615
  · exact B468619
  · exact B468623
  · exact B468627
  · exact B468631
  · exact B468635
  · exact B468639
  · exact B468643
  · exact B468647
  · exact B468651
  · exact B468655
  · exact B468659
  · exact B468663
  · exact B468667
  · exact B468671
  · exact B468675
  · exact B468679
  · exact B468683
  · exact B468687
  · exact B468691
  · exact B468695
  · exact B468699
  · exact B468703
  · exact B468707
  · exact B468711
  · exact B468715
  · exact B468719
  · exact B468723
  · exact B468727
  · exact B468731
  · exact B468735
  · exact B468739
  · exact B468743
  · exact B468747
  · exact B468751
  · exact B468755
  · exact B468759
  · exact B468763
  · exact B468767
  · exact B468771
  · exact B468775
  · exact B468779
  · exact B468783
  · exact B468787
  · exact B468791
  · exact B468795
  · exact B468799
  · exact B468803
  · exact B468807
  · exact B468811
  · exact B468815
  · exact B468819
  · exact B468823
  · exact B468827
  · exact B468831
  · exact B468835
  · exact B468839
  · exact B468843
  · exact B468847
  · exact B468851
  · exact B468855
  · exact B468859
  · exact B468863
  · exact B468867
  · exact B468871
  · exact B468875
  · exact B468879
  · exact B468883
  · exact B468887
  · exact B468891
  · exact B468895
  · exact B468899
  · exact B468903
  · exact B468907
  · exact B468911
  · exact B468915
  · exact B468919
  · exact B468923
  · exact B468927
  · exact B468931
  · exact B468935
  · exact B468939
  · exact B468943
  · exact B468947
  · exact B468951
  · exact B468955
  · exact B468959
  · exact B468963
  · exact B468967
  · exact B468971
  · exact B468975
  · exact B468979
  · exact B468983
  · exact B468987
  · exact B468991
  · exact B468995
  · exact B468999
  · exact B469003
  · exact B469007
  · exact B469011
  · exact B469015
  · exact B469019
  · exact B469023
  · exact B469027
  · exact B469031
  · exact B469035
  · exact B469039
  · exact B469043
  · exact B469047
  · exact B469051
  · exact B469055
  · exact B469059
  · exact B469063
  · exact B469067
  · exact B469071
  · exact B469075
  · exact B469079
  · exact B469083
  · exact B469087
  · exact B469091
  · exact B469095
  · exact B469099
  · exact B469103
  · exact B469107
  · exact B469111
  · exact B469115
  · exact B469119
  · exact B469123
  · exact B469127
  · exact B469131
  · exact B469135
  · exact B469139
  · exact B469143
  · exact B469147
  · exact B469151
  · exact B469155
  · exact B469159
  · exact B469163
  · exact B469167
  · exact B469171
  · exact B469175
  · exact B469179
  · exact B469183
  · exact B469187
  · exact B469191
  · exact B469195
  · exact B469199
  · exact B469203
  · exact B469207
  · exact B469211
  · exact B469215
  · exact B469219
  · exact B469223
  · exact B469227
  · exact B469231
  · exact B469235
  · exact B469239
  · exact B469243
  · exact B469247
  · exact B469251
  · exact B469255
  · exact B469259
  · exact B469263
  · exact B469267
  · exact B469271
  · exact B469275
  · exact B469279
  · exact B469283
  · exact B469287
  · exact B469291
  · exact B469295
  · exact B469299
  · exact B469303
  · exact B469307
  · exact B469311
  · exact B469315
  · exact B469319
  · exact B469323
  · exact B469327
  · exact B469331
  · exact B469335
  · exact B469339
  · exact B469343
  · exact B469347
  · exact B469351
  · exact B469355
  · exact B469359
  · exact B469363
  · exact B469367
  · exact B469371
  · exact B469375
  · exact B469379
  · exact B469383
  · exact B469387
  · exact B469391
  · exact B469395
  · exact B469399
  · exact B469403
  · exact B469407
  · exact B469411
  · exact B469415
  · exact B469419
  · exact B469423
  · exact B469427
  · exact B469431
  · exact B469435
  · exact B469439
  · exact B469443
  · exact B469447
  · exact B469451
  · exact B469455
  · exact B469459
  · exact B469463
  · exact B469467
  · exact B469471
  · exact B469475
  · exact B469479
  · exact B469483
  · exact B469487
  · exact B469491
  · exact B469495
  · exact B469499
  · exact B469503
  · exact B469507
  · exact B469511
  · exact B469515
  · exact B469519
  · exact B469523
  · exact B469527
  · exact B469531
  · exact B469535
  · exact B469539
  · exact B469543
  · exact B469547
  · exact B469551
  · exact B469555
  · exact B469559
  · exact B469563
  · exact B469567
  · exact B469571
  · exact B469575
  · exact B469579
  · exact B469583
  · exact B469587
  · exact B469591
  · exact B469595
  · exact B469599
  · exact B469603
  · exact B469607
  · exact B469611
  · exact B469615
  · exact B469619
  · exact B469623
  · exact B469627
  · exact B469631
  · exact B469635
  · exact B469639
  · exact B469643
  · exact B469647
  · exact B469651
  · exact B469655
  · exact B469659
  · exact B469663
  · exact B469667
  · exact B469671
  · exact B469675
  · exact B469679
  · exact B469683
  · exact B469687
  · exact B469691
  · exact B469695
  · exact B469699
  · exact B469703
  · exact B469707
  · exact B469711
  · exact B469715
  · exact B469719
  · exact B469723
  · exact B469727
  · exact B469731
  · exact B469735
  · exact B469739
  · exact B469743
  · exact B469747
  · exact B469751
  · exact B469755
  · exact B469759
  · exact B469763
  · exact B469767
  · exact B469771
  · exact B469775
  · exact B469779
  · exact B469783
  · exact B469787
  · exact B469791
  · exact B469795
  · exact B469799
  · exact B469803
  · exact B469807
  · exact B469811
  · exact B469815
  · exact B469819
  · exact B469823
  · exact B469827
  · exact B469831
  · exact B469835
  · exact B469839
  · exact B469843
  · exact B469847
  · exact B469851
  · exact B469855
  · exact B469859
  · exact B469863
  · exact B469867
  · exact B469871
  · exact B469875
  · exact B469879
  · exact B469883
  · exact B469887
  · exact B469891
  · exact B469895
  · exact B469899
  · exact B469903
  · exact B469907
  · exact B469911
  · exact B469915
  · exact B469919
  · exact B469923
  · exact B469927
  · exact B469931
  · exact B469935
  · exact B469939
  · exact B469943
  · exact B469947
  · exact B469951
  · exact B469955
  · exact B469959
  · exact B469963
  · exact B469967
  · exact B469971
  · exact B469975
  · exact B469979
  · exact B469983
  · exact B469987
  · exact B469991
  · exact B469995
  · exact B469999
  · exact B470003
  · exact B470007
  · exact B470011
  · exact B470015
  · exact B470019
  · exact B470023
  · exact B470027
  · exact B470031
  · exact B470035
  · exact B470039
  · exact B470043
  · exact B470047
  · exact B470051
  · exact B470055
  · exact B470059
  · exact B470063
  · exact B470067
  · exact B470071
  · exact B470075
  · exact B470079
  · exact B470083
  · exact B470087
  · exact B470091
  · exact B470095
  · exact B470099
  · exact B470103
  · exact B470107
  · exact B470111
  · exact B470115
  · exact B470119
  · exact B470123
  · exact B470127
  · exact B470131
  · exact B470135
  · exact B470139
  · exact B470143
  · exact B470147
  · exact B470151
  · exact B470155
  · exact B470159
  · exact B470163
  · exact B470167
  · exact B470171
  · exact B470175
  · exact B470179
  · exact B470183
  · exact B470187
  · exact B470191
  · exact B470195
  · exact B470199
  · exact B470203
  · exact B470207
  · exact B470211
  · exact B470215
  · exact B470219
  · exact B470223
  · exact B470227
  · exact B470231
  · exact B470235
  · exact B470239
  · exact B470243
  · exact B470247
  · exact B470251
  · exact B470255
  · exact B470259
  · exact B470263
  · exact B470267
  · exact B470271
  · exact B470275
  · exact B470279
  · exact B470283
  · exact B470287
  · exact B470291
  · exact B470295
  · exact B470299
  · exact B470303
  · exact B470307
  · exact B470311
  · exact B470315
  · exact B470319
  · exact B470323
  · exact B470327
  · exact B470331
  · exact B470335
  · exact B470339
  · exact B470343
  · exact B470347
  · exact B470351
  · exact B470355
  · exact B470359
  · exact B470363
  · exact B470367
  · exact B470371
  · exact B470375
  · exact B470379
  · exact B470383
  · exact B470387
  · exact B470391
  · exact B470395
  · exact B470399
  · exact B470403
  · exact B470407
  · exact B470411
  · exact B470415
  · exact B470419
  · exact B470423
  · exact B470427
  · exact B470431
  · exact B470435
  · exact B470439
  · exact B470443
  · exact B470447
  · exact B470451
  · exact B470455
  · exact B470459
  · exact B470463
  · exact B470467
  · exact B470471
  · exact B470475
  · exact B470479
  · exact B470483
  · exact B470487
  · exact B470491
  · exact B470495
  · exact B470499
  · exact B470503
  · exact B470507
  · exact B470511
  · exact B470515
  · exact B470519
  · exact B470523
  · exact B470527
  · exact B470531
  · exact B470535
  · exact B470539
  · exact B470543
  · exact B470547
  · exact B470551
  · exact B470555
  · exact B470559
  · exact B470563
  · exact B470567
  · exact B470571
  · exact B470575
  · exact B470579
  · exact B470583

theorem C1 (j : ℕ) (h1 : 117646 ≤ j) (h2 : j ≤ 117945) : Blo 467785 (4 * j + 3) := by
  interval_cases j
  · exact B470587
  · exact B470591
  · exact B470595
  · exact B470599
  · exact B470603
  · exact B470607
  · exact B470611
  · exact B470615
  · exact B470619
  · exact B470623
  · exact B470627
  · exact B470631
  · exact B470635
  · exact B470639
  · exact B470643
  · exact B470647
  · exact B470651
  · exact B470655
  · exact B470659
  · exact B470663
  · exact B470667
  · exact B470671
  · exact B470675
  · exact B470679
  · exact B470683
  · exact B470687
  · exact B470691
  · exact B470695
  · exact B470699
  · exact B470703
  · exact B470707
  · exact B470711
  · exact B470715
  · exact B470719
  · exact B470723
  · exact B470727
  · exact B470731
  · exact B470735
  · exact B470739
  · exact B470743
  · exact B470747
  · exact B470751
  · exact B470755
  · exact B470759
  · exact B470763
  · exact B470767
  · exact B470771
  · exact B470775
  · exact B470779
  · exact B470783
  · exact B470787
  · exact B470791
  · exact B470795
  · exact B470799
  · exact B470803
  · exact B470807
  · exact B470811
  · exact B470815
  · exact B470819
  · exact B470823
  · exact B470827
  · exact B470831
  · exact B470835
  · exact B470839
  · exact B470843
  · exact B470847
  · exact B470851
  · exact B470855
  · exact B470859
  · exact B470863
  · exact B470867
  · exact B470871
  · exact B470875
  · exact B470879
  · exact B470883
  · exact B470887
  · exact B470891
  · exact B470895
  · exact B470899
  · exact B470903
  · exact B470907
  · exact B470911
  · exact B470915
  · exact B470919
  · exact B470923
  · exact B470927
  · exact B470931
  · exact B470935
  · exact B470939
  · exact B470943
  · exact B470947
  · exact B470951
  · exact B470955
  · exact B470959
  · exact B470963
  · exact B470967
  · exact B470971
  · exact B470975
  · exact B470979
  · exact B470983
  · exact B470987
  · exact B470991
  · exact B470995
  · exact B470999
  · exact B471003
  · exact B471007
  · exact B471011
  · exact B471015
  · exact B471019
  · exact B471023
  · exact B471027
  · exact B471031
  · exact B471035
  · exact B471039
  · exact B471043
  · exact B471047
  · exact B471051
  · exact B471055
  · exact B471059
  · exact B471063
  · exact B471067
  · exact B471071
  · exact B471075
  · exact B471079
  · exact B471083
  · exact B471087
  · exact B471091
  · exact B471095
  · exact B471099
  · exact B471103
  · exact B471107
  · exact B471111
  · exact B471115
  · exact B471119
  · exact B471123
  · exact B471127
  · exact B471131
  · exact B471135
  · exact B471139
  · exact B471143
  · exact B471147
  · exact B471151
  · exact B471155
  · exact B471159
  · exact B471163
  · exact B471167
  · exact B471171
  · exact B471175
  · exact B471179
  · exact B471183
  · exact B471187
  · exact B471191
  · exact B471195
  · exact B471199
  · exact B471203
  · exact B471207
  · exact B471211
  · exact B471215
  · exact B471219
  · exact B471223
  · exact B471227
  · exact B471231
  · exact B471235
  · exact B471239
  · exact B471243
  · exact B471247
  · exact B471251
  · exact B471255
  · exact B471259
  · exact B471263
  · exact B471267
  · exact B471271
  · exact B471275
  · exact B471279
  · exact B471283
  · exact B471287
  · exact B471291
  · exact B471295
  · exact B471299
  · exact B471303
  · exact B471307
  · exact B471311
  · exact B471315
  · exact B471319
  · exact B471323
  · exact B471327
  · exact B471331
  · exact B471335
  · exact B471339
  · exact B471343
  · exact B471347
  · exact B471351
  · exact B471355
  · exact B471359
  · exact B471363
  · exact B471367
  · exact B471371
  · exact B471375
  · exact B471379
  · exact B471383
  · exact B471387
  · exact B471391
  · exact B471395
  · exact B471399
  · exact B471403
  · exact B471407
  · exact B471411
  · exact B471415
  · exact B471419
  · exact B471423
  · exact B471427
  · exact B471431
  · exact B471435
  · exact B471439
  · exact B471443
  · exact B471447
  · exact B471451
  · exact B471455
  · exact B471459
  · exact B471463
  · exact B471467
  · exact B471471
  · exact B471475
  · exact B471479
  · exact B471483
  · exact B471487
  · exact B471491
  · exact B471495
  · exact B471499
  · exact B471503
  · exact B471507
  · exact B471511
  · exact B471515
  · exact B471519
  · exact B471523
  · exact B471527
  · exact B471531
  · exact B471535
  · exact B471539
  · exact B471543
  · exact B471547
  · exact B471551
  · exact B471555
  · exact B471559
  · exact B471563
  · exact B471567
  · exact B471571
  · exact B471575
  · exact B471579
  · exact B471583
  · exact B471587
  · exact B471591
  · exact B471595
  · exact B471599
  · exact B471603
  · exact B471607
  · exact B471611
  · exact B471615
  · exact B471619
  · exact B471623
  · exact B471627
  · exact B471631
  · exact B471635
  · exact B471639
  · exact B471643
  · exact B471647
  · exact B471651
  · exact B471655
  · exact B471659
  · exact B471663
  · exact B471667
  · exact B471671
  · exact B471675
  · exact B471679
  · exact B471683
  · exact B471687
  · exact B471691
  · exact B471695
  · exact B471699
  · exact B471703
  · exact B471707
  · exact B471711
  · exact B471715
  · exact B471719
  · exact B471723
  · exact B471727
  · exact B471731
  · exact B471735
  · exact B471739
  · exact B471743
  · exact B471747
  · exact B471751
  · exact B471755
  · exact B471759
  · exact B471763
  · exact B471767
  · exact B471771
  · exact B471775
  · exact B471779
  · exact B471783

theorem solution (m : ℕ) (hlo : 467785 ≤ m) (hhi : m ≤ 471785) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 116946 ≤ j := by omega
    have hj2 : j ≤ 117945 := by omega
    have hb : Blo 467785 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 117646 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
