-- Prove2me | solution 1 for syracuse_descends_range_179801_183801
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:46.761523+00:00
-- url     : https://prove2.me/submissions/d4cc2c91-5b45-4cc7-bdc5-0eccdbd1c8e6

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


theorem B229493 : Blo 179801 229493 := bbase (se 5 (by rfl) ⟨10757, by rfl⟩ : syracuseStep 229493 = 21515) (by norm_num)
theorem B458885 : Blo 179801 458885 := bbase (se 4 (by rfl) ⟨43020, by rfl⟩ : syracuseStep 458885 = 86041) (by norm_num)
theorem B229549 : Blo 179801 229549 := bbase (se 3 (by rfl) ⟨43040, by rfl⟩ : syracuseStep 229549 = 86081) (by norm_num)
theorem B295093 : Blo 179801 295093 := bbase (se 5 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 295093 = 27665) (by norm_num)
theorem B229645 : Blo 179801 229645 := bbase (se 3 (by rfl) ⟨43058, by rfl⟩ : syracuseStep 229645 = 86117) (by norm_num)
theorem B491957 : Blo 179801 491957 := bbase (se 5 (by rfl) ⟨23060, by rfl⟩ : syracuseStep 491957 = 46121) (by norm_num)
theorem B229817 : Blo 179801 229817 := bbase (se 2 (by rfl) ⟨86181, by rfl⟩ : syracuseStep 229817 = 172363) (by norm_num)
theorem B459229 : Blo 179801 459229 := bbase (se 3 (by rfl) ⟨86105, by rfl⟩ : syracuseStep 459229 = 172211) (by norm_num)
theorem B229873 : Blo 179801 229873 := bbase (se 2 (by rfl) ⟨86202, by rfl⟩ : syracuseStep 229873 = 172405) (by norm_num)
theorem B918053 : Blo 179801 918053 := bbase (se 4 (by rfl) ⟨86067, by rfl⟩ : syracuseStep 918053 = 172135) (by norm_num)
theorem B459341 : Blo 179801 459341 := bbase (se 3 (by rfl) ⟨86126, by rfl⟩ : syracuseStep 459341 = 172253) (by norm_num)
theorem B229969 : Blo 179801 229969 := bbase (se 2 (by rfl) ⟨86238, by rfl⟩ : syracuseStep 229969 = 172477) (by norm_num)
theorem B230141 : Blo 179801 230141 := bbase (se 3 (by rfl) ⟨43151, by rfl⟩ : syracuseStep 230141 = 86303) (by norm_num)
theorem B459533 : Blo 179801 459533 := bbase (se 3 (by rfl) ⟨86162, by rfl⟩ : syracuseStep 459533 = 172325) (by norm_num)
theorem B230197 : Blo 179801 230197 := bbase (se 5 (by rfl) ⟨10790, by rfl⟩ : syracuseStep 230197 = 21581) (by norm_num)
theorem B656261 : Blo 179801 656261 := bbase (se 4 (by rfl) ⟨61524, by rfl⟩ : syracuseStep 656261 = 123049) (by norm_num)
theorem B230293 : Blo 179801 230293 := bbase (se 6 (by rfl) ⟨5397, by rfl⟩ : syracuseStep 230293 = 10795) (by norm_num)
theorem B295949 : Blo 179801 295949 := bbase (se 3 (by rfl) ⟨55490, by rfl⟩ : syracuseStep 295949 = 110981) (by norm_num)
theorem B230465 : Blo 179801 230465 := bbase (se 2 (by rfl) ⟨86424, by rfl⟩ : syracuseStep 230465 = 172849) (by norm_num)
theorem B459877 : Blo 179801 459877 := bbase (se 4 (by rfl) ⟨43113, by rfl⟩ : syracuseStep 459877 = 86227) (by norm_num)
theorem B689269 : Blo 179801 689269 := bbase (se 5 (by rfl) ⟨32309, by rfl⟩ : syracuseStep 689269 = 64619) (by norm_num)
theorem B230521 : Blo 179801 230521 := bbase (se 2 (by rfl) ⟨86445, by rfl⟩ : syracuseStep 230521 = 172891) (by norm_num)
theorem B459989 : Blo 179801 459989 := bbase (se 7 (by rfl) ⟨5390, by rfl⟩ : syracuseStep 459989 = 10781) (by norm_num)
theorem B230617 : Blo 179801 230617 := bbase (se 2 (by rfl) ⟨86481, by rfl⟩ : syracuseStep 230617 = 172963) (by norm_num)
theorem B820469 : Blo 179801 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B591157 : Blo 179801 591157 := bbase (se 5 (by rfl) ⟨27710, by rfl⟩ : syracuseStep 591157 = 55421) (by norm_num)
theorem B755077 : Blo 179801 755077 := bbase (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) (by norm_num)
theorem B230789 : Blo 179801 230789 := bbase (se 4 (by rfl) ⟨21636, by rfl⟩ : syracuseStep 230789 = 43273) (by norm_num)
theorem B460181 : Blo 179801 460181 := bbase (se 6 (by rfl) ⟨10785, by rfl⟩ : syracuseStep 460181 = 21571) (by norm_num)
theorem B689573 : Blo 179801 689573 := bbase (se 4 (by rfl) ⟨64647, by rfl⟩ : syracuseStep 689573 = 129295) (by norm_num)
theorem B230845 : Blo 179801 230845 := bbase (se 3 (by rfl) ⟨43283, by rfl⟩ : syracuseStep 230845 = 86567) (by norm_num)
theorem B230941 : Blo 179801 230941 := bbase (se 3 (by rfl) ⟨43301, by rfl⟩ : syracuseStep 230941 = 86603) (by norm_num)
theorem B362053 : Blo 179801 362053 := bbase (se 4 (by rfl) ⟨33942, by rfl⟩ : syracuseStep 362053 = 67885) (by norm_num)
theorem B886373 : Blo 179801 886373 := bbase (se 4 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 886373 = 166195) (by norm_num)
theorem B329341 : Blo 179801 329341 := bbase (se 3 (by rfl) ⟨61751, by rfl⟩ : syracuseStep 329341 = 123503) (by norm_num)
theorem B231113 : Blo 179801 231113 := bbase (se 2 (by rfl) ⟨86667, by rfl⟩ : syracuseStep 231113 = 173335) (by norm_num)
theorem B460525 : Blo 179801 460525 := bbase (se 3 (by rfl) ⟨86348, by rfl⟩ : syracuseStep 460525 = 172697) (by norm_num)
theorem B231169 : Blo 179801 231169 := bbase (se 2 (by rfl) ⟨86688, by rfl⟩ : syracuseStep 231169 = 173377) (by norm_num)
theorem B919349 : Blo 179801 919349 := bbase (se 5 (by rfl) ⟨43094, by rfl⟩ : syracuseStep 919349 = 86189) (by norm_num)
theorem B460637 : Blo 179801 460637 := bbase (se 3 (by rfl) ⟨86369, by rfl⟩ : syracuseStep 460637 = 172739) (by norm_num)
theorem B231265 : Blo 179801 231265 := bbase (se 2 (by rfl) ⟨86724, by rfl⟩ : syracuseStep 231265 = 173449) (by norm_num)
theorem B198509 : Blo 179801 198509 := bbase (se 3 (by rfl) ⟨37220, by rfl⟩ : syracuseStep 198509 = 74441) (by norm_num)
theorem B198577 : Blo 179801 198577 := bbase (se 2 (by rfl) ⟨74466, by rfl⟩ : syracuseStep 198577 = 148933) (by norm_num)
theorem B231437 : Blo 179801 231437 := bbase (se 3 (by rfl) ⟨43394, by rfl⟩ : syracuseStep 231437 = 86789) (by norm_num)
theorem B460829 : Blo 179801 460829 := bbase (se 3 (by rfl) ⟨86405, by rfl⟩ : syracuseStep 460829 = 172811) (by norm_num)
theorem B231493 : Blo 179801 231493 := bbase (se 4 (by rfl) ⟨21702, by rfl⟩ : syracuseStep 231493 = 43405) (by norm_num)
theorem B821381 : Blo 179801 821381 := bbase (se 4 (by rfl) ⟨77004, by rfl⟩ : syracuseStep 821381 = 154009) (by norm_num)
theorem B231589 : Blo 179801 231589 := bbase (se 4 (by rfl) ⟨21711, by rfl⟩ : syracuseStep 231589 = 43423) (by norm_num)
theorem B231761 : Blo 179801 231761 := bbase (se 2 (by rfl) ⟨86910, by rfl⟩ : syracuseStep 231761 = 173821) (by norm_num)
theorem B3705173 : Blo 179801 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B461173 : Blo 179801 461173 := bbase (se 5 (by rfl) ⟨21617, by rfl⟩ : syracuseStep 461173 = 43235) (by norm_num)
theorem B231817 : Blo 179801 231817 := bbase (se 2 (by rfl) ⟨86931, by rfl⟩ : syracuseStep 231817 = 173863) (by norm_num)
theorem B330149 : Blo 179801 330149 := bbase (se 4 (by rfl) ⟨30951, by rfl⟩ : syracuseStep 330149 = 61903) (by norm_num)
theorem B231865 : Blo 179801 231865 := bbase (se 2 (by rfl) ⟨86949, by rfl⟩ : syracuseStep 231865 = 173899) (by norm_num)
theorem B461285 : Blo 179801 461285 := bbase (se 4 (by rfl) ⟨43245, by rfl⟩ : syracuseStep 461285 = 86491) (by norm_num)
theorem B231913 : Blo 179801 231913 := bbase (se 2 (by rfl) ⟨86967, by rfl⟩ : syracuseStep 231913 = 173935) (by norm_num)
theorem B625205 : Blo 179801 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B232085 : Blo 179801 232085 := bbase (se 6 (by rfl) ⟨5439, by rfl⟩ : syracuseStep 232085 = 10879) (by norm_num)
theorem B461477 : Blo 179801 461477 := bbase (se 4 (by rfl) ⟨43263, by rfl⟩ : syracuseStep 461477 = 86527) (by norm_num)
theorem B232141 : Blo 179801 232141 := bbase (se 3 (by rfl) ⟨43526, by rfl⟩ : syracuseStep 232141 = 87053) (by norm_num)
theorem B232237 : Blo 179801 232237 := bbase (se 3 (by rfl) ⟨43544, by rfl⟩ : syracuseStep 232237 = 87089) (by norm_num)
theorem B232409 : Blo 179801 232409 := bbase (se 2 (by rfl) ⟨87153, by rfl⟩ : syracuseStep 232409 = 174307) (by norm_num)
theorem B330725 : Blo 179801 330725 := bbase (se 4 (by rfl) ⟨31005, by rfl⟩ : syracuseStep 330725 = 62011) (by norm_num)
theorem B658421 : Blo 179801 658421 := bbase (se 5 (by rfl) ⟨30863, by rfl⟩ : syracuseStep 658421 = 61727) (by norm_num)
theorem B461821 : Blo 179801 461821 := bbase (se 3 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 461821 = 173183) (by norm_num)
theorem B232465 : Blo 179801 232465 := bbase (se 2 (by rfl) ⟨87174, by rfl⟩ : syracuseStep 232465 = 174349) (by norm_num)
theorem B920645 : Blo 179801 920645 := bbase (se 4 (by rfl) ⟨86310, by rfl⟩ : syracuseStep 920645 = 172621) (by norm_num)
theorem B461933 : Blo 179801 461933 := bbase (se 3 (by rfl) ⟨86612, by rfl⟩ : syracuseStep 461933 = 173225) (by norm_num)
theorem B232561 : Blo 179801 232561 := bbase (se 2 (by rfl) ⟨87210, by rfl⟩ : syracuseStep 232561 = 174421) (by norm_num)
theorem B658709 : Blo 179801 658709 := bbase (se 6 (by rfl) ⟨15438, by rfl⟩ : syracuseStep 658709 = 30877) (by norm_num)
theorem B462125 : Blo 179801 462125 := bbase (se 3 (by rfl) ⟨86648, by rfl⟩ : syracuseStep 462125 = 173297) (by norm_num)
theorem B396677 : Blo 179801 396677 := bbase (se 4 (by rfl) ⟨37188, by rfl⟩ : syracuseStep 396677 = 74377) (by norm_num)
theorem B3083669 : Blo 179801 3083669 := bbase (se 6 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 3083669 = 144547) (by norm_num)
theorem B691685 : Blo 179801 691685 := bbase (se 4 (by rfl) ⟨64845, by rfl⟩ : syracuseStep 691685 = 129691) (by norm_num)
theorem B462469 : Blo 179801 462469 := bbase (se 4 (by rfl) ⟨43356, by rfl⟩ : syracuseStep 462469 = 86713) (by norm_num)
theorem B462581 : Blo 179801 462581 := bbase (se 5 (by rfl) ⟨21683, by rfl⟩ : syracuseStep 462581 = 43367) (by norm_num)
theorem B691973 : Blo 179801 691973 := bbase (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) (by norm_num)
theorem B560981 : Blo 179801 560981 := bbase (se 9 (by rfl) ⟨1643, by rfl⟩ : syracuseStep 560981 = 3287) (by norm_num)
theorem B462773 : Blo 179801 462773 := bbase (se 5 (by rfl) ⟨21692, by rfl⟩ : syracuseStep 462773 = 43385) (by norm_num)
theorem B2625493 : Blo 179801 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B987157 : Blo 179801 987157 := bbase (se 6 (by rfl) ⟨23136, by rfl⟩ : syracuseStep 987157 = 46273) (by norm_num)
theorem B463117 : Blo 179801 463117 := bbase (se 3 (by rfl) ⟨86834, by rfl⟩ : syracuseStep 463117 = 173669) (by norm_num)
theorem B921941 : Blo 179801 921941 := bbase (se 10 (by rfl) ⟨1350, by rfl⟩ : syracuseStep 921941 = 2701) (by norm_num)
theorem B1380725 : Blo 179801 1380725 := bbase (se 5 (by rfl) ⟨64721, by rfl⟩ : syracuseStep 1380725 = 129443) (by norm_num)
theorem B463229 : Blo 179801 463229 := bbase (se 3 (by rfl) ⟨86855, by rfl⟩ : syracuseStep 463229 = 173711) (by norm_num)
theorem B234041 : Blo 179801 234041 := bbase (se 2 (by rfl) ⟨87765, by rfl⟩ : syracuseStep 234041 = 175531) (by norm_num)
theorem B463421 : Blo 179801 463421 := bbase (se 3 (by rfl) ⟨86891, by rfl⟩ : syracuseStep 463421 = 173783) (by norm_num)
theorem B365237 : Blo 179801 365237 := bbase (se 5 (by rfl) ⟨17120, by rfl⟩ : syracuseStep 365237 = 34241) (by norm_num)
theorem B2954069 : Blo 179801 2954069 := bbase (se 9 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 2954069 = 17309) (by norm_num)
theorem B463765 : Blo 179801 463765 := bbase (se 6 (by rfl) ⟨10869, by rfl⟩ : syracuseStep 463765 = 21739) (by norm_num)
theorem B693157 : Blo 179801 693157 := bbase (se 4 (by rfl) ⟨64983, by rfl⟩ : syracuseStep 693157 = 129967) (by norm_num)
theorem B463877 : Blo 179801 463877 := bbase (se 4 (by rfl) ⟨43488, by rfl⟩ : syracuseStep 463877 = 86977) (by norm_num)
theorem B464069 : Blo 179801 464069 := bbase (se 4 (by rfl) ⟨43506, by rfl⟩ : syracuseStep 464069 = 87013) (by norm_num)
theorem B693461 : Blo 179801 693461 := bbase (se 7 (by rfl) ⟨8126, by rfl⟩ : syracuseStep 693461 = 16253) (by norm_num)
theorem B627941 : Blo 179801 627941 := bbase (se 4 (by rfl) ⟨58869, by rfl⟩ : syracuseStep 627941 = 117739) (by norm_num)
theorem B988469 : Blo 179801 988469 := bbase (se 5 (by rfl) ⟨46334, by rfl⟩ : syracuseStep 988469 = 92669) (by norm_num)
theorem B693749 : Blo 179801 693749 := bbase (se 5 (by rfl) ⟨32519, by rfl⟩ : syracuseStep 693749 = 65039) (by norm_num)
theorem B235009 : Blo 179801 235009 := bbase (se 2 (by rfl) ⟨88128, by rfl⟩ : syracuseStep 235009 = 176257) (by norm_num)
theorem B464413 : Blo 179801 464413 := bbase (se 3 (by rfl) ⟨87077, by rfl⟩ : syracuseStep 464413 = 174155) (by norm_num)
theorem B202297 : Blo 179801 202297 := bbase (se 2 (by rfl) ⟨75861, by rfl⟩ : syracuseStep 202297 = 151723) (by norm_num)
theorem B988757 : Blo 179801 988757 := bbase (se 8 (by rfl) ⟨5793, by rfl⟩ : syracuseStep 988757 = 11587) (by norm_num)
theorem B202333 : Blo 179801 202333 := bbase (se 3 (by rfl) ⟨37937, by rfl⟩ : syracuseStep 202333 = 75875) (by norm_num)
theorem B923237 : Blo 179801 923237 := bbase (se 4 (by rfl) ⟨86553, by rfl⟩ : syracuseStep 923237 = 173107) (by norm_num)
theorem B202369 : Blo 179801 202369 := bbase (se 2 (by rfl) ⟨75888, by rfl⟩ : syracuseStep 202369 = 151777) (by norm_num)
theorem B464525 : Blo 179801 464525 := bbase (se 3 (by rfl) ⟨87098, by rfl⟩ : syracuseStep 464525 = 174197) (by norm_num)
theorem B202405 : Blo 179801 202405 := bbase (se 4 (by rfl) ⟨18975, by rfl⟩ : syracuseStep 202405 = 37951) (by norm_num)
theorem B202441 : Blo 179801 202441 := bbase (se 2 (by rfl) ⟨75915, by rfl⟩ : syracuseStep 202441 = 151831) (by norm_num)
theorem B202477 : Blo 179801 202477 := bbase (se 3 (by rfl) ⟨37964, by rfl⟩ : syracuseStep 202477 = 75929) (by norm_num)
theorem B202513 : Blo 179801 202513 := bbase (se 2 (by rfl) ⟨75942, by rfl⟩ : syracuseStep 202513 = 151885) (by norm_num)
theorem B202549 : Blo 179801 202549 := bbase (se 5 (by rfl) ⟨9494, by rfl⟩ : syracuseStep 202549 = 18989) (by norm_num)
theorem B464717 : Blo 179801 464717 := bbase (se 3 (by rfl) ⟨87134, by rfl⟩ : syracuseStep 464717 = 174269) (by norm_num)
theorem B202585 : Blo 179801 202585 := bbase (se 2 (by rfl) ⟨75969, by rfl⟩ : syracuseStep 202585 = 151939) (by norm_num)
theorem B202621 : Blo 179801 202621 := bbase (se 3 (by rfl) ⟨37991, by rfl⟩ : syracuseStep 202621 = 75983) (by norm_num)
theorem B202657 : Blo 179801 202657 := bbase (se 2 (by rfl) ⟨75996, by rfl⟩ : syracuseStep 202657 = 151993) (by norm_num)
theorem B202693 : Blo 179801 202693 := bbase (se 4 (by rfl) ⟨19002, by rfl⟩ : syracuseStep 202693 = 38005) (by norm_num)
theorem B202729 : Blo 179801 202729 := bbase (se 2 (by rfl) ⟨76023, by rfl⟩ : syracuseStep 202729 = 152047) (by norm_num)
theorem B202765 : Blo 179801 202765 := bbase (se 3 (by rfl) ⟨38018, by rfl⟩ : syracuseStep 202765 = 76037) (by norm_num)
theorem B202801 : Blo 179801 202801 := bbase (se 2 (by rfl) ⟨76050, by rfl⟩ : syracuseStep 202801 = 152101) (by norm_num)
theorem B202837 : Blo 179801 202837 := bbase (se 8 (by rfl) ⟨1188, by rfl⟩ : syracuseStep 202837 = 2377) (by norm_num)
theorem B727157 : Blo 179801 727157 := bbase (se 5 (by rfl) ⟨34085, by rfl⟩ : syracuseStep 727157 = 68171) (by norm_num)
theorem B202873 : Blo 179801 202873 := bbase (se 2 (by rfl) ⟨76077, by rfl⟩ : syracuseStep 202873 = 152155) (by norm_num)
theorem B202909 : Blo 179801 202909 := bbase (se 3 (by rfl) ⟨38045, by rfl⟩ : syracuseStep 202909 = 76091) (by norm_num)
theorem B465061 : Blo 179801 465061 := bbase (se 4 (by rfl) ⟨43599, by rfl⟩ : syracuseStep 465061 = 87199) (by norm_num)
theorem B202945 : Blo 179801 202945 := bbase (se 2 (by rfl) ⟨76104, by rfl⟩ : syracuseStep 202945 = 152209) (by norm_num)
theorem B202981 : Blo 179801 202981 := bbase (se 4 (by rfl) ⟨19029, by rfl⟩ : syracuseStep 202981 = 38059) (by norm_num)
theorem B432373 : Blo 179801 432373 := bbase (se 5 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 432373 = 40535) (by norm_num)
theorem B661765 : Blo 179801 661765 := bbase (se 4 (by rfl) ⟨62040, by rfl⟩ : syracuseStep 661765 = 124081) (by norm_num)
theorem B203017 : Blo 179801 203017 := bbase (se 2 (by rfl) ⟨76131, by rfl⟩ : syracuseStep 203017 = 152263) (by norm_num)
theorem B465173 : Blo 179801 465173 := bbase (se 6 (by rfl) ⟨10902, by rfl⟩ : syracuseStep 465173 = 21805) (by norm_num)
theorem B203053 : Blo 179801 203053 := bbase (se 3 (by rfl) ⟨38072, by rfl⟩ : syracuseStep 203053 = 76145) (by norm_num)
theorem B203089 : Blo 179801 203089 := bbase (se 2 (by rfl) ⟨76158, by rfl⟩ : syracuseStep 203089 = 152317) (by norm_num)
theorem B203125 : Blo 179801 203125 := bbase (se 5 (by rfl) ⟨9521, by rfl⟩ : syracuseStep 203125 = 19043) (by norm_num)
theorem B203161 : Blo 179801 203161 := bbase (se 2 (by rfl) ⟨76185, by rfl⟩ : syracuseStep 203161 = 152371) (by norm_num)
theorem B203197 : Blo 179801 203197 := bbase (se 3 (by rfl) ⟨38099, by rfl⟩ : syracuseStep 203197 = 76199) (by norm_num)
theorem B203233 : Blo 179801 203233 := bbase (se 2 (by rfl) ⟨76212, by rfl⟩ : syracuseStep 203233 = 152425) (by norm_num)
theorem B203269 : Blo 179801 203269 := bbase (se 4 (by rfl) ⟨19056, by rfl⟩ : syracuseStep 203269 = 38113) (by norm_num)
theorem B203305 : Blo 179801 203305 := bbase (se 2 (by rfl) ⟨76239, by rfl⟩ : syracuseStep 203305 = 152479) (by norm_num)
theorem B203341 : Blo 179801 203341 := bbase (se 3 (by rfl) ⟨38126, by rfl⟩ : syracuseStep 203341 = 76253) (by norm_num)
theorem B203377 : Blo 179801 203377 := bbase (se 2 (by rfl) ⟨76266, by rfl⟩ : syracuseStep 203377 = 152533) (by norm_num)
theorem B203413 : Blo 179801 203413 := bbase (se 6 (by rfl) ⟨4767, by rfl⟩ : syracuseStep 203413 = 9535) (by norm_num)
theorem B203449 : Blo 179801 203449 := bbase (se 2 (by rfl) ⟨76293, by rfl⟩ : syracuseStep 203449 = 152587) (by norm_num)
theorem B203485 : Blo 179801 203485 := bbase (se 3 (by rfl) ⟨38153, by rfl⟩ : syracuseStep 203485 = 76307) (by norm_num)
theorem B203521 : Blo 179801 203521 := bbase (se 2 (by rfl) ⟨76320, by rfl⟩ : syracuseStep 203521 = 152641) (by norm_num)
theorem B203557 : Blo 179801 203557 := bbase (se 4 (by rfl) ⟨19083, by rfl⟩ : syracuseStep 203557 = 38167) (by norm_num)
theorem B203593 : Blo 179801 203593 := bbase (se 2 (by rfl) ⟨76347, by rfl⟩ : syracuseStep 203593 = 152695) (by norm_num)
theorem B432989 : Blo 179801 432989 := bbase (se 3 (by rfl) ⟨81185, by rfl⟩ : syracuseStep 432989 = 162371) (by norm_num)
theorem B891749 : Blo 179801 891749 := bbase (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) (by norm_num)
theorem B203629 : Blo 179801 203629 := bbase (se 3 (by rfl) ⟨38180, by rfl⟩ : syracuseStep 203629 = 76361) (by norm_num)
theorem B924533 : Blo 179801 924533 := bbase (se 5 (by rfl) ⟨43337, by rfl⟩ : syracuseStep 924533 = 86675) (by norm_num)
theorem B203665 : Blo 179801 203665 := bbase (se 2 (by rfl) ⟨76374, by rfl⟩ : syracuseStep 203665 = 152749) (by norm_num)
theorem B203701 : Blo 179801 203701 := bbase (se 5 (by rfl) ⟨9548, by rfl⟩ : syracuseStep 203701 = 19097) (by norm_num)
theorem B203737 : Blo 179801 203737 := bbase (se 2 (by rfl) ⟨76401, by rfl⟩ : syracuseStep 203737 = 152803) (by norm_num)
theorem B203773 : Blo 179801 203773 := bbase (se 3 (by rfl) ⟨38207, by rfl⟩ : syracuseStep 203773 = 76415) (by norm_num)
theorem B433181 : Blo 179801 433181 := bbase (se 3 (by rfl) ⟨81221, by rfl⟩ : syracuseStep 433181 = 162443) (by norm_num)
theorem B203809 : Blo 179801 203809 := bbase (se 2 (by rfl) ⟨76428, by rfl⟩ : syracuseStep 203809 = 152857) (by norm_num)
theorem B203845 : Blo 179801 203845 := bbase (se 4 (by rfl) ⟨19110, by rfl⟩ : syracuseStep 203845 = 38221) (by norm_num)
theorem B826453 : Blo 179801 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B203881 : Blo 179801 203881 := bbase (se 2 (by rfl) ⟨76455, by rfl⟩ : syracuseStep 203881 = 152911) (by norm_num)
theorem B433277 : Blo 179801 433277 := bbase (se 3 (by rfl) ⟨81239, by rfl⟩ : syracuseStep 433277 = 162479) (by norm_num)
theorem B203917 : Blo 179801 203917 := bbase (se 3 (by rfl) ⟨38234, by rfl⟩ : syracuseStep 203917 = 76469) (by norm_num)
theorem B924821 : Blo 179801 924821 := bbase (se 6 (by rfl) ⟨21675, by rfl⟩ : syracuseStep 924821 = 43351) (by norm_num)
theorem B203953 : Blo 179801 203953 := bbase (se 2 (by rfl) ⟨76482, by rfl⟩ : syracuseStep 203953 = 152965) (by norm_num)
theorem B203989 : Blo 179801 203989 := bbase (se 7 (by rfl) ⟨2390, by rfl⟩ : syracuseStep 203989 = 4781) (by norm_num)
theorem B204025 : Blo 179801 204025 := bbase (se 2 (by rfl) ⟨76509, by rfl⟩ : syracuseStep 204025 = 153019) (by norm_num)
theorem B695573 : Blo 179801 695573 := bbase (se 6 (by rfl) ⟨16302, by rfl⟩ : syracuseStep 695573 = 32605) (by norm_num)
theorem B204061 : Blo 179801 204061 := bbase (se 3 (by rfl) ⟨38261, by rfl⟩ : syracuseStep 204061 = 76523) (by norm_num)
theorem B204097 : Blo 179801 204097 := bbase (se 2 (by rfl) ⟨76536, by rfl⟩ : syracuseStep 204097 = 153073) (by norm_num)
theorem B204133 : Blo 179801 204133 := bbase (se 4 (by rfl) ⟨19137, by rfl⟩ : syracuseStep 204133 = 38275) (by norm_num)
theorem B204169 : Blo 179801 204169 := bbase (se 2 (by rfl) ⟨76563, by rfl⟩ : syracuseStep 204169 = 153127) (by norm_num)
theorem B269717 : Blo 179801 269717 := bbase (se 6 (by rfl) ⟨6321, by rfl⟩ : syracuseStep 269717 = 12643) (by norm_num)
theorem B269741 : Blo 179801 269741 := bbase (se 3 (by rfl) ⟨50576, by rfl⟩ : syracuseStep 269741 = 101153) (by norm_num)
theorem B204205 : Blo 179801 204205 := bbase (se 3 (by rfl) ⟨38288, by rfl⟩ : syracuseStep 204205 = 76577) (by norm_num)
theorem B269765 : Blo 179801 269765 := bbase (se 4 (by rfl) ⟨25290, by rfl⟩ : syracuseStep 269765 = 50581) (by norm_num)
theorem B204241 : Blo 179801 204241 := bbase (se 2 (by rfl) ⟨76590, by rfl⟩ : syracuseStep 204241 = 153181) (by norm_num)
theorem B990677 : Blo 179801 990677 := bbase (se 7 (by rfl) ⟨11609, by rfl⟩ : syracuseStep 990677 = 23219) (by norm_num)
theorem B269789 : Blo 179801 269789 := bbase (se 3 (by rfl) ⟨50585, by rfl⟩ : syracuseStep 269789 = 101171) (by norm_num)
theorem B269813 : Blo 179801 269813 := bbase (se 5 (by rfl) ⟨12647, by rfl⟩ : syracuseStep 269813 = 25295) (by norm_num)
theorem B204277 : Blo 179801 204277 := bbase (se 5 (by rfl) ⟨9575, by rfl⟩ : syracuseStep 204277 = 19151) (by norm_num)
theorem B269837 : Blo 179801 269837 := bbase (se 3 (by rfl) ⟨50594, by rfl⟩ : syracuseStep 269837 = 101189) (by norm_num)
theorem B204313 : Blo 179801 204313 := bbase (se 2 (by rfl) ⟨76617, by rfl⟩ : syracuseStep 204313 = 153235) (by norm_num)
theorem B269861 : Blo 179801 269861 := bbase (se 4 (by rfl) ⟨25299, by rfl⟩ : syracuseStep 269861 = 50599) (by norm_num)
theorem B695861 : Blo 179801 695861 := bbase (se 5 (by rfl) ⟨32618, by rfl⟩ : syracuseStep 695861 = 65237) (by norm_num)
theorem B269885 : Blo 179801 269885 := bbase (se 3 (by rfl) ⟨50603, by rfl⟩ : syracuseStep 269885 = 101207) (by norm_num)
theorem B204349 : Blo 179801 204349 := bbase (se 3 (by rfl) ⟨38315, by rfl⟩ : syracuseStep 204349 = 76631) (by norm_num)
theorem B269909 : Blo 179801 269909 := bbase (se 8 (by rfl) ⟨1581, by rfl⟩ : syracuseStep 269909 = 3163) (by norm_num)
theorem B368221 : Blo 179801 368221 := bbase (se 3 (by rfl) ⟨69041, by rfl⟩ : syracuseStep 368221 = 138083) (by norm_num)
theorem B204385 : Blo 179801 204385 := bbase (se 2 (by rfl) ⟨76644, by rfl⟩ : syracuseStep 204385 = 153289) (by norm_num)
theorem B269933 : Blo 179801 269933 := bbase (se 3 (by rfl) ⟨50612, by rfl⟩ : syracuseStep 269933 = 101225) (by norm_num)
theorem B269957 : Blo 179801 269957 := bbase (se 4 (by rfl) ⟨25308, by rfl⟩ : syracuseStep 269957 = 50617) (by norm_num)
theorem B204421 : Blo 179801 204421 := bbase (se 4 (by rfl) ⟨19164, by rfl⟩ : syracuseStep 204421 = 38329) (by norm_num)
theorem B269981 : Blo 179801 269981 := bbase (se 3 (by rfl) ⟨50621, by rfl⟩ : syracuseStep 269981 = 101243) (by norm_num)
theorem B204457 : Blo 179801 204457 := bbase (se 2 (by rfl) ⟨76671, by rfl⟩ : syracuseStep 204457 = 153343) (by norm_num)
theorem B270005 : Blo 179801 270005 := bbase (se 5 (by rfl) ⟨12656, by rfl⟩ : syracuseStep 270005 = 25313) (by norm_num)
theorem B270029 : Blo 179801 270029 := bbase (se 3 (by rfl) ⟨50630, by rfl⟩ : syracuseStep 270029 = 101261) (by norm_num)
theorem B204493 : Blo 179801 204493 := bbase (se 3 (by rfl) ⟨38342, by rfl⟩ : syracuseStep 204493 = 76685) (by norm_num)
theorem B2989781 : Blo 179801 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B270053 : Blo 179801 270053 := bbase (se 4 (by rfl) ⟨25317, by rfl⟩ : syracuseStep 270053 = 50635) (by norm_num)
theorem B204529 : Blo 179801 204529 := bbase (se 2 (by rfl) ⟨76698, by rfl⟩ : syracuseStep 204529 = 153397) (by norm_num)
theorem B270077 : Blo 179801 270077 := bbase (se 3 (by rfl) ⟨50639, by rfl⟩ : syracuseStep 270077 = 101279) (by norm_num)
theorem B270101 : Blo 179801 270101 := bbase (se 6 (by rfl) ⟨6330, by rfl⟩ : syracuseStep 270101 = 12661) (by norm_num)
theorem B204565 : Blo 179801 204565 := bbase (se 6 (by rfl) ⟨4794, by rfl⟩ : syracuseStep 204565 = 9589) (by norm_num)
theorem B270125 : Blo 179801 270125 := bbase (se 3 (by rfl) ⟨50648, by rfl⟩ : syracuseStep 270125 = 101297) (by norm_num)
theorem B204601 : Blo 179801 204601 := bbase (se 2 (by rfl) ⟨76725, by rfl⟩ : syracuseStep 204601 = 153451) (by norm_num)
theorem B270149 : Blo 179801 270149 := bbase (se 4 (by rfl) ⟨25326, by rfl⟩ : syracuseStep 270149 = 50653) (by norm_num)
theorem B270173 : Blo 179801 270173 := bbase (se 3 (by rfl) ⟨50657, by rfl⟩ : syracuseStep 270173 = 101315) (by norm_num)
theorem B204637 : Blo 179801 204637 := bbase (se 3 (by rfl) ⟨38369, by rfl⟩ : syracuseStep 204637 = 76739) (by norm_num)
theorem B270197 : Blo 179801 270197 := bbase (se 5 (by rfl) ⟨12665, by rfl⟩ : syracuseStep 270197 = 25331) (by norm_num)
theorem B204673 : Blo 179801 204673 := bbase (se 2 (by rfl) ⟨76752, by rfl⟩ : syracuseStep 204673 = 153505) (by norm_num)
theorem B270221 : Blo 179801 270221 := bbase (se 3 (by rfl) ⟨50666, by rfl⟩ : syracuseStep 270221 = 101333) (by norm_num)
theorem B270245 : Blo 179801 270245 := bbase (se 4 (by rfl) ⟨25335, by rfl⟩ : syracuseStep 270245 = 50671) (by norm_num)
theorem B204709 : Blo 179801 204709 := bbase (se 4 (by rfl) ⟨19191, by rfl⟩ : syracuseStep 204709 = 38383) (by norm_num)
theorem B270269 : Blo 179801 270269 := bbase (se 3 (by rfl) ⟨50675, by rfl⟩ : syracuseStep 270269 = 101351) (by norm_num)
theorem B204745 : Blo 179801 204745 := bbase (se 2 (by rfl) ⟨76779, by rfl⟩ : syracuseStep 204745 = 153559) (by norm_num)
theorem B270293 : Blo 179801 270293 := bbase (se 7 (by rfl) ⟨3167, by rfl⟩ : syracuseStep 270293 = 6335) (by norm_num)
theorem B270317 : Blo 179801 270317 := bbase (se 3 (by rfl) ⟨50684, by rfl⟩ : syracuseStep 270317 = 101369) (by norm_num)
theorem B204781 : Blo 179801 204781 := bbase (se 3 (by rfl) ⟨38396, by rfl⟩ : syracuseStep 204781 = 76793) (by norm_num)
theorem B270341 : Blo 179801 270341 := bbase (se 4 (by rfl) ⟨25344, by rfl⟩ : syracuseStep 270341 = 50689) (by norm_num)
theorem B204817 : Blo 179801 204817 := bbase (se 2 (by rfl) ⟨76806, by rfl⟩ : syracuseStep 204817 = 153613) (by norm_num)
theorem B270365 : Blo 179801 270365 := bbase (se 3 (by rfl) ⟨50693, by rfl⟩ : syracuseStep 270365 = 101387) (by norm_num)
theorem B270389 : Blo 179801 270389 := bbase (se 5 (by rfl) ⟨12674, by rfl⟩ : syracuseStep 270389 = 25349) (by norm_num)
theorem B204853 : Blo 179801 204853 := bbase (se 5 (by rfl) ⟨9602, by rfl⟩ : syracuseStep 204853 = 19205) (by norm_num)
theorem B270413 : Blo 179801 270413 := bbase (se 3 (by rfl) ⟨50702, by rfl⟩ : syracuseStep 270413 = 101405) (by norm_num)
theorem B204889 : Blo 179801 204889 := bbase (se 2 (by rfl) ⟨76833, by rfl⟩ : syracuseStep 204889 = 153667) (by norm_num)
theorem B270437 : Blo 179801 270437 := bbase (se 4 (by rfl) ⟨25353, by rfl⟩ : syracuseStep 270437 = 50707) (by norm_num)
theorem B270461 : Blo 179801 270461 := bbase (se 3 (by rfl) ⟨50711, by rfl⟩ : syracuseStep 270461 = 101423) (by norm_num)
theorem B204925 : Blo 179801 204925 := bbase (se 3 (by rfl) ⟨38423, by rfl⟩ : syracuseStep 204925 = 76847) (by norm_num)
theorem B925829 : Blo 179801 925829 := bbase (se 4 (by rfl) ⟨86796, by rfl⟩ : syracuseStep 925829 = 173593) (by norm_num)
theorem B270485 : Blo 179801 270485 := bbase (se 6 (by rfl) ⟨6339, by rfl⟩ : syracuseStep 270485 = 12679) (by norm_num)
theorem B204961 : Blo 179801 204961 := bbase (se 2 (by rfl) ⟨76860, by rfl⟩ : syracuseStep 204961 = 153721) (by norm_num)
theorem B270509 : Blo 179801 270509 := bbase (se 3 (by rfl) ⟨50720, by rfl⟩ : syracuseStep 270509 = 101441) (by norm_num)
theorem B270533 : Blo 179801 270533 := bbase (se 4 (by rfl) ⟨25362, by rfl⟩ : syracuseStep 270533 = 50725) (by norm_num)
theorem B204997 : Blo 179801 204997 := bbase (se 4 (by rfl) ⟨19218, by rfl⟩ : syracuseStep 204997 = 38437) (by norm_num)
theorem B270557 : Blo 179801 270557 := bbase (se 3 (by rfl) ⟨50729, by rfl⟩ : syracuseStep 270557 = 101459) (by norm_num)
theorem B205033 : Blo 179801 205033 := bbase (se 2 (by rfl) ⟨76887, by rfl⟩ : syracuseStep 205033 = 153775) (by norm_num)
theorem B270581 : Blo 179801 270581 := bbase (se 5 (by rfl) ⟨12683, by rfl⟩ : syracuseStep 270581 = 25367) (by norm_num)
theorem B270605 : Blo 179801 270605 := bbase (se 3 (by rfl) ⟨50738, by rfl⟩ : syracuseStep 270605 = 101477) (by norm_num)
theorem B205069 : Blo 179801 205069 := bbase (se 3 (by rfl) ⟨38450, by rfl⟩ : syracuseStep 205069 = 76901) (by norm_num)
theorem B270629 : Blo 179801 270629 := bbase (se 4 (by rfl) ⟨25371, by rfl⟩ : syracuseStep 270629 = 50743) (by norm_num)
theorem B205105 : Blo 179801 205105 := bbase (se 2 (by rfl) ⟨76914, by rfl⟩ : syracuseStep 205105 = 153829) (by norm_num)
theorem B270653 : Blo 179801 270653 := bbase (se 3 (by rfl) ⟨50747, by rfl⟩ : syracuseStep 270653 = 101495) (by norm_num)
theorem B270677 : Blo 179801 270677 := bbase (se 10 (by rfl) ⟨396, by rfl⟩ : syracuseStep 270677 = 793) (by norm_num)
theorem B205141 : Blo 179801 205141 := bbase (se 10 (by rfl) ⟨300, by rfl⟩ : syracuseStep 205141 = 601) (by norm_num)
theorem B270701 : Blo 179801 270701 := bbase (se 3 (by rfl) ⟨50756, by rfl⟩ : syracuseStep 270701 = 101513) (by norm_num)
theorem B205177 : Blo 179801 205177 := bbase (se 2 (by rfl) ⟨76941, by rfl⟩ : syracuseStep 205177 = 153883) (by norm_num)
theorem B303493 : Blo 179801 303493 := bbase (se 4 (by rfl) ⟨28452, by rfl⟩ : syracuseStep 303493 = 56905) (by norm_num)
theorem B270725 : Blo 179801 270725 := bbase (se 4 (by rfl) ⟨25380, by rfl⟩ : syracuseStep 270725 = 50761) (by norm_num)
theorem B270749 : Blo 179801 270749 := bbase (se 3 (by rfl) ⟨50765, by rfl⟩ : syracuseStep 270749 = 101531) (by norm_num)
theorem B205213 : Blo 179801 205213 := bbase (se 3 (by rfl) ⟨38477, by rfl⟩ : syracuseStep 205213 = 76955) (by norm_num)
theorem B270773 : Blo 179801 270773 := bbase (se 5 (by rfl) ⟨12692, by rfl⟩ : syracuseStep 270773 = 25385) (by norm_num)
theorem B205249 : Blo 179801 205249 := bbase (se 2 (by rfl) ⟨76968, by rfl⟩ : syracuseStep 205249 = 153937) (by norm_num)
theorem B270797 : Blo 179801 270797 := bbase (se 3 (by rfl) ⟨50774, by rfl⟩ : syracuseStep 270797 = 101549) (by norm_num)
theorem B303581 : Blo 179801 303581 := bbase (se 3 (by rfl) ⟨56921, by rfl⟩ : syracuseStep 303581 = 113843) (by norm_num)
theorem B270821 : Blo 179801 270821 := bbase (se 4 (by rfl) ⟨25389, by rfl⟩ : syracuseStep 270821 = 50779) (by norm_num)
theorem B205285 : Blo 179801 205285 := bbase (se 4 (by rfl) ⟨19245, by rfl⟩ : syracuseStep 205285 = 38491) (by norm_num)
theorem B205301 : Blo 179801 205301 := bbase (se 5 (by rfl) ⟨9623, by rfl⟩ : syracuseStep 205301 = 19247) (by norm_num)
theorem B270845 : Blo 179801 270845 := bbase (se 3 (by rfl) ⟨50783, by rfl⟩ : syracuseStep 270845 = 101567) (by norm_num)
theorem B205321 : Blo 179801 205321 := bbase (se 2 (by rfl) ⟨76995, by rfl⟩ : syracuseStep 205321 = 153991) (by norm_num)
theorem B270869 : Blo 179801 270869 := bbase (se 6 (by rfl) ⟨6348, by rfl⟩ : syracuseStep 270869 = 12697) (by norm_num)
theorem B270893 : Blo 179801 270893 := bbase (se 3 (by rfl) ⟨50792, by rfl⟩ : syracuseStep 270893 = 101585) (by norm_num)
theorem B205357 : Blo 179801 205357 := bbase (se 3 (by rfl) ⟨38504, by rfl⟩ : syracuseStep 205357 = 77009) (by norm_num)
theorem B205373 : Blo 179801 205373 := bbase (se 3 (by rfl) ⟨38507, by rfl⟩ : syracuseStep 205373 = 77015) (by norm_num)
theorem B270917 : Blo 179801 270917 := bbase (se 4 (by rfl) ⟨25398, by rfl⟩ : syracuseStep 270917 = 50797) (by norm_num)
theorem B205393 : Blo 179801 205393 := bbase (se 2 (by rfl) ⟨77022, by rfl⟩ : syracuseStep 205393 = 154045) (by norm_num)
theorem B303709 : Blo 179801 303709 := bbase (se 3 (by rfl) ⟨56945, by rfl⟩ : syracuseStep 303709 = 113891) (by norm_num)
theorem B270941 : Blo 179801 270941 := bbase (se 3 (by rfl) ⟨50801, by rfl⟩ : syracuseStep 270941 = 101603) (by norm_num)
theorem B270965 : Blo 179801 270965 := bbase (se 5 (by rfl) ⟨12701, by rfl⟩ : syracuseStep 270965 = 25403) (by norm_num)
theorem B205429 : Blo 179801 205429 := bbase (se 5 (by rfl) ⟨9629, by rfl⟩ : syracuseStep 205429 = 19259) (by norm_num)
theorem B270989 : Blo 179801 270989 := bbase (se 3 (by rfl) ⟨50810, by rfl⟩ : syracuseStep 270989 = 101621) (by norm_num)
theorem B205465 : Blo 179801 205465 := bbase (se 2 (by rfl) ⟨77049, by rfl⟩ : syracuseStep 205465 = 154099) (by norm_num)
theorem B271013 : Blo 179801 271013 := bbase (se 4 (by rfl) ⟨25407, by rfl⟩ : syracuseStep 271013 = 50815) (by norm_num)
theorem B303797 : Blo 179801 303797 := bbase (se 5 (by rfl) ⟨14240, by rfl⟩ : syracuseStep 303797 = 28481) (by norm_num)
theorem B271037 : Blo 179801 271037 := bbase (se 3 (by rfl) ⟨50819, by rfl⟩ : syracuseStep 271037 = 101639) (by norm_num)
theorem B205501 : Blo 179801 205501 := bbase (se 3 (by rfl) ⟨38531, by rfl⟩ : syracuseStep 205501 = 77063) (by norm_num)
theorem B271061 : Blo 179801 271061 := bbase (se 7 (by rfl) ⟨3176, by rfl⟩ : syracuseStep 271061 = 6353) (by norm_num)
theorem B697045 : Blo 179801 697045 := bbase (se 7 (by rfl) ⟨8168, by rfl⟩ : syracuseStep 697045 = 16337) (by norm_num)
theorem B205537 : Blo 179801 205537 := bbase (se 2 (by rfl) ⟨77076, by rfl⟩ : syracuseStep 205537 = 154153) (by norm_num)
theorem B271085 : Blo 179801 271085 := bbase (se 3 (by rfl) ⟨50828, by rfl⟩ : syracuseStep 271085 = 101657) (by norm_num)
theorem B271109 : Blo 179801 271109 := bbase (se 4 (by rfl) ⟨25416, by rfl⟩ : syracuseStep 271109 = 50833) (by norm_num)
theorem B205573 : Blo 179801 205573 := bbase (se 4 (by rfl) ⟨19272, by rfl⟩ : syracuseStep 205573 = 38545) (by norm_num)
theorem B271133 : Blo 179801 271133 := bbase (se 3 (by rfl) ⟨50837, by rfl⟩ : syracuseStep 271133 = 101675) (by norm_num)
theorem B205609 : Blo 179801 205609 := bbase (se 2 (by rfl) ⟨77103, by rfl⟩ : syracuseStep 205609 = 154207) (by norm_num)
theorem B303925 : Blo 179801 303925 := bbase (se 5 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 303925 = 28493) (by norm_num)
theorem B271157 : Blo 179801 271157 := bbase (se 5 (by rfl) ⟨12710, by rfl⟩ : syracuseStep 271157 = 25421) (by norm_num)
theorem B271181 : Blo 179801 271181 := bbase (se 3 (by rfl) ⟨50846, by rfl⟩ : syracuseStep 271181 = 101693) (by norm_num)
theorem B205645 : Blo 179801 205645 := bbase (se 3 (by rfl) ⟨38558, by rfl⟩ : syracuseStep 205645 = 77117) (by norm_num)
theorem B271205 : Blo 179801 271205 := bbase (se 4 (by rfl) ⟨25425, by rfl⟩ : syracuseStep 271205 = 50851) (by norm_num)
theorem B205681 : Blo 179801 205681 := bbase (se 2 (by rfl) ⟨77130, by rfl⟩ : syracuseStep 205681 = 154261) (by norm_num)
theorem B271229 : Blo 179801 271229 := bbase (se 3 (by rfl) ⟨50855, by rfl⟩ : syracuseStep 271229 = 101711) (by norm_num)
theorem B304013 : Blo 179801 304013 := bbase (se 3 (by rfl) ⟨57002, by rfl⟩ : syracuseStep 304013 = 114005) (by norm_num)
theorem B271253 : Blo 179801 271253 := bbase (se 6 (by rfl) ⟨6357, by rfl⟩ : syracuseStep 271253 = 12715) (by norm_num)
theorem B205717 : Blo 179801 205717 := bbase (se 6 (by rfl) ⟨4821, by rfl⟩ : syracuseStep 205717 = 9643) (by norm_num)
theorem B271277 : Blo 179801 271277 := bbase (se 3 (by rfl) ⟨50864, by rfl⟩ : syracuseStep 271277 = 101729) (by norm_num)
theorem B1254325 : Blo 179801 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B205753 : Blo 179801 205753 := bbase (se 2 (by rfl) ⟨77157, by rfl⟩ : syracuseStep 205753 = 154315) (by norm_num)
theorem B271301 : Blo 179801 271301 := bbase (se 4 (by rfl) ⟨25434, by rfl⟩ : syracuseStep 271301 = 50869) (by norm_num)
theorem B271325 : Blo 179801 271325 := bbase (se 3 (by rfl) ⟨50873, by rfl⟩ : syracuseStep 271325 = 101747) (by norm_num)
theorem B205789 : Blo 179801 205789 := bbase (se 3 (by rfl) ⟨38585, by rfl⟩ : syracuseStep 205789 = 77171) (by norm_num)
theorem B271349 : Blo 179801 271349 := bbase (se 5 (by rfl) ⟨12719, by rfl⟩ : syracuseStep 271349 = 25439) (by norm_num)
theorem B205825 : Blo 179801 205825 := bbase (se 2 (by rfl) ⟨77184, by rfl⟩ : syracuseStep 205825 = 154369) (by norm_num)
theorem B697349 : Blo 179801 697349 := bbase (se 4 (by rfl) ⟨65376, by rfl⟩ : syracuseStep 697349 = 130753) (by norm_num)
theorem B304141 : Blo 179801 304141 := bbase (se 3 (by rfl) ⟨57026, by rfl⟩ : syracuseStep 304141 = 114053) (by norm_num)
theorem B271373 : Blo 179801 271373 := bbase (se 3 (by rfl) ⟨50882, by rfl⟩ : syracuseStep 271373 = 101765) (by norm_num)
theorem B271397 : Blo 179801 271397 := bbase (se 4 (by rfl) ⟨25443, by rfl⟩ : syracuseStep 271397 = 50887) (by norm_num)
theorem B205861 : Blo 179801 205861 := bbase (se 4 (by rfl) ⟨19299, by rfl⟩ : syracuseStep 205861 = 38599) (by norm_num)
theorem B894005 : Blo 179801 894005 := bbase (se 5 (by rfl) ⟨41906, by rfl⟩ : syracuseStep 894005 = 83813) (by norm_num)
theorem B271421 : Blo 179801 271421 := bbase (se 3 (by rfl) ⟨50891, by rfl⟩ : syracuseStep 271421 = 101783) (by norm_num)
theorem B205897 : Blo 179801 205897 := bbase (se 2 (by rfl) ⟨77211, by rfl⟩ : syracuseStep 205897 = 154423) (by norm_num)
theorem B271445 : Blo 179801 271445 := bbase (se 8 (by rfl) ⟨1590, by rfl⟩ : syracuseStep 271445 = 3181) (by norm_num)
theorem B304229 : Blo 179801 304229 := bbase (se 4 (by rfl) ⟨28521, by rfl⟩ : syracuseStep 304229 = 57043) (by norm_num)
theorem B271469 : Blo 179801 271469 := bbase (se 3 (by rfl) ⟨50900, by rfl⟩ : syracuseStep 271469 = 101801) (by norm_num)
theorem B205933 : Blo 179801 205933 := bbase (se 3 (by rfl) ⟨38612, by rfl⟩ : syracuseStep 205933 = 77225) (by norm_num)
theorem B271493 : Blo 179801 271493 := bbase (se 4 (by rfl) ⟨25452, by rfl⟩ : syracuseStep 271493 = 50905) (by norm_num)
theorem B205969 : Blo 179801 205969 := bbase (se 2 (by rfl) ⟨77238, by rfl⟩ : syracuseStep 205969 = 154477) (by norm_num)
theorem B271517 : Blo 179801 271517 := bbase (se 3 (by rfl) ⟨50909, by rfl⟩ : syracuseStep 271517 = 101819) (by norm_num)
theorem B271541 : Blo 179801 271541 := bbase (se 5 (by rfl) ⟨12728, by rfl⟩ : syracuseStep 271541 = 25457) (by norm_num)
theorem B206005 : Blo 179801 206005 := bbase (se 5 (by rfl) ⟨9656, by rfl⟩ : syracuseStep 206005 = 19313) (by norm_num)
theorem B271565 : Blo 179801 271565 := bbase (se 3 (by rfl) ⟨50918, by rfl⟩ : syracuseStep 271565 = 101837) (by norm_num)
theorem B206041 : Blo 179801 206041 := bbase (se 2 (by rfl) ⟨77265, by rfl⟩ : syracuseStep 206041 = 154531) (by norm_num)
theorem B304357 : Blo 179801 304357 := bbase (se 4 (by rfl) ⟨28533, by rfl⟩ : syracuseStep 304357 = 57067) (by norm_num)
theorem B271589 : Blo 179801 271589 := bbase (se 4 (by rfl) ⟨25461, by rfl⟩ : syracuseStep 271589 = 50923) (by norm_num)
theorem B271613 : Blo 179801 271613 := bbase (se 3 (by rfl) ⟨50927, by rfl⟩ : syracuseStep 271613 = 101855) (by norm_num)
theorem B206077 : Blo 179801 206077 := bbase (se 3 (by rfl) ⟨38639, by rfl⟩ : syracuseStep 206077 = 77279) (by norm_num)
theorem B271637 : Blo 179801 271637 := bbase (se 6 (by rfl) ⟨6366, by rfl⟩ : syracuseStep 271637 = 12733) (by norm_num)
theorem B206113 : Blo 179801 206113 := bbase (se 2 (by rfl) ⟨77292, by rfl⟩ : syracuseStep 206113 = 154585) (by norm_num)
theorem B271661 : Blo 179801 271661 := bbase (se 3 (by rfl) ⟨50936, by rfl⟩ : syracuseStep 271661 = 101873) (by norm_num)
theorem B304445 : Blo 179801 304445 := bbase (se 3 (by rfl) ⟨57083, by rfl⟩ : syracuseStep 304445 = 114167) (by norm_num)
theorem B271685 : Blo 179801 271685 := bbase (se 4 (by rfl) ⟨25470, by rfl⟩ : syracuseStep 271685 = 50941) (by norm_num)
theorem B206149 : Blo 179801 206149 := bbase (se 4 (by rfl) ⟨19326, by rfl⟩ : syracuseStep 206149 = 38653) (by norm_num)
theorem B271709 : Blo 179801 271709 := bbase (se 3 (by rfl) ⟨50945, by rfl⟩ : syracuseStep 271709 = 101891) (by norm_num)
theorem B206185 : Blo 179801 206185 := bbase (se 2 (by rfl) ⟨77319, by rfl⟩ : syracuseStep 206185 = 154639) (by norm_num)
theorem B271733 : Blo 179801 271733 := bbase (se 5 (by rfl) ⟨12737, by rfl⟩ : syracuseStep 271733 = 25475) (by norm_num)
theorem B664949 : Blo 179801 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B271757 : Blo 179801 271757 := bbase (se 3 (by rfl) ⟨50954, by rfl⟩ : syracuseStep 271757 = 101909) (by norm_num)
theorem B206221 : Blo 179801 206221 := bbase (se 3 (by rfl) ⟨38666, by rfl⟩ : syracuseStep 206221 = 77333) (by norm_num)
theorem B927125 : Blo 179801 927125 := bbase (se 6 (by rfl) ⟨21729, by rfl⟩ : syracuseStep 927125 = 43459) (by norm_num)
theorem B271781 : Blo 179801 271781 := bbase (se 4 (by rfl) ⟨25479, by rfl⟩ : syracuseStep 271781 = 50959) (by norm_num)
theorem B206257 : Blo 179801 206257 := bbase (se 2 (by rfl) ⟨77346, by rfl⟩ : syracuseStep 206257 = 154693) (by norm_num)
theorem B304573 : Blo 179801 304573 := bbase (se 3 (by rfl) ⟨57107, by rfl⟩ : syracuseStep 304573 = 114215) (by norm_num)
theorem B271805 : Blo 179801 271805 := bbase (se 3 (by rfl) ⟨50963, by rfl⟩ : syracuseStep 271805 = 101927) (by norm_num)
theorem B206281 : Blo 179801 206281 := bbase (se 2 (by rfl) ⟨77355, by rfl⟩ : syracuseStep 206281 = 154711) (by norm_num)
theorem B271829 : Blo 179801 271829 := bbase (se 7 (by rfl) ⟨3185, by rfl⟩ : syracuseStep 271829 = 6371) (by norm_num)
theorem B206293 : Blo 179801 206293 := bbase (se 7 (by rfl) ⟨2417, by rfl⟩ : syracuseStep 206293 = 4835) (by norm_num)
theorem B271853 : Blo 179801 271853 := bbase (se 3 (by rfl) ⟨50972, by rfl⟩ : syracuseStep 271853 = 101945) (by norm_num)
theorem B206329 : Blo 179801 206329 := bbase (se 2 (by rfl) ⟨77373, by rfl⟩ : syracuseStep 206329 = 154747) (by norm_num)
theorem B435709 : Blo 179801 435709 := bbase (se 3 (by rfl) ⟨81695, by rfl⟩ : syracuseStep 435709 = 163391) (by norm_num)
theorem B271877 : Blo 179801 271877 := bbase (se 4 (by rfl) ⟨25488, by rfl⟩ : syracuseStep 271877 = 50977) (by norm_num)
theorem B304661 : Blo 179801 304661 := bbase (se 6 (by rfl) ⟨7140, by rfl⟩ : syracuseStep 304661 = 14281) (by norm_num)
theorem B271901 : Blo 179801 271901 := bbase (se 3 (by rfl) ⟨50981, by rfl⟩ : syracuseStep 271901 = 101963) (by norm_num)
theorem B206365 : Blo 179801 206365 := bbase (se 3 (by rfl) ⟨38693, by rfl⟩ : syracuseStep 206365 = 77387) (by norm_num)
theorem B271925 : Blo 179801 271925 := bbase (se 5 (by rfl) ⟨12746, by rfl⟩ : syracuseStep 271925 = 25493) (by norm_num)
theorem B206401 : Blo 179801 206401 := bbase (se 2 (by rfl) ⟨77400, by rfl⟩ : syracuseStep 206401 = 154801) (by norm_num)
theorem B271949 : Blo 179801 271949 := bbase (se 3 (by rfl) ⟨50990, by rfl⟩ : syracuseStep 271949 = 101981) (by norm_num)
theorem B271973 : Blo 179801 271973 := bbase (se 4 (by rfl) ⟨25497, by rfl⟩ : syracuseStep 271973 = 50995) (by norm_num)
theorem B206437 : Blo 179801 206437 := bbase (se 4 (by rfl) ⟨19353, by rfl⟩ : syracuseStep 206437 = 38707) (by norm_num)
theorem B271997 : Blo 179801 271997 := bbase (se 3 (by rfl) ⟨50999, by rfl⟩ : syracuseStep 271997 = 101999) (by norm_num)
theorem B206473 : Blo 179801 206473 := bbase (se 2 (by rfl) ⟨77427, by rfl⟩ : syracuseStep 206473 = 154855) (by norm_num)
theorem B304789 : Blo 179801 304789 := bbase (se 6 (by rfl) ⟨7143, by rfl⟩ : syracuseStep 304789 = 14287) (by norm_num)
theorem B272021 : Blo 179801 272021 := bbase (se 6 (by rfl) ⟨6375, by rfl⟩ : syracuseStep 272021 = 12751) (by norm_num)
theorem B272045 : Blo 179801 272045 := bbase (se 3 (by rfl) ⟨51008, by rfl⟩ : syracuseStep 272045 = 102017) (by norm_num)
theorem B206509 : Blo 179801 206509 := bbase (se 3 (by rfl) ⟨38720, by rfl⟩ : syracuseStep 206509 = 77441) (by norm_num)
theorem B206513 : Blo 179801 206513 := bbase (se 2 (by rfl) ⟨77442, by rfl⟩ : syracuseStep 206513 = 154885) (by norm_num)
theorem B272069 : Blo 179801 272069 := bbase (se 4 (by rfl) ⟨25506, by rfl⟩ : syracuseStep 272069 = 51013) (by norm_num)
theorem B206545 : Blo 179801 206545 := bbase (se 2 (by rfl) ⟨77454, by rfl⟩ : syracuseStep 206545 = 154909) (by norm_num)
theorem B272093 : Blo 179801 272093 := bbase (se 3 (by rfl) ⟨51017, by rfl⟩ : syracuseStep 272093 = 102035) (by norm_num)
theorem B304877 : Blo 179801 304877 := bbase (se 3 (by rfl) ⟨57164, by rfl⟩ : syracuseStep 304877 = 114329) (by norm_num)
theorem B468725 : Blo 179801 468725 := bbase (se 5 (by rfl) ⟨21971, by rfl⟩ : syracuseStep 468725 = 43943) (by norm_num)
theorem B272117 : Blo 179801 272117 := bbase (se 5 (by rfl) ⟨12755, by rfl⟩ : syracuseStep 272117 = 25511) (by norm_num)
theorem B206581 : Blo 179801 206581 := bbase (se 5 (by rfl) ⟨9683, by rfl⟩ : syracuseStep 206581 = 19367) (by norm_num)
theorem B272141 : Blo 179801 272141 := bbase (se 3 (by rfl) ⟨51026, by rfl⟩ : syracuseStep 272141 = 102053) (by norm_num)
theorem B206617 : Blo 179801 206617 := bbase (se 2 (by rfl) ⟨77481, by rfl⟩ : syracuseStep 206617 = 154963) (by norm_num)
theorem B272165 : Blo 179801 272165 := bbase (se 4 (by rfl) ⟨25515, by rfl⟩ : syracuseStep 272165 = 51031) (by norm_num)
theorem B272189 : Blo 179801 272189 := bbase (se 3 (by rfl) ⟨51035, by rfl⟩ : syracuseStep 272189 = 102071) (by norm_num)
theorem B206653 : Blo 179801 206653 := bbase (se 3 (by rfl) ⟨38747, by rfl⟩ : syracuseStep 206653 = 77495) (by norm_num)
theorem B206669 : Blo 179801 206669 := bbase (se 3 (by rfl) ⟨38750, by rfl⟩ : syracuseStep 206669 = 77501) (by norm_num)
theorem B436045 : Blo 179801 436045 := bbase (se 3 (by rfl) ⟨81758, by rfl⟩ : syracuseStep 436045 = 163517) (by norm_num)
theorem B272213 : Blo 179801 272213 := bbase (se 9 (by rfl) ⟨797, by rfl⟩ : syracuseStep 272213 = 1595) (by norm_num)
theorem B206689 : Blo 179801 206689 := bbase (se 2 (by rfl) ⟨77508, by rfl⟩ : syracuseStep 206689 = 155017) (by norm_num)
theorem B305005 : Blo 179801 305005 := bbase (se 3 (by rfl) ⟨57188, by rfl⟩ : syracuseStep 305005 = 114377) (by norm_num)
theorem B272237 : Blo 179801 272237 := bbase (se 3 (by rfl) ⟨51044, by rfl⟩ : syracuseStep 272237 = 102089) (by norm_num)
theorem B272261 : Blo 179801 272261 := bbase (se 4 (by rfl) ⟨25524, by rfl⟩ : syracuseStep 272261 = 51049) (by norm_num)
theorem B206725 : Blo 179801 206725 := bbase (se 4 (by rfl) ⟨19380, by rfl⟩ : syracuseStep 206725 = 38761) (by norm_num)
theorem B272285 : Blo 179801 272285 := bbase (se 3 (by rfl) ⟨51053, by rfl⟩ : syracuseStep 272285 = 102107) (by norm_num)
theorem B206761 : Blo 179801 206761 := bbase (se 2 (by rfl) ⟨77535, by rfl⟩ : syracuseStep 206761 = 155071) (by norm_num)
theorem B272309 : Blo 179801 272309 := bbase (se 5 (by rfl) ⟨12764, by rfl⟩ : syracuseStep 272309 = 25529) (by norm_num)
theorem B305093 : Blo 179801 305093 := bbase (se 4 (by rfl) ⟨28602, by rfl⟩ : syracuseStep 305093 = 57205) (by norm_num)
theorem B272333 : Blo 179801 272333 := bbase (se 3 (by rfl) ⟨51062, by rfl⟩ : syracuseStep 272333 = 102125) (by norm_num)
theorem B272357 : Blo 179801 272357 := bbase (se 4 (by rfl) ⟨25533, by rfl⟩ : syracuseStep 272357 = 51067) (by norm_num)
theorem B272381 : Blo 179801 272381 := bbase (se 3 (by rfl) ⟨51071, by rfl⟩ : syracuseStep 272381 = 102143) (by norm_num)
theorem B272405 : Blo 179801 272405 := bbase (se 6 (by rfl) ⟨6384, by rfl⟩ : syracuseStep 272405 = 12769) (by norm_num)
theorem B272429 : Blo 179801 272429 := bbase (se 3 (by rfl) ⟨51080, by rfl⟩ : syracuseStep 272429 = 102161) (by norm_num)
theorem B305221 : Blo 179801 305221 := bbase (se 4 (by rfl) ⟨28614, by rfl⟩ : syracuseStep 305221 = 57229) (by norm_num)
theorem B272453 : Blo 179801 272453 := bbase (se 4 (by rfl) ⟨25542, by rfl⟩ : syracuseStep 272453 = 51085) (by norm_num)
theorem B272477 : Blo 179801 272477 := bbase (se 3 (by rfl) ⟨51089, by rfl⟩ : syracuseStep 272477 = 102179) (by norm_num)
theorem B272501 : Blo 179801 272501 := bbase (se 5 (by rfl) ⟨12773, by rfl⟩ : syracuseStep 272501 = 25547) (by norm_num)
theorem B272525 : Blo 179801 272525 := bbase (se 3 (by rfl) ⟨51098, by rfl⟩ : syracuseStep 272525 = 102197) (by norm_num)
theorem B1321109 : Blo 179801 1321109 := bbase (se 6 (by rfl) ⟨30963, by rfl⟩ : syracuseStep 1321109 = 61927) (by norm_num)
theorem B305309 : Blo 179801 305309 := bbase (se 3 (by rfl) ⟨57245, by rfl⟩ : syracuseStep 305309 = 114491) (by norm_num)
theorem B272549 : Blo 179801 272549 := bbase (se 4 (by rfl) ⟨25551, by rfl⟩ : syracuseStep 272549 = 51103) (by norm_num)
theorem B469165 : Blo 179801 469165 := bbase (se 3 (by rfl) ⟨87968, by rfl⟩ : syracuseStep 469165 = 175937) (by norm_num)
theorem B272573 : Blo 179801 272573 := bbase (se 3 (by rfl) ⟨51107, by rfl⟩ : syracuseStep 272573 = 102215) (by norm_num)
theorem B272597 : Blo 179801 272597 := bbase (se 7 (by rfl) ⟨3194, by rfl⟩ : syracuseStep 272597 = 6389) (by norm_num)
theorem B272621 : Blo 179801 272621 := bbase (se 3 (by rfl) ⟨51116, by rfl⟩ : syracuseStep 272621 = 102233) (by norm_num)
theorem B272645 : Blo 179801 272645 := bbase (se 4 (by rfl) ⟨25560, by rfl⟩ : syracuseStep 272645 = 51121) (by norm_num)
theorem B305437 : Blo 179801 305437 := bbase (se 3 (by rfl) ⟨57269, by rfl⟩ : syracuseStep 305437 = 114539) (by norm_num)
theorem B272669 : Blo 179801 272669 := bbase (se 3 (by rfl) ⟨51125, by rfl⟩ : syracuseStep 272669 = 102251) (by norm_num)
theorem B272693 : Blo 179801 272693 := bbase (se 5 (by rfl) ⟨12782, by rfl⟩ : syracuseStep 272693 = 25565) (by norm_num)
theorem B272717 : Blo 179801 272717 := bbase (se 3 (by rfl) ⟨51134, by rfl⟩ : syracuseStep 272717 = 102269) (by norm_num)
theorem B272741 : Blo 179801 272741 := bbase (se 4 (by rfl) ⟨25569, by rfl⟩ : syracuseStep 272741 = 51139) (by norm_num)
theorem B305525 : Blo 179801 305525 := bbase (se 5 (by rfl) ⟨14321, by rfl⟩ : syracuseStep 305525 = 28643) (by norm_num)
theorem B272765 : Blo 179801 272765 := bbase (se 3 (by rfl) ⟨51143, by rfl⟩ : syracuseStep 272765 = 102287) (by norm_num)
theorem B371069 : Blo 179801 371069 := bbase (se 3 (by rfl) ⟨69575, by rfl⟩ : syracuseStep 371069 = 139151) (by norm_num)
theorem B272789 : Blo 179801 272789 := bbase (se 6 (by rfl) ⟨6393, by rfl⟩ : syracuseStep 272789 = 12787) (by norm_num)
theorem B272813 : Blo 179801 272813 := bbase (se 3 (by rfl) ⟨51152, by rfl⟩ : syracuseStep 272813 = 102305) (by norm_num)
theorem B436661 : Blo 179801 436661 := bbase (se 5 (by rfl) ⟨20468, by rfl⟩ : syracuseStep 436661 = 40937) (by norm_num)
theorem B272837 : Blo 179801 272837 := bbase (se 4 (by rfl) ⟨25578, by rfl⟩ : syracuseStep 272837 = 51157) (by norm_num)
theorem B272861 : Blo 179801 272861 := bbase (se 3 (by rfl) ⟨51161, by rfl⟩ : syracuseStep 272861 = 102323) (by norm_num)
theorem B305653 : Blo 179801 305653 := bbase (se 5 (by rfl) ⟨14327, by rfl⟩ : syracuseStep 305653 = 28655) (by norm_num)
theorem B272885 : Blo 179801 272885 := bbase (se 5 (by rfl) ⟨12791, by rfl⟩ : syracuseStep 272885 = 25583) (by norm_num)
theorem B272909 : Blo 179801 272909 := bbase (se 3 (by rfl) ⟨51170, by rfl⟩ : syracuseStep 272909 = 102341) (by norm_num)
theorem B272933 : Blo 179801 272933 := bbase (se 4 (by rfl) ⟨25587, by rfl⟩ : syracuseStep 272933 = 51175) (by norm_num)
theorem B272957 : Blo 179801 272957 := bbase (se 3 (by rfl) ⟨51179, by rfl⟩ : syracuseStep 272957 = 102359) (by norm_num)
theorem B305741 : Blo 179801 305741 := bbase (se 3 (by rfl) ⟨57326, by rfl⟩ : syracuseStep 305741 = 114653) (by norm_num)
theorem B272981 : Blo 179801 272981 := bbase (se 8 (by rfl) ⟨1599, by rfl⟩ : syracuseStep 272981 = 3199) (by norm_num)
theorem B273005 : Blo 179801 273005 := bbase (se 3 (by rfl) ⟨51188, by rfl⟩ : syracuseStep 273005 = 102377) (by norm_num)
theorem B273029 : Blo 179801 273029 := bbase (se 4 (by rfl) ⟨25596, by rfl⟩ : syracuseStep 273029 = 51193) (by norm_num)
theorem B273053 : Blo 179801 273053 := bbase (se 3 (by rfl) ⟨51197, by rfl⟩ : syracuseStep 273053 = 102395) (by norm_num)
theorem B928421 : Blo 179801 928421 := bbase (se 4 (by rfl) ⟨87039, by rfl⟩ : syracuseStep 928421 = 174079) (by norm_num)
theorem B1157813 : Blo 179801 1157813 := bbase (se 5 (by rfl) ⟨54272, by rfl⟩ : syracuseStep 1157813 = 108545) (by norm_num)
theorem B273077 : Blo 179801 273077 := bbase (se 5 (by rfl) ⟨12800, by rfl⟩ : syracuseStep 273077 = 25601) (by norm_num)
theorem B404165 : Blo 179801 404165 := bbase (se 4 (by rfl) ⟨37890, by rfl⟩ : syracuseStep 404165 = 75781) (by norm_num)
theorem B305869 : Blo 179801 305869 := bbase (se 3 (by rfl) ⟨57350, by rfl⟩ : syracuseStep 305869 = 114701) (by norm_num)
theorem B273101 : Blo 179801 273101 := bbase (se 3 (by rfl) ⟨51206, by rfl⟩ : syracuseStep 273101 = 102413) (by norm_num)
theorem B273125 : Blo 179801 273125 := bbase (se 4 (by rfl) ⟨25605, by rfl⟩ : syracuseStep 273125 = 51211) (by norm_num)
theorem B273149 : Blo 179801 273149 := bbase (se 3 (by rfl) ⟨51215, by rfl⟩ : syracuseStep 273149 = 102431) (by norm_num)
theorem B273173 : Blo 179801 273173 := bbase (se 6 (by rfl) ⟨6402, by rfl⟩ : syracuseStep 273173 = 12805) (by norm_num)
theorem B305957 : Blo 179801 305957 := bbase (se 4 (by rfl) ⟨28683, by rfl⟩ : syracuseStep 305957 = 57367) (by norm_num)
theorem B273197 : Blo 179801 273197 := bbase (se 3 (by rfl) ⟨51224, by rfl⟩ : syracuseStep 273197 = 102449) (by norm_num)
theorem B273221 : Blo 179801 273221 := bbase (se 4 (by rfl) ⟨25614, by rfl⟩ : syracuseStep 273221 = 51229) (by norm_num)
theorem B273245 : Blo 179801 273245 := bbase (se 3 (by rfl) ⟨51233, by rfl⟩ : syracuseStep 273245 = 102467) (by norm_num)
theorem B437093 : Blo 179801 437093 := bbase (se 4 (by rfl) ⟨40977, by rfl⟩ : syracuseStep 437093 = 81955) (by norm_num)
theorem B273269 : Blo 179801 273269 := bbase (se 5 (by rfl) ⟨12809, by rfl⟩ : syracuseStep 273269 = 25619) (by norm_num)
theorem B273293 : Blo 179801 273293 := bbase (se 3 (by rfl) ⟨51242, by rfl⟩ : syracuseStep 273293 = 102485) (by norm_num)
theorem B306085 : Blo 179801 306085 := bbase (se 4 (by rfl) ⟨28695, by rfl⟩ : syracuseStep 306085 = 57391) (by norm_num)
theorem B273317 : Blo 179801 273317 := bbase (se 4 (by rfl) ⟨25623, by rfl⟩ : syracuseStep 273317 = 51247) (by norm_num)
theorem B273341 : Blo 179801 273341 := bbase (se 3 (by rfl) ⟨51251, by rfl⟩ : syracuseStep 273341 = 102503) (by norm_num)
theorem B273365 : Blo 179801 273365 := bbase (se 7 (by rfl) ⟨3203, by rfl⟩ : syracuseStep 273365 = 6407) (by norm_num)
theorem B928741 : Blo 179801 928741 := bbase (se 4 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 928741 = 174139) (by norm_num)
theorem B273389 : Blo 179801 273389 := bbase (se 3 (by rfl) ⟨51260, by rfl⟩ : syracuseStep 273389 = 102521) (by norm_num)
theorem B306173 : Blo 179801 306173 := bbase (se 3 (by rfl) ⟨57407, by rfl⟩ : syracuseStep 306173 = 114815) (by norm_num)
theorem B273413 : Blo 179801 273413 := bbase (se 4 (by rfl) ⟨25632, by rfl⟩ : syracuseStep 273413 = 51265) (by norm_num)
theorem B273437 : Blo 179801 273437 := bbase (se 3 (by rfl) ⟨51269, by rfl⟩ : syracuseStep 273437 = 102539) (by norm_num)
theorem B273461 : Blo 179801 273461 := bbase (se 5 (by rfl) ⟨12818, by rfl⟩ : syracuseStep 273461 = 25637) (by norm_num)
theorem B273485 : Blo 179801 273485 := bbase (se 3 (by rfl) ⟨51278, by rfl⟩ : syracuseStep 273485 = 102557) (by norm_num)
theorem B207973 : Blo 179801 207973 := bbase (se 4 (by rfl) ⟨19497, by rfl⟩ : syracuseStep 207973 = 38995) (by norm_num)
theorem B273509 : Blo 179801 273509 := bbase (se 4 (by rfl) ⟨25641, by rfl⟩ : syracuseStep 273509 = 51283) (by norm_num)
theorem B306301 : Blo 179801 306301 := bbase (se 3 (by rfl) ⟨57431, by rfl⟩ : syracuseStep 306301 = 114863) (by norm_num)
theorem B273533 : Blo 179801 273533 := bbase (se 3 (by rfl) ⟨51287, by rfl⟩ : syracuseStep 273533 = 102575) (by norm_num)
theorem B404621 : Blo 179801 404621 := bbase (se 3 (by rfl) ⟨75866, by rfl⟩ : syracuseStep 404621 = 151733) (by norm_num)
theorem B273557 : Blo 179801 273557 := bbase (se 6 (by rfl) ⟨6411, by rfl⟩ : syracuseStep 273557 = 12823) (by norm_num)
theorem B273581 : Blo 179801 273581 := bbase (se 3 (by rfl) ⟨51296, by rfl⟩ : syracuseStep 273581 = 102593) (by norm_num)
theorem B273605 : Blo 179801 273605 := bbase (se 4 (by rfl) ⟨25650, by rfl⟩ : syracuseStep 273605 = 51301) (by norm_num)
theorem B404693 : Blo 179801 404693 := bbase (se 7 (by rfl) ⟨4742, by rfl⟩ : syracuseStep 404693 = 9485) (by norm_num)
theorem B306389 : Blo 179801 306389 := bbase (se 7 (by rfl) ⟨3590, by rfl⟩ : syracuseStep 306389 = 7181) (by norm_num)
theorem B273629 : Blo 179801 273629 := bbase (se 3 (by rfl) ⟨51305, by rfl⟩ : syracuseStep 273629 = 102611) (by norm_num)
theorem B273653 : Blo 179801 273653 := bbase (se 5 (by rfl) ⟨12827, by rfl⟩ : syracuseStep 273653 = 25655) (by norm_num)
theorem B273677 : Blo 179801 273677 := bbase (se 3 (by rfl) ⟨51314, by rfl⟩ : syracuseStep 273677 = 102629) (by norm_num)
theorem B404765 : Blo 179801 404765 := bbase (se 3 (by rfl) ⟨75893, by rfl⟩ : syracuseStep 404765 = 151787) (by norm_num)
theorem B273701 : Blo 179801 273701 := bbase (se 4 (by rfl) ⟨25659, by rfl⟩ : syracuseStep 273701 = 51319) (by norm_num)
theorem B273725 : Blo 179801 273725 := bbase (se 3 (by rfl) ⟨51323, by rfl⟩ : syracuseStep 273725 = 102647) (by norm_num)
theorem B306517 : Blo 179801 306517 := bbase (se 11 (by rfl) ⟨224, by rfl⟩ : syracuseStep 306517 = 449) (by norm_num)
theorem B273749 : Blo 179801 273749 := bbase (se 11 (by rfl) ⟨200, by rfl⟩ : syracuseStep 273749 = 401) (by norm_num)
theorem B404837 : Blo 179801 404837 := bbase (se 4 (by rfl) ⟨37953, by rfl⟩ : syracuseStep 404837 = 75907) (by norm_num)
theorem B273773 : Blo 179801 273773 := bbase (se 3 (by rfl) ⟨51332, by rfl⟩ : syracuseStep 273773 = 102665) (by norm_num)
theorem B273797 : Blo 179801 273797 := bbase (se 4 (by rfl) ⟨25668, by rfl⟩ : syracuseStep 273797 = 51337) (by norm_num)
theorem B208265 : Blo 179801 208265 := bbase (se 2 (by rfl) ⟨78099, by rfl⟩ : syracuseStep 208265 = 156199) (by norm_num)
theorem B273821 : Blo 179801 273821 := bbase (se 3 (by rfl) ⟨51341, by rfl⟩ : syracuseStep 273821 = 102683) (by norm_num)
theorem B404909 : Blo 179801 404909 := bbase (se 3 (by rfl) ⟨75920, by rfl⟩ : syracuseStep 404909 = 151841) (by norm_num)
theorem B306605 : Blo 179801 306605 := bbase (se 3 (by rfl) ⟨57488, by rfl⟩ : syracuseStep 306605 = 114977) (by norm_num)
theorem B1748405 : Blo 179801 1748405 := bbase (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) (by norm_num)
theorem B273845 : Blo 179801 273845 := bbase (se 5 (by rfl) ⟨12836, by rfl⟩ : syracuseStep 273845 = 25673) (by norm_num)
theorem B273869 : Blo 179801 273869 := bbase (se 3 (by rfl) ⟨51350, by rfl⟩ : syracuseStep 273869 = 102701) (by norm_num)
theorem B437717 : Blo 179801 437717 := bbase (se 7 (by rfl) ⟨5129, by rfl⟩ : syracuseStep 437717 = 10259) (by norm_num)
theorem B273893 : Blo 179801 273893 := bbase (se 4 (by rfl) ⟨25677, by rfl⟩ : syracuseStep 273893 = 51355) (by norm_num)
theorem B404981 : Blo 179801 404981 := bbase (se 5 (by rfl) ⟨18983, by rfl⟩ : syracuseStep 404981 = 37967) (by norm_num)
theorem B273917 : Blo 179801 273917 := bbase (se 3 (by rfl) ⟨51359, by rfl⟩ : syracuseStep 273917 = 102719) (by norm_num)
theorem B273941 : Blo 179801 273941 := bbase (se 6 (by rfl) ⟨6420, by rfl⟩ : syracuseStep 273941 = 12841) (by norm_num)
theorem B306733 : Blo 179801 306733 := bbase (se 3 (by rfl) ⟨57512, by rfl⟩ : syracuseStep 306733 = 115025) (by norm_num)
theorem B273965 : Blo 179801 273965 := bbase (se 3 (by rfl) ⟨51368, by rfl⟩ : syracuseStep 273965 = 102737) (by norm_num)
theorem B405053 : Blo 179801 405053 := bbase (se 3 (by rfl) ⟨75947, by rfl⟩ : syracuseStep 405053 = 151895) (by norm_num)
theorem B273989 : Blo 179801 273989 := bbase (se 4 (by rfl) ⟨25686, by rfl⟩ : syracuseStep 273989 = 51373) (by norm_num)
theorem B274013 : Blo 179801 274013 := bbase (se 3 (by rfl) ⟨51377, by rfl⟩ : syracuseStep 274013 = 102755) (by norm_num)
theorem B274037 : Blo 179801 274037 := bbase (se 5 (by rfl) ⟨12845, by rfl⟩ : syracuseStep 274037 = 25691) (by norm_num)
theorem B405125 : Blo 179801 405125 := bbase (se 4 (by rfl) ⟨37980, by rfl⟩ : syracuseStep 405125 = 75961) (by norm_num)
theorem B306821 : Blo 179801 306821 := bbase (se 4 (by rfl) ⟨28764, by rfl⟩ : syracuseStep 306821 = 57529) (by norm_num)
theorem B274061 : Blo 179801 274061 := bbase (se 3 (by rfl) ⟨51386, by rfl⟩ : syracuseStep 274061 = 102773) (by norm_num)
theorem B274085 : Blo 179801 274085 := bbase (se 4 (by rfl) ⟨25695, by rfl⟩ : syracuseStep 274085 = 51391) (by norm_num)
theorem B274109 : Blo 179801 274109 := bbase (se 3 (by rfl) ⟨51395, by rfl⟩ : syracuseStep 274109 = 102791) (by norm_num)
theorem B405197 : Blo 179801 405197 := bbase (se 3 (by rfl) ⟨75974, by rfl⟩ : syracuseStep 405197 = 151949) (by norm_num)
theorem B274133 : Blo 179801 274133 := bbase (se 7 (by rfl) ⟨3212, by rfl⟩ : syracuseStep 274133 = 6425) (by norm_num)
theorem B274157 : Blo 179801 274157 := bbase (se 3 (by rfl) ⟨51404, by rfl⟩ : syracuseStep 274157 = 102809) (by norm_num)
theorem B306949 : Blo 179801 306949 := bbase (se 4 (by rfl) ⟨28776, by rfl⟩ : syracuseStep 306949 = 57553) (by norm_num)
theorem B274181 : Blo 179801 274181 := bbase (se 4 (by rfl) ⟨25704, by rfl⟩ : syracuseStep 274181 = 51409) (by norm_num)
theorem B405269 : Blo 179801 405269 := bbase (se 6 (by rfl) ⟨9498, by rfl⟩ : syracuseStep 405269 = 18997) (by norm_num)
theorem B274205 : Blo 179801 274205 := bbase (se 3 (by rfl) ⟨51413, by rfl⟩ : syracuseStep 274205 = 102827) (by norm_num)
theorem B274229 : Blo 179801 274229 := bbase (se 5 (by rfl) ⟨12854, by rfl⟩ : syracuseStep 274229 = 25709) (by norm_num)
theorem B274253 : Blo 179801 274253 := bbase (se 3 (by rfl) ⟨51422, by rfl⟩ : syracuseStep 274253 = 102845) (by norm_num)
theorem B405341 : Blo 179801 405341 := bbase (se 3 (by rfl) ⟨76001, by rfl⟩ : syracuseStep 405341 = 152003) (by norm_num)
theorem B307037 : Blo 179801 307037 := bbase (se 3 (by rfl) ⟨57569, by rfl⟩ : syracuseStep 307037 = 115139) (by norm_num)
theorem B274277 : Blo 179801 274277 := bbase (se 4 (by rfl) ⟨25713, by rfl⟩ : syracuseStep 274277 = 51427) (by norm_num)
theorem B274301 : Blo 179801 274301 := bbase (se 3 (by rfl) ⟨51431, by rfl⟩ : syracuseStep 274301 = 102863) (by norm_num)
theorem B274325 : Blo 179801 274325 := bbase (se 6 (by rfl) ⟨6429, by rfl⟩ : syracuseStep 274325 = 12859) (by norm_num)
theorem B405413 : Blo 179801 405413 := bbase (se 4 (by rfl) ⟨38007, by rfl⟩ : syracuseStep 405413 = 76015) (by norm_num)
theorem B274349 : Blo 179801 274349 := bbase (se 3 (by rfl) ⟨51440, by rfl⟩ : syracuseStep 274349 = 102881) (by norm_num)
theorem B929717 : Blo 179801 929717 := bbase (se 5 (by rfl) ⟨43580, by rfl⟩ : syracuseStep 929717 = 87161) (by norm_num)
theorem B274373 : Blo 179801 274373 := bbase (se 4 (by rfl) ⟨25722, by rfl⟩ : syracuseStep 274373 = 51445) (by norm_num)
theorem B1388501 : Blo 179801 1388501 := bbase (se 7 (by rfl) ⟨16271, by rfl⟩ : syracuseStep 1388501 = 32543) (by norm_num)
theorem B307165 : Blo 179801 307165 := bbase (se 3 (by rfl) ⟨57593, by rfl⟩ : syracuseStep 307165 = 115187) (by norm_num)
theorem B274397 : Blo 179801 274397 := bbase (se 3 (by rfl) ⟨51449, by rfl⟩ : syracuseStep 274397 = 102899) (by norm_num)
theorem B405485 : Blo 179801 405485 := bbase (se 3 (by rfl) ⟨76028, by rfl⟩ : syracuseStep 405485 = 152057) (by norm_num)
theorem B1093621 : Blo 179801 1093621 := bbase (se 5 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 1093621 = 102527) (by norm_num)
theorem B274421 : Blo 179801 274421 := bbase (se 5 (by rfl) ⟨12863, by rfl⟩ : syracuseStep 274421 = 25727) (by norm_num)
theorem B274445 : Blo 179801 274445 := bbase (se 3 (by rfl) ⟨51458, by rfl⟩ : syracuseStep 274445 = 102917) (by norm_num)
theorem B274469 : Blo 179801 274469 := bbase (se 4 (by rfl) ⟨25731, by rfl⟩ : syracuseStep 274469 = 51463) (by norm_num)
theorem B405557 : Blo 179801 405557 := bbase (se 5 (by rfl) ⟨19010, by rfl⟩ : syracuseStep 405557 = 38021) (by norm_num)
theorem B307253 : Blo 179801 307253 := bbase (se 5 (by rfl) ⟨14402, by rfl⟩ : syracuseStep 307253 = 28805) (by norm_num)
theorem B274493 : Blo 179801 274493 := bbase (se 3 (by rfl) ⟨51467, by rfl⟩ : syracuseStep 274493 = 102935) (by norm_num)
theorem B274517 : Blo 179801 274517 := bbase (se 8 (by rfl) ⟨1608, by rfl⟩ : syracuseStep 274517 = 3217) (by norm_num)
theorem B274541 : Blo 179801 274541 := bbase (se 3 (by rfl) ⟨51476, by rfl⟩ : syracuseStep 274541 = 102953) (by norm_num)
theorem B405629 : Blo 179801 405629 := bbase (se 3 (by rfl) ⟨76055, by rfl⟩ : syracuseStep 405629 = 152111) (by norm_num)
theorem B274565 : Blo 179801 274565 := bbase (se 4 (by rfl) ⟨25740, by rfl⟩ : syracuseStep 274565 = 51481) (by norm_num)
theorem B274589 : Blo 179801 274589 := bbase (se 3 (by rfl) ⟨51485, by rfl⟩ : syracuseStep 274589 = 102971) (by norm_num)
theorem B307381 : Blo 179801 307381 := bbase (se 5 (by rfl) ⟨14408, by rfl⟩ : syracuseStep 307381 = 28817) (by norm_num)
theorem B274613 : Blo 179801 274613 := bbase (se 5 (by rfl) ⟨12872, by rfl⟩ : syracuseStep 274613 = 25745) (by norm_num)
theorem B405701 : Blo 179801 405701 := bbase (se 4 (by rfl) ⟨38034, by rfl⟩ : syracuseStep 405701 = 76069) (by norm_num)
theorem B274637 : Blo 179801 274637 := bbase (se 3 (by rfl) ⟨51494, by rfl⟩ : syracuseStep 274637 = 102989) (by norm_num)
theorem B274661 : Blo 179801 274661 := bbase (se 4 (by rfl) ⟨25749, by rfl⟩ : syracuseStep 274661 = 51499) (by norm_num)
theorem B274685 : Blo 179801 274685 := bbase (se 3 (by rfl) ⟨51503, by rfl⟩ : syracuseStep 274685 = 103007) (by norm_num)
theorem B405773 : Blo 179801 405773 := bbase (se 3 (by rfl) ⟨76082, by rfl⟩ : syracuseStep 405773 = 152165) (by norm_num)
theorem B307469 : Blo 179801 307469 := bbase (se 3 (by rfl) ⟨57650, by rfl⟩ : syracuseStep 307469 = 115301) (by norm_num)
theorem B274709 : Blo 179801 274709 := bbase (se 6 (by rfl) ⟨6438, by rfl⟩ : syracuseStep 274709 = 12877) (by norm_num)
theorem B274733 : Blo 179801 274733 := bbase (se 3 (by rfl) ⟨51512, by rfl⟩ : syracuseStep 274733 = 103025) (by norm_num)
theorem B274757 : Blo 179801 274757 := bbase (se 4 (by rfl) ⟨25758, by rfl⟩ : syracuseStep 274757 = 51517) (by norm_num)
theorem B405845 : Blo 179801 405845 := bbase (se 10 (by rfl) ⟨594, by rfl⟩ : syracuseStep 405845 = 1189) (by norm_num)
theorem B274781 : Blo 179801 274781 := bbase (se 3 (by rfl) ⟨51521, by rfl⟩ : syracuseStep 274781 = 103043) (by norm_num)
theorem B274805 : Blo 179801 274805 := bbase (se 5 (by rfl) ⟨12881, by rfl⟩ : syracuseStep 274805 = 25763) (by norm_num)
theorem B307597 : Blo 179801 307597 := bbase (se 3 (by rfl) ⟨57674, by rfl⟩ : syracuseStep 307597 = 115349) (by norm_num)
theorem B274829 : Blo 179801 274829 := bbase (se 3 (by rfl) ⟨51530, by rfl⟩ : syracuseStep 274829 = 103061) (by norm_num)
theorem B405917 : Blo 179801 405917 := bbase (se 3 (by rfl) ⟨76109, by rfl⟩ : syracuseStep 405917 = 152219) (by norm_num)
theorem B307621 : Blo 179801 307621 := bbase (se 4 (by rfl) ⟨28839, by rfl⟩ : syracuseStep 307621 = 57679) (by norm_num)
theorem B274853 : Blo 179801 274853 := bbase (se 4 (by rfl) ⟨25767, by rfl⟩ : syracuseStep 274853 = 51535) (by norm_num)
theorem B274877 : Blo 179801 274877 := bbase (se 3 (by rfl) ⟨51539, by rfl⟩ : syracuseStep 274877 = 103079) (by norm_num)
theorem B274901 : Blo 179801 274901 := bbase (se 7 (by rfl) ⟨3221, by rfl⟩ : syracuseStep 274901 = 6443) (by norm_num)
theorem B405989 : Blo 179801 405989 := bbase (se 4 (by rfl) ⟨38061, by rfl⟩ : syracuseStep 405989 = 76123) (by norm_num)
theorem B307685 : Blo 179801 307685 := bbase (se 4 (by rfl) ⟨28845, by rfl⟩ : syracuseStep 307685 = 57691) (by norm_num)
theorem B274925 : Blo 179801 274925 := bbase (se 3 (by rfl) ⟨51548, by rfl⟩ : syracuseStep 274925 = 103097) (by norm_num)
theorem B274949 : Blo 179801 274949 := bbase (se 4 (by rfl) ⟨25776, by rfl⟩ : syracuseStep 274949 = 51553) (by norm_num)
theorem B274973 : Blo 179801 274973 := bbase (se 3 (by rfl) ⟨51557, by rfl⟩ : syracuseStep 274973 = 103115) (by norm_num)
theorem B406061 : Blo 179801 406061 := bbase (se 3 (by rfl) ⟨76136, by rfl⟩ : syracuseStep 406061 = 152273) (by norm_num)
theorem B274997 : Blo 179801 274997 := bbase (se 5 (by rfl) ⟨12890, by rfl⟩ : syracuseStep 274997 = 25781) (by norm_num)
theorem B1487413 : Blo 179801 1487413 := bbase (se 5 (by rfl) ⟨69722, by rfl⟩ : syracuseStep 1487413 = 139445) (by norm_num)
theorem B275021 : Blo 179801 275021 := bbase (se 3 (by rfl) ⟨51566, by rfl⟩ : syracuseStep 275021 = 103133) (by norm_num)
theorem B307813 : Blo 179801 307813 := bbase (se 4 (by rfl) ⟨28857, by rfl⟩ : syracuseStep 307813 = 57715) (by norm_num)
theorem B275045 : Blo 179801 275045 := bbase (se 4 (by rfl) ⟨25785, by rfl⟩ : syracuseStep 275045 = 51571) (by norm_num)
theorem B406133 : Blo 179801 406133 := bbase (se 5 (by rfl) ⟨19037, by rfl⟩ : syracuseStep 406133 = 38075) (by norm_num)
theorem B275069 : Blo 179801 275069 := bbase (se 3 (by rfl) ⟨51575, by rfl⟩ : syracuseStep 275069 = 103151) (by norm_num)
theorem B209533 : Blo 179801 209533 := bbase (se 3 (by rfl) ⟨39287, by rfl⟩ : syracuseStep 209533 = 78575) (by norm_num)
theorem B275093 : Blo 179801 275093 := bbase (se 6 (by rfl) ⟨6447, by rfl⟩ : syracuseStep 275093 = 12895) (by norm_num)
theorem B275117 : Blo 179801 275117 := bbase (se 3 (by rfl) ⟨51584, by rfl⟩ : syracuseStep 275117 = 103169) (by norm_num)
theorem B406205 : Blo 179801 406205 := bbase (se 3 (by rfl) ⟨76163, by rfl⟩ : syracuseStep 406205 = 152327) (by norm_num)
theorem B307901 : Blo 179801 307901 := bbase (se 3 (by rfl) ⟨57731, by rfl⟩ : syracuseStep 307901 = 115463) (by norm_num)
theorem B275141 : Blo 179801 275141 := bbase (se 4 (by rfl) ⟨25794, by rfl⟩ : syracuseStep 275141 = 51589) (by norm_num)
theorem B275165 : Blo 179801 275165 := bbase (se 3 (by rfl) ⟨51593, by rfl⟩ : syracuseStep 275165 = 103187) (by norm_num)
theorem B701173 : Blo 179801 701173 := bbase (se 5 (by rfl) ⟨32867, by rfl⟩ : syracuseStep 701173 = 65735) (by norm_num)
theorem B275189 : Blo 179801 275189 := bbase (se 5 (by rfl) ⟨12899, by rfl⟩ : syracuseStep 275189 = 25799) (by norm_num)
theorem B406277 : Blo 179801 406277 := bbase (se 4 (by rfl) ⟨38088, by rfl⟩ : syracuseStep 406277 = 76177) (by norm_num)
theorem B275213 : Blo 179801 275213 := bbase (se 3 (by rfl) ⟨51602, by rfl⟩ : syracuseStep 275213 = 103205) (by norm_num)
theorem B275237 : Blo 179801 275237 := bbase (se 4 (by rfl) ⟨25803, by rfl⟩ : syracuseStep 275237 = 51607) (by norm_num)
theorem B308029 : Blo 179801 308029 := bbase (se 3 (by rfl) ⟨57755, by rfl⟩ : syracuseStep 308029 = 115511) (by norm_num)
theorem B275261 : Blo 179801 275261 := bbase (se 3 (by rfl) ⟨51611, by rfl⟩ : syracuseStep 275261 = 103223) (by norm_num)
theorem B406349 : Blo 179801 406349 := bbase (se 3 (by rfl) ⟨76190, by rfl⟩ : syracuseStep 406349 = 152381) (by norm_num)
theorem B8926037 : Blo 179801 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B275285 : Blo 179801 275285 := bbase (se 9 (by rfl) ⟨806, by rfl⟩ : syracuseStep 275285 = 1613) (by norm_num)
theorem B275309 : Blo 179801 275309 := bbase (se 3 (by rfl) ⟨51620, by rfl⟩ : syracuseStep 275309 = 103241) (by norm_num)
theorem B275333 : Blo 179801 275333 := bbase (se 4 (by rfl) ⟨25812, by rfl⟩ : syracuseStep 275333 = 51625) (by norm_num)
theorem B406421 : Blo 179801 406421 := bbase (se 6 (by rfl) ⟨9525, by rfl⟩ : syracuseStep 406421 = 19051) (by norm_num)
theorem B308117 : Blo 179801 308117 := bbase (se 6 (by rfl) ⟨7221, by rfl⟩ : syracuseStep 308117 = 14443) (by norm_num)
theorem B275357 : Blo 179801 275357 := bbase (se 3 (by rfl) ⟨51629, by rfl⟩ : syracuseStep 275357 = 103259) (by norm_num)
theorem B275381 : Blo 179801 275381 := bbase (se 5 (by rfl) ⟨12908, by rfl⟩ : syracuseStep 275381 = 25817) (by norm_num)
theorem B275405 : Blo 179801 275405 := bbase (se 3 (by rfl) ⟨51638, by rfl⟩ : syracuseStep 275405 = 103277) (by norm_num)
theorem B406493 : Blo 179801 406493 := bbase (se 3 (by rfl) ⟨76217, by rfl⟩ : syracuseStep 406493 = 152435) (by norm_num)
theorem B275429 : Blo 179801 275429 := bbase (se 4 (by rfl) ⟨25821, by rfl⟩ : syracuseStep 275429 = 51643) (by norm_num)
theorem B275437 : Blo 179801 275437 := bbase (se 3 (by rfl) ⟨51644, by rfl⟩ : syracuseStep 275437 = 103289) (by norm_num)
theorem B275453 : Blo 179801 275453 := bbase (se 3 (by rfl) ⟨51647, by rfl⟩ : syracuseStep 275453 = 103295) (by norm_num)
theorem B308245 : Blo 179801 308245 := bbase (se 6 (by rfl) ⟨7224, by rfl⟩ : syracuseStep 308245 = 14449) (by norm_num)
theorem B275477 : Blo 179801 275477 := bbase (se 6 (by rfl) ⟨6456, by rfl⟩ : syracuseStep 275477 = 12913) (by norm_num)
theorem B406565 : Blo 179801 406565 := bbase (se 4 (by rfl) ⟨38115, by rfl⟩ : syracuseStep 406565 = 76231) (by norm_num)
theorem B275501 : Blo 179801 275501 := bbase (se 3 (by rfl) ⟨51656, by rfl⟩ : syracuseStep 275501 = 103313) (by norm_num)
theorem B275525 : Blo 179801 275525 := bbase (se 4 (by rfl) ⟨25830, by rfl⟩ : syracuseStep 275525 = 51661) (by norm_num)
theorem B275549 : Blo 179801 275549 := bbase (se 3 (by rfl) ⟨51665, by rfl⟩ : syracuseStep 275549 = 103331) (by norm_num)
theorem B406637 : Blo 179801 406637 := bbase (se 3 (by rfl) ⟨76244, by rfl⟩ : syracuseStep 406637 = 152489) (by norm_num)
theorem B308333 : Blo 179801 308333 := bbase (se 3 (by rfl) ⟨57812, by rfl⟩ : syracuseStep 308333 = 115625) (by norm_num)
theorem B275573 : Blo 179801 275573 := bbase (se 5 (by rfl) ⟨12917, by rfl⟩ : syracuseStep 275573 = 25835) (by norm_num)
theorem B275597 : Blo 179801 275597 := bbase (se 3 (by rfl) ⟨51674, by rfl⟩ : syracuseStep 275597 = 103349) (by norm_num)
theorem B275621 : Blo 179801 275621 := bbase (se 4 (by rfl) ⟨25839, by rfl⟩ : syracuseStep 275621 = 51679) (by norm_num)
theorem B406709 : Blo 179801 406709 := bbase (se 5 (by rfl) ⟨19064, by rfl⟩ : syracuseStep 406709 = 38129) (by norm_num)
theorem B275645 : Blo 179801 275645 := bbase (se 3 (by rfl) ⟨51683, by rfl⟩ : syracuseStep 275645 = 103367) (by norm_num)
theorem B275669 : Blo 179801 275669 := bbase (se 7 (by rfl) ⟨3230, by rfl⟩ : syracuseStep 275669 = 6461) (by norm_num)
theorem B308461 : Blo 179801 308461 := bbase (se 3 (by rfl) ⟨57836, by rfl⟩ : syracuseStep 308461 = 115673) (by norm_num)
theorem B275693 : Blo 179801 275693 := bbase (se 3 (by rfl) ⟨51692, by rfl⟩ : syracuseStep 275693 = 103385) (by norm_num)
theorem B406781 : Blo 179801 406781 := bbase (se 3 (by rfl) ⟨76271, by rfl⟩ : syracuseStep 406781 = 152543) (by norm_num)
theorem B275741 : Blo 179801 275741 := bbase (se 3 (by rfl) ⟨51701, by rfl⟩ : syracuseStep 275741 = 103403) (by norm_num)
theorem B406853 : Blo 179801 406853 := bbase (se 4 (by rfl) ⟨38142, by rfl⟩ : syracuseStep 406853 = 76285) (by norm_num)
theorem B308549 : Blo 179801 308549 := bbase (se 4 (by rfl) ⟨28926, by rfl⟩ : syracuseStep 308549 = 57853) (by norm_num)
theorem B406925 : Blo 179801 406925 := bbase (se 3 (by rfl) ⟨76298, by rfl⟩ : syracuseStep 406925 = 152597) (by norm_num)
theorem B308677 : Blo 179801 308677 := bbase (se 4 (by rfl) ⟨28938, by rfl⟩ : syracuseStep 308677 = 57877) (by norm_num)
theorem B406997 : Blo 179801 406997 := bbase (se 7 (by rfl) ⟨4769, by rfl⟩ : syracuseStep 406997 = 9539) (by norm_num)
theorem B407069 : Blo 179801 407069 := bbase (se 3 (by rfl) ⟨76325, by rfl⟩ : syracuseStep 407069 = 152651) (by norm_num)
theorem B308765 : Blo 179801 308765 := bbase (se 3 (by rfl) ⟨57893, by rfl⟩ : syracuseStep 308765 = 115787) (by norm_num)
theorem B341597 : Blo 179801 341597 := bbase (se 3 (by rfl) ⟨64049, by rfl⟩ : syracuseStep 341597 = 128099) (by norm_num)
theorem B407141 : Blo 179801 407141 := bbase (se 4 (by rfl) ⟨38169, by rfl⟩ : syracuseStep 407141 = 76339) (by norm_num)
theorem B308893 : Blo 179801 308893 := bbase (se 3 (by rfl) ⟨57917, by rfl⟩ : syracuseStep 308893 = 115835) (by norm_num)
theorem B407213 : Blo 179801 407213 := bbase (se 3 (by rfl) ⟨76352, by rfl⟩ : syracuseStep 407213 = 152705) (by norm_num)
theorem B341749 : Blo 179801 341749 := bbase (se 5 (by rfl) ⟨16019, by rfl⟩ : syracuseStep 341749 = 32039) (by norm_num)
theorem B407285 : Blo 179801 407285 := bbase (se 5 (by rfl) ⟨19091, by rfl⟩ : syracuseStep 407285 = 38183) (by norm_num)
theorem B308981 : Blo 179801 308981 := bbase (se 5 (by rfl) ⟨14483, by rfl⟩ : syracuseStep 308981 = 28967) (by norm_num)
theorem B1029941 : Blo 179801 1029941 := bbase (se 5 (by rfl) ⟨48278, by rfl⟩ : syracuseStep 1029941 = 96557) (by norm_num)
theorem B407357 : Blo 179801 407357 := bbase (se 3 (by rfl) ⟨76379, by rfl⟩ : syracuseStep 407357 = 152759) (by norm_num)
theorem B309109 : Blo 179801 309109 := bbase (se 5 (by rfl) ⟨14489, by rfl⟩ : syracuseStep 309109 = 28979) (by norm_num)
theorem B407429 : Blo 179801 407429 := bbase (se 4 (by rfl) ⟨38196, by rfl⟩ : syracuseStep 407429 = 76393) (by norm_num)
theorem B407501 : Blo 179801 407501 := bbase (se 3 (by rfl) ⟨76406, by rfl⟩ : syracuseStep 407501 = 152813) (by norm_num)
theorem B309197 : Blo 179801 309197 := bbase (se 3 (by rfl) ⟨57974, by rfl⟩ : syracuseStep 309197 = 115949) (by norm_num)
theorem B407573 : Blo 179801 407573 := bbase (se 6 (by rfl) ⟨9552, by rfl⟩ : syracuseStep 407573 = 19105) (by norm_num)
theorem B342053 : Blo 179801 342053 := bbase (se 4 (by rfl) ⟨32067, by rfl⟩ : syracuseStep 342053 = 64135) (by norm_num)
theorem B309325 : Blo 179801 309325 := bbase (se 3 (by rfl) ⟨57998, by rfl⟩ : syracuseStep 309325 = 115997) (by norm_num)
theorem B407645 : Blo 179801 407645 := bbase (se 3 (by rfl) ⟨76433, by rfl⟩ : syracuseStep 407645 = 152867) (by norm_num)
theorem B407717 : Blo 179801 407717 := bbase (se 4 (by rfl) ⟨38223, by rfl⟩ : syracuseStep 407717 = 76447) (by norm_num)
theorem B309413 : Blo 179801 309413 := bbase (se 4 (by rfl) ⟨29007, by rfl⟩ : syracuseStep 309413 = 58015) (by norm_num)
theorem B407789 : Blo 179801 407789 := bbase (se 3 (by rfl) ⟨76460, by rfl⟩ : syracuseStep 407789 = 152921) (by norm_num)
theorem B375053 : Blo 179801 375053 := bbase (se 3 (by rfl) ⟨70322, by rfl⟩ : syracuseStep 375053 = 140645) (by norm_num)
theorem B833813 : Blo 179801 833813 := bbase (se 6 (by rfl) ⟨19542, by rfl⟩ : syracuseStep 833813 = 39085) (by norm_num)
theorem B309541 : Blo 179801 309541 := bbase (se 4 (by rfl) ⟨29019, by rfl⟩ : syracuseStep 309541 = 58039) (by norm_num)
theorem B407861 : Blo 179801 407861 := bbase (se 5 (by rfl) ⟨19118, by rfl⟩ : syracuseStep 407861 = 38237) (by norm_num)
theorem B440677 : Blo 179801 440677 := bbase (se 4 (by rfl) ⟨41313, by rfl⟩ : syracuseStep 440677 = 82627) (by norm_num)
theorem B407933 : Blo 179801 407933 := bbase (se 3 (by rfl) ⟨76487, by rfl⟩ : syracuseStep 407933 = 152975) (by norm_num)
theorem B309629 : Blo 179801 309629 := bbase (se 3 (by rfl) ⟨58055, by rfl⟩ : syracuseStep 309629 = 116111) (by norm_num)
theorem B440749 : Blo 179801 440749 := bbase (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) (by norm_num)
theorem B408005 : Blo 179801 408005 := bbase (se 4 (by rfl) ⟨38250, by rfl⟩ : syracuseStep 408005 = 76501) (by norm_num)
theorem B309757 : Blo 179801 309757 := bbase (se 3 (by rfl) ⟨58079, by rfl⟩ : syracuseStep 309757 = 116159) (by norm_num)
theorem B408077 : Blo 179801 408077 := bbase (se 3 (by rfl) ⟨76514, by rfl⟩ : syracuseStep 408077 = 153029) (by norm_num)
theorem B440869 : Blo 179801 440869 := bbase (se 4 (by rfl) ⟨41331, by rfl⟩ : syracuseStep 440869 = 82663) (by norm_num)
theorem B440909 : Blo 179801 440909 := bbase (se 3 (by rfl) ⟨82670, by rfl⟩ : syracuseStep 440909 = 165341) (by norm_num)
theorem B408149 : Blo 179801 408149 := bbase (se 8 (by rfl) ⟨2391, by rfl⟩ : syracuseStep 408149 = 4783) (by norm_num)
theorem B309845 : Blo 179801 309845 := bbase (se 8 (by rfl) ⟨1815, by rfl⟩ : syracuseStep 309845 = 3631) (by norm_num)
theorem B768629 : Blo 179801 768629 := bbase (se 5 (by rfl) ⟨36029, by rfl⟩ : syracuseStep 768629 = 72059) (by norm_num)
theorem B408221 : Blo 179801 408221 := bbase (se 3 (by rfl) ⟨76541, by rfl⟩ : syracuseStep 408221 = 153083) (by norm_num)
theorem B309973 : Blo 179801 309973 := bbase (se 7 (by rfl) ⟨3632, by rfl⟩ : syracuseStep 309973 = 7265) (by norm_num)
theorem B408293 : Blo 179801 408293 := bbase (se 4 (by rfl) ⟨38277, by rfl⟩ : syracuseStep 408293 = 76555) (by norm_num)
theorem B342805 : Blo 179801 342805 := bbase (se 6 (by rfl) ⟨8034, by rfl⟩ : syracuseStep 342805 = 16069) (by norm_num)
theorem B408365 : Blo 179801 408365 := bbase (se 3 (by rfl) ⟨76568, by rfl⟩ : syracuseStep 408365 = 153137) (by norm_num)
theorem B310061 : Blo 179801 310061 := bbase (se 3 (by rfl) ⟨58136, by rfl⟩ : syracuseStep 310061 = 116273) (by norm_num)
theorem B441197 : Blo 179801 441197 := bbase (se 3 (by rfl) ⟨82724, by rfl⟩ : syracuseStep 441197 = 165449) (by norm_num)
theorem B408437 : Blo 179801 408437 := bbase (se 5 (by rfl) ⟨19145, by rfl⟩ : syracuseStep 408437 = 38291) (by norm_num)
theorem B342949 : Blo 179801 342949 := bbase (se 4 (by rfl) ⟨32151, by rfl⟩ : syracuseStep 342949 = 64303) (by norm_num)
theorem B408509 : Blo 179801 408509 := bbase (se 3 (by rfl) ⟨76595, by rfl⟩ : syracuseStep 408509 = 153191) (by norm_num)
theorem B1653749 : Blo 179801 1653749 := bbase (se 5 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 1653749 = 155039) (by norm_num)
theorem B703477 : Blo 179801 703477 := bbase (se 5 (by rfl) ⟨32975, by rfl⟩ : syracuseStep 703477 = 65951) (by norm_num)
theorem B408581 : Blo 179801 408581 := bbase (se 4 (by rfl) ⟨38304, by rfl⟩ : syracuseStep 408581 = 76609) (by norm_num)
theorem B343109 : Blo 179801 343109 := bbase (se 4 (by rfl) ⟨32166, by rfl⟩ : syracuseStep 343109 = 64333) (by norm_num)
theorem B408653 : Blo 179801 408653 := bbase (se 3 (by rfl) ⟨76622, by rfl⟩ : syracuseStep 408653 = 153245) (by norm_num)
theorem B408725 : Blo 179801 408725 := bbase (se 6 (by rfl) ⟨9579, by rfl⟩ : syracuseStep 408725 = 19159) (by norm_num)
theorem B343253 : Blo 179801 343253 := bbase (se 7 (by rfl) ⟨4022, by rfl⟩ : syracuseStep 343253 = 8045) (by norm_num)
theorem B408797 : Blo 179801 408797 := bbase (se 3 (by rfl) ⟨76649, by rfl⟩ : syracuseStep 408797 = 153299) (by norm_num)
theorem B408869 : Blo 179801 408869 := bbase (se 4 (by rfl) ⟨38331, by rfl⟩ : syracuseStep 408869 = 76663) (by norm_num)
theorem B408941 : Blo 179801 408941 := bbase (se 3 (by rfl) ⟨76676, by rfl⟩ : syracuseStep 408941 = 153353) (by norm_num)
theorem B409013 : Blo 179801 409013 := bbase (se 5 (by rfl) ⟨19172, by rfl⟩ : syracuseStep 409013 = 38345) (by norm_num)
theorem B343541 : Blo 179801 343541 := bbase (se 5 (by rfl) ⟨16103, by rfl⟩ : syracuseStep 343541 = 32207) (by norm_num)
theorem B409085 : Blo 179801 409085 := bbase (se 3 (by rfl) ⟨76703, by rfl⟩ : syracuseStep 409085 = 153407) (by norm_num)
theorem B409157 : Blo 179801 409157 := bbase (se 4 (by rfl) ⟨38358, by rfl⟩ : syracuseStep 409157 = 76717) (by norm_num)
theorem B343693 : Blo 179801 343693 := bbase (se 3 (by rfl) ⟨64442, by rfl⟩ : syracuseStep 343693 = 128885) (by norm_num)
theorem B409229 : Blo 179801 409229 := bbase (se 3 (by rfl) ⟨76730, by rfl⟩ : syracuseStep 409229 = 153461) (by norm_num)
theorem B442013 : Blo 179801 442013 := bbase (se 3 (by rfl) ⟨82877, by rfl⟩ : syracuseStep 442013 = 165755) (by norm_num)
theorem B409301 : Blo 179801 409301 := bbase (se 7 (by rfl) ⟨4796, by rfl⟩ : syracuseStep 409301 = 9593) (by norm_num)
theorem B409373 : Blo 179801 409373 := bbase (se 3 (by rfl) ⟨76757, by rfl⟩ : syracuseStep 409373 = 153515) (by norm_num)
theorem B409445 : Blo 179801 409445 := bbase (se 4 (by rfl) ⟨38385, by rfl⟩ : syracuseStep 409445 = 76771) (by norm_num)
theorem B376741 : Blo 179801 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B409517 : Blo 179801 409517 := bbase (se 3 (by rfl) ⟨76784, by rfl⟩ : syracuseStep 409517 = 153569) (by norm_num)
theorem B343997 : Blo 179801 343997 := bbase (se 3 (by rfl) ⟨64499, by rfl⟩ : syracuseStep 343997 = 128999) (by norm_num)
theorem B409589 : Blo 179801 409589 := bbase (se 5 (by rfl) ⟨19199, by rfl⟩ : syracuseStep 409589 = 38399) (by norm_num)
theorem B409661 : Blo 179801 409661 := bbase (se 3 (by rfl) ⟨76811, by rfl⟩ : syracuseStep 409661 = 153623) (by norm_num)
theorem B1556597 : Blo 179801 1556597 := bbase (se 5 (by rfl) ⟨72965, by rfl⟩ : syracuseStep 1556597 = 145931) (by norm_num)
theorem B409733 : Blo 179801 409733 := bbase (se 4 (by rfl) ⟨38412, by rfl⟩ : syracuseStep 409733 = 76825) (by norm_num)
theorem B409805 : Blo 179801 409805 := bbase (se 3 (by rfl) ⟨76838, by rfl⟩ : syracuseStep 409805 = 153677) (by norm_num)
theorem B409877 : Blo 179801 409877 := bbase (se 6 (by rfl) ⟨9606, by rfl⟩ : syracuseStep 409877 = 19213) (by norm_num)
theorem B1163605 : Blo 179801 1163605 := bbase (se 10 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 1163605 = 3409) (by norm_num)
theorem B409949 : Blo 179801 409949 := bbase (se 3 (by rfl) ⟨76865, by rfl⟩ : syracuseStep 409949 = 153731) (by norm_num)
theorem B246125 : Blo 179801 246125 := bbase (se 3 (by rfl) ⟨46148, by rfl⟩ : syracuseStep 246125 = 92297) (by norm_num)
theorem B410021 : Blo 179801 410021 := bbase (se 4 (by rfl) ⟨38439, by rfl⟩ : syracuseStep 410021 = 76879) (by norm_num)
theorem B410093 : Blo 179801 410093 := bbase (se 3 (by rfl) ⟨76892, by rfl⟩ : syracuseStep 410093 = 153785) (by norm_num)
theorem B410165 : Blo 179801 410165 := bbase (se 5 (by rfl) ⟨19226, by rfl⟩ : syracuseStep 410165 = 38453) (by norm_num)
theorem B410237 : Blo 179801 410237 := bbase (se 3 (by rfl) ⟨76919, by rfl⟩ : syracuseStep 410237 = 153839) (by norm_num)
theorem B344749 : Blo 179801 344749 := bbase (se 3 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 344749 = 129281) (by norm_num)
theorem B410309 : Blo 179801 410309 := bbase (se 4 (by rfl) ⟨38466, by rfl⟩ : syracuseStep 410309 = 76933) (by norm_num)
theorem B410381 : Blo 179801 410381 := bbase (se 3 (by rfl) ⟨76946, by rfl⟩ : syracuseStep 410381 = 153893) (by norm_num)
theorem B607013 : Blo 179801 607013 := bbase (se 4 (by rfl) ⟨56907, by rfl⟩ : syracuseStep 607013 = 113815) (by norm_num)
theorem B344893 : Blo 179801 344893 := bbase (se 3 (by rfl) ⟨64667, by rfl⟩ : syracuseStep 344893 = 129335) (by norm_num)
theorem B410453 : Blo 179801 410453 := bbase (se 9 (by rfl) ⟨1202, by rfl⟩ : syracuseStep 410453 = 2405) (by norm_num)
theorem B410525 : Blo 179801 410525 := bbase (se 3 (by rfl) ⟨76973, by rfl⟩ : syracuseStep 410525 = 153947) (by norm_num)
theorem B345053 : Blo 179801 345053 := bbase (se 3 (by rfl) ⟨64697, by rfl⟩ : syracuseStep 345053 = 129395) (by norm_num)
theorem B410597 : Blo 179801 410597 := bbase (se 4 (by rfl) ⟨38493, by rfl⟩ : syracuseStep 410597 = 76987) (by norm_num)
theorem B410669 : Blo 179801 410669 := bbase (se 3 (by rfl) ⟨77000, by rfl⟩ : syracuseStep 410669 = 154001) (by norm_num)
theorem B345197 : Blo 179801 345197 := bbase (se 3 (by rfl) ⟨64724, by rfl⟩ : syracuseStep 345197 = 129449) (by norm_num)
theorem B410741 : Blo 179801 410741 := bbase (se 5 (by rfl) ⟨19253, by rfl⟩ : syracuseStep 410741 = 38507) (by norm_num)
theorem B279733 : Blo 179801 279733 := bbase (se 5 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 279733 = 26225) (by norm_num)
theorem B410813 : Blo 179801 410813 := bbase (se 3 (by rfl) ⟨77027, by rfl⟩ : syracuseStep 410813 = 154055) (by norm_num)
theorem B607445 : Blo 179801 607445 := bbase (se 7 (by rfl) ⟨7118, by rfl⟩ : syracuseStep 607445 = 14237) (by norm_num)
theorem B410885 : Blo 179801 410885 := bbase (se 4 (by rfl) ⟨38520, by rfl⟩ : syracuseStep 410885 = 77041) (by norm_num)
theorem B410957 : Blo 179801 410957 := bbase (se 3 (by rfl) ⟨77054, by rfl⟩ : syracuseStep 410957 = 154109) (by norm_num)
theorem B345485 : Blo 179801 345485 := bbase (se 3 (by rfl) ⟨64778, by rfl⟩ : syracuseStep 345485 = 129557) (by norm_num)
theorem B411029 : Blo 179801 411029 := bbase (se 6 (by rfl) ⟨9633, by rfl⟩ : syracuseStep 411029 = 19267) (by norm_num)
theorem B411101 : Blo 179801 411101 := bbase (se 3 (by rfl) ⟨77081, by rfl⟩ : syracuseStep 411101 = 154163) (by norm_num)
theorem B411149 : Blo 179801 411149 := bbase (se 3 (by rfl) ⟨77090, by rfl⟩ : syracuseStep 411149 = 154181) (by norm_num)
theorem B345637 : Blo 179801 345637 := bbase (se 4 (by rfl) ⟨32403, by rfl⟩ : syracuseStep 345637 = 64807) (by norm_num)
theorem B411173 : Blo 179801 411173 := bbase (se 4 (by rfl) ⟨38547, by rfl⟩ : syracuseStep 411173 = 77095) (by norm_num)
theorem B411245 : Blo 179801 411245 := bbase (se 3 (by rfl) ⟨77108, by rfl⟩ : syracuseStep 411245 = 154217) (by norm_num)
theorem B607877 : Blo 179801 607877 := bbase (se 4 (by rfl) ⟨56988, by rfl⟩ : syracuseStep 607877 = 113977) (by norm_num)
theorem B411317 : Blo 179801 411317 := bbase (se 5 (by rfl) ⟨19280, by rfl⟩ : syracuseStep 411317 = 38561) (by norm_num)
theorem B411389 : Blo 179801 411389 := bbase (se 3 (by rfl) ⟨77135, by rfl⟩ : syracuseStep 411389 = 154271) (by norm_num)
theorem B411461 : Blo 179801 411461 := bbase (se 4 (by rfl) ⟨38574, by rfl⟩ : syracuseStep 411461 = 77149) (by norm_num)
theorem B345941 : Blo 179801 345941 := bbase (se 9 (by rfl) ⟨1013, by rfl⟩ : syracuseStep 345941 = 2027) (by norm_num)
theorem B411533 : Blo 179801 411533 := bbase (se 3 (by rfl) ⟨77162, by rfl⟩ : syracuseStep 411533 = 154325) (by norm_num)
theorem B411605 : Blo 179801 411605 := bbase (se 7 (by rfl) ⟨4823, by rfl⟩ : syracuseStep 411605 = 9647) (by norm_num)
theorem B411677 : Blo 179801 411677 := bbase (se 3 (by rfl) ⟨77189, by rfl⟩ : syracuseStep 411677 = 154379) (by norm_num)
theorem B608309 : Blo 179801 608309 := bbase (se 5 (by rfl) ⟨28514, by rfl⟩ : syracuseStep 608309 = 57029) (by norm_num)
theorem B804917 : Blo 179801 804917 := bbase (se 5 (by rfl) ⟨37730, by rfl⟩ : syracuseStep 804917 = 75461) (by norm_num)
theorem B411749 : Blo 179801 411749 := bbase (se 4 (by rfl) ⟨38601, by rfl⟩ : syracuseStep 411749 = 77203) (by norm_num)
theorem B411821 : Blo 179801 411821 := bbase (se 3 (by rfl) ⟨77216, by rfl⟩ : syracuseStep 411821 = 154433) (by norm_num)
theorem B411893 : Blo 179801 411893 := bbase (se 5 (by rfl) ⟨19307, by rfl⟩ : syracuseStep 411893 = 38615) (by norm_num)
theorem B411965 : Blo 179801 411965 := bbase (se 3 (by rfl) ⟨77243, by rfl⟩ : syracuseStep 411965 = 154487) (by norm_num)
theorem B248141 : Blo 179801 248141 := bbase (se 3 (by rfl) ⟨46526, by rfl⟩ : syracuseStep 248141 = 93053) (by norm_num)
theorem B412037 : Blo 179801 412037 := bbase (se 4 (by rfl) ⟨38628, by rfl⟩ : syracuseStep 412037 = 77257) (by norm_num)
theorem B870821 : Blo 179801 870821 := bbase (se 4 (by rfl) ⟨81639, by rfl⟩ : syracuseStep 870821 = 163279) (by norm_num)
theorem B412109 : Blo 179801 412109 := bbase (se 3 (by rfl) ⟨77270, by rfl⟩ : syracuseStep 412109 = 154541) (by norm_num)
theorem B608741 : Blo 179801 608741 := bbase (se 4 (by rfl) ⟨57069, by rfl⟩ : syracuseStep 608741 = 114139) (by norm_num)
theorem B182777 : Blo 179801 182777 := bbase (se 2 (by rfl) ⟨68541, by rfl⟩ : syracuseStep 182777 = 137083) (by norm_num)
theorem B412181 : Blo 179801 412181 := bbase (se 6 (by rfl) ⟨9660, by rfl⟩ : syracuseStep 412181 = 19321) (by norm_num)
theorem B346693 : Blo 179801 346693 := bbase (se 4 (by rfl) ⟨32502, by rfl⟩ : syracuseStep 346693 = 65005) (by norm_num)
theorem B2345557 : Blo 179801 2345557 := bbase (se 8 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 2345557 = 27487) (by norm_num)
theorem B412253 : Blo 179801 412253 := bbase (se 3 (by rfl) ⟨77297, by rfl⟩ : syracuseStep 412253 = 154595) (by norm_num)
theorem B1493653 : Blo 179801 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B412325 : Blo 179801 412325 := bbase (se 4 (by rfl) ⟨38655, by rfl⟩ : syracuseStep 412325 = 77311) (by norm_num)
theorem B346837 : Blo 179801 346837 := bbase (se 7 (by rfl) ⟨4064, by rfl⟩ : syracuseStep 346837 = 8129) (by norm_num)
theorem B576229 : Blo 179801 576229 := bbase (se 4 (by rfl) ⟨54021, by rfl⟩ : syracuseStep 576229 = 108043) (by norm_num)
theorem B412397 : Blo 179801 412397 := bbase (se 3 (by rfl) ⟨77324, by rfl⟩ : syracuseStep 412397 = 154649) (by norm_num)
theorem B772901 : Blo 179801 772901 := bbase (se 4 (by rfl) ⟨72459, by rfl⟩ : syracuseStep 772901 = 144919) (by norm_num)
theorem B412469 : Blo 179801 412469 := bbase (se 5 (by rfl) ⟨19334, by rfl⟩ : syracuseStep 412469 = 38669) (by norm_num)
theorem B346997 : Blo 179801 346997 := bbase (se 5 (by rfl) ⟨16265, by rfl⟩ : syracuseStep 346997 = 32531) (by norm_num)
theorem B412541 : Blo 179801 412541 := bbase (se 3 (by rfl) ⟨77351, by rfl⟩ : syracuseStep 412541 = 154703) (by norm_num)
theorem B609173 : Blo 179801 609173 := bbase (se 6 (by rfl) ⟨14277, by rfl⟩ : syracuseStep 609173 = 28555) (by norm_num)
theorem B412613 : Blo 179801 412613 := bbase (se 4 (by rfl) ⟨38682, by rfl⟩ : syracuseStep 412613 = 77365) (by norm_num)
theorem B1395701 : Blo 179801 1395701 := bbase (se 5 (by rfl) ⟨65423, by rfl⟩ : syracuseStep 1395701 = 130847) (by norm_num)
theorem B347141 : Blo 179801 347141 := bbase (se 4 (by rfl) ⟨32544, by rfl⟩ : syracuseStep 347141 = 65089) (by norm_num)
theorem B412685 : Blo 179801 412685 := bbase (se 3 (by rfl) ⟨77378, by rfl⟩ : syracuseStep 412685 = 154757) (by norm_num)
theorem B1559573 : Blo 179801 1559573 := bbase (se 6 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 1559573 = 73105) (by norm_num)
theorem B412757 : Blo 179801 412757 := bbase (se 8 (by rfl) ⟨2418, by rfl⟩ : syracuseStep 412757 = 4837) (by norm_num)
theorem B412789 : Blo 179801 412789 := bbase (se 5 (by rfl) ⟨19349, by rfl⟩ : syracuseStep 412789 = 38699) (by norm_num)
theorem B412829 : Blo 179801 412829 := bbase (se 3 (by rfl) ⟨77405, by rfl⟩ : syracuseStep 412829 = 154811) (by norm_num)
theorem B412901 : Blo 179801 412901 := bbase (se 4 (by rfl) ⟨38709, by rfl⟩ : syracuseStep 412901 = 77419) (by norm_num)
theorem B216317 : Blo 179801 216317 := bbase (se 3 (by rfl) ⟨40559, by rfl⟩ : syracuseStep 216317 = 81119) (by norm_num)
theorem B2379029 : Blo 179801 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B347429 : Blo 179801 347429 := bbase (se 4 (by rfl) ⟨32571, by rfl⟩ : syracuseStep 347429 = 65143) (by norm_num)
theorem B412973 : Blo 179801 412973 := bbase (se 3 (by rfl) ⟨77432, by rfl⟩ : syracuseStep 412973 = 154865) (by norm_num)
theorem B609605 : Blo 179801 609605 := bbase (se 4 (by rfl) ⟨57150, by rfl⟩ : syracuseStep 609605 = 114301) (by norm_num)
theorem B413045 : Blo 179801 413045 := bbase (se 5 (by rfl) ⟨19361, by rfl⟩ : syracuseStep 413045 = 38723) (by norm_num)
theorem B347581 : Blo 179801 347581 := bbase (se 3 (by rfl) ⟨65171, by rfl⟩ : syracuseStep 347581 = 130343) (by norm_num)
theorem B413117 : Blo 179801 413117 := bbase (se 3 (by rfl) ⟨77459, by rfl⟩ : syracuseStep 413117 = 154919) (by norm_num)
theorem B413189 : Blo 179801 413189 := bbase (se 4 (by rfl) ⟨38736, by rfl⟩ : syracuseStep 413189 = 77473) (by norm_num)
theorem B577061 : Blo 179801 577061 := bbase (se 4 (by rfl) ⟨54099, by rfl⟩ : syracuseStep 577061 = 108199) (by norm_num)
theorem B413261 : Blo 179801 413261 := bbase (se 3 (by rfl) ⟨77486, by rfl⟩ : syracuseStep 413261 = 154973) (by norm_num)
theorem B413333 : Blo 179801 413333 := bbase (se 6 (by rfl) ⟨9687, by rfl⟩ : syracuseStep 413333 = 19375) (by norm_num)
theorem B413405 : Blo 179801 413405 := bbase (se 3 (by rfl) ⟨77513, by rfl⟩ : syracuseStep 413405 = 155027) (by norm_num)
theorem B347885 : Blo 179801 347885 := bbase (se 3 (by rfl) ⟨65228, by rfl⟩ : syracuseStep 347885 = 130457) (by norm_num)
theorem B610037 : Blo 179801 610037 := bbase (se 5 (by rfl) ⟨28595, by rfl⟩ : syracuseStep 610037 = 57191) (by norm_num)
theorem B413477 : Blo 179801 413477 := bbase (se 4 (by rfl) ⟨38763, by rfl⟩ : syracuseStep 413477 = 77527) (by norm_num)
theorem B413549 : Blo 179801 413549 := bbase (se 3 (by rfl) ⟨77540, by rfl⟩ : syracuseStep 413549 = 155081) (by norm_num)
theorem B217009 : Blo 179801 217009 := bbase (se 2 (by rfl) ⟨81378, by rfl⟩ : syracuseStep 217009 = 162757) (by norm_num)
theorem B217013 : Blo 179801 217013 := bbase (se 5 (by rfl) ⟨10172, by rfl⟩ : syracuseStep 217013 = 20345) (by norm_num)
theorem B184289 : Blo 179801 184289 := bbase (se 2 (by rfl) ⟨69108, by rfl⟩ : syracuseStep 184289 = 138217) (by norm_num)
theorem B512021 : Blo 179801 512021 := bbase (se 6 (by rfl) ⟨12000, by rfl⟩ : syracuseStep 512021 = 24001) (by norm_num)
theorem B610469 : Blo 179801 610469 := bbase (se 4 (by rfl) ⟨57231, by rfl⟩ : syracuseStep 610469 = 114463) (by norm_num)
theorem B413957 : Blo 179801 413957 := bbase (se 4 (by rfl) ⟨38808, by rfl⟩ : syracuseStep 413957 = 77617) (by norm_num)
theorem B741797 : Blo 179801 741797 := bbase (se 4 (by rfl) ⟨69543, by rfl⟩ : syracuseStep 741797 = 139087) (by norm_num)
theorem B217513 : Blo 179801 217513 := bbase (se 2 (by rfl) ⟨81567, by rfl⟩ : syracuseStep 217513 = 163135) (by norm_num)
theorem B348637 : Blo 179801 348637 := bbase (se 3 (by rfl) ⟨65369, by rfl⟩ : syracuseStep 348637 = 130739) (by norm_num)
theorem B774677 : Blo 179801 774677 := bbase (se 6 (by rfl) ⟨18156, by rfl⟩ : syracuseStep 774677 = 36313) (by norm_num)
theorem B184853 : Blo 179801 184853 := bbase (se 6 (by rfl) ⟨4332, by rfl⟩ : syracuseStep 184853 = 8665) (by norm_num)
theorem B184873 : Blo 179801 184873 := bbase (se 2 (by rfl) ⟨69327, by rfl⟩ : syracuseStep 184873 = 138655) (by norm_num)
theorem B184889 : Blo 179801 184889 := bbase (se 2 (by rfl) ⟨69333, by rfl⟩ : syracuseStep 184889 = 138667) (by norm_num)
theorem B610901 : Blo 179801 610901 := bbase (se 8 (by rfl) ⟨3579, by rfl⟩ : syracuseStep 610901 = 7159) (by norm_num)
theorem B348781 : Blo 179801 348781 := bbase (se 3 (by rfl) ⟨65396, by rfl⟩ : syracuseStep 348781 = 130793) (by norm_num)
theorem B348845 : Blo 179801 348845 := bbase (se 3 (by rfl) ⟨65408, by rfl⟩ : syracuseStep 348845 = 130817) (by norm_num)
theorem B512693 : Blo 179801 512693 := bbase (se 5 (by rfl) ⟨24032, by rfl⟩ : syracuseStep 512693 = 48065) (by norm_num)
theorem B774917 : Blo 179801 774917 := bbase (se 4 (by rfl) ⟨72648, by rfl⟩ : syracuseStep 774917 = 145297) (by norm_num)
theorem B217897 : Blo 179801 217897 := bbase (se 2 (by rfl) ⟨81711, by rfl⟩ : syracuseStep 217897 = 163423) (by norm_num)
theorem B1463285 : Blo 179801 1463285 := bbase (se 5 (by rfl) ⟨68591, by rfl⟩ : syracuseStep 1463285 = 137183) (by norm_num)
theorem B611333 : Blo 179801 611333 := bbase (se 4 (by rfl) ⟨57312, by rfl⟩ : syracuseStep 611333 = 114625) (by norm_num)
theorem B185437 : Blo 179801 185437 := bbase (se 3 (by rfl) ⟨34769, by rfl⟩ : syracuseStep 185437 = 69539) (by norm_num)
theorem B513125 : Blo 179801 513125 := bbase (se 4 (by rfl) ⟨48105, by rfl⟩ : syracuseStep 513125 = 96211) (by norm_num)
theorem B185473 : Blo 179801 185473 := bbase (se 2 (by rfl) ⟨69552, by rfl⟩ : syracuseStep 185473 = 139105) (by norm_num)
theorem B578933 : Blo 179801 578933 := bbase (se 5 (by rfl) ⟨27137, by rfl⟩ : syracuseStep 578933 = 54275) (by norm_num)
theorem B611765 : Blo 179801 611765 := bbase (se 5 (by rfl) ⟨28676, by rfl⟩ : syracuseStep 611765 = 57353) (by norm_num)
theorem B185797 : Blo 179801 185797 := bbase (se 4 (by rfl) ⟨17418, by rfl⟩ : syracuseStep 185797 = 34837) (by norm_num)
theorem B218801 : Blo 179801 218801 := bbase (se 2 (by rfl) ⟨82050, by rfl⟩ : syracuseStep 218801 = 164101) (by norm_num)
theorem B1038005 : Blo 179801 1038005 := bbase (se 5 (by rfl) ⟨48656, by rfl⟩ : syracuseStep 1038005 = 97313) (by norm_num)
theorem B513877 : Blo 179801 513877 := bbase (se 9 (by rfl) ⟨1505, by rfl⟩ : syracuseStep 513877 = 3011) (by norm_num)
theorem B612197 : Blo 179801 612197 := bbase (se 4 (by rfl) ⟨57393, by rfl⟩ : syracuseStep 612197 = 114787) (by norm_num)
theorem B382837 : Blo 179801 382837 := bbase (se 5 (by rfl) ⟨17945, by rfl⟩ : syracuseStep 382837 = 35891) (by norm_num)
theorem B939941 : Blo 179801 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B219061 : Blo 179801 219061 := bbase (se 5 (by rfl) ⟨10268, by rfl⟩ : syracuseStep 219061 = 20537) (by norm_num)
theorem B219253 : Blo 179801 219253 := bbase (se 5 (by rfl) ⟨10277, by rfl⟩ : syracuseStep 219253 = 20555) (by norm_num)
theorem B219277 : Blo 179801 219277 := bbase (se 3 (by rfl) ⟨41114, by rfl⟩ : syracuseStep 219277 = 82229) (by norm_num)
theorem B219281 : Blo 179801 219281 := bbase (se 2 (by rfl) ⟨82230, by rfl⟩ : syracuseStep 219281 = 164461) (by norm_num)
theorem B612629 : Blo 179801 612629 := bbase (se 6 (by rfl) ⟨14358, by rfl⟩ : syracuseStep 612629 = 28717) (by norm_num)
theorem B1169909 : Blo 179801 1169909 := bbase (se 5 (by rfl) ⟨54839, by rfl⟩ : syracuseStep 1169909 = 109679) (by norm_num)
theorem B219781 : Blo 179801 219781 := bbase (se 4 (by rfl) ⟨20604, by rfl⟩ : syracuseStep 219781 = 41209) (by norm_num)
theorem B613061 : Blo 179801 613061 := bbase (se 4 (by rfl) ⟨57474, by rfl⟩ : syracuseStep 613061 = 114949) (by norm_num)
theorem B219877 : Blo 179801 219877 := bbase (se 4 (by rfl) ⟨20613, by rfl⟩ : syracuseStep 219877 = 41227) (by norm_num)
theorem B1039189 : Blo 179801 1039189 := bbase (se 9 (by rfl) ⟨3044, by rfl⟩ : syracuseStep 1039189 = 6089) (by norm_num)
theorem B777205 : Blo 179801 777205 := bbase (se 5 (by rfl) ⟨36431, by rfl⟩ : syracuseStep 777205 = 72863) (by norm_num)
theorem B220205 : Blo 179801 220205 := bbase (se 3 (by rfl) ⟨41288, by rfl⟩ : syracuseStep 220205 = 82577) (by norm_num)
theorem B187453 : Blo 179801 187453 := bbase (se 3 (by rfl) ⟨35147, by rfl⟩ : syracuseStep 187453 = 70295) (by norm_num)
theorem B613493 : Blo 179801 613493 := bbase (se 5 (by rfl) ⟨28757, by rfl⟩ : syracuseStep 613493 = 57515) (by norm_num)
theorem B843061 : Blo 179801 843061 := bbase (se 5 (by rfl) ⟨39518, by rfl⟩ : syracuseStep 843061 = 79037) (by norm_num)
theorem B253325 : Blo 179801 253325 := bbase (se 3 (by rfl) ⟨47498, by rfl⟩ : syracuseStep 253325 = 94997) (by norm_num)
theorem B613925 : Blo 179801 613925 := bbase (se 4 (by rfl) ⟨57555, by rfl⟩ : syracuseStep 613925 = 115111) (by norm_num)
theorem B384605 : Blo 179801 384605 := bbase (se 3 (by rfl) ⟨72113, by rfl⟩ : syracuseStep 384605 = 144227) (by norm_num)
theorem B384725 : Blo 179801 384725 := bbase (se 7 (by rfl) ⟨4508, by rfl⟩ : syracuseStep 384725 = 9017) (by norm_num)
theorem B614357 : Blo 179801 614357 := bbase (se 7 (by rfl) ⟨7199, by rfl⟩ : syracuseStep 614357 = 14399) (by norm_num)
theorem B581701 : Blo 179801 581701 := bbase (se 4 (by rfl) ⟨54534, by rfl⟩ : syracuseStep 581701 = 109069) (by norm_num)
theorem B418117 : Blo 179801 418117 := bbase (se 4 (by rfl) ⟨39198, by rfl⟩ : syracuseStep 418117 = 78397) (by norm_num)
theorem B385357 : Blo 179801 385357 := bbase (se 3 (by rfl) ⟨72254, by rfl⟩ : syracuseStep 385357 = 144509) (by norm_num)
theorem B680309 : Blo 179801 680309 := bbase (se 5 (by rfl) ⟨31889, by rfl⟩ : syracuseStep 680309 = 63779) (by norm_num)
theorem B614789 : Blo 179801 614789 := bbase (se 4 (by rfl) ⟨57636, by rfl⟩ : syracuseStep 614789 = 115273) (by norm_num)
theorem B778693 : Blo 179801 778693 := bbase (se 4 (by rfl) ⟨73002, by rfl⟩ : syracuseStep 778693 = 146005) (by norm_num)
theorem B778709 : Blo 179801 778709 := bbase (se 7 (by rfl) ⟨9125, by rfl⟩ : syracuseStep 778709 = 18251) (by norm_num)
theorem B549413 : Blo 179801 549413 := bbase (se 4 (by rfl) ⟨51507, by rfl⟩ : syracuseStep 549413 = 103015) (by norm_num)
theorem B516725 : Blo 179801 516725 := bbase (se 5 (by rfl) ⟨24221, by rfl⟩ : syracuseStep 516725 = 48443) (by norm_num)
theorem B1041173 : Blo 179801 1041173 := bbase (se 6 (by rfl) ⟨24402, by rfl⟩ : syracuseStep 1041173 = 48805) (by norm_num)
theorem B615221 : Blo 179801 615221 := bbase (se 5 (by rfl) ⟨28838, by rfl⟩ : syracuseStep 615221 = 57677) (by norm_num)
theorem B418621 : Blo 179801 418621 := bbase (se 3 (by rfl) ⟨78491, by rfl⟩ : syracuseStep 418621 = 156983) (by norm_num)
theorem B910277 : Blo 179801 910277 := bbase (se 4 (by rfl) ⟨85338, by rfl⟩ : syracuseStep 910277 = 170677) (by norm_num)
theorem B2057237 : Blo 179801 2057237 := bbase (se 6 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 2057237 = 96433) (by norm_num)
theorem B386245 : Blo 179801 386245 := bbase (se 4 (by rfl) ⟨36210, by rfl⟩ : syracuseStep 386245 = 72421) (by norm_num)
theorem B615653 : Blo 179801 615653 := bbase (se 4 (by rfl) ⟨57717, by rfl⟩ : syracuseStep 615653 = 115435) (by norm_num)
theorem B877877 : Blo 179801 877877 := bbase (se 5 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 877877 = 82301) (by norm_num)
theorem B386365 : Blo 179801 386365 := bbase (se 3 (by rfl) ⟨72443, by rfl⟩ : syracuseStep 386365 = 144887) (by norm_num)
theorem B288269 : Blo 179801 288269 := bbase (se 3 (by rfl) ⟨54050, by rfl⟩ : syracuseStep 288269 = 108101) (by norm_num)
theorem B386621 : Blo 179801 386621 := bbase (se 3 (by rfl) ⟨72491, by rfl⟩ : syracuseStep 386621 = 144983) (by norm_num)
theorem B2647637 : Blo 179801 2647637 := bbase (se 8 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 2647637 = 31027) (by norm_num)
theorem B222869 : Blo 179801 222869 := bbase (se 6 (by rfl) ⟨5223, by rfl⟩ : syracuseStep 222869 = 10447) (by norm_num)
theorem B616085 : Blo 179801 616085 := bbase (se 6 (by rfl) ⟨14439, by rfl⟩ : syracuseStep 616085 = 28879) (by norm_num)
theorem B1926805 : Blo 179801 1926805 := bbase (se 6 (by rfl) ⟨45159, by rfl⟩ : syracuseStep 1926805 = 90319) (by norm_num)
theorem B517909 : Blo 179801 517909 := bbase (se 6 (by rfl) ⟨12138, by rfl⟩ : syracuseStep 517909 = 24277) (by norm_num)
theorem B518069 : Blo 179801 518069 := bbase (se 5 (by rfl) ⟨24284, by rfl⟩ : syracuseStep 518069 = 48569) (by norm_num)
theorem B3467285 : Blo 179801 3467285 := bbase (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) (by norm_num)
theorem B616517 : Blo 179801 616517 := bbase (se 4 (by rfl) ⟨57798, by rfl⟩ : syracuseStep 616517 = 115597) (by norm_num)
theorem B944261 : Blo 179801 944261 := bbase (se 4 (by rfl) ⟨88524, by rfl⟩ : syracuseStep 944261 = 177049) (by norm_num)
theorem B518309 : Blo 179801 518309 := bbase (se 4 (by rfl) ⟨48591, by rfl⟩ : syracuseStep 518309 = 97183) (by norm_num)
theorem B911573 : Blo 179801 911573 := bbase (se 7 (by rfl) ⟨10682, by rfl⟩ : syracuseStep 911573 = 21365) (by norm_num)
theorem B518501 : Blo 179801 518501 := bbase (se 4 (by rfl) ⟨48609, by rfl⟩ : syracuseStep 518501 = 97219) (by norm_num)
theorem B387509 : Blo 179801 387509 := bbase (se 5 (by rfl) ⟨18164, by rfl⟩ : syracuseStep 387509 = 36329) (by norm_num)
theorem B289261 : Blo 179801 289261 := bbase (se 3 (by rfl) ⟨54236, by rfl⟩ : syracuseStep 289261 = 108473) (by norm_num)
theorem B616949 : Blo 179801 616949 := bbase (se 5 (by rfl) ⟨28919, by rfl⟩ : syracuseStep 616949 = 57839) (by norm_num)
theorem B616997 : Blo 179801 616997 := bbase (se 4 (by rfl) ⟨57843, by rfl⟩ : syracuseStep 616997 = 115687) (by norm_num)
theorem B387749 : Blo 179801 387749 := bbase (se 4 (by rfl) ⟨36351, by rfl⟩ : syracuseStep 387749 = 72703) (by norm_num)
theorem B780965 : Blo 179801 780965 := bbase (se 4 (by rfl) ⟨73215, by rfl⟩ : syracuseStep 780965 = 146431) (by norm_num)
theorem B584597 : Blo 179801 584597 := bbase (se 6 (by rfl) ⟨13701, by rfl⟩ : syracuseStep 584597 = 27403) (by norm_num)
theorem B617381 : Blo 179801 617381 := bbase (se 4 (by rfl) ⟨57879, by rfl⟩ : syracuseStep 617381 = 115759) (by norm_num)
theorem B1043381 : Blo 179801 1043381 := bbase (se 5 (by rfl) ⟨48908, by rfl⟩ : syracuseStep 1043381 = 97817) (by norm_num)
theorem B289909 : Blo 179801 289909 := bbase (se 5 (by rfl) ⟨13589, by rfl⟩ : syracuseStep 289909 = 27179) (by norm_num)
theorem B388253 : Blo 179801 388253 := bbase (se 3 (by rfl) ⟨72797, by rfl⟩ : syracuseStep 388253 = 145595) (by norm_num)
theorem B650405 : Blo 179801 650405 := bbase (se 4 (by rfl) ⟨60975, by rfl⟩ : syracuseStep 650405 = 121951) (by norm_num)
theorem B388261 : Blo 179801 388261 := bbase (se 4 (by rfl) ⟨36399, by rfl⟩ : syracuseStep 388261 = 72799) (by norm_num)
theorem B257269 : Blo 179801 257269 := bbase (se 5 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 257269 = 24119) (by norm_num)
theorem B879893 : Blo 179801 879893 := bbase (se 6 (by rfl) ⟨20622, by rfl⟩ : syracuseStep 879893 = 41245) (by norm_num)
theorem B519493 : Blo 179801 519493 := bbase (se 4 (by rfl) ⟨48702, by rfl⟩ : syracuseStep 519493 = 97405) (by norm_num)
theorem B617813 : Blo 179801 617813 := bbase (se 11 (by rfl) ⟨452, by rfl⟩ : syracuseStep 617813 = 905) (by norm_num)
theorem B650693 : Blo 179801 650693 := bbase (se 4 (by rfl) ⟨61002, by rfl⟩ : syracuseStep 650693 = 122005) (by norm_num)
theorem B880085 : Blo 179801 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B912869 : Blo 179801 912869 := bbase (se 4 (by rfl) ⟨85581, by rfl⟩ : syracuseStep 912869 = 171163) (by norm_num)
theorem B421373 : Blo 179801 421373 := bbase (se 3 (by rfl) ⟨79007, by rfl⟩ : syracuseStep 421373 = 158015) (by norm_num)
theorem B192029 : Blo 179801 192029 := bbase (se 3 (by rfl) ⟨36005, by rfl⟩ : syracuseStep 192029 = 72011) (by norm_num)
theorem B192089 : Blo 179801 192089 := bbase (se 2 (by rfl) ⟨72033, by rfl⟩ : syracuseStep 192089 = 144067) (by norm_num)
theorem B192217 : Blo 179801 192217 := bbase (se 2 (by rfl) ⟨72081, by rfl⟩ : syracuseStep 192217 = 144163) (by norm_num)
theorem B618245 : Blo 179801 618245 := bbase (se 4 (by rfl) ⟨57960, by rfl⟩ : syracuseStep 618245 = 115921) (by norm_num)
theorem B257861 : Blo 179801 257861 := bbase (se 4 (by rfl) ⟨24174, by rfl⟩ : syracuseStep 257861 = 48349) (by norm_num)
theorem B683909 : Blo 179801 683909 := bbase (se 4 (by rfl) ⟨64116, by rfl⟩ : syracuseStep 683909 = 128233) (by norm_num)
theorem B257941 : Blo 179801 257941 := bbase (se 6 (by rfl) ⟨6045, by rfl⟩ : syracuseStep 257941 = 12091) (by norm_num)
theorem B258061 : Blo 179801 258061 := bbase (se 3 (by rfl) ⟨48386, by rfl⟩ : syracuseStep 258061 = 96773) (by norm_num)
theorem B978965 : Blo 179801 978965 := bbase (se 6 (by rfl) ⟨22944, by rfl⟩ : syracuseStep 978965 = 45889) (by norm_num)
theorem B290837 : Blo 179801 290837 := bbase (se 6 (by rfl) ⟨6816, by rfl⟩ : syracuseStep 290837 = 13633) (by norm_num)
theorem B258157 : Blo 179801 258157 := bbase (se 3 (by rfl) ⟨48404, by rfl⟩ : syracuseStep 258157 = 96809) (by norm_num)
theorem B192661 : Blo 179801 192661 := bbase (se 6 (by rfl) ⟨4515, by rfl⟩ : syracuseStep 192661 = 9031) (by norm_num)
theorem B553109 : Blo 179801 553109 := bbase (se 6 (by rfl) ⟨12963, by rfl⟩ : syracuseStep 553109 = 25927) (by norm_num)
theorem B684197 : Blo 179801 684197 := bbase (se 4 (by rfl) ⟨64143, by rfl⟩ : syracuseStep 684197 = 128287) (by norm_num)
theorem B618677 : Blo 179801 618677 := bbase (se 5 (by rfl) ⟨29000, by rfl⟩ : syracuseStep 618677 = 58001) (by norm_num)
theorem B192781 : Blo 179801 192781 := bbase (se 3 (by rfl) ⟨36146, by rfl⟩ : syracuseStep 192781 = 72293) (by norm_num)
theorem B389389 : Blo 179801 389389 := bbase (se 3 (by rfl) ⟨73010, by rfl⟩ : syracuseStep 389389 = 146021) (by norm_num)
theorem B520597 : Blo 179801 520597 := bbase (se 6 (by rfl) ⟨12201, by rfl⟩ : syracuseStep 520597 = 24403) (by norm_num)
theorem B618965 : Blo 179801 618965 := bbase (se 7 (by rfl) ⟨7253, by rfl⟩ : syracuseStep 618965 = 14507) (by norm_num)
theorem B291293 : Blo 179801 291293 := bbase (se 3 (by rfl) ⟨54617, by rfl⟩ : syracuseStep 291293 = 109235) (by norm_num)
theorem B193033 : Blo 179801 193033 := bbase (se 2 (by rfl) ⟨72387, by rfl⟩ : syracuseStep 193033 = 144775) (by norm_num)
theorem B193037 : Blo 179801 193037 := bbase (se 3 (by rfl) ⟨36194, by rfl⟩ : syracuseStep 193037 = 72389) (by norm_num)
theorem B258653 : Blo 179801 258653 := bbase (se 3 (by rfl) ⟨48497, by rfl⟩ : syracuseStep 258653 = 96995) (by norm_num)
theorem B619109 : Blo 179801 619109 := bbase (se 4 (by rfl) ⟨58041, by rfl⟩ : syracuseStep 619109 = 116083) (by norm_num)
theorem B389765 : Blo 179801 389765 := bbase (se 4 (by rfl) ⟨36540, by rfl⟩ : syracuseStep 389765 = 73081) (by norm_num)
theorem B455341 : Blo 179801 455341 := bbase (se 3 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 455341 = 170753) (by norm_num)
theorem B914165 : Blo 179801 914165 := bbase (se 5 (by rfl) ⟨42851, by rfl⟩ : syracuseStep 914165 = 85703) (by norm_num)
theorem B1372949 : Blo 179801 1372949 := bbase (se 6 (by rfl) ⟨32178, by rfl⟩ : syracuseStep 1372949 = 64357) (by norm_num)
theorem B455453 : Blo 179801 455453 := bbase (se 3 (by rfl) ⟨85397, by rfl⟩ : syracuseStep 455453 = 170795) (by norm_num)
theorem B455645 : Blo 179801 455645 := bbase (se 3 (by rfl) ⟨85433, by rfl⟩ : syracuseStep 455645 = 170867) (by norm_num)
theorem B619541 : Blo 179801 619541 := bbase (se 6 (by rfl) ⟨14520, by rfl⟩ : syracuseStep 619541 = 29041) (by norm_num)
theorem B193601 : Blo 179801 193601 := bbase (se 2 (by rfl) ⟨72600, by rfl⟩ : syracuseStep 193601 = 145201) (by norm_num)
theorem B259205 : Blo 179801 259205 := bbase (se 4 (by rfl) ⟨24300, by rfl⟩ : syracuseStep 259205 = 48601) (by norm_num)
theorem B324821 : Blo 179801 324821 := bbase (se 7 (by rfl) ⟨3806, by rfl⟩ : syracuseStep 324821 = 7613) (by norm_num)
theorem B193789 : Blo 179801 193789 := bbase (se 3 (by rfl) ⟨36335, by rfl⟩ : syracuseStep 193789 = 72671) (by norm_num)
theorem B324901 : Blo 179801 324901 := bbase (se 4 (by rfl) ⟨30459, by rfl⟩ : syracuseStep 324901 = 60919) (by norm_num)
theorem B455989 : Blo 179801 455989 := bbase (se 5 (by rfl) ⟨21374, by rfl⟩ : syracuseStep 455989 = 42749) (by norm_num)
theorem B685381 : Blo 179801 685381 := bbase (se 4 (by rfl) ⟨64254, by rfl⟩ : syracuseStep 685381 = 128509) (by norm_num)
theorem B456101 : Blo 179801 456101 := bbase (se 4 (by rfl) ⟨42759, by rfl⟩ : syracuseStep 456101 = 85519) (by norm_num)
theorem B619973 : Blo 179801 619973 := bbase (se 4 (by rfl) ⟨58122, by rfl⟩ : syracuseStep 619973 = 116245) (by norm_num)
theorem B882181 : Blo 179801 882181 := bbase (se 4 (by rfl) ⟨82704, by rfl⟩ : syracuseStep 882181 = 165409) (by norm_num)
theorem B456293 : Blo 179801 456293 := bbase (se 4 (by rfl) ⟨42777, by rfl⟩ : syracuseStep 456293 = 85555) (by norm_num)
theorem B685685 : Blo 179801 685685 := bbase (se 5 (by rfl) ⟨32141, by rfl⟩ : syracuseStep 685685 = 64283) (by norm_num)
theorem B259781 : Blo 179801 259781 := bbase (se 4 (by rfl) ⟨24354, by rfl⟩ : syracuseStep 259781 = 48709) (by norm_num)
theorem B980693 : Blo 179801 980693 := bbase (se 7 (by rfl) ⟨11492, by rfl⟩ : syracuseStep 980693 = 22985) (by norm_num)
theorem B1242965 : Blo 179801 1242965 := bbase (se 9 (by rfl) ⟨3641, by rfl⟩ : syracuseStep 1242965 = 7283) (by norm_num)
theorem B292709 : Blo 179801 292709 := bbase (se 4 (by rfl) ⟨27441, by rfl⟩ : syracuseStep 292709 = 54883) (by norm_num)
theorem B259957 : Blo 179801 259957 := bbase (se 5 (by rfl) ⟨12185, by rfl⟩ : syracuseStep 259957 = 24371) (by norm_num)
theorem B522101 : Blo 179801 522101 := bbase (se 5 (by rfl) ⟨24473, by rfl⟩ : syracuseStep 522101 = 48947) (by norm_num)
theorem B456637 : Blo 179801 456637 := bbase (se 3 (by rfl) ⟨85619, by rfl⟩ : syracuseStep 456637 = 171239) (by norm_num)
theorem B587749 : Blo 179801 587749 := bbase (se 4 (by rfl) ⟨55101, by rfl⟩ : syracuseStep 587749 = 110203) (by norm_num)
theorem B915461 : Blo 179801 915461 := bbase (se 4 (by rfl) ⟨85824, by rfl⟩ : syracuseStep 915461 = 171649) (by norm_num)
theorem B456749 : Blo 179801 456749 := bbase (se 3 (by rfl) ⟨85640, by rfl⟩ : syracuseStep 456749 = 171281) (by norm_num)
theorem B194609 : Blo 179801 194609 := bbase (se 2 (by rfl) ⟨72978, by rfl⟩ : syracuseStep 194609 = 145957) (by norm_num)
theorem B292933 : Blo 179801 292933 := bbase (se 4 (by rfl) ⟨27462, by rfl⟩ : syracuseStep 292933 = 54925) (by norm_num)
theorem B456941 : Blo 179801 456941 := bbase (se 3 (by rfl) ⟨85676, by rfl⟩ : syracuseStep 456941 = 171353) (by norm_num)
theorem B391405 : Blo 179801 391405 := bbase (se 3 (by rfl) ⟨73388, by rfl⟩ : syracuseStep 391405 = 146777) (by norm_num)
theorem B227605 : Blo 179801 227605 := bbase (se 6 (by rfl) ⟨5334, by rfl⟩ : syracuseStep 227605 = 10669) (by norm_num)
theorem B325981 : Blo 179801 325981 := bbase (se 3 (by rfl) ⟨61121, by rfl⟩ : syracuseStep 325981 = 122243) (by norm_num)
theorem B227701 : Blo 179801 227701 := bbase (se 5 (by rfl) ⟨10673, by rfl⟩ : syracuseStep 227701 = 21347) (by norm_num)
theorem B326125 : Blo 179801 326125 := bbase (se 3 (by rfl) ⟨61148, by rfl⟩ : syracuseStep 326125 = 122297) (by norm_num)
theorem B195053 : Blo 179801 195053 := bbase (se 3 (by rfl) ⟨36572, by rfl⟩ : syracuseStep 195053 = 73145) (by norm_num)
theorem B227873 : Blo 179801 227873 := bbase (se 2 (by rfl) ⟨85452, by rfl⟩ : syracuseStep 227873 = 170905) (by norm_num)
theorem B457285 : Blo 179801 457285 := bbase (se 4 (by rfl) ⟨42870, by rfl⟩ : syracuseStep 457285 = 85741) (by norm_num)
theorem B227929 : Blo 179801 227929 := bbase (se 2 (by rfl) ⟨85473, by rfl⟩ : syracuseStep 227929 = 170947) (by norm_num)
theorem B784997 : Blo 179801 784997 := bbase (se 4 (by rfl) ⟨73593, by rfl⟩ : syracuseStep 784997 = 147187) (by norm_num)
theorem B326285 : Blo 179801 326285 := bbase (se 3 (by rfl) ⟨61178, by rfl⟩ : syracuseStep 326285 = 122357) (by norm_num)
theorem B260749 : Blo 179801 260749 := bbase (se 3 (by rfl) ⟨48890, by rfl⟩ : syracuseStep 260749 = 97781) (by norm_num)
theorem B457397 : Blo 179801 457397 := bbase (se 5 (by rfl) ⟨21440, by rfl⟩ : syracuseStep 457397 = 42881) (by norm_num)
theorem B228025 : Blo 179801 228025 := bbase (se 2 (by rfl) ⟨85509, by rfl⟩ : syracuseStep 228025 = 171019) (by norm_num)
theorem B195301 : Blo 179801 195301 := bbase (se 4 (by rfl) ⟨18309, by rfl⟩ : syracuseStep 195301 = 36619) (by norm_num)
theorem B228197 : Blo 179801 228197 := bbase (se 4 (by rfl) ⟨21393, by rfl⟩ : syracuseStep 228197 = 42787) (by norm_num)
theorem B457589 : Blo 179801 457589 := bbase (se 5 (by rfl) ⟨21449, by rfl⟩ : syracuseStep 457589 = 42899) (by norm_num)
theorem B228253 : Blo 179801 228253 := bbase (se 3 (by rfl) ⟨42797, by rfl⟩ : syracuseStep 228253 = 85595) (by norm_num)
theorem B261085 : Blo 179801 261085 := bbase (se 3 (by rfl) ⟨48953, by rfl⟩ : syracuseStep 261085 = 97907) (by norm_num)
theorem B228349 : Blo 179801 228349 := bbase (se 3 (by rfl) ⟨42815, by rfl⟩ : syracuseStep 228349 = 85631) (by norm_num)
theorem B293917 : Blo 179801 293917 := bbase (se 3 (by rfl) ⟨55109, by rfl⟩ : syracuseStep 293917 = 110219) (by norm_num)
theorem B392293 : Blo 179801 392293 := bbase (se 4 (by rfl) ⟨36777, by rfl⟩ : syracuseStep 392293 = 73555) (by norm_num)
theorem B195733 : Blo 179801 195733 := bbase (se 6 (by rfl) ⟨4587, by rfl⟩ : syracuseStep 195733 = 9175) (by norm_num)
theorem B228521 : Blo 179801 228521 := bbase (se 2 (by rfl) ⟨85695, by rfl⟩ : syracuseStep 228521 = 171391) (by norm_num)
theorem B261301 : Blo 179801 261301 := bbase (se 5 (by rfl) ⟨12248, by rfl⟩ : syracuseStep 261301 = 24497) (by norm_num)
theorem B457933 : Blo 179801 457933 := bbase (se 3 (by rfl) ⟨85862, by rfl⟩ : syracuseStep 457933 = 171725) (by norm_num)
theorem B195805 : Blo 179801 195805 := bbase (se 3 (by rfl) ⟨36713, by rfl⟩ : syracuseStep 195805 = 73427) (by norm_num)
theorem B228577 : Blo 179801 228577 := bbase (se 2 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 228577 = 171433) (by norm_num)
theorem B916757 : Blo 179801 916757 := bbase (se 6 (by rfl) ⟨21486, by rfl⟩ : syracuseStep 916757 = 42973) (by norm_num)
theorem B458045 : Blo 179801 458045 := bbase (se 3 (by rfl) ⟨85883, by rfl⟩ : syracuseStep 458045 = 171767) (by norm_num)
theorem B228673 : Blo 179801 228673 := bbase (se 2 (by rfl) ⟨85752, by rfl⟩ : syracuseStep 228673 = 171505) (by norm_num)
theorem B294349 : Blo 179801 294349 := bbase (se 3 (by rfl) ⟨55190, by rfl⟩ : syracuseStep 294349 = 110381) (by norm_num)
theorem B228845 : Blo 179801 228845 := bbase (se 3 (by rfl) ⟨42908, by rfl⟩ : syracuseStep 228845 = 85817) (by norm_num)
theorem B458237 : Blo 179801 458237 := bbase (se 3 (by rfl) ⟨85919, by rfl⟩ : syracuseStep 458237 = 171839) (by norm_num)
theorem B228901 : Blo 179801 228901 := bbase (se 4 (by rfl) ⟨21459, by rfl⟩ : syracuseStep 228901 = 42919) (by norm_num)
theorem B261677 : Blo 179801 261677 := bbase (se 3 (by rfl) ⟨49064, by rfl⟩ : syracuseStep 261677 = 98129) (by norm_num)
theorem B1408565 : Blo 179801 1408565 := bbase (se 5 (by rfl) ⟨66026, by rfl⟩ : syracuseStep 1408565 = 132053) (by norm_num)
theorem B196177 : Blo 179801 196177 := bbase (se 2 (by rfl) ⟨73566, by rfl⟩ : syracuseStep 196177 = 147133) (by norm_num)
theorem B982613 : Blo 179801 982613 := bbase (se 8 (by rfl) ⟨5757, by rfl⟩ : syracuseStep 982613 = 11515) (by norm_num)
theorem B228997 : Blo 179801 228997 := bbase (se 4 (by rfl) ⟨21468, by rfl⟩ : syracuseStep 228997 = 42937) (by norm_num)
theorem B687797 : Blo 179801 687797 := bbase (se 5 (by rfl) ⟨32240, by rfl⟩ : syracuseStep 687797 = 64481) (by norm_num)
theorem B491221 : Blo 179801 491221 := bbase (se 7 (by rfl) ⟨5756, by rfl⟩ : syracuseStep 491221 = 11513) (by norm_num)
theorem B229169 : Blo 179801 229169 := bbase (se 2 (by rfl) ⟨85938, by rfl⟩ : syracuseStep 229169 = 171877) (by norm_num)
theorem B458581 : Blo 179801 458581 := bbase (se 9 (by rfl) ⟨1343, by rfl⟩ : syracuseStep 458581 = 2687) (by norm_num)
theorem B3211093 : Blo 179801 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B229225 : Blo 179801 229225 := bbase (se 2 (by rfl) ⟨85959, by rfl⟩ : syracuseStep 229225 = 171919) (by norm_num)
theorem B458693 : Blo 179801 458693 := bbase (se 4 (by rfl) ⟨43002, by rfl⟩ : syracuseStep 458693 = 86005) (by norm_num)
theorem B229321 : Blo 179801 229321 := bbase (se 2 (by rfl) ⟨85995, by rfl⟩ : syracuseStep 229321 = 171991) (by norm_num)
theorem B688085 : Blo 179801 688085 := bbase (se 7 (by rfl) ⟨8063, by rfl⟩ : syracuseStep 688085 = 16127) (by norm_num)
theorem B327971 : Blo 179801 327971 := bstep (se 1 (by rfl) ⟨245978, by rfl⟩ : syracuseStep 327971 = 491957) B491957
theorem B1474957 : Blo 179801 1474957 := bstep (se 3 (by rfl) ⟨276554, by rfl⟩ : syracuseStep 1474957 = 553109) B553109
theorem B557489 : Blo 179801 557489 := bstep (se 2 (by rfl) ⟨209058, by rfl⟩ : syracuseStep 557489 = 418117) B418117
theorem B1376837 : Blo 179801 1376837 := bstep (se 4 (by rfl) ⟨129078, by rfl⟩ : syracuseStep 1376837 = 258157) B258157
theorem B230035 : Blo 179801 230035 := bstep (se 1 (by rfl) ⟨172526, by rfl⟩ : syracuseStep 230035 = 345053) B345053
theorem B197299 : Blo 179801 197299 := bstep (se 1 (by rfl) ⟨147974, by rfl⟩ : syracuseStep 197299 = 295949) B295949
theorem B230131 : Blo 179801 230131 := bstep (se 1 (by rfl) ⟨172598, by rfl⟩ : syracuseStep 230131 = 345197) B345197
theorem B459665 : Blo 179801 459665 := bstep (se 2 (by rfl) ⟨172374, by rfl⟩ : syracuseStep 459665 = 344749) B344749
theorem B459715 : Blo 179801 459715 := bstep (se 1 (by rfl) ⟨344786, by rfl⟩ : syracuseStep 459715 = 689573) B689573
theorem B1573829 : Blo 179801 1573829 := bstep (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) B295093
theorem B656333 : Blo 179801 656333 := bstep (se 3 (by rfl) ⟨123062, by rfl⟩ : syracuseStep 656333 = 246125) B246125
theorem B590915 : Blo 179801 590915 := bstep (se 1 (by rfl) ⟨443186, by rfl⟩ : syracuseStep 590915 = 886373) B886373
theorem B459857 : Blo 179801 459857 := bstep (se 2 (by rfl) ⟨172446, by rfl⟩ : syracuseStep 459857 = 344893) B344893
theorem B558161 : Blo 179801 558161 := bstep (se 2 (by rfl) ⟨209310, by rfl⟩ : syracuseStep 558161 = 418621) B418621
theorem B230627 : Blo 179801 230627 := bstep (se 1 (by rfl) ⟨172970, by rfl⟩ : syracuseStep 230627 = 345941) B345941
theorem B1672433 : Blo 179801 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B492941 : Blo 179801 492941 := bstep (se 3 (by rfl) ⟨92426, by rfl⟩ : syracuseStep 492941 = 184853) B184853
theorem B493037 : Blo 179801 493037 := bstep (se 3 (by rfl) ⟨92444, by rfl⟩ : syracuseStep 493037 = 184889) B184889
theorem B624109 : Blo 179801 624109 := bstep (se 3 (by rfl) ⟨117020, by rfl⟩ : syracuseStep 624109 = 234041) B234041
theorem B919025 : Blo 179801 919025 := bstep (se 2 (by rfl) ⟨344634, by rfl⟩ : syracuseStep 919025 = 689269) B689269
theorem B689741 : Blo 179801 689741 := bstep (se 3 (by rfl) ⟨129326, by rfl⟩ : syracuseStep 689741 = 258653) B258653
theorem B231331 : Blo 179801 231331 := bstep (se 1 (by rfl) ⟨173498, by rfl⟩ : syracuseStep 231331 = 346997) B346997
theorem B231427 : Blo 179801 231427 := bstep (se 1 (by rfl) ⟨173570, by rfl⟩ : syracuseStep 231427 = 347141) B347141
theorem B460849 : Blo 179801 460849 := bstep (se 2 (by rfl) ⟨172818, by rfl⟩ : syracuseStep 460849 = 345637) B345637
theorem B461123 : Blo 179801 461123 := bstep (se 1 (by rfl) ⟨345842, by rfl⟩ : syracuseStep 461123 = 691685) B691685
theorem B690545 : Blo 179801 690545 := bstep (se 2 (by rfl) ⟨258954, by rfl⟩ : syracuseStep 690545 = 517909) B517909
theorem B231923 : Blo 179801 231923 := bstep (se 1 (by rfl) ⟨173942, by rfl⟩ : syracuseStep 231923 = 347885) B347885
theorem B461315 : Blo 179801 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B1542725 : Blo 179801 1542725 := bstep (se 4 (by rfl) ⟨144630, by rfl⟩ : syracuseStep 1542725 = 289261) B289261
theorem B1739333 : Blo 179801 1739333 := bstep (se 4 (by rfl) ⟨163062, by rfl⟩ : syracuseStep 1739333 = 326125) B326125
theorem B4000565 : Blo 179801 4000565 := bstep (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) B375053
theorem B625553 : Blo 179801 625553 := bstep (se 2 (by rfl) ⟨234582, by rfl⟩ : syracuseStep 625553 = 469165) B469165
theorem B920483 : Blo 179801 920483 := bstep (se 1 (by rfl) ⟨690362, by rfl⟩ : syracuseStep 920483 = 1380725) B1380725
theorem B494531 : Blo 179801 494531 := bstep (se 1 (by rfl) ⟨370898, by rfl⟩ : syracuseStep 494531 = 741797) B741797
theorem B691213 : Blo 179801 691213 := bstep (se 3 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 691213 = 259205) B259205
theorem B1969379 : Blo 179801 1969379 := bstep (se 1 (by rfl) ⟨1477034, by rfl⟩ : syracuseStep 1969379 = 2954069) B2954069
theorem B462257 : Blo 179801 462257 := bstep (se 2 (by rfl) ⟨173346, by rfl⟩ : syracuseStep 462257 = 346693) B346693
theorem B462307 : Blo 179801 462307 := bstep (se 1 (by rfl) ⟨346730, by rfl⟩ : syracuseStep 462307 = 693461) B693461
theorem B658979 : Blo 179801 658979 := bstep (se 1 (by rfl) ⟨494234, by rfl⟩ : syracuseStep 658979 = 988469) B988469
theorem B462449 : Blo 179801 462449 := bstep (se 2 (by rfl) ⟨173418, by rfl⟩ : syracuseStep 462449 = 346837) B346837
theorem B1773197 : Blo 179801 1773197 := bstep (se 3 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 1773197 = 664949) B664949
theorem B921293 : Blo 179801 921293 := bstep (se 3 (by rfl) ⟨172742, by rfl⟩ : syracuseStep 921293 = 345485) B345485
theorem B659171 : Blo 179801 659171 := bstep (se 1 (by rfl) ⟨494378, by rfl⟩ : syracuseStep 659171 = 988757) B988757
theorem B692003 : Blo 179801 692003 := bstep (se 1 (by rfl) ⟨519002, by rfl⟩ : syracuseStep 692003 = 1038005) B1038005
theorem B626627 : Blo 179801 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B594317 : Blo 179801 594317 := bstep (se 3 (by rfl) ⟨111434, by rfl⟩ : syracuseStep 594317 = 222869) B222869
theorem B692657 : Blo 179801 692657 := bstep (se 2 (by rfl) ⟨259746, by rfl⟩ : syracuseStep 692657 = 519493) B519493
theorem B692749 : Blo 179801 692749 := bstep (se 3 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 692749 = 259781) B259781
theorem B463441 : Blo 179801 463441 := bstep (se 2 (by rfl) ⟨173790, by rfl⟩ : syracuseStep 463441 = 347581) B347581
theorem B1249933 : Blo 179801 1249933 := bstep (se 3 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 1249933 = 468725) B468725
theorem B463715 : Blo 179801 463715 := bstep (se 1 (by rfl) ⟨347786, by rfl⟩ : syracuseStep 463715 = 695573) B695573
theorem B529357 : Blo 179801 529357 := bstep (se 3 (by rfl) ⟨99254, by rfl⟩ : syracuseStep 529357 = 198509) B198509
theorem B463907 : Blo 179801 463907 := bstep (se 1 (by rfl) ⟨347930, by rfl⟩ : syracuseStep 463907 = 695861) B695861
theorem B1316209 : Blo 179801 1316209 := bstep (se 2 (by rfl) ⟨493578, by rfl⟩ : syracuseStep 1316209 = 987157) B987157
theorem B1939085 : Blo 179801 1939085 := bstep (se 3 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 1939085 = 727157) B727157
theorem B202387 : Blo 179801 202387 := bstep (se 1 (by rfl) ⟨151790, by rfl⟩ : syracuseStep 202387 = 303581) B303581
theorem B366275 : Blo 179801 366275 := bstep (se 1 (by rfl) ⟨274706, by rfl⟩ : syracuseStep 366275 = 549413) B549413
theorem B202531 : Blo 179801 202531 := bstep (se 1 (by rfl) ⟨151898, by rfl⟩ : syracuseStep 202531 = 303797) B303797
theorem B694115 : Blo 179801 694115 := bstep (se 1 (by rfl) ⟨520586, by rfl⟩ : syracuseStep 694115 = 1041173) B1041173
theorem B694129 : Blo 179801 694129 := bstep (se 2 (by rfl) ⟨260298, by rfl⟩ : syracuseStep 694129 = 520597) B520597
theorem B202675 : Blo 179801 202675 := bstep (se 1 (by rfl) ⟨152006, by rfl⟩ : syracuseStep 202675 = 304013) B304013
theorem B464849 : Blo 179801 464849 := bstep (se 2 (by rfl) ⟨174318, by rfl⟩ : syracuseStep 464849 = 348637) B348637
theorem B464899 : Blo 179801 464899 := bstep (se 1 (by rfl) ⟨348674, by rfl⟩ : syracuseStep 464899 = 697349) B697349
theorem B596003 : Blo 179801 596003 := bstep (se 1 (by rfl) ⟨447002, by rfl⟩ : syracuseStep 596003 = 894005) B894005
theorem B202819 : Blo 179801 202819 := bstep (se 1 (by rfl) ⟨152114, by rfl⟩ : syracuseStep 202819 = 304229) B304229
theorem B465041 : Blo 179801 465041 := bstep (se 2 (by rfl) ⟨174390, by rfl⟩ : syracuseStep 465041 = 348781) B348781
theorem B661709 : Blo 179801 661709 := bstep (se 3 (by rfl) ⟨124070, by rfl⟩ : syracuseStep 661709 = 248141) B248141
theorem B202963 : Blo 179801 202963 := bstep (se 1 (by rfl) ⟨152222, by rfl⟩ : syracuseStep 202963 = 304445) B304445
theorem B1382669 : Blo 179801 1382669 := bstep (se 3 (by rfl) ⟨259250, by rfl⟩ : syracuseStep 1382669 = 518501) B518501
theorem B203107 : Blo 179801 203107 := bstep (se 1 (by rfl) ⟨152330, by rfl⟩ : syracuseStep 203107 = 304661) B304661
theorem B203251 : Blo 179801 203251 := bstep (se 1 (by rfl) ⟨152438, by rfl⟩ : syracuseStep 203251 = 304877) B304877
theorem B924209 : Blo 179801 924209 := bstep (se 2 (by rfl) ⟨346578, by rfl⟩ : syracuseStep 924209 = 693157) B693157
theorem B203395 : Blo 179801 203395 := bstep (se 1 (by rfl) ⟨152546, by rfl⟩ : syracuseStep 203395 = 305093) B305093
theorem B367249 : Blo 179801 367249 := bstep (se 2 (by rfl) ⟨137718, by rfl⟩ : syracuseStep 367249 = 275437) B275437
theorem B629507 : Blo 179801 629507 := bstep (se 1 (by rfl) ⟨472130, by rfl⟩ : syracuseStep 629507 = 944261) B944261
theorem B203539 : Blo 179801 203539 := bstep (se 1 (by rfl) ⟨152654, by rfl⟩ : syracuseStep 203539 = 305309) B305309
theorem B203683 : Blo 179801 203683 := bstep (se 1 (by rfl) ⟨152762, by rfl⟩ : syracuseStep 203683 = 305525) B305525
theorem B3152837 : Blo 179801 3152837 := bstep (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) B591157
theorem B433201 : Blo 179801 433201 := bstep (se 2 (by rfl) ⟨162450, by rfl⟩ : syracuseStep 433201 = 324901) B324901
theorem B203827 : Blo 179801 203827 := bstep (se 1 (by rfl) ⟨152870, by rfl⟩ : syracuseStep 203827 = 305741) B305741
theorem B269443 : Blo 179801 269443 := bstep (se 1 (by rfl) ⟨202082, by rfl⟩ : syracuseStep 269443 = 404165) B404165
theorem B2202805 : Blo 179801 2202805 := bstep (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) B206513
theorem B203971 : Blo 179801 203971 := bstep (se 1 (by rfl) ⟨152978, by rfl⟩ : syracuseStep 203971 = 305957) B305957
theorem B695587 : Blo 179801 695587 := bstep (se 1 (by rfl) ⟨521690, by rfl⟩ : syracuseStep 695587 = 1043381) B1043381
theorem B204115 : Blo 179801 204115 := bstep (se 1 (by rfl) ⟨153086, by rfl⟩ : syracuseStep 204115 = 306173) B306173
theorem B269729 : Blo 179801 269729 := bstep (se 2 (by rfl) ⟨101148, by rfl⟩ : syracuseStep 269729 = 202297) B202297
theorem B269747 : Blo 179801 269747 := bstep (se 1 (by rfl) ⟨202310, by rfl⟩ : syracuseStep 269747 = 404621) B404621
theorem B433603 : Blo 179801 433603 := bstep (se 1 (by rfl) ⟨325202, by rfl⟩ : syracuseStep 433603 = 650405) B650405
theorem B269777 : Blo 179801 269777 := bstep (se 2 (by rfl) ⟨101166, by rfl⟩ : syracuseStep 269777 = 202333) B202333
theorem B269795 : Blo 179801 269795 := bstep (se 1 (by rfl) ⟨202346, by rfl⟩ : syracuseStep 269795 = 404693) B404693
theorem B204259 : Blo 179801 204259 := bstep (se 1 (by rfl) ⟨153194, by rfl⟩ : syracuseStep 204259 = 306389) B306389
theorem B269825 : Blo 179801 269825 := bstep (se 2 (by rfl) ⟨101184, by rfl⟩ : syracuseStep 269825 = 202369) B202369
theorem B269843 : Blo 179801 269843 := bstep (se 1 (by rfl) ⟨202382, by rfl⟩ : syracuseStep 269843 = 404765) B404765
theorem B269873 : Blo 179801 269873 := bstep (se 2 (by rfl) ⟨101202, by rfl⟩ : syracuseStep 269873 = 202405) B202405
theorem B269891 : Blo 179801 269891 := bstep (se 1 (by rfl) ⟨202418, by rfl⟩ : syracuseStep 269891 = 404837) B404837
theorem B269921 : Blo 179801 269921 := bstep (se 2 (by rfl) ⟨101220, by rfl⟩ : syracuseStep 269921 = 202441) B202441
theorem B269939 : Blo 179801 269939 := bstep (se 1 (by rfl) ⟨202454, by rfl⟩ : syracuseStep 269939 = 404909) B404909
theorem B204403 : Blo 179801 204403 := bstep (se 1 (by rfl) ⟨153302, by rfl⟩ : syracuseStep 204403 = 306605) B306605
theorem B269969 : Blo 179801 269969 := bstep (se 2 (by rfl) ⟨101238, by rfl⟩ : syracuseStep 269969 = 202477) B202477
theorem B269987 : Blo 179801 269987 := bstep (se 1 (by rfl) ⟨202490, by rfl⟩ : syracuseStep 269987 = 404981) B404981
theorem B270017 : Blo 179801 270017 := bstep (se 2 (by rfl) ⟨101256, by rfl⟩ : syracuseStep 270017 = 202513) B202513
theorem B270035 : Blo 179801 270035 := bstep (se 1 (by rfl) ⟨202526, by rfl⟩ : syracuseStep 270035 = 405053) B405053
theorem B270065 : Blo 179801 270065 := bstep (se 2 (by rfl) ⟨101274, by rfl⟩ : syracuseStep 270065 = 202549) B202549
theorem B270083 : Blo 179801 270083 := bstep (se 1 (by rfl) ⟨202562, by rfl⟩ : syracuseStep 270083 = 405125) B405125
theorem B204547 : Blo 179801 204547 := bstep (se 1 (by rfl) ⟨153410, by rfl⟩ : syracuseStep 204547 = 306821) B306821
theorem B270113 : Blo 179801 270113 := bstep (se 2 (by rfl) ⟨101292, by rfl⟩ : syracuseStep 270113 = 202585) B202585
theorem B270131 : Blo 179801 270131 := bstep (se 1 (by rfl) ⟨202598, by rfl⟩ : syracuseStep 270131 = 405197) B405197
theorem B270161 : Blo 179801 270161 := bstep (se 2 (by rfl) ⟨101310, by rfl⟩ : syracuseStep 270161 = 202621) B202621
theorem B270179 : Blo 179801 270179 := bstep (se 1 (by rfl) ⟨202634, by rfl⟩ : syracuseStep 270179 = 405269) B405269
theorem B270209 : Blo 179801 270209 := bstep (se 2 (by rfl) ⟨101328, by rfl⟩ : syracuseStep 270209 = 202657) B202657
theorem B270227 : Blo 179801 270227 := bstep (se 1 (by rfl) ⟨202670, by rfl⟩ : syracuseStep 270227 = 405341) B405341
theorem B204691 : Blo 179801 204691 := bstep (se 1 (by rfl) ⟨153518, by rfl⟩ : syracuseStep 204691 = 307037) B307037
theorem B270257 : Blo 179801 270257 := bstep (se 2 (by rfl) ⟨101346, by rfl⟩ : syracuseStep 270257 = 202693) B202693
theorem B270275 : Blo 179801 270275 := bstep (se 1 (by rfl) ⟨202706, by rfl⟩ : syracuseStep 270275 = 405413) B405413
theorem B270305 : Blo 179801 270305 := bstep (se 2 (by rfl) ⟨101364, by rfl⟩ : syracuseStep 270305 = 202729) B202729
theorem B925667 : Blo 179801 925667 := bstep (se 1 (by rfl) ⟨694250, by rfl⟩ : syracuseStep 925667 = 1388501) B1388501
theorem B270323 : Blo 179801 270323 := bstep (se 1 (by rfl) ⟨202742, by rfl⟩ : syracuseStep 270323 = 405485) B405485
theorem B270353 : Blo 179801 270353 := bstep (se 2 (by rfl) ⟨101382, by rfl⟩ : syracuseStep 270353 = 202765) B202765
theorem B270371 : Blo 179801 270371 := bstep (se 1 (by rfl) ⟨202778, by rfl⟩ : syracuseStep 270371 = 405557) B405557
theorem B204835 : Blo 179801 204835 := bstep (se 1 (by rfl) ⟨153626, by rfl⟩ : syracuseStep 204835 = 307253) B307253
theorem B270401 : Blo 179801 270401 := bstep (se 2 (by rfl) ⟨101400, by rfl⟩ : syracuseStep 270401 = 202801) B202801
theorem B270419 : Blo 179801 270419 := bstep (se 1 (by rfl) ⟨202814, by rfl⟩ : syracuseStep 270419 = 405629) B405629
theorem B270449 : Blo 179801 270449 := bstep (se 2 (by rfl) ⟨101418, by rfl⟩ : syracuseStep 270449 = 202837) B202837
theorem B270467 : Blo 179801 270467 := bstep (se 1 (by rfl) ⟨202850, by rfl⟩ : syracuseStep 270467 = 405701) B405701
theorem B270497 : Blo 179801 270497 := bstep (se 2 (by rfl) ⟨101436, by rfl⟩ : syracuseStep 270497 = 202873) B202873
theorem B270515 : Blo 179801 270515 := bstep (se 1 (by rfl) ⟨202886, by rfl⟩ : syracuseStep 270515 = 405773) B405773
theorem B204979 : Blo 179801 204979 := bstep (se 1 (by rfl) ⟨153734, by rfl⟩ : syracuseStep 204979 = 307469) B307469
theorem B270545 : Blo 179801 270545 := bstep (se 2 (by rfl) ⟨101454, by rfl⟩ : syracuseStep 270545 = 202909) B202909
theorem B270563 : Blo 179801 270563 := bstep (se 1 (by rfl) ⟨202922, by rfl⟩ : syracuseStep 270563 = 405845) B405845
theorem B270593 : Blo 179801 270593 := bstep (se 2 (by rfl) ⟨101472, by rfl⟩ : syracuseStep 270593 = 202945) B202945
theorem B270611 : Blo 179801 270611 := bstep (se 1 (by rfl) ⟨202958, by rfl⟩ : syracuseStep 270611 = 405917) B405917
theorem B270641 : Blo 179801 270641 := bstep (se 2 (by rfl) ⟨101490, by rfl⟩ : syracuseStep 270641 = 202981) B202981
theorem B270659 : Blo 179801 270659 := bstep (se 1 (by rfl) ⟨202994, by rfl⟩ : syracuseStep 270659 = 405989) B405989
theorem B205123 : Blo 179801 205123 := bstep (se 1 (by rfl) ⟨153842, by rfl⟩ : syracuseStep 205123 = 307685) B307685
theorem B270689 : Blo 179801 270689 := bstep (se 2 (by rfl) ⟨101508, by rfl⟩ : syracuseStep 270689 = 203017) B203017
theorem B303473 : Blo 179801 303473 := bstep (se 2 (by rfl) ⟨113802, by rfl⟩ : syracuseStep 303473 = 227605) B227605
theorem B270707 : Blo 179801 270707 := bstep (se 1 (by rfl) ⟨203030, by rfl⟩ : syracuseStep 270707 = 406061) B406061
theorem B270737 : Blo 179801 270737 := bstep (se 2 (by rfl) ⟨101526, by rfl⟩ : syracuseStep 270737 = 203053) B203053
theorem B270755 : Blo 179801 270755 := bstep (se 1 (by rfl) ⟨203066, by rfl⟩ : syracuseStep 270755 = 406133) B406133
theorem B270785 : Blo 179801 270785 := bstep (se 2 (by rfl) ⟨101544, by rfl⟩ : syracuseStep 270785 = 203089) B203089
theorem B434641 : Blo 179801 434641 := bstep (se 2 (by rfl) ⟨162990, by rfl⟩ : syracuseStep 434641 = 325981) B325981
theorem B270803 : Blo 179801 270803 := bstep (se 1 (by rfl) ⟨203102, by rfl⟩ : syracuseStep 270803 = 406205) B406205
theorem B205267 : Blo 179801 205267 := bstep (se 1 (by rfl) ⟨153950, by rfl⟩ : syracuseStep 205267 = 307901) B307901
theorem B303601 : Blo 179801 303601 := bstep (se 2 (by rfl) ⟨113850, by rfl⟩ : syracuseStep 303601 = 227701) B227701
theorem B270833 : Blo 179801 270833 := bstep (se 2 (by rfl) ⟨101562, by rfl⟩ : syracuseStep 270833 = 203125) B203125
theorem B270851 : Blo 179801 270851 := bstep (se 1 (by rfl) ⟨203138, by rfl⟩ : syracuseStep 270851 = 406277) B406277
theorem B303635 : Blo 179801 303635 := bstep (se 1 (by rfl) ⟨227726, by rfl⟩ : syracuseStep 303635 = 455453) B455453
theorem B270881 : Blo 179801 270881 := bstep (se 2 (by rfl) ⟨101580, by rfl⟩ : syracuseStep 270881 = 203161) B203161
theorem B270899 : Blo 179801 270899 := bstep (se 1 (by rfl) ⟨203174, by rfl⟩ : syracuseStep 270899 = 406349) B406349
theorem B270929 : Blo 179801 270929 := bstep (se 2 (by rfl) ⟨101598, by rfl⟩ : syracuseStep 270929 = 203197) B203197
theorem B270947 : Blo 179801 270947 := bstep (se 1 (by rfl) ⟨203210, by rfl⟩ : syracuseStep 270947 = 406421) B406421
theorem B205411 : Blo 179801 205411 := bstep (se 1 (by rfl) ⟨154058, by rfl⟩ : syracuseStep 205411 = 308117) B308117
theorem B270977 : Blo 179801 270977 := bstep (se 2 (by rfl) ⟨101616, by rfl⟩ : syracuseStep 270977 = 203233) B203233
theorem B303763 : Blo 179801 303763 := bstep (se 1 (by rfl) ⟨227822, by rfl⟩ : syracuseStep 303763 = 455645) B455645
theorem B270995 : Blo 179801 270995 := bstep (se 1 (by rfl) ⟨203246, by rfl⟩ : syracuseStep 270995 = 406493) B406493
theorem B271025 : Blo 179801 271025 := bstep (se 2 (by rfl) ⟨101634, by rfl⟩ : syracuseStep 271025 = 203269) B203269
theorem B271043 : Blo 179801 271043 := bstep (se 1 (by rfl) ⟨203282, by rfl⟩ : syracuseStep 271043 = 406565) B406565
theorem B271073 : Blo 179801 271073 := bstep (se 2 (by rfl) ⟨101652, by rfl⟩ : syracuseStep 271073 = 203305) B203305
theorem B271091 : Blo 179801 271091 := bstep (se 1 (by rfl) ⟨203318, by rfl⟩ : syracuseStep 271091 = 406637) B406637
theorem B205555 : Blo 179801 205555 := bstep (se 1 (by rfl) ⟨154166, by rfl⟩ : syracuseStep 205555 = 308333) B308333
theorem B926477 : Blo 179801 926477 := bstep (se 3 (by rfl) ⟨173714, by rfl⟩ : syracuseStep 926477 = 347429) B347429
theorem B271121 : Blo 179801 271121 := bstep (se 2 (by rfl) ⟨101670, by rfl⟩ : syracuseStep 271121 = 203341) B203341
theorem B303905 : Blo 179801 303905 := bstep (se 2 (by rfl) ⟨113964, by rfl⟩ : syracuseStep 303905 = 227929) B227929
theorem B271139 : Blo 179801 271139 := bstep (se 1 (by rfl) ⟨203354, by rfl⟩ : syracuseStep 271139 = 406709) B406709
theorem B271169 : Blo 179801 271169 := bstep (se 2 (by rfl) ⟨101688, by rfl⟩ : syracuseStep 271169 = 203377) B203377
theorem B271187 : Blo 179801 271187 := bstep (se 1 (by rfl) ⟨203390, by rfl⟩ : syracuseStep 271187 = 406781) B406781
theorem B271217 : Blo 179801 271217 := bstep (se 2 (by rfl) ⟨101706, by rfl⟩ : syracuseStep 271217 = 203413) B203413
theorem B271235 : Blo 179801 271235 := bstep (se 1 (by rfl) ⟨203426, by rfl⟩ : syracuseStep 271235 = 406853) B406853
theorem B205699 : Blo 179801 205699 := bstep (se 1 (by rfl) ⟨154274, by rfl⟩ : syracuseStep 205699 = 308549) B308549
theorem B304033 : Blo 179801 304033 := bstep (se 2 (by rfl) ⟨114012, by rfl⟩ : syracuseStep 304033 = 228025) B228025
theorem B271265 : Blo 179801 271265 := bstep (se 2 (by rfl) ⟨101724, by rfl⟩ : syracuseStep 271265 = 203449) B203449
theorem B271283 : Blo 179801 271283 := bstep (se 1 (by rfl) ⟨203462, by rfl⟩ : syracuseStep 271283 = 406925) B406925
theorem B304067 : Blo 179801 304067 := bstep (se 1 (by rfl) ⟨228050, by rfl⟩ : syracuseStep 304067 = 456101) B456101
theorem B271313 : Blo 179801 271313 := bstep (se 2 (by rfl) ⟨101742, by rfl⟩ : syracuseStep 271313 = 203485) B203485
theorem B271331 : Blo 179801 271331 := bstep (se 1 (by rfl) ⟨203498, by rfl⟩ : syracuseStep 271331 = 406997) B406997
theorem B271361 : Blo 179801 271361 := bstep (se 2 (by rfl) ⟨101760, by rfl⟩ : syracuseStep 271361 = 203521) B203521
theorem B1057805 : Blo 179801 1057805 := bstep (se 3 (by rfl) ⟨198338, by rfl⟩ : syracuseStep 1057805 = 396677) B396677
theorem B271379 : Blo 179801 271379 := bstep (se 1 (by rfl) ⟨203534, by rfl⟩ : syracuseStep 271379 = 407069) B407069
theorem B205843 : Blo 179801 205843 := bstep (se 1 (by rfl) ⟨154382, by rfl⟩ : syracuseStep 205843 = 308765) B308765
theorem B271409 : Blo 179801 271409 := bstep (se 2 (by rfl) ⟨101778, by rfl⟩ : syracuseStep 271409 = 203557) B203557
theorem B304195 : Blo 179801 304195 := bstep (se 1 (by rfl) ⟨228146, by rfl⟩ : syracuseStep 304195 = 456293) B456293
theorem B271427 : Blo 179801 271427 := bstep (se 1 (by rfl) ⟨203570, by rfl⟩ : syracuseStep 271427 = 407141) B407141
theorem B271457 : Blo 179801 271457 := bstep (se 2 (by rfl) ⟨101796, by rfl⟩ : syracuseStep 271457 = 203593) B203593
theorem B1385585 : Blo 179801 1385585 := bstep (se 2 (by rfl) ⟨519594, by rfl⟩ : syracuseStep 1385585 = 1039189) B1039189
theorem B271475 : Blo 179801 271475 := bstep (se 1 (by rfl) ⟨203606, by rfl⟩ : syracuseStep 271475 = 407213) B407213
theorem B271505 : Blo 179801 271505 := bstep (se 2 (by rfl) ⟨101814, by rfl⟩ : syracuseStep 271505 = 203629) B203629
theorem B271523 : Blo 179801 271523 := bstep (se 1 (by rfl) ⟨203642, by rfl⟩ : syracuseStep 271523 = 407285) B407285
theorem B205987 : Blo 179801 205987 := bstep (se 1 (by rfl) ⟨154490, by rfl⟩ : syracuseStep 205987 = 308981) B308981
theorem B271553 : Blo 179801 271553 := bstep (se 2 (by rfl) ⟨101832, by rfl⟩ : syracuseStep 271553 = 203665) B203665
theorem B304337 : Blo 179801 304337 := bstep (se 2 (by rfl) ⟨114126, by rfl⟩ : syracuseStep 304337 = 228253) B228253
theorem B271571 : Blo 179801 271571 := bstep (se 1 (by rfl) ⟨203678, by rfl⟩ : syracuseStep 271571 = 407357) B407357
theorem B828643 : Blo 179801 828643 := bstep (se 1 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 828643 = 1242965) B1242965
theorem B271601 : Blo 179801 271601 := bstep (se 2 (by rfl) ⟨101850, by rfl⟩ : syracuseStep 271601 = 203701) B203701
theorem B271619 : Blo 179801 271619 := bstep (se 1 (by rfl) ⟨203714, by rfl⟩ : syracuseStep 271619 = 407429) B407429
theorem B271649 : Blo 179801 271649 := bstep (se 2 (by rfl) ⟨101868, by rfl⟩ : syracuseStep 271649 = 203737) B203737
theorem B271667 : Blo 179801 271667 := bstep (se 1 (by rfl) ⟨203750, by rfl⟩ : syracuseStep 271667 = 407501) B407501
theorem B206131 : Blo 179801 206131 := bstep (se 1 (by rfl) ⟨154598, by rfl⟩ : syracuseStep 206131 = 309197) B309197
theorem B1123661 : Blo 179801 1123661 := bstep (se 3 (by rfl) ⟨210686, by rfl⟩ : syracuseStep 1123661 = 421373) B421373
theorem B304465 : Blo 179801 304465 := bstep (se 2 (by rfl) ⟨114174, by rfl⟩ : syracuseStep 304465 = 228349) B228349
theorem B271697 : Blo 179801 271697 := bstep (se 2 (by rfl) ⟨101886, by rfl⟩ : syracuseStep 271697 = 203773) B203773
theorem B271715 : Blo 179801 271715 := bstep (se 1 (by rfl) ⟨203786, by rfl⟩ : syracuseStep 271715 = 407573) B407573
theorem B304499 : Blo 179801 304499 := bstep (se 1 (by rfl) ⟨228374, by rfl⟩ : syracuseStep 304499 = 456749) B456749
theorem B271745 : Blo 179801 271745 := bstep (se 2 (by rfl) ⟨101904, by rfl⟩ : syracuseStep 271745 = 203809) B203809
theorem B271763 : Blo 179801 271763 := bstep (se 1 (by rfl) ⟨203822, by rfl⟩ : syracuseStep 271763 = 407645) B407645
theorem B271793 : Blo 179801 271793 := bstep (se 2 (by rfl) ⟨101922, by rfl⟩ : syracuseStep 271793 = 203845) B203845
theorem B271811 : Blo 179801 271811 := bstep (se 1 (by rfl) ⟨203858, by rfl⟩ : syracuseStep 271811 = 407717) B407717
theorem B206275 : Blo 179801 206275 := bstep (se 1 (by rfl) ⟨154706, by rfl⟩ : syracuseStep 206275 = 309413) B309413
theorem B697805 : Blo 179801 697805 := bstep (se 3 (by rfl) ⟨130838, by rfl⟩ : syracuseStep 697805 = 261677) B261677
theorem B271841 : Blo 179801 271841 := bstep (se 2 (by rfl) ⟨101940, by rfl⟩ : syracuseStep 271841 = 203881) B203881
theorem B304627 : Blo 179801 304627 := bstep (se 1 (by rfl) ⟨228470, by rfl⟩ : syracuseStep 304627 = 456941) B456941
theorem B271859 : Blo 179801 271859 := bstep (se 1 (by rfl) ⟨203894, by rfl⟩ : syracuseStep 271859 = 407789) B407789
theorem B271889 : Blo 179801 271889 := bstep (se 2 (by rfl) ⟨101958, by rfl⟩ : syracuseStep 271889 = 203917) B203917
theorem B271907 : Blo 179801 271907 := bstep (se 1 (by rfl) ⟨203930, by rfl⟩ : syracuseStep 271907 = 407861) B407861
theorem B271937 : Blo 179801 271937 := bstep (se 2 (by rfl) ⟨101976, by rfl⟩ : syracuseStep 271937 = 203953) B203953
theorem B271955 : Blo 179801 271955 := bstep (se 1 (by rfl) ⟨203966, by rfl⟩ : syracuseStep 271955 = 407933) B407933
theorem B206419 : Blo 179801 206419 := bstep (se 1 (by rfl) ⟨154814, by rfl⟩ : syracuseStep 206419 = 309629) B309629
theorem B271985 : Blo 179801 271985 := bstep (se 2 (by rfl) ⟨101994, by rfl⟩ : syracuseStep 271985 = 203989) B203989
theorem B304769 : Blo 179801 304769 := bstep (se 2 (by rfl) ⟨114288, by rfl⟩ : syracuseStep 304769 = 228577) B228577
theorem B272003 : Blo 179801 272003 := bstep (se 1 (by rfl) ⟨204002, by rfl⟩ : syracuseStep 272003 = 408005) B408005
theorem B272033 : Blo 179801 272033 := bstep (se 2 (by rfl) ⟨102012, by rfl⟩ : syracuseStep 272033 = 204025) B204025
theorem B272051 : Blo 179801 272051 := bstep (se 1 (by rfl) ⟨204038, by rfl⟩ : syracuseStep 272051 = 408077) B408077
theorem B272081 : Blo 179801 272081 := bstep (se 2 (by rfl) ⟨102030, by rfl⟩ : syracuseStep 272081 = 204061) B204061
theorem B272099 : Blo 179801 272099 := bstep (se 1 (by rfl) ⟨204074, by rfl⟩ : syracuseStep 272099 = 408149) B408149
theorem B206563 : Blo 179801 206563 := bstep (se 1 (by rfl) ⟨154922, by rfl⟩ : syracuseStep 206563 = 309845) B309845
theorem B1124081 : Blo 179801 1124081 := bstep (se 2 (by rfl) ⟨421530, by rfl⟩ : syracuseStep 1124081 = 843061) B843061
theorem B304897 : Blo 179801 304897 := bstep (se 2 (by rfl) ⟨114336, by rfl⟩ : syracuseStep 304897 = 228673) B228673
theorem B272129 : Blo 179801 272129 := bstep (se 2 (by rfl) ⟨102048, by rfl⟩ : syracuseStep 272129 = 204097) B204097
theorem B272147 : Blo 179801 272147 := bstep (se 1 (by rfl) ⟨204110, by rfl⟩ : syracuseStep 272147 = 408221) B408221
theorem B304931 : Blo 179801 304931 := bstep (se 1 (by rfl) ⟨228698, by rfl⟩ : syracuseStep 304931 = 457397) B457397
theorem B272177 : Blo 179801 272177 := bstep (se 2 (by rfl) ⟨102066, by rfl⟩ : syracuseStep 272177 = 204133) B204133
theorem B272195 : Blo 179801 272195 := bstep (se 1 (by rfl) ⟨204146, by rfl⟩ : syracuseStep 272195 = 408293) B408293
theorem B272225 : Blo 179801 272225 := bstep (se 2 (by rfl) ⟨102084, by rfl⟩ : syracuseStep 272225 = 204169) B204169
theorem B272243 : Blo 179801 272243 := bstep (se 1 (by rfl) ⟨204182, by rfl⟩ : syracuseStep 272243 = 408365) B408365
theorem B206707 : Blo 179801 206707 := bstep (se 1 (by rfl) ⟨155030, by rfl⟩ : syracuseStep 206707 = 310061) B310061
theorem B272273 : Blo 179801 272273 := bstep (se 2 (by rfl) ⟨102102, by rfl⟩ : syracuseStep 272273 = 204205) B204205
theorem B305059 : Blo 179801 305059 := bstep (se 1 (by rfl) ⟨228794, by rfl⟩ : syracuseStep 305059 = 457589) B457589
theorem B272291 : Blo 179801 272291 := bstep (se 1 (by rfl) ⟨204218, by rfl⟩ : syracuseStep 272291 = 408437) B408437
theorem B272321 : Blo 179801 272321 := bstep (se 2 (by rfl) ⟨102120, by rfl⟩ : syracuseStep 272321 = 204241) B204241
theorem B272339 : Blo 179801 272339 := bstep (se 1 (by rfl) ⟨204254, by rfl⟩ : syracuseStep 272339 = 408509) B408509
theorem B272369 : Blo 179801 272369 := bstep (se 2 (by rfl) ⟨102138, by rfl⟩ : syracuseStep 272369 = 204277) B204277
theorem B272387 : Blo 179801 272387 := bstep (se 1 (by rfl) ⟨204290, by rfl⟩ : syracuseStep 272387 = 408581) B408581
theorem B272417 : Blo 179801 272417 := bstep (se 2 (by rfl) ⟨102156, by rfl⟩ : syracuseStep 272417 = 204313) B204313
theorem B305201 : Blo 179801 305201 := bstep (se 2 (by rfl) ⟨114450, by rfl⟩ : syracuseStep 305201 = 228901) B228901
theorem B272435 : Blo 179801 272435 := bstep (se 1 (by rfl) ⟨204326, by rfl⟩ : syracuseStep 272435 = 408653) B408653
theorem B272465 : Blo 179801 272465 := bstep (se 2 (by rfl) ⟨102174, by rfl⟩ : syracuseStep 272465 = 204349) B204349
theorem B272483 : Blo 179801 272483 := bstep (se 1 (by rfl) ⟨204362, by rfl⟩ : syracuseStep 272483 = 408725) B408725
theorem B272513 : Blo 179801 272513 := bstep (se 2 (by rfl) ⟨102192, by rfl⟩ : syracuseStep 272513 = 204385) B204385
theorem B272531 : Blo 179801 272531 := bstep (se 1 (by rfl) ⟨204398, by rfl⟩ : syracuseStep 272531 = 408797) B408797
theorem B305329 : Blo 179801 305329 := bstep (se 2 (by rfl) ⟨114498, by rfl⟩ : syracuseStep 305329 = 228997) B228997
theorem B272561 : Blo 179801 272561 := bstep (se 2 (by rfl) ⟨102210, by rfl⟩ : syracuseStep 272561 = 204421) B204421
theorem B272579 : Blo 179801 272579 := bstep (se 1 (by rfl) ⟨204434, by rfl⟩ : syracuseStep 272579 = 408869) B408869
theorem B2009285 : Blo 179801 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B305363 : Blo 179801 305363 := bstep (se 1 (by rfl) ⟨229022, by rfl⟩ : syracuseStep 305363 = 458045) B458045
theorem B272609 : Blo 179801 272609 := bstep (se 2 (by rfl) ⟨102228, by rfl⟩ : syracuseStep 272609 = 204457) B204457
theorem B272627 : Blo 179801 272627 := bstep (se 1 (by rfl) ⟨204470, by rfl⟩ : syracuseStep 272627 = 408941) B408941
theorem B1059077 : Blo 179801 1059077 := bstep (se 4 (by rfl) ⟨99288, by rfl⟩ : syracuseStep 1059077 = 198577) B198577
theorem B272657 : Blo 179801 272657 := bstep (se 2 (by rfl) ⟨102246, by rfl⟩ : syracuseStep 272657 = 204493) B204493
theorem B272675 : Blo 179801 272675 := bstep (se 1 (by rfl) ⟨204506, by rfl⟩ : syracuseStep 272675 = 409013) B409013
theorem B272705 : Blo 179801 272705 := bstep (se 2 (by rfl) ⟨102264, by rfl⟩ : syracuseStep 272705 = 204529) B204529
theorem B305491 : Blo 179801 305491 := bstep (se 1 (by rfl) ⟨229118, by rfl⟩ : syracuseStep 305491 = 458237) B458237
theorem B272723 : Blo 179801 272723 := bstep (se 1 (by rfl) ⟨204542, by rfl⟩ : syracuseStep 272723 = 409085) B409085
theorem B272753 : Blo 179801 272753 := bstep (se 2 (by rfl) ⟨102282, by rfl⟩ : syracuseStep 272753 = 204565) B204565
theorem B272771 : Blo 179801 272771 := bstep (se 1 (by rfl) ⟨204578, by rfl⟩ : syracuseStep 272771 = 409157) B409157
theorem B272801 : Blo 179801 272801 := bstep (se 2 (by rfl) ⟨102300, by rfl⟩ : syracuseStep 272801 = 204601) B204601
theorem B272819 : Blo 179801 272819 := bstep (se 1 (by rfl) ⟨204614, by rfl⟩ : syracuseStep 272819 = 409229) B409229
theorem B272849 : Blo 179801 272849 := bstep (se 2 (by rfl) ⟨102318, by rfl⟩ : syracuseStep 272849 = 204637) B204637
theorem B305633 : Blo 179801 305633 := bstep (se 2 (by rfl) ⟨114612, by rfl⟩ : syracuseStep 305633 = 229225) B229225
theorem B272867 : Blo 179801 272867 := bstep (se 1 (by rfl) ⟨204650, by rfl⟩ : syracuseStep 272867 = 409301) B409301
theorem B272897 : Blo 179801 272897 := bstep (se 2 (by rfl) ⟨102336, by rfl⟩ : syracuseStep 272897 = 204673) B204673
theorem B272915 : Blo 179801 272915 := bstep (se 1 (by rfl) ⟨204686, by rfl⟩ : syracuseStep 272915 = 409373) B409373
theorem B272945 : Blo 179801 272945 := bstep (se 2 (by rfl) ⟨102354, by rfl⟩ : syracuseStep 272945 = 204709) B204709
theorem B272963 : Blo 179801 272963 := bstep (se 1 (by rfl) ⟨204722, by rfl⟩ : syracuseStep 272963 = 409445) B409445
theorem B305761 : Blo 179801 305761 := bstep (se 2 (by rfl) ⟨114660, by rfl⟩ : syracuseStep 305761 = 229321) B229321
theorem B272993 : Blo 179801 272993 := bstep (se 2 (by rfl) ⟨102372, by rfl⟩ : syracuseStep 272993 = 204745) B204745
theorem B273011 : Blo 179801 273011 := bstep (se 1 (by rfl) ⟨204758, by rfl⟩ : syracuseStep 273011 = 409517) B409517
theorem B305795 : Blo 179801 305795 := bstep (se 1 (by rfl) ⟨229346, by rfl⟩ : syracuseStep 305795 = 458693) B458693
theorem B273041 : Blo 179801 273041 := bstep (se 2 (by rfl) ⟨102390, by rfl⟩ : syracuseStep 273041 = 204781) B204781
theorem B273059 : Blo 179801 273059 := bstep (se 1 (by rfl) ⟨204794, by rfl⟩ : syracuseStep 273059 = 409589) B409589
theorem B273089 : Blo 179801 273089 := bstep (se 2 (by rfl) ⟨102408, by rfl⟩ : syracuseStep 273089 = 204817) B204817
theorem B273107 : Blo 179801 273107 := bstep (se 1 (by rfl) ⟨204830, by rfl⟩ : syracuseStep 273107 = 409661) B409661
theorem B273137 : Blo 179801 273137 := bstep (se 2 (by rfl) ⟨102426, by rfl⟩ : syracuseStep 273137 = 204853) B204853
theorem B305923 : Blo 179801 305923 := bstep (se 1 (by rfl) ⟨229442, by rfl⟩ : syracuseStep 305923 = 458885) B458885
theorem B273155 : Blo 179801 273155 := bstep (se 1 (by rfl) ⟨204866, by rfl⟩ : syracuseStep 273155 = 409733) B409733
theorem B273185 : Blo 179801 273185 := bstep (se 2 (by rfl) ⟨102444, by rfl⟩ : syracuseStep 273185 = 204889) B204889
theorem B273203 : Blo 179801 273203 := bstep (se 1 (by rfl) ⟨204902, by rfl⟩ : syracuseStep 273203 = 409805) B409805
theorem B273233 : Blo 179801 273233 := bstep (se 2 (by rfl) ⟨102462, by rfl⟩ : syracuseStep 273233 = 204925) B204925
theorem B273251 : Blo 179801 273251 := bstep (se 1 (by rfl) ⟨204938, by rfl⟩ : syracuseStep 273251 = 409877) B409877
theorem B273281 : Blo 179801 273281 := bstep (se 2 (by rfl) ⟨102480, by rfl⟩ : syracuseStep 273281 = 204961) B204961
theorem B306065 : Blo 179801 306065 := bstep (se 2 (by rfl) ⟨114774, by rfl⟩ : syracuseStep 306065 = 229549) B229549
theorem B273299 : Blo 179801 273299 := bstep (se 1 (by rfl) ⟨204974, by rfl⟩ : syracuseStep 273299 = 409949) B409949
theorem B273329 : Blo 179801 273329 := bstep (se 2 (by rfl) ⟨102498, by rfl⟩ : syracuseStep 273329 = 204997) B204997
theorem B273347 : Blo 179801 273347 := bstep (se 1 (by rfl) ⟨205010, by rfl⟩ : syracuseStep 273347 = 410021) B410021
theorem B273377 : Blo 179801 273377 := bstep (se 2 (by rfl) ⟨102516, by rfl⟩ : syracuseStep 273377 = 205033) B205033
theorem B273395 : Blo 179801 273395 := bstep (se 1 (by rfl) ⟨205046, by rfl⟩ : syracuseStep 273395 = 410093) B410093
theorem B306193 : Blo 179801 306193 := bstep (se 2 (by rfl) ⟨114822, by rfl⟩ : syracuseStep 306193 = 229645) B229645
theorem B273425 : Blo 179801 273425 := bstep (se 2 (by rfl) ⟨102534, by rfl⟩ : syracuseStep 273425 = 205069) B205069
theorem B273443 : Blo 179801 273443 := bstep (se 1 (by rfl) ⟨205082, by rfl⟩ : syracuseStep 273443 = 410165) B410165
theorem B306227 : Blo 179801 306227 := bstep (se 1 (by rfl) ⟨229670, by rfl⟩ : syracuseStep 306227 = 459341) B459341
theorem B273473 : Blo 179801 273473 := bstep (se 2 (by rfl) ⟨102552, by rfl⟩ : syracuseStep 273473 = 205105) B205105
theorem B273491 : Blo 179801 273491 := bstep (se 1 (by rfl) ⟨205118, by rfl⟩ : syracuseStep 273491 = 410237) B410237
theorem B1551473 : Blo 179801 1551473 := bstep (se 2 (by rfl) ⟨581802, by rfl⟩ : syracuseStep 1551473 = 1163605) B1163605
theorem B273521 : Blo 179801 273521 := bstep (se 2 (by rfl) ⟨102570, by rfl⟩ : syracuseStep 273521 = 205141) B205141
theorem B273539 : Blo 179801 273539 := bstep (se 1 (by rfl) ⟨205154, by rfl⟩ : syracuseStep 273539 = 410309) B410309
theorem B273569 : Blo 179801 273569 := bstep (se 2 (by rfl) ⟨102588, by rfl⟩ : syracuseStep 273569 = 205177) B205177
theorem B404657 : Blo 179801 404657 := bstep (se 2 (by rfl) ⟨151746, by rfl⟩ : syracuseStep 404657 = 303493) B303493
theorem B306355 : Blo 179801 306355 := bstep (se 1 (by rfl) ⟨229766, by rfl⟩ : syracuseStep 306355 = 459533) B459533
theorem B273587 : Blo 179801 273587 := bstep (se 1 (by rfl) ⟨205190, by rfl⟩ : syracuseStep 273587 = 410381) B410381
theorem B404675 : Blo 179801 404675 := bstep (se 1 (by rfl) ⟨303506, by rfl⟩ : syracuseStep 404675 = 607013) B607013
theorem B273617 : Blo 179801 273617 := bstep (se 2 (by rfl) ⟨102606, by rfl⟩ : syracuseStep 273617 = 205213) B205213
theorem B273635 : Blo 179801 273635 := bstep (se 1 (by rfl) ⟨205226, by rfl⟩ : syracuseStep 273635 = 410453) B410453
theorem B273665 : Blo 179801 273665 := bstep (se 2 (by rfl) ⟨102624, by rfl⟩ : syracuseStep 273665 = 205249) B205249
theorem B437507 : Blo 179801 437507 := bstep (se 1 (by rfl) ⟨328130, by rfl⟩ : syracuseStep 437507 = 656261) B656261
theorem B273683 : Blo 179801 273683 := bstep (se 1 (by rfl) ⟨205262, by rfl⟩ : syracuseStep 273683 = 410525) B410525
theorem B273713 : Blo 179801 273713 := bstep (se 2 (by rfl) ⟨102642, by rfl⟩ : syracuseStep 273713 = 205285) B205285
theorem B306497 : Blo 179801 306497 := bstep (se 2 (by rfl) ⟨114936, by rfl⟩ : syracuseStep 306497 = 229873) B229873
theorem B273731 : Blo 179801 273731 := bstep (se 1 (by rfl) ⟨205298, by rfl⟩ : syracuseStep 273731 = 410597) B410597
theorem B273761 : Blo 179801 273761 := bstep (se 2 (by rfl) ⟨102660, by rfl⟩ : syracuseStep 273761 = 205321) B205321
theorem B273779 : Blo 179801 273779 := bstep (se 1 (by rfl) ⟨205334, by rfl⟩ : syracuseStep 273779 = 410669) B410669
theorem B273809 : Blo 179801 273809 := bstep (se 2 (by rfl) ⟨102678, by rfl⟩ : syracuseStep 273809 = 205357) B205357
theorem B273827 : Blo 179801 273827 := bstep (se 1 (by rfl) ⟨205370, by rfl⟩ : syracuseStep 273827 = 410741) B410741
theorem B306625 : Blo 179801 306625 := bstep (se 2 (by rfl) ⟨114984, by rfl⟩ : syracuseStep 306625 = 229969) B229969
theorem B273857 : Blo 179801 273857 := bstep (se 2 (by rfl) ⟨102696, by rfl⟩ : syracuseStep 273857 = 205393) B205393
theorem B1027525 : Blo 179801 1027525 := bstep (se 4 (by rfl) ⟨96330, by rfl⟩ : syracuseStep 1027525 = 192661) B192661
theorem B404945 : Blo 179801 404945 := bstep (se 2 (by rfl) ⟨151854, by rfl⟩ : syracuseStep 404945 = 303709) B303709
theorem B273875 : Blo 179801 273875 := bstep (se 1 (by rfl) ⟨205406, by rfl⟩ : syracuseStep 273875 = 410813) B410813
theorem B404963 : Blo 179801 404963 := bstep (se 1 (by rfl) ⟨303722, by rfl⟩ : syracuseStep 404963 = 607445) B607445
theorem B306659 : Blo 179801 306659 := bstep (se 1 (by rfl) ⟨229994, by rfl⟩ : syracuseStep 306659 = 459989) B459989
theorem B273905 : Blo 179801 273905 := bstep (se 2 (by rfl) ⟨102714, by rfl⟩ : syracuseStep 273905 = 205429) B205429
theorem B273923 : Blo 179801 273923 := bstep (se 1 (by rfl) ⟨205442, by rfl⟩ : syracuseStep 273923 = 410885) B410885
theorem B273953 : Blo 179801 273953 := bstep (se 2 (by rfl) ⟨102732, by rfl⟩ : syracuseStep 273953 = 205465) B205465
theorem B273971 : Blo 179801 273971 := bstep (se 1 (by rfl) ⟨205478, by rfl⟩ : syracuseStep 273971 = 410957) B410957
theorem B274001 : Blo 179801 274001 := bstep (se 2 (by rfl) ⟨102750, by rfl⟩ : syracuseStep 274001 = 205501) B205501
theorem B306787 : Blo 179801 306787 := bstep (se 1 (by rfl) ⟨230090, by rfl⟩ : syracuseStep 306787 = 460181) B460181
theorem B274019 : Blo 179801 274019 := bstep (se 1 (by rfl) ⟨205514, by rfl⟩ : syracuseStep 274019 = 411029) B411029
theorem B929393 : Blo 179801 929393 := bstep (se 2 (by rfl) ⟨348522, by rfl⟩ : syracuseStep 929393 = 697045) B697045
theorem B274049 : Blo 179801 274049 := bstep (se 2 (by rfl) ⟨102768, by rfl⟩ : syracuseStep 274049 = 205537) B205537
theorem B274067 : Blo 179801 274067 := bstep (se 1 (by rfl) ⟨205550, by rfl⟩ : syracuseStep 274067 = 411101) B411101
theorem B274097 : Blo 179801 274097 := bstep (se 2 (by rfl) ⟨102786, by rfl⟩ : syracuseStep 274097 = 205573) B205573
theorem B274099 : Blo 179801 274099 := bstep (se 1 (by rfl) ⟨205574, by rfl⟩ : syracuseStep 274099 = 411149) B411149
theorem B274115 : Blo 179801 274115 := bstep (se 1 (by rfl) ⟨205586, by rfl⟩ : syracuseStep 274115 = 411173) B411173
theorem B274145 : Blo 179801 274145 := bstep (se 2 (by rfl) ⟨102804, by rfl⟩ : syracuseStep 274145 = 205609) B205609
theorem B405233 : Blo 179801 405233 := bstep (se 2 (by rfl) ⟨151962, by rfl⟩ : syracuseStep 405233 = 303925) B303925
theorem B306929 : Blo 179801 306929 := bstep (se 2 (by rfl) ⟨115098, by rfl⟩ : syracuseStep 306929 = 230197) B230197
theorem B274163 : Blo 179801 274163 := bstep (se 1 (by rfl) ⟨205622, by rfl⟩ : syracuseStep 274163 = 411245) B411245
theorem B405251 : Blo 179801 405251 := bstep (se 1 (by rfl) ⟨303938, by rfl⟩ : syracuseStep 405251 = 607877) B607877
theorem B274193 : Blo 179801 274193 := bstep (se 2 (by rfl) ⟨102822, by rfl⟩ : syracuseStep 274193 = 205645) B205645
theorem B274211 : Blo 179801 274211 := bstep (se 1 (by rfl) ⟨205658, by rfl⟩ : syracuseStep 274211 = 411317) B411317
theorem B274241 : Blo 179801 274241 := bstep (se 2 (by rfl) ⟨102840, by rfl⟩ : syracuseStep 274241 = 205681) B205681
theorem B274259 : Blo 179801 274259 := bstep (se 1 (by rfl) ⟨205694, by rfl⟩ : syracuseStep 274259 = 411389) B411389
theorem B307057 : Blo 179801 307057 := bstep (se 2 (by rfl) ⟨115146, by rfl⟩ : syracuseStep 307057 = 230293) B230293
theorem B274289 : Blo 179801 274289 := bstep (se 2 (by rfl) ⟨102858, by rfl⟩ : syracuseStep 274289 = 205717) B205717
theorem B274307 : Blo 179801 274307 := bstep (se 1 (by rfl) ⟨205730, by rfl⟩ : syracuseStep 274307 = 411461) B411461
theorem B307091 : Blo 179801 307091 := bstep (se 1 (by rfl) ⟨230318, by rfl⟩ : syracuseStep 307091 = 460637) B460637
theorem B274337 : Blo 179801 274337 := bstep (se 2 (by rfl) ⟨102876, by rfl⟩ : syracuseStep 274337 = 205753) B205753
theorem B274355 : Blo 179801 274355 := bstep (se 1 (by rfl) ⟨205766, by rfl⟩ : syracuseStep 274355 = 411533) B411533
theorem B274385 : Blo 179801 274385 := bstep (se 2 (by rfl) ⟨102894, by rfl⟩ : syracuseStep 274385 = 205789) B205789
theorem B274403 : Blo 179801 274403 := bstep (se 1 (by rfl) ⟨205802, by rfl⟩ : syracuseStep 274403 = 411605) B411605
theorem B274433 : Blo 179801 274433 := bstep (se 2 (by rfl) ⟨102912, by rfl⟩ : syracuseStep 274433 = 205825) B205825
theorem B405521 : Blo 179801 405521 := bstep (se 2 (by rfl) ⟨152070, by rfl⟩ : syracuseStep 405521 = 304141) B304141
theorem B307219 : Blo 179801 307219 := bstep (se 1 (by rfl) ⟨230414, by rfl⟩ : syracuseStep 307219 = 460829) B460829
theorem B274451 : Blo 179801 274451 := bstep (se 1 (by rfl) ⟨205838, by rfl⟩ : syracuseStep 274451 = 411677) B411677
theorem B405539 : Blo 179801 405539 := bstep (se 1 (by rfl) ⟨304154, by rfl⟩ : syracuseStep 405539 = 608309) B608309
theorem B536611 : Blo 179801 536611 := bstep (se 1 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 536611 = 804917) B804917
theorem B274481 : Blo 179801 274481 := bstep (se 2 (by rfl) ⟨102930, by rfl⟩ : syracuseStep 274481 = 205861) B205861
theorem B274499 : Blo 179801 274499 := bstep (se 1 (by rfl) ⟨205874, by rfl⟩ : syracuseStep 274499 = 411749) B411749
theorem B274529 : Blo 179801 274529 := bstep (se 2 (by rfl) ⟨102948, by rfl⟩ : syracuseStep 274529 = 205897) B205897
theorem B274547 : Blo 179801 274547 := bstep (se 1 (by rfl) ⟨205910, by rfl⟩ : syracuseStep 274547 = 411821) B411821
theorem B274577 : Blo 179801 274577 := bstep (se 2 (by rfl) ⟨102966, by rfl⟩ : syracuseStep 274577 = 205933) B205933
theorem B307361 : Blo 179801 307361 := bstep (se 2 (by rfl) ⟨115260, by rfl⟩ : syracuseStep 307361 = 230521) B230521
theorem B274595 : Blo 179801 274595 := bstep (se 1 (by rfl) ⟨205946, by rfl⟩ : syracuseStep 274595 = 411893) B411893
theorem B274625 : Blo 179801 274625 := bstep (se 2 (by rfl) ⟨102984, by rfl⟩ : syracuseStep 274625 = 205969) B205969
theorem B274643 : Blo 179801 274643 := bstep (se 1 (by rfl) ⟨205982, by rfl⟩ : syracuseStep 274643 = 411965) B411965
theorem B2470115 : Blo 179801 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B372977 : Blo 179801 372977 := bstep (se 2 (by rfl) ⟨139866, by rfl⟩ : syracuseStep 372977 = 279733) B279733
theorem B274673 : Blo 179801 274673 := bstep (se 2 (by rfl) ⟨103002, by rfl⟩ : syracuseStep 274673 = 206005) B206005
theorem B274691 : Blo 179801 274691 := bstep (se 1 (by rfl) ⟨206018, by rfl⟩ : syracuseStep 274691 = 412037) B412037
theorem B307489 : Blo 179801 307489 := bstep (se 2 (by rfl) ⟨115308, by rfl⟩ : syracuseStep 307489 = 230617) B230617
theorem B274721 : Blo 179801 274721 := bstep (se 2 (by rfl) ⟨103020, by rfl⟩ : syracuseStep 274721 = 206041) B206041
theorem B405809 : Blo 179801 405809 := bstep (se 2 (by rfl) ⟨152178, by rfl⟩ : syracuseStep 405809 = 304357) B304357
theorem B274739 : Blo 179801 274739 := bstep (se 1 (by rfl) ⟨206054, by rfl⟩ : syracuseStep 274739 = 412109) B412109
theorem B405827 : Blo 179801 405827 := bstep (se 1 (by rfl) ⟨304370, by rfl⟩ : syracuseStep 405827 = 608741) B608741
theorem B307523 : Blo 179801 307523 := bstep (se 1 (by rfl) ⟨230642, by rfl⟩ : syracuseStep 307523 = 461285) B461285
theorem B274769 : Blo 179801 274769 := bstep (se 2 (by rfl) ⟨103038, by rfl⟩ : syracuseStep 274769 = 206077) B206077
theorem B274787 : Blo 179801 274787 := bstep (se 1 (by rfl) ⟨206090, by rfl⟩ : syracuseStep 274787 = 412181) B412181
theorem B274817 : Blo 179801 274817 := bstep (se 2 (by rfl) ⟨103056, by rfl⟩ : syracuseStep 274817 = 206113) B206113
theorem B274835 : Blo 179801 274835 := bstep (se 1 (by rfl) ⟨206126, by rfl⟩ : syracuseStep 274835 = 412253) B412253
theorem B274865 : Blo 179801 274865 := bstep (se 2 (by rfl) ⟨103074, by rfl⟩ : syracuseStep 274865 = 206149) B206149
theorem B307651 : Blo 179801 307651 := bstep (se 1 (by rfl) ⟨230738, by rfl⟩ : syracuseStep 307651 = 461477) B461477
theorem B274883 : Blo 179801 274883 := bstep (se 1 (by rfl) ⟨206162, by rfl⟩ : syracuseStep 274883 = 412325) B412325
theorem B930253 : Blo 179801 930253 := bstep (se 3 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 930253 = 348845) B348845
theorem B274913 : Blo 179801 274913 := bstep (se 2 (by rfl) ⟨103092, by rfl⟩ : syracuseStep 274913 = 206185) B206185
theorem B274931 : Blo 179801 274931 := bstep (se 1 (by rfl) ⟨206198, by rfl⟩ : syracuseStep 274931 = 412397) B412397
theorem B274961 : Blo 179801 274961 := bstep (se 2 (by rfl) ⟨103110, by rfl⟩ : syracuseStep 274961 = 206221) B206221
theorem B274979 : Blo 179801 274979 := bstep (se 1 (by rfl) ⟨206234, by rfl⟩ : syracuseStep 274979 = 412469) B412469
theorem B275009 : Blo 179801 275009 := bstep (se 2 (by rfl) ⟨103128, by rfl⟩ : syracuseStep 275009 = 206257) B206257
theorem B406097 : Blo 179801 406097 := bstep (se 2 (by rfl) ⟨152286, by rfl⟩ : syracuseStep 406097 = 304573) B304573
theorem B307793 : Blo 179801 307793 := bstep (se 2 (by rfl) ⟨115422, by rfl⟩ : syracuseStep 307793 = 230845) B230845
theorem B275027 : Blo 179801 275027 := bstep (se 1 (by rfl) ⟨206270, by rfl⟩ : syracuseStep 275027 = 412541) B412541
theorem B275041 : Blo 179801 275041 := bstep (se 2 (by rfl) ⟨103140, by rfl⟩ : syracuseStep 275041 = 206281) B206281
theorem B406115 : Blo 179801 406115 := bstep (se 1 (by rfl) ⟨304586, by rfl⟩ : syracuseStep 406115 = 609173) B609173
theorem B275057 : Blo 179801 275057 := bstep (se 2 (by rfl) ⟨103146, by rfl⟩ : syracuseStep 275057 = 206293) B206293
theorem B275075 : Blo 179801 275075 := bstep (se 1 (by rfl) ⟨206306, by rfl⟩ : syracuseStep 275075 = 412613) B412613
theorem B275105 : Blo 179801 275105 := bstep (se 2 (by rfl) ⟨103164, by rfl⟩ : syracuseStep 275105 = 206329) B206329
theorem B930467 : Blo 179801 930467 := bstep (se 1 (by rfl) ⟨697850, by rfl⟩ : syracuseStep 930467 = 1395701) B1395701
theorem B438947 : Blo 179801 438947 := bstep (se 1 (by rfl) ⟨329210, by rfl⟩ : syracuseStep 438947 = 658421) B658421
theorem B275123 : Blo 179801 275123 := bstep (se 1 (by rfl) ⟨206342, by rfl⟩ : syracuseStep 275123 = 412685) B412685
theorem B307921 : Blo 179801 307921 := bstep (se 2 (by rfl) ⟨115470, by rfl⟩ : syracuseStep 307921 = 230941) B230941
theorem B275153 : Blo 179801 275153 := bstep (se 2 (by rfl) ⟨103182, by rfl⟩ : syracuseStep 275153 = 206365) B206365
theorem B275171 : Blo 179801 275171 := bstep (se 1 (by rfl) ⟨206378, by rfl⟩ : syracuseStep 275171 = 412757) B412757
theorem B307955 : Blo 179801 307955 := bstep (se 1 (by rfl) ⟨230966, by rfl⟩ : syracuseStep 307955 = 461933) B461933
theorem B275201 : Blo 179801 275201 := bstep (se 2 (by rfl) ⟨103200, by rfl⟩ : syracuseStep 275201 = 206401) B206401
theorem B275219 : Blo 179801 275219 := bstep (se 1 (by rfl) ⟨206414, by rfl⟩ : syracuseStep 275219 = 412829) B412829
theorem B275249 : Blo 179801 275249 := bstep (se 2 (by rfl) ⟨103218, by rfl⟩ : syracuseStep 275249 = 206437) B206437
theorem B275267 : Blo 179801 275267 := bstep (se 1 (by rfl) ⟨206450, by rfl⟩ : syracuseStep 275267 = 412901) B412901
theorem B439121 : Blo 179801 439121 := bstep (se 2 (by rfl) ⟨164670, by rfl⟩ : syracuseStep 439121 = 329341) B329341
theorem B275297 : Blo 179801 275297 := bstep (se 2 (by rfl) ⟨103236, by rfl⟩ : syracuseStep 275297 = 206473) B206473
theorem B439139 : Blo 179801 439139 := bstep (se 1 (by rfl) ⟨329354, by rfl⟩ : syracuseStep 439139 = 658709) B658709
theorem B406385 : Blo 179801 406385 := bstep (se 2 (by rfl) ⟨152394, by rfl⟩ : syracuseStep 406385 = 304789) B304789
theorem B2569073 : Blo 179801 2569073 := bstep (se 2 (by rfl) ⟨963402, by rfl⟩ : syracuseStep 2569073 = 1926805) B1926805
theorem B308083 : Blo 179801 308083 := bstep (se 1 (by rfl) ⟨231062, by rfl⟩ : syracuseStep 308083 = 462125) B462125
theorem B275315 : Blo 179801 275315 := bstep (se 1 (by rfl) ⟨206486, by rfl⟩ : syracuseStep 275315 = 412973) B412973
theorem B406403 : Blo 179801 406403 := bstep (se 1 (by rfl) ⟨304802, by rfl⟩ : syracuseStep 406403 = 609605) B609605
theorem B275345 : Blo 179801 275345 := bstep (se 2 (by rfl) ⟨103254, by rfl⟩ : syracuseStep 275345 = 206509) B206509
theorem B275363 : Blo 179801 275363 := bstep (se 1 (by rfl) ⟨206522, by rfl⟩ : syracuseStep 275363 = 413045) B413045
theorem B275393 : Blo 179801 275393 := bstep (se 2 (by rfl) ⟨103272, by rfl⟩ : syracuseStep 275393 = 206545) B206545
theorem B275411 : Blo 179801 275411 := bstep (se 1 (by rfl) ⟨206558, by rfl⟩ : syracuseStep 275411 = 413117) B413117
theorem B275441 : Blo 179801 275441 := bstep (se 2 (by rfl) ⟨103290, by rfl⟩ : syracuseStep 275441 = 206581) B206581
theorem B308225 : Blo 179801 308225 := bstep (se 2 (by rfl) ⟨115584, by rfl⟩ : syracuseStep 308225 = 231169) B231169
theorem B275459 : Blo 179801 275459 := bstep (se 1 (by rfl) ⟨206594, by rfl⟩ : syracuseStep 275459 = 413189) B413189
theorem B275489 : Blo 179801 275489 := bstep (se 2 (by rfl) ⟨103308, by rfl⟩ : syracuseStep 275489 = 206617) B206617
theorem B275507 : Blo 179801 275507 := bstep (se 1 (by rfl) ⟨206630, by rfl⟩ : syracuseStep 275507 = 413261) B413261
theorem B275537 : Blo 179801 275537 := bstep (se 2 (by rfl) ⟨103326, by rfl⟩ : syracuseStep 275537 = 206653) B206653
theorem B275555 : Blo 179801 275555 := bstep (se 1 (by rfl) ⟨206666, by rfl⟩ : syracuseStep 275555 = 413333) B413333
theorem B308353 : Blo 179801 308353 := bstep (se 2 (by rfl) ⟨115632, by rfl⟩ : syracuseStep 308353 = 231265) B231265
theorem B275585 : Blo 179801 275585 := bstep (se 2 (by rfl) ⟨103344, by rfl⟩ : syracuseStep 275585 = 206689) B206689
theorem B406673 : Blo 179801 406673 := bstep (se 2 (by rfl) ⟨152502, by rfl⟩ : syracuseStep 406673 = 305005) B305005
theorem B275603 : Blo 179801 275603 := bstep (se 1 (by rfl) ⟨206702, by rfl⟩ : syracuseStep 275603 = 413405) B413405
theorem B406691 : Blo 179801 406691 := bstep (se 1 (by rfl) ⟨305018, by rfl⟩ : syracuseStep 406691 = 610037) B610037
theorem B308387 : Blo 179801 308387 := bstep (se 1 (by rfl) ⟨231290, by rfl⟩ : syracuseStep 308387 = 462581) B462581
theorem B275633 : Blo 179801 275633 := bstep (se 2 (by rfl) ⟨103362, by rfl⟩ : syracuseStep 275633 = 206725) B206725
theorem B275651 : Blo 179801 275651 := bstep (se 1 (by rfl) ⟨206738, by rfl⟩ : syracuseStep 275651 = 413477) B413477
theorem B275681 : Blo 179801 275681 := bstep (se 2 (by rfl) ⟨103380, by rfl⟩ : syracuseStep 275681 = 206761) B206761
theorem B373987 : Blo 179801 373987 := bstep (se 1 (by rfl) ⟨280490, by rfl⟩ : syracuseStep 373987 = 560981) B560981
theorem B275699 : Blo 179801 275699 := bstep (se 1 (by rfl) ⟨206774, by rfl⟩ : syracuseStep 275699 = 413549) B413549
theorem B308515 : Blo 179801 308515 := bstep (se 1 (by rfl) ⟨231386, by rfl⟩ : syracuseStep 308515 = 462773) B462773
theorem B341347 : Blo 179801 341347 := bstep (se 1 (by rfl) ⟨256010, by rfl⟩ : syracuseStep 341347 = 512021) B512021
theorem B1029509 : Blo 179801 1029509 := bstep (se 4 (by rfl) ⟨96516, by rfl⟩ : syracuseStep 1029509 = 193033) B193033
theorem B406961 : Blo 179801 406961 := bstep (se 2 (by rfl) ⟨152610, by rfl⟩ : syracuseStep 406961 = 305221) B305221
theorem B308657 : Blo 179801 308657 := bstep (se 2 (by rfl) ⟨115746, by rfl⟩ : syracuseStep 308657 = 231493) B231493
theorem B406979 : Blo 179801 406979 := bstep (se 1 (by rfl) ⟨305234, by rfl⟩ : syracuseStep 406979 = 610469) B610469
theorem B275971 : Blo 179801 275971 := bstep (se 1 (by rfl) ⟨206978, by rfl⟩ : syracuseStep 275971 = 413957) B413957
theorem B308785 : Blo 179801 308785 := bstep (se 2 (by rfl) ⟨115794, by rfl⟩ : syracuseStep 308785 = 231589) B231589
theorem B308819 : Blo 179801 308819 := bstep (se 1 (by rfl) ⟨231614, by rfl⟩ : syracuseStep 308819 = 463229) B463229
theorem B407249 : Blo 179801 407249 := bstep (se 2 (by rfl) ⟨152718, by rfl⟩ : syracuseStep 407249 = 305437) B305437
theorem B308947 : Blo 179801 308947 := bstep (se 1 (by rfl) ⟨231710, by rfl⟩ : syracuseStep 308947 = 463421) B463421
theorem B407267 : Blo 179801 407267 := bstep (se 1 (by rfl) ⟨305450, by rfl⟩ : syracuseStep 407267 = 610901) B610901
theorem B243491 : Blo 179801 243491 := bstep (se 1 (by rfl) ⟨182618, by rfl⟩ : syracuseStep 243491 = 365237) B365237
theorem B341795 : Blo 179801 341795 := bstep (se 1 (by rfl) ⟨256346, by rfl⟩ : syracuseStep 341795 = 512693) B512693
theorem B309089 : Blo 179801 309089 := bstep (se 2 (by rfl) ⟨115908, by rfl⟩ : syracuseStep 309089 = 231817) B231817
theorem B866189 : Blo 179801 866189 := bstep (se 3 (by rfl) ⟨162410, by rfl⟩ : syracuseStep 866189 = 324821) B324821
theorem B309217 : Blo 179801 309217 := bstep (se 2 (by rfl) ⟨115956, by rfl⟩ : syracuseStep 309217 = 231913) B231913
theorem B407537 : Blo 179801 407537 := bstep (se 2 (by rfl) ⟨152826, by rfl⟩ : syracuseStep 407537 = 305653) B305653
theorem B407555 : Blo 179801 407555 := bstep (se 1 (by rfl) ⟨305666, by rfl⟩ : syracuseStep 407555 = 611333) B611333
theorem B309251 : Blo 179801 309251 := bstep (se 1 (by rfl) ⟨231938, by rfl⟩ : syracuseStep 309251 = 463877) B463877
theorem B342083 : Blo 179801 342083 := bstep (se 1 (by rfl) ⟨256562, by rfl⟩ : syracuseStep 342083 = 513125) B513125
theorem B3127409 : Blo 179801 3127409 := bstep (se 2 (by rfl) ⟨1172778, by rfl⟩ : syracuseStep 3127409 = 2345557) B2345557
theorem B309379 : Blo 179801 309379 := bstep (se 1 (by rfl) ⟨232034, by rfl⟩ : syracuseStep 309379 = 464069) B464069
theorem B407825 : Blo 179801 407825 := bstep (se 2 (by rfl) ⟨152934, by rfl⟩ : syracuseStep 407825 = 305869) B305869
theorem B309521 : Blo 179801 309521 := bstep (se 2 (by rfl) ⟨116070, by rfl⟩ : syracuseStep 309521 = 232141) B232141
theorem B407843 : Blo 179801 407843 := bstep (se 1 (by rfl) ⟨305882, by rfl⟩ : syracuseStep 407843 = 611765) B611765
theorem B768305 : Blo 179801 768305 := bstep (se 2 (by rfl) ⟨288114, by rfl⟩ : syracuseStep 768305 = 576229) B576229
theorem B309649 : Blo 179801 309649 := bstep (se 2 (by rfl) ⟨116118, by rfl⟩ : syracuseStep 309649 = 232237) B232237
theorem B309683 : Blo 179801 309683 := bstep (se 1 (by rfl) ⟨232262, by rfl⟩ : syracuseStep 309683 = 464525) B464525
theorem B408113 : Blo 179801 408113 := bstep (se 2 (by rfl) ⟨153042, by rfl⟩ : syracuseStep 408113 = 306085) B306085
theorem B309811 : Blo 179801 309811 := bstep (se 1 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 309811 = 464717) B464717
theorem B408131 : Blo 179801 408131 := bstep (se 1 (by rfl) ⟨306098, by rfl⟩ : syracuseStep 408131 = 612197) B612197
theorem B1849997 : Blo 179801 1849997 := bstep (se 3 (by rfl) ⟨346874, by rfl⟩ : syracuseStep 1849997 = 693749) B693749
theorem B309953 : Blo 179801 309953 := bstep (se 2 (by rfl) ⟨116232, by rfl⟩ : syracuseStep 309953 = 232465) B232465
theorem B310081 : Blo 179801 310081 := bstep (se 2 (by rfl) ⟨116280, by rfl⟩ : syracuseStep 310081 = 232561) B232561
theorem B408401 : Blo 179801 408401 := bstep (se 2 (by rfl) ⟨153150, by rfl⟩ : syracuseStep 408401 = 306301) B306301
theorem B408419 : Blo 179801 408419 := bstep (se 1 (by rfl) ⟨306314, by rfl⟩ : syracuseStep 408419 = 612629) B612629
theorem B310115 : Blo 179801 310115 := bstep (se 1 (by rfl) ⟨232586, by rfl⟩ : syracuseStep 310115 = 465173) B465173
theorem B1162117 : Blo 179801 1162117 := bstep (se 4 (by rfl) ⟨108948, by rfl⟩ : syracuseStep 1162117 = 217897) B217897
theorem B343025 : Blo 179801 343025 := bstep (se 2 (by rfl) ⟨128634, by rfl⟩ : syracuseStep 343025 = 257269) B257269
theorem B408689 : Blo 179801 408689 := bstep (se 2 (by rfl) ⟨153258, by rfl⟩ : syracuseStep 408689 = 306517) B306517
theorem B408707 : Blo 179801 408707 := bstep (se 1 (by rfl) ⟨306530, by rfl⟩ : syracuseStep 408707 = 613061) B613061
theorem B408977 : Blo 179801 408977 := bstep (se 2 (by rfl) ⟨153366, by rfl⟩ : syracuseStep 408977 = 306733) B306733
theorem B408995 : Blo 179801 408995 := bstep (se 1 (by rfl) ⟨306746, by rfl⟩ : syracuseStep 408995 = 613493) B613493
theorem B179811 : Blo 179801 179811 := bstep (se 1 (by rfl) ⟨134858, by rfl⟩ : syracuseStep 179811 = 269717) B269717
theorem B179827 : Blo 179801 179827 := bstep (se 1 (by rfl) ⟨134870, by rfl⟩ : syracuseStep 179827 = 269741) B269741
theorem B179843 : Blo 179801 179843 := bstep (se 1 (by rfl) ⟨134882, by rfl⟩ : syracuseStep 179843 = 269765) B269765
theorem B179859 : Blo 179801 179859 := bstep (se 1 (by rfl) ⟨134894, by rfl⟩ : syracuseStep 179859 = 269789) B269789
theorem B179875 : Blo 179801 179875 := bstep (se 1 (by rfl) ⟨134906, by rfl⟩ : syracuseStep 179875 = 269813) B269813
theorem B409265 : Blo 179801 409265 := bstep (se 2 (by rfl) ⟨153474, by rfl⟩ : syracuseStep 409265 = 306949) B306949
theorem B179891 : Blo 179801 179891 := bstep (se 1 (by rfl) ⟨134918, by rfl⟩ : syracuseStep 179891 = 269837) B269837
theorem B179907 : Blo 179801 179907 := bstep (se 1 (by rfl) ⟨134930, by rfl⟩ : syracuseStep 179907 = 269861) B269861
theorem B409283 : Blo 179801 409283 := bstep (se 1 (by rfl) ⟨306962, by rfl⟩ : syracuseStep 409283 = 613925) B613925
theorem B179923 : Blo 179801 179923 := bstep (se 1 (by rfl) ⟨134942, by rfl⟩ : syracuseStep 179923 = 269885) B269885
theorem B179939 : Blo 179801 179939 := bstep (se 1 (by rfl) ⟨134954, by rfl⟩ : syracuseStep 179939 = 269909) B269909
theorem B179955 : Blo 179801 179955 := bstep (se 1 (by rfl) ⟨134966, by rfl⟩ : syracuseStep 179955 = 269933) B269933
theorem B179971 : Blo 179801 179971 := bstep (se 1 (by rfl) ⟨134978, by rfl⟩ : syracuseStep 179971 = 269957) B269957
theorem B179987 : Blo 179801 179987 := bstep (se 1 (by rfl) ⟨134990, by rfl⟩ : syracuseStep 179987 = 269981) B269981
theorem B180003 : Blo 179801 180003 := bstep (se 1 (by rfl) ⟨135002, by rfl⟩ : syracuseStep 180003 = 270005) B270005
theorem B180019 : Blo 179801 180019 := bstep (se 1 (by rfl) ⟨135014, by rfl⟩ : syracuseStep 180019 = 270029) B270029
theorem B2080565 : Blo 179801 2080565 := bstep (se 5 (by rfl) ⟨97526, by rfl⟩ : syracuseStep 2080565 = 195053) B195053
theorem B180035 : Blo 179801 180035 := bstep (se 1 (by rfl) ⟨135026, by rfl⟩ : syracuseStep 180035 = 270053) B270053
theorem B180051 : Blo 179801 180051 := bstep (se 1 (by rfl) ⟨135038, by rfl⟩ : syracuseStep 180051 = 270077) B270077
theorem B180067 : Blo 179801 180067 := bstep (se 1 (by rfl) ⟨135050, by rfl⟩ : syracuseStep 180067 = 270101) B270101
theorem B343921 : Blo 179801 343921 := bstep (se 2 (by rfl) ⟨128970, by rfl⟩ : syracuseStep 343921 = 257941) B257941
theorem B180083 : Blo 179801 180083 := bstep (se 1 (by rfl) ⟨135062, by rfl⟩ : syracuseStep 180083 = 270125) B270125
theorem B180099 : Blo 179801 180099 := bstep (se 1 (by rfl) ⟨135074, by rfl⟩ : syracuseStep 180099 = 270149) B270149
theorem B180115 : Blo 179801 180115 := bstep (se 1 (by rfl) ⟨135086, by rfl⟩ : syracuseStep 180115 = 270173) B270173
theorem B180131 : Blo 179801 180131 := bstep (se 1 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 180131 = 270197) B270197
theorem B180147 : Blo 179801 180147 := bstep (se 1 (by rfl) ⟨135110, by rfl⟩ : syracuseStep 180147 = 270221) B270221
theorem B180163 : Blo 179801 180163 := bstep (se 1 (by rfl) ⟨135122, by rfl⟩ : syracuseStep 180163 = 270245) B270245
theorem B409553 : Blo 179801 409553 := bstep (se 2 (by rfl) ⟨153582, by rfl⟩ : syracuseStep 409553 = 307165) B307165
theorem B180179 : Blo 179801 180179 := bstep (se 1 (by rfl) ⟨135134, by rfl⟩ : syracuseStep 180179 = 270269) B270269
theorem B180195 : Blo 179801 180195 := bstep (se 1 (by rfl) ⟨135146, by rfl⟩ : syracuseStep 180195 = 270293) B270293
theorem B409571 : Blo 179801 409571 := bstep (se 1 (by rfl) ⟨307178, by rfl⟩ : syracuseStep 409571 = 614357) B614357
theorem B1458161 : Blo 179801 1458161 := bstep (se 2 (by rfl) ⟨546810, by rfl⟩ : syracuseStep 1458161 = 1093621) B1093621
theorem B180211 : Blo 179801 180211 := bstep (se 1 (by rfl) ⟨135158, by rfl⟩ : syracuseStep 180211 = 270317) B270317
theorem B180227 : Blo 179801 180227 := bstep (se 1 (by rfl) ⟨135170, by rfl⟩ : syracuseStep 180227 = 270341) B270341
theorem B344081 : Blo 179801 344081 := bstep (se 2 (by rfl) ⟨129030, by rfl⟩ : syracuseStep 344081 = 258061) B258061
theorem B180243 : Blo 179801 180243 := bstep (se 1 (by rfl) ⟨135182, by rfl⟩ : syracuseStep 180243 = 270365) B270365
theorem B180259 : Blo 179801 180259 := bstep (se 1 (by rfl) ⟨135194, by rfl⟩ : syracuseStep 180259 = 270389) B270389
theorem B180275 : Blo 179801 180275 := bstep (se 1 (by rfl) ⟨135206, by rfl⟩ : syracuseStep 180275 = 270413) B270413
theorem B180291 : Blo 179801 180291 := bstep (se 1 (by rfl) ⟨135218, by rfl⟩ : syracuseStep 180291 = 270437) B270437
theorem B180307 : Blo 179801 180307 := bstep (se 1 (by rfl) ⟨135230, by rfl⟩ : syracuseStep 180307 = 270461) B270461
theorem B180323 : Blo 179801 180323 := bstep (se 1 (by rfl) ⟨135242, by rfl⟩ : syracuseStep 180323 = 270485) B270485
theorem B180339 : Blo 179801 180339 := bstep (se 1 (by rfl) ⟨135254, by rfl⟩ : syracuseStep 180339 = 270509) B270509
theorem B180355 : Blo 179801 180355 := bstep (se 1 (by rfl) ⟨135266, by rfl⟩ : syracuseStep 180355 = 270533) B270533
theorem B180371 : Blo 179801 180371 := bstep (se 1 (by rfl) ⟨135278, by rfl⟩ : syracuseStep 180371 = 270557) B270557
theorem B180387 : Blo 179801 180387 := bstep (se 1 (by rfl) ⟨135290, by rfl⟩ : syracuseStep 180387 = 270581) B270581
theorem B180403 : Blo 179801 180403 := bstep (se 1 (by rfl) ⟨135302, by rfl⟩ : syracuseStep 180403 = 270605) B270605
theorem B180419 : Blo 179801 180419 := bstep (se 1 (by rfl) ⟨135314, by rfl⟩ : syracuseStep 180419 = 270629) B270629
theorem B180435 : Blo 179801 180435 := bstep (se 1 (by rfl) ⟨135326, by rfl⟩ : syracuseStep 180435 = 270653) B270653
theorem B180451 : Blo 179801 180451 := bstep (se 1 (by rfl) ⟨135338, by rfl⟩ : syracuseStep 180451 = 270677) B270677
theorem B409841 : Blo 179801 409841 := bstep (se 2 (by rfl) ⟨153690, by rfl⟩ : syracuseStep 409841 = 307381) B307381
theorem B180467 : Blo 179801 180467 := bstep (se 1 (by rfl) ⟨135350, by rfl⟩ : syracuseStep 180467 = 270701) B270701
theorem B180483 : Blo 179801 180483 := bstep (se 1 (by rfl) ⟨135362, by rfl⟩ : syracuseStep 180483 = 270725) B270725
theorem B409859 : Blo 179801 409859 := bstep (se 1 (by rfl) ⟨307394, by rfl⟩ : syracuseStep 409859 = 614789) B614789
theorem B180499 : Blo 179801 180499 := bstep (se 1 (by rfl) ⟨135374, by rfl⟩ : syracuseStep 180499 = 270749) B270749
theorem B180515 : Blo 179801 180515 := bstep (se 1 (by rfl) ⟨135386, by rfl⟩ : syracuseStep 180515 = 270773) B270773
theorem B180531 : Blo 179801 180531 := bstep (se 1 (by rfl) ⟨135398, by rfl⟩ : syracuseStep 180531 = 270797) B270797
theorem B180547 : Blo 179801 180547 := bstep (se 1 (by rfl) ⟨135410, by rfl⟩ : syracuseStep 180547 = 270821) B270821
theorem B999749 : Blo 179801 999749 := bstep (se 4 (by rfl) ⟨93726, by rfl⟩ : syracuseStep 999749 = 187453) B187453
theorem B180563 : Blo 179801 180563 := bstep (se 1 (by rfl) ⟨135422, by rfl⟩ : syracuseStep 180563 = 270845) B270845
theorem B180579 : Blo 179801 180579 := bstep (se 1 (by rfl) ⟨135434, by rfl⟩ : syracuseStep 180579 = 270869) B270869
theorem B180595 : Blo 179801 180595 := bstep (se 1 (by rfl) ⟨135446, by rfl⟩ : syracuseStep 180595 = 270893) B270893
theorem B180611 : Blo 179801 180611 := bstep (se 1 (by rfl) ⟨135458, by rfl⟩ : syracuseStep 180611 = 270917) B270917
theorem B180627 : Blo 179801 180627 := bstep (se 1 (by rfl) ⟨135470, by rfl⟩ : syracuseStep 180627 = 270941) B270941
theorem B180643 : Blo 179801 180643 := bstep (se 1 (by rfl) ⟨135482, by rfl⟩ : syracuseStep 180643 = 270965) B270965
theorem B344483 : Blo 179801 344483 := bstep (se 1 (by rfl) ⟨258362, by rfl⟩ : syracuseStep 344483 = 516725) B516725
theorem B180659 : Blo 179801 180659 := bstep (se 1 (by rfl) ⟨135494, by rfl⟩ : syracuseStep 180659 = 270989) B270989
theorem B180675 : Blo 179801 180675 := bstep (se 1 (by rfl) ⟨135506, by rfl⟩ : syracuseStep 180675 = 271013) B271013
theorem B180691 : Blo 179801 180691 := bstep (se 1 (by rfl) ⟨135518, by rfl⟩ : syracuseStep 180691 = 271037) B271037
theorem B180707 : Blo 179801 180707 := bstep (se 1 (by rfl) ⟨135530, by rfl⟩ : syracuseStep 180707 = 271061) B271061
theorem B180723 : Blo 179801 180723 := bstep (se 1 (by rfl) ⟨135542, by rfl⟩ : syracuseStep 180723 = 271085) B271085
theorem B180739 : Blo 179801 180739 := bstep (se 1 (by rfl) ⟨135554, by rfl⟩ : syracuseStep 180739 = 271109) B271109
theorem B410129 : Blo 179801 410129 := bstep (se 2 (by rfl) ⟨153798, by rfl⟩ : syracuseStep 410129 = 307597) B307597
theorem B180755 : Blo 179801 180755 := bstep (se 1 (by rfl) ⟨135566, by rfl⟩ : syracuseStep 180755 = 271133) B271133
theorem B180771 : Blo 179801 180771 := bstep (se 1 (by rfl) ⟨135578, by rfl⟩ : syracuseStep 180771 = 271157) B271157
theorem B410147 : Blo 179801 410147 := bstep (se 1 (by rfl) ⟨307610, by rfl⟩ : syracuseStep 410147 = 615221) B615221
theorem B410161 : Blo 179801 410161 := bstep (se 2 (by rfl) ⟨153810, by rfl⟩ : syracuseStep 410161 = 307621) B307621
theorem B180787 : Blo 179801 180787 := bstep (se 1 (by rfl) ⟨135590, by rfl⟩ : syracuseStep 180787 = 271181) B271181
theorem B180803 : Blo 179801 180803 := bstep (se 1 (by rfl) ⟨135602, by rfl⟩ : syracuseStep 180803 = 271205) B271205
theorem B180819 : Blo 179801 180819 := bstep (se 1 (by rfl) ⟨135614, by rfl⟩ : syracuseStep 180819 = 271229) B271229
theorem B180835 : Blo 179801 180835 := bstep (se 1 (by rfl) ⟨135626, by rfl⟩ : syracuseStep 180835 = 271253) B271253
theorem B180851 : Blo 179801 180851 := bstep (se 1 (by rfl) ⟨135638, by rfl⟩ : syracuseStep 180851 = 271277) B271277
theorem B606851 : Blo 179801 606851 := bstep (se 1 (by rfl) ⟨455138, by rfl⟩ : syracuseStep 606851 = 910277) B910277
theorem B180867 : Blo 179801 180867 := bstep (se 1 (by rfl) ⟨135650, by rfl⟩ : syracuseStep 180867 = 271301) B271301
theorem B180883 : Blo 179801 180883 := bstep (se 1 (by rfl) ⟨135662, by rfl⟩ : syracuseStep 180883 = 271325) B271325
theorem B180899 : Blo 179801 180899 := bstep (se 1 (by rfl) ⟨135674, by rfl⟩ : syracuseStep 180899 = 271349) B271349
theorem B180915 : Blo 179801 180915 := bstep (se 1 (by rfl) ⟨135686, by rfl⟩ : syracuseStep 180915 = 271373) B271373
theorem B180931 : Blo 179801 180931 := bstep (se 1 (by rfl) ⟨135698, by rfl⟩ : syracuseStep 180931 = 271397) B271397
theorem B180947 : Blo 179801 180947 := bstep (se 1 (by rfl) ⟨135710, by rfl⟩ : syracuseStep 180947 = 271421) B271421
theorem B246497 : Blo 179801 246497 := bstep (se 2 (by rfl) ⟨92436, by rfl⟩ : syracuseStep 246497 = 184873) B184873
theorem B180963 : Blo 179801 180963 := bstep (se 1 (by rfl) ⟨135722, by rfl⟩ : syracuseStep 180963 = 271445) B271445
theorem B1983217 : Blo 179801 1983217 := bstep (se 2 (by rfl) ⟨743706, by rfl⟩ : syracuseStep 1983217 = 1487413) B1487413
theorem B180979 : Blo 179801 180979 := bstep (se 1 (by rfl) ⟨135734, by rfl⟩ : syracuseStep 180979 = 271469) B271469
theorem B180995 : Blo 179801 180995 := bstep (se 1 (by rfl) ⟨135746, by rfl⟩ : syracuseStep 180995 = 271493) B271493
theorem B181011 : Blo 179801 181011 := bstep (se 1 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 181011 = 271517) B271517
theorem B181027 : Blo 179801 181027 := bstep (se 1 (by rfl) ⟨135770, by rfl⟩ : syracuseStep 181027 = 271541) B271541
theorem B410417 : Blo 179801 410417 := bstep (se 2 (by rfl) ⟨153906, by rfl⟩ : syracuseStep 410417 = 307813) B307813
theorem B181043 : Blo 179801 181043 := bstep (se 1 (by rfl) ⟨135782, by rfl⟩ : syracuseStep 181043 = 271565) B271565
theorem B181059 : Blo 179801 181059 := bstep (se 1 (by rfl) ⟨135794, by rfl⟩ : syracuseStep 181059 = 271589) B271589
theorem B410435 : Blo 179801 410435 := bstep (se 1 (by rfl) ⟨307826, by rfl⟩ : syracuseStep 410435 = 615653) B615653
theorem B279377 : Blo 179801 279377 := bstep (se 2 (by rfl) ⟨104766, by rfl⟩ : syracuseStep 279377 = 209533) B209533
theorem B181075 : Blo 179801 181075 := bstep (se 1 (by rfl) ⟨135806, by rfl⟩ : syracuseStep 181075 = 271613) B271613
theorem B181091 : Blo 179801 181091 := bstep (se 1 (by rfl) ⟨135818, by rfl⟩ : syracuseStep 181091 = 271637) B271637
theorem B181107 : Blo 179801 181107 := bstep (se 1 (by rfl) ⟨135830, by rfl⟩ : syracuseStep 181107 = 271661) B271661
theorem B181123 : Blo 179801 181123 := bstep (se 1 (by rfl) ⟨135842, by rfl⟩ : syracuseStep 181123 = 271685) B271685
theorem B607121 : Blo 179801 607121 := bstep (se 2 (by rfl) ⟨227670, by rfl⟩ : syracuseStep 607121 = 455341) B455341
theorem B181139 : Blo 179801 181139 := bstep (se 1 (by rfl) ⟨135854, by rfl⟩ : syracuseStep 181139 = 271709) B271709
theorem B181155 : Blo 179801 181155 := bstep (se 1 (by rfl) ⟨135866, by rfl⟩ : syracuseStep 181155 = 271733) B271733
theorem B181171 : Blo 179801 181171 := bstep (se 1 (by rfl) ⟨135878, by rfl⟩ : syracuseStep 181171 = 271757) B271757
theorem B181187 : Blo 179801 181187 := bstep (se 1 (by rfl) ⟨135890, by rfl⟩ : syracuseStep 181187 = 271781) B271781
theorem B181203 : Blo 179801 181203 := bstep (se 1 (by rfl) ⟨135902, by rfl⟩ : syracuseStep 181203 = 271805) B271805
theorem B181219 : Blo 179801 181219 := bstep (se 1 (by rfl) ⟨135914, by rfl⟩ : syracuseStep 181219 = 271829) B271829
theorem B934897 : Blo 179801 934897 := bstep (se 2 (by rfl) ⟨350586, by rfl⟩ : syracuseStep 934897 = 701173) B701173
theorem B181235 : Blo 179801 181235 := bstep (se 1 (by rfl) ⟨135926, by rfl⟩ : syracuseStep 181235 = 271853) B271853
theorem B181251 : Blo 179801 181251 := bstep (se 1 (by rfl) ⟨135938, by rfl⟩ : syracuseStep 181251 = 271877) B271877
theorem B181267 : Blo 179801 181267 := bstep (se 1 (by rfl) ⟨135950, by rfl⟩ : syracuseStep 181267 = 271901) B271901
theorem B181283 : Blo 179801 181283 := bstep (se 1 (by rfl) ⟨135962, by rfl⟩ : syracuseStep 181283 = 271925) B271925
theorem B181299 : Blo 179801 181299 := bstep (se 1 (by rfl) ⟨135974, by rfl⟩ : syracuseStep 181299 = 271949) B271949
theorem B181315 : Blo 179801 181315 := bstep (se 1 (by rfl) ⟨135986, by rfl⟩ : syracuseStep 181315 = 271973) B271973
theorem B410705 : Blo 179801 410705 := bstep (se 2 (by rfl) ⟨154014, by rfl⟩ : syracuseStep 410705 = 308029) B308029
theorem B181331 : Blo 179801 181331 := bstep (se 1 (by rfl) ⟨135998, by rfl⟩ : syracuseStep 181331 = 271997) B271997
theorem B181347 : Blo 179801 181347 := bstep (se 1 (by rfl) ⟨136010, by rfl⟩ : syracuseStep 181347 = 272021) B272021
theorem B410723 : Blo 179801 410723 := bstep (se 1 (by rfl) ⟨308042, by rfl⟩ : syracuseStep 410723 = 616085) B616085
theorem B181363 : Blo 179801 181363 := bstep (se 1 (by rfl) ⟨136022, by rfl⟩ : syracuseStep 181363 = 272045) B272045
theorem B181379 : Blo 179801 181379 := bstep (se 1 (by rfl) ⟨136034, by rfl⟩ : syracuseStep 181379 = 272069) B272069
theorem B1033357 : Blo 179801 1033357 := bstep (se 3 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 1033357 = 387509) B387509
theorem B181395 : Blo 179801 181395 := bstep (se 1 (by rfl) ⟨136046, by rfl⟩ : syracuseStep 181395 = 272093) B272093
theorem B181411 : Blo 179801 181411 := bstep (se 1 (by rfl) ⟨136058, by rfl⟩ : syracuseStep 181411 = 272117) B272117
theorem B181427 : Blo 179801 181427 := bstep (se 1 (by rfl) ⟨136070, by rfl⟩ : syracuseStep 181427 = 272141) B272141
theorem B181443 : Blo 179801 181443 := bstep (se 1 (by rfl) ⟨136082, by rfl⟩ : syracuseStep 181443 = 272165) B272165
theorem B181459 : Blo 179801 181459 := bstep (se 1 (by rfl) ⟨136094, by rfl⟩ : syracuseStep 181459 = 272189) B272189
theorem B181475 : Blo 179801 181475 := bstep (se 1 (by rfl) ⟨136106, by rfl⟩ : syracuseStep 181475 = 272213) B272213
theorem B181491 : Blo 179801 181491 := bstep (se 1 (by rfl) ⟨136118, by rfl⟩ : syracuseStep 181491 = 272237) B272237
theorem B181507 : Blo 179801 181507 := bstep (se 1 (by rfl) ⟨136130, by rfl⟩ : syracuseStep 181507 = 272261) B272261
theorem B181523 : Blo 179801 181523 := bstep (se 1 (by rfl) ⟨136142, by rfl⟩ : syracuseStep 181523 = 272285) B272285
theorem B181539 : Blo 179801 181539 := bstep (se 1 (by rfl) ⟨136154, by rfl⟩ : syracuseStep 181539 = 272309) B272309
theorem B345379 : Blo 179801 345379 := bstep (se 1 (by rfl) ⟨259034, by rfl⟩ : syracuseStep 345379 = 518069) B518069
theorem B181555 : Blo 179801 181555 := bstep (se 1 (by rfl) ⟨136166, by rfl⟩ : syracuseStep 181555 = 272333) B272333
theorem B181571 : Blo 179801 181571 := bstep (se 1 (by rfl) ⟨136178, by rfl⟩ : syracuseStep 181571 = 272357) B272357
theorem B181587 : Blo 179801 181587 := bstep (se 1 (by rfl) ⟨136190, by rfl⟩ : syracuseStep 181587 = 272381) B272381
theorem B2311523 : Blo 179801 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B181603 : Blo 179801 181603 := bstep (se 1 (by rfl) ⟨136202, by rfl⟩ : syracuseStep 181603 = 272405) B272405
theorem B410993 : Blo 179801 410993 := bstep (se 2 (by rfl) ⟨154122, by rfl⟩ : syracuseStep 410993 = 308245) B308245
theorem B181619 : Blo 179801 181619 := bstep (se 1 (by rfl) ⟨136214, by rfl⟩ : syracuseStep 181619 = 272429) B272429
theorem B181635 : Blo 179801 181635 := bstep (se 1 (by rfl) ⟨136226, by rfl⟩ : syracuseStep 181635 = 272453) B272453
theorem B411011 : Blo 179801 411011 := bstep (se 1 (by rfl) ⟨308258, by rfl⟩ : syracuseStep 411011 = 616517) B616517
theorem B181651 : Blo 179801 181651 := bstep (se 1 (by rfl) ⟨136238, by rfl⟩ : syracuseStep 181651 = 272477) B272477
theorem B181667 : Blo 179801 181667 := bstep (se 1 (by rfl) ⟨136250, by rfl⟩ : syracuseStep 181667 = 272501) B272501
theorem B607661 : Blo 179801 607661 := bstep (se 3 (by rfl) ⟨113936, by rfl⟩ : syracuseStep 607661 = 227873) B227873
theorem B181683 : Blo 179801 181683 := bstep (se 1 (by rfl) ⟨136262, by rfl⟩ : syracuseStep 181683 = 272525) B272525
theorem B181699 : Blo 179801 181699 := bstep (se 1 (by rfl) ⟨136274, by rfl⟩ : syracuseStep 181699 = 272549) B272549
theorem B345539 : Blo 179801 345539 := bstep (se 1 (by rfl) ⟨259154, by rfl⟩ : syracuseStep 345539 = 518309) B518309
theorem B247249 : Blo 179801 247249 := bstep (se 2 (by rfl) ⟨92718, by rfl⟩ : syracuseStep 247249 = 185437) B185437
theorem B181715 : Blo 179801 181715 := bstep (se 1 (by rfl) ⟨136286, by rfl⟩ : syracuseStep 181715 = 272573) B272573
theorem B607715 : Blo 179801 607715 := bstep (se 1 (by rfl) ⟨455786, by rfl⟩ : syracuseStep 607715 = 911573) B911573
theorem B181731 : Blo 179801 181731 := bstep (se 1 (by rfl) ⟨136298, by rfl⟩ : syracuseStep 181731 = 272597) B272597
theorem B181747 : Blo 179801 181747 := bstep (se 1 (by rfl) ⟨136310, by rfl⟩ : syracuseStep 181747 = 272621) B272621
theorem B247297 : Blo 179801 247297 := bstep (se 2 (by rfl) ⟨92736, by rfl⟩ : syracuseStep 247297 = 185473) B185473
theorem B181763 : Blo 179801 181763 := bstep (se 1 (by rfl) ⟨136322, by rfl⟩ : syracuseStep 181763 = 272645) B272645
theorem B181779 : Blo 179801 181779 := bstep (se 1 (by rfl) ⟨136334, by rfl⟩ : syracuseStep 181779 = 272669) B272669
theorem B181795 : Blo 179801 181795 := bstep (se 1 (by rfl) ⟨136346, by rfl⟩ : syracuseStep 181795 = 272693) B272693
theorem B181811 : Blo 179801 181811 := bstep (se 1 (by rfl) ⟨136358, by rfl⟩ : syracuseStep 181811 = 272717) B272717
theorem B181827 : Blo 179801 181827 := bstep (se 1 (by rfl) ⟨136370, by rfl⟩ : syracuseStep 181827 = 272741) B272741
theorem B181843 : Blo 179801 181843 := bstep (se 1 (by rfl) ⟨136382, by rfl⟩ : syracuseStep 181843 = 272765) B272765
theorem B247379 : Blo 179801 247379 := bstep (se 1 (by rfl) ⟨185534, by rfl⟩ : syracuseStep 247379 = 371069) B371069
theorem B181859 : Blo 179801 181859 := bstep (se 1 (by rfl) ⟨136394, by rfl⟩ : syracuseStep 181859 = 272789) B272789
theorem B181875 : Blo 179801 181875 := bstep (se 1 (by rfl) ⟨136406, by rfl⟩ : syracuseStep 181875 = 272813) B272813
theorem B181891 : Blo 179801 181891 := bstep (se 1 (by rfl) ⟨136418, by rfl⟩ : syracuseStep 181891 = 272837) B272837
theorem B411281 : Blo 179801 411281 := bstep (se 2 (by rfl) ⟨154230, by rfl⟩ : syracuseStep 411281 = 308461) B308461
theorem B181907 : Blo 179801 181907 := bstep (se 1 (by rfl) ⟨136430, by rfl⟩ : syracuseStep 181907 = 272861) B272861
theorem B181923 : Blo 179801 181923 := bstep (se 1 (by rfl) ⟨136442, by rfl⟩ : syracuseStep 181923 = 272885) B272885
theorem B411299 : Blo 179801 411299 := bstep (se 1 (by rfl) ⟨308474, by rfl⟩ : syracuseStep 411299 = 616949) B616949
theorem B181939 : Blo 179801 181939 := bstep (se 1 (by rfl) ⟨136454, by rfl⟩ : syracuseStep 181939 = 272909) B272909
theorem B411331 : Blo 179801 411331 := bstep (se 1 (by rfl) ⟨308498, by rfl⟩ : syracuseStep 411331 = 616997) B616997
theorem B181955 : Blo 179801 181955 := bstep (se 1 (by rfl) ⟨136466, by rfl⟩ : syracuseStep 181955 = 272933) B272933
theorem B181971 : Blo 179801 181971 := bstep (se 1 (by rfl) ⟨136478, by rfl⟩ : syracuseStep 181971 = 272957) B272957
theorem B181987 : Blo 179801 181987 := bstep (se 1 (by rfl) ⟨136490, by rfl⟩ : syracuseStep 181987 = 272981) B272981
theorem B607985 : Blo 179801 607985 := bstep (se 2 (by rfl) ⟨227994, by rfl⟩ : syracuseStep 607985 = 455989) B455989
theorem B182003 : Blo 179801 182003 := bstep (se 1 (by rfl) ⟨136502, by rfl⟩ : syracuseStep 182003 = 273005) B273005
theorem B182019 : Blo 179801 182019 := bstep (se 1 (by rfl) ⟨136514, by rfl⟩ : syracuseStep 182019 = 273029) B273029
theorem B182035 : Blo 179801 182035 := bstep (se 1 (by rfl) ⟨136526, by rfl⟩ : syracuseStep 182035 = 273053) B273053
theorem B771875 : Blo 179801 771875 := bstep (se 1 (by rfl) ⟨578906, by rfl⟩ : syracuseStep 771875 = 1157813) B1157813
theorem B182051 : Blo 179801 182051 := bstep (se 1 (by rfl) ⟨136538, by rfl⟩ : syracuseStep 182051 = 273077) B273077
theorem B182067 : Blo 179801 182067 := bstep (se 1 (by rfl) ⟨136550, by rfl⟩ : syracuseStep 182067 = 273101) B273101
theorem B182083 : Blo 179801 182083 := bstep (se 1 (by rfl) ⟨136562, by rfl⟩ : syracuseStep 182083 = 273125) B273125
theorem B182099 : Blo 179801 182099 := bstep (se 1 (by rfl) ⟨136574, by rfl⟩ : syracuseStep 182099 = 273149) B273149
theorem B182115 : Blo 179801 182115 := bstep (se 1 (by rfl) ⟨136586, by rfl⟩ : syracuseStep 182115 = 273173) B273173
theorem B182131 : Blo 179801 182131 := bstep (se 1 (by rfl) ⟨136598, by rfl⟩ : syracuseStep 182131 = 273197) B273197
theorem B182147 : Blo 179801 182147 := bstep (se 1 (by rfl) ⟨136610, by rfl⟩ : syracuseStep 182147 = 273221) B273221
theorem B182163 : Blo 179801 182163 := bstep (se 1 (by rfl) ⟨136622, by rfl⟩ : syracuseStep 182163 = 273245) B273245
theorem B182179 : Blo 179801 182179 := bstep (se 1 (by rfl) ⟨136634, by rfl⟩ : syracuseStep 182179 = 273269) B273269
theorem B411569 : Blo 179801 411569 := bstep (se 2 (by rfl) ⟨154338, by rfl⟩ : syracuseStep 411569 = 308677) B308677
theorem B247729 : Blo 179801 247729 := bstep (se 2 (by rfl) ⟨92898, by rfl⟩ : syracuseStep 247729 = 185797) B185797
theorem B182195 : Blo 179801 182195 := bstep (se 1 (by rfl) ⟨136646, by rfl⟩ : syracuseStep 182195 = 273293) B273293
theorem B182211 : Blo 179801 182211 := bstep (se 1 (by rfl) ⟨136658, by rfl⟩ : syracuseStep 182211 = 273317) B273317
theorem B411587 : Blo 179801 411587 := bstep (se 1 (by rfl) ⟨308690, by rfl⟩ : syracuseStep 411587 = 617381) B617381
theorem B182227 : Blo 179801 182227 := bstep (se 1 (by rfl) ⟨136670, by rfl⟩ : syracuseStep 182227 = 273341) B273341
theorem B182243 : Blo 179801 182243 := bstep (se 1 (by rfl) ⟨136682, by rfl⟩ : syracuseStep 182243 = 273365) B273365
theorem B182259 : Blo 179801 182259 := bstep (se 1 (by rfl) ⟨136694, by rfl⟩ : syracuseStep 182259 = 273389) B273389
theorem B313345 : Blo 179801 313345 := bstep (se 2 (by rfl) ⟨117504, by rfl⟩ : syracuseStep 313345 = 235009) B235009
theorem B182275 : Blo 179801 182275 := bstep (se 1 (by rfl) ⟨136706, by rfl⟩ : syracuseStep 182275 = 273413) B273413
theorem B182291 : Blo 179801 182291 := bstep (se 1 (by rfl) ⟨136718, by rfl⟩ : syracuseStep 182291 = 273437) B273437
theorem B182307 : Blo 179801 182307 := bstep (se 1 (by rfl) ⟨136730, by rfl⟩ : syracuseStep 182307 = 273461) B273461
theorem B182323 : Blo 179801 182323 := bstep (se 1 (by rfl) ⟨136742, by rfl⟩ : syracuseStep 182323 = 273485) B273485
theorem B182339 : Blo 179801 182339 := bstep (se 1 (by rfl) ⟨136754, by rfl⟩ : syracuseStep 182339 = 273509) B273509
theorem B182355 : Blo 179801 182355 := bstep (se 1 (by rfl) ⟨136766, by rfl⟩ : syracuseStep 182355 = 273533) B273533
theorem B182371 : Blo 179801 182371 := bstep (se 1 (by rfl) ⟨136778, by rfl⟩ : syracuseStep 182371 = 273557) B273557
theorem B182387 : Blo 179801 182387 := bstep (se 1 (by rfl) ⟨136790, by rfl⟩ : syracuseStep 182387 = 273581) B273581
theorem B182403 : Blo 179801 182403 := bstep (se 1 (by rfl) ⟨136802, by rfl⟩ : syracuseStep 182403 = 273605) B273605
theorem B182419 : Blo 179801 182419 := bstep (se 1 (by rfl) ⟨136814, by rfl⟩ : syracuseStep 182419 = 273629) B273629
theorem B182435 : Blo 179801 182435 := bstep (se 1 (by rfl) ⟨136826, by rfl⟩ : syracuseStep 182435 = 273653) B273653
theorem B182451 : Blo 179801 182451 := bstep (se 1 (by rfl) ⟨136838, by rfl⟩ : syracuseStep 182451 = 273677) B273677
theorem B182467 : Blo 179801 182467 := bstep (se 1 (by rfl) ⟨136850, by rfl⟩ : syracuseStep 182467 = 273701) B273701
theorem B411857 : Blo 179801 411857 := bstep (se 2 (by rfl) ⟨154446, by rfl⟩ : syracuseStep 411857 = 308893) B308893
theorem B182483 : Blo 179801 182483 := bstep (se 1 (by rfl) ⟨136862, by rfl⟩ : syracuseStep 182483 = 273725) B273725
theorem B182499 : Blo 179801 182499 := bstep (se 1 (by rfl) ⟨136874, by rfl⟩ : syracuseStep 182499 = 273749) B273749
theorem B411875 : Blo 179801 411875 := bstep (se 1 (by rfl) ⟨308906, by rfl⟩ : syracuseStep 411875 = 617813) B617813
theorem B182515 : Blo 179801 182515 := bstep (se 1 (by rfl) ⟨136886, by rfl⟩ : syracuseStep 182515 = 273773) B273773
theorem B182531 : Blo 179801 182531 := bstep (se 1 (by rfl) ⟨136898, by rfl⟩ : syracuseStep 182531 = 273797) B273797
theorem B608525 : Blo 179801 608525 := bstep (se 3 (by rfl) ⟨114098, by rfl⟩ : syracuseStep 608525 = 228197) B228197
theorem B2377997 : Blo 179801 2377997 := bstep (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) B891749
theorem B182547 : Blo 179801 182547 := bstep (se 1 (by rfl) ⟨136910, by rfl⟩ : syracuseStep 182547 = 273821) B273821
theorem B1165603 : Blo 179801 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B182563 : Blo 179801 182563 := bstep (se 1 (by rfl) ⟨136922, by rfl⟩ : syracuseStep 182563 = 273845) B273845
theorem B182579 : Blo 179801 182579 := bstep (se 1 (by rfl) ⟨136934, by rfl⟩ : syracuseStep 182579 = 273869) B273869
theorem B608579 : Blo 179801 608579 := bstep (se 1 (by rfl) ⟨456434, by rfl⟩ : syracuseStep 608579 = 912869) B912869
theorem B182595 : Blo 179801 182595 := bstep (se 1 (by rfl) ⟨136946, by rfl⟩ : syracuseStep 182595 = 273893) B273893
theorem B182611 : Blo 179801 182611 := bstep (se 1 (by rfl) ⟨136958, by rfl⟩ : syracuseStep 182611 = 273917) B273917
theorem B182627 : Blo 179801 182627 := bstep (se 1 (by rfl) ⟨136970, by rfl⟩ : syracuseStep 182627 = 273941) B273941
theorem B182643 : Blo 179801 182643 := bstep (se 1 (by rfl) ⟨136982, by rfl⟩ : syracuseStep 182643 = 273965) B273965
theorem B182659 : Blo 179801 182659 := bstep (se 1 (by rfl) ⟨136994, by rfl⟩ : syracuseStep 182659 = 273989) B273989
theorem B182675 : Blo 179801 182675 := bstep (se 1 (by rfl) ⟨137006, by rfl⟩ : syracuseStep 182675 = 274013) B274013
theorem B182691 : Blo 179801 182691 := bstep (se 1 (by rfl) ⟨137018, by rfl⟩ : syracuseStep 182691 = 274037) B274037
theorem B182707 : Blo 179801 182707 := bstep (se 1 (by rfl) ⟨137030, by rfl⟩ : syracuseStep 182707 = 274061) B274061
theorem B182723 : Blo 179801 182723 := bstep (se 1 (by rfl) ⟨137042, by rfl⟩ : syracuseStep 182723 = 274085) B274085
theorem B182739 : Blo 179801 182739 := bstep (se 1 (by rfl) ⟨137054, by rfl⟩ : syracuseStep 182739 = 274109) B274109
theorem B182755 : Blo 179801 182755 := bstep (se 1 (by rfl) ⟨137066, by rfl⟩ : syracuseStep 182755 = 274133) B274133
theorem B346609 : Blo 179801 346609 := bstep (se 2 (by rfl) ⟨129978, by rfl⟩ : syracuseStep 346609 = 259957) B259957
theorem B412145 : Blo 179801 412145 := bstep (se 2 (by rfl) ⟨154554, by rfl⟩ : syracuseStep 412145 = 309109) B309109
theorem B182771 : Blo 179801 182771 := bstep (se 1 (by rfl) ⟨137078, by rfl⟩ : syracuseStep 182771 = 274157) B274157
theorem B510449 : Blo 179801 510449 := bstep (se 2 (by rfl) ⟨191418, by rfl⟩ : syracuseStep 510449 = 382837) B382837
theorem B182787 : Blo 179801 182787 := bstep (se 1 (by rfl) ⟨137090, by rfl⟩ : syracuseStep 182787 = 274181) B274181
theorem B412163 : Blo 179801 412163 := bstep (se 1 (by rfl) ⟨309122, by rfl⟩ : syracuseStep 412163 = 618245) B618245
theorem B182803 : Blo 179801 182803 := bstep (se 1 (by rfl) ⟨137102, by rfl⟩ : syracuseStep 182803 = 274205) B274205
theorem B182819 : Blo 179801 182819 := bstep (se 1 (by rfl) ⟨137114, by rfl⟩ : syracuseStep 182819 = 274229) B274229
theorem B182835 : Blo 179801 182835 := bstep (se 1 (by rfl) ⟨137126, by rfl⟩ : syracuseStep 182835 = 274253) B274253
theorem B182851 : Blo 179801 182851 := bstep (se 1 (by rfl) ⟨137138, by rfl⟩ : syracuseStep 182851 = 274277) B274277
theorem B608849 : Blo 179801 608849 := bstep (se 2 (by rfl) ⟨228318, by rfl⟩ : syracuseStep 608849 = 456637) B456637
theorem B182867 : Blo 179801 182867 := bstep (se 1 (by rfl) ⟨137150, by rfl⟩ : syracuseStep 182867 = 274301) B274301
theorem B182883 : Blo 179801 182883 := bstep (se 1 (by rfl) ⟨137162, by rfl⟩ : syracuseStep 182883 = 274325) B274325
theorem B182899 : Blo 179801 182899 := bstep (se 1 (by rfl) ⟨137174, by rfl⟩ : syracuseStep 182899 = 274349) B274349
theorem B182915 : Blo 179801 182915 := bstep (se 1 (by rfl) ⟨137186, by rfl⟩ : syracuseStep 182915 = 274373) B274373
theorem B182931 : Blo 179801 182931 := bstep (se 1 (by rfl) ⟨137198, by rfl⟩ : syracuseStep 182931 = 274397) B274397
theorem B182947 : Blo 179801 182947 := bstep (se 1 (by rfl) ⟨137210, by rfl⟩ : syracuseStep 182947 = 274421) B274421
theorem B182963 : Blo 179801 182963 := bstep (se 1 (by rfl) ⟨137222, by rfl⟩ : syracuseStep 182963 = 274445) B274445
theorem B182979 : Blo 179801 182979 := bstep (se 1 (by rfl) ⟨137234, by rfl⟩ : syracuseStep 182979 = 274469) B274469
theorem B182995 : Blo 179801 182995 := bstep (se 1 (by rfl) ⟨137246, by rfl⟩ : syracuseStep 182995 = 274493) B274493
theorem B183011 : Blo 179801 183011 := bstep (se 1 (by rfl) ⟨137258, by rfl⟩ : syracuseStep 183011 = 274517) B274517
theorem B183027 : Blo 179801 183027 := bstep (se 1 (by rfl) ⟨137270, by rfl⟩ : syracuseStep 183027 = 274541) B274541
theorem B183043 : Blo 179801 183043 := bstep (se 1 (by rfl) ⟨137282, by rfl⟩ : syracuseStep 183043 = 274565) B274565
theorem B412433 : Blo 179801 412433 := bstep (se 2 (by rfl) ⟨154662, by rfl⟩ : syracuseStep 412433 = 309325) B309325
theorem B183059 : Blo 179801 183059 := bstep (se 1 (by rfl) ⟨137294, by rfl⟩ : syracuseStep 183059 = 274589) B274589
theorem B183075 : Blo 179801 183075 := bstep (se 1 (by rfl) ⟨137306, by rfl⟩ : syracuseStep 183075 = 274613) B274613
theorem B412451 : Blo 179801 412451 := bstep (se 1 (by rfl) ⟨309338, by rfl⟩ : syracuseStep 412451 = 618677) B618677
theorem B183091 : Blo 179801 183091 := bstep (se 1 (by rfl) ⟨137318, by rfl⟩ : syracuseStep 183091 = 274637) B274637
theorem B183107 : Blo 179801 183107 := bstep (se 1 (by rfl) ⟨137330, by rfl⟩ : syracuseStep 183107 = 274661) B274661
theorem B183123 : Blo 179801 183123 := bstep (se 1 (by rfl) ⟨137342, by rfl⟩ : syracuseStep 183123 = 274685) B274685
theorem B183139 : Blo 179801 183139 := bstep (se 1 (by rfl) ⟨137354, by rfl⟩ : syracuseStep 183139 = 274709) B274709
theorem B183155 : Blo 179801 183155 := bstep (se 1 (by rfl) ⟨137366, by rfl⟩ : syracuseStep 183155 = 274733) B274733
theorem B183171 : Blo 179801 183171 := bstep (se 1 (by rfl) ⟨137378, by rfl⟩ : syracuseStep 183171 = 274757) B274757
theorem B183187 : Blo 179801 183187 := bstep (se 1 (by rfl) ⟨137390, by rfl⟩ : syracuseStep 183187 = 274781) B274781
theorem B183203 : Blo 179801 183203 := bstep (se 1 (by rfl) ⟨137402, by rfl⟩ : syracuseStep 183203 = 274805) B274805
theorem B183219 : Blo 179801 183219 := bstep (se 1 (by rfl) ⟨137414, by rfl⟩ : syracuseStep 183219 = 274829) B274829
theorem B183235 : Blo 179801 183235 := bstep (se 1 (by rfl) ⟨137426, by rfl⟩ : syracuseStep 183235 = 274853) B274853
theorem B183251 : Blo 179801 183251 := bstep (se 1 (by rfl) ⟨137438, by rfl⟩ : syracuseStep 183251 = 274877) B274877
theorem B412643 : Blo 179801 412643 := bstep (se 1 (by rfl) ⟨309482, by rfl⟩ : syracuseStep 412643 = 618965) B618965
theorem B183267 : Blo 179801 183267 := bstep (se 1 (by rfl) ⟨137450, by rfl⟩ : syracuseStep 183267 = 274901) B274901
theorem B576497 : Blo 179801 576497 := bstep (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) B432373
theorem B183283 : Blo 179801 183283 := bstep (se 1 (by rfl) ⟨137462, by rfl⟩ : syracuseStep 183283 = 274925) B274925
theorem B183299 : Blo 179801 183299 := bstep (se 1 (by rfl) ⟨137474, by rfl⟩ : syracuseStep 183299 = 274949) B274949
theorem B183315 : Blo 179801 183315 := bstep (se 1 (by rfl) ⟨137486, by rfl⟩ : syracuseStep 183315 = 274973) B274973
theorem B183331 : Blo 179801 183331 := bstep (se 1 (by rfl) ⟨137498, by rfl⟩ : syracuseStep 183331 = 274997) B274997
theorem B412721 : Blo 179801 412721 := bstep (se 2 (by rfl) ⟨154770, by rfl⟩ : syracuseStep 412721 = 309541) B309541
theorem B183347 : Blo 179801 183347 := bstep (se 1 (by rfl) ⟨137510, by rfl⟩ : syracuseStep 183347 = 275021) B275021
theorem B183363 : Blo 179801 183363 := bstep (se 1 (by rfl) ⟨137522, by rfl⟩ : syracuseStep 183363 = 275045) B275045
theorem B412739 : Blo 179801 412739 := bstep (se 1 (by rfl) ⟨309554, by rfl⟩ : syracuseStep 412739 = 619109) B619109
theorem B1035341 : Blo 179801 1035341 := bstep (se 3 (by rfl) ⟨194126, by rfl⟩ : syracuseStep 1035341 = 388253) B388253
theorem B183379 : Blo 179801 183379 := bstep (se 1 (by rfl) ⟨137534, by rfl⟩ : syracuseStep 183379 = 275069) B275069
theorem B183395 : Blo 179801 183395 := bstep (se 1 (by rfl) ⟨137546, by rfl⟩ : syracuseStep 183395 = 275093) B275093
theorem B609389 : Blo 179801 609389 := bstep (se 3 (by rfl) ⟨114260, by rfl⟩ : syracuseStep 609389 = 228521) B228521
theorem B183411 : Blo 179801 183411 := bstep (se 1 (by rfl) ⟨137558, by rfl⟩ : syracuseStep 183411 = 275117) B275117
theorem B183427 : Blo 179801 183427 := bstep (se 1 (by rfl) ⟨137570, by rfl⟩ : syracuseStep 183427 = 275141) B275141
theorem B183443 : Blo 179801 183443 := bstep (se 1 (by rfl) ⟨137582, by rfl⟩ : syracuseStep 183443 = 275165) B275165
theorem B609443 : Blo 179801 609443 := bstep (se 1 (by rfl) ⟨457082, by rfl⟩ : syracuseStep 609443 = 914165) B914165
theorem B183459 : Blo 179801 183459 := bstep (se 1 (by rfl) ⟨137594, by rfl⟩ : syracuseStep 183459 = 275189) B275189
theorem B183475 : Blo 179801 183475 := bstep (se 1 (by rfl) ⟨137606, by rfl⟩ : syracuseStep 183475 = 275213) B275213
theorem B183491 : Blo 179801 183491 := bstep (se 1 (by rfl) ⟨137618, by rfl⟩ : syracuseStep 183491 = 275237) B275237
theorem B183507 : Blo 179801 183507 := bstep (se 1 (by rfl) ⟨137630, by rfl⟩ : syracuseStep 183507 = 275261) B275261
theorem B5950691 : Blo 179801 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B183523 : Blo 179801 183523 := bstep (se 1 (by rfl) ⟨137642, by rfl⟩ : syracuseStep 183523 = 275285) B275285
theorem B183539 : Blo 179801 183539 := bstep (se 1 (by rfl) ⟨137654, by rfl⟩ : syracuseStep 183539 = 275309) B275309
theorem B183555 : Blo 179801 183555 := bstep (se 1 (by rfl) ⟨137666, by rfl⟩ : syracuseStep 183555 = 275333) B275333
theorem B183571 : Blo 179801 183571 := bstep (se 1 (by rfl) ⟨137678, by rfl⟩ : syracuseStep 183571 = 275357) B275357
theorem B183587 : Blo 179801 183587 := bstep (se 1 (by rfl) ⟨137690, by rfl⟩ : syracuseStep 183587 = 275381) B275381
theorem B183603 : Blo 179801 183603 := bstep (se 1 (by rfl) ⟨137702, by rfl⟩ : syracuseStep 183603 = 275405) B275405
theorem B183619 : Blo 179801 183619 := bstep (se 1 (by rfl) ⟨137714, by rfl⟩ : syracuseStep 183619 = 275429) B275429
theorem B576845 : Blo 179801 576845 := bstep (se 3 (by rfl) ⟨108158, by rfl⟩ : syracuseStep 576845 = 216317) B216317
theorem B413009 : Blo 179801 413009 := bstep (se 2 (by rfl) ⟨154878, by rfl⟩ : syracuseStep 413009 = 309757) B309757
theorem B183635 : Blo 179801 183635 := bstep (se 1 (by rfl) ⟨137726, by rfl⟩ : syracuseStep 183635 = 275453) B275453
theorem B413027 : Blo 179801 413027 := bstep (se 1 (by rfl) ⟨309770, by rfl⟩ : syracuseStep 413027 = 619541) B619541
theorem B183651 : Blo 179801 183651 := bstep (se 1 (by rfl) ⟨137738, by rfl⟩ : syracuseStep 183651 = 275477) B275477
theorem B183667 : Blo 179801 183667 := bstep (se 1 (by rfl) ⟨137750, by rfl⟩ : syracuseStep 183667 = 275501) B275501
theorem B183683 : Blo 179801 183683 := bstep (se 1 (by rfl) ⟨137762, by rfl⟩ : syracuseStep 183683 = 275525) B275525
theorem B6344077 : Blo 179801 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B183699 : Blo 179801 183699 := bstep (se 1 (by rfl) ⟨137774, by rfl⟩ : syracuseStep 183699 = 275549) B275549
theorem B183715 : Blo 179801 183715 := bstep (se 1 (by rfl) ⟨137786, by rfl⟩ : syracuseStep 183715 = 275573) B275573
theorem B609713 : Blo 179801 609713 := bstep (se 2 (by rfl) ⟨228642, by rfl⟩ : syracuseStep 609713 = 457285) B457285
theorem B183731 : Blo 179801 183731 := bstep (se 1 (by rfl) ⟨137798, by rfl⟩ : syracuseStep 183731 = 275597) B275597
theorem B183747 : Blo 179801 183747 := bstep (se 1 (by rfl) ⟨137810, by rfl⟩ : syracuseStep 183747 = 275621) B275621
theorem B183763 : Blo 179801 183763 := bstep (se 1 (by rfl) ⟨137822, by rfl⟩ : syracuseStep 183763 = 275645) B275645
theorem B183779 : Blo 179801 183779 := bstep (se 1 (by rfl) ⟨137834, by rfl⟩ : syracuseStep 183779 = 275669) B275669
theorem B183795 : Blo 179801 183795 := bstep (se 1 (by rfl) ⟨137846, by rfl⟩ : syracuseStep 183795 = 275693) B275693
theorem B347665 : Blo 179801 347665 := bstep (se 2 (by rfl) ⟨130374, by rfl⟩ : syracuseStep 347665 = 260749) B260749
theorem B183827 : Blo 179801 183827 := bstep (se 1 (by rfl) ⟨137870, by rfl⟩ : syracuseStep 183827 = 275741) B275741
theorem B413297 : Blo 179801 413297 := bstep (se 2 (by rfl) ⟨154986, by rfl⟩ : syracuseStep 413297 = 309973) B309973
theorem B413315 : Blo 179801 413315 := bstep (se 1 (by rfl) ⟨309986, by rfl⟩ : syracuseStep 413315 = 619973) B619973
theorem B675533 : Blo 179801 675533 := bstep (se 3 (by rfl) ⟨126662, by rfl⟩ : syracuseStep 675533 = 253325) B253325
theorem B2641805 : Blo 179801 2641805 := bstep (se 3 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 2641805 = 990677) B990677
theorem B2346893 : Blo 179801 2346893 := bstep (se 3 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 2346893 = 880085) B880085
theorem B348067 : Blo 179801 348067 := bstep (se 1 (by rfl) ⟨261050, by rfl⟩ : syracuseStep 348067 = 522101) B522101
theorem B610253 : Blo 179801 610253 := bstep (se 3 (by rfl) ⟨114422, by rfl⟩ : syracuseStep 610253 = 228845) B228845
theorem B348113 : Blo 179801 348113 := bstep (se 2 (by rfl) ⟨130542, by rfl⟩ : syracuseStep 348113 = 261085) B261085
theorem B1036273 : Blo 179801 1036273 := bstep (se 2 (by rfl) ⟨388602, by rfl⟩ : syracuseStep 1036273 = 777205) B777205
theorem B937969 : Blo 179801 937969 := bstep (se 2 (by rfl) ⟨351738, by rfl⟩ : syracuseStep 937969 = 703477) B703477
theorem B610307 : Blo 179801 610307 := bstep (se 1 (by rfl) ⟨457730, by rfl⟩ : syracuseStep 610307 = 915461) B915461
theorem B512077 : Blo 179801 512077 := bstep (se 3 (by rfl) ⟨96014, by rfl⟩ : syracuseStep 512077 = 192029) B192029
theorem B1101937 : Blo 179801 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B512237 : Blo 179801 512237 := bstep (se 3 (by rfl) ⟨96044, by rfl⟩ : syracuseStep 512237 = 192089) B192089
theorem B348401 : Blo 179801 348401 := bstep (se 2 (by rfl) ⟨130650, by rfl⟩ : syracuseStep 348401 = 261301) B261301
theorem B610577 : Blo 179801 610577 := bstep (se 2 (by rfl) ⟨228966, by rfl⟩ : syracuseStep 610577 = 457933) B457933
theorem B512419 : Blo 179801 512419 := bstep (se 1 (by rfl) ⟨384314, by rfl⟩ : syracuseStep 512419 = 768629) B768629
theorem B217523 : Blo 179801 217523 := bstep (se 1 (by rfl) ⟨163142, by rfl⟩ : syracuseStep 217523 = 326285) B326285
theorem B17125829 : Blo 179801 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B1102499 : Blo 179801 1102499 := bstep (se 1 (by rfl) ⟨826874, by rfl⟩ : syracuseStep 1102499 = 1653749) B1653749
theorem B611117 : Blo 179801 611117 := bstep (se 3 (by rfl) ⟨114584, by rfl⟩ : syracuseStep 611117 = 229169) B229169
theorem B611171 : Blo 179801 611171 := bstep (se 1 (by rfl) ⟨458378, by rfl⟩ : syracuseStep 611171 = 916757) B916757
theorem B939043 : Blo 179801 939043 := bstep (se 1 (by rfl) ⟨704282, by rfl⟩ : syracuseStep 939043 = 1408565) B1408565
theorem B611441 : Blo 179801 611441 := bstep (se 2 (by rfl) ⟨229290, by rfl⟩ : syracuseStep 611441 = 458581) B458581
theorem B578701 : Blo 179801 578701 := bstep (se 3 (by rfl) ⟨108506, by rfl⟩ : syracuseStep 578701 = 217013) B217013
theorem B775565 : Blo 179801 775565 := bstep (se 3 (by rfl) ⟨145418, by rfl⟩ : syracuseStep 775565 = 290837) B290837
theorem B1037731 : Blo 179801 1037731 := bstep (se 1 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 1037731 = 1556597) B1556597
theorem B775601 : Blo 179801 775601 := bstep (se 2 (by rfl) ⟨290850, by rfl⟩ : syracuseStep 775601 = 581701) B581701
theorem B611981 : Blo 179801 611981 := bstep (se 3 (by rfl) ⟨114746, by rfl⟩ : syracuseStep 611981 = 229493) B229493
theorem B612035 : Blo 179801 612035 := bstep (se 1 (by rfl) ⟨459026, by rfl⟩ : syracuseStep 612035 = 918053) B918053
theorem B513809 : Blo 179801 513809 := bstep (se 2 (by rfl) ⟨192678, by rfl⟩ : syracuseStep 513809 = 385357) B385357
theorem B1038257 : Blo 179801 1038257 := bstep (se 2 (by rfl) ⟨389346, by rfl⟩ : syracuseStep 1038257 = 778693) B778693
theorem B612305 : Blo 179801 612305 := bstep (se 2 (by rfl) ⟨229614, by rfl⟩ : syracuseStep 612305 = 459229) B459229
theorem B1169477 : Blo 179801 1169477 := bstep (se 4 (by rfl) ⟨109638, by rfl⟩ : syracuseStep 1169477 = 219277) B219277
theorem B612845 : Blo 179801 612845 := bstep (se 3 (by rfl) ⟨114908, by rfl⟩ : syracuseStep 612845 = 229817) B229817
theorem B612899 : Blo 179801 612899 := bstep (se 1 (by rfl) ⟨459674, by rfl⟩ : syracuseStep 612899 = 919349) B919349
theorem B547469 : Blo 179801 547469 := bstep (se 3 (by rfl) ⟨102650, by rfl⟩ : syracuseStep 547469 = 205301) B205301
theorem B514765 : Blo 179801 514765 := bstep (se 3 (by rfl) ⟨96518, by rfl⟩ : syracuseStep 514765 = 193037) B193037
theorem B613169 : Blo 179801 613169 := bstep (se 2 (by rfl) ⟨229938, by rfl⟩ : syracuseStep 613169 = 459877) B459877
theorem B547661 : Blo 179801 547661 := bstep (se 3 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 547661 = 205373) B205373
theorem B514993 : Blo 179801 514993 := bstep (se 2 (by rfl) ⟨193122, by rfl⟩ : syracuseStep 514993 = 386245) B386245
theorem B580547 : Blo 179801 580547 := bstep (se 1 (by rfl) ⟨435410, by rfl⟩ : syracuseStep 580547 = 870821) B870821
theorem B220099 : Blo 179801 220099 := bstep (se 1 (by rfl) ⟨165074, by rfl⟩ : syracuseStep 220099 = 330149) B330149
theorem B515153 : Blo 179801 515153 := bstep (se 2 (by rfl) ⟨193182, by rfl⟩ : syracuseStep 515153 = 386365) B386365
theorem B1006769 : Blo 179801 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B515267 : Blo 179801 515267 := bstep (se 1 (by rfl) ⟨386450, by rfl⟩ : syracuseStep 515267 = 772901) B772901
theorem B220483 : Blo 179801 220483 := bstep (se 1 (by rfl) ⟨165362, by rfl⟩ : syracuseStep 220483 = 330725) B330725
theorem B613709 : Blo 179801 613709 := bstep (se 3 (by rfl) ⟨115070, by rfl⟩ : syracuseStep 613709 = 230141) B230141
theorem B580945 : Blo 179801 580945 := bstep (se 2 (by rfl) ⟨217854, by rfl⟩ : syracuseStep 580945 = 435709) B435709
theorem B1039715 : Blo 179801 1039715 := bstep (se 1 (by rfl) ⟨779786, by rfl⟩ : syracuseStep 1039715 = 1559573) B1559573
theorem B613763 : Blo 179801 613763 := bstep (se 1 (by rfl) ⟨460322, by rfl⟩ : syracuseStep 613763 = 920645) B920645
theorem B482737 : Blo 179801 482737 := bstep (se 2 (by rfl) ⟨181026, by rfl⟩ : syracuseStep 482737 = 362053) B362053
theorem B2055779 : Blo 179801 2055779 := bstep (se 1 (by rfl) ⟨1541834, by rfl⟩ : syracuseStep 2055779 = 3083669) B3083669
theorem B614033 : Blo 179801 614033 := bstep (se 2 (by rfl) ⟨230262, by rfl⟩ : syracuseStep 614033 = 460525) B460525
theorem B384707 : Blo 179801 384707 := bstep (se 1 (by rfl) ⟨288530, by rfl⟩ : syracuseStep 384707 = 577061) B577061
theorem B581393 : Blo 179801 581393 := bstep (se 2 (by rfl) ⟨218022, by rfl⟩ : syracuseStep 581393 = 436045) B436045
theorem B516269 : Blo 179801 516269 := bstep (se 3 (by rfl) ⟨96800, by rfl⟩ : syracuseStep 516269 = 193601) B193601
theorem B614573 : Blo 179801 614573 := bstep (se 3 (by rfl) ⟨115232, by rfl⟩ : syracuseStep 614573 = 230465) B230465
theorem B614627 : Blo 179801 614627 := bstep (se 1 (by rfl) ⟨460970, by rfl⟩ : syracuseStep 614627 = 921941) B921941
theorem B516451 : Blo 179801 516451 := bstep (se 1 (by rfl) ⟨387338, by rfl⟩ : syracuseStep 516451 = 774677) B774677
theorem B614897 : Blo 179801 614897 := bstep (se 2 (by rfl) ⟨230586, by rfl⟩ : syracuseStep 614897 = 461173) B461173
theorem B516611 : Blo 179801 516611 := bstep (se 1 (by rfl) ⟨387458, by rfl⟩ : syracuseStep 516611 = 774917) B774917
theorem B2187917 : Blo 179801 2187917 := bstep (se 3 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 2187917 = 820469) B820469
theorem B975523 : Blo 179801 975523 := bstep (se 1 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 975523 = 1463285) B1463285
theorem B418627 : Blo 179801 418627 := bstep (se 1 (by rfl) ⟨313970, by rfl⟩ : syracuseStep 418627 = 627941) B627941
theorem B1991537 : Blo 179801 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B385955 : Blo 179801 385955 := bstep (se 1 (by rfl) ⟨289466, by rfl⟩ : syracuseStep 385955 = 578933) B578933
theorem B615437 : Blo 179801 615437 := bstep (se 3 (by rfl) ⟨115394, by rfl⟩ : syracuseStep 615437 = 230789) B230789
theorem B615491 : Blo 179801 615491 := bstep (se 1 (by rfl) ⟨461618, by rfl⟩ : syracuseStep 615491 = 923237) B923237
theorem B1041605 : Blo 179801 1041605 := bstep (se 4 (by rfl) ⟨97650, by rfl⟩ : syracuseStep 1041605 = 195301) B195301
theorem B1172677 : Blo 179801 1172677 := bstep (se 4 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 1172677 = 219877) B219877
theorem B1238321 : Blo 179801 1238321 := bstep (se 2 (by rfl) ⟨464370, by rfl⟩ : syracuseStep 1238321 = 928741) B928741
theorem B615761 : Blo 179801 615761 := bstep (se 2 (by rfl) ⟨230910, by rfl⟩ : syracuseStep 615761 = 461821) B461821
theorem B386545 : Blo 179801 386545 := bstep (se 2 (by rfl) ⟨144954, by rfl⟩ : syracuseStep 386545 = 289909) B289909
theorem B550385 : Blo 179801 550385 := bstep (se 2 (by rfl) ⟨206394, by rfl⟩ : syracuseStep 550385 = 412789) B412789
theorem B517681 : Blo 179801 517681 := bstep (se 2 (by rfl) ⟨194130, by rfl⟩ : syracuseStep 517681 = 388261) B388261
theorem B910925 : Blo 179801 910925 := bstep (se 3 (by rfl) ⟨170798, by rfl⟩ : syracuseStep 910925 = 341597) B341597
theorem B779939 : Blo 179801 779939 := bstep (se 1 (by rfl) ⟨584954, by rfl⟩ : syracuseStep 779939 = 1169909) B1169909
theorem B583469 : Blo 179801 583469 := bstep (se 3 (by rfl) ⟨109400, by rfl⟩ : syracuseStep 583469 = 218801) B218801
theorem B616301 : Blo 179801 616301 := bstep (se 3 (by rfl) ⟨115556, by rfl⟩ : syracuseStep 616301 = 231113) B231113
theorem B288659 : Blo 179801 288659 := bstep (se 1 (by rfl) ⟨216494, by rfl⟩ : syracuseStep 288659 = 432989) B432989
theorem B616355 : Blo 179801 616355 := bstep (se 1 (by rfl) ⟨462266, by rfl⟩ : syracuseStep 616355 = 924533) B924533
theorem B288787 : Blo 179801 288787 := bstep (se 1 (by rfl) ⟨216590, by rfl⟩ : syracuseStep 288787 = 433181) B433181
theorem B288851 : Blo 179801 288851 := bstep (se 1 (by rfl) ⟨216638, by rfl⟩ : syracuseStep 288851 = 433277) B433277
theorem B616547 : Blo 179801 616547 := bstep (se 1 (by rfl) ⟨462410, by rfl⟩ : syracuseStep 616547 = 924821) B924821
theorem B616625 : Blo 179801 616625 := bstep (se 2 (by rfl) ⟨231234, by rfl⟩ : syracuseStep 616625 = 462469) B462469
theorem B1239245 : Blo 179801 1239245 := bstep (se 3 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 1239245 = 464717) B464717
theorem B551117 : Blo 179801 551117 := bstep (se 3 (by rfl) ⟨103334, by rfl⟩ : syracuseStep 551117 = 206669) B206669
theorem B256289 : Blo 179801 256289 := bstep (se 2 (by rfl) ⟨96108, by rfl⟩ : syracuseStep 256289 = 192217) B192217
theorem B256403 : Blo 179801 256403 := bstep (se 1 (by rfl) ⟨192302, by rfl⟩ : syracuseStep 256403 = 384605) B384605
theorem B256483 : Blo 179801 256483 := bstep (se 1 (by rfl) ⟨192362, by rfl⟩ : syracuseStep 256483 = 384725) B384725
theorem B1993187 : Blo 179801 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B289345 : Blo 179801 289345 := bstep (se 2 (by rfl) ⟨108504, by rfl⟩ : syracuseStep 289345 = 217009) B217009
theorem B3500657 : Blo 179801 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B617165 : Blo 179801 617165 := bstep (se 3 (by rfl) ⟨115718, by rfl⟩ : syracuseStep 617165 = 231437) B231437
theorem B617219 : Blo 179801 617219 := bstep (se 1 (by rfl) ⟨462914, by rfl⟩ : syracuseStep 617219 = 925829) B925829
theorem B518957 : Blo 179801 518957 := bstep (se 3 (by rfl) ⟨97304, by rfl⟩ : syracuseStep 518957 = 194609) B194609
theorem B453539 : Blo 179801 453539 := bstep (se 1 (by rfl) ⟨340154, by rfl⟩ : syracuseStep 453539 = 680309) B680309
theorem B519139 : Blo 179801 519139 := bstep (se 1 (by rfl) ⟨389354, by rfl⟩ : syracuseStep 519139 = 778709) B778709
theorem B2190349 : Blo 179801 2190349 := bstep (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) B821381
theorem B257041 : Blo 179801 257041 := bstep (se 2 (by rfl) ⟨96390, by rfl⟩ : syracuseStep 257041 = 192781) B192781
theorem B519185 : Blo 179801 519185 := bstep (se 2 (by rfl) ⟨194694, by rfl⟩ : syracuseStep 519185 = 389389) B389389
theorem B617489 : Blo 179801 617489 := bstep (se 2 (by rfl) ⟨231558, by rfl⟩ : syracuseStep 617489 = 463117) B463117
theorem B584749 : Blo 179801 584749 := bstep (se 3 (by rfl) ⟨109640, by rfl⟩ : syracuseStep 584749 = 219281) B219281
theorem B1109189 : Blo 179801 1109189 := bstep (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) B207973
theorem B2092229 : Blo 179801 2092229 := bstep (se 4 (by rfl) ⟨196146, by rfl⟩ : syracuseStep 2092229 = 392293) B392293
theorem B290017 : Blo 179801 290017 := bstep (se 2 (by rfl) ⟨108756, by rfl⟩ : syracuseStep 290017 = 217513) B217513
theorem B1371491 : Blo 179801 1371491 := bstep (se 1 (by rfl) ⟨1028618, by rfl⟩ : syracuseStep 1371491 = 2057237) B2057237
theorem B585251 : Blo 179801 585251 := bstep (se 1 (by rfl) ⟨438938, by rfl⟩ : syracuseStep 585251 = 877877) B877877
theorem B618029 : Blo 179801 618029 := bstep (se 3 (by rfl) ⟨115880, by rfl⟩ : syracuseStep 618029 = 231761) B231761
theorem B618083 : Blo 179801 618083 := bstep (se 1 (by rfl) ⟨463562, by rfl⟩ : syracuseStep 618083 = 927125) B927125
theorem B192179 : Blo 179801 192179 := bstep (se 1 (by rfl) ⟨144134, by rfl⟩ : syracuseStep 192179 = 288269) B288269
theorem B257747 : Blo 179801 257747 := bstep (se 1 (by rfl) ⟨193310, by rfl⟩ : syracuseStep 257747 = 386621) B386621
theorem B1765091 : Blo 179801 1765091 := bstep (se 1 (by rfl) ⟨1323818, by rfl⟩ : syracuseStep 1765091 = 2647637) B2647637
theorem B618353 : Blo 179801 618353 := bstep (se 2 (by rfl) ⟨231882, by rfl⟩ : syracuseStep 618353 = 463765) B463765
theorem B487405 : Blo 179801 487405 := bstep (se 3 (by rfl) ⟨91388, by rfl⟩ : syracuseStep 487405 = 182777) B182777
theorem B880739 : Blo 179801 880739 := bstep (se 1 (by rfl) ⟨660554, by rfl⟩ : syracuseStep 880739 = 1321109) B1321109
theorem B1667213 : Blo 179801 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B291107 : Blo 179801 291107 := bstep (se 1 (by rfl) ⟨218330, by rfl⟩ : syracuseStep 291107 = 436661) B436661
theorem B4714805 : Blo 179801 4714805 := bstep (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) B442013
theorem B258385 : Blo 179801 258385 := bstep (se 2 (by rfl) ⟨96894, by rfl⟩ : syracuseStep 258385 = 193789) B193789
theorem B618893 : Blo 179801 618893 := bstep (se 3 (by rfl) ⟨116042, by rfl⟩ : syracuseStep 618893 = 232085) B232085
theorem B913841 : Blo 179801 913841 := bstep (se 2 (by rfl) ⟨342690, by rfl⟩ : syracuseStep 913841 = 685381) B685381
theorem B258499 : Blo 179801 258499 := bstep (se 1 (by rfl) ⟨193874, by rfl⟩ : syracuseStep 258499 = 387749) B387749
theorem B520643 : Blo 179801 520643 := bstep (se 1 (by rfl) ⟨390482, by rfl⟩ : syracuseStep 520643 = 780965) B780965
theorem B618947 : Blo 179801 618947 := bstep (se 1 (by rfl) ⟨464210, by rfl⟩ : syracuseStep 618947 = 928421) B928421
theorem B291395 : Blo 179801 291395 := bstep (se 1 (by rfl) ⟨218546, by rfl⟩ : syracuseStep 291395 = 437093) B437093
theorem B389731 : Blo 179801 389731 := bstep (se 1 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 389731 = 584597) B584597
theorem B1176241 : Blo 179801 1176241 := bstep (se 2 (by rfl) ⟨441090, by rfl⟩ : syracuseStep 1176241 = 882181) B882181
theorem B619217 : Blo 179801 619217 := bstep (se 2 (by rfl) ⟨232206, by rfl⟩ : syracuseStep 619217 = 464413) B464413
theorem B586595 : Blo 179801 586595 := bstep (se 1 (by rfl) ⟨439946, by rfl⟩ : syracuseStep 586595 = 879893) B879893
theorem B291811 : Blo 179801 291811 := bstep (se 1 (by rfl) ⟨218858, by rfl⟩ : syracuseStep 291811 = 437717) B437717
theorem B455665 : Blo 179801 455665 := bstep (se 2 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 455665 = 341749) B341749
theorem B685169 : Blo 179801 685169 := bstep (se 2 (by rfl) ⟨256938, by rfl⟩ : syracuseStep 685169 = 513877) B513877
theorem B619757 : Blo 179801 619757 := bstep (se 3 (by rfl) ⟨116204, by rfl⟩ : syracuseStep 619757 = 232409) B232409
theorem B292081 : Blo 179801 292081 := bstep (se 2 (by rfl) ⟨109530, by rfl⟩ : syracuseStep 292081 = 219061) B219061
theorem B455939 : Blo 179801 455939 := bstep (se 1 (by rfl) ⟨341954, by rfl⟩ : syracuseStep 455939 = 683909) B683909
theorem B619811 : Blo 179801 619811 := bstep (se 1 (by rfl) ⟨464858, by rfl⟩ : syracuseStep 619811 = 929717) B929717
theorem B783665 : Blo 179801 783665 := bstep (se 2 (by rfl) ⟨293874, by rfl⟩ : syracuseStep 783665 = 587749) B587749
theorem B652643 : Blo 179801 652643 := bstep (se 1 (by rfl) ⟨489482, by rfl⟩ : syracuseStep 652643 = 978965) B978965
theorem B390577 : Blo 179801 390577 := bstep (se 2 (by rfl) ⟨146466, by rfl⟩ : syracuseStep 390577 = 292933) B292933
theorem B456131 : Blo 179801 456131 := bstep (se 1 (by rfl) ⟨342098, by rfl⟩ : syracuseStep 456131 = 684197) B684197
theorem B587213 : Blo 179801 587213 := bstep (se 3 (by rfl) ⟨110102, by rfl⟩ : syracuseStep 587213 = 220205) B220205
theorem B292337 : Blo 179801 292337 := bstep (se 2 (by rfl) ⟨109626, by rfl⟩ : syracuseStep 292337 = 219253) B219253
theorem B620081 : Blo 179801 620081 := bstep (se 2 (by rfl) ⟨232530, by rfl⟩ : syracuseStep 620081 = 465061) B465061
theorem B521873 : Blo 179801 521873 := bstep (se 2 (by rfl) ⟨195702, by rfl⟩ : syracuseStep 521873 = 391405) B391405
theorem B194195 : Blo 179801 194195 := bstep (se 1 (by rfl) ⟨145646, by rfl⟩ : syracuseStep 194195 = 291293) B291293
theorem B882353 : Blo 179801 882353 := bstep (se 2 (by rfl) ⟨330882, by rfl⟩ : syracuseStep 882353 = 661765) B661765
theorem B259843 : Blo 179801 259843 := bstep (se 1 (by rfl) ⟨194882, by rfl⟩ : syracuseStep 259843 = 389765) B389765
theorem B587569 : Blo 179801 587569 := bstep (se 2 (by rfl) ⟨220338, by rfl⟩ : syracuseStep 587569 = 440677) B440677
theorem B915299 : Blo 179801 915299 := bstep (se 1 (by rfl) ⟨686474, by rfl⟩ : syracuseStep 915299 = 1372949) B1372949
theorem B587665 : Blo 179801 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B587825 : Blo 179801 587825 := bstep (se 2 (by rfl) ⟨220434, by rfl⟩ : syracuseStep 587825 = 440869) B440869
theorem B293041 : Blo 179801 293041 := bstep (se 2 (by rfl) ⟨109890, by rfl⟩ : syracuseStep 293041 = 219781) B219781
theorem B555373 : Blo 179801 555373 := bstep (se 3 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 555373 = 208265) B208265
theorem B457073 : Blo 179801 457073 := bstep (se 2 (by rfl) ⟨171402, by rfl⟩ : syracuseStep 457073 = 342805) B342805
theorem B457123 : Blo 179801 457123 := bstep (se 1 (by rfl) ⟨342842, by rfl⟩ : syracuseStep 457123 = 685685) B685685
theorem B653795 : Blo 179801 653795 := bstep (se 1 (by rfl) ⟨490346, by rfl⟩ : syracuseStep 653795 = 980693) B980693
theorem B1735181 : Blo 179801 1735181 := bstep (se 3 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 1735181 = 650693) B650693
theorem B4946453 : Blo 179801 4946453 := bstep (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) B231865
theorem B686627 : Blo 179801 686627 := bstep (se 1 (by rfl) ⟨514970, by rfl⟩ : syracuseStep 686627 = 1029941) B1029941
theorem B457265 : Blo 179801 457265 := bstep (se 2 (by rfl) ⟨171474, by rfl⟩ : syracuseStep 457265 = 342949) B342949
theorem B195139 : Blo 179801 195139 := bstep (se 1 (by rfl) ⟨146354, by rfl⟩ : syracuseStep 195139 = 292709) B292709
theorem B916109 : Blo 179801 916109 := bstep (se 3 (by rfl) ⟨171770, by rfl⟩ : syracuseStep 916109 = 343541) B343541
theorem B228035 : Blo 179801 228035 := bstep (se 1 (by rfl) ⟨171026, by rfl⟩ : syracuseStep 228035 = 342053) B342053
theorem B391889 : Blo 179801 391889 := bstep (se 2 (by rfl) ⟨146958, by rfl⟩ : syracuseStep 391889 = 293917) B293917
theorem B555875 : Blo 179801 555875 := bstep (se 1 (by rfl) ⟨416906, by rfl⟩ : syracuseStep 555875 = 833813) B833813
theorem B260977 : Blo 179801 260977 := bstep (se 2 (by rfl) ⟨97866, by rfl⟩ : syracuseStep 260977 = 195733) B195733
theorem B261073 : Blo 179801 261073 := bstep (se 2 (by rfl) ⟨97902, by rfl⟩ : syracuseStep 261073 = 195805) B195805
theorem B293939 : Blo 179801 293939 := bstep (se 1 (by rfl) ⟨220454, by rfl⟩ : syracuseStep 293939 = 440909) B440909
theorem B523331 : Blo 179801 523331 := bstep (se 1 (by rfl) ⟨392498, by rfl⟩ : syracuseStep 523331 = 784997) B784997
theorem B294131 : Blo 179801 294131 := bstep (se 1 (by rfl) ⟨220598, by rfl⟩ : syracuseStep 294131 = 441197) B441197
theorem B392465 : Blo 179801 392465 := bstep (se 2 (by rfl) ⟨147174, by rfl⟩ : syracuseStep 392465 = 294349) B294349
theorem B228739 : Blo 179801 228739 := bstep (se 1 (by rfl) ⟨171554, by rfl⟩ : syracuseStep 228739 = 343109) B343109
theorem B261569 : Blo 179801 261569 := bstep (se 2 (by rfl) ⟨98088, by rfl⟩ : syracuseStep 261569 = 196177) B196177
theorem B490961 : Blo 179801 490961 := bstep (se 2 (by rfl) ⟨184110, by rfl⟩ : syracuseStep 490961 = 368221) B368221
theorem B228835 : Blo 179801 228835 := bstep (se 1 (by rfl) ⟨171626, by rfl⟩ : syracuseStep 228835 = 343253) B343253
theorem B687629 : Blo 179801 687629 := bstep (se 3 (by rfl) ⟨128930, by rfl⟩ : syracuseStep 687629 = 257861) B257861
theorem B458257 : Blo 179801 458257 := bstep (se 2 (by rfl) ⟨171846, by rfl⟩ : syracuseStep 458257 = 343693) B343693
theorem B654961 : Blo 179801 654961 := bstep (se 2 (by rfl) ⟨245610, by rfl⟩ : syracuseStep 654961 = 491221) B491221
theorem B655075 : Blo 179801 655075 := bstep (se 1 (by rfl) ⟨491306, by rfl⟩ : syracuseStep 655075 = 982613) B982613
theorem B458531 : Blo 179801 458531 := bstep (se 1 (by rfl) ⟨343898, by rfl⟩ : syracuseStep 458531 = 687797) B687797
theorem B491437 : Blo 179801 491437 := bstep (se 3 (by rfl) ⟨92144, by rfl⟩ : syracuseStep 491437 = 184289) B184289
theorem B229331 : Blo 179801 229331 := bstep (se 1 (by rfl) ⟨171998, by rfl⟩ : syracuseStep 229331 = 343997) B343997
theorem B458723 : Blo 179801 458723 := bstep (se 1 (by rfl) ⟨344042, by rfl⟩ : syracuseStep 458723 = 688085) B688085
theorem B229387 : Blo 179801 229387 := bstep (se 1 (by rfl) ⟨172040, by rfl⟩ : syracuseStep 229387 = 344081) B344081
theorem B229655 : Blo 179801 229655 := bstep (se 1 (by rfl) ⟨172241, by rfl⟩ : syracuseStep 229655 = 344483) B344483
theorem B917891 : Blo 179801 917891 := bstep (se 1 (by rfl) ⟨688418, by rfl⟩ : syracuseStep 917891 = 1376837) B1376837
theorem B688601 : Blo 179801 688601 := bstep (se 2 (by rfl) ⟨258225, by rfl⟩ : syracuseStep 688601 = 516451) B516451
theorem B1966609 : Blo 179801 1966609 := bstep (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) B1474957
theorem B1049219 : Blo 179801 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B393943 : Blo 179801 393943 := bstep (se 1 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 393943 = 590915) B590915
theorem B1114955 : Blo 179801 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B1541015 : Blo 179801 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B328627 : Blo 179801 328627 := bstep (se 1 (by rfl) ⟨246470, by rfl⟩ : syracuseStep 328627 = 492941) B492941
theorem B230359 : Blo 179801 230359 := bstep (se 1 (by rfl) ⟨172769, by rfl⟩ : syracuseStep 230359 = 345539) B345539
theorem B328691 : Blo 179801 328691 := bstep (se 1 (by rfl) ⟨246518, by rfl⟩ : syracuseStep 328691 = 493037) B493037
theorem B459827 : Blo 179801 459827 := bstep (se 1 (by rfl) ⟨344870, by rfl⟩ : syracuseStep 459827 = 689741) B689741
theorem B1246529 : Blo 179801 1246529 := bstep (se 2 (by rfl) ⟨467448, by rfl⟩ : syracuseStep 1246529 = 934897) B934897
theorem B1377809 : Blo 179801 1377809 := bstep (se 2 (by rfl) ⟨516678, by rfl⟩ : syracuseStep 1377809 = 1033357) B1033357
theorem B460363 : Blo 179801 460363 := bstep (se 1 (by rfl) ⟨345272, by rfl⟩ : syracuseStep 460363 = 690545) B690545
theorem B460505 : Blo 179801 460505 := bstep (se 2 (by rfl) ⟨172689, by rfl⟩ : syracuseStep 460505 = 345379) B345379
theorem B657325 : Blo 179801 657325 := bstep (se 3 (by rfl) ⟨123248, by rfl⟩ : syracuseStep 657325 = 246497) B246497
theorem B329665 : Blo 179801 329665 := bstep (se 2 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 329665 = 247249) B247249
theorem B329687 : Blo 179801 329687 := bstep (se 1 (by rfl) ⟨247265, by rfl⟩ : syracuseStep 329687 = 494531) B494531
theorem B329729 : Blo 179801 329729 := bstep (se 2 (by rfl) ⟨123648, by rfl⟩ : syracuseStep 329729 = 247297) B247297
theorem B690227 : Blo 179801 690227 := bstep (se 1 (by rfl) ⟨517670, by rfl⟩ : syracuseStep 690227 = 1035341) B1035341
theorem B690241 : Blo 179801 690241 := bstep (se 2 (by rfl) ⟨258840, by rfl⟩ : syracuseStep 690241 = 517681) B517681
theorem B1312919 : Blo 179801 1312919 := bstep (se 1 (by rfl) ⟨984689, by rfl⟩ : syracuseStep 1312919 = 1969379) B1969379
theorem B3967127 : Blo 179801 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B6850861 : Blo 179801 6850861 := bstep (se 3 (by rfl) ⟨1284536, by rfl⟩ : syracuseStep 6850861 = 2569073) B2569073
theorem B1182131 : Blo 179801 1182131 := bstep (se 1 (by rfl) ⟨886598, by rfl⟩ : syracuseStep 1182131 = 1773197) B1773197
theorem B461335 : Blo 179801 461335 := bstep (se 1 (by rfl) ⟨346001, by rfl⟩ : syracuseStep 461335 = 692003) B692003
theorem B232075 : Blo 179801 232075 := bstep (se 1 (by rfl) ⟨174056, by rfl⟩ : syracuseStep 232075 = 348113) B348113
theorem B461771 : Blo 179801 461771 := bstep (se 1 (by rfl) ⟨346328, by rfl⟩ : syracuseStep 461771 = 692657) B692657
theorem B462145 : Blo 179801 462145 := bstep (se 2 (by rfl) ⟨173304, by rfl⟩ : syracuseStep 462145 = 346609) B346609
theorem B1052261 : Blo 179801 1052261 := bstep (se 4 (by rfl) ⟨98649, by rfl⟩ : syracuseStep 1052261 = 197299) B197299
theorem B462743 : Blo 179801 462743 := bstep (se 1 (by rfl) ⟨347057, by rfl⟩ : syracuseStep 462743 = 694115) B694115
theorem B692171 : Blo 179801 692171 := bstep (se 1 (by rfl) ⟨519128, by rfl⟩ : syracuseStep 692171 = 1038257) B1038257
theorem B692185 : Blo 179801 692185 := bstep (se 2 (by rfl) ⟨259569, by rfl⟩ : syracuseStep 692185 = 519139) B519139
theorem B2920465 : Blo 179801 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B921617 : Blo 179801 921617 := bstep (se 2 (by rfl) ⟨345606, by rfl⟩ : syracuseStep 921617 = 691213) B691213
theorem B921779 : Blo 179801 921779 := bstep (se 1 (by rfl) ⟨691334, by rfl⟩ : syracuseStep 921779 = 1382669) B1382669
theorem B659677 : Blo 179801 659677 := bstep (se 3 (by rfl) ⟨123689, by rfl⟩ : syracuseStep 659677 = 247379) B247379
theorem B2232677 : Blo 179801 2232677 := bstep (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) B418627
theorem B364979 : Blo 179801 364979 := bstep (se 1 (by rfl) ⟨273734, by rfl⟩ : syracuseStep 364979 = 547469) B547469
theorem B8458769 : Blo 179801 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B2101891 : Blo 179801 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B463553 : Blo 179801 463553 := bstep (se 2 (by rfl) ⟨173832, by rfl⟩ : syracuseStep 463553 = 347665) B347665
theorem B693143 : Blo 179801 693143 := bstep (se 1 (by rfl) ⟨519857, by rfl⟩ : syracuseStep 693143 = 1039715) B1039715
theorem B365465 : Blo 179801 365465 := bstep (se 2 (by rfl) ⟨137049, by rfl⟩ : syracuseStep 365465 = 274099) B274099
theorem B464089 : Blo 179801 464089 := bstep (se 2 (by rfl) ⟨174033, by rfl⟩ : syracuseStep 464089 = 348067) B348067
theorem B1381697 : Blo 179801 1381697 := bstep (se 2 (by rfl) ⟨518136, by rfl⟩ : syracuseStep 1381697 = 1036273) B1036273
theorem B3118661 : Blo 179801 3118661 := bstep (se 4 (by rfl) ⟨292374, by rfl⟩ : syracuseStep 3118661 = 584749) B584749
theorem B202315 : Blo 179801 202315 := bstep (se 1 (by rfl) ⟨151736, by rfl⟩ : syracuseStep 202315 = 303473) B303473
theorem B202423 : Blo 179801 202423 := bstep (se 1 (by rfl) ⟨151817, by rfl⟩ : syracuseStep 202423 = 303635) B303635
theorem B202603 : Blo 179801 202603 := bstep (se 1 (by rfl) ⟨151952, by rfl⟩ : syracuseStep 202603 = 303905) B303905
theorem B202711 : Blo 179801 202711 := bstep (se 1 (by rfl) ⟨152033, by rfl⟩ : syracuseStep 202711 = 304067) B304067
theorem B923665 : Blo 179801 923665 := bstep (se 2 (by rfl) ⟨346374, by rfl⟩ : syracuseStep 923665 = 692749) B692749
theorem B923723 : Blo 179801 923723 := bstep (se 1 (by rfl) ⟨692792, by rfl⟩ : syracuseStep 923723 = 1385585) B1385585
theorem B694403 : Blo 179801 694403 := bstep (se 1 (by rfl) ⟨520802, by rfl⟩ : syracuseStep 694403 = 1041605) B1041605
theorem B202891 : Blo 179801 202891 := bstep (se 1 (by rfl) ⟨152168, by rfl⟩ : syracuseStep 202891 = 304337) B304337
theorem B825547 : Blo 179801 825547 := bstep (se 1 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 825547 = 1238321) B1238321
theorem B202999 : Blo 179801 202999 := bstep (se 1 (by rfl) ⟨152249, by rfl⟩ : syracuseStep 202999 = 304499) B304499
theorem B465203 : Blo 179801 465203 := bstep (se 1 (by rfl) ⟨348902, by rfl⟩ : syracuseStep 465203 = 697805) B697805
theorem B366923 : Blo 179801 366923 := bstep (se 1 (by rfl) ⟨275192, by rfl⟩ : syracuseStep 366923 = 550385) B550385
theorem B203179 : Blo 179801 203179 := bstep (se 1 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 203179 = 304769) B304769
theorem B203287 : Blo 179801 203287 := bstep (se 1 (by rfl) ⟨152465, by rfl⟩ : syracuseStep 203287 = 304931) B304931
theorem B203467 : Blo 179801 203467 := bstep (se 1 (by rfl) ⟨152600, by rfl⟩ : syracuseStep 203467 = 305201) B305201
theorem B1252057 : Blo 179801 1252057 := bstep (se 2 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 1252057 = 939043) B939043
theorem B826163 : Blo 179801 826163 := bstep (se 1 (by rfl) ⟨619622, by rfl⟩ : syracuseStep 826163 = 1239245) B1239245
theorem B367411 : Blo 179801 367411 := bstep (se 1 (by rfl) ⟨275558, by rfl⟩ : syracuseStep 367411 = 551117) B551117
theorem B203575 : Blo 179801 203575 := bstep (se 1 (by rfl) ⟨152681, by rfl⟩ : syracuseStep 203575 = 305363) B305363
theorem B498649 : Blo 179801 498649 := bstep (se 2 (by rfl) ⟨186993, by rfl⟩ : syracuseStep 498649 = 373987) B373987
theorem B203755 : Blo 179801 203755 := bstep (se 1 (by rfl) ⟨152816, by rfl⟩ : syracuseStep 203755 = 305633) B305633
theorem B2333771 : Blo 179801 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B203863 : Blo 179801 203863 := bstep (se 1 (by rfl) ⟨152897, by rfl⟩ : syracuseStep 203863 = 305795) B305795
theorem B1383641 : Blo 179801 1383641 := bstep (se 2 (by rfl) ⟨518865, by rfl⟩ : syracuseStep 1383641 = 1037731) B1037731
theorem B204043 : Blo 179801 204043 := bstep (se 1 (by rfl) ⟨153032, by rfl⟩ : syracuseStep 204043 = 306065) B306065
theorem B302359 : Blo 179801 302359 := bstep (se 1 (by rfl) ⟨226769, by rfl⟩ : syracuseStep 302359 = 453539) B453539
theorem B367961 : Blo 179801 367961 := bstep (se 2 (by rfl) ⟨137985, by rfl⟩ : syracuseStep 367961 = 275971) B275971
theorem B204151 : Blo 179801 204151 := bstep (se 1 (by rfl) ⟨153113, by rfl⟩ : syracuseStep 204151 = 306227) B306227
theorem B269771 : Blo 179801 269771 := bstep (se 1 (by rfl) ⟨202328, by rfl⟩ : syracuseStep 269771 = 404657) B404657
theorem B269783 : Blo 179801 269783 := bstep (se 1 (by rfl) ⟨202337, by rfl⟩ : syracuseStep 269783 = 404675) B404675
theorem B269849 : Blo 179801 269849 := bstep (se 2 (by rfl) ⟨101193, by rfl⟩ : syracuseStep 269849 = 202387) B202387
theorem B204331 : Blo 179801 204331 := bstep (se 1 (by rfl) ⟨153248, by rfl⟩ : syracuseStep 204331 = 306497) B306497
theorem B269963 : Blo 179801 269963 := bstep (se 1 (by rfl) ⟨202472, by rfl⟩ : syracuseStep 269963 = 404945) B404945
theorem B269975 : Blo 179801 269975 := bstep (se 1 (by rfl) ⟨202481, by rfl⟩ : syracuseStep 269975 = 404963) B404963
theorem B204439 : Blo 179801 204439 := bstep (se 1 (by rfl) ⟨153329, by rfl⟩ : syracuseStep 204439 = 306659) B306659
theorem B270041 : Blo 179801 270041 := bstep (se 2 (by rfl) ⟨101265, by rfl⟩ : syracuseStep 270041 = 202531) B202531
theorem B925505 : Blo 179801 925505 := bstep (se 2 (by rfl) ⟨347064, by rfl⟩ : syracuseStep 925505 = 694129) B694129
theorem B270155 : Blo 179801 270155 := bstep (se 1 (by rfl) ⟨202616, by rfl⟩ : syracuseStep 270155 = 405233) B405233
theorem B204619 : Blo 179801 204619 := bstep (se 1 (by rfl) ⟨153464, by rfl⟩ : syracuseStep 204619 = 306929) B306929
theorem B270167 : Blo 179801 270167 := bstep (se 1 (by rfl) ⟨202625, by rfl⟩ : syracuseStep 270167 = 405251) B405251
theorem B270233 : Blo 179801 270233 := bstep (se 2 (by rfl) ⟨101337, by rfl⟩ : syracuseStep 270233 = 202675) B202675
theorem B204727 : Blo 179801 204727 := bstep (se 1 (by rfl) ⟨153545, by rfl⟩ : syracuseStep 204727 = 307091) B307091
theorem B270347 : Blo 179801 270347 := bstep (se 1 (by rfl) ⟨202760, by rfl⟩ : syracuseStep 270347 = 405521) B405521
theorem B270359 : Blo 179801 270359 := bstep (se 1 (by rfl) ⟨202769, by rfl⟩ : syracuseStep 270359 = 405539) B405539
theorem B270425 : Blo 179801 270425 := bstep (se 2 (by rfl) ⟨101409, by rfl⟩ : syracuseStep 270425 = 202819) B202819
theorem B204907 : Blo 179801 204907 := bstep (se 1 (by rfl) ⟨153680, by rfl⟩ : syracuseStep 204907 = 307361) B307361
theorem B1646743 : Blo 179801 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B270539 : Blo 179801 270539 := bstep (se 1 (by rfl) ⟨202904, by rfl⟩ : syracuseStep 270539 = 405809) B405809
theorem B270551 : Blo 179801 270551 := bstep (se 1 (by rfl) ⟨202913, by rfl⟩ : syracuseStep 270551 = 405827) B405827
theorem B205015 : Blo 179801 205015 := bstep (se 1 (by rfl) ⟨153761, by rfl⟩ : syracuseStep 205015 = 307523) B307523
theorem B270617 : Blo 179801 270617 := bstep (se 2 (by rfl) ⟨101481, by rfl⟩ : syracuseStep 270617 = 202963) B202963
theorem B270731 : Blo 179801 270731 := bstep (se 1 (by rfl) ⟨203048, by rfl⟩ : syracuseStep 270731 = 406097) B406097
theorem B205195 : Blo 179801 205195 := bstep (se 1 (by rfl) ⟨153896, by rfl⟩ : syracuseStep 205195 = 307793) B307793
theorem B270743 : Blo 179801 270743 := bstep (se 1 (by rfl) ⟨203057, by rfl⟩ : syracuseStep 270743 = 406115) B406115
theorem B270809 : Blo 179801 270809 := bstep (se 2 (by rfl) ⟨101553, by rfl⟩ : syracuseStep 270809 = 203107) B203107
theorem B205303 : Blo 179801 205303 := bstep (se 1 (by rfl) ⟨153977, by rfl⟩ : syracuseStep 205303 = 307955) B307955
theorem B270923 : Blo 179801 270923 := bstep (se 1 (by rfl) ⟨203192, by rfl⟩ : syracuseStep 270923 = 406385) B406385
theorem B270935 : Blo 179801 270935 := bstep (se 1 (by rfl) ⟨203201, by rfl⟩ : syracuseStep 270935 = 406403) B406403
theorem B271001 : Blo 179801 271001 := bstep (se 2 (by rfl) ⟨101625, by rfl⟩ : syracuseStep 271001 = 203251) B203251
theorem B205483 : Blo 179801 205483 := bstep (se 1 (by rfl) ⟨154112, by rfl⟩ : syracuseStep 205483 = 308225) B308225
theorem B271115 : Blo 179801 271115 := bstep (se 1 (by rfl) ⟨203336, by rfl⟩ : syracuseStep 271115 = 406673) B406673
theorem B271127 : Blo 179801 271127 := bstep (se 1 (by rfl) ⟨203345, by rfl⟩ : syracuseStep 271127 = 406691) B406691
theorem B205591 : Blo 179801 205591 := bstep (se 1 (by rfl) ⟨154193, by rfl⟩ : syracuseStep 205591 = 308387) B308387
theorem B303959 : Blo 179801 303959 := bstep (se 1 (by rfl) ⟨227969, by rfl⟩ : syracuseStep 303959 = 455939) B455939
theorem B271193 : Blo 179801 271193 := bstep (se 2 (by rfl) ⟨101697, by rfl⟩ : syracuseStep 271193 = 203395) B203395
theorem B435095 : Blo 179801 435095 := bstep (se 1 (by rfl) ⟨326321, by rfl⟩ : syracuseStep 435095 = 652643) B652643
theorem B271307 : Blo 179801 271307 := bstep (se 1 (by rfl) ⟨203480, by rfl⟩ : syracuseStep 271307 = 406961) B406961
theorem B205771 : Blo 179801 205771 := bstep (se 1 (by rfl) ⟨154328, by rfl⟩ : syracuseStep 205771 = 308657) B308657
theorem B304087 : Blo 179801 304087 := bstep (se 1 (by rfl) ⟨228065, by rfl⟩ : syracuseStep 304087 = 456131) B456131
theorem B271319 : Blo 179801 271319 := bstep (se 1 (by rfl) ⟨203489, by rfl⟩ : syracuseStep 271319 = 406979) B406979
theorem B10298389 : Blo 179801 10298389 := bstep (se 6 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 10298389 = 482737) B482737
theorem B5284885 : Blo 179801 5284885 := bstep (se 6 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 5284885 = 247729) B247729
theorem B271385 : Blo 179801 271385 := bstep (se 2 (by rfl) ⟨101769, by rfl⟩ : syracuseStep 271385 = 203539) B203539
theorem B205879 : Blo 179801 205879 := bstep (se 1 (by rfl) ⟨154409, by rfl⟩ : syracuseStep 205879 = 308819) B308819
theorem B271499 : Blo 179801 271499 := bstep (se 1 (by rfl) ⟨203624, by rfl⟩ : syracuseStep 271499 = 407249) B407249
theorem B271511 : Blo 179801 271511 := bstep (se 1 (by rfl) ⟨203633, by rfl⟩ : syracuseStep 271511 = 407267) B407267
theorem B697517 : Blo 179801 697517 := bstep (se 3 (by rfl) ⟨130784, by rfl⟩ : syracuseStep 697517 = 261569) B261569
theorem B1549489 : Blo 179801 1549489 := bstep (se 2 (by rfl) ⟨581058, by rfl⟩ : syracuseStep 1549489 = 1162117) B1162117
theorem B271577 : Blo 179801 271577 := bstep (se 2 (by rfl) ⟨101841, by rfl⟩ : syracuseStep 271577 = 203683) B203683
theorem B206059 : Blo 179801 206059 := bstep (se 1 (by rfl) ⟨154544, by rfl⟩ : syracuseStep 206059 = 309089) B309089
theorem B271691 : Blo 179801 271691 := bstep (se 1 (by rfl) ⟨203768, by rfl⟩ : syracuseStep 271691 = 407537) B407537
theorem B271703 : Blo 179801 271703 := bstep (se 1 (by rfl) ⟨203777, by rfl⟩ : syracuseStep 271703 = 407555) B407555
theorem B206167 : Blo 179801 206167 := bstep (se 1 (by rfl) ⟨154625, by rfl⟩ : syracuseStep 206167 = 309251) B309251
theorem B271769 : Blo 179801 271769 := bstep (se 2 (by rfl) ⟨101913, by rfl⟩ : syracuseStep 271769 = 203827) B203827
theorem B271883 : Blo 179801 271883 := bstep (se 1 (by rfl) ⟨203912, by rfl⟩ : syracuseStep 271883 = 407825) B407825
theorem B206347 : Blo 179801 206347 := bstep (se 1 (by rfl) ⟨154760, by rfl⟩ : syracuseStep 206347 = 309521) B309521
theorem B271895 : Blo 179801 271895 := bstep (se 1 (by rfl) ⟨203921, by rfl⟩ : syracuseStep 271895 = 407843) B407843
theorem B304715 : Blo 179801 304715 := bstep (se 1 (by rfl) ⟨228536, by rfl⟩ : syracuseStep 304715 = 457073) B457073
theorem B271961 : Blo 179801 271961 := bstep (se 2 (by rfl) ⟨101985, by rfl⟩ : syracuseStep 271961 = 203971) B203971
theorem B206455 : Blo 179801 206455 := bstep (se 1 (by rfl) ⟨154841, by rfl⟩ : syracuseStep 206455 = 309683) B309683
theorem B435863 : Blo 179801 435863 := bstep (se 1 (by rfl) ⟨326897, by rfl⟩ : syracuseStep 435863 = 653795) B653795
theorem B1156787 : Blo 179801 1156787 := bstep (se 1 (by rfl) ⟨867590, by rfl⟩ : syracuseStep 1156787 = 1735181) B1735181
theorem B304843 : Blo 179801 304843 := bstep (se 1 (by rfl) ⟨228632, by rfl⟩ : syracuseStep 304843 = 457265) B457265
theorem B272075 : Blo 179801 272075 := bstep (se 1 (by rfl) ⟨204056, by rfl⟩ : syracuseStep 272075 = 408113) B408113
theorem B272087 : Blo 179801 272087 := bstep (se 1 (by rfl) ⟨204065, by rfl⟩ : syracuseStep 272087 = 408131) B408131
theorem B927449 : Blo 179801 927449 := bstep (se 2 (by rfl) ⟨347793, by rfl⟩ : syracuseStep 927449 = 695587) B695587
theorem B272153 : Blo 179801 272153 := bstep (se 2 (by rfl) ⟨102057, by rfl⟩ : syracuseStep 272153 = 204115) B204115
theorem B206635 : Blo 179801 206635 := bstep (se 1 (by rfl) ⟨154976, by rfl⟩ : syracuseStep 206635 = 309953) B309953
theorem B304985 : Blo 179801 304985 := bstep (se 2 (by rfl) ⟨114369, by rfl⟩ : syracuseStep 304985 = 228739) B228739
theorem B1025885 : Blo 179801 1025885 := bstep (se 3 (by rfl) ⟨192353, by rfl⟩ : syracuseStep 1025885 = 384707) B384707
theorem B272267 : Blo 179801 272267 := bstep (se 1 (by rfl) ⟨204200, by rfl⟩ : syracuseStep 272267 = 408401) B408401
theorem B370583 : Blo 179801 370583 := bstep (se 1 (by rfl) ⟨277937, by rfl⟩ : syracuseStep 370583 = 555875) B555875
theorem B272279 : Blo 179801 272279 := bstep (se 1 (by rfl) ⟨204209, by rfl⟩ : syracuseStep 272279 = 408419) B408419
theorem B206743 : Blo 179801 206743 := bstep (se 1 (by rfl) ⟨155057, by rfl⟩ : syracuseStep 206743 = 310115) B310115
theorem B305113 : Blo 179801 305113 := bstep (se 2 (by rfl) ⟨114417, by rfl⟩ : syracuseStep 305113 = 228835) B228835
theorem B272345 : Blo 179801 272345 := bstep (se 2 (by rfl) ⟨102129, by rfl⟩ : syracuseStep 272345 = 204259) B204259
theorem B272459 : Blo 179801 272459 := bstep (se 1 (by rfl) ⟨204344, by rfl⟩ : syracuseStep 272459 = 408689) B408689
theorem B272471 : Blo 179801 272471 := bstep (se 1 (by rfl) ⟨204353, by rfl⟩ : syracuseStep 272471 = 408707) B408707
theorem B272537 : Blo 179801 272537 := bstep (se 2 (by rfl) ⟨102201, by rfl⟩ : syracuseStep 272537 = 204403) B204403
theorem B272651 : Blo 179801 272651 := bstep (se 1 (by rfl) ⟨204488, by rfl⟩ : syracuseStep 272651 = 408977) B408977
theorem B272663 : Blo 179801 272663 := bstep (se 1 (by rfl) ⟨204497, by rfl⟩ : syracuseStep 272663 = 408995) B408995
theorem B272729 : Blo 179801 272729 := bstep (se 2 (by rfl) ⟨102273, by rfl⟩ : syracuseStep 272729 = 204547) B204547
theorem B272843 : Blo 179801 272843 := bstep (se 1 (by rfl) ⟨204632, by rfl⟩ : syracuseStep 272843 = 409265) B409265
theorem B272855 : Blo 179801 272855 := bstep (se 1 (by rfl) ⟨204641, by rfl⟩ : syracuseStep 272855 = 409283) B409283
theorem B305687 : Blo 179801 305687 := bstep (se 1 (by rfl) ⟨229265, by rfl⟩ : syracuseStep 305687 = 458531) B458531
theorem B272921 : Blo 179801 272921 := bstep (se 2 (by rfl) ⟨102345, by rfl⟩ : syracuseStep 272921 = 204691) B204691
theorem B1387043 : Blo 179801 1387043 := bstep (se 1 (by rfl) ⟨1040282, by rfl⟩ : syracuseStep 1387043 = 2080565) B2080565
theorem B273035 : Blo 179801 273035 := bstep (se 1 (by rfl) ⟨204776, by rfl⟩ : syracuseStep 273035 = 409553) B409553
theorem B305815 : Blo 179801 305815 := bstep (se 1 (by rfl) ⟨229361, by rfl⟩ : syracuseStep 305815 = 458723) B458723
theorem B273047 : Blo 179801 273047 := bstep (se 1 (by rfl) ⟨204785, by rfl⟩ : syracuseStep 273047 = 409571) B409571
theorem B273113 : Blo 179801 273113 := bstep (se 2 (by rfl) ⟨102417, by rfl⟩ : syracuseStep 273113 = 204835) B204835
theorem B273227 : Blo 179801 273227 := bstep (se 1 (by rfl) ⟨204920, by rfl⟩ : syracuseStep 273227 = 409841) B409841
theorem B273239 : Blo 179801 273239 := bstep (se 1 (by rfl) ⟨204929, by rfl⟩ : syracuseStep 273239 = 409859) B409859
theorem B273305 : Blo 179801 273305 := bstep (se 2 (by rfl) ⟨102489, by rfl⟩ : syracuseStep 273305 = 204979) B204979
theorem B273419 : Blo 179801 273419 := bstep (se 1 (by rfl) ⟨205064, by rfl⟩ : syracuseStep 273419 = 410129) B410129
theorem B273431 : Blo 179801 273431 := bstep (se 1 (by rfl) ⟨205073, by rfl⟩ : syracuseStep 273431 = 410147) B410147
theorem B404567 : Blo 179801 404567 := bstep (se 1 (by rfl) ⟨303425, by rfl⟩ : syracuseStep 404567 = 606851) B606851
theorem B273497 : Blo 179801 273497 := bstep (se 2 (by rfl) ⟨102561, by rfl⟩ : syracuseStep 273497 = 205123) B205123
theorem B273611 : Blo 179801 273611 := bstep (se 1 (by rfl) ⟨205208, by rfl⟩ : syracuseStep 273611 = 410417) B410417
theorem B273623 : Blo 179801 273623 := bstep (se 1 (by rfl) ⟨205217, by rfl⟩ : syracuseStep 273623 = 410435) B410435
theorem B404747 : Blo 179801 404747 := bstep (se 1 (by rfl) ⟨303560, by rfl⟩ : syracuseStep 404747 = 607121) B607121
theorem B306443 : Blo 179801 306443 := bstep (se 1 (by rfl) ⟨229832, by rfl⟩ : syracuseStep 306443 = 459665) B459665
theorem B273689 : Blo 179801 273689 := bstep (se 2 (by rfl) ⟨102633, by rfl⟩ : syracuseStep 273689 = 205267) B205267
theorem B929069 : Blo 179801 929069 := bstep (se 3 (by rfl) ⟨174200, by rfl⟩ : syracuseStep 929069 = 348401) B348401
theorem B437555 : Blo 179801 437555 := bstep (se 1 (by rfl) ⟨328166, by rfl⟩ : syracuseStep 437555 = 656333) B656333
theorem B404801 : Blo 179801 404801 := bstep (se 2 (by rfl) ⟨151800, by rfl⟩ : syracuseStep 404801 = 303601) B303601
theorem B306571 : Blo 179801 306571 := bstep (se 1 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 306571 = 459857) B459857
theorem B273803 : Blo 179801 273803 := bstep (se 1 (by rfl) ⟨205352, by rfl⟩ : syracuseStep 273803 = 410705) B410705
theorem B372107 : Blo 179801 372107 := bstep (se 1 (by rfl) ⟨279080, by rfl⟩ : syracuseStep 372107 = 558161) B558161
theorem B273815 : Blo 179801 273815 := bstep (se 1 (by rfl) ⟨205361, by rfl⟩ : syracuseStep 273815 = 410723) B410723
theorem B273881 : Blo 179801 273881 := bstep (se 2 (by rfl) ⟨102705, by rfl⟩ : syracuseStep 273881 = 205411) B205411
theorem B2665997 : Blo 179801 2665997 := bstep (se 3 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 2665997 = 999749) B999749
theorem B405017 : Blo 179801 405017 := bstep (se 2 (by rfl) ⟨151881, by rfl⟩ : syracuseStep 405017 = 303763) B303763
theorem B306713 : Blo 179801 306713 := bstep (se 2 (by rfl) ⟨115017, by rfl⟩ : syracuseStep 306713 = 230035) B230035
theorem B273995 : Blo 179801 273995 := bstep (se 1 (by rfl) ⟨205496, by rfl⟩ : syracuseStep 273995 = 410993) B410993
theorem B274007 : Blo 179801 274007 := bstep (se 1 (by rfl) ⟨205505, by rfl⟩ : syracuseStep 274007 = 411011) B411011
theorem B405107 : Blo 179801 405107 := bstep (se 1 (by rfl) ⟨303830, by rfl⟩ : syracuseStep 405107 = 607661) B607661
theorem B405143 : Blo 179801 405143 := bstep (se 1 (by rfl) ⟨303857, by rfl⟩ : syracuseStep 405143 = 607715) B607715
theorem B306841 : Blo 179801 306841 := bstep (se 2 (by rfl) ⟨115065, by rfl⟩ : syracuseStep 306841 = 230131) B230131
theorem B274073 : Blo 179801 274073 := bstep (se 2 (by rfl) ⟨102777, by rfl⟩ : syracuseStep 274073 = 205555) B205555
theorem B1584845 : Blo 179801 1584845 := bstep (se 3 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 1584845 = 594317) B594317
theorem B274187 : Blo 179801 274187 := bstep (se 1 (by rfl) ⟨205640, by rfl⟩ : syracuseStep 274187 = 411281) B411281
theorem B274199 : Blo 179801 274199 := bstep (se 1 (by rfl) ⟨205649, by rfl⟩ : syracuseStep 274199 = 411299) B411299
theorem B1486637 : Blo 179801 1486637 := bstep (se 3 (by rfl) ⟨278744, by rfl⟩ : syracuseStep 1486637 = 557489) B557489
theorem B405323 : Blo 179801 405323 := bstep (se 1 (by rfl) ⟨303992, by rfl⟩ : syracuseStep 405323 = 607985) B607985
theorem B274265 : Blo 179801 274265 := bstep (se 2 (by rfl) ⟨102849, by rfl⟩ : syracuseStep 274265 = 205699) B205699
theorem B405377 : Blo 179801 405377 := bstep (se 2 (by rfl) ⟨152016, by rfl⟩ : syracuseStep 405377 = 304033) B304033
theorem B274379 : Blo 179801 274379 := bstep (se 1 (by rfl) ⟨205784, by rfl⟩ : syracuseStep 274379 = 411569) B411569
theorem B274391 : Blo 179801 274391 := bstep (se 1 (by rfl) ⟨205793, by rfl⟩ : syracuseStep 274391 = 411587) B411587
theorem B274457 : Blo 179801 274457 := bstep (se 2 (by rfl) ⟨102921, by rfl⟩ : syracuseStep 274457 = 205843) B205843
theorem B405593 : Blo 179801 405593 := bstep (se 2 (by rfl) ⟨152097, by rfl⟩ : syracuseStep 405593 = 304195) B304195
theorem B274571 : Blo 179801 274571 := bstep (se 1 (by rfl) ⟨205928, by rfl⟩ : syracuseStep 274571 = 411857) B411857
theorem B274583 : Blo 179801 274583 := bstep (se 1 (by rfl) ⟨205937, by rfl⟩ : syracuseStep 274583 = 411875) B411875
theorem B405683 : Blo 179801 405683 := bstep (se 1 (by rfl) ⟨304262, by rfl⟩ : syracuseStep 405683 = 608525) B608525
theorem B1585331 : Blo 179801 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B405719 : Blo 179801 405719 := bstep (se 1 (by rfl) ⟨304289, by rfl⟩ : syracuseStep 405719 = 608579) B608579
theorem B307415 : Blo 179801 307415 := bstep (se 1 (by rfl) ⟨230561, by rfl⟩ : syracuseStep 307415 = 461123) B461123
theorem B274649 : Blo 179801 274649 := bstep (se 2 (by rfl) ⟨102993, by rfl⟩ : syracuseStep 274649 = 205987) B205987
theorem B274763 : Blo 179801 274763 := bstep (se 1 (by rfl) ⟨206072, by rfl⟩ : syracuseStep 274763 = 412145) B412145
theorem B307543 : Blo 179801 307543 := bstep (se 1 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 307543 = 461315) B461315
theorem B274775 : Blo 179801 274775 := bstep (se 1 (by rfl) ⟨206081, by rfl⟩ : syracuseStep 274775 = 412163) B412163
theorem B1028483 : Blo 179801 1028483 := bstep (se 1 (by rfl) ⟨771362, by rfl⟩ : syracuseStep 1028483 = 1542725) B1542725
theorem B1159555 : Blo 179801 1159555 := bstep (se 1 (by rfl) ⟨869666, by rfl⟩ : syracuseStep 1159555 = 1739333) B1739333
theorem B405899 : Blo 179801 405899 := bstep (se 1 (by rfl) ⟨304424, by rfl⟩ : syracuseStep 405899 = 608849) B608849
theorem B274841 : Blo 179801 274841 := bstep (se 2 (by rfl) ⟨103065, by rfl⟩ : syracuseStep 274841 = 206131) B206131
theorem B405953 : Blo 179801 405953 := bstep (se 2 (by rfl) ⟨152232, by rfl⟩ : syracuseStep 405953 = 304465) B304465
theorem B274955 : Blo 179801 274955 := bstep (se 1 (by rfl) ⟨206216, by rfl⟩ : syracuseStep 274955 = 412433) B412433
theorem B274967 : Blo 179801 274967 := bstep (se 1 (by rfl) ⟨206225, by rfl⟩ : syracuseStep 274967 = 412451) B412451
theorem B2667043 : Blo 179801 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B275033 : Blo 179801 275033 := bstep (se 2 (by rfl) ⟨103137, by rfl⟩ : syracuseStep 275033 = 206275) B206275
theorem B832145 : Blo 179801 832145 := bstep (se 2 (by rfl) ⟨312054, by rfl⟩ : syracuseStep 832145 = 624109) B624109
theorem B275095 : Blo 179801 275095 := bstep (se 1 (by rfl) ⟨206321, by rfl⟩ : syracuseStep 275095 = 412643) B412643
theorem B406169 : Blo 179801 406169 := bstep (se 2 (by rfl) ⟨152313, by rfl⟩ : syracuseStep 406169 = 304627) B304627
theorem B275147 : Blo 179801 275147 := bstep (se 1 (by rfl) ⟨206360, by rfl⟩ : syracuseStep 275147 = 412721) B412721
theorem B275159 : Blo 179801 275159 := bstep (se 1 (by rfl) ⟨206369, by rfl⟩ : syracuseStep 275159 = 412739) B412739
theorem B406259 : Blo 179801 406259 := bstep (se 1 (by rfl) ⟨304694, by rfl⟩ : syracuseStep 406259 = 609389) B609389
theorem B406295 : Blo 179801 406295 := bstep (se 1 (by rfl) ⟨304721, by rfl⟩ : syracuseStep 406295 = 609443) B609443
theorem B275225 : Blo 179801 275225 := bstep (se 2 (by rfl) ⟨103209, by rfl⟩ : syracuseStep 275225 = 206419) B206419
theorem B275339 : Blo 179801 275339 := bstep (se 1 (by rfl) ⟨206504, by rfl⟩ : syracuseStep 275339 = 413009) B413009
theorem B275351 : Blo 179801 275351 := bstep (se 1 (by rfl) ⟨206513, by rfl⟩ : syracuseStep 275351 = 413027) B413027
theorem B406475 : Blo 179801 406475 := bstep (se 1 (by rfl) ⟨304856, by rfl⟩ : syracuseStep 406475 = 609713) B609713
theorem B308171 : Blo 179801 308171 := bstep (se 1 (by rfl) ⟨231128, by rfl⟩ : syracuseStep 308171 = 462257) B462257
theorem B275417 : Blo 179801 275417 := bstep (se 2 (by rfl) ⟨103281, by rfl⟩ : syracuseStep 275417 = 206563) B206563
theorem B406529 : Blo 179801 406529 := bstep (se 2 (by rfl) ⟨152448, by rfl⟩ : syracuseStep 406529 = 304897) B304897
theorem B439319 : Blo 179801 439319 := bstep (se 1 (by rfl) ⟨329489, by rfl⟩ : syracuseStep 439319 = 658979) B658979
theorem B308299 : Blo 179801 308299 := bstep (se 1 (by rfl) ⟨231224, by rfl⟩ : syracuseStep 308299 = 462449) B462449
theorem B275531 : Blo 179801 275531 := bstep (se 1 (by rfl) ⟨206648, by rfl⟩ : syracuseStep 275531 = 413297) B413297
theorem B275543 : Blo 179801 275543 := bstep (se 1 (by rfl) ⟨206657, by rfl⟩ : syracuseStep 275543 = 413315) B413315
theorem B439447 : Blo 179801 439447 := bstep (se 1 (by rfl) ⟨329585, by rfl⟩ : syracuseStep 439447 = 659171) B659171
theorem B275609 : Blo 179801 275609 := bstep (se 2 (by rfl) ⟨103353, by rfl⟩ : syracuseStep 275609 = 206707) B206707
theorem B406745 : Blo 179801 406745 := bstep (se 2 (by rfl) ⟨152529, by rfl⟩ : syracuseStep 406745 = 305059) B305059
theorem B308441 : Blo 179801 308441 := bstep (se 2 (by rfl) ⟨115665, by rfl⟩ : syracuseStep 308441 = 231331) B231331
theorem B406835 : Blo 179801 406835 := bstep (se 1 (by rfl) ⟨305126, by rfl⟩ : syracuseStep 406835 = 610253) B610253
theorem B406871 : Blo 179801 406871 := bstep (se 1 (by rfl) ⟨305153, by rfl⟩ : syracuseStep 406871 = 610307) B610307
theorem B308569 : Blo 179801 308569 := bstep (se 2 (by rfl) ⟨115713, by rfl⟩ : syracuseStep 308569 = 231427) B231427
theorem B341491 : Blo 179801 341491 := bstep (se 1 (by rfl) ⟨256118, by rfl⟩ : syracuseStep 341491 = 512237) B512237
theorem B407051 : Blo 179801 407051 := bstep (se 1 (by rfl) ⟨305288, by rfl⟩ : syracuseStep 407051 = 610577) B610577
theorem B407105 : Blo 179801 407105 := bstep (se 2 (by rfl) ⟨152664, by rfl⟩ : syracuseStep 407105 = 305329) B305329
theorem B11417219 : Blo 179801 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B1554137 : Blo 179801 1554137 := bstep (se 2 (by rfl) ⟨582801, by rfl⟩ : syracuseStep 1554137 = 1165603) B1165603
theorem B734999 : Blo 179801 734999 := bstep (se 1 (by rfl) ⟨551249, by rfl⟩ : syracuseStep 734999 = 1102499) B1102499
theorem B407321 : Blo 179801 407321 := bstep (se 2 (by rfl) ⟨152745, by rfl⟩ : syracuseStep 407321 = 305491) B305491
theorem B407411 : Blo 179801 407411 := bstep (se 1 (by rfl) ⟨305558, by rfl⟩ : syracuseStep 407411 = 611117) B611117
theorem B407447 : Blo 179801 407447 := bstep (se 1 (by rfl) ⟨305585, by rfl⟩ : syracuseStep 407447 = 611171) B611171
theorem B309143 : Blo 179801 309143 := bstep (se 1 (by rfl) ⟨231857, by rfl⟩ : syracuseStep 309143 = 463715) B463715
theorem B341977 : Blo 179801 341977 := bstep (se 2 (by rfl) ⟨128241, by rfl⟩ : syracuseStep 341977 = 256483) B256483
theorem B309271 : Blo 179801 309271 := bstep (se 1 (by rfl) ⟨231953, by rfl⟩ : syracuseStep 309271 = 463907) B463907
theorem B407627 : Blo 179801 407627 := bstep (se 1 (by rfl) ⟨305720, by rfl⟩ : syracuseStep 407627 = 611441) B611441
theorem B407681 : Blo 179801 407681 := bstep (se 2 (by rfl) ⟨152880, by rfl⟩ : syracuseStep 407681 = 305761) B305761
theorem B407897 : Blo 179801 407897 := bstep (se 2 (by rfl) ⟨152961, by rfl⟩ : syracuseStep 407897 = 305923) B305923
theorem B407987 : Blo 179801 407987 := bstep (se 1 (by rfl) ⟨305990, by rfl⟩ : syracuseStep 407987 = 611981) B611981
theorem B1292723 : Blo 179801 1292723 := bstep (se 1 (by rfl) ⟨969542, by rfl⟩ : syracuseStep 1292723 = 1939085) B1939085
theorem B244183 : Blo 179801 244183 := bstep (se 1 (by rfl) ⟨183137, by rfl⟩ : syracuseStep 244183 = 366275) B366275
theorem B408023 : Blo 179801 408023 := bstep (se 1 (by rfl) ⟨306017, by rfl⟩ : syracuseStep 408023 = 612035) B612035
theorem B342539 : Blo 179801 342539 := bstep (se 1 (by rfl) ⟨256904, by rfl⟩ : syracuseStep 342539 = 513809) B513809
theorem B408203 : Blo 179801 408203 := bstep (se 1 (by rfl) ⟨306152, by rfl⟩ : syracuseStep 408203 = 612305) B612305
theorem B309899 : Blo 179801 309899 := bstep (se 1 (by rfl) ⟨232424, by rfl⟩ : syracuseStep 309899 = 464849) B464849
theorem B342721 : Blo 179801 342721 := bstep (se 2 (by rfl) ⟨128520, by rfl⟩ : syracuseStep 342721 = 257041) B257041
theorem B408257 : Blo 179801 408257 := bstep (se 2 (by rfl) ⟨153096, by rfl⟩ : syracuseStep 408257 = 306193) B306193
theorem B310027 : Blo 179801 310027 := bstep (se 1 (by rfl) ⟨232520, by rfl⟩ : syracuseStep 310027 = 465041) B465041
theorem B441139 : Blo 179801 441139 := bstep (se 1 (by rfl) ⟨330854, by rfl⟩ : syracuseStep 441139 = 661709) B661709
theorem B408473 : Blo 179801 408473 := bstep (se 2 (by rfl) ⟨153177, by rfl⟩ : syracuseStep 408473 = 306355) B306355
theorem B408563 : Blo 179801 408563 := bstep (se 1 (by rfl) ⟨306422, by rfl⟩ : syracuseStep 408563 = 612845) B612845
theorem B408599 : Blo 179801 408599 := bstep (se 1 (by rfl) ⟨306449, by rfl⟩ : syracuseStep 408599 = 612899) B612899
theorem B408779 : Blo 179801 408779 := bstep (se 1 (by rfl) ⟨306584, by rfl⟩ : syracuseStep 408779 = 613169) B613169
theorem B408833 : Blo 179801 408833 := bstep (se 2 (by rfl) ⟨153312, by rfl⟩ : syracuseStep 408833 = 306625) B306625
theorem B343435 : Blo 179801 343435 := bstep (se 1 (by rfl) ⟨257576, by rfl⟩ : syracuseStep 343435 = 515153) B515153
theorem B671179 : Blo 179801 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B343511 : Blo 179801 343511 := bstep (se 1 (by rfl) ⟨257633, by rfl⟩ : syracuseStep 343511 = 515267) B515267
theorem B409049 : Blo 179801 409049 := bstep (se 2 (by rfl) ⟨153393, by rfl⟩ : syracuseStep 409049 = 306787) B306787
theorem B409139 : Blo 179801 409139 := bstep (se 1 (by rfl) ⟨306854, by rfl⟩ : syracuseStep 409139 = 613709) B613709
theorem B409175 : Blo 179801 409175 := bstep (se 1 (by rfl) ⟨306881, by rfl⟩ : syracuseStep 409175 = 613763) B613763
theorem B179819 : Blo 179801 179819 := bstep (se 1 (by rfl) ⟨134864, by rfl⟩ : syracuseStep 179819 = 269729) B269729
theorem B179831 : Blo 179801 179831 := bstep (se 1 (by rfl) ⟨134873, by rfl⟩ : syracuseStep 179831 = 269747) B269747
theorem B179851 : Blo 179801 179851 := bstep (se 1 (by rfl) ⟨134888, by rfl⟩ : syracuseStep 179851 = 269777) B269777
theorem B179863 : Blo 179801 179863 := bstep (se 1 (by rfl) ⟨134897, by rfl⟩ : syracuseStep 179863 = 269795) B269795
theorem B179883 : Blo 179801 179883 := bstep (se 1 (by rfl) ⟨134912, by rfl⟩ : syracuseStep 179883 = 269825) B269825
theorem B179895 : Blo 179801 179895 := bstep (se 1 (by rfl) ⟨134921, by rfl⟩ : syracuseStep 179895 = 269843) B269843
theorem B179915 : Blo 179801 179915 := bstep (se 1 (by rfl) ⟨134936, by rfl⟩ : syracuseStep 179915 = 269873) B269873
theorem B179927 : Blo 179801 179927 := bstep (se 1 (by rfl) ⟨134945, by rfl⟩ : syracuseStep 179927 = 269891) B269891
theorem B179947 : Blo 179801 179947 := bstep (se 1 (by rfl) ⟨134960, by rfl⟩ : syracuseStep 179947 = 269921) B269921
theorem B179959 : Blo 179801 179959 := bstep (se 1 (by rfl) ⟨134969, by rfl⟩ : syracuseStep 179959 = 269939) B269939
theorem B1392389 : Blo 179801 1392389 := bstep (se 4 (by rfl) ⟨130536, by rfl⟩ : syracuseStep 1392389 = 261073) B261073
theorem B179979 : Blo 179801 179979 := bstep (se 1 (by rfl) ⟨134984, by rfl⟩ : syracuseStep 179979 = 269969) B269969
theorem B409355 : Blo 179801 409355 := bstep (se 1 (by rfl) ⟨307016, by rfl⟩ : syracuseStep 409355 = 614033) B614033
theorem B179991 : Blo 179801 179991 := bstep (se 1 (by rfl) ⟨134993, by rfl⟩ : syracuseStep 179991 = 269987) B269987
theorem B180011 : Blo 179801 180011 := bstep (se 1 (by rfl) ⟨135008, by rfl⟩ : syracuseStep 180011 = 270017) B270017
theorem B180023 : Blo 179801 180023 := bstep (se 1 (by rfl) ⟨135017, by rfl⟩ : syracuseStep 180023 = 270035) B270035
theorem B409409 : Blo 179801 409409 := bstep (se 2 (by rfl) ⟨153528, by rfl⟩ : syracuseStep 409409 = 307057) B307057
theorem B180043 : Blo 179801 180043 := bstep (se 1 (by rfl) ⟨135032, by rfl⟩ : syracuseStep 180043 = 270065) B270065
theorem B180055 : Blo 179801 180055 := bstep (se 1 (by rfl) ⟨135041, by rfl⟩ : syracuseStep 180055 = 270083) B270083
theorem B180075 : Blo 179801 180075 := bstep (se 1 (by rfl) ⟨135056, by rfl⟩ : syracuseStep 180075 = 270113) B270113
theorem B180087 : Blo 179801 180087 := bstep (se 1 (by rfl) ⟨135065, by rfl⟩ : syracuseStep 180087 = 270131) B270131
theorem B180107 : Blo 179801 180107 := bstep (se 1 (by rfl) ⟨135080, by rfl⟩ : syracuseStep 180107 = 270161) B270161
theorem B180119 : Blo 179801 180119 := bstep (se 1 (by rfl) ⟨135089, by rfl⟩ : syracuseStep 180119 = 270179) B270179
theorem B180139 : Blo 179801 180139 := bstep (se 1 (by rfl) ⟨135104, by rfl⟩ : syracuseStep 180139 = 270209) B270209
theorem B180151 : Blo 179801 180151 := bstep (se 1 (by rfl) ⟨135113, by rfl⟩ : syracuseStep 180151 = 270227) B270227
theorem B180171 : Blo 179801 180171 := bstep (se 1 (by rfl) ⟨135128, by rfl⟩ : syracuseStep 180171 = 270257) B270257
theorem B180183 : Blo 179801 180183 := bstep (se 1 (by rfl) ⟨135137, by rfl⟩ : syracuseStep 180183 = 270275) B270275
theorem B180203 : Blo 179801 180203 := bstep (se 1 (by rfl) ⟨135152, by rfl⟩ : syracuseStep 180203 = 270305) B270305
theorem B180215 : Blo 179801 180215 := bstep (se 1 (by rfl) ⟨135161, by rfl⟩ : syracuseStep 180215 = 270323) B270323
theorem B180235 : Blo 179801 180235 := bstep (se 1 (by rfl) ⟨135176, by rfl⟩ : syracuseStep 180235 = 270353) B270353
theorem B180247 : Blo 179801 180247 := bstep (se 1 (by rfl) ⟨135185, by rfl⟩ : syracuseStep 180247 = 270371) B270371
theorem B409625 : Blo 179801 409625 := bstep (se 2 (by rfl) ⟨153609, by rfl⟩ : syracuseStep 409625 = 307219) B307219
theorem B180267 : Blo 179801 180267 := bstep (se 1 (by rfl) ⟨135200, by rfl⟩ : syracuseStep 180267 = 270401) B270401
theorem B180279 : Blo 179801 180279 := bstep (se 1 (by rfl) ⟨135209, by rfl⟩ : syracuseStep 180279 = 270419) B270419
theorem B180299 : Blo 179801 180299 := bstep (se 1 (by rfl) ⟨135224, by rfl⟩ : syracuseStep 180299 = 270449) B270449
theorem B180311 : Blo 179801 180311 := bstep (se 1 (by rfl) ⟨135233, by rfl⟩ : syracuseStep 180311 = 270467) B270467
theorem B1589341 : Blo 179801 1589341 := bstep (se 3 (by rfl) ⟨298001, by rfl⟩ : syracuseStep 1589341 = 596003) B596003
theorem B180331 : Blo 179801 180331 := bstep (se 1 (by rfl) ⟨135248, by rfl⟩ : syracuseStep 180331 = 270497) B270497
theorem B344179 : Blo 179801 344179 := bstep (se 1 (by rfl) ⟨258134, by rfl⟩ : syracuseStep 344179 = 516269) B516269
theorem B409715 : Blo 179801 409715 := bstep (se 1 (by rfl) ⟨307286, by rfl⟩ : syracuseStep 409715 = 614573) B614573
theorem B180343 : Blo 179801 180343 := bstep (se 1 (by rfl) ⟨135257, by rfl⟩ : syracuseStep 180343 = 270515) B270515
theorem B180363 : Blo 179801 180363 := bstep (se 1 (by rfl) ⟨135272, by rfl⟩ : syracuseStep 180363 = 270545) B270545
theorem B180375 : Blo 179801 180375 := bstep (se 1 (by rfl) ⟨135281, by rfl⟩ : syracuseStep 180375 = 270563) B270563
theorem B409751 : Blo 179801 409751 := bstep (se 1 (by rfl) ⟨307313, by rfl⟩ : syracuseStep 409751 = 614627) B614627
theorem B180395 : Blo 179801 180395 := bstep (se 1 (by rfl) ⟨135296, by rfl⟩ : syracuseStep 180395 = 270593) B270593
theorem B180407 : Blo 179801 180407 := bstep (se 1 (by rfl) ⟨135305, by rfl⟩ : syracuseStep 180407 = 270611) B270611
theorem B180427 : Blo 179801 180427 := bstep (se 1 (by rfl) ⟨135320, by rfl⟩ : syracuseStep 180427 = 270641) B270641
theorem B180439 : Blo 179801 180439 := bstep (se 1 (by rfl) ⟨135329, by rfl⟩ : syracuseStep 180439 = 270659) B270659
theorem B770269 : Blo 179801 770269 := bstep (se 3 (by rfl) ⟨144425, by rfl⟩ : syracuseStep 770269 = 288851) B288851
theorem B180459 : Blo 179801 180459 := bstep (se 1 (by rfl) ⟨135344, by rfl⟩ : syracuseStep 180459 = 270689) B270689
theorem B180471 : Blo 179801 180471 := bstep (se 1 (by rfl) ⟨135353, by rfl⟩ : syracuseStep 180471 = 270707) B270707
theorem B180491 : Blo 179801 180491 := bstep (se 1 (by rfl) ⟨135368, by rfl⟩ : syracuseStep 180491 = 270737) B270737
theorem B180503 : Blo 179801 180503 := bstep (se 1 (by rfl) ⟨135377, by rfl⟩ : syracuseStep 180503 = 270755) B270755
theorem B180523 : Blo 179801 180523 := bstep (se 1 (by rfl) ⟨135392, by rfl⟩ : syracuseStep 180523 = 270785) B270785
theorem B180535 : Blo 179801 180535 := bstep (se 1 (by rfl) ⟨135401, by rfl⟩ : syracuseStep 180535 = 270803) B270803
theorem B180555 : Blo 179801 180555 := bstep (se 1 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 180555 = 270833) B270833
theorem B409931 : Blo 179801 409931 := bstep (se 1 (by rfl) ⟨307448, by rfl⟩ : syracuseStep 409931 = 614897) B614897
theorem B180567 : Blo 179801 180567 := bstep (se 1 (by rfl) ⟨135425, by rfl⟩ : syracuseStep 180567 = 270851) B270851
theorem B344407 : Blo 179801 344407 := bstep (se 1 (by rfl) ⟨258305, by rfl⟩ : syracuseStep 344407 = 516611) B516611
theorem B180587 : Blo 179801 180587 := bstep (se 1 (by rfl) ⟨135440, by rfl⟩ : syracuseStep 180587 = 270881) B270881
theorem B180599 : Blo 179801 180599 := bstep (se 1 (by rfl) ⟨135449, by rfl⟩ : syracuseStep 180599 = 270899) B270899
theorem B409985 : Blo 179801 409985 := bstep (se 2 (by rfl) ⟨153744, by rfl⟩ : syracuseStep 409985 = 307489) B307489
theorem B180619 : Blo 179801 180619 := bstep (se 1 (by rfl) ⟨135464, by rfl⟩ : syracuseStep 180619 = 270929) B270929
theorem B180631 : Blo 179801 180631 := bstep (se 1 (by rfl) ⟨135473, by rfl⟩ : syracuseStep 180631 = 270947) B270947
theorem B180651 : Blo 179801 180651 := bstep (se 1 (by rfl) ⟨135488, by rfl⟩ : syracuseStep 180651 = 270977) B270977
theorem B1458611 : Blo 179801 1458611 := bstep (se 1 (by rfl) ⟨1093958, by rfl⟩ : syracuseStep 1458611 = 2187917) B2187917
theorem B180663 : Blo 179801 180663 := bstep (se 1 (by rfl) ⟨135497, by rfl⟩ : syracuseStep 180663 = 270995) B270995
theorem B344513 : Blo 179801 344513 := bstep (se 2 (by rfl) ⟨129192, by rfl⟩ : syracuseStep 344513 = 258385) B258385
theorem B180683 : Blo 179801 180683 := bstep (se 1 (by rfl) ⟨135512, by rfl⟩ : syracuseStep 180683 = 271025) B271025
theorem B180695 : Blo 179801 180695 := bstep (se 1 (by rfl) ⟨135521, by rfl⟩ : syracuseStep 180695 = 271043) B271043
theorem B180715 : Blo 179801 180715 := bstep (se 1 (by rfl) ⟨135536, by rfl⟩ : syracuseStep 180715 = 271073) B271073
theorem B180727 : Blo 179801 180727 := bstep (se 1 (by rfl) ⟨135545, by rfl⟩ : syracuseStep 180727 = 271091) B271091
theorem B180747 : Blo 179801 180747 := bstep (se 1 (by rfl) ⟨135560, by rfl⟩ : syracuseStep 180747 = 271121) B271121
theorem B180759 : Blo 179801 180759 := bstep (se 1 (by rfl) ⟨135569, by rfl⟩ : syracuseStep 180759 = 271139) B271139
theorem B180779 : Blo 179801 180779 := bstep (se 1 (by rfl) ⟨135584, by rfl⟩ : syracuseStep 180779 = 271169) B271169
theorem B180791 : Blo 179801 180791 := bstep (se 1 (by rfl) ⟨135593, by rfl⟩ : syracuseStep 180791 = 271187) B271187
theorem B180811 : Blo 179801 180811 := bstep (se 1 (by rfl) ⟨135608, by rfl⟩ : syracuseStep 180811 = 271217) B271217
theorem B1327691 : Blo 179801 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B180823 : Blo 179801 180823 := bstep (se 1 (by rfl) ⟨135617, by rfl⟩ : syracuseStep 180823 = 271235) B271235
theorem B344665 : Blo 179801 344665 := bstep (se 2 (by rfl) ⟨129249, by rfl⟩ : syracuseStep 344665 = 258499) B258499
theorem B410201 : Blo 179801 410201 := bstep (se 2 (by rfl) ⟨153825, by rfl⟩ : syracuseStep 410201 = 307651) B307651
theorem B180843 : Blo 179801 180843 := bstep (se 1 (by rfl) ⟨135632, by rfl⟩ : syracuseStep 180843 = 271265) B271265
theorem B180855 : Blo 179801 180855 := bstep (se 1 (by rfl) ⟨135641, by rfl⟩ : syracuseStep 180855 = 271283) B271283
theorem B180875 : Blo 179801 180875 := bstep (se 1 (by rfl) ⟨135656, by rfl⟩ : syracuseStep 180875 = 271313) B271313
theorem B180887 : Blo 179801 180887 := bstep (se 1 (by rfl) ⟨135665, by rfl⟩ : syracuseStep 180887 = 271331) B271331
theorem B180907 : Blo 179801 180907 := bstep (se 1 (by rfl) ⟨135680, by rfl⟩ : syracuseStep 180907 = 271361) B271361
theorem B410291 : Blo 179801 410291 := bstep (se 1 (by rfl) ⟨307718, by rfl⟩ : syracuseStep 410291 = 615437) B615437
theorem B705203 : Blo 179801 705203 := bstep (se 1 (by rfl) ⟨528902, by rfl⟩ : syracuseStep 705203 = 1057805) B1057805
theorem B180919 : Blo 179801 180919 := bstep (se 1 (by rfl) ⟨135689, by rfl⟩ : syracuseStep 180919 = 271379) B271379
theorem B180939 : Blo 179801 180939 := bstep (se 1 (by rfl) ⟨135704, by rfl⟩ : syracuseStep 180939 = 271409) B271409
theorem B180951 : Blo 179801 180951 := bstep (se 1 (by rfl) ⟨135713, by rfl⟩ : syracuseStep 180951 = 271427) B271427
theorem B410327 : Blo 179801 410327 := bstep (se 1 (by rfl) ⟨307745, by rfl⟩ : syracuseStep 410327 = 615491) B615491
theorem B180971 : Blo 179801 180971 := bstep (se 1 (by rfl) ⟨135728, by rfl⟩ : syracuseStep 180971 = 271457) B271457
theorem B180983 : Blo 179801 180983 := bstep (se 1 (by rfl) ⟨135737, by rfl⟩ : syracuseStep 180983 = 271475) B271475
theorem B181003 : Blo 179801 181003 := bstep (se 1 (by rfl) ⟨135752, by rfl⟩ : syracuseStep 181003 = 271505) B271505
theorem B181015 : Blo 179801 181015 := bstep (se 1 (by rfl) ⟨135761, by rfl⟩ : syracuseStep 181015 = 271523) B271523
theorem B181035 : Blo 179801 181035 := bstep (se 1 (by rfl) ⟨135776, by rfl⟩ : syracuseStep 181035 = 271553) B271553
theorem B181047 : Blo 179801 181047 := bstep (se 1 (by rfl) ⟨135785, by rfl⟩ : syracuseStep 181047 = 271571) B271571
theorem B181067 : Blo 179801 181067 := bstep (se 1 (by rfl) ⟨135800, by rfl⟩ : syracuseStep 181067 = 271601) B271601
theorem B181079 : Blo 179801 181079 := bstep (se 1 (by rfl) ⟨135809, by rfl⟩ : syracuseStep 181079 = 271619) B271619
theorem B181099 : Blo 179801 181099 := bstep (se 1 (by rfl) ⟨135824, by rfl⟩ : syracuseStep 181099 = 271649) B271649
theorem B181111 : Blo 179801 181111 := bstep (se 1 (by rfl) ⟨135833, by rfl⟩ : syracuseStep 181111 = 271667) B271667
theorem B181131 : Blo 179801 181131 := bstep (se 1 (by rfl) ⟨135848, by rfl⟩ : syracuseStep 181131 = 271697) B271697
theorem B410507 : Blo 179801 410507 := bstep (se 1 (by rfl) ⟨307880, by rfl⟩ : syracuseStep 410507 = 615761) B615761
theorem B181143 : Blo 179801 181143 := bstep (se 1 (by rfl) ⟨135857, by rfl⟩ : syracuseStep 181143 = 271715) B271715
theorem B181163 : Blo 179801 181163 := bstep (se 1 (by rfl) ⟨135872, by rfl⟩ : syracuseStep 181163 = 271745) B271745
theorem B181175 : Blo 179801 181175 := bstep (se 1 (by rfl) ⟨135881, by rfl⟩ : syracuseStep 181175 = 271763) B271763
theorem B410561 : Blo 179801 410561 := bstep (se 2 (by rfl) ⟨153960, by rfl⟩ : syracuseStep 410561 = 307921) B307921
theorem B181195 : Blo 179801 181195 := bstep (se 1 (by rfl) ⟨135896, by rfl⟩ : syracuseStep 181195 = 271793) B271793
theorem B181207 : Blo 179801 181207 := bstep (se 1 (by rfl) ⟨135905, by rfl⟩ : syracuseStep 181207 = 271811) B271811
theorem B181227 : Blo 179801 181227 := bstep (se 1 (by rfl) ⟨135920, by rfl⟩ : syracuseStep 181227 = 271841) B271841
theorem B181239 : Blo 179801 181239 := bstep (se 1 (by rfl) ⟨135929, by rfl⟩ : syracuseStep 181239 = 271859) B271859
theorem B181259 : Blo 179801 181259 := bstep (se 1 (by rfl) ⟨135944, by rfl⟩ : syracuseStep 181259 = 271889) B271889
theorem B181271 : Blo 179801 181271 := bstep (se 1 (by rfl) ⟨135953, by rfl⟩ : syracuseStep 181271 = 271907) B271907
theorem B181291 : Blo 179801 181291 := bstep (se 1 (by rfl) ⟨135968, by rfl⟩ : syracuseStep 181291 = 271937) B271937
theorem B607283 : Blo 179801 607283 := bstep (se 1 (by rfl) ⟨455462, by rfl⟩ : syracuseStep 607283 = 910925) B910925
theorem B181303 : Blo 179801 181303 := bstep (se 1 (by rfl) ⟨135977, by rfl⟩ : syracuseStep 181303 = 271955) B271955
theorem B181323 : Blo 179801 181323 := bstep (se 1 (by rfl) ⟨135992, by rfl⟩ : syracuseStep 181323 = 271985) B271985
theorem B181335 : Blo 179801 181335 := bstep (se 1 (by rfl) ⟨136001, by rfl⟩ : syracuseStep 181335 = 272003) B272003
theorem B181355 : Blo 179801 181355 := bstep (se 1 (by rfl) ⟨136016, by rfl⟩ : syracuseStep 181355 = 272033) B272033
theorem B181367 : Blo 179801 181367 := bstep (se 1 (by rfl) ⟨136025, by rfl⟩ : syracuseStep 181367 = 272051) B272051
theorem B181387 : Blo 179801 181387 := bstep (se 1 (by rfl) ⟨136040, by rfl⟩ : syracuseStep 181387 = 272081) B272081
theorem B181399 : Blo 179801 181399 := bstep (se 1 (by rfl) ⟨136049, by rfl⟩ : syracuseStep 181399 = 272099) B272099
theorem B410777 : Blo 179801 410777 := bstep (se 2 (by rfl) ⟨154041, by rfl⟩ : syracuseStep 410777 = 308083) B308083
theorem B181419 : Blo 179801 181419 := bstep (se 1 (by rfl) ⟨136064, by rfl⟩ : syracuseStep 181419 = 272129) B272129
theorem B181431 : Blo 179801 181431 := bstep (se 1 (by rfl) ⟨136073, by rfl⟩ : syracuseStep 181431 = 272147) B272147
theorem B181451 : Blo 179801 181451 := bstep (se 1 (by rfl) ⟨136088, by rfl⟩ : syracuseStep 181451 = 272177) B272177
theorem B181463 : Blo 179801 181463 := bstep (se 1 (by rfl) ⟨136097, by rfl⟩ : syracuseStep 181463 = 272195) B272195
theorem B181483 : Blo 179801 181483 := bstep (se 1 (by rfl) ⟨136112, by rfl⟩ : syracuseStep 181483 = 272225) B272225
theorem B410867 : Blo 179801 410867 := bstep (se 1 (by rfl) ⟨308150, by rfl⟩ : syracuseStep 410867 = 616301) B616301
theorem B181495 : Blo 179801 181495 := bstep (se 1 (by rfl) ⟨136121, by rfl⟩ : syracuseStep 181495 = 272243) B272243
theorem B181515 : Blo 179801 181515 := bstep (se 1 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 181515 = 272273) B272273
theorem B705809 : Blo 179801 705809 := bstep (se 2 (by rfl) ⟨264678, by rfl⟩ : syracuseStep 705809 = 529357) B529357
theorem B181527 : Blo 179801 181527 := bstep (se 1 (by rfl) ⟨136145, by rfl⟩ : syracuseStep 181527 = 272291) B272291
theorem B410903 : Blo 179801 410903 := bstep (se 1 (by rfl) ⟨308177, by rfl⟩ : syracuseStep 410903 = 616355) B616355
theorem B181547 : Blo 179801 181547 := bstep (se 1 (by rfl) ⟨136160, by rfl⟩ : syracuseStep 181547 = 272321) B272321
theorem B1361197 : Blo 179801 1361197 := bstep (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) B510449
theorem B181559 : Blo 179801 181559 := bstep (se 1 (by rfl) ⟨136169, by rfl⟩ : syracuseStep 181559 = 272339) B272339
theorem B607553 : Blo 179801 607553 := bstep (se 2 (by rfl) ⟨227832, by rfl⟩ : syracuseStep 607553 = 455665) B455665
theorem B181579 : Blo 179801 181579 := bstep (se 1 (by rfl) ⟨136184, by rfl⟩ : syracuseStep 181579 = 272369) B272369
theorem B181591 : Blo 179801 181591 := bstep (se 1 (by rfl) ⟨136193, by rfl⟩ : syracuseStep 181591 = 272387) B272387
theorem B181611 : Blo 179801 181611 := bstep (se 1 (by rfl) ⟨136208, by rfl⟩ : syracuseStep 181611 = 272417) B272417
theorem B181623 : Blo 179801 181623 := bstep (se 1 (by rfl) ⟨136217, by rfl⟩ : syracuseStep 181623 = 272435) B272435
theorem B181643 : Blo 179801 181643 := bstep (se 1 (by rfl) ⟨136232, by rfl⟩ : syracuseStep 181643 = 272465) B272465
theorem B411031 : Blo 179801 411031 := bstep (se 1 (by rfl) ⟨308273, by rfl⟩ : syracuseStep 411031 = 616547) B616547
theorem B181655 : Blo 179801 181655 := bstep (se 1 (by rfl) ⟨136241, by rfl⟩ : syracuseStep 181655 = 272483) B272483
theorem B181675 : Blo 179801 181675 := bstep (se 1 (by rfl) ⟨136256, by rfl⟩ : syracuseStep 181675 = 272513) B272513
theorem B181687 : Blo 179801 181687 := bstep (se 1 (by rfl) ⟨136265, by rfl⟩ : syracuseStep 181687 = 272531) B272531
theorem B181707 : Blo 179801 181707 := bstep (se 1 (by rfl) ⟨136280, by rfl⟩ : syracuseStep 181707 = 272561) B272561
theorem B411083 : Blo 179801 411083 := bstep (se 1 (by rfl) ⟨308312, by rfl⟩ : syracuseStep 411083 = 616625) B616625
theorem B181719 : Blo 179801 181719 := bstep (se 1 (by rfl) ⟨136289, by rfl⟩ : syracuseStep 181719 = 272579) B272579
theorem B181739 : Blo 179801 181739 := bstep (se 1 (by rfl) ⟨136304, by rfl⟩ : syracuseStep 181739 = 272609) B272609
theorem B181751 : Blo 179801 181751 := bstep (se 1 (by rfl) ⟨136313, by rfl⟩ : syracuseStep 181751 = 272627) B272627
theorem B411137 : Blo 179801 411137 := bstep (se 2 (by rfl) ⟨154176, by rfl⟩ : syracuseStep 411137 = 308353) B308353
theorem B706051 : Blo 179801 706051 := bstep (se 1 (by rfl) ⟨529538, by rfl⟩ : syracuseStep 706051 = 1059077) B1059077
theorem B181771 : Blo 179801 181771 := bstep (se 1 (by rfl) ⟨136328, by rfl⟩ : syracuseStep 181771 = 272657) B272657
theorem B771601 : Blo 179801 771601 := bstep (se 2 (by rfl) ⟨289350, by rfl⟩ : syracuseStep 771601 = 578701) B578701
theorem B181783 : Blo 179801 181783 := bstep (se 1 (by rfl) ⟨136337, by rfl⟩ : syracuseStep 181783 = 272675) B272675
theorem B181803 : Blo 179801 181803 := bstep (se 1 (by rfl) ⟨136352, by rfl⟩ : syracuseStep 181803 = 272705) B272705
theorem B181815 : Blo 179801 181815 := bstep (se 1 (by rfl) ⟨136361, by rfl⟩ : syracuseStep 181815 = 272723) B272723
theorem B181835 : Blo 179801 181835 := bstep (se 1 (by rfl) ⟨136376, by rfl⟩ : syracuseStep 181835 = 272753) B272753
theorem B181847 : Blo 179801 181847 := bstep (se 1 (by rfl) ⟨136385, by rfl⟩ : syracuseStep 181847 = 272771) B272771
theorem B181867 : Blo 179801 181867 := bstep (se 1 (by rfl) ⟨136400, by rfl⟩ : syracuseStep 181867 = 272801) B272801
theorem B181879 : Blo 179801 181879 := bstep (se 1 (by rfl) ⟨136409, by rfl⟩ : syracuseStep 181879 = 272819) B272819
theorem B181899 : Blo 179801 181899 := bstep (se 1 (by rfl) ⟨136424, by rfl⟩ : syracuseStep 181899 = 272849) B272849
theorem B1328791 : Blo 179801 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B181911 : Blo 179801 181911 := bstep (se 1 (by rfl) ⟨136433, by rfl⟩ : syracuseStep 181911 = 272867) B272867
theorem B181931 : Blo 179801 181931 := bstep (se 1 (by rfl) ⟨136448, by rfl⟩ : syracuseStep 181931 = 272897) B272897
theorem B181943 : Blo 179801 181943 := bstep (se 1 (by rfl) ⟨136457, by rfl⟩ : syracuseStep 181943 = 272915) B272915
theorem B181963 : Blo 179801 181963 := bstep (se 1 (by rfl) ⟨136472, by rfl⟩ : syracuseStep 181963 = 272945) B272945
theorem B4933325 : Blo 179801 4933325 := bstep (se 3 (by rfl) ⟨924998, by rfl⟩ : syracuseStep 4933325 = 1849997) B1849997
theorem B181975 : Blo 179801 181975 := bstep (se 1 (by rfl) ⟨136481, by rfl⟩ : syracuseStep 181975 = 272963) B272963
theorem B411353 : Blo 179801 411353 := bstep (se 2 (by rfl) ⟨154257, by rfl⟩ : syracuseStep 411353 = 308515) B308515
theorem B181995 : Blo 179801 181995 := bstep (se 1 (by rfl) ⟨136496, by rfl⟩ : syracuseStep 181995 = 272993) B272993
theorem B182007 : Blo 179801 182007 := bstep (se 1 (by rfl) ⟨136505, by rfl⟩ : syracuseStep 182007 = 273011) B273011
theorem B182027 : Blo 179801 182027 := bstep (se 1 (by rfl) ⟨136520, by rfl⟩ : syracuseStep 182027 = 273041) B273041
theorem B182039 : Blo 179801 182039 := bstep (se 1 (by rfl) ⟨136529, by rfl⟩ : syracuseStep 182039 = 273059) B273059
theorem B182059 : Blo 179801 182059 := bstep (se 1 (by rfl) ⟨136544, by rfl⟩ : syracuseStep 182059 = 273089) B273089
theorem B411443 : Blo 179801 411443 := bstep (se 1 (by rfl) ⟨308582, by rfl⟩ : syracuseStep 411443 = 617165) B617165
theorem B182071 : Blo 179801 182071 := bstep (se 1 (by rfl) ⟨136553, by rfl⟩ : syracuseStep 182071 = 273107) B273107
theorem B1754945 : Blo 179801 1754945 := bstep (se 2 (by rfl) ⟨658104, by rfl⟩ : syracuseStep 1754945 = 1316209) B1316209
theorem B182091 : Blo 179801 182091 := bstep (se 1 (by rfl) ⟨136568, by rfl⟩ : syracuseStep 182091 = 273137) B273137
theorem B182103 : Blo 179801 182103 := bstep (se 1 (by rfl) ⟨136577, by rfl⟩ : syracuseStep 182103 = 273155) B273155
theorem B411479 : Blo 179801 411479 := bstep (se 1 (by rfl) ⟨308609, by rfl⟩ : syracuseStep 411479 = 617219) B617219
theorem B608093 : Blo 179801 608093 := bstep (se 3 (by rfl) ⟨114017, by rfl⟩ : syracuseStep 608093 = 228035) B228035
theorem B182123 : Blo 179801 182123 := bstep (se 1 (by rfl) ⟨136592, by rfl⟩ : syracuseStep 182123 = 273185) B273185
theorem B345971 : Blo 179801 345971 := bstep (se 1 (by rfl) ⟨259478, by rfl⟩ : syracuseStep 345971 = 518957) B518957
theorem B182135 : Blo 179801 182135 := bstep (se 1 (by rfl) ⟨136601, by rfl⟩ : syracuseStep 182135 = 273203) B273203
theorem B182155 : Blo 179801 182155 := bstep (se 1 (by rfl) ⟨136616, by rfl⟩ : syracuseStep 182155 = 273233) B273233
theorem B182167 : Blo 179801 182167 := bstep (se 1 (by rfl) ⟨136625, by rfl⟩ : syracuseStep 182167 = 273251) B273251
theorem B182187 : Blo 179801 182187 := bstep (se 1 (by rfl) ⟨136640, by rfl⟩ : syracuseStep 182187 = 273281) B273281
theorem B182199 : Blo 179801 182199 := bstep (se 1 (by rfl) ⟨136649, by rfl⟩ : syracuseStep 182199 = 273299) B273299
theorem B182219 : Blo 179801 182219 := bstep (se 1 (by rfl) ⟨136664, by rfl⟩ : syracuseStep 182219 = 273329) B273329
theorem B182231 : Blo 179801 182231 := bstep (se 1 (by rfl) ⟨136673, by rfl⟩ : syracuseStep 182231 = 273347) B273347
theorem B182251 : Blo 179801 182251 := bstep (se 1 (by rfl) ⟨136688, by rfl⟩ : syracuseStep 182251 = 273377) B273377
theorem B182263 : Blo 179801 182263 := bstep (se 1 (by rfl) ⟨136697, by rfl⟩ : syracuseStep 182263 = 273395) B273395
theorem B182283 : Blo 179801 182283 := bstep (se 1 (by rfl) ⟨136712, by rfl⟩ : syracuseStep 182283 = 273425) B273425
theorem B346123 : Blo 179801 346123 := bstep (se 1 (by rfl) ⟨259592, by rfl⟩ : syracuseStep 346123 = 519185) B519185
theorem B411659 : Blo 179801 411659 := bstep (se 1 (by rfl) ⟨308744, by rfl⟩ : syracuseStep 411659 = 617489) B617489
theorem B182295 : Blo 179801 182295 := bstep (se 1 (by rfl) ⟨136721, by rfl⟩ : syracuseStep 182295 = 273443) B273443
theorem B182315 : Blo 179801 182315 := bstep (se 1 (by rfl) ⟨136736, by rfl⟩ : syracuseStep 182315 = 273473) B273473
theorem B182327 : Blo 179801 182327 := bstep (se 1 (by rfl) ⟨136745, by rfl⟩ : syracuseStep 182327 = 273491) B273491
theorem B411713 : Blo 179801 411713 := bstep (se 2 (by rfl) ⟨154392, by rfl⟩ : syracuseStep 411713 = 308785) B308785
theorem B1034315 : Blo 179801 1034315 := bstep (se 1 (by rfl) ⟨775736, by rfl⟩ : syracuseStep 1034315 = 1551473) B1551473
theorem B182347 : Blo 179801 182347 := bstep (se 1 (by rfl) ⟨136760, by rfl⟩ : syracuseStep 182347 = 273521) B273521
theorem B182359 : Blo 179801 182359 := bstep (se 1 (by rfl) ⟨136769, by rfl⟩ : syracuseStep 182359 = 273539) B273539
theorem B182379 : Blo 179801 182379 := bstep (se 1 (by rfl) ⟨136784, by rfl⟩ : syracuseStep 182379 = 273569) B273569
theorem B182391 : Blo 179801 182391 := bstep (se 1 (by rfl) ⟨136793, by rfl⟩ : syracuseStep 182391 = 273587) B273587
theorem B739459 : Blo 179801 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B1394819 : Blo 179801 1394819 := bstep (se 1 (by rfl) ⟨1046114, by rfl⟩ : syracuseStep 1394819 = 2092229) B2092229
theorem B182411 : Blo 179801 182411 := bstep (se 1 (by rfl) ⟨136808, by rfl⟩ : syracuseStep 182411 = 273617) B273617
theorem B182423 : Blo 179801 182423 := bstep (se 1 (by rfl) ⟨136817, by rfl⟩ : syracuseStep 182423 = 273635) B273635
theorem B182443 : Blo 179801 182443 := bstep (se 1 (by rfl) ⟨136832, by rfl⟩ : syracuseStep 182443 = 273665) B273665
theorem B182455 : Blo 179801 182455 := bstep (se 1 (by rfl) ⟨136841, by rfl⟩ : syracuseStep 182455 = 273683) B273683
theorem B182475 : Blo 179801 182475 := bstep (se 1 (by rfl) ⟨136856, by rfl⟩ : syracuseStep 182475 = 273713) B273713
theorem B1460429 : Blo 179801 1460429 := bstep (se 3 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 1460429 = 547661) B547661
theorem B182487 : Blo 179801 182487 := bstep (se 1 (by rfl) ⟨136865, by rfl⟩ : syracuseStep 182487 = 273731) B273731
theorem B182507 : Blo 179801 182507 := bstep (se 1 (by rfl) ⟨136880, by rfl⟩ : syracuseStep 182507 = 273761) B273761
theorem B182519 : Blo 179801 182519 := bstep (se 1 (by rfl) ⟨136889, by rfl⟩ : syracuseStep 182519 = 273779) B273779
theorem B182539 : Blo 179801 182539 := bstep (se 1 (by rfl) ⟨136904, by rfl⟩ : syracuseStep 182539 = 273809) B273809
theorem B182551 : Blo 179801 182551 := bstep (se 1 (by rfl) ⟨136913, by rfl⟩ : syracuseStep 182551 = 273827) B273827
theorem B411929 : Blo 179801 411929 := bstep (se 2 (by rfl) ⟨154473, by rfl⟩ : syracuseStep 411929 = 308947) B308947
theorem B182571 : Blo 179801 182571 := bstep (se 1 (by rfl) ⟨136928, by rfl⟩ : syracuseStep 182571 = 273857) B273857
theorem B182583 : Blo 179801 182583 := bstep (se 1 (by rfl) ⟨136937, by rfl⟩ : syracuseStep 182583 = 273875) B273875
theorem B182603 : Blo 179801 182603 := bstep (se 1 (by rfl) ⟨136952, by rfl⟩ : syracuseStep 182603 = 273905) B273905
theorem B182615 : Blo 179801 182615 := bstep (se 1 (by rfl) ⟨136961, by rfl⟩ : syracuseStep 182615 = 273923) B273923
theorem B346457 : Blo 179801 346457 := bstep (se 2 (by rfl) ⟨129921, by rfl⟩ : syracuseStep 346457 = 259843) B259843
theorem B2312549 : Blo 179801 2312549 := bstep (se 4 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 2312549 = 433603) B433603
theorem B182635 : Blo 179801 182635 := bstep (se 1 (by rfl) ⟨136976, by rfl⟩ : syracuseStep 182635 = 273953) B273953
theorem B412019 : Blo 179801 412019 := bstep (se 1 (by rfl) ⟨309014, by rfl⟩ : syracuseStep 412019 = 618029) B618029
theorem B182647 : Blo 179801 182647 := bstep (se 1 (by rfl) ⟨136985, by rfl⟩ : syracuseStep 182647 = 273971) B273971
theorem B182667 : Blo 179801 182667 := bstep (se 1 (by rfl) ⟨137000, by rfl⟩ : syracuseStep 182667 = 274001) B274001
theorem B182679 : Blo 179801 182679 := bstep (se 1 (by rfl) ⟨137009, by rfl⟩ : syracuseStep 182679 = 274019) B274019
theorem B412055 : Blo 179801 412055 := bstep (se 1 (by rfl) ⟨309041, by rfl⟩ : syracuseStep 412055 = 618083) B618083
theorem B182699 : Blo 179801 182699 := bstep (se 1 (by rfl) ⟨137024, by rfl⟩ : syracuseStep 182699 = 274049) B274049
theorem B182711 : Blo 179801 182711 := bstep (se 1 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 182711 = 274067) B274067
theorem B182731 : Blo 179801 182731 := bstep (se 1 (by rfl) ⟨137048, by rfl⟩ : syracuseStep 182731 = 274097) B274097
theorem B182743 : Blo 179801 182743 := bstep (se 1 (by rfl) ⟨137057, by rfl⟩ : syracuseStep 182743 = 274115) B274115
theorem B182763 : Blo 179801 182763 := bstep (se 1 (by rfl) ⟨137072, by rfl⟩ : syracuseStep 182763 = 274145) B274145
theorem B182775 : Blo 179801 182775 := bstep (se 1 (by rfl) ⟨137081, by rfl⟩ : syracuseStep 182775 = 274163) B274163
theorem B182795 : Blo 179801 182795 := bstep (se 1 (by rfl) ⟨137096, by rfl⟩ : syracuseStep 182795 = 274193) B274193
theorem B182807 : Blo 179801 182807 := bstep (se 1 (by rfl) ⟨137105, by rfl⟩ : syracuseStep 182807 = 274211) B274211
theorem B182827 : Blo 179801 182827 := bstep (se 1 (by rfl) ⟨137120, by rfl⟩ : syracuseStep 182827 = 274241) B274241
theorem B182839 : Blo 179801 182839 := bstep (se 1 (by rfl) ⟨137129, by rfl⟩ : syracuseStep 182839 = 274259) B274259
theorem B182859 : Blo 179801 182859 := bstep (se 1 (by rfl) ⟨137144, by rfl⟩ : syracuseStep 182859 = 274289) B274289
theorem B412235 : Blo 179801 412235 := bstep (se 1 (by rfl) ⟨309176, by rfl⟩ : syracuseStep 412235 = 618353) B618353
theorem B182871 : Blo 179801 182871 := bstep (se 1 (by rfl) ⟨137153, by rfl⟩ : syracuseStep 182871 = 274307) B274307
theorem B182891 : Blo 179801 182891 := bstep (se 1 (by rfl) ⟨137168, by rfl⟩ : syracuseStep 182891 = 274337) B274337
theorem B182903 : Blo 179801 182903 := bstep (se 1 (by rfl) ⟨137177, by rfl⟩ : syracuseStep 182903 = 274355) B274355
theorem B412289 : Blo 179801 412289 := bstep (se 2 (by rfl) ⟨154608, by rfl⟩ : syracuseStep 412289 = 309217) B309217
theorem B182923 : Blo 179801 182923 := bstep (se 1 (by rfl) ⟨137192, by rfl⟩ : syracuseStep 182923 = 274385) B274385
theorem B182935 : Blo 179801 182935 := bstep (se 1 (by rfl) ⟨137201, by rfl⟩ : syracuseStep 182935 = 274403) B274403
theorem B182955 : Blo 179801 182955 := bstep (se 1 (by rfl) ⟨137216, by rfl⟩ : syracuseStep 182955 = 274433) B274433
theorem B182967 : Blo 179801 182967 := bstep (se 1 (by rfl) ⟨137225, by rfl⟩ : syracuseStep 182967 = 274451) B274451
theorem B182987 : Blo 179801 182987 := bstep (se 1 (by rfl) ⟨137240, by rfl⟩ : syracuseStep 182987 = 274481) B274481
theorem B182999 : Blo 179801 182999 := bstep (se 1 (by rfl) ⟨137249, by rfl⟩ : syracuseStep 182999 = 274499) B274499
theorem B183019 : Blo 179801 183019 := bstep (se 1 (by rfl) ⟨137264, by rfl⟩ : syracuseStep 183019 = 274529) B274529
theorem B183031 : Blo 179801 183031 := bstep (se 1 (by rfl) ⟨137273, by rfl⟩ : syracuseStep 183031 = 274547) B274547
theorem B183051 : Blo 179801 183051 := bstep (se 1 (by rfl) ⟨137288, by rfl⟩ : syracuseStep 183051 = 274577) B274577
theorem B183063 : Blo 179801 183063 := bstep (se 1 (by rfl) ⟨137297, by rfl⟩ : syracuseStep 183063 = 274595) B274595
theorem B183083 : Blo 179801 183083 := bstep (se 1 (by rfl) ⟨137312, by rfl⟩ : syracuseStep 183083 = 274625) B274625
theorem B183095 : Blo 179801 183095 := bstep (se 1 (by rfl) ⟨137321, by rfl⟩ : syracuseStep 183095 = 274643) B274643
theorem B248651 : Blo 179801 248651 := bstep (se 1 (by rfl) ⟨186488, by rfl⟩ : syracuseStep 248651 = 372977) B372977
theorem B183115 : Blo 179801 183115 := bstep (se 1 (by rfl) ⟨137336, by rfl⟩ : syracuseStep 183115 = 274673) B274673
theorem B183127 : Blo 179801 183127 := bstep (se 1 (by rfl) ⟨137345, by rfl⟩ : syracuseStep 183127 = 274691) B274691
theorem B412505 : Blo 179801 412505 := bstep (se 2 (by rfl) ⟨154689, by rfl⟩ : syracuseStep 412505 = 309379) B309379
theorem B183147 : Blo 179801 183147 := bstep (se 1 (by rfl) ⟨137360, by rfl⟩ : syracuseStep 183147 = 274721) B274721
theorem B183159 : Blo 179801 183159 := bstep (se 1 (by rfl) ⟨137369, by rfl⟩ : syracuseStep 183159 = 274739) B274739
theorem B183179 : Blo 179801 183179 := bstep (se 1 (by rfl) ⟨137384, by rfl⟩ : syracuseStep 183179 = 274769) B274769
theorem B183191 : Blo 179801 183191 := bstep (se 1 (by rfl) ⟨137393, by rfl⟩ : syracuseStep 183191 = 274787) B274787
theorem B183211 : Blo 179801 183211 := bstep (se 1 (by rfl) ⟨137408, by rfl⟩ : syracuseStep 183211 = 274817) B274817
theorem B412595 : Blo 179801 412595 := bstep (se 1 (by rfl) ⟨309446, by rfl⟩ : syracuseStep 412595 = 618893) B618893
theorem B183223 : Blo 179801 183223 := bstep (se 1 (by rfl) ⟨137417, by rfl⟩ : syracuseStep 183223 = 274835) B274835
theorem B609227 : Blo 179801 609227 := bstep (se 1 (by rfl) ⟨456920, by rfl⟩ : syracuseStep 609227 = 913841) B913841
theorem B183243 : Blo 179801 183243 := bstep (se 1 (by rfl) ⟨137432, by rfl⟩ : syracuseStep 183243 = 274865) B274865
theorem B347095 : Blo 179801 347095 := bstep (se 1 (by rfl) ⟨260321, by rfl⟩ : syracuseStep 347095 = 520643) B520643
theorem B183255 : Blo 179801 183255 := bstep (se 1 (by rfl) ⟨137441, by rfl⟩ : syracuseStep 183255 = 274883) B274883
theorem B412631 : Blo 179801 412631 := bstep (se 1 (by rfl) ⟨309473, by rfl⟩ : syracuseStep 412631 = 618947) B618947
theorem B183275 : Blo 179801 183275 := bstep (se 1 (by rfl) ⟨137456, by rfl⟩ : syracuseStep 183275 = 274913) B274913
theorem B183287 : Blo 179801 183287 := bstep (se 1 (by rfl) ⟨137465, by rfl⟩ : syracuseStep 183287 = 274931) B274931
theorem B183307 : Blo 179801 183307 := bstep (se 1 (by rfl) ⟨137480, by rfl⟩ : syracuseStep 183307 = 274961) B274961
theorem B183319 : Blo 179801 183319 := bstep (se 1 (by rfl) ⟨137489, by rfl⟩ : syracuseStep 183319 = 274979) B274979
theorem B183339 : Blo 179801 183339 := bstep (se 1 (by rfl) ⟨137504, by rfl⟩ : syracuseStep 183339 = 275009) B275009
theorem B183351 : Blo 179801 183351 := bstep (se 1 (by rfl) ⟨137513, by rfl⟩ : syracuseStep 183351 = 275027) B275027
theorem B183371 : Blo 179801 183371 := bstep (se 1 (by rfl) ⟨137528, by rfl⟩ : syracuseStep 183371 = 275057) B275057
theorem B183383 : Blo 179801 183383 := bstep (se 1 (by rfl) ⟨137537, by rfl⟩ : syracuseStep 183383 = 275075) B275075
theorem B183403 : Blo 179801 183403 := bstep (se 1 (by rfl) ⟨137552, by rfl⟩ : syracuseStep 183403 = 275105) B275105
theorem B183415 : Blo 179801 183415 := bstep (se 1 (by rfl) ⟨137561, by rfl⟩ : syracuseStep 183415 = 275123) B275123
theorem B183435 : Blo 179801 183435 := bstep (se 1 (by rfl) ⟨137576, by rfl⟩ : syracuseStep 183435 = 275153) B275153
theorem B412811 : Blo 179801 412811 := bstep (se 1 (by rfl) ⟨309608, by rfl⟩ : syracuseStep 412811 = 619217) B619217
theorem B740497 : Blo 179801 740497 := bstep (se 2 (by rfl) ⟨277686, by rfl⟩ : syracuseStep 740497 = 555373) B555373
theorem B183447 : Blo 179801 183447 := bstep (se 1 (by rfl) ⟨137585, by rfl⟩ : syracuseStep 183447 = 275171) B275171
theorem B183467 : Blo 179801 183467 := bstep (se 1 (by rfl) ⟨137600, by rfl⟩ : syracuseStep 183467 = 275201) B275201
theorem B183479 : Blo 179801 183479 := bstep (se 1 (by rfl) ⟨137609, by rfl⟩ : syracuseStep 183479 = 275219) B275219
theorem B412865 : Blo 179801 412865 := bstep (se 2 (by rfl) ⟨154824, by rfl⟩ : syracuseStep 412865 = 309649) B309649
theorem B183499 : Blo 179801 183499 := bstep (se 1 (by rfl) ⟨137624, by rfl⟩ : syracuseStep 183499 = 275249) B275249
theorem B183511 : Blo 179801 183511 := bstep (se 1 (by rfl) ⟨137633, by rfl⟩ : syracuseStep 183511 = 275267) B275267
theorem B609497 : Blo 179801 609497 := bstep (se 2 (by rfl) ⟨228561, by rfl⟩ : syracuseStep 609497 = 457123) B457123
theorem B183531 : Blo 179801 183531 := bstep (se 1 (by rfl) ⟨137648, by rfl⟩ : syracuseStep 183531 = 275297) B275297
theorem B183543 : Blo 179801 183543 := bstep (se 1 (by rfl) ⟨137657, by rfl⟩ : syracuseStep 183543 = 275315) B275315
theorem B183563 : Blo 179801 183563 := bstep (se 1 (by rfl) ⟨137672, by rfl⟩ : syracuseStep 183563 = 275345) B275345
theorem B183575 : Blo 179801 183575 := bstep (se 1 (by rfl) ⟨137681, by rfl⟩ : syracuseStep 183575 = 275363) B275363
theorem B183595 : Blo 179801 183595 := bstep (se 1 (by rfl) ⟨137696, by rfl⟩ : syracuseStep 183595 = 275393) B275393
theorem B183607 : Blo 179801 183607 := bstep (se 1 (by rfl) ⟨137705, by rfl⟩ : syracuseStep 183607 = 275411) B275411
theorem B183627 : Blo 179801 183627 := bstep (se 1 (by rfl) ⟨137720, by rfl⟩ : syracuseStep 183627 = 275441) B275441
theorem B183639 : Blo 179801 183639 := bstep (se 1 (by rfl) ⟨137729, by rfl⟩ : syracuseStep 183639 = 275459) B275459
theorem B183659 : Blo 179801 183659 := bstep (se 1 (by rfl) ⟨137744, by rfl⟩ : syracuseStep 183659 = 275489) B275489
theorem B183671 : Blo 179801 183671 := bstep (se 1 (by rfl) ⟨137753, by rfl⟩ : syracuseStep 183671 = 275507) B275507
theorem B183691 : Blo 179801 183691 := bstep (se 1 (by rfl) ⟨137768, by rfl⟩ : syracuseStep 183691 = 275537) B275537
theorem B183703 : Blo 179801 183703 := bstep (se 1 (by rfl) ⟨137777, by rfl⟩ : syracuseStep 183703 = 275555) B275555
theorem B413081 : Blo 179801 413081 := bstep (se 2 (by rfl) ⟨154905, by rfl⟩ : syracuseStep 413081 = 309811) B309811
theorem B183723 : Blo 179801 183723 := bstep (se 1 (by rfl) ⟨137792, by rfl⟩ : syracuseStep 183723 = 275585) B275585
theorem B183735 : Blo 179801 183735 := bstep (se 1 (by rfl) ⟨137801, by rfl⟩ : syracuseStep 183735 = 275603) B275603
theorem B183755 : Blo 179801 183755 := bstep (se 1 (by rfl) ⟨137816, by rfl⟩ : syracuseStep 183755 = 275633) B275633
theorem B183767 : Blo 179801 183767 := bstep (se 1 (by rfl) ⟨137825, by rfl⟩ : syracuseStep 183767 = 275651) B275651
theorem B183787 : Blo 179801 183787 := bstep (se 1 (by rfl) ⟨137840, by rfl⟩ : syracuseStep 183787 = 275681) B275681
theorem B413171 : Blo 179801 413171 := bstep (se 1 (by rfl) ⟨309878, by rfl⟩ : syracuseStep 413171 = 619757) B619757
theorem B183799 : Blo 179801 183799 := bstep (se 1 (by rfl) ⟨137849, by rfl⟩ : syracuseStep 183799 = 275699) B275699
theorem B413207 : Blo 179801 413207 := bstep (se 1 (by rfl) ⟨309905, by rfl⟩ : syracuseStep 413207 = 619811) B619811
theorem B413387 : Blo 179801 413387 := bstep (se 1 (by rfl) ⟨310040, by rfl⟩ : syracuseStep 413387 = 620081) B620081
theorem B413441 : Blo 179801 413441 := bstep (se 2 (by rfl) ⟨155040, by rfl⟩ : syracuseStep 413441 = 310081) B310081
theorem B347915 : Blo 179801 347915 := bstep (se 1 (by rfl) ⟨260936, by rfl⟩ : syracuseStep 347915 = 521873) B521873
theorem B347969 : Blo 179801 347969 := bstep (se 2 (by rfl) ⟨130488, by rfl⟩ : syracuseStep 347969 = 260977) B260977
theorem B610199 : Blo 179801 610199 := bstep (se 1 (by rfl) ⟨457649, by rfl⟩ : syracuseStep 610199 = 915299) B915299
theorem B577459 : Blo 179801 577459 := bstep (se 1 (by rfl) ⟨433094, by rfl⟩ : syracuseStep 577459 = 866189) B866189
theorem B577601 : Blo 179801 577601 := bstep (se 2 (by rfl) ⟨216600, by rfl⟩ : syracuseStep 577601 = 433201) B433201
theorem B2084939 : Blo 179801 2084939 := bstep (se 1 (by rfl) ⟨1563704, by rfl⟩ : syracuseStep 2084939 = 3127409) B3127409
theorem B512203 : Blo 179801 512203 := bstep (se 1 (by rfl) ⟨384152, by rfl⟩ : syracuseStep 512203 = 768305) B768305
theorem B2937073 : Blo 179801 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B3297635 : Blo 179801 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B610739 : Blo 179801 610739 := bstep (se 1 (by rfl) ⟨458054, by rfl⟩ : syracuseStep 610739 = 916109) B916109
theorem B774593 : Blo 179801 774593 := bstep (se 2 (by rfl) ⟨290472, by rfl⟩ : syracuseStep 774593 = 580945) B580945
theorem B512477 : Blo 179801 512477 := bstep (se 3 (by rfl) ⟨96089, by rfl⟩ : syracuseStep 512477 = 192179) B192179
theorem B611009 : Blo 179801 611009 := bstep (se 2 (by rfl) ⟨229128, by rfl⟩ : syracuseStep 611009 = 458257) B458257
theorem B348887 : Blo 179801 348887 := bstep (se 1 (by rfl) ⟨261665, by rfl⟩ : syracuseStep 348887 = 523331) B523331
theorem B3134213 : Blo 179801 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B873281 : Blo 179801 873281 := bstep (se 2 (by rfl) ⟨327480, by rfl⟩ : syracuseStep 873281 = 654961) B654961
theorem B873433 : Blo 179801 873433 := bstep (se 2 (by rfl) ⟨327537, by rfl⟩ : syracuseStep 873433 = 655075) B655075
theorem B611549 : Blo 179801 611549 := bstep (se 3 (by rfl) ⟨114665, by rfl⟩ : syracuseStep 611549 = 229331) B229331
theorem B5002501 : Blo 179801 5002501 := bstep (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) B937969
theorem B972107 : Blo 179801 972107 := bstep (se 1 (by rfl) ⟨729080, by rfl⟩ : syracuseStep 972107 = 1458161) B1458161
theorem B218647 : Blo 179801 218647 := bstep (se 1 (by rfl) ⟨163985, by rfl⟩ : syracuseStep 218647 = 327971) B327971
theorem B186251 : Blo 179801 186251 := bstep (se 1 (by rfl) ⟨139688, by rfl⟩ : syracuseStep 186251 = 279377) B279377
theorem B579521 : Blo 179801 579521 := bstep (se 2 (by rfl) ⟨217320, by rfl⟩ : syracuseStep 579521 = 434641) B434641
theorem B546881 : Blo 179801 546881 := bstep (se 2 (by rfl) ⟨205080, by rfl⟩ : syracuseStep 546881 = 410161) B410161
theorem B12572813 : Blo 179801 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B1300697 : Blo 179801 1300697 := bstep (se 2 (by rfl) ⟨487761, by rfl⟩ : syracuseStep 1300697 = 975523) B975523
theorem B1562885 : Blo 179801 1562885 := bstep (se 4 (by rfl) ⟨146520, by rfl⟩ : syracuseStep 1562885 = 293041) B293041
theorem B2644289 : Blo 179801 2644289 := bstep (se 2 (by rfl) ⟨991608, by rfl⟩ : syracuseStep 2644289 = 1983217) B1983217
theorem B612683 : Blo 179801 612683 := bstep (se 1 (by rfl) ⟨459512, by rfl⟩ : syracuseStep 612683 = 919025) B919025
theorem B580061 : Blo 179801 580061 := bstep (se 3 (by rfl) ⟨108761, by rfl⟩ : syracuseStep 580061 = 217523) B217523
theorem B514583 : Blo 179801 514583 := bstep (se 1 (by rfl) ⟨385937, by rfl⟩ : syracuseStep 514583 = 771875) B771875
theorem B612953 : Blo 179801 612953 := bstep (se 2 (by rfl) ⟨229857, by rfl⟩ : syracuseStep 612953 = 459715) B459715
theorem B777053 : Blo 179801 777053 := bstep (se 3 (by rfl) ⟨145697, by rfl⟩ : syracuseStep 777053 = 291395) B291395
theorem B1563569 : Blo 179801 1563569 := bstep (se 2 (by rfl) ⟨586338, by rfl⟩ : syracuseStep 1563569 = 1172677) B1172677
theorem B1104857 : Blo 179801 1104857 := bstep (se 2 (by rfl) ⟨414321, by rfl⟩ : syracuseStep 1104857 = 828643) B828643
theorem B417035 : Blo 179801 417035 := bstep (se 1 (by rfl) ⟨312776, by rfl⟩ : syracuseStep 417035 = 625553) B625553
theorem B613655 : Blo 179801 613655 := bstep (se 1 (by rfl) ⟨460241, by rfl⟩ : syracuseStep 613655 = 920483) B920483
theorem B515393 : Blo 179801 515393 := bstep (se 2 (by rfl) ⟨193272, by rfl⟩ : syracuseStep 515393 = 386545) B386545
theorem B384563 : Blo 179801 384563 := bstep (se 1 (by rfl) ⟨288422, by rfl⟩ : syracuseStep 384563 = 576845) B576845
theorem B548441 : Blo 179801 548441 := bstep (se 2 (by rfl) ⟨205665, by rfl⟩ : syracuseStep 548441 = 411331) B411331
theorem B1171037 : Blo 179801 1171037 := bstep (se 3 (by rfl) ⟨219569, by rfl⟩ : syracuseStep 1171037 = 439139) B439139
theorem B450355 : Blo 179801 450355 := bstep (se 1 (by rfl) ⟨337766, by rfl⟩ : syracuseStep 450355 = 675533) B675533
theorem B614195 : Blo 179801 614195 := bstep (se 1 (by rfl) ⟨460646, by rfl⟩ : syracuseStep 614195 = 921293) B921293
theorem B1761203 : Blo 179801 1761203 := bstep (se 1 (by rfl) ⟨1320902, by rfl⟩ : syracuseStep 1761203 = 2641805) B2641805
theorem B1564595 : Blo 179801 1564595 := bstep (se 1 (by rfl) ⟨1173446, by rfl⟩ : syracuseStep 1564595 = 2346893) B2346893
theorem B417793 : Blo 179801 417793 := bstep (se 2 (by rfl) ⟨156672, by rfl⟩ : syracuseStep 417793 = 313345) B313345
theorem B385049 : Blo 179801 385049 := bstep (se 2 (by rfl) ⟨144393, by rfl⟩ : syracuseStep 385049 = 288787) B288787
theorem B614465 : Blo 179801 614465 := bstep (se 2 (by rfl) ⟨230424, by rfl⟩ : syracuseStep 614465 = 460849) B460849
theorem B26665237 : Blo 179801 26665237 := bstep (se 6 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 26665237 = 1249933) B1249933
theorem B1466885 : Blo 179801 1466885 := bstep (se 4 (by rfl) ⟨137520, by rfl⟩ : syracuseStep 1466885 = 275041) B275041
theorem B615005 : Blo 179801 615005 := bstep (se 3 (by rfl) ⟨115313, by rfl⟩ : syracuseStep 615005 = 230627) B230627
theorem B385793 : Blo 179801 385793 := bstep (se 2 (by rfl) ⟨144672, by rfl⟩ : syracuseStep 385793 = 289345) B289345
theorem B517043 : Blo 179801 517043 := bstep (se 1 (by rfl) ⟨387782, by rfl⟩ : syracuseStep 517043 = 775565) B775565
theorem B517067 : Blo 179801 517067 := bstep (se 1 (by rfl) ⟨387800, by rfl⟩ : syracuseStep 517067 = 775601) B775601
theorem B779651 : Blo 179801 779651 := bstep (se 1 (by rfl) ⟨584738, by rfl⟩ : syracuseStep 779651 = 1169477) B1169477
theorem B386689 : Blo 179801 386689 := bstep (se 2 (by rfl) ⟨145008, by rfl⟩ : syracuseStep 386689 = 290017) B290017
theorem B616139 : Blo 179801 616139 := bstep (se 1 (by rfl) ⟨462104, by rfl⟩ : syracuseStep 616139 = 924209) B924209
theorem B517853 : Blo 179801 517853 := bstep (se 3 (by rfl) ⟨97097, by rfl⟩ : syracuseStep 517853 = 194195) B194195
theorem B419671 : Blo 179801 419671 := bstep (se 1 (by rfl) ⟨314753, by rfl⟩ : syracuseStep 419671 = 629507) B629507
theorem B1370033 : Blo 179801 1370033 := bstep (se 2 (by rfl) ⟨513762, by rfl⟩ : syracuseStep 1370033 = 1027525) B1027525
theorem B387031 : Blo 179801 387031 := bstep (se 1 (by rfl) ⟨290273, by rfl⟩ : syracuseStep 387031 = 580547) B580547
theorem B616409 : Blo 179801 616409 := bstep (se 2 (by rfl) ⟨231153, by rfl⟩ : syracuseStep 616409 = 462307) B462307
theorem B649309 : Blo 179801 649309 := bstep (se 3 (by rfl) ⟨121745, by rfl⟩ : syracuseStep 649309 = 243491) B243491
theorem B1370519 : Blo 179801 1370519 := bstep (se 1 (by rfl) ⟨1027889, by rfl⟩ : syracuseStep 1370519 = 2055779) B2055779
theorem B387595 : Blo 179801 387595 := bstep (se 1 (by rfl) ⟨290696, by rfl⟩ : syracuseStep 387595 = 581393) B581393
theorem B649873 : Blo 179801 649873 := bstep (se 2 (by rfl) ⟨243702, by rfl⟩ : syracuseStep 649873 = 487405) B487405
theorem B617111 : Blo 179801 617111 := bstep (se 1 (by rfl) ⟨462833, by rfl⟩ : syracuseStep 617111 = 925667) B925667
theorem B715481 : Blo 179801 715481 := bstep (se 2 (by rfl) ⟨268305, by rfl⟩ : syracuseStep 715481 = 536611) B536611
theorem B682769 : Blo 179801 682769 := bstep (se 2 (by rfl) ⟨256038, by rfl⟩ : syracuseStep 682769 = 512077) B512077
theorem B1469249 : Blo 179801 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B912221 : Blo 179801 912221 := bstep (se 3 (by rfl) ⟨171041, by rfl⟩ : syracuseStep 912221 = 342083) B342083
theorem B617651 : Blo 179801 617651 := bstep (se 1 (by rfl) ⟨463238, by rfl⟩ : syracuseStep 617651 = 926477) B926477
theorem B683225 : Blo 179801 683225 := bstep (se 2 (by rfl) ⟨256209, by rfl⟩ : syracuseStep 683225 = 512419) B512419
theorem B1240337 : Blo 179801 1240337 := bstep (se 2 (by rfl) ⟨465126, by rfl⟩ : syracuseStep 1240337 = 930253) B930253
theorem B257303 : Blo 179801 257303 := bstep (se 1 (by rfl) ⟨192977, by rfl⟩ : syracuseStep 257303 = 385955) B385955
theorem B683437 : Blo 179801 683437 := bstep (se 3 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 683437 = 256289) B256289
theorem B617921 : Blo 179801 617921 := bstep (se 2 (by rfl) ⟨231720, by rfl⟩ : syracuseStep 617921 = 463441) B463441
theorem B519641 : Blo 179801 519641 := bstep (se 2 (by rfl) ⟨194865, by rfl⟩ : syracuseStep 519641 = 389731) B389731
theorem B749107 : Blo 179801 749107 := bstep (se 1 (by rfl) ⟨561830, by rfl⟩ : syracuseStep 749107 = 1123661) B1123661
theorem B1568321 : Blo 179801 1568321 := bstep (se 2 (by rfl) ⟨588120, by rfl⟩ : syracuseStep 1568321 = 1176241) B1176241
theorem B683741 : Blo 179801 683741 := bstep (se 3 (by rfl) ⟨128201, by rfl⟩ : syracuseStep 683741 = 256403) B256403
theorem B519959 : Blo 179801 519959 := bstep (se 1 (by rfl) ⟨389969, by rfl⟩ : syracuseStep 519959 = 779939) B779939
theorem B749387 : Blo 179801 749387 := bstep (se 1 (by rfl) ⟨562040, by rfl⟩ : syracuseStep 749387 = 1124081) B1124081
theorem B388979 : Blo 179801 388979 := bstep (se 1 (by rfl) ⟨291734, by rfl⟩ : syracuseStep 388979 = 583469) B583469
theorem B192439 : Blo 179801 192439 := bstep (se 1 (by rfl) ⟨144329, by rfl⟩ : syracuseStep 192439 = 288659) B288659
theorem B389081 : Blo 179801 389081 := bstep (se 2 (by rfl) ⟨145905, by rfl⟩ : syracuseStep 389081 = 291811) B291811
theorem B618461 : Blo 179801 618461 := bstep (se 3 (by rfl) ⟨115961, by rfl⟩ : syracuseStep 618461 = 231923) B231923
theorem B1339523 : Blo 179801 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B389441 : Blo 179801 389441 := bstep (se 2 (by rfl) ⟨146040, by rfl⟩ : syracuseStep 389441 = 292081) B292081
theorem B455129 : Blo 179801 455129 := bstep (se 2 (by rfl) ⟨170673, by rfl⟩ : syracuseStep 455129 = 341347) B341347
theorem B1045037 : Blo 179801 1045037 := bstep (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) B391889
theorem B520769 : Blo 179801 520769 := bstep (se 2 (by rfl) ⟨195288, by rfl⟩ : syracuseStep 520769 = 390577) B390577
theorem B291671 : Blo 179801 291671 := bstep (se 1 (by rfl) ⟨218753, by rfl⟩ : syracuseStep 291671 = 437507) B437507
theorem B914327 : Blo 179801 914327 := bstep (se 1 (by rfl) ⟨685745, by rfl⟩ : syracuseStep 914327 = 1371491) B1371491
theorem B390167 : Blo 179801 390167 := bstep (se 1 (by rfl) ⟨292625, by rfl⟩ : syracuseStep 390167 = 585251) B585251
theorem B783425 : Blo 179801 783425 := bstep (se 2 (by rfl) ⟨293784, by rfl⟩ : syracuseStep 783425 = 587569) B587569
theorem B619595 : Blo 179801 619595 := bstep (se 1 (by rfl) ⟨464696, by rfl⟩ : syracuseStep 619595 = 929393) B929393
theorem B1176727 : Blo 179801 1176727 := bstep (se 1 (by rfl) ⟨882545, by rfl⟩ : syracuseStep 1176727 = 1765091) B1765091
theorem B1537325 : Blo 179801 1537325 := bstep (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) B576497
theorem B619865 : Blo 179801 619865 := bstep (se 2 (by rfl) ⟨232449, by rfl⟩ : syracuseStep 619865 = 464899) B464899
theorem B587159 : Blo 179801 587159 := bstep (se 1 (by rfl) ⟨440369, by rfl⟩ : syracuseStep 587159 = 880739) B880739
theorem B1111475 : Blo 179801 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B194071 : Blo 179801 194071 := bstep (se 1 (by rfl) ⟨145553, by rfl⟩ : syracuseStep 194071 = 291107) B291107
theorem B620311 : Blo 179801 620311 := bstep (se 1 (by rfl) ⟨465233, by rfl⟩ : syracuseStep 620311 = 930467) B930467
theorem B292631 : Blo 179801 292631 := bstep (se 1 (by rfl) ⟨219473, by rfl⟩ : syracuseStep 292631 = 438947) B438947
theorem B292747 : Blo 179801 292747 := bstep (se 1 (by rfl) ⟨219560, by rfl⟩ : syracuseStep 292747 = 439121) B439121
theorem B391063 : Blo 179801 391063 := bstep (se 1 (by rfl) ⟨293297, by rfl⟩ : syracuseStep 391063 = 586595) B586595
theorem B784349 : Blo 179801 784349 := bstep (se 3 (by rfl) ⟨147065, by rfl⟩ : syracuseStep 784349 = 294131) B294131
theorem B456779 : Blo 179801 456779 := bstep (se 1 (by rfl) ⟨342584, by rfl⟩ : syracuseStep 456779 = 685169) B685169
theorem B260185 : Blo 179801 260185 := bstep (se 2 (by rfl) ⟨97569, by rfl⟩ : syracuseStep 260185 = 195139) B195139
theorem B489665 : Blo 179801 489665 := bstep (se 2 (by rfl) ⟨183624, by rfl⟩ : syracuseStep 489665 = 367249) B367249
theorem B522443 : Blo 179801 522443 := bstep (se 1 (by rfl) ⟨391832, by rfl⟩ : syracuseStep 522443 = 783665) B783665
theorem B686339 : Blo 179801 686339 := bstep (se 1 (by rfl) ⟨514754, by rfl⟩ : syracuseStep 686339 = 1029509) B1029509
theorem B686353 : Blo 179801 686353 := bstep (se 2 (by rfl) ⟨257382, by rfl⟩ : syracuseStep 686353 = 514765) B514765
theorem B391475 : Blo 179801 391475 := bstep (se 1 (by rfl) ⟨293606, by rfl⟩ : syracuseStep 391475 = 587213) B587213
theorem B194891 : Blo 179801 194891 := bstep (se 1 (by rfl) ⟨146168, by rfl⟩ : syracuseStep 194891 = 292337) B292337
theorem B588235 : Blo 179801 588235 := bstep (se 1 (by rfl) ⟨441176, by rfl⟩ : syracuseStep 588235 = 882353) B882353
theorem B227863 : Blo 179801 227863 := bstep (se 1 (by rfl) ⟨170897, by rfl⟩ : syracuseStep 227863 = 341795) B341795
theorem B1309229 : Blo 179801 1309229 := bstep (se 3 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 1309229 = 490961) B490961
theorem B686657 : Blo 179801 686657 := bstep (se 2 (by rfl) ⟨257496, by rfl⟩ : syracuseStep 686657 = 514993) B514993
theorem B293465 : Blo 179801 293465 := bstep (se 2 (by rfl) ⟨110049, by rfl⟩ : syracuseStep 293465 = 220099) B220099
theorem B391883 : Blo 179801 391883 := bstep (se 1 (by rfl) ⟨293912, by rfl⟩ : syracuseStep 391883 = 587825) B587825
theorem B490205 : Blo 179801 490205 := bstep (se 3 (by rfl) ⟨91913, by rfl⟩ : syracuseStep 490205 = 183827) B183827
theorem B359257 : Blo 179801 359257 := bstep (se 2 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 359257 = 269443) B269443
theorem B457751 : Blo 179801 457751 := bstep (se 1 (by rfl) ⟨343313, by rfl⟩ : syracuseStep 457751 = 686627) B686627
theorem B293977 : Blo 179801 293977 := bstep (se 2 (by rfl) ⟨110241, by rfl⟩ : syracuseStep 293977 = 220483) B220483
theorem B687325 : Blo 179801 687325 := bstep (se 3 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 687325 = 257747) B257747
theorem B228683 : Blo 179801 228683 := bstep (se 1 (by rfl) ⟨171512, by rfl⟩ : syracuseStep 228683 = 343025) B343025
theorem B195959 : Blo 179801 195959 := bstep (se 1 (by rfl) ⟨146969, by rfl⟩ : syracuseStep 195959 = 293939) B293939
theorem B261643 : Blo 179801 261643 := bstep (se 1 (by rfl) ⟨196232, by rfl⟩ : syracuseStep 261643 = 392465) B392465
theorem B2620997 : Blo 179801 2620997 := bstep (se 4 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 2620997 = 491437) B491437
theorem B458419 : Blo 179801 458419 := bstep (se 1 (by rfl) ⟨343814, by rfl⟩ : syracuseStep 458419 = 687629) B687629
theorem B458561 : Blo 179801 458561 := bstep (se 2 (by rfl) ⟨171960, by rfl⟩ : syracuseStep 458561 = 343921) B343921
theorem B1671005 : Blo 179801 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B557057 : Blo 179801 557057 := bstep (se 2 (by rfl) ⟨208896, by rfl⟩ : syracuseStep 557057 = 417793) B417793
theorem B458905 : Blo 179801 458905 := bstep (se 2 (by rfl) ⟨172089, by rfl⟩ : syracuseStep 458905 = 344179) B344179
theorem B2195657 : Blo 179801 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B459067 : Blo 179801 459067 := bstep (se 1 (by rfl) ⟨344300, by rfl⟩ : syracuseStep 459067 = 688601) B688601
theorem B35553649 : Blo 179801 35553649 := bstep (se 2 (by rfl) ⟨13332618, by rfl⟩ : syracuseStep 35553649 = 26665237) B26665237
theorem B885127 : Blo 179801 885127 := bstep (se 1 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 885127 = 1327691) B1327691
theorem B459209 : Blo 179801 459209 := bstep (se 2 (by rfl) ⟨172203, by rfl⟩ : syracuseStep 459209 = 344407) B344407
theorem B5833397 : Blo 179801 5833397 := bstep (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) B546881
theorem B2622145 : Blo 179801 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B459553 : Blo 179801 459553 := bstep (se 2 (by rfl) ⟨172332, by rfl⟩ : syracuseStep 459553 = 344665) B344665
theorem B525257 : Blo 179801 525257 := bstep (se 2 (by rfl) ⟨196971, by rfl⟩ : syracuseStep 525257 = 393943) B393943
theorem B918539 : Blo 179801 918539 := bstep (se 1 (by rfl) ⟨688904, by rfl⟩ : syracuseStep 918539 = 1377809) B1377809
theorem B918701 : Blo 179801 918701 := bstep (se 3 (by rfl) ⟨172256, by rfl⟩ : syracuseStep 918701 = 344513) B344513
theorem B13731185 : Blo 179801 13731185 := bstep (se 2 (by rfl) ⟨5149194, by rfl⟩ : syracuseStep 13731185 = 10298389) B10298389
theorem B7046513 : Blo 179801 7046513 := bstep (se 2 (by rfl) ⟨2642442, by rfl⟩ : syracuseStep 7046513 = 5284885) B5284885
theorem B460151 : Blo 179801 460151 := bstep (se 1 (by rfl) ⟨345113, by rfl⟩ : syracuseStep 460151 = 690227) B690227
theorem B689543 : Blo 179801 689543 := bstep (se 1 (by rfl) ⟨517157, by rfl⟩ : syracuseStep 689543 = 1034315) B1034315
theorem B2065985 : Blo 179801 2065985 := bstep (se 2 (by rfl) ⟨774744, by rfl⟩ : syracuseStep 2065985 = 1549489) B1549489
theorem B1541699 : Blo 179801 1541699 := bstep (se 1 (by rfl) ⟨1156274, by rfl⟩ : syracuseStep 1541699 = 2312549) B2312549
theorem B36537925 : Blo 179801 36537925 := bstep (se 4 (by rfl) ⟨3425430, by rfl⟩ : syracuseStep 36537925 = 6850861) B6850861
theorem B788087 : Blo 179801 788087 := bstep (se 1 (by rfl) ⟨591065, by rfl⟩ : syracuseStep 788087 = 1182131) B1182131
theorem B1771721 : Blo 179801 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B559561 : Blo 179801 559561 := bstep (se 2 (by rfl) ⟨209835, by rfl⟩ : syracuseStep 559561 = 419671) B419671
theorem B1378781 : Blo 179801 1378781 := bstep (se 3 (by rfl) ⟨258521, by rfl⟩ : syracuseStep 1378781 = 517043) B517043
theorem B231979 : Blo 179801 231979 := bstep (se 1 (by rfl) ⟨173984, by rfl⟩ : syracuseStep 231979 = 347969) B347969
theorem B461447 : Blo 179801 461447 := bstep (se 1 (by rfl) ⟨346085, by rfl⟩ : syracuseStep 461447 = 692171) B692171
theorem B461497 : Blo 179801 461497 := bstep (se 2 (by rfl) ⟨173061, by rfl⟩ : syracuseStep 461497 = 346123) B346123
theorem B920321 : Blo 179801 920321 := bstep (se 2 (by rfl) ⟨345120, by rfl⟩ : syracuseStep 920321 = 690241) B690241
theorem B985945 : Blo 179801 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B2198423 : Blo 179801 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B5639179 : Blo 179801 5639179 := bstep (se 1 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 5639179 = 8458769) B8458769
theorem B462095 : Blo 179801 462095 := bstep (se 1 (by rfl) ⟨346571, by rfl⟩ : syracuseStep 462095 = 693143) B693143
theorem B921131 : Blo 179801 921131 := bstep (se 1 (by rfl) ⟨690848, by rfl⟩ : syracuseStep 921131 = 1381697) B1381697
theorem B462793 : Blo 179801 462793 := bstep (se 2 (by rfl) ⟨173547, by rfl⟩ : syracuseStep 462793 = 347095) B347095
theorem B462935 : Blo 179801 462935 := bstep (se 1 (by rfl) ⟨347201, by rfl⟩ : syracuseStep 462935 = 694403) B694403
theorem B987329 : Blo 179801 987329 := bstep (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) B740497
theorem B922427 : Blo 179801 922427 := bstep (se 1 (by rfl) ⟨691820, by rfl⟩ : syracuseStep 922427 = 1383641) B1383641
theorem B922589 : Blo 179801 922589 := bstep (se 3 (by rfl) ⟨172985, by rfl⟩ : syracuseStep 922589 = 345971) B345971
theorem B365627 : Blo 179801 365627 := bstep (se 1 (by rfl) ⟨274220, by rfl⟩ : syracuseStep 365627 = 548441) B548441
theorem B4658309 : Blo 179801 4658309 := bstep (se 4 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 4658309 = 873433) B873433
theorem B1545389 : Blo 179801 1545389 := bstep (se 3 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 1545389 = 579521) B579521
theorem B922913 : Blo 179801 922913 := bstep (se 2 (by rfl) ⟨346092, by rfl⟩ : syracuseStep 922913 = 692185) B692185
theorem B1546073 : Blo 179801 1546073 := bstep (se 2 (by rfl) ⟨579777, by rfl⟩ : syracuseStep 1546073 = 1159555) B1159555
theorem B202639 : Blo 179801 202639 := bstep (se 1 (by rfl) ⟨151979, by rfl⟩ : syracuseStep 202639 = 303959) B303959
theorem B465011 : Blo 179801 465011 := bstep (se 1 (by rfl) ⟨348758, by rfl⟩ : syracuseStep 465011 = 697517) B697517
theorem B923885 : Blo 179801 923885 := bstep (se 3 (by rfl) ⟨173228, by rfl⟩ : syracuseStep 923885 = 346457) B346457
theorem B203143 : Blo 179801 203143 := bstep (se 1 (by rfl) ⟨152357, by rfl⟩ : syracuseStep 203143 = 304715) B304715
theorem B203323 : Blo 179801 203323 := bstep (se 1 (by rfl) ⟨152492, by rfl⟩ : syracuseStep 203323 = 304985) B304985
theorem B203791 : Blo 179801 203791 := bstep (se 1 (by rfl) ⟨152843, by rfl⟩ : syracuseStep 203791 = 305687) B305687
theorem B924695 : Blo 179801 924695 := bstep (se 1 (by rfl) ⟨693521, by rfl⟩ : syracuseStep 924695 = 1387043) B1387043
theorem B269711 : Blo 179801 269711 := bstep (se 1 (by rfl) ⟨202283, by rfl⟩ : syracuseStep 269711 = 404567) B404567
theorem B269753 : Blo 179801 269753 := bstep (se 2 (by rfl) ⟨101157, by rfl⟩ : syracuseStep 269753 = 202315) B202315
theorem B269831 : Blo 179801 269831 := bstep (se 1 (by rfl) ⟨202373, by rfl⟩ : syracuseStep 269831 = 404747) B404747
theorem B204295 : Blo 179801 204295 := bstep (se 1 (by rfl) ⟨153221, by rfl⟩ : syracuseStep 204295 = 306443) B306443
theorem B826891 : Blo 179801 826891 := bstep (se 1 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 826891 = 1240337) B1240337
theorem B269867 : Blo 179801 269867 := bstep (se 1 (by rfl) ⟨202400, by rfl⟩ : syracuseStep 269867 = 404801) B404801
theorem B269897 : Blo 179801 269897 := bstep (se 2 (by rfl) ⟨101211, by rfl⟩ : syracuseStep 269897 = 202423) B202423
theorem B1777331 : Blo 179801 1777331 := bstep (se 1 (by rfl) ⟨1332998, by rfl⟩ : syracuseStep 1777331 = 2665997) B2665997
theorem B270011 : Blo 179801 270011 := bstep (se 1 (by rfl) ⟨202508, by rfl⟩ : syracuseStep 270011 = 405017) B405017
theorem B204475 : Blo 179801 204475 := bstep (se 1 (by rfl) ⟨153356, by rfl⟩ : syracuseStep 204475 = 306713) B306713
theorem B827081 : Blo 179801 827081 := bstep (se 2 (by rfl) ⟨310155, by rfl⟩ : syracuseStep 827081 = 620311) B620311
theorem B270071 : Blo 179801 270071 := bstep (se 1 (by rfl) ⟨202553, by rfl⟩ : syracuseStep 270071 = 405107) B405107
theorem B270095 : Blo 179801 270095 := bstep (se 1 (by rfl) ⟨202571, by rfl⟩ : syracuseStep 270095 = 405143) B405143
theorem B1056563 : Blo 179801 1056563 := bstep (se 1 (by rfl) ⟨792422, by rfl⟩ : syracuseStep 1056563 = 1584845) B1584845
theorem B270137 : Blo 179801 270137 := bstep (se 2 (by rfl) ⟨101301, by rfl⟩ : syracuseStep 270137 = 202603) B202603
theorem B991091 : Blo 179801 991091 := bstep (se 1 (by rfl) ⟨743318, by rfl⟩ : syracuseStep 991091 = 1486637) B1486637
theorem B270215 : Blo 179801 270215 := bstep (se 1 (by rfl) ⟨202661, by rfl⟩ : syracuseStep 270215 = 405323) B405323
theorem B499591 : Blo 179801 499591 := bstep (se 1 (by rfl) ⟨374693, by rfl⟩ : syracuseStep 499591 = 749387) B749387
theorem B270251 : Blo 179801 270251 := bstep (se 1 (by rfl) ⟨202688, by rfl⟩ : syracuseStep 270251 = 405377) B405377
theorem B270281 : Blo 179801 270281 := bstep (se 2 (by rfl) ⟨101355, by rfl⟩ : syracuseStep 270281 = 202711) B202711
theorem B270395 : Blo 179801 270395 := bstep (se 1 (by rfl) ⟨202796, by rfl⟩ : syracuseStep 270395 = 405593) B405593
theorem B893015 : Blo 179801 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B270455 : Blo 179801 270455 := bstep (se 1 (by rfl) ⟨202841, by rfl⟩ : syracuseStep 270455 = 405683) B405683
theorem B1056887 : Blo 179801 1056887 := bstep (se 1 (by rfl) ⟨792665, by rfl⟩ : syracuseStep 1056887 = 1585331) B1585331
theorem B270479 : Blo 179801 270479 := bstep (se 1 (by rfl) ⟨202859, by rfl⟩ : syracuseStep 270479 = 405719) B405719
theorem B204943 : Blo 179801 204943 := bstep (se 1 (by rfl) ⟨153707, by rfl⟩ : syracuseStep 204943 = 307415) B307415
theorem B270521 : Blo 179801 270521 := bstep (se 2 (by rfl) ⟨101445, by rfl⟩ : syracuseStep 270521 = 202891) B202891
theorem B270599 : Blo 179801 270599 := bstep (se 1 (by rfl) ⟨202949, by rfl⟩ : syracuseStep 270599 = 405899) B405899
theorem B270635 : Blo 179801 270635 := bstep (se 1 (by rfl) ⟨202976, by rfl⟩ : syracuseStep 270635 = 405953) B405953
theorem B303419 : Blo 179801 303419 := bstep (se 1 (by rfl) ⟨227564, by rfl⟩ : syracuseStep 303419 = 455129) B455129
theorem B270665 : Blo 179801 270665 := bstep (se 2 (by rfl) ⟨101499, by rfl⟩ : syracuseStep 270665 = 202999) B202999
theorem B696691 : Blo 179801 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B270779 : Blo 179801 270779 := bstep (se 1 (by rfl) ⟨203084, by rfl⟩ : syracuseStep 270779 = 406169) B406169
theorem B270839 : Blo 179801 270839 := bstep (se 1 (by rfl) ⟨203129, by rfl⟩ : syracuseStep 270839 = 406259) B406259
theorem B270863 : Blo 179801 270863 := bstep (se 1 (by rfl) ⟨203147, by rfl⟩ : syracuseStep 270863 = 406295) B406295
theorem B270905 : Blo 179801 270905 := bstep (se 2 (by rfl) ⟨101589, by rfl⟩ : syracuseStep 270905 = 203179) B203179
theorem B270983 : Blo 179801 270983 := bstep (se 1 (by rfl) ⟨203237, by rfl⟩ : syracuseStep 270983 = 406475) B406475
theorem B205447 : Blo 179801 205447 := bstep (se 1 (by rfl) ⟨154085, by rfl⟩ : syracuseStep 205447 = 308171) B308171
theorem B271019 : Blo 179801 271019 := bstep (se 1 (by rfl) ⟨203264, by rfl⟩ : syracuseStep 271019 = 406529) B406529
theorem B303817 : Blo 179801 303817 := bstep (se 2 (by rfl) ⟨113931, by rfl⟩ : syracuseStep 303817 = 227863) B227863
theorem B271049 : Blo 179801 271049 := bstep (se 2 (by rfl) ⟨101643, by rfl⟩ : syracuseStep 271049 = 203287) B203287
theorem B271163 : Blo 179801 271163 := bstep (se 1 (by rfl) ⟨203372, by rfl⟩ : syracuseStep 271163 = 406745) B406745
theorem B205627 : Blo 179801 205627 := bstep (se 1 (by rfl) ⟨154220, by rfl⟩ : syracuseStep 205627 = 308441) B308441
theorem B1024883 : Blo 179801 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B271223 : Blo 179801 271223 := bstep (se 1 (by rfl) ⟨203417, by rfl⟩ : syracuseStep 271223 = 406835) B406835
theorem B271247 : Blo 179801 271247 := bstep (se 1 (by rfl) ⟨203435, by rfl⟩ : syracuseStep 271247 = 406871) B406871
theorem B271289 : Blo 179801 271289 := bstep (se 2 (by rfl) ⟨101733, by rfl⟩ : syracuseStep 271289 = 203467) B203467
theorem B271367 : Blo 179801 271367 := bstep (se 1 (by rfl) ⟨203525, by rfl⟩ : syracuseStep 271367 = 407051) B407051
theorem B271403 : Blo 179801 271403 := bstep (se 1 (by rfl) ⟨203552, by rfl⟩ : syracuseStep 271403 = 407105) B407105
theorem B271433 : Blo 179801 271433 := bstep (se 2 (by rfl) ⟨101787, by rfl⟩ : syracuseStep 271433 = 203575) B203575
theorem B7611479 : Blo 179801 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B271547 : Blo 179801 271547 := bstep (se 1 (by rfl) ⟨203660, by rfl⟩ : syracuseStep 271547 = 407321) B407321
theorem B271607 : Blo 179801 271607 := bstep (se 1 (by rfl) ⟨203705, by rfl⟩ : syracuseStep 271607 = 407411) B407411
theorem B271631 : Blo 179801 271631 := bstep (se 1 (by rfl) ⟨203723, by rfl⟩ : syracuseStep 271631 = 407447) B407447
theorem B206095 : Blo 179801 206095 := bstep (se 1 (by rfl) ⟨154571, by rfl⟩ : syracuseStep 206095 = 309143) B309143
theorem B664865 : Blo 179801 664865 := bstep (se 2 (by rfl) ⟨249324, by rfl⟩ : syracuseStep 664865 = 498649) B498649
theorem B271673 : Blo 179801 271673 := bstep (se 2 (by rfl) ⟨101877, by rfl⟩ : syracuseStep 271673 = 203755) B203755
theorem B304519 : Blo 179801 304519 := bstep (se 1 (by rfl) ⟨228389, by rfl⟩ : syracuseStep 304519 = 456779) B456779
theorem B271751 : Blo 179801 271751 := bstep (se 1 (by rfl) ⟨203813, by rfl⟩ : syracuseStep 271751 = 407627) B407627
theorem B271787 : Blo 179801 271787 := bstep (se 1 (by rfl) ⟨203840, by rfl⟩ : syracuseStep 271787 = 407681) B407681
theorem B271817 : Blo 179801 271817 := bstep (se 2 (by rfl) ⟨101931, by rfl⟩ : syracuseStep 271817 = 203863) B203863
theorem B271931 : Blo 179801 271931 := bstep (se 1 (by rfl) ⟨203948, by rfl⟩ : syracuseStep 271931 = 407897) B407897
theorem B271991 : Blo 179801 271991 := bstep (se 1 (by rfl) ⟨203993, by rfl⟩ : syracuseStep 271991 = 407987) B407987
theorem B861815 : Blo 179801 861815 := bstep (se 1 (by rfl) ⟨646361, by rfl⟩ : syracuseStep 861815 = 1292723) B1292723
theorem B272015 : Blo 179801 272015 := bstep (se 1 (by rfl) ⟨204011, by rfl⟩ : syracuseStep 272015 = 408023) B408023
theorem B272057 : Blo 179801 272057 := bstep (se 2 (by rfl) ⟨102021, by rfl⟩ : syracuseStep 272057 = 204043) B204043
theorem B403145 : Blo 179801 403145 := bstep (se 2 (by rfl) ⟨151179, by rfl⟩ : syracuseStep 403145 = 302359) B302359
theorem B272135 : Blo 179801 272135 := bstep (se 1 (by rfl) ⟨204101, by rfl⟩ : syracuseStep 272135 = 408203) B408203
theorem B206599 : Blo 179801 206599 := bstep (se 1 (by rfl) ⟨154949, by rfl⟩ : syracuseStep 206599 = 309899) B309899
theorem B272171 : Blo 179801 272171 := bstep (se 1 (by rfl) ⟨204128, by rfl⟩ : syracuseStep 272171 = 408257) B408257
theorem B272201 : Blo 179801 272201 := bstep (se 2 (by rfl) ⟨102075, by rfl⟩ : syracuseStep 272201 = 204151) B204151
theorem B894905 : Blo 179801 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B272315 : Blo 179801 272315 := bstep (se 1 (by rfl) ⟨204236, by rfl⟩ : syracuseStep 272315 = 408473) B408473
theorem B272375 : Blo 179801 272375 := bstep (se 1 (by rfl) ⟨204281, by rfl⟩ : syracuseStep 272375 = 408563) B408563
theorem B305167 : Blo 179801 305167 := bstep (se 1 (by rfl) ⟨228875, by rfl⟩ : syracuseStep 305167 = 457751) B457751
theorem B272399 : Blo 179801 272399 := bstep (se 1 (by rfl) ⟨204299, by rfl⟩ : syracuseStep 272399 = 408599) B408599
theorem B927773 : Blo 179801 927773 := bstep (se 3 (by rfl) ⟨173957, by rfl⟩ : syracuseStep 927773 = 347915) B347915
theorem B272441 : Blo 179801 272441 := bstep (se 2 (by rfl) ⟨102165, by rfl⟩ : syracuseStep 272441 = 204331) B204331
theorem B1386557 : Blo 179801 1386557 := bstep (se 3 (by rfl) ⟨259979, by rfl⟩ : syracuseStep 1386557 = 519959) B519959
theorem B272519 : Blo 179801 272519 := bstep (se 1 (by rfl) ⟨204389, by rfl⟩ : syracuseStep 272519 = 408779) B408779
theorem B272555 : Blo 179801 272555 := bstep (se 1 (by rfl) ⟨204416, by rfl⟩ : syracuseStep 272555 = 408833) B408833
theorem B272585 : Blo 179801 272585 := bstep (se 2 (by rfl) ⟨102219, by rfl⟩ : syracuseStep 272585 = 204439) B204439
theorem B1026341 : Blo 179801 1026341 := bstep (se 4 (by rfl) ⟨96219, by rfl⟩ : syracuseStep 1026341 = 192439) B192439
theorem B272699 : Blo 179801 272699 := bstep (se 1 (by rfl) ⟨204524, by rfl⟩ : syracuseStep 272699 = 409049) B409049
theorem B272759 : Blo 179801 272759 := bstep (se 1 (by rfl) ⟨204569, by rfl⟩ : syracuseStep 272759 = 409139) B409139
theorem B1747331 : Blo 179801 1747331 := bstep (se 1 (by rfl) ⟨1310498, by rfl⟩ : syracuseStep 1747331 = 2620997) B2620997
theorem B272783 : Blo 179801 272783 := bstep (se 1 (by rfl) ⟨204587, by rfl⟩ : syracuseStep 272783 = 409175) B409175
theorem B600473 : Blo 179801 600473 := bstep (se 2 (by rfl) ⟨225177, by rfl⟩ : syracuseStep 600473 = 450355) B450355
theorem B272825 : Blo 179801 272825 := bstep (se 2 (by rfl) ⟨102309, by rfl⟩ : syracuseStep 272825 = 204619) B204619
theorem B928259 : Blo 179801 928259 := bstep (se 1 (by rfl) ⟨696194, by rfl⟩ : syracuseStep 928259 = 1392389) B1392389
theorem B272903 : Blo 179801 272903 := bstep (se 1 (by rfl) ⟨204677, by rfl⟩ : syracuseStep 272903 = 409355) B409355
theorem B305707 : Blo 179801 305707 := bstep (se 1 (by rfl) ⟨229280, by rfl⟩ : syracuseStep 305707 = 458561) B458561
theorem B272939 : Blo 179801 272939 := bstep (se 1 (by rfl) ⟨204704, by rfl⟩ : syracuseStep 272939 = 409409) B409409
theorem B272969 : Blo 179801 272969 := bstep (se 2 (by rfl) ⟨102363, by rfl⟩ : syracuseStep 272969 = 204727) B204727
theorem B305849 : Blo 179801 305849 := bstep (se 2 (by rfl) ⟨114693, by rfl⟩ : syracuseStep 305849 = 229387) B229387
theorem B273083 : Blo 179801 273083 := bstep (se 1 (by rfl) ⟨204812, by rfl⟩ : syracuseStep 273083 = 409625) B409625
theorem B273143 : Blo 179801 273143 := bstep (se 1 (by rfl) ⟨204857, by rfl⟩ : syracuseStep 273143 = 409715) B409715
theorem B273167 : Blo 179801 273167 := bstep (se 1 (by rfl) ⟨204875, by rfl⟩ : syracuseStep 273167 = 409751) B409751
theorem B273209 : Blo 179801 273209 := bstep (se 2 (by rfl) ⟨102453, by rfl⟩ : syracuseStep 273209 = 204907) B204907
theorem B273287 : Blo 179801 273287 := bstep (se 1 (by rfl) ⟨204965, by rfl⟩ : syracuseStep 273287 = 409931) B409931
theorem B273323 : Blo 179801 273323 := bstep (se 1 (by rfl) ⟨204992, by rfl⟩ : syracuseStep 273323 = 409985) B409985
theorem B273353 : Blo 179801 273353 := bstep (se 2 (by rfl) ⟨102507, by rfl⟩ : syracuseStep 273353 = 205015) B205015
theorem B1027025 : Blo 179801 1027025 := bstep (se 2 (by rfl) ⟨385134, by rfl⟩ : syracuseStep 1027025 = 770269) B770269
theorem B273467 : Blo 179801 273467 := bstep (se 1 (by rfl) ⟨205100, by rfl⟩ : syracuseStep 273467 = 410201) B410201
theorem B699479 : Blo 179801 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B273527 : Blo 179801 273527 := bstep (se 1 (by rfl) ⟨205145, by rfl⟩ : syracuseStep 273527 = 410291) B410291
theorem B470135 : Blo 179801 470135 := bstep (se 1 (by rfl) ⟨352601, by rfl⟩ : syracuseStep 470135 = 705203) B705203
theorem B273551 : Blo 179801 273551 := bstep (se 1 (by rfl) ⟨205163, by rfl⟩ : syracuseStep 273551 = 410327) B410327
theorem B273593 : Blo 179801 273593 := bstep (se 2 (by rfl) ⟨102597, by rfl⟩ : syracuseStep 273593 = 205195) B205195
theorem B273671 : Blo 179801 273671 := bstep (se 1 (by rfl) ⟨205253, by rfl⟩ : syracuseStep 273671 = 410507) B410507
theorem B1027343 : Blo 179801 1027343 := bstep (se 1 (by rfl) ⟨770507, by rfl⟩ : syracuseStep 1027343 = 1541015) B1541015
theorem B273707 : Blo 179801 273707 := bstep (se 1 (by rfl) ⟨205280, by rfl⟩ : syracuseStep 273707 = 410561) B410561
theorem B273737 : Blo 179801 273737 := bstep (se 2 (by rfl) ⟨102651, by rfl⟩ : syracuseStep 273737 = 205303) B205303
theorem B404855 : Blo 179801 404855 := bstep (se 1 (by rfl) ⟨303641, by rfl⟩ : syracuseStep 404855 = 607283) B607283
theorem B306551 : Blo 179801 306551 := bstep (se 1 (by rfl) ⟨229913, by rfl⟩ : syracuseStep 306551 = 459827) B459827
theorem B273851 : Blo 179801 273851 := bstep (se 1 (by rfl) ⟨205388, by rfl⟩ : syracuseStep 273851 = 410777) B410777
theorem B273911 : Blo 179801 273911 := bstep (se 1 (by rfl) ⟨205433, by rfl⟩ : syracuseStep 273911 = 410867) B410867
theorem B470539 : Blo 179801 470539 := bstep (se 1 (by rfl) ⟨352904, by rfl⟩ : syracuseStep 470539 = 705809) B705809
theorem B273935 : Blo 179801 273935 := bstep (se 1 (by rfl) ⟨205451, by rfl⟩ : syracuseStep 273935 = 410903) B410903
theorem B405035 : Blo 179801 405035 := bstep (se 1 (by rfl) ⟨303776, by rfl⟩ : syracuseStep 405035 = 607553) B607553
theorem B831019 : Blo 179801 831019 := bstep (se 1 (by rfl) ⟨623264, by rfl⟩ : syracuseStep 831019 = 1246529) B1246529
theorem B273977 : Blo 179801 273977 := bstep (se 2 (by rfl) ⟨102741, by rfl⟩ : syracuseStep 273977 = 205483) B205483
theorem B274055 : Blo 179801 274055 := bstep (se 1 (by rfl) ⟨205541, by rfl⟩ : syracuseStep 274055 = 411083) B411083
theorem B274091 : Blo 179801 274091 := bstep (se 1 (by rfl) ⟨205568, by rfl⟩ : syracuseStep 274091 = 411137) B411137
theorem B274121 : Blo 179801 274121 := bstep (se 2 (by rfl) ⟨102795, by rfl⟩ : syracuseStep 274121 = 205591) B205591
theorem B3288883 : Blo 179801 3288883 := bstep (se 1 (by rfl) ⟨2466662, by rfl⟩ : syracuseStep 3288883 = 4933325) B4933325
theorem B307003 : Blo 179801 307003 := bstep (se 1 (by rfl) ⟨230252, by rfl⟩ : syracuseStep 307003 = 460505) B460505
theorem B274235 : Blo 179801 274235 := bstep (se 1 (by rfl) ⟨205676, by rfl⟩ : syracuseStep 274235 = 411353) B411353
theorem B274295 : Blo 179801 274295 := bstep (se 1 (by rfl) ⟨205721, by rfl⟩ : syracuseStep 274295 = 411443) B411443
theorem B274319 : Blo 179801 274319 := bstep (se 1 (by rfl) ⟨205739, by rfl⟩ : syracuseStep 274319 = 411479) B411479
theorem B405395 : Blo 179801 405395 := bstep (se 1 (by rfl) ⟨304046, by rfl⟩ : syracuseStep 405395 = 608093) B608093
theorem B274361 : Blo 179801 274361 := bstep (se 2 (by rfl) ⟨102885, by rfl⟩ : syracuseStep 274361 = 205771) B205771
theorem B405449 : Blo 179801 405449 := bstep (se 2 (by rfl) ⟨152043, by rfl⟩ : syracuseStep 405449 = 304087) B304087
theorem B307145 : Blo 179801 307145 := bstep (se 2 (by rfl) ⟨115179, by rfl⟩ : syracuseStep 307145 = 230359) B230359
theorem B274439 : Blo 179801 274439 := bstep (se 1 (by rfl) ⟨205829, by rfl⟩ : syracuseStep 274439 = 411659) B411659
theorem B274475 : Blo 179801 274475 := bstep (se 1 (by rfl) ⟨205856, by rfl⟩ : syracuseStep 274475 = 411713) B411713
theorem B274505 : Blo 179801 274505 := bstep (se 2 (by rfl) ⟨102939, by rfl⟩ : syracuseStep 274505 = 205879) B205879
theorem B929879 : Blo 179801 929879 := bstep (se 1 (by rfl) ⟨697409, by rfl⟩ : syracuseStep 929879 = 1394819) B1394819
theorem B274619 : Blo 179801 274619 := bstep (se 1 (by rfl) ⟨205964, by rfl⟩ : syracuseStep 274619 = 411929) B411929
theorem B274679 : Blo 179801 274679 := bstep (se 1 (by rfl) ⟨206009, by rfl⟩ : syracuseStep 274679 = 412019) B412019
theorem B274703 : Blo 179801 274703 := bstep (se 1 (by rfl) ⟨206027, by rfl⟩ : syracuseStep 274703 = 412055) B412055
theorem B274745 : Blo 179801 274745 := bstep (se 2 (by rfl) ⟨103029, by rfl⟩ : syracuseStep 274745 = 206059) B206059
theorem B274823 : Blo 179801 274823 := bstep (se 1 (by rfl) ⟨206117, by rfl⟩ : syracuseStep 274823 = 412235) B412235
theorem B1814929 : Blo 179801 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B274859 : Blo 179801 274859 := bstep (se 1 (by rfl) ⟨206144, by rfl⟩ : syracuseStep 274859 = 412289) B412289
theorem B274889 : Blo 179801 274889 := bstep (se 2 (by rfl) ⟨103083, by rfl⟩ : syracuseStep 274889 = 206167) B206167
theorem B275003 : Blo 179801 275003 := bstep (se 1 (by rfl) ⟨206252, by rfl⟩ : syracuseStep 275003 = 412505) B412505
theorem B930365 : Blo 179801 930365 := bstep (se 3 (by rfl) ⟨174443, by rfl⟩ : syracuseStep 930365 = 348887) B348887
theorem B275063 : Blo 179801 275063 := bstep (se 1 (by rfl) ⟨206297, by rfl⟩ : syracuseStep 275063 = 412595) B412595
theorem B406151 : Blo 179801 406151 := bstep (se 1 (by rfl) ⟨304613, by rfl⟩ : syracuseStep 406151 = 609227) B609227
theorem B307847 : Blo 179801 307847 := bstep (se 1 (by rfl) ⟨230885, by rfl⟩ : syracuseStep 307847 = 461771) B461771
theorem B275087 : Blo 179801 275087 := bstep (se 1 (by rfl) ⟨206315, by rfl⟩ : syracuseStep 275087 = 412631) B412631
theorem B275129 : Blo 179801 275129 := bstep (se 2 (by rfl) ⟨103173, by rfl⟩ : syracuseStep 275129 = 206347) B206347
theorem B1028801 : Blo 179801 1028801 := bstep (se 2 (by rfl) ⟨385800, by rfl⟩ : syracuseStep 1028801 = 771601) B771601
theorem B275207 : Blo 179801 275207 := bstep (se 1 (by rfl) ⟨206405, by rfl⟩ : syracuseStep 275207 = 412811) B412811
theorem B275243 : Blo 179801 275243 := bstep (se 1 (by rfl) ⟨206432, by rfl⟩ : syracuseStep 275243 = 412865) B412865
theorem B406331 : Blo 179801 406331 := bstep (se 1 (by rfl) ⟨304748, by rfl⟩ : syracuseStep 406331 = 609497) B609497
theorem B275273 : Blo 179801 275273 := bstep (se 2 (by rfl) ⟨103227, by rfl⟩ : syracuseStep 275273 = 206455) B206455
theorem B406457 : Blo 179801 406457 := bstep (se 2 (by rfl) ⟨152421, by rfl⟩ : syracuseStep 406457 = 304843) B304843
theorem B275387 : Blo 179801 275387 := bstep (se 1 (by rfl) ⟨206540, by rfl⟩ : syracuseStep 275387 = 413081) B413081
theorem B275447 : Blo 179801 275447 := bstep (se 1 (by rfl) ⟨206585, by rfl⟩ : syracuseStep 275447 = 413171) B413171
theorem B275471 : Blo 179801 275471 := bstep (se 1 (by rfl) ⟨206603, by rfl⟩ : syracuseStep 275471 = 413207) B413207
theorem B275513 : Blo 179801 275513 := bstep (se 2 (by rfl) ⟨103317, by rfl⟩ : syracuseStep 275513 = 206635) B206635
theorem B701507 : Blo 179801 701507 := bstep (se 1 (by rfl) ⟨526130, by rfl⟩ : syracuseStep 701507 = 1052261) B1052261
theorem B275591 : Blo 179801 275591 := bstep (se 1 (by rfl) ⟨206693, by rfl⟩ : syracuseStep 275591 = 413387) B413387
theorem B275627 : Blo 179801 275627 := bstep (se 1 (by rfl) ⟨206720, by rfl⟩ : syracuseStep 275627 = 413441) B413441
theorem B275657 : Blo 179801 275657 := bstep (se 2 (by rfl) ⟨103371, by rfl⟩ : syracuseStep 275657 = 206743) B206743
theorem B439553 : Blo 179801 439553 := bstep (se 2 (by rfl) ⟨164832, by rfl⟩ : syracuseStep 439553 = 329665) B329665
theorem B406799 : Blo 179801 406799 := bstep (se 1 (by rfl) ⟨305099, by rfl⟩ : syracuseStep 406799 = 610199) B610199
theorem B308495 : Blo 179801 308495 := bstep (se 1 (by rfl) ⟨231371, by rfl⟩ : syracuseStep 308495 = 462743) B462743
theorem B406817 : Blo 179801 406817 := bstep (se 2 (by rfl) ⟨152556, by rfl⟩ : syracuseStep 406817 = 305113) B305113
theorem B1389959 : Blo 179801 1389959 := bstep (se 1 (by rfl) ⟨1042469, by rfl⟩ : syracuseStep 1389959 = 2084939) B2084939
theorem B243145 : Blo 179801 243145 := bstep (se 2 (by rfl) ⟨91179, by rfl⟩ : syracuseStep 243145 = 182359) B182359
theorem B865745 : Blo 179801 865745 := bstep (se 2 (by rfl) ⟨324654, by rfl⟩ : syracuseStep 865745 = 649309) B649309
theorem B1488451 : Blo 179801 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B243319 : Blo 179801 243319 := bstep (se 1 (by rfl) ⟨182489, by rfl⟩ : syracuseStep 243319 = 364979) B364979
theorem B407159 : Blo 179801 407159 := bstep (se 1 (by rfl) ⟨305369, by rfl⟩ : syracuseStep 407159 = 610739) B610739
theorem B341651 : Blo 179801 341651 := bstep (se 1 (by rfl) ⟨256238, by rfl⟩ : syracuseStep 341651 = 512477) B512477
theorem B407339 : Blo 179801 407339 := bstep (se 1 (by rfl) ⟨305504, by rfl⟩ : syracuseStep 407339 = 611009) B611009
theorem B309035 : Blo 179801 309035 := bstep (se 1 (by rfl) ⟨231776, by rfl⟩ : syracuseStep 309035 = 463553) B463553
theorem B243643 : Blo 179801 243643 := bstep (se 1 (by rfl) ⟨182732, by rfl⟩ : syracuseStep 243643 = 365465) B365465
theorem B407699 : Blo 179801 407699 := bstep (se 1 (by rfl) ⟨305774, by rfl⟩ : syracuseStep 407699 = 611549) B611549
theorem B309433 : Blo 179801 309433 := bstep (se 2 (by rfl) ⟨116037, by rfl⟩ : syracuseStep 309433 = 232075) B232075
theorem B866497 : Blo 179801 866497 := bstep (se 2 (by rfl) ⟨324936, by rfl⟩ : syracuseStep 866497 = 649873) B649873
theorem B407753 : Blo 179801 407753 := bstep (se 2 (by rfl) ⟨152907, by rfl⟩ : syracuseStep 407753 = 305815) B305815
theorem B2079107 : Blo 179801 2079107 := bstep (se 1 (by rfl) ⟨1559330, by rfl⟩ : syracuseStep 2079107 = 3118661) B3118661
theorem B867131 : Blo 179801 867131 := bstep (se 1 (by rfl) ⟨650348, by rfl⟩ : syracuseStep 867131 = 1300697) B1300697
theorem B310135 : Blo 179801 310135 := bstep (se 1 (by rfl) ⟨232601, by rfl⟩ : syracuseStep 310135 = 465203) B465203
theorem B408455 : Blo 179801 408455 := bstep (se 1 (by rfl) ⟨306341, by rfl⟩ : syracuseStep 408455 = 612683) B612683
theorem B343055 : Blo 179801 343055 := bstep (se 1 (by rfl) ⟨257291, by rfl⟩ : syracuseStep 343055 = 514583) B514583
theorem B408635 : Blo 179801 408635 := bstep (se 1 (by rfl) ⟨306476, by rfl⟩ : syracuseStep 408635 = 612953) B612953
theorem B408761 : Blo 179801 408761 := bstep (se 2 (by rfl) ⟨153285, by rfl⟩ : syracuseStep 408761 = 306571) B306571
theorem B736571 : Blo 179801 736571 := bstep (se 1 (by rfl) ⟨552428, by rfl⟩ : syracuseStep 736571 = 1104857) B1104857
theorem B1555847 : Blo 179801 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B409103 : Blo 179801 409103 := bstep (se 1 (by rfl) ⟨306827, by rfl⟩ : syracuseStep 409103 = 613655) B613655
theorem B409121 : Blo 179801 409121 := bstep (se 2 (by rfl) ⟨153420, by rfl⟩ : syracuseStep 409121 = 306841) B306841
theorem B343595 : Blo 179801 343595 := bstep (se 1 (by rfl) ⟨257696, by rfl⟩ : syracuseStep 343595 = 515393) B515393
theorem B1752677 : Blo 179801 1752677 := bstep (se 4 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 1752677 = 328627) B328627
theorem B179847 : Blo 179801 179847 := bstep (se 1 (by rfl) ⟨134885, by rfl⟩ : syracuseStep 179847 = 269771) B269771
theorem B179855 : Blo 179801 179855 := bstep (se 1 (by rfl) ⟨134891, by rfl⟩ : syracuseStep 179855 = 269783) B269783
theorem B179899 : Blo 179801 179899 := bstep (se 1 (by rfl) ⟨134924, by rfl⟩ : syracuseStep 179899 = 269849) B269849
theorem B179975 : Blo 179801 179975 := bstep (se 1 (by rfl) ⟨134981, by rfl⟩ : syracuseStep 179975 = 269963) B269963
theorem B179983 : Blo 179801 179983 := bstep (se 1 (by rfl) ⟨134987, by rfl⟩ : syracuseStep 179983 = 269975) B269975
theorem B180027 : Blo 179801 180027 := bstep (se 1 (by rfl) ⟨135020, by rfl⟩ : syracuseStep 180027 = 270041) B270041
theorem B409463 : Blo 179801 409463 := bstep (se 1 (by rfl) ⟨307097, by rfl⟩ : syracuseStep 409463 = 614195) B614195
theorem B180103 : Blo 179801 180103 := bstep (se 1 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 180103 = 270155) B270155
theorem B180111 : Blo 179801 180111 := bstep (se 1 (by rfl) ⟨135083, by rfl⟩ : syracuseStep 180111 = 270167) B270167
theorem B769945 : Blo 179801 769945 := bstep (se 2 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 769945 = 577459) B577459
theorem B180155 : Blo 179801 180155 := bstep (se 1 (by rfl) ⟨135116, by rfl⟩ : syracuseStep 180155 = 270233) B270233
theorem B180231 : Blo 179801 180231 := bstep (se 1 (by rfl) ⟨135173, by rfl⟩ : syracuseStep 180231 = 270347) B270347
theorem B180239 : Blo 179801 180239 := bstep (se 1 (by rfl) ⟨135179, by rfl⟩ : syracuseStep 180239 = 270359) B270359
theorem B409643 : Blo 179801 409643 := bstep (se 1 (by rfl) ⟨307232, by rfl⟩ : syracuseStep 409643 = 614465) B614465
theorem B180283 : Blo 179801 180283 := bstep (se 1 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 180283 = 270425) B270425
theorem B180359 : Blo 179801 180359 := bstep (se 1 (by rfl) ⟨135269, by rfl⟩ : syracuseStep 180359 = 270539) B270539
theorem B180367 : Blo 179801 180367 := bstep (se 1 (by rfl) ⟨135275, by rfl⟩ : syracuseStep 180367 = 270551) B270551
theorem B180411 : Blo 179801 180411 := bstep (se 1 (by rfl) ⟨135308, by rfl⟩ : syracuseStep 180411 = 270617) B270617
theorem B180487 : Blo 179801 180487 := bstep (se 1 (by rfl) ⟨135365, by rfl⟩ : syracuseStep 180487 = 270731) B270731
theorem B180495 : Blo 179801 180495 := bstep (se 1 (by rfl) ⟨135371, by rfl⟩ : syracuseStep 180495 = 270743) B270743
theorem B180539 : Blo 179801 180539 := bstep (se 1 (by rfl) ⟨135404, by rfl⟩ : syracuseStep 180539 = 270809) B270809
theorem B3916097 : Blo 179801 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B180615 : Blo 179801 180615 := bstep (se 1 (by rfl) ⟨135461, by rfl⟩ : syracuseStep 180615 = 270923) B270923
theorem B180623 : Blo 179801 180623 := bstep (se 1 (by rfl) ⟨135467, by rfl⟩ : syracuseStep 180623 = 270935) B270935
theorem B410003 : Blo 179801 410003 := bstep (se 1 (by rfl) ⟨307502, by rfl⟩ : syracuseStep 410003 = 615005) B615005
theorem B180667 : Blo 179801 180667 := bstep (se 1 (by rfl) ⟨135500, by rfl⟩ : syracuseStep 180667 = 271001) B271001
theorem B410057 : Blo 179801 410057 := bstep (se 2 (by rfl) ⟨153771, by rfl⟩ : syracuseStep 410057 = 307543) B307543
theorem B180743 : Blo 179801 180743 := bstep (se 1 (by rfl) ⟨135557, by rfl⟩ : syracuseStep 180743 = 271115) B271115
theorem B180751 : Blo 179801 180751 := bstep (se 1 (by rfl) ⟨135563, by rfl⟩ : syracuseStep 180751 = 271127) B271127
theorem B180795 : Blo 179801 180795 := bstep (se 1 (by rfl) ⟨135596, by rfl⟩ : syracuseStep 180795 = 271193) B271193
theorem B180871 : Blo 179801 180871 := bstep (se 1 (by rfl) ⟨135653, by rfl⟩ : syracuseStep 180871 = 271307) B271307
theorem B344711 : Blo 179801 344711 := bstep (se 1 (by rfl) ⟨258533, by rfl⟩ : syracuseStep 344711 = 517067) B517067
theorem B180879 : Blo 179801 180879 := bstep (se 1 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 180879 = 271319) B271319
theorem B180923 : Blo 179801 180923 := bstep (se 1 (by rfl) ⟨135692, by rfl⟩ : syracuseStep 180923 = 271385) B271385
theorem B3556057 : Blo 179801 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B180999 : Blo 179801 180999 := bstep (se 1 (by rfl) ⟨135749, by rfl⟩ : syracuseStep 180999 = 271499) B271499
theorem B181007 : Blo 179801 181007 := bstep (se 1 (by rfl) ⟨135755, by rfl⟩ : syracuseStep 181007 = 271511) B271511
theorem B181051 : Blo 179801 181051 := bstep (se 1 (by rfl) ⟨135788, by rfl⟩ : syracuseStep 181051 = 271577) B271577
theorem B2802521 : Blo 179801 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B181127 : Blo 179801 181127 := bstep (se 1 (by rfl) ⟨135845, by rfl⟩ : syracuseStep 181127 = 271691) B271691
theorem B181135 : Blo 179801 181135 := bstep (se 1 (by rfl) ⟨135851, by rfl⟩ : syracuseStep 181135 = 271703) B271703
theorem B181179 : Blo 179801 181179 := bstep (se 1 (by rfl) ⟨135884, by rfl⟩ : syracuseStep 181179 = 271769) B271769
theorem B181255 : Blo 179801 181255 := bstep (se 1 (by rfl) ⟨135941, by rfl⟩ : syracuseStep 181255 = 271883) B271883
theorem B181263 : Blo 179801 181263 := bstep (se 1 (by rfl) ⟨135947, by rfl⟩ : syracuseStep 181263 = 271895) B271895
theorem B181307 : Blo 179801 181307 := bstep (se 1 (by rfl) ⟨135980, by rfl⟩ : syracuseStep 181307 = 271961) B271961
theorem B771191 : Blo 179801 771191 := bstep (se 1 (by rfl) ⟨578393, by rfl⟩ : syracuseStep 771191 = 1156787) B1156787
theorem B181383 : Blo 179801 181383 := bstep (se 1 (by rfl) ⟨136037, by rfl⟩ : syracuseStep 181383 = 272075) B272075
theorem B410759 : Blo 179801 410759 := bstep (se 1 (by rfl) ⟨308069, by rfl⟩ : syracuseStep 410759 = 616139) B616139
theorem B181391 : Blo 179801 181391 := bstep (se 1 (by rfl) ⟨136043, by rfl⟩ : syracuseStep 181391 = 272087) B272087
theorem B345235 : Blo 179801 345235 := bstep (se 1 (by rfl) ⟨258926, by rfl⟩ : syracuseStep 345235 = 517853) B517853
theorem B181435 : Blo 179801 181435 := bstep (se 1 (by rfl) ⟨136076, by rfl⟩ : syracuseStep 181435 = 272153) B272153
theorem B181511 : Blo 179801 181511 := bstep (se 1 (by rfl) ⟨136133, by rfl⟩ : syracuseStep 181511 = 272267) B272267
theorem B247055 : Blo 179801 247055 := bstep (se 1 (by rfl) ⟨185291, by rfl⟩ : syracuseStep 247055 = 370583) B370583
theorem B181519 : Blo 179801 181519 := bstep (se 1 (by rfl) ⟨136139, by rfl⟩ : syracuseStep 181519 = 272279) B272279
theorem B181563 : Blo 179801 181563 := bstep (se 1 (by rfl) ⟨136172, by rfl⟩ : syracuseStep 181563 = 272345) B272345
theorem B410939 : Blo 179801 410939 := bstep (se 1 (by rfl) ⟨308204, by rfl⟩ : syracuseStep 410939 = 616409) B616409
theorem B181639 : Blo 179801 181639 := bstep (se 1 (by rfl) ⟨136229, by rfl⟩ : syracuseStep 181639 = 272459) B272459
theorem B181647 : Blo 179801 181647 := bstep (se 1 (by rfl) ⟨136235, by rfl⟩ : syracuseStep 181647 = 272471) B272471
theorem B411065 : Blo 179801 411065 := bstep (se 2 (by rfl) ⟨154149, by rfl⟩ : syracuseStep 411065 = 308299) B308299
theorem B181691 : Blo 179801 181691 := bstep (se 1 (by rfl) ⟨136268, by rfl⟩ : syracuseStep 181691 = 272537) B272537
theorem B181767 : Blo 179801 181767 := bstep (se 1 (by rfl) ⟨136325, by rfl⟩ : syracuseStep 181767 = 272651) B272651
theorem B181775 : Blo 179801 181775 := bstep (se 1 (by rfl) ⟨136331, by rfl⟩ : syracuseStep 181775 = 272663) B272663
theorem B181819 : Blo 179801 181819 := bstep (se 1 (by rfl) ⟨136364, by rfl⟩ : syracuseStep 181819 = 272729) B272729
theorem B181895 : Blo 179801 181895 := bstep (se 1 (by rfl) ⟨136421, by rfl⟩ : syracuseStep 181895 = 272843) B272843
theorem B181903 : Blo 179801 181903 := bstep (se 1 (by rfl) ⟨136427, by rfl⟩ : syracuseStep 181903 = 272855) B272855
theorem B6670001 : Blo 179801 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B181947 : Blo 179801 181947 := bstep (se 1 (by rfl) ⟨136460, by rfl⟩ : syracuseStep 181947 = 272921) B272921
theorem B182023 : Blo 179801 182023 := bstep (se 1 (by rfl) ⟨136517, by rfl⟩ : syracuseStep 182023 = 273035) B273035
theorem B182031 : Blo 179801 182031 := bstep (se 1 (by rfl) ⟨136523, by rfl⟩ : syracuseStep 182031 = 273047) B273047
theorem B411407 : Blo 179801 411407 := bstep (se 1 (by rfl) ⟨308555, by rfl⟩ : syracuseStep 411407 = 617111) B617111
theorem B411425 : Blo 179801 411425 := bstep (se 2 (by rfl) ⟨154284, by rfl⟩ : syracuseStep 411425 = 308569) B308569
theorem B182075 : Blo 179801 182075 := bstep (se 1 (by rfl) ⟨136556, by rfl⟩ : syracuseStep 182075 = 273113) B273113
theorem B476987 : Blo 179801 476987 := bstep (se 1 (by rfl) ⟨357740, by rfl⟩ : syracuseStep 476987 = 715481) B715481
theorem B182151 : Blo 179801 182151 := bstep (se 1 (by rfl) ⟨136613, by rfl⟩ : syracuseStep 182151 = 273227) B273227
theorem B182159 : Blo 179801 182159 := bstep (se 1 (by rfl) ⟨136619, by rfl⟩ : syracuseStep 182159 = 273239) B273239
theorem B608147 : Blo 179801 608147 := bstep (se 1 (by rfl) ⟨456110, by rfl⟩ : syracuseStep 608147 = 912221) B912221
theorem B182203 : Blo 179801 182203 := bstep (se 1 (by rfl) ⟨136652, by rfl⟩ : syracuseStep 182203 = 273305) B273305
theorem B182279 : Blo 179801 182279 := bstep (se 1 (by rfl) ⟨136709, by rfl⟩ : syracuseStep 182279 = 273419) B273419
theorem B182287 : Blo 179801 182287 := bstep (se 1 (by rfl) ⟨136715, by rfl⟩ : syracuseStep 182287 = 273431) B273431
theorem B182331 : Blo 179801 182331 := bstep (se 1 (by rfl) ⟨136748, by rfl⟩ : syracuseStep 182331 = 273497) B273497
theorem B411767 : Blo 179801 411767 := bstep (se 1 (by rfl) ⟨308825, by rfl⟩ : syracuseStep 411767 = 617651) B617651
theorem B182407 : Blo 179801 182407 := bstep (se 1 (by rfl) ⟨136805, by rfl⟩ : syracuseStep 182407 = 273611) B273611
theorem B182415 : Blo 179801 182415 := bstep (se 1 (by rfl) ⟨136811, by rfl⟩ : syracuseStep 182415 = 273623) B273623
theorem B182459 : Blo 179801 182459 := bstep (se 1 (by rfl) ⟨136844, by rfl⟩ : syracuseStep 182459 = 273689) B273689
theorem B182535 : Blo 179801 182535 := bstep (se 1 (by rfl) ⟨136901, by rfl⟩ : syracuseStep 182535 = 273803) B273803
theorem B248071 : Blo 179801 248071 := bstep (se 1 (by rfl) ⟨186053, by rfl⟩ : syracuseStep 248071 = 372107) B372107
theorem B182543 : Blo 179801 182543 := bstep (se 1 (by rfl) ⟨136907, by rfl⟩ : syracuseStep 182543 = 273815) B273815
theorem B411947 : Blo 179801 411947 := bstep (se 1 (by rfl) ⟨308960, by rfl⟩ : syracuseStep 411947 = 617921) B617921
theorem B346427 : Blo 179801 346427 := bstep (se 1 (by rfl) ⟨259820, by rfl⟩ : syracuseStep 346427 = 519641) B519641
theorem B182587 : Blo 179801 182587 := bstep (se 1 (by rfl) ⟨136940, by rfl⟩ : syracuseStep 182587 = 273881) B273881
theorem B182663 : Blo 179801 182663 := bstep (se 1 (by rfl) ⟨136997, by rfl⟩ : syracuseStep 182663 = 273995) B273995
theorem B182671 : Blo 179801 182671 := bstep (se 1 (by rfl) ⟨137003, by rfl⟩ : syracuseStep 182671 = 274007) B274007
theorem B182715 : Blo 179801 182715 := bstep (se 1 (by rfl) ⟨137036, by rfl⟩ : syracuseStep 182715 = 274073) B274073
theorem B182791 : Blo 179801 182791 := bstep (se 1 (by rfl) ⟨137093, by rfl⟩ : syracuseStep 182791 = 274187) B274187
theorem B182799 : Blo 179801 182799 := bstep (se 1 (by rfl) ⟨137099, by rfl⟩ : syracuseStep 182799 = 274199) B274199
theorem B182843 : Blo 179801 182843 := bstep (se 1 (by rfl) ⟨137132, by rfl⟩ : syracuseStep 182843 = 274265) B274265
theorem B182919 : Blo 179801 182919 := bstep (se 1 (by rfl) ⟨137189, by rfl⟩ : syracuseStep 182919 = 274379) B274379
theorem B182927 : Blo 179801 182927 := bstep (se 1 (by rfl) ⟨137195, by rfl⟩ : syracuseStep 182927 = 274391) B274391
theorem B412307 : Blo 179801 412307 := bstep (se 1 (by rfl) ⟨309230, by rfl⟩ : syracuseStep 412307 = 618461) B618461
theorem B182971 : Blo 179801 182971 := bstep (se 1 (by rfl) ⟨137228, by rfl⟩ : syracuseStep 182971 = 274457) B274457
theorem B1231553 : Blo 179801 1231553 := bstep (se 2 (by rfl) ⟨461832, by rfl⟩ : syracuseStep 1231553 = 923665) B923665
theorem B412361 : Blo 179801 412361 := bstep (se 2 (by rfl) ⟨154635, by rfl⟩ : syracuseStep 412361 = 309271) B309271
theorem B183047 : Blo 179801 183047 := bstep (se 1 (by rfl) ⟨137285, by rfl⟩ : syracuseStep 183047 = 274571) B274571
theorem B183055 : Blo 179801 183055 := bstep (se 1 (by rfl) ⟨137291, by rfl⟩ : syracuseStep 183055 = 274583) B274583
theorem B346913 : Blo 179801 346913 := bstep (se 2 (by rfl) ⟨130092, by rfl⟩ : syracuseStep 346913 = 260185) B260185
theorem B183099 : Blo 179801 183099 := bstep (se 1 (by rfl) ⟨137324, by rfl⟩ : syracuseStep 183099 = 274649) B274649
theorem B183175 : Blo 179801 183175 := bstep (se 1 (by rfl) ⟨137381, by rfl⟩ : syracuseStep 183175 = 274763) B274763
theorem B183183 : Blo 179801 183183 := bstep (se 1 (by rfl) ⟨137387, by rfl⟩ : syracuseStep 183183 = 274775) B274775
theorem B1100729 : Blo 179801 1100729 := bstep (se 2 (by rfl) ⟨412773, by rfl⟩ : syracuseStep 1100729 = 825547) B825547
theorem B183227 : Blo 179801 183227 := bstep (se 1 (by rfl) ⟨137420, by rfl⟩ : syracuseStep 183227 = 274841) B274841
theorem B183303 : Blo 179801 183303 := bstep (se 1 (by rfl) ⟨137477, by rfl⟩ : syracuseStep 183303 = 274955) B274955
theorem B183311 : Blo 179801 183311 := bstep (se 1 (by rfl) ⟨137483, by rfl⟩ : syracuseStep 183311 = 274967) B274967
theorem B347179 : Blo 179801 347179 := bstep (se 1 (by rfl) ⟨260384, by rfl⟩ : syracuseStep 347179 = 520769) B520769
theorem B183355 : Blo 179801 183355 := bstep (se 1 (by rfl) ⟨137516, by rfl⟩ : syracuseStep 183355 = 275033) B275033
theorem B183431 : Blo 179801 183431 := bstep (se 1 (by rfl) ⟨137573, by rfl⟩ : syracuseStep 183431 = 275147) B275147
theorem B183439 : Blo 179801 183439 := bstep (se 1 (by rfl) ⟨137579, by rfl⟩ : syracuseStep 183439 = 275159) B275159
theorem B183483 : Blo 179801 183483 := bstep (se 1 (by rfl) ⟨137612, by rfl⟩ : syracuseStep 183483 = 275225) B275225
theorem B183559 : Blo 179801 183559 := bstep (se 1 (by rfl) ⟨137669, by rfl⟩ : syracuseStep 183559 = 275339) B275339
theorem B609551 : Blo 179801 609551 := bstep (se 1 (by rfl) ⟨457163, by rfl⟩ : syracuseStep 609551 = 914327) B914327
theorem B183567 : Blo 179801 183567 := bstep (se 1 (by rfl) ⟨137675, by rfl⟩ : syracuseStep 183567 = 275351) B275351
theorem B183611 : Blo 179801 183611 := bstep (se 1 (by rfl) ⟨137708, by rfl⟩ : syracuseStep 183611 = 275417) B275417
theorem B413063 : Blo 179801 413063 := bstep (se 1 (by rfl) ⟨309797, by rfl⟩ : syracuseStep 413063 = 619595) B619595
theorem B183687 : Blo 179801 183687 := bstep (se 1 (by rfl) ⟨137765, by rfl⟩ : syracuseStep 183687 = 275531) B275531
theorem B183695 : Blo 179801 183695 := bstep (se 1 (by rfl) ⟨137771, by rfl⟩ : syracuseStep 183695 = 275543) B275543
theorem B183739 : Blo 179801 183739 := bstep (se 1 (by rfl) ⟨137804, by rfl⟩ : syracuseStep 183739 = 275609) B275609
theorem B609821 : Blo 179801 609821 := bstep (se 3 (by rfl) ⟨114341, by rfl⟩ : syracuseStep 609821 = 228683) B228683
theorem B413243 : Blo 179801 413243 := bstep (se 1 (by rfl) ⟨309932, by rfl⟩ : syracuseStep 413243 = 619865) B619865
theorem B740983 : Blo 179801 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B413369 : Blo 179801 413369 := bstep (se 2 (by rfl) ⟨155013, by rfl⟩ : syracuseStep 413369 = 310027) B310027
theorem B479009 : Blo 179801 479009 := bstep (se 2 (by rfl) ⟨179628, by rfl⟩ : syracuseStep 479009 = 359257) B359257
theorem B1036091 : Blo 179801 1036091 := bstep (se 1 (by rfl) ⟨777068, by rfl⟩ : syracuseStep 1036091 = 1554137) B1554137
theorem B1986677 : Blo 179801 1986677 := bstep (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) B186251
theorem B348295 : Blo 179801 348295 := bstep (se 1 (by rfl) ⟨261221, by rfl⟩ : syracuseStep 348295 = 522443) B522443
theorem B872819 : Blo 179801 872819 := bstep (se 1 (by rfl) ⟨654614, by rfl⟩ : syracuseStep 872819 = 1309229) B1309229
theorem B348857 : Blo 179801 348857 := bstep (se 2 (by rfl) ⟨130821, by rfl⟩ : syracuseStep 348857 = 261643) B261643
theorem B611225 : Blo 179801 611225 := bstep (se 2 (by rfl) ⟨229209, by rfl⟩ : syracuseStep 611225 = 458419) B458419
theorem B1037549 : Blo 179801 1037549 := bstep (se 3 (by rfl) ⟨194540, by rfl⟩ : syracuseStep 1037549 = 389081) B389081
theorem B2119121 : Blo 179801 2119121 := bstep (se 2 (by rfl) ⟨794670, by rfl⟩ : syracuseStep 2119121 = 1589341) B1589341
theorem B611927 : Blo 179801 611927 := bstep (se 1 (by rfl) ⟨458945, by rfl⟩ : syracuseStep 611927 = 917891) B917891
theorem B972407 : Blo 179801 972407 := bstep (se 1 (by rfl) ⟨729305, by rfl⟩ : syracuseStep 972407 = 1458611) B1458611
theorem B743303 : Blo 179801 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B612413 : Blo 179801 612413 := bstep (se 3 (by rfl) ⟨114827, by rfl⟩ : syracuseStep 612413 = 229655) B229655
theorem B1169963 : Blo 179801 1169963 := bstep (se 1 (by rfl) ⟨877472, by rfl⟩ : syracuseStep 1169963 = 1754945) B1754945
theorem B219791 : Blo 179801 219791 := bstep (se 1 (by rfl) ⟨164843, by rfl⟩ : syracuseStep 219791 = 329687) B329687
theorem B875279 : Blo 179801 875279 := bstep (se 1 (by rfl) ⟨656459, by rfl⟩ : syracuseStep 875279 = 1312919) B1312919
theorem B2644751 : Blo 179801 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B973619 : Blo 179801 973619 := bstep (se 1 (by rfl) ⟨730214, by rfl⟩ : syracuseStep 973619 = 1460429) B1460429
theorem B548041 : Blo 179801 548041 := bstep (se 2 (by rfl) ⟨205515, by rfl⟩ : syracuseStep 548041 = 411031) B411031
theorem B941401 : Blo 179801 941401 := bstep (se 2 (by rfl) ⟨353025, by rfl⟩ : syracuseStep 941401 = 706051) B706051
theorem B613817 : Blo 179801 613817 := bstep (se 2 (by rfl) ⟨230181, by rfl⟩ : syracuseStep 613817 = 460363) B460363
theorem B515585 : Blo 179801 515585 := bstep (se 2 (by rfl) ⟨193344, by rfl⟩ : syracuseStep 515585 = 386689) B386689
theorem B876433 : Blo 179801 876433 := bstep (se 2 (by rfl) ⟨328662, by rfl⟩ : syracuseStep 876433 = 657325) B657325
theorem B516041 : Blo 179801 516041 := bstep (se 2 (by rfl) ⟨193515, by rfl⟩ : syracuseStep 516041 = 387031) B387031
theorem B876509 : Blo 179801 876509 := bstep (se 3 (by rfl) ⟨164345, by rfl⟩ : syracuseStep 876509 = 328691) B328691
theorem B614411 : Blo 179801 614411 := bstep (se 1 (by rfl) ⟨460808, by rfl⟩ : syracuseStep 614411 = 921617) B921617
theorem B385067 : Blo 179801 385067 := bstep (se 1 (by rfl) ⟨288800, by rfl⟩ : syracuseStep 385067 = 577601) B577601
theorem B614519 : Blo 179801 614519 := bstep (se 1 (by rfl) ⟨460889, by rfl⟩ : syracuseStep 614519 = 921779) B921779
theorem B516395 : Blo 179801 516395 := bstep (se 1 (by rfl) ⟨387296, by rfl⟩ : syracuseStep 516395 = 774593) B774593
theorem B2089475 : Blo 179801 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B582187 : Blo 179801 582187 := bstep (se 1 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 582187 = 873281) B873281
theorem B516793 : Blo 179801 516793 := bstep (se 2 (by rfl) ⟨193797, by rfl⟩ : syracuseStep 516793 = 387595) B387595
theorem B615113 : Blo 179801 615113 := bstep (se 2 (by rfl) ⟨230667, by rfl⟩ : syracuseStep 615113 = 461335) B461335
theorem B1467173 : Blo 179801 1467173 := bstep (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) B275095
theorem B648071 : Blo 179801 648071 := bstep (se 1 (by rfl) ⟨486053, by rfl⟩ : syracuseStep 648071 = 972107) B972107
theorem B615815 : Blo 179801 615815 := bstep (se 1 (by rfl) ⟨461861, by rfl⟩ : syracuseStep 615815 = 923723) B923723
theorem B8381875 : Blo 179801 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B1041923 : Blo 179801 1041923 := bstep (se 1 (by rfl) ⟨781442, by rfl⟩ : syracuseStep 1041923 = 1562885) B1562885
theorem B1762859 : Blo 179801 1762859 := bstep (se 1 (by rfl) ⟨1322144, by rfl⟩ : syracuseStep 1762859 = 2644289) B2644289
theorem B386707 : Blo 179801 386707 := bstep (se 1 (by rfl) ⟨290030, by rfl⟩ : syracuseStep 386707 = 580061) B580061
theorem B616193 : Blo 179801 616193 := bstep (se 2 (by rfl) ⟨231072, by rfl⟩ : syracuseStep 616193 = 462145) B462145
theorem B550775 : Blo 179801 550775 := bstep (se 1 (by rfl) ⟨413081, by rfl⟩ : syracuseStep 550775 = 826163) B826163
theorem B911249 : Blo 179801 911249 := bstep (se 2 (by rfl) ⟨341718, by rfl⟩ : syracuseStep 911249 = 683437) B683437
theorem B518035 : Blo 179801 518035 := bstep (se 1 (by rfl) ⟨388526, by rfl⟩ : syracuseStep 518035 = 777053) B777053
theorem B1042379 : Blo 179801 1042379 := bstep (se 1 (by rfl) ⟨781784, by rfl⟩ : syracuseStep 1042379 = 1563569) B1563569
theorem B1959997 : Blo 179801 1959997 := bstep (se 3 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 1959997 = 734999) B734999
theorem B780349 : Blo 179801 780349 := bstep (se 3 (by rfl) ⟨146315, by rfl⟩ : syracuseStep 780349 = 292631) B292631
theorem B256375 : Blo 179801 256375 := bstep (se 1 (by rfl) ⟨192281, by rfl⟩ : syracuseStep 256375 = 384563) B384563
theorem B780691 : Blo 179801 780691 := bstep (se 1 (by rfl) ⟨585518, by rfl⟩ : syracuseStep 780691 = 1171037) B1171037
theorem B617003 : Blo 179801 617003 := bstep (se 1 (by rfl) ⟨462752, by rfl⟩ : syracuseStep 617003 = 925505) B925505
theorem B1174135 : Blo 179801 1174135 := bstep (se 1 (by rfl) ⟨880601, by rfl⟩ : syracuseStep 1174135 = 1761203) B1761203
theorem B1043063 : Blo 179801 1043063 := bstep (se 1 (by rfl) ⟨782297, by rfl⟩ : syracuseStep 1043063 = 1564595) B1564595
theorem B879277 : Blo 179801 879277 := bstep (se 3 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 879277 = 329729) B329729
theorem B256699 : Blo 179801 256699 := bstep (se 1 (by rfl) ⟨192524, by rfl⟩ : syracuseStep 256699 = 385049) B385049
theorem B3893953 : Blo 179801 3893953 := bstep (se 2 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 3893953 = 2920465) B2920465
theorem B682937 : Blo 179801 682937 := bstep (se 2 (by rfl) ⟨256101, by rfl⟩ : syracuseStep 682937 = 512203) B512203
theorem B879569 : Blo 179801 879569 := bstep (se 2 (by rfl) ⟨329838, by rfl⟩ : syracuseStep 879569 = 659677) B659677
theorem B977923 : Blo 179801 977923 := bstep (se 1 (by rfl) ⟨733442, by rfl⟩ : syracuseStep 977923 = 1466885) B1466885
theorem B257195 : Blo 179801 257195 := bstep (se 1 (by rfl) ⟨192896, by rfl⟩ : syracuseStep 257195 = 385793) B385793
theorem B290063 : Blo 179801 290063 := bstep (se 1 (by rfl) ⟨217547, by rfl⟩ : syracuseStep 290063 = 435095) B435095
theorem B978461 : Blo 179801 978461 := bstep (se 3 (by rfl) ⟨183461, by rfl⟩ : syracuseStep 978461 = 366923) B366923
theorem B519709 : Blo 179801 519709 := bstep (se 3 (by rfl) ⟨97445, by rfl⟩ : syracuseStep 519709 = 194891) B194891
theorem B519767 : Blo 179801 519767 := bstep (se 1 (by rfl) ⟨389825, by rfl⟩ : syracuseStep 519767 = 779651) B779651
theorem B290575 : Blo 179801 290575 := bstep (se 1 (by rfl) ⟨217931, by rfl⟩ : syracuseStep 290575 = 435863) B435863
theorem B618299 : Blo 179801 618299 := bstep (se 1 (by rfl) ⟨463724, by rfl⟩ : syracuseStep 618299 = 927449) B927449
theorem B683923 : Blo 179801 683923 := bstep (se 1 (by rfl) ⟨512942, by rfl⟩ : syracuseStep 683923 = 1025885) B1025885
theorem B913355 : Blo 179801 913355 := bstep (se 1 (by rfl) ⟨685016, by rfl⟩ : syracuseStep 913355 = 1370033) B1370033
theorem B8876213 : Blo 179801 8876213 := bstep (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) B832145
theorem B585929 : Blo 179801 585929 := bstep (se 2 (by rfl) ⟨219723, by rfl⟩ : syracuseStep 585929 = 439447) B439447
theorem B1568969 : Blo 179801 1568969 := bstep (se 2 (by rfl) ⟨588363, by rfl⟩ : syracuseStep 1568969 = 1176727) B1176727
theorem B913679 : Blo 179801 913679 := bstep (se 1 (by rfl) ⟨685259, by rfl⟩ : syracuseStep 913679 = 1370519) B1370519
theorem B618785 : Blo 179801 618785 := bstep (se 2 (by rfl) ⟨232044, by rfl⟩ : syracuseStep 618785 = 464089) B464089
theorem B455179 : Blo 179801 455179 := bstep (se 1 (by rfl) ⟨341384, by rfl⟩ : syracuseStep 455179 = 682769) B682769
theorem B1045021 : Blo 179801 1045021 := bstep (se 3 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 1045021 = 391883) B391883
theorem B979499 : Blo 179801 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B455321 : Blo 179801 455321 := bstep (se 2 (by rfl) ⟨170745, by rfl⟩ : syracuseStep 455321 = 341491) B341491
theorem B258761 : Blo 179801 258761 := bstep (se 2 (by rfl) ⟨97035, by rfl⟩ : syracuseStep 258761 = 194071) B194071
theorem B291529 : Blo 179801 291529 := bstep (se 2 (by rfl) ⟨109323, by rfl⟩ : syracuseStep 291529 = 218647) B218647
theorem B455483 : Blo 179801 455483 := bstep (se 1 (by rfl) ⟨341612, by rfl⟩ : syracuseStep 455483 = 683225) B683225
theorem B619379 : Blo 179801 619379 := bstep (se 1 (by rfl) ⟨464534, by rfl⟩ : syracuseStep 619379 = 929069) B929069
theorem B291703 : Blo 179801 291703 := bstep (se 1 (by rfl) ⟨218777, by rfl⟩ : syracuseStep 291703 = 437555) B437555
theorem B1045547 : Blo 179801 1045547 := bstep (se 1 (by rfl) ⟨784160, by rfl⟩ : syracuseStep 1045547 = 1568321) B1568321
theorem B455827 : Blo 179801 455827 := bstep (se 1 (by rfl) ⟨341870, by rfl⟩ : syracuseStep 455827 = 683741) B683741
theorem B390329 : Blo 179801 390329 := bstep (se 2 (by rfl) ⟨146373, by rfl⟩ : syracuseStep 390329 = 292747) B292747
theorem B521417 : Blo 179801 521417 := bstep (se 2 (by rfl) ⟨195531, by rfl⟩ : syracuseStep 521417 = 391063) B391063
theorem B259319 : Blo 179801 259319 := bstep (se 1 (by rfl) ⟨194489, by rfl⟩ : syracuseStep 259319 = 388979) B388979
theorem B455969 : Blo 179801 455969 := bstep (se 2 (by rfl) ⟨170988, by rfl⟩ : syracuseStep 455969 = 341977) B341977
theorem B259627 : Blo 179801 259627 := bstep (se 1 (by rfl) ⟨194720, by rfl⟩ : syracuseStep 259627 = 389441) B389441
theorem B685655 : Blo 179801 685655 := bstep (se 1 (by rfl) ⟨514241, by rfl⟩ : syracuseStep 685655 = 1028483) B1028483
theorem B3995237 : Blo 179801 3995237 := bstep (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) B749107
theorem B915137 : Blo 179801 915137 := bstep (se 2 (by rfl) ⟨343176, by rfl⟩ : syracuseStep 915137 = 686353) B686353
theorem B194447 : Blo 179801 194447 := bstep (se 1 (by rfl) ⟨145835, by rfl⟩ : syracuseStep 194447 = 291671) B291671
theorem B784313 : Blo 179801 784313 := bstep (se 2 (by rfl) ⟨294117, by rfl⟩ : syracuseStep 784313 = 588235) B588235
theorem B325577 : Blo 179801 325577 := bstep (se 2 (by rfl) ⟨122091, by rfl⟩ : syracuseStep 325577 = 244183) B244183
theorem B292879 : Blo 179801 292879 := bstep (se 1 (by rfl) ⟨219659, by rfl⟩ : syracuseStep 292879 = 439319) B439319
theorem B260111 : Blo 179801 260111 := bstep (se 1 (by rfl) ⟨195083, by rfl⟩ : syracuseStep 260111 = 390167) B390167
theorem B1112093 : Blo 179801 1112093 := bstep (se 3 (by rfl) ⟨208517, by rfl⟩ : syracuseStep 1112093 = 417035) B417035
theorem B522283 : Blo 179801 522283 := bstep (se 1 (by rfl) ⟨391712, by rfl⟩ : syracuseStep 522283 = 783425) B783425
theorem B686141 : Blo 179801 686141 := bstep (se 3 (by rfl) ⟨128651, by rfl⟩ : syracuseStep 686141 = 257303) B257303
theorem B2652277 : Blo 179801 2652277 := bstep (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) B248651
theorem B981229 : Blo 179801 981229 := bstep (se 3 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 981229 = 367961) B367961
theorem B456961 : Blo 179801 456961 := bstep (se 2 (by rfl) ⟨171360, by rfl⟩ : syracuseStep 456961 = 342721) B342721
theorem B391439 : Blo 179801 391439 := bstep (se 1 (by rfl) ⟨293579, by rfl⟩ : syracuseStep 391439 = 587159) B587159
theorem B1669409 : Blo 179801 1669409 := bstep (se 2 (by rfl) ⟨626028, by rfl⟩ : syracuseStep 1669409 = 1252057) B1252057
theorem B522557 : Blo 179801 522557 := bstep (se 3 (by rfl) ⟨97979, by rfl⟩ : syracuseStep 522557 = 195959) B195959
theorem B489881 : Blo 179801 489881 := bstep (se 2 (by rfl) ⟨183705, by rfl⟩ : syracuseStep 489881 = 367411) B367411
theorem B588185 : Blo 179801 588185 := bstep (se 2 (by rfl) ⟨220569, by rfl⟩ : syracuseStep 588185 = 441139) B441139
theorem B522899 : Blo 179801 522899 := bstep (se 1 (by rfl) ⟨392174, by rfl⟩ : syracuseStep 522899 = 784349) B784349
theorem B391969 : Blo 179801 391969 := bstep (se 2 (by rfl) ⟨146988, by rfl⟩ : syracuseStep 391969 = 293977) B293977
theorem B326443 : Blo 179801 326443 := bstep (se 1 (by rfl) ⟨244832, by rfl⟩ : syracuseStep 326443 = 489665) B489665
theorem B457559 : Blo 179801 457559 := bstep (se 1 (by rfl) ⟨343169, by rfl⟩ : syracuseStep 457559 = 686339) B686339
theorem B260983 : Blo 179801 260983 := bstep (se 1 (by rfl) ⟨195737, by rfl⟩ : syracuseStep 260983 = 391475) B391475
theorem B916433 : Blo 179801 916433 := bstep (se 2 (by rfl) ⟨343662, by rfl⟩ : syracuseStep 916433 = 687325) B687325
theorem B228359 : Blo 179801 228359 := bstep (se 1 (by rfl) ⟨171269, by rfl⟩ : syracuseStep 228359 = 342539) B342539
theorem B457771 : Blo 179801 457771 := bstep (se 1 (by rfl) ⟨343328, by rfl⟩ : syracuseStep 457771 = 686657) B686657
theorem B195643 : Blo 179801 195643 := bstep (se 1 (by rfl) ⟨146732, by rfl⟩ : syracuseStep 195643 = 293465) B293465
theorem B326803 : Blo 179801 326803 := bstep (se 1 (by rfl) ⟨245102, by rfl⟩ : syracuseStep 326803 = 490205) B490205
theorem B457913 : Blo 179801 457913 := bstep (se 2 (by rfl) ⟨171717, by rfl⟩ : syracuseStep 457913 = 343435) B343435
theorem B229007 : Blo 179801 229007 := bstep (se 1 (by rfl) ⟨171755, by rfl⟩ : syracuseStep 229007 = 343511) B343511
theorem B1114003 : Blo 179801 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B229807 : Blo 179801 229807 := bstep (se 1 (by rfl) ⟨172355, by rfl⟩ : syracuseStep 229807 = 344711) B344711
theorem B1180169 : Blo 179801 1180169 := bstep (se 2 (by rfl) ⟨442563, by rfl⟩ : syracuseStep 1180169 = 885127) B885127
theorem B689057 : Blo 179801 689057 := bstep (se 2 (by rfl) ⟨258396, by rfl⟩ : syracuseStep 689057 = 516793) B516793
theorem B459695 : Blo 179801 459695 := bstep (se 1 (by rfl) ⟨344771, by rfl⟩ : syracuseStep 459695 = 689543) B689543
theorem B1377323 : Blo 179801 1377323 := bstep (se 1 (by rfl) ⟨1032992, by rfl⟩ : syracuseStep 1377323 = 2065985) B2065985
theorem B1181147 : Blo 179801 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B460313 : Blo 179801 460313 := bstep (se 2 (by rfl) ⟨172617, by rfl⟩ : syracuseStep 460313 = 345235) B345235
theorem B230951 : Blo 179801 230951 := bstep (se 1 (by rfl) ⟨173213, by rfl⟩ : syracuseStep 230951 = 346427) B346427
theorem B919187 : Blo 179801 919187 := bstep (se 1 (by rfl) ⟨689390, by rfl⟩ : syracuseStep 919187 = 1378781) B1378781
theorem B821035 : Blo 179801 821035 := bstep (se 1 (by rfl) ⟨615776, by rfl⟩ : syracuseStep 821035 = 1231553) B1231553
theorem B231275 : Blo 179801 231275 := bstep (se 1 (by rfl) ⟨173456, by rfl⟩ : syracuseStep 231275 = 346913) B346913
theorem B690029 : Blo 179801 690029 := bstep (se 3 (by rfl) ⟨129380, by rfl⟩ : syracuseStep 690029 = 258761) B258761
theorem B11175833 : Blo 179801 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B7473389 : Blo 179801 7473389 := bstep (se 3 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 7473389 = 2802521) B2802521
theorem B690713 : Blo 179801 690713 := bstep (se 2 (by rfl) ⟨259017, by rfl⟩ : syracuseStep 690713 = 518035) B518035
theorem B690727 : Blo 179801 690727 := bstep (se 1 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 690727 = 1036091) B1036091
theorem B658219 : Blo 179801 658219 := bstep (se 1 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 658219 = 987329) B987329
theorem B330761 : Blo 179801 330761 := bstep (se 2 (by rfl) ⟨124035, by rfl⟩ : syracuseStep 330761 = 248071) B248071
theorem B232571 : Blo 179801 232571 := bstep (se 1 (by rfl) ⟨174428, by rfl⟩ : syracuseStep 232571 = 348857) B348857
theorem B691517 : Blo 179801 691517 := bstep (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) B259319
theorem B691699 : Blo 179801 691699 := bstep (se 1 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 691699 = 1037549) B1037549
theorem B1412747 : Blo 179801 1412747 := bstep (se 1 (by rfl) ⟨1059560, by rfl⟩ : syracuseStep 1412747 = 2119121) B2119121
theorem B1314593 : Blo 179801 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B462905 : Blo 179801 462905 := bstep (se 2 (by rfl) ⟨173589, by rfl⟩ : syracuseStep 462905 = 347179) B347179
theorem B2101565 : Blo 179801 2101565 := bstep (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) B788087
theorem B627385 : Blo 179801 627385 := bstep (se 2 (by rfl) ⟨235269, by rfl⟩ : syracuseStep 627385 = 470539) B470539
theorem B692945 : Blo 179801 692945 := bstep (se 2 (by rfl) ⟨259854, by rfl⟩ : syracuseStep 692945 = 519709) B519709
theorem B987977 : Blo 179801 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B1184887 : Blo 179801 1184887 := bstep (se 1 (by rfl) ⟨888665, by rfl⟩ : syracuseStep 1184887 = 1777331) B1777331
theorem B660727 : Blo 179801 660727 := bstep (se 1 (by rfl) ⟨495545, by rfl⟩ : syracuseStep 660727 = 991091) B991091
theorem B693629 : Blo 179801 693629 := bstep (se 3 (by rfl) ⟨130055, by rfl⟩ : syracuseStep 693629 = 260111) B260111
theorem B595343 : Blo 179801 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B464393 : Blo 179801 464393 := bstep (se 2 (by rfl) ⟨174147, by rfl⟩ : syracuseStep 464393 = 348295) B348295
theorem B202279 : Blo 179801 202279 := bstep (se 1 (by rfl) ⟨151709, by rfl⟩ : syracuseStep 202279 = 303419) B303419
theorem B432047 : Blo 179801 432047 := bstep (se 1 (by rfl) ⟨324035, by rfl⟩ : syracuseStep 432047 = 648071) B648071
theorem B694615 : Blo 179801 694615 := bstep (se 1 (by rfl) ⟨520961, by rfl⟩ : syracuseStep 694615 = 1041923) B1041923
theorem B268763 : Blo 179801 268763 := bstep (se 1 (by rfl) ⟨201572, by rfl⟩ : syracuseStep 268763 = 403145) B403145
theorem B367183 : Blo 179801 367183 := bstep (se 1 (by rfl) ⟨275387, by rfl⟩ : syracuseStep 367183 = 550775) B550775
theorem B596603 : Blo 179801 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B694919 : Blo 179801 694919 := bstep (se 1 (by rfl) ⟨521189, by rfl⟩ : syracuseStep 694919 = 1042379) B1042379
theorem B924371 : Blo 179801 924371 := bstep (se 1 (by rfl) ⟨693278, by rfl⟩ : syracuseStep 924371 = 1386557) B1386557
theorem B400315 : Blo 179801 400315 := bstep (se 1 (by rfl) ⟨300236, by rfl⟩ : syracuseStep 400315 = 600473) B600473
theorem B695375 : Blo 179801 695375 := bstep (se 1 (by rfl) ⟨521531, by rfl⟩ : syracuseStep 695375 = 1043063) B1043063
theorem B203899 : Blo 179801 203899 := bstep (se 1 (by rfl) ⟨152924, by rfl⟩ : syracuseStep 203899 = 305849) B305849
theorem B5020805 : Blo 179801 5020805 := bstep (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) B941401
theorem B466319 : Blo 179801 466319 := bstep (se 1 (by rfl) ⟨349739, by rfl⟩ : syracuseStep 466319 = 699479) B699479
theorem B269903 : Blo 179801 269903 := bstep (se 1 (by rfl) ⟨202427, by rfl⟩ : syracuseStep 269903 = 404855) B404855
theorem B204367 : Blo 179801 204367 := bstep (se 1 (by rfl) ⟨153275, by rfl⟩ : syracuseStep 204367 = 306551) B306551
theorem B270023 : Blo 179801 270023 := bstep (se 1 (by rfl) ⟨202517, by rfl⟩ : syracuseStep 270023 = 405035) B405035
theorem B270185 : Blo 179801 270185 := bstep (se 2 (by rfl) ⟨101319, by rfl⟩ : syracuseStep 270185 = 202639) B202639
theorem B270263 : Blo 179801 270263 := bstep (se 1 (by rfl) ⟨202697, by rfl⟩ : syracuseStep 270263 = 405395) B405395
theorem B270299 : Blo 179801 270299 := bstep (se 1 (by rfl) ⟨202724, by rfl⟩ : syracuseStep 270299 = 405449) B405449
theorem B204763 : Blo 179801 204763 := bstep (se 1 (by rfl) ⟨153572, by rfl⟩ : syracuseStep 204763 = 307145) B307145
theorem B696377 : Blo 179801 696377 := bstep (se 2 (by rfl) ⟨261141, by rfl⟩ : syracuseStep 696377 = 522283) B522283
theorem B1155329 : Blo 179801 1155329 := bstep (se 2 (by rfl) ⟨433248, by rfl⟩ : syracuseStep 1155329 = 866497) B866497
theorem B1253693 : Blo 179801 1253693 := bstep (se 3 (by rfl) ⟨235067, by rfl⟩ : syracuseStep 1253693 = 470135) B470135
theorem B270767 : Blo 179801 270767 := bstep (se 1 (by rfl) ⟨203075, by rfl⟩ : syracuseStep 270767 = 406151) B406151
theorem B205231 : Blo 179801 205231 := bstep (se 1 (by rfl) ⟨153923, by rfl⟩ : syracuseStep 205231 = 307847) B307847
theorem B303547 : Blo 179801 303547 := bstep (se 1 (by rfl) ⟨227660, by rfl⟩ : syracuseStep 303547 = 455321) B455321
theorem B270857 : Blo 179801 270857 := bstep (se 2 (by rfl) ⟨101571, by rfl⟩ : syracuseStep 270857 = 203143) B203143
theorem B303655 : Blo 179801 303655 := bstep (se 1 (by rfl) ⟨227741, by rfl⟩ : syracuseStep 303655 = 455483) B455483
theorem B270887 : Blo 179801 270887 := bstep (se 1 (by rfl) ⟨203165, by rfl⟩ : syracuseStep 270887 = 406331) B406331
theorem B270971 : Blo 179801 270971 := bstep (se 1 (by rfl) ⟨203228, by rfl⟩ : syracuseStep 270971 = 406457) B406457
theorem B697031 : Blo 179801 697031 := bstep (se 1 (by rfl) ⟨522773, by rfl⟩ : syracuseStep 697031 = 1045547) B1045547
theorem B467671 : Blo 179801 467671 := bstep (se 1 (by rfl) ⟨350753, by rfl⟩ : syracuseStep 467671 = 701507) B701507
theorem B271097 : Blo 179801 271097 := bstep (se 2 (by rfl) ⟨101661, by rfl⟩ : syracuseStep 271097 = 203323) B203323
theorem B271199 : Blo 179801 271199 := bstep (se 1 (by rfl) ⟨203399, by rfl⟩ : syracuseStep 271199 = 406799) B406799
theorem B205663 : Blo 179801 205663 := bstep (se 1 (by rfl) ⟨154247, by rfl⟩ : syracuseStep 205663 = 308495) B308495
theorem B303979 : Blo 179801 303979 := bstep (se 1 (by rfl) ⟨227984, by rfl⟩ : syracuseStep 303979 = 455969) B455969
theorem B271211 : Blo 179801 271211 := bstep (se 1 (by rfl) ⟨203408, by rfl⟩ : syracuseStep 271211 = 406817) B406817
theorem B926639 : Blo 179801 926639 := bstep (se 1 (by rfl) ⟨694979, by rfl⟩ : syracuseStep 926639 = 1389959) B1389959
theorem B435257 : Blo 179801 435257 := bstep (se 2 (by rfl) ⟨163221, by rfl⟩ : syracuseStep 435257 = 326443) B326443
theorem B2663491 : Blo 179801 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B271439 : Blo 179801 271439 := bstep (se 1 (by rfl) ⟨203579, by rfl⟩ : syracuseStep 271439 = 407159) B407159
theorem B271559 : Blo 179801 271559 := bstep (se 1 (by rfl) ⟨203669, by rfl⟩ : syracuseStep 271559 = 407339) B407339
theorem B206023 : Blo 179801 206023 := bstep (se 1 (by rfl) ⟨154517, by rfl⟩ : syracuseStep 206023 = 309035) B309035
theorem B271721 : Blo 179801 271721 := bstep (se 2 (by rfl) ⟨101895, by rfl⟩ : syracuseStep 271721 = 203791) B203791
theorem B271799 : Blo 179801 271799 := bstep (se 1 (by rfl) ⟨203849, by rfl⟩ : syracuseStep 271799 = 407699) B407699
theorem B271835 : Blo 179801 271835 := bstep (se 1 (by rfl) ⟨203876, by rfl⟩ : syracuseStep 271835 = 407753) B407753
theorem B435737 : Blo 179801 435737 := bstep (se 2 (by rfl) ⟨163401, by rfl⟩ : syracuseStep 435737 = 326803) B326803
theorem B1386071 : Blo 179801 1386071 := bstep (se 1 (by rfl) ⟨1039553, by rfl⟩ : syracuseStep 1386071 = 2079107) B2079107
theorem B730721 : Blo 179801 730721 := bstep (se 2 (by rfl) ⟨274020, by rfl⟩ : syracuseStep 730721 = 548041) B548041
theorem B305039 : Blo 179801 305039 := bstep (se 1 (by rfl) ⟨228779, by rfl⟩ : syracuseStep 305039 = 457559) B457559
theorem B272303 : Blo 179801 272303 := bstep (se 1 (by rfl) ⟨204227, by rfl⟩ : syracuseStep 272303 = 408455) B408455
theorem B272393 : Blo 179801 272393 := bstep (se 2 (by rfl) ⟨102147, by rfl⟩ : syracuseStep 272393 = 204295) B204295
theorem B2664485 : Blo 179801 2664485 := bstep (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) B499591
theorem B272423 : Blo 179801 272423 := bstep (se 1 (by rfl) ⟨204317, by rfl⟩ : syracuseStep 272423 = 408635) B408635
theorem B5941349 : Blo 179801 5941349 := bstep (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) B1114003
theorem B305275 : Blo 179801 305275 := bstep (se 1 (by rfl) ⟨228956, by rfl⟩ : syracuseStep 305275 = 457913) B457913
theorem B272507 : Blo 179801 272507 := bstep (se 1 (by rfl) ⟨204380, by rfl⟩ : syracuseStep 272507 = 408761) B408761
theorem B272633 : Blo 179801 272633 := bstep (se 2 (by rfl) ⟨102237, by rfl⟩ : syracuseStep 272633 = 204475) B204475
theorem B272735 : Blo 179801 272735 := bstep (se 1 (by rfl) ⟨204551, by rfl⟩ : syracuseStep 272735 = 409103) B409103
theorem B272747 : Blo 179801 272747 := bstep (se 1 (by rfl) ⟨204560, by rfl⟩ : syracuseStep 272747 = 409121) B409121
theorem B1026593 : Blo 179801 1026593 := bstep (se 2 (by rfl) ⟨384972, by rfl⟩ : syracuseStep 1026593 = 769945) B769945
theorem B272975 : Blo 179801 272975 := bstep (se 1 (by rfl) ⟨204731, by rfl⟩ : syracuseStep 272975 = 409463) B409463
theorem B1485485 : Blo 179801 1485485 := bstep (se 3 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 1485485 = 557057) B557057
theorem B273095 : Blo 179801 273095 := bstep (se 1 (by rfl) ⟨204821, by rfl⟩ : syracuseStep 273095 = 409643) B409643
theorem B273257 : Blo 179801 273257 := bstep (se 2 (by rfl) ⟨102471, by rfl⟩ : syracuseStep 273257 = 204943) B204943
theorem B273335 : Blo 179801 273335 := bstep (se 1 (by rfl) ⟨205001, by rfl⟩ : syracuseStep 273335 = 410003) B410003
theorem B306139 : Blo 179801 306139 := bstep (se 1 (by rfl) ⟨229604, by rfl⟩ : syracuseStep 306139 = 459209) B459209
theorem B273371 : Blo 179801 273371 := bstep (se 1 (by rfl) ⟨205028, by rfl⟩ : syracuseStep 273371 = 410057) B410057
theorem B928921 : Blo 179801 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B273839 : Blo 179801 273839 := bstep (se 1 (by rfl) ⟨205379, by rfl⟩ : syracuseStep 273839 = 410759) B410759
theorem B273929 : Blo 179801 273929 := bstep (se 2 (by rfl) ⟨102723, by rfl⟩ : syracuseStep 273929 = 205447) B205447
theorem B273959 : Blo 179801 273959 := bstep (se 1 (by rfl) ⟨205469, by rfl⟩ : syracuseStep 273959 = 410939) B410939
theorem B4697675 : Blo 179801 4697675 := bstep (se 1 (by rfl) ⟨3523256, by rfl⟩ : syracuseStep 4697675 = 7046513) B7046513
theorem B306767 : Blo 179801 306767 := bstep (se 1 (by rfl) ⟨230075, by rfl⟩ : syracuseStep 306767 = 460151) B460151
theorem B405089 : Blo 179801 405089 := bstep (se 2 (by rfl) ⟨151908, by rfl⟩ : syracuseStep 405089 = 303817) B303817
theorem B274043 : Blo 179801 274043 := bstep (se 1 (by rfl) ⟨205532, by rfl⟩ : syracuseStep 274043 = 411065) B411065
theorem B1027799 : Blo 179801 1027799 := bstep (se 1 (by rfl) ⟨770849, by rfl⟩ : syracuseStep 1027799 = 1541699) B1541699
theorem B274169 : Blo 179801 274169 := bstep (se 2 (by rfl) ⟨102813, by rfl⟩ : syracuseStep 274169 = 205627) B205627
theorem B274271 : Blo 179801 274271 := bstep (se 1 (by rfl) ⟨205703, by rfl⟩ : syracuseStep 274271 = 411407) B411407
theorem B274283 : Blo 179801 274283 := bstep (se 1 (by rfl) ⟨205712, by rfl⟩ : syracuseStep 274283 = 411425) B411425
theorem B405431 : Blo 179801 405431 := bstep (se 1 (by rfl) ⟨304073, by rfl⟩ : syracuseStep 405431 = 608147) B608147
theorem B274511 : Blo 179801 274511 := bstep (se 1 (by rfl) ⟨205883, by rfl⟩ : syracuseStep 274511 = 411767) B411767
theorem B274631 : Blo 179801 274631 := bstep (se 1 (by rfl) ⟨205973, by rfl⟩ : syracuseStep 274631 = 411947) B411947
theorem B274793 : Blo 179801 274793 := bstep (se 2 (by rfl) ⟨103047, by rfl⟩ : syracuseStep 274793 = 206095) B206095
theorem B307631 : Blo 179801 307631 := bstep (se 1 (by rfl) ⟨230723, by rfl⟩ : syracuseStep 307631 = 461447) B461447
theorem B274871 : Blo 179801 274871 := bstep (se 1 (by rfl) ⟨206153, by rfl⟩ : syracuseStep 274871 = 412307) B412307
theorem B274907 : Blo 179801 274907 := bstep (se 1 (by rfl) ⟨206180, by rfl⟩ : syracuseStep 274907 = 412361) B412361
theorem B406025 : Blo 179801 406025 := bstep (se 2 (by rfl) ⟨152259, by rfl⟩ : syracuseStep 406025 = 304519) B304519
theorem B733819 : Blo 179801 733819 := bstep (se 1 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 733819 = 1100729) B1100729
theorem B9679621 : Blo 179801 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B3912461 : Blo 179801 3912461 := bstep (se 3 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 3912461 = 1467173) B1467173
theorem B406367 : Blo 179801 406367 := bstep (se 1 (by rfl) ⟨304775, by rfl⟩ : syracuseStep 406367 = 609551) B609551
theorem B308063 : Blo 179801 308063 := bstep (se 1 (by rfl) ⟨231047, by rfl⟩ : syracuseStep 308063 = 462095) B462095
theorem B275375 : Blo 179801 275375 := bstep (se 1 (by rfl) ⟨206531, by rfl⟩ : syracuseStep 275375 = 413063) B413063
theorem B275465 : Blo 179801 275465 := bstep (se 2 (by rfl) ⟨103299, by rfl⟩ : syracuseStep 275465 = 206599) B206599
theorem B406547 : Blo 179801 406547 := bstep (se 1 (by rfl) ⟨304910, by rfl⟩ : syracuseStep 406547 = 609821) B609821
theorem B275495 : Blo 179801 275495 := bstep (se 1 (by rfl) ⟨206621, by rfl⟩ : syracuseStep 275495 = 413243) B413243
theorem B275579 : Blo 179801 275579 := bstep (se 1 (by rfl) ⟨206684, by rfl⟩ : syracuseStep 275579 = 413369) B413369
theorem B406889 : Blo 179801 406889 := bstep (se 2 (by rfl) ⟨152583, by rfl⟩ : syracuseStep 406889 = 305167) B305167
theorem B308623 : Blo 179801 308623 := bstep (se 1 (by rfl) ⟨231467, by rfl⟩ : syracuseStep 308623 = 462935) B462935
theorem B1324451 : Blo 179801 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B2635253 : Blo 179801 2635253 := bstep (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) B247055
theorem B341833 : Blo 179801 341833 := bstep (se 2 (by rfl) ⟨128187, by rfl⟩ : syracuseStep 341833 = 256375) B256375
theorem B1390445 : Blo 179801 1390445 := bstep (se 3 (by rfl) ⟨260708, by rfl⟩ : syracuseStep 1390445 = 521417) B521417
theorem B407483 : Blo 179801 407483 := bstep (se 1 (by rfl) ⟨305612, by rfl⟩ : syracuseStep 407483 = 611225) B611225
theorem B243751 : Blo 179801 243751 := bstep (se 1 (by rfl) ⟨182813, by rfl⟩ : syracuseStep 243751 = 365627) B365627
theorem B407609 : Blo 179801 407609 := bstep (se 2 (by rfl) ⟨152853, by rfl⟩ : syracuseStep 407609 = 305707) B305707
theorem B309305 : Blo 179801 309305 := bstep (se 2 (by rfl) ⟨115989, by rfl⟩ : syracuseStep 309305 = 231979) B231979
theorem B1030259 : Blo 179801 1030259 := bstep (se 1 (by rfl) ⟨772694, by rfl⟩ : syracuseStep 1030259 = 1545389) B1545389
theorem B5191937 : Blo 179801 5191937 := bstep (se 2 (by rfl) ⟨1946976, by rfl⟩ : syracuseStep 5191937 = 3893953) B3893953
theorem B36616493 : Blo 179801 36616493 := bstep (se 3 (by rfl) ⟨6865592, by rfl⟩ : syracuseStep 36616493 = 13731185) B13731185
theorem B1554821 : Blo 179801 1554821 := bstep (se 4 (by rfl) ⟨145764, by rfl⟩ : syracuseStep 1554821 = 291529) B291529
theorem B407951 : Blo 179801 407951 := bstep (se 1 (by rfl) ⟨305963, by rfl⟩ : syracuseStep 407951 = 611927) B611927
theorem B1030715 : Blo 179801 1030715 := bstep (se 1 (by rfl) ⟨773036, by rfl⟩ : syracuseStep 1030715 = 1546073) B1546073
theorem B7518905 : Blo 179801 7518905 := bstep (se 2 (by rfl) ⟨2819589, by rfl⟩ : syracuseStep 7518905 = 5639179) B5639179
theorem B408275 : Blo 179801 408275 := bstep (se 1 (by rfl) ⟨306206, by rfl⟩ : syracuseStep 408275 = 612413) B612413
theorem B310007 : Blo 179801 310007 := bstep (se 1 (by rfl) ⟨232505, by rfl⟩ : syracuseStep 310007 = 465011) B465011
theorem B179807 : Blo 179801 179807 := bstep (se 1 (by rfl) ⟨134855, by rfl⟩ : syracuseStep 179807 = 269711) B269711
theorem B179835 : Blo 179801 179835 := bstep (se 1 (by rfl) ⟨134876, by rfl⟩ : syracuseStep 179835 = 269753) B269753
theorem B409211 : Blo 179801 409211 := bstep (se 1 (by rfl) ⟨306908, by rfl⟩ : syracuseStep 409211 = 613817) B613817
theorem B179887 : Blo 179801 179887 := bstep (se 1 (by rfl) ⟨134915, by rfl⟩ : syracuseStep 179887 = 269831) B269831
theorem B1982141 : Blo 179801 1982141 := bstep (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) B743303
theorem B179911 : Blo 179801 179911 := bstep (se 1 (by rfl) ⟨134933, by rfl⟩ : syracuseStep 179911 = 269867) B269867
theorem B179931 : Blo 179801 179931 := bstep (se 1 (by rfl) ⟨134948, by rfl⟩ : syracuseStep 179931 = 269897) B269897
theorem B409337 : Blo 179801 409337 := bstep (se 2 (by rfl) ⟨153501, by rfl⟩ : syracuseStep 409337 = 307003) B307003
theorem B180007 : Blo 179801 180007 := bstep (se 1 (by rfl) ⟨135005, by rfl⟩ : syracuseStep 180007 = 270011) B270011
theorem B180047 : Blo 179801 180047 := bstep (se 1 (by rfl) ⟨135035, by rfl⟩ : syracuseStep 180047 = 270071) B270071
theorem B180063 : Blo 179801 180063 := bstep (se 1 (by rfl) ⟨135047, by rfl⟩ : syracuseStep 180063 = 270095) B270095
theorem B868205 : Blo 179801 868205 := bstep (se 3 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 868205 = 325577) B325577
theorem B704375 : Blo 179801 704375 := bstep (se 1 (by rfl) ⟨528281, by rfl⟩ : syracuseStep 704375 = 1056563) B1056563
theorem B180091 : Blo 179801 180091 := bstep (se 1 (by rfl) ⟨135068, by rfl⟩ : syracuseStep 180091 = 270137) B270137
theorem B180143 : Blo 179801 180143 := bstep (se 1 (by rfl) ⟨135107, by rfl⟩ : syracuseStep 180143 = 270215) B270215
theorem B180167 : Blo 179801 180167 := bstep (se 1 (by rfl) ⟨135125, by rfl⟩ : syracuseStep 180167 = 270251) B270251
theorem B180187 : Blo 179801 180187 := bstep (se 1 (by rfl) ⟨135140, by rfl⟩ : syracuseStep 180187 = 270281) B270281
theorem B344027 : Blo 179801 344027 := bstep (se 1 (by rfl) ⟨258020, by rfl⟩ : syracuseStep 344027 = 516041) B516041
theorem B409607 : Blo 179801 409607 := bstep (se 1 (by rfl) ⟨307205, by rfl⟩ : syracuseStep 409607 = 614411) B614411
theorem B180263 : Blo 179801 180263 := bstep (se 1 (by rfl) ⟨135197, by rfl⟩ : syracuseStep 180263 = 270395) B270395
theorem B180303 : Blo 179801 180303 := bstep (se 1 (by rfl) ⟨135227, by rfl⟩ : syracuseStep 180303 = 270455) B270455
theorem B409679 : Blo 179801 409679 := bstep (se 1 (by rfl) ⟨307259, by rfl⟩ : syracuseStep 409679 = 614519) B614519
theorem B704591 : Blo 179801 704591 := bstep (se 1 (by rfl) ⟨528443, by rfl⟩ : syracuseStep 704591 = 1056887) B1056887
theorem B180319 : Blo 179801 180319 := bstep (se 1 (by rfl) ⟨135239, by rfl⟩ : syracuseStep 180319 = 270479) B270479
theorem B180347 : Blo 179801 180347 := bstep (se 1 (by rfl) ⟨135260, by rfl⟩ : syracuseStep 180347 = 270521) B270521
theorem B180399 : Blo 179801 180399 := bstep (se 1 (by rfl) ⟨135299, by rfl⟩ : syracuseStep 180399 = 270599) B270599
theorem B180423 : Blo 179801 180423 := bstep (se 1 (by rfl) ⟨135317, by rfl⟩ : syracuseStep 180423 = 270635) B270635
theorem B344263 : Blo 179801 344263 := bstep (se 1 (by rfl) ⟨258197, by rfl⟩ : syracuseStep 344263 = 516395) B516395
theorem B180443 : Blo 179801 180443 := bstep (se 1 (by rfl) ⟨135332, by rfl⟩ : syracuseStep 180443 = 270665) B270665
theorem B180519 : Blo 179801 180519 := bstep (se 1 (by rfl) ⟨135389, by rfl⟩ : syracuseStep 180519 = 270779) B270779
theorem B180559 : Blo 179801 180559 := bstep (se 1 (by rfl) ⟨135419, by rfl⟩ : syracuseStep 180559 = 270839) B270839
theorem B1392983 : Blo 179801 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B180575 : Blo 179801 180575 := bstep (se 1 (by rfl) ⟨135431, by rfl⟩ : syracuseStep 180575 = 270863) B270863
theorem B180603 : Blo 179801 180603 := bstep (se 1 (by rfl) ⟨135452, by rfl⟩ : syracuseStep 180603 = 270905) B270905
theorem B180655 : Blo 179801 180655 := bstep (se 1 (by rfl) ⟨135491, by rfl⟩ : syracuseStep 180655 = 270983) B270983
theorem B180679 : Blo 179801 180679 := bstep (se 1 (by rfl) ⟨135509, by rfl⟩ : syracuseStep 180679 = 271019) B271019
theorem B180699 : Blo 179801 180699 := bstep (se 1 (by rfl) ⟨135524, by rfl⟩ : syracuseStep 180699 = 271049) B271049
theorem B410075 : Blo 179801 410075 := bstep (se 1 (by rfl) ⟨307556, by rfl⟩ : syracuseStep 410075 = 615113) B615113
theorem B180775 : Blo 179801 180775 := bstep (se 1 (by rfl) ⟨135581, by rfl⟩ : syracuseStep 180775 = 271163) B271163
theorem B180815 : Blo 179801 180815 := bstep (se 1 (by rfl) ⟨135611, by rfl⟩ : syracuseStep 180815 = 271223) B271223
theorem B180831 : Blo 179801 180831 := bstep (se 1 (by rfl) ⟨135623, by rfl⟩ : syracuseStep 180831 = 271247) B271247
theorem B180859 : Blo 179801 180859 := bstep (se 1 (by rfl) ⟨135644, by rfl⟩ : syracuseStep 180859 = 271289) B271289
theorem B180911 : Blo 179801 180911 := bstep (se 1 (by rfl) ⟨135683, by rfl⟩ : syracuseStep 180911 = 271367) B271367
theorem B606905 : Blo 179801 606905 := bstep (se 2 (by rfl) ⟨227589, by rfl⟩ : syracuseStep 606905 = 455179) B455179
theorem B180935 : Blo 179801 180935 := bstep (se 1 (by rfl) ⟨135701, by rfl⟩ : syracuseStep 180935 = 271403) B271403
theorem B1393361 : Blo 179801 1393361 := bstep (se 2 (by rfl) ⟨522510, by rfl⟩ : syracuseStep 1393361 = 1045021) B1045021
theorem B180955 : Blo 179801 180955 := bstep (se 1 (by rfl) ⟨135716, by rfl⟩ : syracuseStep 180955 = 271433) B271433
theorem B181031 : Blo 179801 181031 := bstep (se 1 (by rfl) ⟨135773, by rfl⟩ : syracuseStep 181031 = 271547) B271547
theorem B181071 : Blo 179801 181071 := bstep (se 1 (by rfl) ⟨135803, by rfl⟩ : syracuseStep 181071 = 271607) B271607
theorem B181087 : Blo 179801 181087 := bstep (se 1 (by rfl) ⟨135815, by rfl⟩ : syracuseStep 181087 = 271631) B271631
theorem B443243 : Blo 179801 443243 := bstep (se 1 (by rfl) ⟨332432, by rfl⟩ : syracuseStep 443243 = 664865) B664865
theorem B181115 : Blo 179801 181115 := bstep (se 1 (by rfl) ⟨135836, by rfl⟩ : syracuseStep 181115 = 271673) B271673
theorem B181167 : Blo 179801 181167 := bstep (se 1 (by rfl) ⟨135875, by rfl⟩ : syracuseStep 181167 = 271751) B271751
theorem B410543 : Blo 179801 410543 := bstep (se 1 (by rfl) ⟨307907, by rfl⟩ : syracuseStep 410543 = 615815) B615815
theorem B181191 : Blo 179801 181191 := bstep (se 1 (by rfl) ⟨135893, by rfl⟩ : syracuseStep 181191 = 271787) B271787
theorem B181211 : Blo 179801 181211 := bstep (se 1 (by rfl) ⟨135908, by rfl⟩ : syracuseStep 181211 = 271817) B271817
theorem B181287 : Blo 179801 181287 := bstep (se 1 (by rfl) ⟨135965, by rfl⟩ : syracuseStep 181287 = 271931) B271931
theorem B181327 : Blo 179801 181327 := bstep (se 1 (by rfl) ⟨135995, by rfl⟩ : syracuseStep 181327 = 271991) B271991
theorem B574543 : Blo 179801 574543 := bstep (se 1 (by rfl) ⟨430907, by rfl⟩ : syracuseStep 574543 = 861815) B861815
theorem B181343 : Blo 179801 181343 := bstep (se 1 (by rfl) ⟨136007, by rfl⟩ : syracuseStep 181343 = 272015) B272015
theorem B181371 : Blo 179801 181371 := bstep (se 1 (by rfl) ⟨136028, by rfl⟩ : syracuseStep 181371 = 272057) B272057
theorem B410795 : Blo 179801 410795 := bstep (se 1 (by rfl) ⟨308096, by rfl⟩ : syracuseStep 410795 = 616193) B616193
theorem B181423 : Blo 179801 181423 := bstep (se 1 (by rfl) ⟨136067, by rfl⟩ : syracuseStep 181423 = 272135) B272135
theorem B181447 : Blo 179801 181447 := bstep (se 1 (by rfl) ⟨136085, by rfl⟩ : syracuseStep 181447 = 272171) B272171
theorem B181467 : Blo 179801 181467 := bstep (se 1 (by rfl) ⟨136100, by rfl⟩ : syracuseStep 181467 = 272201) B272201
theorem B607499 : Blo 179801 607499 := bstep (se 1 (by rfl) ⟨455624, by rfl⟩ : syracuseStep 607499 = 911249) B911249
theorem B181543 : Blo 179801 181543 := bstep (se 1 (by rfl) ⟨136157, by rfl⟩ : syracuseStep 181543 = 272315) B272315
theorem B181583 : Blo 179801 181583 := bstep (se 1 (by rfl) ⟨136187, by rfl⟩ : syracuseStep 181583 = 272375) B272375
theorem B181599 : Blo 179801 181599 := bstep (se 1 (by rfl) ⟨136199, by rfl⟩ : syracuseStep 181599 = 272399) B272399
theorem B181627 : Blo 179801 181627 := bstep (se 1 (by rfl) ⟨136220, by rfl⟩ : syracuseStep 181627 = 272441) B272441
theorem B181679 : Blo 179801 181679 := bstep (se 1 (by rfl) ⟨136259, by rfl⟩ : syracuseStep 181679 = 272519) B272519
theorem B181703 : Blo 179801 181703 := bstep (se 1 (by rfl) ⟨136277, by rfl⟩ : syracuseStep 181703 = 272555) B272555
theorem B181723 : Blo 179801 181723 := bstep (se 1 (by rfl) ⟨136292, by rfl⟩ : syracuseStep 181723 = 272585) B272585
theorem B607769 : Blo 179801 607769 := bstep (se 2 (by rfl) ⟨227913, by rfl⟩ : syracuseStep 607769 = 455827) B455827
theorem B181799 : Blo 179801 181799 := bstep (se 1 (by rfl) ⟨136349, by rfl⟩ : syracuseStep 181799 = 272699) B272699
theorem B181839 : Blo 179801 181839 := bstep (se 1 (by rfl) ⟨136379, by rfl⟩ : syracuseStep 181839 = 272759) B272759
theorem B1164887 : Blo 179801 1164887 := bstep (se 1 (by rfl) ⟨873665, by rfl⟩ : syracuseStep 1164887 = 1747331) B1747331
theorem B181855 : Blo 179801 181855 := bstep (se 1 (by rfl) ⟨136391, by rfl⟩ : syracuseStep 181855 = 272783) B272783
theorem B181883 : Blo 179801 181883 := bstep (se 1 (by rfl) ⟨136412, by rfl⟩ : syracuseStep 181883 = 272825) B272825
theorem B181935 : Blo 179801 181935 := bstep (se 1 (by rfl) ⟨136451, by rfl⟩ : syracuseStep 181935 = 272903) B272903
theorem B181959 : Blo 179801 181959 := bstep (se 1 (by rfl) ⟨136469, by rfl⟩ : syracuseStep 181959 = 272939) B272939
theorem B411335 : Blo 179801 411335 := bstep (se 1 (by rfl) ⟨308501, by rfl⟩ : syracuseStep 411335 = 617003) B617003
theorem B181979 : Blo 179801 181979 := bstep (se 1 (by rfl) ⟨136484, by rfl⟩ : syracuseStep 181979 = 272969) B272969
theorem B182055 : Blo 179801 182055 := bstep (se 1 (by rfl) ⟨136541, by rfl⟩ : syracuseStep 182055 = 273083) B273083
theorem B182095 : Blo 179801 182095 := bstep (se 1 (by rfl) ⟨136571, by rfl⟩ : syracuseStep 182095 = 273143) B273143
theorem B182111 : Blo 179801 182111 := bstep (se 1 (by rfl) ⟨136583, by rfl⟩ : syracuseStep 182111 = 273167) B273167
theorem B182139 : Blo 179801 182139 := bstep (se 1 (by rfl) ⟨136604, by rfl⟩ : syracuseStep 182139 = 273209) B273209
theorem B182191 : Blo 179801 182191 := bstep (se 1 (by rfl) ⟨136643, by rfl⟩ : syracuseStep 182191 = 273287) B273287
theorem B182215 : Blo 179801 182215 := bstep (se 1 (by rfl) ⟨136661, by rfl⟩ : syracuseStep 182215 = 273323) B273323
theorem B182235 : Blo 179801 182235 := bstep (se 1 (by rfl) ⟨136676, by rfl⟩ : syracuseStep 182235 = 273353) B273353
theorem B182311 : Blo 179801 182311 := bstep (se 1 (by rfl) ⟨136733, by rfl⟩ : syracuseStep 182311 = 273467) B273467
theorem B346169 : Blo 179801 346169 := bstep (se 2 (by rfl) ⟨129813, by rfl⟩ : syracuseStep 346169 = 259627) B259627
theorem B182351 : Blo 179801 182351 := bstep (se 1 (by rfl) ⟨136763, by rfl⟩ : syracuseStep 182351 = 273527) B273527
theorem B1984601 : Blo 179801 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B182367 : Blo 179801 182367 := bstep (se 1 (by rfl) ⟨136775, by rfl⟩ : syracuseStep 182367 = 273551) B273551
theorem B182395 : Blo 179801 182395 := bstep (se 1 (by rfl) ⟨136796, by rfl⟩ : syracuseStep 182395 = 273593) B273593
theorem B182447 : Blo 179801 182447 := bstep (se 1 (by rfl) ⟨136835, by rfl⟩ : syracuseStep 182447 = 273671) B273671
theorem B182471 : Blo 179801 182471 := bstep (se 1 (by rfl) ⟨136853, by rfl⟩ : syracuseStep 182471 = 273707) B273707
theorem B182491 : Blo 179801 182491 := bstep (se 1 (by rfl) ⟨136868, by rfl⟩ : syracuseStep 182491 = 273737) B273737
theorem B182567 : Blo 179801 182567 := bstep (se 1 (by rfl) ⟨136925, by rfl⟩ : syracuseStep 182567 = 273851) B273851
theorem B182607 : Blo 179801 182607 := bstep (se 1 (by rfl) ⟨136955, by rfl⟩ : syracuseStep 182607 = 273911) B273911
theorem B182623 : Blo 179801 182623 := bstep (se 1 (by rfl) ⟨136967, by rfl⟩ : syracuseStep 182623 = 273935) B273935
theorem B182651 : Blo 179801 182651 := bstep (se 1 (by rfl) ⟨136988, by rfl⟩ : syracuseStep 182651 = 273977) B273977
theorem B1296773 : Blo 179801 1296773 := bstep (se 4 (by rfl) ⟨121572, by rfl⟩ : syracuseStep 1296773 = 243145) B243145
theorem B346511 : Blo 179801 346511 := bstep (se 1 (by rfl) ⟨259883, by rfl⟩ : syracuseStep 346511 = 519767) B519767
theorem B182703 : Blo 179801 182703 := bstep (se 1 (by rfl) ⟨137027, by rfl⟩ : syracuseStep 182703 = 274055) B274055
theorem B182727 : Blo 179801 182727 := bstep (se 1 (by rfl) ⟨137045, by rfl⟩ : syracuseStep 182727 = 274091) B274091
theorem B182747 : Blo 179801 182747 := bstep (se 1 (by rfl) ⟨137060, by rfl⟩ : syracuseStep 182747 = 274121) B274121
theorem B182823 : Blo 179801 182823 := bstep (se 1 (by rfl) ⟨137117, by rfl⟩ : syracuseStep 182823 = 274235) B274235
theorem B412199 : Blo 179801 412199 := bstep (se 1 (by rfl) ⟨309149, by rfl⟩ : syracuseStep 412199 = 618299) B618299
theorem B182863 : Blo 179801 182863 := bstep (se 1 (by rfl) ⟨137147, by rfl⟩ : syracuseStep 182863 = 274295) B274295
theorem B182879 : Blo 179801 182879 := bstep (se 1 (by rfl) ⟨137159, by rfl⟩ : syracuseStep 182879 = 274319) B274319
theorem B182907 : Blo 179801 182907 := bstep (se 1 (by rfl) ⟨137180, by rfl⟩ : syracuseStep 182907 = 274361) B274361
theorem B608903 : Blo 179801 608903 := bstep (se 1 (by rfl) ⟨456677, by rfl⟩ : syracuseStep 608903 = 913355) B913355
theorem B182959 : Blo 179801 182959 := bstep (se 1 (by rfl) ⟨137219, by rfl⟩ : syracuseStep 182959 = 274439) B274439
theorem B608957 : Blo 179801 608957 := bstep (se 3 (by rfl) ⟨114179, by rfl⟩ : syracuseStep 608957 = 228359) B228359
theorem B182983 : Blo 179801 182983 := bstep (se 1 (by rfl) ⟨137237, by rfl⟩ : syracuseStep 182983 = 274475) B274475
theorem B183003 : Blo 179801 183003 := bstep (se 1 (by rfl) ⟨137252, by rfl⟩ : syracuseStep 183003 = 274505) B274505
theorem B4410085 : Blo 179801 4410085 := bstep (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) B826891
theorem B5917475 : Blo 179801 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B183079 : Blo 179801 183079 := bstep (se 1 (by rfl) ⟨137309, by rfl⟩ : syracuseStep 183079 = 274619) B274619
theorem B183119 : Blo 179801 183119 := bstep (se 1 (by rfl) ⟨137339, by rfl⟩ : syracuseStep 183119 = 274679) B274679
theorem B609119 : Blo 179801 609119 := bstep (se 1 (by rfl) ⟨456839, by rfl⟩ : syracuseStep 609119 = 913679) B913679
theorem B183135 : Blo 179801 183135 := bstep (se 1 (by rfl) ⟨137351, by rfl⟩ : syracuseStep 183135 = 274703) B274703
theorem B412523 : Blo 179801 412523 := bstep (se 1 (by rfl) ⟨309392, by rfl⟩ : syracuseStep 412523 = 618785) B618785
theorem B183163 : Blo 179801 183163 := bstep (se 1 (by rfl) ⟨137372, by rfl⟩ : syracuseStep 183163 = 274745) B274745
theorem B412577 : Blo 179801 412577 := bstep (se 2 (by rfl) ⟨154716, by rfl⟩ : syracuseStep 412577 = 309433) B309433
theorem B183215 : Blo 179801 183215 := bstep (se 1 (by rfl) ⟨137411, by rfl⟩ : syracuseStep 183215 = 274823) B274823
theorem B183239 : Blo 179801 183239 := bstep (se 1 (by rfl) ⟨137429, by rfl⟩ : syracuseStep 183239 = 274859) B274859
theorem B183259 : Blo 179801 183259 := bstep (se 1 (by rfl) ⟨137444, by rfl⟩ : syracuseStep 183259 = 274889) B274889
theorem B609281 : Blo 179801 609281 := bstep (se 2 (by rfl) ⟨228480, by rfl⟩ : syracuseStep 609281 = 456961) B456961
theorem B183335 : Blo 179801 183335 := bstep (se 1 (by rfl) ⟨137501, by rfl⟩ : syracuseStep 183335 = 275003) B275003
theorem B183375 : Blo 179801 183375 := bstep (se 1 (by rfl) ⟨137531, by rfl⟩ : syracuseStep 183375 = 275063) B275063
theorem B183391 : Blo 179801 183391 := bstep (se 1 (by rfl) ⟨137543, by rfl⟩ : syracuseStep 183391 = 275087) B275087
theorem B183419 : Blo 179801 183419 := bstep (se 1 (by rfl) ⟨137564, by rfl⟩ : syracuseStep 183419 = 275129) B275129
theorem B183471 : Blo 179801 183471 := bstep (se 1 (by rfl) ⟨137603, by rfl⟩ : syracuseStep 183471 = 275207) B275207
theorem B183495 : Blo 179801 183495 := bstep (se 1 (by rfl) ⟨137621, by rfl⟩ : syracuseStep 183495 = 275243) B275243
theorem B183515 : Blo 179801 183515 := bstep (se 1 (by rfl) ⟨137636, by rfl⟩ : syracuseStep 183515 = 275273) B275273
theorem B412919 : Blo 179801 412919 := bstep (se 1 (by rfl) ⟨309689, by rfl⟩ : syracuseStep 412919 = 619379) B619379
theorem B183591 : Blo 179801 183591 := bstep (se 1 (by rfl) ⟨137693, by rfl⟩ : syracuseStep 183591 = 275387) B275387
theorem B183631 : Blo 179801 183631 := bstep (se 1 (by rfl) ⟨137723, by rfl⟩ : syracuseStep 183631 = 275447) B275447
theorem B183647 : Blo 179801 183647 := bstep (se 1 (by rfl) ⟨137735, by rfl⟩ : syracuseStep 183647 = 275471) B275471
theorem B183675 : Blo 179801 183675 := bstep (se 1 (by rfl) ⟨137756, by rfl⟩ : syracuseStep 183675 = 275513) B275513
theorem B183727 : Blo 179801 183727 := bstep (se 1 (by rfl) ⟨137795, by rfl⟩ : syracuseStep 183727 = 275591) B275591
theorem B183751 : Blo 179801 183751 := bstep (se 1 (by rfl) ⟨137813, by rfl⟩ : syracuseStep 183751 = 275627) B275627
theorem B183771 : Blo 179801 183771 := bstep (se 1 (by rfl) ⟨137828, by rfl⟩ : syracuseStep 183771 = 275657) B275657
theorem B577163 : Blo 179801 577163 := bstep (se 1 (by rfl) ⟨432872, by rfl⟩ : syracuseStep 577163 = 865745) B865745
theorem B610091 : Blo 179801 610091 := bstep (se 1 (by rfl) ⟨457568, by rfl⟩ : syracuseStep 610091 = 915137) B915137
theorem B347977 : Blo 179801 347977 := bstep (se 2 (by rfl) ⟨130491, by rfl⟩ : syracuseStep 347977 = 260983) B260983
theorem B413513 : Blo 179801 413513 := bstep (se 2 (by rfl) ⟨155067, by rfl⟩ : syracuseStep 413513 = 310135) B310135
theorem B741395 : Blo 179801 741395 := bstep (se 1 (by rfl) ⟨556046, by rfl⟩ : syracuseStep 741395 = 1112093) B1112093
theorem B610361 : Blo 179801 610361 := bstep (se 2 (by rfl) ⟨228885, by rfl⟩ : syracuseStep 610361 = 457771) B457771
theorem B348371 : Blo 179801 348371 := bstep (se 1 (by rfl) ⟨261278, by rfl⟩ : syracuseStep 348371 = 522557) B522557
theorem B610685 : Blo 179801 610685 := bstep (se 3 (by rfl) ⟨114503, by rfl⟩ : syracuseStep 610685 = 229007) B229007
theorem B348599 : Blo 179801 348599 := bstep (se 1 (by rfl) ⟨261449, by rfl⟩ : syracuseStep 348599 = 522899) B522899
theorem B578087 : Blo 179801 578087 := bstep (se 1 (by rfl) ⟨433565, by rfl⟩ : syracuseStep 578087 = 867131) B867131
theorem B610955 : Blo 179801 610955 := bstep (se 1 (by rfl) ⟨458216, by rfl⟩ : syracuseStep 610955 = 916433) B916433
theorem B1037231 : Blo 179801 1037231 := bstep (se 1 (by rfl) ⟨777923, by rfl⟩ : syracuseStep 1037231 = 1555847) B1555847
theorem B1168451 : Blo 179801 1168451 := bstep (se 1 (by rfl) ⟨876338, by rfl⟩ : syracuseStep 1168451 = 1752677) B1752677
theorem B1168577 : Blo 179801 1168577 := bstep (se 2 (by rfl) ⟨438216, by rfl⟩ : syracuseStep 1168577 = 876433) B876433
theorem B1463771 : Blo 179801 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B611873 : Blo 179801 611873 := bstep (se 2 (by rfl) ⟨229452, by rfl⟩ : syracuseStep 611873 = 458905) B458905
theorem B2610731 : Blo 179801 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B612089 : Blo 179801 612089 := bstep (se 2 (by rfl) ⟨229533, by rfl⟩ : syracuseStep 612089 = 459067) B459067
theorem B3888931 : Blo 179801 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B47404865 : Blo 179801 47404865 := bstep (se 2 (by rfl) ⟨17776824, by rfl⟩ : syracuseStep 47404865 = 35553649) B35553649
theorem B350171 : Blo 179801 350171 := bstep (se 1 (by rfl) ⟨262628, by rfl⟩ : syracuseStep 350171 = 525257) B525257
theorem B612359 : Blo 179801 612359 := bstep (se 1 (by rfl) ⟨459269, by rfl⟩ : syracuseStep 612359 = 918539) B918539
theorem B776249 : Blo 179801 776249 := bstep (se 2 (by rfl) ⟨291093, by rfl⟩ : syracuseStep 776249 = 582187) B582187
theorem B514127 : Blo 179801 514127 := bstep (se 1 (by rfl) ⟨385595, by rfl⟩ : syracuseStep 514127 = 771191) B771191
theorem B612467 : Blo 179801 612467 := bstep (se 1 (by rfl) ⟨459350, by rfl⟩ : syracuseStep 612467 = 918701) B918701
theorem B3496193 : Blo 179801 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B4741409 : Blo 179801 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B612737 : Blo 179801 612737 := bstep (se 2 (by rfl) ⟨229776, by rfl⟩ : syracuseStep 612737 = 459553) B459553
theorem B4446667 : Blo 179801 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B2611997 : Blo 179801 2611997 := bstep (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) B979499
theorem B613547 : Blo 179801 613547 := bstep (se 1 (by rfl) ⟨460160, by rfl⟩ : syracuseStep 613547 = 920321) B920321
theorem B1465615 : Blo 179801 1465615 := bstep (se 1 (by rfl) ⟨1099211, by rfl⟩ : syracuseStep 1465615 = 2198423) B2198423
theorem B48717233 : Blo 179801 48717233 := bstep (se 2 (by rfl) ⟨18268962, by rfl⟩ : syracuseStep 48717233 = 36537925) B36537925
theorem B515609 : Blo 179801 515609 := bstep (se 2 (by rfl) ⟨193353, by rfl⟩ : syracuseStep 515609 = 386707) B386707
theorem B614087 : Blo 179801 614087 := bstep (se 1 (by rfl) ⟨460565, by rfl⟩ : syracuseStep 614087 = 921131) B921131
theorem B319339 : Blo 179801 319339 := bstep (se 1 (by rfl) ⟨239504, by rfl⟩ : syracuseStep 319339 = 479009) B479009
theorem B2613329 : Blo 179801 2613329 := bstep (se 2 (by rfl) ⟨979998, by rfl⟩ : syracuseStep 2613329 = 1959997) B1959997
theorem B1040465 : Blo 179801 1040465 := bstep (se 2 (by rfl) ⟨390174, by rfl⟩ : syracuseStep 1040465 = 780349) B780349
theorem B581879 : Blo 179801 581879 := bstep (se 1 (by rfl) ⟨436409, by rfl⟩ : syracuseStep 581879 = 872819) B872819
theorem B1040921 : Blo 179801 1040921 := bstep (se 2 (by rfl) ⟨390345, by rfl⟩ : syracuseStep 1040921 = 780691) B780691
theorem B614951 : Blo 179801 614951 := bstep (se 1 (by rfl) ⟨461213, by rfl⟩ : syracuseStep 614951 = 922427) B922427
theorem B746081 : Blo 179801 746081 := bstep (se 2 (by rfl) ⟨279780, by rfl⟩ : syracuseStep 746081 = 559561) B559561
theorem B615059 : Blo 179801 615059 := bstep (se 1 (by rfl) ⟨461294, by rfl⟩ : syracuseStep 615059 = 922589) B922589
theorem B1172141 : Blo 179801 1172141 := bstep (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) B439553
theorem B3105539 : Blo 179801 3105539 := bstep (se 1 (by rfl) ⟨2329154, by rfl⟩ : syracuseStep 3105539 = 4658309) B4658309
theorem B1565513 : Blo 179801 1565513 := bstep (se 2 (by rfl) ⟨587067, by rfl⟩ : syracuseStep 1565513 = 1174135) B1174135
theorem B615275 : Blo 179801 615275 := bstep (se 1 (by rfl) ⟨461456, by rfl⟩ : syracuseStep 615275 = 922913) B922913
theorem B1172369 : Blo 179801 1172369 := bstep (se 2 (by rfl) ⟨439638, by rfl⟩ : syracuseStep 1172369 = 879277) B879277
theorem B615329 : Blo 179801 615329 := bstep (se 2 (by rfl) ⟨230748, by rfl⟩ : syracuseStep 615329 = 461497) B461497
theorem B1369061 : Blo 179801 1369061 := bstep (se 4 (by rfl) ⟨128349, by rfl⟩ : syracuseStep 1369061 = 256699) B256699
theorem B648271 : Blo 179801 648271 := bstep (se 1 (by rfl) ⟨486203, by rfl⟩ : syracuseStep 648271 = 972407) B972407
theorem B1303897 : Blo 179801 1303897 := bstep (se 2 (by rfl) ⟨488961, by rfl⟩ : syracuseStep 1303897 = 977923) B977923
theorem B615923 : Blo 179801 615923 := bstep (se 1 (by rfl) ⟨461942, by rfl⟩ : syracuseStep 615923 = 923885) B923885
theorem B779975 : Blo 179801 779975 := bstep (se 1 (by rfl) ⟨584981, by rfl⟩ : syracuseStep 779975 = 1169963) B1169963
theorem B583519 : Blo 179801 583519 := bstep (se 1 (by rfl) ⟨437639, by rfl⟩ : syracuseStep 583519 = 875279) B875279
theorem B1763167 : Blo 179801 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B649079 : Blo 179801 649079 := bstep (se 1 (by rfl) ⟨486809, by rfl⟩ : syracuseStep 649079 = 973619) B973619
theorem B616463 : Blo 179801 616463 := bstep (se 1 (by rfl) ⟨462347, by rfl⟩ : syracuseStep 616463 = 924695) B924695
theorem B1108025 : Blo 179801 1108025 := bstep (se 2 (by rfl) ⟨415509, by rfl⟩ : syracuseStep 1108025 = 831019) B831019
theorem B1271965 : Blo 179801 1271965 := bstep (se 3 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 1271965 = 476987) B476987
theorem B387433 : Blo 179801 387433 := bstep (se 2 (by rfl) ⟨145287, by rfl⟩ : syracuseStep 387433 = 290575) B290575
theorem B518525 : Blo 179801 518525 := bstep (se 3 (by rfl) ⟨97223, by rfl⟩ : syracuseStep 518525 = 194447) B194447
theorem B4385177 : Blo 179801 4385177 := bstep (se 2 (by rfl) ⟨1644441, by rfl⟩ : syracuseStep 4385177 = 3288883) B3288883
theorem B551387 : Blo 179801 551387 := bstep (se 1 (by rfl) ⟨413540, by rfl⟩ : syracuseStep 551387 = 827081) B827081
theorem B911897 : Blo 179801 911897 := bstep (se 2 (by rfl) ⟨341961, by rfl⟩ : syracuseStep 911897 = 683923) B683923
theorem B617057 : Blo 179801 617057 := bstep (se 2 (by rfl) ⟨231396, by rfl⟩ : syracuseStep 617057 = 462793) B462793
theorem B584339 : Blo 179801 584339 := bstep (se 1 (by rfl) ⟨438254, by rfl⟩ : syracuseStep 584339 = 876509) B876509
theorem B256711 : Blo 179801 256711 := bstep (se 1 (by rfl) ⟨192533, by rfl⟩ : syracuseStep 256711 = 385067) B385067
theorem B683255 : Blo 179801 683255 := bstep (se 1 (by rfl) ⟨512441, by rfl⟩ : syracuseStep 683255 = 1024883) B1024883
theorem B1043837 : Blo 179801 1043837 := bstep (se 3 (by rfl) ⟨195719, by rfl⟩ : syracuseStep 1043837 = 391439) B391439
theorem B5074319 : Blo 179801 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B1175239 : Blo 179801 1175239 := bstep (se 1 (by rfl) ⟨881429, by rfl⟩ : syracuseStep 1175239 = 1762859) B1762859
theorem B388937 : Blo 179801 388937 := bstep (se 2 (by rfl) ⟨145851, by rfl⟩ : syracuseStep 388937 = 291703) B291703
theorem B618515 : Blo 179801 618515 := bstep (se 1 (by rfl) ⟨463886, by rfl⟩ : syracuseStep 618515 = 927773) B927773
theorem B684227 : Blo 179801 684227 := bstep (se 1 (by rfl) ⟨513170, by rfl⟩ : syracuseStep 684227 = 1026341) B1026341
theorem B618839 : Blo 179801 618839 := bstep (se 1 (by rfl) ⟨464129, by rfl⟩ : syracuseStep 618839 = 928259) B928259
theorem B586109 : Blo 179801 586109 := bstep (se 3 (by rfl) ⟨109895, by rfl⟩ : syracuseStep 586109 = 219791) B219791
theorem B455291 : Blo 179801 455291 := bstep (se 1 (by rfl) ⟨341468, by rfl⟩ : syracuseStep 455291 = 682937) B682937
theorem B684683 : Blo 179801 684683 := bstep (se 1 (by rfl) ⟨513512, by rfl⟩ : syracuseStep 684683 = 1027025) B1027025
theorem B586379 : Blo 179801 586379 := bstep (se 1 (by rfl) ⟨439784, by rfl⟩ : syracuseStep 586379 = 879569) B879569
theorem B324425 : Blo 179801 324425 := bstep (se 2 (by rfl) ⟨121659, by rfl⟩ : syracuseStep 324425 = 243319) B243319
theorem B684895 : Blo 179801 684895 := bstep (se 1 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 684895 = 1027343) B1027343
theorem B193375 : Blo 179801 193375 := bstep (se 1 (by rfl) ⟨145031, by rfl⟩ : syracuseStep 193375 = 290063) B290063
theorem B652307 : Blo 179801 652307 := bstep (se 1 (by rfl) ⟨489230, by rfl⟩ : syracuseStep 652307 = 978461) B978461
theorem B324857 : Blo 179801 324857 := bstep (se 2 (by rfl) ⟨121821, by rfl⟩ : syracuseStep 324857 = 243643) B243643
theorem B390505 : Blo 179801 390505 := bstep (se 2 (by rfl) ⟨146439, by rfl⟩ : syracuseStep 390505 = 292879) B292879
theorem B914813 : Blo 179801 914813 := bstep (se 3 (by rfl) ⟨171527, by rfl⟩ : syracuseStep 914813 = 343055) B343055
theorem B619919 : Blo 179801 619919 := bstep (se 1 (by rfl) ⟨464939, by rfl⟩ : syracuseStep 619919 = 929879) B929879
theorem B390619 : Blo 179801 390619 := bstep (se 1 (by rfl) ⟨292964, by rfl⟩ : syracuseStep 390619 = 585929) B585929
theorem B1045979 : Blo 179801 1045979 := bstep (se 1 (by rfl) ⟨784484, by rfl⟩ : syracuseStep 1045979 = 1568969) B1568969
theorem B3536369 : Blo 179801 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B1308305 : Blo 179801 1308305 := bstep (se 2 (by rfl) ⟨490614, by rfl⟩ : syracuseStep 1308305 = 981229) B981229
theorem B620243 : Blo 179801 620243 := bstep (se 1 (by rfl) ⟨465182, by rfl⟩ : syracuseStep 620243 = 930365) B930365
theorem B685853 : Blo 179801 685853 := bstep (se 3 (by rfl) ⟨128597, by rfl⟩ : syracuseStep 685853 = 257195) B257195
theorem B685867 : Blo 179801 685867 := bstep (se 1 (by rfl) ⟨514400, by rfl⟩ : syracuseStep 685867 = 1028801) B1028801
theorem B260219 : Blo 179801 260219 := bstep (se 1 (by rfl) ⟨195164, by rfl⟩ : syracuseStep 260219 = 390329) B390329
theorem B1964189 : Blo 179801 1964189 := bstep (se 3 (by rfl) ⟨368285, by rfl⟩ : syracuseStep 1964189 = 736571) B736571
theorem B522625 : Blo 179801 522625 := bstep (se 2 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 522625 = 391969) B391969
theorem B457103 : Blo 179801 457103 := bstep (se 1 (by rfl) ⟨342827, by rfl⟩ : syracuseStep 457103 = 685655) B685655
theorem B227767 : Blo 179801 227767 := bstep (se 1 (by rfl) ⟨170825, by rfl⟩ : syracuseStep 227767 = 341651) B341651
theorem B522875 : Blo 179801 522875 := bstep (se 1 (by rfl) ⟨392156, by rfl⟩ : syracuseStep 522875 = 784313) B784313
theorem B1374893 : Blo 179801 1374893 := bstep (se 3 (by rfl) ⟨257792, by rfl⟩ : syracuseStep 1374893 = 515585) B515585
theorem B457427 : Blo 179801 457427 := bstep (se 1 (by rfl) ⟨343070, by rfl⟩ : syracuseStep 457427 = 686141) B686141
theorem B260857 : Blo 179801 260857 := bstep (se 2 (by rfl) ⟨97821, by rfl⟩ : syracuseStep 260857 = 195643) B195643
theorem B1112939 : Blo 179801 1112939 := bstep (se 1 (by rfl) ⟨834704, by rfl⟩ : syracuseStep 1112939 = 1669409) B1669409
theorem B326587 : Blo 179801 326587 := bstep (se 1 (by rfl) ⟨244940, by rfl⟩ : syracuseStep 326587 = 489881) B489881
theorem B392123 : Blo 179801 392123 := bstep (se 1 (by rfl) ⟨294092, by rfl⟩ : syracuseStep 392123 = 588185) B588185
theorem B229063 : Blo 179801 229063 := bstep (se 1 (by rfl) ⟨171797, by rfl⟩ : syracuseStep 229063 = 343595) B343595
theorem B459017 : Blo 179801 459017 := bstep (se 2 (by rfl) ⟨172131, by rfl⟩ : syracuseStep 459017 = 344263) B344263
theorem B786779 : Blo 179801 786779 := bstep (se 1 (by rfl) ⟨590084, by rfl⟩ : syracuseStep 786779 = 1180169) B1180169
theorem B295495 : Blo 179801 295495 := bstep (se 1 (by rfl) ⟨221621, by rfl⟩ : syracuseStep 295495 = 443243) B443243
theorem B459371 : Blo 179801 459371 := bstep (se 1 (by rfl) ⟨344528, by rfl⟩ : syracuseStep 459371 = 689057) B689057
theorem B918215 : Blo 179801 918215 := bstep (se 1 (by rfl) ⟨688661, by rfl⟩ : syracuseStep 918215 = 1377323) B1377323
theorem B5604173 : Blo 179801 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B623561 : Blo 179801 623561 := bstep (se 2 (by rfl) ⟨233835, by rfl⟩ : syracuseStep 623561 = 467671) B467671
theorem B460019 : Blo 179801 460019 := bstep (se 1 (by rfl) ⟨345014, by rfl⟩ : syracuseStep 460019 = 690029) B690029
theorem B230779 : Blo 179801 230779 := bstep (se 1 (by rfl) ⟨173084, by rfl⟩ : syracuseStep 230779 = 346169) B346169
theorem B231007 : Blo 179801 231007 := bstep (se 1 (by rfl) ⟨173255, by rfl⟩ : syracuseStep 231007 = 346511) B346511
theorem B460475 : Blo 179801 460475 := bstep (se 1 (by rfl) ⟨345356, by rfl⟩ : syracuseStep 460475 = 690713) B690713
theorem B1738529 : Blo 179801 1738529 := bstep (se 2 (by rfl) ⟨651948, by rfl⟩ : syracuseStep 1738529 = 1303897) B1303897
theorem B461011 : Blo 179801 461011 := bstep (se 1 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 461011 = 691517) B691517
theorem B494263 : Blo 179801 494263 := bstep (se 1 (by rfl) ⟨370697, by rfl⟩ : syracuseStep 494263 = 741395) B741395
theorem B1739485 : Blo 179801 1739485 := bstep (se 3 (by rfl) ⟨326153, by rfl⟩ : syracuseStep 1739485 = 652307) B652307
theorem B232247 : Blo 179801 232247 := bstep (se 1 (by rfl) ⟨174185, by rfl⟩ : syracuseStep 232247 = 348371) B348371
theorem B232399 : Blo 179801 232399 := bstep (se 1 (by rfl) ⟨174299, by rfl⟩ : syracuseStep 232399 = 348599) B348599
theorem B461963 : Blo 179801 461963 := bstep (se 1 (by rfl) ⟨346472, by rfl⟩ : syracuseStep 461963 = 692945) B692945
theorem B691487 : Blo 179801 691487 := bstep (se 1 (by rfl) ⟨518615, by rfl⟩ : syracuseStep 691487 = 1037231) B1037231
theorem B920969 : Blo 179801 920969 := bstep (se 2 (by rfl) ⟨345363, by rfl⟩ : syracuseStep 920969 = 690727) B690727
theorem B462419 : Blo 179801 462419 := bstep (se 1 (by rfl) ⟨346814, by rfl⟩ : syracuseStep 462419 = 693629) B693629
theorem B396895 : Blo 179801 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B1740487 : Blo 179801 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B3149725 : Blo 179801 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B233447 : Blo 179801 233447 := bstep (se 1 (by rfl) ⟨175085, by rfl⟩ : syracuseStep 233447 = 350171) B350171
theorem B2330795 : Blo 179801 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B397735 : Blo 179801 397735 := bstep (se 1 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 397735 = 596603) B596603
theorem B463279 : Blo 179801 463279 := bstep (se 1 (by rfl) ⟨347459, by rfl⟩ : syracuseStep 463279 = 694919) B694919
theorem B1741331 : Blo 179801 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B922265 : Blo 179801 922265 := bstep (se 2 (by rfl) ⟨345849, by rfl⟩ : syracuseStep 922265 = 691699) B691699
theorem B463583 : Blo 179801 463583 := bstep (se 1 (by rfl) ⟨347687, by rfl⟩ : syracuseStep 463583 = 695375) B695375
theorem B3347203 : Blo 179801 3347203 := bstep (se 1 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 3347203 = 5020805) B5020805
theorem B32478155 : Blo 179801 32478155 := bstep (se 1 (by rfl) ⟨24358616, by rfl⟩ : syracuseStep 32478155 = 48717233) B48717233
theorem B463969 : Blo 179801 463969 := bstep (se 2 (by rfl) ⟨173988, by rfl⟩ : syracuseStep 463969 = 347977) B347977
theorem B464251 : Blo 179801 464251 := bstep (se 1 (by rfl) ⟨348188, by rfl⟩ : syracuseStep 464251 = 696377) B696377
theorem B1742219 : Blo 179801 1742219 := bstep (se 1 (by rfl) ⟨1306664, by rfl⟩ : syracuseStep 1742219 = 2613329) B2613329
theorem B693643 : Blo 179801 693643 := bstep (se 1 (by rfl) ⟨520232, by rfl⟩ : syracuseStep 693643 = 1040465) B1040465
theorem B693917 : Blo 179801 693917 := bstep (se 3 (by rfl) ⟨130109, by rfl⟩ : syracuseStep 693917 = 260219) B260219
theorem B693947 : Blo 179801 693947 := bstep (se 1 (by rfl) ⟨520460, by rfl⟩ : syracuseStep 693947 = 1040921) B1040921
theorem B497387 : Blo 179801 497387 := bstep (se 1 (by rfl) ⟨373040, by rfl⟩ : syracuseStep 497387 = 746081) B746081
theorem B464687 : Blo 179801 464687 := bstep (se 1 (by rfl) ⟨348515, by rfl⟩ : syracuseStep 464687 = 697031) B697031
theorem B2070359 : Blo 179801 2070359 := bstep (se 1 (by rfl) ⟨1552769, by rfl⟩ : syracuseStep 2070359 = 3105539) B3105539
theorem B19929037 : Blo 179801 19929037 := bstep (se 3 (by rfl) ⟨3736694, by rfl⟩ : syracuseStep 19929037 = 7473389) B7473389
theorem B924047 : Blo 179801 924047 := bstep (se 1 (by rfl) ⟨693035, by rfl⟩ : syracuseStep 924047 = 1386071) B1386071
theorem B432719 : Blo 179801 432719 := bstep (se 1 (by rfl) ⟨324539, by rfl⟩ : syracuseStep 432719 = 649079) B649079
theorem B203359 : Blo 179801 203359 := bstep (se 1 (by rfl) ⟨152519, by rfl⟩ : syracuseStep 203359 = 305039) B305039
theorem B1776323 : Blo 179801 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B2923451 : Blo 179801 2923451 := bstep (se 1 (by rfl) ⟨2192588, by rfl⟩ : syracuseStep 2923451 = 4385177) B4385177
theorem B367591 : Blo 179801 367591 := bstep (se 1 (by rfl) ⟨275693, by rfl⟩ : syracuseStep 367591 = 551387) B551387
theorem B990323 : Blo 179801 990323 := bstep (se 1 (by rfl) ⟨742742, by rfl⟩ : syracuseStep 990323 = 1485485) B1485485
theorem B269705 : Blo 179801 269705 := bstep (se 2 (by rfl) ⟨101139, by rfl⟩ : syracuseStep 269705 = 202279) B202279
theorem B695891 : Blo 179801 695891 := bstep (se 1 (by rfl) ⟨521918, by rfl⟩ : syracuseStep 695891 = 1043837) B1043837
theorem B3382879 : Blo 179801 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B5185241 : Blo 179801 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B204511 : Blo 179801 204511 := bstep (se 1 (by rfl) ⟨153383, by rfl⟩ : syracuseStep 204511 = 306767) B306767
theorem B270059 : Blo 179801 270059 := bstep (se 1 (by rfl) ⟨202544, by rfl⟩ : syracuseStep 270059 = 405089) B405089
theorem B270287 : Blo 179801 270287 := bstep (se 1 (by rfl) ⟨202715, by rfl⟩ : syracuseStep 270287 = 405431) B405431
theorem B205087 : Blo 179801 205087 := bstep (se 1 (by rfl) ⟨153815, by rfl⟩ : syracuseStep 205087 = 307631) B307631
theorem B270683 : Blo 179801 270683 := bstep (se 1 (by rfl) ⟨203012, by rfl⟩ : syracuseStep 270683 = 406025) B406025
theorem B303527 : Blo 179801 303527 := bstep (se 1 (by rfl) ⟨227645, by rfl⟩ : syracuseStep 303527 = 455291) B455291
theorem B926153 : Blo 179801 926153 := bstep (se 2 (by rfl) ⟨347307, by rfl⟩ : syracuseStep 926153 = 694615) B694615
theorem B696833 : Blo 179801 696833 := bstep (se 2 (by rfl) ⟨261312, by rfl⟩ : syracuseStep 696833 = 522625) B522625
theorem B270911 : Blo 179801 270911 := bstep (se 1 (by rfl) ⟨203183, by rfl⟩ : syracuseStep 270911 = 406367) B406367
theorem B205375 : Blo 179801 205375 := bstep (se 1 (by rfl) ⟨154031, by rfl⟩ : syracuseStep 205375 = 308063) B308063
theorem B303689 : Blo 179801 303689 := bstep (se 2 (by rfl) ⟨113883, by rfl⟩ : syracuseStep 303689 = 227767) B227767
theorem B271031 : Blo 179801 271031 := bstep (se 1 (by rfl) ⟨203273, by rfl⟩ : syracuseStep 271031 = 406547) B406547
theorem B271259 : Blo 179801 271259 := bstep (se 1 (by rfl) ⟨203444, by rfl⟩ : syracuseStep 271259 = 406889) B406889
theorem B697319 : Blo 179801 697319 := bstep (se 1 (by rfl) ⟨522989, by rfl⟩ : syracuseStep 697319 = 1045979) B1045979
theorem B926963 : Blo 179801 926963 := bstep (se 1 (by rfl) ⟨695222, by rfl⟩ : syracuseStep 926963 = 1390445) B1390445
theorem B533753 : Blo 179801 533753 := bstep (se 2 (by rfl) ⟨200157, by rfl⟩ : syracuseStep 533753 = 400315) B400315
theorem B435449 : Blo 179801 435449 := bstep (se 2 (by rfl) ⟨163293, by rfl⟩ : syracuseStep 435449 = 326587) B326587
theorem B271655 : Blo 179801 271655 := bstep (se 1 (by rfl) ⟨203741, by rfl⟩ : syracuseStep 271655 = 407483) B407483
theorem B271739 : Blo 179801 271739 := bstep (se 1 (by rfl) ⟨203804, by rfl⟩ : syracuseStep 271739 = 407609) B407609
theorem B206203 : Blo 179801 206203 := bstep (se 1 (by rfl) ⟨154652, by rfl⟩ : syracuseStep 206203 = 309305) B309305
theorem B271865 : Blo 179801 271865 := bstep (se 2 (by rfl) ⟨101949, by rfl⟩ : syracuseStep 271865 = 203899) B203899
theorem B304735 : Blo 179801 304735 := bstep (se 1 (by rfl) ⟨228551, by rfl⟩ : syracuseStep 304735 = 457103) B457103
theorem B271967 : Blo 179801 271967 := bstep (se 1 (by rfl) ⟨203975, by rfl⟩ : syracuseStep 271967 = 407951) B407951
theorem B304951 : Blo 179801 304951 := bstep (se 1 (by rfl) ⟨228713, by rfl⟩ : syracuseStep 304951 = 457427) B457427
theorem B272183 : Blo 179801 272183 := bstep (se 1 (by rfl) ⟨204137, by rfl⟩ : syracuseStep 272183 = 408275) B408275
theorem B206671 : Blo 179801 206671 := bstep (se 1 (by rfl) ⟨155003, by rfl⟩ : syracuseStep 206671 = 310007) B310007
theorem B272489 : Blo 179801 272489 := bstep (se 2 (by rfl) ⟨102183, by rfl⟩ : syracuseStep 272489 = 204367) B204367
theorem B305417 : Blo 179801 305417 := bstep (se 2 (by rfl) ⟨114531, by rfl⟩ : syracuseStep 305417 = 229063) B229063
theorem B272807 : Blo 179801 272807 := bstep (se 1 (by rfl) ⟨204605, by rfl⟩ : syracuseStep 272807 = 409211) B409211
theorem B1321427 : Blo 179801 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B272891 : Blo 179801 272891 := bstep (se 1 (by rfl) ⟨204668, by rfl⟩ : syracuseStep 272891 = 409337) B409337
theorem B469583 : Blo 179801 469583 := bstep (se 1 (by rfl) ⟨352187, by rfl⟩ : syracuseStep 469583 = 704375) B704375
theorem B273017 : Blo 179801 273017 := bstep (se 2 (by rfl) ⟨102381, by rfl⟩ : syracuseStep 273017 = 204763) B204763
theorem B273071 : Blo 179801 273071 := bstep (se 1 (by rfl) ⟨204803, by rfl⟩ : syracuseStep 273071 = 409607) B409607
theorem B273119 : Blo 179801 273119 := bstep (se 1 (by rfl) ⟨204839, by rfl⟩ : syracuseStep 273119 = 409679) B409679
theorem B469727 : Blo 179801 469727 := bstep (se 1 (by rfl) ⟨352295, by rfl⟩ : syracuseStep 469727 = 704591) B704591
theorem B928655 : Blo 179801 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B273383 : Blo 179801 273383 := bstep (se 1 (by rfl) ⟨205037, by rfl⟩ : syracuseStep 273383 = 410075) B410075
theorem B404603 : Blo 179801 404603 := bstep (se 1 (by rfl) ⟨303452, by rfl⟩ : syracuseStep 404603 = 606905) B606905
theorem B928907 : Blo 179801 928907 := bstep (se 1 (by rfl) ⟨696680, by rfl⟩ : syracuseStep 928907 = 1393361) B1393361
theorem B306409 : Blo 179801 306409 := bstep (se 2 (by rfl) ⟨114903, by rfl⟩ : syracuseStep 306409 = 229807) B229807
theorem B273641 : Blo 179801 273641 := bstep (se 2 (by rfl) ⟨102615, by rfl⟩ : syracuseStep 273641 = 205231) B205231
theorem B404729 : Blo 179801 404729 := bstep (se 2 (by rfl) ⟨151773, by rfl⟩ : syracuseStep 404729 = 303547) B303547
theorem B306463 : Blo 179801 306463 := bstep (se 1 (by rfl) ⟨229847, by rfl⟩ : syracuseStep 306463 = 459695) B459695
theorem B273695 : Blo 179801 273695 := bstep (se 1 (by rfl) ⟨205271, by rfl⟩ : syracuseStep 273695 = 410543) B410543
theorem B404873 : Blo 179801 404873 := bstep (se 2 (by rfl) ⟨151827, by rfl⟩ : syracuseStep 404873 = 303655) B303655
theorem B273863 : Blo 179801 273863 := bstep (se 1 (by rfl) ⟨205397, by rfl⟩ : syracuseStep 273863 = 410795) B410795
theorem B404999 : Blo 179801 404999 := bstep (se 1 (by rfl) ⟨303749, by rfl⟩ : syracuseStep 404999 = 607499) B607499
theorem B405179 : Blo 179801 405179 := bstep (se 1 (by rfl) ⟨303884, by rfl⟩ : syracuseStep 405179 = 607769) B607769
theorem B306875 : Blo 179801 306875 := bstep (se 1 (by rfl) ⟨230156, by rfl⟩ : syracuseStep 306875 = 460313) B460313
theorem B274217 : Blo 179801 274217 := bstep (se 2 (by rfl) ⟨102831, by rfl⟩ : syracuseStep 274217 = 205663) B205663
theorem B274223 : Blo 179801 274223 := bstep (se 1 (by rfl) ⟨205667, by rfl⟩ : syracuseStep 274223 = 411335) B411335
theorem B405305 : Blo 179801 405305 := bstep (se 2 (by rfl) ⟨151989, by rfl⟩ : syracuseStep 405305 = 303979) B303979
theorem B7450555 : Blo 179801 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B1323067 : Blo 179801 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B3551321 : Blo 179801 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B864361 : Blo 179801 864361 := bstep (se 2 (by rfl) ⟨324135, by rfl⟩ : syracuseStep 864361 = 648271) B648271
theorem B766057 : Blo 179801 766057 := bstep (se 2 (by rfl) ⟨287271, by rfl⟩ : syracuseStep 766057 = 574543) B574543
theorem B864515 : Blo 179801 864515 := bstep (se 1 (by rfl) ⟨648386, by rfl⟩ : syracuseStep 864515 = 1296773) B1296773
theorem B274697 : Blo 179801 274697 := bstep (se 2 (by rfl) ⟨103011, by rfl⟩ : syracuseStep 274697 = 206023) B206023
theorem B274799 : Blo 179801 274799 := bstep (se 1 (by rfl) ⟨206099, by rfl⟩ : syracuseStep 274799 = 412199) B412199
theorem B405935 : Blo 179801 405935 := bstep (se 1 (by rfl) ⟨304451, by rfl⟩ : syracuseStep 405935 = 608903) B608903
theorem B405971 : Blo 179801 405971 := bstep (se 1 (by rfl) ⟨304478, by rfl⟩ : syracuseStep 405971 = 608957) B608957
theorem B3944983 : Blo 179801 3944983 := bstep (se 1 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 3944983 = 5917475) B5917475
theorem B406079 : Blo 179801 406079 := bstep (se 1 (by rfl) ⟨304559, by rfl⟩ : syracuseStep 406079 = 609119) B609119
theorem B275015 : Blo 179801 275015 := bstep (se 1 (by rfl) ⟨206261, by rfl⟩ : syracuseStep 275015 = 412523) B412523
theorem B275051 : Blo 179801 275051 := bstep (se 1 (by rfl) ⟨206288, by rfl⟩ : syracuseStep 275051 = 412577) B412577
theorem B406187 : Blo 179801 406187 := bstep (se 1 (by rfl) ⟨304640, by rfl⟩ : syracuseStep 406187 = 609281) B609281
theorem B275279 : Blo 179801 275279 := bstep (se 1 (by rfl) ⟨206459, by rfl⟩ : syracuseStep 275279 = 412919) B412919
theorem B2634605 : Blo 179801 2634605 := bstep (se 3 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 2634605 = 987977) B987977
theorem B406727 : Blo 179801 406727 := bstep (se 1 (by rfl) ⟨305045, by rfl⟩ : syracuseStep 406727 = 610091) B610091
theorem B275675 : Blo 179801 275675 := bstep (se 1 (by rfl) ⟨206756, by rfl⟩ : syracuseStep 275675 = 413513) B413513
theorem B406907 : Blo 179801 406907 := bstep (se 1 (by rfl) ⟨305180, by rfl⟩ : syracuseStep 406907 = 610361) B610361
theorem B308603 : Blo 179801 308603 := bstep (se 1 (by rfl) ⟨231452, by rfl⟩ : syracuseStep 308603 = 462905) B462905
theorem B407033 : Blo 179801 407033 := bstep (se 2 (by rfl) ⟨152637, by rfl⟩ : syracuseStep 407033 = 305275) B305275
theorem B407123 : Blo 179801 407123 := bstep (se 1 (by rfl) ⟨305342, by rfl⟩ : syracuseStep 407123 = 610685) B610685
theorem B407303 : Blo 179801 407303 := bstep (se 1 (by rfl) ⟨305477, by rfl⟩ : syracuseStep 407303 = 610955) B610955
theorem B866285 : Blo 179801 866285 := bstep (se 3 (by rfl) ⟨162428, by rfl⟩ : syracuseStep 866285 = 324857) B324857
theorem B342281 : Blo 179801 342281 := bstep (se 2 (by rfl) ⟨128355, by rfl⟩ : syracuseStep 342281 = 256711) B256711
theorem B5880113 : Blo 179801 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B309595 : Blo 179801 309595 := bstep (se 1 (by rfl) ⟨232196, by rfl⟩ : syracuseStep 309595 = 464393) B464393
theorem B407915 : Blo 179801 407915 := bstep (se 1 (by rfl) ⟨305936, by rfl⟩ : syracuseStep 407915 = 611873) B611873
theorem B408059 : Blo 179801 408059 := bstep (se 1 (by rfl) ⟨306044, by rfl⟩ : syracuseStep 408059 = 612089) B612089
theorem B408185 : Blo 179801 408185 := bstep (se 2 (by rfl) ⟨153069, by rfl⟩ : syracuseStep 408185 = 306139) B306139
theorem B408239 : Blo 179801 408239 := bstep (se 1 (by rfl) ⟨306179, by rfl⟩ : syracuseStep 408239 = 612359) B612359
theorem B1161965 : Blo 179801 1161965 := bstep (se 3 (by rfl) ⟨217868, by rfl⟩ : syracuseStep 1161965 = 435737) B435737
theorem B408311 : Blo 179801 408311 := bstep (se 1 (by rfl) ⟨306233, by rfl⟩ : syracuseStep 408311 = 612467) B612467
theorem B3160939 : Blo 179801 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B408491 : Blo 179801 408491 := bstep (se 1 (by rfl) ⟨306368, by rfl⟩ : syracuseStep 408491 = 612737) B612737
theorem B409031 : Blo 179801 409031 := bstep (se 1 (by rfl) ⟨306773, by rfl⟩ : syracuseStep 409031 = 613547) B613547
theorem B310879 : Blo 179801 310879 := bstep (se 1 (by rfl) ⟨233159, by rfl⟩ : syracuseStep 310879 = 466319) B466319
theorem B343739 : Blo 179801 343739 := bstep (se 1 (by rfl) ⟨257804, by rfl⟩ : syracuseStep 343739 = 515609) B515609
theorem B179935 : Blo 179801 179935 := bstep (se 1 (by rfl) ⟨134951, by rfl⟩ : syracuseStep 179935 = 269903) B269903
theorem B180015 : Blo 179801 180015 := bstep (se 1 (by rfl) ⟨135011, by rfl⟩ : syracuseStep 180015 = 270023) B270023
theorem B409391 : Blo 179801 409391 := bstep (se 1 (by rfl) ⟨307043, by rfl⟩ : syracuseStep 409391 = 614087) B614087
theorem B180123 : Blo 179801 180123 := bstep (se 1 (by rfl) ⟨135092, by rfl⟩ : syracuseStep 180123 = 270185) B270185
theorem B180175 : Blo 179801 180175 := bstep (se 1 (by rfl) ⟨135131, by rfl⟩ : syracuseStep 180175 = 270263) B270263
theorem B180199 : Blo 179801 180199 := bstep (se 1 (by rfl) ⟨135149, by rfl⟩ : syracuseStep 180199 = 270299) B270299
theorem B770219 : Blo 179801 770219 := bstep (se 1 (by rfl) ⟨577664, by rfl⟩ : syracuseStep 770219 = 1155329) B1155329
theorem B835795 : Blo 179801 835795 := bstep (se 1 (by rfl) ⟨626846, by rfl⟩ : syracuseStep 835795 = 1253693) B1253693
theorem B180511 : Blo 179801 180511 := bstep (se 1 (by rfl) ⟨135383, by rfl⟩ : syracuseStep 180511 = 270767) B270767
theorem B180571 : Blo 179801 180571 := bstep (se 1 (by rfl) ⟨135428, by rfl⟩ : syracuseStep 180571 = 270857) B270857
theorem B180591 : Blo 179801 180591 := bstep (se 1 (by rfl) ⟨135443, by rfl⟩ : syracuseStep 180591 = 270887) B270887
theorem B409967 : Blo 179801 409967 := bstep (se 1 (by rfl) ⟨307475, by rfl⟩ : syracuseStep 409967 = 614951) B614951
theorem B180647 : Blo 179801 180647 := bstep (se 1 (by rfl) ⟨135485, by rfl⟩ : syracuseStep 180647 = 270971) B270971
theorem B410039 : Blo 179801 410039 := bstep (se 1 (by rfl) ⟨307529, by rfl⟩ : syracuseStep 410039 = 615059) B615059
theorem B180731 : Blo 179801 180731 := bstep (se 1 (by rfl) ⟨135548, by rfl⟩ : syracuseStep 180731 = 271097) B271097
theorem B180799 : Blo 179801 180799 := bstep (se 1 (by rfl) ⟨135599, by rfl⟩ : syracuseStep 180799 = 271199) B271199
theorem B180807 : Blo 179801 180807 := bstep (se 1 (by rfl) ⟨135605, by rfl⟩ : syracuseStep 180807 = 271211) B271211
theorem B410183 : Blo 179801 410183 := bstep (se 1 (by rfl) ⟨307637, by rfl⟩ : syracuseStep 410183 = 615275) B615275
theorem B410219 : Blo 179801 410219 := bstep (se 1 (by rfl) ⟨307664, by rfl⟩ : syracuseStep 410219 = 615329) B615329
theorem B180959 : Blo 179801 180959 := bstep (se 1 (by rfl) ⟨135719, by rfl⟩ : syracuseStep 180959 = 271439) B271439
theorem B181039 : Blo 179801 181039 := bstep (se 1 (by rfl) ⟨135779, by rfl⟩ : syracuseStep 181039 = 271559) B271559
theorem B181147 : Blo 179801 181147 := bstep (se 1 (by rfl) ⟨135860, by rfl⟩ : syracuseStep 181147 = 271721) B271721
theorem B836513 : Blo 179801 836513 := bstep (se 2 (by rfl) ⟨313692, by rfl⟩ : syracuseStep 836513 = 627385) B627385
theorem B181199 : Blo 179801 181199 := bstep (se 1 (by rfl) ⟨135899, by rfl⟩ : syracuseStep 181199 = 271799) B271799
theorem B181223 : Blo 179801 181223 := bstep (se 1 (by rfl) ⟨135917, by rfl⟩ : syracuseStep 181223 = 271835) B271835
theorem B410615 : Blo 179801 410615 := bstep (se 1 (by rfl) ⟨307961, by rfl⟩ : syracuseStep 410615 = 615923) B615923
theorem B181535 : Blo 179801 181535 := bstep (se 1 (by rfl) ⟨136151, by rfl⟩ : syracuseStep 181535 = 272303) B272303
theorem B181595 : Blo 179801 181595 := bstep (se 1 (by rfl) ⟨136196, by rfl⟩ : syracuseStep 181595 = 272393) B272393
theorem B410975 : Blo 179801 410975 := bstep (se 1 (by rfl) ⟨308231, by rfl⟩ : syracuseStep 410975 = 616463) B616463
theorem B181615 : Blo 179801 181615 := bstep (se 1 (by rfl) ⟨136211, by rfl⟩ : syracuseStep 181615 = 272423) B272423
theorem B738683 : Blo 179801 738683 := bstep (se 1 (by rfl) ⟨554012, by rfl⟩ : syracuseStep 738683 = 1108025) B1108025
theorem B181671 : Blo 179801 181671 := bstep (se 1 (by rfl) ⟨136253, by rfl⟩ : syracuseStep 181671 = 272507) B272507
theorem B181755 : Blo 179801 181755 := bstep (se 1 (by rfl) ⟨136316, by rfl⟩ : syracuseStep 181755 = 272633) B272633
theorem B181823 : Blo 179801 181823 := bstep (se 1 (by rfl) ⟨136367, by rfl⟩ : syracuseStep 181823 = 272735) B272735
theorem B181831 : Blo 179801 181831 := bstep (se 1 (by rfl) ⟨136373, by rfl⟩ : syracuseStep 181831 = 272747) B272747
theorem B345683 : Blo 179801 345683 := bstep (se 1 (by rfl) ⟨259262, by rfl⟩ : syracuseStep 345683 = 518525) B518525
theorem B1394333 : Blo 179801 1394333 := bstep (se 3 (by rfl) ⟨261437, by rfl⟩ : syracuseStep 1394333 = 522875) B522875
theorem B607931 : Blo 179801 607931 := bstep (se 1 (by rfl) ⟨455948, by rfl⟩ : syracuseStep 607931 = 911897) B911897
theorem B1558237 : Blo 179801 1558237 := bstep (se 3 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 1558237 = 584339) B584339
theorem B181983 : Blo 179801 181983 := bstep (se 1 (by rfl) ⟨136487, by rfl⟩ : syracuseStep 181983 = 272975) B272975
theorem B411371 : Blo 179801 411371 := bstep (se 1 (by rfl) ⟨308528, by rfl⟩ : syracuseStep 411371 = 617057) B617057
theorem B182063 : Blo 179801 182063 := bstep (se 1 (by rfl) ⟨136547, by rfl⟩ : syracuseStep 182063 = 273095) B273095
theorem B411497 : Blo 179801 411497 := bstep (se 2 (by rfl) ⟨154311, by rfl⟩ : syracuseStep 411497 = 308623) B308623
theorem B182171 : Blo 179801 182171 := bstep (se 1 (by rfl) ⟨136628, by rfl⟩ : syracuseStep 182171 = 273257) B273257
theorem B182223 : Blo 179801 182223 := bstep (se 1 (by rfl) ⟨136667, by rfl⟩ : syracuseStep 182223 = 273335) B273335
theorem B182247 : Blo 179801 182247 := bstep (se 1 (by rfl) ⟨136685, by rfl⟩ : syracuseStep 182247 = 273371) B273371
theorem B182559 : Blo 179801 182559 := bstep (se 1 (by rfl) ⟨136919, by rfl⟩ : syracuseStep 182559 = 273839) B273839
theorem B182619 : Blo 179801 182619 := bstep (se 1 (by rfl) ⟨136964, by rfl⟩ : syracuseStep 182619 = 273929) B273929
theorem B182639 : Blo 179801 182639 := bstep (se 1 (by rfl) ⟨136979, by rfl⟩ : syracuseStep 182639 = 273959) B273959
theorem B3131783 : Blo 179801 3131783 := bstep (se 1 (by rfl) ⟨2348837, by rfl⟩ : syracuseStep 3131783 = 4697675) B4697675
theorem B182695 : Blo 179801 182695 := bstep (se 1 (by rfl) ⟨137021, by rfl⟩ : syracuseStep 182695 = 274043) B274043
theorem B182779 : Blo 179801 182779 := bstep (se 1 (by rfl) ⟨137084, by rfl⟩ : syracuseStep 182779 = 274169) B274169
theorem B182847 : Blo 179801 182847 := bstep (se 1 (by rfl) ⟨137135, by rfl⟩ : syracuseStep 182847 = 274271) B274271
theorem B182855 : Blo 179801 182855 := bstep (se 1 (by rfl) ⟨137141, by rfl⟩ : syracuseStep 182855 = 274283) B274283
theorem B412343 : Blo 179801 412343 := bstep (se 1 (by rfl) ⟨309257, by rfl⟩ : syracuseStep 412343 = 618515) B618515
theorem B183007 : Blo 179801 183007 := bstep (se 1 (by rfl) ⟨137255, by rfl⟩ : syracuseStep 183007 = 274511) B274511
theorem B183087 : Blo 179801 183087 := bstep (se 1 (by rfl) ⟨137315, by rfl⟩ : syracuseStep 183087 = 274631) B274631
theorem B412559 : Blo 179801 412559 := bstep (se 1 (by rfl) ⟨309419, by rfl⟩ : syracuseStep 412559 = 618839) B618839
theorem B183195 : Blo 179801 183195 := bstep (se 1 (by rfl) ⟨137396, by rfl⟩ : syracuseStep 183195 = 274793) B274793
theorem B183247 : Blo 179801 183247 := bstep (se 1 (by rfl) ⟨137435, by rfl⟩ : syracuseStep 183247 = 274871) B274871
theorem B183271 : Blo 179801 183271 := bstep (se 1 (by rfl) ⟨137453, by rfl⟩ : syracuseStep 183271 = 274907) B274907
theorem B2608307 : Blo 179801 2608307 := bstep (se 1 (by rfl) ⟨1956230, by rfl⟩ : syracuseStep 2608307 = 3912461) B3912461
theorem B216283 : Blo 179801 216283 := bstep (se 1 (by rfl) ⟨162212, by rfl⟩ : syracuseStep 216283 = 324425) B324425
theorem B183583 : Blo 179801 183583 := bstep (se 1 (by rfl) ⟨137687, by rfl⟩ : syracuseStep 183583 = 275375) B275375
theorem B183643 : Blo 179801 183643 := bstep (se 1 (by rfl) ⟨137732, by rfl⟩ : syracuseStep 183643 = 275465) B275465
theorem B183663 : Blo 179801 183663 := bstep (se 1 (by rfl) ⟨137747, by rfl⟩ : syracuseStep 183663 = 275495) B275495
theorem B183719 : Blo 179801 183719 := bstep (se 1 (by rfl) ⟨137789, by rfl⟩ : syracuseStep 183719 = 275579) B275579
theorem B609875 : Blo 179801 609875 := bstep (se 1 (by rfl) ⟨457406, by rfl⟩ : syracuseStep 609875 = 914813) B914813
theorem B413279 : Blo 179801 413279 := bstep (se 1 (by rfl) ⟨309959, by rfl⟩ : syracuseStep 413279 = 619919) B619919
theorem B347809 : Blo 179801 347809 := bstep (se 2 (by rfl) ⟨130428, by rfl⟩ : syracuseStep 347809 = 260857) B260857
theorem B1756835 : Blo 179801 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B872203 : Blo 179801 872203 := bstep (se 1 (by rfl) ⟨654152, by rfl⟩ : syracuseStep 872203 = 1308305) B1308305
theorem B413495 : Blo 179801 413495 := bstep (se 1 (by rfl) ⟨310121, by rfl⟩ : syracuseStep 413495 = 620243) B620243
theorem B3461291 : Blo 179801 3461291 := bstep (se 1 (by rfl) ⟨2595968, by rfl⟩ : syracuseStep 3461291 = 5191937) B5191937
theorem B4378853 : Blo 179801 4378853 := bstep (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) B821035
theorem B1036547 : Blo 179801 1036547 := bstep (se 1 (by rfl) ⟨777410, by rfl⟩ : syracuseStep 1036547 = 1554821) B1554821
theorem B1954153 : Blo 179801 1954153 := bstep (se 2 (by rfl) ⟨732807, by rfl⟩ : syracuseStep 1954153 = 1465615) B1465615
theorem B741959 : Blo 179801 741959 := bstep (se 1 (by rfl) ⟨556469, by rfl⟩ : syracuseStep 741959 = 1112939) B1112939
theorem B2315213 : Blo 179801 2315213 := bstep (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) B868205
theorem B776591 : Blo 179801 776591 := bstep (se 1 (by rfl) ⟨582443, by rfl⟩ : syracuseStep 776591 = 1164887) B1164887
theorem B612791 : Blo 179801 612791 := bstep (se 1 (by rfl) ⟨459593, by rfl⟩ : syracuseStep 612791 = 919187) B919187
theorem B941831 : Blo 179801 941831 := bstep (se 1 (by rfl) ⟨706373, by rfl⟩ : syracuseStep 941831 = 1412747) B1412747
theorem B778025 : Blo 179801 778025 := bstep (se 2 (by rfl) ⟨291759, by rfl⟩ : syracuseStep 778025 = 583519) B583519
theorem B2350889 : Blo 179801 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B876395 : Blo 179801 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B1695953 : Blo 179801 1695953 := bstep (se 2 (by rfl) ⟨635982, by rfl⟩ : syracuseStep 1695953 = 1271965) B1271965
theorem B385391 : Blo 179801 385391 := bstep (se 1 (by rfl) ⟨289043, by rfl⟩ : syracuseStep 385391 = 578087) B578087
theorem B516577 : Blo 179801 516577 := bstep (se 2 (by rfl) ⟨193716, by rfl⟩ : syracuseStep 516577 = 387433) B387433
theorem B778967 : Blo 179801 778967 := bstep (se 1 (by rfl) ⟨584225, by rfl⟩ : syracuseStep 778967 = 1168451) B1168451
theorem B779051 : Blo 179801 779051 := bstep (se 1 (by rfl) ⟨584288, by rfl⟩ : syracuseStep 779051 = 1168577) B1168577
theorem B975847 : Blo 179801 975847 := bstep (se 1 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 975847 = 1463771) B1463771
theorem B877625 : Blo 179801 877625 := bstep (se 2 (by rfl) ⟨329109, by rfl⟩ : syracuseStep 877625 = 658219) B658219
theorem B3531869 : Blo 179801 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B288031 : Blo 179801 288031 := bstep (se 1 (by rfl) ⟨216023, by rfl⟩ : syracuseStep 288031 = 432047) B432047
theorem B517499 : Blo 179801 517499 := bstep (se 1 (by rfl) ⟨388124, by rfl⟩ : syracuseStep 517499 = 776249) B776249
theorem B615869 : Blo 179801 615869 := bstep (se 3 (by rfl) ⟨115475, by rfl⟩ : syracuseStep 615869 = 230951) B230951
theorem B1238561 : Blo 179801 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B616247 : Blo 179801 616247 := bstep (se 1 (by rfl) ⟨462185, by rfl⟩ : syracuseStep 616247 = 924371) B924371
theorem B126412973 : Blo 179801 126412973 := bstep (se 3 (by rfl) ⟨23702432, by rfl⟩ : syracuseStep 126412973 = 47404865) B47404865
theorem B1566985 : Blo 179801 1566985 := bstep (se 2 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 1566985 = 1175239) B1175239
theorem B616733 : Blo 179801 616733 := bstep (se 3 (by rfl) ⟨115637, by rfl⟩ : syracuseStep 616733 = 231275) B231275
theorem B387919 : Blo 179801 387919 := bstep (se 1 (by rfl) ⟨290939, by rfl⟩ : syracuseStep 387919 = 581879) B581879
theorem B1371005 : Blo 179801 1371005 := bstep (se 3 (by rfl) ⟨257063, by rfl⟩ : syracuseStep 1371005 = 514127) B514127
theorem B781427 : Blo 179801 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B1043675 : Blo 179801 1043675 := bstep (se 1 (by rfl) ⟨782756, by rfl⟩ : syracuseStep 1043675 = 1565513) B1565513
theorem B781579 : Blo 179801 781579 := bstep (se 1 (by rfl) ⟨586184, by rfl⟩ : syracuseStep 781579 = 1172369) B1172369
theorem B617759 : Blo 179801 617759 := bstep (se 1 (by rfl) ⟨463319, by rfl⟩ : syracuseStep 617759 = 926639) B926639
theorem B6319397 : Blo 179801 6319397 := bstep (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) B1184887
theorem B912707 : Blo 179801 912707 := bstep (se 1 (by rfl) ⟨684530, by rfl⟩ : syracuseStep 912707 = 1369061) B1369061
theorem B290171 : Blo 179801 290171 := bstep (se 1 (by rfl) ⟨217628, by rfl⟩ : syracuseStep 290171 = 435257) B435257
theorem B97643981 : Blo 179801 97643981 := bstep (se 3 (by rfl) ⟨18308246, by rfl⟩ : syracuseStep 97643981 = 36616493) B36616493
theorem B978425 : Blo 179801 978425 := bstep (se 2 (by rfl) ⟨366909, by rfl⟩ : syracuseStep 978425 = 733819) B733819
theorem B12906161 : Blo 179801 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B487147 : Blo 179801 487147 := bstep (se 1 (by rfl) ⟨365360, by rfl⟩ : syracuseStep 487147 = 730721) B730721
theorem B913193 : Blo 179801 913193 := bstep (se 2 (by rfl) ⟨342447, by rfl⟩ : syracuseStep 913193 = 684895) B684895
theorem B257833 : Blo 179801 257833 := bstep (se 2 (by rfl) ⟨96687, by rfl⟩ : syracuseStep 257833 = 193375) B193375
theorem B519983 : Blo 179801 519983 := bstep (se 1 (by rfl) ⟨389987, by rfl⟩ : syracuseStep 519983 = 779975) B779975
theorem B716701 : Blo 179801 716701 := bstep (se 3 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 716701 = 268763) B268763
theorem B3960899 : Blo 179801 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B880969 : Blo 179801 880969 := bstep (se 2 (by rfl) ⟨330363, by rfl⟩ : syracuseStep 880969 = 660727) B660727
theorem B684395 : Blo 179801 684395 := bstep (se 1 (by rfl) ⟨513296, by rfl⟩ : syracuseStep 684395 = 1026593) B1026593
theorem B520673 : Blo 179801 520673 := bstep (se 2 (by rfl) ⟨195252, by rfl⟩ : syracuseStep 520673 = 390505) B390505
theorem B520825 : Blo 179801 520825 := bstep (se 2 (by rfl) ⟨195309, by rfl⟩ : syracuseStep 520825 = 390619) B390619
theorem B455503 : Blo 179801 455503 := bstep (se 1 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 455503 = 683255) B683255
theorem B914489 : Blo 179801 914489 := bstep (se 2 (by rfl) ⟨342933, by rfl⟩ : syracuseStep 914489 = 685867) B685867
theorem B455777 : Blo 179801 455777 := bstep (se 2 (by rfl) ⟨170916, by rfl⟩ : syracuseStep 455777 = 341833) B341833
theorem B685199 : Blo 179801 685199 := bstep (se 1 (by rfl) ⟨513899, by rfl⟩ : syracuseStep 685199 = 1027799) B1027799
theorem B259291 : Blo 179801 259291 := bstep (se 1 (by rfl) ⟨194468, by rfl⟩ : syracuseStep 259291 = 388937) B388937
theorem B882029 : Blo 179801 882029 := bstep (se 3 (by rfl) ⟨165380, by rfl⟩ : syracuseStep 882029 = 330761) B330761
theorem B325001 : Blo 179801 325001 := bstep (se 2 (by rfl) ⟨121875, by rfl⟩ : syracuseStep 325001 = 243751) B243751
theorem B456151 : Blo 179801 456151 := bstep (se 1 (by rfl) ⟨342113, by rfl⟩ : syracuseStep 456151 = 684227) B684227
theorem B390739 : Blo 179801 390739 := bstep (se 1 (by rfl) ⟨293054, by rfl⟩ : syracuseStep 390739 = 586109) B586109
theorem B620189 : Blo 179801 620189 := bstep (se 3 (by rfl) ⟨116285, by rfl⟩ : syracuseStep 620189 = 232571) B232571
theorem B456455 : Blo 179801 456455 := bstep (se 1 (by rfl) ⟨342341, by rfl⟩ : syracuseStep 456455 = 684683) B684683
theorem B390919 : Blo 179801 390919 := bstep (se 1 (by rfl) ⟨293189, by rfl⟩ : syracuseStep 390919 = 586379) B586379
theorem B5928889 : Blo 179801 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B489577 : Blo 179801 489577 := bstep (se 2 (by rfl) ⟨183591, by rfl⟩ : syracuseStep 489577 = 367183) B367183
theorem B2357579 : Blo 179801 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B457235 : Blo 179801 457235 := bstep (se 1 (by rfl) ⟨342926, by rfl⟩ : syracuseStep 457235 = 685853) B685853
theorem B686839 : Blo 179801 686839 := bstep (se 1 (by rfl) ⟨515129, by rfl⟩ : syracuseStep 686839 = 1030259) B1030259
theorem B1309459 : Blo 179801 1309459 := bstep (se 1 (by rfl) ⟨982094, by rfl⟩ : syracuseStep 1309459 = 1964189) B1964189
theorem B1539101 : Blo 179801 1539101 := bstep (se 3 (by rfl) ⟨288581, by rfl⟩ : syracuseStep 1539101 = 577163) B577163
theorem B687143 : Blo 179801 687143 := bstep (se 1 (by rfl) ⟨515357, by rfl⟩ : syracuseStep 687143 = 1030715) B1030715
theorem B916595 : Blo 179801 916595 := bstep (se 1 (by rfl) ⟨687446, by rfl⟩ : syracuseStep 916595 = 1374893) B1374893
theorem B5012603 : Blo 179801 5012603 := bstep (se 1 (by rfl) ⟨3759452, by rfl⟩ : syracuseStep 5012603 = 7518905) B7518905
theorem B261415 : Blo 179801 261415 := bstep (se 1 (by rfl) ⟨196061, by rfl⟩ : syracuseStep 261415 = 392123) B392123
theorem B425785 : Blo 179801 425785 := bstep (se 2 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 425785 = 319339) B319339
theorem B917405 : Blo 179801 917405 := bstep (se 3 (by rfl) ⟨172013, by rfl⟩ : syracuseStep 917405 = 344027) B344027
theorem B524519 : Blo 179801 524519 := bstep (se 1 (by rfl) ⟨393389, by rfl⟩ : syracuseStep 524519 = 786779) B786779
theorem B9470189 : Blo 179801 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B1114393 : Blo 179801 1114393 := bstep (se 2 (by rfl) ⟨417897, by rfl⟩ : syracuseStep 1114393 = 835795) B835795
theorem B3736115 : Blo 179801 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B557675 : Blo 179801 557675 := bstep (se 1 (by rfl) ⟨418256, by rfl⟩ : syracuseStep 557675 = 836513) B836513
theorem B688769 : Blo 179801 688769 := bstep (se 2 (by rfl) ⟨258288, by rfl⟩ : syracuseStep 688769 = 516577) B516577
theorem B492455 : Blo 179801 492455 := bstep (se 1 (by rfl) ⟨369341, by rfl⟩ : syracuseStep 492455 = 738683) B738683
theorem B230455 : Blo 179801 230455 := bstep (se 1 (by rfl) ⟨172841, by rfl⟩ : syracuseStep 230455 = 345683) B345683
theorem B1738871 : Blo 179801 1738871 := bstep (se 1 (by rfl) ⟨1304153, by rfl⟩ : syracuseStep 1738871 = 2608307) B2608307
theorem B460991 : Blo 179801 460991 := bstep (se 1 (by rfl) ⟨345743, by rfl⟩ : syracuseStep 460991 = 691487) B691487
theorem B2919235 : Blo 179801 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B691031 : Blo 179801 691031 := bstep (se 1 (by rfl) ⟨518273, by rfl⟩ : syracuseStep 691031 = 1036547) B1036547
theorem B1575973 : Blo 179801 1575973 := bstep (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) B295495
theorem B494639 : Blo 179801 494639 := bstep (se 1 (by rfl) ⟨370979, by rfl⟩ : syracuseStep 494639 = 741959) B741959
theorem B1543475 : Blo 179801 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B659017 : Blo 179801 659017 := bstep (se 2 (by rfl) ⟨247131, by rfl⟩ : syracuseStep 659017 = 494263) B494263
theorem B462611 : Blo 179801 462611 := bstep (se 1 (by rfl) ⟨346958, by rfl⟩ : syracuseStep 462611 = 693917) B693917
theorem B462631 : Blo 179801 462631 := bstep (se 1 (by rfl) ⟨346973, by rfl⟩ : syracuseStep 462631 = 693947) B693947
theorem B1380239 : Blo 179801 1380239 := bstep (se 1 (by rfl) ⟨1035179, by rfl⟩ : syracuseStep 1380239 = 2070359) B2070359
theorem B2068901 : Blo 179801 2068901 := bstep (se 4 (by rfl) ⟨193959, by rfl⟩ : syracuseStep 2068901 = 387919) B387919
theorem B1184215 : Blo 179801 1184215 := bstep (se 1 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 1184215 = 1776323) B1776323
theorem B660215 : Blo 179801 660215 := bstep (se 1 (by rfl) ⟨495161, by rfl⟩ : syracuseStep 660215 = 990323) B990323
theorem B529193 : Blo 179801 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B463745 : Blo 179801 463745 := bstep (se 2 (by rfl) ⟨173904, by rfl⟩ : syracuseStep 463745 = 347809) B347809
theorem B463927 : Blo 179801 463927 := bstep (se 1 (by rfl) ⟨347945, by rfl⟩ : syracuseStep 463927 = 695891) B695891
theorem B627887 : Blo 179801 627887 := bstep (se 1 (by rfl) ⟨470915, by rfl⟩ : syracuseStep 627887 = 941831) B941831
theorem B4199633 : Blo 179801 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B955601 : Blo 179801 955601 := bstep (se 2 (by rfl) ⟨358350, by rfl⟩ : syracuseStep 955601 = 716701) B716701
theorem B9934073 : Blo 179801 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B1152481 : Blo 179801 1152481 := bstep (se 2 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 1152481 = 864361) B864361
theorem B1021409 : Blo 179801 1021409 := bstep (se 2 (by rfl) ⟨383028, by rfl⟩ : syracuseStep 1021409 = 766057) B766057
theorem B202351 : Blo 179801 202351 := bstep (se 1 (by rfl) ⟨151763, by rfl⟩ : syracuseStep 202351 = 303527) B303527
theorem B464555 : Blo 179801 464555 := bstep (se 1 (by rfl) ⟨348416, by rfl⟩ : syracuseStep 464555 = 696833) B696833
theorem B202459 : Blo 179801 202459 := bstep (se 1 (by rfl) ⟨151844, by rfl⟩ : syracuseStep 202459 = 303689) B303689
theorem B464879 : Blo 179801 464879 := bstep (se 1 (by rfl) ⟨348659, by rfl⟩ : syracuseStep 464879 = 697319) B697319
theorem B694433 : Blo 179801 694433 := bstep (se 2 (by rfl) ⟨260412, by rfl⟩ : syracuseStep 694433 = 520825) B520825
theorem B4462937 : Blo 179801 4462937 := bstep (se 2 (by rfl) ⟨1673601, by rfl⟩ : syracuseStep 4462937 = 3347203) B3347203
theorem B825707 : Blo 179801 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B203611 : Blo 179801 203611 := bstep (se 1 (by rfl) ⟨152708, by rfl⟩ : syracuseStep 203611 = 305417) B305417
theorem B924857 : Blo 179801 924857 := bstep (se 2 (by rfl) ⟨346821, by rfl⟩ : syracuseStep 924857 = 693643) B693643
theorem B269735 : Blo 179801 269735 := bstep (se 1 (by rfl) ⟨202301, by rfl⟩ : syracuseStep 269735 = 404603) B404603
theorem B695783 : Blo 179801 695783 := bstep (se 1 (by rfl) ⟨521837, by rfl⟩ : syracuseStep 695783 = 1043675) B1043675
theorem B269819 : Blo 179801 269819 := bstep (se 1 (by rfl) ⟨202364, by rfl⟩ : syracuseStep 269819 = 404729) B404729
theorem B269915 : Blo 179801 269915 := bstep (se 1 (by rfl) ⟨202436, by rfl⟩ : syracuseStep 269915 = 404873) B404873
theorem B269999 : Blo 179801 269999 := bstep (se 1 (by rfl) ⟨202499, by rfl⟩ : syracuseStep 269999 = 404999) B404999
theorem B270119 : Blo 179801 270119 := bstep (se 1 (by rfl) ⟨202589, by rfl⟩ : syracuseStep 270119 = 405179) B405179
theorem B204583 : Blo 179801 204583 := bstep (se 1 (by rfl) ⟨153437, by rfl⟩ : syracuseStep 204583 = 306875) B306875
theorem B270203 : Blo 179801 270203 := bstep (se 1 (by rfl) ⟨202652, by rfl⟩ : syracuseStep 270203 = 405305) B405305
theorem B7905185 : Blo 179801 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B270623 : Blo 179801 270623 := bstep (se 1 (by rfl) ⟨202967, by rfl⟩ : syracuseStep 270623 = 405935) B405935
theorem B270647 : Blo 179801 270647 := bstep (se 1 (by rfl) ⟨202985, by rfl⟩ : syracuseStep 270647 = 405971) B405971
theorem B270719 : Blo 179801 270719 := bstep (se 1 (by rfl) ⟨203039, by rfl⟩ : syracuseStep 270719 = 406079) B406079
theorem B270791 : Blo 179801 270791 := bstep (se 1 (by rfl) ⟨203093, by rfl⟩ : syracuseStep 270791 = 406187) B406187
theorem B303851 : Blo 179801 303851 := bstep (se 1 (by rfl) ⟨227888, by rfl⟩ : syracuseStep 303851 = 455777) B455777
theorem B16851725 : Blo 179801 16851725 := bstep (se 3 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 16851725 = 6319397) B6319397
theorem B271145 : Blo 179801 271145 := bstep (se 2 (by rfl) ⟨101679, by rfl⟩ : syracuseStep 271145 = 203359) B203359
theorem B271151 : Blo 179801 271151 := bstep (se 1 (by rfl) ⟨203363, by rfl⟩ : syracuseStep 271151 = 406727) B406727
theorem B271271 : Blo 179801 271271 := bstep (se 1 (by rfl) ⟨203453, by rfl⟩ : syracuseStep 271271 = 406907) B406907
theorem B205735 : Blo 179801 205735 := bstep (se 1 (by rfl) ⟨154301, by rfl⟩ : syracuseStep 205735 = 308603) B308603
theorem B271355 : Blo 179801 271355 := bstep (se 1 (by rfl) ⟨203516, by rfl⟩ : syracuseStep 271355 = 407033) B407033
theorem B1745945 : Blo 179801 1745945 := bstep (se 2 (by rfl) ⟨654729, by rfl⟩ : syracuseStep 1745945 = 1309459) B1309459
theorem B271415 : Blo 179801 271415 := bstep (se 1 (by rfl) ⟨203561, by rfl⟩ : syracuseStep 271415 = 407123) B407123
theorem B304303 : Blo 179801 304303 := bstep (se 1 (by rfl) ⟨228227, by rfl⟩ : syracuseStep 304303 = 456455) B456455
theorem B271535 : Blo 179801 271535 := bstep (se 1 (by rfl) ⟨203651, by rfl⟩ : syracuseStep 271535 = 407303) B407303
theorem B271943 : Blo 179801 271943 := bstep (se 1 (by rfl) ⟨203957, by rfl⟩ : syracuseStep 271943 = 407915) B407915
theorem B272039 : Blo 179801 272039 := bstep (se 1 (by rfl) ⟨204029, by rfl⟩ : syracuseStep 272039 = 408059) B408059
theorem B304823 : Blo 179801 304823 := bstep (se 1 (by rfl) ⟨228617, by rfl⟩ : syracuseStep 304823 = 457235) B457235
theorem B272123 : Blo 179801 272123 := bstep (se 1 (by rfl) ⟨204092, by rfl⟩ : syracuseStep 272123 = 408185) B408185
theorem B272159 : Blo 179801 272159 := bstep (se 1 (by rfl) ⟨204119, by rfl⟩ : syracuseStep 272159 = 408239) B408239
theorem B272207 : Blo 179801 272207 := bstep (se 1 (by rfl) ⟨204155, by rfl⟩ : syracuseStep 272207 = 408311) B408311
theorem B272327 : Blo 179801 272327 := bstep (se 1 (by rfl) ⟨204245, by rfl⟩ : syracuseStep 272327 = 408491) B408491
theorem B1026067 : Blo 179801 1026067 := bstep (se 1 (by rfl) ⟨769550, by rfl⟩ : syracuseStep 1026067 = 1539101) B1539101
theorem B2074733 : Blo 179801 2074733 := bstep (se 3 (by rfl) ⟨389012, by rfl⟩ : syracuseStep 2074733 = 778025) B778025
theorem B272681 : Blo 179801 272681 := bstep (se 2 (by rfl) ⟨102255, by rfl⟩ : syracuseStep 272681 = 204511) B204511
theorem B272687 : Blo 179801 272687 := bstep (se 1 (by rfl) ⟨204515, by rfl⟩ : syracuseStep 272687 = 409031) B409031
theorem B567713 : Blo 179801 567713 := bstep (se 2 (by rfl) ⟨212892, by rfl⟩ : syracuseStep 567713 = 425785) B425785
theorem B272927 : Blo 179801 272927 := bstep (se 1 (by rfl) ⟨204695, by rfl⟩ : syracuseStep 272927 = 409391) B409391
theorem B306011 : Blo 179801 306011 := bstep (se 1 (by rfl) ⟨229508, by rfl⟩ : syracuseStep 306011 = 459017) B459017
theorem B273311 : Blo 179801 273311 := bstep (se 1 (by rfl) ⟨204983, by rfl⟩ : syracuseStep 273311 = 409967) B409967
theorem B273359 : Blo 179801 273359 := bstep (se 1 (by rfl) ⟨205019, by rfl⟩ : syracuseStep 273359 = 410039) B410039
theorem B273449 : Blo 179801 273449 := bstep (se 2 (by rfl) ⟨102543, by rfl⟩ : syracuseStep 273449 = 205087) B205087
theorem B273455 : Blo 179801 273455 := bstep (se 1 (by rfl) ⟨205091, by rfl⟩ : syracuseStep 273455 = 410183) B410183
theorem B306247 : Blo 179801 306247 := bstep (se 1 (by rfl) ⟨229685, by rfl⟩ : syracuseStep 306247 = 459371) B459371
theorem B273479 : Blo 179801 273479 := bstep (se 1 (by rfl) ⟨205109, by rfl⟩ : syracuseStep 273479 = 410219) B410219
theorem B273743 : Blo 179801 273743 := bstep (se 1 (by rfl) ⟨205307, by rfl⟩ : syracuseStep 273743 = 410615) B410615
theorem B273833 : Blo 179801 273833 := bstep (se 2 (by rfl) ⟨102687, by rfl⟩ : syracuseStep 273833 = 205375) B205375
theorem B306679 : Blo 179801 306679 := bstep (se 1 (by rfl) ⟨230009, by rfl⟩ : syracuseStep 306679 = 460019) B460019
theorem B273983 : Blo 179801 273983 := bstep (se 1 (by rfl) ⟨205487, by rfl⟩ : syracuseStep 273983 = 410975) B410975
theorem B929555 : Blo 179801 929555 := bstep (se 1 (by rfl) ⟨697166, by rfl⟩ : syracuseStep 929555 = 1394333) B1394333
theorem B405287 : Blo 179801 405287 := bstep (se 1 (by rfl) ⟨303965, by rfl⟩ : syracuseStep 405287 = 607931) B607931
theorem B306983 : Blo 179801 306983 := bstep (se 1 (by rfl) ⟨230237, by rfl⟩ : syracuseStep 306983 = 460475) B460475
theorem B274247 : Blo 179801 274247 := bstep (se 1 (by rfl) ⟨205685, by rfl⟩ : syracuseStep 274247 = 411371) B411371
theorem B1159019 : Blo 179801 1159019 := bstep (se 1 (by rfl) ⟨869264, by rfl⟩ : syracuseStep 1159019 = 1738529) B1738529
theorem B274331 : Blo 179801 274331 := bstep (se 1 (by rfl) ⟨205748, by rfl⟩ : syracuseStep 274331 = 411497) B411497
theorem B1388461 : Blo 179801 1388461 := bstep (se 3 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 1388461 = 520673) B520673
theorem B274895 : Blo 179801 274895 := bstep (se 1 (by rfl) ⟨206171, by rfl⟩ : syracuseStep 274895 = 412343) B412343
theorem B307705 : Blo 179801 307705 := bstep (se 2 (by rfl) ⟨115389, by rfl⟩ : syracuseStep 307705 = 230779) B230779
theorem B274937 : Blo 179801 274937 := bstep (se 2 (by rfl) ⟨103101, by rfl⟩ : syracuseStep 274937 = 206203) B206203
theorem B275039 : Blo 179801 275039 := bstep (se 1 (by rfl) ⟨206279, by rfl⟩ : syracuseStep 275039 = 412559) B412559
theorem B307975 : Blo 179801 307975 := bstep (se 1 (by rfl) ⟨230981, by rfl⟩ : syracuseStep 307975 = 461963) B461963
theorem B406313 : Blo 179801 406313 := bstep (se 2 (by rfl) ⟨152367, by rfl⟩ : syracuseStep 406313 = 304735) B304735
theorem B308009 : Blo 179801 308009 := bstep (se 2 (by rfl) ⟨115503, by rfl⟩ : syracuseStep 308009 = 231007) B231007
theorem B2077649 : Blo 179801 2077649 := bstep (se 2 (by rfl) ⟨779118, by rfl⟩ : syracuseStep 2077649 = 1558237) B1558237
theorem B406583 : Blo 179801 406583 := bstep (se 1 (by rfl) ⟨304937, by rfl⟩ : syracuseStep 406583 = 609875) B609875
theorem B308279 : Blo 179801 308279 := bstep (se 1 (by rfl) ⟨231209, by rfl⟩ : syracuseStep 308279 = 462419) B462419
theorem B275519 : Blo 179801 275519 := bstep (se 1 (by rfl) ⟨206639, by rfl⟩ : syracuseStep 275519 = 413279) B413279
theorem B406601 : Blo 179801 406601 := bstep (se 2 (by rfl) ⟨152475, by rfl⟩ : syracuseStep 406601 = 304951) B304951
theorem B275561 : Blo 179801 275561 := bstep (se 2 (by rfl) ⟨103335, by rfl⟩ : syracuseStep 275561 = 206671) B206671
theorem B275663 : Blo 179801 275663 := bstep (se 1 (by rfl) ⟨206747, by rfl⟩ : syracuseStep 275663 = 413495) B413495
theorem B2307527 : Blo 179801 2307527 := bstep (se 1 (by rfl) ⟨1730645, by rfl⟩ : syracuseStep 2307527 = 3461291) B3461291
theorem B1553863 : Blo 179801 1553863 := bstep (se 1 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 1553863 = 2330795) B2330795
theorem B1160887 : Blo 179801 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B309055 : Blo 179801 309055 := bstep (se 1 (by rfl) ⟨231791, by rfl⟩ : syracuseStep 309055 = 463583) B463583
theorem B1161479 : Blo 179801 1161479 := bstep (se 1 (by rfl) ⟨871109, by rfl⟩ : syracuseStep 1161479 = 1742219) B1742219
theorem B309791 : Blo 179801 309791 := bstep (se 1 (by rfl) ⟨232343, by rfl⟩ : syracuseStep 309791 = 464687) B464687
theorem B309865 : Blo 179801 309865 := bstep (se 2 (by rfl) ⟨116199, by rfl⟩ : syracuseStep 309865 = 232399) B232399
theorem B408527 : Blo 179801 408527 := bstep (se 1 (by rfl) ⟨306395, by rfl⟩ : syracuseStep 408527 = 612791) B612791
theorem B408545 : Blo 179801 408545 := bstep (se 2 (by rfl) ⟨153204, by rfl⟩ : syracuseStep 408545 = 306409) B306409
theorem B408617 : Blo 179801 408617 := bstep (se 2 (by rfl) ⟨153231, by rfl⟩ : syracuseStep 408617 = 306463) B306463
theorem B1326365 : Blo 179801 1326365 := bstep (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) B497387
theorem B1948967 : Blo 179801 1948967 := bstep (se 1 (by rfl) ⟨1461725, by rfl⟩ : syracuseStep 1948967 = 2923451) B2923451
theorem B179803 : Blo 179801 179803 := bstep (se 1 (by rfl) ⟨134852, by rfl⟩ : syracuseStep 179803 = 269705) B269705
theorem B1162937 : Blo 179801 1162937 := bstep (se 2 (by rfl) ⟨436101, by rfl⟩ : syracuseStep 1162937 = 872203) B872203
theorem B343777 : Blo 179801 343777 := bstep (se 2 (by rfl) ⟨128916, by rfl⟩ : syracuseStep 343777 = 257833) B257833
theorem B3456827 : Blo 179801 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B180039 : Blo 179801 180039 := bstep (se 1 (by rfl) ⟨135029, by rfl⟩ : syracuseStep 180039 = 270059) B270059
theorem B180191 : Blo 179801 180191 := bstep (se 1 (by rfl) ⟨135143, by rfl⟩ : syracuseStep 180191 = 270287) B270287
theorem B1130635 : Blo 179801 1130635 := bstep (se 1 (by rfl) ⟨847976, by rfl⟩ : syracuseStep 1130635 = 1695953) B1695953
theorem B180455 : Blo 179801 180455 := bstep (se 1 (by rfl) ⟨135341, by rfl⟩ : syracuseStep 180455 = 270683) B270683
theorem B180607 : Blo 179801 180607 := bstep (se 1 (by rfl) ⟨135455, by rfl⟩ : syracuseStep 180607 = 270911) B270911
theorem B180687 : Blo 179801 180687 := bstep (se 1 (by rfl) ⟨135515, by rfl⟩ : syracuseStep 180687 = 271031) B271031
theorem B2605537 : Blo 179801 2605537 := bstep (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) B1954153
theorem B180839 : Blo 179801 180839 := bstep (se 1 (by rfl) ⟨135629, by rfl⟩ : syracuseStep 180839 = 271259) B271259
theorem B5259977 : Blo 179801 5259977 := bstep (se 2 (by rfl) ⟨1972491, by rfl⟩ : syracuseStep 5259977 = 3944983) B3944983
theorem B181103 : Blo 179801 181103 := bstep (se 1 (by rfl) ⟨135827, by rfl⟩ : syracuseStep 181103 = 271655) B271655
theorem B181159 : Blo 179801 181159 := bstep (se 1 (by rfl) ⟨135869, by rfl⟩ : syracuseStep 181159 = 271739) B271739
theorem B344999 : Blo 179801 344999 := bstep (se 1 (by rfl) ⟨258749, by rfl⟩ : syracuseStep 344999 = 517499) B517499
theorem B410579 : Blo 179801 410579 := bstep (se 1 (by rfl) ⟨307934, by rfl⟩ : syracuseStep 410579 = 615869) B615869
theorem B181243 : Blo 179801 181243 := bstep (se 1 (by rfl) ⟨135932, by rfl⟩ : syracuseStep 181243 = 271865) B271865
theorem B181311 : Blo 179801 181311 := bstep (se 1 (by rfl) ⟨135983, by rfl⟩ : syracuseStep 181311 = 271967) B271967
theorem B607337 : Blo 179801 607337 := bstep (se 2 (by rfl) ⟨227751, by rfl⟩ : syracuseStep 607337 = 455503) B455503
theorem B181455 : Blo 179801 181455 := bstep (se 1 (by rfl) ⟨136091, by rfl⟩ : syracuseStep 181455 = 272183) B272183
theorem B410831 : Blo 179801 410831 := bstep (se 1 (by rfl) ⟨308123, by rfl⟩ : syracuseStep 410831 = 616247) B616247
theorem B181659 : Blo 179801 181659 := bstep (se 1 (by rfl) ⟨136244, by rfl⟩ : syracuseStep 181659 = 272489) B272489
theorem B411155 : Blo 179801 411155 := bstep (se 1 (by rfl) ⟨308366, by rfl⟩ : syracuseStep 411155 = 616733) B616733
theorem B181871 : Blo 179801 181871 := bstep (se 1 (by rfl) ⟨136403, by rfl⟩ : syracuseStep 181871 = 272807) B272807
theorem B345721 : Blo 179801 345721 := bstep (se 2 (by rfl) ⟨129645, by rfl⟩ : syracuseStep 345721 = 259291) B259291
theorem B181927 : Blo 179801 181927 := bstep (se 1 (by rfl) ⟨136445, by rfl⟩ : syracuseStep 181927 = 272891) B272891
theorem B313055 : Blo 179801 313055 := bstep (se 1 (by rfl) ⟨234791, by rfl⟩ : syracuseStep 313055 = 469583) B469583
theorem B182011 : Blo 179801 182011 := bstep (se 1 (by rfl) ⟨136508, by rfl⟩ : syracuseStep 182011 = 273017) B273017
theorem B182047 : Blo 179801 182047 := bstep (se 1 (by rfl) ⟨136535, by rfl⟩ : syracuseStep 182047 = 273071) B273071
theorem B182079 : Blo 179801 182079 := bstep (se 1 (by rfl) ⟨136559, by rfl⟩ : syracuseStep 182079 = 273119) B273119
theorem B313151 : Blo 179801 313151 := bstep (se 1 (by rfl) ⟨234863, by rfl⟩ : syracuseStep 313151 = 469727) B469727
theorem B608201 : Blo 179801 608201 := bstep (se 2 (by rfl) ⟨228075, by rfl⟩ : syracuseStep 608201 = 456151) B456151
theorem B182255 : Blo 179801 182255 := bstep (se 1 (by rfl) ⟨136691, by rfl⟩ : syracuseStep 182255 = 273383) B273383
theorem B182427 : Blo 179801 182427 := bstep (se 1 (by rfl) ⟨136820, by rfl⟩ : syracuseStep 182427 = 273641) B273641
theorem B182463 : Blo 179801 182463 := bstep (se 1 (by rfl) ⟨136847, by rfl⟩ : syracuseStep 182463 = 273695) B273695
theorem B411839 : Blo 179801 411839 := bstep (se 1 (by rfl) ⟨308879, by rfl⟩ : syracuseStep 411839 = 617759) B617759
theorem B608471 : Blo 179801 608471 := bstep (se 1 (by rfl) ⟨456353, by rfl⟩ : syracuseStep 608471 = 912707) B912707
theorem B182575 : Blo 179801 182575 := bstep (se 1 (by rfl) ⟨136931, by rfl⟩ : syracuseStep 182575 = 273863) B273863
theorem B65095987 : Blo 179801 65095987 := bstep (se 1 (by rfl) ⟨48821990, by rfl⟩ : syracuseStep 65095987 = 97643981) B97643981
theorem B8604107 : Blo 179801 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B608795 : Blo 179801 608795 := bstep (se 1 (by rfl) ⟨456596, by rfl⟩ : syracuseStep 608795 = 913193) B913193
theorem B182811 : Blo 179801 182811 := bstep (se 1 (by rfl) ⟨137108, by rfl⟩ : syracuseStep 182811 = 274217) B274217
theorem B346655 : Blo 179801 346655 := bstep (se 1 (by rfl) ⟨259991, by rfl⟩ : syracuseStep 346655 = 519983) B519983
theorem B182815 : Blo 179801 182815 := bstep (se 1 (by rfl) ⟨137111, by rfl⟩ : syracuseStep 182815 = 274223) B274223
theorem B2640599 : Blo 179801 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B576343 : Blo 179801 576343 := bstep (se 1 (by rfl) ⟨432257, by rfl⟩ : syracuseStep 576343 = 864515) B864515
theorem B183131 : Blo 179801 183131 := bstep (se 1 (by rfl) ⟨137348, by rfl⟩ : syracuseStep 183131 = 274697) B274697
theorem B183199 : Blo 179801 183199 := bstep (se 1 (by rfl) ⟨137399, by rfl⟩ : syracuseStep 183199 = 274799) B274799
theorem B183343 : Blo 179801 183343 := bstep (se 1 (by rfl) ⟨137507, by rfl⟩ : syracuseStep 183343 = 275015) B275015
theorem B183367 : Blo 179801 183367 := bstep (se 1 (by rfl) ⟨137525, by rfl⟩ : syracuseStep 183367 = 275051) B275051
theorem B412793 : Blo 179801 412793 := bstep (se 2 (by rfl) ⟨154797, by rfl⟩ : syracuseStep 412793 = 309595) B309595
theorem B183519 : Blo 179801 183519 := bstep (se 1 (by rfl) ⟨137639, by rfl⟩ : syracuseStep 183519 = 275279) B275279
theorem B1756403 : Blo 179801 1756403 := bstep (se 1 (by rfl) ⟨1317302, by rfl⟩ : syracuseStep 1756403 = 2634605) B2634605
theorem B609659 : Blo 179801 609659 := bstep (se 1 (by rfl) ⟨457244, by rfl⟩ : syracuseStep 609659 = 914489) B914489
theorem B183783 : Blo 179801 183783 := bstep (se 1 (by rfl) ⟨137837, by rfl⟩ : syracuseStep 183783 = 275675) B275675
theorem B216667 : Blo 179801 216667 := bstep (se 1 (by rfl) ⟨162500, by rfl⟩ : syracuseStep 216667 = 325001) B325001
theorem B413459 : Blo 179801 413459 := bstep (se 1 (by rfl) ⟨310094, by rfl⟩ : syracuseStep 413459 = 620189) B620189
theorem B4214585 : Blo 179801 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B577523 : Blo 179801 577523 := bstep (se 1 (by rfl) ⟨433142, by rfl⟩ : syracuseStep 577523 = 866285) B866285
theorem B3920075 : Blo 179801 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B348553 : Blo 179801 348553 := bstep (se 2 (by rfl) ⟨130707, by rfl⟩ : syracuseStep 348553 = 261415) B261415
theorem B774643 : Blo 179801 774643 := bstep (se 1 (by rfl) ⟨580982, by rfl⟩ : syracuseStep 774643 = 1161965) B1161965
theorem B611063 : Blo 179801 611063 := bstep (se 1 (by rfl) ⟨458297, by rfl⟩ : syracuseStep 611063 = 916595) B916595
theorem B414505 : Blo 179801 414505 := bstep (se 2 (by rfl) ⟨155439, by rfl⟩ : syracuseStep 414505 = 310879) B310879
theorem B4510505 : Blo 179801 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B611603 : Blo 179801 611603 := bstep (se 1 (by rfl) ⟨458702, by rfl⟩ : syracuseStep 611603 = 917405) B917405
theorem B513479 : Blo 179801 513479 := bstep (se 1 (by rfl) ⟨385109, by rfl⟩ : syracuseStep 513479 = 770219) B770219
theorem B612143 : Blo 179801 612143 := bstep (se 1 (by rfl) ⟨459107, by rfl⟩ : syracuseStep 612143 = 918215) B918215
theorem B1301129 : Blo 179801 1301129 := bstep (se 2 (by rfl) ⟨487923, by rfl⟩ : syracuseStep 1301129 = 975847) B975847
theorem B2087855 : Blo 179801 2087855 := bstep (se 1 (by rfl) ⟨1565891, by rfl⟩ : syracuseStep 2087855 = 3131783) B3131783
theorem B384041 : Blo 179801 384041 := bstep (se 2 (by rfl) ⟨144015, by rfl⟩ : syracuseStep 384041 = 288031) B288031
theorem B613979 : Blo 179801 613979 := bstep (se 1 (by rfl) ⟨460484, by rfl⟩ : syracuseStep 613979 = 920969) B920969
theorem B1171223 : Blo 179801 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B614681 : Blo 179801 614681 := bstep (se 2 (by rfl) ⟨230505, by rfl⟩ : syracuseStep 614681 = 461011) B461011
theorem B2089313 : Blo 179801 2089313 := bstep (se 2 (by rfl) ⟨783492, by rfl⟩ : syracuseStep 2089313 = 1566985) B1566985
theorem B614843 : Blo 179801 614843 := bstep (se 1 (by rfl) ⟨461132, by rfl⟩ : syracuseStep 614843 = 922265) B922265
theorem B21652103 : Blo 179801 21652103 := bstep (se 1 (by rfl) ⟨16239077, by rfl⟩ : syracuseStep 21652103 = 32478155) B32478155
theorem B2319313 : Blo 179801 2319313 := bstep (se 2 (by rfl) ⟨869742, by rfl⟩ : syracuseStep 2319313 = 1739485) B1739485
theorem B517727 : Blo 179801 517727 := bstep (se 1 (by rfl) ⟨388295, by rfl⟩ : syracuseStep 517727 = 776591) B776591
theorem B616031 : Blo 179801 616031 := bstep (se 1 (by rfl) ⟨462023, by rfl⟩ : syracuseStep 616031 = 924047) B924047
theorem B288377 : Blo 179801 288377 := bstep (se 2 (by rfl) ⟨108141, by rfl⟩ : syracuseStep 288377 = 216283) B216283
theorem B1042105 : Blo 179801 1042105 := bstep (se 2 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 1042105 = 781579) B781579
theorem B288479 : Blo 179801 288479 := bstep (se 1 (by rfl) ⟨216359, by rfl⟩ : syracuseStep 288479 = 432719) B432719
theorem B2320649 : Blo 179801 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B649529 : Blo 179801 649529 := bstep (se 2 (by rfl) ⟨243573, by rfl⟩ : syracuseStep 649529 = 487147) B487147
theorem B1567259 : Blo 179801 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B584263 : Blo 179801 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B1764089 : Blo 179801 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B256927 : Blo 179801 256927 := bstep (se 1 (by rfl) ⟨192695, by rfl⟩ : syracuseStep 256927 = 385391) B385391
theorem B617435 : Blo 179801 617435 := bstep (se 1 (by rfl) ⟨463076, by rfl⟩ : syracuseStep 617435 = 926153) B926153
theorem B1174625 : Blo 179801 1174625 := bstep (se 2 (by rfl) ⟨440484, by rfl⟩ : syracuseStep 1174625 = 880969) B880969
theorem B519311 : Blo 179801 519311 := bstep (se 1 (by rfl) ⟨389483, by rfl⟩ : syracuseStep 519311 = 778967) B778967
theorem B519367 : Blo 179801 519367 := bstep (se 1 (by rfl) ⟨389525, by rfl⟩ : syracuseStep 519367 = 779051) B779051
theorem B617705 : Blo 179801 617705 := bstep (se 2 (by rfl) ⟨231639, by rfl⟩ : syracuseStep 617705 = 463279) B463279
theorem B585083 : Blo 179801 585083 := bstep (se 1 (by rfl) ⟨438812, by rfl⟩ : syracuseStep 585083 = 877625) B877625
theorem B2354579 : Blo 179801 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B617975 : Blo 179801 617975 := bstep (se 1 (by rfl) ⟨463481, by rfl⟩ : syracuseStep 617975 = 926963) B926963
theorem B355835 : Blo 179801 355835 := bstep (se 1 (by rfl) ⟨266876, by rfl⟩ : syracuseStep 355835 = 533753) B533753
theorem B290299 : Blo 179801 290299 := bstep (se 1 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 290299 = 435449) B435449
theorem B84275315 : Blo 179801 84275315 := bstep (se 1 (by rfl) ⟨63206486, by rfl⟩ : syracuseStep 84275315 = 126412973) B126412973
theorem B618625 : Blo 179801 618625 := bstep (se 2 (by rfl) ⟨231984, by rfl⟩ : syracuseStep 618625 = 463969) B463969
theorem B880951 : Blo 179801 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B619001 : Blo 179801 619001 := bstep (se 2 (by rfl) ⟨232125, by rfl⟩ : syracuseStep 619001 = 464251) B464251
theorem B914003 : Blo 179801 914003 := bstep (se 1 (by rfl) ⟨685502, by rfl⟩ : syracuseStep 914003 = 1371005) B1371005
theorem B619103 : Blo 179801 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B520951 : Blo 179801 520951 := bstep (se 1 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 520951 = 781427) B781427
theorem B619271 : Blo 179801 619271 := bstep (se 1 (by rfl) ⟨464453, by rfl⟩ : syracuseStep 619271 = 928907) B928907
theorem B520985 : Blo 179801 520985 := bstep (se 2 (by rfl) ⟨195369, by rfl⟩ : syracuseStep 520985 = 390739) B390739
theorem B619325 : Blo 179801 619325 := bstep (se 3 (by rfl) ⟨116123, by rfl⟩ : syracuseStep 619325 = 232247) B232247
theorem B193447 : Blo 179801 193447 := bstep (se 1 (by rfl) ⟨145085, by rfl⟩ : syracuseStep 193447 = 290171) B290171
theorem B652283 : Blo 179801 652283 := bstep (se 1 (by rfl) ⟨489212, by rfl⟩ : syracuseStep 652283 = 978425) B978425
theorem B521225 : Blo 179801 521225 := bstep (se 2 (by rfl) ⟨195459, by rfl⟩ : syracuseStep 521225 = 390919) B390919
theorem B26572049 : Blo 179801 26572049 := bstep (se 2 (by rfl) ⟨9964518, by rfl⟩ : syracuseStep 26572049 = 19929037) B19929037
theorem B652769 : Blo 179801 652769 := bstep (se 2 (by rfl) ⟨244788, by rfl⟩ : syracuseStep 652769 = 489577) B489577
theorem B456263 : Blo 179801 456263 := bstep (se 1 (by rfl) ⟨342197, by rfl⟩ : syracuseStep 456263 = 684395) B684395
theorem B456799 : Blo 179801 456799 := bstep (se 1 (by rfl) ⟨342599, by rfl⟩ : syracuseStep 456799 = 685199) B685199
theorem B8485013 : Blo 179801 8485013 := bstep (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) B397735
theorem B588019 : Blo 179801 588019 := bstep (se 1 (by rfl) ⟨441014, by rfl⟩ : syracuseStep 588019 = 882029) B882029
theorem B915785 : Blo 179801 915785 := bstep (se 2 (by rfl) ⟨343419, by rfl⟩ : syracuseStep 915785 = 686839) B686839
theorem B490121 : Blo 179801 490121 := bstep (se 2 (by rfl) ⟨183795, by rfl⟩ : syracuseStep 490121 = 367591) B367591
theorem B228187 : Blo 179801 228187 := bstep (se 1 (by rfl) ⟨171140, by rfl⟩ : syracuseStep 228187 = 342281) B342281
theorem B1571719 : Blo 179801 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B458095 : Blo 179801 458095 := bstep (se 1 (by rfl) ⟨343571, by rfl⟩ : syracuseStep 458095 = 687143) B687143
theorem B3341735 : Blo 179801 3341735 := bstep (se 1 (by rfl) ⟨2506301, by rfl⟩ : syracuseStep 3341735 = 5012603) B5012603
theorem B6651317 : Blo 179801 6651317 := bstep (se 5 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 6651317 = 623561) B623561
theorem B229159 : Blo 179801 229159 := bstep (se 1 (by rfl) ⟨171869, by rfl⟩ : syracuseStep 229159 = 343739) B343739
theorem B622525 : Blo 179801 622525 := bstep (se 3 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 622525 = 233447) B233447
theorem B1507513 : Blo 179801 1507513 := bstep (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) B1130635
theorem B2490743 : Blo 179801 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B459179 : Blo 179801 459179 := bstep (se 1 (by rfl) ⟨344384, by rfl⟩ : syracuseStep 459179 = 688769) B688769
theorem B3506651 : Blo 179801 3506651 := bstep (se 1 (by rfl) ⟨2629988, by rfl⟩ : syracuseStep 3506651 = 5259977) B5259977
theorem B328303 : Blo 179801 328303 := bstep (se 1 (by rfl) ⟨246227, by rfl⟩ : syracuseStep 328303 = 492455) B492455
theorem B3474049 : Blo 179801 3474049 := bstep (se 2 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 3474049 = 2605537) B2605537
theorem B5736071 : Blo 179801 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B231103 : Blo 179801 231103 := bstep (se 1 (by rfl) ⟨173327, by rfl⟩ : syracuseStep 231103 = 346655) B346655
theorem B460687 : Blo 179801 460687 := bstep (se 1 (by rfl) ⟨345515, by rfl⟩ : syracuseStep 460687 = 691031) B691031
theorem B329759 : Blo 179801 329759 := bstep (se 1 (by rfl) ⟨247319, by rfl⟩ : syracuseStep 329759 = 494639) B494639
theorem B1411181 : Blo 179801 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B460961 : Blo 179801 460961 := bstep (se 2 (by rfl) ⟨172860, by rfl⟩ : syracuseStep 460961 = 345721) B345721
theorem B919997 : Blo 179801 919997 := bstep (se 3 (by rfl) ⟨172499, by rfl⟩ : syracuseStep 919997 = 344999) B344999
theorem B920159 : Blo 179801 920159 := bstep (se 1 (by rfl) ⟨690119, by rfl⟩ : syracuseStep 920159 = 1380239) B1380239
theorem B1379267 : Blo 179801 1379267 := bstep (se 1 (by rfl) ⟨1034450, by rfl⟩ : syracuseStep 1379267 = 2068901) B2068901
theorem B6622715 : Blo 179801 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B2101297 : Blo 179801 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B462955 : Blo 179801 462955 := bstep (se 1 (by rfl) ⟨347216, by rfl⟩ : syracuseStep 462955 = 694433) B694433
theorem B692489 : Blo 179801 692489 := bstep (se 2 (by rfl) ⟨259683, by rfl⟩ : syracuseStep 692489 = 519367) B519367
theorem B463855 : Blo 179801 463855 := bstep (se 1 (by rfl) ⟨347891, by rfl⟩ : syracuseStep 463855 = 695783) B695783
theorem B824833 : Blo 179801 824833 := bstep (se 2 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 824833 = 618625) B618625
theorem B202567 : Blo 179801 202567 := bstep (se 1 (by rfl) ⟨151925, by rfl⟩ : syracuseStep 202567 = 303851) B303851
theorem B464737 : Blo 179801 464737 := bstep (se 2 (by rfl) ⟨174276, by rfl⟩ : syracuseStep 464737 = 348553) B348553
theorem B1578953 : Blo 179801 1578953 := bstep (se 2 (by rfl) ⟨592107, by rfl⟩ : syracuseStep 1578953 = 1184215) B1184215
theorem B694601 : Blo 179801 694601 := bstep (se 2 (by rfl) ⟨260475, by rfl⟩ : syracuseStep 694601 = 520951) B520951
theorem B203215 : Blo 179801 203215 := bstep (se 1 (by rfl) ⟨152411, by rfl⟩ : syracuseStep 203215 = 304823) B304823
theorem B1383155 : Blo 179801 1383155 := bstep (se 1 (by rfl) ⟨1037366, by rfl⟩ : syracuseStep 1383155 = 2074733) B2074733
theorem B1547099 : Blo 179801 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B433019 : Blo 179801 433019 := bstep (se 1 (by rfl) ⟨324764, by rfl⟩ : syracuseStep 433019 = 649529) B649529
theorem B204007 : Blo 179801 204007 := bstep (se 1 (by rfl) ⟨153005, by rfl⟩ : syracuseStep 204007 = 306011) B306011
theorem B2071817 : Blo 179801 2071817 := bstep (se 2 (by rfl) ⟨776931, by rfl⟩ : syracuseStep 2071817 = 1553863) B1553863
theorem B269801 : Blo 179801 269801 := bstep (se 2 (by rfl) ⟨101175, by rfl⟩ : syracuseStep 269801 = 202351) B202351
theorem B1547849 : Blo 179801 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B269945 : Blo 179801 269945 := bstep (se 2 (by rfl) ⟨101229, by rfl⟩ : syracuseStep 269945 = 202459) B202459
theorem B270191 : Blo 179801 270191 := bstep (se 1 (by rfl) ⟨202643, by rfl⟩ : syracuseStep 270191 = 405287) B405287
theorem B204655 : Blo 179801 204655 := bstep (se 1 (by rfl) ⟨153491, by rfl⟩ : syracuseStep 204655 = 306983) B306983
theorem B1024109 : Blo 179801 1024109 := bstep (se 3 (by rfl) ⟨192020, by rfl⟩ : syracuseStep 1024109 = 384041) B384041
theorem B3514757 : Blo 179801 3514757 := bstep (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) B659017
theorem B270875 : Blo 179801 270875 := bstep (se 1 (by rfl) ⟨203156, by rfl⟩ : syracuseStep 270875 = 406313) B406313
theorem B205339 : Blo 179801 205339 := bstep (se 1 (by rfl) ⟨154004, by rfl⟩ : syracuseStep 205339 = 308009) B308009
theorem B1385099 : Blo 179801 1385099 := bstep (se 1 (by rfl) ⟨1038824, by rfl⟩ : syracuseStep 1385099 = 2077649) B2077649
theorem B434855 : Blo 179801 434855 := bstep (se 1 (by rfl) ⟨326141, by rfl⟩ : syracuseStep 434855 = 652283) B652283
theorem B271055 : Blo 179801 271055 := bstep (se 1 (by rfl) ⟨203291, by rfl⟩ : syracuseStep 271055 = 406583) B406583
theorem B205519 : Blo 179801 205519 := bstep (se 1 (by rfl) ⟨154139, by rfl⟩ : syracuseStep 205519 = 308279) B308279
theorem B271067 : Blo 179801 271067 := bstep (se 1 (by rfl) ⟨203300, by rfl⟩ : syracuseStep 271067 = 406601) B406601
theorem B435179 : Blo 179801 435179 := bstep (se 1 (by rfl) ⟨326384, by rfl⟩ : syracuseStep 435179 = 652769) B652769
theorem B304175 : Blo 179801 304175 := bstep (se 1 (by rfl) ⟨228131, by rfl⟩ : syracuseStep 304175 = 456263) B456263
theorem B304249 : Blo 179801 304249 := bstep (se 2 (by rfl) ⟨114093, by rfl⟩ : syracuseStep 304249 = 228187) B228187
theorem B271481 : Blo 179801 271481 := bstep (se 2 (by rfl) ⟨101805, by rfl⟩ : syracuseStep 271481 = 203611) B203611
theorem B206527 : Blo 179801 206527 := bstep (se 1 (by rfl) ⟨154895, by rfl⟩ : syracuseStep 206527 = 309791) B309791
theorem B272351 : Blo 179801 272351 := bstep (se 1 (by rfl) ⟨204263, by rfl⟩ : syracuseStep 272351 = 408527) B408527
theorem B272363 : Blo 179801 272363 := bstep (se 1 (by rfl) ⟨204272, by rfl⟩ : syracuseStep 272363 = 408545) B408545
theorem B272411 : Blo 179801 272411 := bstep (se 1 (by rfl) ⟨204308, by rfl⟩ : syracuseStep 272411 = 408617) B408617
theorem B4434211 : Blo 179801 4434211 := bstep (se 1 (by rfl) ⟨3325658, by rfl⟩ : syracuseStep 4434211 = 6651317) B6651317
theorem B305545 : Blo 179801 305545 := bstep (se 2 (by rfl) ⟨114579, by rfl⟩ : syracuseStep 305545 = 229159) B229159
theorem B272777 : Blo 179801 272777 := bstep (se 2 (by rfl) ⟨102291, by rfl⟩ : syracuseStep 272777 = 204583) B204583
theorem B2304551 : Blo 179801 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B830033 : Blo 179801 830033 := bstep (se 2 (by rfl) ⟨311262, by rfl⟩ : syracuseStep 830033 = 622525) B622525
theorem B1485857 : Blo 179801 1485857 := bstep (se 2 (by rfl) ⟨557196, by rfl⟩ : syracuseStep 1485857 = 1114393) B1114393
theorem B371783 : Blo 179801 371783 := bstep (se 1 (by rfl) ⟨278837, by rfl⟩ : syracuseStep 371783 = 557675) B557675
theorem B273719 : Blo 179801 273719 := bstep (se 1 (by rfl) ⟨205289, by rfl⟩ : syracuseStep 273719 = 410579) B410579
theorem B404891 : Blo 179801 404891 := bstep (se 1 (by rfl) ⟨303668, by rfl⟩ : syracuseStep 404891 = 607337) B607337
theorem B273887 : Blo 179801 273887 := bstep (se 1 (by rfl) ⟨205415, by rfl⟩ : syracuseStep 273887 = 410831) B410831
theorem B274103 : Blo 179801 274103 := bstep (se 1 (by rfl) ⟨205577, by rfl⟩ : syracuseStep 274103 = 411155) B411155
theorem B208703 : Blo 179801 208703 := bstep (se 1 (by rfl) ⟨156527, by rfl⟩ : syracuseStep 208703 = 313055) B313055
theorem B274313 : Blo 179801 274313 := bstep (se 2 (by rfl) ⟨102867, by rfl⟩ : syracuseStep 274313 = 205735) B205735
theorem B3092417 : Blo 179801 3092417 := bstep (se 2 (by rfl) ⟨1159656, by rfl⟩ : syracuseStep 3092417 = 2319313) B2319313
theorem B405467 : Blo 179801 405467 := bstep (se 1 (by rfl) ⟨304100, by rfl⟩ : syracuseStep 405467 = 608201) B608201
theorem B307273 : Blo 179801 307273 := bstep (se 2 (by rfl) ⟨115227, by rfl⟩ : syracuseStep 307273 = 230455) B230455
theorem B1159247 : Blo 179801 1159247 := bstep (se 1 (by rfl) ⟨869435, by rfl⟩ : syracuseStep 1159247 = 1738871) B1738871
theorem B307327 : Blo 179801 307327 := bstep (se 1 (by rfl) ⟨230495, by rfl⟩ : syracuseStep 307327 = 460991) B460991
theorem B274559 : Blo 179801 274559 := bstep (se 1 (by rfl) ⟨205919, by rfl⟩ : syracuseStep 274559 = 411839) B411839
theorem B405647 : Blo 179801 405647 := bstep (se 1 (by rfl) ⟨304235, by rfl⟩ : syracuseStep 405647 = 608471) B608471
theorem B405737 : Blo 179801 405737 := bstep (se 2 (by rfl) ⟨152151, by rfl⟩ : syracuseStep 405737 = 304303) B304303
theorem B1650941 : Blo 179801 1650941 := bstep (se 3 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 1650941 = 619103) B619103
theorem B405863 : Blo 179801 405863 := bstep (se 1 (by rfl) ⟨304397, by rfl⟩ : syracuseStep 405863 = 608795) B608795
theorem B275195 : Blo 179801 275195 := bstep (se 1 (by rfl) ⟨206396, by rfl⟩ : syracuseStep 275195 = 412793) B412793
theorem B1028983 : Blo 179801 1028983 := bstep (se 1 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 1028983 = 1543475) B1543475
theorem B1389473 : Blo 179801 1389473 := bstep (se 2 (by rfl) ⟨521052, by rfl⟩ : syracuseStep 1389473 = 1042105) B1042105
theorem B406439 : Blo 179801 406439 := bstep (se 1 (by rfl) ⟨304829, by rfl⟩ : syracuseStep 406439 = 609659) B609659
theorem B308407 : Blo 179801 308407 := bstep (se 1 (by rfl) ⟨231305, by rfl⟩ : syracuseStep 308407 = 462611) B462611
theorem B275639 : Blo 179801 275639 := bstep (se 1 (by rfl) ⟨206729, by rfl⟩ : syracuseStep 275639 = 413459) B413459
theorem B440143 : Blo 179801 440143 := bstep (se 1 (by rfl) ⟨330107, by rfl⟩ : syracuseStep 440143 = 660215) B660215
theorem B407375 : Blo 179801 407375 := bstep (se 1 (by rfl) ⟨305531, by rfl⟩ : syracuseStep 407375 = 611063) B611063
theorem B309163 : Blo 179801 309163 := bstep (se 1 (by rfl) ⟨231872, by rfl⟩ : syracuseStep 309163 = 463745) B463745
theorem B2799755 : Blo 179801 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B637067 : Blo 179801 637067 := bstep (se 1 (by rfl) ⟨477800, by rfl⟩ : syracuseStep 637067 = 955601) B955601
theorem B407735 : Blo 179801 407735 := bstep (se 1 (by rfl) ⟨305801, by rfl⟩ : syracuseStep 407735 = 611603) B611603
theorem B342319 : Blo 179801 342319 := bstep (se 1 (by rfl) ⟨256739, by rfl⟩ : syracuseStep 342319 = 513479) B513479
theorem B309703 : Blo 179801 309703 := bstep (se 1 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 309703 = 464555) B464555
theorem B768457 : Blo 179801 768457 := bstep (se 2 (by rfl) ⟨288171, by rfl⟩ : syracuseStep 768457 = 576343) B576343
theorem B408095 : Blo 179801 408095 := bstep (se 1 (by rfl) ⟨306071, by rfl⟩ : syracuseStep 408095 = 612143) B612143
theorem B342569 : Blo 179801 342569 := bstep (se 2 (by rfl) ⟨128463, by rfl⟩ : syracuseStep 342569 = 256927) B256927
theorem B309919 : Blo 179801 309919 := bstep (se 1 (by rfl) ⟨232439, by rfl⟩ : syracuseStep 309919 = 464879) B464879
theorem B408329 : Blo 179801 408329 := bstep (se 2 (by rfl) ⟨153123, by rfl⟩ : syracuseStep 408329 = 306247) B306247
theorem B867419 : Blo 179801 867419 := bstep (se 1 (by rfl) ⟨650564, by rfl⟩ : syracuseStep 867419 = 1301129) B1301129
theorem B769277 : Blo 179801 769277 := bstep (se 3 (by rfl) ⟨144239, by rfl⟩ : syracuseStep 769277 = 288479) B288479
theorem B1391903 : Blo 179801 1391903 := bstep (se 1 (by rfl) ⟨1043927, by rfl⟩ : syracuseStep 1391903 = 2087855) B2087855
theorem B408905 : Blo 179801 408905 := bstep (se 2 (by rfl) ⟨153339, by rfl⟩ : syracuseStep 408905 = 306679) B306679
theorem B835069 : Blo 179801 835069 := bstep (se 3 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 835069 = 313151) B313151
theorem B1031717 : Blo 179801 1031717 := bstep (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) B193447
theorem B179823 : Blo 179801 179823 := bstep (se 1 (by rfl) ⟨134867, by rfl⟩ : syracuseStep 179823 = 269735) B269735
theorem B179879 : Blo 179801 179879 := bstep (se 1 (by rfl) ⟨134909, by rfl⟩ : syracuseStep 179879 = 269819) B269819
theorem B179943 : Blo 179801 179943 := bstep (se 1 (by rfl) ⟨134957, by rfl⟩ : syracuseStep 179943 = 269915) B269915
theorem B409319 : Blo 179801 409319 := bstep (se 1 (by rfl) ⟨306989, by rfl⟩ : syracuseStep 409319 = 613979) B613979
theorem B179999 : Blo 179801 179999 := bstep (se 1 (by rfl) ⟨134999, by rfl⟩ : syracuseStep 179999 = 269999) B269999
theorem B180079 : Blo 179801 180079 := bstep (se 1 (by rfl) ⟨135059, by rfl⟩ : syracuseStep 180079 = 270119) B270119
theorem B1851281 : Blo 179801 1851281 := bstep (se 2 (by rfl) ⟨694230, by rfl⟩ : syracuseStep 1851281 = 1388461) B1388461
theorem B180135 : Blo 179801 180135 := bstep (se 1 (by rfl) ⟨135101, by rfl⟩ : syracuseStep 180135 = 270203) B270203
theorem B409787 : Blo 179801 409787 := bstep (se 1 (by rfl) ⟨307340, by rfl⟩ : syracuseStep 409787 = 614681) B614681
theorem B180415 : Blo 179801 180415 := bstep (se 1 (by rfl) ⟨135311, by rfl⟩ : syracuseStep 180415 = 270623) B270623
theorem B180431 : Blo 179801 180431 := bstep (se 1 (by rfl) ⟨135323, by rfl⟩ : syracuseStep 180431 = 270647) B270647
theorem B1392875 : Blo 179801 1392875 := bstep (se 1 (by rfl) ⟨1044656, by rfl⟩ : syracuseStep 1392875 = 2089313) B2089313
theorem B180479 : Blo 179801 180479 := bstep (se 1 (by rfl) ⟨135359, by rfl⟩ : syracuseStep 180479 = 270719) B270719
theorem B409895 : Blo 179801 409895 := bstep (se 1 (by rfl) ⟨307421, by rfl⟩ : syracuseStep 409895 = 614843) B614843
theorem B180527 : Blo 179801 180527 := bstep (se 1 (by rfl) ⟨135395, by rfl⟩ : syracuseStep 180527 = 270791) B270791
theorem B14434735 : Blo 179801 14434735 := bstep (se 1 (by rfl) ⟨10826051, by rfl⟩ : syracuseStep 14434735 = 21652103) B21652103
theorem B180763 : Blo 179801 180763 := bstep (se 1 (by rfl) ⟨135572, by rfl⟩ : syracuseStep 180763 = 271145) B271145
theorem B180767 : Blo 179801 180767 := bstep (se 1 (by rfl) ⟨135575, by rfl⟩ : syracuseStep 180767 = 271151) B271151
theorem B180847 : Blo 179801 180847 := bstep (se 1 (by rfl) ⟨135635, by rfl⟩ : syracuseStep 180847 = 271271) B271271
theorem B1032857 : Blo 179801 1032857 := bstep (se 2 (by rfl) ⟨387321, by rfl⟩ : syracuseStep 1032857 = 774643) B774643
theorem B410273 : Blo 179801 410273 := bstep (se 2 (by rfl) ⟨153852, by rfl⟩ : syracuseStep 410273 = 307705) B307705
theorem B180903 : Blo 179801 180903 := bstep (se 1 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 180903 = 271355) B271355
theorem B1163963 : Blo 179801 1163963 := bstep (se 1 (by rfl) ⟨872972, by rfl⟩ : syracuseStep 1163963 = 1745945) B1745945
theorem B180943 : Blo 179801 180943 := bstep (se 1 (by rfl) ⟨135707, by rfl⟩ : syracuseStep 180943 = 271415) B271415
theorem B181023 : Blo 179801 181023 := bstep (se 1 (by rfl) ⟨135767, by rfl⟩ : syracuseStep 181023 = 271535) B271535
theorem B410633 : Blo 179801 410633 := bstep (se 2 (by rfl) ⟨153987, by rfl⟩ : syracuseStep 410633 = 307975) B307975
theorem B181295 : Blo 179801 181295 := bstep (se 1 (by rfl) ⟨135971, by rfl⟩ : syracuseStep 181295 = 271943) B271943
theorem B345151 : Blo 179801 345151 := bstep (se 1 (by rfl) ⟨258863, by rfl⟩ : syracuseStep 345151 = 517727) B517727
theorem B410687 : Blo 179801 410687 := bstep (se 1 (by rfl) ⟨308015, by rfl⟩ : syracuseStep 410687 = 616031) B616031
theorem B181359 : Blo 179801 181359 := bstep (se 1 (by rfl) ⟨136019, by rfl⟩ : syracuseStep 181359 = 272039) B272039
theorem B181415 : Blo 179801 181415 := bstep (se 1 (by rfl) ⟨136061, by rfl⟩ : syracuseStep 181415 = 272123) B272123
theorem B181439 : Blo 179801 181439 := bstep (se 1 (by rfl) ⟨136079, by rfl⟩ : syracuseStep 181439 = 272159) B272159
theorem B181471 : Blo 179801 181471 := bstep (se 1 (by rfl) ⟨136103, by rfl⟩ : syracuseStep 181471 = 272207) B272207
theorem B181551 : Blo 179801 181551 := bstep (se 1 (by rfl) ⟨136163, by rfl⟩ : syracuseStep 181551 = 272327) B272327
theorem B181787 : Blo 179801 181787 := bstep (se 1 (by rfl) ⟨136340, by rfl⟩ : syracuseStep 181787 = 272681) B272681
theorem B181791 : Blo 179801 181791 := bstep (se 1 (by rfl) ⟨136343, by rfl⟩ : syracuseStep 181791 = 272687) B272687
theorem B378475 : Blo 179801 378475 := bstep (se 1 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 378475 = 567713) B567713
theorem B181951 : Blo 179801 181951 := bstep (se 1 (by rfl) ⟨136463, by rfl⟩ : syracuseStep 181951 = 272927) B272927
theorem B182207 : Blo 179801 182207 := bstep (se 1 (by rfl) ⟨136655, by rfl⟩ : syracuseStep 182207 = 273311) B273311
theorem B182239 : Blo 179801 182239 := bstep (se 1 (by rfl) ⟨136679, by rfl⟩ : syracuseStep 182239 = 273359) B273359
theorem B411623 : Blo 179801 411623 := bstep (se 1 (by rfl) ⟨308717, by rfl⟩ : syracuseStep 411623 = 617435) B617435
theorem B182299 : Blo 179801 182299 := bstep (se 1 (by rfl) ⟨136724, by rfl⟩ : syracuseStep 182299 = 273449) B273449
theorem B182303 : Blo 179801 182303 := bstep (se 1 (by rfl) ⟨136727, by rfl⟩ : syracuseStep 182303 = 273455) B273455
theorem B182319 : Blo 179801 182319 := bstep (se 1 (by rfl) ⟨136739, by rfl⟩ : syracuseStep 182319 = 273479) B273479
theorem B346207 : Blo 179801 346207 := bstep (se 1 (by rfl) ⟨259655, by rfl⟩ : syracuseStep 346207 = 519311) B519311
theorem B411803 : Blo 179801 411803 := bstep (se 1 (by rfl) ⟨308852, by rfl⟩ : syracuseStep 411803 = 617705) B617705
theorem B182495 : Blo 179801 182495 := bstep (se 1 (by rfl) ⟨136871, by rfl⟩ : syracuseStep 182495 = 273743) B273743
theorem B182555 : Blo 179801 182555 := bstep (se 1 (by rfl) ⟨136916, by rfl⟩ : syracuseStep 182555 = 273833) B273833
theorem B411983 : Blo 179801 411983 := bstep (se 1 (by rfl) ⟨308987, by rfl⟩ : syracuseStep 411983 = 617975) B617975
theorem B182655 : Blo 179801 182655 := bstep (se 1 (by rfl) ⟨136991, by rfl⟩ : syracuseStep 182655 = 273983) B273983
theorem B412073 : Blo 179801 412073 := bstep (se 2 (by rfl) ⟨154527, by rfl⟩ : syracuseStep 412073 = 309055) B309055
theorem B182831 : Blo 179801 182831 := bstep (se 1 (by rfl) ⟨137123, by rfl⟩ : syracuseStep 182831 = 274247) B274247
theorem B772679 : Blo 179801 772679 := bstep (se 1 (by rfl) ⟨579509, by rfl⟩ : syracuseStep 772679 = 1159019) B1159019
theorem B182887 : Blo 179801 182887 := bstep (se 1 (by rfl) ⟨137165, by rfl⟩ : syracuseStep 182887 = 274331) B274331
theorem B56183543 : Blo 179801 56183543 := bstep (se 1 (by rfl) ⟨42137657, by rfl⟩ : syracuseStep 56183543 = 84275315) B84275315
theorem B609065 : Blo 179801 609065 := bstep (se 2 (by rfl) ⟨228399, by rfl⟩ : syracuseStep 609065 = 456799) B456799
theorem B183263 : Blo 179801 183263 := bstep (se 1 (by rfl) ⟨137447, by rfl⟩ : syracuseStep 183263 = 274895) B274895
theorem B183291 : Blo 179801 183291 := bstep (se 1 (by rfl) ⟨137468, by rfl⟩ : syracuseStep 183291 = 274937) B274937
theorem B412667 : Blo 179801 412667 := bstep (se 1 (by rfl) ⟨309500, by rfl⟩ : syracuseStep 412667 = 619001) B619001
theorem B609335 : Blo 179801 609335 := bstep (se 1 (by rfl) ⟨457001, by rfl⟩ : syracuseStep 609335 = 914003) B914003
theorem B183359 : Blo 179801 183359 := bstep (se 1 (by rfl) ⟨137519, by rfl⟩ : syracuseStep 183359 = 275039) B275039
theorem B412847 : Blo 179801 412847 := bstep (se 1 (by rfl) ⟨309635, by rfl⟩ : syracuseStep 412847 = 619271) B619271
theorem B347323 : Blo 179801 347323 := bstep (se 1 (by rfl) ⟨260492, by rfl⟩ : syracuseStep 347323 = 520985) B520985
theorem B412883 : Blo 179801 412883 := bstep (se 1 (by rfl) ⟨309662, by rfl⟩ : syracuseStep 412883 = 619325) B619325
theorem B347483 : Blo 179801 347483 := bstep (se 1 (by rfl) ⟨260612, by rfl⟩ : syracuseStep 347483 = 521225) B521225
theorem B183679 : Blo 179801 183679 := bstep (se 1 (by rfl) ⟨137759, by rfl⟩ : syracuseStep 183679 = 275519) B275519
theorem B183707 : Blo 179801 183707 := bstep (se 1 (by rfl) ⟨137780, by rfl⟩ : syracuseStep 183707 = 275561) B275561
theorem B183775 : Blo 179801 183775 := bstep (se 1 (by rfl) ⟨137831, by rfl⟩ : syracuseStep 183775 = 275663) B275663
theorem B413153 : Blo 179801 413153 := bstep (se 2 (by rfl) ⟨154932, by rfl⟩ : syracuseStep 413153 = 309865) B309865
theorem B17714699 : Blo 179801 17714699 := bstep (se 1 (by rfl) ⟨13286024, by rfl⟩ : syracuseStep 17714699 = 26572049) B26572049
theorem B1560221 : Blo 179801 1560221 := bstep (se 3 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 1560221 = 585083) B585083
theorem B5656675 : Blo 179801 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B774319 : Blo 179801 774319 := bstep (se 1 (by rfl) ⟨580739, by rfl⟩ : syracuseStep 774319 = 1161479) B1161479
theorem B610523 : Blo 179801 610523 := bstep (se 1 (by rfl) ⟨457892, by rfl⟩ : syracuseStep 610523 = 915785) B915785
theorem B610793 : Blo 179801 610793 := bstep (se 2 (by rfl) ⟨229047, by rfl⟩ : syracuseStep 610793 = 458095) B458095
theorem B3101165 : Blo 179801 3101165 := bstep (se 3 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 3101165 = 1162937) B1162937
theorem B1299311 : Blo 179801 1299311 := bstep (se 1 (by rfl) ⟨974483, by rfl⟩ : syracuseStep 1299311 = 1948967) B1948967
theorem B349679 : Blo 179801 349679 := bstep (se 1 (by rfl) ⟨262259, by rfl⟩ : syracuseStep 349679 = 524519) B524519
theorem B6313459 : Blo 179801 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B1760399 : Blo 179801 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B1170935 : Blo 179801 1170935 := bstep (se 1 (by rfl) ⟨878201, by rfl⟩ : syracuseStep 1170935 = 1756403) B1756403
theorem B2809723 : Blo 179801 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B385015 : Blo 179801 385015 := bstep (se 1 (by rfl) ⟨288761, by rfl⟩ : syracuseStep 385015 = 577523) B577523
theorem B1368089 : Blo 179801 1368089 := bstep (se 2 (by rfl) ⟨513033, by rfl⟩ : syracuseStep 1368089 = 1026067) B1026067
theorem B2613383 : Blo 179801 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B86794649 : Blo 179801 86794649 := bstep (se 2 (by rfl) ⟨32547993, by rfl⟩ : syracuseStep 86794649 = 65095987) B65095987
theorem B3007003 : Blo 179801 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B779017 : Blo 179801 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B418591 : Blo 179801 418591 := bstep (se 1 (by rfl) ⟨313943, by rfl⟩ : syracuseStep 418591 = 627887) B627887
theorem B680939 : Blo 179801 680939 := bstep (se 1 (by rfl) ⟨510704, by rfl⟩ : syracuseStep 680939 = 1021409) B1021409
theorem B3892313 : Blo 179801 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B2975291 : Blo 179801 2975291 := bstep (se 1 (by rfl) ⟨2231468, by rfl⟩ : syracuseStep 2975291 = 4462937) B4462937
theorem B550471 : Blo 179801 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B387065 : Blo 179801 387065 := bstep (se 2 (by rfl) ⟨145149, by rfl⟩ : syracuseStep 387065 = 290299) B290299
theorem B288889 : Blo 179801 288889 := bstep (se 2 (by rfl) ⟨108333, by rfl⟩ : syracuseStep 288889 = 216667) B216667
theorem B616571 : Blo 179801 616571 := bstep (se 1 (by rfl) ⟨462428, by rfl⟩ : syracuseStep 616571 = 924857) B924857
theorem B616841 : Blo 179801 616841 := bstep (se 2 (by rfl) ⟨231315, by rfl⟩ : syracuseStep 616841 = 462631) B462631
theorem B780815 : Blo 179801 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B5270123 : Blo 179801 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B1174601 : Blo 179801 1174601 := bstep (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) B880951
theorem B11234483 : Blo 179801 11234483 := bstep (se 1 (by rfl) ⟨8425862, by rfl⟩ : syracuseStep 11234483 = 16851725) B16851725
theorem B552673 : Blo 179801 552673 := bstep (se 2 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 552673 = 414505) B414505
theorem B192251 : Blo 179801 192251 := bstep (se 1 (by rfl) ⟨144188, by rfl⟩ : syracuseStep 192251 = 288377) B288377
theorem B618569 : Blo 179801 618569 := bstep (se 2 (by rfl) ⟨231963, by rfl⟩ : syracuseStep 618569 = 463927) B463927
theorem B1044839 : Blo 179801 1044839 := bstep (se 1 (by rfl) ⟨783629, by rfl⟩ : syracuseStep 1044839 = 1567259) B1567259
theorem B1176059 : Blo 179801 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B1536641 : Blo 179801 1536641 := bstep (se 2 (by rfl) ⟨576240, by rfl⟩ : syracuseStep 1536641 = 1152481) B1152481
theorem B783083 : Blo 179801 783083 := bstep (se 1 (by rfl) ⟨587312, by rfl⟩ : syracuseStep 783083 = 1174625) B1174625
theorem B1569719 : Blo 179801 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B619703 : Blo 179801 619703 := bstep (se 1 (by rfl) ⟨464777, by rfl⟩ : syracuseStep 619703 = 929555) B929555
theorem B784025 : Blo 179801 784025 := bstep (se 2 (by rfl) ⟨294009, by rfl⟩ : syracuseStep 784025 = 588019) B588019
theorem B1538351 : Blo 179801 1538351 := bstep (se 1 (by rfl) ⟨1153763, by rfl⟩ : syracuseStep 1538351 = 2307527) B2307527
theorem B2095625 : Blo 179801 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B948893 : Blo 179801 948893 := bstep (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) B355835
theorem B326747 : Blo 179801 326747 := bstep (se 1 (by rfl) ⟨245060, by rfl⟩ : syracuseStep 326747 = 490121) B490121
theorem B884243 : Blo 179801 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B2227823 : Blo 179801 2227823 := bstep (se 1 (by rfl) ⟨1670867, by rfl⟩ : syracuseStep 2227823 = 3341735) B3341735
theorem B458369 : Blo 179801 458369 := bstep (se 2 (by rfl) ⟨171888, by rfl⟩ : syracuseStep 458369 = 343777) B343777
theorem B688571 : Blo 179801 688571 := bstep (se 1 (by rfl) ⟨516428, by rfl⟩ : syracuseStep 688571 = 1032857) B1032857
theorem B1540741 : Blo 179801 1540741 := bstep (se 4 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 1540741 = 288889) B288889
theorem B9372685 : Blo 179801 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B558121 : Blo 179801 558121 := bstep (se 2 (by rfl) ⟨209295, by rfl⟩ : syracuseStep 558121 = 418591) B418591
theorem B460201 : Blo 179801 460201 := bstep (se 2 (by rfl) ⟨172575, by rfl⟩ : syracuseStep 460201 = 345151) B345151
theorem B37455695 : Blo 179801 37455695 := bstep (se 1 (by rfl) ⟨28091771, by rfl⟩ : syracuseStep 37455695 = 56183543) B56183543
theorem B919511 : Blo 179801 919511 := bstep (se 1 (by rfl) ⟨689633, by rfl⟩ : syracuseStep 919511 = 1379267) B1379267
theorem B231655 : Blo 179801 231655 := bstep (se 1 (by rfl) ⟨173741, by rfl⟩ : syracuseStep 231655 = 347483) B347483
theorem B461609 : Blo 179801 461609 := bstep (se 2 (by rfl) ⟨173103, by rfl⟩ : syracuseStep 461609 = 346207) B346207
theorem B461659 : Blo 179801 461659 := bstep (se 1 (by rfl) ⟨346244, by rfl⟩ : syracuseStep 461659 = 692489) B692489
theorem B2067443 : Blo 179801 2067443 := bstep (se 1 (by rfl) ⟨1550582, by rfl⟩ : syracuseStep 2067443 = 3101165) B3101165
theorem B233119 : Blo 179801 233119 := bstep (se 1 (by rfl) ⟨174839, by rfl⟩ : syracuseStep 233119 = 349679) B349679
theorem B1052635 : Blo 179801 1052635 := bstep (se 1 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 1052635 = 1578953) B1578953
theorem B463067 : Blo 179801 463067 := bstep (se 1 (by rfl) ⟨347300, by rfl⟩ : syracuseStep 463067 = 694601) B694601
theorem B463097 : Blo 179801 463097 := bstep (se 2 (by rfl) ⟨173661, by rfl⟩ : syracuseStep 463097 = 347323) B347323
theorem B922103 : Blo 179801 922103 := bstep (se 1 (by rfl) ⟨691577, by rfl⟩ : syracuseStep 922103 = 1383155) B1383155
theorem B1381211 : Blo 179801 1381211 := bstep (se 1 (by rfl) ⟨1035908, by rfl⟩ : syracuseStep 1381211 = 2071817) B2071817
theorem B1742255 : Blo 179801 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B7542233 : Blo 179801 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B923399 : Blo 179801 923399 := bstep (se 1 (by rfl) ⟨692549, by rfl⟩ : syracuseStep 923399 = 1385099) B1385099
theorem B202783 : Blo 179801 202783 := bstep (se 1 (by rfl) ⟨152087, by rfl⟩ : syracuseStep 202783 = 304175) B304175
theorem B2594875 : Blo 179801 2594875 := bstep (se 1 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 2594875 = 3892313) B3892313
theorem B3513415 : Blo 179801 3513415 := bstep (se 1 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 3513415 = 5270123) B5270123
theorem B2530381 : Blo 179801 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B990571 : Blo 179801 990571 := bstep (se 1 (by rfl) ⟨742928, by rfl⟩ : syracuseStep 990571 = 1485857) B1485857
theorem B269927 : Blo 179801 269927 := bstep (se 1 (by rfl) ⟨202445, by rfl⟩ : syracuseStep 269927 = 404891) B404891
theorem B270089 : Blo 179801 270089 := bstep (se 2 (by rfl) ⟨101283, by rfl⟩ : syracuseStep 270089 = 202567) B202567
theorem B270311 : Blo 179801 270311 := bstep (se 1 (by rfl) ⟨202733, by rfl⟩ : syracuseStep 270311 = 405467) B405467
theorem B270431 : Blo 179801 270431 := bstep (se 1 (by rfl) ⟨202823, by rfl⟩ : syracuseStep 270431 = 405647) B405647
theorem B270491 : Blo 179801 270491 := bstep (se 1 (by rfl) ⟨202868, by rfl⟩ : syracuseStep 270491 = 405737) B405737
theorem B270575 : Blo 179801 270575 := bstep (se 1 (by rfl) ⟨202931, by rfl⟩ : syracuseStep 270575 = 405863) B405863
theorem B696559 : Blo 179801 696559 := bstep (se 1 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 696559 = 1044839) B1044839
theorem B1024427 : Blo 179801 1024427 := bstep (se 1 (by rfl) ⟨768320, by rfl⟩ : syracuseStep 1024427 = 1536641) B1536641
theorem B1024609 : Blo 179801 1024609 := bstep (se 2 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 1024609 = 768457) B768457
theorem B270953 : Blo 179801 270953 := bstep (se 2 (by rfl) ⟨101607, by rfl⟩ : syracuseStep 270953 = 203215) B203215
theorem B926315 : Blo 179801 926315 := bstep (se 1 (by rfl) ⟨694736, by rfl⟩ : syracuseStep 926315 = 1389473) B1389473
theorem B270959 : Blo 179801 270959 := bstep (se 1 (by rfl) ⟨203219, by rfl⟩ : syracuseStep 270959 = 406439) B406439
theorem B271583 : Blo 179801 271583 := bstep (se 1 (by rfl) ⟨203687, by rfl⟩ : syracuseStep 271583 = 407375) B407375
theorem B271823 : Blo 179801 271823 := bstep (se 1 (by rfl) ⟨203867, by rfl⟩ : syracuseStep 271823 = 407735) B407735
theorem B1025567 : Blo 179801 1025567 := bstep (se 1 (by rfl) ⟨769175, by rfl⟩ : syracuseStep 1025567 = 1538351) B1538351
theorem B272009 : Blo 179801 272009 := bstep (se 2 (by rfl) ⟨102003, by rfl⟩ : syracuseStep 272009 = 204007) B204007
theorem B272063 : Blo 179801 272063 := bstep (se 1 (by rfl) ⟨204047, by rfl⟩ : syracuseStep 272063 = 408095) B408095
theorem B272219 : Blo 179801 272219 := bstep (se 1 (by rfl) ⟨204164, by rfl⟩ : syracuseStep 272219 = 408329) B408329
theorem B927935 : Blo 179801 927935 := bstep (se 1 (by rfl) ⟨695951, by rfl⟩ : syracuseStep 927935 = 1391903) B1391903
theorem B272603 : Blo 179801 272603 := bstep (se 1 (by rfl) ⟨204452, by rfl⟩ : syracuseStep 272603 = 408905) B408905
theorem B1485215 : Blo 179801 1485215 := bstep (se 1 (by rfl) ⟨1113911, by rfl⟩ : syracuseStep 1485215 = 2227823) B2227823
theorem B305579 : Blo 179801 305579 := bstep (se 1 (by rfl) ⟨229184, by rfl⟩ : syracuseStep 305579 = 458369) B458369
theorem B272873 : Blo 179801 272873 := bstep (se 2 (by rfl) ⟨102327, by rfl⟩ : syracuseStep 272873 = 204655) B204655
theorem B272879 : Blo 179801 272879 := bstep (se 1 (by rfl) ⟨204659, by rfl⟩ : syracuseStep 272879 = 409319) B409319
theorem B3746297 : Blo 179801 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B273191 : Blo 179801 273191 := bstep (se 1 (by rfl) ⟨204893, by rfl⟩ : syracuseStep 273191 = 409787) B409787
theorem B928583 : Blo 179801 928583 := bstep (se 1 (by rfl) ⟨696437, by rfl⟩ : syracuseStep 928583 = 1392875) B1392875
theorem B273263 : Blo 179801 273263 := bstep (se 1 (by rfl) ⟨204947, by rfl⟩ : syracuseStep 273263 = 409895) B409895
theorem B2010017 : Blo 179801 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B306119 : Blo 179801 306119 := bstep (se 1 (by rfl) ⟨229589, by rfl⟩ : syracuseStep 306119 = 459179) B459179
theorem B2337767 : Blo 179801 2337767 := bstep (se 1 (by rfl) ⟨1753325, by rfl⟩ : syracuseStep 2337767 = 3506651) B3506651
theorem B273515 : Blo 179801 273515 := bstep (se 1 (by rfl) ⟨205136, by rfl⟩ : syracuseStep 273515 = 410273) B410273
theorem B19246313 : Blo 179801 19246313 := bstep (se 2 (by rfl) ⟨7217367, by rfl⟩ : syracuseStep 19246313 = 14434735) B14434735
theorem B273755 : Blo 179801 273755 := bstep (se 1 (by rfl) ⟨205316, by rfl⟩ : syracuseStep 273755 = 410633) B410633
theorem B273785 : Blo 179801 273785 := bstep (se 2 (by rfl) ⟨102669, by rfl⟩ : syracuseStep 273785 = 205339) B205339
theorem B4009337 : Blo 179801 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B273791 : Blo 179801 273791 := bstep (se 1 (by rfl) ⟨205343, by rfl⟩ : syracuseStep 273791 = 410687) B410687
theorem B437737 : Blo 179801 437737 := bstep (se 2 (by rfl) ⟨164151, by rfl⟩ : syracuseStep 437737 = 328303) B328303
theorem B4632065 : Blo 179801 4632065 := bstep (se 2 (by rfl) ⟨1737024, by rfl⟩ : syracuseStep 4632065 = 3474049) B3474049
theorem B274025 : Blo 179801 274025 := bstep (se 2 (by rfl) ⟨102759, by rfl⟩ : syracuseStep 274025 = 205519) B205519
theorem B274415 : Blo 179801 274415 := bstep (se 1 (by rfl) ⟨205811, by rfl⟩ : syracuseStep 274415 = 411623) B411623
theorem B274535 : Blo 179801 274535 := bstep (se 1 (by rfl) ⟨205901, by rfl⟩ : syracuseStep 274535 = 411803) B411803
theorem B307307 : Blo 179801 307307 := bstep (se 1 (by rfl) ⟨230480, by rfl⟩ : syracuseStep 307307 = 460961) B460961
theorem B405665 : Blo 179801 405665 := bstep (se 2 (by rfl) ⟨152124, by rfl⟩ : syracuseStep 405665 = 304249) B304249
theorem B274655 : Blo 179801 274655 := bstep (se 1 (by rfl) ⟨205991, by rfl⟩ : syracuseStep 274655 = 411983) B411983
theorem B274715 : Blo 179801 274715 := bstep (se 1 (by rfl) ⟨206036, by rfl⟩ : syracuseStep 274715 = 412073) B412073
theorem B406043 : Blo 179801 406043 := bstep (se 1 (by rfl) ⟨304532, by rfl⟩ : syracuseStep 406043 = 609065) B609065
theorem B275111 : Blo 179801 275111 := bstep (se 1 (by rfl) ⟨206333, by rfl⟩ : syracuseStep 275111 = 412667) B412667
theorem B406223 : Blo 179801 406223 := bstep (se 1 (by rfl) ⟨304667, by rfl⟩ : syracuseStep 406223 = 609335) B609335
theorem B733961 : Blo 179801 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B275231 : Blo 179801 275231 := bstep (se 1 (by rfl) ⟨206423, by rfl⟩ : syracuseStep 275231 = 412847) B412847
theorem B275255 : Blo 179801 275255 := bstep (se 1 (by rfl) ⟨206441, by rfl⟩ : syracuseStep 275255 = 412883) B412883
theorem B308137 : Blo 179801 308137 := bstep (se 2 (by rfl) ⟨115551, by rfl⟩ : syracuseStep 308137 = 231103) B231103
theorem B275369 : Blo 179801 275369 := bstep (se 2 (by rfl) ⟨103263, by rfl⟩ : syracuseStep 275369 = 206527) B206527
theorem B275435 : Blo 179801 275435 := bstep (se 1 (by rfl) ⟨206576, by rfl⟩ : syracuseStep 275435 = 413153) B413153
theorem B11809799 : Blo 179801 11809799 := bstep (se 1 (by rfl) ⟨8857349, by rfl⟩ : syracuseStep 11809799 = 17714699) B17714699
theorem B1160477 : Blo 179801 1160477 := bstep (se 3 (by rfl) ⟨217589, by rfl⟩ : syracuseStep 1160477 = 435179) B435179
theorem B407015 : Blo 179801 407015 := bstep (se 1 (by rfl) ⟨305261, by rfl⟩ : syracuseStep 407015 = 610523) B610523
theorem B407195 : Blo 179801 407195 := bstep (se 1 (by rfl) ⟨305396, by rfl⟩ : syracuseStep 407195 = 610793) B610793
theorem B5912281 : Blo 179801 5912281 := bstep (se 2 (by rfl) ⟨2217105, by rfl⟩ : syracuseStep 5912281 = 4434211) B4434211
theorem B407393 : Blo 179801 407393 := bstep (se 2 (by rfl) ⟨152772, by rfl⟩ : syracuseStep 407393 = 305545) B305545
theorem B866207 : Blo 179801 866207 := bstep (se 1 (by rfl) ⟨649655, by rfl⟩ : syracuseStep 866207 = 1299311) B1299311
theorem B1031399 : Blo 179801 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B736897 : Blo 179801 736897 := bstep (se 2 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 736897 = 552673) B552673
theorem B179867 : Blo 179801 179867 := bstep (se 1 (by rfl) ⟨134900, by rfl⟩ : syracuseStep 179867 = 269801) B269801
theorem B1031899 : Blo 179801 1031899 := bstep (se 1 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 1031899 = 1547849) B1547849
theorem B179963 : Blo 179801 179963 := bstep (se 1 (by rfl) ⟨134972, by rfl⟩ : syracuseStep 179963 = 269945) B269945
theorem B180127 : Blo 179801 180127 := bstep (se 1 (by rfl) ⟨135095, by rfl⟩ : syracuseStep 180127 = 270191) B270191
theorem B1032173 : Blo 179801 1032173 := bstep (se 3 (by rfl) ⟨193532, by rfl⟩ : syracuseStep 1032173 = 387065) B387065
theorem B2801729 : Blo 179801 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B409697 : Blo 179801 409697 := bstep (se 2 (by rfl) ⟨153636, by rfl⟩ : syracuseStep 409697 = 307273) B307273
theorem B409769 : Blo 179801 409769 := bstep (se 2 (by rfl) ⟨153663, by rfl⟩ : syracuseStep 409769 = 307327) B307327
theorem B1032425 : Blo 179801 1032425 := bstep (se 2 (by rfl) ⟨387159, by rfl⟩ : syracuseStep 1032425 = 774319) B774319
theorem B180583 : Blo 179801 180583 := bstep (se 1 (by rfl) ⟨135437, by rfl⟩ : syracuseStep 180583 = 270875) B270875
theorem B180703 : Blo 179801 180703 := bstep (se 1 (by rfl) ⟨135527, by rfl⟩ : syracuseStep 180703 = 271055) B271055
theorem B180711 : Blo 179801 180711 := bstep (se 1 (by rfl) ⟨135533, by rfl⟩ : syracuseStep 180711 = 271067) B271067
theorem B180987 : Blo 179801 180987 := bstep (se 1 (by rfl) ⟨135740, by rfl⟩ : syracuseStep 180987 = 271481) B271481
theorem B1983527 : Blo 179801 1983527 := bstep (se 1 (by rfl) ⟨1487645, by rfl⟩ : syracuseStep 1983527 = 2975291) B2975291
theorem B181567 : Blo 179801 181567 := bstep (se 1 (by rfl) ⟨136175, by rfl⟩ : syracuseStep 181567 = 272351) B272351
theorem B181575 : Blo 179801 181575 := bstep (se 1 (by rfl) ⟨136181, by rfl⟩ : syracuseStep 181575 = 272363) B272363
theorem B181607 : Blo 179801 181607 := bstep (se 1 (by rfl) ⟨136205, by rfl⟩ : syracuseStep 181607 = 272411) B272411
theorem B411047 : Blo 179801 411047 := bstep (se 1 (by rfl) ⟨308285, by rfl⟩ : syracuseStep 411047 = 616571) B616571
theorem B411209 : Blo 179801 411209 := bstep (se 2 (by rfl) ⟨154203, by rfl⟩ : syracuseStep 411209 = 308407) B308407
theorem B181851 : Blo 179801 181851 := bstep (se 1 (by rfl) ⟨136388, by rfl⟩ : syracuseStep 181851 = 272777) B272777
theorem B411227 : Blo 179801 411227 := bstep (se 1 (by rfl) ⟨308420, by rfl⟩ : syracuseStep 411227 = 616841) B616841
theorem B1099777 : Blo 179801 1099777 := bstep (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) B824833
theorem B247855 : Blo 179801 247855 := bstep (se 1 (by rfl) ⟨185891, by rfl⟩ : syracuseStep 247855 = 371783) B371783
theorem B7489655 : Blo 179801 7489655 := bstep (se 1 (by rfl) ⟨5617241, by rfl⟩ : syracuseStep 7489655 = 11234483) B11234483
theorem B182479 : Blo 179801 182479 := bstep (se 1 (by rfl) ⟨136859, by rfl⟩ : syracuseStep 182479 = 273719) B273719
theorem B182591 : Blo 179801 182591 := bstep (se 1 (by rfl) ⟨136943, by rfl⟩ : syracuseStep 182591 = 273887) B273887
theorem B182735 : Blo 179801 182735 := bstep (se 1 (by rfl) ⟨137051, by rfl⟩ : syracuseStep 182735 = 274103) B274103
theorem B412217 : Blo 179801 412217 := bstep (se 2 (by rfl) ⟨154581, by rfl⟩ : syracuseStep 412217 = 309163) B309163
theorem B182875 : Blo 179801 182875 := bstep (se 1 (by rfl) ⟨137156, by rfl⟩ : syracuseStep 182875 = 274313) B274313
theorem B412379 : Blo 179801 412379 := bstep (se 1 (by rfl) ⟨309284, by rfl⟩ : syracuseStep 412379 = 618569) B618569
theorem B772831 : Blo 179801 772831 := bstep (se 1 (by rfl) ⟨579623, by rfl⟩ : syracuseStep 772831 = 1159247) B1159247
theorem B183039 : Blo 179801 183039 := bstep (se 1 (by rfl) ⟨137279, by rfl⟩ : syracuseStep 183039 = 274559) B274559
theorem B1100627 : Blo 179801 1100627 := bstep (se 1 (by rfl) ⟨825470, by rfl⟩ : syracuseStep 1100627 = 1650941) B1650941
theorem B183463 : Blo 179801 183463 := bstep (se 1 (by rfl) ⟨137597, by rfl⟩ : syracuseStep 183463 = 275195) B275195
theorem B2018533 : Blo 179801 2018533 := bstep (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) B378475
theorem B412937 : Blo 179801 412937 := bstep (se 2 (by rfl) ⟨154851, by rfl⟩ : syracuseStep 412937 = 309703) B309703
theorem B2051405 : Blo 179801 2051405 := bstep (se 3 (by rfl) ⟨384638, by rfl⟩ : syracuseStep 2051405 = 769277) B769277
theorem B413135 : Blo 179801 413135 := bstep (se 1 (by rfl) ⟨309851, by rfl⟩ : syracuseStep 413135 = 619703) B619703
theorem B183759 : Blo 179801 183759 := bstep (se 1 (by rfl) ⟨137819, by rfl⟩ : syracuseStep 183759 = 275639) B275639
theorem B413225 : Blo 179801 413225 := bstep (se 2 (by rfl) ⟨154959, by rfl⟩ : syracuseStep 413225 = 309919) B309919
theorem B1397083 : Blo 179801 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B2347429 : Blo 179801 2347429 := bstep (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) B440143
theorem B512669 : Blo 179801 512669 := bstep (se 3 (by rfl) ⟨96125, by rfl⟩ : syracuseStep 512669 = 192251) B192251
theorem B578279 : Blo 179801 578279 := bstep (se 1 (by rfl) ⟨433709, by rfl⟩ : syracuseStep 578279 = 867419) B867419
theorem B217831 : Blo 179801 217831 := bstep (se 1 (by rfl) ⟨163373, by rfl⟩ : syracuseStep 217831 = 326747) B326747
theorem B1234187 : Blo 179801 1234187 := bstep (se 1 (by rfl) ⟨925640, by rfl⟩ : syracuseStep 1234187 = 1851281) B1851281
theorem B513353 : Blo 179801 513353 := bstep (se 2 (by rfl) ⟨192507, by rfl⟩ : syracuseStep 513353 = 385015) B385015
theorem B1660495 : Blo 179801 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B775975 : Blo 179801 775975 := bstep (se 1 (by rfl) ⟨581981, by rfl⟩ : syracuseStep 775975 = 1163963) B1163963
theorem B1038689 : Blo 179801 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B3824047 : Blo 179801 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B3136157 : Blo 179801 3136157 := bstep (se 3 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 3136157 = 1176059) B1176059
theorem B219839 : Blo 179801 219839 := bstep (se 1 (by rfl) ⟨164879, by rfl⟩ : syracuseStep 219839 = 329759) B329759
theorem B940787 : Blo 179801 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B613331 : Blo 179801 613331 := bstep (se 1 (by rfl) ⟨459998, by rfl⟩ : syracuseStep 613331 = 919997) B919997
theorem B515119 : Blo 179801 515119 := bstep (se 1 (by rfl) ⟨386339, by rfl⟩ : syracuseStep 515119 = 772679) B772679
theorem B613439 : Blo 179801 613439 := bstep (se 1 (by rfl) ⟨460079, by rfl⟩ : syracuseStep 613439 = 920159) B920159
theorem B4415143 : Blo 179801 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B1040147 : Blo 179801 1040147 := bstep (se 1 (by rfl) ⟨780110, by rfl⟩ : syracuseStep 1040147 = 1560221) B1560221
theorem B614249 : Blo 179801 614249 := bstep (se 2 (by rfl) ⟨230343, by rfl⟩ : syracuseStep 614249 = 460687) B460687
theorem B288679 : Blo 179801 288679 := bstep (se 1 (by rfl) ⟨216509, by rfl⟩ : syracuseStep 288679 = 433019) B433019
theorem B1173599 : Blo 179801 1173599 := bstep (se 1 (by rfl) ⟨880199, by rfl⟩ : syracuseStep 1173599 = 1760399) B1760399
theorem B780623 : Blo 179801 780623 := bstep (se 1 (by rfl) ⟨585467, by rfl⟩ : syracuseStep 780623 = 1170935) B1170935
theorem B912059 : Blo 179801 912059 := bstep (se 1 (by rfl) ⟨684044, by rfl⟩ : syracuseStep 912059 = 1368089) B1368089
theorem B682739 : Blo 179801 682739 := bstep (se 1 (by rfl) ⟨512054, by rfl⟩ : syracuseStep 682739 = 1024109) B1024109
theorem B617273 : Blo 179801 617273 := bstep (se 2 (by rfl) ⟨231477, by rfl⟩ : syracuseStep 617273 = 462955) B462955
theorem B57863099 : Blo 179801 57863099 := bstep (se 1 (by rfl) ⟨43397324, by rfl⟩ : syracuseStep 57863099 = 86794649) B86794649
theorem B289903 : Blo 179801 289903 := bstep (se 1 (by rfl) ⟨217427, by rfl⟩ : syracuseStep 289903 = 434855) B434855
theorem B453959 : Blo 179801 453959 := bstep (se 1 (by rfl) ⟨340469, by rfl⟩ : syracuseStep 453959 = 680939) B680939
theorem B1371977 : Blo 179801 1371977 := bstep (se 2 (by rfl) ⟨514491, by rfl⟩ : syracuseStep 1371977 = 1028983) B1028983
theorem B618473 : Blo 179801 618473 := bstep (se 2 (by rfl) ⟨231927, by rfl⟩ : syracuseStep 618473 = 463855) B463855
theorem B913517 : Blo 179801 913517 := bstep (se 3 (by rfl) ⟨171284, by rfl⟩ : syracuseStep 913517 = 342569) B342569
theorem B520543 : Blo 179801 520543 := bstep (se 1 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 520543 = 780815) B780815
theorem B1536367 : Blo 179801 1536367 := bstep (se 1 (by rfl) ⟨1152275, by rfl⟩ : syracuseStep 1536367 = 2304551) B2304551
theorem B553355 : Blo 179801 553355 := bstep (se 1 (by rfl) ⟨415016, by rfl⟩ : syracuseStep 553355 = 830033) B830033
theorem B8417945 : Blo 179801 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B783067 : Blo 179801 783067 := bstep (se 1 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 783067 = 1174601) B1174601
theorem B619649 : Blo 179801 619649 := bstep (se 2 (by rfl) ⟨232368, by rfl⟩ : syracuseStep 619649 = 464737) B464737
theorem B2061611 : Blo 179801 2061611 := bstep (se 1 (by rfl) ⟨1546208, by rfl⟩ : syracuseStep 2061611 = 3092417) B3092417
theorem B456425 : Blo 179801 456425 := bstep (se 2 (by rfl) ⟨171159, by rfl⟩ : syracuseStep 456425 = 342319) B342319
theorem B522055 : Blo 179801 522055 := bstep (se 1 (by rfl) ⟨391541, by rfl⟩ : syracuseStep 522055 = 783083) B783083
theorem B1046479 : Blo 179801 1046479 := bstep (se 1 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 1046479 = 1569719) B1569719
theorem B522683 : Blo 179801 522683 := bstep (se 1 (by rfl) ⟨392012, by rfl⟩ : syracuseStep 522683 = 784025) B784025
theorem B2357981 : Blo 179801 2357981 := bstep (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) B884243
theorem B1866503 : Blo 179801 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B424711 : Blo 179801 424711 := bstep (se 1 (by rfl) ⟨318533, by rfl⟩ : syracuseStep 424711 = 637067) B637067
theorem B1113425 : Blo 179801 1113425 := bstep (se 2 (by rfl) ⟨417534, by rfl⟩ : syracuseStep 1113425 = 835069) B835069
theorem B556541 : Blo 179801 556541 := bstep (se 3 (by rfl) ⟨104351, by rfl⟩ : syracuseStep 556541 = 208703) B208703
theorem B687811 : Blo 179801 687811 := bstep (se 1 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 687811 = 1031717) B1031717
theorem B1867819 : Blo 179801 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B688283 : Blo 179801 688283 := bstep (se 1 (by rfl) ⟨516212, by rfl⟩ : syracuseStep 688283 = 1032425) B1032425
theorem B459047 : Blo 179801 459047 := bstep (se 1 (by rfl) ⟨344285, by rfl⟩ : syracuseStep 459047 = 688571) B688571
theorem B24970463 : Blo 179801 24970463 := bstep (se 1 (by rfl) ⟨18727847, by rfl⟩ : syracuseStep 24970463 = 37455695) B37455695
theorem B1542077 : Blo 179801 1542077 := bstep (se 3 (by rfl) ⟨289139, by rfl⟩ : syracuseStep 1542077 = 578279) B578279
theorem B1378295 : Blo 179801 1378295 := bstep (se 1 (by rfl) ⟨1033721, by rfl⟩ : syracuseStep 1378295 = 2067443) B2067443
theorem B330473 : Blo 179801 330473 := bstep (se 2 (by rfl) ⟨123927, by rfl⟩ : syracuseStep 330473 = 247855) B247855
theorem B920807 : Blo 179801 920807 := bstep (se 1 (by rfl) ⟨690605, by rfl⟩ : syracuseStep 920807 = 1381211) B1381211
theorem B822791 : Blo 179801 822791 := bstep (se 1 (by rfl) ⟨617093, by rfl⟩ : syracuseStep 822791 = 1234187) B1234187
theorem B692459 : Blo 179801 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B2691377 : Blo 179801 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B627191 : Blo 179801 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B693431 : Blo 179801 693431 := bstep (se 1 (by rfl) ⟨520073, by rfl⟩ : syracuseStep 693431 = 1040147) B1040147
theorem B694057 : Blo 179801 694057 := bstep (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) B520543
theorem B990143 : Blo 179801 990143 := bstep (se 1 (by rfl) ⟨742607, by rfl⟩ : syracuseStep 990143 = 1485215) B1485215
theorem B203719 : Blo 179801 203719 := bstep (se 1 (by rfl) ⟨152789, by rfl⟩ : syracuseStep 203719 = 305579) B305579
theorem B38575399 : Blo 179801 38575399 := bstep (se 1 (by rfl) ⟨28931549, by rfl⟩ : syracuseStep 38575399 = 57863099) B57863099
theorem B204079 : Blo 179801 204079 := bstep (se 1 (by rfl) ⟨153059, by rfl⟩ : syracuseStep 204079 = 306119) B306119
theorem B302639 : Blo 179801 302639 := bstep (se 1 (by rfl) ⟨226979, by rfl⟩ : syracuseStep 302639 = 453959) B453959
theorem B3088043 : Blo 179801 3088043 := bstep (se 1 (by rfl) ⟨2316032, by rfl⟩ : syracuseStep 3088043 = 4632065) B4632065
theorem B696073 : Blo 179801 696073 := bstep (se 2 (by rfl) ⟨261027, by rfl⟩ : syracuseStep 696073 = 522055) B522055
theorem B270377 : Blo 179801 270377 := bstep (se 2 (by rfl) ⟨101391, by rfl⟩ : syracuseStep 270377 = 202783) B202783
theorem B204871 : Blo 179801 204871 := bstep (se 1 (by rfl) ⟨153653, by rfl⟩ : syracuseStep 204871 = 307307) B307307
theorem B270443 : Blo 179801 270443 := bstep (se 1 (by rfl) ⟨202832, by rfl⟩ : syracuseStep 270443 = 405665) B405665
theorem B368903 : Blo 179801 368903 := bstep (se 1 (by rfl) ⟨276677, by rfl⟩ : syracuseStep 368903 = 553355) B553355
theorem B270695 : Blo 179801 270695 := bstep (se 1 (by rfl) ⟨203021, by rfl⟩ : syracuseStep 270695 = 406043) B406043
theorem B5611963 : Blo 179801 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B270815 : Blo 179801 270815 := bstep (se 1 (by rfl) ⟨203111, by rfl⟩ : syracuseStep 270815 = 406223) B406223
theorem B7873199 : Blo 179801 7873199 := bstep (se 1 (by rfl) ⟨5904899, by rfl⟩ : syracuseStep 7873199 = 11809799) B11809799
theorem B271343 : Blo 179801 271343 := bstep (se 1 (by rfl) ⟨203507, by rfl⟩ : syracuseStep 271343 = 407015) B407015
theorem B566281 : Blo 179801 566281 := bstep (se 2 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 566281 = 424711) B424711
theorem B271463 : Blo 179801 271463 := bstep (se 1 (by rfl) ⟨203597, by rfl⟩ : syracuseStep 271463 = 407195) B407195
theorem B304283 : Blo 179801 304283 := bstep (se 1 (by rfl) ⟨228212, by rfl⟩ : syracuseStep 304283 = 456425) B456425
theorem B271595 : Blo 179801 271595 := bstep (se 1 (by rfl) ⟨203696, by rfl⟩ : syracuseStep 271595 = 407393) B407393
theorem B1320761 : Blo 179801 1320761 := bstep (se 2 (by rfl) ⟨495285, by rfl⟩ : syracuseStep 1320761 = 990571) B990571
theorem B371027 : Blo 179801 371027 := bstep (se 1 (by rfl) ⟨278270, by rfl⟩ : syracuseStep 371027 = 556541) B556541
theorem B1649261 : Blo 179801 1649261 := bstep (se 3 (by rfl) ⟨309236, by rfl⟩ : syracuseStep 1649261 = 618473) B618473
theorem B273131 : Blo 179801 273131 := bstep (se 1 (by rfl) ⟨204848, by rfl⟩ : syracuseStep 273131 = 409697) B409697
theorem B273179 : Blo 179801 273179 := bstep (se 1 (by rfl) ⟨204884, by rfl⟩ : syracuseStep 273179 = 409769) B409769
theorem B928745 : Blo 179801 928745 := bstep (se 2 (by rfl) ⟨348279, by rfl⟩ : syracuseStep 928745 = 696559) B696559
theorem B1322351 : Blo 179801 1322351 := bstep (se 1 (by rfl) ⟨991763, by rfl⟩ : syracuseStep 1322351 = 1983527) B1983527
theorem B274031 : Blo 179801 274031 := bstep (se 1 (by rfl) ⟨205523, by rfl⟩ : syracuseStep 274031 = 411047) B411047
theorem B274139 : Blo 179801 274139 := bstep (se 1 (by rfl) ⟨205604, by rfl⟩ : syracuseStep 274139 = 411209) B411209
theorem B274151 : Blo 179801 274151 := bstep (se 1 (by rfl) ⟨205613, by rfl⟩ : syracuseStep 274151 = 411227) B411227
theorem B12496913 : Blo 179801 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B4993103 : Blo 179801 4993103 := bstep (se 1 (by rfl) ⟨3744827, by rfl⟩ : syracuseStep 4993103 = 7489655) B7489655
theorem B274811 : Blo 179801 274811 := bstep (se 1 (by rfl) ⟨206108, by rfl⟩ : syracuseStep 274811 = 412217) B412217
theorem B274919 : Blo 179801 274919 := bstep (se 1 (by rfl) ⟨206189, by rfl⟩ : syracuseStep 274919 = 412379) B412379
theorem B307739 : Blo 179801 307739 := bstep (se 1 (by rfl) ⟨230804, by rfl⟩ : syracuseStep 307739 = 461609) B461609
theorem B733751 : Blo 179801 733751 := bstep (se 1 (by rfl) ⟨550313, by rfl⟩ : syracuseStep 733751 = 1100627) B1100627
theorem B275291 : Blo 179801 275291 := bstep (se 1 (by rfl) ⟨206468, by rfl⟩ : syracuseStep 275291 = 412937) B412937
theorem B275423 : Blo 179801 275423 := bstep (se 1 (by rfl) ⟨206567, by rfl⟩ : syracuseStep 275423 = 413135) B413135
theorem B275483 : Blo 179801 275483 := bstep (se 1 (by rfl) ⟨206612, by rfl⟩ : syracuseStep 275483 = 413225) B413225
theorem B308711 : Blo 179801 308711 := bstep (se 1 (by rfl) ⟨231533, by rfl⟩ : syracuseStep 308711 = 463067) B463067
theorem B308731 : Blo 179801 308731 := bstep (se 1 (by rfl) ⟨231548, by rfl⟩ : syracuseStep 308731 = 463097) B463097
theorem B308873 : Blo 179801 308873 := bstep (se 2 (by rfl) ⟨115827, by rfl⟩ : syracuseStep 308873 = 231655) B231655
theorem B342235 : Blo 179801 342235 := bstep (se 1 (by rfl) ⟨256676, by rfl⟩ : syracuseStep 342235 = 513353) B513353
theorem B1161503 : Blo 179801 1161503 := bstep (se 1 (by rfl) ⟨871127, by rfl⟩ : syracuseStep 1161503 = 1742255) B1742255
theorem B1030441 : Blo 179801 1030441 := bstep (se 2 (by rfl) ⟨386415, by rfl⟩ : syracuseStep 1030441 = 772831) B772831
theorem B5028155 : Blo 179801 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B408887 : Blo 179801 408887 := bstep (se 1 (by rfl) ⟨306665, by rfl⟩ : syracuseStep 408887 = 613331) B613331
theorem B408959 : Blo 179801 408959 := bstep (se 1 (by rfl) ⟨306719, by rfl⟩ : syracuseStep 408959 = 613439) B613439
theorem B310825 : Blo 179801 310825 := bstep (se 2 (by rfl) ⟨116559, by rfl⟩ : syracuseStep 310825 = 233119) B233119
theorem B179951 : Blo 179801 179951 := bstep (se 1 (by rfl) ⟨134963, by rfl⟩ : syracuseStep 179951 = 269927) B269927
theorem B180059 : Blo 179801 180059 := bstep (se 1 (by rfl) ⟨135044, by rfl⟩ : syracuseStep 180059 = 270089) B270089
theorem B409499 : Blo 179801 409499 := bstep (se 1 (by rfl) ⟨307124, by rfl⟩ : syracuseStep 409499 = 614249) B614249
theorem B180207 : Blo 179801 180207 := bstep (se 1 (by rfl) ⟨135155, by rfl⟩ : syracuseStep 180207 = 270311) B270311
theorem B180287 : Blo 179801 180287 := bstep (se 1 (by rfl) ⟨135215, by rfl⟩ : syracuseStep 180287 = 270431) B270431
theorem B180327 : Blo 179801 180327 := bstep (se 1 (by rfl) ⟨135245, by rfl⟩ : syracuseStep 180327 = 270491) B270491
theorem B180383 : Blo 179801 180383 := bstep (se 1 (by rfl) ⟨135287, by rfl⟩ : syracuseStep 180383 = 270575) B270575
theorem B180635 : Blo 179801 180635 := bstep (se 1 (by rfl) ⟨135476, by rfl⟩ : syracuseStep 180635 = 270953) B270953
theorem B180639 : Blo 179801 180639 := bstep (se 1 (by rfl) ⟨135479, by rfl⟩ : syracuseStep 180639 = 270959) B270959
theorem B2048489 : Blo 179801 2048489 := bstep (se 2 (by rfl) ⟨768183, by rfl⟩ : syracuseStep 2048489 = 1536367) B1536367
theorem B3129905 : Blo 179801 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B181055 : Blo 179801 181055 := bstep (se 1 (by rfl) ⟨135791, by rfl⟩ : syracuseStep 181055 = 271583) B271583
theorem B181215 : Blo 179801 181215 := bstep (se 1 (by rfl) ⟨135911, by rfl⟩ : syracuseStep 181215 = 271823) B271823
theorem B181339 : Blo 179801 181339 := bstep (se 1 (by rfl) ⟨136004, by rfl⟩ : syracuseStep 181339 = 272009) B272009
theorem B181375 : Blo 179801 181375 := bstep (se 1 (by rfl) ⟨136031, by rfl⟩ : syracuseStep 181375 = 272063) B272063
theorem B410849 : Blo 179801 410849 := bstep (se 2 (by rfl) ⟨154068, by rfl⟩ : syracuseStep 410849 = 308137) B308137
theorem B181479 : Blo 179801 181479 := bstep (se 1 (by rfl) ⟨136109, by rfl⟩ : syracuseStep 181479 = 272219) B272219
theorem B181735 : Blo 179801 181735 := bstep (se 1 (by rfl) ⟨136301, by rfl⟩ : syracuseStep 181735 = 272603) B272603
theorem B181915 : Blo 179801 181915 := bstep (se 1 (by rfl) ⟨136436, by rfl⟩ : syracuseStep 181915 = 272873) B272873
theorem B181919 : Blo 179801 181919 := bstep (se 1 (by rfl) ⟨136439, by rfl⟩ : syracuseStep 181919 = 272879) B272879
theorem B608039 : Blo 179801 608039 := bstep (se 1 (by rfl) ⟨456029, by rfl⟩ : syracuseStep 608039 = 912059) B912059
theorem B182127 : Blo 179801 182127 := bstep (se 1 (by rfl) ⟨136595, by rfl⟩ : syracuseStep 182127 = 273191) B273191
theorem B411515 : Blo 179801 411515 := bstep (se 1 (by rfl) ⟨308636, by rfl⟩ : syracuseStep 411515 = 617273) B617273
theorem B182175 : Blo 179801 182175 := bstep (se 1 (by rfl) ⟨136631, by rfl⟩ : syracuseStep 182175 = 273263) B273263
theorem B1558511 : Blo 179801 1558511 := bstep (se 1 (by rfl) ⟨1168883, by rfl⟩ : syracuseStep 1558511 = 2337767) B2337767
theorem B182343 : Blo 179801 182343 := bstep (se 1 (by rfl) ⟨136757, by rfl⟩ : syracuseStep 182343 = 273515) B273515
theorem B2213993 : Blo 179801 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B12830875 : Blo 179801 12830875 := bstep (se 1 (by rfl) ⟨9623156, by rfl⟩ : syracuseStep 12830875 = 19246313) B19246313
theorem B182503 : Blo 179801 182503 := bstep (se 1 (by rfl) ⟨136877, by rfl⟩ : syracuseStep 182503 = 273755) B273755
theorem B182523 : Blo 179801 182523 := bstep (se 1 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 182523 = 273785) B273785
theorem B2672891 : Blo 179801 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B182527 : Blo 179801 182527 := bstep (se 1 (by rfl) ⟨136895, by rfl⟩ : syracuseStep 182527 = 273791) B273791
theorem B7883041 : Blo 179801 7883041 := bstep (se 2 (by rfl) ⟨2956140, by rfl⟩ : syracuseStep 7883041 = 5912281) B5912281
theorem B1034633 : Blo 179801 1034633 := bstep (se 2 (by rfl) ⟨387987, by rfl⟩ : syracuseStep 1034633 = 775975) B775975
theorem B182683 : Blo 179801 182683 := bstep (se 1 (by rfl) ⟨137012, by rfl⟩ : syracuseStep 182683 = 274025) B274025
theorem B1395305 : Blo 179801 1395305 := bstep (se 2 (by rfl) ⟨523239, by rfl⟩ : syracuseStep 1395305 = 1046479) B1046479
theorem B182943 : Blo 179801 182943 := bstep (se 1 (by rfl) ⟨137207, by rfl⟩ : syracuseStep 182943 = 274415) B274415
theorem B183023 : Blo 179801 183023 := bstep (se 1 (by rfl) ⟨137267, by rfl⟩ : syracuseStep 183023 = 274535) B274535
theorem B609011 : Blo 179801 609011 := bstep (se 1 (by rfl) ⟨456758, by rfl⟩ : syracuseStep 609011 = 913517) B913517
theorem B3459833 : Blo 179801 3459833 := bstep (se 2 (by rfl) ⟨1297437, by rfl⟩ : syracuseStep 3459833 = 2594875) B2594875
theorem B183103 : Blo 179801 183103 := bstep (se 1 (by rfl) ⟨137327, by rfl⟩ : syracuseStep 183103 = 274655) B274655
theorem B183143 : Blo 179801 183143 := bstep (se 1 (by rfl) ⟨137357, by rfl⟩ : syracuseStep 183143 = 274715) B274715
theorem B183407 : Blo 179801 183407 := bstep (se 1 (by rfl) ⟨137555, by rfl⟩ : syracuseStep 183407 = 275111) B275111
theorem B183487 : Blo 179801 183487 := bstep (se 1 (by rfl) ⟨137615, by rfl⟩ : syracuseStep 183487 = 275231) B275231
theorem B183503 : Blo 179801 183503 := bstep (se 1 (by rfl) ⟨137627, by rfl⟩ : syracuseStep 183503 = 275255) B275255
theorem B5098729 : Blo 179801 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B183579 : Blo 179801 183579 := bstep (se 1 (by rfl) ⟨137684, by rfl⟩ : syracuseStep 183579 = 275369) B275369
theorem B183623 : Blo 179801 183623 := bstep (se 1 (by rfl) ⟨137717, by rfl⟩ : syracuseStep 183623 = 275435) B275435
theorem B413099 : Blo 179801 413099 := bstep (se 1 (by rfl) ⟨309824, by rfl⟩ : syracuseStep 413099 = 619649) B619649
theorem B773651 : Blo 179801 773651 := bstep (se 1 (by rfl) ⟨580238, by rfl⟩ : syracuseStep 773651 = 1160477) B1160477
theorem B577471 : Blo 179801 577471 := bstep (se 1 (by rfl) ⟨433103, by rfl⟩ : syracuseStep 577471 = 866207) B866207
theorem B348455 : Blo 179801 348455 := bstep (se 1 (by rfl) ⟨261341, by rfl⟩ : syracuseStep 348455 = 522683) B522683
theorem B5886857 : Blo 179801 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B742283 : Blo 179801 742283 := bstep (se 1 (by rfl) ⟨556712, by rfl⟩ : syracuseStep 742283 = 1113425) B1113425
theorem B1366145 : Blo 179801 1366145 := bstep (se 2 (by rfl) ⟨512304, by rfl⟩ : syracuseStep 1366145 = 1024609) B1024609
theorem B2054321 : Blo 179801 2054321 := bstep (se 2 (by rfl) ⟨770370, by rfl⟩ : syracuseStep 2054321 = 1540741) B1540741
theorem B613007 : Blo 179801 613007 := bstep (se 1 (by rfl) ⟨459755, by rfl⟩ : syracuseStep 613007 = 919511) B919511
theorem B744161 : Blo 179801 744161 := bstep (se 2 (by rfl) ⟨279060, by rfl⟩ : syracuseStep 744161 = 558121) B558121
theorem B1367117 : Blo 179801 1367117 := bstep (se 3 (by rfl) ⟨256334, by rfl⟩ : syracuseStep 1367117 = 512669) B512669
theorem B613601 : Blo 179801 613601 := bstep (se 2 (by rfl) ⟨230100, by rfl⟩ : syracuseStep 613601 = 460201) B460201
theorem B1957229 : Blo 179801 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B1367603 : Blo 179801 1367603 := bstep (se 1 (by rfl) ⟨1025702, by rfl⟩ : syracuseStep 1367603 = 2051405) B2051405
theorem B384905 : Blo 179801 384905 := bstep (se 2 (by rfl) ⟨144339, by rfl⟩ : syracuseStep 384905 = 288679) B288679
theorem B1466369 : Blo 179801 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B614735 : Blo 179801 614735 := bstep (se 1 (by rfl) ⟨461051, by rfl⟩ : syracuseStep 614735 = 922103) B922103
theorem B615545 : Blo 179801 615545 := bstep (se 2 (by rfl) ⟨230829, by rfl⟩ : syracuseStep 615545 = 461659) B461659
theorem B615599 : Blo 179801 615599 := bstep (se 1 (by rfl) ⟨461699, by rfl⟩ : syracuseStep 615599 = 923399) B923399
theorem B386537 : Blo 179801 386537 := bstep (se 2 (by rfl) ⟨144951, by rfl⟩ : syracuseStep 386537 = 289903) B289903
theorem B2090771 : Blo 179801 2090771 := bstep (se 1 (by rfl) ⟨1568078, by rfl⟩ : syracuseStep 2090771 = 3136157) B3136157
theorem B583649 : Blo 179801 583649 := bstep (se 2 (by rfl) ⟨218868, by rfl⟩ : syracuseStep 583649 = 437737) B437737
theorem B1403513 : Blo 179801 1403513 := bstep (se 2 (by rfl) ⟨526317, by rfl⟩ : syracuseStep 1403513 = 1052635) B1052635
theorem B682951 : Blo 179801 682951 := bstep (se 1 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 682951 = 1024427) B1024427
theorem B617543 : Blo 179801 617543 := bstep (se 1 (by rfl) ⟨463157, by rfl⟩ : syracuseStep 617543 = 926315) B926315
theorem B1862777 : Blo 179801 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B1044089 : Blo 179801 1044089 := bstep (se 2 (by rfl) ⟨391533, by rfl⟩ : syracuseStep 1044089 = 783067) B783067
theorem B290441 : Blo 179801 290441 := bstep (se 2 (by rfl) ⟨108915, by rfl⟩ : syracuseStep 290441 = 217831) B217831
theorem B683711 : Blo 179801 683711 := bstep (se 1 (by rfl) ⟨512783, by rfl⟩ : syracuseStep 683711 = 1025567) B1025567
theorem B9990125 : Blo 179801 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B782399 : Blo 179801 782399 := bstep (se 1 (by rfl) ⟨586799, by rfl⟩ : syracuseStep 782399 = 1173599) B1173599
theorem B618623 : Blo 179801 618623 := bstep (se 1 (by rfl) ⟨463967, by rfl⟩ : syracuseStep 618623 = 927935) B927935
theorem B520415 : Blo 179801 520415 := bstep (se 1 (by rfl) ⟨390311, by rfl⟩ : syracuseStep 520415 = 780623) B780623
theorem B455159 : Blo 179801 455159 := bstep (se 1 (by rfl) ⟨341369, by rfl⟩ : syracuseStep 455159 = 682739) B682739
theorem B586237 : Blo 179801 586237 := bstep (se 3 (by rfl) ⟨109919, by rfl⟩ : syracuseStep 586237 = 219839) B219839
theorem B619055 : Blo 179801 619055 := bstep (se 1 (by rfl) ⟨464291, by rfl⟩ : syracuseStep 619055 = 928583) B928583
theorem B1340011 : Blo 179801 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B914651 : Blo 179801 914651 := bstep (se 1 (by rfl) ⟨685988, by rfl⟩ : syracuseStep 914651 = 1371977) B1371977
theorem B1374407 : Blo 179801 1374407 := bstep (se 1 (by rfl) ⟨1030805, by rfl⟩ : syracuseStep 1374407 = 2061611) B2061611
theorem B686825 : Blo 179801 686825 := bstep (se 2 (by rfl) ⟨257559, by rfl⟩ : syracuseStep 686825 = 515119) B515119
theorem B4684553 : Blo 179801 4684553 := bstep (se 2 (by rfl) ⟨1756707, by rfl⟩ : syracuseStep 4684553 = 3513415) B3513415
theorem B3373841 : Blo 179801 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B1571987 : Blo 179801 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B1244335 : Blo 179801 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B687599 : Blo 179801 687599 := bstep (se 1 (by rfl) ⟨515699, by rfl⟩ : syracuseStep 687599 = 1031399) B1031399
theorem B982529 : Blo 179801 982529 := bstep (se 2 (by rfl) ⟨368448, by rfl⟩ : syracuseStep 982529 = 736897) B736897
theorem B917081 : Blo 179801 917081 := bstep (se 2 (by rfl) ⟨343905, by rfl⟩ : syracuseStep 917081 = 687811) B687811
theorem B1375865 : Blo 179801 1375865 := bstep (se 2 (by rfl) ⟨515949, by rfl⟩ : syracuseStep 1375865 = 1031899) B1031899
theorem B688115 : Blo 179801 688115 := bstep (se 1 (by rfl) ⟨516086, by rfl⟩ : syracuseStep 688115 = 1032173) B1032173
theorem B2490425 : Blo 179801 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B458855 : Blo 179801 458855 := bstep (se 1 (by rfl) ⟨344141, by rfl⟩ : syracuseStep 458855 = 688283) B688283
theorem B16646975 : Blo 179801 16646975 := bstep (se 1 (by rfl) ⟨12485231, by rfl⟩ : syracuseStep 16646975 = 24970463) B24970463
theorem B918863 : Blo 179801 918863 := bstep (se 1 (by rfl) ⟨689147, by rfl⟩ : syracuseStep 918863 = 1378295) B1378295
theorem B1475995 : Blo 179801 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B689755 : Blo 179801 689755 := bstep (se 1 (by rfl) ⟨517316, by rfl⟩ : syracuseStep 689755 = 1034633) B1034633
theorem B461639 : Blo 179801 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B232303 : Blo 179801 232303 := bstep (se 1 (by rfl) ⟨174227, by rfl⟩ : syracuseStep 232303 = 348455) B348455
theorem B494855 : Blo 179801 494855 := bstep (se 1 (by rfl) ⟨371141, by rfl⟩ : syracuseStep 494855 = 742283) B742283
theorem B462287 : Blo 179801 462287 := bstep (se 1 (by rfl) ⟨346715, by rfl⟩ : syracuseStep 462287 = 693431) B693431
theorem B823229 : Blo 179801 823229 := bstep (se 3 (by rfl) ⟨154355, by rfl⟩ : syracuseStep 823229 = 308711) B308711
theorem B660095 : Blo 179801 660095 := bstep (se 1 (by rfl) ⟨495071, by rfl⟩ : syracuseStep 660095 = 990143) B990143
theorem B3020165 : Blo 179801 3020165 := bstep (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) B566281
theorem B5248799 : Blo 179801 5248799 := bstep (se 1 (by rfl) ⟨3936599, by rfl⟩ : syracuseStep 5248799 = 7873199) B7873199
theorem B202855 : Blo 179801 202855 := bstep (se 1 (by rfl) ⟨152141, by rfl⟩ : syracuseStep 202855 = 304283) B304283
theorem B989405 : Blo 179801 989405 := bstep (se 3 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 989405 = 371027) B371027
theorem B925409 : Blo 179801 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B696059 : Blo 179801 696059 := bstep (se 1 (by rfl) ⟨522044, by rfl⟩ : syracuseStep 696059 = 1044089) B1044089
theorem B6660083 : Blo 179801 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B8331275 : Blo 179801 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B303439 : Blo 179801 303439 := bstep (se 1 (by rfl) ⟨227579, by rfl⟩ : syracuseStep 303439 = 455159) B455159
theorem B205159 : Blo 179801 205159 := bstep (se 1 (by rfl) ⟨153869, by rfl⟩ : syracuseStep 205159 = 307739) B307739
theorem B205807 : Blo 179801 205807 := bstep (se 1 (by rfl) ⟨154355, by rfl⟩ : syracuseStep 205807 = 308711) B308711
theorem B205915 : Blo 179801 205915 := bstep (se 1 (by rfl) ⟨154436, by rfl⟩ : syracuseStep 205915 = 308873) B308873
theorem B271625 : Blo 179801 271625 := bstep (se 2 (by rfl) ⟨101859, by rfl⟩ : syracuseStep 271625 = 203719) B203719
theorem B3352103 : Blo 179801 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B272105 : Blo 179801 272105 := bstep (se 2 (by rfl) ⟨102039, by rfl⟩ : syracuseStep 272105 = 204079) B204079
theorem B3123035 : Blo 179801 3123035 := bstep (se 1 (by rfl) ⟨2342276, by rfl⟩ : syracuseStep 3123035 = 4684553) B4684553
theorem B272591 : Blo 179801 272591 := bstep (se 1 (by rfl) ⟨204443, by rfl⟩ : syracuseStep 272591 = 408887) B408887
theorem B272639 : Blo 179801 272639 := bstep (se 1 (by rfl) ⟨204479, by rfl⟩ : syracuseStep 272639 = 408959) B408959
theorem B928097 : Blo 179801 928097 := bstep (se 2 (by rfl) ⟨348036, by rfl⟩ : syracuseStep 928097 = 696073) B696073
theorem B272999 : Blo 179801 272999 := bstep (se 1 (by rfl) ⟨204749, by rfl⟩ : syracuseStep 272999 = 409499) B409499
theorem B273161 : Blo 179801 273161 := bstep (se 2 (by rfl) ⟨102435, by rfl⟩ : syracuseStep 273161 = 204871) B204871
theorem B306031 : Blo 179801 306031 := bstep (se 1 (by rfl) ⟨229523, by rfl⟩ : syracuseStep 306031 = 459047) B459047
theorem B7482617 : Blo 179801 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B68431333 : Blo 179801 68431333 := bstep (se 4 (by rfl) ⟨6415437, by rfl⟩ : syracuseStep 68431333 = 12830875) B12830875
theorem B273899 : Blo 179801 273899 := bstep (se 1 (by rfl) ⟨205424, by rfl⟩ : syracuseStep 273899 = 410849) B410849
theorem B405359 : Blo 179801 405359 := bstep (se 1 (by rfl) ⟨304019, by rfl⟩ : syracuseStep 405359 = 608039) B608039
theorem B274343 : Blo 179801 274343 := bstep (se 1 (by rfl) ⟨205757, by rfl⟩ : syracuseStep 274343 = 411515) B411515
theorem B1028051 : Blo 179801 1028051 := bstep (se 1 (by rfl) ⟨771038, by rfl⟩ : syracuseStep 1028051 = 1542077) B1542077
theorem B1781927 : Blo 179801 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B930203 : Blo 179801 930203 := bstep (se 1 (by rfl) ⟨697652, by rfl⟩ : syracuseStep 930203 = 1395305) B1395305
theorem B406007 : Blo 179801 406007 := bstep (se 1 (by rfl) ⟨304505, by rfl⟩ : syracuseStep 406007 = 609011) B609011
theorem B2306555 : Blo 179801 2306555 := bstep (se 1 (by rfl) ⟨1729916, by rfl⟩ : syracuseStep 2306555 = 3459833) B3459833
theorem B275399 : Blo 179801 275399 := bstep (se 1 (by rfl) ⟨206549, by rfl⟩ : syracuseStep 275399 = 413099) B413099
theorem B1030765 : Blo 179801 1030765 := bstep (se 3 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 1030765 = 386537) B386537
theorem B6798305 : Blo 179801 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B408671 : Blo 179801 408671 := bstep (se 1 (by rfl) ⟨306503, by rfl⟩ : syracuseStep 408671 = 613007) B613007
theorem B409067 : Blo 179801 409067 := bstep (se 1 (by rfl) ⟨306800, by rfl⟩ : syracuseStep 409067 = 613601) B613601
theorem B769961 : Blo 179801 769961 := bstep (se 2 (by rfl) ⟨288735, by rfl⟩ : syracuseStep 769961 = 577471) B577471
theorem B180251 : Blo 179801 180251 := bstep (se 1 (by rfl) ⟨135188, by rfl⟩ : syracuseStep 180251 = 270377) B270377
theorem B180295 : Blo 179801 180295 := bstep (se 1 (by rfl) ⟨135221, by rfl⟩ : syracuseStep 180295 = 270443) B270443
theorem B245935 : Blo 179801 245935 := bstep (se 1 (by rfl) ⟨184451, by rfl⟩ : syracuseStep 245935 = 368903) B368903
theorem B409823 : Blo 179801 409823 := bstep (se 1 (by rfl) ⟨307367, by rfl⟩ : syracuseStep 409823 = 614735) B614735
theorem B180463 : Blo 179801 180463 := bstep (se 1 (by rfl) ⟨135347, by rfl⟩ : syracuseStep 180463 = 270695) B270695
theorem B180543 : Blo 179801 180543 := bstep (se 1 (by rfl) ⟨135407, by rfl⟩ : syracuseStep 180543 = 270815) B270815
theorem B3228149 : Blo 179801 3228149 := bstep (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) B302639
theorem B180895 : Blo 179801 180895 := bstep (se 1 (by rfl) ⟨135671, by rfl⟩ : syracuseStep 180895 = 271343) B271343
theorem B180975 : Blo 179801 180975 := bstep (se 1 (by rfl) ⟨135731, by rfl⟩ : syracuseStep 180975 = 271463) B271463
theorem B410363 : Blo 179801 410363 := bstep (se 1 (by rfl) ⟨307772, by rfl⟩ : syracuseStep 410363 = 615545) B615545
theorem B410399 : Blo 179801 410399 := bstep (se 1 (by rfl) ⟨307799, by rfl⟩ : syracuseStep 410399 = 615599) B615599
theorem B1786681 : Blo 179801 1786681 := bstep (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) B1340011
theorem B181063 : Blo 179801 181063 := bstep (se 1 (by rfl) ⟨135797, by rfl⟩ : syracuseStep 181063 = 271595) B271595
theorem B1393847 : Blo 179801 1393847 := bstep (se 1 (by rfl) ⟨1045385, by rfl⟩ : syracuseStep 1393847 = 2090771) B2090771
theorem B247351 : Blo 179801 247351 := bstep (se 1 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 247351 = 371027) B371027
theorem B1099507 : Blo 179801 1099507 := bstep (se 1 (by rfl) ⟨824630, by rfl⟩ : syracuseStep 1099507 = 1649261) B1649261
theorem B935675 : Blo 179801 935675 := bstep (se 1 (by rfl) ⟨701756, by rfl⟩ : syracuseStep 935675 = 1403513) B1403513
theorem B182087 : Blo 179801 182087 := bstep (se 1 (by rfl) ⟨136565, by rfl⟩ : syracuseStep 182087 = 273131) B273131
theorem B182119 : Blo 179801 182119 := bstep (se 1 (by rfl) ⟨136589, by rfl⟩ : syracuseStep 182119 = 273179) B273179
theorem B1984429 : Blo 179801 1984429 := bstep (se 3 (by rfl) ⟨372080, by rfl⟩ : syracuseStep 1984429 = 744161) B744161
theorem B411641 : Blo 179801 411641 := bstep (se 2 (by rfl) ⟨154365, by rfl⟩ : syracuseStep 411641 = 308731) B308731
theorem B411695 : Blo 179801 411695 := bstep (se 1 (by rfl) ⟨308771, by rfl⟩ : syracuseStep 411695 = 617543) B617543
theorem B182687 : Blo 179801 182687 := bstep (se 1 (by rfl) ⟨137015, by rfl⟩ : syracuseStep 182687 = 274031) B274031
theorem B182759 : Blo 179801 182759 := bstep (se 1 (by rfl) ⟨137069, by rfl⟩ : syracuseStep 182759 = 274139) B274139
theorem B182767 : Blo 179801 182767 := bstep (se 1 (by rfl) ⟨137075, by rfl⟩ : syracuseStep 182767 = 274151) B274151
theorem B3328735 : Blo 179801 3328735 := bstep (se 1 (by rfl) ⟨2496551, by rfl⟩ : syracuseStep 3328735 = 4993103) B4993103
theorem B412415 : Blo 179801 412415 := bstep (se 1 (by rfl) ⟨309311, by rfl⟩ : syracuseStep 412415 = 618623) B618623
theorem B346943 : Blo 179801 346943 := bstep (se 1 (by rfl) ⟨260207, by rfl⟩ : syracuseStep 346943 = 520415) B520415
theorem B183207 : Blo 179801 183207 := bstep (se 1 (by rfl) ⟨137405, by rfl⟩ : syracuseStep 183207 = 274811) B274811
theorem B183279 : Blo 179801 183279 := bstep (se 1 (by rfl) ⟨137459, by rfl⟩ : syracuseStep 183279 = 274919) B274919
theorem B412703 : Blo 179801 412703 := bstep (se 1 (by rfl) ⟨309527, by rfl⟩ : syracuseStep 412703 = 619055) B619055
theorem B183527 : Blo 179801 183527 := bstep (se 1 (by rfl) ⟨137645, by rfl⟩ : syracuseStep 183527 = 275291) B275291
theorem B183615 : Blo 179801 183615 := bstep (se 1 (by rfl) ⟨137711, by rfl⟩ : syracuseStep 183615 = 275423) B275423
theorem B183655 : Blo 179801 183655 := bstep (se 1 (by rfl) ⟨137741, by rfl⟩ : syracuseStep 183655 = 275483) B275483
theorem B609767 : Blo 179801 609767 := bstep (se 1 (by rfl) ⟨457325, by rfl⟩ : syracuseStep 609767 = 914651) B914651
theorem B774335 : Blo 179801 774335 := bstep (se 1 (by rfl) ⟨580751, by rfl⟩ : syracuseStep 774335 = 1161503) B1161503
theorem B1659113 : Blo 179801 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B51433865 : Blo 179801 51433865 := bstep (se 2 (by rfl) ⟨19287699, by rfl⟩ : syracuseStep 51433865 = 38575399) B38575399
theorem B2249227 : Blo 179801 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B414433 : Blo 179801 414433 := bstep (se 2 (by rfl) ⟨155412, by rfl⟩ : syracuseStep 414433 = 310825) B310825
theorem B611387 : Blo 179801 611387 := bstep (se 1 (by rfl) ⟨458540, by rfl⟩ : syracuseStep 611387 = 917081) B917081
theorem B2086397 : Blo 179801 2086397 := bstep (se 3 (by rfl) ⟨391199, by rfl⟩ : syracuseStep 2086397 = 782399) B782399
theorem B1365659 : Blo 179801 1365659 := bstep (se 1 (by rfl) ⟨1024244, by rfl⟩ : syracuseStep 1365659 = 2048489) B2048489
theorem B2086603 : Blo 179801 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B1039007 : Blo 179801 1039007 := bstep (se 1 (by rfl) ⟨779255, by rfl⟩ : syracuseStep 1039007 = 1558511) B1558511
theorem B220315 : Blo 179801 220315 := bstep (se 1 (by rfl) ⟨165236, by rfl⟩ : syracuseStep 220315 = 330473) B330473
theorem B613871 : Blo 179801 613871 := bstep (se 1 (by rfl) ⟨460403, by rfl⟩ : syracuseStep 613871 = 920807) B920807
theorem B548527 : Blo 179801 548527 := bstep (se 1 (by rfl) ⟨411395, by rfl⟩ : syracuseStep 548527 = 822791) B822791
theorem B1794251 : Blo 179801 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B418127 : Blo 179801 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B10510721 : Blo 179801 10510721 := bstep (se 2 (by rfl) ⟨3941520, by rfl⟩ : syracuseStep 10510721 = 7883041) B7883041
theorem B3924571 : Blo 179801 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B910601 : Blo 179801 910601 := bstep (se 2 (by rfl) ⟨341475, by rfl⟩ : syracuseStep 910601 = 682951) B682951
theorem B910763 : Blo 179801 910763 := bstep (se 1 (by rfl) ⟨683072, by rfl⟩ : syracuseStep 910763 = 1366145) B1366145
theorem B1369547 : Blo 179801 1369547 := bstep (se 1 (by rfl) ⟨1027160, by rfl⟩ : syracuseStep 1369547 = 2054321) B2054321
theorem B911411 : Blo 179801 911411 := bstep (se 1 (by rfl) ⟨683558, by rfl⟩ : syracuseStep 911411 = 1367117) B1367117
theorem B1304819 : Blo 179801 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B911735 : Blo 179801 911735 := bstep (se 1 (by rfl) ⟨683801, by rfl⟩ : syracuseStep 911735 = 1367603) B1367603
theorem B2058695 : Blo 179801 2058695 := bstep (se 1 (by rfl) ⟨1544021, by rfl⟩ : syracuseStep 2058695 = 3088043) B3088043
theorem B256603 : Blo 179801 256603 := bstep (se 1 (by rfl) ⟨192452, by rfl⟩ : syracuseStep 256603 = 384905) B384905
theorem B977579 : Blo 179801 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B781649 : Blo 179801 781649 := bstep (se 2 (by rfl) ⟨293118, by rfl⟩ : syracuseStep 781649 = 586237) B586237
theorem B880507 : Blo 179801 880507 := bstep (se 1 (by rfl) ⟨660380, by rfl⟩ : syracuseStep 880507 = 1320761) B1320761
theorem B389099 : Blo 179801 389099 := bstep (se 1 (by rfl) ⟨291824, by rfl⟩ : syracuseStep 389099 = 583649) B583649
theorem B619163 : Blo 179801 619163 := bstep (se 1 (by rfl) ⟨464372, by rfl⟩ : syracuseStep 619163 = 928745) B928745
theorem B1241851 : Blo 179801 1241851 := bstep (se 1 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 1241851 = 1862777) B1862777
theorem B881567 : Blo 179801 881567 := bstep (se 1 (by rfl) ⟨661175, by rfl⟩ : syracuseStep 881567 = 1322351) B1322351
theorem B193627 : Blo 179801 193627 := bstep (se 1 (by rfl) ⟨145220, by rfl⟩ : syracuseStep 193627 = 290441) B290441
theorem B455807 : Blo 179801 455807 := bstep (se 1 (by rfl) ⟨341855, by rfl⟩ : syracuseStep 455807 = 683711) B683711
theorem B456313 : Blo 179801 456313 := bstep (se 2 (by rfl) ⟨171117, by rfl⟩ : syracuseStep 456313 = 342235) B342235
theorem B489167 : Blo 179801 489167 := bstep (se 1 (by rfl) ⟨366875, by rfl⟩ : syracuseStep 489167 = 733751) B733751
theorem B1373921 : Blo 179801 1373921 := bstep (se 2 (by rfl) ⟨515220, by rfl⟩ : syracuseStep 1373921 = 1030441) B1030441
theorem B2063069 : Blo 179801 2063069 := bstep (se 3 (by rfl) ⟨386825, by rfl⟩ : syracuseStep 2063069 = 773651) B773651
theorem B916271 : Blo 179801 916271 := bstep (se 1 (by rfl) ⟨687203, by rfl⟩ : syracuseStep 916271 = 1374407) B1374407
theorem B457883 : Blo 179801 457883 := bstep (se 1 (by rfl) ⟨343412, by rfl⟩ : syracuseStep 457883 = 686825) B686825
theorem B1047991 : Blo 179801 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B458399 : Blo 179801 458399 := bstep (se 1 (by rfl) ⟨343799, by rfl⟩ : syracuseStep 458399 = 687599) B687599
theorem B655019 : Blo 179801 655019 := bstep (se 1 (by rfl) ⟨491264, by rfl⟩ : syracuseStep 655019 = 982529) B982529
theorem B917243 : Blo 179801 917243 := bstep (se 1 (by rfl) ⟨687932, by rfl⟩ : syracuseStep 917243 = 1375865) B1375865
theorem B458743 : Blo 179801 458743 := bstep (se 1 (by rfl) ⟨344057, by rfl⟩ : syracuseStep 458743 = 688115) B688115
theorem B1115005 : Blo 179801 1115005 := bstep (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) B418127
theorem B1311653 : Blo 179801 1311653 := bstep (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) B245935
theorem B5276821 : Blo 179801 5276821 := bstep (se 6 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 5276821 = 247351) B247351
theorem B623783 : Blo 179801 623783 := bstep (se 1 (by rfl) ⟨467837, by rfl⟩ : syracuseStep 623783 = 935675) B935675
theorem B1967993 : Blo 179801 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B919673 : Blo 179801 919673 := bstep (se 2 (by rfl) ⟨344877, by rfl⟩ : syracuseStep 919673 = 689755) B689755
theorem B329903 : Blo 179801 329903 := bstep (se 1 (by rfl) ⟨247427, by rfl⟩ : syracuseStep 329903 = 494855) B494855
theorem B11995877 : Blo 179801 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B659603 : Blo 179801 659603 := bstep (se 1 (by rfl) ⟨494702, by rfl⟩ : syracuseStep 659603 = 989405) B989405
theorem B692671 : Blo 179801 692671 := bstep (se 1 (by rfl) ⟨519503, by rfl⟩ : syracuseStep 692671 = 1039007) B1039007
theorem B464039 : Blo 179801 464039 := bstep (se 1 (by rfl) ⟨348029, by rfl⟩ : syracuseStep 464039 = 696059) B696059
theorem B2234735 : Blo 179801 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B4988411 : Blo 179801 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B925181 : Blo 179801 925181 := bstep (se 3 (by rfl) ⟨173471, by rfl⟩ : syracuseStep 925181 = 346943) B346943
theorem B270239 : Blo 179801 270239 := bstep (se 1 (by rfl) ⟨202679, by rfl⟩ : syracuseStep 270239 = 405359) B405359
theorem B1187951 : Blo 179801 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B270473 : Blo 179801 270473 := bstep (se 2 (by rfl) ⟨101427, by rfl⟩ : syracuseStep 270473 = 202855) B202855
theorem B270671 : Blo 179801 270671 := bstep (se 1 (by rfl) ⟨203003, by rfl⟩ : syracuseStep 270671 = 406007) B406007
theorem B303871 : Blo 179801 303871 := bstep (se 1 (by rfl) ⟨227903, by rfl⟩ : syracuseStep 303871 = 455807) B455807
theorem B4532203 : Blo 179801 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B272447 : Blo 179801 272447 := bstep (se 1 (by rfl) ⟨204335, by rfl⟩ : syracuseStep 272447 = 408671) B408671
theorem B305255 : Blo 179801 305255 := bstep (se 1 (by rfl) ⟨228941, by rfl⟩ : syracuseStep 305255 = 457883) B457883
theorem B731369 : Blo 179801 731369 := bstep (se 2 (by rfl) ⟨274263, by rfl⟩ : syracuseStep 731369 = 548527) B548527
theorem B272711 : Blo 179801 272711 := bstep (se 1 (by rfl) ⟨204533, by rfl⟩ : syracuseStep 272711 = 409067) B409067
theorem B305599 : Blo 179801 305599 := bstep (se 1 (by rfl) ⟨229199, by rfl⟩ : syracuseStep 305599 = 458399) B458399
theorem B436679 : Blo 179801 436679 := bstep (se 1 (by rfl) ⟨327509, by rfl⟩ : syracuseStep 436679 = 655019) B655019
theorem B305903 : Blo 179801 305903 := bstep (se 1 (by rfl) ⟨229427, by rfl⟩ : syracuseStep 305903 = 458855) B458855
theorem B273215 : Blo 179801 273215 := bstep (se 1 (by rfl) ⟨204911, by rfl⟩ : syracuseStep 273215 = 409823) B409823
theorem B404585 : Blo 179801 404585 := bstep (se 2 (by rfl) ⟨151719, by rfl⟩ : syracuseStep 404585 = 303439) B303439
theorem B273545 : Blo 179801 273545 := bstep (se 2 (by rfl) ⟨102579, by rfl⟩ : syracuseStep 273545 = 205159) B205159
theorem B273575 : Blo 179801 273575 := bstep (se 1 (by rfl) ⟨205181, by rfl⟩ : syracuseStep 273575 = 410363) B410363
theorem B273599 : Blo 179801 273599 := bstep (se 1 (by rfl) ⟨205199, by rfl⟩ : syracuseStep 273599 = 410399) B410399
theorem B929231 : Blo 179801 929231 := bstep (se 1 (by rfl) ⟨696923, by rfl⟩ : syracuseStep 929231 = 1393847) B1393847
theorem B274409 : Blo 179801 274409 := bstep (se 2 (by rfl) ⟨102903, by rfl⟩ : syracuseStep 274409 = 205807) B205807
theorem B274427 : Blo 179801 274427 := bstep (se 1 (by rfl) ⟨205820, by rfl⟩ : syracuseStep 274427 = 411641) B411641
theorem B274463 : Blo 179801 274463 := bstep (se 1 (by rfl) ⟨205847, by rfl⟩ : syracuseStep 274463 = 411695) B411695
theorem B274553 : Blo 179801 274553 := bstep (se 2 (by rfl) ⟨102957, by rfl⟩ : syracuseStep 274553 = 205915) B205915
theorem B274943 : Blo 179801 274943 := bstep (se 1 (by rfl) ⟨206207, by rfl⟩ : syracuseStep 274943 = 412415) B412415
theorem B307759 : Blo 179801 307759 := bstep (se 1 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 307759 = 461639) B461639
theorem B275135 : Blo 179801 275135 := bstep (se 1 (by rfl) ⟨206351, by rfl⟩ : syracuseStep 275135 = 412703) B412703
theorem B308191 : Blo 179801 308191 := bstep (se 1 (by rfl) ⟨231143, by rfl⟩ : syracuseStep 308191 = 462287) B462287
theorem B406511 : Blo 179801 406511 := bstep (se 1 (by rfl) ⟨304883, by rfl⟩ : syracuseStep 406511 = 609767) B609767
theorem B34289243 : Blo 179801 34289243 := bstep (se 1 (by rfl) ⟨25716932, by rfl⟩ : syracuseStep 34289243 = 51433865) B51433865
theorem B440063 : Blo 179801 440063 := bstep (se 1 (by rfl) ⟨330047, by rfl⟩ : syracuseStep 440063 = 660095) B660095
theorem B407591 : Blo 179801 407591 := bstep (se 1 (by rfl) ⟨305693, by rfl⟩ : syracuseStep 407591 = 611387) B611387
theorem B342137 : Blo 179801 342137 := bstep (se 2 (by rfl) ⟨128301, by rfl⟩ : syracuseStep 342137 = 256603) B256603
theorem B2013443 : Blo 179801 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B4438313 : Blo 179801 4438313 := bstep (se 2 (by rfl) ⟨1664367, by rfl⟩ : syracuseStep 4438313 = 3328735) B3328735
theorem B1390931 : Blo 179801 1390931 := bstep (se 1 (by rfl) ⟨1043198, by rfl⟩ : syracuseStep 1390931 = 2086397) B2086397
theorem B408041 : Blo 179801 408041 := bstep (se 2 (by rfl) ⟨153015, by rfl⟩ : syracuseStep 408041 = 306031) B306031
theorem B309737 : Blo 179801 309737 := bstep (se 2 (by rfl) ⟨116151, by rfl⟩ : syracuseStep 309737 = 232303) B232303
theorem B91241777 : Blo 179801 91241777 := bstep (se 2 (by rfl) ⟨34215666, by rfl⟩ : syracuseStep 91241777 = 68431333) B68431333
theorem B409247 : Blo 179801 409247 := bstep (se 1 (by rfl) ⟨306935, by rfl⟩ : syracuseStep 409247 = 613871) B613871
theorem B4440055 : Blo 179801 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B5554183 : Blo 179801 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B1196167 : Blo 179801 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B607067 : Blo 179801 607067 := bstep (se 1 (by rfl) ⟨455300, by rfl⟩ : syracuseStep 607067 = 910601) B910601
theorem B181083 : Blo 179801 181083 := bstep (se 1 (by rfl) ⟨135812, by rfl⟩ : syracuseStep 181083 = 271625) B271625
theorem B607175 : Blo 179801 607175 := bstep (se 1 (by rfl) ⟨455381, by rfl⟩ : syracuseStep 607175 = 910763) B910763
theorem B1655801 : Blo 179801 1655801 := bstep (se 2 (by rfl) ⟨620925, by rfl⟩ : syracuseStep 1655801 = 1241851) B1241851
theorem B181403 : Blo 179801 181403 := bstep (se 1 (by rfl) ⟨136052, by rfl⟩ : syracuseStep 181403 = 272105) B272105
theorem B2082023 : Blo 179801 2082023 := bstep (se 1 (by rfl) ⟨1561517, by rfl⟩ : syracuseStep 2082023 = 3123035) B3123035
theorem B607607 : Blo 179801 607607 := bstep (se 1 (by rfl) ⟨455705, by rfl⟩ : syracuseStep 607607 = 911411) B911411
theorem B181727 : Blo 179801 181727 := bstep (se 1 (by rfl) ⟨136295, by rfl⟩ : syracuseStep 181727 = 272591) B272591
theorem B869879 : Blo 179801 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B181759 : Blo 179801 181759 := bstep (se 1 (by rfl) ⟨136319, by rfl⟩ : syracuseStep 181759 = 272639) B272639
theorem B607823 : Blo 179801 607823 := bstep (se 1 (by rfl) ⟨455867, by rfl⟩ : syracuseStep 607823 = 911735) B911735
theorem B181999 : Blo 179801 181999 := bstep (se 1 (by rfl) ⟨136499, by rfl⟩ : syracuseStep 181999 = 272999) B272999
theorem B182107 : Blo 179801 182107 := bstep (se 1 (by rfl) ⟨136580, by rfl⟩ : syracuseStep 182107 = 273161) B273161
theorem B608417 : Blo 179801 608417 := bstep (se 2 (by rfl) ⟨228156, by rfl⟩ : syracuseStep 608417 = 456313) B456313
theorem B1231037 : Blo 179801 1231037 := bstep (se 3 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 1231037 = 461639) B461639
theorem B182599 : Blo 179801 182599 := bstep (se 1 (by rfl) ⟨136949, by rfl⟩ : syracuseStep 182599 = 273899) B273899
theorem B182895 : Blo 179801 182895 := bstep (se 1 (by rfl) ⟨137171, by rfl⟩ : syracuseStep 182895 = 274343) B274343
theorem B412775 : Blo 179801 412775 := bstep (se 1 (by rfl) ⟨309581, by rfl⟩ : syracuseStep 412775 = 619163) B619163
theorem B183599 : Blo 179801 183599 := bstep (se 1 (by rfl) ⟨137699, by rfl⟩ : syracuseStep 183599 = 275399) B275399
theorem B11128549 : Blo 179801 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B610847 : Blo 179801 610847 := bstep (se 1 (by rfl) ⟨458135, by rfl⟩ : syracuseStep 610847 = 916271) B916271
theorem B1397321 : Blo 179801 1397321 := bstep (se 2 (by rfl) ⟨523995, by rfl⟩ : syracuseStep 1397321 = 1047991) B1047991
theorem B611495 : Blo 179801 611495 := bstep (se 1 (by rfl) ⟨458621, by rfl⟩ : syracuseStep 611495 = 917243) B917243
theorem B513307 : Blo 179801 513307 := bstep (se 1 (by rfl) ⟨384980, by rfl⟩ : syracuseStep 513307 = 769961) B769961
theorem B611657 : Blo 179801 611657 := bstep (se 2 (by rfl) ⟨229371, by rfl⟩ : syracuseStep 611657 = 458743) B458743
theorem B1660283 : Blo 179801 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B2152099 : Blo 179801 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B11097983 : Blo 179801 11097983 := bstep (se 1 (by rfl) ⟨8323487, by rfl⟩ : syracuseStep 11097983 = 16646975) B16646975
theorem B5232761 : Blo 179801 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B612575 : Blo 179801 612575 := bstep (se 1 (by rfl) ⟨459431, by rfl⟩ : syracuseStep 612575 = 918863) B918863
theorem B1466009 : Blo 179801 1466009 := bstep (se 2 (by rfl) ⟨549753, by rfl⟩ : syracuseStep 1466009 = 1099507) B1099507
theorem B2645905 : Blo 179801 2645905 := bstep (se 2 (by rfl) ⟨992214, by rfl⟩ : syracuseStep 2645905 = 1984429) B1984429
theorem B548819 : Blo 179801 548819 := bstep (se 1 (by rfl) ⟨411614, by rfl⟩ : syracuseStep 548819 = 823229) B823229
theorem B516223 : Blo 179801 516223 := bstep (se 1 (by rfl) ⟨387167, by rfl⟩ : syracuseStep 516223 = 774335) B774335
theorem B1106075 : Blo 179801 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B910439 : Blo 179801 910439 := bstep (se 1 (by rfl) ⟨682829, by rfl⟩ : syracuseStep 910439 = 1365659) B1365659
theorem B3499199 : Blo 179801 3499199 := bstep (se 1 (by rfl) ⟨2624399, by rfl⟩ : syracuseStep 3499199 = 5248799) B5248799
theorem B9528965 : Blo 179801 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B616939 : Blo 179801 616939 := bstep (se 1 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 616939 = 925409) B925409
theorem B1174009 : Blo 179801 1174009 := bstep (se 2 (by rfl) ⟨440253, by rfl⟩ : syracuseStep 1174009 = 880507) B880507
theorem B7007147 : Blo 179801 7007147 := bstep (se 1 (by rfl) ⟨5255360, by rfl⟩ : syracuseStep 7007147 = 10510721) B10510721
theorem B552577 : Blo 179801 552577 := bstep (se 2 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 552577 = 414433) B414433
theorem B913031 : Blo 179801 913031 := bstep (se 1 (by rfl) ⟨684773, by rfl⟩ : syracuseStep 913031 = 1369547) B1369547
theorem B258169 : Blo 179801 258169 := bstep (se 2 (by rfl) ⟨96813, by rfl⟩ : syracuseStep 258169 = 193627) B193627
theorem B618731 : Blo 179801 618731 := bstep (se 1 (by rfl) ⟨464048, by rfl⟩ : syracuseStep 618731 = 928097) B928097
theorem B1372463 : Blo 179801 1372463 := bstep (se 1 (by rfl) ⟨1029347, by rfl⟩ : syracuseStep 1372463 = 2058695) B2058695
theorem B651719 : Blo 179801 651719 := bstep (se 1 (by rfl) ⟨488789, by rfl⟩ : syracuseStep 651719 = 977579) B977579
theorem B521099 : Blo 179801 521099 := bstep (se 1 (by rfl) ⟨390824, by rfl⟩ : syracuseStep 521099 = 781649) B781649
theorem B685367 : Blo 179801 685367 := bstep (se 1 (by rfl) ⟨514025, by rfl⟩ : syracuseStep 685367 = 1028051) B1028051
theorem B259399 : Blo 179801 259399 := bstep (se 1 (by rfl) ⟨194549, by rfl⟩ : syracuseStep 259399 = 389099) B389099
theorem B620135 : Blo 179801 620135 := bstep (se 1 (by rfl) ⟨465101, by rfl⟩ : syracuseStep 620135 = 930203) B930203
theorem B1537703 : Blo 179801 1537703 := bstep (se 1 (by rfl) ⟨1153277, by rfl⟩ : syracuseStep 1537703 = 2306555) B2306555
theorem B587711 : Blo 179801 587711 := bstep (se 1 (by rfl) ⟨440783, by rfl⟩ : syracuseStep 587711 = 881567) B881567
theorem B1374353 : Blo 179801 1374353 := bstep (se 2 (by rfl) ⟨515382, by rfl⟩ : syracuseStep 1374353 = 1030765) B1030765
theorem B326111 : Blo 179801 326111 := bstep (se 1 (by rfl) ⟨244583, by rfl⟩ : syracuseStep 326111 = 489167) B489167
theorem B915947 : Blo 179801 915947 := bstep (se 1 (by rfl) ⟨686960, by rfl⟩ : syracuseStep 915947 = 1373921) B1373921
theorem B293753 : Blo 179801 293753 := bstep (se 2 (by rfl) ⟨110157, by rfl⟩ : syracuseStep 293753 = 220315) B220315
theorem B1375379 : Blo 179801 1375379 := bstep (se 1 (by rfl) ⟨1031534, by rfl⟩ : syracuseStep 1375379 = 2063069) B2063069
theorem B7405577 : Blo 179801 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B688297 : Blo 179801 688297 := bstep (se 2 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 688297 = 516223) B516223
theorem B2949533 : Blo 179801 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B1311995 : Blo 179801 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B820691 : Blo 179801 820691 := bstep (se 1 (by rfl) ⟨615518, by rfl⟩ : syracuseStep 820691 = 1231037) B1231037
theorem B7997251 : Blo 179801 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B29594621 : Blo 179801 29594621 := bstep (se 3 (by rfl) ⟨5548991, by rfl⟩ : syracuseStep 29594621 = 11097983) B11097983
theorem B365879 : Blo 179801 365879 := bstep (se 1 (by rfl) ⟨274409, by rfl⟩ : syracuseStep 365879 = 548819) B548819
theorem B923561 : Blo 179801 923561 := bstep (se 2 (by rfl) ⟨346335, by rfl⟩ : syracuseStep 923561 = 692671) B692671
theorem B2332799 : Blo 179801 2332799 := bstep (se 1 (by rfl) ⟨1749599, by rfl⟩ : syracuseStep 2332799 = 3499199) B3499199
theorem B203503 : Blo 179801 203503 := bstep (se 1 (by rfl) ⟨152627, by rfl⟩ : syracuseStep 203503 = 305255) B305255
theorem B203935 : Blo 179801 203935 := bstep (se 1 (by rfl) ⟨152951, by rfl⟩ : syracuseStep 203935 = 305903) B305903
theorem B269723 : Blo 179801 269723 := bstep (se 1 (by rfl) ⟨202292, by rfl⟩ : syracuseStep 269723 = 404585) B404585
theorem B434479 : Blo 179801 434479 := bstep (se 1 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 434479 = 651719) B651719
theorem B271007 : Blo 179801 271007 := bstep (se 1 (by rfl) ⟨203255, by rfl⟩ : syracuseStep 271007 = 406511) B406511
theorem B1025135 : Blo 179801 1025135 := bstep (se 1 (by rfl) ⟨768851, by rfl⟩ : syracuseStep 1025135 = 1537703) B1537703
theorem B271727 : Blo 179801 271727 := bstep (se 1 (by rfl) ⟨203795, by rfl⟩ : syracuseStep 271727 = 407591) B407591
theorem B2958875 : Blo 179801 2958875 := bstep (se 1 (by rfl) ⟨2219156, by rfl⟩ : syracuseStep 2958875 = 4438313) B4438313
theorem B927287 : Blo 179801 927287 := bstep (se 1 (by rfl) ⟨695465, by rfl⟩ : syracuseStep 927287 = 1390931) B1390931
theorem B272027 : Blo 179801 272027 := bstep (se 1 (by rfl) ⟨204020, by rfl⟩ : syracuseStep 272027 = 408041) B408041
theorem B206491 : Blo 179801 206491 := bstep (se 1 (by rfl) ⟨154868, by rfl⟩ : syracuseStep 206491 = 309737) B309737
theorem B60827851 : Blo 179801 60827851 := bstep (se 1 (by rfl) ⟨45620888, by rfl⟩ : syracuseStep 60827851 = 91241777) B91241777
theorem B272831 : Blo 179801 272831 := bstep (se 1 (by rfl) ⟨204623, by rfl⟩ : syracuseStep 272831 = 409247) B409247
theorem B404711 : Blo 179801 404711 := bstep (se 1 (by rfl) ⟨303533, by rfl⟩ : syracuseStep 404711 = 607067) B607067
theorem B404783 : Blo 179801 404783 := bstep (se 1 (by rfl) ⟨303587, by rfl⟩ : syracuseStep 404783 = 607175) B607175
theorem B1388015 : Blo 179801 1388015 := bstep (se 1 (by rfl) ⟨1041011, by rfl⟩ : syracuseStep 1388015 = 2082023) B2082023
theorem B405071 : Blo 179801 405071 := bstep (se 1 (by rfl) ⟨303803, by rfl⟩ : syracuseStep 405071 = 607607) B607607
theorem B405161 : Blo 179801 405161 := bstep (se 2 (by rfl) ⟨151935, by rfl⟩ : syracuseStep 405161 = 303871) B303871
theorem B405215 : Blo 179801 405215 := bstep (se 1 (by rfl) ⟨303911, by rfl⟩ : syracuseStep 405215 = 607823) B607823
theorem B1486673 : Blo 179801 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B405611 : Blo 179801 405611 := bstep (se 1 (by rfl) ⟨304208, by rfl⟩ : syracuseStep 405611 = 608417) B608417
theorem B275183 : Blo 179801 275183 := bstep (se 1 (by rfl) ⟨206387, by rfl⟩ : syracuseStep 275183 = 412775) B412775
theorem B6042937 : Blo 179801 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B407231 : Blo 179801 407231 := bstep (se 1 (by rfl) ⟨305423, by rfl⟩ : syracuseStep 407231 = 610847) B610847
theorem B931547 : Blo 179801 931547 := bstep (se 1 (by rfl) ⟨698660, by rfl⟩ : syracuseStep 931547 = 1397321) B1397321
theorem B407465 : Blo 179801 407465 := bstep (se 2 (by rfl) ⟨152799, by rfl⟩ : syracuseStep 407465 = 305599) B305599
theorem B407663 : Blo 179801 407663 := bstep (se 1 (by rfl) ⟨305747, by rfl⟩ : syracuseStep 407663 = 611495) B611495
theorem B309359 : Blo 179801 309359 := bstep (se 1 (by rfl) ⟨232019, by rfl⟩ : syracuseStep 309359 = 464039) B464039
theorem B407771 : Blo 179801 407771 := bstep (se 1 (by rfl) ⟨305828, by rfl⟩ : syracuseStep 407771 = 611657) B611657
theorem B3488507 : Blo 179801 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B408383 : Blo 179801 408383 := bstep (se 1 (by rfl) ⟨306287, by rfl⟩ : syracuseStep 408383 = 612575) B612575
theorem B1489823 : Blo 179801 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B736769 : Blo 179801 736769 := bstep (se 2 (by rfl) ⟨276288, by rfl⟩ : syracuseStep 736769 = 552577) B552577
theorem B3325607 : Blo 179801 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B180159 : Blo 179801 180159 := bstep (se 1 (by rfl) ⟨135119, by rfl⟩ : syracuseStep 180159 = 270239) B270239
theorem B180315 : Blo 179801 180315 := bstep (se 1 (by rfl) ⟨135236, by rfl⟩ : syracuseStep 180315 = 270473) B270473
theorem B344225 : Blo 179801 344225 := bstep (se 2 (by rfl) ⟨129084, by rfl⟩ : syracuseStep 344225 = 258169) B258169
theorem B180447 : Blo 179801 180447 := bstep (se 1 (by rfl) ⟨135335, by rfl⟩ : syracuseStep 180447 = 270671) B270671
theorem B410345 : Blo 179801 410345 := bstep (se 2 (by rfl) ⟨153879, by rfl⟩ : syracuseStep 410345 = 307759) B307759
theorem B606959 : Blo 179801 606959 := bstep (se 1 (by rfl) ⟨455219, by rfl⟩ : syracuseStep 606959 = 910439) B910439
theorem B869629 : Blo 179801 869629 := bstep (se 3 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 869629 = 326111) B326111
theorem B410921 : Blo 179801 410921 := bstep (se 2 (by rfl) ⟨154095, by rfl⟩ : syracuseStep 410921 = 308191) B308191
theorem B181631 : Blo 179801 181631 := bstep (se 1 (by rfl) ⟨136223, by rfl⟩ : syracuseStep 181631 = 272447) B272447
theorem B181807 : Blo 179801 181807 := bstep (se 1 (by rfl) ⟨136355, by rfl⟩ : syracuseStep 181807 = 272711) B272711
theorem B345865 : Blo 179801 345865 := bstep (se 2 (by rfl) ⟨129699, by rfl⟩ : syracuseStep 345865 = 259399) B259399
theorem B182143 : Blo 179801 182143 := bstep (se 1 (by rfl) ⟨136607, by rfl⟩ : syracuseStep 182143 = 273215) B273215
theorem B4671431 : Blo 179801 4671431 := bstep (se 1 (by rfl) ⟨3503573, by rfl⟩ : syracuseStep 4671431 = 7007147) B7007147
theorem B182363 : Blo 179801 182363 := bstep (se 1 (by rfl) ⟨136772, by rfl⟩ : syracuseStep 182363 = 273545) B273545
theorem B182383 : Blo 179801 182383 := bstep (se 1 (by rfl) ⟨136787, by rfl⟩ : syracuseStep 182383 = 273575) B273575
theorem B182399 : Blo 179801 182399 := bstep (se 1 (by rfl) ⟨136799, by rfl⟩ : syracuseStep 182399 = 273599) B273599
theorem B2869465 : Blo 179801 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B608687 : Blo 179801 608687 := bstep (se 1 (by rfl) ⟨456515, by rfl⟩ : syracuseStep 608687 = 913031) B913031
theorem B182939 : Blo 179801 182939 := bstep (se 1 (by rfl) ⟨137204, by rfl⟩ : syracuseStep 182939 = 274409) B274409
theorem B182951 : Blo 179801 182951 := bstep (se 1 (by rfl) ⟨137213, by rfl⟩ : syracuseStep 182951 = 274427) B274427
theorem B182975 : Blo 179801 182975 := bstep (se 1 (by rfl) ⟨137231, by rfl⟩ : syracuseStep 182975 = 274463) B274463
theorem B183035 : Blo 179801 183035 := bstep (se 1 (by rfl) ⟨137276, by rfl⟩ : syracuseStep 183035 = 274553) B274553
theorem B412487 : Blo 179801 412487 := bstep (se 1 (by rfl) ⟨309365, by rfl⟩ : syracuseStep 412487 = 618731) B618731
theorem B183295 : Blo 179801 183295 := bstep (se 1 (by rfl) ⟨137471, by rfl⟩ : syracuseStep 183295 = 274943) B274943
theorem B183423 : Blo 179801 183423 := bstep (se 1 (by rfl) ⟨137567, by rfl⟩ : syracuseStep 183423 = 275135) B275135
theorem B347399 : Blo 179801 347399 := bstep (se 1 (by rfl) ⟨260549, by rfl⟩ : syracuseStep 347399 = 521099) B521099
theorem B22859495 : Blo 179801 22859495 := bstep (se 1 (by rfl) ⟨17144621, by rfl⟩ : syracuseStep 22859495 = 34289243) B34289243
theorem B413423 : Blo 179801 413423 := bstep (se 1 (by rfl) ⟨310067, by rfl⟩ : syracuseStep 413423 = 620135) B620135
theorem B610631 : Blo 179801 610631 := bstep (se 1 (by rfl) ⟨457973, by rfl⟩ : syracuseStep 610631 = 915947) B915947
theorem B13161365 : Blo 179801 13161365 := bstep (se 6 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 13161365 = 616939) B616939
theorem B3527873 : Blo 179801 3527873 := bstep (se 2 (by rfl) ⟨1322952, by rfl⟩ : syracuseStep 3527873 = 2645905) B2645905
theorem B5920073 : Blo 179801 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B1594889 : Blo 179801 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B1758941 : Blo 179801 1758941 := bstep (se 3 (by rfl) ⟨329801, by rfl⟩ : syracuseStep 1758941 = 659603) B659603
theorem B874435 : Blo 179801 874435 := bstep (se 1 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 874435 = 1311653) B1311653
theorem B1103867 : Blo 179801 1103867 := bstep (se 1 (by rfl) ⟨827900, by rfl⟩ : syracuseStep 1103867 = 1655801) B1655801
theorem B415855 : Blo 179801 415855 := bstep (se 1 (by rfl) ⟨311891, by rfl⟩ : syracuseStep 415855 = 623783) B623783
theorem B12671477 : Blo 179801 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B613115 : Blo 179801 613115 := bstep (se 1 (by rfl) ⟨459836, by rfl⟩ : syracuseStep 613115 = 919673) B919673
theorem B219935 : Blo 179801 219935 := bstep (se 1 (by rfl) ⟨164951, by rfl⟩ : syracuseStep 219935 = 329903) B329903
theorem B7035761 : Blo 179801 7035761 := bstep (se 2 (by rfl) ⟨2638410, by rfl⟩ : syracuseStep 7035761 = 5276821) B5276821
theorem B1565345 : Blo 179801 1565345 := bstep (se 2 (by rfl) ⟨587004, by rfl⟩ : syracuseStep 1565345 = 1174009) B1174009
theorem B1106855 : Blo 179801 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B2319677 : Blo 179801 2319677 := bstep (se 3 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 2319677 = 869879) B869879
theorem B14838065 : Blo 179801 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B616787 : Blo 179801 616787 := bstep (se 1 (by rfl) ⟨462590, by rfl⟩ : syracuseStep 616787 = 925181) B925181
theorem B977339 : Blo 179801 977339 := bstep (se 1 (by rfl) ⟨733004, by rfl⟩ : syracuseStep 977339 = 1466009) B1466009
theorem B6352643 : Blo 179801 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B487579 : Blo 179801 487579 := bstep (se 1 (by rfl) ⟨365684, by rfl⟩ : syracuseStep 487579 = 731369) B731369
theorem B291119 : Blo 179801 291119 := bstep (se 1 (by rfl) ⟨218339, by rfl⟩ : syracuseStep 291119 = 436679) B436679
theorem B684409 : Blo 179801 684409 := bstep (se 2 (by rfl) ⟨256653, by rfl⟩ : syracuseStep 684409 = 513307) B513307
theorem B619487 : Blo 179801 619487 := bstep (se 1 (by rfl) ⟨464615, by rfl⟩ : syracuseStep 619487 = 929231) B929231
theorem B783341 : Blo 179801 783341 := bstep (se 3 (by rfl) ⟨146876, by rfl⟩ : syracuseStep 783341 = 293753) B293753
theorem B914975 : Blo 179801 914975 := bstep (se 1 (by rfl) ⟨686231, by rfl⟩ : syracuseStep 914975 = 1372463) B1372463
theorem B456911 : Blo 179801 456911 := bstep (se 1 (by rfl) ⟨342683, by rfl⟩ : syracuseStep 456911 = 685367) B685367
theorem B293375 : Blo 179801 293375 := bstep (se 1 (by rfl) ⟨220031, by rfl⟩ : syracuseStep 293375 = 440063) B440063
theorem B391807 : Blo 179801 391807 := bstep (se 1 (by rfl) ⟨293855, by rfl⟩ : syracuseStep 391807 = 587711) B587711
theorem B228091 : Blo 179801 228091 := bstep (se 1 (by rfl) ⟨171068, by rfl⟩ : syracuseStep 228091 = 342137) B342137
theorem B916235 : Blo 179801 916235 := bstep (se 1 (by rfl) ⟨687176, by rfl⟩ : syracuseStep 916235 = 1374353) B1374353
theorem B1342295 : Blo 179801 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B916919 : Blo 179801 916919 := bstep (se 1 (by rfl) ⟨687689, by rfl⟩ : syracuseStep 916919 = 1375379) B1375379
theorem B229483 : Blo 179801 229483 := bstep (se 1 (by rfl) ⟨172112, by rfl⟩ : syracuseStep 229483 = 344225) B344225
theorem B917729 : Blo 179801 917729 := bstep (se 2 (by rfl) ⟨344148, by rfl⟩ : syracuseStep 917729 = 688297) B688297
theorem B1966355 : Blo 179801 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B3114287 : Blo 179801 3114287 := bstep (se 1 (by rfl) ⟨2335715, by rfl⟩ : syracuseStep 3114287 = 4671431) B4671431
theorem B231599 : Blo 179801 231599 := bstep (se 1 (by rfl) ⟨173699, by rfl⟩ : syracuseStep 231599 = 347399) B347399
theorem B461153 : Blo 179801 461153 := bstep (se 2 (by rfl) ⟨172932, by rfl⟩ : syracuseStep 461153 = 345865) B345865
theorem B15239663 : Blo 179801 15239663 := bstep (se 1 (by rfl) ⟨11429747, by rfl⟩ : syracuseStep 15239663 = 22859495) B22859495
theorem B81103801 : Blo 179801 81103801 := bstep (se 2 (by rfl) ⟨30413925, by rfl⟩ : syracuseStep 81103801 = 60827851) B60827851
theorem B19729747 : Blo 179801 19729747 := bstep (se 1 (by rfl) ⟨14797310, by rfl⟩ : syracuseStep 19729747 = 29594621) B29594621
theorem B4690507 : Blo 179801 4690507 := bstep (se 1 (by rfl) ⟨3517880, by rfl⟩ : syracuseStep 4690507 = 7035761) B7035761
theorem B1546451 : Blo 179801 1546451 := bstep (se 1 (by rfl) ⟨1159838, by rfl⟩ : syracuseStep 1546451 = 2319677) B2319677
theorem B1972583 : Blo 179801 1972583 := bstep (se 1 (by rfl) ⟨1479437, by rfl⟩ : syracuseStep 1972583 = 2958875) B2958875
theorem B269807 : Blo 179801 269807 := bstep (se 1 (by rfl) ⟨202355, by rfl⟩ : syracuseStep 269807 = 404711) B404711
theorem B269855 : Blo 179801 269855 := bstep (se 1 (by rfl) ⟨202391, by rfl⟩ : syracuseStep 269855 = 404783) B404783
theorem B925343 : Blo 179801 925343 := bstep (se 1 (by rfl) ⟨694007, by rfl⟩ : syracuseStep 925343 = 1388015) B1388015
theorem B270047 : Blo 179801 270047 := bstep (se 1 (by rfl) ⟨202535, by rfl⟩ : syracuseStep 270047 = 405071) B405071
theorem B270107 : Blo 179801 270107 := bstep (se 1 (by rfl) ⟨202580, by rfl⟩ : syracuseStep 270107 = 405161) B405161
theorem B270143 : Blo 179801 270143 := bstep (se 1 (by rfl) ⟨202607, by rfl⟩ : syracuseStep 270143 = 405215) B405215
theorem B4235095 : Blo 179801 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B991115 : Blo 179801 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B270407 : Blo 179801 270407 := bstep (se 1 (by rfl) ⟨202805, by rfl⟩ : syracuseStep 270407 = 405611) B405611
theorem B271337 : Blo 179801 271337 := bstep (se 2 (by rfl) ⟨101751, by rfl⟩ : syracuseStep 271337 = 203503) B203503
theorem B304121 : Blo 179801 304121 := bstep (se 2 (by rfl) ⟨114045, by rfl⟩ : syracuseStep 304121 = 228091) B228091
theorem B271487 : Blo 179801 271487 := bstep (se 1 (by rfl) ⟨203615, by rfl⟩ : syracuseStep 271487 = 407231) B407231
theorem B271643 : Blo 179801 271643 := bstep (se 1 (by rfl) ⟨203732, by rfl⟩ : syracuseStep 271643 = 407465) B407465
theorem B271775 : Blo 179801 271775 := bstep (se 1 (by rfl) ⟨203831, by rfl⟩ : syracuseStep 271775 = 407663) B407663
theorem B206239 : Blo 179801 206239 := bstep (se 1 (by rfl) ⟨154679, by rfl⟩ : syracuseStep 206239 = 309359) B309359
theorem B304607 : Blo 179801 304607 := bstep (se 1 (by rfl) ⟨228455, by rfl⟩ : syracuseStep 304607 = 456911) B456911
theorem B271847 : Blo 179801 271847 := bstep (se 1 (by rfl) ⟨203885, by rfl⟩ : syracuseStep 271847 = 407771) B407771
theorem B271913 : Blo 179801 271913 := bstep (se 2 (by rfl) ⟨101967, by rfl⟩ : syracuseStep 271913 = 203935) B203935
theorem B272255 : Blo 179801 272255 := bstep (se 1 (by rfl) ⟨204191, by rfl⟩ : syracuseStep 272255 = 408383) B408383
theorem B894863 : Blo 179801 894863 := bstep (se 1 (by rfl) ⟨671147, by rfl⟩ : syracuseStep 894863 = 1342295) B1342295
theorem B993215 : Blo 179801 993215 := bstep (se 1 (by rfl) ⟨744911, by rfl⟩ : syracuseStep 993215 = 1489823) B1489823
theorem B273563 : Blo 179801 273563 := bstep (se 1 (by rfl) ⟨205172, by rfl⟩ : syracuseStep 273563 = 410345) B410345
theorem B404639 : Blo 179801 404639 := bstep (se 1 (by rfl) ⟨303479, by rfl⟩ : syracuseStep 404639 = 606959) B606959
theorem B273947 : Blo 179801 273947 := bstep (se 1 (by rfl) ⟨205460, by rfl⟩ : syracuseStep 273947 = 410921) B410921
theorem B405791 : Blo 179801 405791 := bstep (se 1 (by rfl) ⟨304343, by rfl⟩ : syracuseStep 405791 = 608687) B608687
theorem B1159505 : Blo 179801 1159505 := bstep (se 2 (by rfl) ⟨434814, by rfl⟩ : syracuseStep 1159505 = 869629) B869629
theorem B274991 : Blo 179801 274991 := bstep (se 1 (by rfl) ⟨206243, by rfl⟩ : syracuseStep 274991 = 412487) B412487
theorem B275321 : Blo 179801 275321 := bstep (se 2 (by rfl) ⟨103245, by rfl⟩ : syracuseStep 275321 = 206491) B206491
theorem B10663001 : Blo 179801 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B275615 : Blo 179801 275615 := bstep (se 1 (by rfl) ⟨206711, by rfl⟩ : syracuseStep 275615 = 413423) B413423
theorem B407087 : Blo 179801 407087 := bstep (se 1 (by rfl) ⟨305315, by rfl⟩ : syracuseStep 407087 = 610631) B610631
theorem B243919 : Blo 179801 243919 := bstep (se 1 (by rfl) ⟨182939, by rfl⟩ : syracuseStep 243919 = 365879) B365879
theorem B3946715 : Blo 179801 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B1063259 : Blo 179801 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B735911 : Blo 179801 735911 := bstep (se 1 (by rfl) ⟨551933, by rfl⟩ : syracuseStep 735911 = 1103867) B1103867
theorem B1555199 : Blo 179801 1555199 := bstep (se 1 (by rfl) ⟨1166399, by rfl⟩ : syracuseStep 1555199 = 2332799) B2332799
theorem B408743 : Blo 179801 408743 := bstep (se 1 (by rfl) ⟨306557, by rfl⟩ : syracuseStep 408743 = 613115) B613115
theorem B179815 : Blo 179801 179815 := bstep (se 1 (by rfl) ⟨134861, by rfl⟩ : syracuseStep 179815 = 269723) B269723
theorem B180671 : Blo 179801 180671 := bstep (se 1 (by rfl) ⟨135503, by rfl⟩ : syracuseStep 180671 = 271007) B271007
theorem B737903 : Blo 179801 737903 := bstep (se 1 (by rfl) ⟨553427, by rfl⟩ : syracuseStep 737903 = 1106855) B1106855
theorem B181151 : Blo 179801 181151 := bstep (se 1 (by rfl) ⟨135863, by rfl⟩ : syracuseStep 181151 = 271727) B271727
theorem B181351 : Blo 179801 181351 := bstep (se 1 (by rfl) ⟨136013, by rfl⟩ : syracuseStep 181351 = 272027) B272027
theorem B411191 : Blo 179801 411191 := bstep (se 1 (by rfl) ⟨308393, by rfl⟩ : syracuseStep 411191 = 616787) B616787
theorem B181887 : Blo 179801 181887 := bstep (se 1 (by rfl) ⟨136415, by rfl⟩ : syracuseStep 181887 = 272831) B272831
theorem B1165913 : Blo 179801 1165913 := bstep (se 2 (by rfl) ⟨437217, by rfl⟩ : syracuseStep 1165913 = 874435) B874435
theorem B183455 : Blo 179801 183455 := bstep (se 1 (by rfl) ⟨137591, by rfl⟩ : syracuseStep 183455 = 275183) B275183
theorem B412991 : Blo 179801 412991 := bstep (se 1 (by rfl) ⟨309743, by rfl⟩ : syracuseStep 412991 = 619487) B619487
theorem B609983 : Blo 179801 609983 := bstep (se 1 (by rfl) ⟨457487, by rfl⟩ : syracuseStep 609983 = 914975) B914975
theorem B610823 : Blo 179801 610823 := bstep (se 1 (by rfl) ⟨458117, by rfl⟩ : syracuseStep 610823 = 916235) B916235
theorem B611279 : Blo 179801 611279 := bstep (se 1 (by rfl) ⟨458459, by rfl⟩ : syracuseStep 611279 = 916919) B916919
theorem B2217071 : Blo 179801 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B4937051 : Blo 179801 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B579305 : Blo 179801 579305 := bstep (se 2 (by rfl) ⟨217239, by rfl⟩ : syracuseStep 579305 = 434479) B434479
theorem B776317 : Blo 179801 776317 := bstep (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) B291119
theorem B547127 : Blo 179801 547127 := bstep (se 1 (by rfl) ⟨410345, by rfl⟩ : syracuseStep 547127 = 820691) B820691
theorem B3825953 : Blo 179801 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B8774243 : Blo 179801 8774243 := bstep (se 1 (by rfl) ⟨6580682, by rfl⟩ : syracuseStep 8774243 = 13161365) B13161365
theorem B3498653 : Blo 179801 3498653 := bstep (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) B1311995
theorem B2351915 : Blo 179801 2351915 := bstep (se 1 (by rfl) ⟨1763936, by rfl⟩ : syracuseStep 2351915 = 3527873) B3527873
theorem B1172627 : Blo 179801 1172627 := bstep (se 1 (by rfl) ⟨879470, by rfl⟩ : syracuseStep 1172627 = 1758941) B1758941
theorem B615707 : Blo 179801 615707 := bstep (se 1 (by rfl) ⟨461780, by rfl⟩ : syracuseStep 615707 = 923561) B923561
theorem B8447651 : Blo 179801 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B2484125 : Blo 179801 2484125 := bstep (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) B931547
theorem B650105 : Blo 179801 650105 := bstep (se 2 (by rfl) ⟨243789, by rfl⟩ : syracuseStep 650105 = 487579) B487579
theorem B1043563 : Blo 179801 1043563 := bstep (se 1 (by rfl) ⟨782672, by rfl⟩ : syracuseStep 1043563 = 1565345) B1565345
theorem B912545 : Blo 179801 912545 := bstep (se 2 (by rfl) ⟨342204, by rfl⟩ : syracuseStep 912545 = 684409) B684409
theorem B683423 : Blo 179801 683423 := bstep (se 1 (by rfl) ⟨512567, by rfl⟩ : syracuseStep 683423 = 1025135) B1025135
theorem B618191 : Blo 179801 618191 := bstep (se 1 (by rfl) ⟨463643, by rfl⟩ : syracuseStep 618191 = 927287) B927287
theorem B9892043 : Blo 179801 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B651559 : Blo 179801 651559 := bstep (se 1 (by rfl) ⟨488669, by rfl⟩ : syracuseStep 651559 = 977339) B977339
theorem B8057249 : Blo 179801 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B586493 : Blo 179801 586493 := bstep (se 3 (by rfl) ⟨109967, by rfl⟩ : syracuseStep 586493 = 219935) B219935
theorem B554473 : Blo 179801 554473 := bstep (se 2 (by rfl) ⟨207927, by rfl⟩ : syracuseStep 554473 = 415855) B415855
theorem B522227 : Blo 179801 522227 := bstep (se 1 (by rfl) ⟨391670, by rfl⟩ : syracuseStep 522227 = 783341) B783341
theorem B522409 : Blo 179801 522409 := bstep (se 2 (by rfl) ⟨195903, by rfl⟩ : syracuseStep 522409 = 391807) B391807
theorem B195583 : Blo 179801 195583 := bstep (se 1 (by rfl) ⟨146687, by rfl⟩ : syracuseStep 195583 = 293375) B293375
theorem B2325671 : Blo 179801 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B491179 : Blo 179801 491179 := bstep (se 1 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 491179 = 736769) B736769
theorem B1310903 : Blo 179801 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B491935 : Blo 179801 491935 := bstep (se 1 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 491935 = 737903) B737903
theorem B10159775 : Blo 179801 10159775 := bstep (se 1 (by rfl) ⟨7619831, by rfl⟩ : syracuseStep 10159775 = 15239663) B15239663
theorem B1478047 : Blo 179801 1478047 := bstep (se 1 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 1478047 = 2217071) B2217071
theorem B108138401 : Blo 179801 108138401 := bstep (se 2 (by rfl) ⟨40551900, by rfl⟩ : syracuseStep 108138401 = 81103801) B81103801
theorem B364751 : Blo 179801 364751 := bstep (se 1 (by rfl) ⟨273563, by rfl⟩ : syracuseStep 364751 = 547127) B547127
theorem B1315055 : Blo 179801 1315055 := bstep (se 1 (by rfl) ⟨986291, by rfl⟩ : syracuseStep 1315055 = 1972583) B1972583
theorem B660743 : Blo 179801 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B2332435 : Blo 179801 2332435 := bstep (se 1 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 2332435 = 3498653) B3498653
theorem B202747 : Blo 179801 202747 := bstep (se 1 (by rfl) ⟨152060, by rfl⟩ : syracuseStep 202747 = 304121) B304121
theorem B203071 : Blo 179801 203071 := bstep (se 1 (by rfl) ⟨152303, by rfl⟩ : syracuseStep 203071 = 304607) B304607
theorem B596575 : Blo 179801 596575 := bstep (se 1 (by rfl) ⟨447431, by rfl⟩ : syracuseStep 596575 = 894863) B894863
theorem B662143 : Blo 179801 662143 := bstep (se 1 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 662143 = 993215) B993215
theorem B433403 : Blo 179801 433403 := bstep (se 1 (by rfl) ⟨325052, by rfl⟩ : syracuseStep 433403 = 650105) B650105
theorem B269759 : Blo 179801 269759 := bstep (se 1 (by rfl) ⟨202319, by rfl⟩ : syracuseStep 269759 = 404639) B404639
theorem B6594695 : Blo 179801 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B270527 : Blo 179801 270527 := bstep (se 1 (by rfl) ⟨202895, by rfl⟩ : syracuseStep 270527 = 405791) B405791
theorem B696545 : Blo 179801 696545 := bstep (se 2 (by rfl) ⟨261204, by rfl⟩ : syracuseStep 696545 = 522409) B522409
theorem B271391 : Blo 179801 271391 := bstep (se 1 (by rfl) ⟨203543, by rfl⟩ : syracuseStep 271391 = 407087) B407087
theorem B2631143 : Blo 179801 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B1550447 : Blo 179801 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B272495 : Blo 179801 272495 := bstep (se 1 (by rfl) ⟨204371, by rfl⟩ : syracuseStep 272495 = 408743) B408743
theorem B5646793 : Blo 179801 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B305977 : Blo 179801 305977 := bstep (se 2 (by rfl) ⟨114741, by rfl⟩ : syracuseStep 305977 = 229483) B229483
theorem B2076191 : Blo 179801 2076191 := bstep (se 1 (by rfl) ⟨1557143, by rfl⟩ : syracuseStep 2076191 = 3114287) B3114287
theorem B274127 : Blo 179801 274127 := bstep (se 1 (by rfl) ⟨205595, by rfl⟩ : syracuseStep 274127 = 411191) B411191
theorem B307435 : Blo 179801 307435 := bstep (se 1 (by rfl) ⟨230576, by rfl⟩ : syracuseStep 307435 = 461153) B461153
theorem B274985 : Blo 179801 274985 := bstep (se 2 (by rfl) ⟨103119, by rfl⟩ : syracuseStep 274985 = 206239) B206239
theorem B275327 : Blo 179801 275327 := bstep (se 1 (by rfl) ⟨206495, by rfl⟩ : syracuseStep 275327 = 412991) B412991
theorem B406655 : Blo 179801 406655 := bstep (se 1 (by rfl) ⟨304991, by rfl⟩ : syracuseStep 406655 = 609983) B609983
theorem B407215 : Blo 179801 407215 := bstep (se 1 (by rfl) ⟨305411, by rfl⟩ : syracuseStep 407215 = 610823) B610823
theorem B407519 : Blo 179801 407519 := bstep (se 1 (by rfl) ⟨305639, by rfl⟩ : syracuseStep 407519 = 611279) B611279
theorem B3291367 : Blo 179801 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B1030967 : Blo 179801 1030967 := bstep (se 1 (by rfl) ⟨773225, by rfl⟩ : syracuseStep 1030967 = 1546451) B1546451
theorem B1391417 : Blo 179801 1391417 := bstep (se 2 (by rfl) ⟨521781, by rfl⟩ : syracuseStep 1391417 = 1043563) B1043563
theorem B179871 : Blo 179801 179871 := bstep (se 1 (by rfl) ⟨134903, by rfl⟩ : syracuseStep 179871 = 269807) B269807
theorem B179903 : Blo 179801 179903 := bstep (se 1 (by rfl) ⟨134927, by rfl⟩ : syracuseStep 179903 = 269855) B269855
theorem B180031 : Blo 179801 180031 := bstep (se 1 (by rfl) ⟨135023, by rfl⟩ : syracuseStep 180031 = 270047) B270047
theorem B180071 : Blo 179801 180071 := bstep (se 1 (by rfl) ⟨135053, by rfl⟩ : syracuseStep 180071 = 270107) B270107
theorem B180095 : Blo 179801 180095 := bstep (se 1 (by rfl) ⟨135071, by rfl⟩ : syracuseStep 180095 = 270143) B270143
theorem B180271 : Blo 179801 180271 := bstep (se 1 (by rfl) ⟨135203, by rfl⟩ : syracuseStep 180271 = 270407) B270407
theorem B868745 : Blo 179801 868745 := bstep (se 2 (by rfl) ⟨325779, by rfl⟩ : syracuseStep 868745 = 651559) B651559
theorem B5849495 : Blo 179801 5849495 := bstep (se 1 (by rfl) ⟨4387121, by rfl⟩ : syracuseStep 5849495 = 8774243) B8774243
theorem B180891 : Blo 179801 180891 := bstep (se 1 (by rfl) ⟨135668, by rfl⟩ : syracuseStep 180891 = 271337) B271337
theorem B180991 : Blo 179801 180991 := bstep (se 1 (by rfl) ⟨135743, by rfl⟩ : syracuseStep 180991 = 271487) B271487
theorem B181095 : Blo 179801 181095 := bstep (se 1 (by rfl) ⟨135821, by rfl⟩ : syracuseStep 181095 = 271643) B271643
theorem B410471 : Blo 179801 410471 := bstep (se 1 (by rfl) ⟨307853, by rfl⟩ : syracuseStep 410471 = 615707) B615707
theorem B181183 : Blo 179801 181183 := bstep (se 1 (by rfl) ⟨135887, by rfl⟩ : syracuseStep 181183 = 271775) B271775
theorem B181231 : Blo 179801 181231 := bstep (se 1 (by rfl) ⟨135923, by rfl⟩ : syracuseStep 181231 = 271847) B271847
theorem B181275 : Blo 179801 181275 := bstep (se 1 (by rfl) ⟨135956, by rfl⟩ : syracuseStep 181275 = 271913) B271913
theorem B181503 : Blo 179801 181503 := bstep (se 1 (by rfl) ⟨136127, by rfl⟩ : syracuseStep 181503 = 272255) B272255
theorem B1656083 : Blo 179801 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B739297 : Blo 179801 739297 := bstep (se 2 (by rfl) ⟨277236, by rfl⟩ : syracuseStep 739297 = 554473) B554473
theorem B182375 : Blo 179801 182375 := bstep (se 1 (by rfl) ⟨136781, by rfl⟩ : syracuseStep 182375 = 273563) B273563
theorem B608363 : Blo 179801 608363 := bstep (se 1 (by rfl) ⟨456272, by rfl⟩ : syracuseStep 608363 = 912545) B912545
theorem B182631 : Blo 179801 182631 := bstep (se 1 (by rfl) ⟨136973, by rfl⟩ : syracuseStep 182631 = 273947) B273947
theorem B412127 : Blo 179801 412127 := bstep (se 1 (by rfl) ⟨309095, by rfl⟩ : syracuseStep 412127 = 618191) B618191
theorem B1035089 : Blo 179801 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B773003 : Blo 179801 773003 := bstep (se 1 (by rfl) ⟨579752, by rfl⟩ : syracuseStep 773003 = 1159505) B1159505
theorem B183327 : Blo 179801 183327 := bstep (se 1 (by rfl) ⟨137495, by rfl⟩ : syracuseStep 183327 = 274991) B274991
theorem B183547 : Blo 179801 183547 := bstep (se 1 (by rfl) ⟨137660, by rfl⟩ : syracuseStep 183547 = 275321) B275321
theorem B183743 : Blo 179801 183743 := bstep (se 1 (by rfl) ⟨137807, by rfl⟩ : syracuseStep 183743 = 275615) B275615
theorem B348151 : Blo 179801 348151 := bstep (se 1 (by rfl) ⟨261113, by rfl⟩ : syracuseStep 348151 = 522227) B522227
theorem B708839 : Blo 179801 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B1036799 : Blo 179801 1036799 := bstep (se 1 (by rfl) ⟨777599, by rfl⟩ : syracuseStep 1036799 = 1555199) B1555199
theorem B611819 : Blo 179801 611819 := bstep (se 1 (by rfl) ⟨458864, by rfl⟩ : syracuseStep 611819 = 917729) B917729
theorem B777275 : Blo 179801 777275 := bstep (se 1 (by rfl) ⟨582956, by rfl⟩ : syracuseStep 777275 = 1165913) B1165913
theorem B386203 : Blo 179801 386203 := bstep (se 1 (by rfl) ⟨289652, by rfl⟩ : syracuseStep 386203 = 579305) B579305
theorem B26306329 : Blo 179801 26306329 := bstep (se 2 (by rfl) ⟨9864873, by rfl⟩ : syracuseStep 26306329 = 19729747) B19729747
theorem B616895 : Blo 179801 616895 := bstep (se 1 (by rfl) ⟨462671, by rfl⟩ : syracuseStep 616895 = 925343) B925343
theorem B2550635 : Blo 179801 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B617597 : Blo 179801 617597 := bstep (se 3 (by rfl) ⟨115799, by rfl⟩ : syracuseStep 617597 = 231599) B231599
theorem B1567943 : Blo 179801 1567943 := bstep (se 1 (by rfl) ⟨1175957, by rfl⟩ : syracuseStep 1567943 = 2351915) B2351915
theorem B781751 : Blo 179801 781751 := bstep (se 1 (by rfl) ⟨586313, by rfl⟩ : syracuseStep 781751 = 1172627) B1172627
theorem B6254009 : Blo 179801 6254009 := bstep (se 2 (by rfl) ⟨2345253, by rfl⟩ : syracuseStep 6254009 = 4690507) B4690507
theorem B5631767 : Blo 179801 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B455615 : Blo 179801 455615 := bstep (se 1 (by rfl) ⟨341711, by rfl⟩ : syracuseStep 455615 = 683423) B683423
theorem B325225 : Blo 179801 325225 := bstep (se 2 (by rfl) ⟨121959, by rfl⟩ : syracuseStep 325225 = 243919) B243919
theorem B5371499 : Blo 179801 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B390995 : Blo 179801 390995 := bstep (se 1 (by rfl) ⟨293246, by rfl⟩ : syracuseStep 390995 = 586493) B586493
theorem B7108667 : Blo 179801 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B260777 : Blo 179801 260777 := bstep (se 2 (by rfl) ⟨97791, by rfl⟩ : syracuseStep 260777 = 195583) B195583
theorem B490607 : Blo 179801 490607 := bstep (se 1 (by rfl) ⟨367955, by rfl⟩ : syracuseStep 490607 = 735911) B735911
theorem B654905 : Blo 179801 654905 := bstep (se 2 (by rfl) ⟨245589, by rfl⟩ : syracuseStep 654905 = 491179) B491179
theorem B3899663 : Blo 179801 3899663 := bstep (se 1 (by rfl) ⟨2924747, by rfl⟩ : syracuseStep 3899663 = 5849495) B5849495
theorem B655913 : Blo 179801 655913 := bstep (se 2 (by rfl) ⟨245967, by rfl⟩ : syracuseStep 655913 = 491935) B491935
theorem B690059 : Blo 179801 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B72092267 : Blo 179801 72092267 := bstep (se 1 (by rfl) ⟨54069200, by rfl⟩ : syracuseStep 72092267 = 108138401) B108138401
theorem B985729 : Blo 179801 985729 := bstep (se 2 (by rfl) ⟨369648, by rfl⟩ : syracuseStep 985729 = 739297) B739297
theorem B691199 : Blo 179801 691199 := bstep (se 1 (by rfl) ⟨518399, by rfl⟩ : syracuseStep 691199 = 1036799) B1036799
theorem B1970729 : Blo 179801 1970729 := bstep (se 2 (by rfl) ⟨739023, by rfl⟩ : syracuseStep 1970729 = 1478047) B1478047
theorem B464201 : Blo 179801 464201 := bstep (se 2 (by rfl) ⟨174075, by rfl⟩ : syracuseStep 464201 = 348151) B348151
theorem B4396463 : Blo 179801 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B464363 : Blo 179801 464363 := bstep (se 1 (by rfl) ⟨348272, by rfl⟩ : syracuseStep 464363 = 696545) B696545
theorem B695405 : Blo 179801 695405 := bstep (se 3 (by rfl) ⟨130388, by rfl⟩ : syracuseStep 695405 = 260777) B260777
theorem B4169339 : Blo 179801 4169339 := bstep (se 1 (by rfl) ⟨3127004, by rfl⟩ : syracuseStep 4169339 = 6254009) B6254009
theorem B1384127 : Blo 179801 1384127 := bstep (se 1 (by rfl) ⟨1038095, by rfl⟩ : syracuseStep 1384127 = 2076191) B2076191
theorem B270329 : Blo 179801 270329 := bstep (se 2 (by rfl) ⟨101373, by rfl⟩ : syracuseStep 270329 = 202747) B202747
theorem B270761 : Blo 179801 270761 := bstep (se 2 (by rfl) ⟨101535, by rfl⟩ : syracuseStep 270761 = 203071) B203071
theorem B303743 : Blo 179801 303743 := bstep (se 1 (by rfl) ⟨227807, by rfl⟩ : syracuseStep 303743 = 455615) B455615
theorem B271103 : Blo 179801 271103 := bstep (se 1 (by rfl) ⟨203327, by rfl⟩ : syracuseStep 271103 = 406655) B406655
theorem B795433 : Blo 179801 795433 := bstep (se 2 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 795433 = 596575) B596575
theorem B3580999 : Blo 179801 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B271679 : Blo 179801 271679 := bstep (se 1 (by rfl) ⟨203759, by rfl⟩ : syracuseStep 271679 = 407519) B407519
theorem B927611 : Blo 179801 927611 := bstep (se 1 (by rfl) ⟨695708, by rfl⟩ : syracuseStep 927611 = 1391417) B1391417
theorem B436603 : Blo 179801 436603 := bstep (se 1 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 436603 = 654905) B654905
theorem B273647 : Blo 179801 273647 := bstep (se 1 (by rfl) ⟨205235, by rfl⟩ : syracuseStep 273647 = 410471) B410471
theorem B405575 : Blo 179801 405575 := bstep (se 1 (by rfl) ⟨304181, by rfl⟩ : syracuseStep 405575 = 608363) B608363
theorem B274751 : Blo 179801 274751 := bstep (se 1 (by rfl) ⟨206063, by rfl⟩ : syracuseStep 274751 = 412127) B412127
theorem B35075105 : Blo 179801 35075105 := bstep (se 2 (by rfl) ⟨13153164, by rfl⟩ : syracuseStep 35075105 = 26306329) B26306329
theorem B243167 : Blo 179801 243167 := bstep (se 1 (by rfl) ⟨182375, by rfl⟩ : syracuseStep 243167 = 364751) B364751
theorem B472559 : Blo 179801 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B440495 : Blo 179801 440495 := bstep (se 1 (by rfl) ⟨330371, by rfl⟩ : syracuseStep 440495 = 660743) B660743
theorem B407879 : Blo 179801 407879 := bstep (se 1 (by rfl) ⟨305909, by rfl⟩ : syracuseStep 407879 = 611819) B611819
theorem B407969 : Blo 179801 407969 := bstep (se 2 (by rfl) ⟨152988, by rfl⟩ : syracuseStep 407969 = 305977) B305977
theorem B179839 : Blo 179801 179839 := bstep (se 1 (by rfl) ⟨134879, by rfl⟩ : syracuseStep 179839 = 269759) B269759
theorem B180351 : Blo 179801 180351 := bstep (se 1 (by rfl) ⟨135263, by rfl⟩ : syracuseStep 180351 = 270527) B270527
theorem B409913 : Blo 179801 409913 := bstep (se 2 (by rfl) ⟨153717, by rfl⟩ : syracuseStep 409913 = 307435) B307435
theorem B180927 : Blo 179801 180927 := bstep (se 1 (by rfl) ⟨135695, by rfl⟩ : syracuseStep 180927 = 271391) B271391
theorem B1754095 : Blo 179801 1754095 := bstep (se 1 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 1754095 = 2631143) B2631143
theorem B1033631 : Blo 179801 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B181663 : Blo 179801 181663 := bstep (se 1 (by rfl) ⟨136247, by rfl⟩ : syracuseStep 181663 = 272495) B272495
theorem B411263 : Blo 179801 411263 := bstep (se 1 (by rfl) ⟨308447, by rfl⟩ : syracuseStep 411263 = 616895) B616895
theorem B411731 : Blo 179801 411731 := bstep (se 1 (by rfl) ⟨308798, by rfl⟩ : syracuseStep 411731 = 617597) B617597
theorem B542953 : Blo 179801 542953 := bstep (se 2 (by rfl) ⟨203607, by rfl⟩ : syracuseStep 542953 = 407215) B407215
theorem B182751 : Blo 179801 182751 := bstep (se 1 (by rfl) ⟨137063, by rfl⟩ : syracuseStep 182751 = 274127) B274127
theorem B3754511 : Blo 179801 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B183323 : Blo 179801 183323 := bstep (se 1 (by rfl) ⟨137492, by rfl⟩ : syracuseStep 183323 = 274985) B274985
theorem B183551 : Blo 179801 183551 := bstep (se 1 (by rfl) ⟨137663, by rfl⟩ : syracuseStep 183551 = 275327) B275327
theorem B4739111 : Blo 179801 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B873935 : Blo 179801 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B579163 : Blo 179801 579163 := bstep (se 1 (by rfl) ⟨434372, by rfl⟩ : syracuseStep 579163 = 868745) B868745
theorem B6773183 : Blo 179801 6773183 := bstep (se 1 (by rfl) ⟨5079887, by rfl⟩ : syracuseStep 6773183 = 10159775) B10159775
theorem B514937 : Blo 179801 514937 := bstep (se 2 (by rfl) ⟨193101, by rfl⟩ : syracuseStep 514937 = 386203) B386203
theorem B515335 : Blo 179801 515335 := bstep (se 1 (by rfl) ⟨386501, by rfl⟩ : syracuseStep 515335 = 773003) B773003
theorem B876703 : Blo 179801 876703 := bstep (se 1 (by rfl) ⟨657527, by rfl⟩ : syracuseStep 876703 = 1315055) B1315055
theorem B7529057 : Blo 179801 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B4416221 : Blo 179801 4416221 := bstep (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) B1656083
theorem B518183 : Blo 179801 518183 := bstep (se 1 (by rfl) ⟨388637, by rfl⟩ : syracuseStep 518183 = 777275) B777275
theorem B288935 : Blo 179801 288935 := bstep (se 1 (by rfl) ⟨216701, by rfl⟩ : syracuseStep 288935 = 433403) B433403
theorem B1700423 : Blo 179801 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B1045295 : Blo 179801 1045295 := bstep (se 1 (by rfl) ⟨783971, by rfl⟩ : syracuseStep 1045295 = 1567943) B1567943
theorem B521167 : Blo 179801 521167 := bstep (se 1 (by rfl) ⟨390875, by rfl⟩ : syracuseStep 521167 = 781751) B781751
theorem B3109913 : Blo 179801 3109913 := bstep (se 2 (by rfl) ⟨1166217, by rfl⟩ : syracuseStep 3109913 = 2332435) B2332435
theorem B4388489 : Blo 179801 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B1734533 : Blo 179801 1734533 := bstep (se 4 (by rfl) ⟨162612, by rfl⟩ : syracuseStep 1734533 = 325225) B325225
theorem B882857 : Blo 179801 882857 := bstep (se 2 (by rfl) ⟨331071, by rfl⟩ : syracuseStep 882857 = 662143) B662143
theorem B260663 : Blo 179801 260663 := bstep (se 1 (by rfl) ⟨195497, by rfl⟩ : syracuseStep 260663 = 390995) B390995
theorem B687311 : Blo 179801 687311 := bstep (se 1 (by rfl) ⟨515483, by rfl⟩ : syracuseStep 687311 = 1030967) B1030967
theorem B327071 : Blo 179801 327071 := bstep (se 1 (by rfl) ⟨245303, by rfl⟩ : syracuseStep 327071 = 490607) B490607
theorem B689087 : Blo 179801 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B460039 : Blo 179801 460039 := bstep (se 1 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 460039 = 690059) B690059
theorem B460799 : Blo 179801 460799 := bstep (se 1 (by rfl) ⟨345599, by rfl⟩ : syracuseStep 460799 = 691199) B691199
theorem B1313819 : Blo 179801 1313819 := bstep (se 1 (by rfl) ⟨985364, by rfl⟩ : syracuseStep 1313819 = 1970729) B1970729
theorem B1314305 : Blo 179801 1314305 := bstep (se 2 (by rfl) ⟨492864, by rfl⟩ : syracuseStep 1314305 = 985729) B985729
theorem B463603 : Blo 179801 463603 := bstep (se 1 (by rfl) ⟨347702, by rfl⟩ : syracuseStep 463603 = 695405) B695405
theorem B2593781 : Blo 179801 2593781 := bstep (se 5 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 2593781 = 243167) B243167
theorem B922751 : Blo 179801 922751 := bstep (se 1 (by rfl) ⟨692063, by rfl⟩ : syracuseStep 922751 = 1384127) B1384127
theorem B5019371 : Blo 179801 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B202495 : Blo 179801 202495 := bstep (se 1 (by rfl) ⟨151871, by rfl⟩ : syracuseStep 202495 = 303743) B303743
theorem B694889 : Blo 179801 694889 := bstep (se 2 (by rfl) ⟨260583, by rfl⟩ : syracuseStep 694889 = 521167) B521167
theorem B695101 : Blo 179801 695101 := bstep (se 3 (by rfl) ⟨130331, by rfl⟩ : syracuseStep 695101 = 260663) B260663
theorem B270383 : Blo 179801 270383 := bstep (se 1 (by rfl) ⟨202787, by rfl⟩ : syracuseStep 270383 = 405575) B405575
theorem B696863 : Blo 179801 696863 := bstep (se 1 (by rfl) ⟨522647, by rfl⟩ : syracuseStep 696863 = 1045295) B1045295
theorem B2073275 : Blo 179801 2073275 := bstep (se 1 (by rfl) ⟨1554956, by rfl⟩ : syracuseStep 2073275 = 3109913) B3109913
theorem B2925659 : Blo 179801 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B1156355 : Blo 179801 1156355 := bstep (se 1 (by rfl) ⟨867266, by rfl⟩ : syracuseStep 1156355 = 1734533) B1734533
theorem B271919 : Blo 179801 271919 := bstep (se 1 (by rfl) ⟨203939, by rfl⟩ : syracuseStep 271919 = 407879) B407879
theorem B271979 : Blo 179801 271979 := bstep (se 1 (by rfl) ⟨203984, by rfl⟩ : syracuseStep 271979 = 407969) B407969
theorem B2599775 : Blo 179801 2599775 := bstep (se 1 (by rfl) ⟨1949831, by rfl⟩ : syracuseStep 2599775 = 3899663) B3899663
theorem B273275 : Blo 179801 273275 := bstep (se 1 (by rfl) ⟨204956, by rfl⟩ : syracuseStep 273275 = 409913) B409913
theorem B437275 : Blo 179801 437275 := bstep (se 1 (by rfl) ⟨327956, by rfl⟩ : syracuseStep 437275 = 655913) B655913
theorem B1060577 : Blo 179801 1060577 := bstep (se 2 (by rfl) ⟨397716, by rfl⟩ : syracuseStep 1060577 = 795433) B795433
theorem B274175 : Blo 179801 274175 := bstep (se 1 (by rfl) ⟨205631, by rfl⟩ : syracuseStep 274175 = 411263) B411263
theorem B2895749 : Blo 179801 2895749 := bstep (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) B542953
theorem B2338793 : Blo 179801 2338793 := bstep (se 2 (by rfl) ⟨877047, by rfl⟩ : syracuseStep 2338793 = 1754095) B1754095
theorem B274487 : Blo 179801 274487 := bstep (se 1 (by rfl) ⟨205865, by rfl⟩ : syracuseStep 274487 = 411731) B411731
theorem B2503007 : Blo 179801 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B3159407 : Blo 179801 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B309467 : Blo 179801 309467 := bstep (se 1 (by rfl) ⟨232100, by rfl⟩ : syracuseStep 309467 = 464201) B464201
theorem B2930975 : Blo 179801 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B309575 : Blo 179801 309575 := bstep (se 1 (by rfl) ⟨232181, by rfl⟩ : syracuseStep 309575 = 464363) B464363
theorem B1260157 : Blo 179801 1260157 := bstep (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) B472559
theorem B343291 : Blo 179801 343291 := bstep (se 1 (by rfl) ⟨257468, by rfl⟩ : syracuseStep 343291 = 514937) B514937
theorem B180219 : Blo 179801 180219 := bstep (se 1 (by rfl) ⟨135164, by rfl⟩ : syracuseStep 180219 = 270329) B270329
theorem B180507 : Blo 179801 180507 := bstep (se 1 (by rfl) ⟨135380, by rfl⟩ : syracuseStep 180507 = 270761) B270761
theorem B180735 : Blo 179801 180735 := bstep (se 1 (by rfl) ⟨135551, by rfl⟩ : syracuseStep 180735 = 271103) B271103
theorem B181119 : Blo 179801 181119 := bstep (se 1 (by rfl) ⟨135839, by rfl⟩ : syracuseStep 181119 = 271679) B271679
theorem B345455 : Blo 179801 345455 := bstep (se 1 (by rfl) ⟨259091, by rfl⟩ : syracuseStep 345455 = 518183) B518183
theorem B772217 : Blo 179801 772217 := bstep (se 2 (by rfl) ⟨289581, by rfl⟩ : syracuseStep 772217 = 579163) B579163
theorem B182431 : Blo 179801 182431 := bstep (se 1 (by rfl) ⟨136823, by rfl⟩ : syracuseStep 182431 = 273647) B273647
theorem B183167 : Blo 179801 183167 := bstep (se 1 (by rfl) ⟨137375, by rfl⟩ : syracuseStep 183167 = 274751) B274751
theorem B1133615 : Blo 179801 1133615 := bstep (se 1 (by rfl) ⟨850211, by rfl⟩ : syracuseStep 1133615 = 1700423) B1700423
theorem B23383403 : Blo 179801 23383403 := bstep (se 1 (by rfl) ⟨17537552, by rfl⟩ : syracuseStep 23383403 = 35075105) B35075105
theorem B218047 : Blo 179801 218047 := bstep (se 1 (by rfl) ⟨163535, by rfl⟩ : syracuseStep 218047 = 327071) B327071
theorem B1168937 : Blo 179801 1168937 := bstep (se 2 (by rfl) ⟨438351, by rfl⟩ : syracuseStep 1168937 = 876703) B876703
theorem B48061511 : Blo 179801 48061511 := bstep (se 1 (by rfl) ⟨36046133, by rfl⟩ : syracuseStep 48061511 = 72092267) B72092267
theorem B582137 : Blo 179801 582137 := bstep (se 2 (by rfl) ⟨218301, by rfl⟩ : syracuseStep 582137 = 436603) B436603
theorem B582623 : Blo 179801 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B4515455 : Blo 179801 4515455 := bstep (se 1 (by rfl) ⟨3386591, by rfl⟩ : syracuseStep 4515455 = 6773183) B6773183
theorem B2779559 : Blo 179801 2779559 := bstep (se 1 (by rfl) ⟨2084669, by rfl⟩ : syracuseStep 2779559 = 4169339) B4169339
theorem B19098661 : Blo 179801 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B2354285 : Blo 179801 2354285 := bstep (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) B882857
theorem B2944147 : Blo 179801 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B618407 : Blo 179801 618407 := bstep (se 1 (by rfl) ⟨463805, by rfl⟩ : syracuseStep 618407 = 927611) B927611
theorem B192623 : Blo 179801 192623 := bstep (se 1 (by rfl) ⟨144467, by rfl⟩ : syracuseStep 192623 = 288935) B288935
theorem B293663 : Blo 179801 293663 := bstep (se 1 (by rfl) ⟨220247, by rfl⟩ : syracuseStep 293663 = 440495) B440495
theorem B687113 : Blo 179801 687113 := bstep (se 2 (by rfl) ⟨257667, by rfl⟩ : syracuseStep 687113 = 515335) B515335
theorem B458207 : Blo 179801 458207 := bstep (se 1 (by rfl) ⟨343655, by rfl⟩ : syracuseStep 458207 = 687311) B687311
theorem B459391 : Blo 179801 459391 := bstep (se 1 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 459391 = 689087) B689087
theorem B230303 : Blo 179801 230303 := bstep (se 1 (by rfl) ⟨172727, by rfl⟩ : syracuseStep 230303 = 345455) B345455
theorem B755743 : Blo 179801 755743 := bstep (se 1 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 755743 = 1133615) B1133615
theorem B3346247 : Blo 179801 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B25464881 : Blo 179801 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B463259 : Blo 179801 463259 := bstep (se 1 (by rfl) ⟨347444, by rfl⟩ : syracuseStep 463259 = 694889) B694889
theorem B464575 : Blo 179801 464575 := bstep (se 1 (by rfl) ⟨348431, by rfl⟩ : syracuseStep 464575 = 696863) B696863
theorem B1382183 : Blo 179801 1382183 := bstep (se 1 (by rfl) ⟨1036637, by rfl⟩ : syracuseStep 1382183 = 2073275) B2073275
theorem B269993 : Blo 179801 269993 := bstep (se 2 (by rfl) ⟨101247, by rfl⟩ : syracuseStep 269993 = 202495) B202495
theorem B1680209 : Blo 179801 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B2106271 : Blo 179801 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B926801 : Blo 179801 926801 := bstep (se 2 (by rfl) ⟨347550, by rfl⟩ : syracuseStep 926801 = 695101) B695101
theorem B206311 : Blo 179801 206311 := bstep (se 1 (by rfl) ⟨154733, by rfl⟩ : syracuseStep 206311 = 309467) B309467
theorem B206383 : Blo 179801 206383 := bstep (se 1 (by rfl) ⟨154787, by rfl⟩ : syracuseStep 206383 = 309575) B309575
theorem B305471 : Blo 179801 305471 := bstep (se 1 (by rfl) ⟨229103, by rfl⟩ : syracuseStep 305471 = 458207) B458207
theorem B307199 : Blo 179801 307199 := bstep (se 1 (by rfl) ⟨230399, by rfl⟩ : syracuseStep 307199 = 460799) B460799
theorem B180255 : Blo 179801 180255 := bstep (se 1 (by rfl) ⟨135191, by rfl⟩ : syracuseStep 180255 = 270383) B270383
theorem B1950439 : Blo 179801 1950439 := bstep (se 1 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 1950439 = 2925659) B2925659
theorem B770903 : Blo 179801 770903 := bstep (se 1 (by rfl) ⟨578177, by rfl⟩ : syracuseStep 770903 = 1156355) B1156355
theorem B181279 : Blo 179801 181279 := bstep (se 1 (by rfl) ⟨135959, by rfl⟩ : syracuseStep 181279 = 271919) B271919
theorem B181319 : Blo 179801 181319 := bstep (se 1 (by rfl) ⟨135989, by rfl⟩ : syracuseStep 181319 = 271979) B271979
theorem B1853039 : Blo 179801 1853039 := bstep (se 1 (by rfl) ⟨1389779, by rfl⟩ : syracuseStep 1853039 = 2779559) B2779559
theorem B182183 : Blo 179801 182183 := bstep (se 1 (by rfl) ⟨136637, by rfl⟩ : syracuseStep 182183 = 273275) B273275
theorem B707051 : Blo 179801 707051 := bstep (se 1 (by rfl) ⟨530288, by rfl⟩ : syracuseStep 707051 = 1060577) B1060577
theorem B182783 : Blo 179801 182783 := bstep (se 1 (by rfl) ⟨137087, by rfl⟩ : syracuseStep 182783 = 274175) B274175
theorem B412271 : Blo 179801 412271 := bstep (se 1 (by rfl) ⟨309203, by rfl⟩ : syracuseStep 412271 = 618407) B618407
theorem B1559195 : Blo 179801 1559195 := bstep (se 1 (by rfl) ⟨1169396, by rfl⟩ : syracuseStep 1559195 = 2338793) B2338793
theorem B182991 : Blo 179801 182991 := bstep (se 1 (by rfl) ⟨137243, by rfl⟩ : syracuseStep 182991 = 274487) B274487
theorem B6278093 : Blo 179801 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B1953983 : Blo 179801 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B513661 : Blo 179801 513661 := bstep (se 3 (by rfl) ⟨96311, by rfl⟩ : syracuseStep 513661 = 192623) B192623
theorem B514811 : Blo 179801 514811 := bstep (se 1 (by rfl) ⟨386108, by rfl⟩ : syracuseStep 514811 = 772217) B772217
theorem B613385 : Blo 179801 613385 := bstep (se 2 (by rfl) ⟨230019, by rfl⟩ : syracuseStep 613385 = 460039) B460039
theorem B875879 : Blo 179801 875879 := bstep (se 1 (by rfl) ⟨656909, by rfl⟩ : syracuseStep 875879 = 1313819) B1313819
theorem B15588935 : Blo 179801 15588935 := bstep (se 1 (by rfl) ⟨11691701, by rfl⟩ : syracuseStep 15588935 = 23383403) B23383403
theorem B876203 : Blo 179801 876203 := bstep (se 1 (by rfl) ⟨657152, by rfl⟩ : syracuseStep 876203 = 1314305) B1314305
theorem B1729187 : Blo 179801 1729187 := bstep (se 1 (by rfl) ⟨1296890, by rfl⟩ : syracuseStep 1729187 = 2593781) B2593781
theorem B615167 : Blo 179801 615167 := bstep (se 1 (by rfl) ⟨461375, by rfl⟩ : syracuseStep 615167 = 922751) B922751
theorem B779291 : Blo 179801 779291 := bstep (se 1 (by rfl) ⟨584468, by rfl⟩ : syracuseStep 779291 = 1168937) B1168937
theorem B583033 : Blo 179801 583033 := bstep (se 2 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 583033 = 437275) B437275
theorem B3925529 : Blo 179801 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B32041007 : Blo 179801 32041007 := bstep (se 1 (by rfl) ⟨24030755, by rfl⟩ : syracuseStep 32041007 = 48061511) B48061511
theorem B388091 : Blo 179801 388091 := bstep (se 1 (by rfl) ⟨291068, by rfl⟩ : syracuseStep 388091 = 582137) B582137
theorem B388415 : Blo 179801 388415 := bstep (se 1 (by rfl) ⟨291311, by rfl⟩ : syracuseStep 388415 = 582623) B582623
theorem B618137 : Blo 179801 618137 := bstep (se 2 (by rfl) ⟨231801, by rfl⟩ : syracuseStep 618137 = 463603) B463603
theorem B3010303 : Blo 179801 3010303 := bstep (se 1 (by rfl) ⟨2257727, by rfl⟩ : syracuseStep 3010303 = 4515455) B4515455
theorem B290729 : Blo 179801 290729 := bstep (se 2 (by rfl) ⟨109023, by rfl⟩ : syracuseStep 290729 = 218047) B218047
theorem B1733183 : Blo 179801 1733183 := bstep (se 1 (by rfl) ⟨1299887, by rfl⟩ : syracuseStep 1733183 = 2599775) B2599775
theorem B783101 : Blo 179801 783101 := bstep (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) B293663
theorem B1930499 : Blo 179801 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B1668671 : Blo 179801 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B457721 : Blo 179801 457721 := bstep (se 2 (by rfl) ⟨171645, by rfl⟩ : syracuseStep 457721 = 343291) B343291
theorem B458075 : Blo 179801 458075 := bstep (se 1 (by rfl) ⟨343556, by rfl⟩ : syracuseStep 458075 = 687113) B687113
theorem B2230831 : Blo 179801 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B16976587 : Blo 179801 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B921455 : Blo 179801 921455 := bstep (se 1 (by rfl) ⟨691091, by rfl⟩ : syracuseStep 921455 = 1382183) B1382183
theorem B10392623 : Blo 179801 10392623 := bstep (se 1 (by rfl) ⟨7794467, by rfl⟩ : syracuseStep 10392623 = 15588935) B15588935
theorem B1152791 : Blo 179801 1152791 := bstep (se 1 (by rfl) ⟨864593, by rfl⟩ : syracuseStep 1152791 = 1729187) B1729187
theorem B1120139 : Blo 179801 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B203647 : Blo 179801 203647 := bstep (se 1 (by rfl) ⟨152735, by rfl⟩ : syracuseStep 203647 = 305471) B305471
theorem B204799 : Blo 179801 204799 := bstep (se 1 (by rfl) ⟨153599, by rfl⟩ : syracuseStep 204799 = 307199) B307199
theorem B1155455 : Blo 179801 1155455 := bstep (se 1 (by rfl) ⟨866591, by rfl⟩ : syracuseStep 1155455 = 1733183) B1733183
theorem B1286999 : Blo 179801 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B305147 : Blo 179801 305147 := bstep (se 1 (by rfl) ⟨228860, by rfl⟩ : syracuseStep 305147 = 457721) B457721
theorem B305383 : Blo 179801 305383 := bstep (se 1 (by rfl) ⟨229037, by rfl⟩ : syracuseStep 305383 = 458075) B458075
theorem B2600585 : Blo 179801 2600585 := bstep (se 2 (by rfl) ⟨975219, by rfl⟩ : syracuseStep 2600585 = 1950439) B1950439
theorem B471367 : Blo 179801 471367 := bstep (se 1 (by rfl) ⟨353525, by rfl⟩ : syracuseStep 471367 = 707051) B707051
theorem B274847 : Blo 179801 274847 := bstep (se 1 (by rfl) ⟨206135, by rfl⟩ : syracuseStep 274847 = 412271) B412271
theorem B275081 : Blo 179801 275081 := bstep (se 2 (by rfl) ⟨103155, by rfl⟩ : syracuseStep 275081 = 206311) B206311
theorem B275177 : Blo 179801 275177 := bstep (se 2 (by rfl) ⟨103191, by rfl⟩ : syracuseStep 275177 = 206383) B206383
theorem B308839 : Blo 179801 308839 := bstep (se 1 (by rfl) ⟨231629, by rfl⟩ : syracuseStep 308839 = 463259) B463259
theorem B343207 : Blo 179801 343207 := bstep (se 1 (by rfl) ⟨257405, by rfl⟩ : syracuseStep 343207 = 514811) B514811
theorem B408923 : Blo 179801 408923 := bstep (se 1 (by rfl) ⟨306692, by rfl⟩ : syracuseStep 408923 = 613385) B613385
theorem B179995 : Blo 179801 179995 := bstep (se 1 (by rfl) ⟨134996, by rfl⟩ : syracuseStep 179995 = 269993) B269993
theorem B410111 : Blo 179801 410111 := bstep (se 1 (by rfl) ⟨307583, by rfl⟩ : syracuseStep 410111 = 615167) B615167
theorem B412091 : Blo 179801 412091 := bstep (se 1 (by rfl) ⟨309068, by rfl⟩ : syracuseStep 412091 = 618137) B618137
theorem B1035773 : Blo 179801 1035773 := bstep (se 3 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 1035773 = 388415) B388415
theorem B775277 : Blo 179801 775277 := bstep (se 3 (by rfl) ⟨145364, by rfl⟩ : syracuseStep 775277 = 290729) B290729
theorem B513935 : Blo 179801 513935 := bstep (se 1 (by rfl) ⟨385451, by rfl⟩ : syracuseStep 513935 = 770903) B770903
theorem B612521 : Blo 179801 612521 := bstep (se 2 (by rfl) ⟨229695, by rfl⟩ : syracuseStep 612521 = 459391) B459391
theorem B1235359 : Blo 179801 1235359 := bstep (se 1 (by rfl) ⟨926519, by rfl⟩ : syracuseStep 1235359 = 1853039) B1853039
theorem B2808361 : Blo 179801 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B1039463 : Blo 179801 1039463 := bstep (se 1 (by rfl) ⟨779597, by rfl⟩ : syracuseStep 1039463 = 1559195) B1559195
theorem B777377 : Blo 179801 777377 := bstep (se 2 (by rfl) ⟨291516, by rfl⟩ : syracuseStep 777377 = 583033) B583033
theorem B4185395 : Blo 179801 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B614141 : Blo 179801 614141 := bstep (se 3 (by rfl) ⟨115151, by rfl⟩ : syracuseStep 614141 = 230303) B230303
theorem B1007657 : Blo 179801 1007657 := bstep (se 2 (by rfl) ⟨377871, by rfl⟩ : syracuseStep 1007657 = 755743) B755743
theorem B1302655 : Blo 179801 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B583919 : Blo 179801 583919 := bstep (se 1 (by rfl) ⟨437939, by rfl⟩ : syracuseStep 583919 = 875879) B875879
theorem B584135 : Blo 179801 584135 := bstep (se 1 (by rfl) ⟨438101, by rfl⟩ : syracuseStep 584135 = 876203) B876203
theorem B519527 : Blo 179801 519527 := bstep (se 1 (by rfl) ⟨389645, by rfl⟩ : syracuseStep 519527 = 779291) B779291
theorem B617867 : Blo 179801 617867 := bstep (se 1 (by rfl) ⟨463400, by rfl⟩ : syracuseStep 617867 = 926801) B926801
theorem B2617019 : Blo 179801 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B21360671 : Blo 179801 21360671 := bstep (se 1 (by rfl) ⟨16020503, by rfl⟩ : syracuseStep 21360671 = 32041007) B32041007
theorem B258727 : Blo 179801 258727 := bstep (se 1 (by rfl) ⟨194045, by rfl⟩ : syracuseStep 258727 = 388091) B388091
theorem B684881 : Blo 179801 684881 := bstep (se 2 (by rfl) ⟨256830, by rfl⟩ : syracuseStep 684881 = 513661) B513661
theorem B619433 : Blo 179801 619433 := bstep (se 2 (by rfl) ⟨232287, by rfl⟩ : syracuseStep 619433 = 464575) B464575
theorem B522067 : Blo 179801 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B1112447 : Blo 179801 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B16054949 : Blo 179801 16054949 := bstep (se 4 (by rfl) ⟨1505151, by rfl⟩ : syracuseStep 16054949 = 3010303) B3010303
theorem B1736873 : Blo 179801 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B690515 : Blo 179801 690515 := bstep (se 1 (by rfl) ⟨517886, by rfl⟩ : syracuseStep 690515 = 1035773) B1035773
theorem B692975 : Blo 179801 692975 := bstep (se 1 (by rfl) ⟨519731, by rfl⟩ : syracuseStep 692975 = 1039463) B1039463
theorem B2790263 : Blo 179801 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B628489 : Blo 179801 628489 := bstep (se 2 (by rfl) ⟨235683, by rfl⟩ : syracuseStep 628489 = 471367) B471367
theorem B857999 : Blo 179801 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B203431 : Blo 179801 203431 := bstep (se 1 (by rfl) ⟨152573, by rfl⟩ : syracuseStep 203431 = 305147) B305147
theorem B696089 : Blo 179801 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B1744679 : Blo 179801 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B1647145 : Blo 179801 1647145 := bstep (se 2 (by rfl) ⟨617679, by rfl⟩ : syracuseStep 1647145 = 1235359) B1235359
theorem B3744481 : Blo 179801 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B271529 : Blo 179801 271529 := bstep (se 2 (by rfl) ⟨101823, by rfl⟩ : syracuseStep 271529 = 203647) B203647
theorem B272615 : Blo 179801 272615 := bstep (se 1 (by rfl) ⟨204461, by rfl⟩ : syracuseStep 272615 = 408923) B408923
theorem B273065 : Blo 179801 273065 := bstep (se 2 (by rfl) ⟨102399, by rfl⟩ : syracuseStep 273065 = 204799) B204799
theorem B273407 : Blo 179801 273407 := bstep (se 1 (by rfl) ⟨205055, by rfl⟩ : syracuseStep 273407 = 410111) B410111
theorem B274727 : Blo 179801 274727 := bstep (se 1 (by rfl) ⟨206045, by rfl⟩ : syracuseStep 274727 = 412091) B412091
theorem B407177 : Blo 179801 407177 := bstep (se 2 (by rfl) ⟨152691, by rfl⟩ : syracuseStep 407177 = 305383) B305383
theorem B6928415 : Blo 179801 6928415 := bstep (se 1 (by rfl) ⟨5196311, by rfl⟩ : syracuseStep 6928415 = 10392623) B10392623
theorem B768527 : Blo 179801 768527 := bstep (se 1 (by rfl) ⟨576395, by rfl⟩ : syracuseStep 768527 = 1152791) B1152791
theorem B342623 : Blo 179801 342623 := bstep (se 1 (by rfl) ⟨256967, by rfl⟩ : syracuseStep 342623 = 513935) B513935
theorem B408347 : Blo 179801 408347 := bstep (se 1 (by rfl) ⟨306260, by rfl⟩ : syracuseStep 408347 = 612521) B612521
theorem B409427 : Blo 179801 409427 := bstep (se 1 (by rfl) ⟨307070, by rfl⟩ : syracuseStep 409427 = 614141) B614141
theorem B671771 : Blo 179801 671771 := bstep (se 1 (by rfl) ⟨503828, by rfl⟩ : syracuseStep 671771 = 1007657) B1007657
theorem B770303 : Blo 179801 770303 := bstep (se 1 (by rfl) ⟨577727, by rfl⟩ : syracuseStep 770303 = 1155455) B1155455
theorem B344969 : Blo 179801 344969 := bstep (se 2 (by rfl) ⟨129363, by rfl⟩ : syracuseStep 344969 = 258727) B258727
theorem B411785 : Blo 179801 411785 := bstep (se 2 (by rfl) ⟨154419, by rfl⟩ : syracuseStep 411785 = 308839) B308839
theorem B346351 : Blo 179801 346351 := bstep (se 1 (by rfl) ⟨259763, by rfl⟩ : syracuseStep 346351 = 519527) B519527
theorem B411911 : Blo 179801 411911 := bstep (se 1 (by rfl) ⟨308933, by rfl⟩ : syracuseStep 411911 = 617867) B617867
theorem B14240447 : Blo 179801 14240447 := bstep (se 1 (by rfl) ⟨10680335, by rfl⟩ : syracuseStep 14240447 = 21360671) B21360671
theorem B183231 : Blo 179801 183231 := bstep (se 1 (by rfl) ⟨137423, by rfl⟩ : syracuseStep 183231 = 274847) B274847
theorem B183387 : Blo 179801 183387 := bstep (se 1 (by rfl) ⟨137540, by rfl⟩ : syracuseStep 183387 = 275081) B275081
theorem B183451 : Blo 179801 183451 := bstep (se 1 (by rfl) ⟨137588, by rfl⟩ : syracuseStep 183451 = 275177) B275177
theorem B412955 : Blo 179801 412955 := bstep (se 1 (by rfl) ⟨309716, by rfl⟩ : syracuseStep 412955 = 619433) B619433
theorem B741631 : Blo 179801 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B10703299 : Blo 179801 10703299 := bstep (se 1 (by rfl) ⟨8027474, by rfl⟩ : syracuseStep 10703299 = 16054949) B16054949
theorem B614303 : Blo 179801 614303 := bstep (se 1 (by rfl) ⟨460727, by rfl⟩ : syracuseStep 614303 = 921455) B921455
theorem B2974441 : Blo 179801 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B516851 : Blo 179801 516851 := bstep (se 1 (by rfl) ⟨387638, by rfl⟩ : syracuseStep 516851 = 775277) B775277
theorem B22635449 : Blo 179801 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B746759 : Blo 179801 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B518251 : Blo 179801 518251 := bstep (se 1 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 518251 = 777377) B777377
theorem B389279 : Blo 179801 389279 := bstep (se 1 (by rfl) ⟨291959, by rfl⟩ : syracuseStep 389279 = 583919) B583919
theorem B389423 : Blo 179801 389423 := bstep (se 1 (by rfl) ⟨292067, by rfl⟩ : syracuseStep 389423 = 584135) B584135
theorem B1733723 : Blo 179801 1733723 := bstep (se 1 (by rfl) ⟨1300292, by rfl⟩ : syracuseStep 1733723 = 2600585) B2600585
theorem B456587 : Blo 179801 456587 := bstep (se 1 (by rfl) ⟨342440, by rfl⟩ : syracuseStep 456587 = 684881) B684881
theorem B457609 : Blo 179801 457609 := bstep (se 2 (by rfl) ⟨171603, by rfl⟩ : syracuseStep 457609 = 343207) B343207
theorem B229979 : Blo 179801 229979 := bstep (se 1 (by rfl) ⟨172484, by rfl⟩ : syracuseStep 229979 = 344969) B344969
theorem B2196193 : Blo 179801 2196193 := bstep (se 2 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 2196193 = 1647145) B1647145
theorem B3965921 : Blo 179801 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B460343 : Blo 179801 460343 := bstep (se 1 (by rfl) ⟨345257, by rfl⟩ : syracuseStep 460343 = 690515) B690515
theorem B691001 : Blo 179801 691001 := bstep (se 2 (by rfl) ⟨259125, by rfl⟩ : syracuseStep 691001 = 518251) B518251
theorem B461801 : Blo 179801 461801 := bstep (se 2 (by rfl) ⟨173175, by rfl⟩ : syracuseStep 461801 = 346351) B346351
theorem B461983 : Blo 179801 461983 := bstep (se 1 (by rfl) ⟨346487, by rfl⟩ : syracuseStep 461983 = 692975) B692975
theorem B464059 : Blo 179801 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B988841 : Blo 179801 988841 := bstep (se 2 (by rfl) ⟨370815, by rfl⟩ : syracuseStep 988841 = 741631) B741631
theorem B497839 : Blo 179801 497839 := bstep (se 1 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 497839 = 746759) B746759
theorem B1155815 : Blo 179801 1155815 := bstep (se 1 (by rfl) ⟨866861, by rfl⟩ : syracuseStep 1155815 = 1733723) B1733723
theorem B271241 : Blo 179801 271241 := bstep (se 2 (by rfl) ⟨101715, by rfl⟩ : syracuseStep 271241 = 203431) B203431
theorem B271451 : Blo 179801 271451 := bstep (se 1 (by rfl) ⟨203588, by rfl⟩ : syracuseStep 271451 = 407177) B407177
theorem B304391 : Blo 179801 304391 := bstep (se 1 (by rfl) ⟨228293, by rfl⟩ : syracuseStep 304391 = 456587) B456587
theorem B3351941 : Blo 179801 3351941 := bstep (se 4 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 3351941 = 628489) B628489
theorem B272231 : Blo 179801 272231 := bstep (se 1 (by rfl) ⟨204173, by rfl⟩ : syracuseStep 272231 = 408347) B408347
theorem B272951 : Blo 179801 272951 := bstep (se 1 (by rfl) ⟨204713, by rfl⟩ : syracuseStep 272951 = 409427) B409427
theorem B1157915 : Blo 179801 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B4992641 : Blo 179801 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B274523 : Blo 179801 274523 := bstep (se 1 (by rfl) ⟨205892, by rfl⟩ : syracuseStep 274523 = 411785) B411785
theorem B274607 : Blo 179801 274607 := bstep (se 1 (by rfl) ⟨205955, by rfl⟩ : syracuseStep 274607 = 411911) B411911
theorem B275303 : Blo 179801 275303 := bstep (se 1 (by rfl) ⟨206477, by rfl⟩ : syracuseStep 275303 = 412955) B412955
theorem B1163119 : Blo 179801 1163119 := bstep (se 1 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 1163119 = 1744679) B1744679
theorem B409535 : Blo 179801 409535 := bstep (se 1 (by rfl) ⟨307151, by rfl⟩ : syracuseStep 409535 = 614303) B614303
theorem B344567 : Blo 179801 344567 := bstep (se 1 (by rfl) ⟨258425, by rfl⟩ : syracuseStep 344567 = 516851) B516851
theorem B14271065 : Blo 179801 14271065 := bstep (se 2 (by rfl) ⟨5351649, by rfl⟩ : syracuseStep 14271065 = 10703299) B10703299
theorem B15090299 : Blo 179801 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B181019 : Blo 179801 181019 := bstep (se 1 (by rfl) ⟨135764, by rfl⟩ : syracuseStep 181019 = 271529) B271529
theorem B181743 : Blo 179801 181743 := bstep (se 1 (by rfl) ⟨136307, by rfl⟩ : syracuseStep 181743 = 272615) B272615
theorem B182043 : Blo 179801 182043 := bstep (se 1 (by rfl) ⟨136532, by rfl⟩ : syracuseStep 182043 = 273065) B273065
theorem B182271 : Blo 179801 182271 := bstep (se 1 (by rfl) ⟨136703, by rfl⟩ : syracuseStep 182271 = 273407) B273407
theorem B183151 : Blo 179801 183151 := bstep (se 1 (by rfl) ⟨137363, by rfl⟩ : syracuseStep 183151 = 274727) B274727
theorem B610145 : Blo 179801 610145 := bstep (se 2 (by rfl) ⟨228804, by rfl⟩ : syracuseStep 610145 = 457609) B457609
theorem B512351 : Blo 179801 512351 := bstep (se 1 (by rfl) ⟨384263, by rfl⟩ : syracuseStep 512351 = 768527) B768527
theorem B1791389 : Blo 179801 1791389 := bstep (se 3 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 1791389 = 671771) B671771
theorem B513535 : Blo 179801 513535 := bstep (se 1 (by rfl) ⟨385151, by rfl⟩ : syracuseStep 513535 = 770303) B770303
theorem B9493631 : Blo 179801 9493631 := bstep (se 1 (by rfl) ⟨7120223, by rfl⟩ : syracuseStep 9493631 = 14240447) B14240447
theorem B1860175 : Blo 179801 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B2287997 : Blo 179801 2287997 := bstep (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) B857999
theorem B259519 : Blo 179801 259519 := bstep (se 1 (by rfl) ⟨194639, by rfl⟩ : syracuseStep 259519 = 389279) B389279
theorem B259615 : Blo 179801 259615 := bstep (se 1 (by rfl) ⟨194711, by rfl⟩ : syracuseStep 259615 = 389423) B389423
theorem B4618943 : Blo 179801 4618943 := bstep (se 1 (by rfl) ⟨3464207, by rfl⟩ : syracuseStep 4618943 = 6928415) B6928415
theorem B228415 : Blo 179801 228415 := bstep (se 1 (by rfl) ⟨171311, by rfl⟩ : syracuseStep 228415 = 342623) B342623
theorem B229711 : Blo 179801 229711 := bstep (se 1 (by rfl) ⟨172283, by rfl⟩ : syracuseStep 229711 = 344567) B344567
theorem B10060199 : Blo 179801 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B460667 : Blo 179801 460667 := bstep (se 1 (by rfl) ⟨345500, by rfl⟩ : syracuseStep 460667 = 691001) B691001
theorem B659227 : Blo 179801 659227 := bstep (se 1 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 659227 = 988841) B988841
theorem B6329087 : Blo 179801 6329087 := bstep (se 1 (by rfl) ⟨4746815, by rfl⟩ : syracuseStep 6329087 = 9493631) B9493631
theorem B202927 : Blo 179801 202927 := bstep (se 1 (by rfl) ⟨152195, by rfl⟩ : syracuseStep 202927 = 304391) B304391
theorem B2234627 : Blo 179801 2234627 := bstep (se 1 (by rfl) ⟨1675970, by rfl⟩ : syracuseStep 2234627 = 3351941) B3351941
theorem B1384613 : Blo 179801 1384613 := bstep (se 4 (by rfl) ⟨129807, by rfl⟩ : syracuseStep 1384613 = 259615) B259615
theorem B663785 : Blo 179801 663785 := bstep (se 2 (by rfl) ⟨248919, by rfl⟩ : syracuseStep 663785 = 497839) B497839
theorem B304553 : Blo 179801 304553 := bstep (se 2 (by rfl) ⟨114207, by rfl⟩ : syracuseStep 304553 = 228415) B228415
theorem B1550825 : Blo 179801 1550825 := bstep (se 2 (by rfl) ⟨581559, by rfl⟩ : syracuseStep 1550825 = 1163119) B1163119
theorem B273023 : Blo 179801 273023 := bstep (se 1 (by rfl) ⟨204767, by rfl⟩ : syracuseStep 273023 = 409535) B409535
theorem B9514043 : Blo 179801 9514043 := bstep (se 1 (by rfl) ⟨7135532, by rfl⟩ : syracuseStep 9514043 = 14271065) B14271065
theorem B2928257 : Blo 179801 2928257 := bstep (se 2 (by rfl) ⟨1098096, by rfl⟩ : syracuseStep 2928257 = 2196193) B2196193
theorem B306895 : Blo 179801 306895 := bstep (se 1 (by rfl) ⟨230171, by rfl⟩ : syracuseStep 306895 = 460343) B460343
theorem B307867 : Blo 179801 307867 := bstep (se 1 (by rfl) ⟨230900, by rfl⟩ : syracuseStep 307867 = 461801) B461801
theorem B406763 : Blo 179801 406763 := bstep (se 1 (by rfl) ⟨305072, by rfl⟩ : syracuseStep 406763 = 610145) B610145
theorem B341567 : Blo 179801 341567 := bstep (se 1 (by rfl) ⟨256175, by rfl⟩ : syracuseStep 341567 = 512351) B512351
theorem B1194259 : Blo 179801 1194259 := bstep (se 1 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 1194259 = 1791389) B1791389
theorem B770543 : Blo 179801 770543 := bstep (se 1 (by rfl) ⟨577907, by rfl⟩ : syracuseStep 770543 = 1155815) B1155815
theorem B180827 : Blo 179801 180827 := bstep (se 1 (by rfl) ⟨135620, by rfl⟩ : syracuseStep 180827 = 271241) B271241
theorem B180967 : Blo 179801 180967 := bstep (se 1 (by rfl) ⟨135725, by rfl⟩ : syracuseStep 180967 = 271451) B271451
theorem B181487 : Blo 179801 181487 := bstep (se 1 (by rfl) ⟨136115, by rfl⟩ : syracuseStep 181487 = 272231) B272231
theorem B1525331 : Blo 179801 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B181967 : Blo 179801 181967 := bstep (se 1 (by rfl) ⟨136475, by rfl⟩ : syracuseStep 181967 = 272951) B272951
theorem B771943 : Blo 179801 771943 := bstep (se 1 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 771943 = 1157915) B1157915
theorem B346025 : Blo 179801 346025 := bstep (se 2 (by rfl) ⟨129759, by rfl⟩ : syracuseStep 346025 = 259519) B259519
theorem B3328427 : Blo 179801 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B183015 : Blo 179801 183015 := bstep (se 1 (by rfl) ⟨137261, by rfl⟩ : syracuseStep 183015 = 274523) B274523
theorem B183071 : Blo 179801 183071 := bstep (se 1 (by rfl) ⟨137303, by rfl⟩ : syracuseStep 183071 = 274607) B274607
theorem B183535 : Blo 179801 183535 := bstep (se 1 (by rfl) ⟨137651, by rfl⟩ : syracuseStep 183535 = 275303) B275303
theorem B2643947 : Blo 179801 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B2480233 : Blo 179801 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B613277 : Blo 179801 613277 := bstep (se 3 (by rfl) ⟨114989, by rfl⟩ : syracuseStep 613277 = 229979) B229979
theorem B615977 : Blo 179801 615977 := bstep (se 2 (by rfl) ⟨230991, by rfl⟩ : syracuseStep 615977 = 461983) B461983
theorem B618745 : Blo 179801 618745 := bstep (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) B464059
theorem B684713 : Blo 179801 684713 := bstep (se 2 (by rfl) ⟨256767, by rfl⟩ : syracuseStep 684713 = 513535) B513535
theorem B3079295 : Blo 179801 3079295 := bstep (se 1 (by rfl) ⟨2309471, by rfl⟩ : syracuseStep 3079295 = 4618943) B4618943
theorem B1016887 : Blo 179801 1016887 := bstep (se 1 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 1016887 = 1525331) B1525331
theorem B230683 : Blo 179801 230683 := bstep (se 1 (by rfl) ⟨173012, by rfl⟩ : syracuseStep 230683 = 346025) B346025
theorem B923075 : Blo 179801 923075 := bstep (se 1 (by rfl) ⟨692306, by rfl⟩ : syracuseStep 923075 = 1384613) B1384613
theorem B824993 : Blo 179801 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B203035 : Blo 179801 203035 := bstep (se 1 (by rfl) ⟨152276, by rfl⟩ : syracuseStep 203035 = 304553) B304553
theorem B270569 : Blo 179801 270569 := bstep (se 2 (by rfl) ⟨101463, by rfl⟩ : syracuseStep 270569 = 202927) B202927
theorem B271175 : Blo 179801 271175 := bstep (se 1 (by rfl) ⟨203381, by rfl⟩ : syracuseStep 271175 = 406763) B406763
theorem B306281 : Blo 179801 306281 := bstep (se 2 (by rfl) ⟨114855, by rfl⟩ : syracuseStep 306281 = 229711) B229711
theorem B307111 : Blo 179801 307111 := bstep (se 1 (by rfl) ⟨230333, by rfl⟩ : syracuseStep 307111 = 460667) B460667
theorem B1029257 : Blo 179801 1029257 := bstep (se 2 (by rfl) ⟨385971, by rfl⟩ : syracuseStep 1029257 = 771943) B771943
theorem B1489751 : Blo 179801 1489751 := bstep (se 1 (by rfl) ⟨1117313, by rfl⟩ : syracuseStep 1489751 = 2234627) B2234627
theorem B408851 : Blo 179801 408851 := bstep (se 1 (by rfl) ⟨306638, by rfl⟩ : syracuseStep 408851 = 613277) B613277
theorem B409193 : Blo 179801 409193 := bstep (se 2 (by rfl) ⟨153447, by rfl⟩ : syracuseStep 409193 = 306895) B306895
theorem B442523 : Blo 179801 442523 := bstep (se 1 (by rfl) ⟨331892, by rfl⟩ : syracuseStep 442523 = 663785) B663785
theorem B410489 : Blo 179801 410489 := bstep (se 2 (by rfl) ⟨153933, by rfl⟩ : syracuseStep 410489 = 307867) B307867
theorem B410651 : Blo 179801 410651 := bstep (se 1 (by rfl) ⟨307988, by rfl⟩ : syracuseStep 410651 = 615977) B615977
theorem B1033883 : Blo 179801 1033883 := bstep (se 1 (by rfl) ⟨775412, by rfl⟩ : syracuseStep 1033883 = 1550825) B1550825
theorem B182015 : Blo 179801 182015 := bstep (se 1 (by rfl) ⟨136511, by rfl⟩ : syracuseStep 182015 = 273023) B273023
theorem B6342695 : Blo 179801 6342695 := bstep (se 1 (by rfl) ⟨4757021, by rfl⟩ : syracuseStep 6342695 = 9514043) B9514043
theorem B1952171 : Blo 179801 1952171 := bstep (se 1 (by rfl) ⟨1464128, by rfl⟩ : syracuseStep 1952171 = 2928257) B2928257
theorem B1592345 : Blo 179801 1592345 := bstep (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) B1194259
theorem B2052863 : Blo 179801 2052863 := bstep (se 1 (by rfl) ⟨1539647, by rfl⟩ : syracuseStep 2052863 = 3079295) B3079295
theorem B6706799 : Blo 179801 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B513695 : Blo 179801 513695 := bstep (se 1 (by rfl) ⟨385271, by rfl⟩ : syracuseStep 513695 = 770543) B770543
theorem B2218951 : Blo 179801 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B4219391 : Blo 179801 4219391 := bstep (se 1 (by rfl) ⟨3164543, by rfl⟩ : syracuseStep 4219391 = 6329087) B6329087
theorem B1762631 : Blo 179801 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B878969 : Blo 179801 878969 := bstep (se 2 (by rfl) ⟨329613, by rfl⟩ : syracuseStep 878969 = 659227) B659227
theorem B3306977 : Blo 179801 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B456475 : Blo 179801 456475 := bstep (se 1 (by rfl) ⟨342356, by rfl⟩ : syracuseStep 456475 = 684713) B684713
theorem B227711 : Blo 179801 227711 := bstep (se 1 (by rfl) ⟨170783, by rfl⟩ : syracuseStep 227711 = 341567) B341567
theorem B295015 : Blo 179801 295015 := bstep (se 1 (by rfl) ⟨221261, by rfl⟩ : syracuseStep 295015 = 442523) B442523
theorem B689255 : Blo 179801 689255 := bstep (se 1 (by rfl) ⟨516941, by rfl⟩ : syracuseStep 689255 = 1033883) B1033883
theorem B4228463 : Blo 179801 4228463 := bstep (se 1 (by rfl) ⟨3171347, by rfl⟩ : syracuseStep 4228463 = 6342695) B6342695
theorem B204187 : Blo 179801 204187 := bstep (se 1 (by rfl) ⟨153140, by rfl⟩ : syracuseStep 204187 = 306281) B306281
theorem B270713 : Blo 179801 270713 := bstep (se 2 (by rfl) ⟨101517, by rfl⟩ : syracuseStep 270713 = 203035) B203035
theorem B2204651 : Blo 179801 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B2958601 : Blo 179801 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B993167 : Blo 179801 993167 := bstep (se 1 (by rfl) ⟨744875, by rfl⟩ : syracuseStep 993167 = 1489751) B1489751
theorem B272567 : Blo 179801 272567 := bstep (se 1 (by rfl) ⟨204425, by rfl⟩ : syracuseStep 272567 = 408851) B408851
theorem B272795 : Blo 179801 272795 := bstep (se 1 (by rfl) ⟨204596, by rfl⟩ : syracuseStep 272795 = 409193) B409193
theorem B273659 : Blo 179801 273659 := bstep (se 1 (by rfl) ⟨205244, by rfl⟩ : syracuseStep 273659 = 410489) B410489
theorem B273767 : Blo 179801 273767 := bstep (se 1 (by rfl) ⟨205325, by rfl⟩ : syracuseStep 273767 = 410651) B410651
theorem B1355849 : Blo 179801 1355849 := bstep (se 2 (by rfl) ⟨508443, by rfl⟩ : syracuseStep 1355849 = 1016887) B1016887
theorem B307577 : Blo 179801 307577 := bstep (se 2 (by rfl) ⟨115341, by rfl⟩ : syracuseStep 307577 = 230683) B230683
theorem B4471199 : Blo 179801 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B342463 : Blo 179801 342463 := bstep (se 1 (by rfl) ⟨256847, by rfl⟩ : syracuseStep 342463 = 513695) B513695
theorem B409481 : Blo 179801 409481 := bstep (se 2 (by rfl) ⟨153555, by rfl⟩ : syracuseStep 409481 = 307111) B307111
theorem B180379 : Blo 179801 180379 := bstep (se 1 (by rfl) ⟨135284, by rfl⟩ : syracuseStep 180379 = 270569) B270569
theorem B180783 : Blo 179801 180783 := bstep (se 1 (by rfl) ⟨135587, by rfl⟩ : syracuseStep 180783 = 271175) B271175
theorem B2343917 : Blo 179801 2343917 := bstep (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) B878969
theorem B607229 : Blo 179801 607229 := bstep (se 3 (by rfl) ⟨113855, by rfl⟩ : syracuseStep 607229 = 227711) B227711
theorem B608633 : Blo 179801 608633 := bstep (se 2 (by rfl) ⟨228237, by rfl⟩ : syracuseStep 608633 = 456475) B456475
theorem B4246253 : Blo 179801 4246253 := bstep (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) B1592345
theorem B1301447 : Blo 179801 1301447 := bstep (se 1 (by rfl) ⟨976085, by rfl⟩ : syracuseStep 1301447 = 1952171) B1952171
theorem B1368575 : Blo 179801 1368575 := bstep (se 1 (by rfl) ⟨1026431, by rfl⟩ : syracuseStep 1368575 = 2052863) B2052863
theorem B615383 : Blo 179801 615383 := bstep (se 1 (by rfl) ⟨461537, by rfl⟩ : syracuseStep 615383 = 923075) B923075
theorem B549995 : Blo 179801 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B2812927 : Blo 179801 2812927 := bstep (se 1 (by rfl) ⟨2109695, by rfl⟩ : syracuseStep 2812927 = 4219391) B4219391
theorem B1175087 : Blo 179801 1175087 := bstep (se 1 (by rfl) ⟨881315, by rfl⟩ : syracuseStep 1175087 = 1762631) B1762631
theorem B686171 : Blo 179801 686171 := bstep (se 1 (by rfl) ⟨514628, by rfl⟩ : syracuseStep 686171 = 1029257) B1029257
theorem B393353 : Blo 179801 393353 := bstep (se 2 (by rfl) ⟨147507, by rfl⟩ : syracuseStep 393353 = 295015) B295015
theorem B459503 : Blo 179801 459503 := bstep (se 1 (by rfl) ⟨344627, by rfl⟩ : syracuseStep 459503 = 689255) B689255
theorem B2818975 : Blo 179801 2818975 := bstep (se 1 (by rfl) ⟨2114231, by rfl⟩ : syracuseStep 2818975 = 4228463) B4228463
theorem B5866613 : Blo 179801 5866613 := bstep (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) B549995
theorem B662111 : Blo 179801 662111 := bstep (se 1 (by rfl) ⟨496583, by rfl⟩ : syracuseStep 662111 = 993167) B993167
theorem B205051 : Blo 179801 205051 := bstep (se 1 (by rfl) ⟨153788, by rfl⟩ : syracuseStep 205051 = 307577) B307577
theorem B272249 : Blo 179801 272249 := bstep (se 2 (by rfl) ⟨102093, by rfl⟩ : syracuseStep 272249 = 204187) B204187
theorem B272987 : Blo 179801 272987 := bstep (se 1 (by rfl) ⟨204740, by rfl⟩ : syracuseStep 272987 = 409481) B409481
theorem B404819 : Blo 179801 404819 := bstep (se 1 (by rfl) ⟨303614, by rfl⟩ : syracuseStep 404819 = 607229) B607229
theorem B405755 : Blo 179801 405755 := bstep (se 1 (by rfl) ⟨304316, by rfl⟩ : syracuseStep 405755 = 608633) B608633
theorem B3944801 : Blo 179801 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B2830835 : Blo 179801 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B3750569 : Blo 179801 3750569 := bstep (se 2 (by rfl) ⟨1406463, by rfl⟩ : syracuseStep 3750569 = 2812927) B2812927
theorem B867631 : Blo 179801 867631 := bstep (se 1 (by rfl) ⟨650723, by rfl⟩ : syracuseStep 867631 = 1301447) B1301447
theorem B180475 : Blo 179801 180475 := bstep (se 1 (by rfl) ⟨135356, by rfl⟩ : syracuseStep 180475 = 270713) B270713
theorem B410255 : Blo 179801 410255 := bstep (se 1 (by rfl) ⟨307691, by rfl⟩ : syracuseStep 410255 = 615383) B615383
theorem B181711 : Blo 179801 181711 := bstep (se 1 (by rfl) ⟨136283, by rfl⟩ : syracuseStep 181711 = 272567) B272567
theorem B181863 : Blo 179801 181863 := bstep (se 1 (by rfl) ⟨136397, by rfl⟩ : syracuseStep 181863 = 272795) B272795
theorem B182439 : Blo 179801 182439 := bstep (se 1 (by rfl) ⟨136829, by rfl⟩ : syracuseStep 182439 = 273659) B273659
theorem B182511 : Blo 179801 182511 := bstep (se 1 (by rfl) ⟨136883, by rfl⟩ : syracuseStep 182511 = 273767) B273767
theorem B903899 : Blo 179801 903899 := bstep (se 1 (by rfl) ⟨677924, by rfl⟩ : syracuseStep 903899 = 1355849) B1355849
theorem B1562611 : Blo 179801 1562611 := bstep (se 1 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 1562611 = 2343917) B2343917
theorem B912383 : Blo 179801 912383 := bstep (se 1 (by rfl) ⟨684287, by rfl⟩ : syracuseStep 912383 = 1368575) B1368575
theorem B1469767 : Blo 179801 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B783391 : Blo 179801 783391 := bstep (se 1 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 783391 = 1175087) B1175087
theorem B456617 : Blo 179801 456617 := bstep (se 2 (by rfl) ⟨171231, by rfl⟩ : syracuseStep 456617 = 342463) B342463
theorem B457447 : Blo 179801 457447 := bstep (se 1 (by rfl) ⟨343085, by rfl⟩ : syracuseStep 457447 = 686171) B686171
theorem B2980799 : Blo 179801 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B262235 : Blo 179801 262235 := bstep (se 1 (by rfl) ⟨196676, by rfl⟩ : syracuseStep 262235 = 393353) B393353
theorem B10519469 : Blo 179801 10519469 := bstep (se 3 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 10519469 = 3944801) B3944801
theorem B269879 : Blo 179801 269879 := bstep (se 1 (by rfl) ⟨202409, by rfl⟩ : syracuseStep 269879 = 404819) B404819
theorem B270503 : Blo 179801 270503 := bstep (se 1 (by rfl) ⟨202877, by rfl⟩ : syracuseStep 270503 = 405755) B405755
theorem B304411 : Blo 179801 304411 := bstep (se 1 (by rfl) ⟨228308, by rfl⟩ : syracuseStep 304411 = 456617) B456617
theorem B1156841 : Blo 179801 1156841 := bstep (se 2 (by rfl) ⟨433815, by rfl⟩ : syracuseStep 1156841 = 867631) B867631
theorem B2500379 : Blo 179801 2500379 := bstep (se 1 (by rfl) ⟨1875284, by rfl⟩ : syracuseStep 2500379 = 3750569) B3750569
theorem B273401 : Blo 179801 273401 := bstep (se 2 (by rfl) ⟨102525, by rfl⟩ : syracuseStep 273401 = 205051) B205051
theorem B273503 : Blo 179801 273503 := bstep (se 1 (by rfl) ⟨205127, by rfl⟩ : syracuseStep 273503 = 410255) B410255
theorem B306335 : Blo 179801 306335 := bstep (se 1 (by rfl) ⟨229751, by rfl⟩ : syracuseStep 306335 = 459503) B459503
theorem B3911075 : Blo 179801 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B7548893 : Blo 179801 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B602599 : Blo 179801 602599 := bstep (se 1 (by rfl) ⟨451949, by rfl⟩ : syracuseStep 602599 = 903899) B903899
theorem B441407 : Blo 179801 441407 := bstep (se 1 (by rfl) ⟨331055, by rfl⟩ : syracuseStep 441407 = 662111) B662111
theorem B181499 : Blo 179801 181499 := bstep (se 1 (by rfl) ⟨136124, by rfl⟩ : syracuseStep 181499 = 272249) B272249
theorem B181991 : Blo 179801 181991 := bstep (se 1 (by rfl) ⟨136493, by rfl⟩ : syracuseStep 181991 = 272987) B272987
theorem B608255 : Blo 179801 608255 := bstep (se 1 (by rfl) ⟨456191, by rfl⟩ : syracuseStep 608255 = 912383) B912383
theorem B2083481 : Blo 179801 2083481 := bstep (se 2 (by rfl) ⟨781305, by rfl⟩ : syracuseStep 2083481 = 1562611) B1562611
theorem B609929 : Blo 179801 609929 := bstep (se 2 (by rfl) ⟨228723, by rfl⟩ : syracuseStep 609929 = 457447) B457447
theorem B1987199 : Blo 179801 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B3758633 : Blo 179801 3758633 := bstep (se 2 (by rfl) ⟨1409487, by rfl⟩ : syracuseStep 3758633 = 2818975) B2818975
theorem B1959689 : Blo 179801 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B1044521 : Blo 179801 1044521 := bstep (se 2 (by rfl) ⟨391695, by rfl⟩ : syracuseStep 1044521 = 783391) B783391
theorem B7012979 : Blo 179801 7012979 := bstep (se 1 (by rfl) ⟨5259734, by rfl⟩ : syracuseStep 7012979 = 10519469) B10519469
theorem B204223 : Blo 179801 204223 := bstep (se 1 (by rfl) ⟨153167, by rfl⟩ : syracuseStep 204223 = 306335) B306335
theorem B696347 : Blo 179801 696347 := bstep (se 1 (by rfl) ⟨522260, by rfl⟩ : syracuseStep 696347 = 1044521) B1044521
theorem B699293 : Blo 179801 699293 := bstep (se 3 (by rfl) ⟨131117, by rfl⟩ : syracuseStep 699293 = 262235) B262235
theorem B405503 : Blo 179801 405503 := bstep (se 1 (by rfl) ⟨304127, by rfl⟩ : syracuseStep 405503 = 608255) B608255
theorem B405881 : Blo 179801 405881 := bstep (se 2 (by rfl) ⟨152205, by rfl⟩ : syracuseStep 405881 = 304411) B304411
theorem B1388987 : Blo 179801 1388987 := bstep (se 1 (by rfl) ⟨1041740, by rfl⟩ : syracuseStep 1388987 = 2083481) B2083481
theorem B406619 : Blo 179801 406619 := bstep (se 1 (by rfl) ⟨304964, by rfl⟩ : syracuseStep 406619 = 609929) B609929
theorem B1324799 : Blo 179801 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B2505755 : Blo 179801 2505755 := bstep (se 1 (by rfl) ⟨1879316, by rfl⟩ : syracuseStep 2505755 = 3758633) B3758633
theorem B179919 : Blo 179801 179919 := bstep (se 1 (by rfl) ⟨134939, by rfl⟩ : syracuseStep 179919 = 269879) B269879
theorem B180335 : Blo 179801 180335 := bstep (se 1 (by rfl) ⟨135251, by rfl⟩ : syracuseStep 180335 = 270503) B270503
theorem B803465 : Blo 179801 803465 := bstep (se 2 (by rfl) ⟨301299, by rfl⟩ : syracuseStep 803465 = 602599) B602599
theorem B771227 : Blo 179801 771227 := bstep (se 1 (by rfl) ⟨578420, by rfl⟩ : syracuseStep 771227 = 1156841) B1156841
theorem B182267 : Blo 179801 182267 := bstep (se 1 (by rfl) ⟨136700, by rfl⟩ : syracuseStep 182267 = 273401) B273401
theorem B182335 : Blo 179801 182335 := bstep (se 1 (by rfl) ⟨136751, by rfl⟩ : syracuseStep 182335 = 273503) B273503
theorem B2607383 : Blo 179801 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B5032595 : Blo 179801 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B1306459 : Blo 179801 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B1666919 : Blo 179801 1666919 := bstep (se 1 (by rfl) ⟨1250189, by rfl⟩ : syracuseStep 1666919 = 2500379) B2500379
theorem B1177085 : Blo 179801 1177085 := bstep (se 3 (by rfl) ⟨220703, by rfl⟩ : syracuseStep 1177085 = 441407) B441407
theorem B1738255 : Blo 179801 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B464231 : Blo 179801 464231 := bstep (se 1 (by rfl) ⟨348173, by rfl⟩ : syracuseStep 464231 = 696347) B696347
theorem B466195 : Blo 179801 466195 := bstep (se 1 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 466195 = 699293) B699293
theorem B270335 : Blo 179801 270335 := bstep (se 1 (by rfl) ⟨202751, by rfl⟩ : syracuseStep 270335 = 405503) B405503
theorem B270587 : Blo 179801 270587 := bstep (se 1 (by rfl) ⟨202940, by rfl⟩ : syracuseStep 270587 = 405881) B405881
theorem B925991 : Blo 179801 925991 := bstep (se 1 (by rfl) ⟨694493, by rfl⟩ : syracuseStep 925991 = 1388987) B1388987
theorem B271079 : Blo 179801 271079 := bstep (se 1 (by rfl) ⟨203309, by rfl⟩ : syracuseStep 271079 = 406619) B406619
theorem B272297 : Blo 179801 272297 := bstep (se 2 (by rfl) ⟨102111, by rfl⟩ : syracuseStep 272297 = 204223) B204223
theorem B535643 : Blo 179801 535643 := bstep (se 1 (by rfl) ⟨401732, by rfl⟩ : syracuseStep 535643 = 803465) B803465
theorem B3355063 : Blo 179801 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B6967781 : Blo 179801 6967781 := bstep (se 4 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 6967781 = 1306459) B1306459
theorem B4675319 : Blo 179801 4675319 := bstep (se 1 (by rfl) ⟨3506489, by rfl⟩ : syracuseStep 4675319 = 7012979) B7012979
theorem B514151 : Blo 179801 514151 := bstep (se 1 (by rfl) ⟨385613, by rfl⟩ : syracuseStep 514151 = 771227) B771227
theorem B1111279 : Blo 179801 1111279 := bstep (se 1 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 1111279 = 1666919) B1666919
theorem B784723 : Blo 179801 784723 := bstep (se 1 (by rfl) ⟨588542, by rfl⟩ : syracuseStep 784723 = 1177085) B1177085
theorem B883199 : Blo 179801 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B1670503 : Blo 179801 1670503 := bstep (se 1 (by rfl) ⟨1252877, by rfl⟩ : syracuseStep 1670503 = 2505755) B2505755
theorem B17893669 : Blo 179801 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B3116879 : Blo 179801 3116879 := bstep (se 1 (by rfl) ⟨2337659, by rfl⟩ : syracuseStep 3116879 = 4675319) B4675319
theorem B1481705 : Blo 179801 1481705 := bstep (se 2 (by rfl) ⟨555639, by rfl⟩ : syracuseStep 1481705 = 1111279) B1111279
theorem B309487 : Blo 179801 309487 := bstep (se 1 (by rfl) ⟨232115, by rfl⟩ : syracuseStep 309487 = 464231) B464231
theorem B342767 : Blo 179801 342767 := bstep (se 1 (by rfl) ⟨257075, by rfl⟩ : syracuseStep 342767 = 514151) B514151
theorem B180223 : Blo 179801 180223 := bstep (se 1 (by rfl) ⟨135167, by rfl⟩ : syracuseStep 180223 = 270335) B270335
theorem B180391 : Blo 179801 180391 := bstep (se 1 (by rfl) ⟨135293, by rfl⟩ : syracuseStep 180391 = 270587) B270587
theorem B180719 : Blo 179801 180719 := bstep (se 1 (by rfl) ⟨135539, by rfl⟩ : syracuseStep 180719 = 271079) B271079
theorem B181531 : Blo 179801 181531 := bstep (se 1 (by rfl) ⟨136148, by rfl⟩ : syracuseStep 181531 = 272297) B272297
theorem B2317673 : Blo 179801 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B4645187 : Blo 179801 4645187 := bstep (se 1 (by rfl) ⟨3483890, by rfl⟩ : syracuseStep 4645187 = 6967781) B6967781
theorem B617327 : Blo 179801 617327 := bstep (se 1 (by rfl) ⟨462995, by rfl⟩ : syracuseStep 617327 = 925991) B925991
theorem B357095 : Blo 179801 357095 := bstep (se 1 (by rfl) ⟨267821, by rfl⟩ : syracuseStep 357095 = 535643) B535643
theorem B1046297 : Blo 179801 1046297 := bstep (se 2 (by rfl) ⟨392361, by rfl⟩ : syracuseStep 1046297 = 784723) B784723
theorem B588799 : Blo 179801 588799 := bstep (se 1 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 588799 = 883199) B883199
theorem B621593 : Blo 179801 621593 := bstep (se 2 (by rfl) ⟨233097, by rfl⟩ : syracuseStep 621593 = 466195) B466195
theorem B2227337 : Blo 179801 2227337 := bstep (se 2 (by rfl) ⟨835251, by rfl⟩ : syracuseStep 2227337 = 1670503) B1670503
theorem B23858225 : Blo 179801 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B987803 : Blo 179801 987803 := bstep (se 1 (by rfl) ⟨740852, by rfl⟩ : syracuseStep 987803 = 1481705) B1481705
theorem B1545115 : Blo 179801 1545115 := bstep (se 1 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 1545115 = 2317673) B2317673
theorem B238063 : Blo 179801 238063 := bstep (se 1 (by rfl) ⟨178547, by rfl⟩ : syracuseStep 238063 = 357095) B357095
theorem B697531 : Blo 179801 697531 := bstep (se 1 (by rfl) ⟨523148, by rfl⟩ : syracuseStep 697531 = 1046297) B1046297
theorem B1484891 : Blo 179801 1484891 := bstep (se 1 (by rfl) ⟨1113668, by rfl⟩ : syracuseStep 1484891 = 2227337) B2227337
theorem B2077919 : Blo 179801 2077919 := bstep (se 1 (by rfl) ⟨1558439, by rfl⟩ : syracuseStep 2077919 = 3116879) B3116879
theorem B3096791 : Blo 179801 3096791 := bstep (se 1 (by rfl) ⟨2322593, by rfl⟩ : syracuseStep 3096791 = 4645187) B4645187
theorem B411551 : Blo 179801 411551 := bstep (se 1 (by rfl) ⟨308663, by rfl⟩ : syracuseStep 411551 = 617327) B617327
theorem B412649 : Blo 179801 412649 := bstep (se 2 (by rfl) ⟨154743, by rfl⟩ : syracuseStep 412649 = 309487) B309487
theorem B414395 : Blo 179801 414395 := bstep (se 1 (by rfl) ⟨310796, by rfl⟩ : syracuseStep 414395 = 621593) B621593
theorem B785065 : Blo 179801 785065 := bstep (se 2 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 785065 = 588799) B588799
theorem B228511 : Blo 179801 228511 := bstep (se 1 (by rfl) ⟨171383, by rfl⟩ : syracuseStep 228511 = 342767) B342767
theorem B2064527 : Blo 179801 2064527 := bstep (se 1 (by rfl) ⟨1548395, by rfl⟩ : syracuseStep 2064527 = 3096791) B3096791
theorem B658535 : Blo 179801 658535 := bstep (se 1 (by rfl) ⟨493901, by rfl⟩ : syracuseStep 658535 = 987803) B987803
theorem B989927 : Blo 179801 989927 := bstep (se 1 (by rfl) ⟨742445, by rfl⟩ : syracuseStep 989927 = 1484891) B1484891
theorem B1385279 : Blo 179801 1385279 := bstep (se 1 (by rfl) ⟨1038959, by rfl⟩ : syracuseStep 1385279 = 2077919) B2077919
theorem B304681 : Blo 179801 304681 := bstep (se 2 (by rfl) ⟨114255, by rfl⟩ : syracuseStep 304681 = 228511) B228511
theorem B274367 : Blo 179801 274367 := bstep (se 1 (by rfl) ⟨205775, by rfl⟩ : syracuseStep 274367 = 411551) B411551
theorem B930041 : Blo 179801 930041 := bstep (se 2 (by rfl) ⟨348765, by rfl⟩ : syracuseStep 930041 = 697531) B697531
theorem B275099 : Blo 179801 275099 := bstep (se 1 (by rfl) ⟨206324, by rfl⟩ : syracuseStep 275099 = 412649) B412649
theorem B15905483 : Blo 179801 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B276263 : Blo 179801 276263 := bstep (se 1 (by rfl) ⟨207197, by rfl⟩ : syracuseStep 276263 = 414395) B414395
theorem B317417 : Blo 179801 317417 := bstep (se 2 (by rfl) ⟨119031, by rfl⟩ : syracuseStep 317417 = 238063) B238063
theorem B2060153 : Blo 179801 2060153 := bstep (se 2 (by rfl) ⟨772557, by rfl⟩ : syracuseStep 2060153 = 1545115) B1545115
theorem B1046753 : Blo 179801 1046753 := bstep (se 2 (by rfl) ⟨392532, by rfl⟩ : syracuseStep 1046753 = 785065) B785065
theorem B1376351 : Blo 179801 1376351 := bstep (se 1 (by rfl) ⟨1032263, by rfl⟩ : syracuseStep 1376351 = 2064527) B2064527
theorem B659951 : Blo 179801 659951 := bstep (se 1 (by rfl) ⟨494963, by rfl⟩ : syracuseStep 659951 = 989927) B989927
theorem B923519 : Blo 179801 923519 := bstep (se 1 (by rfl) ⟨692639, by rfl⟩ : syracuseStep 923519 = 1385279) B1385279
theorem B697835 : Blo 179801 697835 := bstep (se 1 (by rfl) ⟨523376, by rfl⟩ : syracuseStep 697835 = 1046753) B1046753
theorem B406241 : Blo 179801 406241 := bstep (se 2 (by rfl) ⟨152340, by rfl⟩ : syracuseStep 406241 = 304681) B304681
theorem B182911 : Blo 179801 182911 := bstep (se 1 (by rfl) ⟨137183, by rfl⟩ : syracuseStep 182911 = 274367) B274367
theorem B1756093 : Blo 179801 1756093 := bstep (se 3 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 1756093 = 658535) B658535
theorem B183399 : Blo 179801 183399 := bstep (se 1 (by rfl) ⟨137549, by rfl⟩ : syracuseStep 183399 = 275099) B275099
theorem B10603655 : Blo 179801 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B184175 : Blo 179801 184175 := bstep (se 1 (by rfl) ⟨138131, by rfl⟩ : syracuseStep 184175 = 276263) B276263
theorem B846445 : Blo 179801 846445 := bstep (se 3 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 846445 = 317417) B317417
theorem B1373435 : Blo 179801 1373435 := bstep (se 1 (by rfl) ⟨1030076, by rfl⟩ : syracuseStep 1373435 = 2060153) B2060153
theorem B620027 : Blo 179801 620027 := bstep (se 1 (by rfl) ⟨465020, by rfl⟩ : syracuseStep 620027 = 930041) B930041
theorem B917567 : Blo 179801 917567 := bstep (se 1 (by rfl) ⟨688175, by rfl⟩ : syracuseStep 917567 = 1376351) B1376351
theorem B2462717 : Blo 179801 2462717 := bstep (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) B923519
theorem B465223 : Blo 179801 465223 := bstep (se 1 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 465223 = 697835) B697835
theorem B270827 : Blo 179801 270827 := bstep (se 1 (by rfl) ⟨203120, by rfl⟩ : syracuseStep 270827 = 406241) B406241
theorem B439967 : Blo 179801 439967 := bstep (se 1 (by rfl) ⟨329975, by rfl⟩ : syracuseStep 439967 = 659951) B659951
theorem B1128593 : Blo 179801 1128593 := bstep (se 2 (by rfl) ⟨423222, by rfl⟩ : syracuseStep 1128593 = 846445) B846445
theorem B2341457 : Blo 179801 2341457 := bstep (se 2 (by rfl) ⟨878046, by rfl⟩ : syracuseStep 2341457 = 1756093) B1756093
theorem B413351 : Blo 179801 413351 := bstep (se 1 (by rfl) ⟨310013, by rfl⟩ : syracuseStep 413351 = 620027) B620027
theorem B7069103 : Blo 179801 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B7858133 : Blo 179801 7858133 := bstep (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) B184175
theorem B915623 : Blo 179801 915623 := bstep (se 1 (by rfl) ⟨686717, by rfl⟩ : syracuseStep 915623 = 1373435) B1373435
theorem B1641811 : Blo 179801 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B275567 : Blo 179801 275567 := bstep (se 1 (by rfl) ⟨206675, by rfl⟩ : syracuseStep 275567 = 413351) B413351
theorem B180551 : Blo 179801 180551 := bstep (se 1 (by rfl) ⟨135413, by rfl⟩ : syracuseStep 180551 = 270827) B270827
theorem B610415 : Blo 179801 610415 := bstep (se 1 (by rfl) ⟨457811, by rfl⟩ : syracuseStep 610415 = 915623) B915623
theorem B1560971 : Blo 179801 1560971 := bstep (se 1 (by rfl) ⟨1170728, by rfl⟩ : syracuseStep 1560971 = 2341457) B2341457
theorem B611711 : Blo 179801 611711 := bstep (se 1 (by rfl) ⟨458783, by rfl⟩ : syracuseStep 611711 = 917567) B917567
theorem B4712735 : Blo 179801 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B5238755 : Blo 179801 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B620297 : Blo 179801 620297 := bstep (se 2 (by rfl) ⟨232611, by rfl⟩ : syracuseStep 620297 = 465223) B465223
theorem B293311 : Blo 179801 293311 := bstep (se 1 (by rfl) ⟨219983, by rfl⟩ : syracuseStep 293311 = 439967) B439967
theorem B752395 : Blo 179801 752395 := bstep (se 1 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 752395 = 1128593) B1128593
theorem B406943 : Blo 179801 406943 := bstep (se 1 (by rfl) ⟨305207, by rfl⟩ : syracuseStep 406943 = 610415) B610415
theorem B407807 : Blo 179801 407807 := bstep (se 1 (by rfl) ⟨305855, by rfl⟩ : syracuseStep 407807 = 611711) B611711
theorem B3492503 : Blo 179801 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B183711 : Blo 179801 183711 := bstep (se 1 (by rfl) ⟨137783, by rfl⟩ : syracuseStep 183711 = 275567) B275567
theorem B1003193 : Blo 179801 1003193 := bstep (se 2 (by rfl) ⟨376197, by rfl⟩ : syracuseStep 1003193 = 752395) B752395
theorem B413531 : Blo 179801 413531 := bstep (se 1 (by rfl) ⟨310148, by rfl⟩ : syracuseStep 413531 = 620297) B620297
theorem B1040647 : Blo 179801 1040647 := bstep (se 1 (by rfl) ⟨780485, by rfl⟩ : syracuseStep 1040647 = 1560971) B1560971
theorem B2189081 : Blo 179801 2189081 := bstep (se 2 (by rfl) ⟨820905, by rfl⟩ : syracuseStep 2189081 = 1641811) B1641811
theorem B3141823 : Blo 179801 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B391081 : Blo 179801 391081 := bstep (se 2 (by rfl) ⟨146655, by rfl⟩ : syracuseStep 391081 = 293311) B293311
theorem B2328335 : Blo 179801 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B271295 : Blo 179801 271295 := bstep (se 1 (by rfl) ⟨203471, by rfl⟩ : syracuseStep 271295 = 406943) B406943
theorem B271871 : Blo 179801 271871 := bstep (se 1 (by rfl) ⟨203903, by rfl⟩ : syracuseStep 271871 = 407807) B407807
theorem B1387529 : Blo 179801 1387529 := bstep (se 2 (by rfl) ⟨520323, by rfl⟩ : syracuseStep 1387529 = 1040647) B1040647
theorem B668795 : Blo 179801 668795 := bstep (se 1 (by rfl) ⟨501596, by rfl⟩ : syracuseStep 668795 = 1003193) B1003193
theorem B275687 : Blo 179801 275687 := bstep (se 1 (by rfl) ⟨206765, by rfl⟩ : syracuseStep 275687 = 413531) B413531
theorem B1459387 : Blo 179801 1459387 := bstep (se 1 (by rfl) ⟨1094540, by rfl⟩ : syracuseStep 1459387 = 2189081) B2189081
theorem B4189097 : Blo 179801 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B521441 : Blo 179801 521441 := bstep (se 2 (by rfl) ⟨195540, by rfl⟩ : syracuseStep 521441 = 391081) B391081
theorem B2792731 : Blo 179801 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B925019 : Blo 179801 925019 := bstep (se 1 (by rfl) ⟨693764, by rfl⟩ : syracuseStep 925019 = 1387529) B1387529
theorem B1552223 : Blo 179801 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B1783453 : Blo 179801 1783453 := bstep (se 3 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 1783453 = 668795) B668795
theorem B180863 : Blo 179801 180863 := bstep (se 1 (by rfl) ⟨135647, by rfl⟩ : syracuseStep 180863 = 271295) B271295
theorem B7783397 : Blo 179801 7783397 := bstep (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) B1459387
theorem B181247 : Blo 179801 181247 := bstep (se 1 (by rfl) ⟨135935, by rfl⟩ : syracuseStep 181247 = 271871) B271871
theorem B347627 : Blo 179801 347627 := bstep (se 1 (by rfl) ⟨260720, by rfl⟩ : syracuseStep 347627 = 521441) B521441
theorem B183791 : Blo 179801 183791 := bstep (se 1 (by rfl) ⟨137843, by rfl⟩ : syracuseStep 183791 = 275687) B275687
theorem B231751 : Blo 179801 231751 := bstep (se 1 (by rfl) ⟨173813, by rfl⟩ : syracuseStep 231751 = 347627) B347627
theorem B5188931 : Blo 179801 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B2377937 : Blo 179801 2377937 := bstep (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) B1783453
theorem B1034815 : Blo 179801 1034815 := bstep (se 1 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 1034815 = 1552223) B1552223
theorem B3723641 : Blo 179801 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B616679 : Blo 179801 616679 := bstep (se 1 (by rfl) ⟨462509, by rfl⟩ : syracuseStep 616679 = 925019) B925019
theorem B1379753 : Blo 179801 1379753 := bstep (se 2 (by rfl) ⟨517407, by rfl⟩ : syracuseStep 1379753 = 1034815) B1034815
theorem B1585291 : Blo 179801 1585291 := bstep (se 1 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 1585291 = 2377937) B2377937
theorem B309001 : Blo 179801 309001 := bstep (se 2 (by rfl) ⟨115875, by rfl⟩ : syracuseStep 309001 = 231751) B231751
theorem B411119 : Blo 179801 411119 := bstep (se 1 (by rfl) ⟨308339, by rfl⟩ : syracuseStep 411119 = 616679) B616679
theorem B3459287 : Blo 179801 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B2482427 : Blo 179801 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B919835 : Blo 179801 919835 := bstep (se 1 (by rfl) ⟨689876, by rfl⟩ : syracuseStep 919835 = 1379753) B1379753
theorem B274079 : Blo 179801 274079 := bstep (se 1 (by rfl) ⟨205559, by rfl⟩ : syracuseStep 274079 = 411119) B411119
theorem B2306191 : Blo 179801 2306191 := bstep (se 1 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 2306191 = 3459287) B3459287
theorem B1654951 : Blo 179801 1654951 := bstep (se 1 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 1654951 = 2482427) B2482427
theorem B2113721 : Blo 179801 2113721 := bstep (se 2 (by rfl) ⟨792645, by rfl⟩ : syracuseStep 2113721 = 1585291) B1585291
theorem B412001 : Blo 179801 412001 := bstep (se 2 (by rfl) ⟨154500, by rfl⟩ : syracuseStep 412001 = 309001) B309001
theorem B1409147 : Blo 179801 1409147 := bstep (se 1 (by rfl) ⟨1056860, by rfl⟩ : syracuseStep 1409147 = 2113721) B2113721
theorem B2206601 : Blo 179801 2206601 := bstep (se 2 (by rfl) ⟨827475, by rfl⟩ : syracuseStep 2206601 = 1654951) B1654951
theorem B274667 : Blo 179801 274667 := bstep (se 1 (by rfl) ⟨206000, by rfl⟩ : syracuseStep 274667 = 412001) B412001
theorem B182719 : Blo 179801 182719 := bstep (se 1 (by rfl) ⟨137039, by rfl⟩ : syracuseStep 182719 = 274079) B274079
theorem B613223 : Blo 179801 613223 := bstep (se 1 (by rfl) ⟨459917, by rfl⟩ : syracuseStep 613223 = 919835) B919835
theorem B3074921 : Blo 179801 3074921 := bstep (se 2 (by rfl) ⟨1153095, by rfl⟩ : syracuseStep 3074921 = 2306191) B2306191
theorem B408815 : Blo 179801 408815 := bstep (se 1 (by rfl) ⟨306611, by rfl⟩ : syracuseStep 408815 = 613223) B613223
theorem B2049947 : Blo 179801 2049947 := bstep (se 1 (by rfl) ⟨1537460, by rfl⟩ : syracuseStep 2049947 = 3074921) B3074921
theorem B183111 : Blo 179801 183111 := bstep (se 1 (by rfl) ⟨137333, by rfl⟩ : syracuseStep 183111 = 274667) B274667
theorem B939431 : Blo 179801 939431 := bstep (se 1 (by rfl) ⟨704573, by rfl⟩ : syracuseStep 939431 = 1409147) B1409147
theorem B1471067 : Blo 179801 1471067 := bstep (se 1 (by rfl) ⟨1103300, by rfl⟩ : syracuseStep 1471067 = 2206601) B2206601
theorem B626287 : Blo 179801 626287 := bstep (se 1 (by rfl) ⟨469715, by rfl⟩ : syracuseStep 626287 = 939431) B939431
theorem B272543 : Blo 179801 272543 := bstep (se 1 (by rfl) ⟨204407, by rfl⟩ : syracuseStep 272543 = 408815) B408815
theorem B1366631 : Blo 179801 1366631 := bstep (se 1 (by rfl) ⟨1024973, by rfl⟩ : syracuseStep 1366631 = 2049947) B2049947
theorem B980711 : Blo 179801 980711 := bstep (se 1 (by rfl) ⟨735533, by rfl⟩ : syracuseStep 980711 = 1471067) B1471067
theorem B835049 : Blo 179801 835049 := bstep (se 2 (by rfl) ⟨313143, by rfl⟩ : syracuseStep 835049 = 626287) B626287
theorem B181695 : Blo 179801 181695 := bstep (se 1 (by rfl) ⟨136271, by rfl⟩ : syracuseStep 181695 = 272543) B272543
theorem B911087 : Blo 179801 911087 := bstep (se 1 (by rfl) ⟨683315, by rfl⟩ : syracuseStep 911087 = 1366631) B1366631
theorem B653807 : Blo 179801 653807 := bstep (se 1 (by rfl) ⟨490355, by rfl⟩ : syracuseStep 653807 = 980711) B980711
theorem B435871 : Blo 179801 435871 := bstep (se 1 (by rfl) ⟨326903, by rfl⟩ : syracuseStep 435871 = 653807) B653807
theorem B607391 : Blo 179801 607391 := bstep (se 1 (by rfl) ⟨455543, by rfl⟩ : syracuseStep 607391 = 911087) B911087
theorem B556699 : Blo 179801 556699 := bstep (se 1 (by rfl) ⟨417524, by rfl⟩ : syracuseStep 556699 = 835049) B835049
theorem B404927 : Blo 179801 404927 := bstep (se 1 (by rfl) ⟨303695, by rfl⟩ : syracuseStep 404927 = 607391) B607391
theorem B742265 : Blo 179801 742265 := bstep (se 2 (by rfl) ⟨278349, by rfl⟩ : syracuseStep 742265 = 556699) B556699
theorem B2324645 : Blo 179801 2324645 := bstep (se 4 (by rfl) ⟨217935, by rfl⟩ : syracuseStep 2324645 = 435871) B435871
theorem B494843 : Blo 179801 494843 := bstep (se 1 (by rfl) ⟨371132, by rfl⟩ : syracuseStep 494843 = 742265) B742265
theorem B269951 : Blo 179801 269951 := bstep (se 1 (by rfl) ⟨202463, by rfl⟩ : syracuseStep 269951 = 404927) B404927
theorem B1549763 : Blo 179801 1549763 := bstep (se 1 (by rfl) ⟨1162322, by rfl⟩ : syracuseStep 1549763 = 2324645) B2324645
theorem B1319581 : Blo 179801 1319581 := bstep (se 3 (by rfl) ⟨247421, by rfl⟩ : syracuseStep 1319581 = 494843) B494843
theorem B179967 : Blo 179801 179967 := bstep (se 1 (by rfl) ⟨134975, by rfl⟩ : syracuseStep 179967 = 269951) B269951
theorem B1033175 : Blo 179801 1033175 := bstep (se 1 (by rfl) ⟨774881, by rfl⟩ : syracuseStep 1033175 = 1549763) B1549763
theorem B688783 : Blo 179801 688783 := bstep (se 1 (by rfl) ⟨516587, by rfl⟩ : syracuseStep 688783 = 1033175) B1033175
theorem B1759441 : Blo 179801 1759441 := bstep (se 2 (by rfl) ⟨659790, by rfl⟩ : syracuseStep 1759441 = 1319581) B1319581
theorem B918377 : Blo 179801 918377 := bstep (se 2 (by rfl) ⟨344391, by rfl⟩ : syracuseStep 918377 = 688783) B688783
theorem B2345921 : Blo 179801 2345921 := bstep (se 2 (by rfl) ⟨879720, by rfl⟩ : syracuseStep 2345921 = 1759441) B1759441
theorem B612251 : Blo 179801 612251 := bstep (se 1 (by rfl) ⟨459188, by rfl⟩ : syracuseStep 612251 = 918377) B918377
theorem B1563947 : Blo 179801 1563947 := bstep (se 1 (by rfl) ⟨1172960, by rfl⟩ : syracuseStep 1563947 = 2345921) B2345921
theorem B408167 : Blo 179801 408167 := bstep (se 1 (by rfl) ⟨306125, by rfl⟩ : syracuseStep 408167 = 612251) B612251
theorem B1042631 : Blo 179801 1042631 := bstep (se 1 (by rfl) ⟨781973, by rfl⟩ : syracuseStep 1042631 = 1563947) B1563947
theorem B695087 : Blo 179801 695087 := bstep (se 1 (by rfl) ⟨521315, by rfl⟩ : syracuseStep 695087 = 1042631) B1042631
theorem B272111 : Blo 179801 272111 := bstep (se 1 (by rfl) ⟨204083, by rfl⟩ : syracuseStep 272111 = 408167) B408167
theorem B463391 : Blo 179801 463391 := bstep (se 1 (by rfl) ⟨347543, by rfl⟩ : syracuseStep 463391 = 695087) B695087
theorem B181407 : Blo 179801 181407 := bstep (se 1 (by rfl) ⟨136055, by rfl⟩ : syracuseStep 181407 = 272111) B272111
theorem B308927 : Blo 179801 308927 := bstep (se 1 (by rfl) ⟨231695, by rfl⟩ : syracuseStep 308927 = 463391) B463391
theorem B205951 : Blo 179801 205951 := bstep (se 1 (by rfl) ⟨154463, by rfl⟩ : syracuseStep 205951 = 308927) B308927
theorem B274601 : Blo 179801 274601 := bstep (se 2 (by rfl) ⟨102975, by rfl⟩ : syracuseStep 274601 = 205951) B205951
theorem B183067 : Blo 179801 183067 := bstep (se 1 (by rfl) ⟨137300, by rfl⟩ : syracuseStep 183067 = 274601) B274601

theorem C0 (j : ℕ) (h1 : 44950 ≤ j) (h2 : j ≤ 45649) : Blo 179801 (4 * j + 3) := by
  interval_cases j
  · exact B179803
  · exact B179807
  · exact B179811
  · exact B179815
  · exact B179819
  · exact B179823
  · exact B179827
  · exact B179831
  · exact B179835
  · exact B179839
  · exact B179843
  · exact B179847
  · exact B179851
  · exact B179855
  · exact B179859
  · exact B179863
  · exact B179867
  · exact B179871
  · exact B179875
  · exact B179879
  · exact B179883
  · exact B179887
  · exact B179891
  · exact B179895
  · exact B179899
  · exact B179903
  · exact B179907
  · exact B179911
  · exact B179915
  · exact B179919
  · exact B179923
  · exact B179927
  · exact B179931
  · exact B179935
  · exact B179939
  · exact B179943
  · exact B179947
  · exact B179951
  · exact B179955
  · exact B179959
  · exact B179963
  · exact B179967
  · exact B179971
  · exact B179975
  · exact B179979
  · exact B179983
  · exact B179987
  · exact B179991
  · exact B179995
  · exact B179999
  · exact B180003
  · exact B180007
  · exact B180011
  · exact B180015
  · exact B180019
  · exact B180023
  · exact B180027
  · exact B180031
  · exact B180035
  · exact B180039
  · exact B180043
  · exact B180047
  · exact B180051
  · exact B180055
  · exact B180059
  · exact B180063
  · exact B180067
  · exact B180071
  · exact B180075
  · exact B180079
  · exact B180083
  · exact B180087
  · exact B180091
  · exact B180095
  · exact B180099
  · exact B180103
  · exact B180107
  · exact B180111
  · exact B180115
  · exact B180119
  · exact B180123
  · exact B180127
  · exact B180131
  · exact B180135
  · exact B180139
  · exact B180143
  · exact B180147
  · exact B180151
  · exact B180155
  · exact B180159
  · exact B180163
  · exact B180167
  · exact B180171
  · exact B180175
  · exact B180179
  · exact B180183
  · exact B180187
  · exact B180191
  · exact B180195
  · exact B180199
  · exact B180203
  · exact B180207
  · exact B180211
  · exact B180215
  · exact B180219
  · exact B180223
  · exact B180227
  · exact B180231
  · exact B180235
  · exact B180239
  · exact B180243
  · exact B180247
  · exact B180251
  · exact B180255
  · exact B180259
  · exact B180263
  · exact B180267
  · exact B180271
  · exact B180275
  · exact B180279
  · exact B180283
  · exact B180287
  · exact B180291
  · exact B180295
  · exact B180299
  · exact B180303
  · exact B180307
  · exact B180311
  · exact B180315
  · exact B180319
  · exact B180323
  · exact B180327
  · exact B180331
  · exact B180335
  · exact B180339
  · exact B180343
  · exact B180347
  · exact B180351
  · exact B180355
  · exact B180359
  · exact B180363
  · exact B180367
  · exact B180371
  · exact B180375
  · exact B180379
  · exact B180383
  · exact B180387
  · exact B180391
  · exact B180395
  · exact B180399
  · exact B180403
  · exact B180407
  · exact B180411
  · exact B180415
  · exact B180419
  · exact B180423
  · exact B180427
  · exact B180431
  · exact B180435
  · exact B180439
  · exact B180443
  · exact B180447
  · exact B180451
  · exact B180455
  · exact B180459
  · exact B180463
  · exact B180467
  · exact B180471
  · exact B180475
  · exact B180479
  · exact B180483
  · exact B180487
  · exact B180491
  · exact B180495
  · exact B180499
  · exact B180503
  · exact B180507
  · exact B180511
  · exact B180515
  · exact B180519
  · exact B180523
  · exact B180527
  · exact B180531
  · exact B180535
  · exact B180539
  · exact B180543
  · exact B180547
  · exact B180551
  · exact B180555
  · exact B180559
  · exact B180563
  · exact B180567
  · exact B180571
  · exact B180575
  · exact B180579
  · exact B180583
  · exact B180587
  · exact B180591
  · exact B180595
  · exact B180599
  · exact B180603
  · exact B180607
  · exact B180611
  · exact B180615
  · exact B180619
  · exact B180623
  · exact B180627
  · exact B180631
  · exact B180635
  · exact B180639
  · exact B180643
  · exact B180647
  · exact B180651
  · exact B180655
  · exact B180659
  · exact B180663
  · exact B180667
  · exact B180671
  · exact B180675
  · exact B180679
  · exact B180683
  · exact B180687
  · exact B180691
  · exact B180695
  · exact B180699
  · exact B180703
  · exact B180707
  · exact B180711
  · exact B180715
  · exact B180719
  · exact B180723
  · exact B180727
  · exact B180731
  · exact B180735
  · exact B180739
  · exact B180743
  · exact B180747
  · exact B180751
  · exact B180755
  · exact B180759
  · exact B180763
  · exact B180767
  · exact B180771
  · exact B180775
  · exact B180779
  · exact B180783
  · exact B180787
  · exact B180791
  · exact B180795
  · exact B180799
  · exact B180803
  · exact B180807
  · exact B180811
  · exact B180815
  · exact B180819
  · exact B180823
  · exact B180827
  · exact B180831
  · exact B180835
  · exact B180839
  · exact B180843
  · exact B180847
  · exact B180851
  · exact B180855
  · exact B180859
  · exact B180863
  · exact B180867
  · exact B180871
  · exact B180875
  · exact B180879
  · exact B180883
  · exact B180887
  · exact B180891
  · exact B180895
  · exact B180899
  · exact B180903
  · exact B180907
  · exact B180911
  · exact B180915
  · exact B180919
  · exact B180923
  · exact B180927
  · exact B180931
  · exact B180935
  · exact B180939
  · exact B180943
  · exact B180947
  · exact B180951
  · exact B180955
  · exact B180959
  · exact B180963
  · exact B180967
  · exact B180971
  · exact B180975
  · exact B180979
  · exact B180983
  · exact B180987
  · exact B180991
  · exact B180995
  · exact B180999
  · exact B181003
  · exact B181007
  · exact B181011
  · exact B181015
  · exact B181019
  · exact B181023
  · exact B181027
  · exact B181031
  · exact B181035
  · exact B181039
  · exact B181043
  · exact B181047
  · exact B181051
  · exact B181055
  · exact B181059
  · exact B181063
  · exact B181067
  · exact B181071
  · exact B181075
  · exact B181079
  · exact B181083
  · exact B181087
  · exact B181091
  · exact B181095
  · exact B181099
  · exact B181103
  · exact B181107
  · exact B181111
  · exact B181115
  · exact B181119
  · exact B181123
  · exact B181127
  · exact B181131
  · exact B181135
  · exact B181139
  · exact B181143
  · exact B181147
  · exact B181151
  · exact B181155
  · exact B181159
  · exact B181163
  · exact B181167
  · exact B181171
  · exact B181175
  · exact B181179
  · exact B181183
  · exact B181187
  · exact B181191
  · exact B181195
  · exact B181199
  · exact B181203
  · exact B181207
  · exact B181211
  · exact B181215
  · exact B181219
  · exact B181223
  · exact B181227
  · exact B181231
  · exact B181235
  · exact B181239
  · exact B181243
  · exact B181247
  · exact B181251
  · exact B181255
  · exact B181259
  · exact B181263
  · exact B181267
  · exact B181271
  · exact B181275
  · exact B181279
  · exact B181283
  · exact B181287
  · exact B181291
  · exact B181295
  · exact B181299
  · exact B181303
  · exact B181307
  · exact B181311
  · exact B181315
  · exact B181319
  · exact B181323
  · exact B181327
  · exact B181331
  · exact B181335
  · exact B181339
  · exact B181343
  · exact B181347
  · exact B181351
  · exact B181355
  · exact B181359
  · exact B181363
  · exact B181367
  · exact B181371
  · exact B181375
  · exact B181379
  · exact B181383
  · exact B181387
  · exact B181391
  · exact B181395
  · exact B181399
  · exact B181403
  · exact B181407
  · exact B181411
  · exact B181415
  · exact B181419
  · exact B181423
  · exact B181427
  · exact B181431
  · exact B181435
  · exact B181439
  · exact B181443
  · exact B181447
  · exact B181451
  · exact B181455
  · exact B181459
  · exact B181463
  · exact B181467
  · exact B181471
  · exact B181475
  · exact B181479
  · exact B181483
  · exact B181487
  · exact B181491
  · exact B181495
  · exact B181499
  · exact B181503
  · exact B181507
  · exact B181511
  · exact B181515
  · exact B181519
  · exact B181523
  · exact B181527
  · exact B181531
  · exact B181535
  · exact B181539
  · exact B181543
  · exact B181547
  · exact B181551
  · exact B181555
  · exact B181559
  · exact B181563
  · exact B181567
  · exact B181571
  · exact B181575
  · exact B181579
  · exact B181583
  · exact B181587
  · exact B181591
  · exact B181595
  · exact B181599
  · exact B181603
  · exact B181607
  · exact B181611
  · exact B181615
  · exact B181619
  · exact B181623
  · exact B181627
  · exact B181631
  · exact B181635
  · exact B181639
  · exact B181643
  · exact B181647
  · exact B181651
  · exact B181655
  · exact B181659
  · exact B181663
  · exact B181667
  · exact B181671
  · exact B181675
  · exact B181679
  · exact B181683
  · exact B181687
  · exact B181691
  · exact B181695
  · exact B181699
  · exact B181703
  · exact B181707
  · exact B181711
  · exact B181715
  · exact B181719
  · exact B181723
  · exact B181727
  · exact B181731
  · exact B181735
  · exact B181739
  · exact B181743
  · exact B181747
  · exact B181751
  · exact B181755
  · exact B181759
  · exact B181763
  · exact B181767
  · exact B181771
  · exact B181775
  · exact B181779
  · exact B181783
  · exact B181787
  · exact B181791
  · exact B181795
  · exact B181799
  · exact B181803
  · exact B181807
  · exact B181811
  · exact B181815
  · exact B181819
  · exact B181823
  · exact B181827
  · exact B181831
  · exact B181835
  · exact B181839
  · exact B181843
  · exact B181847
  · exact B181851
  · exact B181855
  · exact B181859
  · exact B181863
  · exact B181867
  · exact B181871
  · exact B181875
  · exact B181879
  · exact B181883
  · exact B181887
  · exact B181891
  · exact B181895
  · exact B181899
  · exact B181903
  · exact B181907
  · exact B181911
  · exact B181915
  · exact B181919
  · exact B181923
  · exact B181927
  · exact B181931
  · exact B181935
  · exact B181939
  · exact B181943
  · exact B181947
  · exact B181951
  · exact B181955
  · exact B181959
  · exact B181963
  · exact B181967
  · exact B181971
  · exact B181975
  · exact B181979
  · exact B181983
  · exact B181987
  · exact B181991
  · exact B181995
  · exact B181999
  · exact B182003
  · exact B182007
  · exact B182011
  · exact B182015
  · exact B182019
  · exact B182023
  · exact B182027
  · exact B182031
  · exact B182035
  · exact B182039
  · exact B182043
  · exact B182047
  · exact B182051
  · exact B182055
  · exact B182059
  · exact B182063
  · exact B182067
  · exact B182071
  · exact B182075
  · exact B182079
  · exact B182083
  · exact B182087
  · exact B182091
  · exact B182095
  · exact B182099
  · exact B182103
  · exact B182107
  · exact B182111
  · exact B182115
  · exact B182119
  · exact B182123
  · exact B182127
  · exact B182131
  · exact B182135
  · exact B182139
  · exact B182143
  · exact B182147
  · exact B182151
  · exact B182155
  · exact B182159
  · exact B182163
  · exact B182167
  · exact B182171
  · exact B182175
  · exact B182179
  · exact B182183
  · exact B182187
  · exact B182191
  · exact B182195
  · exact B182199
  · exact B182203
  · exact B182207
  · exact B182211
  · exact B182215
  · exact B182219
  · exact B182223
  · exact B182227
  · exact B182231
  · exact B182235
  · exact B182239
  · exact B182243
  · exact B182247
  · exact B182251
  · exact B182255
  · exact B182259
  · exact B182263
  · exact B182267
  · exact B182271
  · exact B182275
  · exact B182279
  · exact B182283
  · exact B182287
  · exact B182291
  · exact B182295
  · exact B182299
  · exact B182303
  · exact B182307
  · exact B182311
  · exact B182315
  · exact B182319
  · exact B182323
  · exact B182327
  · exact B182331
  · exact B182335
  · exact B182339
  · exact B182343
  · exact B182347
  · exact B182351
  · exact B182355
  · exact B182359
  · exact B182363
  · exact B182367
  · exact B182371
  · exact B182375
  · exact B182379
  · exact B182383
  · exact B182387
  · exact B182391
  · exact B182395
  · exact B182399
  · exact B182403
  · exact B182407
  · exact B182411
  · exact B182415
  · exact B182419
  · exact B182423
  · exact B182427
  · exact B182431
  · exact B182435
  · exact B182439
  · exact B182443
  · exact B182447
  · exact B182451
  · exact B182455
  · exact B182459
  · exact B182463
  · exact B182467
  · exact B182471
  · exact B182475
  · exact B182479
  · exact B182483
  · exact B182487
  · exact B182491
  · exact B182495
  · exact B182499
  · exact B182503
  · exact B182507
  · exact B182511
  · exact B182515
  · exact B182519
  · exact B182523
  · exact B182527
  · exact B182531
  · exact B182535
  · exact B182539
  · exact B182543
  · exact B182547
  · exact B182551
  · exact B182555
  · exact B182559
  · exact B182563
  · exact B182567
  · exact B182571
  · exact B182575
  · exact B182579
  · exact B182583
  · exact B182587
  · exact B182591
  · exact B182595
  · exact B182599

theorem C1 (j : ℕ) (h1 : 45650 ≤ j) (h2 : j ≤ 45949) : Blo 179801 (4 * j + 3) := by
  interval_cases j
  · exact B182603
  · exact B182607
  · exact B182611
  · exact B182615
  · exact B182619
  · exact B182623
  · exact B182627
  · exact B182631
  · exact B182635
  · exact B182639
  · exact B182643
  · exact B182647
  · exact B182651
  · exact B182655
  · exact B182659
  · exact B182663
  · exact B182667
  · exact B182671
  · exact B182675
  · exact B182679
  · exact B182683
  · exact B182687
  · exact B182691
  · exact B182695
  · exact B182699
  · exact B182703
  · exact B182707
  · exact B182711
  · exact B182715
  · exact B182719
  · exact B182723
  · exact B182727
  · exact B182731
  · exact B182735
  · exact B182739
  · exact B182743
  · exact B182747
  · exact B182751
  · exact B182755
  · exact B182759
  · exact B182763
  · exact B182767
  · exact B182771
  · exact B182775
  · exact B182779
  · exact B182783
  · exact B182787
  · exact B182791
  · exact B182795
  · exact B182799
  · exact B182803
  · exact B182807
  · exact B182811
  · exact B182815
  · exact B182819
  · exact B182823
  · exact B182827
  · exact B182831
  · exact B182835
  · exact B182839
  · exact B182843
  · exact B182847
  · exact B182851
  · exact B182855
  · exact B182859
  · exact B182863
  · exact B182867
  · exact B182871
  · exact B182875
  · exact B182879
  · exact B182883
  · exact B182887
  · exact B182891
  · exact B182895
  · exact B182899
  · exact B182903
  · exact B182907
  · exact B182911
  · exact B182915
  · exact B182919
  · exact B182923
  · exact B182927
  · exact B182931
  · exact B182935
  · exact B182939
  · exact B182943
  · exact B182947
  · exact B182951
  · exact B182955
  · exact B182959
  · exact B182963
  · exact B182967
  · exact B182971
  · exact B182975
  · exact B182979
  · exact B182983
  · exact B182987
  · exact B182991
  · exact B182995
  · exact B182999
  · exact B183003
  · exact B183007
  · exact B183011
  · exact B183015
  · exact B183019
  · exact B183023
  · exact B183027
  · exact B183031
  · exact B183035
  · exact B183039
  · exact B183043
  · exact B183047
  · exact B183051
  · exact B183055
  · exact B183059
  · exact B183063
  · exact B183067
  · exact B183071
  · exact B183075
  · exact B183079
  · exact B183083
  · exact B183087
  · exact B183091
  · exact B183095
  · exact B183099
  · exact B183103
  · exact B183107
  · exact B183111
  · exact B183115
  · exact B183119
  · exact B183123
  · exact B183127
  · exact B183131
  · exact B183135
  · exact B183139
  · exact B183143
  · exact B183147
  · exact B183151
  · exact B183155
  · exact B183159
  · exact B183163
  · exact B183167
  · exact B183171
  · exact B183175
  · exact B183179
  · exact B183183
  · exact B183187
  · exact B183191
  · exact B183195
  · exact B183199
  · exact B183203
  · exact B183207
  · exact B183211
  · exact B183215
  · exact B183219
  · exact B183223
  · exact B183227
  · exact B183231
  · exact B183235
  · exact B183239
  · exact B183243
  · exact B183247
  · exact B183251
  · exact B183255
  · exact B183259
  · exact B183263
  · exact B183267
  · exact B183271
  · exact B183275
  · exact B183279
  · exact B183283
  · exact B183287
  · exact B183291
  · exact B183295
  · exact B183299
  · exact B183303
  · exact B183307
  · exact B183311
  · exact B183315
  · exact B183319
  · exact B183323
  · exact B183327
  · exact B183331
  · exact B183335
  · exact B183339
  · exact B183343
  · exact B183347
  · exact B183351
  · exact B183355
  · exact B183359
  · exact B183363
  · exact B183367
  · exact B183371
  · exact B183375
  · exact B183379
  · exact B183383
  · exact B183387
  · exact B183391
  · exact B183395
  · exact B183399
  · exact B183403
  · exact B183407
  · exact B183411
  · exact B183415
  · exact B183419
  · exact B183423
  · exact B183427
  · exact B183431
  · exact B183435
  · exact B183439
  · exact B183443
  · exact B183447
  · exact B183451
  · exact B183455
  · exact B183459
  · exact B183463
  · exact B183467
  · exact B183471
  · exact B183475
  · exact B183479
  · exact B183483
  · exact B183487
  · exact B183491
  · exact B183495
  · exact B183499
  · exact B183503
  · exact B183507
  · exact B183511
  · exact B183515
  · exact B183519
  · exact B183523
  · exact B183527
  · exact B183531
  · exact B183535
  · exact B183539
  · exact B183543
  · exact B183547
  · exact B183551
  · exact B183555
  · exact B183559
  · exact B183563
  · exact B183567
  · exact B183571
  · exact B183575
  · exact B183579
  · exact B183583
  · exact B183587
  · exact B183591
  · exact B183595
  · exact B183599
  · exact B183603
  · exact B183607
  · exact B183611
  · exact B183615
  · exact B183619
  · exact B183623
  · exact B183627
  · exact B183631
  · exact B183635
  · exact B183639
  · exact B183643
  · exact B183647
  · exact B183651
  · exact B183655
  · exact B183659
  · exact B183663
  · exact B183667
  · exact B183671
  · exact B183675
  · exact B183679
  · exact B183683
  · exact B183687
  · exact B183691
  · exact B183695
  · exact B183699
  · exact B183703
  · exact B183707
  · exact B183711
  · exact B183715
  · exact B183719
  · exact B183723
  · exact B183727
  · exact B183731
  · exact B183735
  · exact B183739
  · exact B183743
  · exact B183747
  · exact B183751
  · exact B183755
  · exact B183759
  · exact B183763
  · exact B183767
  · exact B183771
  · exact B183775
  · exact B183779
  · exact B183783
  · exact B183787
  · exact B183791
  · exact B183795
  · exact B183799

theorem solution (m : ℕ) (hlo : 179801 ≤ m) (hhi : m ≤ 183801) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 44950 ≤ j := by omega
    have hj2 : j ≤ 45949 := by omega
    have hb : Blo 179801 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 45650 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
