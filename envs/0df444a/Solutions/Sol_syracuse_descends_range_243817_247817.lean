-- Prove2me | solution 1 for syracuse_descends_range_243817_247817
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:01.385138+00:00
-- url     : https://prove2.me/submissions/3e859401-bced-4ef6-9e28-0e45e72a8f9a

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


theorem B589837 : Blo 243817 589837 := bbase (se 3 (by rfl) ⟨110594, by rfl⟩ : syracuseStep 589837 = 221189) (by norm_num)
theorem B393245 : Blo 243817 393245 := bbase (se 3 (by rfl) ⟨73733, by rfl⟩ : syracuseStep 393245 = 147467) (by norm_num)
theorem B622637 : Blo 243817 622637 := bbase (se 3 (by rfl) ⟨116744, by rfl⟩ : syracuseStep 622637 = 233489) (by norm_num)
theorem B262201 : Blo 243817 262201 := bbase (se 2 (by rfl) ⟨98325, by rfl⟩ : syracuseStep 262201 = 196651) (by norm_num)
theorem B557117 : Blo 243817 557117 := bbase (se 3 (by rfl) ⟨104459, by rfl⟩ : syracuseStep 557117 = 208919) (by norm_num)
theorem B557189 : Blo 243817 557189 := bbase (se 4 (by rfl) ⟨52236, by rfl⟩ : syracuseStep 557189 = 104473) (by norm_num)
theorem B295049 : Blo 243817 295049 := bbase (se 2 (by rfl) ⟨110643, by rfl⟩ : syracuseStep 295049 = 221287) (by norm_num)
theorem B557261 : Blo 243817 557261 := bbase (se 3 (by rfl) ⟨104486, by rfl⟩ : syracuseStep 557261 = 208973) (by norm_num)
theorem B622829 : Blo 243817 622829 := bbase (se 3 (by rfl) ⟨116780, by rfl⟩ : syracuseStep 622829 = 233561) (by norm_num)
theorem B557333 : Blo 243817 557333 := bbase (se 6 (by rfl) ⟨13062, by rfl⟩ : syracuseStep 557333 = 26125) (by norm_num)
theorem B524573 : Blo 243817 524573 := bbase (se 3 (by rfl) ⟨98357, by rfl⟩ : syracuseStep 524573 = 196715) (by norm_num)
theorem B557405 : Blo 243817 557405 := bbase (se 3 (by rfl) ⟨104513, by rfl⟩ : syracuseStep 557405 = 209027) (by norm_num)
theorem B524693 : Blo 243817 524693 := bbase (se 6 (by rfl) ⟨12297, by rfl⟩ : syracuseStep 524693 = 24595) (by norm_num)
theorem B557477 : Blo 243817 557477 := bbase (se 4 (by rfl) ⟨52263, by rfl⟩ : syracuseStep 557477 = 104527) (by norm_num)
theorem B557549 : Blo 243817 557549 := bbase (se 3 (by rfl) ⟨104540, by rfl⟩ : syracuseStep 557549 = 209081) (by norm_num)
theorem B262645 : Blo 243817 262645 := bbase (se 5 (by rfl) ⟨12311, by rfl⟩ : syracuseStep 262645 = 24623) (by norm_num)
theorem B787013 : Blo 243817 787013 := bbase (se 4 (by rfl) ⟨73782, by rfl⟩ : syracuseStep 787013 = 147565) (by norm_num)
theorem B623173 : Blo 243817 623173 := bbase (se 4 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 623173 = 116845) (by norm_num)
theorem B262765 : Blo 243817 262765 := bbase (se 3 (by rfl) ⟨49268, by rfl⟩ : syracuseStep 262765 = 98537) (by norm_num)
theorem B590453 : Blo 243817 590453 := bbase (se 5 (by rfl) ⟨27677, by rfl⟩ : syracuseStep 590453 = 55355) (by norm_num)
theorem B623285 : Blo 243817 623285 := bbase (se 5 (by rfl) ⟨29216, by rfl⟩ : syracuseStep 623285 = 58433) (by norm_num)
theorem B1245941 : Blo 243817 1245941 := bbase (se 5 (by rfl) ⟨58403, by rfl⟩ : syracuseStep 1245941 = 116807) (by norm_num)
theorem B590645 : Blo 243817 590645 := bbase (se 5 (by rfl) ⟨27686, by rfl⟩ : syracuseStep 590645 = 55373) (by norm_num)
theorem B295741 : Blo 243817 295741 := bbase (se 3 (by rfl) ⟨55451, by rfl⟩ : syracuseStep 295741 = 110903) (by norm_num)
theorem B295745 : Blo 243817 295745 := bbase (se 2 (by rfl) ⟨110904, by rfl⟩ : syracuseStep 295745 = 221809) (by norm_num)
theorem B263017 : Blo 243817 263017 := bbase (se 2 (by rfl) ⟨98631, by rfl⟩ : syracuseStep 263017 = 197263) (by norm_num)
theorem B263021 : Blo 243817 263021 := bbase (se 3 (by rfl) ⟨49316, by rfl⟩ : syracuseStep 263021 = 98633) (by norm_num)
theorem B623477 : Blo 243817 623477 := bbase (se 5 (by rfl) ⟨29225, by rfl⟩ : syracuseStep 623477 = 58451) (by norm_num)
theorem B590741 : Blo 243817 590741 := bbase (se 6 (by rfl) ⟨13845, by rfl⟩ : syracuseStep 590741 = 27691) (by norm_num)
theorem B394237 : Blo 243817 394237 := bbase (se 3 (by rfl) ⟨73919, by rfl⟩ : syracuseStep 394237 = 147839) (by norm_num)
theorem B525325 : Blo 243817 525325 := bbase (se 3 (by rfl) ⟨98498, by rfl⟩ : syracuseStep 525325 = 196997) (by norm_num)
theorem B623821 : Blo 243817 623821 := bbase (se 3 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 623821 = 233933) (by norm_num)
theorem B886069 : Blo 243817 886069 := bbase (se 5 (by rfl) ⟨41534, by rfl⟩ : syracuseStep 886069 = 83069) (by norm_num)
theorem B296245 : Blo 243817 296245 := bbase (se 5 (by rfl) ⟨13886, by rfl⟩ : syracuseStep 296245 = 27773) (by norm_num)
theorem B623933 : Blo 243817 623933 := bbase (se 3 (by rfl) ⟨116987, by rfl⟩ : syracuseStep 623933 = 233975) (by norm_num)
theorem B263585 : Blo 243817 263585 := bbase (se 2 (by rfl) ⟨98844, by rfl⟩ : syracuseStep 263585 = 197689) (by norm_num)
theorem B624125 : Blo 243817 624125 := bbase (se 3 (by rfl) ⟨117023, by rfl⟩ : syracuseStep 624125 = 234047) (by norm_num)
theorem B263773 : Blo 243817 263773 := bbase (se 3 (by rfl) ⟨49457, by rfl⟩ : syracuseStep 263773 = 98915) (by norm_num)
theorem B394885 : Blo 243817 394885 := bbase (se 4 (by rfl) ⟨37020, by rfl⟩ : syracuseStep 394885 = 74041) (by norm_num)
theorem B296629 : Blo 243817 296629 := bbase (se 5 (by rfl) ⟨13904, by rfl⟩ : syracuseStep 296629 = 27809) (by norm_num)
theorem B624469 : Blo 243817 624469 := bbase (se 9 (by rfl) ⟨1829, by rfl⟩ : syracuseStep 624469 = 3659) (by norm_num)
theorem B526213 : Blo 243817 526213 := bbase (se 4 (by rfl) ⟨49332, by rfl⟩ : syracuseStep 526213 = 98665) (by norm_num)
theorem B624581 : Blo 243817 624581 := bbase (se 4 (by rfl) ⟨58554, by rfl⟩ : syracuseStep 624581 = 117109) (by norm_num)
theorem B526333 : Blo 243817 526333 := bbase (se 3 (by rfl) ⟨98687, by rfl⟩ : syracuseStep 526333 = 197375) (by norm_num)
theorem B1247237 : Blo 243817 1247237 := bbase (se 4 (by rfl) ⟨116928, by rfl⟩ : syracuseStep 1247237 = 233857) (by norm_num)
theorem B624773 : Blo 243817 624773 := bbase (se 4 (by rfl) ⟨58572, by rfl⟩ : syracuseStep 624773 = 117145) (by norm_num)
theorem B1411253 : Blo 243817 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B329941 : Blo 243817 329941 := bbase (se 7 (by rfl) ⟨3866, by rfl⟩ : syracuseStep 329941 = 7733) (by norm_num)
theorem B526589 : Blo 243817 526589 := bbase (se 3 (by rfl) ⟨98735, by rfl⟩ : syracuseStep 526589 = 197471) (by norm_num)
theorem B264593 : Blo 243817 264593 := bbase (se 2 (by rfl) ⟨99222, by rfl⟩ : syracuseStep 264593 = 198445) (by norm_num)
theorem B788885 : Blo 243817 788885 := bbase (se 6 (by rfl) ⟨18489, by rfl⟩ : syracuseStep 788885 = 36979) (by norm_num)
theorem B625117 : Blo 243817 625117 := bbase (se 3 (by rfl) ⟨117209, by rfl⟩ : syracuseStep 625117 = 234419) (by norm_num)
theorem B395813 : Blo 243817 395813 := bbase (se 4 (by rfl) ⟨37107, by rfl⟩ : syracuseStep 395813 = 74215) (by norm_num)
theorem B297533 : Blo 243817 297533 := bbase (se 3 (by rfl) ⟨55787, by rfl⟩ : syracuseStep 297533 = 111575) (by norm_num)
theorem B625229 : Blo 243817 625229 := bbase (se 3 (by rfl) ⟨117230, by rfl⟩ : syracuseStep 625229 = 234461) (by norm_num)
theorem B330421 : Blo 243817 330421 := bbase (se 5 (by rfl) ⟨15488, by rfl⟩ : syracuseStep 330421 = 30977) (by norm_num)
theorem B559813 : Blo 243817 559813 := bbase (se 4 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 559813 = 104965) (by norm_num)
theorem B625421 : Blo 243817 625421 := bbase (se 3 (by rfl) ⟨117266, by rfl⟩ : syracuseStep 625421 = 234533) (by norm_num)
theorem B1870613 : Blo 243817 1870613 := bbase (se 6 (by rfl) ⟨43842, by rfl⟩ : syracuseStep 1870613 = 87685) (by norm_num)
theorem B396269 : Blo 243817 396269 := bbase (se 3 (by rfl) ⟨74300, by rfl⟩ : syracuseStep 396269 = 148601) (by norm_num)
theorem B625765 : Blo 243817 625765 := bbase (se 4 (by rfl) ⟨58665, by rfl⟩ : syracuseStep 625765 = 117331) (by norm_num)
theorem B1510517 : Blo 243817 1510517 := bbase (se 5 (by rfl) ⟨70805, by rfl⟩ : syracuseStep 1510517 = 141611) (by norm_num)
theorem B527477 : Blo 243817 527477 := bbase (se 5 (by rfl) ⟨24725, by rfl⟩ : syracuseStep 527477 = 49451) (by norm_num)
theorem B625877 : Blo 243817 625877 := bbase (se 7 (by rfl) ⟨7334, by rfl⟩ : syracuseStep 625877 = 14669) (by norm_num)
theorem B1248533 : Blo 243817 1248533 := bbase (se 6 (by rfl) ⟨29262, by rfl⟩ : syracuseStep 1248533 = 58525) (by norm_num)
theorem B593173 : Blo 243817 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B527717 : Blo 243817 527717 := bbase (se 4 (by rfl) ⟨49473, by rfl⟩ : syracuseStep 527717 = 98947) (by norm_num)
theorem B626069 : Blo 243817 626069 := bbase (se 6 (by rfl) ⟨14673, by rfl⟩ : syracuseStep 626069 = 29347) (by norm_num)
theorem B593509 : Blo 243817 593509 := bbase (se 4 (by rfl) ⟨55641, by rfl⟩ : syracuseStep 593509 = 111283) (by norm_num)
theorem B495325 : Blo 243817 495325 := bbase (se 3 (by rfl) ⟨92873, by rfl⟩ : syracuseStep 495325 = 185747) (by norm_num)
theorem B823013 : Blo 243817 823013 := bbase (se 4 (by rfl) ⟨77157, by rfl⟩ : syracuseStep 823013 = 154315) (by norm_num)
theorem B626413 : Blo 243817 626413 := bbase (se 3 (by rfl) ⟨117452, by rfl⟩ : syracuseStep 626413 = 234905) (by norm_num)
theorem B528157 : Blo 243817 528157 := bbase (se 3 (by rfl) ⟨99029, by rfl⟩ : syracuseStep 528157 = 198059) (by norm_num)
theorem B15109973 : Blo 243817 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B528221 : Blo 243817 528221 := bbase (se 3 (by rfl) ⟨99041, by rfl⟩ : syracuseStep 528221 = 198083) (by norm_num)
theorem B626525 : Blo 243817 626525 := bbase (se 3 (by rfl) ⟨117473, by rfl⟩ : syracuseStep 626525 = 234947) (by norm_num)
theorem B528229 : Blo 243817 528229 := bbase (se 4 (by rfl) ⟨49521, by rfl⟩ : syracuseStep 528229 = 99043) (by norm_num)
theorem B561053 : Blo 243817 561053 := bbase (se 3 (by rfl) ⟨105197, by rfl⟩ : syracuseStep 561053 = 210395) (by norm_num)
theorem B266161 : Blo 243817 266161 := bbase (se 2 (by rfl) ⟨99810, by rfl⟩ : syracuseStep 266161 = 199621) (by norm_num)
theorem B626717 : Blo 243817 626717 := bbase (se 3 (by rfl) ⟨117509, by rfl⟩ : syracuseStep 626717 = 235019) (by norm_num)
theorem B888965 : Blo 243817 888965 := bbase (se 4 (by rfl) ⟨83340, by rfl⟩ : syracuseStep 888965 = 166681) (by norm_num)
theorem B823445 : Blo 243817 823445 := bbase (se 6 (by rfl) ⟨19299, by rfl⟩ : syracuseStep 823445 = 38599) (by norm_num)
theorem B1052837 : Blo 243817 1052837 := bbase (se 4 (by rfl) ⟨98703, by rfl⟩ : syracuseStep 1052837 = 197407) (by norm_num)
theorem B594125 : Blo 243817 594125 := bbase (se 3 (by rfl) ⟨111398, by rfl⟩ : syracuseStep 594125 = 222797) (by norm_num)
theorem B2265365 : Blo 243817 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B627029 : Blo 243817 627029 := bbase (se 10 (by rfl) ⟨918, by rfl⟩ : syracuseStep 627029 = 1837) (by norm_num)
theorem B2003285 : Blo 243817 2003285 := bbase (se 10 (by rfl) ⟨2934, by rfl⟩ : syracuseStep 2003285 = 5869) (by norm_num)
theorem B627061 : Blo 243817 627061 := bbase (se 5 (by rfl) ⟨29393, by rfl⟩ : syracuseStep 627061 = 58787) (by norm_num)
theorem B463333 : Blo 243817 463333 := bbase (se 4 (by rfl) ⟨43437, by rfl⟩ : syracuseStep 463333 = 86875) (by norm_num)
theorem B627173 : Blo 243817 627173 := bbase (se 4 (by rfl) ⟨58797, by rfl⟩ : syracuseStep 627173 = 117595) (by norm_num)
theorem B1249829 : Blo 243817 1249829 := bbase (se 4 (by rfl) ⟨117171, by rfl⟩ : syracuseStep 1249829 = 234343) (by norm_num)
theorem B823877 : Blo 243817 823877 := bbase (se 4 (by rfl) ⟨77238, by rfl⟩ : syracuseStep 823877 = 154477) (by norm_num)
theorem B627277 : Blo 243817 627277 := bbase (se 3 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 627277 = 235229) (by norm_num)
theorem B463477 : Blo 243817 463477 := bbase (se 5 (by rfl) ⟨21725, by rfl⟩ : syracuseStep 463477 = 43451) (by norm_num)
theorem B594557 : Blo 243817 594557 := bbase (se 3 (by rfl) ⟨111479, by rfl⟩ : syracuseStep 594557 = 222959) (by norm_num)
theorem B266965 : Blo 243817 266965 := bbase (se 7 (by rfl) ⟨3128, by rfl⟩ : syracuseStep 266965 = 6257) (by norm_num)
theorem B1577717 : Blo 243817 1577717 := bbase (se 5 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 1577717 = 147911) (by norm_num)
theorem B463637 : Blo 243817 463637 := bbase (se 6 (by rfl) ⟨10866, by rfl⟩ : syracuseStep 463637 = 21733) (by norm_num)
theorem B529237 : Blo 243817 529237 := bbase (se 9 (by rfl) ⟨1550, by rfl⟩ : syracuseStep 529237 = 3101) (by norm_num)
theorem B496469 : Blo 243817 496469 := bbase (se 9 (by rfl) ⟨1454, by rfl⟩ : syracuseStep 496469 = 2909) (by norm_num)
theorem B463781 : Blo 243817 463781 := bbase (se 4 (by rfl) ⟨43479, by rfl⟩ : syracuseStep 463781 = 86959) (by norm_num)
theorem B824309 : Blo 243817 824309 := bbase (se 5 (by rfl) ⟨38639, by rfl⟩ : syracuseStep 824309 = 77279) (by norm_num)
theorem B791653 : Blo 243817 791653 := bbase (se 4 (by rfl) ⟨74217, by rfl⟩ : syracuseStep 791653 = 148435) (by norm_num)
theorem B365741 : Blo 243817 365741 := bbase (se 3 (by rfl) ⟨68576, by rfl⟩ : syracuseStep 365741 = 137153) (by norm_num)
theorem B365765 : Blo 243817 365765 := bbase (se 4 (by rfl) ⟨34290, by rfl⟩ : syracuseStep 365765 = 68581) (by norm_num)
theorem B464069 : Blo 243817 464069 := bbase (se 4 (by rfl) ⟨43506, by rfl⟩ : syracuseStep 464069 = 87013) (by norm_num)
theorem B365789 : Blo 243817 365789 := bbase (se 3 (by rfl) ⟨68585, by rfl⟩ : syracuseStep 365789 = 137171) (by norm_num)
theorem B595181 : Blo 243817 595181 := bbase (se 3 (by rfl) ⟨111596, by rfl⟩ : syracuseStep 595181 = 223193) (by norm_num)
theorem B365813 : Blo 243817 365813 := bbase (se 5 (by rfl) ⟨17147, by rfl⟩ : syracuseStep 365813 = 34295) (by norm_num)
theorem B365837 : Blo 243817 365837 := bbase (se 3 (by rfl) ⟨68594, by rfl⟩ : syracuseStep 365837 = 137189) (by norm_num)
theorem B365861 : Blo 243817 365861 := bbase (se 4 (by rfl) ⟨34299, by rfl⟩ : syracuseStep 365861 = 68599) (by norm_num)
theorem B562469 : Blo 243817 562469 := bbase (se 4 (by rfl) ⟨52731, by rfl⟩ : syracuseStep 562469 = 105463) (by norm_num)
theorem B365885 : Blo 243817 365885 := bbase (se 3 (by rfl) ⟨68603, by rfl⟩ : syracuseStep 365885 = 137207) (by norm_num)
theorem B365909 : Blo 243817 365909 := bbase (se 14 (by rfl) ⟨33, by rfl⟩ : syracuseStep 365909 = 67) (by norm_num)
theorem B464221 : Blo 243817 464221 := bbase (se 3 (by rfl) ⟨87041, by rfl⟩ : syracuseStep 464221 = 174083) (by norm_num)
theorem B333157 : Blo 243817 333157 := bbase (se 4 (by rfl) ⟨31233, by rfl⟩ : syracuseStep 333157 = 62467) (by norm_num)
theorem B365933 : Blo 243817 365933 := bbase (se 3 (by rfl) ⟨68612, by rfl⟩ : syracuseStep 365933 = 137225) (by norm_num)
theorem B365957 : Blo 243817 365957 := bbase (se 4 (by rfl) ⟨34308, by rfl⟩ : syracuseStep 365957 = 68617) (by norm_num)
theorem B365981 : Blo 243817 365981 := bbase (se 3 (by rfl) ⟨68621, by rfl⟩ : syracuseStep 365981 = 137243) (by norm_num)
theorem B824741 : Blo 243817 824741 := bbase (se 4 (by rfl) ⟨77319, by rfl⟩ : syracuseStep 824741 = 154639) (by norm_num)
theorem B366005 : Blo 243817 366005 := bbase (se 5 (by rfl) ⟨17156, by rfl⟩ : syracuseStep 366005 = 34313) (by norm_num)
theorem B366029 : Blo 243817 366029 := bbase (se 3 (by rfl) ⟨68630, by rfl⟩ : syracuseStep 366029 = 137261) (by norm_num)
theorem B366053 : Blo 243817 366053 := bbase (se 4 (by rfl) ⟨34317, by rfl⟩ : syracuseStep 366053 = 68635) (by norm_num)
theorem B2168309 : Blo 243817 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B366077 : Blo 243817 366077 := bbase (se 3 (by rfl) ⟨68639, by rfl⟩ : syracuseStep 366077 = 137279) (by norm_num)
theorem B366101 : Blo 243817 366101 := bbase (se 6 (by rfl) ⟨8580, by rfl⟩ : syracuseStep 366101 = 17161) (by norm_num)
theorem B366125 : Blo 243817 366125 := bbase (se 3 (by rfl) ⟨68648, by rfl⟩ : syracuseStep 366125 = 137297) (by norm_num)
theorem B366149 : Blo 243817 366149 := bbase (se 4 (by rfl) ⟨34326, by rfl⟩ : syracuseStep 366149 = 68653) (by norm_num)
theorem B366173 : Blo 243817 366173 := bbase (se 3 (by rfl) ⟨68657, by rfl⟩ : syracuseStep 366173 = 137315) (by norm_num)
theorem B366197 : Blo 243817 366197 := bbase (se 5 (by rfl) ⟨17165, by rfl⟩ : syracuseStep 366197 = 34331) (by norm_num)
theorem B366221 : Blo 243817 366221 := bbase (se 3 (by rfl) ⟨68666, by rfl⟩ : syracuseStep 366221 = 137333) (by norm_num)
theorem B464525 : Blo 243817 464525 := bbase (se 3 (by rfl) ⟨87098, by rfl⟩ : syracuseStep 464525 = 174197) (by norm_num)
theorem B366245 : Blo 243817 366245 := bbase (se 4 (by rfl) ⟨34335, by rfl⟩ : syracuseStep 366245 = 68671) (by norm_num)
theorem B366269 : Blo 243817 366269 := bbase (se 3 (by rfl) ⟨68675, by rfl⟩ : syracuseStep 366269 = 137351) (by norm_num)
theorem B366293 : Blo 243817 366293 := bbase (se 7 (by rfl) ⟨4292, by rfl⟩ : syracuseStep 366293 = 8585) (by norm_num)
theorem B366317 : Blo 243817 366317 := bbase (se 3 (by rfl) ⟨68684, by rfl⟩ : syracuseStep 366317 = 137369) (by norm_num)
theorem B366341 : Blo 243817 366341 := bbase (se 4 (by rfl) ⟨34344, by rfl⟩ : syracuseStep 366341 = 68689) (by norm_num)
theorem B366365 : Blo 243817 366365 := bbase (se 3 (by rfl) ⟨68693, by rfl⟩ : syracuseStep 366365 = 137387) (by norm_num)
theorem B366389 : Blo 243817 366389 := bbase (se 5 (by rfl) ⟨17174, by rfl⟩ : syracuseStep 366389 = 34349) (by norm_num)
theorem B1251125 : Blo 243817 1251125 := bbase (se 5 (by rfl) ⟨58646, by rfl⟩ : syracuseStep 1251125 = 117293) (by norm_num)
theorem B366413 : Blo 243817 366413 := bbase (se 3 (by rfl) ⟨68702, by rfl⟩ : syracuseStep 366413 = 137405) (by norm_num)
theorem B825173 : Blo 243817 825173 := bbase (se 9 (by rfl) ⟨2417, by rfl⟩ : syracuseStep 825173 = 4835) (by norm_num)
theorem B366437 : Blo 243817 366437 := bbase (se 4 (by rfl) ⟨34353, by rfl⟩ : syracuseStep 366437 = 68707) (by norm_num)
theorem B366461 : Blo 243817 366461 := bbase (se 3 (by rfl) ⟨68711, by rfl⟩ : syracuseStep 366461 = 137423) (by norm_num)
theorem B366485 : Blo 243817 366485 := bbase (se 6 (by rfl) ⟨8589, by rfl⟩ : syracuseStep 366485 = 17179) (by norm_num)
theorem B1054613 : Blo 243817 1054613 := bbase (se 6 (by rfl) ⟨24717, by rfl⟩ : syracuseStep 1054613 = 49435) (by norm_num)
theorem B366509 : Blo 243817 366509 := bbase (se 3 (by rfl) ⟨68720, by rfl⟩ : syracuseStep 366509 = 137441) (by norm_num)
theorem B366533 : Blo 243817 366533 := bbase (se 4 (by rfl) ⟨34362, by rfl⟩ : syracuseStep 366533 = 68725) (by norm_num)
theorem B1185749 : Blo 243817 1185749 := bbase (se 7 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 1185749 = 27791) (by norm_num)
theorem B366557 : Blo 243817 366557 := bbase (se 3 (by rfl) ⟨68729, by rfl⟩ : syracuseStep 366557 = 137459) (by norm_num)
theorem B366581 : Blo 243817 366581 := bbase (se 5 (by rfl) ⟨17183, by rfl⟩ : syracuseStep 366581 = 34367) (by norm_num)
theorem B366605 : Blo 243817 366605 := bbase (se 3 (by rfl) ⟨68738, by rfl⟩ : syracuseStep 366605 = 137477) (by norm_num)
theorem B366629 : Blo 243817 366629 := bbase (se 4 (by rfl) ⟨34371, by rfl⟩ : syracuseStep 366629 = 68743) (by norm_num)
theorem B333877 : Blo 243817 333877 := bbase (se 5 (by rfl) ⟨15650, by rfl⟩ : syracuseStep 333877 = 31301) (by norm_num)
theorem B366653 : Blo 243817 366653 := bbase (se 3 (by rfl) ⟨68747, by rfl⟩ : syracuseStep 366653 = 137495) (by norm_num)
theorem B366677 : Blo 243817 366677 := bbase (se 8 (by rfl) ⟨2148, by rfl⟩ : syracuseStep 366677 = 4297) (by norm_num)
theorem B366701 : Blo 243817 366701 := bbase (se 3 (by rfl) ⟨68756, by rfl⟩ : syracuseStep 366701 = 137513) (by norm_num)
theorem B661621 : Blo 243817 661621 := bbase (se 5 (by rfl) ⟨31013, by rfl⟩ : syracuseStep 661621 = 62027) (by norm_num)
theorem B366725 : Blo 243817 366725 := bbase (se 4 (by rfl) ⟨34380, by rfl⟩ : syracuseStep 366725 = 68761) (by norm_num)
theorem B1054853 : Blo 243817 1054853 := bbase (se 4 (by rfl) ⟨98892, by rfl⟩ : syracuseStep 1054853 = 197785) (by norm_num)
theorem B366749 : Blo 243817 366749 := bbase (se 3 (by rfl) ⟨68765, by rfl⟩ : syracuseStep 366749 = 137531) (by norm_num)
theorem B694453 : Blo 243817 694453 := bbase (se 5 (by rfl) ⟨32552, by rfl⟩ : syracuseStep 694453 = 65105) (by norm_num)
theorem B366773 : Blo 243817 366773 := bbase (se 5 (by rfl) ⟨17192, by rfl⟩ : syracuseStep 366773 = 34385) (by norm_num)
theorem B366797 : Blo 243817 366797 := bbase (se 3 (by rfl) ⟨68774, by rfl⟩ : syracuseStep 366797 = 137549) (by norm_num)
theorem B366821 : Blo 243817 366821 := bbase (se 4 (by rfl) ⟨34389, by rfl⟩ : syracuseStep 366821 = 68779) (by norm_num)
theorem B366845 : Blo 243817 366845 := bbase (se 3 (by rfl) ⟨68783, by rfl⟩ : syracuseStep 366845 = 137567) (by norm_num)
theorem B825605 : Blo 243817 825605 := bbase (se 4 (by rfl) ⟨77400, by rfl⟩ : syracuseStep 825605 = 154801) (by norm_num)
theorem B366869 : Blo 243817 366869 := bbase (se 6 (by rfl) ⟨8598, by rfl⟩ : syracuseStep 366869 = 17197) (by norm_num)
theorem B891157 : Blo 243817 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B366893 : Blo 243817 366893 := bbase (se 3 (by rfl) ⟨68792, by rfl⟩ : syracuseStep 366893 = 137585) (by norm_num)
theorem B366917 : Blo 243817 366917 := bbase (se 4 (by rfl) ⟨34398, by rfl⟩ : syracuseStep 366917 = 68797) (by norm_num)
theorem B366941 : Blo 243817 366941 := bbase (se 3 (by rfl) ⟨68801, by rfl⟩ : syracuseStep 366941 = 137603) (by norm_num)
theorem B366965 : Blo 243817 366965 := bbase (se 5 (by rfl) ⟨17201, by rfl⟩ : syracuseStep 366965 = 34403) (by norm_num)
theorem B465277 : Blo 243817 465277 := bbase (se 3 (by rfl) ⟨87239, by rfl⟩ : syracuseStep 465277 = 174479) (by norm_num)
theorem B366989 : Blo 243817 366989 := bbase (se 3 (by rfl) ⟨68810, by rfl⟩ : syracuseStep 366989 = 137621) (by norm_num)
theorem B367013 : Blo 243817 367013 := bbase (se 4 (by rfl) ⟨34407, by rfl⟩ : syracuseStep 367013 = 68815) (by norm_num)
theorem B367037 : Blo 243817 367037 := bbase (se 3 (by rfl) ⟨68819, by rfl⟩ : syracuseStep 367037 = 137639) (by norm_num)
theorem B367061 : Blo 243817 367061 := bbase (se 7 (by rfl) ⟨4301, by rfl⟩ : syracuseStep 367061 = 8603) (by norm_num)
theorem B367085 : Blo 243817 367085 := bbase (se 3 (by rfl) ⟨68828, by rfl⟩ : syracuseStep 367085 = 137657) (by norm_num)
theorem B367109 : Blo 243817 367109 := bbase (se 4 (by rfl) ⟨34416, by rfl⟩ : syracuseStep 367109 = 68833) (by norm_num)
theorem B465421 : Blo 243817 465421 := bbase (se 3 (by rfl) ⟨87266, by rfl⟩ : syracuseStep 465421 = 174533) (by norm_num)
theorem B367133 : Blo 243817 367133 := bbase (se 3 (by rfl) ⟨68837, by rfl⟩ : syracuseStep 367133 = 137675) (by norm_num)
theorem B498221 : Blo 243817 498221 := bbase (se 3 (by rfl) ⟨93416, by rfl⟩ : syracuseStep 498221 = 186833) (by norm_num)
theorem B367157 : Blo 243817 367157 := bbase (se 5 (by rfl) ⟨17210, by rfl⟩ : syracuseStep 367157 = 34421) (by norm_num)
theorem B367181 : Blo 243817 367181 := bbase (se 3 (by rfl) ⟨68846, by rfl⟩ : syracuseStep 367181 = 137693) (by norm_num)
theorem B367205 : Blo 243817 367205 := bbase (se 4 (by rfl) ⟨34425, by rfl⟩ : syracuseStep 367205 = 68851) (by norm_num)
theorem B367229 : Blo 243817 367229 := bbase (se 3 (by rfl) ⟨68855, by rfl⟩ : syracuseStep 367229 = 137711) (by norm_num)
theorem B367253 : Blo 243817 367253 := bbase (se 6 (by rfl) ⟨8607, by rfl⟩ : syracuseStep 367253 = 17215) (by norm_num)
theorem B498325 : Blo 243817 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B367277 : Blo 243817 367277 := bbase (se 3 (by rfl) ⟨68864, by rfl⟩ : syracuseStep 367277 = 137729) (by norm_num)
theorem B465581 : Blo 243817 465581 := bbase (se 3 (by rfl) ⟨87296, by rfl⟩ : syracuseStep 465581 = 174593) (by norm_num)
theorem B826037 : Blo 243817 826037 := bbase (se 5 (by rfl) ⟨38720, by rfl⟩ : syracuseStep 826037 = 77441) (by norm_num)
theorem B367301 : Blo 243817 367301 := bbase (se 4 (by rfl) ⟨34434, by rfl⟩ : syracuseStep 367301 = 68869) (by norm_num)
theorem B334541 : Blo 243817 334541 := bbase (se 3 (by rfl) ⟨62726, by rfl⟩ : syracuseStep 334541 = 125453) (by norm_num)
theorem B367325 : Blo 243817 367325 := bbase (se 3 (by rfl) ⟨68873, by rfl⟩ : syracuseStep 367325 = 137747) (by norm_num)
theorem B367349 : Blo 243817 367349 := bbase (se 5 (by rfl) ⟨17219, by rfl⟩ : syracuseStep 367349 = 34439) (by norm_num)
theorem B367373 : Blo 243817 367373 := bbase (se 3 (by rfl) ⟨68882, by rfl⟩ : syracuseStep 367373 = 137765) (by norm_num)
theorem B367397 : Blo 243817 367397 := bbase (se 4 (by rfl) ⟨34443, by rfl⟩ : syracuseStep 367397 = 68887) (by norm_num)
theorem B367421 : Blo 243817 367421 := bbase (se 3 (by rfl) ⟨68891, by rfl⟩ : syracuseStep 367421 = 137783) (by norm_num)
theorem B465725 : Blo 243817 465725 := bbase (se 3 (by rfl) ⟨87323, by rfl⟩ : syracuseStep 465725 = 174647) (by norm_num)
theorem B367445 : Blo 243817 367445 := bbase (se 9 (by rfl) ⟨1076, by rfl⟩ : syracuseStep 367445 = 2153) (by norm_num)
theorem B662357 : Blo 243817 662357 := bbase (se 9 (by rfl) ⟨1940, by rfl⟩ : syracuseStep 662357 = 3881) (by norm_num)
theorem B367469 : Blo 243817 367469 := bbase (se 3 (by rfl) ⟨68900, by rfl⟩ : syracuseStep 367469 = 137801) (by norm_num)
theorem B1121141 : Blo 243817 1121141 := bbase (se 5 (by rfl) ⟨52553, by rfl⟩ : syracuseStep 1121141 = 105107) (by norm_num)
theorem B367493 : Blo 243817 367493 := bbase (se 4 (by rfl) ⟨34452, by rfl⟩ : syracuseStep 367493 = 68905) (by norm_num)
theorem B367517 : Blo 243817 367517 := bbase (se 3 (by rfl) ⟨68909, by rfl⟩ : syracuseStep 367517 = 137819) (by norm_num)
theorem B367541 : Blo 243817 367541 := bbase (se 5 (by rfl) ⟨17228, by rfl⟩ : syracuseStep 367541 = 34457) (by norm_num)
theorem B596933 : Blo 243817 596933 := bbase (se 4 (by rfl) ⟨55962, by rfl⟩ : syracuseStep 596933 = 111925) (by norm_num)
theorem B367565 : Blo 243817 367565 := bbase (se 3 (by rfl) ⟨68918, by rfl⟩ : syracuseStep 367565 = 137837) (by norm_num)
theorem B367589 : Blo 243817 367589 := bbase (se 4 (by rfl) ⟨34461, by rfl⟩ : syracuseStep 367589 = 68923) (by norm_num)
theorem B367613 : Blo 243817 367613 := bbase (se 3 (by rfl) ⟨68927, by rfl⟩ : syracuseStep 367613 = 137855) (by norm_num)
theorem B367637 : Blo 243817 367637 := bbase (se 6 (by rfl) ⟨8616, by rfl⟩ : syracuseStep 367637 = 17233) (by norm_num)
theorem B367661 : Blo 243817 367661 := bbase (se 3 (by rfl) ⟨68936, by rfl⟩ : syracuseStep 367661 = 137873) (by norm_num)
theorem B367685 : Blo 243817 367685 := bbase (se 4 (by rfl) ⟨34470, by rfl⟩ : syracuseStep 367685 = 68941) (by norm_num)
theorem B1252421 : Blo 243817 1252421 := bbase (se 4 (by rfl) ⟨117414, by rfl⟩ : syracuseStep 1252421 = 234829) (by norm_num)
theorem B367709 : Blo 243817 367709 := bbase (se 3 (by rfl) ⟨68945, by rfl⟩ : syracuseStep 367709 = 137891) (by norm_num)
theorem B466013 : Blo 243817 466013 := bbase (se 3 (by rfl) ⟨87377, by rfl⟩ : syracuseStep 466013 = 174755) (by norm_num)
theorem B826469 : Blo 243817 826469 := bbase (se 4 (by rfl) ⟨77481, by rfl⟩ : syracuseStep 826469 = 154963) (by norm_num)
theorem B367733 : Blo 243817 367733 := bbase (se 5 (by rfl) ⟨17237, by rfl⟩ : syracuseStep 367733 = 34475) (by norm_num)
theorem B367757 : Blo 243817 367757 := bbase (se 3 (by rfl) ⟨68954, by rfl⟩ : syracuseStep 367757 = 137909) (by norm_num)
theorem B367781 : Blo 243817 367781 := bbase (se 4 (by rfl) ⟨34479, by rfl⟩ : syracuseStep 367781 = 68959) (by norm_num)
theorem B367805 : Blo 243817 367805 := bbase (se 3 (by rfl) ⟨68963, by rfl⟩ : syracuseStep 367805 = 137927) (by norm_num)
theorem B367829 : Blo 243817 367829 := bbase (se 7 (by rfl) ⟨4310, by rfl⟩ : syracuseStep 367829 = 8621) (by norm_num)
theorem B367853 : Blo 243817 367853 := bbase (se 3 (by rfl) ⟨68972, by rfl⟩ : syracuseStep 367853 = 137945) (by norm_num)
theorem B466165 : Blo 243817 466165 := bbase (se 5 (by rfl) ⟨21851, by rfl⟩ : syracuseStep 466165 = 43703) (by norm_num)
theorem B695557 : Blo 243817 695557 := bbase (se 4 (by rfl) ⟨65208, by rfl⟩ : syracuseStep 695557 = 130417) (by norm_num)
theorem B367877 : Blo 243817 367877 := bbase (se 4 (by rfl) ⟨34488, by rfl⟩ : syracuseStep 367877 = 68977) (by norm_num)
theorem B367901 : Blo 243817 367901 := bbase (se 3 (by rfl) ⟨68981, by rfl⟩ : syracuseStep 367901 = 137963) (by norm_num)
theorem B367925 : Blo 243817 367925 := bbase (se 5 (by rfl) ⟨17246, by rfl⟩ : syracuseStep 367925 = 34493) (by norm_num)
theorem B367949 : Blo 243817 367949 := bbase (se 3 (by rfl) ⟨68990, by rfl⟩ : syracuseStep 367949 = 137981) (by norm_num)
theorem B367973 : Blo 243817 367973 := bbase (se 4 (by rfl) ⟨34497, by rfl⟩ : syracuseStep 367973 = 68995) (by norm_num)
theorem B367997 : Blo 243817 367997 := bbase (se 3 (by rfl) ⟨68999, by rfl⟩ : syracuseStep 367997 = 137999) (by norm_num)
theorem B368021 : Blo 243817 368021 := bbase (se 6 (by rfl) ⟨8625, by rfl⟩ : syracuseStep 368021 = 17251) (by norm_num)
theorem B368045 : Blo 243817 368045 := bbase (se 3 (by rfl) ⟨69008, by rfl⟩ : syracuseStep 368045 = 138017) (by norm_num)
theorem B368069 : Blo 243817 368069 := bbase (se 4 (by rfl) ⟨34506, by rfl⟩ : syracuseStep 368069 = 69013) (by norm_num)
theorem B368093 : Blo 243817 368093 := bbase (se 3 (by rfl) ⟨69017, by rfl⟩ : syracuseStep 368093 = 138035) (by norm_num)
theorem B368117 : Blo 243817 368117 := bbase (se 5 (by rfl) ⟨17255, by rfl⟩ : syracuseStep 368117 = 34511) (by norm_num)
theorem B368141 : Blo 243817 368141 := bbase (se 3 (by rfl) ⟨69026, by rfl⟩ : syracuseStep 368141 = 138053) (by norm_num)
theorem B826901 : Blo 243817 826901 := bbase (se 6 (by rfl) ⟨19380, by rfl⟩ : syracuseStep 826901 = 38761) (by norm_num)
theorem B368165 : Blo 243817 368165 := bbase (se 4 (by rfl) ⟨34515, by rfl⟩ : syracuseStep 368165 = 69031) (by norm_num)
theorem B466469 : Blo 243817 466469 := bbase (se 4 (by rfl) ⟨43731, by rfl⟩ : syracuseStep 466469 = 87463) (by norm_num)
theorem B368189 : Blo 243817 368189 := bbase (se 3 (by rfl) ⟨69035, by rfl⟩ : syracuseStep 368189 = 138071) (by norm_num)
theorem B368213 : Blo 243817 368213 := bbase (se 8 (by rfl) ⟨2157, by rfl⟩ : syracuseStep 368213 = 4315) (by norm_num)
theorem B368237 : Blo 243817 368237 := bbase (se 3 (by rfl) ⟨69044, by rfl⟩ : syracuseStep 368237 = 138089) (by norm_num)
theorem B368261 : Blo 243817 368261 := bbase (se 4 (by rfl) ⟨34524, by rfl⟩ : syracuseStep 368261 = 69049) (by norm_num)
theorem B368285 : Blo 243817 368285 := bbase (se 3 (by rfl) ⟨69053, by rfl⟩ : syracuseStep 368285 = 138107) (by norm_num)
theorem B368309 : Blo 243817 368309 := bbase (se 5 (by rfl) ⟨17264, by rfl⟩ : syracuseStep 368309 = 34529) (by norm_num)
theorem B368333 : Blo 243817 368333 := bbase (se 3 (by rfl) ⟨69062, by rfl⟩ : syracuseStep 368333 = 138125) (by norm_num)
theorem B368357 : Blo 243817 368357 := bbase (se 4 (by rfl) ⟨34533, by rfl⟩ : syracuseStep 368357 = 69067) (by norm_num)
theorem B368381 : Blo 243817 368381 := bbase (se 3 (by rfl) ⟨69071, by rfl⟩ : syracuseStep 368381 = 138143) (by norm_num)
theorem B368405 : Blo 243817 368405 := bbase (se 6 (by rfl) ⟨8634, by rfl⟩ : syracuseStep 368405 = 17269) (by norm_num)
theorem B368429 : Blo 243817 368429 := bbase (se 3 (by rfl) ⟨69080, by rfl⟩ : syracuseStep 368429 = 138161) (by norm_num)
theorem B368453 : Blo 243817 368453 := bbase (se 4 (by rfl) ⟨34542, by rfl⟩ : syracuseStep 368453 = 69085) (by norm_num)
theorem B368477 : Blo 243817 368477 := bbase (se 3 (by rfl) ⟨69089, by rfl⟩ : syracuseStep 368477 = 138179) (by norm_num)
theorem B368501 : Blo 243817 368501 := bbase (se 5 (by rfl) ⟨17273, by rfl⟩ : syracuseStep 368501 = 34547) (by norm_num)
theorem B368525 : Blo 243817 368525 := bbase (se 3 (by rfl) ⟨69098, by rfl⟩ : syracuseStep 368525 = 138197) (by norm_num)
theorem B368549 : Blo 243817 368549 := bbase (se 4 (by rfl) ⟨34551, by rfl⟩ : syracuseStep 368549 = 69103) (by norm_num)
theorem B368573 : Blo 243817 368573 := bbase (se 3 (by rfl) ⟨69107, by rfl⟩ : syracuseStep 368573 = 138215) (by norm_num)
theorem B827333 : Blo 243817 827333 := bbase (se 4 (by rfl) ⟨77562, by rfl⟩ : syracuseStep 827333 = 155125) (by norm_num)
theorem B368597 : Blo 243817 368597 := bbase (se 7 (by rfl) ⟨4319, by rfl⟩ : syracuseStep 368597 = 8639) (by norm_num)
theorem B368621 : Blo 243817 368621 := bbase (se 3 (by rfl) ⟨69116, by rfl⟩ : syracuseStep 368621 = 138233) (by norm_num)
theorem B368645 : Blo 243817 368645 := bbase (se 4 (by rfl) ⟨34560, by rfl⟩ : syracuseStep 368645 = 69121) (by norm_num)
theorem B368669 : Blo 243817 368669 := bbase (se 3 (by rfl) ⟨69125, by rfl⟩ : syracuseStep 368669 = 138251) (by norm_num)
theorem B368693 : Blo 243817 368693 := bbase (se 5 (by rfl) ⟨17282, by rfl⟩ : syracuseStep 368693 = 34565) (by norm_num)
theorem B368717 : Blo 243817 368717 := bbase (se 3 (by rfl) ⟨69134, by rfl⟩ : syracuseStep 368717 = 138269) (by norm_num)
theorem B16162901 : Blo 243817 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B270425 : Blo 243817 270425 := bbase (se 2 (by rfl) ⟨101409, by rfl⟩ : syracuseStep 270425 = 202819) (by norm_num)
theorem B401501 : Blo 243817 401501 := bbase (se 3 (by rfl) ⟨75281, by rfl⟩ : syracuseStep 401501 = 150563) (by norm_num)
theorem B368741 : Blo 243817 368741 := bbase (se 4 (by rfl) ⟨34569, by rfl⟩ : syracuseStep 368741 = 69139) (by norm_num)
theorem B368765 : Blo 243817 368765 := bbase (se 3 (by rfl) ⟨69143, by rfl⟩ : syracuseStep 368765 = 138287) (by norm_num)
theorem B368789 : Blo 243817 368789 := bbase (se 6 (by rfl) ⟨8643, by rfl⟩ : syracuseStep 368789 = 17287) (by norm_num)
theorem B368813 : Blo 243817 368813 := bbase (se 3 (by rfl) ⟨69152, by rfl⟩ : syracuseStep 368813 = 138305) (by norm_num)
theorem B368837 : Blo 243817 368837 := bbase (se 4 (by rfl) ⟨34578, by rfl⟩ : syracuseStep 368837 = 69157) (by norm_num)
theorem B4726997 : Blo 243817 4726997 := bbase (se 7 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 4726997 = 110789) (by norm_num)
theorem B368861 : Blo 243817 368861 := bbase (se 3 (by rfl) ⟨69161, by rfl⟩ : syracuseStep 368861 = 138323) (by norm_num)
theorem B368885 : Blo 243817 368885 := bbase (se 5 (by rfl) ⟨17291, by rfl⟩ : syracuseStep 368885 = 34583) (by norm_num)
theorem B368909 : Blo 243817 368909 := bbase (se 3 (by rfl) ⟨69170, by rfl⟩ : syracuseStep 368909 = 138341) (by norm_num)
theorem B467221 : Blo 243817 467221 := bbase (se 6 (by rfl) ⟨10950, by rfl⟩ : syracuseStep 467221 = 21901) (by norm_num)
theorem B368933 : Blo 243817 368933 := bbase (se 4 (by rfl) ⟨34587, by rfl⟩ : syracuseStep 368933 = 69175) (by norm_num)
theorem B368957 : Blo 243817 368957 := bbase (se 3 (by rfl) ⟨69179, by rfl⟩ : syracuseStep 368957 = 138359) (by norm_num)
theorem B368981 : Blo 243817 368981 := bbase (se 10 (by rfl) ⟨540, by rfl⟩ : syracuseStep 368981 = 1081) (by norm_num)
theorem B2662741 : Blo 243817 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B1253717 : Blo 243817 1253717 := bbase (se 10 (by rfl) ⟨1836, by rfl⟩ : syracuseStep 1253717 = 3673) (by norm_num)
theorem B369005 : Blo 243817 369005 := bbase (se 3 (by rfl) ⟨69188, by rfl⟩ : syracuseStep 369005 = 138377) (by norm_num)
theorem B827765 : Blo 243817 827765 := bbase (se 5 (by rfl) ⟨38801, by rfl⟩ : syracuseStep 827765 = 77603) (by norm_num)
theorem B1057141 : Blo 243817 1057141 := bbase (se 5 (by rfl) ⟨49553, by rfl⟩ : syracuseStep 1057141 = 99107) (by norm_num)
theorem B369029 : Blo 243817 369029 := bbase (se 4 (by rfl) ⟨34596, by rfl⟩ : syracuseStep 369029 = 69193) (by norm_num)
theorem B369053 : Blo 243817 369053 := bbase (se 3 (by rfl) ⟨69197, by rfl⟩ : syracuseStep 369053 = 138395) (by norm_num)
theorem B467365 : Blo 243817 467365 := bbase (se 4 (by rfl) ⟨43815, by rfl⟩ : syracuseStep 467365 = 87631) (by norm_num)
theorem B369077 : Blo 243817 369077 := bbase (se 5 (by rfl) ⟨17300, by rfl⟩ : syracuseStep 369077 = 34601) (by norm_num)
theorem B369101 : Blo 243817 369101 := bbase (se 3 (by rfl) ⟨69206, by rfl⟩ : syracuseStep 369101 = 138413) (by norm_num)
theorem B369125 : Blo 243817 369125 := bbase (se 4 (by rfl) ⟨34605, by rfl⟩ : syracuseStep 369125 = 69211) (by norm_num)
theorem B369149 : Blo 243817 369149 := bbase (se 3 (by rfl) ⟨69215, by rfl⟩ : syracuseStep 369149 = 138431) (by norm_num)
theorem B369173 : Blo 243817 369173 := bbase (se 6 (by rfl) ⟨8652, by rfl⟩ : syracuseStep 369173 = 17305) (by norm_num)
theorem B369197 : Blo 243817 369197 := bbase (se 3 (by rfl) ⟨69224, by rfl⟩ : syracuseStep 369197 = 138449) (by norm_num)
theorem B369221 : Blo 243817 369221 := bbase (se 4 (by rfl) ⟨34614, by rfl⟩ : syracuseStep 369221 = 69229) (by norm_num)
theorem B467525 : Blo 243817 467525 := bbase (se 4 (by rfl) ⟨43830, by rfl⟩ : syracuseStep 467525 = 87661) (by norm_num)
theorem B1679957 : Blo 243817 1679957 := bbase (se 8 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 1679957 = 19687) (by norm_num)
theorem B369245 : Blo 243817 369245 := bbase (se 3 (by rfl) ⟨69233, by rfl⟩ : syracuseStep 369245 = 138467) (by norm_num)
theorem B369269 : Blo 243817 369269 := bbase (se 5 (by rfl) ⟨17309, by rfl⟩ : syracuseStep 369269 = 34619) (by norm_num)
theorem B533117 : Blo 243817 533117 := bbase (se 3 (by rfl) ⟨99959, by rfl⟩ : syracuseStep 533117 = 199919) (by norm_num)
theorem B369293 : Blo 243817 369293 := bbase (se 3 (by rfl) ⟨69242, by rfl⟩ : syracuseStep 369293 = 138485) (by norm_num)
theorem B369317 : Blo 243817 369317 := bbase (se 4 (by rfl) ⟨34623, by rfl⟩ : syracuseStep 369317 = 69247) (by norm_num)
theorem B369341 : Blo 243817 369341 := bbase (se 3 (by rfl) ⟨69251, by rfl⟩ : syracuseStep 369341 = 138503) (by norm_num)
theorem B369365 : Blo 243817 369365 := bbase (se 7 (by rfl) ⟨4328, by rfl⟩ : syracuseStep 369365 = 8657) (by norm_num)
theorem B467669 : Blo 243817 467669 := bbase (se 7 (by rfl) ⟨5480, by rfl⟩ : syracuseStep 467669 = 10961) (by norm_num)
theorem B926437 : Blo 243817 926437 := bbase (se 4 (by rfl) ⟨86853, by rfl⟩ : syracuseStep 926437 = 173707) (by norm_num)
theorem B697061 : Blo 243817 697061 := bbase (se 4 (by rfl) ⟨65349, by rfl⟩ : syracuseStep 697061 = 130699) (by norm_num)
theorem B402149 : Blo 243817 402149 := bbase (se 4 (by rfl) ⟨37701, by rfl⟩ : syracuseStep 402149 = 75403) (by norm_num)
theorem B369389 : Blo 243817 369389 := bbase (se 3 (by rfl) ⟨69260, by rfl⟩ : syracuseStep 369389 = 138521) (by norm_num)
theorem B369413 : Blo 243817 369413 := bbase (se 4 (by rfl) ⟨34632, by rfl⟩ : syracuseStep 369413 = 69265) (by norm_num)
theorem B369437 : Blo 243817 369437 := bbase (se 3 (by rfl) ⟨69269, by rfl⟩ : syracuseStep 369437 = 138539) (by norm_num)
theorem B828197 : Blo 243817 828197 := bbase (se 4 (by rfl) ⟨77643, by rfl⟩ : syracuseStep 828197 = 155287) (by norm_num)
theorem B369461 : Blo 243817 369461 := bbase (se 5 (by rfl) ⟨17318, by rfl⟩ : syracuseStep 369461 = 34637) (by norm_num)
theorem B369485 : Blo 243817 369485 := bbase (se 3 (by rfl) ⟨69278, by rfl⟩ : syracuseStep 369485 = 138557) (by norm_num)
theorem B369509 : Blo 243817 369509 := bbase (se 4 (by rfl) ⟨34641, by rfl⟩ : syracuseStep 369509 = 69283) (by norm_num)
theorem B369533 : Blo 243817 369533 := bbase (se 3 (by rfl) ⟨69287, by rfl⟩ : syracuseStep 369533 = 138575) (by norm_num)
theorem B4203413 : Blo 243817 4203413 := bbase (se 6 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 4203413 = 197035) (by norm_num)
theorem B369557 : Blo 243817 369557 := bbase (se 6 (by rfl) ⟨8661, by rfl⟩ : syracuseStep 369557 = 17323) (by norm_num)
theorem B369581 : Blo 243817 369581 := bbase (se 3 (by rfl) ⟨69296, by rfl⟩ : syracuseStep 369581 = 138593) (by norm_num)
theorem B1254325 : Blo 243817 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B369605 : Blo 243817 369605 := bbase (se 4 (by rfl) ⟨34650, by rfl⟩ : syracuseStep 369605 = 69301) (by norm_num)
theorem B369629 : Blo 243817 369629 := bbase (se 3 (by rfl) ⟨69305, by rfl⟩ : syracuseStep 369629 = 138611) (by norm_num)
theorem B369653 : Blo 243817 369653 := bbase (se 5 (by rfl) ⟨17327, by rfl⟩ : syracuseStep 369653 = 34655) (by norm_num)
theorem B467957 : Blo 243817 467957 := bbase (se 5 (by rfl) ⟨21935, by rfl⟩ : syracuseStep 467957 = 43871) (by norm_num)
theorem B369677 : Blo 243817 369677 := bbase (se 3 (by rfl) ⟨69314, by rfl⟩ : syracuseStep 369677 = 138629) (by norm_num)
theorem B926741 : Blo 243817 926741 := bbase (se 6 (by rfl) ⟨21720, by rfl⟩ : syracuseStep 926741 = 43441) (by norm_num)
theorem B369701 : Blo 243817 369701 := bbase (se 4 (by rfl) ⟨34659, by rfl⟩ : syracuseStep 369701 = 69319) (by norm_num)
theorem B369725 : Blo 243817 369725 := bbase (se 3 (by rfl) ⟨69323, by rfl⟩ : syracuseStep 369725 = 138647) (by norm_num)
theorem B369749 : Blo 243817 369749 := bbase (se 8 (by rfl) ⟨2166, by rfl⟩ : syracuseStep 369749 = 4333) (by norm_num)
theorem B369773 : Blo 243817 369773 := bbase (se 3 (by rfl) ⟨69332, by rfl⟩ : syracuseStep 369773 = 138665) (by norm_num)
theorem B369797 : Blo 243817 369797 := bbase (se 4 (by rfl) ⟨34668, by rfl⟩ : syracuseStep 369797 = 69337) (by norm_num)
theorem B468109 : Blo 243817 468109 := bbase (se 3 (by rfl) ⟨87770, by rfl⟩ : syracuseStep 468109 = 175541) (by norm_num)
theorem B369821 : Blo 243817 369821 := bbase (se 3 (by rfl) ⟨69341, by rfl⟩ : syracuseStep 369821 = 138683) (by norm_num)
theorem B369845 : Blo 243817 369845 := bbase (se 5 (by rfl) ⟨17336, by rfl⟩ : syracuseStep 369845 = 34673) (by norm_num)
theorem B369869 : Blo 243817 369869 := bbase (se 3 (by rfl) ⟨69350, by rfl⟩ : syracuseStep 369869 = 138701) (by norm_num)
theorem B828629 : Blo 243817 828629 := bbase (se 7 (by rfl) ⟨9710, by rfl⟩ : syracuseStep 828629 = 19421) (by norm_num)
theorem B369893 : Blo 243817 369893 := bbase (se 4 (by rfl) ⟨34677, by rfl⟩ : syracuseStep 369893 = 69355) (by norm_num)
theorem B369917 : Blo 243817 369917 := bbase (se 3 (by rfl) ⟨69359, by rfl⟩ : syracuseStep 369917 = 138719) (by norm_num)
theorem B369941 : Blo 243817 369941 := bbase (se 6 (by rfl) ⟨8670, by rfl⟩ : syracuseStep 369941 = 17341) (by norm_num)
theorem B369965 : Blo 243817 369965 := bbase (se 3 (by rfl) ⟨69368, by rfl⟩ : syracuseStep 369965 = 138737) (by norm_num)
theorem B369989 : Blo 243817 369989 := bbase (se 4 (by rfl) ⟨34686, by rfl⟩ : syracuseStep 369989 = 69373) (by norm_num)
theorem B370013 : Blo 243817 370013 := bbase (se 3 (by rfl) ⟨69377, by rfl⟩ : syracuseStep 370013 = 138755) (by norm_num)
theorem B370037 : Blo 243817 370037 := bbase (se 5 (by rfl) ⟨17345, by rfl⟩ : syracuseStep 370037 = 34691) (by norm_num)
theorem B370061 : Blo 243817 370061 := bbase (se 3 (by rfl) ⟨69386, by rfl⟩ : syracuseStep 370061 = 138773) (by norm_num)
theorem B370085 : Blo 243817 370085 := bbase (se 4 (by rfl) ⟨34695, by rfl⟩ : syracuseStep 370085 = 69391) (by norm_num)
theorem B468413 : Blo 243817 468413 := bbase (se 3 (by rfl) ⟨87827, by rfl⟩ : syracuseStep 468413 = 175655) (by norm_num)
theorem B370109 : Blo 243817 370109 := bbase (se 3 (by rfl) ⟨69395, by rfl⟩ : syracuseStep 370109 = 138791) (by norm_num)
theorem B370133 : Blo 243817 370133 := bbase (se 7 (by rfl) ⟨4337, by rfl⟩ : syracuseStep 370133 = 8675) (by norm_num)
theorem B370157 : Blo 243817 370157 := bbase (se 3 (by rfl) ⟨69404, by rfl⟩ : syracuseStep 370157 = 138809) (by norm_num)
theorem B501245 : Blo 243817 501245 := bbase (se 3 (by rfl) ⟨93983, by rfl⟩ : syracuseStep 501245 = 187967) (by norm_num)
theorem B370181 : Blo 243817 370181 := bbase (se 4 (by rfl) ⟨34704, by rfl⟩ : syracuseStep 370181 = 69409) (by norm_num)
theorem B370205 : Blo 243817 370205 := bbase (se 3 (by rfl) ⟨69413, by rfl⟩ : syracuseStep 370205 = 138827) (by norm_num)
theorem B370229 : Blo 243817 370229 := bbase (se 5 (by rfl) ⟨17354, by rfl⟩ : syracuseStep 370229 = 34709) (by norm_num)
theorem B370253 : Blo 243817 370253 := bbase (se 3 (by rfl) ⟨69422, by rfl⟩ : syracuseStep 370253 = 138845) (by norm_num)
theorem B370277 : Blo 243817 370277 := bbase (se 4 (by rfl) ⟨34713, by rfl⟩ : syracuseStep 370277 = 69427) (by norm_num)
theorem B370301 : Blo 243817 370301 := bbase (se 3 (by rfl) ⟨69431, by rfl⟩ : syracuseStep 370301 = 138863) (by norm_num)
theorem B829061 : Blo 243817 829061 := bbase (se 4 (by rfl) ⟨77724, by rfl⟩ : syracuseStep 829061 = 155449) (by norm_num)
theorem B370325 : Blo 243817 370325 := bbase (se 6 (by rfl) ⟨8679, by rfl⟩ : syracuseStep 370325 = 17359) (by norm_num)
theorem B370349 : Blo 243817 370349 := bbase (se 3 (by rfl) ⟨69440, by rfl⟩ : syracuseStep 370349 = 138881) (by norm_num)
theorem B370373 : Blo 243817 370373 := bbase (se 4 (by rfl) ⟨34722, by rfl⟩ : syracuseStep 370373 = 69445) (by norm_num)
theorem B370397 : Blo 243817 370397 := bbase (se 3 (by rfl) ⟨69449, by rfl⟩ : syracuseStep 370397 = 138899) (by norm_num)
theorem B370421 : Blo 243817 370421 := bbase (se 5 (by rfl) ⟨17363, by rfl⟩ : syracuseStep 370421 = 34727) (by norm_num)
theorem B370445 : Blo 243817 370445 := bbase (se 3 (by rfl) ⟨69458, by rfl⟩ : syracuseStep 370445 = 138917) (by norm_num)
theorem B370469 : Blo 243817 370469 := bbase (se 4 (by rfl) ⟨34731, by rfl⟩ : syracuseStep 370469 = 69463) (by norm_num)
theorem B370493 : Blo 243817 370493 := bbase (se 3 (by rfl) ⟨69467, by rfl⟩ : syracuseStep 370493 = 138935) (by norm_num)
theorem B370517 : Blo 243817 370517 := bbase (se 9 (by rfl) ⟨1085, by rfl⟩ : syracuseStep 370517 = 2171) (by norm_num)
theorem B370541 : Blo 243817 370541 := bbase (se 3 (by rfl) ⟨69476, by rfl⟩ : syracuseStep 370541 = 138953) (by norm_num)
theorem B370565 : Blo 243817 370565 := bbase (se 4 (by rfl) ⟨34740, by rfl⟩ : syracuseStep 370565 = 69481) (by norm_num)
theorem B370589 : Blo 243817 370589 := bbase (se 3 (by rfl) ⟨69485, by rfl⟩ : syracuseStep 370589 = 138971) (by norm_num)
theorem B370613 : Blo 243817 370613 := bbase (se 5 (by rfl) ⟨17372, by rfl⟩ : syracuseStep 370613 = 34745) (by norm_num)
theorem B370637 : Blo 243817 370637 := bbase (se 3 (by rfl) ⟨69494, by rfl⟩ : syracuseStep 370637 = 138989) (by norm_num)
theorem B370661 : Blo 243817 370661 := bbase (se 4 (by rfl) ⟨34749, by rfl⟩ : syracuseStep 370661 = 69499) (by norm_num)
theorem B370685 : Blo 243817 370685 := bbase (se 3 (by rfl) ⟨69503, by rfl⟩ : syracuseStep 370685 = 139007) (by norm_num)
theorem B370709 : Blo 243817 370709 := bbase (se 6 (by rfl) ⟨8688, by rfl⟩ : syracuseStep 370709 = 17377) (by norm_num)
theorem B370733 : Blo 243817 370733 := bbase (se 3 (by rfl) ⟨69512, by rfl⟩ : syracuseStep 370733 = 139025) (by norm_num)
theorem B829493 : Blo 243817 829493 := bbase (se 5 (by rfl) ⟨38882, by rfl⟩ : syracuseStep 829493 = 77765) (by norm_num)
theorem B370757 : Blo 243817 370757 := bbase (se 4 (by rfl) ⟨34758, by rfl⟩ : syracuseStep 370757 = 69517) (by norm_num)
theorem B370781 : Blo 243817 370781 := bbase (se 3 (by rfl) ⟨69521, by rfl⟩ : syracuseStep 370781 = 139043) (by norm_num)
theorem B370805 : Blo 243817 370805 := bbase (se 5 (by rfl) ⟨17381, by rfl⟩ : syracuseStep 370805 = 34763) (by norm_num)
theorem B370813 : Blo 243817 370813 := bbase (se 3 (by rfl) ⟨69527, by rfl⟩ : syracuseStep 370813 = 139055) (by norm_num)
theorem B370829 : Blo 243817 370829 := bbase (se 3 (by rfl) ⟨69530, by rfl⟩ : syracuseStep 370829 = 139061) (by norm_num)
theorem B370853 : Blo 243817 370853 := bbase (se 4 (by rfl) ⟨34767, by rfl⟩ : syracuseStep 370853 = 69535) (by norm_num)
theorem B469165 : Blo 243817 469165 := bbase (se 3 (by rfl) ⟨87968, by rfl⟩ : syracuseStep 469165 = 175937) (by norm_num)
theorem B370877 : Blo 243817 370877 := bbase (se 3 (by rfl) ⟨69539, by rfl⟩ : syracuseStep 370877 = 139079) (by norm_num)
theorem B370901 : Blo 243817 370901 := bbase (se 7 (by rfl) ⟨4346, by rfl⟩ : syracuseStep 370901 = 8693) (by norm_num)
theorem B370925 : Blo 243817 370925 := bbase (se 3 (by rfl) ⟨69548, by rfl⟩ : syracuseStep 370925 = 139097) (by norm_num)
theorem B370949 : Blo 243817 370949 := bbase (se 4 (by rfl) ⟨34776, by rfl⟩ : syracuseStep 370949 = 69553) (by norm_num)
theorem B698645 : Blo 243817 698645 := bbase (se 6 (by rfl) ⟨16374, by rfl⟩ : syracuseStep 698645 = 32749) (by norm_num)
theorem B370973 : Blo 243817 370973 := bbase (se 3 (by rfl) ⟨69557, by rfl⟩ : syracuseStep 370973 = 139115) (by norm_num)
theorem B370997 : Blo 243817 370997 := bbase (se 5 (by rfl) ⟨17390, by rfl⟩ : syracuseStep 370997 = 34781) (by norm_num)
theorem B469309 : Blo 243817 469309 := bbase (se 3 (by rfl) ⟨87995, by rfl⟩ : syracuseStep 469309 = 175991) (by norm_num)
theorem B371021 : Blo 243817 371021 := bbase (se 3 (by rfl) ⟨69566, by rfl⟩ : syracuseStep 371021 = 139133) (by norm_num)
theorem B371045 : Blo 243817 371045 := bbase (se 4 (by rfl) ⟨34785, by rfl⟩ : syracuseStep 371045 = 69571) (by norm_num)
theorem B633197 : Blo 243817 633197 := bbase (se 3 (by rfl) ⟨118724, by rfl⟩ : syracuseStep 633197 = 237449) (by norm_num)
theorem B1878389 : Blo 243817 1878389 := bbase (se 5 (by rfl) ⟨88049, by rfl⟩ : syracuseStep 1878389 = 176099) (by norm_num)
theorem B371069 : Blo 243817 371069 := bbase (se 3 (by rfl) ⟨69575, by rfl⟩ : syracuseStep 371069 = 139151) (by norm_num)
theorem B1583509 : Blo 243817 1583509 := bbase (se 6 (by rfl) ⟨37113, by rfl⟩ : syracuseStep 1583509 = 74227) (by norm_num)
theorem B371093 : Blo 243817 371093 := bbase (se 6 (by rfl) ⟨8697, by rfl⟩ : syracuseStep 371093 = 17395) (by norm_num)
theorem B371117 : Blo 243817 371117 := bbase (se 3 (by rfl) ⟨69584, by rfl⟩ : syracuseStep 371117 = 139169) (by norm_num)
theorem B371141 : Blo 243817 371141 := bbase (se 4 (by rfl) ⟨34794, by rfl⟩ : syracuseStep 371141 = 69589) (by norm_num)
theorem B469469 : Blo 243817 469469 := bbase (se 3 (by rfl) ⟨88025, by rfl⟩ : syracuseStep 469469 = 176051) (by norm_num)
theorem B371165 : Blo 243817 371165 := bbase (se 3 (by rfl) ⟨69593, by rfl⟩ : syracuseStep 371165 = 139187) (by norm_num)
theorem B829925 : Blo 243817 829925 := bbase (se 4 (by rfl) ⟨77805, by rfl⟩ : syracuseStep 829925 = 155611) (by norm_num)
theorem B371189 : Blo 243817 371189 := bbase (se 5 (by rfl) ⟨17399, by rfl⟩ : syracuseStep 371189 = 34799) (by norm_num)
theorem B371213 : Blo 243817 371213 := bbase (se 3 (by rfl) ⟨69602, by rfl⟩ : syracuseStep 371213 = 139205) (by norm_num)
theorem B371237 : Blo 243817 371237 := bbase (se 4 (by rfl) ⟨34803, by rfl⟩ : syracuseStep 371237 = 69607) (by norm_num)
theorem B371261 : Blo 243817 371261 := bbase (se 3 (by rfl) ⟨69611, by rfl⟩ : syracuseStep 371261 = 139223) (by norm_num)
theorem B371285 : Blo 243817 371285 := bbase (se 8 (by rfl) ⟨2175, by rfl⟩ : syracuseStep 371285 = 4351) (by norm_num)
theorem B469613 : Blo 243817 469613 := bbase (se 3 (by rfl) ⟨88052, by rfl⟩ : syracuseStep 469613 = 176105) (by norm_num)
theorem B371309 : Blo 243817 371309 := bbase (se 3 (by rfl) ⟨69620, by rfl⟩ : syracuseStep 371309 = 139241) (by norm_num)
theorem B371333 : Blo 243817 371333 := bbase (se 4 (by rfl) ⟨34812, by rfl⟩ : syracuseStep 371333 = 69625) (by norm_num)
theorem B371357 : Blo 243817 371357 := bbase (se 3 (by rfl) ⟨69629, by rfl⟩ : syracuseStep 371357 = 139259) (by norm_num)
theorem B371381 : Blo 243817 371381 := bbase (se 5 (by rfl) ⟨17408, by rfl⟩ : syracuseStep 371381 = 34817) (by norm_num)
theorem B535229 : Blo 243817 535229 := bbase (se 3 (by rfl) ⟨100355, by rfl⟩ : syracuseStep 535229 = 200711) (by norm_num)
theorem B404165 : Blo 243817 404165 := bbase (se 4 (by rfl) ⟨37890, by rfl⟩ : syracuseStep 404165 = 75781) (by norm_num)
theorem B371405 : Blo 243817 371405 := bbase (se 3 (by rfl) ⟨69638, by rfl⟩ : syracuseStep 371405 = 139277) (by norm_num)
theorem B371429 : Blo 243817 371429 := bbase (se 4 (by rfl) ⟨34821, by rfl⟩ : syracuseStep 371429 = 69643) (by norm_num)
theorem B371453 : Blo 243817 371453 := bbase (se 3 (by rfl) ⟨69647, by rfl⟩ : syracuseStep 371453 = 139295) (by norm_num)
theorem B371477 : Blo 243817 371477 := bbase (se 6 (by rfl) ⟨8706, by rfl⟩ : syracuseStep 371477 = 17413) (by norm_num)
theorem B371501 : Blo 243817 371501 := bbase (se 3 (by rfl) ⟨69656, by rfl⟩ : syracuseStep 371501 = 139313) (by norm_num)
theorem B994117 : Blo 243817 994117 := bbase (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) (by norm_num)
theorem B371525 : Blo 243817 371525 := bbase (se 4 (by rfl) ⟨34830, by rfl⟩ : syracuseStep 371525 = 69661) (by norm_num)
theorem B371549 : Blo 243817 371549 := bbase (se 3 (by rfl) ⟨69665, by rfl⟩ : syracuseStep 371549 = 139331) (by norm_num)
theorem B371573 : Blo 243817 371573 := bbase (se 5 (by rfl) ⟨17417, by rfl⟩ : syracuseStep 371573 = 34835) (by norm_num)
theorem B469901 : Blo 243817 469901 := bbase (se 3 (by rfl) ⟨88106, by rfl⟩ : syracuseStep 469901 = 176213) (by norm_num)
theorem B371597 : Blo 243817 371597 := bbase (se 3 (by rfl) ⟨69674, by rfl⟩ : syracuseStep 371597 = 139349) (by norm_num)
theorem B830357 : Blo 243817 830357 := bbase (se 6 (by rfl) ⟨19461, by rfl⟩ : syracuseStep 830357 = 38923) (by norm_num)
theorem B371621 : Blo 243817 371621 := bbase (se 4 (by rfl) ⟨34839, by rfl⟩ : syracuseStep 371621 = 69679) (by norm_num)
theorem B699317 : Blo 243817 699317 := bbase (se 5 (by rfl) ⟨32780, by rfl⟩ : syracuseStep 699317 = 65561) (by norm_num)
theorem B371645 : Blo 243817 371645 := bbase (se 3 (by rfl) ⟨69683, by rfl⟩ : syracuseStep 371645 = 139367) (by norm_num)
theorem B371669 : Blo 243817 371669 := bbase (se 7 (by rfl) ⟨4355, by rfl⟩ : syracuseStep 371669 = 8711) (by norm_num)
theorem B371693 : Blo 243817 371693 := bbase (se 3 (by rfl) ⟨69692, by rfl⟩ : syracuseStep 371693 = 139385) (by norm_num)
theorem B371717 : Blo 243817 371717 := bbase (se 4 (by rfl) ⟨34848, by rfl⟩ : syracuseStep 371717 = 69697) (by norm_num)
theorem B470053 : Blo 243817 470053 := bbase (se 4 (by rfl) ⟨44067, by rfl⟩ : syracuseStep 470053 = 88135) (by norm_num)
theorem B371773 : Blo 243817 371773 := bbase (se 3 (by rfl) ⟨69707, by rfl⟩ : syracuseStep 371773 = 139415) (by norm_num)
theorem B928853 : Blo 243817 928853 := bbase (se 8 (by rfl) ⟨5442, by rfl⟩ : syracuseStep 928853 = 10885) (by norm_num)
theorem B830789 : Blo 243817 830789 := bbase (se 4 (by rfl) ⟨77886, by rfl⟩ : syracuseStep 830789 = 155773) (by norm_num)
theorem B470357 : Blo 243817 470357 := bbase (se 11 (by rfl) ⟨344, by rfl⟩ : syracuseStep 470357 = 689) (by norm_num)
theorem B699749 : Blo 243817 699749 := bbase (se 4 (by rfl) ⟨65601, by rfl⟩ : syracuseStep 699749 = 131203) (by norm_num)
theorem B929141 : Blo 243817 929141 := bbase (se 5 (by rfl) ⟨43553, by rfl⟩ : syracuseStep 929141 = 87107) (by norm_num)
theorem B372109 : Blo 243817 372109 := bbase (se 3 (by rfl) ⟨69770, by rfl⟩ : syracuseStep 372109 = 139541) (by norm_num)
theorem B536149 : Blo 243817 536149 := bbase (se 8 (by rfl) ⟨3141, by rfl⟩ : syracuseStep 536149 = 6283) (by norm_num)
theorem B831221 : Blo 243817 831221 := bbase (se 5 (by rfl) ⟨38963, by rfl⟩ : syracuseStep 831221 = 77927) (by norm_num)
theorem B1781621 : Blo 243817 1781621 := bbase (se 5 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 1781621 = 167027) (by norm_num)
theorem B274297 : Blo 243817 274297 := bbase (se 2 (by rfl) ⟨102861, by rfl⟩ : syracuseStep 274297 = 205723) (by norm_num)
theorem B274333 : Blo 243817 274333 := bbase (se 3 (by rfl) ⟨51437, by rfl⟩ : syracuseStep 274333 = 102875) (by norm_num)
theorem B274369 : Blo 243817 274369 := bbase (se 2 (by rfl) ⟨102888, by rfl⟩ : syracuseStep 274369 = 205777) (by norm_num)
theorem B274405 : Blo 243817 274405 := bbase (se 4 (by rfl) ⟨25725, by rfl⟩ : syracuseStep 274405 = 51451) (by norm_num)
theorem B274441 : Blo 243817 274441 := bbase (se 2 (by rfl) ⟨102915, by rfl⟩ : syracuseStep 274441 = 205831) (by norm_num)
theorem B274477 : Blo 243817 274477 := bbase (se 3 (by rfl) ⟨51464, by rfl⟩ : syracuseStep 274477 = 102929) (by norm_num)
theorem B274513 : Blo 243817 274513 := bbase (se 2 (by rfl) ⟨102942, by rfl⟩ : syracuseStep 274513 = 205885) (by norm_num)
theorem B700501 : Blo 243817 700501 := bbase (se 8 (by rfl) ⟨4104, by rfl⟩ : syracuseStep 700501 = 8209) (by norm_num)
theorem B274549 : Blo 243817 274549 := bbase (se 5 (by rfl) ⟨12869, by rfl⟩ : syracuseStep 274549 = 25739) (by norm_num)
theorem B274585 : Blo 243817 274585 := bbase (se 2 (by rfl) ⟨102969, by rfl⟩ : syracuseStep 274585 = 205939) (by norm_num)
theorem B831653 : Blo 243817 831653 := bbase (se 4 (by rfl) ⟨77967, by rfl⟩ : syracuseStep 831653 = 155935) (by norm_num)
theorem B274621 : Blo 243817 274621 := bbase (se 3 (by rfl) ⟨51491, by rfl⟩ : syracuseStep 274621 = 102983) (by norm_num)
theorem B372941 : Blo 243817 372941 := bbase (se 3 (by rfl) ⟨69926, by rfl⟩ : syracuseStep 372941 = 139853) (by norm_num)
theorem B274657 : Blo 243817 274657 := bbase (se 2 (by rfl) ⟨102996, by rfl⟩ : syracuseStep 274657 = 205993) (by norm_num)
theorem B274693 : Blo 243817 274693 := bbase (se 4 (by rfl) ⟨25752, by rfl⟩ : syracuseStep 274693 = 51505) (by norm_num)
theorem B274729 : Blo 243817 274729 := bbase (se 2 (by rfl) ⟨103023, by rfl⟩ : syracuseStep 274729 = 206047) (by norm_num)
theorem B274765 : Blo 243817 274765 := bbase (se 3 (by rfl) ⟨51518, by rfl⟩ : syracuseStep 274765 = 103037) (by norm_num)
theorem B274801 : Blo 243817 274801 := bbase (se 2 (by rfl) ⟨103050, by rfl⟩ : syracuseStep 274801 = 206101) (by norm_num)
theorem B274837 : Blo 243817 274837 := bbase (se 6 (by rfl) ⟨6441, by rfl⟩ : syracuseStep 274837 = 12883) (by norm_num)
theorem B274873 : Blo 243817 274873 := bbase (se 2 (by rfl) ⟨103077, by rfl⟩ : syracuseStep 274873 = 206155) (by norm_num)
theorem B274909 : Blo 243817 274909 := bbase (se 3 (by rfl) ⟨51545, by rfl⟩ : syracuseStep 274909 = 103091) (by norm_num)
theorem B274945 : Blo 243817 274945 := bbase (se 2 (by rfl) ⟨103104, by rfl⟩ : syracuseStep 274945 = 206209) (by norm_num)
theorem B930325 : Blo 243817 930325 := bbase (se 6 (by rfl) ⟨21804, by rfl⟩ : syracuseStep 930325 = 43609) (by norm_num)
theorem B274981 : Blo 243817 274981 := bbase (se 4 (by rfl) ⟨25779, by rfl⟩ : syracuseStep 274981 = 51559) (by norm_num)
theorem B1389109 : Blo 243817 1389109 := bbase (se 5 (by rfl) ⟨65114, by rfl⟩ : syracuseStep 1389109 = 130229) (by norm_num)
theorem B275017 : Blo 243817 275017 := bbase (se 2 (by rfl) ⟨103131, by rfl⟩ : syracuseStep 275017 = 206263) (by norm_num)
theorem B832085 : Blo 243817 832085 := bbase (se 8 (by rfl) ⟨4875, by rfl⟩ : syracuseStep 832085 = 9751) (by norm_num)
theorem B275053 : Blo 243817 275053 := bbase (se 3 (by rfl) ⟨51572, by rfl⟩ : syracuseStep 275053 = 103145) (by norm_num)
theorem B275089 : Blo 243817 275089 := bbase (se 2 (by rfl) ⟨103158, by rfl⟩ : syracuseStep 275089 = 206317) (by norm_num)
theorem B275125 : Blo 243817 275125 := bbase (se 5 (by rfl) ⟨12896, by rfl⟩ : syracuseStep 275125 = 25793) (by norm_num)
theorem B275161 : Blo 243817 275161 := bbase (se 2 (by rfl) ⟨103185, by rfl⟩ : syracuseStep 275161 = 206371) (by norm_num)
theorem B275197 : Blo 243817 275197 := bbase (se 3 (by rfl) ⟨51599, by rfl⟩ : syracuseStep 275197 = 103199) (by norm_num)
theorem B275233 : Blo 243817 275233 := bbase (se 2 (by rfl) ⟨103212, by rfl⟩ : syracuseStep 275233 = 206425) (by norm_num)
theorem B275269 : Blo 243817 275269 := bbase (se 4 (by rfl) ⟨25806, by rfl⟩ : syracuseStep 275269 = 51613) (by norm_num)
theorem B930629 : Blo 243817 930629 := bbase (se 4 (by rfl) ⟨87246, by rfl⟩ : syracuseStep 930629 = 174493) (by norm_num)
theorem B373573 : Blo 243817 373573 := bbase (se 4 (by rfl) ⟨35022, by rfl⟩ : syracuseStep 373573 = 70045) (by norm_num)
theorem B8926037 : Blo 243817 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B308057 : Blo 243817 308057 := bbase (se 2 (by rfl) ⟨115521, by rfl⟩ : syracuseStep 308057 = 231043) (by norm_num)
theorem B275305 : Blo 243817 275305 := bbase (se 2 (by rfl) ⟨103239, by rfl⟩ : syracuseStep 275305 = 206479) (by norm_num)
theorem B471941 : Blo 243817 471941 := bbase (se 4 (by rfl) ⟨44244, by rfl⟩ : syracuseStep 471941 = 88489) (by norm_num)
theorem B275341 : Blo 243817 275341 := bbase (se 3 (by rfl) ⟨51626, by rfl⟩ : syracuseStep 275341 = 103253) (by norm_num)
theorem B275377 : Blo 243817 275377 := bbase (se 2 (by rfl) ⟨103266, by rfl⟩ : syracuseStep 275377 = 206533) (by norm_num)
theorem B471997 : Blo 243817 471997 := bbase (se 3 (by rfl) ⟨88499, by rfl⟩ : syracuseStep 471997 = 176999) (by norm_num)
theorem B275413 : Blo 243817 275413 := bbase (se 7 (by rfl) ⟨3227, by rfl⟩ : syracuseStep 275413 = 6455) (by norm_num)
theorem B275449 : Blo 243817 275449 := bbase (se 2 (by rfl) ⟨103293, by rfl⟩ : syracuseStep 275449 = 206587) (by norm_num)
theorem B832517 : Blo 243817 832517 := bbase (se 4 (by rfl) ⟨78048, by rfl⟩ : syracuseStep 832517 = 156097) (by norm_num)
theorem B373781 : Blo 243817 373781 := bbase (se 6 (by rfl) ⟨8760, by rfl⟩ : syracuseStep 373781 = 17521) (by norm_num)
theorem B275485 : Blo 243817 275485 := bbase (se 3 (by rfl) ⟨51653, by rfl⟩ : syracuseStep 275485 = 103307) (by norm_num)
theorem B275521 : Blo 243817 275521 := bbase (se 2 (by rfl) ⟨103320, by rfl⟩ : syracuseStep 275521 = 206641) (by norm_num)
theorem B275557 : Blo 243817 275557 := bbase (se 4 (by rfl) ⟨25833, by rfl⟩ : syracuseStep 275557 = 51667) (by norm_num)
theorem B275593 : Blo 243817 275593 := bbase (se 2 (by rfl) ⟨103347, by rfl⟩ : syracuseStep 275593 = 206695) (by norm_num)
theorem B373909 : Blo 243817 373909 := bbase (se 6 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 373909 = 17527) (by norm_num)
theorem B275629 : Blo 243817 275629 := bbase (se 3 (by rfl) ⟨51680, by rfl⟩ : syracuseStep 275629 = 103361) (by norm_num)
theorem B275665 : Blo 243817 275665 := bbase (se 2 (by rfl) ⟨103374, by rfl⟩ : syracuseStep 275665 = 206749) (by norm_num)
theorem B275701 : Blo 243817 275701 := bbase (se 5 (by rfl) ⟨12923, by rfl⟩ : syracuseStep 275701 = 25847) (by norm_num)
theorem B275737 : Blo 243817 275737 := bbase (se 2 (by rfl) ⟨103401, by rfl⟩ : syracuseStep 275737 = 206803) (by norm_num)
theorem B275773 : Blo 243817 275773 := bbase (se 3 (by rfl) ⟨51707, by rfl⟩ : syracuseStep 275773 = 103415) (by norm_num)
theorem B275809 : Blo 243817 275809 := bbase (se 2 (by rfl) ⟨103428, by rfl⟩ : syracuseStep 275809 = 206857) (by norm_num)
theorem B308605 : Blo 243817 308605 := bbase (se 3 (by rfl) ⟨57863, by rfl⟩ : syracuseStep 308605 = 115727) (by norm_num)
theorem B275845 : Blo 243817 275845 := bbase (se 4 (by rfl) ⟨25860, by rfl⟩ : syracuseStep 275845 = 51721) (by norm_num)
theorem B275881 : Blo 243817 275881 := bbase (se 2 (by rfl) ⟨103455, by rfl⟩ : syracuseStep 275881 = 206911) (by norm_num)
theorem B832949 : Blo 243817 832949 := bbase (se 5 (by rfl) ⟨39044, by rfl⟩ : syracuseStep 832949 = 78089) (by norm_num)
theorem B275917 : Blo 243817 275917 := bbase (se 3 (by rfl) ⟨51734, by rfl⟩ : syracuseStep 275917 = 103469) (by norm_num)
theorem B308701 : Blo 243817 308701 := bbase (se 3 (by rfl) ⟨57881, by rfl⟩ : syracuseStep 308701 = 115763) (by norm_num)
theorem B275953 : Blo 243817 275953 := bbase (se 2 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 275953 = 206965) (by norm_num)
theorem B275989 : Blo 243817 275989 := bbase (se 6 (by rfl) ⟨6468, by rfl⟩ : syracuseStep 275989 = 12937) (by norm_num)
theorem B3814933 : Blo 243817 3814933 := bbase (se 6 (by rfl) ⟨89412, by rfl⟩ : syracuseStep 3814933 = 178825) (by norm_num)
theorem B276025 : Blo 243817 276025 := bbase (se 2 (by rfl) ⟨103509, by rfl⟩ : syracuseStep 276025 = 207019) (by norm_num)
theorem B276061 : Blo 243817 276061 := bbase (se 3 (by rfl) ⟨51761, by rfl⟩ : syracuseStep 276061 = 103523) (by norm_num)
theorem B276097 : Blo 243817 276097 := bbase (se 2 (by rfl) ⟨103536, by rfl⟩ : syracuseStep 276097 = 207073) (by norm_num)
theorem B308873 : Blo 243817 308873 := bbase (se 2 (by rfl) ⟨115827, by rfl⟩ : syracuseStep 308873 = 231655) (by norm_num)
theorem B276133 : Blo 243817 276133 := bbase (se 4 (by rfl) ⟨25887, by rfl⟩ : syracuseStep 276133 = 51775) (by norm_num)
theorem B308929 : Blo 243817 308929 := bbase (se 2 (by rfl) ⟨115848, by rfl⟩ : syracuseStep 308929 = 231697) (by norm_num)
theorem B276169 : Blo 243817 276169 := bbase (se 2 (by rfl) ⟨103563, by rfl⟩ : syracuseStep 276169 = 207127) (by norm_num)
theorem B669397 : Blo 243817 669397 := bbase (se 7 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 669397 = 15689) (by norm_num)
theorem B276205 : Blo 243817 276205 := bbase (se 3 (by rfl) ⟨51788, by rfl⟩ : syracuseStep 276205 = 103577) (by norm_num)
theorem B276241 : Blo 243817 276241 := bbase (se 2 (by rfl) ⟨103590, by rfl⟩ : syracuseStep 276241 = 207181) (by norm_num)
theorem B309025 : Blo 243817 309025 := bbase (se 2 (by rfl) ⟨115884, by rfl⟩ : syracuseStep 309025 = 231769) (by norm_num)
theorem B276277 : Blo 243817 276277 := bbase (se 5 (by rfl) ⟨12950, by rfl⟩ : syracuseStep 276277 = 25901) (by norm_num)
theorem B1259333 : Blo 243817 1259333 := bbase (se 4 (by rfl) ⟨118062, by rfl⟩ : syracuseStep 1259333 = 236125) (by norm_num)
theorem B1718101 : Blo 243817 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B505685 : Blo 243817 505685 := bbase (se 9 (by rfl) ⟨1481, by rfl⟩ : syracuseStep 505685 = 2963) (by norm_num)
theorem B276313 : Blo 243817 276313 := bbase (se 2 (by rfl) ⟨103617, by rfl⟩ : syracuseStep 276313 = 207235) (by norm_num)
theorem B833381 : Blo 243817 833381 := bbase (se 4 (by rfl) ⟨78129, by rfl⟩ : syracuseStep 833381 = 156259) (by norm_num)
theorem B276349 : Blo 243817 276349 := bbase (se 3 (by rfl) ⟨51815, by rfl⟩ : syracuseStep 276349 = 103631) (by norm_num)
theorem B276385 : Blo 243817 276385 := bbase (se 2 (by rfl) ⟨103644, by rfl⟩ : syracuseStep 276385 = 207289) (by norm_num)
theorem B276421 : Blo 243817 276421 := bbase (se 4 (by rfl) ⟨25914, by rfl⟩ : syracuseStep 276421 = 51829) (by norm_num)
theorem B309197 : Blo 243817 309197 := bbase (se 3 (by rfl) ⟨57974, by rfl⟩ : syracuseStep 309197 = 115949) (by norm_num)
theorem B276457 : Blo 243817 276457 := bbase (se 2 (by rfl) ⟨103671, by rfl⟩ : syracuseStep 276457 = 207343) (by norm_num)
theorem B309253 : Blo 243817 309253 := bbase (se 4 (by rfl) ⟨28992, by rfl⟩ : syracuseStep 309253 = 57985) (by norm_num)
theorem B276493 : Blo 243817 276493 := bbase (se 3 (by rfl) ⟨51842, by rfl⟩ : syracuseStep 276493 = 103685) (by norm_num)
theorem B276529 : Blo 243817 276529 := bbase (se 2 (by rfl) ⟨103698, by rfl⟩ : syracuseStep 276529 = 207397) (by norm_num)
theorem B276565 : Blo 243817 276565 := bbase (se 8 (by rfl) ⟨1620, by rfl⟩ : syracuseStep 276565 = 3241) (by norm_num)
theorem B309349 : Blo 243817 309349 := bbase (se 4 (by rfl) ⟨29001, by rfl⟩ : syracuseStep 309349 = 58003) (by norm_num)
theorem B276601 : Blo 243817 276601 := bbase (se 2 (by rfl) ⟨103725, by rfl⟩ : syracuseStep 276601 = 207451) (by norm_num)
theorem B276637 : Blo 243817 276637 := bbase (se 3 (by rfl) ⟨51869, by rfl⟩ : syracuseStep 276637 = 103739) (by norm_num)
theorem B276673 : Blo 243817 276673 := bbase (se 2 (by rfl) ⟨103752, by rfl⟩ : syracuseStep 276673 = 207505) (by norm_num)
theorem B276709 : Blo 243817 276709 := bbase (se 4 (by rfl) ⟨25941, by rfl⟩ : syracuseStep 276709 = 51883) (by norm_num)
theorem B276745 : Blo 243817 276745 := bbase (se 2 (by rfl) ⟨103779, by rfl⟩ : syracuseStep 276745 = 207559) (by norm_num)
theorem B309521 : Blo 243817 309521 := bbase (se 2 (by rfl) ⟨116070, by rfl⟩ : syracuseStep 309521 = 232141) (by norm_num)
theorem B833813 : Blo 243817 833813 := bbase (se 6 (by rfl) ⟨19542, by rfl⟩ : syracuseStep 833813 = 39085) (by norm_num)
theorem B276781 : Blo 243817 276781 := bbase (se 3 (by rfl) ⟨51896, by rfl⟩ : syracuseStep 276781 = 103793) (by norm_num)
theorem B309577 : Blo 243817 309577 := bbase (se 2 (by rfl) ⟨116091, by rfl⟩ : syracuseStep 309577 = 232183) (by norm_num)
theorem B276817 : Blo 243817 276817 := bbase (se 2 (by rfl) ⟨103806, by rfl⟩ : syracuseStep 276817 = 207613) (by norm_num)
theorem B440677 : Blo 243817 440677 := bbase (se 4 (by rfl) ⟨41313, by rfl⟩ : syracuseStep 440677 = 82627) (by norm_num)
theorem B276853 : Blo 243817 276853 := bbase (se 5 (by rfl) ⟨12977, by rfl⟩ : syracuseStep 276853 = 25955) (by norm_num)
theorem B276889 : Blo 243817 276889 := bbase (se 2 (by rfl) ⟨103833, by rfl⟩ : syracuseStep 276889 = 207667) (by norm_num)
theorem B309673 : Blo 243817 309673 := bbase (se 2 (by rfl) ⟨116127, by rfl⟩ : syracuseStep 309673 = 232255) (by norm_num)
theorem B440749 : Blo 243817 440749 := bbase (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) (by norm_num)
theorem B276925 : Blo 243817 276925 := bbase (se 3 (by rfl) ⟨51923, by rfl⟩ : syracuseStep 276925 = 103847) (by norm_num)
theorem B276961 : Blo 243817 276961 := bbase (se 2 (by rfl) ⟨103860, by rfl⟩ : syracuseStep 276961 = 207721) (by norm_num)
theorem B1391093 : Blo 243817 1391093 := bbase (se 5 (by rfl) ⟨65207, by rfl⟩ : syracuseStep 1391093 = 130415) (by norm_num)
theorem B276997 : Blo 243817 276997 := bbase (se 4 (by rfl) ⟨25968, by rfl⟩ : syracuseStep 276997 = 51937) (by norm_num)
theorem B277033 : Blo 243817 277033 := bbase (se 2 (by rfl) ⟨103887, by rfl⟩ : syracuseStep 277033 = 207775) (by norm_num)
theorem B277069 : Blo 243817 277069 := bbase (se 3 (by rfl) ⟨51950, by rfl⟩ : syracuseStep 277069 = 103901) (by norm_num)
theorem B309845 : Blo 243817 309845 := bbase (se 8 (by rfl) ⟨1815, by rfl⟩ : syracuseStep 309845 = 3631) (by norm_num)
theorem B277105 : Blo 243817 277105 := bbase (se 2 (by rfl) ⟨103914, by rfl⟩ : syracuseStep 277105 = 207829) (by norm_num)
theorem B309901 : Blo 243817 309901 := bbase (se 3 (by rfl) ⟨58106, by rfl⟩ : syracuseStep 309901 = 116213) (by norm_num)
theorem B277141 : Blo 243817 277141 := bbase (se 6 (by rfl) ⟨6495, by rfl⟩ : syracuseStep 277141 = 12991) (by norm_num)
theorem B1522357 : Blo 243817 1522357 := bbase (se 5 (by rfl) ⟨71360, by rfl⟩ : syracuseStep 1522357 = 142721) (by norm_num)
theorem B277177 : Blo 243817 277177 := bbase (se 2 (by rfl) ⟨103941, by rfl⟩ : syracuseStep 277177 = 207883) (by norm_num)
theorem B834245 : Blo 243817 834245 := bbase (se 4 (by rfl) ⟨78210, by rfl⟩ : syracuseStep 834245 = 156421) (by norm_num)
theorem B277213 : Blo 243817 277213 := bbase (se 3 (by rfl) ⟨51977, by rfl⟩ : syracuseStep 277213 = 103955) (by norm_num)
theorem B309997 : Blo 243817 309997 := bbase (se 3 (by rfl) ⟨58124, by rfl⟩ : syracuseStep 309997 = 116249) (by norm_num)
theorem B277249 : Blo 243817 277249 := bbase (se 2 (by rfl) ⟨103968, by rfl⟩ : syracuseStep 277249 = 207937) (by norm_num)
theorem B277285 : Blo 243817 277285 := bbase (se 4 (by rfl) ⟨25995, by rfl⟩ : syracuseStep 277285 = 51991) (by norm_num)
theorem B277321 : Blo 243817 277321 := bbase (se 2 (by rfl) ⟨103995, by rfl⟩ : syracuseStep 277321 = 207991) (by norm_num)
theorem B277357 : Blo 243817 277357 := bbase (se 3 (by rfl) ⟨52004, by rfl⟩ : syracuseStep 277357 = 104009) (by norm_num)
theorem B703349 : Blo 243817 703349 := bbase (se 5 (by rfl) ⟨32969, by rfl⟩ : syracuseStep 703349 = 65939) (by norm_num)
theorem B932741 : Blo 243817 932741 := bbase (se 4 (by rfl) ⟨87444, by rfl⟩ : syracuseStep 932741 = 174889) (by norm_num)
theorem B277393 : Blo 243817 277393 := bbase (se 2 (by rfl) ⟨104022, by rfl⟩ : syracuseStep 277393 = 208045) (by norm_num)
theorem B310169 : Blo 243817 310169 := bbase (se 2 (by rfl) ⟨116313, by rfl⟩ : syracuseStep 310169 = 232627) (by norm_num)
theorem B539549 : Blo 243817 539549 := bbase (se 3 (by rfl) ⟨101165, by rfl⟩ : syracuseStep 539549 = 202331) (by norm_num)
theorem B441253 : Blo 243817 441253 := bbase (se 4 (by rfl) ⟨41367, by rfl⟩ : syracuseStep 441253 = 82735) (by norm_num)
theorem B277429 : Blo 243817 277429 := bbase (se 5 (by rfl) ⟨13004, by rfl⟩ : syracuseStep 277429 = 26009) (by norm_num)
theorem B310225 : Blo 243817 310225 := bbase (se 2 (by rfl) ⟨116334, by rfl⟩ : syracuseStep 310225 = 232669) (by norm_num)
theorem B277465 : Blo 243817 277465 := bbase (se 2 (by rfl) ⟨104049, by rfl⟩ : syracuseStep 277465 = 208099) (by norm_num)
theorem B277501 : Blo 243817 277501 := bbase (se 3 (by rfl) ⟨52031, by rfl⟩ : syracuseStep 277501 = 104063) (by norm_num)
theorem B277537 : Blo 243817 277537 := bbase (se 2 (by rfl) ⟨104076, by rfl⟩ : syracuseStep 277537 = 208153) (by norm_num)
theorem B310321 : Blo 243817 310321 := bbase (se 2 (by rfl) ⟨116370, by rfl⟩ : syracuseStep 310321 = 232741) (by norm_num)
theorem B277573 : Blo 243817 277573 := bbase (se 4 (by rfl) ⟨26022, by rfl⟩ : syracuseStep 277573 = 52045) (by norm_num)
theorem B277609 : Blo 243817 277609 := bbase (se 2 (by rfl) ⟨104103, by rfl⟩ : syracuseStep 277609 = 208207) (by norm_num)
theorem B474221 : Blo 243817 474221 := bbase (se 3 (by rfl) ⟨88916, by rfl⟩ : syracuseStep 474221 = 177833) (by norm_num)
theorem B834677 : Blo 243817 834677 := bbase (se 5 (by rfl) ⟨39125, by rfl⟩ : syracuseStep 834677 = 78251) (by norm_num)
theorem B277645 : Blo 243817 277645 := bbase (se 3 (by rfl) ⟨52058, by rfl⟩ : syracuseStep 277645 = 104117) (by norm_num)
theorem B933029 : Blo 243817 933029 := bbase (se 4 (by rfl) ⟨87471, by rfl⟩ : syracuseStep 933029 = 174943) (by norm_num)
theorem B277681 : Blo 243817 277681 := bbase (se 2 (by rfl) ⟨104130, by rfl⟩ : syracuseStep 277681 = 208261) (by norm_num)
theorem B277717 : Blo 243817 277717 := bbase (se 7 (by rfl) ⟨3254, by rfl⟩ : syracuseStep 277717 = 6509) (by norm_num)
theorem B310493 : Blo 243817 310493 := bbase (se 3 (by rfl) ⟨58217, by rfl⟩ : syracuseStep 310493 = 116435) (by norm_num)
theorem B277753 : Blo 243817 277753 := bbase (se 2 (by rfl) ⟨104157, by rfl⟩ : syracuseStep 277753 = 208315) (by norm_num)
theorem B310549 : Blo 243817 310549 := bbase (se 6 (by rfl) ⟨7278, by rfl⟩ : syracuseStep 310549 = 14557) (by norm_num)
theorem B277789 : Blo 243817 277789 := bbase (se 3 (by rfl) ⟨52085, by rfl⟩ : syracuseStep 277789 = 104171) (by norm_num)
theorem B507197 : Blo 243817 507197 := bbase (se 3 (by rfl) ⟨95099, by rfl⟩ : syracuseStep 507197 = 190199) (by norm_num)
theorem B277825 : Blo 243817 277825 := bbase (se 2 (by rfl) ⟨104184, by rfl⟩ : syracuseStep 277825 = 208369) (by norm_num)
theorem B998725 : Blo 243817 998725 := bbase (se 4 (by rfl) ⟨93630, by rfl⟩ : syracuseStep 998725 = 187261) (by norm_num)
theorem B277861 : Blo 243817 277861 := bbase (se 4 (by rfl) ⟨26049, by rfl⟩ : syracuseStep 277861 = 52099) (by norm_num)
theorem B310645 : Blo 243817 310645 := bbase (se 5 (by rfl) ⟨14561, by rfl⟩ : syracuseStep 310645 = 29123) (by norm_num)
theorem B277897 : Blo 243817 277897 := bbase (se 2 (by rfl) ⟨104211, by rfl⟩ : syracuseStep 277897 = 208423) (by norm_num)
theorem B277933 : Blo 243817 277933 := bbase (se 3 (by rfl) ⟨52112, by rfl⟩ : syracuseStep 277933 = 104225) (by norm_num)
theorem B277969 : Blo 243817 277969 := bbase (se 2 (by rfl) ⟨104238, by rfl⟩ : syracuseStep 277969 = 208477) (by norm_num)
theorem B278005 : Blo 243817 278005 := bbase (se 5 (by rfl) ⟨13031, by rfl⟩ : syracuseStep 278005 = 26063) (by norm_num)
theorem B900629 : Blo 243817 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B278041 : Blo 243817 278041 := bbase (se 2 (by rfl) ⟨104265, by rfl⟩ : syracuseStep 278041 = 208531) (by norm_num)
theorem B310817 : Blo 243817 310817 := bbase (se 2 (by rfl) ⟨116556, by rfl⟩ : syracuseStep 310817 = 233113) (by norm_num)
theorem B835109 : Blo 243817 835109 := bbase (se 4 (by rfl) ⟨78291, by rfl⟩ : syracuseStep 835109 = 156583) (by norm_num)
theorem B441917 : Blo 243817 441917 := bbase (se 3 (by rfl) ⟨82859, by rfl⟩ : syracuseStep 441917 = 165719) (by norm_num)
theorem B278077 : Blo 243817 278077 := bbase (se 3 (by rfl) ⟨52139, by rfl⟩ : syracuseStep 278077 = 104279) (by norm_num)
theorem B310873 : Blo 243817 310873 := bbase (se 2 (by rfl) ⟨116577, by rfl⟩ : syracuseStep 310873 = 233155) (by norm_num)
theorem B278113 : Blo 243817 278113 := bbase (se 2 (by rfl) ⟨104292, by rfl⟩ : syracuseStep 278113 = 208585) (by norm_num)
theorem B278149 : Blo 243817 278149 := bbase (se 4 (by rfl) ⟨26076, by rfl⟩ : syracuseStep 278149 = 52153) (by norm_num)
theorem B278185 : Blo 243817 278185 := bbase (se 2 (by rfl) ⟨104319, by rfl⟩ : syracuseStep 278185 = 208639) (by norm_num)
theorem B310969 : Blo 243817 310969 := bbase (se 2 (by rfl) ⟨116613, by rfl⟩ : syracuseStep 310969 = 233227) (by norm_num)
theorem B278221 : Blo 243817 278221 := bbase (se 3 (by rfl) ⟨52166, by rfl⟩ : syracuseStep 278221 = 104333) (by norm_num)
theorem B278257 : Blo 243817 278257 := bbase (se 2 (by rfl) ⟨104346, by rfl⟩ : syracuseStep 278257 = 208693) (by norm_num)
theorem B278293 : Blo 243817 278293 := bbase (se 6 (by rfl) ⟨6522, by rfl⟩ : syracuseStep 278293 = 13045) (by norm_num)
theorem B278329 : Blo 243817 278329 := bbase (se 2 (by rfl) ⟨104373, by rfl⟩ : syracuseStep 278329 = 208747) (by norm_num)
theorem B278365 : Blo 243817 278365 := bbase (se 3 (by rfl) ⟨52193, by rfl⟩ : syracuseStep 278365 = 104387) (by norm_num)
theorem B311141 : Blo 243817 311141 := bbase (se 4 (by rfl) ⟨29169, by rfl⟩ : syracuseStep 311141 = 58339) (by norm_num)
theorem B278401 : Blo 243817 278401 := bbase (se 2 (by rfl) ⟨104400, by rfl⟩ : syracuseStep 278401 = 208801) (by norm_num)
theorem B311197 : Blo 243817 311197 := bbase (se 3 (by rfl) ⟨58349, by rfl⟩ : syracuseStep 311197 = 116699) (by norm_num)
theorem B278437 : Blo 243817 278437 := bbase (se 4 (by rfl) ⟨26103, by rfl⟩ : syracuseStep 278437 = 52207) (by norm_num)
theorem B278473 : Blo 243817 278473 := bbase (se 2 (by rfl) ⟨104427, by rfl⟩ : syracuseStep 278473 = 208855) (by norm_num)
theorem B835541 : Blo 243817 835541 := bbase (se 7 (by rfl) ⟨9791, by rfl⟩ : syracuseStep 835541 = 19583) (by norm_num)
theorem B278509 : Blo 243817 278509 := bbase (se 3 (by rfl) ⟨52220, by rfl⟩ : syracuseStep 278509 = 104441) (by norm_num)
theorem B311293 : Blo 243817 311293 := bbase (se 3 (by rfl) ⟨58367, by rfl⟩ : syracuseStep 311293 = 116735) (by norm_num)
theorem B278545 : Blo 243817 278545 := bbase (se 2 (by rfl) ⟨104454, by rfl⟩ : syracuseStep 278545 = 208909) (by norm_num)
theorem B704533 : Blo 243817 704533 := bbase (se 6 (by rfl) ⟨16512, by rfl⟩ : syracuseStep 704533 = 33025) (by norm_num)
theorem B278581 : Blo 243817 278581 := bbase (se 5 (by rfl) ⟨13058, by rfl⟩ : syracuseStep 278581 = 26117) (by norm_num)
theorem B278617 : Blo 243817 278617 := bbase (se 2 (by rfl) ⟨104481, by rfl⟩ : syracuseStep 278617 = 208963) (by norm_num)
theorem B278629 : Blo 243817 278629 := bbase (se 4 (by rfl) ⟨26121, by rfl⟩ : syracuseStep 278629 = 52243) (by norm_num)
theorem B278653 : Blo 243817 278653 := bbase (se 3 (by rfl) ⟨52247, by rfl⟩ : syracuseStep 278653 = 104495) (by norm_num)
theorem B606341 : Blo 243817 606341 := bbase (se 4 (by rfl) ⟨56844, by rfl⟩ : syracuseStep 606341 = 113689) (by norm_num)
theorem B278689 : Blo 243817 278689 := bbase (se 2 (by rfl) ⟨104508, by rfl⟩ : syracuseStep 278689 = 209017) (by norm_num)
theorem B311465 : Blo 243817 311465 := bbase (se 2 (by rfl) ⟨116799, by rfl⟩ : syracuseStep 311465 = 233599) (by norm_num)
theorem B704693 : Blo 243817 704693 := bbase (se 5 (by rfl) ⟨33032, by rfl⟩ : syracuseStep 704693 = 66065) (by norm_num)
theorem B278725 : Blo 243817 278725 := bbase (se 4 (by rfl) ⟨26130, by rfl⟩ : syracuseStep 278725 = 52261) (by norm_num)
theorem B311521 : Blo 243817 311521 := bbase (se 2 (by rfl) ⟨116820, by rfl⟩ : syracuseStep 311521 = 233641) (by norm_num)
theorem B278761 : Blo 243817 278761 := bbase (se 2 (by rfl) ⟨104535, by rfl⟩ : syracuseStep 278761 = 209071) (by norm_num)
theorem B278825 : Blo 243817 278825 := bbase (se 2 (by rfl) ⟨104559, by rfl⟩ : syracuseStep 278825 = 209119) (by norm_num)
theorem B475445 : Blo 243817 475445 := bbase (se 5 (by rfl) ⟨22286, by rfl⟩ : syracuseStep 475445 = 44573) (by norm_num)
theorem B311617 : Blo 243817 311617 := bbase (se 2 (by rfl) ⟨116856, by rfl⟩ : syracuseStep 311617 = 233713) (by norm_num)
theorem B934213 : Blo 243817 934213 := bbase (se 4 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 934213 = 175165) (by norm_num)
theorem B835973 : Blo 243817 835973 := bbase (se 4 (by rfl) ⟨78372, by rfl⟩ : syracuseStep 835973 = 156745) (by norm_num)
theorem B409997 : Blo 243817 409997 := bbase (se 3 (by rfl) ⟨76874, by rfl⟩ : syracuseStep 409997 = 153749) (by norm_num)
theorem B704933 : Blo 243817 704933 := bbase (se 4 (by rfl) ⟨66087, by rfl⟩ : syracuseStep 704933 = 132175) (by norm_num)
theorem B311789 : Blo 243817 311789 := bbase (se 3 (by rfl) ⟨58460, by rfl⟩ : syracuseStep 311789 = 116921) (by norm_num)
theorem B311845 : Blo 243817 311845 := bbase (se 4 (by rfl) ⟨29235, by rfl⟩ : syracuseStep 311845 = 58471) (by norm_num)
theorem B279085 : Blo 243817 279085 := bbase (se 3 (by rfl) ⟨52328, by rfl⟩ : syracuseStep 279085 = 104657) (by norm_num)
theorem B705125 : Blo 243817 705125 := bbase (se 4 (by rfl) ⟨66105, by rfl⟩ : syracuseStep 705125 = 132211) (by norm_num)
theorem B934517 : Blo 243817 934517 := bbase (se 5 (by rfl) ⟨43805, by rfl⟩ : syracuseStep 934517 = 87611) (by norm_num)
theorem B311941 : Blo 243817 311941 := bbase (se 4 (by rfl) ⟨29244, by rfl⟩ : syracuseStep 311941 = 58489) (by norm_num)
theorem B1393301 : Blo 243817 1393301 := bbase (se 6 (by rfl) ⟨32655, by rfl⟩ : syracuseStep 1393301 = 65311) (by norm_num)
theorem B508717 : Blo 243817 508717 := bbase (se 3 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 508717 = 190769) (by norm_num)
theorem B312113 : Blo 243817 312113 := bbase (se 2 (by rfl) ⟨117042, by rfl⟩ : syracuseStep 312113 = 234085) (by norm_num)
theorem B312169 : Blo 243817 312169 := bbase (se 2 (by rfl) ⟨117063, by rfl⟩ : syracuseStep 312169 = 234127) (by norm_num)
theorem B312265 : Blo 243817 312265 := bbase (se 2 (by rfl) ⟨117099, by rfl⟩ : syracuseStep 312265 = 234199) (by norm_num)
theorem B312437 : Blo 243817 312437 := bbase (se 5 (by rfl) ⟨14645, by rfl⟩ : syracuseStep 312437 = 29291) (by norm_num)
theorem B312493 : Blo 243817 312493 := bbase (se 3 (by rfl) ⟨58592, by rfl⟩ : syracuseStep 312493 = 117185) (by norm_num)
theorem B312589 : Blo 243817 312589 := bbase (se 3 (by rfl) ⟨58610, by rfl⟩ : syracuseStep 312589 = 117221) (by norm_num)
theorem B312761 : Blo 243817 312761 := bbase (se 2 (by rfl) ⟨117285, by rfl⟩ : syracuseStep 312761 = 234571) (by norm_num)
theorem B247249 : Blo 243817 247249 := bbase (se 2 (by rfl) ⟨92718, by rfl⟩ : syracuseStep 247249 = 185437) (by norm_num)
theorem B312817 : Blo 243817 312817 := bbase (se 2 (by rfl) ⟨117306, by rfl⟩ : syracuseStep 312817 = 234613) (by norm_num)
theorem B247297 : Blo 243817 247297 := bbase (se 2 (by rfl) ⟨92736, by rfl⟩ : syracuseStep 247297 = 185473) (by norm_num)
theorem B312913 : Blo 243817 312913 := bbase (se 2 (by rfl) ⟨117342, by rfl⟩ : syracuseStep 312913 = 234685) (by norm_num)
theorem B313085 : Blo 243817 313085 := bbase (se 3 (by rfl) ⟨58703, by rfl⟩ : syracuseStep 313085 = 117407) (by norm_num)
theorem B313141 : Blo 243817 313141 := bbase (se 5 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 313141 = 29357) (by norm_num)
theorem B411493 : Blo 243817 411493 := bbase (se 4 (by rfl) ⟨38577, by rfl⟩ : syracuseStep 411493 = 77155) (by norm_num)
theorem B313237 : Blo 243817 313237 := bbase (se 6 (by rfl) ⟨7341, by rfl⟩ : syracuseStep 313237 = 14683) (by norm_num)
theorem B411581 : Blo 243817 411581 := bbase (se 3 (by rfl) ⟨77171, by rfl⟩ : syracuseStep 411581 = 154343) (by norm_num)
theorem B280541 : Blo 243817 280541 := bbase (se 3 (by rfl) ⟨52601, by rfl⟩ : syracuseStep 280541 = 105203) (by norm_num)
theorem B280577 : Blo 243817 280577 := bbase (se 2 (by rfl) ⟨105216, by rfl⟩ : syracuseStep 280577 = 210433) (by norm_num)
theorem B2803733 : Blo 243817 2803733 := bbase (se 6 (by rfl) ⟨65712, by rfl⟩ : syracuseStep 2803733 = 131425) (by norm_num)
theorem B411709 : Blo 243817 411709 := bbase (se 3 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 411709 = 154391) (by norm_num)
theorem B313409 : Blo 243817 313409 := bbase (se 2 (by rfl) ⟨117528, by rfl⟩ : syracuseStep 313409 = 235057) (by norm_num)
theorem B12863573 : Blo 243817 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B313465 : Blo 243817 313465 := bbase (se 2 (by rfl) ⟨117549, by rfl⟩ : syracuseStep 313465 = 235099) (by norm_num)
theorem B444541 : Blo 243817 444541 := bbase (se 3 (by rfl) ⟨83351, by rfl⟩ : syracuseStep 444541 = 166703) (by norm_num)
theorem B411797 : Blo 243817 411797 := bbase (se 6 (by rfl) ⟨9651, by rfl⟩ : syracuseStep 411797 = 19303) (by norm_num)
theorem B313561 : Blo 243817 313561 := bbase (se 2 (by rfl) ⟨117585, by rfl⟩ : syracuseStep 313561 = 235171) (by norm_num)
theorem B444685 : Blo 243817 444685 := bbase (se 3 (by rfl) ⟨83378, by rfl⟩ : syracuseStep 444685 = 166757) (by norm_num)
theorem B411925 : Blo 243817 411925 := bbase (se 6 (by rfl) ⟨9654, by rfl⟩ : syracuseStep 411925 = 19309) (by norm_num)
theorem B248141 : Blo 243817 248141 := bbase (se 3 (by rfl) ⟨46526, by rfl⟩ : syracuseStep 248141 = 93053) (by norm_num)
theorem B412013 : Blo 243817 412013 := bbase (se 3 (by rfl) ⟨77252, by rfl⟩ : syracuseStep 412013 = 154505) (by norm_num)
theorem B248189 : Blo 243817 248189 := bbase (se 3 (by rfl) ⟨46535, by rfl⟩ : syracuseStep 248189 = 93071) (by norm_num)
theorem B444845 : Blo 243817 444845 := bbase (se 3 (by rfl) ⟨83408, by rfl⟩ : syracuseStep 444845 = 166817) (by norm_num)
theorem B444901 : Blo 243817 444901 := bbase (se 4 (by rfl) ⟨41709, by rfl⟩ : syracuseStep 444901 = 83419) (by norm_num)
theorem B412141 : Blo 243817 412141 := bbase (se 3 (by rfl) ⟨77276, by rfl⟩ : syracuseStep 412141 = 154553) (by norm_num)
theorem B2378261 : Blo 243817 2378261 := bbase (se 6 (by rfl) ⟨55740, by rfl⟩ : syracuseStep 2378261 = 111481) (by norm_num)
theorem B412229 : Blo 243817 412229 := bbase (se 4 (by rfl) ⟨38646, by rfl⟩ : syracuseStep 412229 = 77293) (by norm_num)
theorem B248465 : Blo 243817 248465 := bbase (se 2 (by rfl) ⟨93174, by rfl⟩ : syracuseStep 248465 = 186349) (by norm_num)
theorem B248497 : Blo 243817 248497 := bbase (se 2 (by rfl) ⟨93186, by rfl⟩ : syracuseStep 248497 = 186373) (by norm_num)
theorem B936629 : Blo 243817 936629 := bbase (se 5 (by rfl) ⟨43904, by rfl⟩ : syracuseStep 936629 = 87809) (by norm_num)
theorem B412357 : Blo 243817 412357 := bbase (se 4 (by rfl) ⟨38658, by rfl⟩ : syracuseStep 412357 = 77317) (by norm_num)
theorem B412445 : Blo 243817 412445 := bbase (se 3 (by rfl) ⟨77333, by rfl⟩ : syracuseStep 412445 = 154667) (by norm_num)
theorem B2116469 : Blo 243817 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B412573 : Blo 243817 412573 := bbase (se 3 (by rfl) ⟨77357, by rfl⟩ : syracuseStep 412573 = 154715) (by norm_num)
theorem B248789 : Blo 243817 248789 := bbase (se 7 (by rfl) ⟨2915, by rfl⟩ : syracuseStep 248789 = 5831) (by norm_num)
theorem B936917 : Blo 243817 936917 := bbase (se 7 (by rfl) ⟨10979, by rfl⟩ : syracuseStep 936917 = 21959) (by norm_num)
theorem B412661 : Blo 243817 412661 := bbase (se 5 (by rfl) ⟨19343, by rfl⟩ : syracuseStep 412661 = 38687) (by norm_num)
theorem B412789 : Blo 243817 412789 := bbase (se 5 (by rfl) ⟨19349, by rfl⟩ : syracuseStep 412789 = 38699) (by norm_num)
theorem B314501 : Blo 243817 314501 := bbase (se 4 (by rfl) ⟨29484, by rfl⟩ : syracuseStep 314501 = 58969) (by norm_num)
theorem B412877 : Blo 243817 412877 := bbase (se 3 (by rfl) ⟨77414, by rfl⟩ : syracuseStep 412877 = 154829) (by norm_num)
theorem B347437 : Blo 243817 347437 := bbase (se 3 (by rfl) ⟨65144, by rfl⟩ : syracuseStep 347437 = 130289) (by norm_num)
theorem B413005 : Blo 243817 413005 := bbase (se 3 (by rfl) ⟨77438, by rfl⟩ : syracuseStep 413005 = 154877) (by norm_num)
theorem B1264997 : Blo 243817 1264997 := bbase (se 4 (by rfl) ⟨118593, by rfl⟩ : syracuseStep 1264997 = 237187) (by norm_num)
theorem B413093 : Blo 243817 413093 := bbase (se 4 (by rfl) ⟨38727, by rfl⟩ : syracuseStep 413093 = 77455) (by norm_num)
theorem B413221 : Blo 243817 413221 := bbase (se 4 (by rfl) ⟨38739, by rfl⟩ : syracuseStep 413221 = 77479) (by norm_num)
theorem B1855061 : Blo 243817 1855061 := bbase (se 8 (by rfl) ⟨10869, by rfl⟩ : syracuseStep 1855061 = 21739) (by norm_num)
theorem B446069 : Blo 243817 446069 := bbase (se 5 (by rfl) ⟨20909, by rfl⟩ : syracuseStep 446069 = 41819) (by norm_num)
theorem B413309 : Blo 243817 413309 := bbase (se 3 (by rfl) ⟨77495, by rfl⟩ : syracuseStep 413309 = 154991) (by norm_num)
theorem B413437 : Blo 243817 413437 := bbase (se 3 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 413437 = 155039) (by norm_num)
theorem B413525 : Blo 243817 413525 := bbase (se 9 (by rfl) ⟨1211, by rfl⟩ : syracuseStep 413525 = 2423) (by norm_num)
theorem B413653 : Blo 243817 413653 := bbase (se 7 (by rfl) ⟨4847, by rfl⟩ : syracuseStep 413653 = 9695) (by norm_num)
theorem B413741 : Blo 243817 413741 := bbase (se 3 (by rfl) ⟨77576, by rfl⟩ : syracuseStep 413741 = 155153) (by norm_num)
theorem B348229 : Blo 243817 348229 := bbase (se 4 (by rfl) ⟨32646, by rfl⟩ : syracuseStep 348229 = 65293) (by norm_num)
theorem B1986677 : Blo 243817 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B938101 : Blo 243817 938101 := bbase (se 5 (by rfl) ⟨43973, by rfl⟩ : syracuseStep 938101 = 87947) (by norm_num)
theorem B413869 : Blo 243817 413869 := bbase (se 3 (by rfl) ⟨77600, by rfl⟩ : syracuseStep 413869 = 155201) (by norm_num)
theorem B413957 : Blo 243817 413957 := bbase (se 4 (by rfl) ⟨38808, by rfl⟩ : syracuseStep 413957 = 77617) (by norm_num)
theorem B414085 : Blo 243817 414085 := bbase (se 4 (by rfl) ⟨38820, by rfl⟩ : syracuseStep 414085 = 77641) (by norm_num)
theorem B348565 : Blo 243817 348565 := bbase (se 6 (by rfl) ⟨8169, by rfl⟩ : syracuseStep 348565 = 16339) (by norm_num)
theorem B938405 : Blo 243817 938405 := bbase (se 4 (by rfl) ⟨87975, by rfl⟩ : syracuseStep 938405 = 175951) (by norm_num)
theorem B414173 : Blo 243817 414173 := bbase (se 3 (by rfl) ⟨77657, by rfl⟩ : syracuseStep 414173 = 155315) (by norm_num)
theorem B414301 : Blo 243817 414301 := bbase (se 3 (by rfl) ⟨77681, by rfl⟩ : syracuseStep 414301 = 155363) (by norm_num)
theorem B348781 : Blo 243817 348781 := bbase (se 3 (by rfl) ⟨65396, by rfl⟩ : syracuseStep 348781 = 130793) (by norm_num)
theorem B414389 : Blo 243817 414389 := bbase (se 5 (by rfl) ⟨19424, by rfl⟩ : syracuseStep 414389 = 38849) (by norm_num)
theorem B414517 : Blo 243817 414517 := bbase (se 5 (by rfl) ⟨19430, by rfl⟩ : syracuseStep 414517 = 38861) (by norm_num)
theorem B414605 : Blo 243817 414605 := bbase (se 3 (by rfl) ⟨77738, by rfl⟩ : syracuseStep 414605 = 155477) (by norm_num)
theorem B349157 : Blo 243817 349157 := bbase (se 4 (by rfl) ⟨32733, by rfl⟩ : syracuseStep 349157 = 65467) (by norm_num)
theorem B414733 : Blo 243817 414733 := bbase (se 3 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 414733 = 155525) (by norm_num)
theorem B414821 : Blo 243817 414821 := bbase (se 4 (by rfl) ⟨38889, by rfl⟩ : syracuseStep 414821 = 77779) (by norm_num)
theorem B251101 : Blo 243817 251101 := bbase (se 3 (by rfl) ⟨47081, by rfl⟩ : syracuseStep 251101 = 94163) (by norm_num)
theorem B414949 : Blo 243817 414949 := bbase (se 4 (by rfl) ⟨38901, by rfl⟩ : syracuseStep 414949 = 77803) (by norm_num)
theorem B415037 : Blo 243817 415037 := bbase (se 3 (by rfl) ⟨77819, by rfl⟩ : syracuseStep 415037 = 155639) (by norm_num)
theorem B415165 : Blo 243817 415165 := bbase (se 3 (by rfl) ⟨77843, by rfl⟩ : syracuseStep 415165 = 155687) (by norm_num)
theorem B415253 : Blo 243817 415253 := bbase (se 6 (by rfl) ⟨9732, by rfl⟩ : syracuseStep 415253 = 19465) (by norm_num)
theorem B415381 : Blo 243817 415381 := bbase (se 6 (by rfl) ⟨9735, by rfl⟩ : syracuseStep 415381 = 19471) (by norm_num)
theorem B415469 : Blo 243817 415469 := bbase (se 3 (by rfl) ⟨77900, by rfl⟩ : syracuseStep 415469 = 155801) (by norm_num)
theorem B415597 : Blo 243817 415597 := bbase (se 3 (by rfl) ⟨77924, by rfl⟩ : syracuseStep 415597 = 155849) (by norm_num)
theorem B382837 : Blo 243817 382837 := bbase (se 5 (by rfl) ⟨17945, by rfl⟩ : syracuseStep 382837 = 35891) (by norm_num)
theorem B415685 : Blo 243817 415685 := bbase (se 4 (by rfl) ⟨38970, by rfl⟩ : syracuseStep 415685 = 77941) (by norm_num)
theorem B415813 : Blo 243817 415813 := bbase (se 4 (by rfl) ⟨38982, by rfl⟩ : syracuseStep 415813 = 77965) (by norm_num)
theorem B415901 : Blo 243817 415901 := bbase (se 3 (by rfl) ⟨77981, by rfl⟩ : syracuseStep 415901 = 155963) (by norm_num)
theorem B416029 : Blo 243817 416029 := bbase (se 3 (by rfl) ⟨78005, by rfl⟩ : syracuseStep 416029 = 156011) (by norm_num)
theorem B416117 : Blo 243817 416117 := bbase (se 5 (by rfl) ⟨19505, by rfl⟩ : syracuseStep 416117 = 39011) (by norm_num)
theorem B350581 : Blo 243817 350581 := bbase (se 5 (by rfl) ⟨16433, by rfl⟩ : syracuseStep 350581 = 32867) (by norm_num)
theorem B3365333 : Blo 243817 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B940517 : Blo 243817 940517 := bbase (se 4 (by rfl) ⟨88173, by rfl⟩ : syracuseStep 940517 = 176347) (by norm_num)
theorem B416245 : Blo 243817 416245 := bbase (se 5 (by rfl) ⟨19511, by rfl⟩ : syracuseStep 416245 = 39023) (by norm_num)
theorem B416333 : Blo 243817 416333 := bbase (se 3 (by rfl) ⟨78062, by rfl⟩ : syracuseStep 416333 = 156125) (by norm_num)
theorem B1235573 : Blo 243817 1235573 := bbase (se 5 (by rfl) ⟨57917, by rfl⟩ : syracuseStep 1235573 = 115835) (by norm_num)
theorem B416461 : Blo 243817 416461 := bbase (se 3 (by rfl) ⟨78086, by rfl⟩ : syracuseStep 416461 = 156173) (by norm_num)
theorem B940805 : Blo 243817 940805 := bbase (se 4 (by rfl) ⟨88200, by rfl⟩ : syracuseStep 940805 = 176401) (by norm_num)
theorem B416549 : Blo 243817 416549 := bbase (se 4 (by rfl) ⟨39051, by rfl⟩ : syracuseStep 416549 = 78103) (by norm_num)
theorem B2087765 : Blo 243817 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B416677 : Blo 243817 416677 := bbase (se 4 (by rfl) ⟨39063, by rfl⟩ : syracuseStep 416677 = 78127) (by norm_num)
theorem B351173 : Blo 243817 351173 := bbase (se 4 (by rfl) ⟨32922, by rfl⟩ : syracuseStep 351173 = 65845) (by norm_num)
theorem B416765 : Blo 243817 416765 := bbase (se 3 (by rfl) ⟨78143, by rfl⟩ : syracuseStep 416765 = 156287) (by norm_num)
theorem B351253 : Blo 243817 351253 := bbase (se 6 (by rfl) ⟨8232, by rfl⟩ : syracuseStep 351253 = 16465) (by norm_num)
theorem B416893 : Blo 243817 416893 := bbase (se 3 (by rfl) ⟨78167, by rfl⟩ : syracuseStep 416893 = 156335) (by norm_num)
theorem B351373 : Blo 243817 351373 := bbase (se 3 (by rfl) ⟨65882, by rfl⟩ : syracuseStep 351373 = 131765) (by norm_num)
theorem B416981 : Blo 243817 416981 := bbase (se 7 (by rfl) ⟨4886, by rfl⟩ : syracuseStep 416981 = 9773) (by norm_num)
theorem B351469 : Blo 243817 351469 := bbase (se 3 (by rfl) ⟨65900, by rfl⟩ : syracuseStep 351469 = 131801) (by norm_num)
theorem B417109 : Blo 243817 417109 := bbase (se 11 (by rfl) ⟨305, by rfl⟩ : syracuseStep 417109 = 611) (by norm_num)
theorem B417197 : Blo 243817 417197 := bbase (se 3 (by rfl) ⟨78224, by rfl⟩ : syracuseStep 417197 = 156449) (by norm_num)
theorem B2547125 : Blo 243817 2547125 := bbase (se 5 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 2547125 = 238793) (by norm_num)
theorem B417325 : Blo 243817 417325 := bbase (se 3 (by rfl) ⟨78248, by rfl⟩ : syracuseStep 417325 = 156497) (by norm_num)
theorem B417413 : Blo 243817 417413 := bbase (se 4 (by rfl) ⟨39132, by rfl⟩ : syracuseStep 417413 = 78265) (by norm_num)
theorem B351965 : Blo 243817 351965 := bbase (se 3 (by rfl) ⟨65993, by rfl⟩ : syracuseStep 351965 = 131987) (by norm_num)
theorem B417541 : Blo 243817 417541 := bbase (se 4 (by rfl) ⟨39144, by rfl⟩ : syracuseStep 417541 = 78289) (by norm_num)
theorem B548621 : Blo 243817 548621 := bbase (se 3 (by rfl) ⟨102866, by rfl⟩ : syracuseStep 548621 = 205733) (by norm_num)
theorem B548693 : Blo 243817 548693 := bbase (se 9 (by rfl) ⟨1607, by rfl⟩ : syracuseStep 548693 = 3215) (by norm_num)
theorem B417629 : Blo 243817 417629 := bbase (se 3 (by rfl) ⟨78305, by rfl⟩ : syracuseStep 417629 = 156611) (by norm_num)
theorem B1236869 : Blo 243817 1236869 := bbase (se 4 (by rfl) ⟨115956, by rfl⟩ : syracuseStep 1236869 = 231913) (by norm_num)
theorem B548765 : Blo 243817 548765 := bbase (se 3 (by rfl) ⟨102893, by rfl⟩ : syracuseStep 548765 = 205787) (by norm_num)
theorem B417725 : Blo 243817 417725 := bbase (se 3 (by rfl) ⟨78323, by rfl⟩ : syracuseStep 417725 = 156647) (by norm_num)
theorem B417757 : Blo 243817 417757 := bbase (se 3 (by rfl) ⟨78329, by rfl⟩ : syracuseStep 417757 = 156659) (by norm_num)
theorem B548837 : Blo 243817 548837 := bbase (se 4 (by rfl) ⟨51453, by rfl⟩ : syracuseStep 548837 = 102907) (by norm_num)
theorem B548909 : Blo 243817 548909 := bbase (se 3 (by rfl) ⟨102920, by rfl⟩ : syracuseStep 548909 = 205841) (by norm_num)
theorem B417845 : Blo 243817 417845 := bbase (se 5 (by rfl) ⟨19586, by rfl⟩ : syracuseStep 417845 = 39173) (by norm_num)
theorem B548981 : Blo 243817 548981 := bbase (se 5 (by rfl) ⟨25733, by rfl⟩ : syracuseStep 548981 = 51467) (by norm_num)
theorem B1597589 : Blo 243817 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B417973 : Blo 243817 417973 := bbase (se 5 (by rfl) ⟨19592, by rfl⟩ : syracuseStep 417973 = 39185) (by norm_num)
theorem B549053 : Blo 243817 549053 := bbase (se 3 (by rfl) ⟨102947, by rfl⟩ : syracuseStep 549053 = 205895) (by norm_num)
theorem B549125 : Blo 243817 549125 := bbase (se 4 (by rfl) ⟨51480, by rfl⟩ : syracuseStep 549125 = 102961) (by norm_num)
theorem B352517 : Blo 243817 352517 := bbase (se 4 (by rfl) ⟨33048, by rfl⟩ : syracuseStep 352517 = 66097) (by norm_num)
theorem B418061 : Blo 243817 418061 := bbase (se 3 (by rfl) ⟨78386, by rfl⟩ : syracuseStep 418061 = 156773) (by norm_num)
theorem B909605 : Blo 243817 909605 := bbase (se 4 (by rfl) ⟨85275, by rfl⟩ : syracuseStep 909605 = 170551) (by norm_num)
theorem B549197 : Blo 243817 549197 := bbase (se 3 (by rfl) ⟨102974, by rfl⟩ : syracuseStep 549197 = 205949) (by norm_num)
theorem B418189 : Blo 243817 418189 := bbase (se 3 (by rfl) ⟨78410, by rfl⟩ : syracuseStep 418189 = 156821) (by norm_num)
theorem B549269 : Blo 243817 549269 := bbase (se 6 (by rfl) ⟨12873, by rfl⟩ : syracuseStep 549269 = 25747) (by norm_num)
theorem B549341 : Blo 243817 549341 := bbase (se 3 (by rfl) ⟨103001, by rfl⟩ : syracuseStep 549341 = 206003) (by norm_num)
theorem B2679317 : Blo 243817 2679317 := bbase (se 6 (by rfl) ⟨62796, by rfl⟩ : syracuseStep 2679317 = 125593) (by norm_num)
theorem B549413 : Blo 243817 549413 := bbase (se 4 (by rfl) ⟨51507, by rfl⟩ : syracuseStep 549413 = 103015) (by norm_num)
theorem B549485 : Blo 243817 549485 := bbase (se 3 (by rfl) ⟨103028, by rfl⟩ : syracuseStep 549485 = 206057) (by norm_num)
theorem B746101 : Blo 243817 746101 := bbase (se 5 (by rfl) ⟨34973, by rfl⟩ : syracuseStep 746101 = 69947) (by norm_num)
theorem B549557 : Blo 243817 549557 := bbase (se 5 (by rfl) ⟨25760, by rfl⟩ : syracuseStep 549557 = 51521) (by norm_num)
theorem B549629 : Blo 243817 549629 := bbase (se 3 (by rfl) ⟨103055, by rfl⟩ : syracuseStep 549629 = 206111) (by norm_num)
theorem B549701 : Blo 243817 549701 := bbase (se 4 (by rfl) ⟨51534, by rfl⟩ : syracuseStep 549701 = 103069) (by norm_num)
theorem B549773 : Blo 243817 549773 := bbase (se 3 (by rfl) ⟨103082, by rfl⟩ : syracuseStep 549773 = 206165) (by norm_num)
theorem B549845 : Blo 243817 549845 := bbase (se 7 (by rfl) ⟨6443, by rfl⟩ : syracuseStep 549845 = 12887) (by norm_num)
theorem B549917 : Blo 243817 549917 := bbase (se 3 (by rfl) ⟨103109, by rfl⟩ : syracuseStep 549917 = 206219) (by norm_num)
theorem B549989 : Blo 243817 549989 := bbase (se 4 (by rfl) ⟨51561, by rfl⟩ : syracuseStep 549989 = 103123) (by norm_num)
theorem B1238165 : Blo 243817 1238165 := bbase (se 6 (by rfl) ⟨29019, by rfl⟩ : syracuseStep 1238165 = 58039) (by norm_num)
theorem B550061 : Blo 243817 550061 := bbase (se 3 (by rfl) ⟨103136, by rfl⟩ : syracuseStep 550061 = 206273) (by norm_num)
theorem B1172677 : Blo 243817 1172677 := bbase (se 4 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 1172677 = 219877) (by norm_num)
theorem B550133 : Blo 243817 550133 := bbase (se 5 (by rfl) ⟨25787, by rfl⟩ : syracuseStep 550133 = 51575) (by norm_num)
theorem B550205 : Blo 243817 550205 := bbase (se 3 (by rfl) ⟨103163, by rfl⟩ : syracuseStep 550205 = 206327) (by norm_num)
theorem B550277 : Blo 243817 550277 := bbase (se 4 (by rfl) ⟨51588, by rfl⟩ : syracuseStep 550277 = 103177) (by norm_num)
theorem B550349 : Blo 243817 550349 := bbase (se 3 (by rfl) ⟨103190, by rfl⟩ : syracuseStep 550349 = 206381) (by norm_num)
theorem B550421 : Blo 243817 550421 := bbase (se 6 (by rfl) ⟨12900, by rfl⟩ : syracuseStep 550421 = 25801) (by norm_num)
theorem B550493 : Blo 243817 550493 := bbase (se 3 (by rfl) ⟨103217, by rfl⟩ : syracuseStep 550493 = 206435) (by norm_num)
theorem B550565 : Blo 243817 550565 := bbase (se 4 (by rfl) ⟨51615, by rfl⟩ : syracuseStep 550565 = 103231) (by norm_num)
theorem B550637 : Blo 243817 550637 := bbase (se 3 (by rfl) ⟨103244, by rfl⟩ : syracuseStep 550637 = 206489) (by norm_num)
theorem B550709 : Blo 243817 550709 := bbase (se 5 (by rfl) ⟨25814, by rfl⟩ : syracuseStep 550709 = 51629) (by norm_num)
theorem B550781 : Blo 243817 550781 := bbase (se 3 (by rfl) ⟨103271, by rfl⟩ : syracuseStep 550781 = 206543) (by norm_num)
theorem B550853 : Blo 243817 550853 := bbase (se 4 (by rfl) ⟨51642, by rfl⟩ : syracuseStep 550853 = 103285) (by norm_num)
theorem B550925 : Blo 243817 550925 := bbase (se 3 (by rfl) ⟨103298, by rfl⟩ : syracuseStep 550925 = 206597) (by norm_num)
theorem B550997 : Blo 243817 550997 := bbase (se 8 (by rfl) ⟨3228, by rfl⟩ : syracuseStep 550997 = 6457) (by norm_num)
theorem B419941 : Blo 243817 419941 := bbase (se 4 (by rfl) ⟨39369, by rfl⟩ : syracuseStep 419941 = 78739) (by norm_num)
theorem B2648213 : Blo 243817 2648213 := bbase (se 6 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 2648213 = 124135) (by norm_num)
theorem B551069 : Blo 243817 551069 := bbase (se 3 (by rfl) ⟨103325, by rfl⟩ : syracuseStep 551069 = 206651) (by norm_num)
theorem B3565781 : Blo 243817 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B551141 : Blo 243817 551141 := bbase (se 4 (by rfl) ⟨51669, by rfl⟩ : syracuseStep 551141 = 103339) (by norm_num)
theorem B551213 : Blo 243817 551213 := bbase (se 3 (by rfl) ⟨103352, by rfl⟩ : syracuseStep 551213 = 206705) (by norm_num)
theorem B1403189 : Blo 243817 1403189 := bbase (se 5 (by rfl) ⟨65774, by rfl⟩ : syracuseStep 1403189 = 131549) (by norm_num)
theorem B1042789 : Blo 243817 1042789 := bbase (se 4 (by rfl) ⟨97761, by rfl⟩ : syracuseStep 1042789 = 195523) (by norm_num)
theorem B551285 : Blo 243817 551285 := bbase (se 5 (by rfl) ⟨25841, by rfl⟩ : syracuseStep 551285 = 51683) (by norm_num)
theorem B1239461 : Blo 243817 1239461 := bbase (se 4 (by rfl) ⟨116199, by rfl⟩ : syracuseStep 1239461 = 232399) (by norm_num)
theorem B551357 : Blo 243817 551357 := bbase (se 3 (by rfl) ⟨103379, by rfl⟩ : syracuseStep 551357 = 206759) (by norm_num)
theorem B551429 : Blo 243817 551429 := bbase (se 4 (by rfl) ⟨51696, by rfl⟩ : syracuseStep 551429 = 103393) (by norm_num)
theorem B551501 : Blo 243817 551501 := bbase (se 3 (by rfl) ⟨103406, by rfl⟩ : syracuseStep 551501 = 206813) (by norm_num)
theorem B551573 : Blo 243817 551573 := bbase (se 6 (by rfl) ⟨12927, by rfl⟩ : syracuseStep 551573 = 25855) (by norm_num)
theorem B551645 : Blo 243817 551645 := bbase (se 3 (by rfl) ⟨103433, by rfl⟩ : syracuseStep 551645 = 206867) (by norm_num)
theorem B551717 : Blo 243817 551717 := bbase (se 4 (by rfl) ⟨51723, by rfl⟩ : syracuseStep 551717 = 103447) (by norm_num)
theorem B551789 : Blo 243817 551789 := bbase (se 3 (by rfl) ⟨103460, by rfl⟩ : syracuseStep 551789 = 206921) (by norm_num)
theorem B617341 : Blo 243817 617341 := bbase (se 3 (by rfl) ⟨115751, by rfl⟩ : syracuseStep 617341 = 231503) (by norm_num)
theorem B1567669 : Blo 243817 1567669 := bbase (se 5 (by rfl) ⟨73484, by rfl⟩ : syracuseStep 1567669 = 146969) (by norm_num)
theorem B551861 : Blo 243817 551861 := bbase (se 5 (by rfl) ⟨25868, by rfl⟩ : syracuseStep 551861 = 51737) (by norm_num)
theorem B1600469 : Blo 243817 1600469 := bbase (se 7 (by rfl) ⟨18755, by rfl⟩ : syracuseStep 1600469 = 37511) (by norm_num)
theorem B617453 : Blo 243817 617453 := bbase (se 3 (by rfl) ⟨115772, by rfl⟩ : syracuseStep 617453 = 231545) (by norm_num)
theorem B551933 : Blo 243817 551933 := bbase (se 3 (by rfl) ⟨103487, by rfl⟩ : syracuseStep 551933 = 206975) (by norm_num)
theorem B879653 : Blo 243817 879653 := bbase (se 4 (by rfl) ⟨82467, by rfl⟩ : syracuseStep 879653 = 164935) (by norm_num)
theorem B552005 : Blo 243817 552005 := bbase (se 4 (by rfl) ⟨51750, by rfl⟩ : syracuseStep 552005 = 103501) (by norm_num)
theorem B420941 : Blo 243817 420941 := bbase (se 3 (by rfl) ⟨78926, by rfl⟩ : syracuseStep 420941 = 157853) (by norm_num)
theorem B552077 : Blo 243817 552077 := bbase (se 3 (by rfl) ⟨103514, by rfl⟩ : syracuseStep 552077 = 207029) (by norm_num)
theorem B617645 : Blo 243817 617645 := bbase (se 3 (by rfl) ⟨115808, by rfl⟩ : syracuseStep 617645 = 231617) (by norm_num)
theorem B1862837 : Blo 243817 1862837 := bbase (se 5 (by rfl) ⟨87320, by rfl⟩ : syracuseStep 1862837 = 174641) (by norm_num)
theorem B552149 : Blo 243817 552149 := bbase (se 7 (by rfl) ⟨6470, by rfl⟩ : syracuseStep 552149 = 12941) (by norm_num)
theorem B552221 : Blo 243817 552221 := bbase (se 3 (by rfl) ⟨103541, by rfl⟩ : syracuseStep 552221 = 207083) (by norm_num)
theorem B552293 : Blo 243817 552293 := bbase (se 4 (by rfl) ⟨51777, by rfl⟩ : syracuseStep 552293 = 103555) (by norm_num)
theorem B552365 : Blo 243817 552365 := bbase (se 3 (by rfl) ⟨103568, by rfl⟩ : syracuseStep 552365 = 207137) (by norm_num)
theorem B880085 : Blo 243817 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B552437 : Blo 243817 552437 := bbase (se 5 (by rfl) ⟨25895, by rfl⟩ : syracuseStep 552437 = 51791) (by norm_num)
theorem B617989 : Blo 243817 617989 := bbase (se 4 (by rfl) ⟨57936, by rfl⟩ : syracuseStep 617989 = 115873) (by norm_num)
theorem B552509 : Blo 243817 552509 := bbase (se 3 (by rfl) ⟨103595, by rfl⟩ : syracuseStep 552509 = 207191) (by norm_num)
theorem B355909 : Blo 243817 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B618101 : Blo 243817 618101 := bbase (se 5 (by rfl) ⟨28973, by rfl⟩ : syracuseStep 618101 = 57947) (by norm_num)
theorem B552581 : Blo 243817 552581 := bbase (se 4 (by rfl) ⟨51804, by rfl⟩ : syracuseStep 552581 = 103609) (by norm_num)
theorem B1240757 : Blo 243817 1240757 := bbase (se 5 (by rfl) ⟨58160, by rfl⟩ : syracuseStep 1240757 = 116321) (by norm_num)
theorem B552653 : Blo 243817 552653 := bbase (se 3 (by rfl) ⟨103622, by rfl⟩ : syracuseStep 552653 = 207245) (by norm_num)
theorem B552725 : Blo 243817 552725 := bbase (se 6 (by rfl) ⟨12954, by rfl⟩ : syracuseStep 552725 = 25909) (by norm_num)
theorem B618293 : Blo 243817 618293 := bbase (se 5 (by rfl) ⟨28982, by rfl⟩ : syracuseStep 618293 = 57965) (by norm_num)
theorem B552797 : Blo 243817 552797 := bbase (se 3 (by rfl) ⟨103649, by rfl⟩ : syracuseStep 552797 = 207299) (by norm_num)
theorem B421741 : Blo 243817 421741 := bbase (se 3 (by rfl) ⟨79076, by rfl⟩ : syracuseStep 421741 = 158153) (by norm_num)
theorem B552869 : Blo 243817 552869 := bbase (se 4 (by rfl) ⟨51831, by rfl⟩ : syracuseStep 552869 = 103663) (by norm_num)
theorem B1142741 : Blo 243817 1142741 := bbase (se 7 (by rfl) ⟨13391, by rfl⟩ : syracuseStep 1142741 = 26783) (by norm_num)
theorem B552941 : Blo 243817 552941 := bbase (se 3 (by rfl) ⟨103676, by rfl⟩ : syracuseStep 552941 = 207353) (by norm_num)
theorem B815093 : Blo 243817 815093 := bbase (se 5 (by rfl) ⟨38207, by rfl⟩ : syracuseStep 815093 = 76415) (by norm_num)
theorem B880661 : Blo 243817 880661 := bbase (se 6 (by rfl) ⟨20640, by rfl⟩ : syracuseStep 880661 = 41281) (by norm_num)
theorem B553013 : Blo 243817 553013 := bbase (se 5 (by rfl) ⟨25922, by rfl⟩ : syracuseStep 553013 = 51845) (by norm_num)
theorem B553085 : Blo 243817 553085 := bbase (se 3 (by rfl) ⟨103703, by rfl⟩ : syracuseStep 553085 = 207407) (by norm_num)
theorem B422021 : Blo 243817 422021 := bbase (se 4 (by rfl) ⟨39564, by rfl⟩ : syracuseStep 422021 = 79129) (by norm_num)
theorem B618637 : Blo 243817 618637 := bbase (se 3 (by rfl) ⟨115994, by rfl⟩ : syracuseStep 618637 = 231989) (by norm_num)
theorem B585877 : Blo 243817 585877 := bbase (se 6 (by rfl) ⟨13731, by rfl⟩ : syracuseStep 585877 = 27463) (by norm_num)
theorem B1896629 : Blo 243817 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B553157 : Blo 243817 553157 := bbase (se 4 (by rfl) ⟨51858, by rfl⟩ : syracuseStep 553157 = 103717) (by norm_num)
theorem B618749 : Blo 243817 618749 := bbase (se 3 (by rfl) ⟨116015, by rfl⟩ : syracuseStep 618749 = 232031) (by norm_num)
theorem B553229 : Blo 243817 553229 := bbase (se 3 (by rfl) ⟨103730, by rfl⟩ : syracuseStep 553229 = 207461) (by norm_num)
theorem B553301 : Blo 243817 553301 := bbase (se 10 (by rfl) ⟨810, by rfl⟩ : syracuseStep 553301 = 1621) (by norm_num)
theorem B586109 : Blo 243817 586109 := bbase (se 3 (by rfl) ⟨109895, by rfl⟩ : syracuseStep 586109 = 219791) (by norm_num)
theorem B553373 : Blo 243817 553373 := bbase (se 3 (by rfl) ⟨103757, by rfl⟩ : syracuseStep 553373 = 207515) (by norm_num)
theorem B618941 : Blo 243817 618941 := bbase (se 3 (by rfl) ⟨116051, by rfl⟩ : syracuseStep 618941 = 232103) (by norm_num)
theorem B553445 : Blo 243817 553445 := bbase (se 4 (by rfl) ⟨51885, by rfl⟩ : syracuseStep 553445 = 103771) (by norm_num)
theorem B422405 : Blo 243817 422405 := bbase (se 4 (by rfl) ⟨39600, by rfl⟩ : syracuseStep 422405 = 79201) (by norm_num)
theorem B586253 : Blo 243817 586253 := bbase (se 3 (by rfl) ⟨109922, by rfl⟩ : syracuseStep 586253 = 219845) (by norm_num)
theorem B553517 : Blo 243817 553517 := bbase (se 3 (by rfl) ⟨103784, by rfl⟩ : syracuseStep 553517 = 207569) (by norm_num)
theorem B553589 : Blo 243817 553589 := bbase (se 5 (by rfl) ⟨25949, by rfl⟩ : syracuseStep 553589 = 51899) (by norm_num)
theorem B553661 : Blo 243817 553661 := bbase (se 3 (by rfl) ⟨103811, by rfl⟩ : syracuseStep 553661 = 207623) (by norm_num)
theorem B586493 : Blo 243817 586493 := bbase (se 3 (by rfl) ⟨109967, by rfl⟩ : syracuseStep 586493 = 219935) (by norm_num)
theorem B553733 : Blo 243817 553733 := bbase (se 4 (by rfl) ⟨51912, by rfl⟩ : syracuseStep 553733 = 103825) (by norm_num)
theorem B619285 : Blo 243817 619285 := bbase (se 6 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 619285 = 29029) (by norm_num)
theorem B1504021 : Blo 243817 1504021 := bbase (se 6 (by rfl) ⟨35250, by rfl⟩ : syracuseStep 1504021 = 70501) (by norm_num)
theorem B553805 : Blo 243817 553805 := bbase (se 3 (by rfl) ⟨103838, by rfl⟩ : syracuseStep 553805 = 207677) (by norm_num)
theorem B619397 : Blo 243817 619397 := bbase (se 4 (by rfl) ⟨58068, by rfl⟩ : syracuseStep 619397 = 116137) (by norm_num)
theorem B553877 : Blo 243817 553877 := bbase (se 6 (by rfl) ⟨12981, by rfl⟩ : syracuseStep 553877 = 25963) (by norm_num)
theorem B1242053 : Blo 243817 1242053 := bbase (se 4 (by rfl) ⟨116442, by rfl⟩ : syracuseStep 1242053 = 232885) (by norm_num)
theorem B553949 : Blo 243817 553949 := bbase (se 3 (by rfl) ⟨103865, by rfl⟩ : syracuseStep 553949 = 207731) (by norm_num)
theorem B554021 : Blo 243817 554021 := bbase (se 4 (by rfl) ⟨51939, by rfl⟩ : syracuseStep 554021 = 103879) (by norm_num)
theorem B619589 : Blo 243817 619589 := bbase (se 4 (by rfl) ⟨58086, by rfl⟩ : syracuseStep 619589 = 116173) (by norm_num)
theorem B554093 : Blo 243817 554093 := bbase (se 3 (by rfl) ⟨103892, by rfl⟩ : syracuseStep 554093 = 207785) (by norm_num)
theorem B554165 : Blo 243817 554165 := bbase (se 5 (by rfl) ⟨25976, by rfl⟩ : syracuseStep 554165 = 51953) (by norm_num)
theorem B554237 : Blo 243817 554237 := bbase (se 3 (by rfl) ⟨103919, by rfl⟩ : syracuseStep 554237 = 207839) (by norm_num)
theorem B1045781 : Blo 243817 1045781 := bbase (se 6 (by rfl) ⟨24510, by rfl⟩ : syracuseStep 1045781 = 49021) (by norm_num)
theorem B1176869 : Blo 243817 1176869 := bbase (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) (by norm_num)
theorem B554309 : Blo 243817 554309 := bbase (se 4 (by rfl) ⟨51966, by rfl⟩ : syracuseStep 554309 = 103933) (by norm_num)
theorem B521549 : Blo 243817 521549 := bbase (se 3 (by rfl) ⟨97790, by rfl⟩ : syracuseStep 521549 = 195581) (by norm_num)
theorem B554381 : Blo 243817 554381 := bbase (se 3 (by rfl) ⟨103946, by rfl⟩ : syracuseStep 554381 = 207893) (by norm_num)
theorem B619933 : Blo 243817 619933 := bbase (se 3 (by rfl) ⟨116237, by rfl⟩ : syracuseStep 619933 = 232475) (by norm_num)
theorem B554453 : Blo 243817 554453 := bbase (se 7 (by rfl) ⟨6497, by rfl⟩ : syracuseStep 554453 = 12995) (by norm_num)
theorem B587261 : Blo 243817 587261 := bbase (se 3 (by rfl) ⟨110111, by rfl⟩ : syracuseStep 587261 = 220223) (by norm_num)
theorem B620045 : Blo 243817 620045 := bbase (se 3 (by rfl) ⟨116258, by rfl⟩ : syracuseStep 620045 = 232517) (by norm_num)
theorem B554525 : Blo 243817 554525 := bbase (se 3 (by rfl) ⟨103973, by rfl⟩ : syracuseStep 554525 = 207947) (by norm_num)
theorem B521797 : Blo 243817 521797 := bbase (se 4 (by rfl) ⟨48918, by rfl⟩ : syracuseStep 521797 = 97837) (by norm_num)
theorem B554597 : Blo 243817 554597 := bbase (se 4 (by rfl) ⟨51993, by rfl⟩ : syracuseStep 554597 = 103987) (by norm_num)
theorem B783989 : Blo 243817 783989 := bbase (se 5 (by rfl) ⟨36749, by rfl⟩ : syracuseStep 783989 = 73499) (by norm_num)
theorem B554669 : Blo 243817 554669 := bbase (se 3 (by rfl) ⟨104000, by rfl⟩ : syracuseStep 554669 = 208001) (by norm_num)
theorem B620237 : Blo 243817 620237 := bbase (se 3 (by rfl) ⟨116294, by rfl⟩ : syracuseStep 620237 = 232589) (by norm_num)
theorem B554741 : Blo 243817 554741 := bbase (se 5 (by rfl) ⟨26003, by rfl⟩ : syracuseStep 554741 = 52007) (by norm_num)
theorem B554813 : Blo 243817 554813 := bbase (se 3 (by rfl) ⟨104027, by rfl⟩ : syracuseStep 554813 = 208055) (by norm_num)
theorem B5699413 : Blo 243817 5699413 := bbase (se 9 (by rfl) ⟨16697, by rfl⟩ : syracuseStep 5699413 = 33395) (by norm_num)
theorem B554885 : Blo 243817 554885 := bbase (se 4 (by rfl) ⟨52020, by rfl⟩ : syracuseStep 554885 = 104041) (by norm_num)
theorem B554957 : Blo 243817 554957 := bbase (se 3 (by rfl) ⟨104054, by rfl⟩ : syracuseStep 554957 = 208109) (by norm_num)
theorem B948181 : Blo 243817 948181 := bbase (se 7 (by rfl) ⟨11111, by rfl⟩ : syracuseStep 948181 = 22223) (by norm_num)
theorem B555029 : Blo 243817 555029 := bbase (se 6 (by rfl) ⟨13008, by rfl⟩ : syracuseStep 555029 = 26017) (by norm_num)
theorem B620581 : Blo 243817 620581 := bbase (se 4 (by rfl) ⟨58179, by rfl⟩ : syracuseStep 620581 = 116359) (by norm_num)
theorem B522301 : Blo 243817 522301 := bbase (se 3 (by rfl) ⟨97931, by rfl⟩ : syracuseStep 522301 = 195863) (by norm_num)
theorem B555101 : Blo 243817 555101 := bbase (se 3 (by rfl) ⟨104081, by rfl⟩ : syracuseStep 555101 = 208163) (by norm_num)
theorem B391277 : Blo 243817 391277 := bbase (se 3 (by rfl) ⟨73364, by rfl⟩ : syracuseStep 391277 = 146729) (by norm_num)
theorem B620693 : Blo 243817 620693 := bbase (se 6 (by rfl) ⟨14547, by rfl⟩ : syracuseStep 620693 = 29095) (by norm_num)
theorem B555173 : Blo 243817 555173 := bbase (se 4 (by rfl) ⟨52047, by rfl⟩ : syracuseStep 555173 = 104095) (by norm_num)
theorem B1243349 : Blo 243817 1243349 := bbase (se 7 (by rfl) ⟨14570, by rfl⟩ : syracuseStep 1243349 = 29141) (by norm_num)
theorem B555245 : Blo 243817 555245 := bbase (se 3 (by rfl) ⟨104108, by rfl⟩ : syracuseStep 555245 = 208217) (by norm_num)
theorem B1046789 : Blo 243817 1046789 := bbase (se 4 (by rfl) ⟨98136, by rfl⟩ : syracuseStep 1046789 = 196273) (by norm_num)
theorem B555317 : Blo 243817 555317 := bbase (se 5 (by rfl) ⟨26030, by rfl⟩ : syracuseStep 555317 = 52061) (by norm_num)
theorem B620885 : Blo 243817 620885 := bbase (se 10 (by rfl) ⟨909, by rfl⟩ : syracuseStep 620885 = 1819) (by norm_num)
theorem B555389 : Blo 243817 555389 := bbase (se 3 (by rfl) ⟨104135, by rfl⟩ : syracuseStep 555389 = 208271) (by norm_num)
theorem B260501 : Blo 243817 260501 := bbase (se 6 (by rfl) ⟨6105, by rfl⟩ : syracuseStep 260501 = 12211) (by norm_num)
theorem B555461 : Blo 243817 555461 := bbase (se 4 (by rfl) ⟨52074, by rfl⟩ : syracuseStep 555461 = 104149) (by norm_num)
theorem B555533 : Blo 243817 555533 := bbase (se 3 (by rfl) ⟨104162, by rfl⟩ : syracuseStep 555533 = 208325) (by norm_num)
theorem B555605 : Blo 243817 555605 := bbase (se 8 (by rfl) ⟨3255, by rfl⟩ : syracuseStep 555605 = 6511) (by norm_num)
theorem B260749 : Blo 243817 260749 := bbase (se 3 (by rfl) ⟨48890, by rfl⟩ : syracuseStep 260749 = 97781) (by norm_num)
theorem B555677 : Blo 243817 555677 := bbase (se 3 (by rfl) ⟨104189, by rfl⟩ : syracuseStep 555677 = 208379) (by norm_num)
theorem B621229 : Blo 243817 621229 := bbase (se 3 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 621229 = 232961) (by norm_num)
theorem B555749 : Blo 243817 555749 := bbase (se 4 (by rfl) ⟨52101, by rfl⟩ : syracuseStep 555749 = 104203) (by norm_num)
theorem B4193045 : Blo 243817 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B621341 : Blo 243817 621341 := bbase (se 3 (by rfl) ⟨116501, by rfl⟩ : syracuseStep 621341 = 233003) (by norm_num)
theorem B555821 : Blo 243817 555821 := bbase (se 3 (by rfl) ⟨104216, by rfl⟩ : syracuseStep 555821 = 208433) (by norm_num)
theorem B1571669 : Blo 243817 1571669 := bbase (se 9 (by rfl) ⟨4604, by rfl⟩ : syracuseStep 1571669 = 9209) (by norm_num)
theorem B588637 : Blo 243817 588637 := bbase (se 3 (by rfl) ⟨110369, by rfl⟩ : syracuseStep 588637 = 220739) (by norm_num)
theorem B555893 : Blo 243817 555893 := bbase (se 5 (by rfl) ⟨26057, by rfl⟩ : syracuseStep 555893 = 52115) (by norm_num)
theorem B523189 : Blo 243817 523189 := bbase (se 5 (by rfl) ⟨24524, by rfl⟩ : syracuseStep 523189 = 49049) (by norm_num)
theorem B555965 : Blo 243817 555965 := bbase (se 3 (by rfl) ⟨104243, by rfl⟩ : syracuseStep 555965 = 208487) (by norm_num)
theorem B621533 : Blo 243817 621533 := bbase (se 3 (by rfl) ⟨116537, by rfl⟩ : syracuseStep 621533 = 233075) (by norm_num)
theorem B556037 : Blo 243817 556037 := bbase (se 4 (by rfl) ⟨52128, by rfl⟩ : syracuseStep 556037 = 104257) (by norm_num)
theorem B687109 : Blo 243817 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B752645 : Blo 243817 752645 := bbase (se 4 (by rfl) ⟨70560, by rfl⟩ : syracuseStep 752645 = 141121) (by norm_num)
theorem B261193 : Blo 243817 261193 := bbase (se 2 (by rfl) ⟨97947, by rfl⟩ : syracuseStep 261193 = 195895) (by norm_num)
theorem B556109 : Blo 243817 556109 := bbase (se 3 (by rfl) ⟨104270, by rfl⟩ : syracuseStep 556109 = 208541) (by norm_num)
theorem B293977 : Blo 243817 293977 := bbase (se 2 (by rfl) ⟨110241, by rfl⟩ : syracuseStep 293977 = 220483) (by norm_num)
theorem B261253 : Blo 243817 261253 := bbase (se 4 (by rfl) ⟨24492, by rfl⟩ : syracuseStep 261253 = 48985) (by norm_num)
theorem B556181 : Blo 243817 556181 := bbase (se 6 (by rfl) ⟨13035, by rfl⟩ : syracuseStep 556181 = 26071) (by norm_num)
theorem B752789 : Blo 243817 752789 := bbase (se 6 (by rfl) ⟨17643, by rfl⟩ : syracuseStep 752789 = 35287) (by norm_num)
theorem B294049 : Blo 243817 294049 := bbase (se 2 (by rfl) ⟨110268, by rfl⟩ : syracuseStep 294049 = 220537) (by norm_num)
theorem B556253 : Blo 243817 556253 := bbase (se 3 (by rfl) ⟨104297, by rfl⟩ : syracuseStep 556253 = 208595) (by norm_num)
theorem B556325 : Blo 243817 556325 := bbase (se 4 (by rfl) ⟨52155, by rfl⟩ : syracuseStep 556325 = 104311) (by norm_num)
theorem B621877 : Blo 243817 621877 := bbase (se 5 (by rfl) ⟨29150, by rfl⟩ : syracuseStep 621877 = 58301) (by norm_num)
theorem B556397 : Blo 243817 556397 := bbase (se 3 (by rfl) ⟨104324, by rfl⟩ : syracuseStep 556397 = 208649) (by norm_num)
theorem B458117 : Blo 243817 458117 := bbase (se 4 (by rfl) ⟨42948, by rfl⟩ : syracuseStep 458117 = 85897) (by norm_num)
theorem B523685 : Blo 243817 523685 := bbase (se 4 (by rfl) ⟨49095, by rfl⟩ : syracuseStep 523685 = 98191) (by norm_num)
theorem B621989 : Blo 243817 621989 := bbase (se 4 (by rfl) ⟨58311, by rfl⟩ : syracuseStep 621989 = 116623) (by norm_num)
theorem B556469 : Blo 243817 556469 := bbase (se 5 (by rfl) ⟨26084, by rfl⟩ : syracuseStep 556469 = 52169) (by norm_num)
theorem B261569 : Blo 243817 261569 := bbase (se 2 (by rfl) ⟨98088, by rfl⟩ : syracuseStep 261569 = 196177) (by norm_num)
theorem B1244645 : Blo 243817 1244645 := bbase (se 4 (by rfl) ⟨116685, by rfl⟩ : syracuseStep 1244645 = 233371) (by norm_num)
theorem B556541 : Blo 243817 556541 := bbase (se 3 (by rfl) ⟨104351, by rfl⟩ : syracuseStep 556541 = 208703) (by norm_num)
theorem B556613 : Blo 243817 556613 := bbase (se 4 (by rfl) ⟨52182, by rfl⟩ : syracuseStep 556613 = 104365) (by norm_num)
theorem B392789 : Blo 243817 392789 := bbase (se 8 (by rfl) ⟨2301, by rfl⟩ : syracuseStep 392789 = 4603) (by norm_num)
theorem B622181 : Blo 243817 622181 := bbase (se 4 (by rfl) ⟨58329, by rfl⟩ : syracuseStep 622181 = 116659) (by norm_num)
theorem B556685 : Blo 243817 556685 := bbase (se 3 (by rfl) ⟨104378, by rfl⟩ : syracuseStep 556685 = 208757) (by norm_num)
theorem B556757 : Blo 243817 556757 := bbase (se 7 (by rfl) ⟨6524, by rfl⟩ : syracuseStep 556757 = 13049) (by norm_num)
theorem B786181 : Blo 243817 786181 := bbase (se 4 (by rfl) ⟨73704, by rfl⟩ : syracuseStep 786181 = 147409) (by norm_num)
theorem B556829 : Blo 243817 556829 := bbase (se 3 (by rfl) ⟨104405, by rfl⟩ : syracuseStep 556829 = 208811) (by norm_num)
theorem B1408853 : Blo 243817 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B556901 : Blo 243817 556901 := bbase (se 4 (by rfl) ⟨52209, by rfl⟩ : syracuseStep 556901 = 104419) (by norm_num)
theorem B262013 : Blo 243817 262013 := bbase (se 3 (by rfl) ⟨49127, by rfl⟩ : syracuseStep 262013 = 98255) (by norm_num)
theorem B556973 : Blo 243817 556973 := bbase (se 3 (by rfl) ⟨104432, by rfl⟩ : syracuseStep 556973 = 208865) (by norm_num)
theorem B262073 : Blo 243817 262073 := bbase (se 2 (by rfl) ⟨98277, by rfl⟩ : syracuseStep 262073 = 196555) (by norm_num)
theorem B622525 : Blo 243817 622525 := bbase (se 3 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 622525 = 233447) (by norm_num)
theorem B1048565 : Blo 243817 1048565 := bbase (se 5 (by rfl) ⟨49151, by rfl⟩ : syracuseStep 1048565 = 98303) (by norm_num)
theorem B557045 : Blo 243817 557045 := bbase (se 5 (by rfl) ⟨26111, by rfl⟩ : syracuseStep 557045 = 52223) (by norm_num)
theorem B786449 : Blo 243817 786449 := bstep (se 2 (by rfl) ⟨294918, by rfl⟩ : syracuseStep 786449 = 589837) B589837
theorem B262163 : Blo 243817 262163 := bstep (se 1 (by rfl) ⟨196622, by rfl⟩ : syracuseStep 262163 = 393245) B393245
theorem B721133 : Blo 243817 721133 := bstep (se 3 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 721133 = 270425) B270425
theorem B557297 : Blo 243817 557297 := bstep (se 2 (by rfl) ⟨208986, by rfl⟩ : syracuseStep 557297 = 417973) B417973
theorem B557315 : Blo 243817 557315 := bstep (se 1 (by rfl) ⟨417986, by rfl⟩ : syracuseStep 557315 = 835973) B835973
theorem B786797 : Blo 243817 786797 := bstep (se 3 (by rfl) ⟨147524, by rfl⟩ : syracuseStep 786797 = 295049) B295049
theorem B622961 : Blo 243817 622961 := bstep (se 2 (by rfl) ⟨233610, by rfl⟩ : syracuseStep 622961 = 467221) B467221
theorem B524675 : Blo 243817 524675 := bstep (se 1 (by rfl) ⟨393506, by rfl⟩ : syracuseStep 524675 = 787013) B787013
theorem B393635 : Blo 243817 393635 := bstep (se 1 (by rfl) ⟨295226, by rfl⟩ : syracuseStep 393635 = 590453) B590453
theorem B623011 : Blo 243817 623011 := bstep (se 1 (by rfl) ⟨467258, by rfl⟩ : syracuseStep 623011 = 934517) B934517
theorem B1245617 : Blo 243817 1245617 := bstep (se 2 (by rfl) ⟨467106, by rfl⟩ : syracuseStep 1245617 = 934213) B934213
theorem B1409521 : Blo 243817 1409521 := bstep (se 2 (by rfl) ⟨528570, by rfl⟩ : syracuseStep 1409521 = 1057141) B1057141
theorem B557585 : Blo 243817 557585 := bstep (se 2 (by rfl) ⟨209094, by rfl⟩ : syracuseStep 557585 = 418189) B418189
theorem B393763 : Blo 243817 393763 := bstep (se 1 (by rfl) ⟨295322, by rfl⟩ : syracuseStep 393763 = 590645) B590645
theorem B623153 : Blo 243817 623153 := bstep (se 2 (by rfl) ⟨233682, by rfl⟩ : syracuseStep 623153 = 467365) B467365
theorem B393827 : Blo 243817 393827 := bstep (se 1 (by rfl) ⟨295370, by rfl⟩ : syracuseStep 393827 = 590741) B590741
theorem B394321 : Blo 243817 394321 := bstep (se 2 (by rfl) ⟨147870, by rfl⟩ : syracuseStep 394321 = 295741) B295741
theorem B1672433 : Blo 243817 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B1869155 : Blo 243817 1869155 := bstep (se 1 (by rfl) ⟨1401866, by rfl⟩ : syracuseStep 1869155 = 2803733) B2803733
theorem B624145 : Blo 243817 624145 := bstep (se 2 (by rfl) ⟨234054, by rfl⟩ : syracuseStep 624145 = 468109) B468109
theorem B525923 : Blo 243817 525923 := bstep (se 1 (by rfl) ⟨394442, by rfl⟩ : syracuseStep 525923 = 788885) B788885
theorem B296563 : Blo 243817 296563 := bstep (se 1 (by rfl) ⟨222422, by rfl⟩ : syracuseStep 296563 = 444845) B444845
theorem B1181425 : Blo 243817 1181425 := bstep (se 2 (by rfl) ⟨443034, by rfl⟩ : syracuseStep 1181425 = 886069) B886069
theorem B394993 : Blo 243817 394993 := bstep (se 2 (by rfl) ⟨148122, by rfl⟩ : syracuseStep 394993 = 296245) B296245
theorem B624419 : Blo 243817 624419 := bstep (se 1 (by rfl) ⟨468314, by rfl⟩ : syracuseStep 624419 = 936629) B936629
theorem B1247075 : Blo 243817 1247075 := bstep (se 1 (by rfl) ⟨935306, by rfl⟩ : syracuseStep 1247075 = 1870613) B1870613
theorem B1410979 : Blo 243817 1410979 := bstep (se 1 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 1410979 = 2116469) B2116469
theorem B329665 : Blo 243817 329665 := bstep (se 2 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 329665 = 247249) B247249
theorem B624611 : Blo 243817 624611 := bstep (se 1 (by rfl) ⟨468458, by rfl⟩ : syracuseStep 624611 = 936917) B936917
theorem B264179 : Blo 243817 264179 := bstep (se 1 (by rfl) ⟨198134, by rfl⟩ : syracuseStep 264179 = 396269) B396269
theorem B329729 : Blo 243817 329729 := bstep (se 2 (by rfl) ⟨123648, by rfl⟩ : syracuseStep 329729 = 247297) B247297
theorem B788653 : Blo 243817 788653 := bstep (se 3 (by rfl) ⟨147872, by rfl⟩ : syracuseStep 788653 = 295745) B295745
theorem B526513 : Blo 243817 526513 := bstep (se 2 (by rfl) ⟨197442, by rfl⟩ : syracuseStep 526513 = 394885) B394885
theorem B821485 : Blo 243817 821485 := bstep (se 3 (by rfl) ⟨154028, by rfl⟩ : syracuseStep 821485 = 308057) B308057
theorem B297379 : Blo 243817 297379 := bstep (se 1 (by rfl) ⟨223034, by rfl⟩ : syracuseStep 297379 = 446069) B446069
theorem B1247885 : Blo 243817 1247885 := bstep (se 3 (by rfl) ⟨233978, by rfl⟩ : syracuseStep 1247885 = 467957) B467957
theorem B592643 : Blo 243817 592643 := bstep (se 1 (by rfl) ⟨444482, by rfl⟩ : syracuseStep 592643 = 888965) B888965
theorem B559921 : Blo 243817 559921 := bstep (se 2 (by rfl) ⟨209970, by rfl⟩ : syracuseStep 559921 = 419941) B419941
theorem B396083 : Blo 243817 396083 := bstep (se 1 (by rfl) ⟨297062, by rfl⟩ : syracuseStep 396083 = 594125) B594125
theorem B494417 : Blo 243817 494417 := bstep (se 2 (by rfl) ⟨185406, by rfl⟩ : syracuseStep 494417 = 370813) B370813
theorem B592721 : Blo 243817 592721 := bstep (se 2 (by rfl) ⟨222270, by rfl⟩ : syracuseStep 592721 = 444541) B444541
theorem B625553 : Blo 243817 625553 := bstep (se 2 (by rfl) ⟨234582, by rfl⟩ : syracuseStep 625553 = 469165) B469165
theorem B625603 : Blo 243817 625603 := bstep (se 1 (by rfl) ⟨469202, by rfl⟩ : syracuseStep 625603 = 938405) B938405
theorem B592913 : Blo 243817 592913 := bstep (se 2 (by rfl) ⟨222342, by rfl⟩ : syracuseStep 592913 = 444685) B444685
theorem B625745 : Blo 243817 625745 := bstep (se 2 (by rfl) ⟨234654, by rfl⟩ : syracuseStep 625745 = 469309) B469309
theorem B396371 : Blo 243817 396371 := bstep (se 1 (by rfl) ⟨297278, by rfl⟩ : syracuseStep 396371 = 594557) B594557
theorem B1051811 : Blo 243817 1051811 := bstep (se 1 (by rfl) ⟨788858, by rfl⟩ : syracuseStep 1051811 = 1577717) B1577717
theorem B330979 : Blo 243817 330979 := bstep (se 1 (by rfl) ⟨248234, by rfl⟩ : syracuseStep 330979 = 496469) B496469
theorem B593201 : Blo 243817 593201 := bstep (se 2 (by rfl) ⟨222450, by rfl⟩ : syracuseStep 593201 = 444901) B444901
theorem B396787 : Blo 243817 396787 := bstep (se 1 (by rfl) ⟨297590, by rfl⟩ : syracuseStep 396787 = 595181) B595181
theorem B1445539 : Blo 243817 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B823121 : Blo 243817 823121 := bstep (se 2 (by rfl) ⟨308670, by rfl⟩ : syracuseStep 823121 = 617341) B617341
theorem B790499 : Blo 243817 790499 := bstep (se 1 (by rfl) ⟨592874, by rfl⟩ : syracuseStep 790499 = 1185749) B1185749
theorem B626737 : Blo 243817 626737 := bstep (se 2 (by rfl) ⟨235026, by rfl⟩ : syracuseStep 626737 = 470053) B470053
theorem B627011 : Blo 243817 627011 := bstep (se 1 (by rfl) ⟨470258, by rfl⟩ : syracuseStep 627011 = 940517) B940517
theorem B823661 : Blo 243817 823661 := bstep (se 3 (by rfl) ⟨154436, by rfl⟩ : syracuseStep 823661 = 308873) B308873
theorem B790897 : Blo 243817 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B332147 : Blo 243817 332147 := bstep (se 1 (by rfl) ⟨249110, by rfl⟩ : syracuseStep 332147 = 498221) B498221
theorem B463249 : Blo 243817 463249 := bstep (se 2 (by rfl) ⟨173718, by rfl⟩ : syracuseStep 463249 = 347437) B347437
theorem B823715 : Blo 243817 823715 := bstep (se 1 (by rfl) ⟨617786, by rfl⟩ : syracuseStep 823715 = 1235573) B1235573
theorem B2822597 : Blo 243817 2822597 := bstep (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) B529237
theorem B627203 : Blo 243817 627203 := bstep (se 1 (by rfl) ⟨470402, by rfl⟩ : syracuseStep 627203 = 940805) B940805
theorem B496145 : Blo 243817 496145 := bstep (se 2 (by rfl) ⟨186054, by rfl⟩ : syracuseStep 496145 = 372109) B372109
theorem B397955 : Blo 243817 397955 := bstep (se 1 (by rfl) ⟨298466, by rfl⟩ : syracuseStep 397955 = 596933) B596933
theorem B823985 : Blo 243817 823985 := bstep (se 2 (by rfl) ⟨308994, by rfl⟩ : syracuseStep 823985 = 617989) B617989
theorem B791345 : Blo 243817 791345 := bstep (se 2 (by rfl) ⟨296754, by rfl⟩ : syracuseStep 791345 = 593509) B593509
theorem B660433 : Blo 243817 660433 := bstep (se 2 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 660433 = 495325) B495325
theorem B562321 : Blo 243817 562321 := bstep (se 2 (by rfl) ⟨210870, by rfl⟩ : syracuseStep 562321 = 421741) B421741
theorem B365729 : Blo 243817 365729 := bstep (se 2 (by rfl) ⟨137148, by rfl⟩ : syracuseStep 365729 = 274297) B274297
theorem B365747 : Blo 243817 365747 := bstep (se 1 (by rfl) ⟨274310, by rfl⟩ : syracuseStep 365747 = 548621) B548621
theorem B824525 : Blo 243817 824525 := bstep (se 3 (by rfl) ⟨154598, by rfl⟩ : syracuseStep 824525 = 309197) B309197
theorem B365777 : Blo 243817 365777 := bstep (se 2 (by rfl) ⟨137166, by rfl⟩ : syracuseStep 365777 = 274333) B274333
theorem B365795 : Blo 243817 365795 := bstep (se 1 (by rfl) ⟨274346, by rfl⟩ : syracuseStep 365795 = 548693) B548693
theorem B365825 : Blo 243817 365825 := bstep (se 2 (by rfl) ⟨137184, by rfl⟩ : syracuseStep 365825 = 274369) B274369
theorem B824579 : Blo 243817 824579 := bstep (se 1 (by rfl) ⟨618434, by rfl⟩ : syracuseStep 824579 = 1236869) B1236869
theorem B365843 : Blo 243817 365843 := bstep (se 1 (by rfl) ⟨274382, by rfl⟩ : syracuseStep 365843 = 548765) B548765
theorem B365873 : Blo 243817 365873 := bstep (se 2 (by rfl) ⟨137202, by rfl⟩ : syracuseStep 365873 = 274405) B274405
theorem B365891 : Blo 243817 365891 := bstep (se 1 (by rfl) ⟨274418, by rfl⟩ : syracuseStep 365891 = 548837) B548837
theorem B2102597 : Blo 243817 2102597 := bstep (se 4 (by rfl) ⟨197118, by rfl⟩ : syracuseStep 2102597 = 394237) B394237
theorem B365921 : Blo 243817 365921 := bstep (se 2 (by rfl) ⟨137220, by rfl⟩ : syracuseStep 365921 = 274441) B274441
theorem B365939 : Blo 243817 365939 := bstep (se 1 (by rfl) ⟨274454, by rfl⟩ : syracuseStep 365939 = 548909) B548909
theorem B365969 : Blo 243817 365969 := bstep (se 2 (by rfl) ⟨137238, by rfl⟩ : syracuseStep 365969 = 274477) B274477
theorem B267667 : Blo 243817 267667 := bstep (se 1 (by rfl) ⟨200750, by rfl⟩ : syracuseStep 267667 = 401501) B401501
theorem B365987 : Blo 243817 365987 := bstep (se 1 (by rfl) ⟨274490, by rfl⟩ : syracuseStep 365987 = 548981) B548981
theorem B464305 : Blo 243817 464305 := bstep (se 2 (by rfl) ⟨174114, by rfl⟩ : syracuseStep 464305 = 348229) B348229
theorem B366017 : Blo 243817 366017 := bstep (se 2 (by rfl) ⟨137256, by rfl⟩ : syracuseStep 366017 = 274513) B274513
theorem B366035 : Blo 243817 366035 := bstep (se 1 (by rfl) ⟨274526, by rfl⟩ : syracuseStep 366035 = 549053) B549053
theorem B3151331 : Blo 243817 3151331 := bstep (se 1 (by rfl) ⟨2363498, by rfl⟩ : syracuseStep 3151331 = 4726997) B4726997
theorem B366065 : Blo 243817 366065 := bstep (se 2 (by rfl) ⟨137274, by rfl⟩ : syracuseStep 366065 = 274549) B274549
theorem B1250801 : Blo 243817 1250801 := bstep (se 2 (by rfl) ⟨469050, by rfl⟩ : syracuseStep 1250801 = 938101) B938101
theorem B366083 : Blo 243817 366083 := bstep (se 1 (by rfl) ⟨274562, by rfl⟩ : syracuseStep 366083 = 549125) B549125
theorem B824849 : Blo 243817 824849 := bstep (se 2 (by rfl) ⟨309318, by rfl⟩ : syracuseStep 824849 = 618637) B618637
theorem B366113 : Blo 243817 366113 := bstep (se 2 (by rfl) ⟨137292, by rfl⟩ : syracuseStep 366113 = 274585) B274585
theorem B366131 : Blo 243817 366131 := bstep (se 1 (by rfl) ⟨274598, by rfl⟩ : syracuseStep 366131 = 549197) B549197
theorem B366161 : Blo 243817 366161 := bstep (se 2 (by rfl) ⟨137310, by rfl⟩ : syracuseStep 366161 = 274621) B274621
theorem B366179 : Blo 243817 366179 := bstep (se 1 (by rfl) ⟨274634, by rfl⟩ : syracuseStep 366179 = 549269) B549269
theorem B366209 : Blo 243817 366209 := bstep (se 2 (by rfl) ⟨137328, by rfl⟩ : syracuseStep 366209 = 274657) B274657
theorem B366227 : Blo 243817 366227 := bstep (se 1 (by rfl) ⟨274670, by rfl⟩ : syracuseStep 366227 = 549341) B549341
theorem B366257 : Blo 243817 366257 := bstep (se 2 (by rfl) ⟨137346, by rfl⟩ : syracuseStep 366257 = 274693) B274693
theorem B366275 : Blo 243817 366275 := bstep (se 1 (by rfl) ⟨274706, by rfl⟩ : syracuseStep 366275 = 549413) B549413
theorem B366305 : Blo 243817 366305 := bstep (se 2 (by rfl) ⟨137364, by rfl⟩ : syracuseStep 366305 = 274729) B274729
theorem B1119971 : Blo 243817 1119971 := bstep (se 1 (by rfl) ⟨839978, by rfl⟩ : syracuseStep 1119971 = 1679957) B1679957
theorem B366323 : Blo 243817 366323 := bstep (se 1 (by rfl) ⟨274742, by rfl⟩ : syracuseStep 366323 = 549485) B549485
theorem B366353 : Blo 243817 366353 := bstep (se 2 (by rfl) ⟨137382, by rfl⟩ : syracuseStep 366353 = 274765) B274765
theorem B366371 : Blo 243817 366371 := bstep (se 1 (by rfl) ⟨274778, by rfl⟩ : syracuseStep 366371 = 549557) B549557
theorem B366401 : Blo 243817 366401 := bstep (se 2 (by rfl) ⟨137400, by rfl⟩ : syracuseStep 366401 = 274801) B274801
theorem B464707 : Blo 243817 464707 := bstep (se 1 (by rfl) ⟨348530, by rfl⟩ : syracuseStep 464707 = 697061) B697061
theorem B366419 : Blo 243817 366419 := bstep (se 1 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 366419 = 549629) B549629
theorem B366449 : Blo 243817 366449 := bstep (se 2 (by rfl) ⟨137418, by rfl⟩ : syracuseStep 366449 = 274837) B274837
theorem B464753 : Blo 243817 464753 := bstep (se 2 (by rfl) ⟨174282, by rfl⟩ : syracuseStep 464753 = 348565) B348565
theorem B366467 : Blo 243817 366467 := bstep (se 1 (by rfl) ⟨274850, by rfl⟩ : syracuseStep 366467 = 549701) B549701
theorem B366497 : Blo 243817 366497 := bstep (se 2 (by rfl) ⟨137436, by rfl⟩ : syracuseStep 366497 = 274873) B274873
theorem B366515 : Blo 243817 366515 := bstep (se 1 (by rfl) ⟨274886, by rfl⟩ : syracuseStep 366515 = 549773) B549773
theorem B366545 : Blo 243817 366545 := bstep (se 2 (by rfl) ⟨137454, by rfl⟩ : syracuseStep 366545 = 274909) B274909
theorem B366563 : Blo 243817 366563 := bstep (se 1 (by rfl) ⟨274922, by rfl⟩ : syracuseStep 366563 = 549845) B549845
theorem B366593 : Blo 243817 366593 := bstep (se 2 (by rfl) ⟨137472, by rfl⟩ : syracuseStep 366593 = 274945) B274945
theorem B366611 : Blo 243817 366611 := bstep (se 1 (by rfl) ⟨274958, by rfl⟩ : syracuseStep 366611 = 549917) B549917
theorem B825389 : Blo 243817 825389 := bstep (se 3 (by rfl) ⟨154760, by rfl⟩ : syracuseStep 825389 = 309521) B309521
theorem B366641 : Blo 243817 366641 := bstep (se 2 (by rfl) ⟨137490, by rfl⟩ : syracuseStep 366641 = 274981) B274981
theorem B366659 : Blo 243817 366659 := bstep (se 1 (by rfl) ⟨274994, by rfl⟩ : syracuseStep 366659 = 549989) B549989
theorem B366689 : Blo 243817 366689 := bstep (se 2 (by rfl) ⟨137508, by rfl⟩ : syracuseStep 366689 = 275017) B275017
theorem B825443 : Blo 243817 825443 := bstep (se 1 (by rfl) ⟨619082, by rfl⟩ : syracuseStep 825443 = 1238165) B1238165
theorem B366707 : Blo 243817 366707 := bstep (se 1 (by rfl) ⟨275030, by rfl⟩ : syracuseStep 366707 = 550061) B550061
theorem B366737 : Blo 243817 366737 := bstep (se 2 (by rfl) ⟨137526, by rfl⟩ : syracuseStep 366737 = 275053) B275053
theorem B465041 : Blo 243817 465041 := bstep (se 2 (by rfl) ⟨174390, by rfl⟩ : syracuseStep 465041 = 348781) B348781
theorem B366755 : Blo 243817 366755 := bstep (se 1 (by rfl) ⟨275066, by rfl⟩ : syracuseStep 366755 = 550133) B550133
theorem B366785 : Blo 243817 366785 := bstep (se 2 (by rfl) ⟨137544, by rfl⟩ : syracuseStep 366785 = 275089) B275089
theorem B661709 : Blo 243817 661709 := bstep (se 3 (by rfl) ⟨124070, by rfl⟩ : syracuseStep 661709 = 248141) B248141
theorem B366803 : Blo 243817 366803 := bstep (se 1 (by rfl) ⟨275102, by rfl⟩ : syracuseStep 366803 = 550205) B550205
theorem B366833 : Blo 243817 366833 := bstep (se 2 (by rfl) ⟨137562, by rfl⟩ : syracuseStep 366833 = 275125) B275125
theorem B366851 : Blo 243817 366851 := bstep (se 1 (by rfl) ⟨275138, by rfl⟩ : syracuseStep 366851 = 550277) B550277
theorem B366881 : Blo 243817 366881 := bstep (se 2 (by rfl) ⟨137580, by rfl⟩ : syracuseStep 366881 = 275161) B275161
theorem B366899 : Blo 243817 366899 := bstep (se 1 (by rfl) ⟨275174, by rfl⟩ : syracuseStep 366899 = 550349) B550349
theorem B366929 : Blo 243817 366929 := bstep (se 2 (by rfl) ⟨137598, by rfl⟩ : syracuseStep 366929 = 275197) B275197
theorem B334163 : Blo 243817 334163 := bstep (se 1 (by rfl) ⟨250622, by rfl⟩ : syracuseStep 334163 = 501245) B501245
theorem B366947 : Blo 243817 366947 := bstep (se 1 (by rfl) ⟨275210, by rfl⟩ : syracuseStep 366947 = 550421) B550421
theorem B825713 : Blo 243817 825713 := bstep (se 2 (by rfl) ⟨309642, by rfl⟩ : syracuseStep 825713 = 619285) B619285
theorem B2005361 : Blo 243817 2005361 := bstep (se 2 (by rfl) ⟨752010, by rfl⟩ : syracuseStep 2005361 = 1504021) B1504021
theorem B366977 : Blo 243817 366977 := bstep (se 2 (by rfl) ⟨137616, by rfl⟩ : syracuseStep 366977 = 275233) B275233
theorem B694669 : Blo 243817 694669 := bstep (se 3 (by rfl) ⟨130250, by rfl⟩ : syracuseStep 694669 = 260501) B260501
theorem B366995 : Blo 243817 366995 := bstep (se 1 (by rfl) ⟨275246, by rfl⟩ : syracuseStep 366995 = 550493) B550493
theorem B367025 : Blo 243817 367025 := bstep (se 2 (by rfl) ⟨137634, by rfl⟩ : syracuseStep 367025 = 275269) B275269
theorem B498097 : Blo 243817 498097 := bstep (se 2 (by rfl) ⟨186786, by rfl⟩ : syracuseStep 498097 = 373573) B373573
theorem B367043 : Blo 243817 367043 := bstep (se 1 (by rfl) ⟨275282, by rfl⟩ : syracuseStep 367043 = 550565) B550565
theorem B367073 : Blo 243817 367073 := bstep (se 2 (by rfl) ⟨137652, by rfl⟩ : syracuseStep 367073 = 275305) B275305
theorem B367091 : Blo 243817 367091 := bstep (se 1 (by rfl) ⟨275318, by rfl⟩ : syracuseStep 367091 = 550637) B550637
theorem B367121 : Blo 243817 367121 := bstep (se 2 (by rfl) ⟨137670, by rfl⟩ : syracuseStep 367121 = 275341) B275341
theorem B367139 : Blo 243817 367139 := bstep (se 1 (by rfl) ⟨275354, by rfl⟩ : syracuseStep 367139 = 550709) B550709
theorem B367169 : Blo 243817 367169 := bstep (se 2 (by rfl) ⟨137688, by rfl⟩ : syracuseStep 367169 = 275377) B275377
theorem B1874501 : Blo 243817 1874501 := bstep (se 4 (by rfl) ⟨175734, by rfl⟩ : syracuseStep 1874501 = 351469) B351469
theorem B629329 : Blo 243817 629329 := bstep (se 2 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 629329 = 471997) B471997
theorem B367187 : Blo 243817 367187 := bstep (se 1 (by rfl) ⟨275390, by rfl⟩ : syracuseStep 367187 = 550781) B550781
theorem B367217 : Blo 243817 367217 := bstep (se 2 (by rfl) ⟨137706, by rfl⟩ : syracuseStep 367217 = 275413) B275413
theorem B367235 : Blo 243817 367235 := bstep (se 1 (by rfl) ⟨275426, by rfl⟩ : syracuseStep 367235 = 550853) B550853
theorem B367265 : Blo 243817 367265 := bstep (se 2 (by rfl) ⟨137724, by rfl⟩ : syracuseStep 367265 = 275449) B275449
theorem B367283 : Blo 243817 367283 := bstep (se 1 (by rfl) ⟨275462, by rfl⟩ : syracuseStep 367283 = 550925) B550925
theorem B367313 : Blo 243817 367313 := bstep (se 2 (by rfl) ⟨137742, by rfl⟩ : syracuseStep 367313 = 275485) B275485
theorem B367331 : Blo 243817 367331 := bstep (se 1 (by rfl) ⟨275498, by rfl⟩ : syracuseStep 367331 = 550997) B550997
theorem B367361 : Blo 243817 367361 := bstep (se 2 (by rfl) ⟨137760, by rfl⟩ : syracuseStep 367361 = 275521) B275521
theorem B989965 : Blo 243817 989965 := bstep (se 3 (by rfl) ⟨185618, by rfl⟩ : syracuseStep 989965 = 371237) B371237
theorem B1055501 : Blo 243817 1055501 := bstep (se 3 (by rfl) ⟨197906, by rfl⟩ : syracuseStep 1055501 = 395813) B395813
theorem B367379 : Blo 243817 367379 := bstep (se 1 (by rfl) ⟨275534, by rfl⟩ : syracuseStep 367379 = 551069) B551069
theorem B367409 : Blo 243817 367409 := bstep (se 2 (by rfl) ⟨137778, by rfl⟩ : syracuseStep 367409 = 275557) B275557
theorem B1055537 : Blo 243817 1055537 := bstep (se 2 (by rfl) ⟨395826, by rfl⟩ : syracuseStep 1055537 = 791653) B791653
theorem B367427 : Blo 243817 367427 := bstep (se 1 (by rfl) ⟨275570, by rfl⟩ : syracuseStep 367427 = 551141) B551141
theorem B793421 : Blo 243817 793421 := bstep (se 3 (by rfl) ⟨148766, by rfl⟩ : syracuseStep 793421 = 297533) B297533
theorem B367457 : Blo 243817 367457 := bstep (se 2 (by rfl) ⟨137796, by rfl⟩ : syracuseStep 367457 = 275593) B275593
theorem B465763 : Blo 243817 465763 := bstep (se 1 (by rfl) ⟨349322, by rfl⟩ : syracuseStep 465763 = 698645) B698645
theorem B498545 : Blo 243817 498545 := bstep (se 2 (by rfl) ⟨186954, by rfl⟩ : syracuseStep 498545 = 373909) B373909
theorem B367475 : Blo 243817 367475 := bstep (se 1 (by rfl) ⟨275606, by rfl⟩ : syracuseStep 367475 = 551213) B551213
theorem B826253 : Blo 243817 826253 := bstep (se 3 (by rfl) ⟨154922, by rfl⟩ : syracuseStep 826253 = 309845) B309845
theorem B367505 : Blo 243817 367505 := bstep (se 2 (by rfl) ⟨137814, by rfl⟩ : syracuseStep 367505 = 275629) B275629
theorem B367523 : Blo 243817 367523 := bstep (se 1 (by rfl) ⟨275642, by rfl⟩ : syracuseStep 367523 = 551285) B551285
theorem B1252259 : Blo 243817 1252259 := bstep (se 1 (by rfl) ⟨939194, by rfl⟩ : syracuseStep 1252259 = 1878389) B1878389
theorem B367553 : Blo 243817 367553 := bstep (se 2 (by rfl) ⟨137832, by rfl⟩ : syracuseStep 367553 = 275665) B275665
theorem B826307 : Blo 243817 826307 := bstep (se 1 (by rfl) ⟨619730, by rfl⟩ : syracuseStep 826307 = 1239461) B1239461
theorem B334801 : Blo 243817 334801 := bstep (se 2 (by rfl) ⟨125550, by rfl⟩ : syracuseStep 334801 = 251101) B251101
theorem B367571 : Blo 243817 367571 := bstep (se 1 (by rfl) ⟨275678, by rfl⟩ : syracuseStep 367571 = 551357) B551357
theorem B367601 : Blo 243817 367601 := bstep (se 2 (by rfl) ⟨137850, by rfl⟩ : syracuseStep 367601 = 275701) B275701
theorem B367619 : Blo 243817 367619 := bstep (se 1 (by rfl) ⟨275714, by rfl⟩ : syracuseStep 367619 = 551429) B551429
theorem B367649 : Blo 243817 367649 := bstep (se 2 (by rfl) ⟨137868, by rfl⟩ : syracuseStep 367649 = 275737) B275737
theorem B662573 : Blo 243817 662573 := bstep (se 3 (by rfl) ⟨124232, by rfl⟩ : syracuseStep 662573 = 248465) B248465
theorem B367667 : Blo 243817 367667 := bstep (se 1 (by rfl) ⟨275750, by rfl⟩ : syracuseStep 367667 = 551501) B551501
theorem B367697 : Blo 243817 367697 := bstep (se 2 (by rfl) ⟨137886, by rfl⟩ : syracuseStep 367697 = 275773) B275773
theorem B367715 : Blo 243817 367715 := bstep (se 1 (by rfl) ⟨275786, by rfl⟩ : syracuseStep 367715 = 551573) B551573
theorem B367745 : Blo 243817 367745 := bstep (se 2 (by rfl) ⟨137904, by rfl⟩ : syracuseStep 367745 = 275809) B275809
theorem B269443 : Blo 243817 269443 := bstep (se 1 (by rfl) ⟨202082, by rfl⟩ : syracuseStep 269443 = 404165) B404165
theorem B367763 : Blo 243817 367763 := bstep (se 1 (by rfl) ⟨275822, by rfl⟩ : syracuseStep 367763 = 551645) B551645
theorem B367793 : Blo 243817 367793 := bstep (se 2 (by rfl) ⟨137922, by rfl⟩ : syracuseStep 367793 = 275845) B275845
theorem B367811 : Blo 243817 367811 := bstep (se 1 (by rfl) ⟨275858, by rfl⟩ : syracuseStep 367811 = 551717) B551717
theorem B892109 : Blo 243817 892109 := bstep (se 3 (by rfl) ⟨167270, by rfl⟩ : syracuseStep 892109 = 334541) B334541
theorem B826577 : Blo 243817 826577 := bstep (se 2 (by rfl) ⟨309966, by rfl⟩ : syracuseStep 826577 = 619933) B619933
theorem B367841 : Blo 243817 367841 := bstep (se 2 (by rfl) ⟨137940, by rfl⟩ : syracuseStep 367841 = 275881) B275881
theorem B367859 : Blo 243817 367859 := bstep (se 1 (by rfl) ⟨275894, by rfl⟩ : syracuseStep 367859 = 551789) B551789
theorem B367889 : Blo 243817 367889 := bstep (se 2 (by rfl) ⟨137958, by rfl⟩ : syracuseStep 367889 = 275917) B275917
theorem B367907 : Blo 243817 367907 := bstep (se 1 (by rfl) ⟨275930, by rfl⟩ : syracuseStep 367907 = 551861) B551861
theorem B466211 : Blo 243817 466211 := bstep (se 1 (by rfl) ⟨349658, by rfl⟩ : syracuseStep 466211 = 699317) B699317
theorem B367937 : Blo 243817 367937 := bstep (se 2 (by rfl) ⟨137976, by rfl⟩ : syracuseStep 367937 = 275953) B275953
theorem B367955 : Blo 243817 367955 := bstep (se 1 (by rfl) ⟨275966, by rfl⟩ : syracuseStep 367955 = 551933) B551933
theorem B367985 : Blo 243817 367985 := bstep (se 2 (by rfl) ⟨137994, by rfl⟩ : syracuseStep 367985 = 275989) B275989
theorem B5086577 : Blo 243817 5086577 := bstep (se 2 (by rfl) ⟨1907466, by rfl⟩ : syracuseStep 5086577 = 3814933) B3814933
theorem B368003 : Blo 243817 368003 := bstep (se 1 (by rfl) ⟨276002, by rfl⟩ : syracuseStep 368003 = 552005) B552005
theorem B368033 : Blo 243817 368033 := bstep (se 2 (by rfl) ⟨138012, by rfl⟩ : syracuseStep 368033 = 276025) B276025
theorem B695729 : Blo 243817 695729 := bstep (se 2 (by rfl) ⟨260898, by rfl⟩ : syracuseStep 695729 = 521797) B521797
theorem B368051 : Blo 243817 368051 := bstep (se 1 (by rfl) ⟨276038, by rfl⟩ : syracuseStep 368051 = 552077) B552077
theorem B368081 : Blo 243817 368081 := bstep (se 2 (by rfl) ⟨138030, by rfl⟩ : syracuseStep 368081 = 276061) B276061
theorem B368099 : Blo 243817 368099 := bstep (se 1 (by rfl) ⟨276074, by rfl⟩ : syracuseStep 368099 = 552149) B552149
theorem B368129 : Blo 243817 368129 := bstep (se 2 (by rfl) ⟨138048, by rfl⟩ : syracuseStep 368129 = 276097) B276097
theorem B368147 : Blo 243817 368147 := bstep (se 1 (by rfl) ⟨276110, by rfl⟩ : syracuseStep 368147 = 552221) B552221
theorem B368177 : Blo 243817 368177 := bstep (se 2 (by rfl) ⟨138066, by rfl⟩ : syracuseStep 368177 = 276133) B276133
theorem B368195 : Blo 243817 368195 := bstep (se 1 (by rfl) ⟨276146, by rfl⟩ : syracuseStep 368195 = 552293) B552293
theorem B466499 : Blo 243817 466499 := bstep (se 1 (by rfl) ⟨349874, by rfl⟩ : syracuseStep 466499 = 699749) B699749
theorem B368225 : Blo 243817 368225 := bstep (se 2 (by rfl) ⟨138084, by rfl⟩ : syracuseStep 368225 = 276169) B276169
theorem B892529 : Blo 243817 892529 := bstep (se 2 (by rfl) ⟨334698, by rfl⟩ : syracuseStep 892529 = 669397) B669397
theorem B368243 : Blo 243817 368243 := bstep (se 1 (by rfl) ⟨276182, by rfl⟩ : syracuseStep 368243 = 552365) B552365
theorem B368273 : Blo 243817 368273 := bstep (se 2 (by rfl) ⟨138102, by rfl⟩ : syracuseStep 368273 = 276205) B276205
theorem B368291 : Blo 243817 368291 := bstep (se 1 (by rfl) ⟨276218, by rfl⟩ : syracuseStep 368291 = 552437) B552437
theorem B368321 : Blo 243817 368321 := bstep (se 2 (by rfl) ⟨138120, by rfl⟩ : syracuseStep 368321 = 276241) B276241
theorem B1253069 : Blo 243817 1253069 := bstep (se 3 (by rfl) ⟨234950, by rfl⟩ : syracuseStep 1253069 = 469901) B469901
theorem B368339 : Blo 243817 368339 := bstep (se 1 (by rfl) ⟨276254, by rfl⟩ : syracuseStep 368339 = 552509) B552509
theorem B827117 : Blo 243817 827117 := bstep (se 3 (by rfl) ⟨155084, by rfl⟩ : syracuseStep 827117 = 310169) B310169
theorem B368369 : Blo 243817 368369 := bstep (se 2 (by rfl) ⟨138138, by rfl⟩ : syracuseStep 368369 = 276277) B276277
theorem B368387 : Blo 243817 368387 := bstep (se 1 (by rfl) ⟨276290, by rfl⟩ : syracuseStep 368387 = 552581) B552581
theorem B368417 : Blo 243817 368417 := bstep (se 2 (by rfl) ⟨138156, by rfl⟩ : syracuseStep 368417 = 276313) B276313
theorem B827171 : Blo 243817 827171 := bstep (se 1 (by rfl) ⟨620378, by rfl⟩ : syracuseStep 827171 = 1240757) B1240757
theorem B368435 : Blo 243817 368435 := bstep (se 1 (by rfl) ⟨276326, by rfl⟩ : syracuseStep 368435 = 552653) B552653
theorem B368465 : Blo 243817 368465 := bstep (se 2 (by rfl) ⟨138174, by rfl⟩ : syracuseStep 368465 = 276349) B276349
theorem B368483 : Blo 243817 368483 := bstep (se 1 (by rfl) ⟨276362, by rfl⟩ : syracuseStep 368483 = 552725) B552725
theorem B368513 : Blo 243817 368513 := bstep (se 2 (by rfl) ⟨138192, by rfl⟩ : syracuseStep 368513 = 276385) B276385
theorem B663437 : Blo 243817 663437 := bstep (se 3 (by rfl) ⟨124394, by rfl⟩ : syracuseStep 663437 = 248789) B248789
theorem B368531 : Blo 243817 368531 := bstep (se 1 (by rfl) ⟨276398, by rfl⟩ : syracuseStep 368531 = 552797) B552797
theorem B1187747 : Blo 243817 1187747 := bstep (se 1 (by rfl) ⟨890810, by rfl⟩ : syracuseStep 1187747 = 1781621) B1781621
theorem B368561 : Blo 243817 368561 := bstep (se 2 (by rfl) ⟨138210, by rfl⟩ : syracuseStep 368561 = 276421) B276421
theorem B368579 : Blo 243817 368579 := bstep (se 1 (by rfl) ⟨276434, by rfl⟩ : syracuseStep 368579 = 552869) B552869
theorem B368609 : Blo 243817 368609 := bstep (se 2 (by rfl) ⟨138228, by rfl⟩ : syracuseStep 368609 = 276457) B276457
theorem B761827 : Blo 243817 761827 := bstep (se 1 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 761827 = 1142741) B1142741
theorem B368627 : Blo 243817 368627 := bstep (se 1 (by rfl) ⟨276470, by rfl⟩ : syracuseStep 368627 = 552941) B552941
theorem B368657 : Blo 243817 368657 := bstep (se 2 (by rfl) ⟨138246, by rfl⟩ : syracuseStep 368657 = 276493) B276493
theorem B368675 : Blo 243817 368675 := bstep (se 1 (by rfl) ⟨276506, by rfl⟩ : syracuseStep 368675 = 553013) B553013
theorem B827441 : Blo 243817 827441 := bstep (se 2 (by rfl) ⟨310290, by rfl⟩ : syracuseStep 827441 = 620581) B620581
theorem B368705 : Blo 243817 368705 := bstep (se 2 (by rfl) ⟨138264, by rfl⟩ : syracuseStep 368705 = 276529) B276529
theorem B696401 : Blo 243817 696401 := bstep (se 2 (by rfl) ⟨261150, by rfl⟩ : syracuseStep 696401 = 522301) B522301
theorem B368723 : Blo 243817 368723 := bstep (se 1 (by rfl) ⟨276542, by rfl⟩ : syracuseStep 368723 = 553085) B553085
theorem B368753 : Blo 243817 368753 := bstep (se 2 (by rfl) ⟨138282, by rfl⟩ : syracuseStep 368753 = 276565) B276565
theorem B368771 : Blo 243817 368771 := bstep (se 1 (by rfl) ⟨276578, by rfl⟩ : syracuseStep 368771 = 553157) B553157
theorem B368801 : Blo 243817 368801 := bstep (se 2 (by rfl) ⟨138300, by rfl⟩ : syracuseStep 368801 = 276601) B276601
theorem B368819 : Blo 243817 368819 := bstep (se 1 (by rfl) ⟨276614, by rfl⟩ : syracuseStep 368819 = 553229) B553229
theorem B368849 : Blo 243817 368849 := bstep (se 2 (by rfl) ⟨138318, by rfl⟩ : syracuseStep 368849 = 276637) B276637
theorem B368867 : Blo 243817 368867 := bstep (se 1 (by rfl) ⟨276650, by rfl⟩ : syracuseStep 368867 = 553301) B553301
theorem B925937 : Blo 243817 925937 := bstep (se 2 (by rfl) ⟨347226, by rfl⟩ : syracuseStep 925937 = 694453) B694453
theorem B368897 : Blo 243817 368897 := bstep (se 2 (by rfl) ⟨138336, by rfl⟩ : syracuseStep 368897 = 276673) B276673
theorem B368915 : Blo 243817 368915 := bstep (se 1 (by rfl) ⟨276686, by rfl⟩ : syracuseStep 368915 = 553373) B553373
theorem B368945 : Blo 243817 368945 := bstep (se 2 (by rfl) ⟨138354, by rfl⟩ : syracuseStep 368945 = 276709) B276709
theorem B368963 : Blo 243817 368963 := bstep (se 1 (by rfl) ⟨276722, by rfl⟩ : syracuseStep 368963 = 553445) B553445
theorem B368993 : Blo 243817 368993 := bstep (se 2 (by rfl) ⟨138372, by rfl⟩ : syracuseStep 368993 = 276745) B276745
theorem B1188209 : Blo 243817 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B369011 : Blo 243817 369011 := bstep (se 1 (by rfl) ⟨276758, by rfl⟩ : syracuseStep 369011 = 553517) B553517
theorem B369041 : Blo 243817 369041 := bstep (se 2 (by rfl) ⟨138390, by rfl⟩ : syracuseStep 369041 = 276781) B276781
theorem B369059 : Blo 243817 369059 := bstep (se 1 (by rfl) ⟨276794, by rfl⟩ : syracuseStep 369059 = 553589) B553589
theorem B369089 : Blo 243817 369089 := bstep (se 2 (by rfl) ⟨138408, by rfl⟩ : syracuseStep 369089 = 276817) B276817
theorem B369107 : Blo 243817 369107 := bstep (se 1 (by rfl) ⟨276830, by rfl⟩ : syracuseStep 369107 = 553661) B553661
theorem B369137 : Blo 243817 369137 := bstep (se 2 (by rfl) ⟨138426, by rfl⟩ : syracuseStep 369137 = 276853) B276853
theorem B467441 : Blo 243817 467441 := bstep (se 2 (by rfl) ⟨175290, by rfl⟩ : syracuseStep 467441 = 350581) B350581
theorem B369155 : Blo 243817 369155 := bstep (se 1 (by rfl) ⟨276866, by rfl⟩ : syracuseStep 369155 = 553733) B553733
theorem B369185 : Blo 243817 369185 := bstep (se 2 (by rfl) ⟨138444, by rfl⟩ : syracuseStep 369185 = 276889) B276889
theorem B369203 : Blo 243817 369203 := bstep (se 1 (by rfl) ⟨276902, by rfl⟩ : syracuseStep 369203 = 553805) B553805
theorem B827981 : Blo 243817 827981 := bstep (se 3 (by rfl) ⟨155246, by rfl⟩ : syracuseStep 827981 = 310493) B310493
theorem B369233 : Blo 243817 369233 := bstep (se 2 (by rfl) ⟨138462, by rfl⟩ : syracuseStep 369233 = 276925) B276925
theorem B369251 : Blo 243817 369251 := bstep (se 1 (by rfl) ⟨276938, by rfl⟩ : syracuseStep 369251 = 553877) B553877
theorem B369281 : Blo 243817 369281 := bstep (se 2 (by rfl) ⟨138480, by rfl⟩ : syracuseStep 369281 = 276961) B276961
theorem B828035 : Blo 243817 828035 := bstep (se 1 (by rfl) ⟨621026, by rfl⟩ : syracuseStep 828035 = 1242053) B1242053
theorem B369299 : Blo 243817 369299 := bstep (se 1 (by rfl) ⟨276974, by rfl⟩ : syracuseStep 369299 = 553949) B553949
theorem B369329 : Blo 243817 369329 := bstep (se 2 (by rfl) ⟨138498, by rfl⟩ : syracuseStep 369329 = 276997) B276997
theorem B369347 : Blo 243817 369347 := bstep (se 1 (by rfl) ⟨277010, by rfl⟩ : syracuseStep 369347 = 554021) B554021
theorem B369377 : Blo 243817 369377 := bstep (se 2 (by rfl) ⟨138516, by rfl⟩ : syracuseStep 369377 = 277033) B277033
theorem B369395 : Blo 243817 369395 := bstep (se 1 (by rfl) ⟨277046, by rfl⟩ : syracuseStep 369395 = 554093) B554093
theorem B369425 : Blo 243817 369425 := bstep (se 2 (by rfl) ⟨138534, by rfl⟩ : syracuseStep 369425 = 277069) B277069
theorem B369443 : Blo 243817 369443 := bstep (se 1 (by rfl) ⟨277082, by rfl⟩ : syracuseStep 369443 = 554165) B554165
theorem B369473 : Blo 243817 369473 := bstep (se 2 (by rfl) ⟨138552, by rfl⟩ : syracuseStep 369473 = 277105) B277105
theorem B369491 : Blo 243817 369491 := bstep (se 1 (by rfl) ⟨277118, by rfl⟩ : syracuseStep 369491 = 554237) B554237
theorem B697187 : Blo 243817 697187 := bstep (se 1 (by rfl) ⟨522890, by rfl⟩ : syracuseStep 697187 = 1045781) B1045781
theorem B664433 : Blo 243817 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B369521 : Blo 243817 369521 := bstep (se 2 (by rfl) ⟨138570, by rfl⟩ : syracuseStep 369521 = 277141) B277141
theorem B369539 : Blo 243817 369539 := bstep (se 1 (by rfl) ⟨277154, by rfl⟩ : syracuseStep 369539 = 554309) B554309
theorem B828305 : Blo 243817 828305 := bstep (se 2 (by rfl) ⟨310614, by rfl⟩ : syracuseStep 828305 = 621229) B621229
theorem B369569 : Blo 243817 369569 := bstep (se 2 (by rfl) ⟨138588, by rfl⟩ : syracuseStep 369569 = 277177) B277177
theorem B369587 : Blo 243817 369587 := bstep (se 1 (by rfl) ⟨277190, by rfl⟩ : syracuseStep 369587 = 554381) B554381
theorem B1582021 : Blo 243817 1582021 := bstep (se 4 (by rfl) ⟨148314, by rfl⟩ : syracuseStep 1582021 = 296629) B296629
theorem B369617 : Blo 243817 369617 := bstep (se 2 (by rfl) ⟨138606, by rfl⟩ : syracuseStep 369617 = 277213) B277213
theorem B369635 : Blo 243817 369635 := bstep (se 1 (by rfl) ⟨277226, by rfl⟩ : syracuseStep 369635 = 554453) B554453
theorem B369665 : Blo 243817 369665 := bstep (se 2 (by rfl) ⟨138624, by rfl⟩ : syracuseStep 369665 = 277249) B277249
theorem B369683 : Blo 243817 369683 := bstep (se 1 (by rfl) ⟨277262, by rfl⟩ : syracuseStep 369683 = 554525) B554525
theorem B369713 : Blo 243817 369713 := bstep (se 2 (by rfl) ⟨138642, by rfl⟩ : syracuseStep 369713 = 277285) B277285
theorem B369731 : Blo 243817 369731 := bstep (se 1 (by rfl) ⟨277298, by rfl⟩ : syracuseStep 369731 = 554597) B554597
theorem B369761 : Blo 243817 369761 := bstep (se 2 (by rfl) ⟨138660, by rfl⟩ : syracuseStep 369761 = 277321) B277321
theorem B369779 : Blo 243817 369779 := bstep (se 1 (by rfl) ⟨277334, by rfl⟩ : syracuseStep 369779 = 554669) B554669
theorem B369809 : Blo 243817 369809 := bstep (se 2 (by rfl) ⟨138678, by rfl⟩ : syracuseStep 369809 = 277357) B277357
theorem B369827 : Blo 243817 369827 := bstep (se 1 (by rfl) ⟨277370, by rfl⟩ : syracuseStep 369827 = 554741) B554741
theorem B697517 : Blo 243817 697517 := bstep (se 3 (by rfl) ⟨130784, by rfl⟩ : syracuseStep 697517 = 261569) B261569
theorem B369857 : Blo 243817 369857 := bstep (se 2 (by rfl) ⟨138696, by rfl⟩ : syracuseStep 369857 = 277393) B277393
theorem B369875 : Blo 243817 369875 := bstep (se 1 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 369875 = 554813) B554813
theorem B337123 : Blo 243817 337123 := bstep (se 1 (by rfl) ⟨252842, by rfl⟩ : syracuseStep 337123 = 505685) B505685
theorem B697585 : Blo 243817 697585 := bstep (se 2 (by rfl) ⟨261594, by rfl⟩ : syracuseStep 697585 = 523189) B523189
theorem B369905 : Blo 243817 369905 := bstep (se 2 (by rfl) ⟨138714, by rfl⟩ : syracuseStep 369905 = 277429) B277429
theorem B369923 : Blo 243817 369923 := bstep (se 1 (by rfl) ⟨277442, by rfl⟩ : syracuseStep 369923 = 554885) B554885
theorem B369953 : Blo 243817 369953 := bstep (se 2 (by rfl) ⟨138732, by rfl⟩ : syracuseStep 369953 = 277465) B277465
theorem B369971 : Blo 243817 369971 := bstep (se 1 (by rfl) ⟨277478, by rfl⟩ : syracuseStep 369971 = 554957) B554957
theorem B370001 : Blo 243817 370001 := bstep (se 2 (by rfl) ⟨138750, by rfl⟩ : syracuseStep 370001 = 277501) B277501
theorem B370019 : Blo 243817 370019 := bstep (se 1 (by rfl) ⟨277514, by rfl⟩ : syracuseStep 370019 = 555029) B555029
theorem B468337 : Blo 243817 468337 := bstep (se 2 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 468337 = 351253) B351253
theorem B370049 : Blo 243817 370049 := bstep (se 2 (by rfl) ⟨138768, by rfl⟩ : syracuseStep 370049 = 277537) B277537
theorem B370067 : Blo 243817 370067 := bstep (se 1 (by rfl) ⟨277550, by rfl⟩ : syracuseStep 370067 = 555101) B555101
theorem B828845 : Blo 243817 828845 := bstep (se 3 (by rfl) ⟨155408, by rfl⟩ : syracuseStep 828845 = 310817) B310817
theorem B370097 : Blo 243817 370097 := bstep (se 2 (by rfl) ⟨138786, by rfl⟩ : syracuseStep 370097 = 277573) B277573
theorem B370115 : Blo 243817 370115 := bstep (se 1 (by rfl) ⟨277586, by rfl⟩ : syracuseStep 370115 = 555173) B555173
theorem B370145 : Blo 243817 370145 := bstep (se 2 (by rfl) ⟨138804, by rfl⟩ : syracuseStep 370145 = 277609) B277609
theorem B828899 : Blo 243817 828899 := bstep (se 1 (by rfl) ⟨621674, by rfl⟩ : syracuseStep 828899 = 1243349) B1243349
theorem B370163 : Blo 243817 370163 := bstep (se 1 (by rfl) ⟨277622, by rfl⟩ : syracuseStep 370163 = 555245) B555245
theorem B697859 : Blo 243817 697859 := bstep (se 1 (by rfl) ⟨523394, by rfl⟩ : syracuseStep 697859 = 1046789) B1046789
theorem B468497 : Blo 243817 468497 := bstep (se 2 (by rfl) ⟨175686, by rfl⟩ : syracuseStep 468497 = 351373) B351373
theorem B370193 : Blo 243817 370193 := bstep (se 2 (by rfl) ⟨138822, by rfl⟩ : syracuseStep 370193 = 277645) B277645
theorem B370211 : Blo 243817 370211 := bstep (se 1 (by rfl) ⟨277658, by rfl⟩ : syracuseStep 370211 = 555317) B555317
theorem B370241 : Blo 243817 370241 := bstep (se 2 (by rfl) ⟨138840, by rfl⟩ : syracuseStep 370241 = 277681) B277681
theorem B370259 : Blo 243817 370259 := bstep (se 1 (by rfl) ⟨277694, by rfl⟩ : syracuseStep 370259 = 555389) B555389
theorem B370289 : Blo 243817 370289 := bstep (se 2 (by rfl) ⟨138858, by rfl⟩ : syracuseStep 370289 = 277717) B277717
theorem B370307 : Blo 243817 370307 := bstep (se 1 (by rfl) ⟨277730, by rfl⟩ : syracuseStep 370307 = 555461) B555461
theorem B370337 : Blo 243817 370337 := bstep (se 2 (by rfl) ⟨138876, by rfl⟩ : syracuseStep 370337 = 277753) B277753
theorem B927395 : Blo 243817 927395 := bstep (se 1 (by rfl) ⟨695546, by rfl⟩ : syracuseStep 927395 = 1391093) B1391093
theorem B927409 : Blo 243817 927409 := bstep (se 2 (by rfl) ⟨347778, by rfl⟩ : syracuseStep 927409 = 695557) B695557
theorem B370355 : Blo 243817 370355 := bstep (se 1 (by rfl) ⟨277766, by rfl⟩ : syracuseStep 370355 = 555533) B555533
theorem B370385 : Blo 243817 370385 := bstep (se 2 (by rfl) ⟨138894, by rfl⟩ : syracuseStep 370385 = 277789) B277789
theorem B370403 : Blo 243817 370403 := bstep (se 1 (by rfl) ⟨277802, by rfl⟩ : syracuseStep 370403 = 555605) B555605
theorem B829169 : Blo 243817 829169 := bstep (se 2 (by rfl) ⟨310938, by rfl⟩ : syracuseStep 829169 = 621877) B621877
theorem B370433 : Blo 243817 370433 := bstep (se 2 (by rfl) ⟨138912, by rfl⟩ : syracuseStep 370433 = 277825) B277825
theorem B370451 : Blo 243817 370451 := bstep (se 1 (by rfl) ⟨277838, by rfl⟩ : syracuseStep 370451 = 555677) B555677
theorem B370481 : Blo 243817 370481 := bstep (se 2 (by rfl) ⟨138930, by rfl⟩ : syracuseStep 370481 = 277861) B277861
theorem B370499 : Blo 243817 370499 := bstep (se 1 (by rfl) ⟨277874, by rfl⟩ : syracuseStep 370499 = 555749) B555749
theorem B370529 : Blo 243817 370529 := bstep (se 2 (by rfl) ⟨138948, by rfl⟩ : syracuseStep 370529 = 277897) B277897
theorem B2795363 : Blo 243817 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B370547 : Blo 243817 370547 := bstep (se 1 (by rfl) ⟨277910, by rfl⟩ : syracuseStep 370547 = 555821) B555821
theorem B370577 : Blo 243817 370577 := bstep (se 2 (by rfl) ⟨138966, by rfl⟩ : syracuseStep 370577 = 277933) B277933
theorem B468899 : Blo 243817 468899 := bstep (se 1 (by rfl) ⟨351674, by rfl⟩ : syracuseStep 468899 = 703349) B703349
theorem B370595 : Blo 243817 370595 := bstep (se 1 (by rfl) ⟨277946, by rfl⟩ : syracuseStep 370595 = 555893) B555893
theorem B370625 : Blo 243817 370625 := bstep (se 2 (by rfl) ⟨138984, by rfl⟩ : syracuseStep 370625 = 277969) B277969
theorem B370643 : Blo 243817 370643 := bstep (se 1 (by rfl) ⟨277982, by rfl⟩ : syracuseStep 370643 = 555965) B555965
theorem B370673 : Blo 243817 370673 := bstep (se 2 (by rfl) ⟨139002, by rfl⟩ : syracuseStep 370673 = 278005) B278005
theorem B370691 : Blo 243817 370691 := bstep (se 1 (by rfl) ⟨278018, by rfl⟩ : syracuseStep 370691 = 556037) B556037
theorem B501763 : Blo 243817 501763 := bstep (se 1 (by rfl) ⟨376322, by rfl⟩ : syracuseStep 501763 = 752645) B752645
theorem B370721 : Blo 243817 370721 := bstep (se 2 (by rfl) ⟨139020, by rfl⟩ : syracuseStep 370721 = 278041) B278041
theorem B370739 : Blo 243817 370739 := bstep (se 1 (by rfl) ⟨278054, by rfl⟩ : syracuseStep 370739 = 556109) B556109
theorem B370769 : Blo 243817 370769 := bstep (se 2 (by rfl) ⟨139038, by rfl⟩ : syracuseStep 370769 = 278077) B278077
theorem B370787 : Blo 243817 370787 := bstep (se 1 (by rfl) ⟨278090, by rfl⟩ : syracuseStep 370787 = 556181) B556181
theorem B501859 : Blo 243817 501859 := bstep (se 1 (by rfl) ⟨376394, by rfl⟩ : syracuseStep 501859 = 752789) B752789
theorem B370817 : Blo 243817 370817 := bstep (se 2 (by rfl) ⟨139056, by rfl⟩ : syracuseStep 370817 = 278113) B278113
theorem B370835 : Blo 243817 370835 := bstep (se 1 (by rfl) ⟨278126, by rfl⟩ : syracuseStep 370835 = 556253) B556253
theorem B370865 : Blo 243817 370865 := bstep (se 2 (by rfl) ⟨139074, by rfl⟩ : syracuseStep 370865 = 278149) B278149
theorem B370883 : Blo 243817 370883 := bstep (se 1 (by rfl) ⟨278162, by rfl⟩ : syracuseStep 370883 = 556325) B556325
theorem B338131 : Blo 243817 338131 := bstep (se 1 (by rfl) ⟨253598, by rfl⟩ : syracuseStep 338131 = 507197) B507197
theorem B370913 : Blo 243817 370913 := bstep (se 2 (by rfl) ⟨139092, by rfl⟩ : syracuseStep 370913 = 278185) B278185
theorem B370931 : Blo 243817 370931 := bstep (se 1 (by rfl) ⟨278198, by rfl⟩ : syracuseStep 370931 = 556397) B556397
theorem B305411 : Blo 243817 305411 := bstep (se 1 (by rfl) ⟨229058, by rfl⟩ : syracuseStep 305411 = 458117) B458117
theorem B829709 : Blo 243817 829709 := bstep (se 3 (by rfl) ⟨155570, by rfl⟩ : syracuseStep 829709 = 311141) B311141
theorem B370961 : Blo 243817 370961 := bstep (se 2 (by rfl) ⟨139110, by rfl⟩ : syracuseStep 370961 = 278221) B278221
theorem B370979 : Blo 243817 370979 := bstep (se 1 (by rfl) ⟨278234, by rfl⟩ : syracuseStep 370979 = 556469) B556469
theorem B371009 : Blo 243817 371009 := bstep (se 2 (by rfl) ⟨139128, by rfl⟩ : syracuseStep 371009 = 278257) B278257
theorem B829763 : Blo 243817 829763 := bstep (se 1 (by rfl) ⟨622322, by rfl⟩ : syracuseStep 829763 = 1244645) B1244645
theorem B698701 : Blo 243817 698701 := bstep (se 3 (by rfl) ⟨131006, by rfl⟩ : syracuseStep 698701 = 262013) B262013
theorem B371027 : Blo 243817 371027 := bstep (se 1 (by rfl) ⟨278270, by rfl⟩ : syracuseStep 371027 = 556541) B556541
theorem B600419 : Blo 243817 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B371057 : Blo 243817 371057 := bstep (se 2 (by rfl) ⟨139146, by rfl⟩ : syracuseStep 371057 = 278293) B278293
theorem B371075 : Blo 243817 371075 := bstep (se 1 (by rfl) ⟨278306, by rfl⟩ : syracuseStep 371075 = 556613) B556613
theorem B371105 : Blo 243817 371105 := bstep (se 2 (by rfl) ⟨139164, by rfl⟩ : syracuseStep 371105 = 278329) B278329
theorem B371123 : Blo 243817 371123 := bstep (se 1 (by rfl) ⟨278342, by rfl⟩ : syracuseStep 371123 = 556685) B556685
theorem B371153 : Blo 243817 371153 := bstep (se 2 (by rfl) ⟨139182, by rfl⟩ : syracuseStep 371153 = 278365) B278365
theorem B371171 : Blo 243817 371171 := bstep (se 1 (by rfl) ⟨278378, by rfl⟩ : syracuseStep 371171 = 556757) B556757
theorem B698861 : Blo 243817 698861 := bstep (se 3 (by rfl) ⟨131036, by rfl⟩ : syracuseStep 698861 = 262073) B262073
theorem B371201 : Blo 243817 371201 := bstep (se 2 (by rfl) ⟨139200, by rfl⟩ : syracuseStep 371201 = 278401) B278401
theorem B371219 : Blo 243817 371219 := bstep (se 1 (by rfl) ⟨278414, by rfl⟩ : syracuseStep 371219 = 556829) B556829
theorem B371249 : Blo 243817 371249 := bstep (se 2 (by rfl) ⟨139218, by rfl⟩ : syracuseStep 371249 = 278437) B278437
theorem B371267 : Blo 243817 371267 := bstep (se 1 (by rfl) ⟨278450, by rfl⟩ : syracuseStep 371267 = 556901) B556901
theorem B830033 : Blo 243817 830033 := bstep (se 2 (by rfl) ⟨311262, by rfl⟩ : syracuseStep 830033 = 622525) B622525
theorem B371297 : Blo 243817 371297 := bstep (se 2 (by rfl) ⟨139236, by rfl⟩ : syracuseStep 371297 = 278473) B278473
theorem B371315 : Blo 243817 371315 := bstep (se 1 (by rfl) ⟨278486, by rfl⟩ : syracuseStep 371315 = 556973) B556973
theorem B371345 : Blo 243817 371345 := bstep (se 2 (by rfl) ⟨139254, by rfl⟩ : syracuseStep 371345 = 278509) B278509
theorem B699043 : Blo 243817 699043 := bstep (se 1 (by rfl) ⟨524282, by rfl⟩ : syracuseStep 699043 = 1048565) B1048565
theorem B371363 : Blo 243817 371363 := bstep (se 1 (by rfl) ⟨278522, by rfl⟩ : syracuseStep 371363 = 557045) B557045
theorem B371393 : Blo 243817 371393 := bstep (se 2 (by rfl) ⟨139272, by rfl⟩ : syracuseStep 371393 = 278545) B278545
theorem B371411 : Blo 243817 371411 := bstep (se 1 (by rfl) ⟨278558, by rfl⟩ : syracuseStep 371411 = 557117) B557117
theorem B371441 : Blo 243817 371441 := bstep (se 2 (by rfl) ⟨139290, by rfl⟩ : syracuseStep 371441 = 278581) B278581
theorem B404227 : Blo 243817 404227 := bstep (se 1 (by rfl) ⟨303170, by rfl⟩ : syracuseStep 404227 = 606341) B606341
theorem B371459 : Blo 243817 371459 := bstep (se 1 (by rfl) ⟨278594, by rfl⟩ : syracuseStep 371459 = 557189) B557189
theorem B371489 : Blo 243817 371489 := bstep (se 2 (by rfl) ⟨139308, by rfl⟩ : syracuseStep 371489 = 278617) B278617
theorem B469795 : Blo 243817 469795 := bstep (se 1 (by rfl) ⟨352346, by rfl⟩ : syracuseStep 469795 = 704693) B704693
theorem B371507 : Blo 243817 371507 := bstep (se 1 (by rfl) ⟨278630, by rfl⟩ : syracuseStep 371507 = 557261) B557261
theorem B371537 : Blo 243817 371537 := bstep (se 2 (by rfl) ⟨139326, by rfl⟩ : syracuseStep 371537 = 278653) B278653
theorem B371555 : Blo 243817 371555 := bstep (se 1 (by rfl) ⟨278666, by rfl⟩ : syracuseStep 371555 = 557333) B557333
theorem B371585 : Blo 243817 371585 := bstep (se 2 (by rfl) ⟨139344, by rfl⟩ : syracuseStep 371585 = 278689) B278689
theorem B371603 : Blo 243817 371603 := bstep (se 1 (by rfl) ⟨278702, by rfl⟩ : syracuseStep 371603 = 557405) B557405
theorem B371633 : Blo 243817 371633 := bstep (se 2 (by rfl) ⟨139362, by rfl⟩ : syracuseStep 371633 = 278725) B278725
theorem B273331 : Blo 243817 273331 := bstep (se 1 (by rfl) ⟨204998, by rfl⟩ : syracuseStep 273331 = 409997) B409997
theorem B469955 : Blo 243817 469955 := bstep (se 1 (by rfl) ⟨352466, by rfl⟩ : syracuseStep 469955 = 704933) B704933
theorem B371651 : Blo 243817 371651 := bstep (se 1 (by rfl) ⟨278738, by rfl⟩ : syracuseStep 371651 = 557477) B557477
theorem B371681 : Blo 243817 371681 := bstep (se 2 (by rfl) ⟨139380, by rfl⟩ : syracuseStep 371681 = 278761) B278761
theorem B371699 : Blo 243817 371699 := bstep (se 1 (by rfl) ⟨278774, by rfl⟩ : syracuseStep 371699 = 557549) B557549
theorem B1125389 : Blo 243817 1125389 := bstep (se 3 (by rfl) ⟨211010, by rfl⟩ : syracuseStep 1125389 = 422021) B422021
theorem B928867 : Blo 243817 928867 := bstep (se 1 (by rfl) ⟨696650, by rfl⟩ : syracuseStep 928867 = 1393301) B1393301
theorem B830573 : Blo 243817 830573 := bstep (se 3 (by rfl) ⟨155732, by rfl⟩ : syracuseStep 830573 = 311465) B311465
theorem B3550321 : Blo 243817 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B5057677 : Blo 243817 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B830627 : Blo 243817 830627 := bstep (se 1 (by rfl) ⟨622970, by rfl⟩ : syracuseStep 830627 = 1245941) B1245941
theorem B1486021 : Blo 243817 1486021 := bstep (se 4 (by rfl) ⟨139314, by rfl⟩ : syracuseStep 1486021 = 278629) B278629
theorem B6040973 : Blo 243817 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B372113 : Blo 243817 372113 := bstep (se 2 (by rfl) ⟨139542, by rfl⟩ : syracuseStep 372113 = 279085) B279085
theorem B830897 : Blo 243817 830897 := bstep (se 2 (by rfl) ⟨311586, by rfl⟩ : syracuseStep 830897 = 623173) B623173
theorem B994801 : Blo 243817 994801 := bstep (se 2 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 994801 = 746101) B746101
theorem B831437 : Blo 243817 831437 := bstep (se 3 (by rfl) ⟨155894, by rfl⟩ : syracuseStep 831437 = 311789) B311789
theorem B274387 : Blo 243817 274387 := bstep (se 1 (by rfl) ⟨205790, by rfl⟩ : syracuseStep 274387 = 411581) B411581
theorem B831491 : Blo 243817 831491 := bstep (se 1 (by rfl) ⟨623618, by rfl⟩ : syracuseStep 831491 = 1247237) B1247237
theorem B700433 : Blo 243817 700433 := bstep (se 2 (by rfl) ⟨262662, by rfl⟩ : syracuseStep 700433 = 525325) B525325
theorem B274531 : Blo 243817 274531 := bstep (se 1 (by rfl) ⟨205898, by rfl⟩ : syracuseStep 274531 = 411797) B411797
theorem B274675 : Blo 243817 274675 := bstep (se 1 (by rfl) ⟨206006, by rfl⟩ : syracuseStep 274675 = 412013) B412013
theorem B1880333 : Blo 243817 1880333 := bstep (se 3 (by rfl) ⟨352562, by rfl⟩ : syracuseStep 1880333 = 705125) B705125
theorem B831761 : Blo 243817 831761 := bstep (se 2 (by rfl) ⟨311910, by rfl⟩ : syracuseStep 831761 = 623821) B623821
theorem B1585507 : Blo 243817 1585507 := bstep (se 1 (by rfl) ⟨1189130, by rfl⟩ : syracuseStep 1585507 = 2378261) B2378261
theorem B274819 : Blo 243817 274819 := bstep (se 1 (by rfl) ⟨206114, by rfl⟩ : syracuseStep 274819 = 412229) B412229
theorem B274963 : Blo 243817 274963 := bstep (se 1 (by rfl) ⟨206222, by rfl⟩ : syracuseStep 274963 = 412445) B412445
theorem B275107 : Blo 243817 275107 := bstep (se 1 (by rfl) ⟨206330, by rfl⟩ : syracuseStep 275107 = 412661) B412661
theorem B832301 : Blo 243817 832301 := bstep (se 3 (by rfl) ⟨156056, by rfl⟩ : syracuseStep 832301 = 312113) B312113
theorem B275251 : Blo 243817 275251 := bstep (se 1 (by rfl) ⟨206438, by rfl⟩ : syracuseStep 275251 = 412877) B412877
theorem B832355 : Blo 243817 832355 := bstep (se 1 (by rfl) ⟨624266, by rfl⟩ : syracuseStep 832355 = 1248533) B1248533
theorem B275395 : Blo 243817 275395 := bstep (se 1 (by rfl) ⟨206546, by rfl⟩ : syracuseStep 275395 = 413093) B413093
theorem B701389 : Blo 243817 701389 := bstep (se 3 (by rfl) ⟨131510, by rfl⟩ : syracuseStep 701389 = 263021) B263021
theorem B275539 : Blo 243817 275539 := bstep (se 1 (by rfl) ⟨206654, by rfl⟩ : syracuseStep 275539 = 413309) B413309
theorem B832625 : Blo 243817 832625 := bstep (se 2 (by rfl) ⟨312234, by rfl⟩ : syracuseStep 832625 = 624469) B624469
theorem B701617 : Blo 243817 701617 := bstep (se 2 (by rfl) ⟨263106, by rfl⟩ : syracuseStep 701617 = 526213) B526213
theorem B275683 : Blo 243817 275683 := bstep (se 1 (by rfl) ⟨206762, by rfl⟩ : syracuseStep 275683 = 413525) B413525
theorem B10073315 : Blo 243817 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B931085 : Blo 243817 931085 := bstep (se 3 (by rfl) ⟨174578, by rfl⟩ : syracuseStep 931085 = 349157) B349157
theorem B701777 : Blo 243817 701777 := bstep (se 2 (by rfl) ⟨263166, by rfl⟩ : syracuseStep 701777 = 526333) B526333
theorem B275827 : Blo 243817 275827 := bstep (se 1 (by rfl) ⟨206870, by rfl⟩ : syracuseStep 275827 = 413741) B413741
theorem B996749 : Blo 243817 996749 := bstep (se 3 (by rfl) ⟨186890, by rfl⟩ : syracuseStep 996749 = 373781) B373781
theorem B1324451 : Blo 243817 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B701891 : Blo 243817 701891 := bstep (se 1 (by rfl) ⟨526418, by rfl⟩ : syracuseStep 701891 = 1052837) B1052837
theorem B275971 : Blo 243817 275971 := bstep (se 1 (by rfl) ⟨206978, by rfl⟩ : syracuseStep 275971 = 413957) B413957
theorem B439921 : Blo 243817 439921 := bstep (se 2 (by rfl) ⟨164970, by rfl⟩ : syracuseStep 439921 = 329941) B329941
theorem B833165 : Blo 243817 833165 := bstep (se 3 (by rfl) ⟨156218, by rfl⟩ : syracuseStep 833165 = 312437) B312437
theorem B276115 : Blo 243817 276115 := bstep (se 1 (by rfl) ⟨207086, by rfl⟩ : syracuseStep 276115 = 414173) B414173
theorem B833219 : Blo 243817 833219 := bstep (se 1 (by rfl) ⟨624914, by rfl⟩ : syracuseStep 833219 = 1249829) B1249829
theorem B276259 : Blo 243817 276259 := bstep (se 1 (by rfl) ⟨207194, by rfl⟩ : syracuseStep 276259 = 414389) B414389
theorem B1390385 : Blo 243817 1390385 := bstep (se 2 (by rfl) ⟨521394, by rfl⟩ : syracuseStep 1390385 = 1042789) B1042789
theorem B309091 : Blo 243817 309091 := bstep (se 1 (by rfl) ⟨231818, by rfl⟩ : syracuseStep 309091 = 463637) B463637
theorem B2111345 : Blo 243817 2111345 := bstep (se 2 (by rfl) ⟨791754, by rfl⟩ : syracuseStep 2111345 = 1583509) B1583509
theorem B276403 : Blo 243817 276403 := bstep (se 1 (by rfl) ⟨207302, by rfl⟩ : syracuseStep 276403 = 414605) B414605
theorem B309187 : Blo 243817 309187 := bstep (se 1 (by rfl) ⟨231890, by rfl⟩ : syracuseStep 309187 = 463781) B463781
theorem B833489 : Blo 243817 833489 := bstep (se 2 (by rfl) ⟨312558, by rfl⟩ : syracuseStep 833489 = 625117) B625117
theorem B276547 : Blo 243817 276547 := bstep (se 1 (by rfl) ⟨207410, by rfl⟩ : syracuseStep 276547 = 414821) B414821
theorem B243827 : Blo 243817 243827 := bstep (se 1 (by rfl) ⟨182870, by rfl⟩ : syracuseStep 243827 = 365741) B365741
theorem B243843 : Blo 243817 243843 := bstep (se 1 (by rfl) ⟨182882, by rfl⟩ : syracuseStep 243843 = 365765) B365765
theorem B243859 : Blo 243817 243859 := bstep (se 1 (by rfl) ⟨182894, by rfl⟩ : syracuseStep 243859 = 365789) B365789
theorem B243875 : Blo 243817 243875 := bstep (se 1 (by rfl) ⟨182906, by rfl⟩ : syracuseStep 243875 = 365813) B365813
theorem B243891 : Blo 243817 243891 := bstep (se 1 (by rfl) ⟨182918, by rfl⟩ : syracuseStep 243891 = 365837) B365837
theorem B243907 : Blo 243817 243907 := bstep (se 1 (by rfl) ⟨182930, by rfl⟩ : syracuseStep 243907 = 365861) B365861
theorem B243923 : Blo 243817 243923 := bstep (se 1 (by rfl) ⟨182942, by rfl⟩ : syracuseStep 243923 = 365885) B365885
theorem B276691 : Blo 243817 276691 := bstep (se 1 (by rfl) ⟨207518, by rfl⟩ : syracuseStep 276691 = 415037) B415037
theorem B243939 : Blo 243817 243939 := bstep (se 1 (by rfl) ⟨182954, by rfl⟩ : syracuseStep 243939 = 365909) B365909
theorem B440561 : Blo 243817 440561 := bstep (se 2 (by rfl) ⟨165210, by rfl⟩ : syracuseStep 440561 = 330421) B330421
theorem B243955 : Blo 243817 243955 := bstep (se 1 (by rfl) ⟨182966, by rfl⟩ : syracuseStep 243955 = 365933) B365933
theorem B243971 : Blo 243817 243971 := bstep (se 1 (by rfl) ⟨182978, by rfl⟩ : syracuseStep 243971 = 365957) B365957
theorem B1325317 : Blo 243817 1325317 := bstep (se 4 (by rfl) ⟨124248, by rfl⟩ : syracuseStep 1325317 = 248497) B248497
theorem B243987 : Blo 243817 243987 := bstep (se 1 (by rfl) ⟨182990, by rfl⟩ : syracuseStep 243987 = 365981) B365981
theorem B244003 : Blo 243817 244003 := bstep (se 1 (by rfl) ⟨183002, by rfl⟩ : syracuseStep 244003 = 366005) B366005
theorem B244019 : Blo 243817 244019 := bstep (se 1 (by rfl) ⟨183014, by rfl⟩ : syracuseStep 244019 = 366029) B366029
theorem B244035 : Blo 243817 244035 := bstep (se 1 (by rfl) ⟨183026, by rfl⟩ : syracuseStep 244035 = 366053) B366053
theorem B244051 : Blo 243817 244051 := bstep (se 1 (by rfl) ⟨183038, by rfl⟩ : syracuseStep 244051 = 366077) B366077
theorem B244067 : Blo 243817 244067 := bstep (se 1 (by rfl) ⟨183050, by rfl⟩ : syracuseStep 244067 = 366101) B366101
theorem B276835 : Blo 243817 276835 := bstep (se 1 (by rfl) ⟨207626, by rfl⟩ : syracuseStep 276835 = 415253) B415253
theorem B244083 : Blo 243817 244083 := bstep (se 1 (by rfl) ⟨183062, by rfl⟩ : syracuseStep 244083 = 366125) B366125
theorem B244099 : Blo 243817 244099 := bstep (se 1 (by rfl) ⟨183074, by rfl⟩ : syracuseStep 244099 = 366149) B366149
theorem B244115 : Blo 243817 244115 := bstep (se 1 (by rfl) ⟨183086, by rfl⟩ : syracuseStep 244115 = 366173) B366173
theorem B244131 : Blo 243817 244131 := bstep (se 1 (by rfl) ⟨183098, by rfl⟩ : syracuseStep 244131 = 366197) B366197
theorem B702893 : Blo 243817 702893 := bstep (se 3 (by rfl) ⟨131792, by rfl⟩ : syracuseStep 702893 = 263585) B263585
theorem B1325489 : Blo 243817 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B244147 : Blo 243817 244147 := bstep (se 1 (by rfl) ⟨183110, by rfl⟩ : syracuseStep 244147 = 366221) B366221
theorem B309683 : Blo 243817 309683 := bstep (se 1 (by rfl) ⟨232262, by rfl⟩ : syracuseStep 309683 = 464525) B464525
theorem B244163 : Blo 243817 244163 := bstep (se 1 (by rfl) ⟨183122, by rfl⟩ : syracuseStep 244163 = 366245) B366245
theorem B1423813 : Blo 243817 1423813 := bstep (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) B266965
theorem B244179 : Blo 243817 244179 := bstep (se 1 (by rfl) ⟨183134, by rfl⟩ : syracuseStep 244179 = 366269) B366269
theorem B244195 : Blo 243817 244195 := bstep (se 1 (by rfl) ⟨183146, by rfl⟩ : syracuseStep 244195 = 366293) B366293
theorem B834029 : Blo 243817 834029 := bstep (se 3 (by rfl) ⟨156380, by rfl⟩ : syracuseStep 834029 = 312761) B312761
theorem B244211 : Blo 243817 244211 := bstep (se 1 (by rfl) ⟨183158, by rfl⟩ : syracuseStep 244211 = 366317) B366317
theorem B276979 : Blo 243817 276979 := bstep (se 1 (by rfl) ⟨207734, by rfl⟩ : syracuseStep 276979 = 415469) B415469
theorem B244227 : Blo 243817 244227 := bstep (se 1 (by rfl) ⟨183170, by rfl⟩ : syracuseStep 244227 = 366341) B366341
theorem B244243 : Blo 243817 244243 := bstep (se 1 (by rfl) ⟨183182, by rfl⟩ : syracuseStep 244243 = 366365) B366365
theorem B244259 : Blo 243817 244259 := bstep (se 1 (by rfl) ⟨183194, by rfl⟩ : syracuseStep 244259 = 366389) B366389
theorem B834083 : Blo 243817 834083 := bstep (se 1 (by rfl) ⟨625562, by rfl⟩ : syracuseStep 834083 = 1251125) B1251125
theorem B244275 : Blo 243817 244275 := bstep (se 1 (by rfl) ⟨183206, by rfl⟩ : syracuseStep 244275 = 366413) B366413
theorem B244291 : Blo 243817 244291 := bstep (se 1 (by rfl) ⟨183218, by rfl⟩ : syracuseStep 244291 = 366437) B366437
theorem B244307 : Blo 243817 244307 := bstep (se 1 (by rfl) ⟨183230, by rfl⟩ : syracuseStep 244307 = 366461) B366461
theorem B244323 : Blo 243817 244323 := bstep (se 1 (by rfl) ⟨183242, by rfl⟩ : syracuseStep 244323 = 366485) B366485
theorem B703075 : Blo 243817 703075 := bstep (se 1 (by rfl) ⟨527306, by rfl⟩ : syracuseStep 703075 = 1054613) B1054613
theorem B244339 : Blo 243817 244339 := bstep (se 1 (by rfl) ⟨183254, by rfl⟩ : syracuseStep 244339 = 366509) B366509
theorem B244355 : Blo 243817 244355 := bstep (se 1 (by rfl) ⟨183266, by rfl⟩ : syracuseStep 244355 = 366533) B366533
theorem B277123 : Blo 243817 277123 := bstep (se 1 (by rfl) ⟨207842, by rfl⟩ : syracuseStep 277123 = 415685) B415685
theorem B244371 : Blo 243817 244371 := bstep (se 1 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 244371 = 366557) B366557
theorem B244387 : Blo 243817 244387 := bstep (se 1 (by rfl) ⟨183290, by rfl⟩ : syracuseStep 244387 = 366581) B366581
theorem B244403 : Blo 243817 244403 := bstep (se 1 (by rfl) ⟨183302, by rfl⟩ : syracuseStep 244403 = 366605) B366605
theorem B244419 : Blo 243817 244419 := bstep (se 1 (by rfl) ⟨183314, by rfl⟩ : syracuseStep 244419 = 366629) B366629
theorem B244435 : Blo 243817 244435 := bstep (se 1 (by rfl) ⟨183326, by rfl⟩ : syracuseStep 244435 = 366653) B366653
theorem B244451 : Blo 243817 244451 := bstep (se 1 (by rfl) ⟨183338, by rfl⟩ : syracuseStep 244451 = 366677) B366677
theorem B244467 : Blo 243817 244467 := bstep (se 1 (by rfl) ⟨183350, by rfl⟩ : syracuseStep 244467 = 366701) B366701
theorem B244483 : Blo 243817 244483 := bstep (se 1 (by rfl) ⟨183362, by rfl⟩ : syracuseStep 244483 = 366725) B366725
theorem B703235 : Blo 243817 703235 := bstep (se 1 (by rfl) ⟨527426, by rfl⟩ : syracuseStep 703235 = 1054853) B1054853
theorem B244499 : Blo 243817 244499 := bstep (se 1 (by rfl) ⟨183374, by rfl⟩ : syracuseStep 244499 = 366749) B366749
theorem B277267 : Blo 243817 277267 := bstep (se 1 (by rfl) ⟨207950, by rfl⟩ : syracuseStep 277267 = 415901) B415901
theorem B244515 : Blo 243817 244515 := bstep (se 1 (by rfl) ⟨183386, by rfl⟩ : syracuseStep 244515 = 366773) B366773
theorem B834353 : Blo 243817 834353 := bstep (se 2 (by rfl) ⟨312882, by rfl⟩ : syracuseStep 834353 = 625765) B625765
theorem B244531 : Blo 243817 244531 := bstep (se 1 (by rfl) ⟨183398, by rfl⟩ : syracuseStep 244531 = 366797) B366797
theorem B244547 : Blo 243817 244547 := bstep (se 1 (by rfl) ⟨183410, by rfl⟩ : syracuseStep 244547 = 366821) B366821
theorem B244563 : Blo 243817 244563 := bstep (se 1 (by rfl) ⟨183422, by rfl⟩ : syracuseStep 244563 = 366845) B366845
theorem B244579 : Blo 243817 244579 := bstep (se 1 (by rfl) ⟨183434, by rfl⟩ : syracuseStep 244579 = 366869) B366869
theorem B244595 : Blo 243817 244595 := bstep (se 1 (by rfl) ⟨183446, by rfl⟩ : syracuseStep 244595 = 366893) B366893
theorem B244611 : Blo 243817 244611 := bstep (se 1 (by rfl) ⟨183458, by rfl⟩ : syracuseStep 244611 = 366917) B366917
theorem B244627 : Blo 243817 244627 := bstep (se 1 (by rfl) ⟨183470, by rfl⟩ : syracuseStep 244627 = 366941) B366941
theorem B244643 : Blo 243817 244643 := bstep (se 1 (by rfl) ⟨183482, by rfl⟩ : syracuseStep 244643 = 366965) B366965
theorem B277411 : Blo 243817 277411 := bstep (se 1 (by rfl) ⟨208058, by rfl⟩ : syracuseStep 277411 = 416117) B416117
theorem B244659 : Blo 243817 244659 := bstep (se 1 (by rfl) ⟨183494, by rfl⟩ : syracuseStep 244659 = 366989) B366989
theorem B244675 : Blo 243817 244675 := bstep (se 1 (by rfl) ⟨183506, by rfl⟩ : syracuseStep 244675 = 367013) B367013
theorem B244691 : Blo 243817 244691 := bstep (se 1 (by rfl) ⟨183518, by rfl⟩ : syracuseStep 244691 = 367037) B367037
theorem B244707 : Blo 243817 244707 := bstep (se 1 (by rfl) ⟨183530, by rfl⟩ : syracuseStep 244707 = 367061) B367061
theorem B2243555 : Blo 243817 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B244723 : Blo 243817 244723 := bstep (se 1 (by rfl) ⟨183542, by rfl⟩ : syracuseStep 244723 = 367085) B367085
theorem B244739 : Blo 243817 244739 := bstep (se 1 (by rfl) ⟨183554, by rfl⟩ : syracuseStep 244739 = 367109) B367109
theorem B244755 : Blo 243817 244755 := bstep (se 1 (by rfl) ⟨183566, by rfl⟩ : syracuseStep 244755 = 367133) B367133
theorem B244771 : Blo 243817 244771 := bstep (se 1 (by rfl) ⟨183578, by rfl⟩ : syracuseStep 244771 = 367157) B367157
theorem B244787 : Blo 243817 244787 := bstep (se 1 (by rfl) ⟨183590, by rfl⟩ : syracuseStep 244787 = 367181) B367181
theorem B277555 : Blo 243817 277555 := bstep (se 1 (by rfl) ⟨208166, by rfl⟩ : syracuseStep 277555 = 416333) B416333
theorem B244803 : Blo 243817 244803 := bstep (se 1 (by rfl) ⟨183602, by rfl⟩ : syracuseStep 244803 = 367205) B367205
theorem B244819 : Blo 243817 244819 := bstep (se 1 (by rfl) ⟨183614, by rfl⟩ : syracuseStep 244819 = 367229) B367229
theorem B244835 : Blo 243817 244835 := bstep (se 1 (by rfl) ⟨183626, by rfl⟩ : syracuseStep 244835 = 367253) B367253
theorem B244851 : Blo 243817 244851 := bstep (se 1 (by rfl) ⟨183638, by rfl⟩ : syracuseStep 244851 = 367277) B367277
theorem B310387 : Blo 243817 310387 := bstep (se 1 (by rfl) ⟨232790, by rfl⟩ : syracuseStep 310387 = 465581) B465581
theorem B244867 : Blo 243817 244867 := bstep (se 1 (by rfl) ⟨183650, by rfl⟩ : syracuseStep 244867 = 367301) B367301
theorem B244883 : Blo 243817 244883 := bstep (se 1 (by rfl) ⟨183662, by rfl⟩ : syracuseStep 244883 = 367325) B367325
theorem B244899 : Blo 243817 244899 := bstep (se 1 (by rfl) ⟨183674, by rfl⟩ : syracuseStep 244899 = 367349) B367349
theorem B244915 : Blo 243817 244915 := bstep (se 1 (by rfl) ⟨183686, by rfl⟩ : syracuseStep 244915 = 367373) B367373
theorem B244931 : Blo 243817 244931 := bstep (se 1 (by rfl) ⟨183698, by rfl⟩ : syracuseStep 244931 = 367397) B367397
theorem B277699 : Blo 243817 277699 := bstep (se 1 (by rfl) ⟨208274, by rfl⟩ : syracuseStep 277699 = 416549) B416549
theorem B244947 : Blo 243817 244947 := bstep (se 1 (by rfl) ⟨183710, by rfl⟩ : syracuseStep 244947 = 367421) B367421
theorem B310483 : Blo 243817 310483 := bstep (se 1 (by rfl) ⟨232862, by rfl⟩ : syracuseStep 310483 = 465725) B465725
theorem B1391843 : Blo 243817 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B244963 : Blo 243817 244963 := bstep (se 1 (by rfl) ⟨183722, by rfl⟩ : syracuseStep 244963 = 367445) B367445
theorem B244979 : Blo 243817 244979 := bstep (se 1 (by rfl) ⟨183734, by rfl⟩ : syracuseStep 244979 = 367469) B367469
theorem B244995 : Blo 243817 244995 := bstep (se 1 (by rfl) ⟨183746, by rfl⟩ : syracuseStep 244995 = 367493) B367493
theorem B245011 : Blo 243817 245011 := bstep (se 1 (by rfl) ⟨183758, by rfl⟩ : syracuseStep 245011 = 367517) B367517
theorem B245027 : Blo 243817 245027 := bstep (se 1 (by rfl) ⟨183770, by rfl⟩ : syracuseStep 245027 = 367541) B367541
theorem B245043 : Blo 243817 245043 := bstep (se 1 (by rfl) ⟨183782, by rfl⟩ : syracuseStep 245043 = 367565) B367565
theorem B245059 : Blo 243817 245059 := bstep (se 1 (by rfl) ⟨183794, by rfl⟩ : syracuseStep 245059 = 367589) B367589
theorem B834893 : Blo 243817 834893 := bstep (se 3 (by rfl) ⟨156542, by rfl⟩ : syracuseStep 834893 = 313085) B313085
theorem B245075 : Blo 243817 245075 := bstep (se 1 (by rfl) ⟨183806, by rfl⟩ : syracuseStep 245075 = 367613) B367613
theorem B277843 : Blo 243817 277843 := bstep (se 1 (by rfl) ⟨208382, by rfl⟩ : syracuseStep 277843 = 416765) B416765
theorem B245091 : Blo 243817 245091 := bstep (se 1 (by rfl) ⟨183818, by rfl⟩ : syracuseStep 245091 = 367637) B367637
theorem B245107 : Blo 243817 245107 := bstep (se 1 (by rfl) ⟨183830, by rfl⟩ : syracuseStep 245107 = 367661) B367661
theorem B245123 : Blo 243817 245123 := bstep (se 1 (by rfl) ⟨183842, by rfl⟩ : syracuseStep 245123 = 367685) B367685
theorem B834947 : Blo 243817 834947 := bstep (se 1 (by rfl) ⟨626210, by rfl⟩ : syracuseStep 834947 = 1252421) B1252421
theorem B245139 : Blo 243817 245139 := bstep (se 1 (by rfl) ⟨183854, by rfl⟩ : syracuseStep 245139 = 367709) B367709
theorem B245155 : Blo 243817 245155 := bstep (se 1 (by rfl) ⟨183866, by rfl⟩ : syracuseStep 245155 = 367733) B367733
theorem B474545 : Blo 243817 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B245171 : Blo 243817 245171 := bstep (se 1 (by rfl) ⟨183878, by rfl⟩ : syracuseStep 245171 = 367757) B367757
theorem B245187 : Blo 243817 245187 := bstep (se 1 (by rfl) ⟨183890, by rfl⟩ : syracuseStep 245187 = 367781) B367781
theorem B245203 : Blo 243817 245203 := bstep (se 1 (by rfl) ⟨183902, by rfl⟩ : syracuseStep 245203 = 367805) B367805
theorem B245219 : Blo 243817 245219 := bstep (se 1 (by rfl) ⟨183914, by rfl⟩ : syracuseStep 245219 = 367829) B367829
theorem B277987 : Blo 243817 277987 := bstep (se 1 (by rfl) ⟨208490, by rfl⟩ : syracuseStep 277987 = 416981) B416981
theorem B245235 : Blo 243817 245235 := bstep (se 1 (by rfl) ⟨183926, by rfl⟩ : syracuseStep 245235 = 367853) B367853
theorem B245251 : Blo 243817 245251 := bstep (se 1 (by rfl) ⟨183938, by rfl⟩ : syracuseStep 245251 = 367877) B367877
theorem B245267 : Blo 243817 245267 := bstep (se 1 (by rfl) ⟨183950, by rfl⟩ : syracuseStep 245267 = 367901) B367901
theorem B245283 : Blo 243817 245283 := bstep (se 1 (by rfl) ⟨183962, by rfl⟩ : syracuseStep 245283 = 367925) B367925
theorem B245299 : Blo 243817 245299 := bstep (se 1 (by rfl) ⟨183974, by rfl⟩ : syracuseStep 245299 = 367949) B367949
theorem B245315 : Blo 243817 245315 := bstep (se 1 (by rfl) ⟨183986, by rfl⟩ : syracuseStep 245315 = 367973) B367973
theorem B245331 : Blo 243817 245331 := bstep (se 1 (by rfl) ⟨183998, by rfl⟩ : syracuseStep 245331 = 367997) B367997
theorem B245347 : Blo 243817 245347 := bstep (se 1 (by rfl) ⟨184010, by rfl⟩ : syracuseStep 245347 = 368021) B368021
theorem B245363 : Blo 243817 245363 := bstep (se 1 (by rfl) ⟨184022, by rfl⟩ : syracuseStep 245363 = 368045) B368045
theorem B278131 : Blo 243817 278131 := bstep (se 1 (by rfl) ⟨208598, by rfl⟩ : syracuseStep 278131 = 417197) B417197
theorem B245379 : Blo 243817 245379 := bstep (se 1 (by rfl) ⟨184034, by rfl⟩ : syracuseStep 245379 = 368069) B368069
theorem B835217 : Blo 243817 835217 := bstep (se 2 (by rfl) ⟨313206, by rfl⟩ : syracuseStep 835217 = 626413) B626413
theorem B245395 : Blo 243817 245395 := bstep (se 1 (by rfl) ⟨184046, by rfl⟩ : syracuseStep 245395 = 368093) B368093
theorem B245411 : Blo 243817 245411 := bstep (se 1 (by rfl) ⟨184058, by rfl⟩ : syracuseStep 245411 = 368117) B368117
theorem B245427 : Blo 243817 245427 := bstep (se 1 (by rfl) ⟨184070, by rfl⟩ : syracuseStep 245427 = 368141) B368141
theorem B245443 : Blo 243817 245443 := bstep (se 1 (by rfl) ⟨184082, by rfl⟩ : syracuseStep 245443 = 368165) B368165
theorem B310979 : Blo 243817 310979 := bstep (se 1 (by rfl) ⟨233234, by rfl⟩ : syracuseStep 310979 = 466469) B466469
theorem B704209 : Blo 243817 704209 := bstep (se 2 (by rfl) ⟨264078, by rfl⟩ : syracuseStep 704209 = 528157) B528157
theorem B245459 : Blo 243817 245459 := bstep (se 1 (by rfl) ⟨184094, by rfl⟩ : syracuseStep 245459 = 368189) B368189
theorem B245475 : Blo 243817 245475 := bstep (se 1 (by rfl) ⟨184106, by rfl⟩ : syracuseStep 245475 = 368213) B368213
theorem B245491 : Blo 243817 245491 := bstep (se 1 (by rfl) ⟨184118, by rfl⟩ : syracuseStep 245491 = 368237) B368237
theorem B245507 : Blo 243817 245507 := bstep (se 1 (by rfl) ⟨184130, by rfl⟩ : syracuseStep 245507 = 368261) B368261
theorem B278275 : Blo 243817 278275 := bstep (se 1 (by rfl) ⟨208706, by rfl⟩ : syracuseStep 278275 = 417413) B417413
theorem B245523 : Blo 243817 245523 := bstep (se 1 (by rfl) ⟨184142, by rfl⟩ : syracuseStep 245523 = 368285) B368285
theorem B245539 : Blo 243817 245539 := bstep (se 1 (by rfl) ⟨184154, by rfl⟩ : syracuseStep 245539 = 368309) B368309
theorem B704305 : Blo 243817 704305 := bstep (se 2 (by rfl) ⟨264114, by rfl⟩ : syracuseStep 704305 = 528229) B528229
theorem B245555 : Blo 243817 245555 := bstep (se 1 (by rfl) ⟨184166, by rfl⟩ : syracuseStep 245555 = 368333) B368333
theorem B245571 : Blo 243817 245571 := bstep (se 1 (by rfl) ⟨184178, by rfl⟩ : syracuseStep 245571 = 368357) B368357
theorem B245587 : Blo 243817 245587 := bstep (se 1 (by rfl) ⟨184190, by rfl⟩ : syracuseStep 245587 = 368381) B368381
theorem B245603 : Blo 243817 245603 := bstep (se 1 (by rfl) ⟨184202, by rfl⟩ : syracuseStep 245603 = 368405) B368405
theorem B245619 : Blo 243817 245619 := bstep (se 1 (by rfl) ⟨184214, by rfl⟩ : syracuseStep 245619 = 368429) B368429
theorem B245635 : Blo 243817 245635 := bstep (se 1 (by rfl) ⟨184226, by rfl⟩ : syracuseStep 245635 = 368453) B368453
theorem B245651 : Blo 243817 245651 := bstep (se 1 (by rfl) ⟨184238, by rfl⟩ : syracuseStep 245651 = 368477) B368477
theorem B278419 : Blo 243817 278419 := bstep (se 1 (by rfl) ⟨208814, by rfl⟩ : syracuseStep 278419 = 417629) B417629
theorem B245667 : Blo 243817 245667 := bstep (se 1 (by rfl) ⟨184250, by rfl⟩ : syracuseStep 245667 = 368501) B368501
theorem B245683 : Blo 243817 245683 := bstep (se 1 (by rfl) ⟨184262, by rfl⟩ : syracuseStep 245683 = 368525) B368525
theorem B245699 : Blo 243817 245699 := bstep (se 1 (by rfl) ⟨184274, by rfl⟩ : syracuseStep 245699 = 368549) B368549
theorem B278483 : Blo 243817 278483 := bstep (se 1 (by rfl) ⟨208862, by rfl⟩ : syracuseStep 278483 = 417725) B417725
theorem B245715 : Blo 243817 245715 := bstep (se 1 (by rfl) ⟨184286, by rfl⟩ : syracuseStep 245715 = 368573) B368573
theorem B245731 : Blo 243817 245731 := bstep (se 1 (by rfl) ⟨184298, by rfl⟩ : syracuseStep 245731 = 368597) B368597
theorem B245747 : Blo 243817 245747 := bstep (se 1 (by rfl) ⟨184310, by rfl⟩ : syracuseStep 245747 = 368621) B368621
theorem B245763 : Blo 243817 245763 := bstep (se 1 (by rfl) ⟨184322, by rfl⟩ : syracuseStep 245763 = 368645) B368645
theorem B245779 : Blo 243817 245779 := bstep (se 1 (by rfl) ⟨184334, by rfl⟩ : syracuseStep 245779 = 368669) B368669
theorem B245795 : Blo 243817 245795 := bstep (se 1 (by rfl) ⟨184346, by rfl⟩ : syracuseStep 245795 = 368693) B368693
theorem B278563 : Blo 243817 278563 := bstep (se 1 (by rfl) ⟨208922, by rfl⟩ : syracuseStep 278563 = 417845) B417845
theorem B245811 : Blo 243817 245811 := bstep (se 1 (by rfl) ⟨184358, by rfl⟩ : syracuseStep 245811 = 368717) B368717
theorem B245827 : Blo 243817 245827 := bstep (se 1 (by rfl) ⟨184370, by rfl⟩ : syracuseStep 245827 = 368741) B368741
theorem B245843 : Blo 243817 245843 := bstep (se 1 (by rfl) ⟨184382, by rfl⟩ : syracuseStep 245843 = 368765) B368765
theorem B245859 : Blo 243817 245859 := bstep (se 1 (by rfl) ⟨184394, by rfl⟩ : syracuseStep 245859 = 368789) B368789
theorem B1065059 : Blo 243817 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B934001 : Blo 243817 934001 := bstep (se 2 (by rfl) ⟨350250, by rfl⟩ : syracuseStep 934001 = 700501) B700501
theorem B245875 : Blo 243817 245875 := bstep (se 1 (by rfl) ⟨184406, by rfl⟩ : syracuseStep 245875 = 368813) B368813
theorem B245891 : Blo 243817 245891 := bstep (se 1 (by rfl) ⟨184418, by rfl⟩ : syracuseStep 245891 = 368837) B368837
theorem B245907 : Blo 243817 245907 := bstep (se 1 (by rfl) ⟨184430, by rfl⟩ : syracuseStep 245907 = 368861) B368861
theorem B245923 : Blo 243817 245923 := bstep (se 1 (by rfl) ⟨184442, by rfl⟩ : syracuseStep 245923 = 368885) B368885
theorem B835757 : Blo 243817 835757 := bstep (se 3 (by rfl) ⟨156704, by rfl⟩ : syracuseStep 835757 = 313409) B313409
theorem B245939 : Blo 243817 245939 := bstep (se 1 (by rfl) ⟨184454, by rfl⟩ : syracuseStep 245939 = 368909) B368909
theorem B278707 : Blo 243817 278707 := bstep (se 1 (by rfl) ⟨209030, by rfl⟩ : syracuseStep 278707 = 418061) B418061
theorem B606403 : Blo 243817 606403 := bstep (se 1 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 606403 = 909605) B909605
theorem B245955 : Blo 243817 245955 := bstep (se 1 (by rfl) ⟨184466, by rfl⟩ : syracuseStep 245955 = 368933) B368933
theorem B245971 : Blo 243817 245971 := bstep (se 1 (by rfl) ⟨184478, by rfl⟩ : syracuseStep 245971 = 368957) B368957
theorem B245987 : Blo 243817 245987 := bstep (se 1 (by rfl) ⟨184490, by rfl⟩ : syracuseStep 245987 = 368981) B368981
theorem B835811 : Blo 243817 835811 := bstep (se 1 (by rfl) ⟨626858, by rfl⟩ : syracuseStep 835811 = 1253717) B1253717
theorem B246003 : Blo 243817 246003 := bstep (se 1 (by rfl) ⟨184502, by rfl⟩ : syracuseStep 246003 = 369005) B369005
theorem B246019 : Blo 243817 246019 := bstep (se 1 (by rfl) ⟨184514, by rfl⟩ : syracuseStep 246019 = 369029) B369029
theorem B246035 : Blo 243817 246035 := bstep (se 1 (by rfl) ⟨184526, by rfl⟩ : syracuseStep 246035 = 369053) B369053
theorem B246051 : Blo 243817 246051 := bstep (se 1 (by rfl) ⟨184538, by rfl⟩ : syracuseStep 246051 = 369077) B369077
theorem B246067 : Blo 243817 246067 := bstep (se 1 (by rfl) ⟨184550, by rfl⟩ : syracuseStep 246067 = 369101) B369101
theorem B246083 : Blo 243817 246083 := bstep (se 1 (by rfl) ⟨184562, by rfl⟩ : syracuseStep 246083 = 369125) B369125
theorem B1982789 : Blo 243817 1982789 := bstep (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) B371773
theorem B246099 : Blo 243817 246099 := bstep (se 1 (by rfl) ⟨184574, by rfl⟩ : syracuseStep 246099 = 369149) B369149
theorem B246115 : Blo 243817 246115 := bstep (se 1 (by rfl) ⟨184586, by rfl⟩ : syracuseStep 246115 = 369173) B369173
theorem B1786211 : Blo 243817 1786211 := bstep (se 1 (by rfl) ⟨1339658, by rfl⟩ : syracuseStep 1786211 = 2679317) B2679317
theorem B246131 : Blo 243817 246131 := bstep (se 1 (by rfl) ⟨184598, by rfl⟩ : syracuseStep 246131 = 369197) B369197
theorem B246147 : Blo 243817 246147 := bstep (se 1 (by rfl) ⟨184610, by rfl⟩ : syracuseStep 246147 = 369221) B369221
theorem B311683 : Blo 243817 311683 := bstep (se 1 (by rfl) ⟨233762, by rfl⟩ : syracuseStep 311683 = 467525) B467525
theorem B246163 : Blo 243817 246163 := bstep (se 1 (by rfl) ⟨184622, by rfl⟩ : syracuseStep 246163 = 369245) B369245
theorem B246179 : Blo 243817 246179 := bstep (se 1 (by rfl) ⟨184634, by rfl⟩ : syracuseStep 246179 = 369269) B369269
theorem B246195 : Blo 243817 246195 := bstep (se 1 (by rfl) ⟨184646, by rfl⟩ : syracuseStep 246195 = 369293) B369293
theorem B246211 : Blo 243817 246211 := bstep (se 1 (by rfl) ⟨184658, by rfl⟩ : syracuseStep 246211 = 369317) B369317
theorem B246227 : Blo 243817 246227 := bstep (se 1 (by rfl) ⟨184670, by rfl⟩ : syracuseStep 246227 = 369341) B369341
theorem B246243 : Blo 243817 246243 := bstep (se 1 (by rfl) ⟨184682, by rfl⟩ : syracuseStep 246243 = 369365) B369365
theorem B311779 : Blo 243817 311779 := bstep (se 1 (by rfl) ⟨233834, by rfl⟩ : syracuseStep 311779 = 467669) B467669
theorem B836081 : Blo 243817 836081 := bstep (se 2 (by rfl) ⟨313530, by rfl⟩ : syracuseStep 836081 = 627061) B627061
theorem B246259 : Blo 243817 246259 := bstep (se 1 (by rfl) ⟨184694, by rfl⟩ : syracuseStep 246259 = 369389) B369389
theorem B246275 : Blo 243817 246275 := bstep (se 1 (by rfl) ⟨184706, by rfl⟩ : syracuseStep 246275 = 369413) B369413
theorem B246291 : Blo 243817 246291 := bstep (se 1 (by rfl) ⟨184718, by rfl⟩ : syracuseStep 246291 = 369437) B369437
theorem B246307 : Blo 243817 246307 := bstep (se 1 (by rfl) ⟨184730, by rfl⟩ : syracuseStep 246307 = 369461) B369461
theorem B246323 : Blo 243817 246323 := bstep (se 1 (by rfl) ⟨184742, by rfl⟩ : syracuseStep 246323 = 369485) B369485
theorem B246339 : Blo 243817 246339 := bstep (se 1 (by rfl) ⟨184754, by rfl⟩ : syracuseStep 246339 = 369509) B369509
theorem B246355 : Blo 243817 246355 := bstep (se 1 (by rfl) ⟨184766, by rfl⟩ : syracuseStep 246355 = 369533) B369533
theorem B2802275 : Blo 243817 2802275 := bstep (se 1 (by rfl) ⟨2101706, by rfl⟩ : syracuseStep 2802275 = 4203413) B4203413
theorem B246371 : Blo 243817 246371 := bstep (se 1 (by rfl) ⟨184778, by rfl⟩ : syracuseStep 246371 = 369557) B369557
theorem B246387 : Blo 243817 246387 := bstep (se 1 (by rfl) ⟨184790, by rfl⟩ : syracuseStep 246387 = 369581) B369581
theorem B246403 : Blo 243817 246403 := bstep (se 1 (by rfl) ⟨184802, by rfl⟩ : syracuseStep 246403 = 369605) B369605
theorem B246419 : Blo 243817 246419 := bstep (se 1 (by rfl) ⟨184814, by rfl⟩ : syracuseStep 246419 = 369629) B369629
theorem B246435 : Blo 243817 246435 := bstep (se 1 (by rfl) ⟨184826, by rfl⟩ : syracuseStep 246435 = 369653) B369653
theorem B246451 : Blo 243817 246451 := bstep (se 1 (by rfl) ⟨184838, by rfl⟩ : syracuseStep 246451 = 369677) B369677
theorem B246467 : Blo 243817 246467 := bstep (se 1 (by rfl) ⟨184850, by rfl⟩ : syracuseStep 246467 = 369701) B369701
theorem B246483 : Blo 243817 246483 := bstep (se 1 (by rfl) ⟨184862, by rfl⟩ : syracuseStep 246483 = 369725) B369725
theorem B246499 : Blo 243817 246499 := bstep (se 1 (by rfl) ⟨184874, by rfl⟩ : syracuseStep 246499 = 369749) B369749
theorem B1852145 : Blo 243817 1852145 := bstep (se 2 (by rfl) ⟨694554, by rfl⟩ : syracuseStep 1852145 = 1389109) B1389109
theorem B246515 : Blo 243817 246515 := bstep (se 1 (by rfl) ⟨184886, by rfl⟩ : syracuseStep 246515 = 369773) B369773
theorem B246531 : Blo 243817 246531 := bstep (se 1 (by rfl) ⟨184898, by rfl⟩ : syracuseStep 246531 = 369797) B369797
theorem B836369 : Blo 243817 836369 := bstep (se 2 (by rfl) ⟨313638, by rfl⟩ : syracuseStep 836369 = 627277) B627277
theorem B246547 : Blo 243817 246547 := bstep (se 1 (by rfl) ⟨184910, by rfl⟩ : syracuseStep 246547 = 369821) B369821
theorem B246563 : Blo 243817 246563 := bstep (se 1 (by rfl) ⟨184922, by rfl⟩ : syracuseStep 246563 = 369845) B369845
theorem B246579 : Blo 243817 246579 := bstep (se 1 (by rfl) ⟨184934, by rfl⟩ : syracuseStep 246579 = 369869) B369869
theorem B246595 : Blo 243817 246595 := bstep (se 1 (by rfl) ⟨184946, by rfl⟩ : syracuseStep 246595 = 369893) B369893
theorem B246611 : Blo 243817 246611 := bstep (se 1 (by rfl) ⟨184958, by rfl⟩ : syracuseStep 246611 = 369917) B369917
theorem B246627 : Blo 243817 246627 := bstep (se 1 (by rfl) ⟨184970, by rfl⟩ : syracuseStep 246627 = 369941) B369941
theorem B246643 : Blo 243817 246643 := bstep (se 1 (by rfl) ⟨184982, by rfl⟩ : syracuseStep 246643 = 369965) B369965
theorem B246659 : Blo 243817 246659 := bstep (se 1 (by rfl) ⟨184994, by rfl⟩ : syracuseStep 246659 = 369989) B369989
theorem B246675 : Blo 243817 246675 := bstep (se 1 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 246675 = 370013) B370013
theorem B246691 : Blo 243817 246691 := bstep (se 1 (by rfl) ⟨185018, by rfl⟩ : syracuseStep 246691 = 370037) B370037
theorem B246707 : Blo 243817 246707 := bstep (se 1 (by rfl) ⟨185030, by rfl⟩ : syracuseStep 246707 = 370061) B370061
theorem B246723 : Blo 243817 246723 := bstep (se 1 (by rfl) ⟨185042, by rfl⟩ : syracuseStep 246723 = 370085) B370085
theorem B312275 : Blo 243817 312275 := bstep (se 1 (by rfl) ⟨234206, by rfl⟩ : syracuseStep 312275 = 468413) B468413
theorem B246739 : Blo 243817 246739 := bstep (se 1 (by rfl) ⟨185054, by rfl⟩ : syracuseStep 246739 = 370109) B370109
theorem B246755 : Blo 243817 246755 := bstep (se 1 (by rfl) ⟨185066, by rfl⟩ : syracuseStep 246755 = 370133) B370133
theorem B246771 : Blo 243817 246771 := bstep (se 1 (by rfl) ⟨185078, by rfl⟩ : syracuseStep 246771 = 370157) B370157
theorem B246787 : Blo 243817 246787 := bstep (se 1 (by rfl) ⟨185090, by rfl⟩ : syracuseStep 246787 = 370181) B370181
theorem B246803 : Blo 243817 246803 := bstep (se 1 (by rfl) ⟨185102, by rfl⟩ : syracuseStep 246803 = 370205) B370205
theorem B246819 : Blo 243817 246819 := bstep (se 1 (by rfl) ⟨185114, by rfl⟩ : syracuseStep 246819 = 370229) B370229
theorem B705581 : Blo 243817 705581 := bstep (se 3 (by rfl) ⟨132296, by rfl⟩ : syracuseStep 705581 = 264593) B264593
theorem B246835 : Blo 243817 246835 := bstep (se 1 (by rfl) ⟨185126, by rfl⟩ : syracuseStep 246835 = 370253) B370253
theorem B246851 : Blo 243817 246851 := bstep (se 1 (by rfl) ⟨185138, by rfl⟩ : syracuseStep 246851 = 370277) B370277
theorem B246867 : Blo 243817 246867 := bstep (se 1 (by rfl) ⟨185150, by rfl⟩ : syracuseStep 246867 = 370301) B370301
theorem B246883 : Blo 243817 246883 := bstep (se 1 (by rfl) ⟨185162, by rfl⟩ : syracuseStep 246883 = 370325) B370325
theorem B246899 : Blo 243817 246899 := bstep (se 1 (by rfl) ⟨185174, by rfl⟩ : syracuseStep 246899 = 370349) B370349
theorem B246915 : Blo 243817 246915 := bstep (se 1 (by rfl) ⟨185186, by rfl⟩ : syracuseStep 246915 = 370373) B370373
theorem B246931 : Blo 243817 246931 := bstep (se 1 (by rfl) ⟨185198, by rfl⟩ : syracuseStep 246931 = 370397) B370397
theorem B246947 : Blo 243817 246947 := bstep (se 1 (by rfl) ⟨185210, by rfl⟩ : syracuseStep 246947 = 370421) B370421
theorem B246963 : Blo 243817 246963 := bstep (se 1 (by rfl) ⟨185222, by rfl⟩ : syracuseStep 246963 = 370445) B370445
theorem B246979 : Blo 243817 246979 := bstep (se 1 (by rfl) ⟨185234, by rfl⟩ : syracuseStep 246979 = 370469) B370469
theorem B246995 : Blo 243817 246995 := bstep (se 1 (by rfl) ⟨185246, by rfl⟩ : syracuseStep 246995 = 370493) B370493
theorem B247011 : Blo 243817 247011 := bstep (se 1 (by rfl) ⟨185258, by rfl⟩ : syracuseStep 247011 = 370517) B370517
theorem B247027 : Blo 243817 247027 := bstep (se 1 (by rfl) ⟨185270, by rfl⟩ : syracuseStep 247027 = 370541) B370541
theorem B247043 : Blo 243817 247043 := bstep (se 1 (by rfl) ⟨185282, by rfl⟩ : syracuseStep 247043 = 370565) B370565
theorem B247059 : Blo 243817 247059 := bstep (se 1 (by rfl) ⟨185294, by rfl⟩ : syracuseStep 247059 = 370589) B370589
theorem B247075 : Blo 243817 247075 := bstep (se 1 (by rfl) ⟨185306, by rfl⟩ : syracuseStep 247075 = 370613) B370613
theorem B247091 : Blo 243817 247091 := bstep (se 1 (by rfl) ⟨185318, by rfl⟩ : syracuseStep 247091 = 370637) B370637
theorem B247107 : Blo 243817 247107 := bstep (se 1 (by rfl) ⟨185330, by rfl⟩ : syracuseStep 247107 = 370661) B370661
theorem B247123 : Blo 243817 247123 := bstep (se 1 (by rfl) ⟨185342, by rfl⟩ : syracuseStep 247123 = 370685) B370685
theorem B247139 : Blo 243817 247139 := bstep (se 1 (by rfl) ⟨185354, by rfl⟩ : syracuseStep 247139 = 370709) B370709
theorem B247155 : Blo 243817 247155 := bstep (se 1 (by rfl) ⟨185366, by rfl⟩ : syracuseStep 247155 = 370733) B370733
theorem B247171 : Blo 243817 247171 := bstep (se 1 (by rfl) ⟨185378, by rfl⟩ : syracuseStep 247171 = 370757) B370757
theorem B247187 : Blo 243817 247187 := bstep (se 1 (by rfl) ⟨185390, by rfl⟩ : syracuseStep 247187 = 370781) B370781
theorem B247203 : Blo 243817 247203 := bstep (se 1 (by rfl) ⟨185402, by rfl⟩ : syracuseStep 247203 = 370805) B370805
theorem B247219 : Blo 243817 247219 := bstep (se 1 (by rfl) ⟨185414, by rfl⟩ : syracuseStep 247219 = 370829) B370829
theorem B247235 : Blo 243817 247235 := bstep (se 1 (by rfl) ⟨185426, by rfl⟩ : syracuseStep 247235 = 370853) B370853
theorem B247251 : Blo 243817 247251 := bstep (se 1 (by rfl) ⟨185438, by rfl⟩ : syracuseStep 247251 = 370877) B370877
theorem B247267 : Blo 243817 247267 := bstep (se 1 (by rfl) ⟨185450, by rfl⟩ : syracuseStep 247267 = 370901) B370901
theorem B2377187 : Blo 243817 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B247283 : Blo 243817 247283 := bstep (se 1 (by rfl) ⟨185462, by rfl⟩ : syracuseStep 247283 = 370925) B370925
theorem B247299 : Blo 243817 247299 := bstep (se 1 (by rfl) ⟨185474, by rfl⟩ : syracuseStep 247299 = 370949) B370949
theorem B247315 : Blo 243817 247315 := bstep (se 1 (by rfl) ⟨185486, by rfl⟩ : syracuseStep 247315 = 370973) B370973
theorem B935459 : Blo 243817 935459 := bstep (se 1 (by rfl) ⟨701594, by rfl⟩ : syracuseStep 935459 = 1403189) B1403189
theorem B247331 : Blo 243817 247331 := bstep (se 1 (by rfl) ⟨185498, by rfl⟩ : syracuseStep 247331 = 370997) B370997
theorem B247347 : Blo 243817 247347 := bstep (se 1 (by rfl) ⟨185510, by rfl⟩ : syracuseStep 247347 = 371021) B371021
theorem B247363 : Blo 243817 247363 := bstep (se 1 (by rfl) ⟨185522, by rfl⟩ : syracuseStep 247363 = 371045) B371045
theorem B247379 : Blo 243817 247379 := bstep (se 1 (by rfl) ⟨185534, by rfl⟩ : syracuseStep 247379 = 371069) B371069
theorem B247395 : Blo 243817 247395 := bstep (se 1 (by rfl) ⟨185546, by rfl⟩ : syracuseStep 247395 = 371093) B371093
theorem B247411 : Blo 243817 247411 := bstep (se 1 (by rfl) ⟨185558, by rfl⟩ : syracuseStep 247411 = 371117) B371117
theorem B247427 : Blo 243817 247427 := bstep (se 1 (by rfl) ⟨185570, by rfl⟩ : syracuseStep 247427 = 371141) B371141
theorem B312979 : Blo 243817 312979 := bstep (se 1 (by rfl) ⟨234734, by rfl⟩ : syracuseStep 312979 = 469469) B469469
theorem B247443 : Blo 243817 247443 := bstep (se 1 (by rfl) ⟨185582, by rfl⟩ : syracuseStep 247443 = 371165) B371165
theorem B247459 : Blo 243817 247459 := bstep (se 1 (by rfl) ⟨185594, by rfl⟩ : syracuseStep 247459 = 371189) B371189
theorem B247475 : Blo 243817 247475 := bstep (se 1 (by rfl) ⟨185606, by rfl⟩ : syracuseStep 247475 = 371213) B371213
theorem B247491 : Blo 243817 247491 := bstep (se 1 (by rfl) ⟨185618, by rfl⟩ : syracuseStep 247491 = 371237) B371237
theorem B247507 : Blo 243817 247507 := bstep (se 1 (by rfl) ⟨185630, by rfl⟩ : syracuseStep 247507 = 371261) B371261
theorem B247523 : Blo 243817 247523 := bstep (se 1 (by rfl) ⟨185642, by rfl⟩ : syracuseStep 247523 = 371285) B371285
theorem B313075 : Blo 243817 313075 := bstep (se 1 (by rfl) ⟨234806, by rfl⟩ : syracuseStep 313075 = 469613) B469613
theorem B247539 : Blo 243817 247539 := bstep (se 1 (by rfl) ⟨185654, by rfl⟩ : syracuseStep 247539 = 371309) B371309
theorem B247555 : Blo 243817 247555 := bstep (se 1 (by rfl) ⟨185666, by rfl⟩ : syracuseStep 247555 = 371333) B371333
theorem B247571 : Blo 243817 247571 := bstep (se 1 (by rfl) ⟨185678, by rfl⟩ : syracuseStep 247571 = 371357) B371357
theorem B247587 : Blo 243817 247587 := bstep (se 1 (by rfl) ⟨185690, by rfl⟩ : syracuseStep 247587 = 371381) B371381
theorem B444209 : Blo 243817 444209 := bstep (se 2 (by rfl) ⟨166578, by rfl⟩ : syracuseStep 444209 = 333157) B333157
theorem B247603 : Blo 243817 247603 := bstep (se 1 (by rfl) ⟨185702, by rfl⟩ : syracuseStep 247603 = 371405) B371405
theorem B247619 : Blo 243817 247619 := bstep (se 1 (by rfl) ⟨185714, by rfl⟩ : syracuseStep 247619 = 371429) B371429
theorem B411473 : Blo 243817 411473 := bstep (se 2 (by rfl) ⟨154302, by rfl⟩ : syracuseStep 411473 = 308605) B308605
theorem B247635 : Blo 243817 247635 := bstep (se 1 (by rfl) ⟨185726, by rfl⟩ : syracuseStep 247635 = 371453) B371453
theorem B247651 : Blo 243817 247651 := bstep (se 1 (by rfl) ⟨185738, by rfl⟩ : syracuseStep 247651 = 371477) B371477
theorem B247667 : Blo 243817 247667 := bstep (se 1 (by rfl) ⟨185750, by rfl⟩ : syracuseStep 247667 = 371501) B371501
theorem B247683 : Blo 243817 247683 := bstep (se 1 (by rfl) ⟨185762, by rfl⟩ : syracuseStep 247683 = 371525) B371525
theorem B247699 : Blo 243817 247699 := bstep (se 1 (by rfl) ⟨185774, by rfl⟩ : syracuseStep 247699 = 371549) B371549
theorem B247715 : Blo 243817 247715 := bstep (se 1 (by rfl) ⟨185786, by rfl⟩ : syracuseStep 247715 = 371573) B371573
theorem B247731 : Blo 243817 247731 := bstep (se 1 (by rfl) ⟨185798, by rfl⟩ : syracuseStep 247731 = 371597) B371597
theorem B247747 : Blo 243817 247747 := bstep (se 1 (by rfl) ⟨185810, by rfl⟩ : syracuseStep 247747 = 371621) B371621
theorem B411601 : Blo 243817 411601 := bstep (se 2 (by rfl) ⟨154350, by rfl⟩ : syracuseStep 411601 = 308701) B308701
theorem B247763 : Blo 243817 247763 := bstep (se 1 (by rfl) ⟨185822, by rfl⟩ : syracuseStep 247763 = 371645) B371645
theorem B1066979 : Blo 243817 1066979 := bstep (se 1 (by rfl) ⟨800234, by rfl⟩ : syracuseStep 1066979 = 1600469) B1600469
theorem B247779 : Blo 243817 247779 := bstep (se 1 (by rfl) ⟨185834, by rfl⟩ : syracuseStep 247779 = 371669) B371669
theorem B411635 : Blo 243817 411635 := bstep (se 1 (by rfl) ⟨308726, by rfl⟩ : syracuseStep 411635 = 617453) B617453
theorem B247795 : Blo 243817 247795 := bstep (se 1 (by rfl) ⟨185846, by rfl⟩ : syracuseStep 247795 = 371693) B371693
theorem B247811 : Blo 243817 247811 := bstep (se 1 (by rfl) ⟨185858, by rfl⟩ : syracuseStep 247811 = 371717) B371717
theorem B280627 : Blo 243817 280627 := bstep (se 1 (by rfl) ⟨210470, by rfl⟩ : syracuseStep 280627 = 420941) B420941
theorem B411763 : Blo 243817 411763 := bstep (se 1 (by rfl) ⟨308822, by rfl⟩ : syracuseStep 411763 = 617645) B617645
theorem B313571 : Blo 243817 313571 := bstep (se 1 (by rfl) ⟨235178, by rfl⟩ : syracuseStep 313571 = 470357) B470357
theorem B411905 : Blo 243817 411905 := bstep (se 2 (by rfl) ⟨154464, by rfl⟩ : syracuseStep 411905 = 308929) B308929
theorem B412033 : Blo 243817 412033 := bstep (se 2 (by rfl) ⟨154512, by rfl⟩ : syracuseStep 412033 = 309025) B309025
theorem B412067 : Blo 243817 412067 := bstep (se 1 (by rfl) ⟨309050, by rfl⟩ : syracuseStep 412067 = 618101) B618101
theorem B510449 : Blo 243817 510449 := bstep (se 2 (by rfl) ⟨191418, by rfl⟩ : syracuseStep 510449 = 382837) B382837
theorem B936461 : Blo 243817 936461 := bstep (se 3 (by rfl) ⟨175586, by rfl⟩ : syracuseStep 936461 = 351173) B351173
theorem B412195 : Blo 243817 412195 := bstep (se 1 (by rfl) ⟨309146, by rfl⟩ : syracuseStep 412195 = 618293) B618293
theorem B1264241 : Blo 243817 1264241 := bstep (se 2 (by rfl) ⟨474090, by rfl⟩ : syracuseStep 1264241 = 948181) B948181
theorem B543395 : Blo 243817 543395 := bstep (se 1 (by rfl) ⟨407546, by rfl⟩ : syracuseStep 543395 = 815093) B815093
theorem B412337 : Blo 243817 412337 := bstep (se 2 (by rfl) ⟨154626, by rfl⟩ : syracuseStep 412337 = 309253) B309253
theorem B445169 : Blo 243817 445169 := bstep (se 2 (by rfl) ⟨166938, by rfl⟩ : syracuseStep 445169 = 333877) B333877
theorem B412465 : Blo 243817 412465 := bstep (se 2 (by rfl) ⟨154674, by rfl⟩ : syracuseStep 412465 = 309349) B309349
theorem B248627 : Blo 243817 248627 := bstep (se 1 (by rfl) ⟨186470, by rfl⟩ : syracuseStep 248627 = 372941) B372941
theorem B412499 : Blo 243817 412499 := bstep (se 1 (by rfl) ⟨309374, by rfl⟩ : syracuseStep 412499 = 618749) B618749
theorem B412627 : Blo 243817 412627 := bstep (se 1 (by rfl) ⟨309470, by rfl⟩ : syracuseStep 412627 = 618941) B618941
theorem B281603 : Blo 243817 281603 := bstep (se 1 (by rfl) ⟨211202, by rfl⟩ : syracuseStep 281603 = 422405) B422405
theorem B838669 : Blo 243817 838669 := bstep (se 3 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 838669 = 314501) B314501
theorem B412769 : Blo 243817 412769 := bstep (se 2 (by rfl) ⟨154788, by rfl⟩ : syracuseStep 412769 = 309577) B309577
theorem B412897 : Blo 243817 412897 := bstep (se 2 (by rfl) ⟨154836, by rfl⟩ : syracuseStep 412897 = 309673) B309673
theorem B5950691 : Blo 243817 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B412931 : Blo 243817 412931 := bstep (se 1 (by rfl) ⟨309698, by rfl⟩ : syracuseStep 412931 = 619397) B619397
theorem B314627 : Blo 243817 314627 := bstep (se 1 (by rfl) ⟨235970, by rfl⟩ : syracuseStep 314627 = 471941) B471941
theorem B413059 : Blo 243817 413059 := bstep (se 1 (by rfl) ⟨309794, by rfl⟩ : syracuseStep 413059 = 619589) B619589
theorem B347665 : Blo 243817 347665 := bstep (se 2 (by rfl) ⟨130374, by rfl⟩ : syracuseStep 347665 = 260749) B260749
theorem B413201 : Blo 243817 413201 := bstep (se 2 (by rfl) ⟨154950, by rfl⟩ : syracuseStep 413201 = 309901) B309901
theorem B347699 : Blo 243817 347699 := bstep (se 1 (by rfl) ⟨260774, by rfl⟩ : syracuseStep 347699 = 521549) B521549
theorem B413329 : Blo 243817 413329 := bstep (se 2 (by rfl) ⟨154998, by rfl⟩ : syracuseStep 413329 = 309997) B309997
theorem B413363 : Blo 243817 413363 := bstep (se 1 (by rfl) ⟨310022, by rfl⟩ : syracuseStep 413363 = 620045) B620045
theorem B413491 : Blo 243817 413491 := bstep (se 1 (by rfl) ⟨310118, by rfl⟩ : syracuseStep 413491 = 620237) B620237
theorem B839555 : Blo 243817 839555 := bstep (se 1 (by rfl) ⟨629666, by rfl⟩ : syracuseStep 839555 = 1259333) B1259333
theorem B2346893 : Blo 243817 2346893 := bstep (se 3 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 2346893 = 880085) B880085
theorem B413633 : Blo 243817 413633 := bstep (se 2 (by rfl) ⟨155112, by rfl⟩ : syracuseStep 413633 = 310225) B310225
theorem B413761 : Blo 243817 413761 := bstep (se 2 (by rfl) ⟨155160, by rfl⟩ : syracuseStep 413761 = 310321) B310321
theorem B348257 : Blo 243817 348257 := bstep (se 2 (by rfl) ⟨130596, by rfl⟩ : syracuseStep 348257 = 261193) B261193
theorem B413795 : Blo 243817 413795 := bstep (se 1 (by rfl) ⟨310346, by rfl⟩ : syracuseStep 413795 = 620693) B620693
theorem B348337 : Blo 243817 348337 := bstep (se 2 (by rfl) ⟨130626, by rfl⟩ : syracuseStep 348337 = 261253) B261253
theorem B413923 : Blo 243817 413923 := bstep (se 1 (by rfl) ⟨310442, by rfl⟩ : syracuseStep 413923 = 620885) B620885
theorem B414065 : Blo 243817 414065 := bstep (se 2 (by rfl) ⟨155274, by rfl⟩ : syracuseStep 414065 = 310549) B310549
theorem B1331633 : Blo 243817 1331633 := bstep (se 2 (by rfl) ⟨499362, by rfl⟩ : syracuseStep 1331633 = 998725) B998725
theorem B414193 : Blo 243817 414193 := bstep (se 2 (by rfl) ⟨155322, by rfl⟩ : syracuseStep 414193 = 310645) B310645
theorem B414227 : Blo 243817 414227 := bstep (se 1 (by rfl) ⟨310670, by rfl⟩ : syracuseStep 414227 = 621341) B621341
theorem B938573 : Blo 243817 938573 := bstep (se 3 (by rfl) ⟨175982, by rfl⟩ : syracuseStep 938573 = 351965) B351965
theorem B414355 : Blo 243817 414355 := bstep (se 1 (by rfl) ⟨310766, by rfl⟩ : syracuseStep 414355 = 621533) B621533
theorem B316147 : Blo 243817 316147 := bstep (se 1 (by rfl) ⟨237110, by rfl⟩ : syracuseStep 316147 = 474221) B474221
theorem B414497 : Blo 243817 414497 := bstep (se 2 (by rfl) ⟨155436, by rfl⟩ : syracuseStep 414497 = 310873) B310873
theorem B414625 : Blo 243817 414625 := bstep (se 2 (by rfl) ⟨155484, by rfl⟩ : syracuseStep 414625 = 310969) B310969
theorem B349123 : Blo 243817 349123 := bstep (se 1 (by rfl) ⟨261842, by rfl⟩ : syracuseStep 349123 = 523685) B523685
theorem B414659 : Blo 243817 414659 := bstep (se 1 (by rfl) ⟨310994, by rfl⟩ : syracuseStep 414659 = 621989) B621989
theorem B414787 : Blo 243817 414787 := bstep (se 1 (by rfl) ⟨311090, by rfl⟩ : syracuseStep 414787 = 622181) B622181
theorem B1496141 : Blo 243817 1496141 := bstep (se 3 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 1496141 = 561053) B561053
theorem B414929 : Blo 243817 414929 := bstep (se 2 (by rfl) ⟨155598, by rfl⟩ : syracuseStep 414929 = 311197) B311197
theorem B939235 : Blo 243817 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B415057 : Blo 243817 415057 := bstep (se 2 (by rfl) ⟨155646, by rfl⟩ : syracuseStep 415057 = 311293) B311293
theorem B939377 : Blo 243817 939377 := bstep (se 2 (by rfl) ⟨352266, by rfl⟩ : syracuseStep 939377 = 704533) B704533
theorem B415091 : Blo 243817 415091 := bstep (se 1 (by rfl) ⟨311318, by rfl⟩ : syracuseStep 415091 = 622637) B622637
theorem B349601 : Blo 243817 349601 := bstep (se 2 (by rfl) ⟨131100, by rfl⟩ : syracuseStep 349601 = 262201) B262201
theorem B415219 : Blo 243817 415219 := bstep (se 1 (by rfl) ⟨311414, by rfl⟩ : syracuseStep 415219 = 622829) B622829
theorem B349715 : Blo 243817 349715 := bstep (se 1 (by rfl) ⟨262286, by rfl⟩ : syracuseStep 349715 = 524573) B524573
theorem B316963 : Blo 243817 316963 := bstep (se 1 (by rfl) ⟨237722, by rfl⟩ : syracuseStep 316963 = 475445) B475445
theorem B349795 : Blo 243817 349795 := bstep (se 1 (by rfl) ⟨262346, by rfl⟩ : syracuseStep 349795 = 524693) B524693
theorem B415361 : Blo 243817 415361 := bstep (se 2 (by rfl) ⟨155760, by rfl⟩ : syracuseStep 415361 = 311521) B311521
theorem B415489 : Blo 243817 415489 := bstep (se 2 (by rfl) ⟨155808, by rfl⟩ : syracuseStep 415489 = 311617) B311617
theorem B415523 : Blo 243817 415523 := bstep (se 1 (by rfl) ⟨311642, by rfl⟩ : syracuseStep 415523 = 623285) B623285
theorem B415651 : Blo 243817 415651 := bstep (se 1 (by rfl) ⟨311738, by rfl⟩ : syracuseStep 415651 = 623477) B623477
theorem B940045 : Blo 243817 940045 := bstep (se 3 (by rfl) ⟨176258, by rfl⟩ : syracuseStep 940045 = 352517) B352517
theorem B415793 : Blo 243817 415793 := bstep (se 2 (by rfl) ⟨155922, by rfl⟩ : syracuseStep 415793 = 311845) B311845
theorem B350353 : Blo 243817 350353 := bstep (se 2 (by rfl) ⟨131382, by rfl⟩ : syracuseStep 350353 = 262765) B262765
theorem B415921 : Blo 243817 415921 := bstep (se 2 (by rfl) ⟨155970, by rfl⟩ : syracuseStep 415921 = 311941) B311941
theorem B415955 : Blo 243817 415955 := bstep (se 1 (by rfl) ⟨311966, by rfl⟩ : syracuseStep 415955 = 623933) B623933
theorem B1235249 : Blo 243817 1235249 := bstep (se 2 (by rfl) ⟨463218, by rfl⟩ : syracuseStep 1235249 = 926437) B926437
theorem B416083 : Blo 243817 416083 := bstep (se 1 (by rfl) ⟨312062, by rfl⟩ : syracuseStep 416083 = 624125) B624125
theorem B678289 : Blo 243817 678289 := bstep (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) B508717
theorem B416225 : Blo 243817 416225 := bstep (se 2 (by rfl) ⟨156084, by rfl⟩ : syracuseStep 416225 = 312169) B312169
theorem B416353 : Blo 243817 416353 := bstep (se 2 (by rfl) ⟨156132, by rfl⟩ : syracuseStep 416353 = 312265) B312265
theorem B416387 : Blo 243817 416387 := bstep (se 1 (by rfl) ⟨312290, by rfl⟩ : syracuseStep 416387 = 624581) B624581
theorem B8575715 : Blo 243817 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B416515 : Blo 243817 416515 := bstep (se 1 (by rfl) ⟨312386, by rfl⟩ : syracuseStep 416515 = 624773) B624773
theorem B940835 : Blo 243817 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B351059 : Blo 243817 351059 := bstep (se 1 (by rfl) ⟨263294, by rfl⟩ : syracuseStep 351059 = 526589) B526589
theorem B416657 : Blo 243817 416657 := bstep (se 2 (by rfl) ⟨156246, by rfl⟩ : syracuseStep 416657 = 312493) B312493
theorem B1563569 : Blo 243817 1563569 := bstep (se 2 (by rfl) ⟨586338, by rfl⟩ : syracuseStep 1563569 = 1172677) B1172677
theorem B416785 : Blo 243817 416785 := bstep (se 2 (by rfl) ⟨156294, by rfl⟩ : syracuseStep 416785 = 312589) B312589
theorem B416819 : Blo 243817 416819 := bstep (se 1 (by rfl) ⟨312614, by rfl⟩ : syracuseStep 416819 = 625229) B625229
theorem B416947 : Blo 243817 416947 := bstep (se 1 (by rfl) ⟨312710, by rfl⟩ : syracuseStep 416947 = 625421) B625421
theorem B1072397 : Blo 243817 1072397 := bstep (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) B402149
theorem B417089 : Blo 243817 417089 := bstep (se 2 (by rfl) ⟨156408, by rfl⟩ : syracuseStep 417089 = 312817) B312817
theorem B1007011 : Blo 243817 1007011 := bstep (se 1 (by rfl) ⟨755258, by rfl⟩ : syracuseStep 1007011 = 1510517) B1510517
theorem B417217 : Blo 243817 417217 := bstep (se 2 (by rfl) ⟨156456, by rfl⟩ : syracuseStep 417217 = 312913) B312913
theorem B351697 : Blo 243817 351697 := bstep (se 2 (by rfl) ⟨131886, by rfl⟩ : syracuseStep 351697 = 263773) B263773
theorem B417251 : Blo 243817 417251 := bstep (se 1 (by rfl) ⟨312938, by rfl⟩ : syracuseStep 417251 = 625877) B625877
theorem B351811 : Blo 243817 351811 := bstep (se 1 (by rfl) ⟨263858, by rfl⟩ : syracuseStep 351811 = 527717) B527717
theorem B417379 : Blo 243817 417379 := bstep (se 1 (by rfl) ⟨313034, by rfl⟩ : syracuseStep 417379 = 626069) B626069
theorem B1236707 : Blo 243817 1236707 := bstep (se 1 (by rfl) ⟨927530, by rfl⟩ : syracuseStep 1236707 = 1855061) B1855061
theorem B417521 : Blo 243817 417521 := bstep (se 2 (by rfl) ⟨156570, by rfl⟩ : syracuseStep 417521 = 313141) B313141
theorem B548657 : Blo 243817 548657 := bstep (se 2 (by rfl) ⟨205746, by rfl⟩ : syracuseStep 548657 = 411493) B411493
theorem B548675 : Blo 243817 548675 := bstep (se 1 (by rfl) ⟨411506, by rfl⟩ : syracuseStep 548675 = 823013) B823013
theorem B417649 : Blo 243817 417649 := bstep (se 2 (by rfl) ⟨156618, by rfl⟩ : syracuseStep 417649 = 313237) B313237
theorem B417683 : Blo 243817 417683 := bstep (se 1 (by rfl) ⟨313262, by rfl⟩ : syracuseStep 417683 = 626525) B626525
theorem B1400773 : Blo 243817 1400773 := bstep (se 4 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 1400773 = 262645) B262645
theorem B417811 : Blo 243817 417811 := bstep (se 1 (by rfl) ⟨313358, by rfl⟩ : syracuseStep 417811 = 626717) B626717
theorem B548945 : Blo 243817 548945 := bstep (se 2 (by rfl) ⟨205854, by rfl⟩ : syracuseStep 548945 = 411709) B411709
theorem B548963 : Blo 243817 548963 := bstep (se 1 (by rfl) ⟨411722, by rfl⟩ : syracuseStep 548963 = 823445) B823445
theorem B417953 : Blo 243817 417953 := bstep (se 2 (by rfl) ⟨156732, by rfl⟩ : syracuseStep 417953 = 313465) B313465
theorem B418019 : Blo 243817 418019 := bstep (se 1 (by rfl) ⟨313514, by rfl⟩ : syracuseStep 418019 = 627029) B627029
theorem B1335523 : Blo 243817 1335523 := bstep (se 1 (by rfl) ⟨1001642, by rfl⟩ : syracuseStep 1335523 = 2003285) B2003285
theorem B418081 : Blo 243817 418081 := bstep (se 2 (by rfl) ⟨156780, by rfl⟩ : syracuseStep 418081 = 313561) B313561
theorem B418115 : Blo 243817 418115 := bstep (se 1 (by rfl) ⟨313586, by rfl⟩ : syracuseStep 418115 = 627173) B627173
theorem B549233 : Blo 243817 549233 := bstep (se 2 (by rfl) ⟨205962, by rfl⟩ : syracuseStep 549233 = 411925) B411925
theorem B549251 : Blo 243817 549251 := bstep (se 1 (by rfl) ⟨411938, by rfl⟩ : syracuseStep 549251 = 823877) B823877
theorem B2974133 : Blo 243817 2974133 := bstep (se 5 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 2974133 = 278825) B278825
theorem B1237517 : Blo 243817 1237517 := bstep (se 3 (by rfl) ⟨232034, by rfl⟩ : syracuseStep 1237517 = 464069) B464069
theorem B549521 : Blo 243817 549521 := bstep (se 2 (by rfl) ⟨206070, by rfl⟩ : syracuseStep 549521 = 412141) B412141
theorem B549539 : Blo 243817 549539 := bstep (se 1 (by rfl) ⟨412154, by rfl⟩ : syracuseStep 549539 = 824309) B824309
theorem B1499917 : Blo 243817 1499917 := bstep (se 3 (by rfl) ⟨281234, by rfl⟩ : syracuseStep 1499917 = 562469) B562469
theorem B549809 : Blo 243817 549809 := bstep (se 2 (by rfl) ⟨206178, by rfl⟩ : syracuseStep 549809 = 412357) B412357
theorem B746417 : Blo 243817 746417 := bstep (se 2 (by rfl) ⟨279906, by rfl⟩ : syracuseStep 746417 = 559813) B559813
theorem B549827 : Blo 243817 549827 := bstep (se 1 (by rfl) ⟨412370, by rfl⟩ : syracuseStep 549827 = 824741) B824741
theorem B8119237 : Blo 243817 8119237 := bstep (se 4 (by rfl) ⟨761178, by rfl⟩ : syracuseStep 8119237 = 1522357) B1522357
theorem B550097 : Blo 243817 550097 := bstep (se 2 (by rfl) ⟨206286, by rfl⟩ : syracuseStep 550097 = 412573) B412573
theorem B550115 : Blo 243817 550115 := bstep (se 1 (by rfl) ⟨412586, by rfl⟩ : syracuseStep 550115 = 825173) B825173
theorem B2090225 : Blo 243817 2090225 := bstep (se 2 (by rfl) ⟨783834, by rfl⟩ : syracuseStep 2090225 = 1567669) B1567669
theorem B2647349 : Blo 243817 2647349 := bstep (se 5 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 2647349 = 248189) B248189
theorem B1566029 : Blo 243817 1566029 := bstep (se 3 (by rfl) ⟨293630, by rfl⟩ : syracuseStep 1566029 = 587261) B587261
theorem B550385 : Blo 243817 550385 := bstep (se 2 (by rfl) ⟨206394, by rfl⟩ : syracuseStep 550385 = 412789) B412789
theorem B550403 : Blo 243817 550403 := bstep (se 1 (by rfl) ⟨412802, by rfl⟩ : syracuseStep 550403 = 825605) B825605
theorem B550673 : Blo 243817 550673 := bstep (se 2 (by rfl) ⟨206502, by rfl⟩ : syracuseStep 550673 = 413005) B413005
theorem B550691 : Blo 243817 550691 := bstep (se 1 (by rfl) ⟨413018, by rfl⟩ : syracuseStep 550691 = 826037) B826037
theorem B1402757 : Blo 243817 1402757 := bstep (se 4 (by rfl) ⟨131508, by rfl⟩ : syracuseStep 1402757 = 263017) B263017
theorem B747427 : Blo 243817 747427 := bstep (se 1 (by rfl) ⟨560570, by rfl⟩ : syracuseStep 747427 = 1121141) B1121141
theorem B550961 : Blo 243817 550961 := bstep (se 2 (by rfl) ⟨206610, by rfl⟩ : syracuseStep 550961 = 413221) B413221
theorem B550979 : Blo 243817 550979 := bstep (se 1 (by rfl) ⟨413234, by rfl⟩ : syracuseStep 550979 = 826469) B826469
theorem B714865 : Blo 243817 714865 := bstep (se 2 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 714865 = 536149) B536149
theorem B2353349 : Blo 243817 2353349 := bstep (se 4 (by rfl) ⟨220626, by rfl⟩ : syracuseStep 2353349 = 441253) B441253
theorem B1698083 : Blo 243817 1698083 := bstep (se 1 (by rfl) ⟨1273562, by rfl⟩ : syracuseStep 1698083 = 2547125) B2547125
theorem B551249 : Blo 243817 551249 := bstep (se 2 (by rfl) ⟨206718, by rfl⟩ : syracuseStep 551249 = 413437) B413437
theorem B551267 : Blo 243817 551267 := bstep (se 1 (by rfl) ⟨413450, by rfl⟩ : syracuseStep 551267 = 826901) B826901
theorem B354881 : Blo 243817 354881 := bstep (se 2 (by rfl) ⟨133080, by rfl⟩ : syracuseStep 354881 = 266161) B266161
theorem B748109 : Blo 243817 748109 := bstep (se 3 (by rfl) ⟨140270, by rfl⟩ : syracuseStep 748109 = 280541) B280541
theorem B551537 : Blo 243817 551537 := bstep (se 2 (by rfl) ⟨206826, by rfl⟩ : syracuseStep 551537 = 413653) B413653
theorem B551555 : Blo 243817 551555 := bstep (se 1 (by rfl) ⟨413666, by rfl⟩ : syracuseStep 551555 = 827333) B827333
theorem B748205 : Blo 243817 748205 := bstep (se 3 (by rfl) ⟨140288, by rfl⟩ : syracuseStep 748205 = 280577) B280577
theorem B10775267 : Blo 243817 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B781169 : Blo 243817 781169 := bstep (se 2 (by rfl) ⟨292938, by rfl⟩ : syracuseStep 781169 = 585877) B585877
theorem B551825 : Blo 243817 551825 := bstep (se 2 (by rfl) ⟨206934, by rfl⟩ : syracuseStep 551825 = 413869) B413869
theorem B551843 : Blo 243817 551843 := bstep (se 1 (by rfl) ⟨413882, by rfl⟩ : syracuseStep 551843 = 827765) B827765
theorem B1043405 : Blo 243817 1043405 := bstep (se 3 (by rfl) ⟨195638, by rfl⟩ : syracuseStep 1043405 = 391277) B391277
theorem B355411 : Blo 243817 355411 := bstep (se 1 (by rfl) ⟨266558, by rfl⟩ : syracuseStep 355411 = 533117) B533117
theorem B552113 : Blo 243817 552113 := bstep (se 2 (by rfl) ⟨207042, by rfl⟩ : syracuseStep 552113 = 414085) B414085
theorem B552131 : Blo 243817 552131 := bstep (se 1 (by rfl) ⟨414098, by rfl⟩ : syracuseStep 552131 = 828197) B828197
theorem B617777 : Blo 243817 617777 := bstep (se 2 (by rfl) ⟨231666, by rfl⟩ : syracuseStep 617777 = 463333) B463333
theorem B617827 : Blo 243817 617827 := bstep (se 1 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 617827 = 926741) B926741
theorem B1240433 : Blo 243817 1240433 := bstep (se 2 (by rfl) ⟨465162, by rfl⟩ : syracuseStep 1240433 = 930325) B930325
theorem B552401 : Blo 243817 552401 := bstep (se 2 (by rfl) ⟨207150, by rfl⟩ : syracuseStep 552401 = 414301) B414301
theorem B552419 : Blo 243817 552419 := bstep (se 1 (by rfl) ⟨414314, by rfl⟩ : syracuseStep 552419 = 828629) B828629
theorem B617969 : Blo 243817 617969 := bstep (se 2 (by rfl) ⟨231738, by rfl⟩ : syracuseStep 617969 = 463477) B463477
theorem B1568261 : Blo 243817 1568261 := bstep (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) B294049
theorem B552689 : Blo 243817 552689 := bstep (se 2 (by rfl) ⟨207258, by rfl⟩ : syracuseStep 552689 = 414517) B414517
theorem B552707 : Blo 243817 552707 := bstep (se 1 (by rfl) ⟨414530, by rfl⟩ : syracuseStep 552707 = 829061) B829061
theorem B552977 : Blo 243817 552977 := bstep (se 2 (by rfl) ⟨207366, by rfl⟩ : syracuseStep 552977 = 414733) B414733
theorem B552995 : Blo 243817 552995 := bstep (se 1 (by rfl) ⟨414746, by rfl⟩ : syracuseStep 552995 = 829493) B829493
theorem B1765475 : Blo 243817 1765475 := bstep (se 1 (by rfl) ⟨1324106, by rfl⟩ : syracuseStep 1765475 = 2648213) B2648213
theorem B422131 : Blo 243817 422131 := bstep (se 1 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 422131 = 633197) B633197
theorem B553265 : Blo 243817 553265 := bstep (se 2 (by rfl) ⟨207474, by rfl⟩ : syracuseStep 553265 = 414949) B414949
theorem B553283 : Blo 243817 553283 := bstep (se 1 (by rfl) ⟨414962, by rfl⟩ : syracuseStep 553283 = 829925) B829925
theorem B618961 : Blo 243817 618961 := bstep (se 2 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 618961 = 464221) B464221
theorem B356819 : Blo 243817 356819 := bstep (se 1 (by rfl) ⟨267614, by rfl⟩ : syracuseStep 356819 = 535229) B535229
theorem B553553 : Blo 243817 553553 := bstep (se 2 (by rfl) ⟨207582, by rfl⟩ : syracuseStep 553553 = 415165) B415165
theorem B553571 : Blo 243817 553571 := bstep (se 1 (by rfl) ⟨415178, by rfl⟩ : syracuseStep 553571 = 830357) B830357
theorem B586435 : Blo 243817 586435 := bstep (se 1 (by rfl) ⟨439826, by rfl⟩ : syracuseStep 586435 = 879653) B879653
theorem B619235 : Blo 243817 619235 := bstep (se 1 (by rfl) ⟨464426, by rfl⟩ : syracuseStep 619235 = 928853) B928853
theorem B1241891 : Blo 243817 1241891 := bstep (se 1 (by rfl) ⟨931418, by rfl⟩ : syracuseStep 1241891 = 1862837) B1862837
theorem B553841 : Blo 243817 553841 := bstep (se 2 (by rfl) ⟨207690, by rfl⟩ : syracuseStep 553841 = 415381) B415381
theorem B553859 : Blo 243817 553859 := bstep (se 1 (by rfl) ⟨415394, by rfl⟩ : syracuseStep 553859 = 830789) B830789
theorem B1766285 : Blo 243817 1766285 := bstep (se 3 (by rfl) ⟨331178, by rfl⟩ : syracuseStep 1766285 = 662357) B662357
theorem B619427 : Blo 243817 619427 := bstep (se 1 (by rfl) ⟨464570, by rfl⟩ : syracuseStep 619427 = 929141) B929141
theorem B2290801 : Blo 243817 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B7599217 : Blo 243817 7599217 := bstep (se 2 (by rfl) ⟨2849706, by rfl⟩ : syracuseStep 7599217 = 5699413) B5699413
theorem B554129 : Blo 243817 554129 := bstep (se 2 (by rfl) ⟨207798, by rfl⟩ : syracuseStep 554129 = 415597) B415597
theorem B554147 : Blo 243817 554147 := bstep (se 1 (by rfl) ⟨415610, by rfl⟩ : syracuseStep 554147 = 831221) B831221
theorem B587107 : Blo 243817 587107 := bstep (se 1 (by rfl) ⟨440330, by rfl⟩ : syracuseStep 587107 = 880661) B880661
theorem B554417 : Blo 243817 554417 := bstep (se 2 (by rfl) ⟨207906, by rfl⟩ : syracuseStep 554417 = 415813) B415813
theorem B554435 : Blo 243817 554435 := bstep (se 1 (by rfl) ⟨415826, by rfl⟩ : syracuseStep 554435 = 831653) B831653
theorem B882161 : Blo 243817 882161 := bstep (se 2 (by rfl) ⟨330810, by rfl⟩ : syracuseStep 882161 = 661621) B661621
theorem B1242701 : Blo 243817 1242701 := bstep (se 3 (by rfl) ⟨233006, by rfl⟩ : syracuseStep 1242701 = 466013) B466013
theorem B390739 : Blo 243817 390739 := bstep (se 1 (by rfl) ⟨293054, by rfl⟩ : syracuseStep 390739 = 586109) B586109
theorem B1406605 : Blo 243817 1406605 := bstep (se 3 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 1406605 = 527477) B527477
theorem B390835 : Blo 243817 390835 := bstep (se 1 (by rfl) ⟨293126, by rfl⟩ : syracuseStep 390835 = 586253) B586253
theorem B554705 : Blo 243817 554705 := bstep (se 2 (by rfl) ⟨208014, by rfl⟩ : syracuseStep 554705 = 416029) B416029
theorem B554723 : Blo 243817 554723 := bstep (se 1 (by rfl) ⟨416042, by rfl⟩ : syracuseStep 554723 = 832085) B832085
theorem B587569 : Blo 243817 587569 := bstep (se 2 (by rfl) ⟨220338, by rfl⟩ : syracuseStep 587569 = 440677) B440677
theorem B620369 : Blo 243817 620369 := bstep (se 2 (by rfl) ⟨232638, by rfl⟩ : syracuseStep 620369 = 465277) B465277
theorem B390995 : Blo 243817 390995 := bstep (se 1 (by rfl) ⟨293246, by rfl⟩ : syracuseStep 390995 = 586493) B586493
theorem B620419 : Blo 243817 620419 := bstep (se 1 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 620419 = 930629) B930629
theorem B587665 : Blo 243817 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B554993 : Blo 243817 554993 := bstep (se 2 (by rfl) ⟨208122, by rfl⟩ : syracuseStep 554993 = 416245) B416245
theorem B555011 : Blo 243817 555011 := bstep (se 1 (by rfl) ⟨416258, by rfl⟩ : syracuseStep 555011 = 832517) B832517
theorem B620561 : Blo 243817 620561 := bstep (se 2 (by rfl) ⟨232710, by rfl⟩ : syracuseStep 620561 = 465421) B465421
theorem B784579 : Blo 243817 784579 := bstep (se 1 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 784579 = 1176869) B1176869
theorem B3373325 : Blo 243817 3373325 := bstep (se 3 (by rfl) ⟨632498, by rfl⟩ : syracuseStep 3373325 = 1264997) B1264997
theorem B555281 : Blo 243817 555281 := bstep (se 2 (by rfl) ⟨208230, by rfl⟩ : syracuseStep 555281 = 416461) B416461
theorem B555299 : Blo 243817 555299 := bstep (se 1 (by rfl) ⟨416474, by rfl⟩ : syracuseStep 555299 = 832949) B832949
theorem B522659 : Blo 243817 522659 := bstep (se 1 (by rfl) ⟨391994, by rfl⟩ : syracuseStep 522659 = 783989) B783989
theorem B784849 : Blo 243817 784849 := bstep (se 2 (by rfl) ⟨294318, by rfl⟩ : syracuseStep 784849 = 588637) B588637
theorem B555569 : Blo 243817 555569 := bstep (se 2 (by rfl) ⟨208338, by rfl⟩ : syracuseStep 555569 = 416677) B416677
theorem B555587 : Blo 243817 555587 := bstep (se 1 (by rfl) ⟨416690, by rfl⟩ : syracuseStep 555587 = 833381) B833381
theorem B916145 : Blo 243817 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B391969 : Blo 243817 391969 := bstep (se 2 (by rfl) ⟨146988, by rfl⟩ : syracuseStep 391969 = 293977) B293977
theorem B555857 : Blo 243817 555857 := bstep (se 2 (by rfl) ⟨208446, by rfl⟩ : syracuseStep 555857 = 416893) B416893
theorem B555875 : Blo 243817 555875 := bstep (se 1 (by rfl) ⟨416906, by rfl⟩ : syracuseStep 555875 = 833813) B833813
theorem B1047437 : Blo 243817 1047437 := bstep (se 3 (by rfl) ⟨196394, by rfl⟩ : syracuseStep 1047437 = 392789) B392789
theorem B621553 : Blo 243817 621553 := bstep (se 2 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 621553 = 466165) B466165
theorem B556145 : Blo 243817 556145 := bstep (se 2 (by rfl) ⟨208554, by rfl⟩ : syracuseStep 556145 = 417109) B417109
theorem B556163 : Blo 243817 556163 := bstep (se 1 (by rfl) ⟨417122, by rfl⟩ : syracuseStep 556163 = 834245) B834245
theorem B1047779 : Blo 243817 1047779 := bstep (se 1 (by rfl) ⟨785834, by rfl⟩ : syracuseStep 1047779 = 1571669) B1571669
theorem B621827 : Blo 243817 621827 := bstep (se 1 (by rfl) ⟨466370, by rfl⟩ : syracuseStep 621827 = 932741) B932741
theorem B359699 : Blo 243817 359699 := bstep (se 1 (by rfl) ⟨269774, by rfl⟩ : syracuseStep 359699 = 539549) B539549
theorem B556433 : Blo 243817 556433 := bstep (se 2 (by rfl) ⟨208662, by rfl⟩ : syracuseStep 556433 = 417325) B417325
theorem B556451 : Blo 243817 556451 := bstep (se 1 (by rfl) ⟨417338, by rfl⟩ : syracuseStep 556451 = 834677) B834677
theorem B622019 : Blo 243817 622019 := bstep (se 1 (by rfl) ⟨466514, by rfl⟩ : syracuseStep 622019 = 933029) B933029
theorem B1408589 : Blo 243817 1408589 := bstep (se 3 (by rfl) ⟨264110, by rfl⟩ : syracuseStep 1408589 = 528221) B528221
theorem B1048241 : Blo 243817 1048241 := bstep (se 2 (by rfl) ⟨393090, by rfl⟩ : syracuseStep 1048241 = 786181) B786181
theorem B556721 : Blo 243817 556721 := bstep (se 2 (by rfl) ⟨208770, by rfl⟩ : syracuseStep 556721 = 417541) B417541
theorem B556739 : Blo 243817 556739 := bstep (se 1 (by rfl) ⟨417554, by rfl⟩ : syracuseStep 556739 = 835109) B835109
theorem B294611 : Blo 243817 294611 := bstep (se 1 (by rfl) ⟨220958, by rfl⟩ : syracuseStep 294611 = 441917) B441917
theorem B557009 : Blo 243817 557009 := bstep (se 2 (by rfl) ⟨208878, by rfl⟩ : syracuseStep 557009 = 417757) B417757
theorem B557027 : Blo 243817 557027 := bstep (se 1 (by rfl) ⟨417770, by rfl⟩ : syracuseStep 557027 = 835541) B835541
theorem B557081 : Blo 243817 557081 := bstep (se 2 (by rfl) ⟨208905, by rfl⟩ : syracuseStep 557081 = 417811) B417811
theorem B2097197 : Blo 243817 2097197 := bstep (se 3 (by rfl) ⟨393224, by rfl⟩ : syracuseStep 2097197 = 786449) B786449
theorem B622667 : Blo 243817 622667 := bstep (se 1 (by rfl) ⟨467000, by rfl⟩ : syracuseStep 622667 = 934001) B934001
theorem B557171 : Blo 243817 557171 := bstep (se 1 (by rfl) ⟨417878, by rfl⟩ : syracuseStep 557171 = 835757) B835757
theorem B557207 : Blo 243817 557207 := bstep (se 1 (by rfl) ⟨417905, by rfl⟩ : syracuseStep 557207 = 835811) B835811
theorem B524531 : Blo 243817 524531 := bstep (se 1 (by rfl) ⟨393398, by rfl⟩ : syracuseStep 524531 = 786797) B786797
theorem B262423 : Blo 243817 262423 := bstep (se 1 (by rfl) ⟨196817, by rfl⟩ : syracuseStep 262423 = 393635) B393635
theorem B557387 : Blo 243817 557387 := bstep (se 1 (by rfl) ⟨418040, by rfl⟩ : syracuseStep 557387 = 836081) B836081
theorem B557441 : Blo 243817 557441 := bstep (se 2 (by rfl) ⟨209040, by rfl⟩ : syracuseStep 557441 = 418081) B418081
theorem B1868183 : Blo 243817 1868183 := bstep (se 1 (by rfl) ⟨1401137, by rfl⟩ : syracuseStep 1868183 = 2802275) B2802275
theorem B557579 : Blo 243817 557579 := bstep (se 1 (by rfl) ⟨418184, by rfl⟩ : syracuseStep 557579 = 836369) B836369
theorem B1114717 : Blo 243817 1114717 := bstep (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) B418019
theorem B525017 : Blo 243817 525017 := bstep (se 2 (by rfl) ⟨196881, by rfl⟩ : syracuseStep 525017 = 393763) B393763
theorem B1114955 : Blo 243817 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B1246103 : Blo 243817 1246103 := bstep (se 1 (by rfl) ⟨934577, by rfl⟩ : syracuseStep 1246103 = 1869155) B1869155
theorem B885725 : Blo 243817 885725 := bstep (se 3 (by rfl) ⟨166073, by rfl⟩ : syracuseStep 885725 = 332147) B332147
theorem B1999889 : Blo 243817 1999889 := bstep (se 2 (by rfl) ⟨749958, by rfl⟩ : syracuseStep 1999889 = 1499917) B1499917
theorem B623639 : Blo 243817 623639 := bstep (se 1 (by rfl) ⟨467729, by rfl⟩ : syracuseStep 623639 = 935459) B935459
theorem B951517 : Blo 243817 951517 := bstep (se 3 (by rfl) ⟨178409, by rfl⟩ : syracuseStep 951517 = 356819) B356819
theorem B525761 : Blo 243817 525761 := bstep (se 2 (by rfl) ⟨197160, by rfl⟩ : syracuseStep 525761 = 394321) B394321
theorem B1050205 : Blo 243817 1050205 := bstep (se 3 (by rfl) ⟨196913, by rfl⟩ : syracuseStep 1050205 = 393827) B393827
theorem B624307 : Blo 243817 624307 := bstep (se 1 (by rfl) ⟨468230, by rfl⟩ : syracuseStep 624307 = 936461) B936461
theorem B362263 : Blo 243817 362263 := bstep (se 1 (by rfl) ⟨271697, by rfl⟩ : syracuseStep 362263 = 543395) B543395
theorem B624449 : Blo 243817 624449 := bstep (se 2 (by rfl) ⟨234168, by rfl⟩ : syracuseStep 624449 = 468337) B468337
theorem B296779 : Blo 243817 296779 := bstep (se 1 (by rfl) ⟨222584, by rfl⟩ : syracuseStep 296779 = 445169) B445169
theorem B264055 : Blo 243817 264055 := bstep (se 1 (by rfl) ⟨198041, by rfl⟩ : syracuseStep 264055 = 396083) B396083
theorem B329611 : Blo 243817 329611 := bstep (se 1 (by rfl) ⟨247208, by rfl⟩ : syracuseStep 329611 = 494417) B494417
theorem B395147 : Blo 243817 395147 := bstep (se 1 (by rfl) ⟨296360, by rfl⟩ : syracuseStep 395147 = 592721) B592721
theorem B395275 : Blo 243817 395275 := bstep (se 1 (by rfl) ⟨296456, by rfl⟩ : syracuseStep 395275 = 592913) B592913
theorem B3967127 : Blo 243817 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B395417 : Blo 243817 395417 := bstep (se 2 (by rfl) ⟨148281, by rfl⟩ : syracuseStep 395417 = 296563) B296563
theorem B1575233 : Blo 243817 1575233 := bstep (se 2 (by rfl) ⟨590712, by rfl⟩ : syracuseStep 1575233 = 1181425) B1181425
theorem B526657 : Blo 243817 526657 := bstep (se 2 (by rfl) ⟨197496, by rfl⟩ : syracuseStep 526657 = 394993) B394993
theorem B559703 : Blo 243817 559703 := bstep (se 1 (by rfl) ⟨419777, by rfl⟩ : syracuseStep 559703 = 839555) B839555
theorem B526999 : Blo 243817 526999 := bstep (se 1 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 526999 = 790499) B790499
theorem B953153 : Blo 243817 953153 := bstep (se 2 (by rfl) ⟨357432, by rfl⟩ : syracuseStep 953153 = 714865) B714865
theorem B1051537 : Blo 243817 1051537 := bstep (se 2 (by rfl) ⟨394326, by rfl⟩ : syracuseStep 1051537 = 788653) B788653
theorem B887755 : Blo 243817 887755 := bstep (se 1 (by rfl) ⟨665816, by rfl⟩ : syracuseStep 887755 = 1331633) B1331633
theorem B625715 : Blo 243817 625715 := bstep (se 1 (by rfl) ⟨469286, by rfl⟩ : syracuseStep 625715 = 938573) B938573
theorem B265303 : Blo 243817 265303 := bstep (se 1 (by rfl) ⟨198977, by rfl⟩ : syracuseStep 265303 = 397955) B397955
theorem B527563 : Blo 243817 527563 := bstep (se 1 (by rfl) ⟨395672, by rfl⟩ : syracuseStep 527563 = 791345) B791345
theorem B396505 : Blo 243817 396505 := bstep (se 2 (by rfl) ⟨148689, by rfl⟩ : syracuseStep 396505 = 297379) B297379
theorem B626251 : Blo 243817 626251 := bstep (se 1 (by rfl) ⟨469688, by rfl⟩ : syracuseStep 626251 = 939377) B939377
theorem B2100887 : Blo 243817 2100887 := bstep (se 1 (by rfl) ⟨1575665, by rfl⟩ : syracuseStep 2100887 = 3151331) B3151331
theorem B626393 : Blo 243817 626393 := bstep (se 2 (by rfl) ⟨234897, by rfl⟩ : syracuseStep 626393 = 469795) B469795
theorem B364441 : Blo 243817 364441 := bstep (se 2 (by rfl) ⟨136665, by rfl⟩ : syracuseStep 364441 = 273331) B273331
theorem B1118225 : Blo 243817 1118225 := bstep (se 2 (by rfl) ⟨419334, by rfl⟩ : syracuseStep 1118225 = 838669) B838669
theorem B5279813 : Blo 243817 5279813 := bstep (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) B989965
theorem B823499 : Blo 243817 823499 := bstep (se 1 (by rfl) ⟨617624, by rfl⟩ : syracuseStep 823499 = 1235249) B1235249
theorem B1249667 : Blo 243817 1249667 := bstep (se 1 (by rfl) ⟨937250, by rfl⟩ : syracuseStep 1249667 = 1874501) B1874501
theorem B823769 : Blo 243817 823769 := bstep (se 2 (by rfl) ⟨308913, by rfl⟩ : syracuseStep 823769 = 617827) B617827
theorem B627223 : Blo 243817 627223 := bstep (se 1 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 627223 = 940835) B940835
theorem B528947 : Blo 243817 528947 := bstep (se 1 (by rfl) ⟨396710, by rfl⟩ : syracuseStep 528947 = 793421) B793421
theorem B332363 : Blo 243817 332363 := bstep (se 1 (by rfl) ⟨249272, by rfl⟩ : syracuseStep 332363 = 498545) B498545
theorem B529049 : Blo 243817 529049 := bstep (se 2 (by rfl) ⟨198393, by rfl⟩ : syracuseStep 529049 = 396787) B396787
theorem B463553 : Blo 243817 463553 := bstep (se 2 (by rfl) ⟨173832, by rfl⟩ : syracuseStep 463553 = 347665) B347665
theorem B1184557 : Blo 243817 1184557 := bstep (se 3 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 1184557 = 444209) B444209
theorem B594739 : Blo 243817 594739 := bstep (se 1 (by rfl) ⟨446054, by rfl⟩ : syracuseStep 594739 = 892109) B892109
theorem B463819 : Blo 243817 463819 := bstep (se 1 (by rfl) ⟨347864, by rfl⟩ : syracuseStep 463819 = 695729) B695729
theorem B595019 : Blo 243817 595019 := bstep (se 1 (by rfl) ⟨446264, by rfl⟩ : syracuseStep 595019 = 892529) B892529
theorem B824471 : Blo 243817 824471 := bstep (se 1 (by rfl) ⟨618353, by rfl⟩ : syracuseStep 824471 = 1236707) B1236707
theorem B365771 : Blo 243817 365771 := bstep (se 1 (by rfl) ⟨274328, by rfl⟩ : syracuseStep 365771 = 548657) B548657
theorem B365783 : Blo 243817 365783 := bstep (se 1 (by rfl) ⟨274337, by rfl⟩ : syracuseStep 365783 = 548675) B548675
theorem B791831 : Blo 243817 791831 := bstep (se 1 (by rfl) ⟨593873, by rfl⟩ : syracuseStep 791831 = 1187747) B1187747
theorem B365849 : Blo 243817 365849 := bstep (se 2 (by rfl) ⟨137193, by rfl⟩ : syracuseStep 365849 = 274387) B274387
theorem B365963 : Blo 243817 365963 := bstep (se 1 (by rfl) ⟨274472, by rfl⟩ : syracuseStep 365963 = 548945) B548945
theorem B464267 : Blo 243817 464267 := bstep (se 1 (by rfl) ⟨348200, by rfl⟩ : syracuseStep 464267 = 696401) B696401
theorem B365975 : Blo 243817 365975 := bstep (se 1 (by rfl) ⟨274481, by rfl⟩ : syracuseStep 365975 = 548963) B548963
theorem B366041 : Blo 243817 366041 := bstep (se 2 (by rfl) ⟨137265, by rfl⟩ : syracuseStep 366041 = 274531) B274531
theorem B464449 : Blo 243817 464449 := bstep (se 2 (by rfl) ⟨174168, by rfl⟩ : syracuseStep 464449 = 348337) B348337
theorem B366155 : Blo 243817 366155 := bstep (se 1 (by rfl) ⟨274616, by rfl⟩ : syracuseStep 366155 = 549233) B549233
theorem B792139 : Blo 243817 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B366167 : Blo 243817 366167 := bstep (se 1 (by rfl) ⟨274625, by rfl⟩ : syracuseStep 366167 = 549251) B549251
theorem B366233 : Blo 243817 366233 := bstep (se 2 (by rfl) ⟨137337, by rfl⟩ : syracuseStep 366233 = 274675) B274675
theorem B562841 : Blo 243817 562841 := bstep (se 2 (by rfl) ⟨211065, by rfl⟩ : syracuseStep 562841 = 422131) B422131
theorem B825011 : Blo 243817 825011 := bstep (se 1 (by rfl) ⟨618758, by rfl⟩ : syracuseStep 825011 = 1237517) B1237517
theorem B366347 : Blo 243817 366347 := bstep (se 1 (by rfl) ⟨274760, by rfl⟩ : syracuseStep 366347 = 549521) B549521
theorem B366359 : Blo 243817 366359 := bstep (se 1 (by rfl) ⟨274769, by rfl⟩ : syracuseStep 366359 = 549539) B549539
theorem B1054529 : Blo 243817 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B366425 : Blo 243817 366425 := bstep (se 2 (by rfl) ⟨137409, by rfl⟩ : syracuseStep 366425 = 274819) B274819
theorem B464791 : Blo 243817 464791 := bstep (se 1 (by rfl) ⟨348593, by rfl⟩ : syracuseStep 464791 = 697187) B697187
theorem B825281 : Blo 243817 825281 := bstep (se 2 (by rfl) ⟨309480, by rfl⟩ : syracuseStep 825281 = 618961) B618961
theorem B366539 : Blo 243817 366539 := bstep (se 1 (by rfl) ⟨274904, by rfl⟩ : syracuseStep 366539 = 549809) B549809
theorem B497611 : Blo 243817 497611 := bstep (se 1 (by rfl) ⟨373208, by rfl⟩ : syracuseStep 497611 = 746417) B746417
theorem B366551 : Blo 243817 366551 := bstep (se 1 (by rfl) ⟨274913, by rfl⟩ : syracuseStep 366551 = 549827) B549827
theorem B366617 : Blo 243817 366617 := bstep (se 2 (by rfl) ⟨137481, by rfl⟩ : syracuseStep 366617 = 274963) B274963
theorem B465011 : Blo 243817 465011 := bstep (se 1 (by rfl) ⟨348758, by rfl⟩ : syracuseStep 465011 = 697517) B697517
theorem B366731 : Blo 243817 366731 := bstep (se 1 (by rfl) ⟨275048, by rfl⟩ : syracuseStep 366731 = 550097) B550097
theorem B366743 : Blo 243817 366743 := bstep (se 1 (by rfl) ⟨275057, by rfl⟩ : syracuseStep 366743 = 550115) B550115
theorem B366809 : Blo 243817 366809 := bstep (se 2 (by rfl) ⟨137553, by rfl⟩ : syracuseStep 366809 = 275107) B275107
theorem B891101 : Blo 243817 891101 := bstep (se 3 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 891101 = 334163) B334163
theorem B366923 : Blo 243817 366923 := bstep (se 1 (by rfl) ⟨275192, by rfl⟩ : syracuseStep 366923 = 550385) B550385
theorem B366935 : Blo 243817 366935 := bstep (se 1 (by rfl) ⟨275201, by rfl⟩ : syracuseStep 366935 = 550403) B550403
theorem B465239 : Blo 243817 465239 := bstep (se 1 (by rfl) ⟨348929, by rfl⟩ : syracuseStep 465239 = 697859) B697859
theorem B367001 : Blo 243817 367001 := bstep (se 2 (by rfl) ⟨137625, by rfl⟩ : syracuseStep 367001 = 275251) B275251
theorem B825821 : Blo 243817 825821 := bstep (se 3 (by rfl) ⟨154841, by rfl⟩ : syracuseStep 825821 = 309683) B309683
theorem B367115 : Blo 243817 367115 := bstep (se 1 (by rfl) ⟨275336, by rfl⟩ : syracuseStep 367115 = 550673) B550673
theorem B367127 : Blo 243817 367127 := bstep (se 1 (by rfl) ⟨275345, by rfl⟩ : syracuseStep 367127 = 550691) B550691
theorem B367193 : Blo 243817 367193 := bstep (se 2 (by rfl) ⟨137697, by rfl⟩ : syracuseStep 367193 = 275395) B275395
theorem B465497 : Blo 243817 465497 := bstep (se 2 (by rfl) ⟨174561, by rfl⟩ : syracuseStep 465497 = 349123) B349123
theorem B367307 : Blo 243817 367307 := bstep (se 1 (by rfl) ⟨275480, by rfl⟩ : syracuseStep 367307 = 550961) B550961
theorem B367319 : Blo 243817 367319 := bstep (se 1 (by rfl) ⟨275489, by rfl⟩ : syracuseStep 367319 = 550979) B550979
theorem B367385 : Blo 243817 367385 := bstep (se 2 (by rfl) ⟨137769, by rfl⟩ : syracuseStep 367385 = 275539) B275539
theorem B3054401 : Blo 243817 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B10132289 : Blo 243817 10132289 := bstep (se 2 (by rfl) ⟨3799608, by rfl⟩ : syracuseStep 10132289 = 7599217) B7599217
theorem B367499 : Blo 243817 367499 := bstep (se 1 (by rfl) ⟨275624, by rfl⟩ : syracuseStep 367499 = 551249) B551249
theorem B367511 : Blo 243817 367511 := bstep (se 1 (by rfl) ⟨275633, by rfl⟩ : syracuseStep 367511 = 551267) B551267
theorem B1252313 : Blo 243817 1252313 := bstep (se 2 (by rfl) ⟨469617, by rfl⟩ : syracuseStep 1252313 = 939235) B939235
theorem B367577 : Blo 243817 367577 := bstep (se 2 (by rfl) ⟨137841, by rfl⟩ : syracuseStep 367577 = 275683) B275683
theorem B465907 : Blo 243817 465907 := bstep (se 1 (by rfl) ⟨349430, by rfl⟩ : syracuseStep 465907 = 698861) B698861
theorem B498739 : Blo 243817 498739 := bstep (se 1 (by rfl) ⟨374054, by rfl⟩ : syracuseStep 498739 = 748109) B748109
theorem B367691 : Blo 243817 367691 := bstep (se 1 (by rfl) ⟨275768, by rfl⟩ : syracuseStep 367691 = 551537) B551537
theorem B367703 : Blo 243817 367703 := bstep (se 1 (by rfl) ⟨275777, by rfl⟩ : syracuseStep 367703 = 551555) B551555
theorem B498803 : Blo 243817 498803 := bstep (se 1 (by rfl) ⟨374102, by rfl⟩ : syracuseStep 498803 = 748205) B748205
theorem B7183511 : Blo 243817 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B367769 : Blo 243817 367769 := bstep (se 2 (by rfl) ⟨137913, by rfl⟩ : syracuseStep 367769 = 275827) B275827
theorem B367883 : Blo 243817 367883 := bstep (se 1 (by rfl) ⟨275912, by rfl⟩ : syracuseStep 367883 = 551825) B551825
theorem B367895 : Blo 243817 367895 := bstep (se 1 (by rfl) ⟨275921, by rfl⟩ : syracuseStep 367895 = 551843) B551843
theorem B695603 : Blo 243817 695603 := bstep (se 1 (by rfl) ⟨521702, by rfl⟩ : syracuseStep 695603 = 1043405) B1043405
theorem B367961 : Blo 243817 367961 := bstep (se 2 (by rfl) ⟨137985, by rfl⟩ : syracuseStep 367961 = 275971) B275971
theorem B1580381 : Blo 243817 1580381 := bstep (se 3 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 1580381 = 592643) B592643
theorem B368075 : Blo 243817 368075 := bstep (se 1 (by rfl) ⟨276056, by rfl⟩ : syracuseStep 368075 = 552113) B552113
theorem B368087 : Blo 243817 368087 := bstep (se 1 (by rfl) ⟨276065, by rfl⟩ : syracuseStep 368087 = 552131) B552131
theorem B466393 : Blo 243817 466393 := bstep (se 2 (by rfl) ⟨174897, by rfl⟩ : syracuseStep 466393 = 349795) B349795
theorem B663005 : Blo 243817 663005 := bstep (se 3 (by rfl) ⟨124313, by rfl⟩ : syracuseStep 663005 = 248627) B248627
theorem B1875473 : Blo 243817 1875473 := bstep (se 2 (by rfl) ⟨703302, by rfl⟩ : syracuseStep 1875473 = 1406605) B1406605
theorem B368153 : Blo 243817 368153 := bstep (se 2 (by rfl) ⟨138057, by rfl⟩ : syracuseStep 368153 = 276115) B276115
theorem B826955 : Blo 243817 826955 := bstep (se 1 (by rfl) ⟨620216, by rfl⟩ : syracuseStep 826955 = 1240433) B1240433
theorem B368267 : Blo 243817 368267 := bstep (se 1 (by rfl) ⟨276200, by rfl⟩ : syracuseStep 368267 = 552401) B552401
theorem B368279 : Blo 243817 368279 := bstep (se 1 (by rfl) ⟨276209, by rfl⟩ : syracuseStep 368279 = 552419) B552419
theorem B368345 : Blo 243817 368345 := bstep (se 2 (by rfl) ⟨138129, by rfl⟩ : syracuseStep 368345 = 276259) B276259
theorem B368459 : Blo 243817 368459 := bstep (se 1 (by rfl) ⟨276344, by rfl⟩ : syracuseStep 368459 = 552689) B552689
theorem B368471 : Blo 243817 368471 := bstep (se 1 (by rfl) ⟨276353, by rfl⟩ : syracuseStep 368471 = 552707) B552707
theorem B827225 : Blo 243817 827225 := bstep (se 2 (by rfl) ⟨310209, by rfl⟩ : syracuseStep 827225 = 620419) B620419
theorem B368537 : Blo 243817 368537 := bstep (se 2 (by rfl) ⟨138201, by rfl⟩ : syracuseStep 368537 = 276403) B276403
theorem B368651 : Blo 243817 368651 := bstep (se 1 (by rfl) ⟨276488, by rfl⟩ : syracuseStep 368651 = 552977) B552977
theorem B466955 : Blo 243817 466955 := bstep (se 1 (by rfl) ⟨350216, by rfl⟩ : syracuseStep 466955 = 700433) B700433
theorem B1253393 : Blo 243817 1253393 := bstep (se 2 (by rfl) ⟨470022, by rfl⟩ : syracuseStep 1253393 = 940045) B940045
theorem B368663 : Blo 243817 368663 := bstep (se 1 (by rfl) ⟨276497, by rfl⟩ : syracuseStep 368663 = 552995) B552995
theorem B368729 : Blo 243817 368729 := bstep (se 2 (by rfl) ⟨138273, by rfl⟩ : syracuseStep 368729 = 276547) B276547
theorem B1253555 : Blo 243817 1253555 := bstep (se 1 (by rfl) ⟨940166, by rfl⟩ : syracuseStep 1253555 = 1880333) B1880333
theorem B467137 : Blo 243817 467137 := bstep (se 2 (by rfl) ⟨175176, by rfl⟩ : syracuseStep 467137 = 350353) B350353
theorem B368843 : Blo 243817 368843 := bstep (se 1 (by rfl) ⟨276632, by rfl⟩ : syracuseStep 368843 = 553265) B553265
theorem B368855 : Blo 243817 368855 := bstep (se 1 (by rfl) ⟨276641, by rfl⟩ : syracuseStep 368855 = 553283) B553283
theorem B1056989 : Blo 243817 1056989 := bstep (se 3 (by rfl) ⟨198185, by rfl⟩ : syracuseStep 1056989 = 396371) B396371
theorem B368921 : Blo 243817 368921 := bstep (se 2 (by rfl) ⟨138345, by rfl⟩ : syracuseStep 368921 = 276691) B276691
theorem B369035 : Blo 243817 369035 := bstep (se 1 (by rfl) ⟨276776, by rfl⟩ : syracuseStep 369035 = 553553) B553553
theorem B369047 : Blo 243817 369047 := bstep (se 1 (by rfl) ⟨276785, by rfl⟩ : syracuseStep 369047 = 553571) B553571
theorem B369113 : Blo 243817 369113 := bstep (se 2 (by rfl) ⟨138417, by rfl⟩ : syracuseStep 369113 = 276835) B276835
theorem B926225 : Blo 243817 926225 := bstep (se 2 (by rfl) ⟨347334, by rfl⟩ : syracuseStep 926225 = 694669) B694669
theorem B827927 : Blo 243817 827927 := bstep (se 1 (by rfl) ⟨620945, by rfl⟩ : syracuseStep 827927 = 1241891) B1241891
theorem B664129 : Blo 243817 664129 := bstep (se 2 (by rfl) ⟨249048, by rfl⟩ : syracuseStep 664129 = 498097) B498097
theorem B369227 : Blo 243817 369227 := bstep (se 1 (by rfl) ⟨276920, by rfl⟩ : syracuseStep 369227 = 553841) B553841
theorem B369239 : Blo 243817 369239 := bstep (se 1 (by rfl) ⟨276929, by rfl⟩ : syracuseStep 369239 = 553859) B553859
theorem B3711581 : Blo 243817 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B369305 : Blo 243817 369305 := bstep (se 2 (by rfl) ⟨138489, by rfl⟩ : syracuseStep 369305 = 276979) B276979
theorem B2859725 : Blo 243817 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B959197 : Blo 243817 959197 := bstep (se 3 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 959197 = 359699) B359699
theorem B369419 : Blo 243817 369419 := bstep (se 1 (by rfl) ⟨277064, by rfl⟩ : syracuseStep 369419 = 554129) B554129
theorem B369431 : Blo 243817 369431 := bstep (se 1 (by rfl) ⟨277073, by rfl⟩ : syracuseStep 369431 = 554147) B554147
theorem B1581869 : Blo 243817 1581869 := bstep (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) B593201
theorem B369497 : Blo 243817 369497 := bstep (se 2 (by rfl) ⟨138561, by rfl⟩ : syracuseStep 369497 = 277123) B277123
theorem B467851 : Blo 243817 467851 := bstep (se 1 (by rfl) ⟨350888, by rfl⟩ : syracuseStep 467851 = 701777) B701777
theorem B664499 : Blo 243817 664499 := bstep (se 1 (by rfl) ⟨498374, by rfl⟩ : syracuseStep 664499 = 996749) B996749
theorem B369611 : Blo 243817 369611 := bstep (se 1 (by rfl) ⟨277208, by rfl⟩ : syracuseStep 369611 = 554417) B554417
theorem B369623 : Blo 243817 369623 := bstep (se 1 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 369623 = 554435) B554435
theorem B467927 : Blo 243817 467927 := bstep (se 1 (by rfl) ⟨350945, by rfl⟩ : syracuseStep 467927 = 701891) B701891
theorem B369689 : Blo 243817 369689 := bstep (se 2 (by rfl) ⟨138633, by rfl⟩ : syracuseStep 369689 = 277267) B277267
theorem B828467 : Blo 243817 828467 := bstep (se 1 (by rfl) ⟨621350, by rfl⟩ : syracuseStep 828467 = 1242701) B1242701
theorem B369803 : Blo 243817 369803 := bstep (se 1 (by rfl) ⟨277352, by rfl⟩ : syracuseStep 369803 = 554705) B554705
theorem B369815 : Blo 243817 369815 := bstep (se 1 (by rfl) ⟨277361, by rfl⟩ : syracuseStep 369815 = 554723) B554723
theorem B926923 : Blo 243817 926923 := bstep (se 1 (by rfl) ⟨695192, by rfl⟩ : syracuseStep 926923 = 1390385) B1390385
theorem B369881 : Blo 243817 369881 := bstep (se 2 (by rfl) ⟨138705, by rfl⟩ : syracuseStep 369881 = 277411) B277411
theorem B828737 : Blo 243817 828737 := bstep (se 2 (by rfl) ⟨310776, by rfl⟩ : syracuseStep 828737 = 621553) B621553
theorem B369995 : Blo 243817 369995 := bstep (se 1 (by rfl) ⟨277496, by rfl⟩ : syracuseStep 369995 = 554993) B554993
theorem B370007 : Blo 243817 370007 := bstep (se 1 (by rfl) ⟨277505, by rfl⟩ : syracuseStep 370007 = 555011) B555011
theorem B370073 : Blo 243817 370073 := bstep (se 2 (by rfl) ⟨138777, by rfl⟩ : syracuseStep 370073 = 277555) B277555
theorem B927197 : Blo 243817 927197 := bstep (se 3 (by rfl) ⟨173849, by rfl⟩ : syracuseStep 927197 = 347699) B347699
theorem B370187 : Blo 243817 370187 := bstep (se 1 (by rfl) ⟨277640, by rfl⟩ : syracuseStep 370187 = 555281) B555281
theorem B370199 : Blo 243817 370199 := bstep (se 1 (by rfl) ⟨277649, by rfl⟩ : syracuseStep 370199 = 555299) B555299
theorem B370265 : Blo 243817 370265 := bstep (se 2 (by rfl) ⟨138849, by rfl⟩ : syracuseStep 370265 = 277699) B277699
theorem B468595 : Blo 243817 468595 := bstep (se 1 (by rfl) ⟨351446, by rfl⟩ : syracuseStep 468595 = 702893) B702893
theorem B370379 : Blo 243817 370379 := bstep (se 1 (by rfl) ⟨277784, by rfl⟩ : syracuseStep 370379 = 555569) B555569
theorem B370391 : Blo 243817 370391 := bstep (se 1 (by rfl) ⟨277793, by rfl⟩ : syracuseStep 370391 = 555587) B555587
theorem B370457 : Blo 243817 370457 := bstep (se 2 (by rfl) ⟨138921, by rfl⟩ : syracuseStep 370457 = 277843) B277843
theorem B468823 : Blo 243817 468823 := bstep (se 1 (by rfl) ⟨351617, by rfl⟩ : syracuseStep 468823 = 703235) B703235
theorem B829277 : Blo 243817 829277 := bstep (se 3 (by rfl) ⟨155489, by rfl⟩ : syracuseStep 829277 = 310979) B310979
theorem B370571 : Blo 243817 370571 := bstep (se 1 (by rfl) ⟨277928, by rfl⟩ : syracuseStep 370571 = 555857) B555857
theorem B370583 : Blo 243817 370583 := bstep (se 1 (by rfl) ⟨277937, by rfl⟩ : syracuseStep 370583 = 555875) B555875
theorem B698291 : Blo 243817 698291 := bstep (se 1 (by rfl) ⟨523718, by rfl⟩ : syracuseStep 698291 = 1047437) B1047437
theorem B468929 : Blo 243817 468929 := bstep (se 2 (by rfl) ⟨175848, by rfl⟩ : syracuseStep 468929 = 351697) B351697
theorem B370649 : Blo 243817 370649 := bstep (se 2 (by rfl) ⟨138993, by rfl⟩ : syracuseStep 370649 = 277987) B277987
theorem B370763 : Blo 243817 370763 := bstep (se 1 (by rfl) ⟨278072, by rfl⟩ : syracuseStep 370763 = 556145) B556145
theorem B370775 : Blo 243817 370775 := bstep (se 1 (by rfl) ⟨278081, by rfl⟩ : syracuseStep 370775 = 556163) B556163
theorem B469081 : Blo 243817 469081 := bstep (se 2 (by rfl) ⟨175905, by rfl⟩ : syracuseStep 469081 = 351811) B351811
theorem B927895 : Blo 243817 927895 := bstep (se 1 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 927895 = 1391843) B1391843
theorem B698519 : Blo 243817 698519 := bstep (se 1 (by rfl) ⟨523889, by rfl⟩ : syracuseStep 698519 = 1047779) B1047779
theorem B370841 : Blo 243817 370841 := bstep (se 2 (by rfl) ⟨139065, by rfl⟩ : syracuseStep 370841 = 278131) B278131
theorem B370955 : Blo 243817 370955 := bstep (se 1 (by rfl) ⟨278216, by rfl⟩ : syracuseStep 370955 = 556433) B556433
theorem B370967 : Blo 243817 370967 := bstep (se 1 (by rfl) ⟨278225, by rfl⟩ : syracuseStep 370967 = 556451) B556451
theorem B371033 : Blo 243817 371033 := bstep (se 2 (by rfl) ⟨139137, by rfl⟩ : syracuseStep 371033 = 278275) B278275
theorem B698827 : Blo 243817 698827 := bstep (se 1 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 698827 = 1048241) B1048241
theorem B371147 : Blo 243817 371147 := bstep (se 1 (by rfl) ⟨278360, by rfl⟩ : syracuseStep 371147 = 556721) B556721
theorem B371159 : Blo 243817 371159 := bstep (se 1 (by rfl) ⟨278369, by rfl⟩ : syracuseStep 371159 = 556739) B556739
theorem B371225 : Blo 243817 371225 := bstep (se 2 (by rfl) ⟨139209, by rfl⟩ : syracuseStep 371225 = 278419) B278419
theorem B371339 : Blo 243817 371339 := bstep (se 1 (by rfl) ⟨278504, by rfl⟩ : syracuseStep 371339 = 557009) B557009
theorem B371351 : Blo 243817 371351 := bstep (se 1 (by rfl) ⟨278513, by rfl⟩ : syracuseStep 371351 = 557027) B557027
theorem B371417 : Blo 243817 371417 := bstep (se 2 (by rfl) ⟨139281, by rfl⟩ : syracuseStep 371417 = 278563) B278563
theorem B699101 : Blo 243817 699101 := bstep (se 3 (by rfl) ⟨131081, by rfl⟩ : syracuseStep 699101 = 262163) B262163
theorem B371531 : Blo 243817 371531 := bstep (se 1 (by rfl) ⟨278648, by rfl⟩ : syracuseStep 371531 = 557297) B557297
theorem B371543 : Blo 243817 371543 := bstep (se 1 (by rfl) ⟨278657, by rfl⟩ : syracuseStep 371543 = 557315) B557315
theorem B1321859 : Blo 243817 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B1190807 : Blo 243817 1190807 := bstep (se 1 (by rfl) ⟨893105, by rfl⟩ : syracuseStep 1190807 = 1786211) B1786211
theorem B371609 : Blo 243817 371609 := bstep (se 2 (by rfl) ⟨139353, by rfl⟩ : syracuseStep 371609 = 278707) B278707
theorem B928685 : Blo 243817 928685 := bstep (se 3 (by rfl) ⟨174128, by rfl⟩ : syracuseStep 928685 = 348257) B348257
theorem B830411 : Blo 243817 830411 := bstep (se 1 (by rfl) ⟨622808, by rfl⟩ : syracuseStep 830411 = 1245617) B1245617
theorem B1780697 : Blo 243817 1780697 := bstep (se 2 (by rfl) ⟨667761, by rfl⟩ : syracuseStep 1780697 = 1335523) B1335523
theorem B371723 : Blo 243817 371723 := bstep (se 1 (by rfl) ⟨278792, by rfl⟩ : syracuseStep 371723 = 557585) B557585
theorem B830681 : Blo 243817 830681 := bstep (se 2 (by rfl) ⟨311505, by rfl⟩ : syracuseStep 830681 = 623011) B623011
theorem B1879361 : Blo 243817 1879361 := bstep (se 2 (by rfl) ⟨704760, by rfl⟩ : syracuseStep 1879361 = 1409521) B1409521
theorem B470387 : Blo 243817 470387 := bstep (se 1 (by rfl) ⟨352790, by rfl⟩ : syracuseStep 470387 = 705581) B705581
theorem B1584791 : Blo 243817 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B274315 : Blo 243817 274315 := bstep (se 1 (by rfl) ⟨205736, by rfl⟩ : syracuseStep 274315 = 411473) B411473
theorem B831383 : Blo 243817 831383 := bstep (se 1 (by rfl) ⟨623537, by rfl⟩ : syracuseStep 831383 = 1247075) B1247075
theorem B2109361 : Blo 243817 2109361 := bstep (se 2 (by rfl) ⟨791010, by rfl⟩ : syracuseStep 2109361 = 1582021) B1582021
theorem B10825649 : Blo 243817 10825649 := bstep (se 2 (by rfl) ⟨4059618, by rfl⟩ : syracuseStep 10825649 = 8119237) B8119237
theorem B274423 : Blo 243817 274423 := bstep (se 1 (by rfl) ⟨205817, by rfl⟩ : syracuseStep 274423 = 411635) B411635
theorem B1323053 : Blo 243817 1323053 := bstep (se 3 (by rfl) ⟨248072, by rfl⟩ : syracuseStep 1323053 = 496145) B496145
theorem B274603 : Blo 243817 274603 := bstep (se 1 (by rfl) ⟨205952, by rfl⟩ : syracuseStep 274603 = 411905) B411905
theorem B274711 : Blo 243817 274711 := bstep (se 1 (by rfl) ⟨206033, by rfl⟩ : syracuseStep 274711 = 412067) B412067
theorem B930113 : Blo 243817 930113 := bstep (se 2 (by rfl) ⟨348792, by rfl⟩ : syracuseStep 930113 = 697585) B697585
theorem B831923 : Blo 243817 831923 := bstep (se 1 (by rfl) ⟨623942, by rfl⟩ : syracuseStep 831923 = 1247885) B1247885
theorem B274891 : Blo 243817 274891 := bstep (se 1 (by rfl) ⟨206168, by rfl⟩ : syracuseStep 274891 = 412337) B412337
theorem B274999 : Blo 243817 274999 := bstep (se 1 (by rfl) ⟨206249, by rfl⟩ : syracuseStep 274999 = 412499) B412499
theorem B832193 : Blo 243817 832193 := bstep (se 2 (by rfl) ⟨312072, by rfl⟩ : syracuseStep 832193 = 624145) B624145
theorem B275179 : Blo 243817 275179 := bstep (se 1 (by rfl) ⟨206384, by rfl⟩ : syracuseStep 275179 = 412769) B412769
theorem B701207 : Blo 243817 701207 := bstep (se 1 (by rfl) ⟨525905, by rfl⟩ : syracuseStep 701207 = 1051811) B1051811
theorem B275287 : Blo 243817 275287 := bstep (se 1 (by rfl) ⟨206465, by rfl⟩ : syracuseStep 275287 = 412931) B412931
theorem B275467 : Blo 243817 275467 := bstep (se 1 (by rfl) ⟨206600, by rfl⟩ : syracuseStep 275467 = 413201) B413201
theorem B275575 : Blo 243817 275575 := bstep (se 1 (by rfl) ⟨206681, by rfl⟩ : syracuseStep 275575 = 413363) B413363
theorem B996569 : Blo 243817 996569 := bstep (se 2 (by rfl) ⟨373713, by rfl⟩ : syracuseStep 996569 = 747427) B747427
theorem B1881305 : Blo 243817 1881305 := bstep (se 2 (by rfl) ⟨705489, by rfl⟩ : syracuseStep 1881305 = 1410979) B1410979
theorem B832733 : Blo 243817 832733 := bstep (se 3 (by rfl) ⟨156137, by rfl⟩ : syracuseStep 832733 = 312275) B312275
theorem B439553 : Blo 243817 439553 := bstep (se 2 (by rfl) ⟨164832, by rfl⟩ : syracuseStep 439553 = 329665) B329665
theorem B275755 : Blo 243817 275755 := bstep (se 1 (by rfl) ⟨206816, by rfl⟩ : syracuseStep 275755 = 413633) B413633
theorem B669017 : Blo 243817 669017 := bstep (se 2 (by rfl) ⟨250881, by rfl⟩ : syracuseStep 669017 = 501763) B501763
theorem B275863 : Blo 243817 275863 := bstep (se 1 (by rfl) ⟨206897, by rfl⟩ : syracuseStep 275863 = 413795) B413795
theorem B702017 : Blo 243817 702017 := bstep (se 2 (by rfl) ⟨263256, by rfl⟩ : syracuseStep 702017 = 526513) B526513
theorem B276043 : Blo 243817 276043 := bstep (se 1 (by rfl) ⟨207032, by rfl⟩ : syracuseStep 276043 = 414065) B414065
theorem B1881731 : Blo 243817 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B276151 : Blo 243817 276151 := bstep (se 1 (by rfl) ⟨207113, by rfl⟩ : syracuseStep 276151 = 414227) B414227
theorem B931601 : Blo 243817 931601 := bstep (se 2 (by rfl) ⟨349350, by rfl⟩ : syracuseStep 931601 = 698701) B698701
theorem B276331 : Blo 243817 276331 := bstep (se 1 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 276331 = 414497) B414497
theorem B276439 : Blo 243817 276439 := bstep (se 1 (by rfl) ⟨207329, by rfl⟩ : syracuseStep 276439 = 414659) B414659
theorem B997427 : Blo 243817 997427 := bstep (se 1 (by rfl) ⟨748070, by rfl⟩ : syracuseStep 997427 = 1496141) B1496141
theorem B243819 : Blo 243817 243819 := bstep (se 1 (by rfl) ⟨182864, by rfl⟩ : syracuseStep 243819 = 365729) B365729
theorem B243831 : Blo 243817 243831 := bstep (se 1 (by rfl) ⟨182873, by rfl⟩ : syracuseStep 243831 = 365747) B365747
theorem B243851 : Blo 243817 243851 := bstep (se 1 (by rfl) ⟨182888, by rfl⟩ : syracuseStep 243851 = 365777) B365777
theorem B276619 : Blo 243817 276619 := bstep (se 1 (by rfl) ⟨207464, by rfl⟩ : syracuseStep 276619 = 414929) B414929
theorem B243863 : Blo 243817 243863 := bstep (se 1 (by rfl) ⟨182897, by rfl⟩ : syracuseStep 243863 = 365795) B365795
theorem B243883 : Blo 243817 243883 := bstep (se 1 (by rfl) ⟨182912, by rfl⟩ : syracuseStep 243883 = 365825) B365825
theorem B243895 : Blo 243817 243895 := bstep (se 1 (by rfl) ⟨182921, by rfl⟩ : syracuseStep 243895 = 365843) B365843
theorem B243915 : Blo 243817 243915 := bstep (se 1 (by rfl) ⟨182936, by rfl⟩ : syracuseStep 243915 = 365873) B365873
theorem B243927 : Blo 243817 243927 := bstep (se 1 (by rfl) ⟨182945, by rfl⟩ : syracuseStep 243927 = 365891) B365891
theorem B932057 : Blo 243817 932057 := bstep (se 2 (by rfl) ⟨349521, by rfl⟩ : syracuseStep 932057 = 699043) B699043
theorem B243947 : Blo 243817 243947 := bstep (se 1 (by rfl) ⟨182960, by rfl⟩ : syracuseStep 243947 = 365921) B365921
theorem B243959 : Blo 243817 243959 := bstep (se 1 (by rfl) ⟨182969, by rfl⟩ : syracuseStep 243959 = 365939) B365939
theorem B276727 : Blo 243817 276727 := bstep (se 1 (by rfl) ⟨207545, by rfl⟩ : syracuseStep 276727 = 415091) B415091
theorem B243979 : Blo 243817 243979 := bstep (se 1 (by rfl) ⟨182984, by rfl⟩ : syracuseStep 243979 = 365969) B365969
theorem B243991 : Blo 243817 243991 := bstep (se 1 (by rfl) ⟨182993, by rfl⟩ : syracuseStep 243991 = 365987) B365987
theorem B244011 : Blo 243817 244011 := bstep (se 1 (by rfl) ⟨183008, by rfl⟩ : syracuseStep 244011 = 366017) B366017
theorem B244023 : Blo 243817 244023 := bstep (se 1 (by rfl) ⟨183017, by rfl⟩ : syracuseStep 244023 = 366035) B366035
theorem B244043 : Blo 243817 244043 := bstep (se 1 (by rfl) ⟨183032, by rfl⟩ : syracuseStep 244043 = 366065) B366065
theorem B833867 : Blo 243817 833867 := bstep (se 1 (by rfl) ⟨625400, by rfl⟩ : syracuseStep 833867 = 1250801) B1250801
theorem B244055 : Blo 243817 244055 := bstep (se 1 (by rfl) ⟨183041, by rfl⟩ : syracuseStep 244055 = 366083) B366083
theorem B538969 : Blo 243817 538969 := bstep (se 2 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 538969 = 404227) B404227
theorem B244075 : Blo 243817 244075 := bstep (se 1 (by rfl) ⟨183056, by rfl⟩ : syracuseStep 244075 = 366113) B366113
theorem B244087 : Blo 243817 244087 := bstep (se 1 (by rfl) ⟨183065, by rfl⟩ : syracuseStep 244087 = 366131) B366131
theorem B244107 : Blo 243817 244107 := bstep (se 1 (by rfl) ⟨183080, by rfl⟩ : syracuseStep 244107 = 366161) B366161
theorem B244119 : Blo 243817 244119 := bstep (se 1 (by rfl) ⟨183089, by rfl⟩ : syracuseStep 244119 = 366179) B366179
theorem B276907 : Blo 243817 276907 := bstep (se 1 (by rfl) ⟨207680, by rfl⟩ : syracuseStep 276907 = 415361) B415361
theorem B244139 : Blo 243817 244139 := bstep (se 1 (by rfl) ⟨183104, by rfl⟩ : syracuseStep 244139 = 366209) B366209
theorem B932269 : Blo 243817 932269 := bstep (se 3 (by rfl) ⟨174800, by rfl⟩ : syracuseStep 932269 = 349601) B349601
theorem B244151 : Blo 243817 244151 := bstep (se 1 (by rfl) ⟨183113, by rfl⟩ : syracuseStep 244151 = 366227) B366227
theorem B244171 : Blo 243817 244171 := bstep (se 1 (by rfl) ⟨183128, by rfl⟩ : syracuseStep 244171 = 366257) B366257
theorem B244183 : Blo 243817 244183 := bstep (se 1 (by rfl) ⟨183137, by rfl⟩ : syracuseStep 244183 = 366275) B366275
theorem B244203 : Blo 243817 244203 := bstep (se 1 (by rfl) ⟨183152, by rfl⟩ : syracuseStep 244203 = 366305) B366305
theorem B244215 : Blo 243817 244215 := bstep (se 1 (by rfl) ⟨183161, by rfl⟩ : syracuseStep 244215 = 366323) B366323
theorem B244235 : Blo 243817 244235 := bstep (se 1 (by rfl) ⟨183176, by rfl⟩ : syracuseStep 244235 = 366353) B366353
theorem B244247 : Blo 243817 244247 := bstep (se 1 (by rfl) ⟨183185, by rfl⟩ : syracuseStep 244247 = 366371) B366371
theorem B277015 : Blo 243817 277015 := bstep (se 1 (by rfl) ⟨207761, by rfl⟩ : syracuseStep 277015 = 415523) B415523
theorem B244267 : Blo 243817 244267 := bstep (se 1 (by rfl) ⟨183200, by rfl⟩ : syracuseStep 244267 = 366401) B366401
theorem B244279 : Blo 243817 244279 := bstep (se 1 (by rfl) ⟨183209, by rfl⟩ : syracuseStep 244279 = 366419) B366419
theorem B244299 : Blo 243817 244299 := bstep (se 1 (by rfl) ⟨183224, by rfl⟩ : syracuseStep 244299 = 366449) B366449
theorem B309835 : Blo 243817 309835 := bstep (se 1 (by rfl) ⟨232376, by rfl⟩ : syracuseStep 309835 = 464753) B464753
theorem B244311 : Blo 243817 244311 := bstep (se 1 (by rfl) ⟨183233, by rfl⟩ : syracuseStep 244311 = 366467) B366467
theorem B834137 : Blo 243817 834137 := bstep (se 2 (by rfl) ⟨312801, by rfl⟩ : syracuseStep 834137 = 625603) B625603
theorem B244331 : Blo 243817 244331 := bstep (se 1 (by rfl) ⟨183248, by rfl⟩ : syracuseStep 244331 = 366497) B366497
theorem B244343 : Blo 243817 244343 := bstep (se 1 (by rfl) ⟨183257, by rfl⟩ : syracuseStep 244343 = 366515) B366515
theorem B244363 : Blo 243817 244363 := bstep (se 1 (by rfl) ⟨183272, by rfl⟩ : syracuseStep 244363 = 366545) B366545
theorem B244375 : Blo 243817 244375 := bstep (se 1 (by rfl) ⟨183281, by rfl⟩ : syracuseStep 244375 = 366563) B366563
theorem B244395 : Blo 243817 244395 := bstep (se 1 (by rfl) ⟨183296, by rfl⟩ : syracuseStep 244395 = 366593) B366593
theorem B244407 : Blo 243817 244407 := bstep (se 1 (by rfl) ⟨183305, by rfl⟩ : syracuseStep 244407 = 366611) B366611
theorem B244427 : Blo 243817 244427 := bstep (se 1 (by rfl) ⟨183320, by rfl⟩ : syracuseStep 244427 = 366641) B366641
theorem B277195 : Blo 243817 277195 := bstep (se 1 (by rfl) ⟨207896, by rfl⟩ : syracuseStep 277195 = 415793) B415793
theorem B244439 : Blo 243817 244439 := bstep (se 1 (by rfl) ⟨183329, by rfl⟩ : syracuseStep 244439 = 366659) B366659
theorem B932573 : Blo 243817 932573 := bstep (se 3 (by rfl) ⟨174857, by rfl⟩ : syracuseStep 932573 = 349715) B349715
theorem B244459 : Blo 243817 244459 := bstep (se 1 (by rfl) ⟨183344, by rfl⟩ : syracuseStep 244459 = 366689) B366689
theorem B244471 : Blo 243817 244471 := bstep (se 1 (by rfl) ⟨183353, by rfl⟩ : syracuseStep 244471 = 366707) B366707
theorem B244491 : Blo 243817 244491 := bstep (se 1 (by rfl) ⟨183368, by rfl⟩ : syracuseStep 244491 = 366737) B366737
theorem B244503 : Blo 243817 244503 := bstep (se 1 (by rfl) ⟨183377, by rfl⟩ : syracuseStep 244503 = 366755) B366755
theorem B473881 : Blo 243817 473881 := bstep (se 2 (by rfl) ⟨177705, by rfl⟩ : syracuseStep 473881 = 355411) B355411
theorem B244523 : Blo 243817 244523 := bstep (se 1 (by rfl) ⟨183392, by rfl⟩ : syracuseStep 244523 = 366785) B366785
theorem B441139 : Blo 243817 441139 := bstep (se 1 (by rfl) ⟨330854, by rfl⟩ : syracuseStep 441139 = 661709) B661709
theorem B277303 : Blo 243817 277303 := bstep (se 1 (by rfl) ⟨207977, by rfl⟩ : syracuseStep 277303 = 415955) B415955
theorem B244535 : Blo 243817 244535 := bstep (se 1 (by rfl) ⟨183401, by rfl⟩ : syracuseStep 244535 = 366803) B366803
theorem B4733761 : Blo 243817 4733761 := bstep (se 2 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 4733761 = 3550321) B3550321
theorem B244555 : Blo 243817 244555 := bstep (se 1 (by rfl) ⟨183416, by rfl⟩ : syracuseStep 244555 = 366833) B366833
theorem B244567 : Blo 243817 244567 := bstep (se 1 (by rfl) ⟨183425, by rfl⟩ : syracuseStep 244567 = 366851) B366851
theorem B244587 : Blo 243817 244587 := bstep (se 1 (by rfl) ⟨183440, by rfl⟩ : syracuseStep 244587 = 366881) B366881
theorem B244599 : Blo 243817 244599 := bstep (se 1 (by rfl) ⟨183449, by rfl⟩ : syracuseStep 244599 = 366899) B366899
theorem B244619 : Blo 243817 244619 := bstep (se 1 (by rfl) ⟨183464, by rfl⟩ : syracuseStep 244619 = 366929) B366929
theorem B244631 : Blo 243817 244631 := bstep (se 1 (by rfl) ⟨183473, by rfl⟩ : syracuseStep 244631 = 366947) B366947
theorem B244651 : Blo 243817 244651 := bstep (se 1 (by rfl) ⟨183488, by rfl⟩ : syracuseStep 244651 = 366977) B366977
theorem B1981361 : Blo 243817 1981361 := bstep (se 2 (by rfl) ⟨743010, by rfl⟩ : syracuseStep 1981361 = 1486021) B1486021
theorem B244663 : Blo 243817 244663 := bstep (se 1 (by rfl) ⟨183497, by rfl⟩ : syracuseStep 244663 = 366995) B366995
theorem B244683 : Blo 243817 244683 := bstep (se 1 (by rfl) ⟨183512, by rfl⟩ : syracuseStep 244683 = 367025) B367025
theorem B244695 : Blo 243817 244695 := bstep (se 1 (by rfl) ⟨183521, by rfl⟩ : syracuseStep 244695 = 367043) B367043
theorem B441305 : Blo 243817 441305 := bstep (se 2 (by rfl) ⟨165489, by rfl⟩ : syracuseStep 441305 = 330979) B330979
theorem B244715 : Blo 243817 244715 := bstep (se 1 (by rfl) ⟨183536, by rfl⟩ : syracuseStep 244715 = 367073) B367073
theorem B277483 : Blo 243817 277483 := bstep (se 1 (by rfl) ⟨208112, by rfl⟩ : syracuseStep 277483 = 416225) B416225
theorem B244727 : Blo 243817 244727 := bstep (se 1 (by rfl) ⟨183545, by rfl⟩ : syracuseStep 244727 = 367091) B367091
theorem B244747 : Blo 243817 244747 := bstep (se 1 (by rfl) ⟨183560, by rfl⟩ : syracuseStep 244747 = 367121) B367121
theorem B244759 : Blo 243817 244759 := bstep (se 1 (by rfl) ⟨183569, by rfl⟩ : syracuseStep 244759 = 367139) B367139
theorem B244779 : Blo 243817 244779 := bstep (se 1 (by rfl) ⟨183584, by rfl⟩ : syracuseStep 244779 = 367169) B367169
theorem B244791 : Blo 243817 244791 := bstep (se 1 (by rfl) ⟨183593, by rfl⟩ : syracuseStep 244791 = 367187) B367187
theorem B244811 : Blo 243817 244811 := bstep (se 1 (by rfl) ⟨183608, by rfl⟩ : syracuseStep 244811 = 367217) B367217
theorem B277591 : Blo 243817 277591 := bstep (se 1 (by rfl) ⟨208193, by rfl⟩ : syracuseStep 277591 = 416387) B416387
theorem B244823 : Blo 243817 244823 := bstep (se 1 (by rfl) ⟨183617, by rfl⟩ : syracuseStep 244823 = 367235) B367235
theorem B244843 : Blo 243817 244843 := bstep (se 1 (by rfl) ⟨183632, by rfl⟩ : syracuseStep 244843 = 367265) B367265
theorem B244855 : Blo 243817 244855 := bstep (se 1 (by rfl) ⟨183641, by rfl⟩ : syracuseStep 244855 = 367283) B367283
theorem B244875 : Blo 243817 244875 := bstep (se 1 (by rfl) ⟨183656, by rfl⟩ : syracuseStep 244875 = 367313) B367313
theorem B244887 : Blo 243817 244887 := bstep (se 1 (by rfl) ⟨183665, by rfl⟩ : syracuseStep 244887 = 367331) B367331
theorem B5717143 : Blo 243817 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B244907 : Blo 243817 244907 := bstep (se 1 (by rfl) ⟨183680, by rfl⟩ : syracuseStep 244907 = 367361) B367361
theorem B703667 : Blo 243817 703667 := bstep (se 1 (by rfl) ⟨527750, by rfl⟩ : syracuseStep 703667 = 1055501) B1055501
theorem B244919 : Blo 243817 244919 := bstep (se 1 (by rfl) ⟨183689, by rfl⟩ : syracuseStep 244919 = 367379) B367379
theorem B244939 : Blo 243817 244939 := bstep (se 1 (by rfl) ⟨183704, by rfl⟩ : syracuseStep 244939 = 367409) B367409
theorem B703691 : Blo 243817 703691 := bstep (se 1 (by rfl) ⟨527768, by rfl⟩ : syracuseStep 703691 = 1055537) B1055537
theorem B244951 : Blo 243817 244951 := bstep (se 1 (by rfl) ⟨183713, by rfl⟩ : syracuseStep 244951 = 367427) B367427
theorem B244971 : Blo 243817 244971 := bstep (se 1 (by rfl) ⟨183728, by rfl⟩ : syracuseStep 244971 = 367457) B367457
theorem B244983 : Blo 243817 244983 := bstep (se 1 (by rfl) ⟨183737, by rfl⟩ : syracuseStep 244983 = 367475) B367475
theorem B245003 : Blo 243817 245003 := bstep (se 1 (by rfl) ⟨183752, by rfl⟩ : syracuseStep 245003 = 367505) B367505
theorem B277771 : Blo 243817 277771 := bstep (se 1 (by rfl) ⟨208328, by rfl⟩ : syracuseStep 277771 = 416657) B416657
theorem B245015 : Blo 243817 245015 := bstep (se 1 (by rfl) ⟨183761, by rfl⟩ : syracuseStep 245015 = 367523) B367523
theorem B834839 : Blo 243817 834839 := bstep (se 1 (by rfl) ⟨626129, by rfl⟩ : syracuseStep 834839 = 1252259) B1252259
theorem B245035 : Blo 243817 245035 := bstep (se 1 (by rfl) ⟨183776, by rfl⟩ : syracuseStep 245035 = 367553) B367553
theorem B245047 : Blo 243817 245047 := bstep (se 1 (by rfl) ⟨183785, by rfl⟩ : syracuseStep 245047 = 367571) B367571
theorem B1326401 : Blo 243817 1326401 := bstep (se 2 (by rfl) ⟨497400, by rfl⟩ : syracuseStep 1326401 = 994801) B994801
theorem B245067 : Blo 243817 245067 := bstep (se 1 (by rfl) ⟨183800, by rfl⟩ : syracuseStep 245067 = 367601) B367601
theorem B245079 : Blo 243817 245079 := bstep (se 1 (by rfl) ⟨183809, by rfl⟩ : syracuseStep 245079 = 367619) B367619
theorem B245099 : Blo 243817 245099 := bstep (se 1 (by rfl) ⟨183824, by rfl⟩ : syracuseStep 245099 = 367649) B367649
theorem B441715 : Blo 243817 441715 := bstep (se 1 (by rfl) ⟨331286, by rfl⟩ : syracuseStep 441715 = 662573) B662573
theorem B277879 : Blo 243817 277879 := bstep (se 1 (by rfl) ⟨208409, by rfl⟩ : syracuseStep 277879 = 416819) B416819
theorem B245111 : Blo 243817 245111 := bstep (se 1 (by rfl) ⟨183833, by rfl⟩ : syracuseStep 245111 = 367667) B367667
theorem B245131 : Blo 243817 245131 := bstep (se 1 (by rfl) ⟨183848, by rfl⟩ : syracuseStep 245131 = 367697) B367697
theorem B245143 : Blo 243817 245143 := bstep (se 1 (by rfl) ⟨183857, by rfl⟩ : syracuseStep 245143 = 367715) B367715
theorem B245163 : Blo 243817 245163 := bstep (se 1 (by rfl) ⟨183872, by rfl⟩ : syracuseStep 245163 = 367745) B367745
theorem B245175 : Blo 243817 245175 := bstep (se 1 (by rfl) ⟨183881, by rfl⟩ : syracuseStep 245175 = 367763) B367763
theorem B245195 : Blo 243817 245195 := bstep (se 1 (by rfl) ⟨183896, by rfl⟩ : syracuseStep 245195 = 367793) B367793
theorem B245207 : Blo 243817 245207 := bstep (se 1 (by rfl) ⟨183905, by rfl⟩ : syracuseStep 245207 = 367811) B367811
theorem B245227 : Blo 243817 245227 := bstep (se 1 (by rfl) ⟨183920, by rfl⟩ : syracuseStep 245227 = 367841) B367841
theorem B245239 : Blo 243817 245239 := bstep (se 1 (by rfl) ⟨183929, by rfl⟩ : syracuseStep 245239 = 367859) B367859
theorem B245259 : Blo 243817 245259 := bstep (se 1 (by rfl) ⟨183944, by rfl⟩ : syracuseStep 245259 = 367889) B367889
theorem B245271 : Blo 243817 245271 := bstep (se 1 (by rfl) ⟨183953, by rfl⟩ : syracuseStep 245271 = 367907) B367907
theorem B310807 : Blo 243817 310807 := bstep (se 1 (by rfl) ⟨233105, by rfl⟩ : syracuseStep 310807 = 466211) B466211
theorem B245291 : Blo 243817 245291 := bstep (se 1 (by rfl) ⟨183968, by rfl⟩ : syracuseStep 245291 = 367937) B367937
theorem B278059 : Blo 243817 278059 := bstep (se 1 (by rfl) ⟨208544, by rfl⟩ : syracuseStep 278059 = 417089) B417089
theorem B245303 : Blo 243817 245303 := bstep (se 1 (by rfl) ⟨183977, by rfl⟩ : syracuseStep 245303 = 367955) B367955
theorem B245323 : Blo 243817 245323 := bstep (se 1 (by rfl) ⟨183992, by rfl⟩ : syracuseStep 245323 = 367985) B367985
theorem B3391051 : Blo 243817 3391051 := bstep (se 1 (by rfl) ⟨2543288, by rfl⟩ : syracuseStep 3391051 = 5086577) B5086577
theorem B245335 : Blo 243817 245335 := bstep (se 1 (by rfl) ⟨184001, by rfl⟩ : syracuseStep 245335 = 368003) B368003
theorem B245355 : Blo 243817 245355 := bstep (se 1 (by rfl) ⟨184016, by rfl⟩ : syracuseStep 245355 = 368033) B368033
theorem B245367 : Blo 243817 245367 := bstep (se 1 (by rfl) ⟨184025, by rfl⟩ : syracuseStep 245367 = 368051) B368051
theorem B245387 : Blo 243817 245387 := bstep (se 1 (by rfl) ⟨184040, by rfl⟩ : syracuseStep 245387 = 368081) B368081
theorem B245399 : Blo 243817 245399 := bstep (se 1 (by rfl) ⟨184049, by rfl⟩ : syracuseStep 245399 = 368099) B368099
theorem B278167 : Blo 243817 278167 := bstep (se 1 (by rfl) ⟨208625, by rfl⟩ : syracuseStep 278167 = 417251) B417251
theorem B245419 : Blo 243817 245419 := bstep (se 1 (by rfl) ⟨184064, by rfl⟩ : syracuseStep 245419 = 368129) B368129
theorem B245431 : Blo 243817 245431 := bstep (se 1 (by rfl) ⟨184073, by rfl⟩ : syracuseStep 245431 = 368147) B368147
theorem B245451 : Blo 243817 245451 := bstep (se 1 (by rfl) ⟨184088, by rfl⟩ : syracuseStep 245451 = 368177) B368177
theorem B245463 : Blo 243817 245463 := bstep (se 1 (by rfl) ⟨184097, by rfl⟩ : syracuseStep 245463 = 368195) B368195
theorem B245483 : Blo 243817 245483 := bstep (se 1 (by rfl) ⟨184112, by rfl⟩ : syracuseStep 245483 = 368225) B368225
theorem B245495 : Blo 243817 245495 := bstep (se 1 (by rfl) ⟨184121, by rfl⟩ : syracuseStep 245495 = 368243) B368243
theorem B245515 : Blo 243817 245515 := bstep (se 1 (by rfl) ⟨184136, by rfl⟩ : syracuseStep 245515 = 368273) B368273
theorem B245527 : Blo 243817 245527 := bstep (se 1 (by rfl) ⟨184145, by rfl⟩ : syracuseStep 245527 = 368291) B368291
theorem B245547 : Blo 243817 245547 := bstep (se 1 (by rfl) ⟨184160, by rfl⟩ : syracuseStep 245547 = 368321) B368321
theorem B835379 : Blo 243817 835379 := bstep (se 1 (by rfl) ⟨626534, by rfl⟩ : syracuseStep 835379 = 1253069) B1253069
theorem B245559 : Blo 243817 245559 := bstep (se 1 (by rfl) ⟨184169, by rfl⟩ : syracuseStep 245559 = 368339) B368339
theorem B245579 : Blo 243817 245579 := bstep (se 1 (by rfl) ⟨184184, by rfl⟩ : syracuseStep 245579 = 368369) B368369
theorem B278347 : Blo 243817 278347 := bstep (se 1 (by rfl) ⟨208760, by rfl⟩ : syracuseStep 278347 = 417521) B417521
theorem B245591 : Blo 243817 245591 := bstep (se 1 (by rfl) ⟨184193, by rfl⟩ : syracuseStep 245591 = 368387) B368387
theorem B245611 : Blo 243817 245611 := bstep (se 1 (by rfl) ⟨184208, by rfl⟩ : syracuseStep 245611 = 368417) B368417
theorem B245623 : Blo 243817 245623 := bstep (se 1 (by rfl) ⟨184217, by rfl⟩ : syracuseStep 245623 = 368435) B368435
theorem B245643 : Blo 243817 245643 := bstep (se 1 (by rfl) ⟨184232, by rfl⟩ : syracuseStep 245643 = 368465) B368465
theorem B245655 : Blo 243817 245655 := bstep (se 1 (by rfl) ⟨184241, by rfl⟩ : syracuseStep 245655 = 368483) B368483
theorem B245675 : Blo 243817 245675 := bstep (se 1 (by rfl) ⟨184256, by rfl⟩ : syracuseStep 245675 = 368513) B368513
theorem B245687 : Blo 243817 245687 := bstep (se 1 (by rfl) ⟨184265, by rfl⟩ : syracuseStep 245687 = 368531) B368531
theorem B278455 : Blo 243817 278455 := bstep (se 1 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 278455 = 417683) B417683
theorem B245707 : Blo 243817 245707 := bstep (se 1 (by rfl) ⟨184280, by rfl⟩ : syracuseStep 245707 = 368561) B368561
theorem B245719 : Blo 243817 245719 := bstep (se 1 (by rfl) ⟨184289, by rfl⟩ : syracuseStep 245719 = 368579) B368579
theorem B704477 : Blo 243817 704477 := bstep (se 3 (by rfl) ⟨132089, by rfl⟩ : syracuseStep 704477 = 264179) B264179
theorem B245739 : Blo 243817 245739 := bstep (se 1 (by rfl) ⟨184304, by rfl⟩ : syracuseStep 245739 = 368609) B368609
theorem B245751 : Blo 243817 245751 := bstep (se 1 (by rfl) ⟨184313, by rfl⟩ : syracuseStep 245751 = 368627) B368627
theorem B245771 : Blo 243817 245771 := bstep (se 1 (by rfl) ⟨184328, by rfl⟩ : syracuseStep 245771 = 368657) B368657
theorem B245783 : Blo 243817 245783 := bstep (se 1 (by rfl) ⟨184337, by rfl⟩ : syracuseStep 245783 = 368675) B368675
theorem B245803 : Blo 243817 245803 := bstep (se 1 (by rfl) ⟨184352, by rfl⟩ : syracuseStep 245803 = 368705) B368705
theorem B245815 : Blo 243817 245815 := bstep (se 1 (by rfl) ⟨184361, by rfl⟩ : syracuseStep 245815 = 368723) B368723
theorem B835649 : Blo 243817 835649 := bstep (se 2 (by rfl) ⟨313368, by rfl⟩ : syracuseStep 835649 = 626737) B626737
theorem B245835 : Blo 243817 245835 := bstep (se 1 (by rfl) ⟨184376, by rfl⟩ : syracuseStep 245835 = 368753) B368753
theorem B245847 : Blo 243817 245847 := bstep (se 1 (by rfl) ⟨184385, by rfl⟩ : syracuseStep 245847 = 368771) B368771
theorem B245867 : Blo 243817 245867 := bstep (se 1 (by rfl) ⟨184400, by rfl⟩ : syracuseStep 245867 = 368801) B368801
theorem B278635 : Blo 243817 278635 := bstep (se 1 (by rfl) ⟨208976, by rfl⟩ : syracuseStep 278635 = 417953) B417953
theorem B245879 : Blo 243817 245879 := bstep (se 1 (by rfl) ⟨184409, by rfl⟩ : syracuseStep 245879 = 368819) B368819
theorem B245899 : Blo 243817 245899 := bstep (se 1 (by rfl) ⟨184424, by rfl⟩ : syracuseStep 245899 = 368849) B368849
theorem B245911 : Blo 243817 245911 := bstep (se 1 (by rfl) ⟨184433, by rfl⟩ : syracuseStep 245911 = 368867) B368867
theorem B245931 : Blo 243817 245931 := bstep (se 1 (by rfl) ⟨184448, by rfl⟩ : syracuseStep 245931 = 368897) B368897
theorem B245943 : Blo 243817 245943 := bstep (se 1 (by rfl) ⟨184457, by rfl⟩ : syracuseStep 245943 = 368915) B368915
theorem B245963 : Blo 243817 245963 := bstep (se 1 (by rfl) ⟨184472, by rfl⟩ : syracuseStep 245963 = 368945) B368945
theorem B245975 : Blo 243817 245975 := bstep (se 1 (by rfl) ⟨184481, by rfl⟩ : syracuseStep 245975 = 368963) B368963
theorem B278743 : Blo 243817 278743 := bstep (se 1 (by rfl) ⟨209057, by rfl⟩ : syracuseStep 278743 = 418115) B418115
theorem B245995 : Blo 243817 245995 := bstep (se 1 (by rfl) ⟨184496, by rfl⟩ : syracuseStep 245995 = 368993) B368993
theorem B246007 : Blo 243817 246007 := bstep (se 1 (by rfl) ⟨184505, by rfl⟩ : syracuseStep 246007 = 369011) B369011
theorem B246027 : Blo 243817 246027 := bstep (se 1 (by rfl) ⟨184520, by rfl⟩ : syracuseStep 246027 = 369041) B369041
theorem B246039 : Blo 243817 246039 := bstep (se 1 (by rfl) ⟨184529, by rfl⟩ : syracuseStep 246039 = 369059) B369059
theorem B1982755 : Blo 243817 1982755 := bstep (se 1 (by rfl) ⟨1487066, by rfl⟩ : syracuseStep 1982755 = 2974133) B2974133
theorem B246059 : Blo 243817 246059 := bstep (se 1 (by rfl) ⟨184544, by rfl⟩ : syracuseStep 246059 = 369089) B369089
theorem B246071 : Blo 243817 246071 := bstep (se 1 (by rfl) ⟨184553, by rfl⟩ : syracuseStep 246071 = 369107) B369107
theorem B246091 : Blo 243817 246091 := bstep (se 1 (by rfl) ⟨184568, by rfl⟩ : syracuseStep 246091 = 369137) B369137
theorem B311627 : Blo 243817 311627 := bstep (se 1 (by rfl) ⟨233720, by rfl⟩ : syracuseStep 311627 = 467441) B467441
theorem B246103 : Blo 243817 246103 := bstep (se 1 (by rfl) ⟨184577, by rfl⟩ : syracuseStep 246103 = 369155) B369155
theorem B246123 : Blo 243817 246123 := bstep (se 1 (by rfl) ⟨184592, by rfl⟩ : syracuseStep 246123 = 369185) B369185
theorem B246135 : Blo 243817 246135 := bstep (se 1 (by rfl) ⟨184601, by rfl⟩ : syracuseStep 246135 = 369203) B369203
theorem B246155 : Blo 243817 246155 := bstep (se 1 (by rfl) ⟨184616, by rfl⟩ : syracuseStep 246155 = 369233) B369233
theorem B246167 : Blo 243817 246167 := bstep (se 1 (by rfl) ⟨184625, by rfl⟩ : syracuseStep 246167 = 369251) B369251
theorem B246187 : Blo 243817 246187 := bstep (se 1 (by rfl) ⟨184640, by rfl⟩ : syracuseStep 246187 = 369281) B369281
theorem B246199 : Blo 243817 246199 := bstep (se 1 (by rfl) ⟨184649, by rfl⟩ : syracuseStep 246199 = 369299) B369299
theorem B246219 : Blo 243817 246219 := bstep (se 1 (by rfl) ⟨184664, by rfl⟩ : syracuseStep 246219 = 369329) B369329
theorem B246231 : Blo 243817 246231 := bstep (se 1 (by rfl) ⟨184673, by rfl⟩ : syracuseStep 246231 = 369347) B369347
theorem B2114009 : Blo 243817 2114009 := bstep (se 2 (by rfl) ⟨792753, by rfl⟩ : syracuseStep 2114009 = 1585507) B1585507
theorem B246251 : Blo 243817 246251 := bstep (se 1 (by rfl) ⟨184688, by rfl⟩ : syracuseStep 246251 = 369377) B369377
theorem B246263 : Blo 243817 246263 := bstep (se 1 (by rfl) ⟨184697, by rfl⟩ : syracuseStep 246263 = 369395) B369395
theorem B246283 : Blo 243817 246283 := bstep (se 1 (by rfl) ⟨184712, by rfl⟩ : syracuseStep 246283 = 369425) B369425
theorem B246295 : Blo 243817 246295 := bstep (se 1 (by rfl) ⟨184721, by rfl⟩ : syracuseStep 246295 = 369443) B369443
theorem B246315 : Blo 243817 246315 := bstep (se 1 (by rfl) ⟨184736, by rfl⟩ : syracuseStep 246315 = 369473) B369473
theorem B246327 : Blo 243817 246327 := bstep (se 1 (by rfl) ⟨184745, by rfl⟩ : syracuseStep 246327 = 369491) B369491
theorem B442955 : Blo 243817 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B246347 : Blo 243817 246347 := bstep (se 1 (by rfl) ⟨184760, by rfl⟩ : syracuseStep 246347 = 369521) B369521
theorem B246359 : Blo 243817 246359 := bstep (se 1 (by rfl) ⟨184769, by rfl⟩ : syracuseStep 246359 = 369539) B369539
theorem B836189 : Blo 243817 836189 := bstep (se 3 (by rfl) ⟨156785, by rfl⟩ : syracuseStep 836189 = 313571) B313571
theorem B246379 : Blo 243817 246379 := bstep (se 1 (by rfl) ⟨184784, by rfl⟩ : syracuseStep 246379 = 369569) B369569
theorem B246391 : Blo 243817 246391 := bstep (se 1 (by rfl) ⟨184793, by rfl⟩ : syracuseStep 246391 = 369587) B369587
theorem B246411 : Blo 243817 246411 := bstep (se 1 (by rfl) ⟨184808, by rfl⟩ : syracuseStep 246411 = 369617) B369617
theorem B246423 : Blo 243817 246423 := bstep (se 1 (by rfl) ⟨184817, by rfl⟩ : syracuseStep 246423 = 369635) B369635
theorem B246443 : Blo 243817 246443 := bstep (se 1 (by rfl) ⟨184832, by rfl⟩ : syracuseStep 246443 = 369665) B369665
theorem B246455 : Blo 243817 246455 := bstep (se 1 (by rfl) ⟨184841, by rfl⟩ : syracuseStep 246455 = 369683) B369683
theorem B246475 : Blo 243817 246475 := bstep (se 1 (by rfl) ⟨184856, by rfl⟩ : syracuseStep 246475 = 369713) B369713
theorem B246487 : Blo 243817 246487 := bstep (se 1 (by rfl) ⟨184865, by rfl⟩ : syracuseStep 246487 = 369731) B369731
theorem B246507 : Blo 243817 246507 := bstep (se 1 (by rfl) ⟨184880, by rfl⟩ : syracuseStep 246507 = 369761) B369761
theorem B246519 : Blo 243817 246519 := bstep (se 1 (by rfl) ⟨184889, by rfl⟩ : syracuseStep 246519 = 369779) B369779
theorem B2999045 : Blo 243817 2999045 := bstep (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) B562321
theorem B246539 : Blo 243817 246539 := bstep (se 1 (by rfl) ⟨184904, by rfl⟩ : syracuseStep 246539 = 369809) B369809
theorem B246551 : Blo 243817 246551 := bstep (se 1 (by rfl) ⟨184913, by rfl⟩ : syracuseStep 246551 = 369827) B369827
theorem B246571 : Blo 243817 246571 := bstep (se 1 (by rfl) ⟨184928, by rfl⟩ : syracuseStep 246571 = 369857) B369857
theorem B246583 : Blo 243817 246583 := bstep (se 1 (by rfl) ⟨184937, by rfl⟩ : syracuseStep 246583 = 369875) B369875
theorem B1393483 : Blo 243817 1393483 := bstep (se 1 (by rfl) ⟨1045112, by rfl⟩ : syracuseStep 1393483 = 2090225) B2090225
theorem B246603 : Blo 243817 246603 := bstep (se 1 (by rfl) ⟨184952, by rfl⟩ : syracuseStep 246603 = 369905) B369905
theorem B246615 : Blo 243817 246615 := bstep (se 1 (by rfl) ⟨184961, by rfl⟩ : syracuseStep 246615 = 369923) B369923
theorem B246635 : Blo 243817 246635 := bstep (se 1 (by rfl) ⟨184976, by rfl⟩ : syracuseStep 246635 = 369953) B369953
theorem B246647 : Blo 243817 246647 := bstep (se 1 (by rfl) ⟨184985, by rfl⟩ : syracuseStep 246647 = 369971) B369971
theorem B246667 : Blo 243817 246667 := bstep (se 1 (by rfl) ⟨185000, by rfl⟩ : syracuseStep 246667 = 370001) B370001
theorem B246679 : Blo 243817 246679 := bstep (se 1 (by rfl) ⟨185009, by rfl⟩ : syracuseStep 246679 = 370019) B370019
theorem B246699 : Blo 243817 246699 := bstep (se 1 (by rfl) ⟨185024, by rfl⟩ : syracuseStep 246699 = 370049) B370049
theorem B246711 : Blo 243817 246711 := bstep (se 1 (by rfl) ⟨185033, by rfl⟩ : syracuseStep 246711 = 370067) B370067
theorem B246731 : Blo 243817 246731 := bstep (se 1 (by rfl) ⟨185048, by rfl⟩ : syracuseStep 246731 = 370097) B370097
theorem B246743 : Blo 243817 246743 := bstep (se 1 (by rfl) ⟨185057, by rfl⟩ : syracuseStep 246743 = 370115) B370115
theorem B246763 : Blo 243817 246763 := bstep (se 1 (by rfl) ⟨185072, by rfl⟩ : syracuseStep 246763 = 370145) B370145
theorem B246775 : Blo 243817 246775 := bstep (se 1 (by rfl) ⟨185081, by rfl⟩ : syracuseStep 246775 = 370163) B370163
theorem B312331 : Blo 243817 312331 := bstep (se 1 (by rfl) ⟨234248, by rfl⟩ : syracuseStep 312331 = 468497) B468497
theorem B246795 : Blo 243817 246795 := bstep (se 1 (by rfl) ⟨185096, by rfl⟩ : syracuseStep 246795 = 370193) B370193
theorem B246807 : Blo 243817 246807 := bstep (se 1 (by rfl) ⟨185105, by rfl⟩ : syracuseStep 246807 = 370211) B370211
theorem B246827 : Blo 243817 246827 := bstep (se 1 (by rfl) ⟨185120, by rfl⟩ : syracuseStep 246827 = 370241) B370241
theorem B246839 : Blo 243817 246839 := bstep (se 1 (by rfl) ⟨185129, by rfl⟩ : syracuseStep 246839 = 370259) B370259
theorem B246859 : Blo 243817 246859 := bstep (se 1 (by rfl) ⟨185144, by rfl⟩ : syracuseStep 246859 = 370289) B370289
theorem B246871 : Blo 243817 246871 := bstep (se 1 (by rfl) ⟨185153, by rfl⟩ : syracuseStep 246871 = 370307) B370307
theorem B1393757 : Blo 243817 1393757 := bstep (se 3 (by rfl) ⟨261329, by rfl⟩ : syracuseStep 1393757 = 522659) B522659
theorem B246891 : Blo 243817 246891 := bstep (se 1 (by rfl) ⟨185168, by rfl⟩ : syracuseStep 246891 = 370337) B370337
theorem B246903 : Blo 243817 246903 := bstep (se 1 (by rfl) ⟨185177, by rfl⟩ : syracuseStep 246903 = 370355) B370355
theorem B246923 : Blo 243817 246923 := bstep (se 1 (by rfl) ⟨185192, by rfl⟩ : syracuseStep 246923 = 370385) B370385
theorem B246935 : Blo 243817 246935 := bstep (se 1 (by rfl) ⟨185201, by rfl⟩ : syracuseStep 246935 = 370403) B370403
theorem B246955 : Blo 243817 246955 := bstep (se 1 (by rfl) ⟨185216, by rfl⟩ : syracuseStep 246955 = 370433) B370433
theorem B246967 : Blo 243817 246967 := bstep (se 1 (by rfl) ⟨185225, by rfl⟩ : syracuseStep 246967 = 370451) B370451
theorem B246987 : Blo 243817 246987 := bstep (se 1 (by rfl) ⟨185240, by rfl⟩ : syracuseStep 246987 = 370481) B370481
theorem B246999 : Blo 243817 246999 := bstep (se 1 (by rfl) ⟨185249, by rfl⟩ : syracuseStep 246999 = 370499) B370499
theorem B247019 : Blo 243817 247019 := bstep (se 1 (by rfl) ⟨185264, by rfl⟩ : syracuseStep 247019 = 370529) B370529
theorem B247031 : Blo 243817 247031 := bstep (se 1 (by rfl) ⟨185273, by rfl⟩ : syracuseStep 247031 = 370547) B370547
theorem B935171 : Blo 243817 935171 := bstep (se 1 (by rfl) ⟨701378, by rfl⟩ : syracuseStep 935171 = 1402757) B1402757
theorem B247051 : Blo 243817 247051 := bstep (se 1 (by rfl) ⟨185288, by rfl⟩ : syracuseStep 247051 = 370577) B370577
theorem B935185 : Blo 243817 935185 := bstep (se 2 (by rfl) ⟨350694, by rfl⟩ : syracuseStep 935185 = 701389) B701389
theorem B312599 : Blo 243817 312599 := bstep (se 1 (by rfl) ⟨234449, by rfl⟩ : syracuseStep 312599 = 468899) B468899
theorem B247063 : Blo 243817 247063 := bstep (se 1 (by rfl) ⟨185297, by rfl⟩ : syracuseStep 247063 = 370595) B370595
theorem B247083 : Blo 243817 247083 := bstep (se 1 (by rfl) ⟨185312, by rfl⟩ : syracuseStep 247083 = 370625) B370625
theorem B1361197 : Blo 243817 1361197 := bstep (se 3 (by rfl) ⟨255224, by rfl⟩ : syracuseStep 1361197 = 510449) B510449
theorem B247095 : Blo 243817 247095 := bstep (se 1 (by rfl) ⟨185321, by rfl⟩ : syracuseStep 247095 = 370643) B370643
theorem B247115 : Blo 243817 247115 := bstep (se 1 (by rfl) ⟨185336, by rfl⟩ : syracuseStep 247115 = 370673) B370673
theorem B247127 : Blo 243817 247127 := bstep (se 1 (by rfl) ⟨185345, by rfl⟩ : syracuseStep 247127 = 370691) B370691
theorem B247147 : Blo 243817 247147 := bstep (se 1 (by rfl) ⟨185360, by rfl⟩ : syracuseStep 247147 = 370721) B370721
theorem B247159 : Blo 243817 247159 := bstep (se 1 (by rfl) ⟨185369, by rfl⟩ : syracuseStep 247159 = 370739) B370739
theorem B247179 : Blo 243817 247179 := bstep (se 1 (by rfl) ⟨185384, by rfl⟩ : syracuseStep 247179 = 370769) B370769
theorem B247191 : Blo 243817 247191 := bstep (se 1 (by rfl) ⟨185393, by rfl⟩ : syracuseStep 247191 = 370787) B370787
theorem B247211 : Blo 243817 247211 := bstep (se 1 (by rfl) ⟨185408, by rfl⟩ : syracuseStep 247211 = 370817) B370817
theorem B247223 : Blo 243817 247223 := bstep (se 1 (by rfl) ⟨185417, by rfl⟩ : syracuseStep 247223 = 370835) B370835
theorem B247243 : Blo 243817 247243 := bstep (se 1 (by rfl) ⟨185432, by rfl⟩ : syracuseStep 247243 = 370865) B370865
theorem B247255 : Blo 243817 247255 := bstep (se 1 (by rfl) ⟨185441, by rfl⟩ : syracuseStep 247255 = 370883) B370883
theorem B247275 : Blo 243817 247275 := bstep (se 1 (by rfl) ⟨185456, by rfl⟩ : syracuseStep 247275 = 370913) B370913
theorem B247287 : Blo 243817 247287 := bstep (se 1 (by rfl) ⟨185465, by rfl⟩ : syracuseStep 247287 = 370931) B370931
theorem B247307 : Blo 243817 247307 := bstep (se 1 (by rfl) ⟨185480, by rfl⟩ : syracuseStep 247307 = 370961) B370961
theorem B1132055 : Blo 243817 1132055 := bstep (se 1 (by rfl) ⟨849041, by rfl⟩ : syracuseStep 1132055 = 1698083) B1698083
theorem B247319 : Blo 243817 247319 := bstep (se 1 (by rfl) ⟨185489, by rfl⟩ : syracuseStep 247319 = 370979) B370979
theorem B247339 : Blo 243817 247339 := bstep (se 1 (by rfl) ⟨185504, by rfl⟩ : syracuseStep 247339 = 371009) B371009
theorem B247351 : Blo 243817 247351 := bstep (se 1 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 247351 = 371027) B371027
theorem B935489 : Blo 243817 935489 := bstep (se 2 (by rfl) ⟨350808, by rfl⟩ : syracuseStep 935489 = 701617) B701617
theorem B247371 : Blo 243817 247371 := bstep (se 1 (by rfl) ⟨185528, by rfl⟩ : syracuseStep 247371 = 371057) B371057
theorem B247383 : Blo 243817 247383 := bstep (se 1 (by rfl) ⟨185537, by rfl⟩ : syracuseStep 247383 = 371075) B371075
theorem B247403 : Blo 243817 247403 := bstep (se 1 (by rfl) ⟨185552, by rfl⟩ : syracuseStep 247403 = 371105) B371105
theorem B247415 : Blo 243817 247415 := bstep (se 1 (by rfl) ⟨185561, by rfl⟩ : syracuseStep 247415 = 371123) B371123
theorem B247435 : Blo 243817 247435 := bstep (se 1 (by rfl) ⟨185576, by rfl⟩ : syracuseStep 247435 = 371153) B371153
theorem B247447 : Blo 243817 247447 := bstep (se 1 (by rfl) ⟨185585, by rfl⟩ : syracuseStep 247447 = 371171) B371171
theorem B247467 : Blo 243817 247467 := bstep (se 1 (by rfl) ⟨185600, by rfl⟩ : syracuseStep 247467 = 371201) B371201
theorem B247479 : Blo 243817 247479 := bstep (se 1 (by rfl) ⟨185609, by rfl⟩ : syracuseStep 247479 = 371219) B371219
theorem B247499 : Blo 243817 247499 := bstep (se 1 (by rfl) ⟨185624, by rfl⟩ : syracuseStep 247499 = 371249) B371249
theorem B247511 : Blo 243817 247511 := bstep (se 1 (by rfl) ⟨185633, by rfl⟩ : syracuseStep 247511 = 371267) B371267
theorem B247531 : Blo 243817 247531 := bstep (se 1 (by rfl) ⟨185648, by rfl⟩ : syracuseStep 247531 = 371297) B371297
theorem B247543 : Blo 243817 247543 := bstep (se 1 (by rfl) ⟨185657, by rfl⟩ : syracuseStep 247543 = 371315) B371315
theorem B247563 : Blo 243817 247563 := bstep (se 1 (by rfl) ⟨185672, by rfl⟩ : syracuseStep 247563 = 371345) B371345
theorem B247575 : Blo 243817 247575 := bstep (se 1 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 247575 = 371363) B371363
theorem B247595 : Blo 243817 247595 := bstep (se 1 (by rfl) ⟨185696, by rfl⟩ : syracuseStep 247595 = 371393) B371393
theorem B247607 : Blo 243817 247607 := bstep (se 1 (by rfl) ⟨185705, by rfl⟩ : syracuseStep 247607 = 371411) B371411
theorem B247627 : Blo 243817 247627 := bstep (se 1 (by rfl) ⟨185720, by rfl⟩ : syracuseStep 247627 = 371441) B371441
theorem B247639 : Blo 243817 247639 := bstep (se 1 (by rfl) ⟨185729, by rfl⟩ : syracuseStep 247639 = 371459) B371459
theorem B3131237 : Blo 243817 3131237 := bstep (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) B587107
theorem B247659 : Blo 243817 247659 := bstep (se 1 (by rfl) ⟨185744, by rfl⟩ : syracuseStep 247659 = 371489) B371489
theorem B247671 : Blo 243817 247671 := bstep (se 1 (by rfl) ⟨185753, by rfl⟩ : syracuseStep 247671 = 371507) B371507
theorem B247691 : Blo 243817 247691 := bstep (se 1 (by rfl) ⟨185768, by rfl⟩ : syracuseStep 247691 = 371537) B371537
theorem B247703 : Blo 243817 247703 := bstep (se 1 (by rfl) ⟨185777, by rfl⟩ : syracuseStep 247703 = 371555) B371555
theorem B247723 : Blo 243817 247723 := bstep (se 1 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 247723 = 371585) B371585
theorem B247735 : Blo 243817 247735 := bstep (se 1 (by rfl) ⟨185801, by rfl⟩ : syracuseStep 247735 = 371603) B371603
theorem B247755 : Blo 243817 247755 := bstep (se 1 (by rfl) ⟨185816, by rfl⟩ : syracuseStep 247755 = 371633) B371633
theorem B313303 : Blo 243817 313303 := bstep (se 1 (by rfl) ⟨234977, by rfl⟩ : syracuseStep 313303 = 469955) B469955
theorem B247767 : Blo 243817 247767 := bstep (se 1 (by rfl) ⟨185825, by rfl⟩ : syracuseStep 247767 = 371651) B371651
theorem B247787 : Blo 243817 247787 := bstep (se 1 (by rfl) ⟨185840, by rfl⟩ : syracuseStep 247787 = 371681) B371681
theorem B247799 : Blo 243817 247799 := bstep (se 1 (by rfl) ⟨185849, by rfl⟩ : syracuseStep 247799 = 371699) B371699
theorem B2508893 : Blo 243817 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B1427557 : Blo 243817 1427557 := bstep (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) B267667
theorem B411851 : Blo 243817 411851 := bstep (se 1 (by rfl) ⟨308888, by rfl⟩ : syracuseStep 411851 = 617777) B617777
theorem B936157 : Blo 243817 936157 := bstep (se 3 (by rfl) ⟨175529, by rfl⟩ : syracuseStep 936157 = 351059) B351059
theorem B248075 : Blo 243817 248075 := bstep (se 1 (by rfl) ⟨186056, by rfl⟩ : syracuseStep 248075 = 372113) B372113
theorem B2083117 : Blo 243817 2083117 := bstep (se 3 (by rfl) ⟨390584, by rfl⟩ : syracuseStep 2083117 = 781169) B781169
theorem B411979 : Blo 243817 411979 := bstep (se 1 (by rfl) ⟨308984, by rfl⟩ : syracuseStep 411979 = 617969) B617969
theorem B412121 : Blo 243817 412121 := bstep (se 2 (by rfl) ⟨154545, by rfl⟩ : syracuseStep 412121 = 309091) B309091
theorem B412249 : Blo 243817 412249 := bstep (se 2 (by rfl) ⟨154593, by rfl⟩ : syracuseStep 412249 = 309187) B309187
theorem B412823 : Blo 243817 412823 := bstep (se 1 (by rfl) ⟨309617, by rfl⟩ : syracuseStep 412823 = 619235) B619235
theorem B904385 : Blo 243817 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B412951 : Blo 243817 412951 := bstep (se 1 (by rfl) ⟨309713, by rfl⟩ : syracuseStep 412951 = 619427) B619427
theorem B839005 : Blo 243817 839005 := bstep (se 3 (by rfl) ⟨157313, by rfl⟩ : syracuseStep 839005 = 314627) B314627
theorem B839105 : Blo 243817 839105 := bstep (se 2 (by rfl) ⟨314664, by rfl⟩ : syracuseStep 839105 = 629329) B629329
theorem B937433 : Blo 243817 937433 := bstep (se 2 (by rfl) ⟨351537, by rfl⟩ : syracuseStep 937433 = 703075) B703075
theorem B2084453 : Blo 243817 2084453 := bstep (se 4 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 2084453 = 390835) B390835
theorem B1265453 : Blo 243817 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B413579 : Blo 243817 413579 := bstep (se 1 (by rfl) ⟨310184, by rfl⟩ : syracuseStep 413579 = 620369) B620369
theorem B446401 : Blo 243817 446401 := bstep (se 2 (by rfl) ⟨167400, by rfl⟩ : syracuseStep 446401 = 334801) B334801
theorem B413707 : Blo 243817 413707 := bstep (se 1 (by rfl) ⟨310280, by rfl⟩ : syracuseStep 413707 = 620561) B620561
theorem B413849 : Blo 243817 413849 := bstep (se 2 (by rfl) ⟨155193, by rfl⟩ : syracuseStep 413849 = 310387) B310387
theorem B2248883 : Blo 243817 2248883 := bstep (se 1 (by rfl) ⟨1686662, by rfl⟩ : syracuseStep 2248883 = 3373325) B3373325
theorem B413977 : Blo 243817 413977 := bstep (se 2 (by rfl) ⟨155241, by rfl⟩ : syracuseStep 413977 = 310483) B310483
theorem B610763 : Blo 243817 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B1495703 : Blo 243817 1495703 := bstep (se 1 (by rfl) ⟨1121777, by rfl⟩ : syracuseStep 1495703 = 2243555) B2243555
theorem B3134213 : Blo 243817 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B414551 : Blo 243817 414551 := bstep (se 1 (by rfl) ⟨310913, by rfl⟩ : syracuseStep 414551 = 621827) B621827
theorem B938945 : Blo 243817 938945 := bstep (se 2 (by rfl) ⟨352104, by rfl⟩ : syracuseStep 938945 = 704209) B704209
theorem B414679 : Blo 243817 414679 := bstep (se 1 (by rfl) ⟨311009, by rfl⟩ : syracuseStep 414679 = 622019) B622019
theorem B939059 : Blo 243817 939059 := bstep (se 1 (by rfl) ⟨704294, by rfl⟩ : syracuseStep 939059 = 1408589) B1408589
theorem B939073 : Blo 243817 939073 := bstep (se 2 (by rfl) ⟨352152, by rfl⟩ : syracuseStep 939073 = 704305) B704305
theorem B742621 : Blo 243817 742621 := bstep (se 3 (by rfl) ⟨139241, by rfl⟩ : syracuseStep 742621 = 278483) B278483
theorem B710039 : Blo 243817 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B480755 : Blo 243817 480755 := bstep (se 1 (by rfl) ⟨360566, by rfl⟩ : syracuseStep 480755 = 721133) B721133
theorem B415307 : Blo 243817 415307 := bstep (se 1 (by rfl) ⟨311480, by rfl⟩ : syracuseStep 415307 = 622961) B622961
theorem B808537 : Blo 243817 808537 := bstep (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) B606403
theorem B415435 : Blo 243817 415435 := bstep (se 1 (by rfl) ⟨311576, by rfl⟩ : syracuseStep 415435 = 623153) B623153
theorem B1234763 : Blo 243817 1234763 := bstep (se 1 (by rfl) ⟨926072, by rfl⟩ : syracuseStep 1234763 = 1852145) B1852145
theorem B415577 : Blo 243817 415577 := bstep (se 2 (by rfl) ⟨155841, by rfl⟩ : syracuseStep 415577 = 311683) B311683
theorem B2676581 : Blo 243817 2676581 := bstep (se 4 (by rfl) ⟨250929, by rfl⟩ : syracuseStep 2676581 = 501859) B501859
theorem B415705 : Blo 243817 415705 := bstep (se 2 (by rfl) ⟨155889, by rfl⟩ : syracuseStep 415705 = 311779) B311779
theorem B1399133 : Blo 243817 1399133 := bstep (se 3 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 1399133 = 524675) B524675
theorem B5986709 : Blo 243817 5986709 := bstep (se 6 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 5986709 = 280627) B280627
theorem B350615 : Blo 243817 350615 := bstep (se 1 (by rfl) ⟨262961, by rfl⟩ : syracuseStep 350615 = 525923) B525923
theorem B416279 : Blo 243817 416279 := bstep (se 1 (by rfl) ⟨312209, by rfl⟩ : syracuseStep 416279 = 624419) B624419
theorem B4381253 : Blo 243817 4381253 := bstep (se 4 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 4381253 = 821485) B821485
theorem B416407 : Blo 243817 416407 := bstep (se 1 (by rfl) ⟨312305, by rfl⟩ : syracuseStep 416407 = 624611) B624611
theorem B449497 : Blo 243817 449497 := bstep (se 2 (by rfl) ⟨168561, by rfl⟩ : syracuseStep 449497 = 337123) B337123
theorem B842827 : Blo 243817 842827 := bstep (se 1 (by rfl) ⟨632120, by rfl⟩ : syracuseStep 842827 = 1264241) B1264241
theorem B417035 : Blo 243817 417035 := bstep (se 1 (by rfl) ⟨312776, by rfl⟩ : syracuseStep 417035 = 625553) B625553
theorem B417163 : Blo 243817 417163 := bstep (se 1 (by rfl) ⟨312872, by rfl⟩ : syracuseStep 417163 = 625745) B625745
theorem B417305 : Blo 243817 417305 := bstep (se 2 (by rfl) ⟨156489, by rfl⟩ : syracuseStep 417305 = 312979) B312979
theorem B1236545 : Blo 243817 1236545 := bstep (se 2 (by rfl) ⟨463704, by rfl⟩ : syracuseStep 1236545 = 927409) B927409
theorem B417433 : Blo 243817 417433 := bstep (se 2 (by rfl) ⟨156537, by rfl⟩ : syracuseStep 417433 = 313075) B313075
theorem B548747 : Blo 243817 548747 := bstep (se 1 (by rfl) ⟨411560, by rfl⟩ : syracuseStep 548747 = 823121) B823121
theorem B1564595 : Blo 243817 1564595 := bstep (se 1 (by rfl) ⟨1173446, by rfl⟩ : syracuseStep 1564595 = 2346893) B2346893
theorem B548801 : Blo 243817 548801 := bstep (se 2 (by rfl) ⟨205800, by rfl⟩ : syracuseStep 548801 = 411601) B411601
theorem B549017 : Blo 243817 549017 := bstep (se 2 (by rfl) ⟨205881, by rfl⟩ : syracuseStep 549017 = 411763) B411763
theorem B418007 : Blo 243817 418007 := bstep (se 1 (by rfl) ⟨313505, by rfl⟩ : syracuseStep 418007 = 627011) B627011
theorem B549107 : Blo 243817 549107 := bstep (se 1 (by rfl) ⟨411830, by rfl⟩ : syracuseStep 549107 = 823661) B823661
theorem B549143 : Blo 243817 549143 := bstep (se 1 (by rfl) ⟨411857, by rfl⟩ : syracuseStep 549143 = 823715) B823715
theorem B450841 : Blo 243817 450841 := bstep (se 2 (by rfl) ⟨169065, by rfl⟩ : syracuseStep 450841 = 338131) B338131
theorem B418135 : Blo 243817 418135 := bstep (se 1 (by rfl) ⟨313601, by rfl⟩ : syracuseStep 418135 = 627203) B627203
theorem B549323 : Blo 243817 549323 := bstep (se 1 (by rfl) ⟨411992, by rfl⟩ : syracuseStep 549323 = 823985) B823985
theorem B549377 : Blo 243817 549377 := bstep (se 2 (by rfl) ⟨206016, by rfl⟩ : syracuseStep 549377 = 412033) B412033
theorem B549593 : Blo 243817 549593 := bstep (se 2 (by rfl) ⟨206097, by rfl⟩ : syracuseStep 549593 = 412195) B412195
theorem B549683 : Blo 243817 549683 := bstep (se 1 (by rfl) ⟨412262, by rfl⟩ : syracuseStep 549683 = 824525) B824525
theorem B549719 : Blo 243817 549719 := bstep (se 1 (by rfl) ⟨412289, by rfl⟩ : syracuseStep 549719 = 824579) B824579
theorem B1401731 : Blo 243817 1401731 := bstep (se 1 (by rfl) ⟨1051298, by rfl⟩ : syracuseStep 1401731 = 2102597) B2102597
theorem B549899 : Blo 243817 549899 := bstep (se 1 (by rfl) ⟨412424, by rfl⟩ : syracuseStep 549899 = 824849) B824849
theorem B549953 : Blo 243817 549953 := bstep (se 2 (by rfl) ⟨206232, by rfl⟩ : syracuseStep 549953 = 412465) B412465
theorem B746561 : Blo 243817 746561 := bstep (se 2 (by rfl) ⟨279960, by rfl⟩ : syracuseStep 746561 = 559921) B559921
theorem B3531869 : Blo 243817 3531869 := bstep (se 3 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 3531869 = 1324451) B1324451
theorem B746647 : Blo 243817 746647 := bstep (se 1 (by rfl) ⟨559985, by rfl⟩ : syracuseStep 746647 = 1119971) B1119971
theorem B550169 : Blo 243817 550169 := bstep (se 2 (by rfl) ⟨206313, by rfl⟩ : syracuseStep 550169 = 412627) B412627
theorem B550259 : Blo 243817 550259 := bstep (se 1 (by rfl) ⟨412694, by rfl⟩ : syracuseStep 550259 = 825389) B825389
theorem B550295 : Blo 243817 550295 := bstep (se 1 (by rfl) ⟨412721, by rfl⟩ : syracuseStep 550295 = 825443) B825443
theorem B1238489 : Blo 243817 1238489 := bstep (se 2 (by rfl) ⟨464433, by rfl⟩ : syracuseStep 1238489 = 928867) B928867
theorem B6743569 : Blo 243817 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B550475 : Blo 243817 550475 := bstep (se 1 (by rfl) ⟨412856, by rfl⟩ : syracuseStep 550475 = 825713) B825713
theorem B1336907 : Blo 243817 1336907 := bstep (se 1 (by rfl) ⟨1002680, by rfl⟩ : syracuseStep 1336907 = 2005361) B2005361
theorem B550529 : Blo 243817 550529 := bstep (se 2 (by rfl) ⟨206448, by rfl⟩ : syracuseStep 550529 = 412897) B412897
theorem B550745 : Blo 243817 550745 := bstep (se 2 (by rfl) ⟨206529, by rfl⟩ : syracuseStep 550745 = 413059) B413059
theorem B550835 : Blo 243817 550835 := bstep (se 1 (by rfl) ⟨413126, by rfl⟩ : syracuseStep 550835 = 826253) B826253
theorem B1042379 : Blo 243817 1042379 := bstep (se 1 (by rfl) ⟨781784, by rfl⟩ : syracuseStep 1042379 = 1563569) B1563569
theorem B550871 : Blo 243817 550871 := bstep (se 1 (by rfl) ⟨413153, by rfl⟩ : syracuseStep 550871 = 826307) B826307
theorem B551051 : Blo 243817 551051 := bstep (se 1 (by rfl) ⟨413288, by rfl⟩ : syracuseStep 551051 = 826577) B826577
theorem B551105 : Blo 243817 551105 := bstep (se 2 (by rfl) ⟨206664, by rfl⟩ : syracuseStep 551105 = 413329) B413329
theorem B1927385 : Blo 243817 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B551321 : Blo 243817 551321 := bstep (se 2 (by rfl) ⟨206745, by rfl⟩ : syracuseStep 551321 = 413491) B413491
theorem B551411 : Blo 243817 551411 := bstep (se 1 (by rfl) ⟨413558, by rfl⟩ : syracuseStep 551411 = 827117) B827117
theorem B551447 : Blo 243817 551447 := bstep (se 1 (by rfl) ⟨413585, by rfl⟩ : syracuseStep 551447 = 827171) B827171
theorem B2845277 : Blo 243817 2845277 := bstep (se 3 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 2845277 = 1066979) B1066979
theorem B879277 : Blo 243817 879277 := bstep (se 3 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 879277 = 329729) B329729
theorem B551627 : Blo 243817 551627 := bstep (se 1 (by rfl) ⟨413720, by rfl⟩ : syracuseStep 551627 = 827441) B827441
theorem B551681 : Blo 243817 551681 := bstep (se 2 (by rfl) ⟨206880, by rfl⟩ : syracuseStep 551681 = 413761) B413761
theorem B617291 : Blo 243817 617291 := bstep (se 1 (by rfl) ⟨462968, by rfl⟩ : syracuseStep 617291 = 925937) B925937
theorem B551897 : Blo 243817 551897 := bstep (se 2 (by rfl) ⟨206961, by rfl⟩ : syracuseStep 551897 = 413923) B413923
theorem B1240109 : Blo 243817 1240109 := bstep (se 3 (by rfl) ⟨232520, by rfl⟩ : syracuseStep 1240109 = 465041) B465041
theorem B551987 : Blo 243817 551987 := bstep (se 1 (by rfl) ⟨413990, by rfl⟩ : syracuseStep 551987 = 827981) B827981
theorem B552023 : Blo 243817 552023 := bstep (se 1 (by rfl) ⟨414017, by rfl⟩ : syracuseStep 552023 = 828035) B828035
theorem B617665 : Blo 243817 617665 := bstep (se 2 (by rfl) ⟨231624, by rfl⟩ : syracuseStep 617665 = 463249) B463249
theorem B552203 : Blo 243817 552203 := bstep (se 1 (by rfl) ⟨414152, by rfl⟩ : syracuseStep 552203 = 828305) B828305
theorem B1174829 : Blo 243817 1174829 := bstep (se 3 (by rfl) ⟨220280, by rfl⟩ : syracuseStep 1174829 = 440561) B440561
theorem B552257 : Blo 243817 552257 := bstep (se 2 (by rfl) ⟨207096, by rfl⟩ : syracuseStep 552257 = 414193) B414193
theorem B814429 : Blo 243817 814429 := bstep (se 3 (by rfl) ⟨152705, by rfl⟩ : syracuseStep 814429 = 305411) B305411
theorem B552473 : Blo 243817 552473 := bstep (se 2 (by rfl) ⟨207177, by rfl⟩ : syracuseStep 552473 = 414355) B414355
theorem B1764899 : Blo 243817 1764899 := bstep (se 1 (by rfl) ⟨1323674, by rfl⟩ : syracuseStep 1764899 = 2647349) B2647349
theorem B1044019 : Blo 243817 1044019 := bstep (se 1 (by rfl) ⟨783014, by rfl⟩ : syracuseStep 1044019 = 1566029) B1566029
theorem B781913 : Blo 243817 781913 := bstep (se 2 (by rfl) ⟨293217, by rfl⟩ : syracuseStep 781913 = 586435) B586435
theorem B1601117 : Blo 243817 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B552563 : Blo 243817 552563 := bstep (se 1 (by rfl) ⟨414422, by rfl⟩ : syracuseStep 552563 = 828845) B828845
theorem B552599 : Blo 243817 552599 := bstep (se 1 (by rfl) ⟨414449, by rfl⟩ : syracuseStep 552599 = 828899) B828899
theorem B421529 : Blo 243817 421529 := bstep (se 2 (by rfl) ⟨158073, by rfl⟩ : syracuseStep 421529 = 316147) B316147
theorem B618263 : Blo 243817 618263 := bstep (se 1 (by rfl) ⟨463697, by rfl⟩ : syracuseStep 618263 = 927395) B927395
theorem B3534637 : Blo 243817 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B552779 : Blo 243817 552779 := bstep (se 1 (by rfl) ⟨414584, by rfl⟩ : syracuseStep 552779 = 829169) B829169
theorem B552833 : Blo 243817 552833 := bstep (se 2 (by rfl) ⟨207312, by rfl⟩ : syracuseStep 552833 = 414625) B414625
theorem B1863575 : Blo 243817 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B880577 : Blo 243817 880577 := bstep (se 2 (by rfl) ⟨330216, by rfl⟩ : syracuseStep 880577 = 660433) B660433
theorem B553049 : Blo 243817 553049 := bstep (se 2 (by rfl) ⟨207393, by rfl⟩ : syracuseStep 553049 = 414787) B414787
theorem B1568899 : Blo 243817 1568899 := bstep (se 1 (by rfl) ⟨1176674, by rfl⟩ : syracuseStep 1568899 = 2353349) B2353349
theorem B946349 : Blo 243817 946349 := bstep (se 3 (by rfl) ⟨177440, by rfl⟩ : syracuseStep 946349 = 354881) B354881
theorem B553139 : Blo 243817 553139 := bstep (se 1 (by rfl) ⟨414854, by rfl⟩ : syracuseStep 553139 = 829709) B829709
theorem B553175 : Blo 243817 553175 := bstep (se 1 (by rfl) ⟨414881, by rfl⟩ : syracuseStep 553175 = 829763) B829763
theorem B553355 : Blo 243817 553355 := bstep (se 1 (by rfl) ⟨415016, by rfl⟩ : syracuseStep 553355 = 830033) B830033
theorem B553409 : Blo 243817 553409 := bstep (se 2 (by rfl) ⟨207528, by rfl⟩ : syracuseStep 553409 = 415057) B415057
theorem B619073 : Blo 243817 619073 := bstep (se 2 (by rfl) ⟨232152, by rfl⟩ : syracuseStep 619073 = 464305) B464305
theorem B553625 : Blo 243817 553625 := bstep (se 2 (by rfl) ⟨207609, by rfl⟩ : syracuseStep 553625 = 415219) B415219
theorem B750259 : Blo 243817 750259 := bstep (se 1 (by rfl) ⟨562694, by rfl⟩ : syracuseStep 750259 = 1125389) B1125389
theorem B422617 : Blo 243817 422617 := bstep (se 2 (by rfl) ⟨158481, by rfl⟩ : syracuseStep 422617 = 316963) B316963
theorem B553715 : Blo 243817 553715 := bstep (se 1 (by rfl) ⟨415286, by rfl⟩ : syracuseStep 553715 = 830573) B830573
theorem B553751 : Blo 243817 553751 := bstep (se 1 (by rfl) ⟨415313, by rfl⟩ : syracuseStep 553751 = 830627) B830627
theorem B520985 : Blo 243817 520985 := bstep (se 2 (by rfl) ⟨195369, by rfl⟩ : syracuseStep 520985 = 390739) B390739
theorem B586561 : Blo 243817 586561 := bstep (se 2 (by rfl) ⟨219960, by rfl⟩ : syracuseStep 586561 = 439921) B439921
theorem B5370725 : Blo 243817 5370725 := bstep (se 4 (by rfl) ⟨503505, by rfl⟩ : syracuseStep 5370725 = 1007011) B1007011
theorem B4027315 : Blo 243817 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B553931 : Blo 243817 553931 := bstep (se 1 (by rfl) ⟨415448, by rfl⟩ : syracuseStep 553931 = 830897) B830897
theorem B553985 : Blo 243817 553985 := bstep (se 2 (by rfl) ⟨207744, by rfl⟩ : syracuseStep 553985 = 415489) B415489
theorem B1045507 : Blo 243817 1045507 := bstep (se 1 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 1045507 = 1568261) B1568261
theorem B783425 : Blo 243817 783425 := bstep (se 2 (by rfl) ⟨293784, by rfl⟩ : syracuseStep 783425 = 587569) B587569
theorem B619609 : Blo 243817 619609 := bstep (se 2 (by rfl) ⟨232353, by rfl⟩ : syracuseStep 619609 = 464707) B464707
theorem B554201 : Blo 243817 554201 := bstep (se 2 (by rfl) ⟨207825, by rfl⟩ : syracuseStep 554201 = 415651) B415651
theorem B554291 : Blo 243817 554291 := bstep (se 1 (by rfl) ⟨415718, by rfl⟩ : syracuseStep 554291 = 831437) B831437
theorem B554327 : Blo 243817 554327 := bstep (se 1 (by rfl) ⟨415745, by rfl⟩ : syracuseStep 554327 = 831491) B831491
theorem B750941 : Blo 243817 750941 := bstep (se 3 (by rfl) ⟨140801, by rfl⟩ : syracuseStep 750941 = 281603) B281603
theorem B1176983 : Blo 243817 1176983 := bstep (se 1 (by rfl) ⟨882737, by rfl⟩ : syracuseStep 1176983 = 1765475) B1765475
theorem B554507 : Blo 243817 554507 := bstep (se 1 (by rfl) ⟨415880, by rfl⟩ : syracuseStep 554507 = 831761) B831761
theorem B554561 : Blo 243817 554561 := bstep (se 2 (by rfl) ⟨207960, by rfl⟩ : syracuseStep 554561 = 415921) B415921
theorem B1046105 : Blo 243817 1046105 := bstep (se 2 (by rfl) ⟨392289, by rfl⟩ : syracuseStep 1046105 = 784579) B784579
theorem B1767089 : Blo 243817 1767089 := bstep (se 2 (by rfl) ⟨662658, by rfl⟩ : syracuseStep 1767089 = 1325317) B1325317
theorem B554777 : Blo 243817 554777 := bstep (se 2 (by rfl) ⟨208041, by rfl⟩ : syracuseStep 554777 = 416083) B416083
theorem B554867 : Blo 243817 554867 := bstep (se 1 (by rfl) ⟨416150, by rfl⟩ : syracuseStep 554867 = 832301) B832301
theorem B554903 : Blo 243817 554903 := bstep (se 1 (by rfl) ⟨416177, by rfl⟩ : syracuseStep 554903 = 832355) B832355
theorem B1898417 : Blo 243817 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B1177523 : Blo 243817 1177523 := bstep (se 1 (by rfl) ⟨883142, by rfl⟩ : syracuseStep 1177523 = 1766285) B1766285
theorem B1046465 : Blo 243817 1046465 := bstep (se 2 (by rfl) ⟨392424, by rfl⟩ : syracuseStep 1046465 = 784849) B784849
theorem B555083 : Blo 243817 555083 := bstep (se 1 (by rfl) ⟨416312, by rfl⟩ : syracuseStep 555083 = 832625) B832625
theorem B555137 : Blo 243817 555137 := bstep (se 2 (by rfl) ⟨208176, by rfl⟩ : syracuseStep 555137 = 416353) B416353
theorem B6715543 : Blo 243817 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B620723 : Blo 243817 620723 := bstep (se 1 (by rfl) ⟨465542, by rfl⟩ : syracuseStep 620723 = 931085) B931085
theorem B588107 : Blo 243817 588107 := bstep (se 1 (by rfl) ⟨441080, by rfl⟩ : syracuseStep 588107 = 882161) B882161
theorem B555353 : Blo 243817 555353 := bstep (se 2 (by rfl) ⟨208257, by rfl⟩ : syracuseStep 555353 = 416515) B416515
theorem B522625 : Blo 243817 522625 := bstep (se 2 (by rfl) ⟨195984, by rfl⟩ : syracuseStep 522625 = 391969) B391969
theorem B555443 : Blo 243817 555443 := bstep (se 1 (by rfl) ⟨416582, by rfl⟩ : syracuseStep 555443 = 833165) B833165
theorem B555479 : Blo 243817 555479 := bstep (se 1 (by rfl) ⟨416609, by rfl⟩ : syracuseStep 555479 = 833219) B833219
theorem B621017 : Blo 243817 621017 := bstep (se 2 (by rfl) ⟨232881, by rfl⟩ : syracuseStep 621017 = 465763) B465763
theorem B260663 : Blo 243817 260663 := bstep (se 1 (by rfl) ⟨195497, by rfl⟩ : syracuseStep 260663 = 390995) B390995
theorem B1407563 : Blo 243817 1407563 := bstep (se 1 (by rfl) ⟨1055672, by rfl⟩ : syracuseStep 1407563 = 2111345) B2111345
theorem B555659 : Blo 243817 555659 := bstep (se 1 (by rfl) ⟨416744, by rfl⟩ : syracuseStep 555659 = 833489) B833489
theorem B555713 : Blo 243817 555713 := bstep (se 2 (by rfl) ⟨208392, by rfl⟩ : syracuseStep 555713 = 416785) B416785
theorem B359257 : Blo 243817 359257 := bstep (se 2 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 359257 = 269443) B269443
theorem B1243997 : Blo 243817 1243997 := bstep (se 3 (by rfl) ⟨233249, by rfl⟩ : syracuseStep 1243997 = 466499) B466499
theorem B555929 : Blo 243817 555929 := bstep (se 2 (by rfl) ⟨208473, by rfl⟩ : syracuseStep 555929 = 416947) B416947
theorem B556019 : Blo 243817 556019 := bstep (se 1 (by rfl) ⟨417014, by rfl⟩ : syracuseStep 556019 = 834029) B834029
theorem B556055 : Blo 243817 556055 := bstep (se 1 (by rfl) ⟨417041, by rfl⟩ : syracuseStep 556055 = 834083) B834083
theorem B556235 : Blo 243817 556235 := bstep (se 1 (by rfl) ⟨417176, by rfl⟩ : syracuseStep 556235 = 834353) B834353
theorem B785629 : Blo 243817 785629 := bstep (se 3 (by rfl) ⟨147305, by rfl⟩ : syracuseStep 785629 = 294611) B294611
theorem B556289 : Blo 243817 556289 := bstep (se 2 (by rfl) ⟨208608, by rfl⟩ : syracuseStep 556289 = 417217) B417217
theorem B556505 : Blo 243817 556505 := bstep (se 2 (by rfl) ⟨208689, by rfl⟩ : syracuseStep 556505 = 417379) B417379
theorem B556595 : Blo 243817 556595 := bstep (se 1 (by rfl) ⟨417446, by rfl⟩ : syracuseStep 556595 = 834893) B834893
theorem B556631 : Blo 243817 556631 := bstep (se 1 (by rfl) ⟨417473, by rfl⟩ : syracuseStep 556631 = 834947) B834947
theorem B1769165 : Blo 243817 1769165 := bstep (se 3 (by rfl) ⟨331718, by rfl⟩ : syracuseStep 1769165 = 663437) B663437
theorem B556811 : Blo 243817 556811 := bstep (se 1 (by rfl) ⟨417608, by rfl⟩ : syracuseStep 556811 = 835217) B835217
theorem B556865 : Blo 243817 556865 := bstep (se 2 (by rfl) ⟨208824, by rfl⟩ : syracuseStep 556865 = 417649) B417649
theorem B1867697 : Blo 243817 1867697 := bstep (se 2 (by rfl) ⟨700386, by rfl⟩ : syracuseStep 1867697 = 1400773) B1400773
theorem B1015769 : Blo 243817 1015769 := bstep (se 2 (by rfl) ⟨380913, by rfl⟩ : syracuseStep 1015769 = 761827) B761827
theorem B557099 : Blo 243817 557099 := bstep (se 1 (by rfl) ⟨417824, by rfl⟩ : syracuseStep 557099 = 835649) B835649
theorem B622849 : Blo 243817 622849 := bstep (se 2 (by rfl) ⟨233568, by rfl⟩ : syracuseStep 622849 = 467137) B467137
theorem B1245455 : Blo 243817 1245455 := bstep (se 1 (by rfl) ⟨934091, by rfl⟩ : syracuseStep 1245455 = 1868183) B1868183
theorem B1409339 : Blo 243817 1409339 := bstep (se 1 (by rfl) ⟨1057004, by rfl⟩ : syracuseStep 1409339 = 2114009) B2114009
theorem B557459 : Blo 243817 557459 := bstep (se 1 (by rfl) ⟨418094, by rfl⟩ : syracuseStep 557459 = 836189) B836189
theorem B557513 : Blo 243817 557513 := bstep (se 2 (by rfl) ⟨209067, by rfl⟩ : syracuseStep 557513 = 418135) B418135
theorem B10584533 : Blo 243817 10584533 := bstep (se 7 (by rfl) ⟨124037, by rfl⟩ : syracuseStep 10584533 = 248075) B248075
theorem B1999363 : Blo 243817 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B590483 : Blo 243817 590483 := bstep (se 1 (by rfl) ⟨442862, by rfl⟩ : syracuseStep 590483 = 885725) B885725
theorem B885505 : Blo 243817 885505 := bstep (se 2 (by rfl) ⟨332064, by rfl⟩ : syracuseStep 885505 = 664129) B664129
theorem B623447 : Blo 243817 623447 := bstep (se 1 (by rfl) ⟨467585, by rfl⟩ : syracuseStep 623447 = 935171) B935171
theorem B1278929 : Blo 243817 1278929 := bstep (se 2 (by rfl) ⟨479598, by rfl⟩ : syracuseStep 1278929 = 959197) B959197
theorem B754703 : Blo 243817 754703 := bstep (se 1 (by rfl) ⟨566027, by rfl⟩ : syracuseStep 754703 = 1132055) B1132055
theorem B623659 : Blo 243817 623659 := bstep (se 1 (by rfl) ⟨467744, by rfl⟩ : syracuseStep 623659 = 935489) B935489
theorem B623801 : Blo 243817 623801 := bstep (se 2 (by rfl) ⟨233925, by rfl⟩ : syracuseStep 623801 = 467851) B467851
theorem B263431 : Blo 243817 263431 := bstep (se 1 (by rfl) ⟨197573, by rfl⟩ : syracuseStep 263431 = 395147) B395147
theorem B1672595 : Blo 243817 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B263611 : Blo 243817 263611 := bstep (se 1 (by rfl) ⟨197708, by rfl⟩ : syracuseStep 263611 = 395417) B395417
theorem B1181213 : Blo 243817 1181213 := bstep (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) B442955
theorem B886301 : Blo 243817 886301 := bstep (se 3 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 886301 = 332363) B332363
theorem B1050155 : Blo 243817 1050155 := bstep (se 1 (by rfl) ⟨787616, by rfl⟩ : syracuseStep 1050155 = 1575233) B1575233
theorem B1246913 : Blo 243817 1246913 := bstep (se 2 (by rfl) ⟨467592, by rfl⟩ : syracuseStep 1246913 = 935185) B935185
theorem B1410797 : Blo 243817 1410797 := bstep (se 3 (by rfl) ⟨264524, by rfl⟩ : syracuseStep 1410797 = 529049) B529049
theorem B624793 : Blo 243817 624793 := bstep (se 2 (by rfl) ⟨234297, by rfl⟩ : syracuseStep 624793 = 468595) B468595
theorem B559403 : Blo 243817 559403 := bstep (se 1 (by rfl) ⟨419552, by rfl⟩ : syracuseStep 559403 = 839105) B839105
theorem B624955 : Blo 243817 624955 := bstep (se 1 (by rfl) ⟨468716, by rfl⟩ : syracuseStep 624955 = 937433) B937433
theorem B395705 : Blo 243817 395705 := bstep (se 2 (by rfl) ⟨148389, by rfl⟩ : syracuseStep 395705 = 296779) B296779
theorem B625097 : Blo 243817 625097 := bstep (se 2 (by rfl) ⟨234411, by rfl⟩ : syracuseStep 625097 = 468823) B468823
theorem B527033 : Blo 243817 527033 := bstep (se 2 (by rfl) ⟨197637, by rfl⟩ : syracuseStep 527033 = 395275) B395275
theorem B625441 : Blo 243817 625441 := bstep (se 2 (by rfl) ⟨234540, by rfl⟩ : syracuseStep 625441 = 469081) B469081
theorem B1903409 : Blo 243817 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B1248209 : Blo 243817 1248209 := bstep (se 2 (by rfl) ⟨468078, by rfl⟩ : syracuseStep 1248209 = 936157) B936157
theorem B625963 : Blo 243817 625963 := bstep (se 1 (by rfl) ⟨469472, by rfl⟩ : syracuseStep 625963 = 938945) B938945
theorem B626039 : Blo 243817 626039 := bstep (se 1 (by rfl) ⟨469529, by rfl⟩ : syracuseStep 626039 = 939059) B939059
theorem B396679 : Blo 243817 396679 := bstep (se 1 (by rfl) ⟨297509, by rfl⟩ : syracuseStep 396679 = 595019) B595019
theorem B527887 : Blo 243817 527887 := bstep (se 1 (by rfl) ⟨395915, by rfl⟩ : syracuseStep 527887 = 791831) B791831
theorem B823175 : Blo 243817 823175 := bstep (se 1 (by rfl) ⟨617381, by rfl⟩ : syracuseStep 823175 = 1234763) B1234763
theorem B1183673 : Blo 243817 1183673 := bstep (se 2 (by rfl) ⟨443877, by rfl⟩ : syracuseStep 1183673 = 887755) B887755
theorem B594067 : Blo 243817 594067 := bstep (se 1 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 594067 = 891101) B891101
theorem B823553 : Blo 243817 823553 := bstep (se 2 (by rfl) ⟨308832, by rfl⟩ : syracuseStep 823553 = 617665) B617665
theorem B5017949 : Blo 243817 5017949 := bstep (se 3 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 5017949 = 1881731) B1881731
theorem B2920835 : Blo 243817 2920835 := bstep (se 1 (by rfl) ⟨2190626, by rfl⟩ : syracuseStep 2920835 = 4381253) B4381253
theorem B1085905 : Blo 243817 1085905 := bstep (se 2 (by rfl) ⟨407214, by rfl⟩ : syracuseStep 1085905 = 814429) B814429
theorem B2036267 : Blo 243817 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B6754859 : Blo 243817 6754859 := bstep (se 1 (by rfl) ⟨5066144, by rfl⟩ : syracuseStep 6754859 = 10132289) B10132289
theorem B4789007 : Blo 243817 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B463735 : Blo 243817 463735 := bstep (se 1 (by rfl) ⟨347801, by rfl⟩ : syracuseStep 463735 = 695603) B695603
theorem B1053587 : Blo 243817 1053587 := bstep (se 1 (by rfl) ⟨790190, by rfl⟩ : syracuseStep 1053587 = 1580381) B1580381
theorem B1250315 : Blo 243817 1250315 := bstep (se 1 (by rfl) ⟨937736, by rfl⟩ : syracuseStep 1250315 = 1875473) B1875473
theorem B824363 : Blo 243817 824363 := bstep (se 1 (by rfl) ⟨618272, by rfl⟩ : syracuseStep 824363 = 1236545) B1236545
theorem B1250477 : Blo 243817 1250477 := bstep (se 3 (by rfl) ⟨234464, by rfl⟩ : syracuseStep 1250477 = 468929) B468929
theorem B365753 : Blo 243817 365753 := bstep (se 2 (by rfl) ⟨137157, by rfl⟩ : syracuseStep 365753 = 274315) B274315
theorem B595201 : Blo 243817 595201 := bstep (se 2 (by rfl) ⟨223200, by rfl⟩ : syracuseStep 595201 = 446401) B446401
theorem B365831 : Blo 243817 365831 := bstep (se 1 (by rfl) ⟨274373, by rfl⟩ : syracuseStep 365831 = 548747) B548747
theorem B365867 : Blo 243817 365867 := bstep (se 1 (by rfl) ⟨274400, by rfl⟩ : syracuseStep 365867 = 548801) B548801
theorem B660797 : Blo 243817 660797 := bstep (se 3 (by rfl) ⟨123899, by rfl⟩ : syracuseStep 660797 = 247799) B247799
theorem B365897 : Blo 243817 365897 := bstep (se 2 (by rfl) ⟨137211, by rfl⟩ : syracuseStep 365897 = 274423) B274423
theorem B366011 : Blo 243817 366011 := bstep (se 1 (by rfl) ⟨274508, by rfl⟩ : syracuseStep 366011 = 549017) B549017
theorem B366071 : Blo 243817 366071 := bstep (se 1 (by rfl) ⟨274553, by rfl⟩ : syracuseStep 366071 = 549107) B549107
theorem B366095 : Blo 243817 366095 := bstep (se 1 (by rfl) ⟨274571, by rfl⟩ : syracuseStep 366095 = 549143) B549143
theorem B366137 : Blo 243817 366137 := bstep (se 2 (by rfl) ⟨137301, by rfl⟩ : syracuseStep 366137 = 274603) B274603
theorem B366215 : Blo 243817 366215 := bstep (se 1 (by rfl) ⟨274661, by rfl⟩ : syracuseStep 366215 = 549323) B549323
theorem B366251 : Blo 243817 366251 := bstep (se 1 (by rfl) ⟨274688, by rfl⟩ : syracuseStep 366251 = 549377) B549377
theorem B366281 : Blo 243817 366281 := bstep (se 2 (by rfl) ⟨137355, by rfl⟩ : syracuseStep 366281 = 274711) B274711
theorem B366395 : Blo 243817 366395 := bstep (se 1 (by rfl) ⟨274796, by rfl⟩ : syracuseStep 366395 = 549593) B549593
theorem B1054579 : Blo 243817 1054579 := bstep (se 1 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 1054579 = 1581869) B1581869
theorem B366455 : Blo 243817 366455 := bstep (se 1 (by rfl) ⟨274841, by rfl⟩ : syracuseStep 366455 = 549683) B549683
theorem B366479 : Blo 243817 366479 := bstep (se 1 (by rfl) ⟨274859, by rfl⟩ : syracuseStep 366479 = 549719) B549719
theorem B366521 : Blo 243817 366521 := bstep (se 2 (by rfl) ⟨137445, by rfl⟩ : syracuseStep 366521 = 274891) B274891
theorem B366599 : Blo 243817 366599 := bstep (se 1 (by rfl) ⟨274949, by rfl⟩ : syracuseStep 366599 = 549899) B549899
theorem B366635 : Blo 243817 366635 := bstep (se 1 (by rfl) ⟨274976, by rfl⟩ : syracuseStep 366635 = 549953) B549953
theorem B497707 : Blo 243817 497707 := bstep (se 1 (by rfl) ⟨373280, by rfl⟩ : syracuseStep 497707 = 746561) B746561
theorem B366665 : Blo 243817 366665 := bstep (se 2 (by rfl) ⟨137499, by rfl⟩ : syracuseStep 366665 = 274999) B274999
theorem B366779 : Blo 243817 366779 := bstep (se 1 (by rfl) ⟨275084, by rfl⟩ : syracuseStep 366779 = 550169) B550169
theorem B366839 : Blo 243817 366839 := bstep (se 1 (by rfl) ⟨275129, by rfl⟩ : syracuseStep 366839 = 550259) B550259
theorem B366863 : Blo 243817 366863 := bstep (se 1 (by rfl) ⟨275147, by rfl⟩ : syracuseStep 366863 = 550295) B550295
theorem B563489 : Blo 243817 563489 := bstep (se 2 (by rfl) ⟨211308, by rfl⟩ : syracuseStep 563489 = 422617) B422617
theorem B366905 : Blo 243817 366905 := bstep (se 2 (by rfl) ⟨137589, by rfl⟩ : syracuseStep 366905 = 275179) B275179
theorem B825659 : Blo 243817 825659 := bstep (se 1 (by rfl) ⟨619244, by rfl⟩ : syracuseStep 825659 = 1238489) B1238489
theorem B366983 : Blo 243817 366983 := bstep (se 1 (by rfl) ⟨275237, by rfl⟩ : syracuseStep 366983 = 550475) B550475
theorem B891271 : Blo 243817 891271 := bstep (se 1 (by rfl) ⟨668453, by rfl⟩ : syracuseStep 891271 = 1336907) B1336907
theorem B1579409 : Blo 243817 1579409 := bstep (se 2 (by rfl) ⟨592278, by rfl⟩ : syracuseStep 1579409 = 1184557) B1184557
theorem B792985 : Blo 243817 792985 := bstep (se 2 (by rfl) ⟨297369, by rfl⟩ : syracuseStep 792985 = 594739) B594739
theorem B367019 : Blo 243817 367019 := bstep (se 1 (by rfl) ⟨275264, by rfl⟩ : syracuseStep 367019 = 550529) B550529
theorem B367049 : Blo 243817 367049 := bstep (se 2 (by rfl) ⟨137643, by rfl⟩ : syracuseStep 367049 = 275287) B275287
theorem B367163 : Blo 243817 367163 := bstep (se 1 (by rfl) ⟨275372, by rfl⟩ : syracuseStep 367163 = 550745) B550745
theorem B367223 : Blo 243817 367223 := bstep (se 1 (by rfl) ⟨275417, by rfl⟩ : syracuseStep 367223 = 550835) B550835
theorem B465527 : Blo 243817 465527 := bstep (se 1 (by rfl) ⟨349145, by rfl⟩ : syracuseStep 465527 = 698291) B698291
theorem B694919 : Blo 243817 694919 := bstep (se 1 (by rfl) ⟨521189, by rfl⟩ : syracuseStep 694919 = 1042379) B1042379
theorem B367247 : Blo 243817 367247 := bstep (se 1 (by rfl) ⟨275435, by rfl⟩ : syracuseStep 367247 = 550871) B550871
theorem B367289 : Blo 243817 367289 := bstep (se 2 (by rfl) ⟨137733, by rfl⟩ : syracuseStep 367289 = 275467) B275467
theorem B1252097 : Blo 243817 1252097 := bstep (se 2 (by rfl) ⟨469536, by rfl⟩ : syracuseStep 1252097 = 939073) B939073
theorem B367367 : Blo 243817 367367 := bstep (se 1 (by rfl) ⟨275525, by rfl⟩ : syracuseStep 367367 = 551051) B551051
theorem B465679 : Blo 243817 465679 := bstep (se 1 (by rfl) ⟨349259, by rfl⟩ : syracuseStep 465679 = 698519) B698519
theorem B826145 : Blo 243817 826145 := bstep (se 2 (by rfl) ⟨309804, by rfl⟩ : syracuseStep 826145 = 619609) B619609
theorem B367403 : Blo 243817 367403 := bstep (se 1 (by rfl) ⟨275552, by rfl⟩ : syracuseStep 367403 = 551105) B551105
theorem B1284923 : Blo 243817 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B367433 : Blo 243817 367433 := bstep (se 2 (by rfl) ⟨137787, by rfl⟩ : syracuseStep 367433 = 275575) B275575
theorem B367547 : Blo 243817 367547 := bstep (se 1 (by rfl) ⟨275660, by rfl⟩ : syracuseStep 367547 = 551321) B551321
theorem B990161 : Blo 243817 990161 := bstep (se 2 (by rfl) ⟨371310, by rfl⟩ : syracuseStep 990161 = 742621) B742621
theorem B367607 : Blo 243817 367607 := bstep (se 1 (by rfl) ⟨275705, by rfl⟩ : syracuseStep 367607 = 551411) B551411
theorem B367631 : Blo 243817 367631 := bstep (se 1 (by rfl) ⟨275723, by rfl⟩ : syracuseStep 367631 = 551447) B551447
theorem B367673 : Blo 243817 367673 := bstep (se 2 (by rfl) ⟨137877, by rfl⟩ : syracuseStep 367673 = 275755) B275755
theorem B367751 : Blo 243817 367751 := bstep (se 1 (by rfl) ⟨275813, by rfl⟩ : syracuseStep 367751 = 551627) B551627
theorem B466067 : Blo 243817 466067 := bstep (se 1 (by rfl) ⟨349550, by rfl⟩ : syracuseStep 466067 = 699101) B699101
theorem B367787 : Blo 243817 367787 := bstep (se 1 (by rfl) ⟨275840, by rfl⟩ : syracuseStep 367787 = 551681) B551681
theorem B367817 : Blo 243817 367817 := bstep (se 2 (by rfl) ⟨137931, by rfl⟩ : syracuseStep 367817 = 275863) B275863
theorem B793871 : Blo 243817 793871 := bstep (se 1 (by rfl) ⟨595403, by rfl⟩ : syracuseStep 793871 = 1190807) B1190807
theorem B1187131 : Blo 243817 1187131 := bstep (se 1 (by rfl) ⟨890348, by rfl⟩ : syracuseStep 1187131 = 1780697) B1780697
theorem B367931 : Blo 243817 367931 := bstep (se 1 (by rfl) ⟨275948, by rfl⟩ : syracuseStep 367931 = 551897) B551897
theorem B826739 : Blo 243817 826739 := bstep (se 1 (by rfl) ⟨620054, by rfl⟩ : syracuseStep 826739 = 1240109) B1240109
theorem B367991 : Blo 243817 367991 := bstep (se 1 (by rfl) ⟨275993, by rfl⟩ : syracuseStep 367991 = 551987) B551987
theorem B368015 : Blo 243817 368015 := bstep (se 1 (by rfl) ⟨276011, by rfl⟩ : syracuseStep 368015 = 552023) B552023
theorem B368057 : Blo 243817 368057 := bstep (se 2 (by rfl) ⟨138021, by rfl⟩ : syracuseStep 368057 = 276043) B276043
theorem B1056185 : Blo 243817 1056185 := bstep (se 2 (by rfl) ⟨396069, by rfl⟩ : syracuseStep 1056185 = 792139) B792139
theorem B368135 : Blo 243817 368135 := bstep (se 1 (by rfl) ⟨276101, by rfl⟩ : syracuseStep 368135 = 552203) B552203
theorem B368171 : Blo 243817 368171 := bstep (se 1 (by rfl) ⟨276128, by rfl⟩ : syracuseStep 368171 = 552257) B552257
theorem B1252907 : Blo 243817 1252907 := bstep (se 1 (by rfl) ⟨939680, by rfl⟩ : syracuseStep 1252907 = 1879361) B1879361
theorem B368201 : Blo 243817 368201 := bstep (se 2 (by rfl) ⟨138075, by rfl⟩ : syracuseStep 368201 = 276151) B276151
theorem B368315 : Blo 243817 368315 := bstep (se 1 (by rfl) ⟨276236, by rfl⟩ : syracuseStep 368315 = 552473) B552473
theorem B368375 : Blo 243817 368375 := bstep (se 1 (by rfl) ⟨276281, by rfl⟩ : syracuseStep 368375 = 552563) B552563
theorem B368399 : Blo 243817 368399 := bstep (se 1 (by rfl) ⟨276299, by rfl⟩ : syracuseStep 368399 = 552599) B552599
theorem B1056527 : Blo 243817 1056527 := bstep (se 1 (by rfl) ⟨792395, by rfl⟩ : syracuseStep 1056527 = 1584791) B1584791
theorem B368441 : Blo 243817 368441 := bstep (se 2 (by rfl) ⟨138165, by rfl⟩ : syracuseStep 368441 = 276331) B276331
theorem B368519 : Blo 243817 368519 := bstep (se 1 (by rfl) ⟨276389, by rfl⟩ : syracuseStep 368519 = 552779) B552779
theorem B368555 : Blo 243817 368555 := bstep (se 1 (by rfl) ⟨276416, by rfl⟩ : syracuseStep 368555 = 552833) B552833
theorem B663481 : Blo 243817 663481 := bstep (se 2 (by rfl) ⟨248805, by rfl⟩ : syracuseStep 663481 = 497611) B497611
theorem B368585 : Blo 243817 368585 := bstep (se 2 (by rfl) ⟨138219, by rfl⟩ : syracuseStep 368585 = 276439) B276439
theorem B7217099 : Blo 243817 7217099 := bstep (se 1 (by rfl) ⟨5412824, by rfl⟩ : syracuseStep 7217099 = 10825649) B10825649
theorem B368699 : Blo 243817 368699 := bstep (se 1 (by rfl) ⟨276524, by rfl⟩ : syracuseStep 368699 = 553049) B553049
theorem B630899 : Blo 243817 630899 := bstep (se 1 (by rfl) ⟨473174, by rfl⟩ : syracuseStep 630899 = 946349) B946349
theorem B368759 : Blo 243817 368759 := bstep (se 1 (by rfl) ⟨276569, by rfl⟩ : syracuseStep 368759 = 553139) B553139
theorem B368783 : Blo 243817 368783 := bstep (se 1 (by rfl) ⟨276587, by rfl⟩ : syracuseStep 368783 = 553175) B553175
theorem B368825 : Blo 243817 368825 := bstep (se 2 (by rfl) ⟨138309, by rfl⟩ : syracuseStep 368825 = 276619) B276619
theorem B8954057 : Blo 243817 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B368903 : Blo 243817 368903 := bstep (se 1 (by rfl) ⟨276677, by rfl⟩ : syracuseStep 368903 = 553355) B553355
theorem B368939 : Blo 243817 368939 := bstep (se 1 (by rfl) ⟨276704, by rfl⟩ : syracuseStep 368939 = 553409) B553409
theorem B368969 : Blo 243817 368969 := bstep (se 2 (by rfl) ⟨138363, by rfl⟩ : syracuseStep 368969 = 276727) B276727
theorem B369083 : Blo 243817 369083 := bstep (se 1 (by rfl) ⟨276812, by rfl⟩ : syracuseStep 369083 = 553625) B553625
theorem B1876445 : Blo 243817 1876445 := bstep (se 3 (by rfl) ⟨351833, by rfl⟩ : syracuseStep 1876445 = 703667) B703667
theorem B369143 : Blo 243817 369143 := bstep (se 1 (by rfl) ⟨276857, by rfl⟩ : syracuseStep 369143 = 553715) B553715
theorem B696833 : Blo 243817 696833 := bstep (se 2 (by rfl) ⟨261312, by rfl⟩ : syracuseStep 696833 = 522625) B522625
theorem B369167 : Blo 243817 369167 := bstep (se 1 (by rfl) ⟨276875, by rfl⟩ : syracuseStep 369167 = 553751) B553751
theorem B467471 : Blo 243817 467471 := bstep (se 1 (by rfl) ⟨350603, by rfl⟩ : syracuseStep 467471 = 701207) B701207
theorem B369209 : Blo 243817 369209 := bstep (se 2 (by rfl) ⟨138453, by rfl⟩ : syracuseStep 369209 = 276907) B276907
theorem B3580483 : Blo 243817 3580483 := bstep (se 1 (by rfl) ⟨2685362, by rfl⟩ : syracuseStep 3580483 = 5370725) B5370725
theorem B369287 : Blo 243817 369287 := bstep (se 1 (by rfl) ⟨276965, by rfl⟩ : syracuseStep 369287 = 553931) B553931
theorem B369323 : Blo 243817 369323 := bstep (se 1 (by rfl) ⟨276992, by rfl⟩ : syracuseStep 369323 = 553985) B553985
theorem B369353 : Blo 243817 369353 := bstep (se 2 (by rfl) ⟨138507, by rfl⟩ : syracuseStep 369353 = 277015) B277015
theorem B664379 : Blo 243817 664379 := bstep (se 1 (by rfl) ⟨498284, by rfl⟩ : syracuseStep 664379 = 996569) B996569
theorem B369467 : Blo 243817 369467 := bstep (se 1 (by rfl) ⟨277100, by rfl⟩ : syracuseStep 369467 = 554201) B554201
theorem B1254203 : Blo 243817 1254203 := bstep (se 1 (by rfl) ⟨940652, by rfl⟩ : syracuseStep 1254203 = 1881305) B1881305
theorem B369527 : Blo 243817 369527 := bstep (se 1 (by rfl) ⟨277145, by rfl⟩ : syracuseStep 369527 = 554291) B554291
theorem B369551 : Blo 243817 369551 := bstep (se 1 (by rfl) ⟨277163, by rfl⟩ : syracuseStep 369551 = 554327) B554327
theorem B500627 : Blo 243817 500627 := bstep (se 1 (by rfl) ⟨375470, by rfl⟩ : syracuseStep 500627 = 750941) B750941
theorem B369593 : Blo 243817 369593 := bstep (se 2 (by rfl) ⟨138597, by rfl⟩ : syracuseStep 369593 = 277195) B277195
theorem B1254365 : Blo 243817 1254365 := bstep (se 3 (by rfl) ⟨235193, by rfl⟩ : syracuseStep 1254365 = 470387) B470387
theorem B369671 : Blo 243817 369671 := bstep (se 1 (by rfl) ⟨277253, by rfl⟩ : syracuseStep 369671 = 554507) B554507
theorem B631841 : Blo 243817 631841 := bstep (se 2 (by rfl) ⟨236940, by rfl⟩ : syracuseStep 631841 = 473881) B473881
theorem B369707 : Blo 243817 369707 := bstep (se 1 (by rfl) ⟨277280, by rfl⟩ : syracuseStep 369707 = 554561) B554561
theorem B468011 : Blo 243817 468011 := bstep (se 1 (by rfl) ⟨351008, by rfl⟩ : syracuseStep 468011 = 702017) B702017
theorem B697403 : Blo 243817 697403 := bstep (se 1 (by rfl) ⟨523052, by rfl⟩ : syracuseStep 697403 = 1046105) B1046105
theorem B369737 : Blo 243817 369737 := bstep (se 2 (by rfl) ⟨138651, by rfl⟩ : syracuseStep 369737 = 277303) B277303
theorem B369851 : Blo 243817 369851 := bstep (se 1 (by rfl) ⟨277388, by rfl⟩ : syracuseStep 369851 = 554777) B554777
theorem B369911 : Blo 243817 369911 := bstep (se 1 (by rfl) ⟨277433, by rfl⟩ : syracuseStep 369911 = 554867) B554867
theorem B369935 : Blo 243817 369935 := bstep (se 1 (by rfl) ⟨277451, by rfl⟩ : syracuseStep 369935 = 554903) B554903
theorem B599329 : Blo 243817 599329 := bstep (se 2 (by rfl) ⟨224748, by rfl⟩ : syracuseStep 599329 = 449497) B449497
theorem B697643 : Blo 243817 697643 := bstep (se 1 (by rfl) ⟨523232, by rfl⟩ : syracuseStep 697643 = 1046465) B1046465
theorem B369977 : Blo 243817 369977 := bstep (se 2 (by rfl) ⟨138741, by rfl⟩ : syracuseStep 369977 = 277483) B277483
theorem B664951 : Blo 243817 664951 := bstep (se 1 (by rfl) ⟨498713, by rfl⟩ : syracuseStep 664951 = 997427) B997427
theorem B370055 : Blo 243817 370055 := bstep (se 1 (by rfl) ⟨277541, by rfl⟩ : syracuseStep 370055 = 555083) B555083
theorem B664985 : Blo 243817 664985 := bstep (se 2 (by rfl) ⟨249369, by rfl⟩ : syracuseStep 664985 = 498739) B498739
theorem B370091 : Blo 243817 370091 := bstep (se 1 (by rfl) ⟨277568, by rfl⟩ : syracuseStep 370091 = 555137) B555137
theorem B1123769 : Blo 243817 1123769 := bstep (se 2 (by rfl) ⟨421413, by rfl⟩ : syracuseStep 1123769 = 842827) B842827
theorem B370121 : Blo 243817 370121 := bstep (se 2 (by rfl) ⟨138795, by rfl⟩ : syracuseStep 370121 = 277591) B277591
theorem B370235 : Blo 243817 370235 := bstep (se 1 (by rfl) ⟨277676, by rfl⟩ : syracuseStep 370235 = 555353) B555353
theorem B370295 : Blo 243817 370295 := bstep (se 1 (by rfl) ⟨277721, by rfl⟩ : syracuseStep 370295 = 555443) B555443
theorem B370319 : Blo 243817 370319 := bstep (se 1 (by rfl) ⟨277739, by rfl⟩ : syracuseStep 370319 = 555479) B555479
theorem B370361 : Blo 243817 370361 := bstep (se 2 (by rfl) ⟨138885, by rfl⟩ : syracuseStep 370361 = 277771) B277771
theorem B1124077 : Blo 243817 1124077 := bstep (se 3 (by rfl) ⟨210764, by rfl⟩ : syracuseStep 1124077 = 421529) B421529
theorem B370439 : Blo 243817 370439 := bstep (se 1 (by rfl) ⟨277829, by rfl⟩ : syracuseStep 370439 = 555659) B555659
theorem B370475 : Blo 243817 370475 := bstep (se 1 (by rfl) ⟨277856, by rfl⟩ : syracuseStep 370475 = 555713) B555713
theorem B370505 : Blo 243817 370505 := bstep (se 2 (by rfl) ⟨138939, by rfl⟩ : syracuseStep 370505 = 277879) B277879
theorem B829331 : Blo 243817 829331 := bstep (se 1 (by rfl) ⟨621998, by rfl⟩ : syracuseStep 829331 = 1243997) B1243997
theorem B370619 : Blo 243817 370619 := bstep (se 1 (by rfl) ⟨277964, by rfl⟩ : syracuseStep 370619 = 555929) B555929
theorem B1320907 : Blo 243817 1320907 := bstep (se 1 (by rfl) ⟨990680, by rfl⟩ : syracuseStep 1320907 = 1981361) B1981361
theorem B370679 : Blo 243817 370679 := bstep (se 1 (by rfl) ⟨278009, by rfl⟩ : syracuseStep 370679 = 556019) B556019
theorem B370703 : Blo 243817 370703 := bstep (se 1 (by rfl) ⟨278027, by rfl⟩ : syracuseStep 370703 = 556055) B556055
theorem B370745 : Blo 243817 370745 := bstep (se 2 (by rfl) ⟨139029, by rfl⟩ : syracuseStep 370745 = 278059) B278059
theorem B469127 : Blo 243817 469127 := bstep (se 1 (by rfl) ⟨351845, by rfl⟩ : syracuseStep 469127 = 703691) B703691
theorem B370823 : Blo 243817 370823 := bstep (se 1 (by rfl) ⟨278117, by rfl⟩ : syracuseStep 370823 = 556235) B556235
theorem B370859 : Blo 243817 370859 := bstep (se 1 (by rfl) ⟨278144, by rfl⟩ : syracuseStep 370859 = 556289) B556289
theorem B370889 : Blo 243817 370889 := bstep (se 2 (by rfl) ⟨139083, by rfl⟩ : syracuseStep 370889 = 278167) B278167
theorem B371003 : Blo 243817 371003 := bstep (se 1 (by rfl) ⟨278252, by rfl⟩ : syracuseStep 371003 = 556505) B556505
theorem B371063 : Blo 243817 371063 := bstep (se 1 (by rfl) ⟨278297, by rfl⟩ : syracuseStep 371063 = 556595) B556595
theorem B371087 : Blo 243817 371087 := bstep (se 1 (by rfl) ⟨278315, by rfl⟩ : syracuseStep 371087 = 556631) B556631
theorem B371129 : Blo 243817 371129 := bstep (se 2 (by rfl) ⟨139173, by rfl⟩ : syracuseStep 371129 = 278347) B278347
theorem B371207 : Blo 243817 371207 := bstep (se 1 (by rfl) ⟨278405, by rfl⟩ : syracuseStep 371207 = 556811) B556811
theorem B371243 : Blo 243817 371243 := bstep (se 1 (by rfl) ⟨278432, by rfl⟩ : syracuseStep 371243 = 556865) B556865
theorem B371273 : Blo 243817 371273 := bstep (se 2 (by rfl) ⟨139227, by rfl⟩ : syracuseStep 371273 = 278455) B278455
theorem B469651 : Blo 243817 469651 := bstep (se 1 (by rfl) ⟨352238, by rfl⟩ : syracuseStep 469651 = 704477) B704477
theorem B371387 : Blo 243817 371387 := bstep (se 1 (by rfl) ⟨278540, by rfl⟩ : syracuseStep 371387 = 557081) B557081
theorem B371447 : Blo 243817 371447 := bstep (se 1 (by rfl) ⟨278585, by rfl⟩ : syracuseStep 371447 = 557171) B557171
theorem B371471 : Blo 243817 371471 := bstep (se 1 (by rfl) ⟨278603, by rfl⟩ : syracuseStep 371471 = 557207) B557207
theorem B371513 : Blo 243817 371513 := bstep (se 2 (by rfl) ⟨139317, by rfl⟩ : syracuseStep 371513 = 278635) B278635
theorem B371591 : Blo 243817 371591 := bstep (se 1 (by rfl) ⟨278693, by rfl⟩ : syracuseStep 371591 = 557387) B557387
theorem B371627 : Blo 243817 371627 := bstep (se 1 (by rfl) ⟨278720, by rfl⟩ : syracuseStep 371627 = 557441) B557441
theorem B371657 : Blo 243817 371657 := bstep (se 2 (by rfl) ⟨139371, by rfl⟩ : syracuseStep 371657 = 278743) B278743
theorem B371719 : Blo 243817 371719 := bstep (se 1 (by rfl) ⟨278789, by rfl⟩ : syracuseStep 371719 = 557579) B557579
theorem B601121 : Blo 243817 601121 := bstep (se 2 (by rfl) ⟨225420, by rfl⟩ : syracuseStep 601121 = 450841) B450841
theorem B830735 : Blo 243817 830735 := bstep (se 1 (by rfl) ⟨623051, by rfl⟩ : syracuseStep 830735 = 1246103) B1246103
theorem B929171 : Blo 243817 929171 := bstep (se 1 (by rfl) ⟨696878, by rfl⟩ : syracuseStep 929171 = 1393757) B1393757
theorem B1486289 : Blo 243817 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B831005 : Blo 243817 831005 := bstep (se 3 (by rfl) ⟨155813, by rfl⟩ : syracuseStep 831005 = 311627) B311627
theorem B274567 : Blo 243817 274567 := bstep (se 1 (by rfl) ⟨205925, by rfl⟩ : syracuseStep 274567 = 411851) B411851
theorem B274747 : Blo 243817 274747 := bstep (se 1 (by rfl) ⟨206060, by rfl⟩ : syracuseStep 274747 = 412121) B412121
theorem B373135 : Blo 243817 373135 := bstep (se 1 (by rfl) ⟨279851, by rfl⟩ : syracuseStep 373135 = 559703) B559703
theorem B1814929 : Blo 243817 1814929 := bstep (se 2 (by rfl) ⟨680598, by rfl⟩ : syracuseStep 1814929 = 1361197) B1361197
theorem B635435 : Blo 243817 635435 := bstep (se 1 (by rfl) ⟨476576, by rfl⟩ : syracuseStep 635435 = 953153) B953153
theorem B8991425 : Blo 243817 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B275215 : Blo 243817 275215 := bstep (se 1 (by rfl) ⟨206411, by rfl⟩ : syracuseStep 275215 = 412823) B412823
theorem B832409 : Blo 243817 832409 := bstep (se 2 (by rfl) ⟨312153, by rfl⟩ : syracuseStep 832409 = 624307) B624307
theorem B1389635 : Blo 243817 1389635 := bstep (se 1 (by rfl) ⟨1042226, by rfl⟩ : syracuseStep 1389635 = 2084453) B2084453
theorem B439481 : Blo 243817 439481 := bstep (se 2 (by rfl) ⟨164805, by rfl⟩ : syracuseStep 439481 = 329611) B329611
theorem B275719 : Blo 243817 275719 := bstep (se 1 (by rfl) ⟨206789, by rfl⟩ : syracuseStep 275719 = 413579) B413579
theorem B3519875 : Blo 243817 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B275899 : Blo 243817 275899 := bstep (se 1 (by rfl) ⟨206924, by rfl⟩ : syracuseStep 275899 = 413849) B413849
theorem B833111 : Blo 243817 833111 := bstep (se 1 (by rfl) ⟨624833, by rfl⟩ : syracuseStep 833111 = 1249667) B1249667
theorem B702209 : Blo 243817 702209 := bstep (se 2 (by rfl) ⟨263328, by rfl⟩ : syracuseStep 702209 = 526657) B526657
theorem B309035 : Blo 243817 309035 := bstep (se 1 (by rfl) ⟨231776, by rfl⟩ : syracuseStep 309035 = 463553) B463553
theorem B276367 : Blo 243817 276367 := bstep (se 1 (by rfl) ⟨207275, by rfl⟩ : syracuseStep 276367 = 414551) B414551
theorem B931769 : Blo 243817 931769 := bstep (se 2 (by rfl) ⟨349413, by rfl⟩ : syracuseStep 931769 = 698827) B698827
theorem B833597 : Blo 243817 833597 := bstep (se 3 (by rfl) ⟨156299, by rfl⟩ : syracuseStep 833597 = 312599) B312599
theorem B243847 : Blo 243817 243847 := bstep (se 1 (by rfl) ⟨182885, by rfl⟩ : syracuseStep 243847 = 365771) B365771
theorem B243855 : Blo 243817 243855 := bstep (se 1 (by rfl) ⟨182891, by rfl⟩ : syracuseStep 243855 = 365783) B365783
theorem B243899 : Blo 243817 243899 := bstep (se 1 (by rfl) ⟨182924, by rfl⟩ : syracuseStep 243899 = 365849) B365849
theorem B702665 : Blo 243817 702665 := bstep (se 2 (by rfl) ⟨263499, by rfl⟩ : syracuseStep 702665 = 526999) B526999
theorem B1784045 : Blo 243817 1784045 := bstep (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) B669017
theorem B243975 : Blo 243817 243975 := bstep (se 1 (by rfl) ⟨182981, by rfl⟩ : syracuseStep 243975 = 365963) B365963
theorem B309511 : Blo 243817 309511 := bstep (se 1 (by rfl) ⟨232133, by rfl⟩ : syracuseStep 309511 = 464267) B464267
theorem B243983 : Blo 243817 243983 := bstep (se 1 (by rfl) ⟨182987, by rfl⟩ : syracuseStep 243983 = 365975) B365975
theorem B473359 : Blo 243817 473359 := bstep (se 1 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 473359 = 710039) B710039
theorem B244027 : Blo 243817 244027 := bstep (se 1 (by rfl) ⟨183020, by rfl⟩ : syracuseStep 244027 = 366041) B366041
theorem B244103 : Blo 243817 244103 := bstep (se 1 (by rfl) ⟨183077, by rfl⟩ : syracuseStep 244103 = 366155) B366155
theorem B276871 : Blo 243817 276871 := bstep (se 1 (by rfl) ⟨207653, by rfl⟩ : syracuseStep 276871 = 415307) B415307
theorem B244111 : Blo 243817 244111 := bstep (se 1 (by rfl) ⟨183083, by rfl⟩ : syracuseStep 244111 = 366167) B366167
theorem B244155 : Blo 243817 244155 := bstep (se 1 (by rfl) ⟨183116, by rfl⟩ : syracuseStep 244155 = 366233) B366233
theorem B375227 : Blo 243817 375227 := bstep (se 1 (by rfl) ⟨281420, by rfl⟩ : syracuseStep 375227 = 562841) B562841
theorem B244231 : Blo 243817 244231 := bstep (se 1 (by rfl) ⟨183173, by rfl⟩ : syracuseStep 244231 = 366347) B366347
theorem B244239 : Blo 243817 244239 := bstep (se 1 (by rfl) ⟨183179, by rfl⟩ : syracuseStep 244239 = 366359) B366359
theorem B703019 : Blo 243817 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B244283 : Blo 243817 244283 := bstep (se 1 (by rfl) ⟨183212, by rfl⟩ : syracuseStep 244283 = 366425) B366425
theorem B277051 : Blo 243817 277051 := bstep (se 1 (by rfl) ⟨207788, by rfl⟩ : syracuseStep 277051 = 415577) B415577
theorem B1784387 : Blo 243817 1784387 := bstep (se 1 (by rfl) ⟨1338290, by rfl⟩ : syracuseStep 1784387 = 2676581) B2676581
theorem B244359 : Blo 243817 244359 := bstep (se 1 (by rfl) ⟨183269, by rfl⟩ : syracuseStep 244359 = 366539) B366539
theorem B244367 : Blo 243817 244367 := bstep (se 1 (by rfl) ⟨183275, by rfl⟩ : syracuseStep 244367 = 366551) B366551
theorem B244411 : Blo 243817 244411 := bstep (se 1 (by rfl) ⟨183308, by rfl⟩ : syracuseStep 244411 = 366617) B366617
theorem B310007 : Blo 243817 310007 := bstep (se 1 (by rfl) ⟨232505, by rfl⟩ : syracuseStep 310007 = 465011) B465011
theorem B244487 : Blo 243817 244487 := bstep (se 1 (by rfl) ⟨183365, by rfl⟩ : syracuseStep 244487 = 366731) B366731
theorem B244495 : Blo 243817 244495 := bstep (se 1 (by rfl) ⟨183371, by rfl⟩ : syracuseStep 244495 = 366743) B366743
theorem B244539 : Blo 243817 244539 := bstep (se 1 (by rfl) ⟨183404, by rfl⟩ : syracuseStep 244539 = 366809) B366809
theorem B244615 : Blo 243817 244615 := bstep (se 1 (by rfl) ⟨183461, by rfl⟩ : syracuseStep 244615 = 366923) B366923
theorem B244623 : Blo 243817 244623 := bstep (se 1 (by rfl) ⟨183467, by rfl⟩ : syracuseStep 244623 = 366935) B366935
theorem B310159 : Blo 243817 310159 := bstep (se 1 (by rfl) ⟨232619, by rfl⟩ : syracuseStep 310159 = 465239) B465239
theorem B932755 : Blo 243817 932755 := bstep (se 1 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 932755 = 1399133) B1399133
theorem B703417 : Blo 243817 703417 := bstep (se 2 (by rfl) ⟨263781, by rfl⟩ : syracuseStep 703417 = 527563) B527563
theorem B244667 : Blo 243817 244667 := bstep (se 1 (by rfl) ⟨183500, by rfl⟩ : syracuseStep 244667 = 367001) B367001
theorem B244743 : Blo 243817 244743 := bstep (se 1 (by rfl) ⟨183557, by rfl⟩ : syracuseStep 244743 = 367115) B367115
theorem B244751 : Blo 243817 244751 := bstep (se 1 (by rfl) ⟨183563, by rfl⟩ : syracuseStep 244751 = 367127) B367127
theorem B277519 : Blo 243817 277519 := bstep (se 1 (by rfl) ⟨208139, by rfl⟩ : syracuseStep 277519 = 416279) B416279
theorem B244795 : Blo 243817 244795 := bstep (se 1 (by rfl) ⟨183596, by rfl⟩ : syracuseStep 244795 = 367193) B367193
theorem B310331 : Blo 243817 310331 := bstep (se 1 (by rfl) ⟨232748, by rfl⟩ : syracuseStep 310331 = 465497) B465497
theorem B244871 : Blo 243817 244871 := bstep (se 1 (by rfl) ⟨183653, by rfl⟩ : syracuseStep 244871 = 367307) B367307
theorem B244879 : Blo 243817 244879 := bstep (se 1 (by rfl) ⟨183659, by rfl⟩ : syracuseStep 244879 = 367319) B367319
theorem B244923 : Blo 243817 244923 := bstep (se 1 (by rfl) ⟨183692, by rfl⟩ : syracuseStep 244923 = 367385) B367385
theorem B244999 : Blo 243817 244999 := bstep (se 1 (by rfl) ⟨183749, by rfl⟩ : syracuseStep 244999 = 367499) B367499
theorem B245007 : Blo 243817 245007 := bstep (se 1 (by rfl) ⟨183755, by rfl⟩ : syracuseStep 245007 = 367511) B367511
theorem B834875 : Blo 243817 834875 := bstep (se 1 (by rfl) ⟨626156, by rfl⟩ : syracuseStep 834875 = 1252313) B1252313
theorem B245051 : Blo 243817 245051 := bstep (se 1 (by rfl) ⟨183788, by rfl⟩ : syracuseStep 245051 = 367577) B367577
theorem B245127 : Blo 243817 245127 := bstep (se 1 (by rfl) ⟨183845, by rfl⟩ : syracuseStep 245127 = 367691) B367691
theorem B245135 : Blo 243817 245135 := bstep (se 1 (by rfl) ⟨183851, by rfl⟩ : syracuseStep 245135 = 367703) B367703
theorem B1392025 : Blo 243817 1392025 := bstep (se 2 (by rfl) ⟨522009, by rfl⟩ : syracuseStep 1392025 = 1044019) B1044019
theorem B835001 : Blo 243817 835001 := bstep (se 2 (by rfl) ⟨313125, by rfl⟩ : syracuseStep 835001 = 626251) B626251
theorem B245179 : Blo 243817 245179 := bstep (se 1 (by rfl) ⟨183884, by rfl⟩ : syracuseStep 245179 = 367769) B367769
theorem B245255 : Blo 243817 245255 := bstep (se 1 (by rfl) ⟨183941, by rfl⟩ : syracuseStep 245255 = 367883) B367883
theorem B278023 : Blo 243817 278023 := bstep (se 1 (by rfl) ⟨208517, by rfl⟩ : syracuseStep 278023 = 417035) B417035
theorem B245263 : Blo 243817 245263 := bstep (se 1 (by rfl) ⟨183947, by rfl⟩ : syracuseStep 245263 = 367895) B367895
theorem B245307 : Blo 243817 245307 := bstep (se 1 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 245307 = 367961) B367961
theorem B245383 : Blo 243817 245383 := bstep (se 1 (by rfl) ⟨184037, by rfl⟩ : syracuseStep 245383 = 368075) B368075
theorem B245391 : Blo 243817 245391 := bstep (se 1 (by rfl) ⟨184043, by rfl⟩ : syracuseStep 245391 = 368087) B368087
theorem B245435 : Blo 243817 245435 := bstep (se 1 (by rfl) ⟨184076, by rfl⟩ : syracuseStep 245435 = 368153) B368153
theorem B278203 : Blo 243817 278203 := bstep (se 1 (by rfl) ⟨208652, by rfl⟩ : syracuseStep 278203 = 417305) B417305
theorem B245511 : Blo 243817 245511 := bstep (se 1 (by rfl) ⟨184133, by rfl⟩ : syracuseStep 245511 = 368267) B368267
theorem B245519 : Blo 243817 245519 := bstep (se 1 (by rfl) ⟨184139, by rfl⟩ : syracuseStep 245519 = 368279) B368279
theorem B5062445 : Blo 243817 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B245563 : Blo 243817 245563 := bstep (se 1 (by rfl) ⟨184172, by rfl⟩ : syracuseStep 245563 = 368345) B368345
theorem B245639 : Blo 243817 245639 := bstep (se 1 (by rfl) ⟨184229, by rfl⟩ : syracuseStep 245639 = 368459) B368459
theorem B245647 : Blo 243817 245647 := bstep (se 1 (by rfl) ⟨184235, by rfl⟩ : syracuseStep 245647 = 368471) B368471
theorem B245691 : Blo 243817 245691 := bstep (se 1 (by rfl) ⟨184268, by rfl⟩ : syracuseStep 245691 = 368537) B368537
theorem B245767 : Blo 243817 245767 := bstep (se 1 (by rfl) ⟨184325, by rfl⟩ : syracuseStep 245767 = 368651) B368651
theorem B311303 : Blo 243817 311303 := bstep (se 1 (by rfl) ⟨233477, by rfl⟩ : syracuseStep 311303 = 466955) B466955
theorem B835595 : Blo 243817 835595 := bstep (se 1 (by rfl) ⟨626696, by rfl⟩ : syracuseStep 835595 = 1253393) B1253393
theorem B245775 : Blo 243817 245775 := bstep (se 1 (by rfl) ⟨184331, by rfl⟩ : syracuseStep 245775 = 368663) B368663
theorem B245819 : Blo 243817 245819 := bstep (se 1 (by rfl) ⟨184364, by rfl⟩ : syracuseStep 245819 = 368729) B368729
theorem B835703 : Blo 243817 835703 := bstep (se 1 (by rfl) ⟨626777, by rfl⟩ : syracuseStep 835703 = 1253555) B1253555
theorem B245895 : Blo 243817 245895 := bstep (se 1 (by rfl) ⟨184421, by rfl⟩ : syracuseStep 245895 = 368843) B368843
theorem B245903 : Blo 243817 245903 := bstep (se 1 (by rfl) ⟨184427, by rfl⟩ : syracuseStep 245903 = 368855) B368855
theorem B278671 : Blo 243817 278671 := bstep (se 1 (by rfl) ⟨209003, by rfl⟩ : syracuseStep 278671 = 418007) B418007
theorem B704659 : Blo 243817 704659 := bstep (se 1 (by rfl) ⟨528494, by rfl⟩ : syracuseStep 704659 = 1056989) B1056989
theorem B245947 : Blo 243817 245947 := bstep (se 1 (by rfl) ⟨184460, by rfl⟩ : syracuseStep 245947 = 368921) B368921
theorem B246023 : Blo 243817 246023 := bstep (se 1 (by rfl) ⟨184517, by rfl⟩ : syracuseStep 246023 = 369035) B369035
theorem B246031 : Blo 243817 246031 := bstep (se 1 (by rfl) ⟨184523, by rfl⟩ : syracuseStep 246031 = 369047) B369047
theorem B246075 : Blo 243817 246075 := bstep (se 1 (by rfl) ⟨184556, by rfl⟩ : syracuseStep 246075 = 369113) B369113
theorem B246151 : Blo 243817 246151 := bstep (se 1 (by rfl) ⟨184613, by rfl⟩ : syracuseStep 246151 = 369227) B369227
theorem B246159 : Blo 243817 246159 := bstep (se 1 (by rfl) ⟨184619, by rfl⟩ : syracuseStep 246159 = 369239) B369239
theorem B2474387 : Blo 243817 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B246203 : Blo 243817 246203 := bstep (se 1 (by rfl) ⟨184652, by rfl⟩ : syracuseStep 246203 = 369305) B369305
theorem B246279 : Blo 243817 246279 := bstep (se 1 (by rfl) ⟨184709, by rfl⟩ : syracuseStep 246279 = 369419) B369419
theorem B246287 : Blo 243817 246287 := bstep (se 1 (by rfl) ⟨184715, by rfl⟩ : syracuseStep 246287 = 369431) B369431
theorem B246331 : Blo 243817 246331 := bstep (se 1 (by rfl) ⟨184748, by rfl⟩ : syracuseStep 246331 = 369497) B369497
theorem B934487 : Blo 243817 934487 := bstep (se 1 (by rfl) ⟨700865, by rfl⟩ : syracuseStep 934487 = 1401731) B1401731
theorem B442999 : Blo 243817 442999 := bstep (se 1 (by rfl) ⟨332249, by rfl⟩ : syracuseStep 442999 = 664499) B664499
theorem B246407 : Blo 243817 246407 := bstep (se 1 (by rfl) ⟨184805, by rfl⟩ : syracuseStep 246407 = 369611) B369611
theorem B246415 : Blo 243817 246415 := bstep (se 1 (by rfl) ⟨184811, by rfl⟩ : syracuseStep 246415 = 369623) B369623
theorem B311951 : Blo 243817 311951 := bstep (se 1 (by rfl) ⟨233963, by rfl⟩ : syracuseStep 311951 = 467927) B467927
theorem B246459 : Blo 243817 246459 := bstep (se 1 (by rfl) ⟨184844, by rfl⟩ : syracuseStep 246459 = 369689) B369689
theorem B836297 : Blo 243817 836297 := bstep (se 2 (by rfl) ⟨313611, by rfl⟩ : syracuseStep 836297 = 627223) B627223
theorem B246535 : Blo 243817 246535 := bstep (se 1 (by rfl) ⟨184901, by rfl⟩ : syracuseStep 246535 = 369803) B369803
theorem B246543 : Blo 243817 246543 := bstep (se 1 (by rfl) ⟨184907, by rfl⟩ : syracuseStep 246543 = 369815) B369815
theorem B3982117 : Blo 243817 3982117 := bstep (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) B746647
theorem B246587 : Blo 243817 246587 := bstep (se 1 (by rfl) ⟨184940, by rfl⟩ : syracuseStep 246587 = 369881) B369881
theorem B246663 : Blo 243817 246663 := bstep (se 1 (by rfl) ⟨184997, by rfl⟩ : syracuseStep 246663 = 369995) B369995
theorem B246671 : Blo 243817 246671 := bstep (se 1 (by rfl) ⟨185003, by rfl⟩ : syracuseStep 246671 = 370007) B370007
theorem B1000345 : Blo 243817 1000345 := bstep (se 2 (by rfl) ⟨375129, by rfl⟩ : syracuseStep 1000345 = 750259) B750259
theorem B246715 : Blo 243817 246715 := bstep (se 1 (by rfl) ⟨185036, by rfl⟩ : syracuseStep 246715 = 370073) B370073
theorem B246791 : Blo 243817 246791 := bstep (se 1 (by rfl) ⟨185093, by rfl⟩ : syracuseStep 246791 = 370187) B370187
theorem B246799 : Blo 243817 246799 := bstep (se 1 (by rfl) ⟨185099, by rfl⟩ : syracuseStep 246799 = 370199) B370199
theorem B246843 : Blo 243817 246843 := bstep (se 1 (by rfl) ⟨185132, by rfl⟩ : syracuseStep 246843 = 370265) B370265
theorem B934973 : Blo 243817 934973 := bstep (se 3 (by rfl) ⟨175307, by rfl⟩ : syracuseStep 934973 = 350615) B350615
theorem B2114693 : Blo 243817 2114693 := bstep (se 4 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 2114693 = 396505) B396505
theorem B246919 : Blo 243817 246919 := bstep (se 1 (by rfl) ⟨185189, by rfl⟩ : syracuseStep 246919 = 370379) B370379
theorem B246927 : Blo 243817 246927 := bstep (se 1 (by rfl) ⟨185195, by rfl⟩ : syracuseStep 246927 = 370391) B370391
theorem B246971 : Blo 243817 246971 := bstep (se 1 (by rfl) ⟨185228, by rfl⟩ : syracuseStep 246971 = 370457) B370457
theorem B247047 : Blo 243817 247047 := bstep (se 1 (by rfl) ⟨185285, by rfl⟩ : syracuseStep 247047 = 370571) B370571
theorem B247055 : Blo 243817 247055 := bstep (se 1 (by rfl) ⟨185291, by rfl⟩ : syracuseStep 247055 = 370583) B370583
theorem B247099 : Blo 243817 247099 := bstep (se 1 (by rfl) ⟨185324, by rfl⟩ : syracuseStep 247099 = 370649) B370649
theorem B1394009 : Blo 243817 1394009 := bstep (se 2 (by rfl) ⟨522753, by rfl⟩ : syracuseStep 1394009 = 1045507) B1045507
theorem B247175 : Blo 243817 247175 := bstep (se 1 (by rfl) ⟨185381, by rfl⟩ : syracuseStep 247175 = 370763) B370763
theorem B247183 : Blo 243817 247183 := bstep (se 1 (by rfl) ⟨185387, by rfl⟩ : syracuseStep 247183 = 370775) B370775
theorem B247227 : Blo 243817 247227 := bstep (se 1 (by rfl) ⟨185420, by rfl⟩ : syracuseStep 247227 = 370841) B370841
theorem B247303 : Blo 243817 247303 := bstep (se 1 (by rfl) ⟨185477, by rfl⟩ : syracuseStep 247303 = 370955) B370955
theorem B247311 : Blo 243817 247311 := bstep (se 1 (by rfl) ⟨185483, by rfl⟩ : syracuseStep 247311 = 370967) B370967
theorem B247355 : Blo 243817 247355 := bstep (se 1 (by rfl) ⟨185516, by rfl⟩ : syracuseStep 247355 = 371033) B371033
theorem B247431 : Blo 243817 247431 := bstep (se 1 (by rfl) ⟨185573, by rfl⟩ : syracuseStep 247431 = 371147) B371147
theorem B247439 : Blo 243817 247439 := bstep (se 1 (by rfl) ⟨185579, by rfl⟩ : syracuseStep 247439 = 371159) B371159
theorem B247483 : Blo 243817 247483 := bstep (se 1 (by rfl) ⟨185612, by rfl⟩ : syracuseStep 247483 = 371225) B371225
theorem B247559 : Blo 243817 247559 := bstep (se 1 (by rfl) ⟨185669, by rfl⟩ : syracuseStep 247559 = 371339) B371339
theorem B247567 : Blo 243817 247567 := bstep (se 1 (by rfl) ⟨185675, by rfl⟩ : syracuseStep 247567 = 371351) B371351
theorem B247611 : Blo 243817 247611 := bstep (se 1 (by rfl) ⟨185708, by rfl⟩ : syracuseStep 247611 = 371417) B371417
theorem B4474693 : Blo 243817 4474693 := bstep (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) B839005
theorem B411527 : Blo 243817 411527 := bstep (se 1 (by rfl) ⟨308645, by rfl⟩ : syracuseStep 411527 = 617291) B617291
theorem B247687 : Blo 243817 247687 := bstep (se 1 (by rfl) ⟨185765, by rfl⟩ : syracuseStep 247687 = 371531) B371531
theorem B247695 : Blo 243817 247695 := bstep (se 1 (by rfl) ⟨185771, by rfl⟩ : syracuseStep 247695 = 371543) B371543
theorem B247739 : Blo 243817 247739 := bstep (se 1 (by rfl) ⟨185804, by rfl⟩ : syracuseStep 247739 = 371609) B371609
theorem B247815 : Blo 243817 247815 := bstep (se 1 (by rfl) ⟨185861, by rfl⟩ : syracuseStep 247815 = 371723) B371723
theorem B1067411 : Blo 243817 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B412175 : Blo 243817 412175 := bstep (se 1 (by rfl) ⟨309131, by rfl⟩ : syracuseStep 412175 = 618263) B618263
theorem B1330141 : Blo 243817 1330141 := bstep (se 3 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 1330141 = 498803) B498803
theorem B412715 : Blo 243817 412715 := bstep (se 1 (by rfl) ⟨309536, by rfl⟩ : syracuseStep 412715 = 619073) B619073
theorem B2411693 : Blo 243817 2411693 := bstep (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) B904385
theorem B347323 : Blo 243817 347323 := bstep (se 1 (by rfl) ⟨260492, by rfl⟩ : syracuseStep 347323 = 520985) B520985
theorem B413113 : Blo 243817 413113 := bstep (se 2 (by rfl) ⟨154917, by rfl⟩ : syracuseStep 413113 = 309835) B309835
theorem B3132877 : Blo 243817 3132877 := bstep (se 3 (by rfl) ⟨587414, by rfl⟩ : syracuseStep 3132877 = 1174829) B1174829
theorem B6311681 : Blo 243817 6311681 := bstep (se 2 (by rfl) ⟨2366880, by rfl⟩ : syracuseStep 6311681 = 4733761) B4733761
theorem B479009 : Blo 243817 479009 := bstep (se 2 (by rfl) ⟨179628, by rfl⟩ : syracuseStep 479009 = 359257) B359257
theorem B413815 : Blo 243817 413815 := bstep (se 1 (by rfl) ⟨310361, by rfl⟩ : syracuseStep 413815 = 620723) B620723
theorem B7622857 : Blo 243817 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B2085101 : Blo 243817 2085101 := bstep (se 3 (by rfl) ⟨390956, by rfl⟩ : syracuseStep 2085101 = 781913) B781913
theorem B414011 : Blo 243817 414011 := bstep (se 1 (by rfl) ⟨310508, by rfl⟩ : syracuseStep 414011 = 621017) B621017
theorem B938375 : Blo 243817 938375 := bstep (se 1 (by rfl) ⟨703781, by rfl⟩ : syracuseStep 938375 = 1407563) B1407563
theorem B414409 : Blo 243817 414409 := bstep (se 2 (by rfl) ⟨155403, by rfl⟩ : syracuseStep 414409 = 310807) B310807
theorem B677179 : Blo 243817 677179 := bstep (se 1 (by rfl) ⟨507884, by rfl⟩ : syracuseStep 677179 = 1015769) B1015769
theorem B1398131 : Blo 243817 1398131 := bstep (se 1 (by rfl) ⟨1048598, by rfl⟩ : syracuseStep 1398131 = 2097197) B2097197
theorem B415111 : Blo 243817 415111 := bstep (se 1 (by rfl) ⟨311333, by rfl⟩ : syracuseStep 415111 = 622667) B622667
theorem B349687 : Blo 243817 349687 := bstep (se 1 (by rfl) ⟨262265, by rfl⟩ : syracuseStep 349687 = 524531) B524531
theorem B2643673 : Blo 243817 2643673 := bstep (se 2 (by rfl) ⟨991377, by rfl⟩ : syracuseStep 2643673 = 1982755) B1982755
theorem B350011 : Blo 243817 350011 := bstep (se 1 (by rfl) ⟨262508, by rfl⟩ : syracuseStep 350011 = 525017) B525017
theorem B743303 : Blo 243817 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B1333259 : Blo 243817 1333259 := bstep (se 1 (by rfl) ⟨999944, by rfl⟩ : syracuseStep 1333259 = 1999889) B1999889
theorem B415759 : Blo 243817 415759 := bstep (se 1 (by rfl) ⟨311819, by rfl⟩ : syracuseStep 415759 = 623639) B623639
theorem B350507 : Blo 243817 350507 := bstep (se 1 (by rfl) ⟨262880, by rfl⟩ : syracuseStep 350507 = 525761) B525761
theorem B1857977 : Blo 243817 1857977 := bstep (se 2 (by rfl) ⟨696741, by rfl⟩ : syracuseStep 1857977 = 1393483) B1393483
theorem B416299 : Blo 243817 416299 := bstep (se 1 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 416299 = 624449) B624449
theorem B2087491 : Blo 243817 2087491 := bstep (se 1 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 2087491 = 3131237) B3131237
theorem B416441 : Blo 243817 416441 := bstep (se 2 (by rfl) ⟨156165, by rfl⟩ : syracuseStep 416441 = 312331) B312331
theorem B2644751 : Blo 243817 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B1399589 : Blo 243817 1399589 := bstep (se 4 (by rfl) ⟨131211, by rfl⟩ : syracuseStep 1399589 = 262423) B262423
theorem B1235897 : Blo 243817 1235897 := bstep (se 2 (by rfl) ⟨463461, by rfl⟩ : syracuseStep 1235897 = 926923) B926923
theorem B3988541 : Blo 243817 3988541 := bstep (se 3 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 3988541 = 1495703) B1495703
theorem B7625933 : Blo 243817 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B417143 : Blo 243817 417143 := bstep (se 1 (by rfl) ⟨312857, by rfl⟩ : syracuseStep 417143 = 625715) B625715
theorem B1400273 : Blo 243817 1400273 := bstep (se 2 (by rfl) ⟨525102, by rfl⟩ : syracuseStep 1400273 = 1050205) B1050205
theorem B483017 : Blo 243817 483017 := bstep (se 2 (by rfl) ⟨181131, by rfl⟩ : syracuseStep 483017 = 362263) B362263
theorem B1400591 : Blo 243817 1400591 := bstep (se 1 (by rfl) ⟨1050443, by rfl⟩ : syracuseStep 1400591 = 2100887) B2100887
theorem B417595 : Blo 243817 417595 := bstep (se 1 (by rfl) ⟨313196, by rfl⟩ : syracuseStep 417595 = 626393) B626393
theorem B352073 : Blo 243817 352073 := bstep (se 2 (by rfl) ⟨132027, by rfl⟩ : syracuseStep 352073 = 264055) B264055
theorem B843635 : Blo 243817 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B417737 : Blo 243817 417737 := bstep (se 2 (by rfl) ⟨156651, by rfl⟩ : syracuseStep 417737 = 313303) B313303
theorem B745483 : Blo 243817 745483 := bstep (se 1 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 745483 = 1118225) B1118225
theorem B1499255 : Blo 243817 1499255 := bstep (se 1 (by rfl) ⟨1124441, by rfl⟩ : syracuseStep 1499255 = 2248883) B2248883
theorem B548999 : Blo 243817 548999 := bstep (se 1 (by rfl) ⟨411749, by rfl⟩ : syracuseStep 548999 = 823499) B823499
theorem B1237193 : Blo 243817 1237193 := bstep (se 2 (by rfl) ⟨463947, by rfl⟩ : syracuseStep 1237193 = 927895) B927895
theorem B549179 : Blo 243817 549179 := bstep (se 1 (by rfl) ⟨411884, by rfl⟩ : syracuseStep 549179 = 823769) B823769
theorem B352631 : Blo 243817 352631 := bstep (se 1 (by rfl) ⟨264473, by rfl⟩ : syracuseStep 352631 = 528947) B528947
theorem B2777489 : Blo 243817 2777489 := bstep (se 2 (by rfl) ⟨1041558, by rfl⟩ : syracuseStep 2777489 = 2083117) B2083117
theorem B549305 : Blo 243817 549305 := bstep (se 2 (by rfl) ⟨205989, by rfl⟩ : syracuseStep 549305 = 411979) B411979
theorem B2089475 : Blo 243817 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B1172141 : Blo 243817 1172141 := bstep (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) B439553
theorem B549647 : Blo 243817 549647 := bstep (se 1 (by rfl) ⟨412235, by rfl⟩ : syracuseStep 549647 = 824471) B824471
theorem B549665 : Blo 243817 549665 := bstep (se 2 (by rfl) ⟨206124, by rfl⟩ : syracuseStep 549665 = 412249) B412249
theorem B1172369 : Blo 243817 1172369 := bstep (se 2 (by rfl) ⟨439638, by rfl⟩ : syracuseStep 1172369 = 879277) B879277
theorem B320503 : Blo 243817 320503 := bstep (se 1 (by rfl) ⟨240377, by rfl⟩ : syracuseStep 320503 = 480755) B480755
theorem B550007 : Blo 243817 550007 := bstep (se 1 (by rfl) ⟨412505, by rfl⟩ : syracuseStep 550007 = 825011) B825011
theorem B1402049 : Blo 243817 1402049 := bstep (se 2 (by rfl) ⟨525768, by rfl⟩ : syracuseStep 1402049 = 1051537) B1051537
theorem B550187 : Blo 243817 550187 := bstep (se 1 (by rfl) ⟨412640, by rfl⟩ : syracuseStep 550187 = 825281) B825281
theorem B353737 : Blo 243817 353737 := bstep (se 2 (by rfl) ⟨132651, by rfl⟩ : syracuseStep 353737 = 265303) B265303
theorem B3991139 : Blo 243817 3991139 := bstep (se 1 (by rfl) ⟨2993354, by rfl⟩ : syracuseStep 3991139 = 5986709) B5986709
theorem B550547 : Blo 243817 550547 := bstep (se 1 (by rfl) ⟨412910, by rfl⟩ : syracuseStep 550547 = 825821) B825821
theorem B550601 : Blo 243817 550601 := bstep (se 2 (by rfl) ⟨206475, by rfl⟩ : syracuseStep 550601 = 412951) B412951
theorem B6514805 : Blo 243817 6514805 := bstep (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) B610763
theorem B551303 : Blo 243817 551303 := bstep (se 1 (by rfl) ⟨413477, by rfl⟩ : syracuseStep 551303 = 826955) B826955
theorem B4712849 : Blo 243817 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B485921 : Blo 243817 485921 := bstep (se 2 (by rfl) ⟨182220, by rfl⟩ : syracuseStep 485921 = 364441) B364441
theorem B551483 : Blo 243817 551483 := bstep (se 1 (by rfl) ⟨413612, by rfl⟩ : syracuseStep 551483 = 827225) B827225
theorem B2812481 : Blo 243817 2812481 := bstep (se 2 (by rfl) ⟨1054680, by rfl⟩ : syracuseStep 2812481 = 2109361) B2109361
theorem B1043063 : Blo 243817 1043063 := bstep (se 1 (by rfl) ⟨782297, by rfl⟩ : syracuseStep 1043063 = 1564595) B1564595
theorem B551609 : Blo 243817 551609 := bstep (se 2 (by rfl) ⟨206853, by rfl⟩ : syracuseStep 551609 = 413707) B413707
theorem B2091865 : Blo 243817 2091865 := bstep (se 2 (by rfl) ⟨784449, by rfl⟩ : syracuseStep 2091865 = 1568899) B1568899
theorem B617483 : Blo 243817 617483 := bstep (se 1 (by rfl) ⟨463112, by rfl⟩ : syracuseStep 617483 = 926225) B926225
theorem B551951 : Blo 243817 551951 := bstep (se 1 (by rfl) ⟨413963, by rfl⟩ : syracuseStep 551951 = 827927) B827927
theorem B551969 : Blo 243817 551969 := bstep (se 2 (by rfl) ⟨206988, by rfl⟩ : syracuseStep 551969 = 413977) B413977
theorem B2780405 : Blo 243817 2780405 := bstep (se 5 (by rfl) ⟨130331, by rfl⟩ : syracuseStep 2780405 = 260663) B260663
theorem B552311 : Blo 243817 552311 := bstep (se 1 (by rfl) ⟨414233, by rfl⟩ : syracuseStep 552311 = 828467) B828467
theorem B2354579 : Blo 243817 2354579 := bstep (se 1 (by rfl) ⟨1765934, by rfl⟩ : syracuseStep 2354579 = 3531869) B3531869
theorem B1568285 : Blo 243817 1568285 := bstep (se 3 (by rfl) ⟨294053, by rfl⟩ : syracuseStep 1568285 = 588107) B588107
theorem B552491 : Blo 243817 552491 := bstep (se 1 (by rfl) ⟨414368, by rfl⟩ : syracuseStep 552491 = 828737) B828737
theorem B618131 : Blo 243817 618131 := bstep (se 1 (by rfl) ⟨463598, by rfl⟩ : syracuseStep 618131 = 927197) B927197
theorem B782081 : Blo 243817 782081 := bstep (se 2 (by rfl) ⟨293280, by rfl⟩ : syracuseStep 782081 = 586561) B586561
theorem B5074757 : Blo 243817 5074757 := bstep (se 4 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 5074757 = 951517) B951517
theorem B552851 : Blo 243817 552851 := bstep (se 1 (by rfl) ⟨414638, by rfl⟩ : syracuseStep 552851 = 829277) B829277
theorem B5369753 : Blo 243817 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B618425 : Blo 243817 618425 := bstep (se 2 (by rfl) ⟨231909, by rfl⟩ : syracuseStep 618425 = 463819) B463819
theorem B552905 : Blo 243817 552905 := bstep (se 2 (by rfl) ⟨207339, by rfl⟩ : syracuseStep 552905 = 414679) B414679
theorem B1896851 : Blo 243817 1896851 := bstep (se 1 (by rfl) ⟨1422638, by rfl⟩ : syracuseStep 1896851 = 2845277) B2845277
theorem B881239 : Blo 243817 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B619123 : Blo 243817 619123 := bstep (se 1 (by rfl) ⟨464342, by rfl⟩ : syracuseStep 619123 = 928685) B928685
theorem B553607 : Blo 243817 553607 := bstep (se 1 (by rfl) ⟨415205, by rfl⟩ : syracuseStep 553607 = 830411) B830411
theorem B619265 : Blo 243817 619265 := bstep (se 2 (by rfl) ⟨232224, by rfl⟩ : syracuseStep 619265 = 464449) B464449
theorem B1078049 : Blo 243817 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B553787 : Blo 243817 553787 := bstep (se 1 (by rfl) ⟨415340, by rfl⟩ : syracuseStep 553787 = 830681) B830681
theorem B553913 : Blo 243817 553913 := bstep (se 2 (by rfl) ⟨207717, by rfl⟩ : syracuseStep 553913 = 415435) B415435
theorem B1176599 : Blo 243817 1176599 := bstep (se 1 (by rfl) ⟨882449, by rfl⟩ : syracuseStep 1176599 = 1764899) B1764899
theorem B619721 : Blo 243817 619721 := bstep (se 2 (by rfl) ⟨232395, by rfl⟩ : syracuseStep 619721 = 464791) B464791
theorem B1242383 : Blo 243817 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B554255 : Blo 243817 554255 := bstep (se 1 (by rfl) ⟨415691, by rfl⟩ : syracuseStep 554255 = 831383) B831383
theorem B554273 : Blo 243817 554273 := bstep (se 2 (by rfl) ⟨207852, by rfl⟩ : syracuseStep 554273 = 415705) B415705
theorem B587051 : Blo 243817 587051 := bstep (se 1 (by rfl) ⟨440288, by rfl⟩ : syracuseStep 587051 = 880577) B880577
theorem B882035 : Blo 243817 882035 := bstep (se 1 (by rfl) ⟨661526, by rfl⟩ : syracuseStep 882035 = 1323053) B1323053
theorem B620075 : Blo 243817 620075 := bstep (se 1 (by rfl) ⟨465056, by rfl⟩ : syracuseStep 620075 = 930113) B930113
theorem B554615 : Blo 243817 554615 := bstep (se 1 (by rfl) ⟨415961, by rfl⟩ : syracuseStep 554615 = 831923) B831923
theorem B718625 : Blo 243817 718625 := bstep (se 2 (by rfl) ⟨269484, by rfl⟩ : syracuseStep 718625 = 538969) B538969
theorem B554795 : Blo 243817 554795 := bstep (se 1 (by rfl) ⟨416096, by rfl⟩ : syracuseStep 554795 = 832193) B832193
theorem B1243025 : Blo 243817 1243025 := bstep (se 2 (by rfl) ⟨466134, by rfl⟩ : syracuseStep 1243025 = 932269) B932269
theorem B522283 : Blo 243817 522283 := bstep (se 1 (by rfl) ⟨391712, by rfl⟩ : syracuseStep 522283 = 783425) B783425
theorem B555155 : Blo 243817 555155 := bstep (se 1 (by rfl) ⟨416366, by rfl⟩ : syracuseStep 555155 = 832733) B832733
theorem B555209 : Blo 243817 555209 := bstep (se 2 (by rfl) ⟨208203, by rfl⟩ : syracuseStep 555209 = 416407) B416407
theorem B784655 : Blo 243817 784655 := bstep (se 1 (by rfl) ⟨588491, by rfl⟩ : syracuseStep 784655 = 1176983) B1176983
theorem B588185 : Blo 243817 588185 := bstep (se 2 (by rfl) ⟨220569, by rfl⟩ : syracuseStep 588185 = 441139) B441139
theorem B1178059 : Blo 243817 1178059 := bstep (se 1 (by rfl) ⟨883544, by rfl⟩ : syracuseStep 1178059 = 1767089) B1767089
theorem B621067 : Blo 243817 621067 := bstep (se 1 (by rfl) ⟨465800, by rfl⟩ : syracuseStep 621067 = 931601) B931601
theorem B1768013 : Blo 243817 1768013 := bstep (se 3 (by rfl) ⟨331502, by rfl⟩ : syracuseStep 1768013 = 663005) B663005
theorem B785015 : Blo 243817 785015 := bstep (se 1 (by rfl) ⟨588761, by rfl⟩ : syracuseStep 785015 = 1177523) B1177523
theorem B621209 : Blo 243817 621209 := bstep (se 2 (by rfl) ⟨232953, by rfl⟩ : syracuseStep 621209 = 465907) B465907
theorem B621371 : Blo 243817 621371 := bstep (se 1 (by rfl) ⟨466028, by rfl⟩ : syracuseStep 621371 = 932057) B932057
theorem B555911 : Blo 243817 555911 := bstep (se 1 (by rfl) ⟨416933, by rfl⟩ : syracuseStep 555911 = 833867) B833867
theorem B1047505 : Blo 243817 1047505 := bstep (se 2 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 1047505 = 785629) B785629
theorem B556091 : Blo 243817 556091 := bstep (se 1 (by rfl) ⟨417068, by rfl⟩ : syracuseStep 556091 = 834137) B834137
theorem B621715 : Blo 243817 621715 := bstep (se 1 (by rfl) ⟨466286, by rfl⟩ : syracuseStep 621715 = 932573) B932573
theorem B588953 : Blo 243817 588953 := bstep (se 2 (by rfl) ⟨220857, by rfl⟩ : syracuseStep 588953 = 441715) B441715
theorem B556217 : Blo 243817 556217 := bstep (se 2 (by rfl) ⟨208581, by rfl⟩ : syracuseStep 556217 = 417163) B417163
theorem B621857 : Blo 243817 621857 := bstep (se 2 (by rfl) ⟨233196, by rfl⟩ : syracuseStep 621857 = 466393) B466393
theorem B294203 : Blo 243817 294203 := bstep (se 1 (by rfl) ⟨220652, by rfl⟩ : syracuseStep 294203 = 441305) B441305
theorem B4521401 : Blo 243817 4521401 := bstep (se 2 (by rfl) ⟨1695525, by rfl⟩ : syracuseStep 4521401 = 3391051) B3391051
theorem B556559 : Blo 243817 556559 := bstep (se 1 (by rfl) ⟨417419, by rfl⟩ : syracuseStep 556559 = 834839) B834839
theorem B556577 : Blo 243817 556577 := bstep (se 2 (by rfl) ⟨208716, by rfl⟩ : syracuseStep 556577 = 417433) B417433
theorem B884267 : Blo 243817 884267 := bstep (se 1 (by rfl) ⟨663200, by rfl⟩ : syracuseStep 884267 = 1326401) B1326401
theorem B1179443 : Blo 243817 1179443 := bstep (se 1 (by rfl) ⟨884582, by rfl⟩ : syracuseStep 1179443 = 1769165) B1769165
theorem B556919 : Blo 243817 556919 := bstep (se 1 (by rfl) ⟨417689, by rfl⟩ : syracuseStep 556919 = 835379) B835379
theorem B1245131 : Blo 243817 1245131 := bstep (se 1 (by rfl) ⟨933848, by rfl⟩ : syracuseStep 1245131 = 1867697) B1867697
theorem B557063 : Blo 243817 557063 := bstep (se 1 (by rfl) ⟨417797, by rfl⟩ : syracuseStep 557063 = 835595) B835595
theorem B557135 : Blo 243817 557135 := bstep (se 1 (by rfl) ⟨417851, by rfl⟩ : syracuseStep 557135 = 835703) B835703
theorem B622991 : Blo 243817 622991 := bstep (se 1 (by rfl) ⟨467243, by rfl⟩ : syracuseStep 622991 = 934487) B934487
theorem B393655 : Blo 243817 393655 := bstep (se 1 (by rfl) ⟨295241, by rfl⟩ : syracuseStep 393655 = 590483) B590483
theorem B557531 : Blo 243817 557531 := bstep (se 1 (by rfl) ⟨418148, by rfl⟩ : syracuseStep 557531 = 836297) B836297
theorem B852619 : Blo 243817 852619 := bstep (se 1 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 852619 = 1278929) B1278929
theorem B623315 : Blo 243817 623315 := bstep (se 1 (by rfl) ⟨467486, by rfl⟩ : syracuseStep 623315 = 934973) B934973
theorem B1409795 : Blo 243817 1409795 := bstep (se 1 (by rfl) ⟨1057346, by rfl⟩ : syracuseStep 1409795 = 2114693) B2114693
theorem B590665 : Blo 243817 590665 := bstep (se 2 (by rfl) ⟨221499, by rfl⟩ : syracuseStep 590665 = 442999) B442999
theorem B10617749 : Blo 243817 10617749 := bstep (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) B497707
theorem B1115063 : Blo 243817 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B1180673 : Blo 243817 1180673 := bstep (se 2 (by rfl) ⟨442752, by rfl⟩ : syracuseStep 1180673 = 885505) B885505
theorem B787475 : Blo 243817 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B590867 : Blo 243817 590867 := bstep (se 1 (by rfl) ⟨443150, by rfl⟩ : syracuseStep 590867 = 886301) B886301
theorem B5309489 : Blo 243817 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B427337 : Blo 243817 427337 := bstep (se 2 (by rfl) ⟨160251, by rfl⟩ : syracuseStep 427337 = 320503) B320503
theorem B1246589 : Blo 243817 1246589 := bstep (se 3 (by rfl) ⟨233735, by rfl⟩ : syracuseStep 1246589 = 467471) B467471
theorem B886601 : Blo 243817 886601 := bstep (se 2 (by rfl) ⟨332475, by rfl⟩ : syracuseStep 886601 = 664951) B664951
theorem B1607795 : Blo 243817 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B5966257 : Blo 243817 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B789115 : Blo 243817 789115 := bstep (se 1 (by rfl) ⟨591836, by rfl⟩ : syracuseStep 789115 = 1183673) B1183673
theorem B3345299 : Blo 243817 3345299 := bstep (se 1 (by rfl) ⟨2508974, by rfl⟩ : syracuseStep 3345299 = 5017949) B5017949
theorem B625583 : Blo 243817 625583 := bstep (se 1 (by rfl) ⟨469187, by rfl⟩ : syracuseStep 625583 = 938375) B938375
theorem B3313021 : Blo 243817 3313021 := bstep (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) B1242383
theorem B626201 : Blo 243817 626201 := bstep (se 2 (by rfl) ⟨234825, by rfl⟩ : syracuseStep 626201 = 469651) B469651
theorem B2789153 : Blo 243817 2789153 := bstep (se 2 (by rfl) ⟨1045932, by rfl⟩ : syracuseStep 2789153 = 2091865) B2091865
theorem B1773521 : Blo 243817 1773521 := bstep (se 2 (by rfl) ⟨665070, by rfl⟩ : syracuseStep 1773521 = 1330141) B1330141
theorem B888839 : Blo 243817 888839 := bstep (se 1 (by rfl) ⟨666629, by rfl⟩ : syracuseStep 888839 = 1333259) B1333259
theorem B463097 : Blo 243817 463097 := bstep (se 2 (by rfl) ⟨173661, by rfl⟩ : syracuseStep 463097 = 347323) B347323
theorem B1052939 : Blo 243817 1052939 := bstep (se 1 (by rfl) ⟨789704, by rfl⟩ : syracuseStep 1052939 = 1579409) B1579409
theorem B528905 : Blo 243817 528905 := bstep (se 2 (by rfl) ⟨198339, by rfl⟩ : syracuseStep 528905 = 396679) B396679
theorem B823931 : Blo 243817 823931 := bstep (se 1 (by rfl) ⟨617948, by rfl⟩ : syracuseStep 823931 = 1235897) B1235897
theorem B660107 : Blo 243817 660107 := bstep (se 1 (by rfl) ⟨495080, by rfl⟩ : syracuseStep 660107 = 990161) B990161
theorem B1872557 : Blo 243817 1872557 := bstep (se 3 (by rfl) ⟨351104, by rfl⟩ : syracuseStep 1872557 = 702209) B702209
theorem B2659027 : Blo 243817 2659027 := bstep (se 1 (by rfl) ⟨1994270, by rfl⟩ : syracuseStep 2659027 = 3988541) B3988541
theorem B824093 : Blo 243817 824093 := bstep (se 3 (by rfl) ⟨154517, by rfl⟩ : syracuseStep 824093 = 309035) B309035
theorem B5083955 : Blo 243817 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B529247 : Blo 243817 529247 := bstep (se 1 (by rfl) ⟨396935, by rfl⟩ : syracuseStep 529247 = 793871) B793871
theorem B365999 : Blo 243817 365999 := bstep (se 1 (by rfl) ⟨274499, by rfl⟩ : syracuseStep 365999 = 548999) B548999
theorem B824795 : Blo 243817 824795 := bstep (se 1 (by rfl) ⟨618596, by rfl⟩ : syracuseStep 824795 = 1237193) B1237193
theorem B5969371 : Blo 243817 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B366089 : Blo 243817 366089 := bstep (se 2 (by rfl) ⟨137283, by rfl⟩ : syracuseStep 366089 = 274567) B274567
theorem B792089 : Blo 243817 792089 := bstep (se 2 (by rfl) ⟨297033, by rfl⟩ : syracuseStep 792089 = 594067) B594067
theorem B366119 : Blo 243817 366119 := bstep (se 1 (by rfl) ⟨274589, by rfl⟩ : syracuseStep 366119 = 549179) B549179
theorem B10163809 : Blo 243817 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B366203 : Blo 243817 366203 := bstep (se 1 (by rfl) ⟨274652, by rfl⟩ : syracuseStep 366203 = 549305) B549305
theorem B1250963 : Blo 243817 1250963 := bstep (se 1 (by rfl) ⟨938222, by rfl⟩ : syracuseStep 1250963 = 1876445) B1876445
theorem B464555 : Blo 243817 464555 := bstep (se 1 (by rfl) ⟨348416, by rfl⟩ : syracuseStep 464555 = 696833) B696833
theorem B366329 : Blo 243817 366329 := bstep (se 2 (by rfl) ⟨137373, by rfl⟩ : syracuseStep 366329 = 274747) B274747
theorem B366431 : Blo 243817 366431 := bstep (se 1 (by rfl) ⟨274823, by rfl⟩ : syracuseStep 366431 = 549647) B549647
theorem B497513 : Blo 243817 497513 := bstep (se 2 (by rfl) ⟨186567, by rfl⟩ : syracuseStep 497513 = 373135) B373135
theorem B366443 : Blo 243817 366443 := bstep (se 1 (by rfl) ⟨274832, by rfl⟩ : syracuseStep 366443 = 549665) B549665
theorem B464935 : Blo 243817 464935 := bstep (se 1 (by rfl) ⟨348701, by rfl⟩ : syracuseStep 464935 = 697403) B697403
theorem B366671 : Blo 243817 366671 := bstep (se 1 (by rfl) ⟨275003, by rfl⟩ : syracuseStep 366671 = 550007) B550007
theorem B825497 : Blo 243817 825497 := bstep (se 2 (by rfl) ⟨309561, by rfl⟩ : syracuseStep 825497 = 619123) B619123
theorem B366791 : Blo 243817 366791 := bstep (se 1 (by rfl) ⟨275093, by rfl⟩ : syracuseStep 366791 = 550187) B550187
theorem B465095 : Blo 243817 465095 := bstep (se 1 (by rfl) ⟨348821, by rfl⟩ : syracuseStep 465095 = 697643) B697643
theorem B366953 : Blo 243817 366953 := bstep (se 2 (by rfl) ⟨137607, by rfl⟩ : syracuseStep 366953 = 275215) B275215
theorem B2660759 : Blo 243817 2660759 := bstep (se 1 (by rfl) ⟨1995569, by rfl⟩ : syracuseStep 2660759 = 3991139) B3991139
theorem B367031 : Blo 243817 367031 := bstep (se 1 (by rfl) ⟨275273, by rfl⟩ : syracuseStep 367031 = 550547) B550547
theorem B367067 : Blo 243817 367067 := bstep (se 1 (by rfl) ⟨275300, by rfl⟩ : syracuseStep 367067 = 550601) B550601
theorem B1055213 : Blo 243817 1055213 := bstep (se 3 (by rfl) ⟨197852, by rfl⟩ : syracuseStep 1055213 = 395705) B395705
theorem B4758365 : Blo 243817 4758365 := bstep (se 3 (by rfl) ⟨892193, by rfl⟩ : syracuseStep 4758365 = 1784387) B1784387
theorem B367535 : Blo 243817 367535 := bstep (se 1 (by rfl) ⟨275651, by rfl⟩ : syracuseStep 367535 = 551303) B551303
theorem B3611621 : Blo 243817 3611621 := bstep (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) B677179
theorem B793601 : Blo 243817 793601 := bstep (se 2 (by rfl) ⟨297600, by rfl⟩ : syracuseStep 793601 = 595201) B595201
theorem B367625 : Blo 243817 367625 := bstep (se 2 (by rfl) ⟨137859, by rfl⟩ : syracuseStep 367625 = 275719) B275719
theorem B367655 : Blo 243817 367655 := bstep (se 1 (by rfl) ⟨275741, by rfl⟩ : syracuseStep 367655 = 551483) B551483
theorem B1874987 : Blo 243817 1874987 := bstep (se 1 (by rfl) ⟨1406240, by rfl⟩ : syracuseStep 1874987 = 2812481) B2812481
theorem B695375 : Blo 243817 695375 := bstep (se 1 (by rfl) ⟨521531, by rfl⟩ : syracuseStep 695375 = 1043063) B1043063
theorem B367739 : Blo 243817 367739 := bstep (se 1 (by rfl) ⟨275804, by rfl⟩ : syracuseStep 367739 = 551609) B551609
theorem B367865 : Blo 243817 367865 := bstep (se 2 (by rfl) ⟨137949, by rfl⟩ : syracuseStep 367865 = 275899) B275899
theorem B826685 : Blo 243817 826685 := bstep (se 3 (by rfl) ⟨155003, by rfl⟩ : syracuseStep 826685 = 310007) B310007
theorem B466249 : Blo 243817 466249 := bstep (se 2 (by rfl) ⟨174843, by rfl⟩ : syracuseStep 466249 = 349687) B349687
theorem B367967 : Blo 243817 367967 := bstep (se 1 (by rfl) ⟨275975, by rfl⟩ : syracuseStep 367967 = 551951) B551951
theorem B367979 : Blo 243817 367979 := bstep (se 1 (by rfl) ⟨275984, by rfl⟩ : syracuseStep 367979 = 551969) B551969
theorem B368207 : Blo 243817 368207 := bstep (se 1 (by rfl) ⟨276155, by rfl⟩ : syracuseStep 368207 = 552311) B552311
theorem B368327 : Blo 243817 368327 := bstep (se 1 (by rfl) ⟨276245, by rfl⟩ : syracuseStep 368327 = 552491) B552491
theorem B368489 : Blo 243817 368489 := bstep (se 2 (by rfl) ⟨138183, by rfl⟩ : syracuseStep 368489 = 276367) B276367
theorem B3383171 : Blo 243817 3383171 := bstep (se 1 (by rfl) ⟨2537378, by rfl⟩ : syracuseStep 3383171 = 5074757) B5074757
theorem B368567 : Blo 243817 368567 := bstep (se 1 (by rfl) ⟨276425, by rfl⟩ : syracuseStep 368567 = 552851) B552851
theorem B3579835 : Blo 243817 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B368603 : Blo 243817 368603 := bstep (se 1 (by rfl) ⟨276452, by rfl⟩ : syracuseStep 368603 = 552905) B552905
theorem B696377 : Blo 243817 696377 := bstep (se 2 (by rfl) ⟨261141, by rfl⟩ : syracuseStep 696377 = 522283) B522283
theorem B827549 : Blo 243817 827549 := bstep (se 3 (by rfl) ⟨155165, by rfl⟩ : syracuseStep 827549 = 310331) B310331
theorem B631145 : Blo 243817 631145 := bstep (se 2 (by rfl) ⟨236679, by rfl⟩ : syracuseStep 631145 = 473359) B473359
theorem B369071 : Blo 243817 369071 := bstep (se 1 (by rfl) ⟨276803, by rfl⟩ : syracuseStep 369071 = 553607) B553607
theorem B369161 : Blo 243817 369161 := bstep (se 2 (by rfl) ⟨138435, by rfl⟩ : syracuseStep 369161 = 276871) B276871
theorem B1188361 : Blo 243817 1188361 := bstep (se 2 (by rfl) ⟨445635, by rfl⟩ : syracuseStep 1188361 = 891271) B891271
theorem B1057313 : Blo 243817 1057313 := bstep (se 2 (by rfl) ⟨396492, by rfl⟩ : syracuseStep 1057313 = 792985) B792985
theorem B369191 : Blo 243817 369191 := bstep (se 1 (by rfl) ⟨276893, by rfl⟩ : syracuseStep 369191 = 553787) B553787
theorem B369275 : Blo 243817 369275 := bstep (se 1 (by rfl) ⟨276956, by rfl⟩ : syracuseStep 369275 = 553913) B553913
theorem B828089 : Blo 243817 828089 := bstep (se 2 (by rfl) ⟨310533, by rfl⟩ : syracuseStep 828089 = 621067) B621067
theorem B926423 : Blo 243817 926423 := bstep (se 1 (by rfl) ⟨694817, by rfl⟩ : syracuseStep 926423 = 1389635) B1389635
theorem B369401 : Blo 243817 369401 := bstep (se 2 (by rfl) ⟨138525, by rfl⟩ : syracuseStep 369401 = 277051) B277051
theorem B369503 : Blo 243817 369503 := bstep (se 1 (by rfl) ⟨277127, by rfl⟩ : syracuseStep 369503 = 554255) B554255
theorem B369515 : Blo 243817 369515 := bstep (se 1 (by rfl) ⟨277136, by rfl⟩ : syracuseStep 369515 = 554273) B554273
theorem B369743 : Blo 243817 369743 := bstep (se 1 (by rfl) ⟨277307, by rfl⟩ : syracuseStep 369743 = 554615) B554615
theorem B369863 : Blo 243817 369863 := bstep (se 1 (by rfl) ⟨277397, by rfl⟩ : syracuseStep 369863 = 554795) B554795
theorem B828683 : Blo 243817 828683 := bstep (se 1 (by rfl) ⟨621512, by rfl⟩ : syracuseStep 828683 = 1243025) B1243025
theorem B370025 : Blo 243817 370025 := bstep (se 2 (by rfl) ⟨138759, by rfl⟩ : syracuseStep 370025 = 277519) B277519
theorem B370103 : Blo 243817 370103 := bstep (se 1 (by rfl) ⟨277577, by rfl⟩ : syracuseStep 370103 = 555155) B555155
theorem B468443 : Blo 243817 468443 := bstep (se 1 (by rfl) ⟨351332, by rfl⟩ : syracuseStep 468443 = 702665) B702665
theorem B370139 : Blo 243817 370139 := bstep (se 1 (by rfl) ⟨277604, by rfl⟩ : syracuseStep 370139 = 555209) B555209
theorem B1189363 : Blo 243817 1189363 := bstep (se 1 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 1189363 = 1784045) B1784045
theorem B828953 : Blo 243817 828953 := bstep (se 2 (by rfl) ⟨310857, by rfl⟩ : syracuseStep 828953 = 621715) B621715
theorem B468679 : Blo 243817 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B1582841 : Blo 243817 1582841 := bstep (se 2 (by rfl) ⟨593565, by rfl⟩ : syracuseStep 1582841 = 1187131) B1187131
theorem B1288045 : Blo 243817 1288045 := bstep (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) B483017
theorem B370607 : Blo 243817 370607 := bstep (se 1 (by rfl) ⟨277955, by rfl⟩ : syracuseStep 370607 = 555911) B555911
theorem B370697 : Blo 243817 370697 := bstep (se 2 (by rfl) ⟨139011, by rfl⟩ : syracuseStep 370697 = 278023) B278023
theorem B370727 : Blo 243817 370727 := bstep (se 1 (by rfl) ⟨278045, by rfl⟩ : syracuseStep 370727 = 556091) B556091
theorem B370811 : Blo 243817 370811 := bstep (se 1 (by rfl) ⟨278108, by rfl⟩ : syracuseStep 370811 = 556217) B556217
theorem B370937 : Blo 243817 370937 := bstep (se 2 (by rfl) ⟨139101, by rfl⟩ : syracuseStep 370937 = 278203) B278203
theorem B371039 : Blo 243817 371039 := bstep (se 1 (by rfl) ⟨278279, by rfl⟩ : syracuseStep 371039 = 556559) B556559
theorem B371051 : Blo 243817 371051 := bstep (se 1 (by rfl) ⟨278288, by rfl⟩ : syracuseStep 371051 = 556577) B556577
theorem B371279 : Blo 243817 371279 := bstep (se 1 (by rfl) ⟨278459, by rfl⟩ : syracuseStep 371279 = 556919) B556919
theorem B830087 : Blo 243817 830087 := bstep (se 1 (by rfl) ⟨622565, by rfl⟩ : syracuseStep 830087 = 1245131) B1245131
theorem B993977 : Blo 243817 993977 := bstep (se 2 (by rfl) ⟨372741, by rfl⟩ : syracuseStep 993977 = 745483) B745483
theorem B830141 : Blo 243817 830141 := bstep (se 3 (by rfl) ⟨155651, by rfl⟩ : syracuseStep 830141 = 311303) B311303
theorem B371399 : Blo 243817 371399 := bstep (se 1 (by rfl) ⟨278549, by rfl⟩ : syracuseStep 371399 = 557099) B557099
theorem B830303 : Blo 243817 830303 := bstep (se 1 (by rfl) ⟨622727, by rfl⟩ : syracuseStep 830303 = 1245455) B1245455
theorem B371561 : Blo 243817 371561 := bstep (se 2 (by rfl) ⟨139335, by rfl⟩ : syracuseStep 371561 = 278671) B278671
theorem B1649591 : Blo 243817 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B371639 : Blo 243817 371639 := bstep (se 1 (by rfl) ⟨278729, by rfl⟩ : syracuseStep 371639 = 557459) B557459
theorem B371675 : Blo 243817 371675 := bstep (se 1 (by rfl) ⟨278756, by rfl⟩ : syracuseStep 371675 = 557513) B557513
theorem B7056355 : Blo 243817 7056355 := bstep (se 1 (by rfl) ⟨5292266, by rfl⟩ : syracuseStep 7056355 = 10584533) B10584533
theorem B830465 : Blo 243817 830465 := bstep (se 2 (by rfl) ⟨311424, by rfl⟩ : syracuseStep 830465 = 622849) B622849
theorem B2665817 : Blo 243817 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B503135 : Blo 243817 503135 := bstep (se 1 (by rfl) ⟨377351, by rfl⟩ : syracuseStep 503135 = 754703) B754703
theorem B929339 : Blo 243817 929339 := bstep (se 1 (by rfl) ⟨697004, by rfl⟩ : syracuseStep 929339 = 1394009) B1394009
theorem B700103 : Blo 243817 700103 := bstep (se 1 (by rfl) ⟨525077, by rfl⟩ : syracuseStep 700103 = 1050155) B1050155
theorem B831275 : Blo 243817 831275 := bstep (se 1 (by rfl) ⟨623456, by rfl⟩ : syracuseStep 831275 = 1246913) B1246913
theorem B274351 : Blo 243817 274351 := bstep (se 1 (by rfl) ⟨205763, by rfl⟩ : syracuseStep 274351 = 411527) B411527
theorem B831545 : Blo 243817 831545 := bstep (se 2 (by rfl) ⟨311829, by rfl⟩ : syracuseStep 831545 = 623659) B623659
theorem B372935 : Blo 243817 372935 := bstep (se 1 (by rfl) ⟨279701, by rfl⟩ : syracuseStep 372935 = 559403) B559403
theorem B274783 : Blo 243817 274783 := bstep (se 1 (by rfl) ⟨206087, by rfl⟩ : syracuseStep 274783 = 412175) B412175
theorem B831869 : Blo 243817 831869 := bstep (se 3 (by rfl) ⟨155975, by rfl⟩ : syracuseStep 831869 = 311951) B311951
theorem B799105 : Blo 243817 799105 := bstep (se 2 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 799105 = 599329) B599329
theorem B832139 : Blo 243817 832139 := bstep (se 1 (by rfl) ⟨624104, by rfl⟩ : syracuseStep 832139 = 1248209) B1248209
theorem B275143 : Blo 243817 275143 := bstep (se 1 (by rfl) ⟨206357, by rfl⟩ : syracuseStep 275143 = 412715) B412715
theorem B9679621 : Blo 243817 9679621 := bstep (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) B1814929
theorem B4207787 : Blo 243817 4207787 := bstep (se 1 (by rfl) ⟨3155840, by rfl⟩ : syracuseStep 4207787 = 6311681) B6311681
theorem B1684909 : Blo 243817 1684909 := bstep (se 3 (by rfl) ⟨315920, by rfl⟩ : syracuseStep 1684909 = 631841) B631841
theorem B1390067 : Blo 243817 1390067 := bstep (se 1 (by rfl) ⟨1042550, by rfl⟩ : syracuseStep 1390067 = 2085101) B2085101
theorem B833057 : Blo 243817 833057 := bstep (se 2 (by rfl) ⟨312396, by rfl⟩ : syracuseStep 833057 = 624793) B624793
theorem B276007 : Blo 243817 276007 := bstep (se 1 (by rfl) ⟨207005, by rfl⟩ : syracuseStep 276007 = 414011) B414011
theorem B1947223 : Blo 243817 1947223 := bstep (se 1 (by rfl) ⟨1460417, by rfl⟩ : syracuseStep 1947223 = 2920835) B2920835
theorem B1357511 : Blo 243817 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B4503239 : Blo 243817 4503239 := bstep (se 1 (by rfl) ⟨3377429, by rfl⟩ : syracuseStep 4503239 = 6754859) B6754859
theorem B833273 : Blo 243817 833273 := bstep (se 2 (by rfl) ⟨312477, by rfl⟩ : syracuseStep 833273 = 624955) B624955
theorem B3192671 : Blo 243817 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B833543 : Blo 243817 833543 := bstep (se 1 (by rfl) ⟨625157, by rfl⟩ : syracuseStep 833543 = 1250315) B1250315
theorem B833651 : Blo 243817 833651 := bstep (se 1 (by rfl) ⟨625238, by rfl⟩ : syracuseStep 833651 = 1250477) B1250477
theorem B243835 : Blo 243817 243835 := bstep (se 1 (by rfl) ⟨182876, by rfl⟩ : syracuseStep 243835 = 365753) B365753
theorem B243887 : Blo 243817 243887 := bstep (se 1 (by rfl) ⟨182915, by rfl⟩ : syracuseStep 243887 = 365831) B365831
theorem B243911 : Blo 243817 243911 := bstep (se 1 (by rfl) ⟨182933, by rfl⟩ : syracuseStep 243911 = 365867) B365867
theorem B440531 : Blo 243817 440531 := bstep (se 1 (by rfl) ⟨330398, by rfl⟩ : syracuseStep 440531 = 660797) B660797
theorem B243931 : Blo 243817 243931 := bstep (se 1 (by rfl) ⟨182948, by rfl⟩ : syracuseStep 243931 = 365897) B365897
theorem B932087 : Blo 243817 932087 := bstep (se 1 (by rfl) ⟨699065, by rfl⟩ : syracuseStep 932087 = 1398131) B1398131
theorem B244007 : Blo 243817 244007 := bstep (se 1 (by rfl) ⟨183005, by rfl⟩ : syracuseStep 244007 = 366011) B366011
theorem B244047 : Blo 243817 244047 := bstep (se 1 (by rfl) ⟨183035, by rfl⟩ : syracuseStep 244047 = 366071) B366071
theorem B244063 : Blo 243817 244063 := bstep (se 1 (by rfl) ⟨183047, by rfl⟩ : syracuseStep 244063 = 366095) B366095
theorem B244091 : Blo 243817 244091 := bstep (se 1 (by rfl) ⟨183068, by rfl⟩ : syracuseStep 244091 = 366137) B366137
theorem B833921 : Blo 243817 833921 := bstep (se 2 (by rfl) ⟨312720, by rfl⟩ : syracuseStep 833921 = 625441) B625441
theorem B244143 : Blo 243817 244143 := bstep (se 1 (by rfl) ⟨183107, by rfl⟩ : syracuseStep 244143 = 366215) B366215
theorem B244167 : Blo 243817 244167 := bstep (se 1 (by rfl) ⟨183125, by rfl⟩ : syracuseStep 244167 = 366251) B366251
theorem B244187 : Blo 243817 244187 := bstep (se 1 (by rfl) ⟨183140, by rfl⟩ : syracuseStep 244187 = 366281) B366281
theorem B244263 : Blo 243817 244263 := bstep (se 1 (by rfl) ⟨183197, by rfl⟩ : syracuseStep 244263 = 366395) B366395
theorem B244303 : Blo 243817 244303 := bstep (se 1 (by rfl) ⟨183227, by rfl⟩ : syracuseStep 244303 = 366455) B366455
theorem B244319 : Blo 243817 244319 := bstep (se 1 (by rfl) ⟨183239, by rfl⟩ : syracuseStep 244319 = 366479) B366479
theorem B244347 : Blo 243817 244347 := bstep (se 1 (by rfl) ⟨183260, by rfl⟩ : syracuseStep 244347 = 366521) B366521
theorem B244399 : Blo 243817 244399 := bstep (se 1 (by rfl) ⟨183299, by rfl⟩ : syracuseStep 244399 = 366599) B366599
theorem B244423 : Blo 243817 244423 := bstep (se 1 (by rfl) ⟨183317, by rfl⟩ : syracuseStep 244423 = 366635) B366635
theorem B244443 : Blo 243817 244443 := bstep (se 1 (by rfl) ⟨183332, by rfl⟩ : syracuseStep 244443 = 366665) B366665
theorem B244519 : Blo 243817 244519 := bstep (se 1 (by rfl) ⟨183389, by rfl⟩ : syracuseStep 244519 = 366779) B366779
theorem B244559 : Blo 243817 244559 := bstep (se 1 (by rfl) ⟨183419, by rfl⟩ : syracuseStep 244559 = 366839) B366839
theorem B244575 : Blo 243817 244575 := bstep (se 1 (by rfl) ⟨183431, by rfl⟩ : syracuseStep 244575 = 366863) B366863
theorem B375659 : Blo 243817 375659 := bstep (se 1 (by rfl) ⟨281744, by rfl⟩ : syracuseStep 375659 = 563489) B563489
theorem B244603 : Blo 243817 244603 := bstep (se 1 (by rfl) ⟨183452, by rfl⟩ : syracuseStep 244603 = 366905) B366905
theorem B244655 : Blo 243817 244655 := bstep (se 1 (by rfl) ⟨183491, by rfl⟩ : syracuseStep 244655 = 366983) B366983
theorem B244679 : Blo 243817 244679 := bstep (se 1 (by rfl) ⟨183509, by rfl⟩ : syracuseStep 244679 = 367019) B367019
theorem B244699 : Blo 243817 244699 := bstep (se 1 (by rfl) ⟨183524, by rfl⟩ : syracuseStep 244699 = 367049) B367049
theorem B244775 : Blo 243817 244775 := bstep (se 1 (by rfl) ⟨183581, by rfl⟩ : syracuseStep 244775 = 367163) B367163
theorem B834617 : Blo 243817 834617 := bstep (se 2 (by rfl) ⟨312981, by rfl⟩ : syracuseStep 834617 = 625963) B625963
theorem B244815 : Blo 243817 244815 := bstep (se 1 (by rfl) ⟨183611, by rfl⟩ : syracuseStep 244815 = 367223) B367223
theorem B244831 : Blo 243817 244831 := bstep (se 1 (by rfl) ⟨183623, by rfl⟩ : syracuseStep 244831 = 367247) B367247
theorem B244859 : Blo 243817 244859 := bstep (se 1 (by rfl) ⟨183644, by rfl⟩ : syracuseStep 244859 = 367289) B367289
theorem B277627 : Blo 243817 277627 := bstep (se 1 (by rfl) ⟨208220, by rfl⟩ : syracuseStep 277627 = 416441) B416441
theorem B834731 : Blo 243817 834731 := bstep (se 1 (by rfl) ⟨626048, by rfl⟩ : syracuseStep 834731 = 1252097) B1252097
theorem B244911 : Blo 243817 244911 := bstep (se 1 (by rfl) ⟨183683, by rfl⟩ : syracuseStep 244911 = 367367) B367367
theorem B933059 : Blo 243817 933059 := bstep (se 1 (by rfl) ⟨699794, by rfl⟩ : syracuseStep 933059 = 1399589) B1399589
theorem B244935 : Blo 243817 244935 := bstep (se 1 (by rfl) ⟨183701, by rfl⟩ : syracuseStep 244935 = 367403) B367403
theorem B244955 : Blo 243817 244955 := bstep (se 1 (by rfl) ⟨183716, by rfl⟩ : syracuseStep 244955 = 367433) B367433
theorem B4177169 : Blo 243817 4177169 := bstep (se 2 (by rfl) ⟨1566438, by rfl⟩ : syracuseStep 4177169 = 3132877) B3132877
theorem B245031 : Blo 243817 245031 := bstep (se 1 (by rfl) ⟨183773, by rfl⟩ : syracuseStep 245031 = 367547) B367547
theorem B245071 : Blo 243817 245071 := bstep (se 1 (by rfl) ⟨183803, by rfl⟩ : syracuseStep 245071 = 367607) B367607
theorem B245087 : Blo 243817 245087 := bstep (se 1 (by rfl) ⟨183815, by rfl⟩ : syracuseStep 245087 = 367631) B367631
theorem B245115 : Blo 243817 245115 := bstep (se 1 (by rfl) ⟨183836, by rfl⟩ : syracuseStep 245115 = 367673) B367673
theorem B245167 : Blo 243817 245167 := bstep (se 1 (by rfl) ⟨183875, by rfl⟩ : syracuseStep 245167 = 367751) B367751
theorem B310711 : Blo 243817 310711 := bstep (se 1 (by rfl) ⟨233033, by rfl⟩ : syracuseStep 310711 = 466067) B466067
theorem B245191 : Blo 243817 245191 := bstep (se 1 (by rfl) ⟨183893, by rfl⟩ : syracuseStep 245191 = 367787) B367787
theorem B245211 : Blo 243817 245211 := bstep (se 1 (by rfl) ⟨183908, by rfl⟩ : syracuseStep 245211 = 367817) B367817
theorem B245287 : Blo 243817 245287 := bstep (se 1 (by rfl) ⟨183965, by rfl⟩ : syracuseStep 245287 = 367931) B367931
theorem B245327 : Blo 243817 245327 := bstep (se 1 (by rfl) ⟨183995, by rfl⟩ : syracuseStep 245327 = 367991) B367991
theorem B278095 : Blo 243817 278095 := bstep (se 1 (by rfl) ⟨208571, by rfl⟩ : syracuseStep 278095 = 417143) B417143
theorem B245343 : Blo 243817 245343 := bstep (se 1 (by rfl) ⟨184007, by rfl⟩ : syracuseStep 245343 = 368015) B368015
theorem B245371 : Blo 243817 245371 := bstep (se 1 (by rfl) ⟨184028, by rfl⟩ : syracuseStep 245371 = 368057) B368057
theorem B704123 : Blo 243817 704123 := bstep (se 1 (by rfl) ⟨528092, by rfl⟩ : syracuseStep 704123 = 1056185) B1056185
theorem B933515 : Blo 243817 933515 := bstep (se 1 (by rfl) ⟨700136, by rfl⟩ : syracuseStep 933515 = 1400273) B1400273
theorem B245423 : Blo 243817 245423 := bstep (se 1 (by rfl) ⟨184067, by rfl⟩ : syracuseStep 245423 = 368135) B368135
theorem B1982141 : Blo 243817 1982141 := bstep (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) B743303
theorem B245447 : Blo 243817 245447 := bstep (se 1 (by rfl) ⟨184085, by rfl⟩ : syracuseStep 245447 = 368171) B368171
theorem B835271 : Blo 243817 835271 := bstep (se 1 (by rfl) ⟨626453, by rfl⟩ : syracuseStep 835271 = 1252907) B1252907
theorem B245467 : Blo 243817 245467 := bstep (se 1 (by rfl) ⟨184100, by rfl⟩ : syracuseStep 245467 = 368201) B368201
theorem B245543 : Blo 243817 245543 := bstep (se 1 (by rfl) ⟨184157, by rfl⟩ : syracuseStep 245543 = 368315) B368315
theorem B245583 : Blo 243817 245583 := bstep (se 1 (by rfl) ⟨184187, by rfl⟩ : syracuseStep 245583 = 368375) B368375
theorem B245599 : Blo 243817 245599 := bstep (se 1 (by rfl) ⟨184199, by rfl⟩ : syracuseStep 245599 = 368399) B368399
theorem B933727 : Blo 243817 933727 := bstep (se 1 (by rfl) ⟨700295, by rfl⟩ : syracuseStep 933727 = 1400591) B1400591
theorem B704351 : Blo 243817 704351 := bstep (se 1 (by rfl) ⟨528263, by rfl⟩ : syracuseStep 704351 = 1056527) B1056527
theorem B245627 : Blo 243817 245627 := bstep (se 1 (by rfl) ⟨184220, by rfl⟩ : syracuseStep 245627 = 368441) B368441
theorem B245679 : Blo 243817 245679 := bstep (se 1 (by rfl) ⟨184259, by rfl⟩ : syracuseStep 245679 = 368519) B368519
theorem B245703 : Blo 243817 245703 := bstep (se 1 (by rfl) ⟨184277, by rfl⟩ : syracuseStep 245703 = 368555) B368555
theorem B245723 : Blo 243817 245723 := bstep (se 1 (by rfl) ⟨184292, by rfl⟩ : syracuseStep 245723 = 368585) B368585
theorem B278491 : Blo 243817 278491 := bstep (se 1 (by rfl) ⟨208868, by rfl⟩ : syracuseStep 278491 = 417737) B417737
theorem B1982501 : Blo 243817 1982501 := bstep (se 4 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 1982501 = 371719) B371719
theorem B245799 : Blo 243817 245799 := bstep (se 1 (by rfl) ⟨184349, by rfl⟩ : syracuseStep 245799 = 368699) B368699
theorem B245839 : Blo 243817 245839 := bstep (se 1 (by rfl) ⟨184379, by rfl⟩ : syracuseStep 245839 = 368759) B368759
theorem B999503 : Blo 243817 999503 := bstep (se 1 (by rfl) ⟨749627, by rfl⟩ : syracuseStep 999503 = 1499255) B1499255
theorem B245855 : Blo 243817 245855 := bstep (se 1 (by rfl) ⟨184391, by rfl⟩ : syracuseStep 245855 = 368783) B368783
theorem B245883 : Blo 243817 245883 := bstep (se 1 (by rfl) ⟨184412, by rfl⟩ : syracuseStep 245883 = 368825) B368825
theorem B245935 : Blo 243817 245935 := bstep (se 1 (by rfl) ⟨184451, by rfl⟩ : syracuseStep 245935 = 368903) B368903
theorem B245959 : Blo 243817 245959 := bstep (se 1 (by rfl) ⟨184469, by rfl⟩ : syracuseStep 245959 = 368939) B368939
theorem B245979 : Blo 243817 245979 := bstep (se 1 (by rfl) ⟨184484, by rfl⟩ : syracuseStep 245979 = 368969) B368969
theorem B1851659 : Blo 243817 1851659 := bstep (se 1 (by rfl) ⟨1388744, by rfl⟩ : syracuseStep 1851659 = 2777489) B2777489
theorem B246055 : Blo 243817 246055 := bstep (se 1 (by rfl) ⟨184541, by rfl⟩ : syracuseStep 246055 = 369083) B369083
theorem B246095 : Blo 243817 246095 := bstep (se 1 (by rfl) ⟨184571, by rfl⟩ : syracuseStep 246095 = 369143) B369143
theorem B1392983 : Blo 243817 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B246111 : Blo 243817 246111 := bstep (se 1 (by rfl) ⟨184583, by rfl⟩ : syracuseStep 246111 = 369167) B369167
theorem B246139 : Blo 243817 246139 := bstep (se 1 (by rfl) ⟨184604, by rfl⟩ : syracuseStep 246139 = 369209) B369209
theorem B246191 : Blo 243817 246191 := bstep (se 1 (by rfl) ⟨184643, by rfl⟩ : syracuseStep 246191 = 369287) B369287
theorem B246215 : Blo 243817 246215 := bstep (se 1 (by rfl) ⟨184661, by rfl⟩ : syracuseStep 246215 = 369323) B369323
theorem B246235 : Blo 243817 246235 := bstep (se 1 (by rfl) ⟨184676, by rfl⟩ : syracuseStep 246235 = 369353) B369353
theorem B442919 : Blo 243817 442919 := bstep (se 1 (by rfl) ⟨332189, by rfl⟩ : syracuseStep 442919 = 664379) B664379
theorem B246311 : Blo 243817 246311 := bstep (se 1 (by rfl) ⟨184733, by rfl⟩ : syracuseStep 246311 = 369467) B369467
theorem B836135 : Blo 243817 836135 := bstep (se 1 (by rfl) ⟨627101, by rfl⟩ : syracuseStep 836135 = 1254203) B1254203
theorem B246351 : Blo 243817 246351 := bstep (se 1 (by rfl) ⟨184763, by rfl⟩ : syracuseStep 246351 = 369527) B369527
theorem B246367 : Blo 243817 246367 := bstep (se 1 (by rfl) ⟨184775, by rfl⟩ : syracuseStep 246367 = 369551) B369551
theorem B246395 : Blo 243817 246395 := bstep (se 1 (by rfl) ⟨184796, by rfl⟩ : syracuseStep 246395 = 369593) B369593
theorem B836243 : Blo 243817 836243 := bstep (se 1 (by rfl) ⟨627182, by rfl⟩ : syracuseStep 836243 = 1254365) B1254365
theorem B246447 : Blo 243817 246447 := bstep (se 1 (by rfl) ⟨184835, by rfl⟩ : syracuseStep 246447 = 369671) B369671
theorem B246471 : Blo 243817 246471 := bstep (se 1 (by rfl) ⟨184853, by rfl⟩ : syracuseStep 246471 = 369707) B369707
theorem B312007 : Blo 243817 312007 := bstep (se 1 (by rfl) ⟨234005, by rfl⟩ : syracuseStep 312007 = 468011) B468011
theorem B246491 : Blo 243817 246491 := bstep (se 1 (by rfl) ⟨184868, by rfl⟩ : syracuseStep 246491 = 369737) B369737
theorem B934685 : Blo 243817 934685 := bstep (se 3 (by rfl) ⟨175253, by rfl⟩ : syracuseStep 934685 = 350507) B350507
theorem B246567 : Blo 243817 246567 := bstep (se 1 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 246567 = 369851) B369851
theorem B934699 : Blo 243817 934699 := bstep (se 1 (by rfl) ⟨701024, by rfl⟩ : syracuseStep 934699 = 1402049) B1402049
theorem B246607 : Blo 243817 246607 := bstep (se 1 (by rfl) ⟨184955, by rfl⟩ : syracuseStep 246607 = 369911) B369911
theorem B246623 : Blo 243817 246623 := bstep (se 1 (by rfl) ⟨184967, by rfl⟩ : syracuseStep 246623 = 369935) B369935
theorem B246651 : Blo 243817 246651 := bstep (se 1 (by rfl) ⟨184988, by rfl⟩ : syracuseStep 246651 = 369977) B369977
theorem B246703 : Blo 243817 246703 := bstep (se 1 (by rfl) ⟨185027, by rfl⟩ : syracuseStep 246703 = 370055) B370055
theorem B443323 : Blo 243817 443323 := bstep (se 1 (by rfl) ⟨332492, by rfl⟩ : syracuseStep 443323 = 664985) B664985
theorem B246727 : Blo 243817 246727 := bstep (se 1 (by rfl) ⟨185045, by rfl⟩ : syracuseStep 246727 = 370091) B370091
theorem B246747 : Blo 243817 246747 := bstep (se 1 (by rfl) ⟨185060, by rfl⟩ : syracuseStep 246747 = 370121) B370121
theorem B246823 : Blo 243817 246823 := bstep (se 1 (by rfl) ⟨185117, by rfl⟩ : syracuseStep 246823 = 370235) B370235
theorem B246863 : Blo 243817 246863 := bstep (se 1 (by rfl) ⟨185147, by rfl⟩ : syracuseStep 246863 = 370295) B370295
theorem B246879 : Blo 243817 246879 := bstep (se 1 (by rfl) ⟨185159, by rfl⟩ : syracuseStep 246879 = 370319) B370319
theorem B246907 : Blo 243817 246907 := bstep (se 1 (by rfl) ⟨185180, by rfl⟩ : syracuseStep 246907 = 370361) B370361
theorem B246959 : Blo 243817 246959 := bstep (se 1 (by rfl) ⟨185219, by rfl⟩ : syracuseStep 246959 = 370439) B370439
theorem B246983 : Blo 243817 246983 := bstep (se 1 (by rfl) ⟨185237, by rfl⟩ : syracuseStep 246983 = 370475) B370475
theorem B247003 : Blo 243817 247003 := bstep (se 1 (by rfl) ⟨185252, by rfl⟩ : syracuseStep 247003 = 370505) B370505
theorem B247079 : Blo 243817 247079 := bstep (se 1 (by rfl) ⟨185309, by rfl⟩ : syracuseStep 247079 = 370619) B370619
theorem B247119 : Blo 243817 247119 := bstep (se 1 (by rfl) ⟨185339, by rfl⟩ : syracuseStep 247119 = 370679) B370679
theorem B247135 : Blo 243817 247135 := bstep (se 1 (by rfl) ⟨185351, by rfl⟩ : syracuseStep 247135 = 370703) B370703
theorem B247163 : Blo 243817 247163 := bstep (se 1 (by rfl) ⟨185372, by rfl⟩ : syracuseStep 247163 = 370745) B370745
theorem B4343203 : Blo 243817 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B312751 : Blo 243817 312751 := bstep (se 1 (by rfl) ⟨234563, by rfl⟩ : syracuseStep 312751 = 469127) B469127
theorem B247215 : Blo 243817 247215 := bstep (se 1 (by rfl) ⟨185411, by rfl⟩ : syracuseStep 247215 = 370823) B370823
theorem B247239 : Blo 243817 247239 := bstep (se 1 (by rfl) ⟨185429, by rfl⟩ : syracuseStep 247239 = 370859) B370859
theorem B247259 : Blo 243817 247259 := bstep (se 1 (by rfl) ⟨185444, by rfl⟩ : syracuseStep 247259 = 370889) B370889
theorem B247335 : Blo 243817 247335 := bstep (se 1 (by rfl) ⟨185501, by rfl⟩ : syracuseStep 247335 = 371003) B371003
theorem B247375 : Blo 243817 247375 := bstep (se 1 (by rfl) ⟨185531, by rfl⟩ : syracuseStep 247375 = 371063) B371063
theorem B247391 : Blo 243817 247391 := bstep (se 1 (by rfl) ⟨185543, by rfl⟩ : syracuseStep 247391 = 371087) B371087
theorem B247419 : Blo 243817 247419 := bstep (se 1 (by rfl) ⟨185564, by rfl⟩ : syracuseStep 247419 = 371129) B371129
theorem B247471 : Blo 243817 247471 := bstep (se 1 (by rfl) ⟨185603, by rfl⟩ : syracuseStep 247471 = 371207) B371207
theorem B1853117 : Blo 243817 1853117 := bstep (se 3 (by rfl) ⟨347459, by rfl⟩ : syracuseStep 1853117 = 694919) B694919
theorem B247495 : Blo 243817 247495 := bstep (se 1 (by rfl) ⟨185621, by rfl⟩ : syracuseStep 247495 = 371243) B371243
theorem B247515 : Blo 243817 247515 := bstep (se 1 (by rfl) ⟨185636, by rfl⟩ : syracuseStep 247515 = 371273) B371273
theorem B247591 : Blo 243817 247591 := bstep (se 1 (by rfl) ⟨185693, by rfl⟩ : syracuseStep 247591 = 371387) B371387
theorem B247631 : Blo 243817 247631 := bstep (se 1 (by rfl) ⟨185723, by rfl⟩ : syracuseStep 247631 = 371447) B371447
theorem B247647 : Blo 243817 247647 := bstep (se 1 (by rfl) ⟨185735, by rfl⟩ : syracuseStep 247647 = 371471) B371471
theorem B247675 : Blo 243817 247675 := bstep (se 1 (by rfl) ⟨185756, by rfl⟩ : syracuseStep 247675 = 371513) B371513
theorem B247727 : Blo 243817 247727 := bstep (se 1 (by rfl) ⟨185795, by rfl⟩ : syracuseStep 247727 = 371591) B371591
theorem B247751 : Blo 243817 247751 := bstep (se 1 (by rfl) ⟨185813, by rfl⟩ : syracuseStep 247751 = 371627) B371627
theorem B247771 : Blo 243817 247771 := bstep (se 1 (by rfl) ⟨185828, by rfl⟩ : syracuseStep 247771 = 371657) B371657
theorem B411655 : Blo 243817 411655 := bstep (se 1 (by rfl) ⟨308741, by rfl⟩ : syracuseStep 411655 = 617483) B617483
theorem B3426461 : Blo 243817 3426461 := bstep (se 3 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 3426461 = 1284923) B1284923
theorem B1853603 : Blo 243817 1853603 := bstep (se 1 (by rfl) ⟨1390202, by rfl⟩ : syracuseStep 1853603 = 2780405) B2780405
theorem B3524897 : Blo 243817 3524897 := bstep (se 2 (by rfl) ⟨1321836, by rfl⟩ : syracuseStep 3524897 = 2643673) B2643673
theorem B1886597 : Blo 243817 1886597 := bstep (se 4 (by rfl) ⟨176868, by rfl⟩ : syracuseStep 1886597 = 353737) B353737
theorem B412087 : Blo 243817 412087 := bstep (se 1 (by rfl) ⟨309065, by rfl⟩ : syracuseStep 412087 = 618131) B618131
theorem B412283 : Blo 243817 412283 := bstep (se 1 (by rfl) ⟨309212, by rfl⟩ : syracuseStep 412283 = 618425) B618425
theorem B1264567 : Blo 243817 1264567 := bstep (se 1 (by rfl) ⟨948425, by rfl⟩ : syracuseStep 1264567 = 1896851) B1896851
theorem B412681 : Blo 243817 412681 := bstep (se 2 (by rfl) ⟨154755, by rfl⟩ : syracuseStep 412681 = 309511) B309511
theorem B412843 : Blo 243817 412843 := bstep (se 1 (by rfl) ⟨309632, by rfl⟩ : syracuseStep 412843 = 619265) B619265
theorem B413147 : Blo 243817 413147 := bstep (se 1 (by rfl) ⟨309860, by rfl⟩ : syracuseStep 413147 = 619721) B619721
theorem B2346583 : Blo 243817 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B413383 : Blo 243817 413383 := bstep (se 1 (by rfl) ⟨310037, by rfl⟩ : syracuseStep 413383 = 620075) B620075
theorem B413545 : Blo 243817 413545 := bstep (se 2 (by rfl) ⟨155079, by rfl⟩ : syracuseStep 413545 = 310159) B310159
theorem B479083 : Blo 243817 479083 := bstep (se 1 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 479083 = 718625) B718625
theorem B937889 : Blo 243817 937889 := bstep (se 2 (by rfl) ⟨351708, by rfl⟩ : syracuseStep 937889 = 703417) B703417
theorem B1396673 : Blo 243817 1396673 := bstep (se 2 (by rfl) ⟨523752, by rfl⟩ : syracuseStep 1396673 = 1047505) B1047505
theorem B250151 : Blo 243817 250151 := bstep (se 1 (by rfl) ⟨187613, by rfl⟩ : syracuseStep 250151 = 375227) B375227
theorem B414139 : Blo 243817 414139 := bstep (se 1 (by rfl) ⟨310604, by rfl⟩ : syracuseStep 414139 = 621209) B621209
theorem B1856033 : Blo 243817 1856033 := bstep (se 2 (by rfl) ⟨696012, by rfl⟩ : syracuseStep 1856033 = 1392025) B1392025
theorem B414247 : Blo 243817 414247 := bstep (se 1 (by rfl) ⟨310685, by rfl⟩ : syracuseStep 414247 = 621371) B621371
theorem B414571 : Blo 243817 414571 := bstep (se 1 (by rfl) ⟨310928, by rfl⟩ : syracuseStep 414571 = 621857) B621857
theorem B938861 : Blo 243817 938861 := bstep (se 3 (by rfl) ⟨176036, by rfl⟩ : syracuseStep 938861 = 352073) B352073
theorem B2249693 : Blo 243817 2249693 := bstep (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) B843635
theorem B939545 : Blo 243817 939545 := bstep (se 2 (by rfl) ⟨352329, by rfl⟩ : syracuseStep 939545 = 704659) B704659
theorem B939559 : Blo 243817 939559 := bstep (se 1 (by rfl) ⟨704669, by rfl⟩ : syracuseStep 939559 = 1409339) B1409339
theorem B415631 : Blo 243817 415631 := bstep (se 1 (by rfl) ⟨311723, by rfl⟩ : syracuseStep 415631 = 623447) B623447
theorem B4773977 : Blo 243817 4773977 := bstep (se 2 (by rfl) ⟨1790241, by rfl⟩ : syracuseStep 4773977 = 3580483) B3580483
theorem B415867 : Blo 243817 415867 := bstep (se 1 (by rfl) ⟨311900, by rfl⟩ : syracuseStep 415867 = 623801) B623801
theorem B940349 : Blo 243817 940349 := bstep (se 3 (by rfl) ⟨176315, by rfl⟩ : syracuseStep 940349 = 352631) B352631
theorem B940531 : Blo 243817 940531 := bstep (se 1 (by rfl) ⟨705398, by rfl⟩ : syracuseStep 940531 = 1410797) B1410797
theorem B1333793 : Blo 243817 1333793 := bstep (se 2 (by rfl) ⟨500172, by rfl⟩ : syracuseStep 1333793 = 1000345) B1000345
theorem B711607 : Blo 243817 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B416731 : Blo 243817 416731 := bstep (se 1 (by rfl) ⟨312548, by rfl⟩ : syracuseStep 416731 = 625097) B625097
theorem B1268939 : Blo 243817 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B351481 : Blo 243817 351481 := bstep (se 2 (by rfl) ⟨131805, by rfl⟩ : syracuseStep 351481 = 263611) B263611
theorem B2874797 : Blo 243817 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B417359 : Blo 243817 417359 := bstep (se 1 (by rfl) ⟨313019, by rfl⟩ : syracuseStep 417359 = 626039) B626039
theorem B1498769 : Blo 243817 1498769 := bstep (se 2 (by rfl) ⟨562038, by rfl⟩ : syracuseStep 1498769 = 1124077) B1124077
theorem B2809565 : Blo 243817 2809565 := bstep (se 3 (by rfl) ⟨526793, by rfl⟩ : syracuseStep 2809565 = 1053587) B1053587
theorem B1335005 : Blo 243817 1335005 := bstep (se 3 (by rfl) ⟨250313, by rfl⟩ : syracuseStep 1335005 = 500627) B500627
theorem B5791493 : Blo 243817 5791493 := bstep (se 4 (by rfl) ⟨542952, by rfl⟩ : syracuseStep 5791493 = 1085905) B1085905
theorem B319339 : Blo 243817 319339 := bstep (se 1 (by rfl) ⟨239504, by rfl⟩ : syracuseStep 319339 = 479009) B479009
theorem B548783 : Blo 243817 548783 := bstep (se 1 (by rfl) ⟨411587, by rfl⟩ : syracuseStep 548783 = 823175) B823175
theorem B1761209 : Blo 243817 1761209 := bstep (se 2 (by rfl) ⟨660453, by rfl⟩ : syracuseStep 1761209 = 1320907) B1320907
theorem B549035 : Blo 243817 549035 := bstep (se 1 (by rfl) ⟨411776, by rfl⟩ : syracuseStep 549035 = 823553) B823553
theorem B549575 : Blo 243817 549575 := bstep (se 1 (by rfl) ⟨412181, by rfl⟩ : syracuseStep 549575 = 824363) B824363
theorem B550439 : Blo 243817 550439 := bstep (se 1 (by rfl) ⟨412829, by rfl⟩ : syracuseStep 550439 = 825659) B825659
theorem B1238651 : Blo 243817 1238651 := bstep (se 1 (by rfl) ⟨928988, by rfl⟩ : syracuseStep 1238651 = 1857977) B1857977
theorem B1763167 : Blo 243817 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B550763 : Blo 243817 550763 := bstep (se 1 (by rfl) ⟨413072, by rfl⟩ : syracuseStep 550763 = 826145) B826145
theorem B550817 : Blo 243817 550817 := bstep (se 2 (by rfl) ⟨206556, by rfl⟩ : syracuseStep 550817 = 413113) B413113
theorem B551159 : Blo 243817 551159 := bstep (se 1 (by rfl) ⟨413369, by rfl⟩ : syracuseStep 551159 = 826739) B826739
theorem B4811399 : Blo 243817 4811399 := bstep (se 1 (by rfl) ⟨3608549, by rfl⟩ : syracuseStep 4811399 = 7217099) B7217099
theorem B420599 : Blo 243817 420599 := bstep (se 1 (by rfl) ⟨315449, by rfl⟩ : syracuseStep 420599 = 630899) B630899
theorem B551753 : Blo 243817 551753 := bstep (se 2 (by rfl) ⟨206907, by rfl⟩ : syracuseStep 551753 = 413815) B413815
theorem B781427 : Blo 243817 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B781579 : Blo 243817 781579 := bstep (se 1 (by rfl) ⟨586184, by rfl⟩ : syracuseStep 781579 = 1172369) B1172369
theorem B1174985 : Blo 243817 1174985 := bstep (se 2 (by rfl) ⟨440619, by rfl⟩ : syracuseStep 1174985 = 881239) B881239
theorem B552545 : Blo 243817 552545 := bstep (se 2 (by rfl) ⟨207204, by rfl⟩ : syracuseStep 552545 = 414409) B414409
theorem B749179 : Blo 243817 749179 := bstep (se 1 (by rfl) ⟨561884, by rfl⟩ : syracuseStep 749179 = 1123769) B1123769
theorem B618313 : Blo 243817 618313 := bstep (se 2 (by rfl) ⟨231867, by rfl⟩ : syracuseStep 618313 = 463735) B463735
theorem B552887 : Blo 243817 552887 := bstep (se 1 (by rfl) ⟨414665, by rfl⟩ : syracuseStep 552887 = 829331) B829331
theorem B1404965 : Blo 243817 1404965 := bstep (se 4 (by rfl) ⟨131715, by rfl⟩ : syracuseStep 1404965 = 263431) B263431
theorem B3141899 : Blo 243817 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B1241405 : Blo 243817 1241405 := bstep (se 3 (by rfl) ⟨232763, by rfl⟩ : syracuseStep 1241405 = 465527) B465527
theorem B323947 : Blo 243817 323947 := bstep (se 1 (by rfl) ⟨242960, by rfl⟩ : syracuseStep 323947 = 485921) B485921
theorem B1405421 : Blo 243817 1405421 := bstep (se 3 (by rfl) ⟨263516, by rfl⟩ : syracuseStep 1405421 = 527033) B527033
theorem B553481 : Blo 243817 553481 := bstep (se 2 (by rfl) ⟨207555, by rfl⟩ : syracuseStep 553481 = 415111) B415111
theorem B553823 : Blo 243817 553823 := bstep (se 1 (by rfl) ⟨415367, by rfl⟩ : syracuseStep 553823 = 830735) B830735
theorem B619447 : Blo 243817 619447 := bstep (se 1 (by rfl) ⟨464585, by rfl⟩ : syracuseStep 619447 = 929171) B929171
theorem B1569719 : Blo 243817 1569719 := bstep (se 1 (by rfl) ⟨1177289, by rfl⟩ : syracuseStep 1569719 = 2354579) B2354579
theorem B1045523 : Blo 243817 1045523 := bstep (se 1 (by rfl) ⟨784142, by rfl⟩ : syracuseStep 1045523 = 1568285) B1568285
theorem B554003 : Blo 243817 554003 := bstep (se 1 (by rfl) ⟨415502, by rfl⟩ : syracuseStep 554003 = 831005) B831005
theorem B1406105 : Blo 243817 1406105 := bstep (se 2 (by rfl) ⟨527289, by rfl⟩ : syracuseStep 1406105 = 1054579) B1054579
theorem B521387 : Blo 243817 521387 := bstep (se 1 (by rfl) ⟨391040, by rfl⟩ : syracuseStep 521387 = 782081) B782081
theorem B554345 : Blo 243817 554345 := bstep (se 2 (by rfl) ⟨207879, by rfl⟩ : syracuseStep 554345 = 415759) B415759
theorem B2815397 : Blo 243817 2815397 := bstep (se 4 (by rfl) ⟨263943, by rfl⟩ : syracuseStep 2815397 = 527887) B527887
theorem B1602989 : Blo 243817 1602989 := bstep (se 3 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 1602989 = 601121) B601121
theorem B423623 : Blo 243817 423623 := bstep (se 1 (by rfl) ⟨317717, by rfl⟩ : syracuseStep 423623 = 635435) B635435
theorem B5994283 : Blo 243817 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B1570745 : Blo 243817 1570745 := bstep (se 2 (by rfl) ⟨589029, by rfl⟩ : syracuseStep 1570745 = 1178059) B1178059
theorem B554939 : Blo 243817 554939 := bstep (se 1 (by rfl) ⟨416204, by rfl⟩ : syracuseStep 554939 = 832409) B832409
theorem B784399 : Blo 243817 784399 := bstep (se 1 (by rfl) ⟨588299, by rfl⟩ : syracuseStep 784399 = 1176599) B1176599
theorem B555065 : Blo 243817 555065 := bstep (se 2 (by rfl) ⟨208149, by rfl⟩ : syracuseStep 555065 = 416299) B416299
theorem B2783321 : Blo 243817 2783321 := bstep (se 2 (by rfl) ⟨1043745, by rfl⟩ : syracuseStep 2783321 = 2087491) B2087491
theorem B292987 : Blo 243817 292987 := bstep (se 1 (by rfl) ⟨219740, by rfl⟩ : syracuseStep 292987 = 439481) B439481
theorem B784541 : Blo 243817 784541 := bstep (se 3 (by rfl) ⟨147101, by rfl⟩ : syracuseStep 784541 = 294203) B294203
theorem B391367 : Blo 243817 391367 := bstep (se 1 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 391367 = 587051) B587051
theorem B588023 : Blo 243817 588023 := bstep (se 1 (by rfl) ⟨441017, by rfl⟩ : syracuseStep 588023 = 882035) B882035
theorem B620905 : Blo 243817 620905 := bstep (se 2 (by rfl) ⟨232839, by rfl⟩ : syracuseStep 620905 = 465679) B465679
theorem B555407 : Blo 243817 555407 := bstep (se 1 (by rfl) ⟨416555, by rfl⟩ : syracuseStep 555407 = 833111) B833111
theorem B1243673 : Blo 243817 1243673 := bstep (se 2 (by rfl) ⟨466377, by rfl⟩ : syracuseStep 1243673 = 932755) B932755
theorem B3963437 : Blo 243817 3963437 := bstep (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) B1486289
theorem B621179 : Blo 243817 621179 := bstep (se 1 (by rfl) ⟨465884, by rfl⟩ : syracuseStep 621179 = 931769) B931769
theorem B555731 : Blo 243817 555731 := bstep (se 1 (by rfl) ⟨416798, by rfl⟩ : syracuseStep 555731 = 833597) B833597
theorem B523103 : Blo 243817 523103 := bstep (se 1 (by rfl) ⟨392327, by rfl⟩ : syracuseStep 523103 = 784655) B784655
theorem B392123 : Blo 243817 392123 := bstep (se 1 (by rfl) ⟨294092, by rfl⟩ : syracuseStep 392123 = 588185) B588185
theorem B1866725 : Blo 243817 1866725 := bstep (se 4 (by rfl) ⟨175005, by rfl⟩ : syracuseStep 1866725 = 350011) B350011
theorem B1178675 : Blo 243817 1178675 := bstep (se 1 (by rfl) ⟨884006, by rfl⟩ : syracuseStep 1178675 = 1768013) B1768013
theorem B523343 : Blo 243817 523343 := bstep (se 1 (by rfl) ⟨392507, by rfl⟩ : syracuseStep 523343 = 785015) B785015
theorem B392635 : Blo 243817 392635 := bstep (se 1 (by rfl) ⟨294476, by rfl⟩ : syracuseStep 392635 = 588953) B588953
theorem B556583 : Blo 243817 556583 := bstep (se 1 (by rfl) ⟨417437, by rfl⟩ : syracuseStep 556583 = 834875) B834875
theorem B556667 : Blo 243817 556667 := bstep (se 1 (by rfl) ⟨417500, by rfl⟩ : syracuseStep 556667 = 835001) B835001
theorem B3014267 : Blo 243817 3014267 := bstep (se 1 (by rfl) ⟨2260700, by rfl⟩ : syracuseStep 3014267 = 4521401) B4521401
theorem B3538565 : Blo 243817 3538565 := bstep (se 4 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 3538565 = 663481) B663481
theorem B589511 : Blo 243817 589511 := bstep (se 1 (by rfl) ⟨442133, by rfl⟩ : syracuseStep 589511 = 884267) B884267
theorem B556793 : Blo 243817 556793 := bstep (se 2 (by rfl) ⟨208797, by rfl⟩ : syracuseStep 556793 = 417595) B417595
theorem B3374963 : Blo 243817 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B786295 : Blo 243817 786295 := bstep (se 1 (by rfl) ⟨589721, by rfl⟩ : syracuseStep 786295 = 1179443) B1179443
theorem B557423 : Blo 243817 557423 := bstep (se 1 (by rfl) ⟨418067, by rfl⟩ : syracuseStep 557423 = 836135) B836135
theorem B557495 : Blo 243817 557495 := bstep (se 1 (by rfl) ⟨418121, by rfl⟩ : syracuseStep 557495 = 836243) B836243
theorem B623123 : Blo 243817 623123 := bstep (se 1 (by rfl) ⟨467342, by rfl⟩ : syracuseStep 623123 = 934685) B934685
theorem B524873 : Blo 243817 524873 := bstep (se 2 (by rfl) ⟨196827, by rfl⟩ : syracuseStep 524873 = 393655) B393655
theorem B7078499 : Blo 243817 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B787115 : Blo 243817 787115 := bstep (se 1 (by rfl) ⟨590336, by rfl⟩ : syracuseStep 787115 = 1180673) B1180673
theorem B524983 : Blo 243817 524983 := bstep (se 1 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 524983 = 787475) B787475
theorem B393911 : Blo 243817 393911 := bstep (se 1 (by rfl) ⟨295433, by rfl⟩ : syracuseStep 393911 = 590867) B590867
theorem B3539659 : Blo 243817 3539659 := bstep (se 1 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 3539659 = 5309489) B5309489
theorem B1246265 : Blo 243817 1246265 := bstep (se 2 (by rfl) ⟨467349, by rfl⟩ : syracuseStep 1246265 = 934699) B934699
theorem B787553 : Blo 243817 787553 := bstep (se 2 (by rfl) ⟨295332, by rfl⟩ : syracuseStep 787553 = 590665) B590665
theorem B591067 : Blo 243817 591067 := bstep (se 1 (by rfl) ⟨443300, by rfl⟩ : syracuseStep 591067 = 886601) B886601
theorem B1181117 : Blo 243817 1181117 := bstep (se 3 (by rfl) ⟨221459, by rfl⟩ : syracuseStep 1181117 = 442919) B442919
theorem B2230199 : Blo 243817 2230199 := bstep (se 1 (by rfl) ⟨1672649, by rfl⟩ : syracuseStep 2230199 = 3345299) B3345299
theorem B624905 : Blo 243817 624905 := bstep (se 2 (by rfl) ⟨234339, by rfl⟩ : syracuseStep 624905 = 468679) B468679
theorem B625259 : Blo 243817 625259 := bstep (se 1 (by rfl) ⟨468944, by rfl⟩ : syracuseStep 625259 = 937889) B937889
theorem B1182347 : Blo 243817 1182347 := bstep (se 1 (by rfl) ⟨886760, by rfl⟩ : syracuseStep 1182347 = 1773521) B1773521
theorem B592559 : Blo 243817 592559 := bstep (se 1 (by rfl) ⟨444419, by rfl⟩ : syracuseStep 592559 = 888839) B888839
theorem B1248371 : Blo 243817 1248371 := bstep (se 1 (by rfl) ⟨936278, by rfl⟩ : syracuseStep 1248371 = 1872557) B1872557
theorem B625907 : Blo 243817 625907 := bstep (se 1 (by rfl) ⟨469430, by rfl⟩ : syracuseStep 625907 = 938861) B938861
theorem B1052153 : Blo 243817 1052153 := bstep (se 2 (by rfl) ⟨394557, by rfl⟩ : syracuseStep 1052153 = 789115) B789115
theorem B528059 : Blo 243817 528059 := bstep (se 1 (by rfl) ⟨396044, by rfl⟩ : syracuseStep 528059 = 792089) B792089
theorem B626363 : Blo 243817 626363 := bstep (se 1 (by rfl) ⟨469772, by rfl⟩ : syracuseStep 626363 = 939545) B939545
theorem B1249181 : Blo 243817 1249181 := bstep (se 3 (by rfl) ⟨234221, by rfl⟩ : syracuseStep 1249181 = 468443) B468443
theorem B9408473 : Blo 243817 9408473 := bstep (se 2 (by rfl) ⟨3528177, by rfl⟩ : syracuseStep 9408473 = 7056355) B7056355
theorem B3182651 : Blo 243817 3182651 := bstep (se 1 (by rfl) ⟨2386988, by rfl⟩ : syracuseStep 3182651 = 4773977) B4773977
theorem B626899 : Blo 243817 626899 := bstep (se 1 (by rfl) ⟨470174, by rfl⟩ : syracuseStep 626899 = 940349) B940349
theorem B1773839 : Blo 243817 1773839 := bstep (se 1 (by rfl) ⟨1330379, by rfl⟩ : syracuseStep 1773839 = 2660759) B2660759
theorem B529067 : Blo 243817 529067 := bstep (se 1 (by rfl) ⟨396800, by rfl⟩ : syracuseStep 529067 = 793601) B793601
theorem B1249991 : Blo 243817 1249991 := bstep (se 1 (by rfl) ⟨937493, by rfl⟩ : syracuseStep 1249991 = 1874987) B1874987
theorem B463583 : Blo 243817 463583 := bstep (se 1 (by rfl) ⟨347687, by rfl⟩ : syracuseStep 463583 = 695375) B695375
theorem B2364389 : Blo 243817 2364389 := bstep (se 4 (by rfl) ⟨221661, by rfl⟩ : syracuseStep 2364389 = 443323) B443323
theorem B824417 : Blo 243817 824417 := bstep (se 2 (by rfl) ⟨309156, by rfl⟩ : syracuseStep 824417 = 618313) B618313
theorem B1873043 : Blo 243817 1873043 := bstep (se 1 (by rfl) ⟨1404782, by rfl⟩ : syracuseStep 1873043 = 2809565) B2809565
theorem B890003 : Blo 243817 890003 := bstep (se 1 (by rfl) ⟨667502, by rfl⟩ : syracuseStep 890003 = 1335005) B1335005
theorem B365801 : Blo 243817 365801 := bstep (se 2 (by rfl) ⟨137175, by rfl⟩ : syracuseStep 365801 = 274351) B274351
theorem B365855 : Blo 243817 365855 := bstep (se 1 (by rfl) ⟨274391, by rfl⟩ : syracuseStep 365855 = 548783) B548783
theorem B366023 : Blo 243817 366023 := bstep (se 1 (by rfl) ⟨274517, by rfl⟩ : syracuseStep 366023 = 549035) B549035
theorem B5936885 : Blo 243817 5936885 := bstep (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) B556583
theorem B366377 : Blo 243817 366377 := bstep (se 2 (by rfl) ⟨137391, by rfl⟩ : syracuseStep 366377 = 274783) B274783
theorem B366383 : Blo 243817 366383 := bstep (se 1 (by rfl) ⟨274787, by rfl⟩ : syracuseStep 366383 = 549575) B549575
theorem B431929 : Blo 243817 431929 := bstep (se 2 (by rfl) ⟨161973, by rfl⟩ : syracuseStep 431929 = 323947) B323947
theorem B366857 : Blo 243817 366857 := bstep (se 2 (by rfl) ⟨137571, by rfl⟩ : syracuseStep 366857 = 275143) B275143
theorem B3545369 : Blo 243817 3545369 := bstep (se 2 (by rfl) ⟨1329513, by rfl⟩ : syracuseStep 3545369 = 2659027) B2659027
theorem B366959 : Blo 243817 366959 := bstep (se 1 (by rfl) ⟨275219, by rfl⟩ : syracuseStep 366959 = 550439) B550439
theorem B825767 : Blo 243817 825767 := bstep (se 1 (by rfl) ⟨619325, by rfl⟩ : syracuseStep 825767 = 1238651) B1238651
theorem B367175 : Blo 243817 367175 := bstep (se 1 (by rfl) ⟨275381, by rfl⟩ : syracuseStep 367175 = 550763) B550763
theorem B825929 : Blo 243817 825929 := bstep (se 2 (by rfl) ⟨309723, by rfl⟩ : syracuseStep 825929 = 619447) B619447
theorem B367211 : Blo 243817 367211 := bstep (se 1 (by rfl) ⟨275408, by rfl⟩ : syracuseStep 367211 = 550817) B550817
theorem B4168421 : Blo 243817 4168421 := bstep (se 4 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 4168421 = 781579) B781579
theorem B367439 : Blo 243817 367439 := bstep (se 1 (by rfl) ⟨275579, by rfl⟩ : syracuseStep 367439 = 551159) B551159
theorem B662651 : Blo 243817 662651 := bstep (se 1 (by rfl) ⟨496988, by rfl⟩ : syracuseStep 662651 = 993977) B993977
theorem B367835 : Blo 243817 367835 := bstep (se 1 (by rfl) ⟨275876, by rfl⟩ : syracuseStep 367835 = 551753) B551753
theorem B1121597 : Blo 243817 1121597 := bstep (se 3 (by rfl) ⟨210299, by rfl⟩ : syracuseStep 1121597 = 420599) B420599
theorem B368009 : Blo 243817 368009 := bstep (se 2 (by rfl) ⟨138003, by rfl⟩ : syracuseStep 368009 = 276007) B276007
theorem B1252745 : Blo 243817 1252745 := bstep (se 2 (by rfl) ⟨469779, by rfl⟩ : syracuseStep 1252745 = 939559) B939559
theorem B1777211 : Blo 243817 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B335423 : Blo 243817 335423 := bstep (se 1 (by rfl) ⟨251567, by rfl⟩ : syracuseStep 335423 = 503135) B503135
theorem B368363 : Blo 243817 368363 := bstep (se 1 (by rfl) ⟨276272, by rfl⟩ : syracuseStep 368363 = 552545) B552545
theorem B466735 : Blo 243817 466735 := bstep (se 1 (by rfl) ⟨350051, by rfl⟩ : syracuseStep 466735 = 700103) B700103
theorem B368591 : Blo 243817 368591 := bstep (se 1 (by rfl) ⟨276443, by rfl⟩ : syracuseStep 368591 = 552887) B552887
theorem B827603 : Blo 243817 827603 := bstep (se 1 (by rfl) ⟨620702, by rfl⟩ : syracuseStep 827603 = 1241405) B1241405
theorem B368987 : Blo 243817 368987 := bstep (se 1 (by rfl) ⟨276740, by rfl⟩ : syracuseStep 368987 = 553481) B553481
theorem B827873 : Blo 243817 827873 := bstep (se 2 (by rfl) ⟨310452, by rfl⟩ : syracuseStep 827873 = 620905) B620905
theorem B54206981 : Blo 243817 54206981 := bstep (se 4 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 54206981 = 10163809) B10163809
theorem B369215 : Blo 243817 369215 := bstep (se 1 (by rfl) ⟨276911, by rfl⟩ : syracuseStep 369215 = 553823) B553823
theorem B1254041 : Blo 243817 1254041 := bstep (se 2 (by rfl) ⟨470265, by rfl⟩ : syracuseStep 1254041 = 940531) B940531
theorem B697015 : Blo 243817 697015 := bstep (se 1 (by rfl) ⟨522761, by rfl⟩ : syracuseStep 697015 = 1045523) B1045523
theorem B369335 : Blo 243817 369335 := bstep (se 1 (by rfl) ⟨277001, by rfl⟩ : syracuseStep 369335 = 554003) B554003
theorem B369563 : Blo 243817 369563 := bstep (se 1 (by rfl) ⟨277172, by rfl⟩ : syracuseStep 369563 = 554345) B554345
theorem B1876931 : Blo 243817 1876931 := bstep (se 1 (by rfl) ⟨1407698, by rfl⟩ : syracuseStep 1876931 = 2815397) B2815397
theorem B926711 : Blo 243817 926711 := bstep (se 1 (by rfl) ⟨695033, by rfl⟩ : syracuseStep 926711 = 1390067) B1390067
theorem B4007029 : Blo 243817 4007029 := bstep (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) B375659
theorem B369959 : Blo 243817 369959 := bstep (se 1 (by rfl) ⟨277469, by rfl⟩ : syracuseStep 369959 = 554939) B554939
theorem B370043 : Blo 243817 370043 := bstep (se 1 (by rfl) ⟨277532, by rfl⟩ : syracuseStep 370043 = 555065) B555065
theorem B370169 : Blo 243817 370169 := bstep (se 2 (by rfl) ⟨138813, by rfl⟩ : syracuseStep 370169 = 277627) B277627
theorem B370271 : Blo 243817 370271 := bstep (se 1 (by rfl) ⟨277703, by rfl⟩ : syracuseStep 370271 = 555407) B555407
theorem B8038045 : Blo 243817 8038045 := bstep (se 3 (by rfl) ⟨1507133, by rfl⟩ : syracuseStep 8038045 = 3014267) B3014267
theorem B468641 : Blo 243817 468641 := bstep (se 2 (by rfl) ⟨175740, by rfl⟩ : syracuseStep 468641 = 351481) B351481
theorem B829115 : Blo 243817 829115 := bstep (se 1 (by rfl) ⟨621836, by rfl⟩ : syracuseStep 829115 = 1243673) B1243673
theorem B370487 : Blo 243817 370487 := bstep (se 1 (by rfl) ⟨277865, by rfl⟩ : syracuseStep 370487 = 555731) B555731
theorem B370793 : Blo 243817 370793 := bstep (se 2 (by rfl) ⟨139047, by rfl⟩ : syracuseStep 370793 = 278095) B278095
theorem B469415 : Blo 243817 469415 := bstep (se 1 (by rfl) ⟨352061, by rfl⟩ : syracuseStep 469415 = 704123) B704123
theorem B371111 : Blo 243817 371111 := bstep (se 1 (by rfl) ⟨278333, by rfl⟩ : syracuseStep 371111 = 556667) B556667
theorem B1321427 : Blo 243817 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B371195 : Blo 243817 371195 := bstep (se 1 (by rfl) ⟨278396, by rfl⟩ : syracuseStep 371195 = 556793) B556793
theorem B469567 : Blo 243817 469567 := bstep (se 1 (by rfl) ⟨352175, by rfl⟩ : syracuseStep 469567 = 704351) B704351
theorem B371321 : Blo 243817 371321 := bstep (se 2 (by rfl) ⟨139245, by rfl⟩ : syracuseStep 371321 = 278491) B278491
theorem B371375 : Blo 243817 371375 := bstep (se 1 (by rfl) ⟨278531, by rfl⟩ : syracuseStep 371375 = 557063) B557063
theorem B1321667 : Blo 243817 1321667 := bstep (se 1 (by rfl) ⟨991250, by rfl⟩ : syracuseStep 1321667 = 1982501) B1982501
theorem B666335 : Blo 243817 666335 := bstep (se 1 (by rfl) ⟨499751, by rfl⟩ : syracuseStep 666335 = 999503) B999503
theorem B371423 : Blo 243817 371423 := bstep (se 1 (by rfl) ⟨278567, by rfl⟩ : syracuseStep 371423 = 557135) B557135
theorem B928655 : Blo 243817 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B371687 : Blo 243817 371687 := bstep (se 1 (by rfl) ⟨278765, by rfl⟩ : syracuseStep 371687 = 557531) B557531
theorem B994493 : Blo 243817 994493 := bstep (se 3 (by rfl) ⟨186467, by rfl⟩ : syracuseStep 994493 = 372935) B372935
theorem B831059 : Blo 243817 831059 := bstep (se 1 (by rfl) ⟨623294, by rfl⟩ : syracuseStep 831059 = 1246589) B1246589
theorem B1257731 : Blo 243817 1257731 := bstep (se 1 (by rfl) ⟨943298, by rfl⟩ : syracuseStep 1257731 = 1886597) B1886597
theorem B274855 : Blo 243817 274855 := bstep (se 1 (by rfl) ⟨206141, by rfl⟩ : syracuseStep 274855 = 412283) B412283
theorem B1585817 : Blo 243817 1585817 := bstep (se 2 (by rfl) ⟨594681, by rfl⟩ : syracuseStep 1585817 = 1189363) B1189363
theorem B275431 : Blo 243817 275431 := bstep (se 1 (by rfl) ⟨206573, by rfl⟩ : syracuseStep 275431 = 413147) B413147
theorem B1717393 : Blo 243817 1717393 := bstep (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) B1288045
theorem B931115 : Blo 243817 931115 := bstep (se 1 (by rfl) ⟨698336, by rfl⟩ : syracuseStep 931115 = 1396673) B1396673
theorem B6337925 : Blo 243817 6337925 := bstep (se 4 (by rfl) ⟨594180, by rfl⟩ : syracuseStep 6337925 = 1188361) B1188361
theorem B701959 : Blo 243817 701959 := bstep (se 1 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 701959 = 1052939) B1052939
theorem B2668277 : Blo 243817 2668277 := bstep (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) B250151
theorem B3389303 : Blo 243817 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B243999 : Blo 243817 243999 := bstep (se 1 (by rfl) ⟨182999, by rfl⟩ : syracuseStep 243999 = 365999) B365999
theorem B244059 : Blo 243817 244059 := bstep (se 1 (by rfl) ⟨183044, by rfl⟩ : syracuseStep 244059 = 366089) B366089
theorem B244079 : Blo 243817 244079 := bstep (se 1 (by rfl) ⟨183059, by rfl⟩ : syracuseStep 244079 = 366119) B366119
theorem B244135 : Blo 243817 244135 := bstep (se 1 (by rfl) ⟨183101, by rfl⟩ : syracuseStep 244135 = 366203) B366203
theorem B833975 : Blo 243817 833975 := bstep (se 1 (by rfl) ⟨625481, by rfl⟩ : syracuseStep 833975 = 1250963) B1250963
theorem B244219 : Blo 243817 244219 := bstep (se 1 (by rfl) ⟨183164, by rfl⟩ : syracuseStep 244219 = 366329) B366329
theorem B244287 : Blo 243817 244287 := bstep (se 1 (by rfl) ⟨183215, by rfl⟩ : syracuseStep 244287 = 366431) B366431
theorem B244295 : Blo 243817 244295 := bstep (se 1 (by rfl) ⟨183221, by rfl⟩ : syracuseStep 244295 = 366443) B366443
theorem B1686089 : Blo 243817 1686089 := bstep (se 2 (by rfl) ⟨632283, by rfl⟩ : syracuseStep 1686089 = 1264567) B1264567
theorem B277087 : Blo 243817 277087 := bstep (se 1 (by rfl) ⟨207815, by rfl⟩ : syracuseStep 277087 = 415631) B415631
theorem B244447 : Blo 243817 244447 := bstep (se 1 (by rfl) ⟨183335, by rfl⟩ : syracuseStep 244447 = 366671) B366671
theorem B244527 : Blo 243817 244527 := bstep (se 1 (by rfl) ⟨183395, by rfl⟩ : syracuseStep 244527 = 366791) B366791
theorem B310063 : Blo 243817 310063 := bstep (se 1 (by rfl) ⟨232547, by rfl⟩ : syracuseStep 310063 = 465095) B465095
theorem B244635 : Blo 243817 244635 := bstep (se 1 (by rfl) ⟨183476, by rfl⟩ : syracuseStep 244635 = 366953) B366953
theorem B244687 : Blo 243817 244687 := bstep (se 1 (by rfl) ⟨183515, by rfl⟩ : syracuseStep 244687 = 367031) B367031
theorem B244711 : Blo 243817 244711 := bstep (se 1 (by rfl) ⟨183533, by rfl⟩ : syracuseStep 244711 = 367067) B367067
theorem B703475 : Blo 243817 703475 := bstep (se 1 (by rfl) ⟨527606, by rfl⟩ : syracuseStep 703475 = 1055213) B1055213
theorem B245023 : Blo 243817 245023 := bstep (se 1 (by rfl) ⟨183767, by rfl⟩ : syracuseStep 245023 = 367535) B367535
theorem B2407747 : Blo 243817 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B245083 : Blo 243817 245083 := bstep (se 1 (by rfl) ⟨183812, by rfl⟩ : syracuseStep 245083 = 367625) B367625
theorem B245103 : Blo 243817 245103 := bstep (se 1 (by rfl) ⟨183827, by rfl⟩ : syracuseStep 245103 = 367655) B367655
theorem B245159 : Blo 243817 245159 := bstep (se 1 (by rfl) ⟨183869, by rfl⟩ : syracuseStep 245159 = 367739) B367739
theorem B3128777 : Blo 243817 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B998905 : Blo 243817 998905 := bstep (se 2 (by rfl) ⟨374589, by rfl⟩ : syracuseStep 998905 = 749179) B749179
theorem B245243 : Blo 243817 245243 := bstep (se 1 (by rfl) ⟨183932, by rfl⟩ : syracuseStep 245243 = 367865) B367865
theorem B245311 : Blo 243817 245311 := bstep (se 1 (by rfl) ⟨183983, by rfl⟩ : syracuseStep 245311 = 367967) B367967
theorem B245319 : Blo 243817 245319 := bstep (se 1 (by rfl) ⟨183989, by rfl⟩ : syracuseStep 245319 = 367979) B367979
theorem B1326701 : Blo 243817 1326701 := bstep (se 3 (by rfl) ⟨248756, by rfl⟩ : syracuseStep 1326701 = 497513) B497513
theorem B1916531 : Blo 243817 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B245471 : Blo 243817 245471 := bstep (se 1 (by rfl) ⟨184103, by rfl⟩ : syracuseStep 245471 = 368207) B368207
theorem B278239 : Blo 243817 278239 := bstep (se 1 (by rfl) ⟨208679, by rfl⟩ : syracuseStep 278239 = 417359) B417359
theorem B999179 : Blo 243817 999179 := bstep (se 1 (by rfl) ⟨749384, by rfl⟩ : syracuseStep 999179 = 1498769) B1498769
theorem B245551 : Blo 243817 245551 := bstep (se 1 (by rfl) ⟨184163, by rfl⟩ : syracuseStep 245551 = 368327) B368327
theorem B638777 : Blo 243817 638777 := bstep (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) B479083
theorem B245659 : Blo 243817 245659 := bstep (se 1 (by rfl) ⟨184244, by rfl⟩ : syracuseStep 245659 = 368489) B368489
theorem B245711 : Blo 243817 245711 := bstep (se 1 (by rfl) ⟨184283, by rfl⟩ : syracuseStep 245711 = 368567) B368567
theorem B245735 : Blo 243817 245735 := bstep (se 1 (by rfl) ⟨184301, by rfl⟩ : syracuseStep 245735 = 368603) B368603
theorem B246047 : Blo 243817 246047 := bstep (se 1 (by rfl) ⟨184535, by rfl⟩ : syracuseStep 246047 = 369071) B369071
theorem B246107 : Blo 243817 246107 := bstep (se 1 (by rfl) ⟨184580, by rfl⟩ : syracuseStep 246107 = 369161) B369161
theorem B704875 : Blo 243817 704875 := bstep (se 1 (by rfl) ⟨528656, by rfl⟩ : syracuseStep 704875 = 1057313) B1057313
theorem B246127 : Blo 243817 246127 := bstep (se 1 (by rfl) ⟨184595, by rfl⟩ : syracuseStep 246127 = 369191) B369191
theorem B246183 : Blo 243817 246183 := bstep (se 1 (by rfl) ⟨184637, by rfl⟩ : syracuseStep 246183 = 369275) B369275
theorem B246267 : Blo 243817 246267 := bstep (se 1 (by rfl) ⟨184700, by rfl⟩ : syracuseStep 246267 = 369401) B369401
theorem B1065473 : Blo 243817 1065473 := bstep (se 2 (by rfl) ⟨399552, by rfl⟩ : syracuseStep 1065473 = 799105) B799105
theorem B246335 : Blo 243817 246335 := bstep (se 1 (by rfl) ⟨184751, by rfl⟩ : syracuseStep 246335 = 369503) B369503
theorem B246343 : Blo 243817 246343 := bstep (se 1 (by rfl) ⟨184757, by rfl⟩ : syracuseStep 246343 = 369515) B369515
theorem B246495 : Blo 243817 246495 := bstep (se 1 (by rfl) ⟨184871, by rfl⟩ : syracuseStep 246495 = 369743) B369743
theorem B246575 : Blo 243817 246575 := bstep (se 1 (by rfl) ⟨184931, by rfl⟩ : syracuseStep 246575 = 369863) B369863
theorem B246683 : Blo 243817 246683 := bstep (se 1 (by rfl) ⟨185012, by rfl⟩ : syracuseStep 246683 = 370025) B370025
theorem B246735 : Blo 243817 246735 := bstep (se 1 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 246735 = 370103) B370103
theorem B246759 : Blo 243817 246759 := bstep (se 1 (by rfl) ⟨185069, by rfl⟩ : syracuseStep 246759 = 370139) B370139
theorem B247071 : Blo 243817 247071 := bstep (se 1 (by rfl) ⟨185303, by rfl⟩ : syracuseStep 247071 = 370607) B370607
theorem B247131 : Blo 243817 247131 := bstep (se 1 (by rfl) ⟨185348, by rfl⟩ : syracuseStep 247131 = 370697) B370697
theorem B247151 : Blo 243817 247151 := bstep (se 1 (by rfl) ⟨185363, by rfl⟩ : syracuseStep 247151 = 370727) B370727
theorem B247207 : Blo 243817 247207 := bstep (se 1 (by rfl) ⟨185405, by rfl⟩ : syracuseStep 247207 = 370811) B370811
theorem B3556781 : Blo 243817 3556781 := bstep (se 3 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 3556781 = 1333793) B1333793
theorem B247291 : Blo 243817 247291 := bstep (se 1 (by rfl) ⟨185468, by rfl⟩ : syracuseStep 247291 = 370937) B370937
theorem B247359 : Blo 243817 247359 := bstep (se 1 (by rfl) ⟨185519, by rfl⟩ : syracuseStep 247359 = 371039) B371039
theorem B247367 : Blo 243817 247367 := bstep (se 1 (by rfl) ⟨185525, by rfl⟩ : syracuseStep 247367 = 371051) B371051
theorem B247519 : Blo 243817 247519 := bstep (se 1 (by rfl) ⟨185639, by rfl⟩ : syracuseStep 247519 = 371279) B371279
theorem B247599 : Blo 243817 247599 := bstep (se 1 (by rfl) ⟨185699, by rfl⟩ : syracuseStep 247599 = 371399) B371399
theorem B2246545 : Blo 243817 2246545 := bstep (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) B1684909
theorem B247707 : Blo 243817 247707 := bstep (se 1 (by rfl) ⟨185780, by rfl⟩ : syracuseStep 247707 = 371561) B371561
theorem B1099727 : Blo 243817 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B247759 : Blo 243817 247759 := bstep (se 1 (by rfl) ⟨185819, by rfl⟩ : syracuseStep 247759 = 371639) B371639
theorem B247783 : Blo 243817 247783 := bstep (se 1 (by rfl) ⟨185837, by rfl⟩ : syracuseStep 247783 = 371675) B371675
theorem B1394941 : Blo 243817 1394941 := bstep (se 3 (by rfl) ⟨261551, by rfl⟩ : syracuseStep 1394941 = 523103) B523103
theorem B936643 : Blo 243817 936643 := bstep (se 1 (by rfl) ⟨702482, by rfl⟩ : syracuseStep 936643 = 1404965) B1404965
theorem B936947 : Blo 243817 936947 := bstep (se 1 (by rfl) ⟨702710, by rfl⟩ : syracuseStep 936947 = 1405421) B1405421
theorem B937403 : Blo 243817 937403 := bstep (se 1 (by rfl) ⟨703052, by rfl⟩ : syracuseStep 937403 = 1406105) B1406105
theorem B347591 : Blo 243817 347591 := bstep (se 1 (by rfl) ⟨260693, by rfl⟩ : syracuseStep 347591 = 521387) B521387
theorem B2805191 : Blo 243817 2805191 := bstep (se 1 (by rfl) ⟨2103893, by rfl⟩ : syracuseStep 2805191 = 4207787) B4207787
theorem B1068659 : Blo 243817 1068659 := bstep (se 1 (by rfl) ⟨801494, by rfl⟩ : syracuseStep 1068659 = 1602989) B1602989
theorem B3002159 : Blo 243817 3002159 := bstep (se 1 (by rfl) ⟨2251619, by rfl⟩ : syracuseStep 3002159 = 4503239) B4503239
theorem B282415 : Blo 243817 282415 := bstep (se 1 (by rfl) ⟨211811, by rfl⟩ : syracuseStep 282415 = 423623) B423623
theorem B1855547 : Blo 243817 1855547 := bstep (se 1 (by rfl) ⟨1391660, by rfl⟩ : syracuseStep 1855547 = 2783321) B2783321
theorem B2642291 : Blo 243817 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B414119 : Blo 243817 414119 := bstep (se 1 (by rfl) ⟨310589, by rfl⟩ : syracuseStep 414119 = 621179) B621179
theorem B414281 : Blo 243817 414281 := bstep (se 2 (by rfl) ⟨155355, by rfl⟩ : syracuseStep 414281 = 310711) B310711
theorem B348895 : Blo 243817 348895 := bstep (se 1 (by rfl) ⟨261671, by rfl⟩ : syracuseStep 348895 = 523343) B523343
theorem B2249975 : Blo 243817 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B4773113 : Blo 243817 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B1857005 : Blo 243817 1857005 := bstep (se 3 (by rfl) ⟨348188, by rfl⟩ : syracuseStep 1857005 = 696377) B696377
theorem B1234439 : Blo 243817 1234439 := bstep (se 1 (by rfl) ⟨925829, by rfl⟩ : syracuseStep 1234439 = 1851659) B1851659
theorem B415327 : Blo 243817 415327 := bstep (se 1 (by rfl) ⟨311495, by rfl⟩ : syracuseStep 415327 = 622991) B622991
theorem B415543 : Blo 243817 415543 := bstep (se 1 (by rfl) ⟨311657, by rfl⟩ : syracuseStep 415543 = 623315) B623315
theorem B939863 : Blo 243817 939863 := bstep (se 1 (by rfl) ⟨704897, by rfl⟩ : syracuseStep 939863 = 1409795) B1409795
theorem B743375 : Blo 243817 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B1562597 : Blo 243817 1562597 := bstep (se 4 (by rfl) ⟨146493, by rfl⟩ : syracuseStep 1562597 = 292987) B292987
theorem B1234925 : Blo 243817 1234925 := bstep (se 3 (by rfl) ⟨231548, by rfl⟩ : syracuseStep 1234925 = 463097) B463097
theorem B1136825 : Blo 243817 1136825 := bstep (se 2 (by rfl) ⟨426309, by rfl⟩ : syracuseStep 1136825 = 852619) B852619
theorem B284891 : Blo 243817 284891 := bstep (se 1 (by rfl) ⟨213668, by rfl⟩ : syracuseStep 284891 = 427337) B427337
theorem B416009 : Blo 243817 416009 := bstep (se 2 (by rfl) ⟨156003, by rfl⟩ : syracuseStep 416009 = 312007) B312007
theorem B1235411 : Blo 243817 1235411 := bstep (se 1 (by rfl) ⟨926558, by rfl⟩ : syracuseStep 1235411 = 1853117) B1853117
theorem B1071863 : Blo 243817 1071863 := bstep (se 1 (by rfl) ⟨803897, by rfl⟩ : syracuseStep 1071863 = 1607795) B1607795
theorem B2284307 : Blo 243817 2284307 := bstep (se 1 (by rfl) ⟨1713230, by rfl⟩ : syracuseStep 2284307 = 3426461) B3426461
theorem B1235735 : Blo 243817 1235735 := bstep (se 1 (by rfl) ⟨926801, by rfl⟩ : syracuseStep 1235735 = 1853603) B1853603
theorem B2349931 : Blo 243817 2349931 := bstep (se 1 (by rfl) ⟨1762448, by rfl⟩ : syracuseStep 2349931 = 3524897) B3524897
theorem B1760285 : Blo 243817 1760285 := bstep (se 3 (by rfl) ⟨330053, by rfl⟩ : syracuseStep 1760285 = 660107) B660107
theorem B5790937 : Blo 243817 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B417001 : Blo 243817 417001 := bstep (se 2 (by rfl) ⟨156375, by rfl⟩ : syracuseStep 417001 = 312751) B312751
theorem B417055 : Blo 243817 417055 := bstep (se 1 (by rfl) ⟨312791, by rfl⟩ : syracuseStep 417055 = 625583) B625583
theorem B417467 : Blo 243817 417467 := bstep (se 1 (by rfl) ⟨313100, by rfl⟩ : syracuseStep 417467 = 626201) B626201
theorem B2350889 : Blo 243817 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B4185917 : Blo 243817 4185917 := bstep (se 3 (by rfl) ⟨784859, by rfl⟩ : syracuseStep 4185917 = 1569719) B1569719
theorem B1859435 : Blo 243817 1859435 := bstep (se 1 (by rfl) ⟨1394576, by rfl⟩ : syracuseStep 1859435 = 2789153) B2789153
theorem B548873 : Blo 243817 548873 := bstep (se 2 (by rfl) ⟨205827, by rfl⟩ : syracuseStep 548873 = 411655) B411655
theorem B352603 : Blo 243817 352603 := bstep (se 1 (by rfl) ⟨264452, by rfl⟩ : syracuseStep 352603 = 528905) B528905
theorem B1237355 : Blo 243817 1237355 := bstep (se 1 (by rfl) ⟨928016, by rfl⟩ : syracuseStep 1237355 = 1856033) B1856033
theorem B549287 : Blo 243817 549287 := bstep (se 1 (by rfl) ⟨411965, by rfl⟩ : syracuseStep 549287 = 823931) B823931
theorem B549395 : Blo 243817 549395 := bstep (se 1 (by rfl) ⟨412046, by rfl⟩ : syracuseStep 549395 = 824093) B824093
theorem B352831 : Blo 243817 352831 := bstep (se 1 (by rfl) ⟨264623, by rfl⟩ : syracuseStep 352831 = 529247) B529247
theorem B7955009 : Blo 243817 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B549449 : Blo 243817 549449 := bstep (se 2 (by rfl) ⟨206043, by rfl⟩ : syracuseStep 549449 = 412087) B412087
theorem B1499795 : Blo 243817 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B549863 : Blo 243817 549863 := bstep (se 1 (by rfl) ⟨412397, by rfl⟩ : syracuseStep 549863 = 824795) B824795
theorem B550241 : Blo 243817 550241 := bstep (se 2 (by rfl) ⟨206340, by rfl⟩ : syracuseStep 550241 = 412681) B412681
theorem B550331 : Blo 243817 550331 := bstep (se 1 (by rfl) ⟨412748, by rfl⟩ : syracuseStep 550331 = 825497) B825497
theorem B550457 : Blo 243817 550457 := bstep (se 2 (by rfl) ⟨206421, by rfl⟩ : syracuseStep 550457 = 412843) B412843
theorem B1238813 : Blo 243817 1238813 := bstep (se 3 (by rfl) ⟨232277, by rfl⟩ : syracuseStep 1238813 = 464555) B464555
theorem B4417361 : Blo 243817 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B3172243 : Blo 243817 3172243 := bstep (se 1 (by rfl) ⟨2379182, by rfl⟩ : syracuseStep 3172243 = 4758365) B4758365
theorem B4220909 : Blo 243817 4220909 := bstep (se 3 (by rfl) ⟨791420, by rfl⟩ : syracuseStep 4220909 = 1582841) B1582841
theorem B845959 : Blo 243817 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B551123 : Blo 243817 551123 := bstep (se 1 (by rfl) ⟨413342, by rfl⟩ : syracuseStep 551123 = 826685) B826685
theorem B551177 : Blo 243817 551177 := bstep (se 2 (by rfl) ⟨206691, by rfl⟩ : syracuseStep 551177 = 413383) B413383
theorem B551393 : Blo 243817 551393 := bstep (se 2 (by rfl) ⟨206772, by rfl⟩ : syracuseStep 551393 = 413545) B413545
theorem B3860995 : Blo 243817 3860995 := bstep (se 1 (by rfl) ⟨2895746, by rfl⟩ : syracuseStep 3860995 = 5791493) B5791493
theorem B2255447 : Blo 243817 2255447 := bstep (se 1 (by rfl) ⟨1691585, by rfl⟩ : syracuseStep 2255447 = 3383171) B3383171
theorem B1174139 : Blo 243817 1174139 := bstep (se 1 (by rfl) ⟨880604, by rfl⟩ : syracuseStep 1174139 = 1761209) B1761209
theorem B551699 : Blo 243817 551699 := bstep (se 1 (by rfl) ⟨413774, by rfl⟩ : syracuseStep 551699 = 827549) B827549
theorem B420763 : Blo 243817 420763 := bstep (se 1 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 420763 = 631145) B631145
theorem B552059 : Blo 243817 552059 := bstep (se 1 (by rfl) ⟨414044, by rfl⟩ : syracuseStep 552059 = 828089) B828089
theorem B617615 : Blo 243817 617615 := bstep (se 1 (by rfl) ⟨463211, by rfl⟩ : syracuseStep 617615 = 926423) B926423
theorem B552185 : Blo 243817 552185 := bstep (se 2 (by rfl) ⟨207069, by rfl⟩ : syracuseStep 552185 = 414139) B414139
theorem B552329 : Blo 243817 552329 := bstep (se 2 (by rfl) ⟨207123, by rfl⟩ : syracuseStep 552329 = 414247) B414247
theorem B552455 : Blo 243817 552455 := bstep (se 1 (by rfl) ⟨414341, by rfl⟩ : syracuseStep 552455 = 828683) B828683
theorem B12906161 : Blo 243817 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B552635 : Blo 243817 552635 := bstep (se 1 (by rfl) ⟨414476, by rfl⟩ : syracuseStep 552635 = 828953) B828953
theorem B552761 : Blo 243817 552761 := bstep (se 2 (by rfl) ⟨207285, by rfl⟩ : syracuseStep 552761 = 414571) B414571
theorem B553391 : Blo 243817 553391 := bstep (se 1 (by rfl) ⟨415043, by rfl⟩ : syracuseStep 553391 = 830087) B830087
theorem B3207599 : Blo 243817 3207599 := bstep (se 1 (by rfl) ⟨2405699, by rfl⟩ : syracuseStep 3207599 = 4811399) B4811399
theorem B553427 : Blo 243817 553427 := bstep (se 1 (by rfl) ⟨415070, by rfl⟩ : syracuseStep 553427 = 830141) B830141
theorem B553535 : Blo 243817 553535 := bstep (se 1 (by rfl) ⟨415151, by rfl⟩ : syracuseStep 553535 = 830303) B830303
theorem B7959161 : Blo 243817 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B553643 : Blo 243817 553643 := bstep (se 1 (by rfl) ⟨415232, by rfl⟩ : syracuseStep 553643 = 830465) B830465
theorem B14480117 : Blo 243817 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B520951 : Blo 243817 520951 := bstep (se 1 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 520951 = 781427) B781427
theorem B783323 : Blo 243817 783323 := bstep (se 1 (by rfl) ⟨587492, by rfl⟩ : syracuseStep 783323 = 1174985) B1174985
theorem B619559 : Blo 243817 619559 := bstep (se 1 (by rfl) ⟨464669, by rfl⟩ : syracuseStep 619559 = 929339) B929339
theorem B7992377 : Blo 243817 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B554183 : Blo 243817 554183 := bstep (se 1 (by rfl) ⟨415637, by rfl⟩ : syracuseStep 554183 = 831275) B831275
theorem B1045865 : Blo 243817 1045865 := bstep (se 2 (by rfl) ⟨392199, by rfl⟩ : syracuseStep 1045865 = 784399) B784399
theorem B554363 : Blo 243817 554363 := bstep (se 1 (by rfl) ⟨415772, by rfl⟩ : syracuseStep 554363 = 831545) B831545
theorem B619913 : Blo 243817 619913 := bstep (se 2 (by rfl) ⟨232467, by rfl⟩ : syracuseStep 619913 = 464935) B464935
theorem B554489 : Blo 243817 554489 := bstep (se 2 (by rfl) ⟨207933, by rfl⟩ : syracuseStep 554489 = 415867) B415867
theorem B2094599 : Blo 243817 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B554579 : Blo 243817 554579 := bstep (se 1 (by rfl) ⟨415934, by rfl⟩ : syracuseStep 554579 = 831869) B831869
theorem B554759 : Blo 243817 554759 := bstep (se 1 (by rfl) ⟨416069, by rfl⟩ : syracuseStep 554759 = 832139) B832139
theorem B10385189 : Blo 243817 10385189 := bstep (se 4 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 10385189 = 1947223) B1947223
theorem B555371 : Blo 243817 555371 := bstep (se 1 (by rfl) ⟨416528, by rfl⟩ : syracuseStep 555371 = 833057) B833057
theorem B555515 : Blo 243817 555515 := bstep (se 1 (by rfl) ⟨416636, by rfl⟩ : syracuseStep 555515 = 833273) B833273
theorem B2128447 : Blo 243817 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B948809 : Blo 243817 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B555641 : Blo 243817 555641 := bstep (se 2 (by rfl) ⟨208365, by rfl⟩ : syracuseStep 555641 = 416731) B416731
theorem B1047163 : Blo 243817 1047163 := bstep (se 1 (by rfl) ⟨785372, by rfl⟩ : syracuseStep 1047163 = 1570745) B1570745
theorem B555695 : Blo 243817 555695 := bstep (se 1 (by rfl) ⟨416771, by rfl⟩ : syracuseStep 555695 = 833543) B833543
theorem B555767 : Blo 243817 555767 := bstep (se 1 (by rfl) ⟨416825, by rfl⟩ : syracuseStep 555767 = 833651) B833651
theorem B523027 : Blo 243817 523027 := bstep (se 1 (by rfl) ⟨392270, by rfl⟩ : syracuseStep 523027 = 784541) B784541
theorem B260911 : Blo 243817 260911 := bstep (se 1 (by rfl) ⟨195683, by rfl⟩ : syracuseStep 260911 = 391367) B391367
theorem B293687 : Blo 243817 293687 := bstep (se 1 (by rfl) ⟨220265, by rfl⟩ : syracuseStep 293687 = 440531) B440531
theorem B392015 : Blo 243817 392015 := bstep (se 1 (by rfl) ⟨294011, by rfl⟩ : syracuseStep 392015 = 588023) B588023
theorem B621391 : Blo 243817 621391 := bstep (se 1 (by rfl) ⟨466043, by rfl⟩ : syracuseStep 621391 = 932087) B932087
theorem B555947 : Blo 243817 555947 := bstep (se 1 (by rfl) ⟨416960, by rfl⟩ : syracuseStep 555947 = 833921) B833921
theorem B621665 : Blo 243817 621665 := bstep (se 2 (by rfl) ⟨233124, by rfl⟩ : syracuseStep 621665 = 466249) B466249
theorem B523513 : Blo 243817 523513 := bstep (se 2 (by rfl) ⟨196317, by rfl⟩ : syracuseStep 523513 = 392635) B392635
theorem B261415 : Blo 243817 261415 := bstep (se 1 (by rfl) ⟨196061, by rfl⟩ : syracuseStep 261415 = 392123) B392123
theorem B1244483 : Blo 243817 1244483 := bstep (se 1 (by rfl) ⟨933362, by rfl⟩ : syracuseStep 1244483 = 1866725) B1866725
theorem B785783 : Blo 243817 785783 := bstep (se 1 (by rfl) ⟨589337, by rfl⟩ : syracuseStep 785783 = 1178675) B1178675
theorem B556411 : Blo 243817 556411 := bstep (se 1 (by rfl) ⟨417308, by rfl⟩ : syracuseStep 556411 = 834617) B834617
theorem B556487 : Blo 243817 556487 := bstep (se 1 (by rfl) ⟨417365, by rfl⟩ : syracuseStep 556487 = 834731) B834731
theorem B622039 : Blo 243817 622039 := bstep (se 1 (by rfl) ⟨466529, by rfl⟩ : syracuseStep 622039 = 933059) B933059
theorem B2784779 : Blo 243817 2784779 := bstep (se 1 (by rfl) ⟨2088584, by rfl⟩ : syracuseStep 2784779 = 4177169) B4177169
theorem B2359043 : Blo 243817 2359043 := bstep (se 1 (by rfl) ⟨1769282, by rfl⟩ : syracuseStep 2359043 = 3538565) B3538565
theorem B622343 : Blo 243817 622343 := bstep (se 1 (by rfl) ⟨466757, by rfl⟩ : syracuseStep 622343 = 933515) B933515
theorem B1244969 : Blo 243817 1244969 := bstep (se 2 (by rfl) ⟨466863, by rfl⟩ : syracuseStep 1244969 = 933727) B933727
theorem B393007 : Blo 243817 393007 := bstep (se 1 (by rfl) ⟨294755, by rfl⟩ : syracuseStep 393007 = 589511) B589511
theorem B556847 : Blo 243817 556847 := bstep (se 1 (by rfl) ⟨417635, by rfl⟩ : syracuseStep 556847 = 835271) B835271
theorem B425785 : Blo 243817 425785 := bstep (se 2 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 425785 = 319339) B319339
theorem B1048393 : Blo 243817 1048393 := bstep (se 2 (by rfl) ⟨393147, by rfl⟩ : syracuseStep 1048393 = 786295) B786295
theorem B4718999 : Blo 243817 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B262607 : Blo 243817 262607 := bstep (se 1 (by rfl) ⟨196955, by rfl⟩ : syracuseStep 262607 = 393911) B393911
theorem B525035 : Blo 243817 525035 := bstep (se 1 (by rfl) ⟨393776, by rfl⟩ : syracuseStep 525035 = 787553) B787553
theorem B4719545 : Blo 243817 4719545 := bstep (se 2 (by rfl) ⟨1769829, by rfl⟩ : syracuseStep 4719545 = 3539659) B3539659
theorem B787411 : Blo 243817 787411 := bstep (se 1 (by rfl) ⟨590558, by rfl⟩ : syracuseStep 787411 = 1181117) B1181117
theorem B5342705 : Blo 243817 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B788231 : Blo 243817 788231 := bstep (se 1 (by rfl) ⟨591173, by rfl⟩ : syracuseStep 788231 = 1182347) B1182347
theorem B2098973 : Blo 243817 2098973 := bstep (se 3 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 2098973 = 787115) B787115
theorem B395039 : Blo 243817 395039 := bstep (se 1 (by rfl) ⟨296279, by rfl⟩ : syracuseStep 395039 = 592559) B592559
theorem B624631 : Blo 243817 624631 := bstep (se 1 (by rfl) ⟨468473, by rfl⟩ : syracuseStep 624631 = 936947) B936947
theorem B10717393 : Blo 243817 10717393 := bstep (se 2 (by rfl) ⟨4019022, by rfl⟩ : syracuseStep 10717393 = 8038045) B8038045
theorem B624935 : Blo 243817 624935 := bstep (se 1 (by rfl) ⟨468701, by rfl⟩ : syracuseStep 624935 = 937403) B937403
theorem B1870127 : Blo 243817 1870127 := bstep (se 1 (by rfl) ⟨1402595, by rfl⟩ : syracuseStep 1870127 = 2805191) B2805191
theorem B4229657 : Blo 243817 4229657 := bstep (se 2 (by rfl) ⟨1586121, by rfl⟩ : syracuseStep 4229657 = 3172243) B3172243
theorem B2001439 : Blo 243817 2001439 := bstep (se 1 (by rfl) ⟨1501079, by rfl⟩ : syracuseStep 2001439 = 3002159) B3002159
theorem B1182559 : Blo 243817 1182559 := bstep (se 1 (by rfl) ⟨886919, by rfl⟩ : syracuseStep 1182559 = 1773839) B1773839
theorem B36637717 : Blo 243817 36637717 := bstep (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) B1717393
theorem B5999933 : Blo 243817 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B1576259 : Blo 243817 1576259 := bstep (se 1 (by rfl) ⟨1182194, by rfl⟩ : syracuseStep 1576259 = 2364389) B2364389
theorem B5147993 : Blo 243817 5147993 := bstep (se 2 (by rfl) ⟨1930497, by rfl⟩ : syracuseStep 5147993 = 3860995) B3860995
theorem B626089 : Blo 243817 626089 := bstep (se 2 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 626089 = 469567) B469567
theorem B1248695 : Blo 243817 1248695 := bstep (se 1 (by rfl) ⟨936521, by rfl⟩ : syracuseStep 1248695 = 1873043) B1873043
theorem B593335 : Blo 243817 593335 := bstep (se 1 (by rfl) ⟨445001, by rfl⟩ : syracuseStep 593335 = 890003) B890003
theorem B3182075 : Blo 243817 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B1248857 : Blo 243817 1248857 := bstep (se 2 (by rfl) ⟨468321, by rfl⟩ : syracuseStep 1248857 = 936643) B936643
theorem B822959 : Blo 243817 822959 := bstep (se 1 (by rfl) ⟨617219, by rfl⟩ : syracuseStep 822959 = 1234439) B1234439
theorem B561017 : Blo 243817 561017 := bstep (se 2 (by rfl) ⟨210381, by rfl⟩ : syracuseStep 561017 = 420763) B420763
theorem B626575 : Blo 243817 626575 := bstep (se 1 (by rfl) ⟨469931, by rfl⟩ : syracuseStep 626575 = 939863) B939863
theorem B823283 : Blo 243817 823283 := bstep (se 1 (by rfl) ⟨617462, by rfl⟩ : syracuseStep 823283 = 1234925) B1234925
theorem B757883 : Blo 243817 757883 := bstep (se 1 (by rfl) ⟨568412, by rfl⟩ : syracuseStep 757883 = 1136825) B1136825
theorem B2363579 : Blo 243817 2363579 := bstep (se 1 (by rfl) ⟨1772684, by rfl⟩ : syracuseStep 2363579 = 3545369) B3545369
theorem B823607 : Blo 243817 823607 := bstep (se 1 (by rfl) ⟨617705, by rfl⟩ : syracuseStep 823607 = 1235411) B1235411
theorem B823823 : Blo 243817 823823 := bstep (se 1 (by rfl) ⟨617867, by rfl⟩ : syracuseStep 823823 = 1235735) B1235735
theorem B1184807 : Blo 243817 1184807 := bstep (se 1 (by rfl) ⟨888605, by rfl⟩ : syracuseStep 1184807 = 1777211) B1777211
theorem B2790611 : Blo 243817 2790611 := bstep (se 1 (by rfl) ⟨2092958, by rfl⟩ : syracuseStep 2790611 = 4185917) B4185917
theorem B365915 : Blo 243817 365915 := bstep (se 1 (by rfl) ⟨274436, by rfl⟩ : syracuseStep 365915 = 548873) B548873
theorem B824903 : Blo 243817 824903 := bstep (se 1 (by rfl) ⟨618677, by rfl⟩ : syracuseStep 824903 = 1237355) B1237355
theorem B366191 : Blo 243817 366191 := bstep (se 1 (by rfl) ⟨274643, by rfl⟩ : syracuseStep 366191 = 549287) B549287
theorem B366263 : Blo 243817 366263 := bstep (se 1 (by rfl) ⟨274697, by rfl⟩ : syracuseStep 366263 = 549395) B549395
theorem B366299 : Blo 243817 366299 := bstep (se 1 (by rfl) ⟨274724, by rfl⟩ : syracuseStep 366299 = 549449) B549449
theorem B366473 : Blo 243817 366473 := bstep (se 2 (by rfl) ⟨137427, by rfl⟩ : syracuseStep 366473 = 274855) B274855
theorem B759709 : Blo 243817 759709 := bstep (se 3 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 759709 = 284891) B284891
theorem B1251287 : Blo 243817 1251287 := bstep (se 1 (by rfl) ⟨938465, by rfl⟩ : syracuseStep 1251287 = 1876931) B1876931
theorem B366575 : Blo 243817 366575 := bstep (se 1 (by rfl) ⟨274931, by rfl⟩ : syracuseStep 366575 = 549863) B549863
theorem B366827 : Blo 243817 366827 := bstep (se 1 (by rfl) ⟨275120, by rfl⟩ : syracuseStep 366827 = 550241) B550241
theorem B366887 : Blo 243817 366887 := bstep (se 1 (by rfl) ⟨275165, by rfl⟩ : syracuseStep 366887 = 550331) B550331
theorem B465193 : Blo 243817 465193 := bstep (se 2 (by rfl) ⟨174447, by rfl⟩ : syracuseStep 465193 = 348895) B348895
theorem B694601 : Blo 243817 694601 := bstep (se 2 (by rfl) ⟨260475, by rfl⟩ : syracuseStep 694601 = 520951) B520951
theorem B366971 : Blo 243817 366971 := bstep (se 1 (by rfl) ⟨275228, by rfl⟩ : syracuseStep 366971 = 550457) B550457
theorem B1251773 : Blo 243817 1251773 := bstep (se 3 (by rfl) ⟨234707, by rfl⟩ : syracuseStep 1251773 = 469415) B469415
theorem B3152357 : Blo 243817 3152357 := bstep (se 4 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 3152357 = 591067) B591067
theorem B825875 : Blo 243817 825875 := bstep (se 1 (by rfl) ⟨619406, by rfl⟩ : syracuseStep 825875 = 1238813) B1238813
theorem B2792069 : Blo 243817 2792069 := bstep (se 4 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 2792069 = 523513) B523513
theorem B367241 : Blo 243817 367241 := bstep (se 2 (by rfl) ⟨137715, by rfl⟩ : syracuseStep 367241 = 275431) B275431
theorem B367415 : Blo 243817 367415 := bstep (se 1 (by rfl) ⟨275561, by rfl⟩ : syracuseStep 367415 = 551123) B551123
theorem B367451 : Blo 243817 367451 := bstep (se 1 (by rfl) ⟨275588, by rfl⟩ : syracuseStep 367451 = 551177) B551177
theorem B367595 : Blo 243817 367595 := bstep (se 1 (by rfl) ⟨275696, by rfl⟩ : syracuseStep 367595 = 551393) B551393
theorem B367799 : Blo 243817 367799 := bstep (se 1 (by rfl) ⟨275849, by rfl⟩ : syracuseStep 367799 = 551699) B551699
theorem B368039 : Blo 243817 368039 := bstep (se 1 (by rfl) ⟨276029, by rfl⟩ : syracuseStep 368039 = 552059) B552059
theorem B662995 : Blo 243817 662995 := bstep (se 1 (by rfl) ⟨497246, by rfl⟩ : syracuseStep 662995 = 994493) B994493
theorem B368123 : Blo 243817 368123 := bstep (se 1 (by rfl) ⟨276092, by rfl⟩ : syracuseStep 368123 = 552185) B552185
theorem B368219 : Blo 243817 368219 := bstep (se 1 (by rfl) ⟨276164, by rfl⟩ : syracuseStep 368219 = 552329) B552329
theorem B368303 : Blo 243817 368303 := bstep (se 1 (by rfl) ⟨276227, by rfl⟩ : syracuseStep 368303 = 552455) B552455
theorem B368423 : Blo 243817 368423 := bstep (se 1 (by rfl) ⟨276317, by rfl⟩ : syracuseStep 368423 = 552635) B552635
theorem B368507 : Blo 243817 368507 := bstep (se 1 (by rfl) ⟨276380, by rfl⟩ : syracuseStep 368507 = 552761) B552761
theorem B368927 : Blo 243817 368927 := bstep (se 1 (by rfl) ⟨276695, by rfl⟩ : syracuseStep 368927 = 553391) B553391
theorem B2138399 : Blo 243817 2138399 := bstep (se 1 (by rfl) ⟨1603799, by rfl⟩ : syracuseStep 2138399 = 3207599) B3207599
theorem B368951 : Blo 243817 368951 := bstep (se 1 (by rfl) ⟨276713, by rfl⟩ : syracuseStep 368951 = 553427) B553427
theorem B369023 : Blo 243817 369023 := bstep (se 1 (by rfl) ⟨276767, by rfl⟩ : syracuseStep 369023 = 553535) B553535
theorem B1057211 : Blo 243817 1057211 := bstep (se 1 (by rfl) ⟨792908, by rfl⟩ : syracuseStep 1057211 = 1585817) B1585817
theorem B369095 : Blo 243817 369095 := bstep (se 1 (by rfl) ⟨276821, by rfl⟩ : syracuseStep 369095 = 553643) B553643
theorem B369449 : Blo 243817 369449 := bstep (se 2 (by rfl) ⟨138543, by rfl⟩ : syracuseStep 369449 = 277087) B277087
theorem B369455 : Blo 243817 369455 := bstep (se 1 (by rfl) ⟨277091, by rfl⟩ : syracuseStep 369455 = 554183) B554183
theorem B697243 : Blo 243817 697243 := bstep (se 1 (by rfl) ⟨522932, by rfl⟩ : syracuseStep 697243 = 1045865) B1045865
theorem B369575 : Blo 243817 369575 := bstep (se 1 (by rfl) ⟨277181, by rfl⟩ : syracuseStep 369575 = 554363) B554363
theorem B369659 : Blo 243817 369659 := bstep (se 1 (by rfl) ⟨277244, by rfl⟩ : syracuseStep 369659 = 554489) B554489
theorem B697369 : Blo 243817 697369 := bstep (se 2 (by rfl) ⟨261513, by rfl⟩ : syracuseStep 697369 = 523027) B523027
theorem B369719 : Blo 243817 369719 := bstep (se 1 (by rfl) ⟨277289, by rfl⟩ : syracuseStep 369719 = 554579) B554579
theorem B828521 : Blo 243817 828521 := bstep (se 2 (by rfl) ⟨310695, by rfl⟩ : syracuseStep 828521 = 621391) B621391
theorem B1778851 : Blo 243817 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B369839 : Blo 243817 369839 := bstep (se 1 (by rfl) ⟨277379, by rfl⟩ : syracuseStep 369839 = 554759) B554759
theorem B926909 : Blo 243817 926909 := bstep (se 3 (by rfl) ⟨173795, by rfl⟩ : syracuseStep 926909 = 347591) B347591
theorem B6923459 : Blo 243817 6923459 := bstep (se 1 (by rfl) ⟨5192594, by rfl⟩ : syracuseStep 6923459 = 10385189) B10385189
theorem B894461 : Blo 243817 894461 := bstep (se 3 (by rfl) ⟨167711, by rfl⟩ : syracuseStep 894461 = 335423) B335423
theorem B370247 : Blo 243817 370247 := bstep (se 1 (by rfl) ⟨277685, by rfl⟩ : syracuseStep 370247 = 555371) B555371
theorem B370343 : Blo 243817 370343 := bstep (se 1 (by rfl) ⟨277757, by rfl⟩ : syracuseStep 370343 = 555515) B555515
theorem B1124059 : Blo 243817 1124059 := bstep (se 1 (by rfl) ⟨843044, by rfl⟩ : syracuseStep 1124059 = 1686089) B1686089
theorem B632539 : Blo 243817 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B370427 : Blo 243817 370427 := bstep (se 1 (by rfl) ⟨277820, by rfl⟩ : syracuseStep 370427 = 555641) B555641
theorem B370463 : Blo 243817 370463 := bstep (se 1 (by rfl) ⟨277847, by rfl⟩ : syracuseStep 370463 = 555695) B555695
theorem B370511 : Blo 243817 370511 := bstep (se 1 (by rfl) ⟨277883, by rfl⟩ : syracuseStep 370511 = 555767) B555767
theorem B370631 : Blo 243817 370631 := bstep (se 1 (by rfl) ⟨277973, by rfl⟩ : syracuseStep 370631 = 555947) B555947
theorem B829385 : Blo 243817 829385 := bstep (se 2 (by rfl) ⟨311019, by rfl⟩ : syracuseStep 829385 = 622039) B622039
theorem B468983 : Blo 243817 468983 := bstep (se 1 (by rfl) ⟨351737, by rfl⟩ : syracuseStep 468983 = 703475) B703475
theorem B829655 : Blo 243817 829655 := bstep (se 1 (by rfl) ⟨622241, by rfl⟩ : syracuseStep 829655 = 1244483) B1244483
theorem B370985 : Blo 243817 370985 := bstep (se 2 (by rfl) ⟨139119, by rfl⟩ : syracuseStep 370985 = 278239) B278239
theorem B370991 : Blo 243817 370991 := bstep (se 1 (by rfl) ⟨278243, by rfl⟩ : syracuseStep 370991 = 556487) B556487
theorem B567713 : Blo 243817 567713 := bstep (se 2 (by rfl) ⟨212892, by rfl⟩ : syracuseStep 567713 = 425785) B425785
theorem B666119 : Blo 243817 666119 := bstep (se 1 (by rfl) ⟨499589, by rfl⟩ : syracuseStep 666119 = 999179) B999179
theorem B829979 : Blo 243817 829979 := bstep (se 1 (by rfl) ⟨622484, by rfl⟩ : syracuseStep 829979 = 1244969) B1244969
theorem B371231 : Blo 243817 371231 := bstep (se 1 (by rfl) ⟨278423, by rfl⟩ : syracuseStep 371231 = 556847) B556847
theorem B371615 : Blo 243817 371615 := bstep (se 1 (by rfl) ⟨278711, by rfl⟩ : syracuseStep 371615 = 557423) B557423
theorem B371663 : Blo 243817 371663 := bstep (se 1 (by rfl) ⟨278747, by rfl⟩ : syracuseStep 371663 = 557495) B557495
theorem B470137 : Blo 243817 470137 := bstep (se 2 (by rfl) ⟨176301, by rfl⟩ : syracuseStep 470137 = 352603) B352603
theorem B830843 : Blo 243817 830843 := bstep (se 1 (by rfl) ⟨623132, by rfl⟩ : syracuseStep 830843 = 1246265) B1246265
theorem B470441 : Blo 243817 470441 := bstep (se 2 (by rfl) ⟨176415, by rfl⟩ : syracuseStep 470441 = 352831) B352831
theorem B929353 : Blo 243817 929353 := bstep (se 2 (by rfl) ⟨348507, by rfl⟩ : syracuseStep 929353 = 697015) B697015
theorem B699977 : Blo 243817 699977 := bstep (se 2 (by rfl) ⟨262491, by rfl⟩ : syracuseStep 699977 = 524983) B524983
theorem B2371187 : Blo 243817 2371187 := bstep (se 1 (by rfl) ⟨1778390, by rfl⟩ : syracuseStep 2371187 = 3556781) B3556781
theorem B1486799 : Blo 243817 1486799 := bstep (se 1 (by rfl) ⟨1115099, by rfl⟩ : syracuseStep 1486799 = 2230199) B2230199
theorem B733151 : Blo 243817 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B832247 : Blo 243817 832247 := bstep (se 1 (by rfl) ⟨624185, by rfl⟩ : syracuseStep 832247 = 1248371) B1248371
theorem B12530645 : Blo 243817 12530645 := bstep (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) B293687
theorem B701435 : Blo 243817 701435 := bstep (se 1 (by rfl) ⟨526076, by rfl⟩ : syracuseStep 701435 = 1052153) B1052153
theorem B2995393 : Blo 243817 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B832787 : Blo 243817 832787 := bstep (se 1 (by rfl) ⟨624590, by rfl⟩ : syracuseStep 832787 = 1249181) B1249181
theorem B6272315 : Blo 243817 6272315 := bstep (se 1 (by rfl) ⟨4704236, by rfl⟩ : syracuseStep 6272315 = 9408473) B9408473
theorem B1127945 : Blo 243817 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B276079 : Blo 243817 276079 := bstep (se 1 (by rfl) ⟨207059, by rfl⟩ : syracuseStep 276079 = 414119) B414119
theorem B276187 : Blo 243817 276187 := bstep (se 1 (by rfl) ⟨207140, by rfl⟩ : syracuseStep 276187 = 414281) B414281
theorem B833327 : Blo 243817 833327 := bstep (se 1 (by rfl) ⟨624995, by rfl⟩ : syracuseStep 833327 = 1249991) B1249991
theorem B243867 : Blo 243817 243867 := bstep (se 1 (by rfl) ⟨182900, by rfl⟩ : syracuseStep 243867 = 365801) B365801
theorem B243903 : Blo 243817 243903 := bstep (se 1 (by rfl) ⟨182927, by rfl⟩ : syracuseStep 243903 = 365855) B365855
theorem B244015 : Blo 243817 244015 := bstep (se 1 (by rfl) ⟨183011, by rfl⟩ : syracuseStep 244015 = 366023) B366023
theorem B244251 : Blo 243817 244251 := bstep (se 1 (by rfl) ⟨183188, by rfl⟩ : syracuseStep 244251 = 366377) B366377
theorem B244255 : Blo 243817 244255 := bstep (se 1 (by rfl) ⟨183191, by rfl⟩ : syracuseStep 244255 = 366383) B366383
theorem B277339 : Blo 243817 277339 := bstep (se 1 (by rfl) ⟨208004, by rfl⟩ : syracuseStep 277339 = 416009) B416009
theorem B244571 : Blo 243817 244571 := bstep (se 1 (by rfl) ⟨183428, by rfl⟩ : syracuseStep 244571 = 366857) B366857
theorem B244639 : Blo 243817 244639 := bstep (se 1 (by rfl) ⟨183479, by rfl⟩ : syracuseStep 244639 = 366959) B366959
theorem B1391525 : Blo 243817 1391525 := bstep (se 4 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 1391525 = 260911) B260911
theorem B244783 : Blo 243817 244783 := bstep (se 1 (by rfl) ⟨183587, by rfl⟩ : syracuseStep 244783 = 367175) B367175
theorem B244807 : Blo 243817 244807 := bstep (se 1 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 244807 = 367211) B367211
theorem B1522871 : Blo 243817 1522871 := bstep (se 1 (by rfl) ⟨1142153, by rfl⟩ : syracuseStep 1522871 = 2284307) B2284307
theorem B244959 : Blo 243817 244959 := bstep (se 1 (by rfl) ⟨183719, by rfl⟩ : syracuseStep 244959 = 367439) B367439
theorem B441767 : Blo 243817 441767 := bstep (se 1 (by rfl) ⟨331325, by rfl⟩ : syracuseStep 441767 = 662651) B662651
theorem B245223 : Blo 243817 245223 := bstep (se 1 (by rfl) ⟨183917, by rfl⟩ : syracuseStep 245223 = 367835) B367835
theorem B245339 : Blo 243817 245339 := bstep (se 1 (by rfl) ⟨184004, by rfl⟩ : syracuseStep 245339 = 368009) B368009
theorem B835163 : Blo 243817 835163 := bstep (se 1 (by rfl) ⟨626372, by rfl⟩ : syracuseStep 835163 = 1252745) B1252745
theorem B376553 : Blo 243817 376553 := bstep (se 2 (by rfl) ⟨141207, by rfl⟩ : syracuseStep 376553 = 282415) B282415
theorem B278311 : Blo 243817 278311 := bstep (se 1 (by rfl) ⟨208733, by rfl⟩ : syracuseStep 278311 = 417467) B417467
theorem B245575 : Blo 243817 245575 := bstep (se 1 (by rfl) ⟨184181, by rfl⟩ : syracuseStep 245575 = 368363) B368363
theorem B1982333 : Blo 243817 1982333 := bstep (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) B743375
theorem B245727 : Blo 243817 245727 := bstep (se 1 (by rfl) ⟨184295, by rfl⟩ : syracuseStep 245727 = 368591) B368591
theorem B245991 : Blo 243817 245991 := bstep (se 1 (by rfl) ⟨184493, by rfl⟩ : syracuseStep 245991 = 368987) B368987
theorem B835865 : Blo 243817 835865 := bstep (se 2 (by rfl) ⟨313449, by rfl⟩ : syracuseStep 835865 = 626899) B626899
theorem B246143 : Blo 243817 246143 := bstep (se 1 (by rfl) ⟨184607, by rfl⟩ : syracuseStep 246143 = 369215) B369215
theorem B999863 : Blo 243817 999863 := bstep (se 1 (by rfl) ⟨749897, by rfl⟩ : syracuseStep 999863 = 1499795) B1499795
theorem B836027 : Blo 243817 836027 := bstep (se 1 (by rfl) ⟨627020, by rfl⟩ : syracuseStep 836027 = 1254041) B1254041
theorem B246223 : Blo 243817 246223 := bstep (se 1 (by rfl) ⟨184667, by rfl⟩ : syracuseStep 246223 = 369335) B369335
theorem B246375 : Blo 243817 246375 := bstep (se 1 (by rfl) ⟨184781, by rfl⟩ : syracuseStep 246375 = 369563) B369563
theorem B246639 : Blo 243817 246639 := bstep (se 1 (by rfl) ⟨184979, by rfl⟩ : syracuseStep 246639 = 369959) B369959
theorem B246695 : Blo 243817 246695 := bstep (se 1 (by rfl) ⟨185021, by rfl⟩ : syracuseStep 246695 = 370043) B370043
theorem B246779 : Blo 243817 246779 := bstep (se 1 (by rfl) ⟨185084, by rfl⟩ : syracuseStep 246779 = 370169) B370169
theorem B246847 : Blo 243817 246847 := bstep (se 1 (by rfl) ⟨185135, by rfl⟩ : syracuseStep 246847 = 370271) B370271
theorem B312427 : Blo 243817 312427 := bstep (se 1 (by rfl) ⟨234320, by rfl⟩ : syracuseStep 312427 = 468641) B468641
theorem B246991 : Blo 243817 246991 := bstep (se 1 (by rfl) ⟨185243, by rfl⟩ : syracuseStep 246991 = 370487) B370487
theorem B247195 : Blo 243817 247195 := bstep (se 1 (by rfl) ⟨185396, by rfl⟩ : syracuseStep 247195 = 370793) B370793
theorem B247407 : Blo 243817 247407 := bstep (se 1 (by rfl) ⟨185555, by rfl⟩ : syracuseStep 247407 = 371111) B371111
theorem B247463 : Blo 243817 247463 := bstep (se 1 (by rfl) ⟨185597, by rfl⟩ : syracuseStep 247463 = 371195) B371195
theorem B247547 : Blo 243817 247547 := bstep (se 1 (by rfl) ⟨185660, by rfl⟩ : syracuseStep 247547 = 371321) B371321
theorem B247583 : Blo 243817 247583 := bstep (se 1 (by rfl) ⟨185687, by rfl⟩ : syracuseStep 247583 = 371375) B371375
theorem B444223 : Blo 243817 444223 := bstep (se 1 (by rfl) ⟨333167, by rfl⟩ : syracuseStep 444223 = 666335) B666335
theorem B247615 : Blo 243817 247615 := bstep (se 1 (by rfl) ⟨185711, by rfl⟩ : syracuseStep 247615 = 371423) B371423
theorem B247791 : Blo 243817 247791 := bstep (se 1 (by rfl) ⟨185843, by rfl⟩ : syracuseStep 247791 = 371687) B371687
theorem B935945 : Blo 243817 935945 := bstep (se 2 (by rfl) ⟨350979, by rfl⟩ : syracuseStep 935945 = 701959) B701959
theorem B411743 : Blo 243817 411743 := bstep (se 1 (by rfl) ⟨308807, by rfl⟩ : syracuseStep 411743 = 617615) B617615
theorem B575905 : Blo 243817 575905 := bstep (se 2 (by rfl) ⟨215964, by rfl⟩ : syracuseStep 575905 = 431929) B431929
theorem B8604107 : Blo 243817 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B838487 : Blo 243817 838487 := bstep (se 1 (by rfl) ⟨628865, by rfl⟩ : syracuseStep 838487 = 1257731) B1257731
theorem B9653411 : Blo 243817 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B413039 : Blo 243817 413039 := bstep (se 1 (by rfl) ⟨309779, by rfl⟩ : syracuseStep 413039 = 619559) B619559
theorem B5328251 : Blo 243817 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B2837929 : Blo 243817 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B1396217 : Blo 243817 1396217 := bstep (se 2 (by rfl) ⟨523581, by rfl⟩ : syracuseStep 1396217 = 1047163) B1047163
theorem B413275 : Blo 243817 413275 := bstep (se 1 (by rfl) ⟨309956, by rfl⟩ : syracuseStep 413275 = 619913) B619913
theorem B1396399 : Blo 243817 1396399 := bstep (se 1 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 1396399 = 2094599) B2094599
theorem B413417 : Blo 243817 413417 := bstep (se 2 (by rfl) ⟨155031, by rfl⟩ : syracuseStep 413417 = 310063) B310063
theorem B3133241 : Blo 243817 3133241 := bstep (se 2 (by rfl) ⟨1174965, by rfl⟩ : syracuseStep 3133241 = 2349931) B2349931
theorem B7721249 : Blo 243817 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B348553 : Blo 243817 348553 := bstep (se 2 (by rfl) ⟨130707, by rfl⟩ : syracuseStep 348553 = 261415) B261415
theorem B741881 : Blo 243817 741881 := bstep (se 2 (by rfl) ⟨278205, by rfl⟩ : syracuseStep 741881 = 556411) B556411
theorem B1331873 : Blo 243817 1331873 := bstep (se 2 (by rfl) ⟨499452, by rfl⟩ : syracuseStep 1331873 = 998905) B998905
theorem B414443 : Blo 243817 414443 := bstep (se 1 (by rfl) ⟨310832, by rfl⟩ : syracuseStep 414443 = 621665) B621665
theorem B2085851 : Blo 243817 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B1856519 : Blo 243817 1856519 := bstep (se 1 (by rfl) ⟨1392389, by rfl⟩ : syracuseStep 1856519 = 2784779) B2784779
theorem B1397857 : Blo 243817 1397857 := bstep (se 2 (by rfl) ⟨524196, by rfl⟩ : syracuseStep 1397857 = 1048393) B1048393
theorem B414895 : Blo 243817 414895 := bstep (se 1 (by rfl) ⟨311171, by rfl⟩ : syracuseStep 414895 = 622343) B622343
theorem B710315 : Blo 243817 710315 := bstep (se 1 (by rfl) ⟨532736, by rfl⟩ : syracuseStep 710315 = 1065473) B1065473
theorem B415415 : Blo 243817 415415 := bstep (se 1 (by rfl) ⟨311561, by rfl⟩ : syracuseStep 415415 = 623123) B623123
theorem B349915 : Blo 243817 349915 := bstep (se 1 (by rfl) ⟨262436, by rfl⟩ : syracuseStep 349915 = 524873) B524873
theorem B939833 : Blo 243817 939833 := bstep (se 2 (by rfl) ⟨352437, by rfl⟩ : syracuseStep 939833 = 704875) B704875
theorem B416603 : Blo 243817 416603 := bstep (se 1 (by rfl) ⟨312452, by rfl⟩ : syracuseStep 416603 = 624905) B624905
theorem B416839 : Blo 243817 416839 := bstep (se 1 (by rfl) ⟨312629, by rfl⟩ : syracuseStep 416839 = 625259) B625259
theorem B1236221 : Blo 243817 1236221 := bstep (se 3 (by rfl) ⟨231791, by rfl⟩ : syracuseStep 1236221 = 463583) B463583
theorem B417271 : Blo 243817 417271 := bstep (se 1 (by rfl) ⟨312953, by rfl⟩ : syracuseStep 417271 = 625907) B625907
theorem B712439 : Blo 243817 712439 := bstep (se 1 (by rfl) ⟨534329, by rfl⟩ : syracuseStep 712439 = 1068659) B1068659
theorem B352039 : Blo 243817 352039 := bstep (se 1 (by rfl) ⟨264029, by rfl⟩ : syracuseStep 352039 = 528059) B528059
theorem B417575 : Blo 243817 417575 := bstep (se 1 (by rfl) ⟨313181, by rfl⟩ : syracuseStep 417575 = 626363) B626363
theorem B1237031 : Blo 243817 1237031 := bstep (se 1 (by rfl) ⟨927773, by rfl⟩ : syracuseStep 1237031 = 1855547) B1855547
theorem B2121767 : Blo 243817 2121767 := bstep (se 1 (by rfl) ⟨1591325, by rfl⟩ : syracuseStep 2121767 = 3182651) B3182651
theorem B1761527 : Blo 243817 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B1859921 : Blo 243817 1859921 := bstep (se 2 (by rfl) ⟨697470, by rfl⟩ : syracuseStep 1859921 = 1394941) B1394941
theorem B352711 : Blo 243817 352711 := bstep (se 1 (by rfl) ⟨264533, by rfl⟩ : syracuseStep 352711 = 529067) B529067
theorem B549611 : Blo 243817 549611 := bstep (se 1 (by rfl) ⟨412208, by rfl⟩ : syracuseStep 549611 = 824417) B824417
theorem B1238003 : Blo 243817 1238003 := bstep (se 1 (by rfl) ⟨928502, by rfl⟩ : syracuseStep 1238003 = 1857005) B1857005
theorem B3957923 : Blo 243817 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B1041731 : Blo 243817 1041731 := bstep (se 1 (by rfl) ⟨781298, by rfl⟩ : syracuseStep 1041731 = 1562597) B1562597
theorem B550511 : Blo 243817 550511 := bstep (se 1 (by rfl) ⟨412883, by rfl⟩ : syracuseStep 550511 = 825767) B825767
theorem B550619 : Blo 243817 550619 := bstep (se 1 (by rfl) ⟨412964, by rfl⟩ : syracuseStep 550619 = 825929) B825929
theorem B2778947 : Blo 243817 2778947 := bstep (se 1 (by rfl) ⟨2084210, by rfl⟩ : syracuseStep 2778947 = 4168421) B4168421
theorem B714575 : Blo 243817 714575 := bstep (se 1 (by rfl) ⟨535931, by rfl⟩ : syracuseStep 714575 = 1071863) B1071863
theorem B1173523 : Blo 243817 1173523 := bstep (se 1 (by rfl) ⟨880142, by rfl⟩ : syracuseStep 1173523 = 1760285) B1760285
theorem B747731 : Blo 243817 747731 := bstep (se 1 (by rfl) ⟨560798, by rfl⟩ : syracuseStep 747731 = 1121597) B1121597
theorem B9038141 : Blo 243817 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B1567259 : Blo 243817 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B1239623 : Blo 243817 1239623 := bstep (se 1 (by rfl) ⟨929717, by rfl⟩ : syracuseStep 1239623 = 1859435) B1859435
theorem B551735 : Blo 243817 551735 := bstep (se 1 (by rfl) ⟨413801, by rfl⟩ : syracuseStep 551735 = 827603) B827603
theorem B551915 : Blo 243817 551915 := bstep (se 1 (by rfl) ⟨413936, by rfl⟩ : syracuseStep 551915 = 827873) B827873
theorem B36137987 : Blo 243817 36137987 := bstep (se 1 (by rfl) ⟨27103490, by rfl⟩ : syracuseStep 36137987 = 54206981) B54206981
theorem B5303339 : Blo 243817 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B617807 : Blo 243817 617807 := bstep (se 1 (by rfl) ⟨463355, by rfl⟩ : syracuseStep 617807 = 926711) B926711
theorem B552743 : Blo 243817 552743 := bstep (se 1 (by rfl) ⟨414557, by rfl⟩ : syracuseStep 552743 = 829115) B829115
theorem B2944907 : Blo 243817 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B2813939 : Blo 243817 2813939 := bstep (se 1 (by rfl) ⟨2110454, by rfl⟩ : syracuseStep 2813939 = 4220909) B4220909
theorem B880951 : Blo 243817 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B1503631 : Blo 243817 1503631 := bstep (se 1 (by rfl) ⟨1127723, by rfl⟩ : syracuseStep 1503631 = 2255447) B2255447
theorem B782759 : Blo 243817 782759 := bstep (se 1 (by rfl) ⟨587069, by rfl⟩ : syracuseStep 782759 = 1174139) B1174139
theorem B881111 : Blo 243817 881111 := bstep (se 1 (by rfl) ⟨660833, by rfl⟩ : syracuseStep 881111 = 1321667) B1321667
theorem B619103 : Blo 243817 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B553769 : Blo 243817 553769 := bstep (se 2 (by rfl) ⟨207663, by rfl⟩ : syracuseStep 553769 = 415327) B415327
theorem B554039 : Blo 243817 554039 := bstep (se 1 (by rfl) ⟨415529, by rfl⟩ : syracuseStep 554039 = 831059) B831059
theorem B554057 : Blo 243817 554057 := bstep (se 2 (by rfl) ⟨207771, by rfl⟩ : syracuseStep 554057 = 415543) B415543
theorem B5306107 : Blo 243817 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B522215 : Blo 243817 522215 := bstep (se 1 (by rfl) ⟨391661, by rfl⟩ : syracuseStep 522215 = 783323) B783323
theorem B620743 : Blo 243817 620743 := bstep (se 1 (by rfl) ⟨465557, by rfl⟩ : syracuseStep 620743 = 931115) B931115
theorem B4225283 : Blo 243817 4225283 := bstep (se 1 (by rfl) ⟨3168962, by rfl⟩ : syracuseStep 4225283 = 6337925) B6337925
theorem B555983 : Blo 243817 555983 := bstep (se 1 (by rfl) ⟨416987, by rfl⟩ : syracuseStep 555983 = 833975) B833975
theorem B556001 : Blo 243817 556001 := bstep (se 2 (by rfl) ⟨208500, by rfl⟩ : syracuseStep 556001 = 417001) B417001
theorem B556073 : Blo 243817 556073 := bstep (se 2 (by rfl) ⟨208527, by rfl⟩ : syracuseStep 556073 = 417055) B417055
theorem B3210329 : Blo 243817 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B261343 : Blo 243817 261343 := bstep (se 1 (by rfl) ⟨196007, by rfl⟩ : syracuseStep 261343 = 392015) B392015
theorem B1703405 : Blo 243817 1703405 := bstep (se 3 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 1703405 = 638777) B638777
theorem B523855 : Blo 243817 523855 := bstep (se 1 (by rfl) ⟨392891, by rfl⟩ : syracuseStep 523855 = 785783) B785783
theorem B524009 : Blo 243817 524009 := bstep (se 2 (by rfl) ⟨196503, by rfl⟩ : syracuseStep 524009 = 393007) B393007
theorem B622313 : Blo 243817 622313 := bstep (se 2 (by rfl) ⟨233367, by rfl⟩ : syracuseStep 622313 = 466735) B466735
theorem B884467 : Blo 243817 884467 := bstep (se 1 (by rfl) ⟨663350, by rfl⟩ : syracuseStep 884467 = 1326701) B1326701
theorem B1277687 : Blo 243817 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B1572695 : Blo 243817 1572695 := bstep (se 1 (by rfl) ⟨1179521, by rfl⟩ : syracuseStep 1572695 = 2359043) B2359043
theorem B557243 : Blo 243817 557243 := bstep (se 1 (by rfl) ⟨417932, by rfl⟩ : syracuseStep 557243 = 835865) B835865
theorem B3145999 : Blo 243817 3145999 := bstep (se 1 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 3145999 = 4718999) B4718999
theorem B557351 : Blo 243817 557351 := bstep (se 1 (by rfl) ⟨418013, by rfl⟩ : syracuseStep 557351 = 836027) B836027
theorem B3146363 : Blo 243817 3146363 := bstep (se 1 (by rfl) ⟨2359772, by rfl⟩ : syracuseStep 3146363 = 4719545) B4719545
theorem B263359 : Blo 243817 263359 := bstep (se 1 (by rfl) ⟨197519, by rfl⟩ : syracuseStep 263359 = 395039) B395039
theorem B1049881 : Blo 243817 1049881 := bstep (se 2 (by rfl) ⟨393705, by rfl⟩ : syracuseStep 1049881 = 787411) B787411
theorem B623963 : Blo 243817 623963 := bstep (se 1 (by rfl) ⟨467972, by rfl⟩ : syracuseStep 623963 = 935945) B935945
theorem B1246751 : Blo 243817 1246751 := bstep (se 1 (by rfl) ⟨935063, by rfl⟩ : syracuseStep 1246751 = 1870127) B1870127
theorem B5736071 : Blo 243817 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B2819771 : Blo 243817 2819771 := bstep (se 1 (by rfl) ⟨2114828, by rfl⟩ : syracuseStep 2819771 = 4229657) B4229657
theorem B558991 : Blo 243817 558991 := bstep (se 1 (by rfl) ⟨419243, by rfl⟩ : syracuseStep 558991 = 838487) B838487
theorem B3999955 : Blo 243817 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B1050839 : Blo 243817 1050839 := bstep (se 1 (by rfl) ⟨788129, by rfl⟩ : syracuseStep 1050839 = 1576259) B1576259
theorem B1575719 : Blo 243817 1575719 := bstep (se 1 (by rfl) ⟨1181789, by rfl⟩ : syracuseStep 1575719 = 2363579) B2363579
theorem B14289857 : Blo 243817 14289857 := bstep (se 2 (by rfl) ⟨5358696, by rfl⟩ : syracuseStep 14289857 = 10717393) B10717393
theorem B494587 : Blo 243817 494587 := bstep (se 1 (by rfl) ⟨370940, by rfl⟩ : syracuseStep 494587 = 741881) B741881
theorem B887915 : Blo 243817 887915 := bstep (se 1 (by rfl) ⟨665936, by rfl⟩ : syracuseStep 887915 = 1331873) B1331873
theorem B1576745 : Blo 243817 1576745 := bstep (se 2 (by rfl) ⟨591279, by rfl⟩ : syracuseStep 1576745 = 1182559) B1182559
theorem B626555 : Blo 243817 626555 := bstep (se 1 (by rfl) ⟨469916, by rfl⟩ : syracuseStep 626555 = 939833) B939833
theorem B626849 : Blo 243817 626849 := bstep (se 2 (by rfl) ⟨235068, by rfl⟩ : syracuseStep 626849 = 470137) B470137
theorem B463067 : Blo 243817 463067 := bstep (se 1 (by rfl) ⟨347300, by rfl⟩ : syracuseStep 463067 = 694601) B694601
theorem B2101571 : Blo 243817 2101571 := bstep (se 1 (by rfl) ⟨1576178, by rfl⟩ : syracuseStep 2101571 = 3152357) B3152357
theorem B2101949 : Blo 243817 2101949 := bstep (se 3 (by rfl) ⟨394115, by rfl⟩ : syracuseStep 2101949 = 788231) B788231
theorem B824147 : Blo 243817 824147 := bstep (se 1 (by rfl) ⟨618110, by rfl⟩ : syracuseStep 824147 = 1236221) B1236221
theorem B824687 : Blo 243817 824687 := bstep (se 1 (by rfl) ⟨618515, by rfl⟩ : syracuseStep 824687 = 1237031) B1237031
theorem B1414511 : Blo 243817 1414511 := bstep (se 1 (by rfl) ⟨1060883, by rfl⟩ : syracuseStep 1414511 = 2121767) B2121767
theorem B366407 : Blo 243817 366407 := bstep (se 1 (by rfl) ⟨274805, by rfl⟩ : syracuseStep 366407 = 549611) B549611
theorem B2004841 : Blo 243817 2004841 := bstep (se 2 (by rfl) ⟨751815, by rfl⟩ : syracuseStep 2004841 = 1503631) B1503631
theorem B825335 : Blo 243817 825335 := bstep (se 1 (by rfl) ⟨619001, by rfl⟩ : syracuseStep 825335 = 1238003) B1238003
theorem B694487 : Blo 243817 694487 := bstep (se 1 (by rfl) ⟨520865, by rfl⟩ : syracuseStep 694487 = 1041731) B1041731
theorem B367007 : Blo 243817 367007 := bstep (se 1 (by rfl) ⟨275255, by rfl⟩ : syracuseStep 367007 = 550511) B550511
theorem B367079 : Blo 243817 367079 := bstep (se 1 (by rfl) ⟨275309, by rfl⟩ : syracuseStep 367079 = 550619) B550619
theorem B498487 : Blo 243817 498487 := bstep (se 1 (by rfl) ⟨373865, by rfl⟩ : syracuseStep 498487 = 747731) B747731
theorem B826415 : Blo 243817 826415 := bstep (se 1 (by rfl) ⟨619811, by rfl⟩ : syracuseStep 826415 = 1239623) B1239623
theorem B367823 : Blo 243817 367823 := bstep (se 1 (by rfl) ⟨275867, by rfl⟩ : syracuseStep 367823 = 551735) B551735
theorem B367943 : Blo 243817 367943 := bstep (se 1 (by rfl) ⟨275957, by rfl⟩ : syracuseStep 367943 = 551915) B551915
theorem B24091991 : Blo 243817 24091991 := bstep (se 1 (by rfl) ⟨18068993, by rfl⟩ : syracuseStep 24091991 = 36137987) B36137987
theorem B368105 : Blo 243817 368105 := bstep (se 2 (by rfl) ⟨138039, by rfl⟩ : syracuseStep 368105 = 276079) B276079
theorem B368249 : Blo 243817 368249 := bstep (se 2 (by rfl) ⟨138093, by rfl⟩ : syracuseStep 368249 = 276187) B276187
theorem B466553 : Blo 243817 466553 := bstep (se 2 (by rfl) ⟨174957, by rfl⟩ : syracuseStep 466553 = 349915) B349915
theorem B466651 : Blo 243817 466651 := bstep (se 1 (by rfl) ⟨349988, by rfl⟩ : syracuseStep 466651 = 699977) B699977
theorem B1580791 : Blo 243817 1580791 := bstep (se 1 (by rfl) ⟨1185593, by rfl⟩ : syracuseStep 1580791 = 2371187) B2371187
theorem B368495 : Blo 243817 368495 := bstep (se 1 (by rfl) ⟨276371, by rfl⟩ : syracuseStep 368495 = 552743) B552743
theorem B991199 : Blo 243817 991199 := bstep (se 1 (by rfl) ⟨743399, by rfl⟩ : syracuseStep 991199 = 1486799) B1486799
theorem B1875959 : Blo 243817 1875959 := bstep (se 1 (by rfl) ⟨1406969, by rfl⟩ : syracuseStep 1875959 = 2813939) B2813939
theorem B827657 : Blo 243817 827657 := bstep (se 2 (by rfl) ⟨310371, by rfl⟩ : syracuseStep 827657 = 620743) B620743
theorem B369179 : Blo 243817 369179 := bstep (se 1 (by rfl) ⟨276884, by rfl⟩ : syracuseStep 369179 = 553769) B553769
theorem B467623 : Blo 243817 467623 := bstep (se 1 (by rfl) ⟨350717, by rfl⟩ : syracuseStep 467623 = 701435) B701435
theorem B369359 : Blo 243817 369359 := bstep (se 1 (by rfl) ⟨277019, by rfl⟩ : syracuseStep 369359 = 554039) B554039
theorem B369371 : Blo 243817 369371 := bstep (se 1 (by rfl) ⟨277028, by rfl⟩ : syracuseStep 369371 = 554057) B554057
theorem B369785 : Blo 243817 369785 := bstep (se 2 (by rfl) ⟨138669, by rfl⟩ : syracuseStep 369785 = 277339) B277339
theorem B2369189 : Blo 243817 2369189 := bstep (se 4 (by rfl) ⟨222111, by rfl⟩ : syracuseStep 2369189 = 444223) B444223
theorem B927683 : Blo 243817 927683 := bstep (se 1 (by rfl) ⟨695762, by rfl⟩ : syracuseStep 927683 = 1391525) B1391525
theorem B370655 : Blo 243817 370655 := bstep (se 1 (by rfl) ⟨277991, by rfl⟩ : syracuseStep 370655 = 555983) B555983
theorem B370667 : Blo 243817 370667 := bstep (se 1 (by rfl) ⟨278000, by rfl⟩ : syracuseStep 370667 = 556001) B556001
theorem B370715 : Blo 243817 370715 := bstep (se 1 (by rfl) ⟨278036, by rfl⟩ : syracuseStep 370715 = 556073) B556073
theorem B2140219 : Blo 243817 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B698473 : Blo 243817 698473 := bstep (se 2 (by rfl) ⟨261927, by rfl⟩ : syracuseStep 698473 = 523855) B523855
theorem B5286221 : Blo 243817 5286221 := bstep (se 3 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 5286221 = 1982333) B1982333
theorem B469385 : Blo 243817 469385 := bstep (se 2 (by rfl) ⟨176019, by rfl⟩ : syracuseStep 469385 = 352039) B352039
theorem B371081 : Blo 243817 371081 := bstep (se 2 (by rfl) ⟨139155, by rfl⟩ : syracuseStep 371081 = 278311) B278311
theorem B666575 : Blo 243817 666575 := bstep (se 1 (by rfl) ⟨499931, by rfl⟩ : syracuseStep 666575 = 999863) B999863
theorem B470281 : Blo 243817 470281 := bstep (se 2 (by rfl) ⟨176355, by rfl⟩ : syracuseStep 470281 = 352711) B352711
theorem B20589997 : Blo 243817 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B929657 : Blo 243817 929657 := bstep (se 2 (by rfl) ⟨348621, by rfl⟩ : syracuseStep 929657 = 697243) B697243
theorem B700285 : Blo 243817 700285 := bstep (se 3 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 700285 = 262607) B262607
theorem B929825 : Blo 243817 929825 := bstep (se 2 (by rfl) ⟨348684, by rfl⟩ : syracuseStep 929825 = 697369) B697369
theorem B274495 : Blo 243817 274495 := bstep (se 1 (by rfl) ⟨205871, by rfl⟩ : syracuseStep 274495 = 411743) B411743
theorem B6435607 : Blo 243817 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B275359 : Blo 243817 275359 := bstep (se 1 (by rfl) ⟨206519, by rfl⟩ : syracuseStep 275359 = 413039) B413039
theorem B3552167 : Blo 243817 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B832463 : Blo 243817 832463 := bstep (se 1 (by rfl) ⟨624347, by rfl⟩ : syracuseStep 832463 = 1248695) B1248695
theorem B930811 : Blo 243817 930811 := bstep (se 1 (by rfl) ⟨698108, by rfl⟩ : syracuseStep 930811 = 1396217) B1396217
theorem B832571 : Blo 243817 832571 := bstep (se 1 (by rfl) ⟨624428, by rfl⟩ : syracuseStep 832571 = 1248857) B1248857
theorem B275611 : Blo 243817 275611 := bstep (se 1 (by rfl) ⟨206708, by rfl⟩ : syracuseStep 275611 = 413417) B413417
theorem B832841 : Blo 243817 832841 := bstep (se 2 (by rfl) ⟨312315, by rfl⟩ : syracuseStep 832841 = 624631) B624631
theorem B3159485 : Blo 243817 3159485 := bstep (se 3 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 3159485 = 1184807) B1184807
theorem B276295 : Blo 243817 276295 := bstep (se 1 (by rfl) ⟨207221, by rfl⟩ : syracuseStep 276295 = 414443) B414443
theorem B767873 : Blo 243817 767873 := bstep (se 2 (by rfl) ⟨287952, by rfl⟩ : syracuseStep 767873 = 575905) B575905
theorem B1390567 : Blo 243817 1390567 := bstep (se 1 (by rfl) ⟨1042925, by rfl⟩ : syracuseStep 1390567 = 2085851) B2085851
theorem B2668585 : Blo 243817 2668585 := bstep (se 2 (by rfl) ⟨1000719, by rfl⟩ : syracuseStep 2668585 = 2001439) B2001439
theorem B243943 : Blo 243817 243943 := bstep (se 1 (by rfl) ⟨182957, by rfl⟩ : syracuseStep 243943 = 365915) B365915
theorem B244127 : Blo 243817 244127 := bstep (se 1 (by rfl) ⟨183095, by rfl⟩ : syracuseStep 244127 = 366191) B366191
theorem B473543 : Blo 243817 473543 := bstep (se 1 (by rfl) ⟨355157, by rfl⟩ : syracuseStep 473543 = 710315) B710315
theorem B244175 : Blo 243817 244175 := bstep (se 1 (by rfl) ⟨183131, by rfl⟩ : syracuseStep 244175 = 366263) B366263
theorem B276943 : Blo 243817 276943 := bstep (se 1 (by rfl) ⟨207707, by rfl⟩ : syracuseStep 276943 = 415415) B415415
theorem B244199 : Blo 243817 244199 := bstep (se 1 (by rfl) ⟨183149, by rfl⟩ : syracuseStep 244199 = 366299) B366299
theorem B244315 : Blo 243817 244315 := bstep (se 1 (by rfl) ⟨183236, by rfl⟩ : syracuseStep 244315 = 366473) B366473
theorem B834191 : Blo 243817 834191 := bstep (se 1 (by rfl) ⟨625643, by rfl⟩ : syracuseStep 834191 = 1251287) B1251287
theorem B244383 : Blo 243817 244383 := bstep (se 1 (by rfl) ⟨183287, by rfl⟩ : syracuseStep 244383 = 366575) B366575
theorem B244551 : Blo 243817 244551 := bstep (se 1 (by rfl) ⟨183413, by rfl⟩ : syracuseStep 244551 = 366827) B366827
theorem B244591 : Blo 243817 244591 := bstep (se 1 (by rfl) ⟨183443, by rfl⟩ : syracuseStep 244591 = 366887) B366887
theorem B244647 : Blo 243817 244647 := bstep (se 1 (by rfl) ⟨183485, by rfl⟩ : syracuseStep 244647 = 366971) B366971
theorem B834515 : Blo 243817 834515 := bstep (se 1 (by rfl) ⟨625886, by rfl⟩ : syracuseStep 834515 = 1251773) B1251773
theorem B244827 : Blo 243817 244827 := bstep (se 1 (by rfl) ⟨183620, by rfl⟩ : syracuseStep 244827 = 367241) B367241
theorem B244943 : Blo 243817 244943 := bstep (se 1 (by rfl) ⟨183707, by rfl⟩ : syracuseStep 244943 = 367415) B367415
theorem B3783905 : Blo 243817 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B834785 : Blo 243817 834785 := bstep (se 2 (by rfl) ⟨313044, by rfl⟩ : syracuseStep 834785 = 626089) B626089
theorem B244967 : Blo 243817 244967 := bstep (se 1 (by rfl) ⟨183725, by rfl⟩ : syracuseStep 244967 = 367451) B367451
theorem B277735 : Blo 243817 277735 := bstep (se 1 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 277735 = 416603) B416603
theorem B245063 : Blo 243817 245063 := bstep (se 1 (by rfl) ⟨183797, by rfl⟩ : syracuseStep 245063 = 367595) B367595
theorem B245199 : Blo 243817 245199 := bstep (se 1 (by rfl) ⟨183899, by rfl⟩ : syracuseStep 245199 = 367799) B367799
theorem B245359 : Blo 243817 245359 := bstep (se 1 (by rfl) ⟨184019, by rfl⟩ : syracuseStep 245359 = 368039) B368039
theorem B245415 : Blo 243817 245415 := bstep (se 1 (by rfl) ⟨184061, by rfl⟩ : syracuseStep 245415 = 368123) B368123
theorem B245479 : Blo 243817 245479 := bstep (se 1 (by rfl) ⟨184109, by rfl⟩ : syracuseStep 245479 = 368219) B368219
theorem B245535 : Blo 243817 245535 := bstep (se 1 (by rfl) ⟨184151, by rfl⟩ : syracuseStep 245535 = 368303) B368303
theorem B474959 : Blo 243817 474959 := bstep (se 1 (by rfl) ⟨356219, by rfl⟩ : syracuseStep 474959 = 712439) B712439
theorem B835433 : Blo 243817 835433 := bstep (se 2 (by rfl) ⟨313287, by rfl⟩ : syracuseStep 835433 = 626575) B626575
theorem B245615 : Blo 243817 245615 := bstep (se 1 (by rfl) ⟨184211, by rfl⟩ : syracuseStep 245615 = 368423) B368423
theorem B278383 : Blo 243817 278383 := bstep (se 1 (by rfl) ⟨208787, by rfl⟩ : syracuseStep 278383 = 417575) B417575
theorem B245671 : Blo 243817 245671 := bstep (se 1 (by rfl) ⟨184253, by rfl⟩ : syracuseStep 245671 = 368507) B368507
theorem B245951 : Blo 243817 245951 := bstep (se 1 (by rfl) ⟨184463, by rfl⟩ : syracuseStep 245951 = 368927) B368927
theorem B1425599 : Blo 243817 1425599 := bstep (se 1 (by rfl) ⟨1069199, by rfl⟩ : syracuseStep 1425599 = 2138399) B2138399
theorem B245967 : Blo 243817 245967 := bstep (se 1 (by rfl) ⟨184475, by rfl⟩ : syracuseStep 245967 = 368951) B368951
theorem B246015 : Blo 243817 246015 := bstep (se 1 (by rfl) ⟨184511, by rfl⟩ : syracuseStep 246015 = 369023) B369023
theorem B704807 : Blo 243817 704807 := bstep (se 1 (by rfl) ⟨528605, by rfl⟩ : syracuseStep 704807 = 1057211) B1057211
theorem B246063 : Blo 243817 246063 := bstep (se 1 (by rfl) ⟨184547, by rfl⟩ : syracuseStep 246063 = 369095) B369095
theorem B246299 : Blo 243817 246299 := bstep (se 1 (by rfl) ⟨184724, by rfl⟩ : syracuseStep 246299 = 369449) B369449
theorem B246303 : Blo 243817 246303 := bstep (se 1 (by rfl) ⟨184727, by rfl⟩ : syracuseStep 246303 = 369455) B369455
theorem B246383 : Blo 243817 246383 := bstep (se 1 (by rfl) ⟨184787, by rfl⟩ : syracuseStep 246383 = 369575) B369575
theorem B246439 : Blo 243817 246439 := bstep (se 1 (by rfl) ⟨184829, by rfl⟩ : syracuseStep 246439 = 369659) B369659
theorem B246479 : Blo 243817 246479 := bstep (se 1 (by rfl) ⟨184859, by rfl⟩ : syracuseStep 246479 = 369719) B369719
theorem B2638615 : Blo 243817 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B246559 : Blo 243817 246559 := bstep (se 1 (by rfl) ⟨184919, by rfl⟩ : syracuseStep 246559 = 369839) B369839
theorem B9487205 : Blo 243817 9487205 := bstep (se 4 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 9487205 = 1778851) B1778851
theorem B246831 : Blo 243817 246831 := bstep (se 1 (by rfl) ⟨185123, by rfl⟩ : syracuseStep 246831 = 370247) B370247
theorem B246895 : Blo 243817 246895 := bstep (se 1 (by rfl) ⟨185171, by rfl⟩ : syracuseStep 246895 = 370343) B370343
theorem B246951 : Blo 243817 246951 := bstep (se 1 (by rfl) ⟨185213, by rfl⟩ : syracuseStep 246951 = 370427) B370427
theorem B246975 : Blo 243817 246975 := bstep (se 1 (by rfl) ⟨185231, by rfl⟩ : syracuseStep 246975 = 370463) B370463
theorem B1852631 : Blo 243817 1852631 := bstep (se 1 (by rfl) ⟨1389473, by rfl⟩ : syracuseStep 1852631 = 2778947) B2778947
theorem B476383 : Blo 243817 476383 := bstep (se 1 (by rfl) ⟨357287, by rfl⟩ : syracuseStep 476383 = 714575) B714575
theorem B247007 : Blo 243817 247007 := bstep (se 1 (by rfl) ⟨185255, by rfl⟩ : syracuseStep 247007 = 370511) B370511
theorem B247087 : Blo 243817 247087 := bstep (se 1 (by rfl) ⟨185315, by rfl⟩ : syracuseStep 247087 = 370631) B370631
theorem B312655 : Blo 243817 312655 := bstep (se 1 (by rfl) ⟨234491, by rfl⟩ : syracuseStep 312655 = 468983) B468983
theorem B247323 : Blo 243817 247323 := bstep (se 1 (by rfl) ⟨185492, by rfl⟩ : syracuseStep 247323 = 370985) B370985
theorem B247327 : Blo 243817 247327 := bstep (se 1 (by rfl) ⟨185495, by rfl⟩ : syracuseStep 247327 = 370991) B370991
theorem B378475 : Blo 243817 378475 := bstep (se 1 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 378475 = 567713) B567713
theorem B444079 : Blo 243817 444079 := bstep (se 1 (by rfl) ⟨333059, by rfl⟩ : syracuseStep 444079 = 666119) B666119
theorem B247487 : Blo 243817 247487 := bstep (se 1 (by rfl) ⟨185615, by rfl⟩ : syracuseStep 247487 = 371231) B371231
theorem B247743 : Blo 243817 247743 := bstep (se 1 (by rfl) ⟨185807, by rfl⟩ : syracuseStep 247743 = 371615) B371615
theorem B247775 : Blo 243817 247775 := bstep (se 1 (by rfl) ⟨185831, by rfl⟩ : syracuseStep 247775 = 371663) B371663
theorem B411871 : Blo 243817 411871 := bstep (se 1 (by rfl) ⟨308903, by rfl⟩ : syracuseStep 411871 = 617807) B617807
theorem B313627 : Blo 243817 313627 := bstep (se 1 (by rfl) ⟨235220, by rfl⟩ : syracuseStep 313627 = 470441) B470441
theorem B3164453 : Blo 243817 3164453 := bstep (se 4 (by rfl) ⟨296667, by rfl⟩ : syracuseStep 3164453 = 593335) B593335
theorem B412735 : Blo 243817 412735 := bstep (se 1 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 412735 = 619103) B619103
theorem B4181543 : Blo 243817 4181543 := bstep (se 1 (by rfl) ⟨3136157, by rfl⟩ : syracuseStep 4181543 = 6272315) B6272315
theorem B348143 : Blo 243817 348143 := bstep (se 1 (by rfl) ⟨261107, by rfl⟩ : syracuseStep 348143 = 522215) B522215
theorem B348457 : Blo 243817 348457 := bstep (se 2 (by rfl) ⟨130671, by rfl⟩ : syracuseStep 348457 = 261343) B261343
theorem B1397357 : Blo 243817 1397357 := bstep (se 3 (by rfl) ⟨262004, by rfl⟩ : syracuseStep 1397357 = 524009) B524009
theorem B1004141 : Blo 243817 1004141 := bstep (se 3 (by rfl) ⟨188276, by rfl⟩ : syracuseStep 1004141 = 376553) B376553
theorem B4051781 : Blo 243817 4051781 := bstep (se 4 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 4051781 = 759709) B759709
theorem B1496045 : Blo 243817 1496045 := bstep (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) B561017
theorem B1135603 : Blo 243817 1135603 := bstep (se 1 (by rfl) ⟨851702, by rfl⟩ : syracuseStep 1135603 = 1703405) B1703405
theorem B414875 : Blo 243817 414875 := bstep (se 1 (by rfl) ⟨311156, by rfl⟩ : syracuseStep 414875 = 622313) B622313
theorem B2021021 : Blo 243817 2021021 := bstep (se 3 (by rfl) ⟨378941, by rfl⟩ : syracuseStep 2021021 = 757883) B757883
theorem B350023 : Blo 243817 350023 := bstep (se 1 (by rfl) ⟨262517, by rfl⟩ : syracuseStep 350023 = 525035) B525035
theorem B3561803 : Blo 243817 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B1399315 : Blo 243817 1399315 := bstep (se 1 (by rfl) ⟨1049486, by rfl⟩ : syracuseStep 1399315 = 2098973) B2098973
theorem B416569 : Blo 243817 416569 := bstep (se 2 (by rfl) ⟨156213, by rfl⟩ : syracuseStep 416569 = 312427) B312427
theorem B416623 : Blo 243817 416623 := bstep (se 1 (by rfl) ⟨312467, by rfl⟩ : syracuseStep 416623 = 624935) B624935
theorem B1858949 : Blo 243817 1858949 := bstep (se 4 (by rfl) ⟨174276, by rfl⟩ : syracuseStep 1858949 = 348553) B348553
theorem B1498745 : Blo 243817 1498745 := bstep (se 2 (by rfl) ⟨562029, by rfl⟩ : syracuseStep 1498745 = 1124059) B1124059
theorem B843385 : Blo 243817 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B2121383 : Blo 243817 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B548639 : Blo 243817 548639 := bstep (se 1 (by rfl) ⟨411479, by rfl⟩ : syracuseStep 548639 = 822959) B822959
theorem B2088827 : Blo 243817 2088827 := bstep (se 1 (by rfl) ⟨1566620, by rfl⟩ : syracuseStep 2088827 = 3133241) B3133241
theorem B548855 : Blo 243817 548855 := bstep (se 1 (by rfl) ⟨411641, by rfl⟩ : syracuseStep 548855 = 823283) B823283
theorem B1564697 : Blo 243817 1564697 := bstep (se 2 (by rfl) ⟨586761, by rfl⟩ : syracuseStep 1564697 = 1173523) B1173523
theorem B549071 : Blo 243817 549071 := bstep (se 1 (by rfl) ⟨411803, by rfl⟩ : syracuseStep 549071 = 823607) B823607
theorem B549215 : Blo 243817 549215 := bstep (se 1 (by rfl) ⟨411911, by rfl⟩ : syracuseStep 549215 = 823823) B823823
theorem B1237679 : Blo 243817 1237679 := bstep (se 1 (by rfl) ⟨928259, by rfl⟩ : syracuseStep 1237679 = 1856519) B1856519
theorem B1860407 : Blo 243817 1860407 := bstep (se 1 (by rfl) ⟨1395305, by rfl⟩ : syracuseStep 1860407 = 2790611) B2790611
theorem B549935 : Blo 243817 549935 := bstep (se 1 (by rfl) ⟨412451, by rfl⟩ : syracuseStep 549935 = 824903) B824903
theorem B2385229 : Blo 243817 2385229 := bstep (se 3 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 2385229 = 894461) B894461
theorem B3007853 : Blo 243817 3007853 := bstep (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) B1127945
theorem B48850289 : Blo 243817 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B550583 : Blo 243817 550583 := bstep (se 1 (by rfl) ⟨412937, by rfl⟩ : syracuseStep 550583 = 825875) B825875
theorem B1861379 : Blo 243817 1861379 := bstep (se 1 (by rfl) ⟨1396034, by rfl⟩ : syracuseStep 1861379 = 2792069) B2792069
theorem B1239137 : Blo 243817 1239137 := bstep (se 2 (by rfl) ⟨464676, by rfl⟩ : syracuseStep 1239137 = 929353) B929353
theorem B551033 : Blo 243817 551033 := bstep (se 2 (by rfl) ⟨206637, by rfl⟩ : syracuseStep 551033 = 413275) B413275
theorem B1861865 : Blo 243817 1861865 := bstep (se 2 (by rfl) ⟨698199, by rfl⟩ : syracuseStep 1861865 = 1396399) B1396399
theorem B1174351 : Blo 243817 1174351 := bstep (se 1 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 1174351 = 1761527) B1761527
theorem B1239947 : Blo 243817 1239947 := bstep (se 1 (by rfl) ⟨929960, by rfl⟩ : syracuseStep 1239947 = 1859921) B1859921
theorem B1174601 : Blo 243817 1174601 := bstep (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) B880951
theorem B552347 : Blo 243817 552347 := bstep (se 1 (by rfl) ⟨414260, by rfl⟩ : syracuseStep 552347 = 828521) B828521
theorem B617939 : Blo 243817 617939 := bstep (se 1 (by rfl) ⟨463454, by rfl⟩ : syracuseStep 617939 = 926909) B926909
theorem B4615639 : Blo 243817 4615639 := bstep (se 1 (by rfl) ⟨3461729, by rfl⟩ : syracuseStep 4615639 = 6923459) B6923459
theorem B552923 : Blo 243817 552923 := bstep (se 1 (by rfl) ⟨414692, by rfl⟩ : syracuseStep 552923 = 829385) B829385
theorem B1863809 : Blo 243817 1863809 := bstep (se 2 (by rfl) ⟨698928, by rfl⟩ : syracuseStep 1863809 = 1397857) B1397857
theorem B553103 : Blo 243817 553103 := bstep (se 1 (by rfl) ⟨414827, by rfl⟩ : syracuseStep 553103 = 829655) B829655
theorem B6025427 : Blo 243817 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B553193 : Blo 243817 553193 := bstep (se 2 (by rfl) ⟨207447, by rfl⟩ : syracuseStep 553193 = 414895) B414895
theorem B3993857 : Blo 243817 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B1044839 : Blo 243817 1044839 := bstep (se 1 (by rfl) ⟨783629, by rfl⟩ : syracuseStep 1044839 = 1567259) B1567259
theorem B553319 : Blo 243817 553319 := bstep (se 1 (by rfl) ⟨414989, by rfl⟩ : syracuseStep 553319 = 829979) B829979
theorem B3535559 : Blo 243817 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B553895 : Blo 243817 553895 := bstep (se 1 (by rfl) ⟨415421, by rfl⟩ : syracuseStep 553895 = 830843) B830843
theorem B7074809 : Blo 243817 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B1963271 : Blo 243817 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B488767 : Blo 243817 488767 := bstep (se 1 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 488767 = 733151) B733151
theorem B521839 : Blo 243817 521839 := bstep (se 1 (by rfl) ⟨391379, by rfl⟩ : syracuseStep 521839 = 782759) B782759
theorem B587407 : Blo 243817 587407 := bstep (se 1 (by rfl) ⟨440555, by rfl⟩ : syracuseStep 587407 = 881111) B881111
theorem B620257 : Blo 243817 620257 := bstep (se 2 (by rfl) ⟨232596, by rfl⟩ : syracuseStep 620257 = 465193) B465193
theorem B554831 : Blo 243817 554831 := bstep (se 1 (by rfl) ⟨416123, by rfl⟩ : syracuseStep 554831 = 832247) B832247
theorem B8353763 : Blo 243817 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B555191 : Blo 243817 555191 := bstep (se 1 (by rfl) ⟨416393, by rfl⟩ : syracuseStep 555191 = 832787) B832787
theorem B13727981 : Blo 243817 13727981 := bstep (se 3 (by rfl) ⟨2573996, by rfl⟩ : syracuseStep 13727981 = 5147993) B5147993
theorem B555551 : Blo 243817 555551 := bstep (se 1 (by rfl) ⟨416663, by rfl⟩ : syracuseStep 555551 = 833327) B833327
theorem B555785 : Blo 243817 555785 := bstep (se 2 (by rfl) ⟨208419, by rfl⟩ : syracuseStep 555785 = 416839) B416839
theorem B2816855 : Blo 243817 2816855 := bstep (se 1 (by rfl) ⟨2112641, by rfl⟩ : syracuseStep 2816855 = 4225283) B4225283
theorem B883993 : Blo 243817 883993 := bstep (se 2 (by rfl) ⟨331497, by rfl⟩ : syracuseStep 883993 = 662995) B662995
theorem B556361 : Blo 243817 556361 := bstep (se 2 (by rfl) ⟨208635, by rfl⟩ : syracuseStep 556361 = 417271) B417271
theorem B1015247 : Blo 243817 1015247 := bstep (se 1 (by rfl) ⟨761435, by rfl⟩ : syracuseStep 1015247 = 1522871) B1522871
theorem B294511 : Blo 243817 294511 := bstep (se 1 (by rfl) ⟨220883, by rfl⟩ : syracuseStep 294511 = 441767) B441767
theorem B1179289 : Blo 243817 1179289 := bstep (se 2 (by rfl) ⟨442233, by rfl⟩ : syracuseStep 1179289 = 884467) B884467
theorem B556775 : Blo 243817 556775 := bstep (se 1 (by rfl) ⟨417581, by rfl⟩ : syracuseStep 556775 = 835163) B835163
theorem B851791 : Blo 243817 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B1048463 : Blo 243817 1048463 := bstep (se 1 (by rfl) ⟨786347, by rfl⟩ : syracuseStep 1048463 = 1572695) B1572695
theorem B950399 : Blo 243817 950399 := bstep (se 1 (by rfl) ⟨712799, by rfl⟩ : syracuseStep 950399 = 1425599) B1425599
theorem B4194665 : Blo 243817 4194665 := bstep (se 2 (by rfl) ⟨1572999, by rfl⟩ : syracuseStep 4194665 = 3145999) B3145999
theorem B2097575 : Blo 243817 2097575 := bstep (se 1 (by rfl) ⟨1573181, by rfl⟩ : syracuseStep 2097575 = 3146363) B3146363
theorem B6324803 : Blo 243817 6324803 := bstep (se 1 (by rfl) ⟨4743602, by rfl⟩ : syracuseStep 6324803 = 9487205) B9487205
theorem B623497 : Blo 243817 623497 := bstep (se 2 (by rfl) ⟨233811, by rfl⟩ : syracuseStep 623497 = 467623) B467623
theorem B2786237 : Blo 243817 2786237 := bstep (se 3 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 2786237 = 1044839) B1044839
theorem B3180305 : Blo 243817 3180305 := bstep (se 2 (by rfl) ⟨1192614, by rfl⟩ : syracuseStep 3180305 = 2385229) B2385229
theorem B1050479 : Blo 243817 1050479 := bstep (se 1 (by rfl) ⟨787859, by rfl⟩ : syracuseStep 1050479 = 1575719) B1575719
theorem B591943 : Blo 243817 591943 := bstep (se 1 (by rfl) ⟨443957, by rfl⟩ : syracuseStep 591943 = 887915) B887915
theorem B592105 : Blo 243817 592105 := bstep (se 2 (by rfl) ⟨222039, by rfl⟩ : syracuseStep 592105 = 444079) B444079
theorem B2787695 : Blo 243817 2787695 := bstep (se 1 (by rfl) ⟨2090771, by rfl⟩ : syracuseStep 2787695 = 4181543) B4181543
theorem B1051163 : Blo 243817 1051163 := bstep (se 1 (by rfl) ⟨788372, by rfl⟩ : syracuseStep 1051163 = 1576745) B1576745
theorem B2853625 : Blo 243817 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B1347347 : Blo 243817 1347347 := bstep (se 1 (by rfl) ⟨1010510, by rfl⟩ : syracuseStep 1347347 = 2021021) B2021021
theorem B659449 : Blo 243817 659449 := bstep (se 2 (by rfl) ⟨247293, by rfl⟩ : syracuseStep 659449 = 494587) B494587
theorem B462991 : Blo 243817 462991 := bstep (se 1 (by rfl) ⟨347243, by rfl⟩ : syracuseStep 462991 = 694487) B694487
theorem B627041 : Blo 243817 627041 := bstep (se 2 (by rfl) ⟨235140, by rfl⟩ : syracuseStep 627041 = 470281) B470281
theorem B16061327 : Blo 243817 16061327 := bstep (se 1 (by rfl) ⟨12045995, by rfl⟩ : syracuseStep 16061327 = 24091991) B24091991
theorem B1414255 : Blo 243817 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B365759 : Blo 243817 365759 := bstep (se 1 (by rfl) ⟨274319, by rfl⟩ : syracuseStep 365759 = 548639) B548639
theorem B660799 : Blo 243817 660799 := bstep (se 1 (by rfl) ⟨495599, by rfl⟩ : syracuseStep 660799 = 991199) B991199
theorem B365903 : Blo 243817 365903 := bstep (se 1 (by rfl) ⟨274427, by rfl⟩ : syracuseStep 365903 = 548855) B548855
theorem B1250639 : Blo 243817 1250639 := bstep (se 1 (by rfl) ⟨937979, by rfl⟩ : syracuseStep 1250639 = 1875959) B1875959
theorem B365993 : Blo 243817 365993 := bstep (se 2 (by rfl) ⟨137247, by rfl⟩ : syracuseStep 365993 = 274495) B274495
theorem B366047 : Blo 243817 366047 := bstep (se 1 (by rfl) ⟨274535, by rfl⟩ : syracuseStep 366047 = 549071) B549071
theorem B366143 : Blo 243817 366143 := bstep (se 1 (by rfl) ⟨274607, by rfl⟩ : syracuseStep 366143 = 549215) B549215
theorem B464609 : Blo 243817 464609 := bstep (se 2 (by rfl) ⟨174228, by rfl⟩ : syracuseStep 464609 = 348457) B348457
theorem B825119 : Blo 243817 825119 := bstep (se 1 (by rfl) ⟨618839, by rfl⟩ : syracuseStep 825119 = 1237679) B1237679
theorem B366623 : Blo 243817 366623 := bstep (se 1 (by rfl) ⟨274967, by rfl⟩ : syracuseStep 366623 = 549935) B549935
theorem B2005235 : Blo 243817 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B1579459 : Blo 243817 1579459 := bstep (se 1 (by rfl) ⟨1184594, by rfl⟩ : syracuseStep 1579459 = 2369189) B2369189
theorem B367055 : Blo 243817 367055 := bstep (se 1 (by rfl) ⟨275291, by rfl⟩ : syracuseStep 367055 = 550583) B550583
theorem B367145 : Blo 243817 367145 := bstep (se 2 (by rfl) ⟨137679, by rfl⟩ : syracuseStep 367145 = 275359) B275359
theorem B1514137 : Blo 243817 1514137 := bstep (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) B1135603
theorem B826091 : Blo 243817 826091 := bstep (se 1 (by rfl) ⟨619568, by rfl⟩ : syracuseStep 826091 = 1239137) B1239137
theorem B367355 : Blo 243817 367355 := bstep (se 1 (by rfl) ⟨275516, by rfl⟩ : syracuseStep 367355 = 551033) B551033
theorem B367481 : Blo 243817 367481 := bstep (se 2 (by rfl) ⟨137805, by rfl⟩ : syracuseStep 367481 = 275611) B275611
theorem B826631 : Blo 243817 826631 := bstep (se 1 (by rfl) ⟨619973, by rfl⟩ : syracuseStep 826631 = 1239947) B1239947
theorem B695785 : Blo 243817 695785 := bstep (se 2 (by rfl) ⟨260919, by rfl⟩ : syracuseStep 695785 = 521839) B521839
theorem B368231 : Blo 243817 368231 := bstep (se 1 (by rfl) ⟨276173, by rfl⟩ : syracuseStep 368231 = 552347) B552347
theorem B827009 : Blo 243817 827009 := bstep (se 2 (by rfl) ⟨310128, by rfl⟩ : syracuseStep 827009 = 620257) B620257
theorem B368393 : Blo 243817 368393 := bstep (se 2 (by rfl) ⟨138147, by rfl⟩ : syracuseStep 368393 = 276295) B276295
theorem B466697 : Blo 243817 466697 := bstep (se 2 (by rfl) ⟨175011, by rfl⟩ : syracuseStep 466697 = 350023) B350023
theorem B368615 : Blo 243817 368615 := bstep (se 1 (by rfl) ⟨276461, by rfl⟩ : syracuseStep 368615 = 552923) B552923
theorem B368735 : Blo 243817 368735 := bstep (se 1 (by rfl) ⟨276551, by rfl⟩ : syracuseStep 368735 = 553103) B553103
theorem B368795 : Blo 243817 368795 := bstep (se 1 (by rfl) ⟨276596, by rfl⟩ : syracuseStep 368795 = 553193) B553193
theorem B2662571 : Blo 243817 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B368879 : Blo 243817 368879 := bstep (se 1 (by rfl) ⟨276659, by rfl⟩ : syracuseStep 368879 = 553319) B553319
theorem B369257 : Blo 243817 369257 := bstep (se 2 (by rfl) ⟨138471, by rfl⟩ : syracuseStep 369257 = 276943) B276943
theorem B369263 : Blo 243817 369263 := bstep (se 1 (by rfl) ⟨276947, by rfl⟩ : syracuseStep 369263 = 553895) B553895
theorem B2368111 : Blo 243817 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B2106323 : Blo 243817 2106323 := bstep (se 1 (by rfl) ⟨1579742, by rfl⟩ : syracuseStep 2106323 = 3159485) B3159485
theorem B664649 : Blo 243817 664649 := bstep (se 2 (by rfl) ⟨249243, by rfl⟩ : syracuseStep 664649 = 498487) B498487
theorem B369887 : Blo 243817 369887 := bstep (se 1 (by rfl) ⟨277415, by rfl⟩ : syracuseStep 369887 = 554831) B554831
theorem B370127 : Blo 243817 370127 := bstep (se 1 (by rfl) ⟨277595, by rfl⟩ : syracuseStep 370127 = 555191) B555191
theorem B9151987 : Blo 243817 9151987 := bstep (se 1 (by rfl) ⟨6863990, by rfl⟩ : syracuseStep 9151987 = 13727981) B13727981
theorem B370313 : Blo 243817 370313 := bstep (se 2 (by rfl) ⟨138867, by rfl⟩ : syracuseStep 370313 = 277735) B277735
theorem B370367 : Blo 243817 370367 := bstep (se 1 (by rfl) ⟨277775, by rfl⟩ : syracuseStep 370367 = 555551) B555551
theorem B370523 : Blo 243817 370523 := bstep (se 1 (by rfl) ⟨277892, by rfl⟩ : syracuseStep 370523 = 555785) B555785
theorem B10692485 : Blo 243817 10692485 := bstep (se 4 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 10692485 = 2004841) B2004841
theorem B1877903 : Blo 243817 1877903 := bstep (se 1 (by rfl) ⟨1408427, by rfl⟩ : syracuseStep 1877903 = 2816855) B2816855
theorem B1124513 : Blo 243817 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B370907 : Blo 243817 370907 := bstep (se 1 (by rfl) ⟨278180, by rfl⟩ : syracuseStep 370907 = 556361) B556361
theorem B2107721 : Blo 243817 2107721 := bstep (se 2 (by rfl) ⟨790395, by rfl⟩ : syracuseStep 2107721 = 1580791) B1580791
theorem B371177 : Blo 243817 371177 := bstep (se 2 (by rfl) ⟨139191, by rfl⟩ : syracuseStep 371177 = 278383) B278383
theorem B371183 : Blo 243817 371183 := bstep (se 1 (by rfl) ⟨278387, by rfl⟩ : syracuseStep 371183 = 556775) B556775
theorem B698975 : Blo 243817 698975 := bstep (se 1 (by rfl) ⟨524231, by rfl⟩ : syracuseStep 698975 = 1048463) B1048463
theorem B928381 : Blo 243817 928381 := bstep (se 3 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 928381 = 348143) B348143
theorem B371495 : Blo 243817 371495 := bstep (se 1 (by rfl) ⟨278621, by rfl⟩ : syracuseStep 371495 = 557243) B557243
theorem B469871 : Blo 243817 469871 := bstep (se 1 (by rfl) ⟨352403, by rfl⟩ : syracuseStep 469871 = 704807) B704807
theorem B371567 : Blo 243817 371567 := bstep (se 1 (by rfl) ⟨278675, by rfl⟩ : syracuseStep 371567 = 557351) B557351
theorem B831167 : Blo 243817 831167 := bstep (se 1 (by rfl) ⟨623375, by rfl⟩ : syracuseStep 831167 = 1246751) B1246751
theorem B3518153 : Blo 243817 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B1879847 : Blo 243817 1879847 := bstep (se 1 (by rfl) ⟨1409885, by rfl⟩ : syracuseStep 1879847 = 2819771) B2819771
theorem B700559 : Blo 243817 700559 := bstep (se 1 (by rfl) ⟨525419, by rfl⟩ : syracuseStep 700559 = 1050839) B1050839
theorem B2109635 : Blo 243817 2109635 := bstep (se 1 (by rfl) ⟨1582226, by rfl⟩ : syracuseStep 2109635 = 3164453) B3164453
theorem B635177 : Blo 243817 635177 := bstep (se 2 (by rfl) ⟨238191, by rfl⟩ : syracuseStep 635177 = 476383) B476383
theorem B931297 : Blo 243817 931297 := bstep (se 2 (by rfl) ⟨349236, by rfl⟩ : syracuseStep 931297 = 698473) B698473
theorem B308711 : Blo 243817 308711 := bstep (se 1 (by rfl) ⟨231533, by rfl⟩ : syracuseStep 308711 = 463067) B463067
theorem B931571 : Blo 243817 931571 := bstep (se 1 (by rfl) ⟨698678, by rfl⟩ : syracuseStep 931571 = 1397357) B1397357
theorem B669427 : Blo 243817 669427 := bstep (se 1 (by rfl) ⟨502070, by rfl⟩ : syracuseStep 669427 = 1004141) B1004141
theorem B2701187 : Blo 243817 2701187 := bstep (se 1 (by rfl) ⟨2025890, by rfl⟩ : syracuseStep 2701187 = 4051781) B4051781
theorem B997363 : Blo 243817 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B276583 : Blo 243817 276583 := bstep (se 1 (by rfl) ⟨207437, by rfl⟩ : syracuseStep 276583 = 414875) B414875
theorem B244271 : Blo 243817 244271 := bstep (se 1 (by rfl) ⟨183203, by rfl⟩ : syracuseStep 244271 = 366407) B366407
theorem B2374535 : Blo 243817 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B244671 : Blo 243817 244671 := bstep (se 1 (by rfl) ⟨183503, by rfl⟩ : syracuseStep 244671 = 367007) B367007
theorem B244719 : Blo 243817 244719 := bstep (se 1 (by rfl) ⟨183539, by rfl⟩ : syracuseStep 244719 = 367079) B367079
theorem B245215 : Blo 243817 245215 := bstep (se 1 (by rfl) ⟨183911, by rfl⟩ : syracuseStep 245215 = 367823) B367823
theorem B245295 : Blo 243817 245295 := bstep (se 1 (by rfl) ⟨183971, by rfl⟩ : syracuseStep 245295 = 367943) B367943
theorem B245403 : Blo 243817 245403 := bstep (se 1 (by rfl) ⟨184052, by rfl⟩ : syracuseStep 245403 = 368105) B368105
theorem B245499 : Blo 243817 245499 := bstep (se 1 (by rfl) ⟨184124, by rfl⟩ : syracuseStep 245499 = 368249) B368249
theorem B311035 : Blo 243817 311035 := bstep (se 1 (by rfl) ⟨233276, by rfl⟩ : syracuseStep 311035 = 466553) B466553
theorem B999163 : Blo 243817 999163 := bstep (se 1 (by rfl) ⟨749372, by rfl⟩ : syracuseStep 999163 = 1498745) B1498745
theorem B933713 : Blo 243817 933713 := bstep (se 2 (by rfl) ⟨350142, by rfl⟩ : syracuseStep 933713 = 700285) B700285
theorem B245663 : Blo 243817 245663 := bstep (se 1 (by rfl) ⟨184247, by rfl⟩ : syracuseStep 245663 = 368495) B368495
theorem B1392551 : Blo 243817 1392551 := bstep (se 1 (by rfl) ⟨1044413, by rfl⟩ : syracuseStep 1392551 = 2088827) B2088827
theorem B246119 : Blo 243817 246119 := bstep (se 1 (by rfl) ⟨184589, by rfl⟩ : syracuseStep 246119 = 369179) B369179
theorem B246239 : Blo 243817 246239 := bstep (se 1 (by rfl) ⟨184679, by rfl⟩ : syracuseStep 246239 = 369359) B369359
theorem B246247 : Blo 243817 246247 := bstep (se 1 (by rfl) ⟨184685, by rfl⟩ : syracuseStep 246247 = 369371) B369371
theorem B246523 : Blo 243817 246523 := bstep (se 1 (by rfl) ⟨184892, by rfl⟩ : syracuseStep 246523 = 369785) B369785
theorem B247103 : Blo 243817 247103 := bstep (se 1 (by rfl) ⟨185327, by rfl⟩ : syracuseStep 247103 = 370655) B370655
theorem B247111 : Blo 243817 247111 := bstep (se 1 (by rfl) ⟨185333, by rfl⟩ : syracuseStep 247111 = 370667) B370667
theorem B247143 : Blo 243817 247143 := bstep (se 1 (by rfl) ⟨185357, by rfl⟩ : syracuseStep 247143 = 370715) B370715
theorem B3524147 : Blo 243817 3524147 := bstep (se 1 (by rfl) ⟨2643110, by rfl⟩ : syracuseStep 3524147 = 5286221) B5286221
theorem B312923 : Blo 243817 312923 := bstep (se 1 (by rfl) ⟨234692, by rfl⟩ : syracuseStep 312923 = 469385) B469385
theorem B247387 : Blo 243817 247387 := bstep (se 1 (by rfl) ⟨185540, by rfl⟩ : syracuseStep 247387 = 371081) B371081
theorem B444383 : Blo 243817 444383 := bstep (se 1 (by rfl) ⟨333287, by rfl⟩ : syracuseStep 444383 = 666575) B666575
theorem B411959 : Blo 243817 411959 := bstep (se 1 (by rfl) ⟨308969, by rfl⟩ : syracuseStep 411959 = 617939) B617939
theorem B1854089 : Blo 243817 1854089 := bstep (se 2 (by rfl) ⟨695283, by rfl⟩ : syracuseStep 1854089 = 1390567) B1390567
theorem B3558113 : Blo 243817 3558113 := bstep (se 2 (by rfl) ⟨1334292, by rfl⟩ : syracuseStep 3558113 = 2668585) B2668585
theorem B4016951 : Blo 243817 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B2018533 : Blo 243817 2018533 := bstep (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) B378475
theorem B511915 : Blo 243817 511915 := bstep (se 1 (by rfl) ⟨383936, by rfl⟩ : syracuseStep 511915 = 767873) B767873
theorem B315695 : Blo 243817 315695 := bstep (se 1 (by rfl) ⟨236771, by rfl⟩ : syracuseStep 315695 = 473543) B473543
theorem B676831 : Blo 243817 676831 := bstep (se 1 (by rfl) ⟨507623, by rfl⟩ : syracuseStep 676831 = 1015247) B1015247
theorem B1135721 : Blo 243817 1135721 := bstep (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) B851791
theorem B316639 : Blo 243817 316639 := bstep (se 1 (by rfl) ⟨237479, by rfl⟩ : syracuseStep 316639 = 474959) B474959
theorem B1235087 : Blo 243817 1235087 := bstep (se 1 (by rfl) ⟨926315, by rfl⟩ : syracuseStep 1235087 = 1852631) B1852631
theorem B415975 : Blo 243817 415975 := bstep (se 1 (by rfl) ⟨311981, by rfl⟩ : syracuseStep 415975 = 623963) B623963
theorem B3824047 : Blo 243817 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B351145 : Blo 243817 351145 := bstep (se 2 (by rfl) ⟨131679, by rfl⟩ : syracuseStep 351145 = 263359) B263359
theorem B1399841 : Blo 243817 1399841 := bstep (se 2 (by rfl) ⟨524940, by rfl⟩ : syracuseStep 1399841 = 1049881) B1049881
theorem B416873 : Blo 243817 416873 := bstep (se 2 (by rfl) ⟨156327, by rfl⟩ : syracuseStep 416873 = 312655) B312655
theorem B9526571 : Blo 243817 9526571 := bstep (se 1 (by rfl) ⟨7144928, by rfl⟩ : syracuseStep 9526571 = 14289857) B14289857
theorem B417703 : Blo 243817 417703 := bstep (se 1 (by rfl) ⟨313277, by rfl⟩ : syracuseStep 417703 = 626555) B626555
theorem B417899 : Blo 243817 417899 := bstep (se 1 (by rfl) ⟨313424, by rfl⟩ : syracuseStep 417899 = 626849) B626849
theorem B1401047 : Blo 243817 1401047 := bstep (se 1 (by rfl) ⟨1050785, by rfl⟩ : syracuseStep 1401047 = 2101571) B2101571
theorem B5333273 : Blo 243817 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B549161 : Blo 243817 549161 := bstep (se 2 (by rfl) ⟨205935, by rfl⟩ : syracuseStep 549161 = 411871) B411871
theorem B418169 : Blo 243817 418169 := bstep (se 2 (by rfl) ⟨156813, by rfl⟩ : syracuseStep 418169 = 313627) B313627
theorem B1401299 : Blo 243817 1401299 := bstep (se 1 (by rfl) ⟨1050974, by rfl⟩ : syracuseStep 1401299 = 2101949) B2101949
theorem B549431 : Blo 243817 549431 := bstep (se 1 (by rfl) ⟨412073, by rfl⟩ : syracuseStep 549431 = 824147) B824147
theorem B549791 : Blo 243817 549791 := bstep (se 1 (by rfl) ⟨412343, by rfl⟩ : syracuseStep 549791 = 824687) B824687
theorem B943007 : Blo 243817 943007 := bstep (se 1 (by rfl) ⟨707255, by rfl⟩ : syracuseStep 943007 = 1414511) B1414511
theorem B1565801 : Blo 243817 1565801 := bstep (se 2 (by rfl) ⟨587175, by rfl⟩ : syracuseStep 1565801 = 1174351) B1174351
theorem B550223 : Blo 243817 550223 := bstep (se 1 (by rfl) ⟨412667, by rfl⟩ : syracuseStep 550223 = 825335) B825335
theorem B550313 : Blo 243817 550313 := bstep (se 2 (by rfl) ⟨206367, by rfl⟩ : syracuseStep 550313 = 412735) B412735
theorem B27453329 : Blo 243817 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B550943 : Blo 243817 550943 := bstep (se 1 (by rfl) ⟨413207, by rfl⟩ : syracuseStep 550943 = 826415) B826415
theorem B1239299 : Blo 243817 1239299 := bstep (se 1 (by rfl) ⟨929474, by rfl⟩ : syracuseStep 1239299 = 1858949) B1858949
theorem B1043131 : Blo 243817 1043131 := bstep (se 1 (by rfl) ⟨782348, by rfl⟩ : syracuseStep 1043131 = 1564697) B1564697
theorem B551771 : Blo 243817 551771 := bstep (se 1 (by rfl) ⟨413828, by rfl⟩ : syracuseStep 551771 = 827657) B827657
theorem B1240271 : Blo 243817 1240271 := bstep (se 1 (by rfl) ⟨930203, by rfl⟩ : syracuseStep 1240271 = 1860407) B1860407
theorem B32566859 : Blo 243817 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B8580809 : Blo 243817 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B1240919 : Blo 243817 1240919 := bstep (se 1 (by rfl) ⟨930689, by rfl⟩ : syracuseStep 1240919 = 1861379) B1861379
theorem B618455 : Blo 243817 618455 := bstep (se 1 (by rfl) ⟨463841, by rfl⟩ : syracuseStep 618455 = 927683) B927683
theorem B1241081 : Blo 243817 1241081 := bstep (se 2 (by rfl) ⟨465405, by rfl⟩ : syracuseStep 1241081 = 930811) B930811
theorem B1241243 : Blo 243817 1241243 := bstep (se 1 (by rfl) ⟨930932, by rfl⟩ : syracuseStep 1241243 = 1861865) B1861865
theorem B651689 : Blo 243817 651689 := bstep (se 2 (by rfl) ⟨244383, by rfl⟩ : syracuseStep 651689 = 488767) B488767
theorem B783067 : Blo 243817 783067 := bstep (se 1 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 783067 = 1174601) B1174601
theorem B783209 : Blo 243817 783209 := bstep (se 2 (by rfl) ⟨293703, by rfl⟩ : syracuseStep 783209 = 587407) B587407
theorem B619771 : Blo 243817 619771 := bstep (se 1 (by rfl) ⟨464828, by rfl⟩ : syracuseStep 619771 = 929657) B929657
theorem B619883 : Blo 243817 619883 := bstep (se 1 (by rfl) ⟨464912, by rfl⟩ : syracuseStep 619883 = 929825) B929825
theorem B1242539 : Blo 243817 1242539 := bstep (se 1 (by rfl) ⟨931904, by rfl⟩ : syracuseStep 1242539 = 1863809) B1863809
theorem B2357039 : Blo 243817 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B554975 : Blo 243817 554975 := bstep (se 1 (by rfl) ⟨416231, by rfl⟩ : syracuseStep 554975 = 832463) B832463
theorem B4716539 : Blo 243817 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B1865753 : Blo 243817 1865753 := bstep (se 2 (by rfl) ⟨699657, by rfl⟩ : syracuseStep 1865753 = 1399315) B1399315
theorem B555047 : Blo 243817 555047 := bstep (se 1 (by rfl) ⟨416285, by rfl⟩ : syracuseStep 555047 = 832571) B832571
theorem B1308847 : Blo 243817 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B555227 : Blo 243817 555227 := bstep (se 1 (by rfl) ⟨416420, by rfl⟩ : syracuseStep 555227 = 832841) B832841
theorem B555425 : Blo 243817 555425 := bstep (se 2 (by rfl) ⟨208284, by rfl⟩ : syracuseStep 555425 = 416569) B416569
theorem B555497 : Blo 243817 555497 := bstep (se 2 (by rfl) ⟨208311, by rfl⟩ : syracuseStep 555497 = 416623) B416623
theorem B5569175 : Blo 243817 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B1178657 : Blo 243817 1178657 := bstep (se 2 (by rfl) ⟨441996, by rfl⟩ : syracuseStep 1178657 = 883993) B883993
theorem B556127 : Blo 243817 556127 := bstep (se 1 (by rfl) ⟨417095, by rfl⟩ : syracuseStep 556127 = 834191) B834191
theorem B98466965 : Blo 243817 98466965 := bstep (se 6 (by rfl) ⟨2307819, by rfl⟩ : syracuseStep 98466965 = 4615639) B4615639
theorem B556343 : Blo 243817 556343 := bstep (se 1 (by rfl) ⟨417257, by rfl⟩ : syracuseStep 556343 = 834515) B834515
theorem B2981285 : Blo 243817 2981285 := bstep (se 4 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 2981285 = 558991) B558991
theorem B392681 : Blo 243817 392681 := bstep (se 2 (by rfl) ⟨147255, by rfl⟩ : syracuseStep 392681 = 294511) B294511
theorem B2522603 : Blo 243817 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B556523 : Blo 243817 556523 := bstep (se 1 (by rfl) ⟨417392, by rfl⟩ : syracuseStep 556523 = 834785) B834785
theorem B1572385 : Blo 243817 1572385 := bstep (se 2 (by rfl) ⟨589644, by rfl⟩ : syracuseStep 1572385 = 1179289) B1179289
theorem B622201 : Blo 243817 622201 := bstep (se 2 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 622201 = 466651) B466651
theorem B556955 : Blo 243817 556955 := bstep (se 1 (by rfl) ⟨417716, by rfl⟩ : syracuseStep 556955 = 835433) B835433
theorem B296255 : Blo 243817 296255 := bstep (se 1 (by rfl) ⟨222191, by rfl⟩ : syracuseStep 296255 = 444383) B444383
theorem B789257 : Blo 243817 789257 := bstep (se 2 (by rfl) ⟨295971, by rfl⟩ : syracuseStep 789257 = 591943) B591943
theorem B789473 : Blo 243817 789473 := bstep (se 2 (by rfl) ⟨296052, by rfl⟩ : syracuseStep 789473 = 592105) B592105
theorem B757147 : Blo 243817 757147 := bstep (se 1 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 757147 = 1135721) B1135721
theorem B3804833 : Blo 243817 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B823229 : Blo 243817 823229 := bstep (se 3 (by rfl) ⟨154355, by rfl⟩ : syracuseStep 823229 = 308711) B308711
theorem B823391 : Blo 243817 823391 := bstep (se 1 (by rfl) ⟨617543, by rfl⟩ : syracuseStep 823391 = 1235087) B1235087
theorem B2691377 : Blo 243817 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B6951349 : Blo 243817 6951349 := bstep (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) B651689
theorem B1775047 : Blo 243817 1775047 := bstep (se 1 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 1775047 = 2662571) B2662571
theorem B366107 : Blo 243817 366107 := bstep (se 1 (by rfl) ⟨274580, by rfl⟩ : syracuseStep 366107 = 549161) B549161
theorem B366287 : Blo 243817 366287 := bstep (se 1 (by rfl) ⟨274715, by rfl⟩ : syracuseStep 366287 = 549431) B549431
theorem B366527 : Blo 243817 366527 := bstep (se 1 (by rfl) ⟨274895, by rfl⟩ : syracuseStep 366527 = 549791) B549791
theorem B366815 : Blo 243817 366815 := bstep (se 1 (by rfl) ⟨275111, by rfl⟩ : syracuseStep 366815 = 550223) B550223
theorem B366875 : Blo 243817 366875 := bstep (se 1 (by rfl) ⟨275156, by rfl⟩ : syracuseStep 366875 = 550313) B550313
theorem B1251935 : Blo 243817 1251935 := bstep (se 1 (by rfl) ⟨938951, by rfl⟩ : syracuseStep 1251935 = 1877903) B1877903
theorem B367295 : Blo 243817 367295 := bstep (se 1 (by rfl) ⟨275471, by rfl⟩ : syracuseStep 367295 = 550943) B550943
theorem B826199 : Blo 243817 826199 := bstep (se 1 (by rfl) ⟨619649, by rfl⟩ : syracuseStep 826199 = 1239299) B1239299
theorem B826361 : Blo 243817 826361 := bstep (se 2 (by rfl) ⟨309885, by rfl⟩ : syracuseStep 826361 = 619771) B619771
theorem B14851133 : Blo 243817 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B465983 : Blo 243817 465983 := bstep (se 1 (by rfl) ⟨349487, by rfl⟩ : syracuseStep 465983 = 698975) B698975
theorem B367847 : Blo 243817 367847 := bstep (se 1 (by rfl) ⟨275885, by rfl⟩ : syracuseStep 367847 = 551771) B551771
theorem B826847 : Blo 243817 826847 := bstep (se 1 (by rfl) ⟨620135, by rfl⟩ : syracuseStep 826847 = 1240271) B1240271
theorem B1253231 : Blo 243817 1253231 := bstep (se 1 (by rfl) ⟨939923, by rfl⟩ : syracuseStep 1253231 = 1879847) B1879847
theorem B827279 : Blo 243817 827279 := bstep (se 1 (by rfl) ⟨620459, by rfl⟩ : syracuseStep 827279 = 1240919) B1240919
theorem B827387 : Blo 243817 827387 := bstep (se 1 (by rfl) ⟨620540, by rfl⟩ : syracuseStep 827387 = 1241081) B1241081
theorem B467039 : Blo 243817 467039 := bstep (se 1 (by rfl) ⟨350279, by rfl⟩ : syracuseStep 467039 = 700559) B700559
theorem B827495 : Blo 243817 827495 := bstep (se 1 (by rfl) ⟨620621, by rfl⟩ : syracuseStep 827495 = 1241243) B1241243
theorem B368777 : Blo 243817 368777 := bstep (se 2 (by rfl) ⟨138291, by rfl⟩ : syracuseStep 368777 = 276583) B276583
theorem B1745129 : Blo 243817 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B2105945 : Blo 243817 2105945 := bstep (se 2 (by rfl) ⟨789729, by rfl⟩ : syracuseStep 2105945 = 1579459) B1579459
theorem B828359 : Blo 243817 828359 := bstep (se 1 (by rfl) ⟨621269, by rfl⟩ : syracuseStep 828359 = 1242539) B1242539
theorem B468193 : Blo 243817 468193 := bstep (se 2 (by rfl) ⟨175572, by rfl⟩ : syracuseStep 468193 = 351145) B351145
theorem B369983 : Blo 243817 369983 := bstep (se 1 (by rfl) ⟨277487, by rfl⟩ : syracuseStep 369983 = 554975) B554975
theorem B370031 : Blo 243817 370031 := bstep (se 1 (by rfl) ⟨277523, by rfl⟩ : syracuseStep 370031 = 555047) B555047
theorem B370151 : Blo 243817 370151 := bstep (se 1 (by rfl) ⟨277613, by rfl⟩ : syracuseStep 370151 = 555227) B555227
theorem B370283 : Blo 243817 370283 := bstep (se 1 (by rfl) ⟨277712, by rfl⟩ : syracuseStep 370283 = 555425) B555425
theorem B370331 : Blo 243817 370331 := bstep (se 1 (by rfl) ⟨277748, by rfl⟩ : syracuseStep 370331 = 555497) B555497
theorem B1583023 : Blo 243817 1583023 := bstep (se 1 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 1583023 = 2374535) B2374535
theorem B927713 : Blo 243817 927713 := bstep (se 2 (by rfl) ⟨347892, by rfl⟩ : syracuseStep 927713 = 695785) B695785
theorem B370751 : Blo 243817 370751 := bstep (se 1 (by rfl) ⟨278063, by rfl⟩ : syracuseStep 370751 = 556127) B556127
theorem B65644643 : Blo 243817 65644643 := bstep (se 1 (by rfl) ⟨49233482, by rfl⟩ : syracuseStep 65644643 = 98466965) B98466965
theorem B829601 : Blo 243817 829601 := bstep (se 2 (by rfl) ⟨311100, by rfl⟩ : syracuseStep 829601 = 622201) B622201
theorem B370895 : Blo 243817 370895 := bstep (se 1 (by rfl) ⟨278171, by rfl⟩ : syracuseStep 370895 = 556343) B556343
theorem B1681735 : Blo 243817 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B371015 : Blo 243817 371015 := bstep (se 1 (by rfl) ⟨278261, by rfl⟩ : syracuseStep 371015 = 556523) B556523
theorem B371303 : Blo 243817 371303 := bstep (se 1 (by rfl) ⟨278477, by rfl⟩ : syracuseStep 371303 = 556955) B556955
theorem B928367 : Blo 243817 928367 := bstep (se 1 (by rfl) ⟨696275, by rfl⟩ : syracuseStep 928367 = 1392551) B1392551
theorem B633599 : Blo 243817 633599 := bstep (se 1 (by rfl) ⟨475199, by rfl⟩ : syracuseStep 633599 = 950399) B950399
theorem B2796443 : Blo 243817 2796443 := bstep (se 1 (by rfl) ⟨2097332, by rfl⟩ : syracuseStep 2796443 = 4194665) B4194665
theorem B3157481 : Blo 243817 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B831329 : Blo 243817 831329 := bstep (se 2 (by rfl) ⟨311748, by rfl⟩ : syracuseStep 831329 = 623497) B623497
theorem B700319 : Blo 243817 700319 := bstep (se 1 (by rfl) ⟨525239, by rfl⟩ : syracuseStep 700319 = 1050479) B1050479
theorem B274639 : Blo 243817 274639 := bstep (se 1 (by rfl) ⟨205979, by rfl⟩ : syracuseStep 274639 = 411959) B411959
theorem B700775 : Blo 243817 700775 := bstep (se 1 (by rfl) ⟨525581, by rfl⟩ : syracuseStep 700775 = 1051163) B1051163
theorem B2372075 : Blo 243817 2372075 := bstep (se 1 (by rfl) ⟨1779056, by rfl⟩ : syracuseStep 2372075 = 3558113) B3558113
theorem B12202649 : Blo 243817 12202649 := bstep (se 2 (by rfl) ⟨4575993, by rfl⟩ : syracuseStep 12202649 = 9151987) B9151987
theorem B898231 : Blo 243817 898231 := bstep (se 1 (by rfl) ⟨673673, by rfl⟩ : syracuseStep 898231 = 1347347) B1347347
theorem B243839 : Blo 243817 243839 := bstep (se 1 (by rfl) ⟨182879, by rfl⟩ : syracuseStep 243839 = 365759) B365759
theorem B243935 : Blo 243817 243935 := bstep (se 1 (by rfl) ⟨182951, by rfl⟩ : syracuseStep 243935 = 365903) B365903
theorem B833759 : Blo 243817 833759 := bstep (se 1 (by rfl) ⟨625319, by rfl⟩ : syracuseStep 833759 = 1250639) B1250639
theorem B1390841 : Blo 243817 1390841 := bstep (se 2 (by rfl) ⟨521565, by rfl⟩ : syracuseStep 1390841 = 1043131) B1043131
theorem B243995 : Blo 243817 243995 := bstep (se 1 (by rfl) ⟨182996, by rfl⟩ : syracuseStep 243995 = 365993) B365993
theorem B244031 : Blo 243817 244031 := bstep (se 1 (by rfl) ⟨183023, by rfl⟩ : syracuseStep 244031 = 366047) B366047
theorem B244095 : Blo 243817 244095 := bstep (se 1 (by rfl) ⟨183071, by rfl⟩ : syracuseStep 244095 = 366143) B366143
theorem B309739 : Blo 243817 309739 := bstep (se 1 (by rfl) ⟨232304, by rfl⟩ : syracuseStep 309739 = 464609) B464609
theorem B244415 : Blo 243817 244415 := bstep (se 1 (by rfl) ⟨183311, by rfl⟩ : syracuseStep 244415 = 366623) B366623
theorem B834461 : Blo 243817 834461 := bstep (se 3 (by rfl) ⟨156461, by rfl⟩ : syracuseStep 834461 = 312923) B312923
theorem B244703 : Blo 243817 244703 := bstep (se 1 (by rfl) ⟨183527, by rfl⟩ : syracuseStep 244703 = 367055) B367055
theorem B244763 : Blo 243817 244763 := bstep (se 1 (by rfl) ⟨183572, by rfl⟩ : syracuseStep 244763 = 367145) B367145
theorem B244903 : Blo 243817 244903 := bstep (se 1 (by rfl) ⟨183677, by rfl⟩ : syracuseStep 244903 = 367355) B367355
theorem B244987 : Blo 243817 244987 := bstep (se 1 (by rfl) ⟨183740, by rfl⟩ : syracuseStep 244987 = 367481) B367481
theorem B933227 : Blo 243817 933227 := bstep (se 1 (by rfl) ⟨699920, by rfl⟩ : syracuseStep 933227 = 1399841) B1399841
theorem B277915 : Blo 243817 277915 := bstep (se 1 (by rfl) ⟨208436, by rfl⟩ : syracuseStep 277915 = 416873) B416873
theorem B245487 : Blo 243817 245487 := bstep (se 1 (by rfl) ⟨184115, by rfl⟩ : syracuseStep 245487 = 368231) B368231
theorem B245595 : Blo 243817 245595 := bstep (se 1 (by rfl) ⟨184196, by rfl⟩ : syracuseStep 245595 = 368393) B368393
theorem B311131 : Blo 243817 311131 := bstep (se 1 (by rfl) ⟨233348, by rfl⟩ : syracuseStep 311131 = 466697) B466697
theorem B245743 : Blo 243817 245743 := bstep (se 1 (by rfl) ⟨184307, by rfl⟩ : syracuseStep 245743 = 368615) B368615
theorem B245823 : Blo 243817 245823 := bstep (se 1 (by rfl) ⟨184367, by rfl⟩ : syracuseStep 245823 = 368735) B368735
theorem B278599 : Blo 243817 278599 := bstep (se 1 (by rfl) ⟨208949, by rfl⟩ : syracuseStep 278599 = 417899) B417899
theorem B245863 : Blo 243817 245863 := bstep (se 1 (by rfl) ⟨184397, by rfl⟩ : syracuseStep 245863 = 368795) B368795
theorem B934031 : Blo 243817 934031 := bstep (se 1 (by rfl) ⟨700523, by rfl⟩ : syracuseStep 934031 = 1401047) B1401047
theorem B245919 : Blo 243817 245919 := bstep (se 1 (by rfl) ⟨184439, by rfl⟩ : syracuseStep 245919 = 368879) B368879
theorem B3555515 : Blo 243817 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B278779 : Blo 243817 278779 := bstep (se 1 (by rfl) ⟨209084, by rfl⟩ : syracuseStep 278779 = 418169) B418169
theorem B934199 : Blo 243817 934199 := bstep (se 1 (by rfl) ⟨700649, by rfl⟩ : syracuseStep 934199 = 1401299) B1401299
theorem B246171 : Blo 243817 246171 := bstep (se 1 (by rfl) ⟨184628, by rfl⟩ : syracuseStep 246171 = 369257) B369257
theorem B246175 : Blo 243817 246175 := bstep (se 1 (by rfl) ⟨184631, by rfl⟩ : syracuseStep 246175 = 369263) B369263
theorem B443099 : Blo 243817 443099 := bstep (se 1 (by rfl) ⟨332324, by rfl⟩ : syracuseStep 443099 = 664649) B664649
theorem B246591 : Blo 243817 246591 := bstep (se 1 (by rfl) ⟨184943, by rfl⟩ : syracuseStep 246591 = 369887) B369887
theorem B246751 : Blo 243817 246751 := bstep (se 1 (by rfl) ⟨185063, by rfl⟩ : syracuseStep 246751 = 370127) B370127
theorem B246875 : Blo 243817 246875 := bstep (se 1 (by rfl) ⟨185156, by rfl⟩ : syracuseStep 246875 = 370313) B370313
theorem B246911 : Blo 243817 246911 := bstep (se 1 (by rfl) ⟨185183, by rfl⟩ : syracuseStep 246911 = 370367) B370367
theorem B1688741 : Blo 243817 1688741 := bstep (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) B316639
theorem B247015 : Blo 243817 247015 := bstep (se 1 (by rfl) ⟨185261, by rfl⟩ : syracuseStep 247015 = 370523) B370523
theorem B7128323 : Blo 243817 7128323 := bstep (se 1 (by rfl) ⟨5346242, by rfl⟩ : syracuseStep 7128323 = 10692485) B10692485
theorem B18302219 : Blo 243817 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B902441 : Blo 243817 902441 := bstep (se 2 (by rfl) ⟨338415, by rfl⟩ : syracuseStep 902441 = 676831) B676831
theorem B247271 : Blo 243817 247271 := bstep (se 1 (by rfl) ⟨185453, by rfl⟩ : syracuseStep 247271 = 370907) B370907
theorem B1885673 : Blo 243817 1885673 := bstep (se 2 (by rfl) ⟨707127, by rfl⟩ : syracuseStep 1885673 = 1414255) B1414255
theorem B247451 : Blo 243817 247451 := bstep (se 1 (by rfl) ⟨185588, by rfl⟩ : syracuseStep 247451 = 371177) B371177
theorem B247455 : Blo 243817 247455 := bstep (se 1 (by rfl) ⟨185591, by rfl⟩ : syracuseStep 247455 = 371183) B371183
theorem B247663 : Blo 243817 247663 := bstep (se 1 (by rfl) ⟨185747, by rfl⟩ : syracuseStep 247663 = 371495) B371495
theorem B313247 : Blo 243817 313247 := bstep (se 1 (by rfl) ⟨234935, by rfl⟩ : syracuseStep 313247 = 469871) B469871
theorem B247711 : Blo 243817 247711 := bstep (se 1 (by rfl) ⟨185783, by rfl⟩ : syracuseStep 247711 = 371567) B371567
theorem B21711239 : Blo 243817 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B2345435 : Blo 243817 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B5720539 : Blo 243817 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B412303 : Blo 243817 412303 := bstep (se 1 (by rfl) ⟨309227, by rfl⟩ : syracuseStep 412303 = 618455) B618455
theorem B1329817 : Blo 243817 1329817 := bstep (se 2 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 1329817 = 997363) B997363
theorem B5098729 : Blo 243817 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B2018849 : Blo 243817 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B413255 : Blo 243817 413255 := bstep (se 1 (by rfl) ⟨309941, by rfl⟩ : syracuseStep 413255 = 619883) B619883
theorem B1987523 : Blo 243817 1987523 := bstep (se 1 (by rfl) ⟨1490642, by rfl⟩ : syracuseStep 1987523 = 2981285) B2981285
theorem B414713 : Blo 243817 414713 := bstep (se 2 (by rfl) ⟨155517, by rfl⟩ : syracuseStep 414713 = 311035) B311035
theorem B1332217 : Blo 243817 1332217 := bstep (se 2 (by rfl) ⟨499581, by rfl⟩ : syracuseStep 1332217 = 999163) B999163
theorem B1398383 : Blo 243817 1398383 := bstep (se 1 (by rfl) ⟨1048787, by rfl⟩ : syracuseStep 1398383 = 2097575) B2097575
theorem B4216535 : Blo 243817 4216535 := bstep (se 1 (by rfl) ⟨3162401, by rfl⟩ : syracuseStep 4216535 = 6324803) B6324803
theorem B1857491 : Blo 243817 1857491 := bstep (se 1 (by rfl) ⟨1393118, by rfl⟩ : syracuseStep 1857491 = 2786237) B2786237
theorem B841853 : Blo 243817 841853 := bstep (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) B315695
theorem B2349431 : Blo 243817 2349431 := bstep (se 1 (by rfl) ⟨1762073, by rfl⟩ : syracuseStep 2349431 = 3524147) B3524147
theorem B2120203 : Blo 243817 2120203 := bstep (se 1 (by rfl) ⟨1590152, by rfl⟩ : syracuseStep 2120203 = 3180305) B3180305
theorem B1858463 : Blo 243817 1858463 := bstep (se 1 (by rfl) ⟨1393847, by rfl⟩ : syracuseStep 1858463 = 2787695) B2787695
theorem B1236059 : Blo 243817 1236059 := bstep (se 1 (by rfl) ⟨927044, by rfl⟩ : syracuseStep 1236059 = 1854089) B1854089
theorem B2677967 : Blo 243817 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B2514685 : Blo 243817 2514685 := bstep (se 3 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 2514685 = 943007) B943007
theorem B418027 : Blo 243817 418027 := bstep (se 1 (by rfl) ⟨313520, by rfl⟩ : syracuseStep 418027 = 627041) B627041
theorem B10707551 : Blo 243817 10707551 := bstep (se 1 (by rfl) ⟨8030663, by rfl⟩ : syracuseStep 10707551 = 16061327) B16061327
theorem B1237841 : Blo 243817 1237841 := bstep (se 2 (by rfl) ⟨464190, by rfl⟩ : syracuseStep 1237841 = 928381) B928381
theorem B550079 : Blo 243817 550079 := bstep (se 1 (by rfl) ⟨412559, by rfl⟩ : syracuseStep 550079 = 825119) B825119
theorem B1336823 : Blo 243817 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B550727 : Blo 243817 550727 := bstep (se 1 (by rfl) ⟨413045, by rfl⟩ : syracuseStep 550727 = 826091) B826091
theorem B6285437 : Blo 243817 6285437 := bstep (se 3 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 6285437 = 2357039) B2357039
theorem B551087 : Blo 243817 551087 := bstep (se 1 (by rfl) ⟨413315, by rfl⟩ : syracuseStep 551087 = 826631) B826631
theorem B6351047 : Blo 243817 6351047 := bstep (se 1 (by rfl) ⟨4763285, by rfl⟩ : syracuseStep 6351047 = 9526571) B9526571
theorem B551339 : Blo 243817 551339 := bstep (se 1 (by rfl) ⟨413504, by rfl⟩ : syracuseStep 551339 = 827009) B827009
theorem B682553 : Blo 243817 682553 := bstep (se 2 (by rfl) ⟨255957, by rfl⟩ : syracuseStep 682553 = 511915) B511915
theorem B879265 : Blo 243817 879265 := bstep (se 2 (by rfl) ⟨329724, by rfl⟩ : syracuseStep 879265 = 659449) B659449
theorem B617321 : Blo 243817 617321 := bstep (se 2 (by rfl) ⟨231495, by rfl⟩ : syracuseStep 617321 = 462991) B462991
theorem B1404215 : Blo 243817 1404215 := bstep (se 1 (by rfl) ⟨1053161, by rfl⟩ : syracuseStep 1404215 = 2106323) B2106323
theorem B1043867 : Blo 243817 1043867 := bstep (se 1 (by rfl) ⟨782900, by rfl⟩ : syracuseStep 1043867 = 1565801) B1565801
theorem B1044089 : Blo 243817 1044089 := bstep (se 2 (by rfl) ⟨391533, by rfl⟩ : syracuseStep 1044089 = 783067) B783067
theorem B749675 : Blo 243817 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B1405147 : Blo 243817 1405147 := bstep (se 1 (by rfl) ⟨1053860, by rfl⟩ : syracuseStep 1405147 = 2107721) B2107721
theorem B881065 : Blo 243817 881065 := bstep (se 2 (by rfl) ⟨330399, by rfl⟩ : syracuseStep 881065 = 660799) B660799
theorem B1241729 : Blo 243817 1241729 := bstep (se 2 (by rfl) ⟨465648, by rfl⟩ : syracuseStep 1241729 = 931297) B931297
theorem B554111 : Blo 243817 554111 := bstep (se 1 (by rfl) ⟨415583, by rfl⟩ : syracuseStep 554111 = 831167) B831167
theorem B1406423 : Blo 243817 1406423 := bstep (se 1 (by rfl) ⟨1054817, by rfl⟩ : syracuseStep 1406423 = 2109635) B2109635
theorem B423451 : Blo 243817 423451 := bstep (se 1 (by rfl) ⟨317588, by rfl⟩ : syracuseStep 423451 = 635177) B635177
theorem B554633 : Blo 243817 554633 := bstep (se 2 (by rfl) ⟨207987, by rfl⟩ : syracuseStep 554633 = 415975) B415975
theorem B522139 : Blo 243817 522139 := bstep (se 1 (by rfl) ⟨391604, by rfl⟩ : syracuseStep 522139 = 783209) B783209
theorem B621047 : Blo 243817 621047 := bstep (se 1 (by rfl) ⟨465785, by rfl⟩ : syracuseStep 621047 = 931571) B931571
theorem B1800791 : Blo 243817 1800791 := bstep (se 1 (by rfl) ⟨1350593, by rfl⟩ : syracuseStep 1800791 = 2701187) B2701187
theorem B3570277 : Blo 243817 3570277 := bstep (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) B669427
theorem B3144359 : Blo 243817 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B1243835 : Blo 243817 1243835 := bstep (se 1 (by rfl) ⟨932876, by rfl⟩ : syracuseStep 1243835 = 1865753) B1865753
theorem B785771 : Blo 243817 785771 := bstep (se 1 (by rfl) ⟨589328, by rfl⟩ : syracuseStep 785771 = 1178657) B1178657
theorem B2096513 : Blo 243817 2096513 := bstep (se 2 (by rfl) ⟨786192, by rfl⟩ : syracuseStep 2096513 = 1572385) B1572385
theorem B261787 : Blo 243817 261787 := bstep (se 1 (by rfl) ⟨196340, by rfl⟩ : syracuseStep 261787 = 392681) B392681
theorem B556937 : Blo 243817 556937 := bstep (se 2 (by rfl) ⟨208851, by rfl⟩ : syracuseStep 556937 = 417703) B417703
theorem B622475 : Blo 243817 622475 := bstep (se 1 (by rfl) ⟨466856, by rfl⟩ : syracuseStep 622475 = 933713) B933713
theorem B622687 : Blo 243817 622687 := bstep (se 1 (by rfl) ⟨467015, by rfl⟩ : syracuseStep 622687 = 934031) B934031
theorem B622799 : Blo 243817 622799 := bstep (se 1 (by rfl) ⟨467099, by rfl⟩ : syracuseStep 622799 = 934199) B934199
theorem B1999133 : Blo 243817 1999133 := bstep (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) B749675
theorem B557369 : Blo 243817 557369 := bstep (se 2 (by rfl) ⟨209013, by rfl⟩ : syracuseStep 557369 = 418027) B418027
theorem B295399 : Blo 243817 295399 := bstep (se 1 (by rfl) ⟨221549, by rfl⟩ : syracuseStep 295399 = 443099) B443099
theorem B4653677 : Blo 243817 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B4752215 : Blo 243817 4752215 := bstep (se 1 (by rfl) ⟨3564161, by rfl⟩ : syracuseStep 4752215 = 7128323) B7128323
theorem B624257 : Blo 243817 624257 := bstep (se 2 (by rfl) ⟨234096, by rfl⟩ : syracuseStep 624257 = 468193) B468193
theorem B526171 : Blo 243817 526171 := bstep (se 1 (by rfl) ⟨394628, by rfl⟩ : syracuseStep 526171 = 789257) B789257
theorem B790013 : Blo 243817 790013 := bstep (se 3 (by rfl) ⟨148127, by rfl⟩ : syracuseStep 790013 = 296255) B296255
theorem B1773089 : Blo 243817 1773089 := bstep (se 2 (by rfl) ⟨664908, by rfl⟩ : syracuseStep 1773089 = 1329817) B1329817
theorem B9900755 : Blo 243817 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B824039 : Blo 243817 824039 := bstep (se 1 (by rfl) ⟨618029, by rfl⟩ : syracuseStep 824039 = 1236059) B1236059
theorem B366185 : Blo 243817 366185 := bstep (se 2 (by rfl) ⟨137319, by rfl⟩ : syracuseStep 366185 = 274639) B274639
theorem B1873529 : Blo 243817 1873529 := bstep (se 2 (by rfl) ⟨702573, by rfl⟩ : syracuseStep 1873529 = 1405147) B1405147
theorem B825227 : Blo 243817 825227 := bstep (se 1 (by rfl) ⟨618920, by rfl⟩ : syracuseStep 825227 = 1237841) B1237841
theorem B366719 : Blo 243817 366719 := bstep (se 1 (by rfl) ⟨275039, by rfl⟩ : syracuseStep 366719 = 550079) B550079
theorem B891215 : Blo 243817 891215 := bstep (se 1 (by rfl) ⟨668411, by rfl⟩ : syracuseStep 891215 = 1336823) B1336823
theorem B367151 : Blo 243817 367151 := bstep (se 1 (by rfl) ⟨275363, by rfl⟩ : syracuseStep 367151 = 550727) B550727
theorem B1776289 : Blo 243817 1776289 := bstep (se 2 (by rfl) ⟨666108, by rfl⟩ : syracuseStep 1776289 = 1332217) B1332217
theorem B367391 : Blo 243817 367391 := bstep (se 1 (by rfl) ⟨275543, by rfl⟩ : syracuseStep 367391 = 551087) B551087
theorem B4234031 : Blo 243817 4234031 := bstep (se 1 (by rfl) ⟨3175523, by rfl⟩ : syracuseStep 4234031 = 6351047) B6351047
theorem B367559 : Blo 243817 367559 := bstep (se 1 (by rfl) ⟨275669, by rfl⟩ : syracuseStep 367559 = 551339) B551339
theorem B2366729 : Blo 243817 2366729 := bstep (se 2 (by rfl) ⟨887523, by rfl⟩ : syracuseStep 2366729 = 1775047) B1775047
theorem B695911 : Blo 243817 695911 := bstep (se 1 (by rfl) ⟨521933, by rfl⟩ : syracuseStep 695911 = 1043867) B1043867
theorem B2104987 : Blo 243817 2104987 := bstep (se 1 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 2104987 = 3157481) B3157481
theorem B696059 : Blo 243817 696059 := bstep (se 1 (by rfl) ⟨522044, by rfl⟩ : syracuseStep 696059 = 1044089) B1044089
theorem B696185 : Blo 243817 696185 := bstep (se 2 (by rfl) ⟨261069, by rfl⟩ : syracuseStep 696185 = 522139) B522139
theorem B2105261 : Blo 243817 2105261 := bstep (se 3 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 2105261 = 789473) B789473
theorem B466879 : Blo 243817 466879 := bstep (se 1 (by rfl) ⟨350159, by rfl⟩ : syracuseStep 466879 = 700319) B700319
theorem B467183 : Blo 243817 467183 := bstep (se 1 (by rfl) ⟨350387, by rfl⟩ : syracuseStep 467183 = 700775) B700775
theorem B1581383 : Blo 243817 1581383 := bstep (se 1 (by rfl) ⟨1186037, by rfl⟩ : syracuseStep 1581383 = 2372075) B2372075
theorem B827819 : Blo 243817 827819 := bstep (se 1 (by rfl) ⟨620864, by rfl⟩ : syracuseStep 827819 = 1241729) B1241729
theorem B8135099 : Blo 243817 8135099 := bstep (se 1 (by rfl) ⟨6101324, by rfl⟩ : syracuseStep 8135099 = 12202649) B12202649
theorem B2826937 : Blo 243817 2826937 := bstep (se 2 (by rfl) ⟨1060101, by rfl⟩ : syracuseStep 2826937 = 2120203) B2120203
theorem B369407 : Blo 243817 369407 := bstep (se 1 (by rfl) ⟨277055, by rfl⟩ : syracuseStep 369407 = 554111) B554111
theorem B4760369 : Blo 243817 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B369755 : Blo 243817 369755 := bstep (se 1 (by rfl) ⟨277316, by rfl⟩ : syracuseStep 369755 = 554633) B554633
theorem B5383597 : Blo 243817 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B927227 : Blo 243817 927227 := bstep (se 1 (by rfl) ⟨695420, by rfl⟩ : syracuseStep 927227 = 1390841) B1390841
theorem B829223 : Blo 243817 829223 := bstep (se 1 (by rfl) ⟨621917, by rfl⟩ : syracuseStep 829223 = 1243835) B1243835
theorem B370553 : Blo 243817 370553 := bstep (se 2 (by rfl) ⟨138957, by rfl⟩ : syracuseStep 370553 = 277915) B277915
theorem B3352913 : Blo 243817 3352913 := bstep (se 2 (by rfl) ⟨1257342, by rfl⟩ : syracuseStep 3352913 = 2514685) B2514685
theorem B371291 : Blo 243817 371291 := bstep (se 1 (by rfl) ⟨278468, by rfl⟩ : syracuseStep 371291 = 556937) B556937
theorem B371465 : Blo 243817 371465 := bstep (se 2 (by rfl) ⟨139299, by rfl⟩ : syracuseStep 371465 = 278599) B278599
theorem B2370343 : Blo 243817 2370343 := bstep (se 1 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 2370343 = 3555515) B3555515
theorem B371705 : Blo 243817 371705 := bstep (se 2 (by rfl) ⟨139389, by rfl⟩ : syracuseStep 371705 = 278779) B278779
theorem B1125827 : Blo 243817 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B12201479 : Blo 243817 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B601627 : Blo 243817 601627 := bstep (se 1 (by rfl) ⟨451220, by rfl⟩ : syracuseStep 601627 = 902441) B902441
theorem B1257115 : Blo 243817 1257115 := bstep (se 1 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 1257115 = 1885673) B1885673
theorem B275503 : Blo 243817 275503 := bstep (se 1 (by rfl) ⟨206627, by rfl⟩ : syracuseStep 275503 = 413255) B413255
theorem B2536555 : Blo 243817 2536555 := bstep (se 1 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 2536555 = 3804833) B3804833
theorem B2110697 : Blo 243817 2110697 := bstep (se 2 (by rfl) ⟨791511, by rfl⟩ : syracuseStep 2110697 = 1583023) B1583023
theorem B2242313 : Blo 243817 2242313 := bstep (se 2 (by rfl) ⟨840867, by rfl⟩ : syracuseStep 2242313 = 1681735) B1681735
theorem B1325015 : Blo 243817 1325015 := bstep (se 1 (by rfl) ⟨993761, by rfl⟩ : syracuseStep 1325015 = 1987523) B1987523
theorem B276475 : Blo 243817 276475 := bstep (se 1 (by rfl) ⟨207356, by rfl⟩ : syracuseStep 276475 = 414713) B414713
theorem B244071 : Blo 243817 244071 := bstep (se 1 (by rfl) ⟨183053, by rfl⟩ : syracuseStep 244071 = 366107) B366107
theorem B932255 : Blo 243817 932255 := bstep (se 1 (by rfl) ⟨699191, by rfl⟩ : syracuseStep 932255 = 1398383) B1398383
theorem B244191 : Blo 243817 244191 := bstep (se 1 (by rfl) ⟨183143, by rfl⟩ : syracuseStep 244191 = 366287) B366287
theorem B244351 : Blo 243817 244351 := bstep (se 1 (by rfl) ⟨183263, by rfl⟩ : syracuseStep 244351 = 366527) B366527
theorem B244543 : Blo 243817 244543 := bstep (se 1 (by rfl) ⟨183407, by rfl⟩ : syracuseStep 244543 = 366815) B366815
theorem B244583 : Blo 243817 244583 := bstep (se 1 (by rfl) ⟨183437, by rfl⟩ : syracuseStep 244583 = 366875) B366875
theorem B6798305 : Blo 243817 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B834623 : Blo 243817 834623 := bstep (se 1 (by rfl) ⟨625967, by rfl⟩ : syracuseStep 834623 = 1251935) B1251935
theorem B244863 : Blo 243817 244863 := bstep (se 1 (by rfl) ⟨183647, by rfl⟩ : syracuseStep 244863 = 367295) B367295
theorem B310655 : Blo 243817 310655 := bstep (se 1 (by rfl) ⟨232991, by rfl⟩ : syracuseStep 310655 = 465983) B465983
theorem B1785311 : Blo 243817 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B245231 : Blo 243817 245231 := bstep (se 1 (by rfl) ⟨183923, by rfl⟩ : syracuseStep 245231 = 367847) B367847
theorem B835325 : Blo 243817 835325 := bstep (se 3 (by rfl) ⟨156623, by rfl⟩ : syracuseStep 835325 = 313247) B313247
theorem B835487 : Blo 243817 835487 := bstep (se 1 (by rfl) ⟨626615, by rfl⟩ : syracuseStep 835487 = 1253231) B1253231
theorem B311359 : Blo 243817 311359 := bstep (se 1 (by rfl) ⟨233519, by rfl⟩ : syracuseStep 311359 = 467039) B467039
theorem B245851 : Blo 243817 245851 := bstep (se 1 (by rfl) ⟨184388, by rfl⟩ : syracuseStep 245851 = 368777) B368777
theorem B2244941 : Blo 243817 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B246655 : Blo 243817 246655 := bstep (se 1 (by rfl) ⟨184991, by rfl⟩ : syracuseStep 246655 = 369983) B369983
theorem B246687 : Blo 243817 246687 := bstep (se 1 (by rfl) ⟨185015, by rfl⟩ : syracuseStep 246687 = 370031) B370031
theorem B246767 : Blo 243817 246767 := bstep (se 1 (by rfl) ⟨185075, by rfl⟩ : syracuseStep 246767 = 370151) B370151
theorem B246855 : Blo 243817 246855 := bstep (se 1 (by rfl) ⟨185141, by rfl⟩ : syracuseStep 246855 = 370283) B370283
theorem B246887 : Blo 243817 246887 := bstep (se 1 (by rfl) ⟨185165, by rfl⟩ : syracuseStep 246887 = 370331) B370331
theorem B247167 : Blo 243817 247167 := bstep (se 1 (by rfl) ⟨185375, by rfl⟩ : syracuseStep 247167 = 370751) B370751
theorem B43763095 : Blo 243817 43763095 := bstep (se 1 (by rfl) ⟨32822321, by rfl⟩ : syracuseStep 43763095 = 65644643) B65644643
theorem B247263 : Blo 243817 247263 := bstep (se 1 (by rfl) ⟨185447, by rfl⟩ : syracuseStep 247263 = 370895) B370895
theorem B1820141 : Blo 243817 1820141 := bstep (se 3 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 1820141 = 682553) B682553
theorem B247343 : Blo 243817 247343 := bstep (se 1 (by rfl) ⟨185507, by rfl⟩ : syracuseStep 247343 = 371015) B371015
theorem B1197641 : Blo 243817 1197641 := bstep (se 2 (by rfl) ⟨449115, by rfl⟩ : syracuseStep 1197641 = 898231) B898231
theorem B247535 : Blo 243817 247535 := bstep (se 1 (by rfl) ⟨185651, by rfl⟩ : syracuseStep 247535 = 371303) B371303
theorem B411547 : Blo 243817 411547 := bstep (se 1 (by rfl) ⟨308660, by rfl⟩ : syracuseStep 411547 = 617321) B617321
theorem B936143 : Blo 243817 936143 := bstep (se 1 (by rfl) ⟨702107, by rfl⟩ : syracuseStep 936143 = 1404215) B1404215
theorem B412985 : Blo 243817 412985 := bstep (se 2 (by rfl) ⟨154869, by rfl⟩ : syracuseStep 412985 = 309739) B309739
theorem B937615 : Blo 243817 937615 := bstep (se 1 (by rfl) ⟨703211, by rfl⟩ : syracuseStep 937615 = 1406423) B1406423
theorem B414031 : Blo 243817 414031 := bstep (se 1 (by rfl) ⟨310523, by rfl⟩ : syracuseStep 414031 = 621047) B621047
theorem B1200527 : Blo 243817 1200527 := bstep (se 1 (by rfl) ⟨900395, by rfl⟩ : syracuseStep 1200527 = 1800791) B1800791
theorem B349049 : Blo 243817 349049 := bstep (se 2 (by rfl) ⟨130893, by rfl⟩ : syracuseStep 349049 = 261787) B261787
theorem B1397675 : Blo 243817 1397675 := bstep (se 1 (by rfl) ⟨1048256, by rfl⟩ : syracuseStep 1397675 = 2096513) B2096513
theorem B414841 : Blo 243817 414841 := bstep (se 2 (by rfl) ⟨155565, by rfl⟩ : syracuseStep 414841 = 311131) B311131
theorem B414983 : Blo 243817 414983 := bstep (se 1 (by rfl) ⟨311237, by rfl⟩ : syracuseStep 414983 = 622475) B622475
theorem B14474159 : Blo 243817 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B1563623 : Blo 243817 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B548819 : Blo 243817 548819 := bstep (se 1 (by rfl) ⟨411614, by rfl⟩ : syracuseStep 548819 = 823229) B823229
theorem B548927 : Blo 243817 548927 := bstep (se 1 (by rfl) ⟨411695, by rfl⟩ : syracuseStep 548927 = 823391) B823391
theorem B1794251 : Blo 243817 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B7627385 : Blo 243817 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B549737 : Blo 243817 549737 := bstep (se 2 (by rfl) ⟨206151, by rfl⟩ : syracuseStep 549737 = 412303) B412303
theorem B1172353 : Blo 243817 1172353 := bstep (se 2 (by rfl) ⟨439632, by rfl⟩ : syracuseStep 1172353 = 879265) B879265
theorem B2811023 : Blo 243817 2811023 := bstep (se 1 (by rfl) ⟨2108267, by rfl⟩ : syracuseStep 2811023 = 4216535) B4216535
theorem B1238327 : Blo 243817 1238327 := bstep (se 1 (by rfl) ⟨928745, by rfl⟩ : syracuseStep 1238327 = 1857491) B1857491
theorem B1566287 : Blo 243817 1566287 := bstep (se 1 (by rfl) ⟨1174715, by rfl⟩ : syracuseStep 1566287 = 2349431) B2349431
theorem B1009529 : Blo 243817 1009529 := bstep (se 2 (by rfl) ⟨378573, by rfl⟩ : syracuseStep 1009529 = 757147) B757147
theorem B550799 : Blo 243817 550799 := bstep (se 1 (by rfl) ⟨413099, by rfl⟩ : syracuseStep 550799 = 826199) B826199
theorem B1238975 : Blo 243817 1238975 := bstep (se 1 (by rfl) ⟨929231, by rfl⟩ : syracuseStep 1238975 = 1858463) B1858463
theorem B550907 : Blo 243817 550907 := bstep (se 1 (by rfl) ⟨413180, by rfl⟩ : syracuseStep 550907 = 826361) B826361
theorem B551231 : Blo 243817 551231 := bstep (se 1 (by rfl) ⟨413423, by rfl⟩ : syracuseStep 551231 = 826847) B826847
theorem B551519 : Blo 243817 551519 := bstep (se 1 (by rfl) ⟨413639, by rfl⟩ : syracuseStep 551519 = 827279) B827279
theorem B551591 : Blo 243817 551591 := bstep (se 1 (by rfl) ⟨413693, by rfl⟩ : syracuseStep 551591 = 827387) B827387
theorem B551663 : Blo 243817 551663 := bstep (se 1 (by rfl) ⟨413747, by rfl⟩ : syracuseStep 551663 = 827495) B827495
theorem B1403963 : Blo 243817 1403963 := bstep (se 1 (by rfl) ⟨1052972, by rfl⟩ : syracuseStep 1403963 = 2105945) B2105945
theorem B7138367 : Blo 243817 7138367 := bstep (se 1 (by rfl) ⟨5353775, by rfl⟩ : syracuseStep 7138367 = 10707551) B10707551
theorem B1174753 : Blo 243817 1174753 := bstep (se 2 (by rfl) ⟨440532, by rfl⟩ : syracuseStep 1174753 = 881065) B881065
theorem B9268465 : Blo 243817 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B552239 : Blo 243817 552239 := bstep (se 1 (by rfl) ⟨414179, by rfl⟩ : syracuseStep 552239 = 828359) B828359
theorem B618475 : Blo 243817 618475 := bstep (se 1 (by rfl) ⟨463856, by rfl⟩ : syracuseStep 618475 = 927713) B927713
theorem B4190291 : Blo 243817 4190291 := bstep (se 1 (by rfl) ⟨3142718, by rfl⟩ : syracuseStep 4190291 = 6285437) B6285437
theorem B553067 : Blo 243817 553067 := bstep (se 1 (by rfl) ⟨414800, by rfl⟩ : syracuseStep 553067 = 829601) B829601
theorem B618911 : Blo 243817 618911 := bstep (se 1 (by rfl) ⟨464183, by rfl⟩ : syracuseStep 618911 = 928367) B928367
theorem B422399 : Blo 243817 422399 := bstep (se 1 (by rfl) ⟨316799, by rfl⟩ : syracuseStep 422399 = 633599) B633599
theorem B1864295 : Blo 243817 1864295 := bstep (se 1 (by rfl) ⟨1398221, by rfl⟩ : syracuseStep 1864295 = 2796443) B2796443
theorem B554219 : Blo 243817 554219 := bstep (se 1 (by rfl) ⟨415664, by rfl⟩ : syracuseStep 554219 = 831329) B831329
theorem B2258405 : Blo 243817 2258405 := bstep (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) B423451
theorem B555839 : Blo 243817 555839 := bstep (se 1 (by rfl) ⟨416879, by rfl⟩ : syracuseStep 555839 = 833759) B833759
theorem B2096239 : Blo 243817 2096239 := bstep (se 1 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 2096239 = 3144359) B3144359
theorem B556307 : Blo 243817 556307 := bstep (se 1 (by rfl) ⟨417230, by rfl⟩ : syracuseStep 556307 = 834461) B834461
theorem B523847 : Blo 243817 523847 := bstep (se 1 (by rfl) ⟨392885, by rfl⟩ : syracuseStep 523847 = 785771) B785771
theorem B622151 : Blo 243817 622151 := bstep (se 1 (by rfl) ⟨466613, by rfl⟩ : syracuseStep 622151 = 933227) B933227
theorem B393865 : Blo 243817 393865 := bstep (se 2 (by rfl) ⟨147699, by rfl⟩ : syracuseStep 393865 = 295399) B295399
theorem B3769249 : Blo 243817 3769249 := bstep (se 2 (by rfl) ⟨1413468, by rfl⟩ : syracuseStep 3769249 = 2826937) B2826937
theorem B1213427 : Blo 243817 1213427 := bstep (se 1 (by rfl) ⟨910070, by rfl⟩ : syracuseStep 1213427 = 1820141) B1820141
theorem B624095 : Blo 243817 624095 := bstep (se 1 (by rfl) ⟨468071, by rfl⟩ : syracuseStep 624095 = 936143) B936143
theorem B7178129 : Blo 243817 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B526675 : Blo 243817 526675 := bstep (se 1 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 526675 = 790013) B790013
theorem B1182059 : Blo 243817 1182059 := bstep (se 1 (by rfl) ⟨886544, by rfl⟩ : syracuseStep 1182059 = 1773089) B1773089
theorem B1249019 : Blo 243817 1249019 := bstep (se 1 (by rfl) ⟨936764, by rfl⟩ : syracuseStep 1249019 = 1873529) B1873529
theorem B594143 : Blo 243817 594143 := bstep (se 1 (by rfl) ⟨445607, by rfl⟩ : syracuseStep 594143 = 891215) B891215
theorem B12357953 : Blo 243817 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B2822687 : Blo 243817 2822687 := bstep (se 1 (by rfl) ⟨2117015, by rfl⟩ : syracuseStep 2822687 = 4234031) B4234031
theorem B1577819 : Blo 243817 1577819 := bstep (se 1 (by rfl) ⟨1183364, by rfl⟩ : syracuseStep 1577819 = 2366729) B2366729
theorem B1250153 : Blo 243817 1250153 := bstep (se 2 (by rfl) ⟨468807, by rfl⟩ : syracuseStep 1250153 = 937615) B937615
theorem B1676153 : Blo 243817 1676153 := bstep (se 2 (by rfl) ⟨628557, by rfl⟩ : syracuseStep 1676153 = 1257115) B1257115
theorem B464039 : Blo 243817 464039 := bstep (se 1 (by rfl) ⟨348029, by rfl⟩ : syracuseStep 464039 = 696059) B696059
theorem B464123 : Blo 243817 464123 := bstep (se 1 (by rfl) ⟨348092, by rfl⟩ : syracuseStep 464123 = 696185) B696185
theorem B365879 : Blo 243817 365879 := bstep (se 1 (by rfl) ⟨274409, by rfl⟩ : syracuseStep 365879 = 548819) B548819
theorem B824633 : Blo 243817 824633 := bstep (se 2 (by rfl) ⟨309237, by rfl⟩ : syracuseStep 824633 = 618475) B618475
theorem B365951 : Blo 243817 365951 := bstep (se 1 (by rfl) ⟨274463, by rfl⟩ : syracuseStep 365951 = 548927) B548927
theorem B1054255 : Blo 243817 1054255 := bstep (se 1 (by rfl) ⟨790691, by rfl⟩ : syracuseStep 1054255 = 1581383) B1581383
theorem B366491 : Blo 243817 366491 := bstep (se 1 (by rfl) ⟨274868, by rfl⟩ : syracuseStep 366491 = 549737) B549737
theorem B1874015 : Blo 243817 1874015 := bstep (se 1 (by rfl) ⟨1405511, by rfl⟩ : syracuseStep 1874015 = 2811023) B2811023
theorem B825551 : Blo 243817 825551 := bstep (se 1 (by rfl) ⟨619163, by rfl⟩ : syracuseStep 825551 = 1238327) B1238327
theorem B367199 : Blo 243817 367199 := bstep (se 1 (by rfl) ⟨275399, by rfl⟩ : syracuseStep 367199 = 550799) B550799
theorem B825983 : Blo 243817 825983 := bstep (se 1 (by rfl) ⟨619487, by rfl⟩ : syracuseStep 825983 = 1238975) B1238975
theorem B367271 : Blo 243817 367271 := bstep (se 1 (by rfl) ⟨275453, by rfl⟩ : syracuseStep 367271 = 550907) B550907
theorem B367337 : Blo 243817 367337 := bstep (se 2 (by rfl) ⟨137751, by rfl⟩ : syracuseStep 367337 = 275503) B275503
theorem B3382073 : Blo 243817 3382073 := bstep (se 2 (by rfl) ⟨1268277, by rfl⟩ : syracuseStep 3382073 = 2536555) B2536555
theorem B367487 : Blo 243817 367487 := bstep (se 1 (by rfl) ⟨275615, by rfl⟩ : syracuseStep 367487 = 551231) B551231
theorem B2235275 : Blo 243817 2235275 := bstep (se 1 (by rfl) ⟨1676456, by rfl⟩ : syracuseStep 2235275 = 3352913) B3352913
theorem B367679 : Blo 243817 367679 := bstep (se 1 (by rfl) ⟨275759, by rfl⟩ : syracuseStep 367679 = 551519) B551519
theorem B367727 : Blo 243817 367727 := bstep (se 1 (by rfl) ⟨275795, by rfl⟩ : syracuseStep 367727 = 551591) B551591
theorem B367775 : Blo 243817 367775 := bstep (se 1 (by rfl) ⟨275831, by rfl⟩ : syracuseStep 367775 = 551663) B551663
theorem B4758911 : Blo 243817 4758911 := bstep (se 1 (by rfl) ⟨3569183, by rfl⟩ : syracuseStep 4758911 = 7138367) B7138367
theorem B368159 : Blo 243817 368159 := bstep (se 1 (by rfl) ⟨276119, by rfl⟩ : syracuseStep 368159 = 552239) B552239
theorem B8134319 : Blo 243817 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B368633 : Blo 243817 368633 := bstep (se 2 (by rfl) ⟨138237, by rfl⟩ : syracuseStep 368633 = 276475) B276475
theorem B2793527 : Blo 243817 2793527 := bstep (se 1 (by rfl) ⟨2095145, by rfl⟩ : syracuseStep 2793527 = 4190291) B4190291
theorem B368711 : Blo 243817 368711 := bstep (se 1 (by rfl) ⟨276533, by rfl⟩ : syracuseStep 368711 = 553067) B553067
theorem B369479 : Blo 243817 369479 := bstep (se 1 (by rfl) ⟨277109, by rfl⟩ : syracuseStep 369479 = 554219) B554219
theorem B2368385 : Blo 243817 2368385 := bstep (se 2 (by rfl) ⟨888144, by rfl⟩ : syracuseStep 2368385 = 1776289) B1776289
theorem B828413 : Blo 243817 828413 := bstep (se 3 (by rfl) ⟨155327, by rfl⟩ : syracuseStep 828413 = 310655) B310655
theorem B2794985 : Blo 243817 2794985 := bstep (se 2 (by rfl) ⟨1048119, by rfl⟩ : syracuseStep 2794985 = 2096239) B2096239
theorem B370559 : Blo 243817 370559 := bstep (se 1 (by rfl) ⟨277919, by rfl⟩ : syracuseStep 370559 = 555839) B555839
theorem B4532203 : Blo 243817 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B927881 : Blo 243817 927881 := bstep (se 2 (by rfl) ⟨347955, by rfl⟩ : syracuseStep 927881 = 695911) B695911
theorem B370871 : Blo 243817 370871 := bstep (se 1 (by rfl) ⟨278153, by rfl⟩ : syracuseStep 370871 = 556307) B556307
theorem B1190207 : Blo 243817 1190207 := bstep (se 1 (by rfl) ⟨892655, by rfl⟩ : syracuseStep 1190207 = 1785311) B1785311
theorem B830249 : Blo 243817 830249 := bstep (se 2 (by rfl) ⟨311343, by rfl⟩ : syracuseStep 830249 = 622687) B622687
theorem B371579 : Blo 243817 371579 := bstep (se 1 (by rfl) ⟨278684, by rfl⟩ : syracuseStep 371579 = 557369) B557369
theorem B798427 : Blo 243817 798427 := bstep (se 1 (by rfl) ⟨598820, by rfl⟩ : syracuseStep 798427 = 1197641) B1197641
theorem B275323 : Blo 243817 275323 := bstep (se 1 (by rfl) ⟨206492, by rfl⟩ : syracuseStep 275323 = 412985) B412985
theorem B930797 : Blo 243817 930797 := bstep (se 3 (by rfl) ⟨174524, by rfl⟩ : syracuseStep 930797 = 349049) B349049
theorem B701561 : Blo 243817 701561 := bstep (se 2 (by rfl) ⟨263085, by rfl⟩ : syracuseStep 701561 = 526171) B526171
theorem B800351 : Blo 243817 800351 := bstep (se 1 (by rfl) ⟨600263, by rfl⟩ : syracuseStep 800351 = 1200527) B1200527
theorem B6600503 : Blo 243817 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B931783 : Blo 243817 931783 := bstep (se 1 (by rfl) ⟨698837, by rfl⟩ : syracuseStep 931783 = 1397675) B1397675
theorem B276655 : Blo 243817 276655 := bstep (se 1 (by rfl) ⟨207491, by rfl⟩ : syracuseStep 276655 = 414983) B414983
theorem B3160457 : Blo 243817 3160457 := bstep (se 2 (by rfl) ⟨1185171, by rfl⟩ : syracuseStep 3160457 = 2370343) B2370343
theorem B244123 : Blo 243817 244123 := bstep (se 1 (by rfl) ⟨183092, by rfl⟩ : syracuseStep 244123 = 366185) B366185
theorem B244479 : Blo 243817 244479 := bstep (se 1 (by rfl) ⟨183359, by rfl⟩ : syracuseStep 244479 = 366719) B366719
theorem B244767 : Blo 243817 244767 := bstep (se 1 (by rfl) ⟨183575, by rfl⟩ : syracuseStep 244767 = 367151) B367151
theorem B244927 : Blo 243817 244927 := bstep (se 1 (by rfl) ⟨183695, by rfl⟩ : syracuseStep 244927 = 367391) B367391
theorem B9649439 : Blo 243817 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B245039 : Blo 243817 245039 := bstep (se 1 (by rfl) ⟨183779, by rfl⟩ : syracuseStep 245039 = 367559) B367559
theorem B802169 : Blo 243817 802169 := bstep (se 2 (by rfl) ⟨300813, by rfl⟩ : syracuseStep 802169 = 601627) B601627
theorem B1196167 : Blo 243817 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B311455 : Blo 243817 311455 := bstep (se 1 (by rfl) ⟨233591, by rfl⟩ : syracuseStep 311455 = 467183) B467183
theorem B5423399 : Blo 243817 5423399 := bstep (se 1 (by rfl) ⟨4067549, by rfl⟩ : syracuseStep 5423399 = 8135099) B8135099
theorem B246271 : Blo 243817 246271 := bstep (se 1 (by rfl) ⟨184703, by rfl⟩ : syracuseStep 246271 = 369407) B369407
theorem B246503 : Blo 243817 246503 := bstep (se 1 (by rfl) ⟨184877, by rfl⟩ : syracuseStep 246503 = 369755) B369755
theorem B673019 : Blo 243817 673019 := bstep (se 1 (by rfl) ⟨504764, by rfl⟩ : syracuseStep 673019 = 1009529) B1009529
theorem B247035 : Blo 243817 247035 := bstep (se 1 (by rfl) ⟨185276, by rfl⟩ : syracuseStep 247035 = 370553) B370553
theorem B247527 : Blo 243817 247527 := bstep (se 1 (by rfl) ⟨185645, by rfl⟩ : syracuseStep 247527 = 371291) B371291
theorem B247643 : Blo 243817 247643 := bstep (se 1 (by rfl) ⟨185732, by rfl⟩ : syracuseStep 247643 = 371465) B371465
theorem B247803 : Blo 243817 247803 := bstep (se 1 (by rfl) ⟨185852, by rfl⟩ : syracuseStep 247803 = 371705) B371705
theorem B935975 : Blo 243817 935975 := bstep (se 1 (by rfl) ⟨701981, by rfl⟩ : syracuseStep 935975 = 1403963) B1403963
theorem B412607 : Blo 243817 412607 := bstep (se 1 (by rfl) ⟨309455, by rfl⟩ : syracuseStep 412607 = 618911) B618911
theorem B281599 : Blo 243817 281599 := bstep (se 1 (by rfl) ⟨211199, by rfl⟩ : syracuseStep 281599 = 422399) B422399
theorem B1494875 : Blo 243817 1494875 := bstep (se 1 (by rfl) ⟨1121156, by rfl⟩ : syracuseStep 1494875 = 2242313) B2242313
theorem B1396925 : Blo 243817 1396925 := bstep (se 3 (by rfl) ⟨261923, by rfl⟩ : syracuseStep 1396925 = 523847) B523847
theorem B2806649 : Blo 243817 2806649 := bstep (se 2 (by rfl) ⟨1052493, by rfl⟩ : syracuseStep 2806649 = 2104987) B2104987
theorem B414767 : Blo 243817 414767 := bstep (se 1 (by rfl) ⟨311075, by rfl⟩ : syracuseStep 414767 = 622151) B622151
theorem B415145 : Blo 243817 415145 := bstep (se 2 (by rfl) ⟨155679, by rfl⟩ : syracuseStep 415145 = 311359) B311359
theorem B415199 : Blo 243817 415199 := bstep (se 1 (by rfl) ⟨311399, by rfl⟩ : syracuseStep 415199 = 622799) B622799
theorem B1332755 : Blo 243817 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B1496627 : Blo 243817 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B3168143 : Blo 243817 3168143 := bstep (se 1 (by rfl) ⟨2376107, by rfl⟩ : syracuseStep 3168143 = 4752215) B4752215
theorem B416171 : Blo 243817 416171 := bstep (se 1 (by rfl) ⟨312128, by rfl⟩ : syracuseStep 416171 = 624257) B624257
theorem B1563137 : Blo 243817 1563137 := bstep (se 2 (by rfl) ⟨586176, by rfl⟩ : syracuseStep 1563137 = 1172353) B1172353
theorem B12409805 : Blo 243817 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B20339693 : Blo 243817 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B58350793 : Blo 243817 58350793 := bstep (se 2 (by rfl) ⟨21881547, by rfl⟩ : syracuseStep 58350793 = 43763095) B43763095
theorem B548729 : Blo 243817 548729 := bstep (se 2 (by rfl) ⟨205773, by rfl⟩ : syracuseStep 548729 = 411547) B411547
theorem B549359 : Blo 243817 549359 := bstep (se 1 (by rfl) ⟨412019, by rfl⟩ : syracuseStep 549359 = 824039) B824039
theorem B550151 : Blo 243817 550151 := bstep (se 1 (by rfl) ⟨412613, by rfl⟩ : syracuseStep 550151 = 825227) B825227
theorem B1566337 : Blo 243817 1566337 := bstep (se 2 (by rfl) ⟨587376, by rfl⟩ : syracuseStep 1566337 = 1174753) B1174753
theorem B1042415 : Blo 243817 1042415 := bstep (se 1 (by rfl) ⟨781811, by rfl⟩ : syracuseStep 1042415 = 1563623) B1563623
theorem B1403507 : Blo 243817 1403507 := bstep (se 1 (by rfl) ⟨1052630, by rfl⟩ : syracuseStep 1403507 = 2105261) B2105261
theorem B551879 : Blo 243817 551879 := bstep (se 1 (by rfl) ⟨413909, by rfl⟩ : syracuseStep 551879 = 827819) B827819
theorem B552041 : Blo 243817 552041 := bstep (se 2 (by rfl) ⟨207015, by rfl⟩ : syracuseStep 552041 = 414031) B414031
theorem B3173579 : Blo 243817 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B618151 : Blo 243817 618151 := bstep (se 1 (by rfl) ⟨463613, by rfl⟩ : syracuseStep 618151 = 927227) B927227
theorem B1044191 : Blo 243817 1044191 := bstep (se 1 (by rfl) ⟨783143, by rfl⟩ : syracuseStep 1044191 = 1566287) B1566287
theorem B552815 : Blo 243817 552815 := bstep (se 1 (by rfl) ⟨414611, by rfl⟩ : syracuseStep 552815 = 829223) B829223
theorem B553121 : Blo 243817 553121 := bstep (se 2 (by rfl) ⟨207420, by rfl⟩ : syracuseStep 553121 = 414841) B414841
theorem B750551 : Blo 243817 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B1242863 : Blo 243817 1242863 := bstep (se 1 (by rfl) ⟨932147, by rfl⟩ : syracuseStep 1242863 = 1864295) B1864295
theorem B1407131 : Blo 243817 1407131 := bstep (se 1 (by rfl) ⟨1055348, by rfl⟩ : syracuseStep 1407131 = 2110697) B2110697
theorem B1505603 : Blo 243817 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B883343 : Blo 243817 883343 := bstep (se 1 (by rfl) ⟨662507, by rfl⟩ : syracuseStep 883343 = 1325015) B1325015
theorem B621503 : Blo 243817 621503 := bstep (se 1 (by rfl) ⟨466127, by rfl⟩ : syracuseStep 621503 = 932255) B932255
theorem B556415 : Blo 243817 556415 := bstep (se 1 (by rfl) ⟨417311, by rfl⟩ : syracuseStep 556415 = 834623) B834623
theorem B556883 : Blo 243817 556883 := bstep (se 1 (by rfl) ⟨417662, by rfl⟩ : syracuseStep 556883 = 835325) B835325
theorem B622505 : Blo 243817 622505 := bstep (se 2 (by rfl) ⟨233439, by rfl⟩ : syracuseStep 622505 = 466879) B466879
theorem B556991 : Blo 243817 556991 := bstep (se 1 (by rfl) ⟨417743, by rfl⟩ : syracuseStep 556991 = 835487) B835487
theorem B4785419 : Blo 243817 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B623983 : Blo 243817 623983 := bstep (se 1 (by rfl) ⟨467987, by rfl⟩ : syracuseStep 623983 = 935975) B935975
theorem B788039 : Blo 243817 788039 := bstep (se 1 (by rfl) ⟨591029, by rfl⟩ : syracuseStep 788039 = 1182059) B1182059
theorem B396095 : Blo 243817 396095 := bstep (se 1 (by rfl) ⟨297071, by rfl⟩ : syracuseStep 396095 = 594143) B594143
theorem B1051879 : Blo 243817 1051879 := bstep (se 1 (by rfl) ⟨788909, by rfl⟩ : syracuseStep 1051879 = 1577819) B1577819
theorem B1117435 : Blo 243817 1117435 := bstep (se 1 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 1117435 = 1676153) B1676153
theorem B1871099 : Blo 243817 1871099 := bstep (se 1 (by rfl) ⟨1403324, by rfl⟩ : syracuseStep 1871099 = 2806649) B2806649
theorem B2100613 : Blo 243817 2100613 := bstep (se 4 (by rfl) ⟨196932, by rfl⟩ : syracuseStep 2100613 = 393865) B393865
theorem B888503 : Blo 243817 888503 := bstep (se 1 (by rfl) ⟨666377, by rfl⟩ : syracuseStep 888503 = 1332755) B1332755
theorem B1249343 : Blo 243817 1249343 := bstep (se 1 (by rfl) ⟨937007, by rfl⟩ : syracuseStep 1249343 = 1874015) B1874015
theorem B824201 : Blo 243817 824201 := bstep (se 2 (by rfl) ⟨309075, by rfl⟩ : syracuseStep 824201 = 618151) B618151
theorem B365819 : Blo 243817 365819 := bstep (se 1 (by rfl) ⟨274364, by rfl⟩ : syracuseStep 365819 = 548729) B548729
theorem B366239 : Blo 243817 366239 := bstep (se 1 (by rfl) ⟨274679, by rfl⟩ : syracuseStep 366239 = 549359) B549359
theorem B1578923 : Blo 243817 1578923 := bstep (se 1 (by rfl) ⟨1184192, by rfl⟩ : syracuseStep 1578923 = 2368385) B2368385
theorem B366767 : Blo 243817 366767 := bstep (se 1 (by rfl) ⟨275075, by rfl⟩ : syracuseStep 366767 = 550151) B550151
theorem B367097 : Blo 243817 367097 := bstep (se 2 (by rfl) ⟨137661, by rfl⟩ : syracuseStep 367097 = 275323) B275323
theorem B694943 : Blo 243817 694943 := bstep (se 1 (by rfl) ⟨521207, by rfl⟩ : syracuseStep 694943 = 1042415) B1042415
theorem B793471 : Blo 243817 793471 := bstep (se 1 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 793471 = 1190207) B1190207
theorem B367919 : Blo 243817 367919 := bstep (se 1 (by rfl) ⟨275939, by rfl⟩ : syracuseStep 367919 = 551879) B551879
theorem B368027 : Blo 243817 368027 := bstep (se 1 (by rfl) ⟨276020, by rfl⟩ : syracuseStep 368027 = 552041) B552041
theorem B696127 : Blo 243817 696127 := bstep (se 1 (by rfl) ⟨522095, by rfl⟩ : syracuseStep 696127 = 1044191) B1044191
theorem B368543 : Blo 243817 368543 := bstep (se 1 (by rfl) ⟨276407, by rfl⟩ : syracuseStep 368543 = 552815) B552815
theorem B368747 : Blo 243817 368747 := bstep (se 1 (by rfl) ⟨276560, by rfl⟩ : syracuseStep 368747 = 553121) B553121
theorem B368873 : Blo 243817 368873 := bstep (se 2 (by rfl) ⟨138327, by rfl⟩ : syracuseStep 368873 = 276655) B276655
theorem B467707 : Blo 243817 467707 := bstep (se 1 (by rfl) ⟨350780, by rfl⟩ : syracuseStep 467707 = 701561) B701561
theorem B533567 : Blo 243817 533567 := bstep (se 1 (by rfl) ⟨400175, by rfl⟩ : syracuseStep 533567 = 800351) B800351
theorem B828575 : Blo 243817 828575 := bstep (se 1 (by rfl) ⟨621431, by rfl⟩ : syracuseStep 828575 = 1242863) B1242863
theorem B4400335 : Blo 243817 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B2106971 : Blo 243817 2106971 := bstep (se 1 (by rfl) ⟨1580228, by rfl⟩ : syracuseStep 2106971 = 3160457) B3160457
theorem B77801057 : Blo 243817 77801057 := bstep (se 2 (by rfl) ⟨29175396, by rfl⟩ : syracuseStep 77801057 = 58350793) B58350793
theorem B6432959 : Blo 243817 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B8005877 : Blo 243817 8005877 := bstep (se 5 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 8005877 = 750551) B750551
theorem B534779 : Blo 243817 534779 := bstep (se 1 (by rfl) ⟨401084, by rfl⟩ : syracuseStep 534779 = 802169) B802169
theorem B370943 : Blo 243817 370943 := bstep (se 1 (by rfl) ⟨278207, by rfl⟩ : syracuseStep 370943 = 556415) B556415
theorem B371255 : Blo 243817 371255 := bstep (se 1 (by rfl) ⟨278441, by rfl⟩ : syracuseStep 371255 = 556883) B556883
theorem B371327 : Blo 243817 371327 := bstep (se 1 (by rfl) ⟨278495, by rfl⟩ : syracuseStep 371327 = 556991) B556991
theorem B3615599 : Blo 243817 3615599 := bstep (se 1 (by rfl) ⟨2711699, by rfl⟩ : syracuseStep 3615599 = 5423399) B5423399
theorem B5025665 : Blo 243817 5025665 := bstep (se 2 (by rfl) ⟨1884624, by rfl⟩ : syracuseStep 5025665 = 3769249) B3769249
theorem B275071 : Blo 243817 275071 := bstep (se 1 (by rfl) ⟨206303, by rfl⟩ : syracuseStep 275071 = 412607) B412607
theorem B832679 : Blo 243817 832679 := bstep (se 1 (by rfl) ⟨624509, by rfl⟩ : syracuseStep 832679 = 1249019) B1249019
theorem B6042937 : Blo 243817 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B931283 : Blo 243817 931283 := bstep (se 1 (by rfl) ⟨698462, by rfl⟩ : syracuseStep 931283 = 1396925) B1396925
theorem B8238635 : Blo 243817 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B1881791 : Blo 243817 1881791 := bstep (se 1 (by rfl) ⟨1411343, by rfl⟩ : syracuseStep 1881791 = 2822687) B2822687
theorem B702233 : Blo 243817 702233 := bstep (se 2 (by rfl) ⟨263337, by rfl⟩ : syracuseStep 702233 = 526675) B526675
theorem B833435 : Blo 243817 833435 := bstep (se 1 (by rfl) ⟨625076, by rfl⟩ : syracuseStep 833435 = 1250153) B1250153
theorem B276511 : Blo 243817 276511 := bstep (se 1 (by rfl) ⟨207383, by rfl⟩ : syracuseStep 276511 = 414767) B414767
theorem B309359 : Blo 243817 309359 := bstep (se 1 (by rfl) ⟨232019, by rfl⟩ : syracuseStep 309359 = 464039) B464039
theorem B309415 : Blo 243817 309415 := bstep (se 1 (by rfl) ⟨232061, by rfl⟩ : syracuseStep 309415 = 464123) B464123
theorem B243919 : Blo 243817 243919 := bstep (se 1 (by rfl) ⟨182939, by rfl⟩ : syracuseStep 243919 = 365879) B365879
theorem B243967 : Blo 243817 243967 := bstep (se 1 (by rfl) ⟨182975, by rfl⟩ : syracuseStep 243967 = 365951) B365951
theorem B276763 : Blo 243817 276763 := bstep (se 1 (by rfl) ⟨207572, by rfl⟩ : syracuseStep 276763 = 415145) B415145
theorem B276799 : Blo 243817 276799 := bstep (se 1 (by rfl) ⟨207599, by rfl⟩ : syracuseStep 276799 = 415199) B415199
theorem B997751 : Blo 243817 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B2112095 : Blo 243817 2112095 := bstep (se 1 (by rfl) ⟨1584071, by rfl⟩ : syracuseStep 2112095 = 3168143) B3168143
theorem B244327 : Blo 243817 244327 := bstep (se 1 (by rfl) ⟨183245, by rfl⟩ : syracuseStep 244327 = 366491) B366491
theorem B277447 : Blo 243817 277447 := bstep (se 1 (by rfl) ⟨208085, by rfl⟩ : syracuseStep 277447 = 416171) B416171
theorem B244799 : Blo 243817 244799 := bstep (se 1 (by rfl) ⟨183599, by rfl⟩ : syracuseStep 244799 = 367199) B367199
theorem B244847 : Blo 243817 244847 := bstep (se 1 (by rfl) ⟨183635, by rfl⟩ : syracuseStep 244847 = 367271) B367271
theorem B244891 : Blo 243817 244891 := bstep (se 1 (by rfl) ⟨183668, by rfl⟩ : syracuseStep 244891 = 367337) B367337
theorem B244991 : Blo 243817 244991 := bstep (se 1 (by rfl) ⟨183743, by rfl⟩ : syracuseStep 244991 = 367487) B367487
theorem B1490183 : Blo 243817 1490183 := bstep (se 1 (by rfl) ⟨1117637, by rfl⟩ : syracuseStep 1490183 = 2235275) B2235275
theorem B245119 : Blo 243817 245119 := bstep (se 1 (by rfl) ⟨183839, by rfl⟩ : syracuseStep 245119 = 367679) B367679
theorem B245151 : Blo 243817 245151 := bstep (se 1 (by rfl) ⟨183863, by rfl⟩ : syracuseStep 245151 = 367727) B367727
theorem B245183 : Blo 243817 245183 := bstep (se 1 (by rfl) ⟨183887, by rfl⟩ : syracuseStep 245183 = 367775) B367775
theorem B1064569 : Blo 243817 1064569 := bstep (se 2 (by rfl) ⟨399213, by rfl⟩ : syracuseStep 1064569 = 798427) B798427
theorem B245439 : Blo 243817 245439 := bstep (se 1 (by rfl) ⟨184079, by rfl⟩ : syracuseStep 245439 = 368159) B368159
theorem B5422879 : Blo 243817 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B245755 : Blo 243817 245755 := bstep (se 1 (by rfl) ⟨184316, by rfl⟩ : syracuseStep 245755 = 368633) B368633
theorem B245807 : Blo 243817 245807 := bstep (se 1 (by rfl) ⟨184355, by rfl⟩ : syracuseStep 245807 = 368711) B368711
theorem B246319 : Blo 243817 246319 := bstep (se 1 (by rfl) ⟨184739, by rfl⟩ : syracuseStep 246319 = 369479) B369479
theorem B247039 : Blo 243817 247039 := bstep (se 1 (by rfl) ⟨185279, by rfl⟩ : syracuseStep 247039 = 370559) B370559
theorem B247247 : Blo 243817 247247 := bstep (se 1 (by rfl) ⟨185435, by rfl⟩ : syracuseStep 247247 = 370871) B370871
theorem B935671 : Blo 243817 935671 := bstep (se 1 (by rfl) ⟨701753, by rfl⟩ : syracuseStep 935671 = 1403507) B1403507
theorem B247719 : Blo 243817 247719 := bstep (se 1 (by rfl) ⟨185789, by rfl⟩ : syracuseStep 247719 = 371579) B371579
theorem B2115719 : Blo 243817 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B938087 : Blo 243817 938087 := bstep (se 1 (by rfl) ⟨703565, by rfl⟩ : syracuseStep 938087 = 1407131) B1407131
theorem B1003735 : Blo 243817 1003735 := bstep (se 1 (by rfl) ⟨752801, by rfl⟩ : syracuseStep 1003735 = 1505603) B1505603
theorem B414335 : Blo 243817 414335 := bstep (se 1 (by rfl) ⟨310751, by rfl⟩ : syracuseStep 414335 = 621503) B621503
theorem B3986333 : Blo 243817 3986333 := bstep (se 3 (by rfl) ⟨747437, by rfl⟩ : syracuseStep 3986333 = 1494875) B1494875
theorem B415003 : Blo 243817 415003 := bstep (se 1 (by rfl) ⟨311252, by rfl⟩ : syracuseStep 415003 = 622505) B622505
theorem B1594889 : Blo 243817 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B415273 : Blo 243817 415273 := bstep (se 2 (by rfl) ⟨155727, by rfl⟩ : syracuseStep 415273 = 311455) B311455
theorem B808951 : Blo 243817 808951 := bstep (se 1 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 808951 = 1213427) B1213427
theorem B448679 : Blo 243817 448679 := bstep (se 1 (by rfl) ⟨336509, by rfl⟩ : syracuseStep 448679 = 673019) B673019
theorem B416063 : Blo 243817 416063 := bstep (se 1 (by rfl) ⟨312047, by rfl⟩ : syracuseStep 416063 = 624095) B624095
theorem B2088449 : Blo 243817 2088449 := bstep (se 2 (by rfl) ⟨783168, by rfl⟩ : syracuseStep 2088449 = 1566337) B1566337
theorem B549755 : Blo 243817 549755 := bstep (se 1 (by rfl) ⟨412316, by rfl⟩ : syracuseStep 549755 = 824633) B824633
theorem B550367 : Blo 243817 550367 := bstep (se 1 (by rfl) ⟨412775, by rfl⟩ : syracuseStep 550367 = 825551) B825551
theorem B1042091 : Blo 243817 1042091 := bstep (se 1 (by rfl) ⟨781568, by rfl⟩ : syracuseStep 1042091 = 1563137) B1563137
theorem B550655 : Blo 243817 550655 := bstep (se 1 (by rfl) ⟨412991, by rfl⟩ : syracuseStep 550655 = 825983) B825983
theorem B2254715 : Blo 243817 2254715 := bstep (se 1 (by rfl) ⟨1691036, by rfl⟩ : syracuseStep 2254715 = 3382073) B3382073
theorem B13559795 : Blo 243817 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B3172607 : Blo 243817 3172607 := bstep (se 1 (by rfl) ⟨2379455, by rfl⟩ : syracuseStep 3172607 = 4758911) B4758911
theorem B1501861 : Blo 243817 1501861 := bstep (se 4 (by rfl) ⟨140799, by rfl⟩ : syracuseStep 1501861 = 281599) B281599
theorem B1862351 : Blo 243817 1862351 := bstep (se 1 (by rfl) ⟨1396763, by rfl⟩ : syracuseStep 1862351 = 2793527) B2793527
theorem B552275 : Blo 243817 552275 := bstep (se 1 (by rfl) ⟨414206, by rfl⟩ : syracuseStep 552275 = 828413) B828413
theorem B1863323 : Blo 243817 1863323 := bstep (se 1 (by rfl) ⟨1397492, by rfl⟩ : syracuseStep 1863323 = 2794985) B2794985
theorem B618587 : Blo 243817 618587 := bstep (se 1 (by rfl) ⟨463940, by rfl⟩ : syracuseStep 618587 = 927881) B927881
theorem B2355581 : Blo 243817 2355581 := bstep (se 3 (by rfl) ⟨441671, by rfl⟩ : syracuseStep 2355581 = 883343) B883343
theorem B553499 : Blo 243817 553499 := bstep (se 1 (by rfl) ⟨415124, by rfl⟩ : syracuseStep 553499 = 830249) B830249
theorem B1405673 : Blo 243817 1405673 := bstep (se 2 (by rfl) ⟨527127, by rfl⟩ : syracuseStep 1405673 = 1054255) B1054255
theorem B33092813 : Blo 243817 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B1242377 : Blo 243817 1242377 := bstep (se 2 (by rfl) ⟨465891, by rfl⟩ : syracuseStep 1242377 = 931783) B931783
theorem B620531 : Blo 243817 620531 := bstep (se 1 (by rfl) ⟨465398, by rfl⟩ : syracuseStep 620531 = 930797) B930797
theorem B623609 : Blo 243817 623609 := bstep (se 2 (by rfl) ⟨233853, by rfl⟩ : syracuseStep 623609 = 467707) B467707
theorem B525359 : Blo 243817 525359 := bstep (se 1 (by rfl) ⟨394019, by rfl⟩ : syracuseStep 525359 = 788039) B788039
theorem B1410479 : Blo 243817 1410479 := bstep (se 1 (by rfl) ⟨1057859, by rfl⟩ : syracuseStep 1410479 = 2115719) B2115719
theorem B5867113 : Blo 243817 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B1247399 : Blo 243817 1247399 := bstep (se 1 (by rfl) ⟨935549, by rfl⟩ : syracuseStep 1247399 = 1871099) B1871099
theorem B1247561 : Blo 243817 1247561 := bstep (se 2 (by rfl) ⟨467835, by rfl⟩ : syracuseStep 1247561 = 935671) B935671
theorem B625391 : Blo 243817 625391 := bstep (se 1 (by rfl) ⟨469043, by rfl⟩ : syracuseStep 625391 = 938087) B938087
theorem B88247501 : Blo 243817 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B2657555 : Blo 243817 2657555 := bstep (se 1 (by rfl) ⟨1993166, by rfl⟩ : syracuseStep 2657555 = 3986333) B3986333
theorem B2002481 : Blo 243817 2002481 := bstep (se 2 (by rfl) ⟨750930, by rfl⟩ : syracuseStep 2002481 = 1501861) B1501861
theorem B1052615 : Blo 243817 1052615 := bstep (se 1 (by rfl) ⟨789461, by rfl⟩ : syracuseStep 1052615 = 1578923) B1578923
theorem B299119 : Blo 243817 299119 := bstep (se 1 (by rfl) ⟨224339, by rfl⟩ : syracuseStep 299119 = 448679) B448679
theorem B463295 : Blo 243817 463295 := bstep (se 1 (by rfl) ⟨347471, by rfl⟩ : syracuseStep 463295 = 694943) B694943
theorem B824957 : Blo 243817 824957 := bstep (se 3 (by rfl) ⟨154679, by rfl⟩ : syracuseStep 824957 = 309359) B309359
theorem B366503 : Blo 243817 366503 := bstep (se 1 (by rfl) ⟨274877, by rfl⟩ : syracuseStep 366503 = 549755) B549755
theorem B366761 : Blo 243817 366761 := bstep (se 2 (by rfl) ⟨137535, by rfl⟩ : syracuseStep 366761 = 275071) B275071
theorem B366911 : Blo 243817 366911 := bstep (se 1 (by rfl) ⟨275183, by rfl⟩ : syracuseStep 366911 = 550367) B550367
theorem B694727 : Blo 243817 694727 := bstep (se 1 (by rfl) ⟨521045, by rfl⟩ : syracuseStep 694727 = 1042091) B1042091
theorem B367103 : Blo 243817 367103 := bstep (se 1 (by rfl) ⟨275327, by rfl⟩ : syracuseStep 367103 = 550655) B550655
theorem B1056253 : Blo 243817 1056253 := bstep (se 3 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 1056253 = 396095) B396095
theorem B368183 : Blo 243817 368183 := bstep (se 1 (by rfl) ⟨276137, by rfl⟩ : syracuseStep 368183 = 552275) B552275
theorem B3350443 : Blo 243817 3350443 := bstep (se 1 (by rfl) ⟨2512832, by rfl⟩ : syracuseStep 3350443 = 5025665) B5025665
theorem B368681 : Blo 243817 368681 := bstep (se 2 (by rfl) ⟨138255, by rfl⟩ : syracuseStep 368681 = 276511) B276511
theorem B368999 : Blo 243817 368999 := bstep (se 1 (by rfl) ⟨276749, by rfl⟩ : syracuseStep 368999 = 553499) B553499
theorem B369017 : Blo 243817 369017 := bstep (se 2 (by rfl) ⟨138381, by rfl⟩ : syracuseStep 369017 = 276763) B276763
theorem B369065 : Blo 243817 369065 := bstep (se 2 (by rfl) ⟨138399, by rfl⟩ : syracuseStep 369065 = 276799) B276799
theorem B828251 : Blo 243817 828251 := bstep (se 1 (by rfl) ⟨621188, by rfl⟩ : syracuseStep 828251 = 1242377) B1242377
theorem B1254527 : Blo 243817 1254527 := bstep (se 1 (by rfl) ⟨940895, by rfl⟩ : syracuseStep 1254527 = 1881791) B1881791
theorem B1057961 : Blo 243817 1057961 := bstep (se 2 (by rfl) ⟨396735, by rfl⟩ : syracuseStep 1057961 = 793471) B793471
theorem B468155 : Blo 243817 468155 := bstep (se 1 (by rfl) ⟨351116, by rfl⟩ : syracuseStep 468155 = 702233) B702233
theorem B369929 : Blo 243817 369929 := bstep (se 2 (by rfl) ⟨138723, by rfl⟩ : syracuseStep 369929 = 277447) B277447
theorem B665167 : Blo 243817 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B2369341 : Blo 243817 2369341 := bstep (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) B888503
theorem B1419425 : Blo 243817 1419425 := bstep (se 2 (by rfl) ⟨532284, by rfl⟩ : syracuseStep 1419425 = 1064569) B1064569
theorem B993455 : Blo 243817 993455 := bstep (se 1 (by rfl) ⟨745091, by rfl⟩ : syracuseStep 993455 = 1490183) B1490183
theorem B928169 : Blo 243817 928169 := bstep (se 2 (by rfl) ⟨348063, by rfl⟩ : syracuseStep 928169 = 696127) B696127
theorem B3190279 : Blo 243817 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B5353253 : Blo 243817 5353253 := bstep (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) B1003735
theorem B831977 : Blo 243817 831977 := bstep (se 2 (by rfl) ⟨311991, by rfl⟩ : syracuseStep 831977 = 623983) B623983
theorem B832895 : Blo 243817 832895 := bstep (se 1 (by rfl) ⟨624671, by rfl⟩ : syracuseStep 832895 = 1249343) B1249343
theorem B1422845 : Blo 243817 1422845 := bstep (se 3 (by rfl) ⟨266783, by rfl⟩ : syracuseStep 1422845 = 533567) B533567
theorem B276223 : Blo 243817 276223 := bstep (se 1 (by rfl) ⟨207167, by rfl⟩ : syracuseStep 276223 = 414335) B414335
theorem B243879 : Blo 243817 243879 := bstep (se 1 (by rfl) ⟨182909, by rfl⟩ : syracuseStep 243879 = 365819) B365819
theorem B1063259 : Blo 243817 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B244159 : Blo 243817 244159 := bstep (se 1 (by rfl) ⟨183119, by rfl⟩ : syracuseStep 244159 = 366239) B366239
theorem B244511 : Blo 243817 244511 := bstep (se 1 (by rfl) ⟨183383, by rfl⟩ : syracuseStep 244511 = 366767) B366767
theorem B277375 : Blo 243817 277375 := bstep (se 1 (by rfl) ⟨208031, by rfl⟩ : syracuseStep 277375 = 416063) B416063
theorem B1489913 : Blo 243817 1489913 := bstep (se 2 (by rfl) ⟨558717, by rfl⟩ : syracuseStep 1489913 = 1117435) B1117435
theorem B244731 : Blo 243817 244731 := bstep (se 1 (by rfl) ⟨183548, by rfl⟩ : syracuseStep 244731 = 367097) B367097
theorem B2800817 : Blo 243817 2800817 := bstep (se 2 (by rfl) ⟨1050306, by rfl⟩ : syracuseStep 2800817 = 2100613) B2100613
theorem B245279 : Blo 243817 245279 := bstep (se 1 (by rfl) ⟨183959, by rfl⟩ : syracuseStep 245279 = 367919) B367919
theorem B245351 : Blo 243817 245351 := bstep (se 1 (by rfl) ⟨184013, by rfl⟩ : syracuseStep 245351 = 368027) B368027
theorem B1392299 : Blo 243817 1392299 := bstep (se 1 (by rfl) ⟨1044224, by rfl⟩ : syracuseStep 1392299 = 2088449) B2088449
theorem B245695 : Blo 243817 245695 := bstep (se 1 (by rfl) ⟨184271, by rfl⟩ : syracuseStep 245695 = 368543) B368543
theorem B245831 : Blo 243817 245831 := bstep (se 1 (by rfl) ⟨184373, by rfl⟩ : syracuseStep 245831 = 368747) B368747
theorem B245915 : Blo 243817 245915 := bstep (se 1 (by rfl) ⟨184436, by rfl⟩ : syracuseStep 245915 = 368873) B368873
theorem B247295 : Blo 243817 247295 := bstep (se 1 (by rfl) ⟨185471, by rfl⟩ : syracuseStep 247295 = 370943) B370943
theorem B2115071 : Blo 243817 2115071 := bstep (se 1 (by rfl) ⟨1586303, by rfl⟩ : syracuseStep 2115071 = 3172607) B3172607
theorem B247503 : Blo 243817 247503 := bstep (se 1 (by rfl) ⟨185627, by rfl⟩ : syracuseStep 247503 = 371255) B371255
theorem B247551 : Blo 243817 247551 := bstep (se 1 (by rfl) ⟨185663, by rfl⟩ : syracuseStep 247551 = 371327) B371327
theorem B2410399 : Blo 243817 2410399 := bstep (se 1 (by rfl) ⟨1807799, by rfl⟩ : syracuseStep 2410399 = 3615599) B3615599
theorem B412391 : Blo 243817 412391 := bstep (se 1 (by rfl) ⟨309293, by rfl⟩ : syracuseStep 412391 = 618587) B618587
theorem B412553 : Blo 243817 412553 := bstep (se 2 (by rfl) ⟨154707, by rfl⟩ : syracuseStep 412553 = 309415) B309415
theorem B937115 : Blo 243817 937115 := bstep (se 1 (by rfl) ⟨702836, by rfl⟩ : syracuseStep 937115 = 1405673) B1405673
theorem B5492423 : Blo 243817 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B413687 : Blo 243817 413687 := bstep (se 1 (by rfl) ⟨310265, by rfl⟩ : syracuseStep 413687 = 620531) B620531
theorem B7230505 : Blo 243817 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B549467 : Blo 243817 549467 := bstep (se 1 (by rfl) ⟨412100, by rfl⟩ : syracuseStep 549467 = 824201) B824201
theorem B1402505 : Blo 243817 1402505 := bstep (se 2 (by rfl) ⟨525939, by rfl⟩ : syracuseStep 1402505 = 1051879) B1051879
theorem B552383 : Blo 243817 552383 := bstep (se 1 (by rfl) ⟨414287, by rfl⟩ : syracuseStep 552383 = 828575) B828575
theorem B1404647 : Blo 243817 1404647 := bstep (se 1 (by rfl) ⟨1053485, by rfl⟩ : syracuseStep 1404647 = 2106971) B2106971
theorem B51867371 : Blo 243817 51867371 := bstep (se 1 (by rfl) ⟨38900528, by rfl⟩ : syracuseStep 51867371 = 77801057) B77801057
theorem B1503143 : Blo 243817 1503143 := bstep (se 1 (by rfl) ⟨1127357, by rfl⟩ : syracuseStep 1503143 = 2254715) B2254715
theorem B9039863 : Blo 243817 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B4288639 : Blo 243817 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B5337251 : Blo 243817 5337251 := bstep (se 1 (by rfl) ⟨4002938, by rfl⟩ : syracuseStep 5337251 = 8005877) B8005877
theorem B356519 : Blo 243817 356519 := bstep (se 1 (by rfl) ⟨267389, by rfl⟩ : syracuseStep 356519 = 534779) B534779
theorem B553337 : Blo 243817 553337 := bstep (se 2 (by rfl) ⟨207501, by rfl⟩ : syracuseStep 553337 = 415003) B415003
theorem B8057249 : Blo 243817 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B1241567 : Blo 243817 1241567 := bstep (se 1 (by rfl) ⟨931175, by rfl⟩ : syracuseStep 1241567 = 1862351) B1862351
theorem B553697 : Blo 243817 553697 := bstep (se 2 (by rfl) ⟨207636, by rfl⟩ : syracuseStep 553697 = 415273) B415273
theorem B1242215 : Blo 243817 1242215 := bstep (se 1 (by rfl) ⟨931661, by rfl⟩ : syracuseStep 1242215 = 1863323) B1863323
theorem B1078601 : Blo 243817 1078601 := bstep (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) B808951
theorem B1570387 : Blo 243817 1570387 := bstep (se 1 (by rfl) ⟨1177790, by rfl⟩ : syracuseStep 1570387 = 2355581) B2355581
theorem B555119 : Blo 243817 555119 := bstep (se 1 (by rfl) ⟨416339, by rfl⟩ : syracuseStep 555119 = 832679) B832679
theorem B620855 : Blo 243817 620855 := bstep (se 1 (by rfl) ⟨465641, by rfl⟩ : syracuseStep 620855 = 931283) B931283
theorem B555623 : Blo 243817 555623 := bstep (se 1 (by rfl) ⟨416717, by rfl⟩ : syracuseStep 555623 = 833435) B833435
theorem B1408063 : Blo 243817 1408063 := bstep (se 1 (by rfl) ⟨1056047, by rfl⟩ : syracuseStep 1408063 = 2112095) B2112095
theorem B950717 : Blo 243817 950717 := bstep (se 3 (by rfl) ⟨178259, by rfl⟩ : syracuseStep 950717 = 356519) B356519
theorem B1410047 : Blo 243817 1410047 := bstep (se 1 (by rfl) ⟨1057535, by rfl⟩ : syracuseStep 1410047 = 2115071) B2115071
theorem B15140533 : Blo 243817 15140533 := bstep (se 5 (by rfl) ⟨709712, by rfl⟩ : syracuseStep 15140533 = 1419425) B1419425
theorem B624743 : Blo 243817 624743 := bstep (se 1 (by rfl) ⟨468557, by rfl⟩ : syracuseStep 624743 = 937115) B937115
theorem B886889 : Blo 243817 886889 := bstep (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) B665167
theorem B1771703 : Blo 243817 1771703 := bstep (se 1 (by rfl) ⟨1328777, by rfl⟩ : syracuseStep 1771703 = 2657555) B2657555
theorem B3213865 : Blo 243817 3213865 := bstep (se 2 (by rfl) ⟨1205199, by rfl⟩ : syracuseStep 3213865 = 2410399) B2410399
theorem B2821229 : Blo 243817 2821229 := bstep (se 3 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 2821229 = 1057961) B1057961
theorem B11505077 : Blo 243817 11505077 := bstep (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) B1078601
theorem B463151 : Blo 243817 463151 := bstep (se 1 (by rfl) ⟨347363, by rfl⟩ : syracuseStep 463151 = 694727) B694727
theorem B398825 : Blo 243817 398825 := bstep (se 2 (by rfl) ⟨149559, by rfl⟩ : syracuseStep 398825 = 299119) B299119
theorem B366311 : Blo 243817 366311 := bstep (se 1 (by rfl) ⟨274733, by rfl⟩ : syracuseStep 366311 = 549467) B549467
theorem B9640673 : Blo 243817 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B662303 : Blo 243817 662303 := bstep (se 1 (by rfl) ⟨496727, by rfl⟩ : syracuseStep 662303 = 993455) B993455
theorem B368255 : Blo 243817 368255 := bstep (se 1 (by rfl) ⟨276191, by rfl⟩ : syracuseStep 368255 = 552383) B552383
theorem B368297 : Blo 243817 368297 := bstep (se 2 (by rfl) ⟨138111, by rfl⟩ : syracuseStep 368297 = 276223) B276223
theorem B34578247 : Blo 243817 34578247 := bstep (se 1 (by rfl) ⟨25933685, by rfl⟩ : syracuseStep 34578247 = 51867371) B51867371
theorem B368891 : Blo 243817 368891 := bstep (se 1 (by rfl) ⟨276668, by rfl⟩ : syracuseStep 368891 = 553337) B553337
theorem B827711 : Blo 243817 827711 := bstep (se 1 (by rfl) ⟨620783, by rfl⟩ : syracuseStep 827711 = 1241567) B1241567
theorem B369131 : Blo 243817 369131 := bstep (se 1 (by rfl) ⟨276848, by rfl⟩ : syracuseStep 369131 = 553697) B553697
theorem B828143 : Blo 243817 828143 := bstep (se 1 (by rfl) ⟨621107, by rfl⟩ : syracuseStep 828143 = 1242215) B1242215
theorem B369833 : Blo 243817 369833 := bstep (se 2 (by rfl) ⟨138687, by rfl⟩ : syracuseStep 369833 = 277375) B277375
theorem B370079 : Blo 243817 370079 := bstep (se 1 (by rfl) ⟨277559, by rfl⟩ : syracuseStep 370079 = 555119) B555119
theorem B1877417 : Blo 243817 1877417 := bstep (se 2 (by rfl) ⟨704031, by rfl⟩ : syracuseStep 1877417 = 1408063) B1408063
theorem B370415 : Blo 243817 370415 := bstep (se 1 (by rfl) ⟨277811, by rfl⟩ : syracuseStep 370415 = 555623) B555623
theorem B993275 : Blo 243817 993275 := bstep (se 1 (by rfl) ⟨744956, by rfl⟩ : syracuseStep 993275 = 1489913) B1489913
theorem B928199 : Blo 243817 928199 := bstep (se 1 (by rfl) ⟨696149, by rfl⟩ : syracuseStep 928199 = 1392299) B1392299
theorem B4467257 : Blo 243817 4467257 := bstep (se 2 (by rfl) ⟨1675221, by rfl⟩ : syracuseStep 4467257 = 3350443) B3350443
theorem B831599 : Blo 243817 831599 := bstep (se 1 (by rfl) ⟨623699, by rfl⟩ : syracuseStep 831599 = 1247399) B1247399
theorem B831707 : Blo 243817 831707 := bstep (se 1 (by rfl) ⟨623780, by rfl⟩ : syracuseStep 831707 = 1247561) B1247561
theorem B274927 : Blo 243817 274927 := bstep (se 1 (by rfl) ⟨206195, by rfl⟩ : syracuseStep 274927 = 412391) B412391
theorem B275035 : Blo 243817 275035 := bstep (se 1 (by rfl) ⟨206276, by rfl⟩ : syracuseStep 275035 = 412553) B412553
theorem B58831667 : Blo 243817 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B3159121 : Blo 243817 3159121 := bstep (se 2 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 3159121 = 2369341) B2369341
theorem B701743 : Blo 243817 701743 := bstep (se 1 (by rfl) ⟨526307, by rfl⟩ : syracuseStep 701743 = 1052615) B1052615
theorem B275791 : Blo 243817 275791 := bstep (se 1 (by rfl) ⟨206843, by rfl⟩ : syracuseStep 275791 = 413687) B413687
theorem B308863 : Blo 243817 308863 := bstep (se 1 (by rfl) ⟨231647, by rfl⟩ : syracuseStep 308863 = 463295) B463295
theorem B244335 : Blo 243817 244335 := bstep (se 1 (by rfl) ⟨183251, by rfl⟩ : syracuseStep 244335 = 366503) B366503
theorem B244507 : Blo 243817 244507 := bstep (se 1 (by rfl) ⟨183380, by rfl⟩ : syracuseStep 244507 = 366761) B366761
theorem B244607 : Blo 243817 244607 := bstep (se 1 (by rfl) ⟨183455, by rfl⟩ : syracuseStep 244607 = 366911) B366911
theorem B244735 : Blo 243817 244735 := bstep (se 1 (by rfl) ⟨183551, by rfl⟩ : syracuseStep 244735 = 367103) B367103
theorem B245455 : Blo 243817 245455 := bstep (se 1 (by rfl) ⟨184091, by rfl⟩ : syracuseStep 245455 = 368183) B368183
theorem B245787 : Blo 243817 245787 := bstep (se 1 (by rfl) ⟨184340, by rfl⟩ : syracuseStep 245787 = 368681) B368681
theorem B5718185 : Blo 243817 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B245999 : Blo 243817 245999 := bstep (se 1 (by rfl) ⟨184499, by rfl⟩ : syracuseStep 245999 = 368999) B368999
theorem B246011 : Blo 243817 246011 := bstep (se 1 (by rfl) ⟨184508, by rfl⟩ : syracuseStep 246011 = 369017) B369017
theorem B246043 : Blo 243817 246043 := bstep (se 1 (by rfl) ⟨184532, by rfl⟩ : syracuseStep 246043 = 369065) B369065
theorem B836351 : Blo 243817 836351 := bstep (se 1 (by rfl) ⟨627263, by rfl⟩ : syracuseStep 836351 = 1254527) B1254527
theorem B312103 : Blo 243817 312103 := bstep (se 1 (by rfl) ⟨234077, by rfl⟩ : syracuseStep 312103 = 468155) B468155
theorem B246619 : Blo 243817 246619 := bstep (se 1 (by rfl) ⟨184964, by rfl⟩ : syracuseStep 246619 = 369929) B369929
theorem B935003 : Blo 243817 935003 := bstep (se 1 (by rfl) ⟨701252, by rfl⟩ : syracuseStep 935003 = 1402505) B1402505
theorem B936431 : Blo 243817 936431 := bstep (se 1 (by rfl) ⟨702323, by rfl⟩ : syracuseStep 936431 = 1404647) B1404647
theorem B1002095 : Blo 243817 1002095 := bstep (se 1 (by rfl) ⟨751571, by rfl⟩ : syracuseStep 1002095 = 1503143) B1503143
theorem B3558167 : Blo 243817 3558167 := bstep (se 1 (by rfl) ⟨2668625, by rfl⟩ : syracuseStep 3558167 = 5337251) B5337251
theorem B413903 : Blo 243817 413903 := bstep (se 1 (by rfl) ⟨310427, by rfl⟩ : syracuseStep 413903 = 620855) B620855
theorem B708839 : Blo 243817 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B415739 : Blo 243817 415739 := bstep (se 1 (by rfl) ⟨311804, by rfl⟩ : syracuseStep 415739 = 623609) B623609
theorem B350239 : Blo 243817 350239 := bstep (se 1 (by rfl) ⟨262679, by rfl⟩ : syracuseStep 350239 = 525359) B525359
theorem B940319 : Blo 243817 940319 := bstep (se 1 (by rfl) ⟨705239, by rfl⟩ : syracuseStep 940319 = 1410479) B1410479
theorem B416927 : Blo 243817 416927 := bstep (se 1 (by rfl) ⟨312695, by rfl⟩ : syracuseStep 416927 = 625391) B625391
theorem B7822817 : Blo 243817 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B1334987 : Blo 243817 1334987 := bstep (se 1 (by rfl) ⟨1001240, by rfl⟩ : syracuseStep 1334987 = 2002481) B2002481
theorem B3661615 : Blo 243817 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B549971 : Blo 243817 549971 := bstep (se 1 (by rfl) ⟨412478, by rfl⟩ : syracuseStep 549971 = 824957) B824957
theorem B4253705 : Blo 243817 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B552167 : Blo 243817 552167 := bstep (se 1 (by rfl) ⟨414125, by rfl⟩ : syracuseStep 552167 = 828251) B828251
theorem B618779 : Blo 243817 618779 := bstep (se 1 (by rfl) ⟨464084, by rfl⟩ : syracuseStep 618779 = 928169) B928169
theorem B2093849 : Blo 243817 2093849 := bstep (se 2 (by rfl) ⟨785193, by rfl⟩ : syracuseStep 2093849 = 1570387) B1570387
theorem B3568835 : Blo 243817 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B6026575 : Blo 243817 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B5371499 : Blo 243817 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B554651 : Blo 243817 554651 := bstep (se 1 (by rfl) ⟨415988, by rfl⟩ : syracuseStep 554651 = 831977) B831977
theorem B555263 : Blo 243817 555263 := bstep (se 1 (by rfl) ⟨416447, by rfl⟩ : syracuseStep 555263 = 832895) B832895
theorem B948563 : Blo 243817 948563 := bstep (se 1 (by rfl) ⟨711422, by rfl⟩ : syracuseStep 948563 = 1422845) B1422845
theorem B1408337 : Blo 243817 1408337 := bstep (se 2 (by rfl) ⟨528126, by rfl⟩ : syracuseStep 1408337 = 1056253) B1056253
theorem B1867211 : Blo 243817 1867211 := bstep (se 1 (by rfl) ⟨1400408, by rfl⟩ : syracuseStep 1867211 = 2800817) B2800817
theorem B557567 : Blo 243817 557567 := bstep (se 1 (by rfl) ⟨418175, by rfl⟩ : syracuseStep 557567 = 836351) B836351
theorem B623335 : Blo 243817 623335 := bstep (se 1 (by rfl) ⟨467501, by rfl⟩ : syracuseStep 623335 = 935003) B935003
theorem B1181135 : Blo 243817 1181135 := bstep (se 1 (by rfl) ⟨885851, by rfl⟩ : syracuseStep 1181135 = 1771703) B1771703
theorem B624287 : Blo 243817 624287 := bstep (se 1 (by rfl) ⟨468215, by rfl⟩ : syracuseStep 624287 = 936431) B936431
theorem B20187377 : Blo 243817 20187377 := bstep (se 2 (by rfl) ⟨7570266, by rfl⟩ : syracuseStep 20187377 = 15140533) B15140533
theorem B7670051 : Blo 243817 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B265883 : Blo 243817 265883 := bstep (se 1 (by rfl) ⟨199412, by rfl⟩ : syracuseStep 265883 = 398825) B398825
theorem B626879 : Blo 243817 626879 := bstep (se 1 (by rfl) ⟨470159, by rfl⟩ : syracuseStep 626879 = 940319) B940319
theorem B6427115 : Blo 243817 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B5215211 : Blo 243817 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B889991 : Blo 243817 889991 := bstep (se 1 (by rfl) ⟨667493, by rfl⟩ : syracuseStep 889991 = 1334987) B1334987
theorem B2365037 : Blo 243817 2365037 := bstep (se 3 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 2365037 = 886889) B886889
theorem B366569 : Blo 243817 366569 := bstep (se 2 (by rfl) ⟨137463, by rfl⟩ : syracuseStep 366569 = 274927) B274927
theorem B366647 : Blo 243817 366647 := bstep (se 1 (by rfl) ⟨274985, by rfl⟩ : syracuseStep 366647 = 549971) B549971
theorem B366713 : Blo 243817 366713 := bstep (se 2 (by rfl) ⟨137517, by rfl⟩ : syracuseStep 366713 = 275035) B275035
theorem B1251611 : Blo 243817 1251611 := bstep (se 1 (by rfl) ⟨938708, by rfl⟩ : syracuseStep 1251611 = 1877417) B1877417
theorem B662183 : Blo 243817 662183 := bstep (se 1 (by rfl) ⟨496637, by rfl⟩ : syracuseStep 662183 = 993275) B993275
theorem B8035433 : Blo 243817 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B367721 : Blo 243817 367721 := bstep (se 2 (by rfl) ⟨137895, by rfl⟩ : syracuseStep 367721 = 275791) B275791
theorem B368111 : Blo 243817 368111 := bstep (se 1 (by rfl) ⟨276083, by rfl⟩ : syracuseStep 368111 = 552167) B552167
theorem B466985 : Blo 243817 466985 := bstep (se 2 (by rfl) ⟨175119, by rfl⟩ : syracuseStep 466985 = 350239) B350239
theorem B3580999 : Blo 243817 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B369767 : Blo 243817 369767 := bstep (se 1 (by rfl) ⟨277325, by rfl⟩ : syracuseStep 369767 = 554651) B554651
theorem B370175 : Blo 243817 370175 := bstep (se 1 (by rfl) ⟨277631, by rfl⟩ : syracuseStep 370175 = 555263) B555263
theorem B632375 : Blo 243817 632375 := bstep (se 1 (by rfl) ⟨474281, by rfl⟩ : syracuseStep 632375 = 948563) B948563
theorem B3812123 : Blo 243817 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B2535245 : Blo 243817 2535245 := bstep (se 3 (by rfl) ⟨475358, by rfl⟩ : syracuseStep 2535245 = 950717) B950717
theorem B668063 : Blo 243817 668063 := bstep (se 1 (by rfl) ⟨501047, by rfl⟩ : syracuseStep 668063 = 1002095) B1002095
theorem B2372111 : Blo 243817 2372111 := bstep (se 1 (by rfl) ⟨1779083, by rfl⟩ : syracuseStep 2372111 = 3558167) B3558167
theorem B1880819 : Blo 243817 1880819 := bstep (se 1 (by rfl) ⟨1410614, by rfl⟩ : syracuseStep 1880819 = 2821229) B2821229
theorem B275935 : Blo 243817 275935 := bstep (se 1 (by rfl) ⟨206951, by rfl⟩ : syracuseStep 275935 = 413903) B413903
theorem B472559 : Blo 243817 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B308767 : Blo 243817 308767 := bstep (se 1 (by rfl) ⟨231575, by rfl⟩ : syracuseStep 308767 = 463151) B463151
theorem B244207 : Blo 243817 244207 := bstep (se 1 (by rfl) ⟨183155, by rfl⟩ : syracuseStep 244207 = 366311) B366311
theorem B277159 : Blo 243817 277159 := bstep (se 1 (by rfl) ⟨207869, by rfl⟩ : syracuseStep 277159 = 415739) B415739
theorem B441535 : Blo 243817 441535 := bstep (se 1 (by rfl) ⟨331151, by rfl⟩ : syracuseStep 441535 = 662303) B662303
theorem B277951 : Blo 243817 277951 := bstep (se 1 (by rfl) ⟨208463, by rfl⟩ : syracuseStep 277951 = 416927) B416927
theorem B245503 : Blo 243817 245503 := bstep (se 1 (by rfl) ⟨184127, by rfl⟩ : syracuseStep 245503 = 368255) B368255
theorem B245531 : Blo 243817 245531 := bstep (se 1 (by rfl) ⟨184148, by rfl⟩ : syracuseStep 245531 = 368297) B368297
theorem B245927 : Blo 243817 245927 := bstep (se 1 (by rfl) ⟨184445, by rfl⟩ : syracuseStep 245927 = 368891) B368891
theorem B246087 : Blo 243817 246087 := bstep (se 1 (by rfl) ⟨184565, by rfl⟩ : syracuseStep 246087 = 369131) B369131
theorem B246555 : Blo 243817 246555 := bstep (se 1 (by rfl) ⟨184916, by rfl⟩ : syracuseStep 246555 = 369833) B369833
theorem B246719 : Blo 243817 246719 := bstep (se 1 (by rfl) ⟨185039, by rfl⟩ : syracuseStep 246719 = 370079) B370079
theorem B246943 : Blo 243817 246943 := bstep (se 1 (by rfl) ⟨185207, by rfl⟩ : syracuseStep 246943 = 370415) B370415
theorem B2835803 : Blo 243817 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B4212161 : Blo 243817 4212161 := bstep (se 2 (by rfl) ⟨1579560, by rfl⟩ : syracuseStep 4212161 = 3159121) B3159121
theorem B935657 : Blo 243817 935657 := bstep (se 2 (by rfl) ⟨350871, by rfl⟩ : syracuseStep 935657 = 701743) B701743
theorem B411817 : Blo 243817 411817 := bstep (se 2 (by rfl) ⟨154431, by rfl⟩ : syracuseStep 411817 = 308863) B308863
theorem B412519 : Blo 243817 412519 := bstep (se 1 (by rfl) ⟨309389, by rfl⟩ : syracuseStep 412519 = 618779) B618779
theorem B1395899 : Blo 243817 1395899 := bstep (se 1 (by rfl) ⟨1046924, by rfl⟩ : syracuseStep 1395899 = 2093849) B2093849
theorem B2379223 : Blo 243817 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B938891 : Blo 243817 938891 := bstep (se 1 (by rfl) ⟨704168, by rfl⟩ : syracuseStep 938891 = 1408337) B1408337
theorem B940031 : Blo 243817 940031 := bstep (se 1 (by rfl) ⟨705023, by rfl⟩ : syracuseStep 940031 = 1410047) B1410047
theorem B416137 : Blo 243817 416137 := bstep (se 2 (by rfl) ⟨156051, by rfl⟩ : syracuseStep 416137 = 312103) B312103
theorem B416495 : Blo 243817 416495 := bstep (se 1 (by rfl) ⟨312371, by rfl⟩ : syracuseStep 416495 = 624743) B624743
theorem B4285153 : Blo 243817 4285153 := bstep (se 2 (by rfl) ⟨1606932, by rfl⟩ : syracuseStep 4285153 = 3213865) B3213865
theorem B551807 : Blo 243817 551807 := bstep (se 1 (by rfl) ⟨413855, by rfl⟩ : syracuseStep 551807 = 827711) B827711
theorem B552095 : Blo 243817 552095 := bstep (se 1 (by rfl) ⟨414071, by rfl⟩ : syracuseStep 552095 = 828143) B828143
theorem B618799 : Blo 243817 618799 := bstep (se 1 (by rfl) ⟨464099, by rfl⟩ : syracuseStep 618799 = 928199) B928199
theorem B2978171 : Blo 243817 2978171 := bstep (se 1 (by rfl) ⟨2233628, by rfl⟩ : syracuseStep 2978171 = 4467257) B4467257
theorem B554399 : Blo 243817 554399 := bstep (se 1 (by rfl) ⟨415799, by rfl⟩ : syracuseStep 554399 = 831599) B831599
theorem B554471 : Blo 243817 554471 := bstep (se 1 (by rfl) ⟨415853, by rfl⟩ : syracuseStep 554471 = 831707) B831707
theorem B39221111 : Blo 243817 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B19528613 : Blo 243817 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B1244807 : Blo 243817 1244807 := bstep (se 1 (by rfl) ⟨933605, by rfl⟩ : syracuseStep 1244807 = 1867211) B1867211
theorem B46104329 : Blo 243817 46104329 := bstep (se 2 (by rfl) ⟨17289123, by rfl⟩ : syracuseStep 46104329 = 34578247) B34578247
theorem B1245293 : Blo 243817 1245293 := bstep (se 3 (by rfl) ⟨233492, by rfl⟩ : syracuseStep 1245293 = 466985) B466985
theorem B787423 : Blo 243817 787423 := bstep (se 1 (by rfl) ⟨590567, by rfl⟩ : syracuseStep 787423 = 1181135) B1181135
theorem B623771 : Blo 243817 623771 := bstep (se 1 (by rfl) ⟨467828, by rfl⟩ : syracuseStep 623771 = 935657) B935657
theorem B5113367 : Blo 243817 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B625927 : Blo 243817 625927 := bstep (se 1 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 625927 = 938891) B938891
theorem B3476807 : Blo 243817 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B593327 : Blo 243817 593327 := bstep (se 1 (by rfl) ⟨444995, by rfl⟩ : syracuseStep 593327 = 889991) B889991
theorem B1576691 : Blo 243817 1576691 := bstep (se 1 (by rfl) ⟨1182518, by rfl⟩ : syracuseStep 1576691 = 2365037) B2365037
theorem B626687 : Blo 243817 626687 := bstep (se 1 (by rfl) ⟨470015, by rfl⟩ : syracuseStep 626687 = 940031) B940031
theorem B825065 : Blo 243817 825065 := bstep (se 2 (by rfl) ⟨309399, by rfl⟩ : syracuseStep 825065 = 618799) B618799
theorem B367871 : Blo 243817 367871 := bstep (se 1 (by rfl) ⟨275903, by rfl⟩ : syracuseStep 367871 = 551807) B551807
theorem B367913 : Blo 243817 367913 := bstep (se 2 (by rfl) ⟨137967, by rfl⟩ : syracuseStep 367913 = 275935) B275935
theorem B368063 : Blo 243817 368063 := bstep (se 1 (by rfl) ⟨276047, by rfl⟩ : syracuseStep 368063 = 552095) B552095
theorem B1581407 : Blo 243817 1581407 := bstep (se 1 (by rfl) ⟨1186055, by rfl⟩ : syracuseStep 1581407 = 2372111) B2372111
theorem B1253879 : Blo 243817 1253879 := bstep (se 1 (by rfl) ⟨940409, by rfl⟩ : syracuseStep 1253879 = 1880819) B1880819
theorem B369545 : Blo 243817 369545 := bstep (se 2 (by rfl) ⟨138579, by rfl⟩ : syracuseStep 369545 = 277159) B277159
theorem B369599 : Blo 243817 369599 := bstep (se 1 (by rfl) ⟨277199, by rfl⟩ : syracuseStep 369599 = 554399) B554399
theorem B369647 : Blo 243817 369647 := bstep (se 1 (by rfl) ⟨277235, by rfl⟩ : syracuseStep 369647 = 554471) B554471
theorem B370601 : Blo 243817 370601 := bstep (se 2 (by rfl) ⟨138975, by rfl⟩ : syracuseStep 370601 = 277951) B277951
theorem B13019075 : Blo 243817 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B829871 : Blo 243817 829871 := bstep (se 1 (by rfl) ⟨622403, by rfl⟩ : syracuseStep 829871 = 1244807) B1244807
theorem B371711 : Blo 243817 371711 := bstep (se 1 (by rfl) ⟨278783, by rfl⟩ : syracuseStep 371711 = 557567) B557567
theorem B5713537 : Blo 243817 5713537 := bstep (se 2 (by rfl) ⟨2142576, by rfl⟩ : syracuseStep 5713537 = 4285153) B4285153
theorem B831113 : Blo 243817 831113 := bstep (se 2 (by rfl) ⟨311667, by rfl⟩ : syracuseStep 831113 = 623335) B623335
theorem B930599 : Blo 243817 930599 := bstep (se 1 (by rfl) ⟨697949, by rfl⟩ : syracuseStep 930599 = 1395899) B1395899
theorem B1260157 : Blo 243817 1260157 := bstep (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) B472559
theorem B244379 : Blo 243817 244379 := bstep (se 1 (by rfl) ⟨183284, by rfl⟩ : syracuseStep 244379 = 366569) B366569
theorem B244431 : Blo 243817 244431 := bstep (se 1 (by rfl) ⟨183323, by rfl⟩ : syracuseStep 244431 = 366647) B366647
theorem B244475 : Blo 243817 244475 := bstep (se 1 (by rfl) ⟨183356, by rfl⟩ : syracuseStep 244475 = 366713) B366713
theorem B834407 : Blo 243817 834407 := bstep (se 1 (by rfl) ⟨625805, by rfl⟩ : syracuseStep 834407 = 1251611) B1251611
theorem B441455 : Blo 243817 441455 := bstep (se 1 (by rfl) ⟨331091, by rfl⟩ : syracuseStep 441455 = 662183) B662183
theorem B277663 : Blo 243817 277663 := bstep (se 1 (by rfl) ⟨208247, by rfl⟩ : syracuseStep 277663 = 416495) B416495
theorem B5356955 : Blo 243817 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B245147 : Blo 243817 245147 := bstep (se 1 (by rfl) ⟨183860, by rfl⟩ : syracuseStep 245147 = 367721) B367721
theorem B245407 : Blo 243817 245407 := bstep (se 1 (by rfl) ⟨184055, by rfl⟩ : syracuseStep 245407 = 368111) B368111
theorem B246511 : Blo 243817 246511 := bstep (se 1 (by rfl) ⟨184883, by rfl⟩ : syracuseStep 246511 = 369767) B369767
theorem B246783 : Blo 243817 246783 := bstep (se 1 (by rfl) ⟨185087, by rfl⟩ : syracuseStep 246783 = 370175) B370175
theorem B2541415 : Blo 243817 2541415 := bstep (se 1 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 2541415 = 3812123) B3812123
theorem B411689 : Blo 243817 411689 := bstep (se 2 (by rfl) ⟨154383, by rfl⟩ : syracuseStep 411689 = 308767) B308767
theorem B1690163 : Blo 243817 1690163 := bstep (se 1 (by rfl) ⟨1267622, by rfl⟩ : syracuseStep 1690163 = 2535245) B2535245
theorem B1985447 : Blo 243817 1985447 := bstep (se 1 (by rfl) ⟨1489085, by rfl⟩ : syracuseStep 1985447 = 2978171) B2978171
theorem B445375 : Blo 243817 445375 := bstep (se 1 (by rfl) ⟨334031, by rfl⟩ : syracuseStep 445375 = 668063) B668063
theorem B709021 : Blo 243817 709021 := bstep (se 3 (by rfl) ⟨132941, by rfl⟩ : syracuseStep 709021 = 265883) B265883
theorem B1890535 : Blo 243817 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B2808107 : Blo 243817 2808107 := bstep (se 1 (by rfl) ⟨2106080, by rfl⟩ : syracuseStep 2808107 = 4212161) B4212161
theorem B416191 : Blo 243817 416191 := bstep (se 1 (by rfl) ⟨312143, by rfl⟩ : syracuseStep 416191 = 624287) B624287
theorem B13458251 : Blo 243817 13458251 := bstep (se 1 (by rfl) ⟨10093688, by rfl⟩ : syracuseStep 13458251 = 20187377) B20187377
theorem B417919 : Blo 243817 417919 := bstep (se 1 (by rfl) ⟨313439, by rfl⟩ : syracuseStep 417919 = 626879) B626879
theorem B549089 : Blo 243817 549089 := bstep (se 2 (by rfl) ⟨205908, by rfl⟩ : syracuseStep 549089 = 411817) B411817
theorem B4284743 : Blo 243817 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B550025 : Blo 243817 550025 := bstep (se 2 (by rfl) ⟨206259, by rfl⟩ : syracuseStep 550025 = 412519) B412519
theorem B3172297 : Blo 243817 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B19098661 : Blo 243817 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B421583 : Blo 243817 421583 := bstep (se 1 (by rfl) ⟨316187, by rfl⟩ : syracuseStep 421583 = 632375) B632375
theorem B554849 : Blo 243817 554849 := bstep (se 2 (by rfl) ⟨208068, by rfl⟩ : syracuseStep 554849 = 416137) B416137
theorem B26147407 : Blo 243817 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B588713 : Blo 243817 588713 := bstep (se 2 (by rfl) ⟨220767, by rfl⟩ : syracuseStep 588713 = 441535) B441535
theorem B30736219 : Blo 243817 30736219 := bstep (se 1 (by rfl) ⟨23052164, by rfl⟩ : syracuseStep 30736219 = 46104329) B46104329
theorem B557225 : Blo 243817 557225 := bstep (se 2 (by rfl) ⟨208959, by rfl⟩ : syracuseStep 557225 = 417919) B417919
theorem B3408911 : Blo 243817 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B1049897 : Blo 243817 1049897 := bstep (se 2 (by rfl) ⟨393711, by rfl⟩ : syracuseStep 1049897 = 787423) B787423
theorem B395551 : Blo 243817 395551 := bstep (se 1 (by rfl) ⟨296663, by rfl⟩ : syracuseStep 395551 = 593327) B593327
theorem B1051127 : Blo 243817 1051127 := bstep (se 1 (by rfl) ⟨788345, by rfl⟩ : syracuseStep 1051127 = 1576691) B1576691
theorem B4229729 : Blo 243817 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B25464881 : Blo 243817 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B1872071 : Blo 243817 1872071 := bstep (se 1 (by rfl) ⟨1404053, by rfl⟩ : syracuseStep 1872071 = 2808107) B2808107
theorem B366059 : Blo 243817 366059 := bstep (se 1 (by rfl) ⟨274544, by rfl⟩ : syracuseStep 366059 = 549089) B549089
theorem B1054271 : Blo 243817 1054271 := bstep (se 1 (by rfl) ⟨790703, by rfl⟩ : syracuseStep 1054271 = 1581407) B1581407
theorem B366683 : Blo 243817 366683 := bstep (se 1 (by rfl) ⟨275012, by rfl⟩ : syracuseStep 366683 = 550025) B550025
theorem B1680209 : Blo 243817 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B369899 : Blo 243817 369899 := bstep (se 1 (by rfl) ⟨277424, by rfl⟩ : syracuseStep 369899 = 554849) B554849
theorem B370217 : Blo 243817 370217 := bstep (se 2 (by rfl) ⟨138831, by rfl⟩ : syracuseStep 370217 = 277663) B277663
theorem B1124221 : Blo 243817 1124221 := bstep (se 3 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 1124221 = 421583) B421583
theorem B830195 : Blo 243817 830195 := bstep (se 1 (by rfl) ⟨622646, by rfl⟩ : syracuseStep 830195 = 1245293) B1245293
theorem B274459 : Blo 243817 274459 := bstep (se 1 (by rfl) ⟨205844, by rfl⟩ : syracuseStep 274459 = 411689) B411689
theorem B1126775 : Blo 243817 1126775 := bstep (se 1 (by rfl) ⟨845081, by rfl⟩ : syracuseStep 1126775 = 1690163) B1690163
theorem B1323631 : Blo 243817 1323631 := bstep (se 1 (by rfl) ⟨992723, by rfl⟩ : syracuseStep 1323631 = 1985447) B1985447
theorem B3388553 : Blo 243817 3388553 := bstep (se 2 (by rfl) ⟨1270707, by rfl⟩ : syracuseStep 3388553 = 2541415) B2541415
theorem B834569 : Blo 243817 834569 := bstep (se 2 (by rfl) ⟨312963, by rfl⟩ : syracuseStep 834569 = 625927) B625927
theorem B245247 : Blo 243817 245247 := bstep (se 1 (by rfl) ⟨183935, by rfl⟩ : syracuseStep 245247 = 367871) B367871
theorem B7618049 : Blo 243817 7618049 := bstep (se 2 (by rfl) ⟨2856768, by rfl⟩ : syracuseStep 7618049 = 5713537) B5713537
theorem B245275 : Blo 243817 245275 := bstep (se 1 (by rfl) ⟨183956, by rfl⟩ : syracuseStep 245275 = 367913) B367913
theorem B245375 : Blo 243817 245375 := bstep (se 1 (by rfl) ⟨184031, by rfl⟩ : syracuseStep 245375 = 368063) B368063
theorem B2375333 : Blo 243817 2375333 := bstep (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) B445375
theorem B835919 : Blo 243817 835919 := bstep (se 1 (by rfl) ⟨626939, by rfl⟩ : syracuseStep 835919 = 1253879) B1253879
theorem B246363 : Blo 243817 246363 := bstep (se 1 (by rfl) ⟨184772, by rfl⟩ : syracuseStep 246363 = 369545) B369545
theorem B246399 : Blo 243817 246399 := bstep (se 1 (by rfl) ⟨184799, by rfl⟩ : syracuseStep 246399 = 369599) B369599
theorem B246431 : Blo 243817 246431 := bstep (se 1 (by rfl) ⟨184823, by rfl⟩ : syracuseStep 246431 = 369647) B369647
theorem B247067 : Blo 243817 247067 := bstep (se 1 (by rfl) ⟨185300, by rfl⟩ : syracuseStep 247067 = 370601) B370601
theorem B247807 : Blo 243817 247807 := bstep (se 1 (by rfl) ⟨185855, by rfl⟩ : syracuseStep 247807 = 371711) B371711
theorem B40981625 : Blo 243817 40981625 := bstep (se 2 (by rfl) ⟨15368109, by rfl⟩ : syracuseStep 40981625 = 30736219) B30736219
theorem B415847 : Blo 243817 415847 := bstep (se 1 (by rfl) ⟨311885, by rfl⟩ : syracuseStep 415847 = 623771) B623771
theorem B4708853 : Blo 243817 4708853 := bstep (se 5 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 4708853 = 441455) B441455
theorem B2317871 : Blo 243817 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B417791 : Blo 243817 417791 := bstep (se 1 (by rfl) ⟨313343, by rfl⟩ : syracuseStep 417791 = 626687) B626687
theorem B45703925 : Blo 243817 45703925 := bstep (se 5 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 45703925 = 4284743) B4284743
theorem B550043 : Blo 243817 550043 := bstep (se 1 (by rfl) ⟨412532, by rfl⟩ : syracuseStep 550043 = 825065) B825065
theorem B8972167 : Blo 243817 8972167 := bstep (se 1 (by rfl) ⟨6729125, by rfl⟩ : syracuseStep 8972167 = 13458251) B13458251
theorem B945361 : Blo 243817 945361 := bstep (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) B709021
theorem B8679383 : Blo 243817 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B553247 : Blo 243817 553247 := bstep (se 1 (by rfl) ⟨414935, by rfl⟩ : syracuseStep 553247 = 829871) B829871
theorem B554075 : Blo 243817 554075 := bstep (se 1 (by rfl) ⟨415556, by rfl⟩ : syracuseStep 554075 = 831113) B831113
theorem B1569901 : Blo 243817 1569901 := bstep (se 3 (by rfl) ⟨294356, by rfl⟩ : syracuseStep 1569901 = 588713) B588713
theorem B2520713 : Blo 243817 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B620399 : Blo 243817 620399 := bstep (se 1 (by rfl) ⟨465299, by rfl⟩ : syracuseStep 620399 = 930599) B930599
theorem B554921 : Blo 243817 554921 := bstep (se 2 (by rfl) ⟨208095, by rfl⟩ : syracuseStep 554921 = 416191) B416191
theorem B34863209 : Blo 243817 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B556271 : Blo 243817 556271 := bstep (se 1 (by rfl) ⟨417203, by rfl⟩ : syracuseStep 556271 = 834407) B834407
theorem B3571303 : Blo 243817 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B557279 : Blo 243817 557279 := bstep (se 1 (by rfl) ⟨417959, by rfl⟩ : syracuseStep 557279 = 835919) B835919
theorem B2819819 : Blo 243817 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B11962889 : Blo 243817 11962889 := bstep (se 2 (by rfl) ⟨4486083, by rfl⟩ : syracuseStep 11962889 = 8972167) B8972167
theorem B16976587 : Blo 243817 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B1248047 : Blo 243817 1248047 := bstep (se 1 (by rfl) ⟨936035, by rfl⟩ : syracuseStep 1248047 = 1872071) B1872071
theorem B527401 : Blo 243817 527401 := bstep (se 2 (by rfl) ⟨197775, by rfl⟩ : syracuseStep 527401 = 395551) B395551
theorem B1545247 : Blo 243817 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B365945 : Blo 243817 365945 := bstep (se 2 (by rfl) ⟨137229, by rfl⟩ : syracuseStep 365945 = 274459) B274459
theorem B1120139 : Blo 243817 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B366695 : Blo 243817 366695 := bstep (se 1 (by rfl) ⟨275021, by rfl⟩ : syracuseStep 366695 = 550043) B550043
theorem B368831 : Blo 243817 368831 := bstep (se 1 (by rfl) ⟨276623, by rfl⟩ : syracuseStep 368831 = 553247) B553247
theorem B369383 : Blo 243817 369383 := bstep (se 1 (by rfl) ⟨277037, by rfl⟩ : syracuseStep 369383 = 554075) B554075
theorem B1680475 : Blo 243817 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B369947 : Blo 243817 369947 := bstep (se 1 (by rfl) ⟨277460, by rfl⟩ : syracuseStep 369947 = 554921) B554921
theorem B23242139 : Blo 243817 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B4761737 : Blo 243817 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B370847 : Blo 243817 370847 := bstep (se 1 (by rfl) ⟨278135, by rfl⟩ : syracuseStep 370847 = 556271) B556271
theorem B1583555 : Blo 243817 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B371483 : Blo 243817 371483 := bstep (se 1 (by rfl) ⟨278612, by rfl⟩ : syracuseStep 371483 = 557225) B557225
theorem B2272607 : Blo 243817 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B699931 : Blo 243817 699931 := bstep (se 1 (by rfl) ⟨524948, by rfl⟩ : syracuseStep 699931 = 1049897) B1049897
theorem B700751 : Blo 243817 700751 := bstep (se 1 (by rfl) ⟨525563, by rfl⟩ : syracuseStep 700751 = 1051127) B1051127
theorem B244039 : Blo 243817 244039 := bstep (se 1 (by rfl) ⟨183029, by rfl⟩ : syracuseStep 244039 = 366059) B366059
theorem B702847 : Blo 243817 702847 := bstep (se 1 (by rfl) ⟨527135, by rfl⟩ : syracuseStep 702847 = 1054271) B1054271
theorem B244455 : Blo 243817 244455 := bstep (se 1 (by rfl) ⟨183341, by rfl⟩ : syracuseStep 244455 = 366683) B366683
theorem B277231 : Blo 243817 277231 := bstep (se 1 (by rfl) ⟨207923, by rfl⟩ : syracuseStep 277231 = 415847) B415847
theorem B278527 : Blo 243817 278527 := bstep (se 1 (by rfl) ⟨208895, by rfl⟩ : syracuseStep 278527 = 417791) B417791
theorem B246599 : Blo 243817 246599 := bstep (se 1 (by rfl) ⟨184949, by rfl⟩ : syracuseStep 246599 = 369899) B369899
theorem B246811 : Blo 243817 246811 := bstep (se 1 (by rfl) ⟨185108, by rfl⟩ : syracuseStep 246811 = 370217) B370217
theorem B5786255 : Blo 243817 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B413599 : Blo 243817 413599 := bstep (se 1 (by rfl) ⟨310199, by rfl⟩ : syracuseStep 413599 = 620399) B620399
theorem B3004733 : Blo 243817 3004733 := bstep (se 3 (by rfl) ⟨563387, by rfl⟩ : syracuseStep 3004733 = 1126775) B1126775
theorem B1498961 : Blo 243817 1498961 := bstep (se 2 (by rfl) ⟨562110, by rfl⟩ : syracuseStep 1498961 = 1124221) B1124221
theorem B27321083 : Blo 243817 27321083 := bstep (se 1 (by rfl) ⟨20490812, by rfl⟩ : syracuseStep 27321083 = 40981625) B40981625
theorem B3139235 : Blo 243817 3139235 := bstep (se 1 (by rfl) ⟨2354426, by rfl⟩ : syracuseStep 3139235 = 4708853) B4708853
theorem B30469283 : Blo 243817 30469283 := bstep (se 1 (by rfl) ⟨22851962, by rfl⟩ : syracuseStep 30469283 = 45703925) B45703925
theorem B1764841 : Blo 243817 1764841 := bstep (se 2 (by rfl) ⟨661815, by rfl⟩ : syracuseStep 1764841 = 1323631) B1323631
theorem B5041925 : Blo 243817 5041925 := bstep (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) B945361
theorem B2093201 : Blo 243817 2093201 := bstep (se 2 (by rfl) ⟨784950, by rfl⟩ : syracuseStep 2093201 = 1569901) B1569901
theorem B553463 : Blo 243817 553463 := bstep (se 1 (by rfl) ⟨415097, by rfl⟩ : syracuseStep 553463 = 830195) B830195
theorem B2259035 : Blo 243817 2259035 := bstep (se 1 (by rfl) ⟨1694276, by rfl⟩ : syracuseStep 2259035 = 3388553) B3388553
theorem B556379 : Blo 243817 556379 := bstep (se 1 (by rfl) ⟨417284, by rfl⟩ : syracuseStep 556379 = 834569) B834569
theorem B5078699 : Blo 243817 5078699 := bstep (se 1 (by rfl) ⟨3809024, by rfl⟩ : syracuseStep 5078699 = 7618049) B7618049
theorem B1868669 : Blo 243817 1868669 := bstep (se 3 (by rfl) ⟨350375, by rfl⟩ : syracuseStep 1868669 = 700751) B700751
theorem B1515071 : Blo 243817 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B368975 : Blo 243817 368975 := bstep (se 1 (by rfl) ⟨276731, by rfl⟩ : syracuseStep 368975 = 553463) B553463
theorem B369641 : Blo 243817 369641 := bstep (se 2 (by rfl) ⟨138615, by rfl⟩ : syracuseStep 369641 = 277231) B277231
theorem B370919 : Blo 243817 370919 := bstep (se 1 (by rfl) ⟨278189, by rfl⟩ : syracuseStep 370919 = 556379) B556379
theorem B3385799 : Blo 243817 3385799 := bstep (se 1 (by rfl) ⟨2539349, by rfl⟩ : syracuseStep 3385799 = 5078699) B5078699
theorem B371369 : Blo 243817 371369 := bstep (se 2 (by rfl) ⟨139263, by rfl⟩ : syracuseStep 371369 = 278527) B278527
theorem B371519 : Blo 243817 371519 := bstep (se 1 (by rfl) ⟨278639, by rfl⟩ : syracuseStep 371519 = 557279) B557279
theorem B2240633 : Blo 243817 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B7975259 : Blo 243817 7975259 := bstep (se 1 (by rfl) ⟨5981444, by rfl⟩ : syracuseStep 7975259 = 11962889) B11962889
theorem B832031 : Blo 243817 832031 := bstep (se 1 (by rfl) ⟨624023, by rfl⟩ : syracuseStep 832031 = 1248047) B1248047
theorem B243963 : Blo 243817 243963 := bstep (se 1 (by rfl) ⟨182972, by rfl⟩ : syracuseStep 243963 = 365945) B365945
theorem B703201 : Blo 243817 703201 := bstep (se 2 (by rfl) ⟨263700, by rfl⟩ : syracuseStep 703201 = 527401) B527401
theorem B244463 : Blo 243817 244463 := bstep (se 1 (by rfl) ⟨183347, by rfl⟩ : syracuseStep 244463 = 366695) B366695
theorem B7519517 : Blo 243817 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B933241 : Blo 243817 933241 := bstep (se 2 (by rfl) ⟨349965, by rfl⟩ : syracuseStep 933241 = 699931) B699931
theorem B999307 : Blo 243817 999307 := bstep (se 1 (by rfl) ⟨749480, by rfl⟩ : syracuseStep 999307 = 1498961) B1498961
theorem B245887 : Blo 243817 245887 := bstep (se 1 (by rfl) ⟨184415, by rfl⟩ : syracuseStep 245887 = 368831) B368831
theorem B246255 : Blo 243817 246255 := bstep (se 1 (by rfl) ⟨184691, by rfl⟩ : syracuseStep 246255 = 369383) B369383
theorem B8012621 : Blo 243817 8012621 := bstep (se 3 (by rfl) ⟨1502366, by rfl⟩ : syracuseStep 8012621 = 3004733) B3004733
theorem B246631 : Blo 243817 246631 := bstep (se 1 (by rfl) ⟨184973, by rfl⟩ : syracuseStep 246631 = 369947) B369947
theorem B247231 : Blo 243817 247231 := bstep (se 1 (by rfl) ⟨185423, by rfl⟩ : syracuseStep 247231 = 370847) B370847
theorem B247655 : Blo 243817 247655 := bstep (se 1 (by rfl) ⟨185741, by rfl⟩ : syracuseStep 247655 = 371483) B371483
theorem B3361283 : Blo 243817 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B1395467 : Blo 243817 1395467 := bstep (se 1 (by rfl) ⟨1046600, by rfl⟩ : syracuseStep 1395467 = 2093201) B2093201
theorem B937129 : Blo 243817 937129 := bstep (se 2 (by rfl) ⟨351423, by rfl⟩ : syracuseStep 937129 = 702847) B702847
theorem B3857503 : Blo 243817 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B22635449 : Blo 243817 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B746759 : Blo 243817 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B2353121 : Blo 243817 2353121 := bstep (se 2 (by rfl) ⟨882420, by rfl⟩ : syracuseStep 2353121 = 1764841) B1764841
theorem B551465 : Blo 243817 551465 := bstep (se 2 (by rfl) ⟨206799, by rfl⟩ : syracuseStep 551465 = 413599) B413599
theorem B18214055 : Blo 243817 18214055 := bstep (se 1 (by rfl) ⟨13660541, by rfl⟩ : syracuseStep 18214055 = 27321083) B27321083
theorem B15494759 : Blo 243817 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B2092823 : Blo 243817 2092823 := bstep (se 1 (by rfl) ⟨1569617, by rfl⟩ : syracuseStep 2092823 = 3139235) B3139235
theorem B4222813 : Blo 243817 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B2060329 : Blo 243817 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B3174491 : Blo 243817 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B20312855 : Blo 243817 20312855 := bstep (se 1 (by rfl) ⟨15234641, by rfl⟩ : syracuseStep 20312855 = 30469283) B30469283
theorem B1506023 : Blo 243817 1506023 := bstep (se 1 (by rfl) ⟨1129517, by rfl⟩ : syracuseStep 1506023 = 2259035) B2259035
theorem B5341747 : Blo 243817 5341747 := bstep (se 1 (by rfl) ⟨4006310, by rfl⟩ : syracuseStep 5341747 = 8012621) B8012621
theorem B1245779 : Blo 243817 1245779 := bstep (se 1 (by rfl) ⟨934334, by rfl⟩ : syracuseStep 1245779 = 1868669) B1868669
theorem B1249505 : Blo 243817 1249505 := bstep (se 2 (by rfl) ⟨468564, by rfl⟩ : syracuseStep 1249505 = 937129) B937129
theorem B497839 : Blo 243817 497839 := bstep (se 1 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 497839 = 746759) B746759
theorem B367643 : Blo 243817 367643 := bstep (se 1 (by rfl) ⟨275732, by rfl⟩ : syracuseStep 367643 = 551465) B551465
theorem B10329839 : Blo 243817 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B5316839 : Blo 243817 5316839 := bstep (se 1 (by rfl) ⟨3987629, by rfl⟩ : syracuseStep 5316839 = 7975259) B7975259
theorem B13541903 : Blo 243817 13541903 := bstep (se 1 (by rfl) ⟨10156427, by rfl⟩ : syracuseStep 13541903 = 20312855) B20312855
theorem B4040189 : Blo 243817 4040189 := bstep (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) B1515071
theorem B8465309 : Blo 243817 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B5975021 : Blo 243817 5975021 := bstep (se 3 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 5975021 = 2240633) B2240633
theorem B2240855 : Blo 243817 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B930311 : Blo 243817 930311 := bstep (se 1 (by rfl) ⟨697733, by rfl⟩ : syracuseStep 930311 = 1395467) B1395467
theorem B245983 : Blo 243817 245983 := bstep (se 1 (by rfl) ⟨184487, by rfl⟩ : syracuseStep 245983 = 368975) B368975
theorem B15090299 : Blo 243817 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B246427 : Blo 243817 246427 := bstep (se 1 (by rfl) ⟨184820, by rfl⟩ : syracuseStep 246427 = 369641) B369641
theorem B247279 : Blo 243817 247279 := bstep (se 1 (by rfl) ⟨185459, by rfl⟩ : syracuseStep 247279 = 370919) B370919
theorem B247579 : Blo 243817 247579 := bstep (se 1 (by rfl) ⟨185684, by rfl⟩ : syracuseStep 247579 = 371369) B371369
theorem B247679 : Blo 243817 247679 := bstep (se 1 (by rfl) ⟨185759, by rfl⟩ : syracuseStep 247679 = 371519) B371519
theorem B12142703 : Blo 243817 12142703 := bstep (se 1 (by rfl) ⟨9107027, by rfl⟩ : syracuseStep 12142703 = 18214055) B18214055
theorem B1395215 : Blo 243817 1395215 := bstep (se 1 (by rfl) ⟨1046411, by rfl⟩ : syracuseStep 1395215 = 2092823) B2092823
theorem B937601 : Blo 243817 937601 := bstep (se 2 (by rfl) ⟨351600, by rfl⟩ : syracuseStep 937601 = 703201) B703201
theorem B1004015 : Blo 243817 1004015 := bstep (se 1 (by rfl) ⟨753011, by rfl⟩ : syracuseStep 1004015 = 1506023) B1506023
theorem B5329637 : Blo 243817 5329637 := bstep (se 4 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 5329637 = 999307) B999307
theorem B5630417 : Blo 243817 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B2747105 : Blo 243817 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B1568747 : Blo 243817 1568747 := bstep (se 1 (by rfl) ⟨1176560, by rfl⟩ : syracuseStep 1568747 = 2353121) B2353121
theorem B2257199 : Blo 243817 2257199 := bstep (se 1 (by rfl) ⟨1692899, by rfl⟩ : syracuseStep 2257199 = 3385799) B3385799
theorem B554687 : Blo 243817 554687 := bstep (se 1 (by rfl) ⟨416015, by rfl⟩ : syracuseStep 554687 = 832031) B832031
theorem B5143337 : Blo 243817 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B1244321 : Blo 243817 1244321 := bstep (se 2 (by rfl) ⟨466620, by rfl⟩ : syracuseStep 1244321 = 933241) B933241
theorem B5013011 : Blo 243817 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B10060199 : Blo 243817 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B8095135 : Blo 243817 8095135 := bstep (se 1 (by rfl) ⟨6071351, by rfl⟩ : syracuseStep 8095135 = 12142703) B12142703
theorem B625067 : Blo 243817 625067 := bstep (se 1 (by rfl) ⟨468800, by rfl⟩ : syracuseStep 625067 = 937601) B937601
theorem B6886559 : Blo 243817 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B3544559 : Blo 243817 3544559 := bstep (se 1 (by rfl) ⟨2658419, by rfl⟩ : syracuseStep 3544559 = 5316839) B5316839
theorem B2693459 : Blo 243817 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B5643539 : Blo 243817 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B663785 : Blo 243817 663785 := bstep (se 2 (by rfl) ⟨248919, by rfl⟩ : syracuseStep 663785 = 497839) B497839
theorem B369791 : Blo 243817 369791 := bstep (se 1 (by rfl) ⟨277343, by rfl⟩ : syracuseStep 369791 = 554687) B554687
theorem B829547 : Blo 243817 829547 := bstep (se 1 (by rfl) ⟨622160, by rfl⟩ : syracuseStep 829547 = 1244321) B1244321
theorem B830519 : Blo 243817 830519 := bstep (se 1 (by rfl) ⟨622889, by rfl⟩ : syracuseStep 830519 = 1245779) B1245779
theorem B7122329 : Blo 243817 7122329 := bstep (se 2 (by rfl) ⟨2670873, by rfl⟩ : syracuseStep 7122329 = 5341747) B5341747
theorem B930143 : Blo 243817 930143 := bstep (se 1 (by rfl) ⟨697607, by rfl⟩ : syracuseStep 930143 = 1395215) B1395215
theorem B833003 : Blo 243817 833003 := bstep (se 1 (by rfl) ⟨624752, by rfl⟩ : syracuseStep 833003 = 1249505) B1249505
theorem B669343 : Blo 243817 669343 := bstep (se 1 (by rfl) ⟨502007, by rfl⟩ : syracuseStep 669343 = 1004015) B1004015
theorem B3553091 : Blo 243817 3553091 := bstep (se 1 (by rfl) ⟨2664818, by rfl⟩ : syracuseStep 3553091 = 5329637) B5329637
theorem B245095 : Blo 243817 245095 := bstep (se 1 (by rfl) ⟨183821, by rfl⟩ : syracuseStep 245095 = 367643) B367643
theorem B9027935 : Blo 243817 9027935 := bstep (se 1 (by rfl) ⟨6770951, by rfl⟩ : syracuseStep 9027935 = 13541903) B13541903
theorem B3753611 : Blo 243817 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B3983347 : Blo 243817 3983347 := bstep (se 1 (by rfl) ⟨2987510, by rfl⟩ : syracuseStep 3983347 = 5975021) B5975021
theorem B1493903 : Blo 243817 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B3428891 : Blo 243817 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B1831403 : Blo 243817 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B1045831 : Blo 243817 1045831 := bstep (se 1 (by rfl) ⟨784373, by rfl⟩ : syracuseStep 1045831 = 1568747) B1568747
theorem B1504799 : Blo 243817 1504799 := bstep (se 1 (by rfl) ⟨1128599, by rfl⟩ : syracuseStep 1504799 = 2257199) B2257199
theorem B620207 : Blo 243817 620207 := bstep (se 1 (by rfl) ⟨465155, by rfl⟩ : syracuseStep 620207 = 930311) B930311
theorem B3342007 : Blo 243817 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B5311129 : Blo 243817 5311129 := bstep (se 2 (by rfl) ⟨1991673, by rfl⟩ : syracuseStep 5311129 = 3983347) B3983347
theorem B2363039 : Blo 243817 2363039 := bstep (se 1 (by rfl) ⟨1772279, by rfl⟩ : syracuseStep 2363039 = 3544559) B3544559
theorem B7182557 : Blo 243817 7182557 := bstep (se 3 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 7182557 = 2693459) B2693459
theorem B892457 : Blo 243817 892457 := bstep (se 2 (by rfl) ⟨334671, by rfl⟩ : syracuseStep 892457 = 669343) B669343
theorem B1220935 : Blo 243817 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B2368727 : Blo 243817 2368727 := bstep (se 1 (by rfl) ⟨1776545, by rfl⟩ : syracuseStep 2368727 = 3553091) B3553091
theorem B2502407 : Blo 243817 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B10793513 : Blo 243817 10793513 := bstep (se 2 (by rfl) ⟨4047567, by rfl⟩ : syracuseStep 10793513 = 8095135) B8095135
theorem B995935 : Blo 243817 995935 := bstep (se 1 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 995935 = 1493903) B1493903
theorem B18364157 : Blo 243817 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B442523 : Blo 243817 442523 := bstep (se 1 (by rfl) ⟨331892, by rfl⟩ : syracuseStep 442523 = 663785) B663785
theorem B246527 : Blo 243817 246527 := bstep (se 1 (by rfl) ⟨184895, by rfl⟩ : syracuseStep 246527 = 369791) B369791
theorem B1394441 : Blo 243817 1394441 := bstep (se 2 (by rfl) ⟨522915, by rfl⟩ : syracuseStep 1394441 = 1045831) B1045831
theorem B1003199 : Blo 243817 1003199 := bstep (se 1 (by rfl) ⟨752399, by rfl⟩ : syracuseStep 1003199 = 1504799) B1504799
theorem B413471 : Blo 243817 413471 := bstep (se 1 (by rfl) ⟨310103, by rfl⟩ : syracuseStep 413471 = 620207) B620207
theorem B6018623 : Blo 243817 6018623 := bstep (se 1 (by rfl) ⟨4513967, by rfl⟩ : syracuseStep 6018623 = 9027935) B9027935
theorem B6706799 : Blo 243817 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B416711 : Blo 243817 416711 := bstep (se 1 (by rfl) ⟨312533, by rfl⟩ : syracuseStep 416711 = 625067) B625067
theorem B2285927 : Blo 243817 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B3762359 : Blo 243817 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B553031 : Blo 243817 553031 := bstep (se 1 (by rfl) ⟨414773, by rfl⟩ : syracuseStep 553031 = 829547) B829547
theorem B553679 : Blo 243817 553679 := bstep (se 1 (by rfl) ⟨415259, by rfl⟩ : syracuseStep 553679 = 830519) B830519
theorem B4748219 : Blo 243817 4748219 := bstep (se 1 (by rfl) ⟨3561164, by rfl⟩ : syracuseStep 4748219 = 7122329) B7122329
theorem B620095 : Blo 243817 620095 := bstep (se 1 (by rfl) ⟨465071, by rfl⟩ : syracuseStep 620095 = 930143) B930143
theorem B555335 : Blo 243817 555335 := bstep (se 1 (by rfl) ⟨416501, by rfl⟩ : syracuseStep 555335 = 833003) B833003
theorem B4456009 : Blo 243817 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B295015 : Blo 243817 295015 := bstep (se 1 (by rfl) ⟨221261, by rfl⟩ : syracuseStep 295015 = 442523) B442523
theorem B1575359 : Blo 243817 1575359 := bstep (se 1 (by rfl) ⟨1181519, by rfl⟩ : syracuseStep 1575359 = 2363039) B2363039
theorem B7081505 : Blo 243817 7081505 := bstep (se 2 (by rfl) ⟨2655564, by rfl⟩ : syracuseStep 7081505 = 5311129) B5311129
theorem B4788371 : Blo 243817 4788371 := bstep (se 1 (by rfl) ⟨3591278, by rfl⟩ : syracuseStep 4788371 = 7182557) B7182557
theorem B594971 : Blo 243817 594971 := bstep (se 1 (by rfl) ⟨446228, by rfl⟩ : syracuseStep 594971 = 892457) B892457
theorem B1579151 : Blo 243817 1579151 := bstep (se 1 (by rfl) ⟨1184363, by rfl⟩ : syracuseStep 1579151 = 2368727) B2368727
theorem B826793 : Blo 243817 826793 := bstep (se 2 (by rfl) ⟨310047, by rfl⟩ : syracuseStep 826793 = 620095) B620095
theorem B368687 : Blo 243817 368687 := bstep (se 1 (by rfl) ⟨276515, by rfl⟩ : syracuseStep 368687 = 553031) B553031
theorem B369119 : Blo 243817 369119 := bstep (se 1 (by rfl) ⟨276839, by rfl⟩ : syracuseStep 369119 = 553679) B553679
theorem B370223 : Blo 243817 370223 := bstep (se 1 (by rfl) ⟨277667, by rfl⟩ : syracuseStep 370223 = 555335) B555335
theorem B5941345 : Blo 243817 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B929627 : Blo 243817 929627 := bstep (se 1 (by rfl) ⟨697220, by rfl⟩ : syracuseStep 929627 = 1394441) B1394441
theorem B275647 : Blo 243817 275647 := bstep (se 1 (by rfl) ⟨206735, by rfl⟩ : syracuseStep 275647 = 413471) B413471
theorem B4012415 : Blo 243817 4012415 := bstep (se 1 (by rfl) ⟨3009311, by rfl⟩ : syracuseStep 4012415 = 6018623) B6018623
theorem B4471199 : Blo 243817 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B277807 : Blo 243817 277807 := bstep (se 1 (by rfl) ⟨208355, by rfl⟩ : syracuseStep 277807 = 416711) B416711
theorem B1523951 : Blo 243817 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B1327913 : Blo 243817 1327913 := bstep (se 2 (by rfl) ⟨497967, by rfl⟩ : syracuseStep 1327913 = 995935) B995935
theorem B2508239 : Blo 243817 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B7195675 : Blo 243817 7195675 := bstep (se 1 (by rfl) ⟨5396756, by rfl⟩ : syracuseStep 7195675 = 10793513) B10793513
theorem B3165479 : Blo 243817 3165479 := bstep (se 1 (by rfl) ⟨2374109, by rfl⟩ : syracuseStep 3165479 = 4748219) B4748219
theorem B12242771 : Blo 243817 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B2675197 : Blo 243817 2675197 := bstep (se 3 (by rfl) ⟨501599, by rfl⟩ : syracuseStep 2675197 = 1003199) B1003199
theorem B1627913 : Blo 243817 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B1668271 : Blo 243817 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B393353 : Blo 243817 393353 := bstep (se 2 (by rfl) ⟨147507, by rfl⟩ : syracuseStep 393353 = 295015) B295015
theorem B1015967 : Blo 243817 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B885275 : Blo 243817 885275 := bstep (se 1 (by rfl) ⟨663956, by rfl⟩ : syracuseStep 885275 = 1327913) B1327913
theorem B1672159 : Blo 243817 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B1050239 : Blo 243817 1050239 := bstep (se 1 (by rfl) ⟨787679, by rfl⟩ : syracuseStep 1050239 = 1575359) B1575359
theorem B4721003 : Blo 243817 4721003 := bstep (se 1 (by rfl) ⟨3540752, by rfl⟩ : syracuseStep 4721003 = 7081505) B7081505
theorem B8161847 : Blo 243817 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B396647 : Blo 243817 396647 := bstep (se 1 (by rfl) ⟨297485, by rfl⟩ : syracuseStep 396647 = 594971) B594971
theorem B1085275 : Blo 243817 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B1052767 : Blo 243817 1052767 := bstep (se 1 (by rfl) ⟨789575, by rfl⟩ : syracuseStep 1052767 = 1579151) B1579151
theorem B367529 : Blo 243817 367529 := bstep (se 2 (by rfl) ⟨137823, by rfl⟩ : syracuseStep 367529 = 275647) B275647
theorem B370409 : Blo 243817 370409 := bstep (se 2 (by rfl) ⟨138903, by rfl⟩ : syracuseStep 370409 = 277807) B277807
theorem B2110319 : Blo 243817 2110319 := bstep (se 1 (by rfl) ⟨1582739, by rfl⟩ : syracuseStep 2110319 = 3165479) B3165479
theorem B3192247 : Blo 243817 3192247 := bstep (se 1 (by rfl) ⟨2394185, by rfl⟩ : syracuseStep 3192247 = 4788371) B4788371
theorem B245791 : Blo 243817 245791 := bstep (se 1 (by rfl) ⟨184343, by rfl⟩ : syracuseStep 245791 = 368687) B368687
theorem B246079 : Blo 243817 246079 := bstep (se 1 (by rfl) ⟨184559, by rfl⟩ : syracuseStep 246079 = 369119) B369119
theorem B246815 : Blo 243817 246815 := bstep (se 1 (by rfl) ⟨185111, by rfl⟩ : syracuseStep 246815 = 370223) B370223
theorem B2674943 : Blo 243817 2674943 := bstep (se 1 (by rfl) ⟨2006207, by rfl⟩ : syracuseStep 2674943 = 4012415) B4012415
theorem B7921793 : Blo 243817 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B9594233 : Blo 243817 9594233 := bstep (se 2 (by rfl) ⟨3597837, by rfl⟩ : syracuseStep 9594233 = 7195675) B7195675
theorem B551195 : Blo 243817 551195 := bstep (se 1 (by rfl) ⟨413396, by rfl⟩ : syracuseStep 551195 = 826793) B826793
theorem B3566929 : Blo 243817 3566929 := bstep (se 2 (by rfl) ⟨1337598, by rfl⟩ : syracuseStep 3566929 = 2675197) B2675197
theorem B2224361 : Blo 243817 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B619751 : Blo 243817 619751 := bstep (se 1 (by rfl) ⟨464813, by rfl⟩ : syracuseStep 619751 = 929627) B929627
theorem B2980799 : Blo 243817 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B262235 : Blo 243817 262235 := bstep (se 1 (by rfl) ⟨196676, by rfl⟩ : syracuseStep 262235 = 393353) B393353
theorem B590183 : Blo 243817 590183 := bstep (se 1 (by rfl) ⟨442637, by rfl⟩ : syracuseStep 590183 = 885275) B885275
theorem B2229545 : Blo 243817 2229545 := bstep (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) B1672159
theorem B3147335 : Blo 243817 3147335 := bstep (se 1 (by rfl) ⟨2360501, by rfl⟩ : syracuseStep 3147335 = 4721003) B4721003
theorem B5441231 : Blo 243817 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B264431 : Blo 243817 264431 := bstep (se 1 (by rfl) ⟨198323, by rfl⟩ : syracuseStep 264431 = 396647) B396647
theorem B4755905 : Blo 243817 4755905 := bstep (se 2 (by rfl) ⟨1783464, by rfl⟩ : syracuseStep 4755905 = 3566929) B3566929
theorem B1447033 : Blo 243817 1447033 := bstep (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) B1085275
theorem B5281195 : Blo 243817 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B6396155 : Blo 243817 6396155 := bstep (se 1 (by rfl) ⟨4797116, by rfl⟩ : syracuseStep 6396155 = 9594233) B9594233
theorem B367463 : Blo 243817 367463 := bstep (se 1 (by rfl) ⟨275597, by rfl⟩ : syracuseStep 367463 = 551195) B551195
theorem B1482907 : Blo 243817 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B700159 : Blo 243817 700159 := bstep (se 1 (by rfl) ⟨525119, by rfl⟩ : syracuseStep 700159 = 1050239) B1050239
theorem B1783295 : Blo 243817 1783295 := bstep (se 1 (by rfl) ⟨1337471, by rfl⟩ : syracuseStep 1783295 = 2674943) B2674943
theorem B245019 : Blo 243817 245019 := bstep (se 1 (by rfl) ⟨183764, by rfl⟩ : syracuseStep 245019 = 367529) B367529
theorem B246939 : Blo 243817 246939 := bstep (se 1 (by rfl) ⟨185204, by rfl⟩ : syracuseStep 246939 = 370409) B370409
theorem B413167 : Blo 243817 413167 := bstep (se 1 (by rfl) ⟨309875, by rfl⟩ : syracuseStep 413167 = 619751) B619751
theorem B1987199 : Blo 243817 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B2709245 : Blo 243817 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B1403689 : Blo 243817 1403689 := bstep (se 2 (by rfl) ⟨526383, by rfl⟩ : syracuseStep 1403689 = 1052767) B1052767
theorem B4256329 : Blo 243817 4256329 := bstep (se 2 (by rfl) ⟨1596123, by rfl⟩ : syracuseStep 4256329 = 3192247) B3192247
theorem B1406879 : Blo 243817 1406879 := bstep (se 1 (by rfl) ⟨1055159, by rfl⟩ : syracuseStep 1406879 = 2110319) B2110319
theorem B393455 : Blo 243817 393455 := bstep (se 1 (by rfl) ⟨295091, by rfl⟩ : syracuseStep 393455 = 590183) B590183
theorem B2098223 : Blo 243817 2098223 := bstep (se 1 (by rfl) ⟨1573667, by rfl⟩ : syracuseStep 2098223 = 3147335) B3147335
theorem B1871585 : Blo 243817 1871585 := bstep (se 2 (by rfl) ⟨701844, by rfl⟩ : syracuseStep 1871585 = 1403689) B1403689
theorem B4264103 : Blo 243817 4264103 := bstep (se 1 (by rfl) ⟨3198077, by rfl⟩ : syracuseStep 4264103 = 6396155) B6396155
theorem B5675105 : Blo 243817 5675105 := bstep (se 2 (by rfl) ⟨2128164, by rfl⟩ : syracuseStep 5675105 = 4256329) B4256329
theorem B1188863 : Blo 243817 1188863 := bstep (se 1 (by rfl) ⟨891647, by rfl⟩ : syracuseStep 1188863 = 1783295) B1783295
theorem B1977209 : Blo 243817 1977209 := bstep (se 2 (by rfl) ⟨741453, by rfl⟩ : syracuseStep 1977209 = 1482907) B1482907
theorem B699293 : Blo 243817 699293 := bstep (se 3 (by rfl) ⟨131117, by rfl⟩ : syracuseStep 699293 = 262235) B262235
theorem B1486363 : Blo 243817 1486363 := bstep (se 1 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 1486363 = 2229545) B2229545
theorem B1324799 : Blo 243817 1324799 := bstep (se 1 (by rfl) ⟨993599, by rfl⟩ : syracuseStep 1324799 = 1987199) B1987199
theorem B244975 : Blo 243817 244975 := bstep (se 1 (by rfl) ⟨183731, by rfl⟩ : syracuseStep 244975 = 367463) B367463
theorem B7224653 : Blo 243817 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B933545 : Blo 243817 933545 := bstep (se 2 (by rfl) ⟨350079, by rfl⟩ : syracuseStep 933545 = 700159) B700159
theorem B705149 : Blo 243817 705149 := bstep (se 3 (by rfl) ⟨132215, by rfl⟩ : syracuseStep 705149 = 264431) B264431
theorem B937919 : Blo 243817 937919 := bstep (se 1 (by rfl) ⟨703439, by rfl⟩ : syracuseStep 937919 = 1406879) B1406879
theorem B3627487 : Blo 243817 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B3170603 : Blo 243817 3170603 := bstep (se 1 (by rfl) ⟨2377952, by rfl⟩ : syracuseStep 3170603 = 4755905) B4755905
theorem B550889 : Blo 243817 550889 := bstep (se 2 (by rfl) ⟨206583, by rfl⟩ : syracuseStep 550889 = 413167) B413167
theorem B1929377 : Blo 243817 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B7041593 : Blo 243817 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B5145005 : Blo 243817 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B1049213 : Blo 243817 1049213 := bstep (se 3 (by rfl) ⟨196727, by rfl⟩ : syracuseStep 1049213 = 393455) B393455
theorem B1247723 : Blo 243817 1247723 := bstep (se 1 (by rfl) ⟨935792, by rfl⟩ : syracuseStep 1247723 = 1871585) B1871585
theorem B625279 : Blo 243817 625279 := bstep (se 1 (by rfl) ⟨468959, by rfl⟩ : syracuseStep 625279 = 937919) B937919
theorem B792575 : Blo 243817 792575 := bstep (se 1 (by rfl) ⟨594431, by rfl⟩ : syracuseStep 792575 = 1188863) B1188863
theorem B367259 : Blo 243817 367259 := bstep (se 1 (by rfl) ⟨275444, by rfl⟩ : syracuseStep 367259 = 550889) B550889
theorem B1318139 : Blo 243817 1318139 := bstep (se 1 (by rfl) ⟨988604, by rfl⟩ : syracuseStep 1318139 = 1977209) B1977209
theorem B4694395 : Blo 243817 4694395 := bstep (se 1 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 4694395 = 7041593) B7041593
theorem B470099 : Blo 243817 470099 := bstep (se 1 (by rfl) ⟨352574, by rfl⟩ : syracuseStep 470099 = 705149) B705149
theorem B19346597 : Blo 243817 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B1981817 : Blo 243817 1981817 := bstep (se 2 (by rfl) ⟨743181, by rfl⟩ : syracuseStep 1981817 = 1486363) B1486363
theorem B2113735 : Blo 243817 2113735 := bstep (se 1 (by rfl) ⟨1585301, by rfl⟩ : syracuseStep 2113735 = 3170603) B3170603
theorem B1398815 : Blo 243817 1398815 := bstep (se 1 (by rfl) ⟨1049111, by rfl⟩ : syracuseStep 1398815 = 2098223) B2098223
theorem B2842735 : Blo 243817 2842735 := bstep (se 1 (by rfl) ⟨2132051, by rfl⟩ : syracuseStep 2842735 = 4264103) B4264103
theorem B15133613 : Blo 243817 15133613 := bstep (se 3 (by rfl) ⟨2837552, by rfl⟩ : syracuseStep 15133613 = 5675105) B5675105
theorem B1864781 : Blo 243817 1864781 := bstep (se 3 (by rfl) ⟨349646, by rfl⟩ : syracuseStep 1864781 = 699293) B699293
theorem B883199 : Blo 243817 883199 := bstep (se 1 (by rfl) ⟨662399, by rfl⟩ : syracuseStep 883199 = 1324799) B1324799
theorem B4816435 : Blo 243817 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B622363 : Blo 243817 622363 := bstep (se 1 (by rfl) ⟨466772, by rfl⟩ : syracuseStep 622363 = 933545) B933545
theorem B2818313 : Blo 243817 2818313 := bstep (se 2 (by rfl) ⟨1056867, by rfl⟩ : syracuseStep 2818313 = 2113735) B2113735
theorem B6259193 : Blo 243817 6259193 := bstep (se 2 (by rfl) ⟨2347197, by rfl⟩ : syracuseStep 6259193 = 4694395) B4694395
theorem B528383 : Blo 243817 528383 := bstep (se 1 (by rfl) ⟨396287, by rfl⟩ : syracuseStep 528383 = 792575) B792575
theorem B1321211 : Blo 243817 1321211 := bstep (se 1 (by rfl) ⟨990908, by rfl⟩ : syracuseStep 1321211 = 1981817) B1981817
theorem B829817 : Blo 243817 829817 := bstep (se 2 (by rfl) ⟨311181, by rfl⟩ : syracuseStep 829817 = 622363) B622363
theorem B831815 : Blo 243817 831815 := bstep (se 1 (by rfl) ⟨623861, by rfl⟩ : syracuseStep 831815 = 1247723) B1247723
theorem B2797901 : Blo 243817 2797901 := bstep (se 3 (by rfl) ⟨524606, by rfl⟩ : syracuseStep 2797901 = 1049213) B1049213
theorem B833705 : Blo 243817 833705 := bstep (se 2 (by rfl) ⟨312639, by rfl⟩ : syracuseStep 833705 = 625279) B625279
theorem B932543 : Blo 243817 932543 := bstep (se 1 (by rfl) ⟨699407, by rfl⟩ : syracuseStep 932543 = 1398815) B1398815
theorem B244839 : Blo 243817 244839 := bstep (se 1 (by rfl) ⟨183629, by rfl⟩ : syracuseStep 244839 = 367259) B367259
theorem B313399 : Blo 243817 313399 := bstep (se 1 (by rfl) ⟨235049, by rfl⟩ : syracuseStep 313399 = 470099) B470099
theorem B40356301 : Blo 243817 40356301 := bstep (se 3 (by rfl) ⟨7566806, by rfl⟩ : syracuseStep 40356301 = 15133613) B15133613
theorem B12897731 : Blo 243817 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B3790313 : Blo 243817 3790313 := bstep (se 2 (by rfl) ⟨1421367, by rfl⟩ : syracuseStep 3790313 = 2842735) B2842735
theorem B13720013 : Blo 243817 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B878759 : Blo 243817 878759 := bstep (se 1 (by rfl) ⟨659069, by rfl⟩ : syracuseStep 878759 = 1318139) B1318139
theorem B1243187 : Blo 243817 1243187 := bstep (se 1 (by rfl) ⟨932390, by rfl⟩ : syracuseStep 1243187 = 1864781) B1864781
theorem B588799 : Blo 243817 588799 := bstep (se 1 (by rfl) ⟨441599, by rfl⟩ : syracuseStep 588799 = 883199) B883199
theorem B6421913 : Blo 243817 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B53808401 : Blo 243817 53808401 := bstep (se 2 (by rfl) ⟨20178150, by rfl⟩ : syracuseStep 53808401 = 40356301) B40356301
theorem B2526875 : Blo 243817 2526875 := bstep (se 1 (by rfl) ⟨1895156, by rfl⟩ : syracuseStep 2526875 = 3790313) B3790313
theorem B9146675 : Blo 243817 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B828791 : Blo 243817 828791 := bstep (se 1 (by rfl) ⟨621593, by rfl⟩ : syracuseStep 828791 = 1243187) B1243187
theorem B1878875 : Blo 243817 1878875 := bstep (se 1 (by rfl) ⟨1409156, by rfl⟩ : syracuseStep 1878875 = 2818313) B2818313
theorem B4172795 : Blo 243817 4172795 := bstep (se 1 (by rfl) ⟨3129596, by rfl⟩ : syracuseStep 4172795 = 6259193) B6259193
theorem B8598487 : Blo 243817 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B4281275 : Blo 243817 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B417865 : Blo 243817 417865 := bstep (se 2 (by rfl) ⟨156699, by rfl⟩ : syracuseStep 417865 = 313399) B313399
theorem B585839 : Blo 243817 585839 := bstep (se 1 (by rfl) ⟨439379, by rfl⟩ : syracuseStep 585839 = 878759) B878759
theorem B880807 : Blo 243817 880807 := bstep (se 1 (by rfl) ⟨660605, by rfl⟩ : syracuseStep 880807 = 1321211) B1321211
theorem B553211 : Blo 243817 553211 := bstep (se 1 (by rfl) ⟨414908, by rfl⟩ : syracuseStep 553211 = 829817) B829817
theorem B554543 : Blo 243817 554543 := bstep (se 1 (by rfl) ⟨415907, by rfl⟩ : syracuseStep 554543 = 831815) B831815
theorem B1865267 : Blo 243817 1865267 := bstep (se 1 (by rfl) ⟨1398950, by rfl⟩ : syracuseStep 1865267 = 2797901) B2797901
theorem B785065 : Blo 243817 785065 := bstep (se 2 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 785065 = 588799) B588799
theorem B555803 : Blo 243817 555803 := bstep (se 1 (by rfl) ⟨416852, by rfl⟩ : syracuseStep 555803 = 833705) B833705
theorem B621695 : Blo 243817 621695 := bstep (se 1 (by rfl) ⟨466271, by rfl⟩ : syracuseStep 621695 = 932543) B932543
theorem B1409021 : Blo 243817 1409021 := bstep (se 3 (by rfl) ⟨264191, by rfl⟩ : syracuseStep 1409021 = 528383) B528383
theorem B557153 : Blo 243817 557153 := bstep (se 2 (by rfl) ⟨208932, by rfl⟩ : syracuseStep 557153 = 417865) B417865
theorem B6097783 : Blo 243817 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B1252583 : Blo 243817 1252583 := bstep (se 1 (by rfl) ⟨939437, by rfl⟩ : syracuseStep 1252583 = 1878875) B1878875
theorem B368807 : Blo 243817 368807 := bstep (se 1 (by rfl) ⟨276605, by rfl⟩ : syracuseStep 368807 = 553211) B553211
theorem B369695 : Blo 243817 369695 := bstep (se 1 (by rfl) ⟨277271, by rfl⟩ : syracuseStep 369695 = 554543) B554543
theorem B370535 : Blo 243817 370535 := bstep (se 1 (by rfl) ⟨277901, by rfl⟩ : syracuseStep 370535 = 555803) B555803
theorem B1684583 : Blo 243817 1684583 := bstep (se 1 (by rfl) ⟨1263437, by rfl⟩ : syracuseStep 1684583 = 2526875) B2526875
theorem B11416733 : Blo 243817 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B414463 : Blo 243817 414463 := bstep (se 1 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 414463 = 621695) B621695
theorem B939347 : Blo 243817 939347 := bstep (se 1 (by rfl) ⟨704510, by rfl⟩ : syracuseStep 939347 = 1409021) B1409021
theorem B1562237 : Blo 243817 1562237 := bstep (se 3 (by rfl) ⟨292919, by rfl⟩ : syracuseStep 1562237 = 585839) B585839
theorem B35872267 : Blo 243817 35872267 := bstep (se 1 (by rfl) ⟨26904200, by rfl⟩ : syracuseStep 35872267 = 53808401) B53808401
theorem B1174409 : Blo 243817 1174409 := bstep (se 2 (by rfl) ⟨440403, by rfl⟩ : syracuseStep 1174409 = 880807) B880807
theorem B552527 : Blo 243817 552527 := bstep (se 1 (by rfl) ⟨414395, by rfl⟩ : syracuseStep 552527 = 828791) B828791
theorem B11464649 : Blo 243817 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B2781863 : Blo 243817 2781863 := bstep (se 1 (by rfl) ⟨2086397, by rfl⟩ : syracuseStep 2781863 = 4172795) B4172795
theorem B1046753 : Blo 243817 1046753 := bstep (se 2 (by rfl) ⟨392532, by rfl⟩ : syracuseStep 1046753 = 785065) B785065
theorem B1243511 : Blo 243817 1243511 := bstep (se 1 (by rfl) ⟨932633, by rfl⟩ : syracuseStep 1243511 = 1865267) B1865267
theorem B626231 : Blo 243817 626231 := bstep (se 1 (by rfl) ⟨469673, by rfl⟩ : syracuseStep 626231 = 939347) B939347
theorem B8130377 : Blo 243817 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B368351 : Blo 243817 368351 := bstep (se 1 (by rfl) ⟨276263, by rfl⟩ : syracuseStep 368351 = 552527) B552527
theorem B7643099 : Blo 243817 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B1123055 : Blo 243817 1123055 := bstep (se 1 (by rfl) ⟨842291, by rfl⟩ : syracuseStep 1123055 = 1684583) B1684583
theorem B7611155 : Blo 243817 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B697835 : Blo 243817 697835 := bstep (se 1 (by rfl) ⟨523376, by rfl⟩ : syracuseStep 697835 = 1046753) B1046753
theorem B829007 : Blo 243817 829007 := bstep (se 1 (by rfl) ⟨621755, by rfl⟩ : syracuseStep 829007 = 1243511) B1243511
theorem B371435 : Blo 243817 371435 := bstep (se 1 (by rfl) ⟨278576, by rfl⟩ : syracuseStep 371435 = 557153) B557153
theorem B835055 : Blo 243817 835055 := bstep (se 1 (by rfl) ⟨626291, by rfl⟩ : syracuseStep 835055 = 1252583) B1252583
theorem B245871 : Blo 243817 245871 := bstep (se 1 (by rfl) ⟨184403, by rfl⟩ : syracuseStep 245871 = 368807) B368807
theorem B246463 : Blo 243817 246463 := bstep (se 1 (by rfl) ⟨184847, by rfl⟩ : syracuseStep 246463 = 369695) B369695
theorem B247023 : Blo 243817 247023 := bstep (se 1 (by rfl) ⟨185267, by rfl⟩ : syracuseStep 247023 = 370535) B370535
theorem B1854575 : Blo 243817 1854575 := bstep (se 1 (by rfl) ⟨1390931, by rfl⟩ : syracuseStep 1854575 = 2781863) B2781863
theorem B47829689 : Blo 243817 47829689 := bstep (se 2 (by rfl) ⟨17936133, by rfl⟩ : syracuseStep 47829689 = 35872267) B35872267
theorem B1041491 : Blo 243817 1041491 := bstep (se 1 (by rfl) ⟨781118, by rfl⟩ : syracuseStep 1041491 = 1562237) B1562237
theorem B552617 : Blo 243817 552617 := bstep (se 2 (by rfl) ⟨207231, by rfl⟩ : syracuseStep 552617 = 414463) B414463
theorem B782939 : Blo 243817 782939 := bstep (se 1 (by rfl) ⟨587204, by rfl⟩ : syracuseStep 782939 = 1174409) B1174409
theorem B31886459 : Blo 243817 31886459 := bstep (se 1 (by rfl) ⟨23914844, by rfl⟩ : syracuseStep 31886459 = 47829689) B47829689
theorem B694327 : Blo 243817 694327 := bstep (se 1 (by rfl) ⟨520745, by rfl⟩ : syracuseStep 694327 = 1041491) B1041491
theorem B368411 : Blo 243817 368411 := bstep (se 1 (by rfl) ⟨276308, by rfl⟩ : syracuseStep 368411 = 552617) B552617
theorem B5420251 : Blo 243817 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B245567 : Blo 243817 245567 := bstep (se 1 (by rfl) ⟨184175, by rfl⟩ : syracuseStep 245567 = 368351) B368351
theorem B5095399 : Blo 243817 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B247623 : Blo 243817 247623 := bstep (se 1 (by rfl) ⟨185717, by rfl⟩ : syracuseStep 247623 = 371435) B371435
theorem B1236383 : Blo 243817 1236383 := bstep (se 1 (by rfl) ⟨927287, by rfl⟩ : syracuseStep 1236383 = 1854575) B1854575
theorem B417487 : Blo 243817 417487 := bstep (se 1 (by rfl) ⟨313115, by rfl⟩ : syracuseStep 417487 = 626231) B626231
theorem B1860893 : Blo 243817 1860893 := bstep (se 3 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 1860893 = 697835) B697835
theorem B748703 : Blo 243817 748703 := bstep (se 1 (by rfl) ⟨561527, by rfl⟩ : syracuseStep 748703 = 1123055) B1123055
theorem B5074103 : Blo 243817 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B552671 : Blo 243817 552671 := bstep (se 1 (by rfl) ⟨414503, by rfl⟩ : syracuseStep 552671 = 829007) B829007
theorem B521959 : Blo 243817 521959 := bstep (se 1 (by rfl) ⟨391469, by rfl⟩ : syracuseStep 521959 = 782939) B782939
theorem B556703 : Blo 243817 556703 := bstep (se 1 (by rfl) ⟨417527, by rfl⟩ : syracuseStep 556703 = 835055) B835055
theorem B824255 : Blo 243817 824255 := bstep (se 1 (by rfl) ⟨618191, by rfl⟩ : syracuseStep 824255 = 1236383) B1236383
theorem B499135 : Blo 243817 499135 := bstep (se 1 (by rfl) ⟨374351, by rfl⟩ : syracuseStep 499135 = 748703) B748703
theorem B3382735 : Blo 243817 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B695945 : Blo 243817 695945 := bstep (se 2 (by rfl) ⟨260979, by rfl⟩ : syracuseStep 695945 = 521959) B521959
theorem B368447 : Blo 243817 368447 := bstep (se 1 (by rfl) ⟨276335, by rfl⟩ : syracuseStep 368447 = 552671) B552671
theorem B925769 : Blo 243817 925769 := bstep (se 2 (by rfl) ⟨347163, by rfl⟩ : syracuseStep 925769 = 694327) B694327
theorem B371135 : Blo 243817 371135 := bstep (se 1 (by rfl) ⟨278351, by rfl⟩ : syracuseStep 371135 = 556703) B556703
theorem B6793865 : Blo 243817 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B245607 : Blo 243817 245607 := bstep (se 1 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 245607 = 368411) B368411
theorem B7227001 : Blo 243817 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B21257639 : Blo 243817 21257639 := bstep (se 1 (by rfl) ⟨15943229, by rfl⟩ : syracuseStep 21257639 = 31886459) B31886459
theorem B1240595 : Blo 243817 1240595 := bstep (se 1 (by rfl) ⟨930446, by rfl⟩ : syracuseStep 1240595 = 1860893) B1860893
theorem B556649 : Blo 243817 556649 := bstep (se 2 (by rfl) ⟨208743, by rfl⟩ : syracuseStep 556649 = 417487) B417487
theorem B463963 : Blo 243817 463963 := bstep (se 1 (by rfl) ⟨347972, by rfl⟩ : syracuseStep 463963 = 695945) B695945
theorem B4529243 : Blo 243817 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B827063 : Blo 243817 827063 := bstep (se 1 (by rfl) ⟨620297, by rfl⟩ : syracuseStep 827063 = 1240595) B1240595
theorem B38544005 : Blo 243817 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B665513 : Blo 243817 665513 := bstep (se 2 (by rfl) ⟨249567, by rfl⟩ : syracuseStep 665513 = 499135) B499135
theorem B371099 : Blo 243817 371099 := bstep (se 1 (by rfl) ⟨278324, by rfl⟩ : syracuseStep 371099 = 556649) B556649
theorem B14171759 : Blo 243817 14171759 := bstep (se 1 (by rfl) ⟨10628819, by rfl⟩ : syracuseStep 14171759 = 21257639) B21257639
theorem B245631 : Blo 243817 245631 := bstep (se 1 (by rfl) ⟨184223, by rfl⟩ : syracuseStep 245631 = 368447) B368447
theorem B247423 : Blo 243817 247423 := bstep (se 1 (by rfl) ⟨185567, by rfl⟩ : syracuseStep 247423 = 371135) B371135
theorem B4510313 : Blo 243817 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B549503 : Blo 243817 549503 := bstep (se 1 (by rfl) ⟨412127, by rfl⟩ : syracuseStep 549503 = 824255) B824255
theorem B617179 : Blo 243817 617179 := bstep (se 1 (by rfl) ⟨462884, by rfl⟩ : syracuseStep 617179 = 925769) B925769
theorem B822905 : Blo 243817 822905 := bstep (se 2 (by rfl) ⟨308589, by rfl⟩ : syracuseStep 822905 = 617179) B617179
theorem B366335 : Blo 243817 366335 := bstep (se 1 (by rfl) ⟨274751, by rfl⟩ : syracuseStep 366335 = 549503) B549503
theorem B25696003 : Blo 243817 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B9447839 : Blo 243817 9447839 := bstep (se 1 (by rfl) ⟨7085879, by rfl⟩ : syracuseStep 9447839 = 14171759) B14171759
theorem B443675 : Blo 243817 443675 := bstep (se 1 (by rfl) ⟨332756, by rfl⟩ : syracuseStep 443675 = 665513) B665513
theorem B247399 : Blo 243817 247399 := bstep (se 1 (by rfl) ⟨185549, by rfl⟩ : syracuseStep 247399 = 371099) B371099
theorem B12077981 : Blo 243817 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B3006875 : Blo 243817 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B551375 : Blo 243817 551375 := bstep (se 1 (by rfl) ⟨413531, by rfl⟩ : syracuseStep 551375 = 827063) B827063
theorem B618617 : Blo 243817 618617 := bstep (se 2 (by rfl) ⟨231981, by rfl⟩ : syracuseStep 618617 = 463963) B463963
theorem B1183133 : Blo 243817 1183133 := bstep (se 3 (by rfl) ⟨221837, by rfl⟩ : syracuseStep 1183133 = 443675) B443675
theorem B2004583 : Blo 243817 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B6298559 : Blo 243817 6298559 := bstep (se 1 (by rfl) ⟨4723919, by rfl⟩ : syracuseStep 6298559 = 9447839) B9447839
theorem B367583 : Blo 243817 367583 := bstep (se 1 (by rfl) ⟨275687, by rfl⟩ : syracuseStep 367583 = 551375) B551375
theorem B244223 : Blo 243817 244223 := bstep (se 1 (by rfl) ⟨183167, by rfl⟩ : syracuseStep 244223 = 366335) B366335
theorem B34261337 : Blo 243817 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B412411 : Blo 243817 412411 := bstep (se 1 (by rfl) ⟨309308, by rfl⟩ : syracuseStep 412411 = 618617) B618617
theorem B8051987 : Blo 243817 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B548603 : Blo 243817 548603 := bstep (se 1 (by rfl) ⟨411452, by rfl⟩ : syracuseStep 548603 = 822905) B822905
theorem B4199039 : Blo 243817 4199039 := bstep (se 1 (by rfl) ⟨3149279, by rfl⟩ : syracuseStep 4199039 = 6298559) B6298559
theorem B365735 : Blo 243817 365735 := bstep (se 1 (by rfl) ⟨274301, by rfl⟩ : syracuseStep 365735 = 548603) B548603
theorem B91363565 : Blo 243817 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B3155021 : Blo 243817 3155021 := bstep (se 3 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 3155021 = 1183133) B1183133
theorem B245055 : Blo 243817 245055 := bstep (se 1 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 245055 = 367583) B367583
theorem B2672777 : Blo 243817 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B549881 : Blo 243817 549881 := bstep (se 2 (by rfl) ⟨206205, by rfl⟩ : syracuseStep 549881 = 412411) B412411
theorem B5367991 : Blo 243817 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B366587 : Blo 243817 366587 := bstep (se 1 (by rfl) ⟨274940, by rfl⟩ : syracuseStep 366587 = 549881) B549881
theorem B2103347 : Blo 243817 2103347 := bstep (se 1 (by rfl) ⟨1577510, by rfl⟩ : syracuseStep 2103347 = 3155021) B3155021
theorem B1781851 : Blo 243817 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B7157321 : Blo 243817 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B2799359 : Blo 243817 2799359 := bstep (se 1 (by rfl) ⟨2099519, by rfl⟩ : syracuseStep 2799359 = 4199039) B4199039
theorem B243823 : Blo 243817 243823 := bstep (se 1 (by rfl) ⟨182867, by rfl⟩ : syracuseStep 243823 = 365735) B365735
theorem B60909043 : Blo 243817 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B81212057 : Blo 243817 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B244391 : Blo 243817 244391 := bstep (se 1 (by rfl) ⟨183293, by rfl⟩ : syracuseStep 244391 = 366587) B366587
theorem B2375801 : Blo 243817 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B4771547 : Blo 243817 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B1402231 : Blo 243817 1402231 := bstep (se 1 (by rfl) ⟨1051673, by rfl⟩ : syracuseStep 1402231 = 2103347) B2103347
theorem B1866239 : Blo 243817 1866239 := bstep (se 1 (by rfl) ⟨1399679, by rfl⟩ : syracuseStep 1866239 = 2799359) B2799359
theorem B1869641 : Blo 243817 1869641 := bstep (se 2 (by rfl) ⟨701115, by rfl⟩ : syracuseStep 1869641 = 1402231) B1402231
theorem B3181031 : Blo 243817 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B54141371 : Blo 243817 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B1583867 : Blo 243817 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B1244159 : Blo 243817 1244159 := bstep (se 1 (by rfl) ⟨933119, by rfl⟩ : syracuseStep 1244159 = 1866239) B1866239
theorem B1246427 : Blo 243817 1246427 := bstep (se 1 (by rfl) ⟨934820, by rfl⟩ : syracuseStep 1246427 = 1869641) B1869641
theorem B1055911 : Blo 243817 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B829439 : Blo 243817 829439 := bstep (se 1 (by rfl) ⟨622079, by rfl⟩ : syracuseStep 829439 = 1244159) B1244159
theorem B36094247 : Blo 243817 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B2120687 : Blo 243817 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B1413791 : Blo 243817 1413791 := bstep (se 1 (by rfl) ⟨1060343, by rfl⟩ : syracuseStep 1413791 = 2120687) B2120687
theorem B24062831 : Blo 243817 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B830951 : Blo 243817 830951 := bstep (se 1 (by rfl) ⟨623213, by rfl⟩ : syracuseStep 830951 = 1246427) B1246427
theorem B552959 : Blo 243817 552959 := bstep (se 1 (by rfl) ⟨414719, by rfl⟩ : syracuseStep 552959 = 829439) B829439
theorem B1407881 : Blo 243817 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B368639 : Blo 243817 368639 := bstep (se 1 (by rfl) ⟨276479, by rfl⟩ : syracuseStep 368639 = 552959) B552959
theorem B16041887 : Blo 243817 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B938587 : Blo 243817 938587 := bstep (se 1 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 938587 = 1407881) B1407881
theorem B942527 : Blo 243817 942527 := bstep (se 1 (by rfl) ⟨706895, by rfl⟩ : syracuseStep 942527 = 1413791) B1413791
theorem B553967 : Blo 243817 553967 := bstep (se 1 (by rfl) ⟨415475, by rfl⟩ : syracuseStep 553967 = 830951) B830951
theorem B1251449 : Blo 243817 1251449 := bstep (se 2 (by rfl) ⟨469293, by rfl⟩ : syracuseStep 1251449 = 938587) B938587
theorem B369311 : Blo 243817 369311 := bstep (se 1 (by rfl) ⟨276983, by rfl⟩ : syracuseStep 369311 = 553967) B553967
theorem B10694591 : Blo 243817 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B245759 : Blo 243817 245759 := bstep (se 1 (by rfl) ⟨184319, by rfl⟩ : syracuseStep 245759 = 368639) B368639
theorem B2513405 : Blo 243817 2513405 := bstep (se 3 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 2513405 = 942527) B942527
theorem B1675603 : Blo 243817 1675603 := bstep (se 1 (by rfl) ⟨1256702, by rfl⟩ : syracuseStep 1675603 = 2513405) B2513405
theorem B834299 : Blo 243817 834299 := bstep (se 1 (by rfl) ⟨625724, by rfl⟩ : syracuseStep 834299 = 1251449) B1251449
theorem B246207 : Blo 243817 246207 := bstep (se 1 (by rfl) ⟨184655, by rfl⟩ : syracuseStep 246207 = 369311) B369311
theorem B7129727 : Blo 243817 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B4753151 : Blo 243817 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B2234137 : Blo 243817 2234137 := bstep (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) B1675603
theorem B556199 : Blo 243817 556199 := bstep (se 1 (by rfl) ⟨417149, by rfl⟩ : syracuseStep 556199 = 834299) B834299
theorem B370799 : Blo 243817 370799 := bstep (se 1 (by rfl) ⟨278099, by rfl⟩ : syracuseStep 370799 = 556199) B556199
theorem B3168767 : Blo 243817 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B2978849 : Blo 243817 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B247199 : Blo 243817 247199 := bstep (se 1 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 247199 = 370799) B370799
theorem B1985899 : Blo 243817 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B15820757 : Blo 243817 15820757 := bstep (se 7 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 15820757 = 370799) B370799
theorem B8450045 : Blo 243817 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B2647865 : Blo 243817 2647865 := bstep (se 2 (by rfl) ⟨992949, by rfl⟩ : syracuseStep 2647865 = 1985899) B1985899
theorem B10547171 : Blo 243817 10547171 := bstep (se 1 (by rfl) ⟨7910378, by rfl⟩ : syracuseStep 10547171 = 15820757) B15820757
theorem B5633363 : Blo 243817 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B7031447 : Blo 243817 7031447 := bstep (se 1 (by rfl) ⟨5273585, by rfl⟩ : syracuseStep 7031447 = 10547171) B10547171
theorem B3755575 : Blo 243817 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B1765243 : Blo 243817 1765243 := bstep (se 1 (by rfl) ⟨1323932, by rfl⟩ : syracuseStep 1765243 = 2647865) B2647865
theorem B4687631 : Blo 243817 4687631 := bstep (se 1 (by rfl) ⟨3515723, by rfl⟩ : syracuseStep 4687631 = 7031447) B7031447
theorem B5007433 : Blo 243817 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B2353657 : Blo 243817 2353657 := bstep (se 2 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 2353657 = 1765243) B1765243
theorem B3125087 : Blo 243817 3125087 := bstep (se 1 (by rfl) ⟨2343815, by rfl⟩ : syracuseStep 3125087 = 4687631) B4687631
theorem B6676577 : Blo 243817 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B3138209 : Blo 243817 3138209 := bstep (se 2 (by rfl) ⟨1176828, by rfl⟩ : syracuseStep 3138209 = 2353657) B2353657
theorem B2083391 : Blo 243817 2083391 := bstep (se 1 (by rfl) ⟨1562543, by rfl⟩ : syracuseStep 2083391 = 3125087) B3125087
theorem B4451051 : Blo 243817 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B2092139 : Blo 243817 2092139 := bstep (se 1 (by rfl) ⟨1569104, by rfl⟩ : syracuseStep 2092139 = 3138209) B3138209
theorem B1388927 : Blo 243817 1388927 := bstep (se 1 (by rfl) ⟨1041695, by rfl⟩ : syracuseStep 1388927 = 2083391) B2083391
theorem B2967367 : Blo 243817 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B1394759 : Blo 243817 1394759 := bstep (se 1 (by rfl) ⟨1046069, by rfl⟩ : syracuseStep 1394759 = 2092139) B2092139
theorem B925951 : Blo 243817 925951 := bstep (se 1 (by rfl) ⟨694463, by rfl⟩ : syracuseStep 925951 = 1388927) B1388927
theorem B929839 : Blo 243817 929839 := bstep (se 1 (by rfl) ⟨697379, by rfl⟩ : syracuseStep 929839 = 1394759) B1394759
theorem B3956489 : Blo 243817 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B2637659 : Blo 243817 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B1234601 : Blo 243817 1234601 := bstep (se 2 (by rfl) ⟨462975, by rfl⟩ : syracuseStep 1234601 = 925951) B925951
theorem B1239785 : Blo 243817 1239785 := bstep (se 2 (by rfl) ⟨464919, by rfl⟩ : syracuseStep 1239785 = 929839) B929839
theorem B823067 : Blo 243817 823067 := bstep (se 1 (by rfl) ⟨617300, by rfl⟩ : syracuseStep 823067 = 1234601) B1234601
theorem B826523 : Blo 243817 826523 := bstep (se 1 (by rfl) ⟨619892, by rfl⟩ : syracuseStep 826523 = 1239785) B1239785
theorem B1758439 : Blo 243817 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B2344585 : Blo 243817 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B548711 : Blo 243817 548711 := bstep (se 1 (by rfl) ⟨411533, by rfl⟩ : syracuseStep 548711 = 823067) B823067
theorem B551015 : Blo 243817 551015 := bstep (se 1 (by rfl) ⟨413261, by rfl⟩ : syracuseStep 551015 = 826523) B826523
theorem B365807 : Blo 243817 365807 := bstep (se 1 (by rfl) ⟨274355, by rfl⟩ : syracuseStep 365807 = 548711) B548711
theorem B367343 : Blo 243817 367343 := bstep (se 1 (by rfl) ⟨275507, by rfl⟩ : syracuseStep 367343 = 551015) B551015
theorem B3126113 : Blo 243817 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B243871 : Blo 243817 243871 := bstep (se 1 (by rfl) ⟨182903, by rfl⟩ : syracuseStep 243871 = 365807) B365807
theorem B244895 : Blo 243817 244895 := bstep (se 1 (by rfl) ⟨183671, by rfl⟩ : syracuseStep 244895 = 367343) B367343
theorem B2084075 : Blo 243817 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B1389383 : Blo 243817 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B926255 : Blo 243817 926255 := bstep (se 1 (by rfl) ⟨694691, by rfl⟩ : syracuseStep 926255 = 1389383) B1389383
theorem B617503 : Blo 243817 617503 := bstep (se 1 (by rfl) ⟨463127, by rfl⟩ : syracuseStep 617503 = 926255) B926255
theorem B823337 : Blo 243817 823337 := bstep (se 2 (by rfl) ⟨308751, by rfl⟩ : syracuseStep 823337 = 617503) B617503
theorem B548891 : Blo 243817 548891 := bstep (se 1 (by rfl) ⟨411668, by rfl⟩ : syracuseStep 548891 = 823337) B823337
theorem B365927 : Blo 243817 365927 := bstep (se 1 (by rfl) ⟨274445, by rfl⟩ : syracuseStep 365927 = 548891) B548891
theorem B243951 : Blo 243817 243951 := bstep (se 1 (by rfl) ⟨182963, by rfl⟩ : syracuseStep 243951 = 365927) B365927

theorem C0 (j : ℕ) (h1 : 60954 ≤ j) (h2 : j ≤ 61653) : Blo 243817 (4 * j + 3) := by
  interval_cases j
  · exact B243819
  · exact B243823
  · exact B243827
  · exact B243831
  · exact B243835
  · exact B243839
  · exact B243843
  · exact B243847
  · exact B243851
  · exact B243855
  · exact B243859
  · exact B243863
  · exact B243867
  · exact B243871
  · exact B243875
  · exact B243879
  · exact B243883
  · exact B243887
  · exact B243891
  · exact B243895
  · exact B243899
  · exact B243903
  · exact B243907
  · exact B243911
  · exact B243915
  · exact B243919
  · exact B243923
  · exact B243927
  · exact B243931
  · exact B243935
  · exact B243939
  · exact B243943
  · exact B243947
  · exact B243951
  · exact B243955
  · exact B243959
  · exact B243963
  · exact B243967
  · exact B243971
  · exact B243975
  · exact B243979
  · exact B243983
  · exact B243987
  · exact B243991
  · exact B243995
  · exact B243999
  · exact B244003
  · exact B244007
  · exact B244011
  · exact B244015
  · exact B244019
  · exact B244023
  · exact B244027
  · exact B244031
  · exact B244035
  · exact B244039
  · exact B244043
  · exact B244047
  · exact B244051
  · exact B244055
  · exact B244059
  · exact B244063
  · exact B244067
  · exact B244071
  · exact B244075
  · exact B244079
  · exact B244083
  · exact B244087
  · exact B244091
  · exact B244095
  · exact B244099
  · exact B244103
  · exact B244107
  · exact B244111
  · exact B244115
  · exact B244119
  · exact B244123
  · exact B244127
  · exact B244131
  · exact B244135
  · exact B244139
  · exact B244143
  · exact B244147
  · exact B244151
  · exact B244155
  · exact B244159
  · exact B244163
  · exact B244167
  · exact B244171
  · exact B244175
  · exact B244179
  · exact B244183
  · exact B244187
  · exact B244191
  · exact B244195
  · exact B244199
  · exact B244203
  · exact B244207
  · exact B244211
  · exact B244215
  · exact B244219
  · exact B244223
  · exact B244227
  · exact B244231
  · exact B244235
  · exact B244239
  · exact B244243
  · exact B244247
  · exact B244251
  · exact B244255
  · exact B244259
  · exact B244263
  · exact B244267
  · exact B244271
  · exact B244275
  · exact B244279
  · exact B244283
  · exact B244287
  · exact B244291
  · exact B244295
  · exact B244299
  · exact B244303
  · exact B244307
  · exact B244311
  · exact B244315
  · exact B244319
  · exact B244323
  · exact B244327
  · exact B244331
  · exact B244335
  · exact B244339
  · exact B244343
  · exact B244347
  · exact B244351
  · exact B244355
  · exact B244359
  · exact B244363
  · exact B244367
  · exact B244371
  · exact B244375
  · exact B244379
  · exact B244383
  · exact B244387
  · exact B244391
  · exact B244395
  · exact B244399
  · exact B244403
  · exact B244407
  · exact B244411
  · exact B244415
  · exact B244419
  · exact B244423
  · exact B244427
  · exact B244431
  · exact B244435
  · exact B244439
  · exact B244443
  · exact B244447
  · exact B244451
  · exact B244455
  · exact B244459
  · exact B244463
  · exact B244467
  · exact B244471
  · exact B244475
  · exact B244479
  · exact B244483
  · exact B244487
  · exact B244491
  · exact B244495
  · exact B244499
  · exact B244503
  · exact B244507
  · exact B244511
  · exact B244515
  · exact B244519
  · exact B244523
  · exact B244527
  · exact B244531
  · exact B244535
  · exact B244539
  · exact B244543
  · exact B244547
  · exact B244551
  · exact B244555
  · exact B244559
  · exact B244563
  · exact B244567
  · exact B244571
  · exact B244575
  · exact B244579
  · exact B244583
  · exact B244587
  · exact B244591
  · exact B244595
  · exact B244599
  · exact B244603
  · exact B244607
  · exact B244611
  · exact B244615
  · exact B244619
  · exact B244623
  · exact B244627
  · exact B244631
  · exact B244635
  · exact B244639
  · exact B244643
  · exact B244647
  · exact B244651
  · exact B244655
  · exact B244659
  · exact B244663
  · exact B244667
  · exact B244671
  · exact B244675
  · exact B244679
  · exact B244683
  · exact B244687
  · exact B244691
  · exact B244695
  · exact B244699
  · exact B244703
  · exact B244707
  · exact B244711
  · exact B244715
  · exact B244719
  · exact B244723
  · exact B244727
  · exact B244731
  · exact B244735
  · exact B244739
  · exact B244743
  · exact B244747
  · exact B244751
  · exact B244755
  · exact B244759
  · exact B244763
  · exact B244767
  · exact B244771
  · exact B244775
  · exact B244779
  · exact B244783
  · exact B244787
  · exact B244791
  · exact B244795
  · exact B244799
  · exact B244803
  · exact B244807
  · exact B244811
  · exact B244815
  · exact B244819
  · exact B244823
  · exact B244827
  · exact B244831
  · exact B244835
  · exact B244839
  · exact B244843
  · exact B244847
  · exact B244851
  · exact B244855
  · exact B244859
  · exact B244863
  · exact B244867
  · exact B244871
  · exact B244875
  · exact B244879
  · exact B244883
  · exact B244887
  · exact B244891
  · exact B244895
  · exact B244899
  · exact B244903
  · exact B244907
  · exact B244911
  · exact B244915
  · exact B244919
  · exact B244923
  · exact B244927
  · exact B244931
  · exact B244935
  · exact B244939
  · exact B244943
  · exact B244947
  · exact B244951
  · exact B244955
  · exact B244959
  · exact B244963
  · exact B244967
  · exact B244971
  · exact B244975
  · exact B244979
  · exact B244983
  · exact B244987
  · exact B244991
  · exact B244995
  · exact B244999
  · exact B245003
  · exact B245007
  · exact B245011
  · exact B245015
  · exact B245019
  · exact B245023
  · exact B245027
  · exact B245031
  · exact B245035
  · exact B245039
  · exact B245043
  · exact B245047
  · exact B245051
  · exact B245055
  · exact B245059
  · exact B245063
  · exact B245067
  · exact B245071
  · exact B245075
  · exact B245079
  · exact B245083
  · exact B245087
  · exact B245091
  · exact B245095
  · exact B245099
  · exact B245103
  · exact B245107
  · exact B245111
  · exact B245115
  · exact B245119
  · exact B245123
  · exact B245127
  · exact B245131
  · exact B245135
  · exact B245139
  · exact B245143
  · exact B245147
  · exact B245151
  · exact B245155
  · exact B245159
  · exact B245163
  · exact B245167
  · exact B245171
  · exact B245175
  · exact B245179
  · exact B245183
  · exact B245187
  · exact B245191
  · exact B245195
  · exact B245199
  · exact B245203
  · exact B245207
  · exact B245211
  · exact B245215
  · exact B245219
  · exact B245223
  · exact B245227
  · exact B245231
  · exact B245235
  · exact B245239
  · exact B245243
  · exact B245247
  · exact B245251
  · exact B245255
  · exact B245259
  · exact B245263
  · exact B245267
  · exact B245271
  · exact B245275
  · exact B245279
  · exact B245283
  · exact B245287
  · exact B245291
  · exact B245295
  · exact B245299
  · exact B245303
  · exact B245307
  · exact B245311
  · exact B245315
  · exact B245319
  · exact B245323
  · exact B245327
  · exact B245331
  · exact B245335
  · exact B245339
  · exact B245343
  · exact B245347
  · exact B245351
  · exact B245355
  · exact B245359
  · exact B245363
  · exact B245367
  · exact B245371
  · exact B245375
  · exact B245379
  · exact B245383
  · exact B245387
  · exact B245391
  · exact B245395
  · exact B245399
  · exact B245403
  · exact B245407
  · exact B245411
  · exact B245415
  · exact B245419
  · exact B245423
  · exact B245427
  · exact B245431
  · exact B245435
  · exact B245439
  · exact B245443
  · exact B245447
  · exact B245451
  · exact B245455
  · exact B245459
  · exact B245463
  · exact B245467
  · exact B245471
  · exact B245475
  · exact B245479
  · exact B245483
  · exact B245487
  · exact B245491
  · exact B245495
  · exact B245499
  · exact B245503
  · exact B245507
  · exact B245511
  · exact B245515
  · exact B245519
  · exact B245523
  · exact B245527
  · exact B245531
  · exact B245535
  · exact B245539
  · exact B245543
  · exact B245547
  · exact B245551
  · exact B245555
  · exact B245559
  · exact B245563
  · exact B245567
  · exact B245571
  · exact B245575
  · exact B245579
  · exact B245583
  · exact B245587
  · exact B245591
  · exact B245595
  · exact B245599
  · exact B245603
  · exact B245607
  · exact B245611
  · exact B245615
  · exact B245619
  · exact B245623
  · exact B245627
  · exact B245631
  · exact B245635
  · exact B245639
  · exact B245643
  · exact B245647
  · exact B245651
  · exact B245655
  · exact B245659
  · exact B245663
  · exact B245667
  · exact B245671
  · exact B245675
  · exact B245679
  · exact B245683
  · exact B245687
  · exact B245691
  · exact B245695
  · exact B245699
  · exact B245703
  · exact B245707
  · exact B245711
  · exact B245715
  · exact B245719
  · exact B245723
  · exact B245727
  · exact B245731
  · exact B245735
  · exact B245739
  · exact B245743
  · exact B245747
  · exact B245751
  · exact B245755
  · exact B245759
  · exact B245763
  · exact B245767
  · exact B245771
  · exact B245775
  · exact B245779
  · exact B245783
  · exact B245787
  · exact B245791
  · exact B245795
  · exact B245799
  · exact B245803
  · exact B245807
  · exact B245811
  · exact B245815
  · exact B245819
  · exact B245823
  · exact B245827
  · exact B245831
  · exact B245835
  · exact B245839
  · exact B245843
  · exact B245847
  · exact B245851
  · exact B245855
  · exact B245859
  · exact B245863
  · exact B245867
  · exact B245871
  · exact B245875
  · exact B245879
  · exact B245883
  · exact B245887
  · exact B245891
  · exact B245895
  · exact B245899
  · exact B245903
  · exact B245907
  · exact B245911
  · exact B245915
  · exact B245919
  · exact B245923
  · exact B245927
  · exact B245931
  · exact B245935
  · exact B245939
  · exact B245943
  · exact B245947
  · exact B245951
  · exact B245955
  · exact B245959
  · exact B245963
  · exact B245967
  · exact B245971
  · exact B245975
  · exact B245979
  · exact B245983
  · exact B245987
  · exact B245991
  · exact B245995
  · exact B245999
  · exact B246003
  · exact B246007
  · exact B246011
  · exact B246015
  · exact B246019
  · exact B246023
  · exact B246027
  · exact B246031
  · exact B246035
  · exact B246039
  · exact B246043
  · exact B246047
  · exact B246051
  · exact B246055
  · exact B246059
  · exact B246063
  · exact B246067
  · exact B246071
  · exact B246075
  · exact B246079
  · exact B246083
  · exact B246087
  · exact B246091
  · exact B246095
  · exact B246099
  · exact B246103
  · exact B246107
  · exact B246111
  · exact B246115
  · exact B246119
  · exact B246123
  · exact B246127
  · exact B246131
  · exact B246135
  · exact B246139
  · exact B246143
  · exact B246147
  · exact B246151
  · exact B246155
  · exact B246159
  · exact B246163
  · exact B246167
  · exact B246171
  · exact B246175
  · exact B246179
  · exact B246183
  · exact B246187
  · exact B246191
  · exact B246195
  · exact B246199
  · exact B246203
  · exact B246207
  · exact B246211
  · exact B246215
  · exact B246219
  · exact B246223
  · exact B246227
  · exact B246231
  · exact B246235
  · exact B246239
  · exact B246243
  · exact B246247
  · exact B246251
  · exact B246255
  · exact B246259
  · exact B246263
  · exact B246267
  · exact B246271
  · exact B246275
  · exact B246279
  · exact B246283
  · exact B246287
  · exact B246291
  · exact B246295
  · exact B246299
  · exact B246303
  · exact B246307
  · exact B246311
  · exact B246315
  · exact B246319
  · exact B246323
  · exact B246327
  · exact B246331
  · exact B246335
  · exact B246339
  · exact B246343
  · exact B246347
  · exact B246351
  · exact B246355
  · exact B246359
  · exact B246363
  · exact B246367
  · exact B246371
  · exact B246375
  · exact B246379
  · exact B246383
  · exact B246387
  · exact B246391
  · exact B246395
  · exact B246399
  · exact B246403
  · exact B246407
  · exact B246411
  · exact B246415
  · exact B246419
  · exact B246423
  · exact B246427
  · exact B246431
  · exact B246435
  · exact B246439
  · exact B246443
  · exact B246447
  · exact B246451
  · exact B246455
  · exact B246459
  · exact B246463
  · exact B246467
  · exact B246471
  · exact B246475
  · exact B246479
  · exact B246483
  · exact B246487
  · exact B246491
  · exact B246495
  · exact B246499
  · exact B246503
  · exact B246507
  · exact B246511
  · exact B246515
  · exact B246519
  · exact B246523
  · exact B246527
  · exact B246531
  · exact B246535
  · exact B246539
  · exact B246543
  · exact B246547
  · exact B246551
  · exact B246555
  · exact B246559
  · exact B246563
  · exact B246567
  · exact B246571
  · exact B246575
  · exact B246579
  · exact B246583
  · exact B246587
  · exact B246591
  · exact B246595
  · exact B246599
  · exact B246603
  · exact B246607
  · exact B246611
  · exact B246615

theorem C1 (j : ℕ) (h1 : 61654 ≤ j) (h2 : j ≤ 61953) : Blo 243817 (4 * j + 3) := by
  interval_cases j
  · exact B246619
  · exact B246623
  · exact B246627
  · exact B246631
  · exact B246635
  · exact B246639
  · exact B246643
  · exact B246647
  · exact B246651
  · exact B246655
  · exact B246659
  · exact B246663
  · exact B246667
  · exact B246671
  · exact B246675
  · exact B246679
  · exact B246683
  · exact B246687
  · exact B246691
  · exact B246695
  · exact B246699
  · exact B246703
  · exact B246707
  · exact B246711
  · exact B246715
  · exact B246719
  · exact B246723
  · exact B246727
  · exact B246731
  · exact B246735
  · exact B246739
  · exact B246743
  · exact B246747
  · exact B246751
  · exact B246755
  · exact B246759
  · exact B246763
  · exact B246767
  · exact B246771
  · exact B246775
  · exact B246779
  · exact B246783
  · exact B246787
  · exact B246791
  · exact B246795
  · exact B246799
  · exact B246803
  · exact B246807
  · exact B246811
  · exact B246815
  · exact B246819
  · exact B246823
  · exact B246827
  · exact B246831
  · exact B246835
  · exact B246839
  · exact B246843
  · exact B246847
  · exact B246851
  · exact B246855
  · exact B246859
  · exact B246863
  · exact B246867
  · exact B246871
  · exact B246875
  · exact B246879
  · exact B246883
  · exact B246887
  · exact B246891
  · exact B246895
  · exact B246899
  · exact B246903
  · exact B246907
  · exact B246911
  · exact B246915
  · exact B246919
  · exact B246923
  · exact B246927
  · exact B246931
  · exact B246935
  · exact B246939
  · exact B246943
  · exact B246947
  · exact B246951
  · exact B246955
  · exact B246959
  · exact B246963
  · exact B246967
  · exact B246971
  · exact B246975
  · exact B246979
  · exact B246983
  · exact B246987
  · exact B246991
  · exact B246995
  · exact B246999
  · exact B247003
  · exact B247007
  · exact B247011
  · exact B247015
  · exact B247019
  · exact B247023
  · exact B247027
  · exact B247031
  · exact B247035
  · exact B247039
  · exact B247043
  · exact B247047
  · exact B247051
  · exact B247055
  · exact B247059
  · exact B247063
  · exact B247067
  · exact B247071
  · exact B247075
  · exact B247079
  · exact B247083
  · exact B247087
  · exact B247091
  · exact B247095
  · exact B247099
  · exact B247103
  · exact B247107
  · exact B247111
  · exact B247115
  · exact B247119
  · exact B247123
  · exact B247127
  · exact B247131
  · exact B247135
  · exact B247139
  · exact B247143
  · exact B247147
  · exact B247151
  · exact B247155
  · exact B247159
  · exact B247163
  · exact B247167
  · exact B247171
  · exact B247175
  · exact B247179
  · exact B247183
  · exact B247187
  · exact B247191
  · exact B247195
  · exact B247199
  · exact B247203
  · exact B247207
  · exact B247211
  · exact B247215
  · exact B247219
  · exact B247223
  · exact B247227
  · exact B247231
  · exact B247235
  · exact B247239
  · exact B247243
  · exact B247247
  · exact B247251
  · exact B247255
  · exact B247259
  · exact B247263
  · exact B247267
  · exact B247271
  · exact B247275
  · exact B247279
  · exact B247283
  · exact B247287
  · exact B247291
  · exact B247295
  · exact B247299
  · exact B247303
  · exact B247307
  · exact B247311
  · exact B247315
  · exact B247319
  · exact B247323
  · exact B247327
  · exact B247331
  · exact B247335
  · exact B247339
  · exact B247343
  · exact B247347
  · exact B247351
  · exact B247355
  · exact B247359
  · exact B247363
  · exact B247367
  · exact B247371
  · exact B247375
  · exact B247379
  · exact B247383
  · exact B247387
  · exact B247391
  · exact B247395
  · exact B247399
  · exact B247403
  · exact B247407
  · exact B247411
  · exact B247415
  · exact B247419
  · exact B247423
  · exact B247427
  · exact B247431
  · exact B247435
  · exact B247439
  · exact B247443
  · exact B247447
  · exact B247451
  · exact B247455
  · exact B247459
  · exact B247463
  · exact B247467
  · exact B247471
  · exact B247475
  · exact B247479
  · exact B247483
  · exact B247487
  · exact B247491
  · exact B247495
  · exact B247499
  · exact B247503
  · exact B247507
  · exact B247511
  · exact B247515
  · exact B247519
  · exact B247523
  · exact B247527
  · exact B247531
  · exact B247535
  · exact B247539
  · exact B247543
  · exact B247547
  · exact B247551
  · exact B247555
  · exact B247559
  · exact B247563
  · exact B247567
  · exact B247571
  · exact B247575
  · exact B247579
  · exact B247583
  · exact B247587
  · exact B247591
  · exact B247595
  · exact B247599
  · exact B247603
  · exact B247607
  · exact B247611
  · exact B247615
  · exact B247619
  · exact B247623
  · exact B247627
  · exact B247631
  · exact B247635
  · exact B247639
  · exact B247643
  · exact B247647
  · exact B247651
  · exact B247655
  · exact B247659
  · exact B247663
  · exact B247667
  · exact B247671
  · exact B247675
  · exact B247679
  · exact B247683
  · exact B247687
  · exact B247691
  · exact B247695
  · exact B247699
  · exact B247703
  · exact B247707
  · exact B247711
  · exact B247715
  · exact B247719
  · exact B247723
  · exact B247727
  · exact B247731
  · exact B247735
  · exact B247739
  · exact B247743
  · exact B247747
  · exact B247751
  · exact B247755
  · exact B247759
  · exact B247763
  · exact B247767
  · exact B247771
  · exact B247775
  · exact B247779
  · exact B247783
  · exact B247787
  · exact B247791
  · exact B247795
  · exact B247799
  · exact B247803
  · exact B247807
  · exact B247811
  · exact B247815

theorem solution (m : ℕ) (hlo : 243817 ≤ m) (hhi : m ≤ 247817) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 60954 ≤ j := by omega
    have hj2 : j ≤ 61953 := by omega
    have hb : Blo 243817 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 61654 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
