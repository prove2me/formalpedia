-- Prove2me | solution 1 for syracuse_descends_range_171799_175799
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:44.504464+00:00
-- url     : https://prove2.me/submissions/0dedc6c9-30d0-4837-85b6-296daabdb751

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


theorem B196609 : Blo 171799 196609 := bbase (se 2 (by rfl) ⟨73728, by rfl⟩ : syracuseStep 196609 = 147457) (by norm_num)
theorem B262157 : Blo 171799 262157 := bbase (se 3 (by rfl) ⟨49154, by rfl⟩ : syracuseStep 262157 = 98309) (by norm_num)
theorem B1310741 : Blo 171799 1310741 := bbase (se 6 (by rfl) ⟨30720, by rfl⟩ : syracuseStep 1310741 = 61441) (by norm_num)
theorem B327701 : Blo 171799 327701 := bbase (se 6 (by rfl) ⟨7680, by rfl⟩ : syracuseStep 327701 = 15361) (by norm_num)
theorem B393245 : Blo 171799 393245 := bbase (se 3 (by rfl) ⟨73733, by rfl⟩ : syracuseStep 393245 = 147467) (by norm_num)
theorem B294941 : Blo 171799 294941 := bbase (se 3 (by rfl) ⟨55301, by rfl⟩ : syracuseStep 294941 = 110603) (by norm_num)
theorem B262181 : Blo 171799 262181 := bbase (se 4 (by rfl) ⟨24579, by rfl⟩ : syracuseStep 262181 = 49159) (by norm_num)
theorem B196645 : Blo 171799 196645 := bbase (se 4 (by rfl) ⟨18435, by rfl⟩ : syracuseStep 196645 = 36871) (by norm_num)
theorem B262205 : Blo 171799 262205 := bbase (se 3 (by rfl) ⟨49163, by rfl⟩ : syracuseStep 262205 = 98327) (by norm_num)
theorem B196681 : Blo 171799 196681 := bbase (se 2 (by rfl) ⟨73755, by rfl⟩ : syracuseStep 196681 = 147511) (by norm_num)
theorem B262229 : Blo 171799 262229 := bbase (se 8 (by rfl) ⟨1536, by rfl⟩ : syracuseStep 262229 = 3073) (by norm_num)
theorem B393317 : Blo 171799 393317 := bbase (se 4 (by rfl) ⟨36873, by rfl⟩ : syracuseStep 393317 = 73747) (by norm_num)
theorem B262253 : Blo 171799 262253 := bbase (se 3 (by rfl) ⟨49172, by rfl⟩ : syracuseStep 262253 = 98345) (by norm_num)
theorem B196717 : Blo 171799 196717 := bbase (se 3 (by rfl) ⟨36884, by rfl⟩ : syracuseStep 196717 = 73769) (by norm_num)
theorem B262277 : Blo 171799 262277 := bbase (se 4 (by rfl) ⟨24588, by rfl⟩ : syracuseStep 262277 = 49177) (by norm_num)
theorem B196753 : Blo 171799 196753 := bbase (se 2 (by rfl) ⟨73782, by rfl⟩ : syracuseStep 196753 = 147565) (by norm_num)
theorem B295069 : Blo 171799 295069 := bbase (se 3 (by rfl) ⟨55325, by rfl⟩ : syracuseStep 295069 = 110651) (by norm_num)
theorem B262301 : Blo 171799 262301 := bbase (se 3 (by rfl) ⟨49181, by rfl⟩ : syracuseStep 262301 = 98363) (by norm_num)
theorem B393389 : Blo 171799 393389 := bbase (se 3 (by rfl) ⟨73760, by rfl⟩ : syracuseStep 393389 = 147521) (by norm_num)
theorem B262325 : Blo 171799 262325 := bbase (se 5 (by rfl) ⟨12296, by rfl⟩ : syracuseStep 262325 = 24593) (by norm_num)
theorem B196789 : Blo 171799 196789 := bbase (se 5 (by rfl) ⟨9224, by rfl⟩ : syracuseStep 196789 = 18449) (by norm_num)
theorem B262349 : Blo 171799 262349 := bbase (se 3 (by rfl) ⟨49190, by rfl⟩ : syracuseStep 262349 = 98381) (by norm_num)
theorem B196825 : Blo 171799 196825 := bbase (se 2 (by rfl) ⟨73809, by rfl⟩ : syracuseStep 196825 = 147619) (by norm_num)
theorem B262373 : Blo 171799 262373 := bbase (se 4 (by rfl) ⟨24597, by rfl⟩ : syracuseStep 262373 = 49195) (by norm_num)
theorem B983285 : Blo 171799 983285 := bbase (se 5 (by rfl) ⟨46091, by rfl⟩ : syracuseStep 983285 = 92183) (by norm_num)
theorem B393461 : Blo 171799 393461 := bbase (se 5 (by rfl) ⟨18443, by rfl⟩ : syracuseStep 393461 = 36887) (by norm_num)
theorem B295157 : Blo 171799 295157 := bbase (se 5 (by rfl) ⟨13835, by rfl⟩ : syracuseStep 295157 = 27671) (by norm_num)
theorem B262397 : Blo 171799 262397 := bbase (se 3 (by rfl) ⟨49199, by rfl⟩ : syracuseStep 262397 = 98399) (by norm_num)
theorem B196861 : Blo 171799 196861 := bbase (se 3 (by rfl) ⟨36911, by rfl⟩ : syracuseStep 196861 = 73823) (by norm_num)
theorem B262421 : Blo 171799 262421 := bbase (se 6 (by rfl) ⟨6150, by rfl⟩ : syracuseStep 262421 = 12301) (by norm_num)
theorem B196897 : Blo 171799 196897 := bbase (se 2 (by rfl) ⟨73836, by rfl⟩ : syracuseStep 196897 = 147673) (by norm_num)
theorem B622885 : Blo 171799 622885 := bbase (se 4 (by rfl) ⟨58395, by rfl⟩ : syracuseStep 622885 = 116791) (by norm_num)
theorem B262445 : Blo 171799 262445 := bbase (se 3 (by rfl) ⟨49208, by rfl⟩ : syracuseStep 262445 = 98417) (by norm_num)
theorem B327989 : Blo 171799 327989 := bbase (se 5 (by rfl) ⟨15374, by rfl⟩ : syracuseStep 327989 = 30749) (by norm_num)
theorem B393533 : Blo 171799 393533 := bbase (se 3 (by rfl) ⟨73787, by rfl⟩ : syracuseStep 393533 = 147575) (by norm_num)
theorem B262469 : Blo 171799 262469 := bbase (se 4 (by rfl) ⟨24606, by rfl⟩ : syracuseStep 262469 = 49213) (by norm_num)
theorem B196933 : Blo 171799 196933 := bbase (se 4 (by rfl) ⟨18462, by rfl⟩ : syracuseStep 196933 = 36925) (by norm_num)
theorem B590165 : Blo 171799 590165 := bbase (se 10 (by rfl) ⟨864, by rfl⟩ : syracuseStep 590165 = 1729) (by norm_num)
theorem B262493 : Blo 171799 262493 := bbase (se 3 (by rfl) ⟨49217, by rfl⟩ : syracuseStep 262493 = 98435) (by norm_num)
theorem B196969 : Blo 171799 196969 := bbase (se 2 (by rfl) ⟨73863, by rfl⟩ : syracuseStep 196969 = 147727) (by norm_num)
theorem B295285 : Blo 171799 295285 := bbase (se 5 (by rfl) ⟨13841, by rfl⟩ : syracuseStep 295285 = 27683) (by norm_num)
theorem B262517 : Blo 171799 262517 := bbase (se 5 (by rfl) ⟨12305, by rfl⟩ : syracuseStep 262517 = 24611) (by norm_num)
theorem B393605 : Blo 171799 393605 := bbase (se 4 (by rfl) ⟨36900, by rfl⟩ : syracuseStep 393605 = 73801) (by norm_num)
theorem B262541 : Blo 171799 262541 := bbase (se 3 (by rfl) ⟨49226, by rfl⟩ : syracuseStep 262541 = 98453) (by norm_num)
theorem B197005 : Blo 171799 197005 := bbase (se 3 (by rfl) ⟨36938, by rfl⟩ : syracuseStep 197005 = 73877) (by norm_num)
theorem B262565 : Blo 171799 262565 := bbase (se 4 (by rfl) ⟨24615, by rfl⟩ : syracuseStep 262565 = 49231) (by norm_num)
theorem B197041 : Blo 171799 197041 := bbase (se 2 (by rfl) ⟨73890, by rfl⟩ : syracuseStep 197041 = 147781) (by norm_num)
theorem B262589 : Blo 171799 262589 := bbase (se 3 (by rfl) ⟨49235, by rfl⟩ : syracuseStep 262589 = 98471) (by norm_num)
theorem B623045 : Blo 171799 623045 := bbase (se 4 (by rfl) ⟨58410, by rfl⟩ : syracuseStep 623045 = 116821) (by norm_num)
theorem B328141 : Blo 171799 328141 := bbase (se 3 (by rfl) ⟨61526, by rfl⟩ : syracuseStep 328141 = 123053) (by norm_num)
theorem B393677 : Blo 171799 393677 := bbase (se 3 (by rfl) ⟨73814, by rfl⟩ : syracuseStep 393677 = 147629) (by norm_num)
theorem B295373 : Blo 171799 295373 := bbase (se 3 (by rfl) ⟨55382, by rfl⟩ : syracuseStep 295373 = 110765) (by norm_num)
theorem B262613 : Blo 171799 262613 := bbase (se 7 (by rfl) ⟨3077, by rfl⟩ : syracuseStep 262613 = 6155) (by norm_num)
theorem B197077 : Blo 171799 197077 := bbase (se 7 (by rfl) ⟨2309, by rfl⟩ : syracuseStep 197077 = 4619) (by norm_num)
theorem B262637 : Blo 171799 262637 := bbase (se 3 (by rfl) ⟨49244, by rfl⟩ : syracuseStep 262637 = 98489) (by norm_num)
theorem B197113 : Blo 171799 197113 := bbase (se 2 (by rfl) ⟨73917, by rfl⟩ : syracuseStep 197113 = 147835) (by norm_num)
theorem B262661 : Blo 171799 262661 := bbase (se 4 (by rfl) ⟨24624, by rfl⟩ : syracuseStep 262661 = 49249) (by norm_num)
theorem B393749 : Blo 171799 393749 := bbase (se 6 (by rfl) ⟨9228, by rfl⟩ : syracuseStep 393749 = 18457) (by norm_num)
theorem B262685 : Blo 171799 262685 := bbase (se 3 (by rfl) ⟨49253, by rfl⟩ : syracuseStep 262685 = 98507) (by norm_num)
theorem B197149 : Blo 171799 197149 := bbase (se 3 (by rfl) ⟨36965, by rfl⟩ : syracuseStep 197149 = 73931) (by norm_num)
theorem B262709 : Blo 171799 262709 := bbase (se 5 (by rfl) ⟨12314, by rfl⟩ : syracuseStep 262709 = 24629) (by norm_num)
theorem B197185 : Blo 171799 197185 := bbase (se 2 (by rfl) ⟨73944, by rfl⟩ : syracuseStep 197185 = 147889) (by norm_num)
theorem B295501 : Blo 171799 295501 := bbase (se 3 (by rfl) ⟨55406, by rfl⟩ : syracuseStep 295501 = 110813) (by norm_num)
theorem B262733 : Blo 171799 262733 := bbase (se 3 (by rfl) ⟨49262, by rfl⟩ : syracuseStep 262733 = 98525) (by norm_num)
theorem B393821 : Blo 171799 393821 := bbase (se 3 (by rfl) ⟨73841, by rfl⟩ : syracuseStep 393821 = 147683) (by norm_num)
theorem B262757 : Blo 171799 262757 := bbase (se 4 (by rfl) ⟨24633, by rfl⟩ : syracuseStep 262757 = 49267) (by norm_num)
theorem B197221 : Blo 171799 197221 := bbase (se 4 (by rfl) ⟨18489, by rfl⟩ : syracuseStep 197221 = 36979) (by norm_num)
theorem B262781 : Blo 171799 262781 := bbase (se 3 (by rfl) ⟨49271, by rfl⟩ : syracuseStep 262781 = 98543) (by norm_num)
theorem B197257 : Blo 171799 197257 := bbase (se 2 (by rfl) ⟨73971, by rfl⟩ : syracuseStep 197257 = 147943) (by norm_num)
theorem B262805 : Blo 171799 262805 := bbase (se 6 (by rfl) ⟨6159, by rfl⟩ : syracuseStep 262805 = 12319) (by norm_num)
theorem B393893 : Blo 171799 393893 := bbase (se 4 (by rfl) ⟨36927, by rfl⟩ : syracuseStep 393893 = 73855) (by norm_num)
theorem B295589 : Blo 171799 295589 := bbase (se 4 (by rfl) ⟨27711, by rfl⟩ : syracuseStep 295589 = 55423) (by norm_num)
theorem B262829 : Blo 171799 262829 := bbase (se 3 (by rfl) ⟨49280, by rfl⟩ : syracuseStep 262829 = 98561) (by norm_num)
theorem B197293 : Blo 171799 197293 := bbase (se 3 (by rfl) ⟨36992, by rfl⟩ : syracuseStep 197293 = 73985) (by norm_num)
theorem B262853 : Blo 171799 262853 := bbase (se 4 (by rfl) ⟨24642, by rfl⟩ : syracuseStep 262853 = 49285) (by norm_num)
theorem B197329 : Blo 171799 197329 := bbase (se 2 (by rfl) ⟨73998, by rfl⟩ : syracuseStep 197329 = 147997) (by norm_num)
theorem B262877 : Blo 171799 262877 := bbase (se 3 (by rfl) ⟨49289, by rfl⟩ : syracuseStep 262877 = 98579) (by norm_num)
theorem B393965 : Blo 171799 393965 := bbase (se 3 (by rfl) ⟨73868, by rfl⟩ : syracuseStep 393965 = 147737) (by norm_num)
theorem B262901 : Blo 171799 262901 := bbase (se 5 (by rfl) ⟨12323, by rfl⟩ : syracuseStep 262901 = 24647) (by norm_num)
theorem B197365 : Blo 171799 197365 := bbase (se 5 (by rfl) ⟨9251, by rfl⟩ : syracuseStep 197365 = 18503) (by norm_num)
theorem B328445 : Blo 171799 328445 := bbase (se 3 (by rfl) ⟨61583, by rfl⟩ : syracuseStep 328445 = 123167) (by norm_num)
theorem B590597 : Blo 171799 590597 := bbase (se 4 (by rfl) ⟨55368, by rfl⟩ : syracuseStep 590597 = 110737) (by norm_num)
theorem B262925 : Blo 171799 262925 := bbase (se 3 (by rfl) ⟨49298, by rfl⟩ : syracuseStep 262925 = 98597) (by norm_num)
theorem B197401 : Blo 171799 197401 := bbase (se 2 (by rfl) ⟨74025, by rfl⟩ : syracuseStep 197401 = 148051) (by norm_num)
theorem B295717 : Blo 171799 295717 := bbase (se 4 (by rfl) ⟨27723, by rfl⟩ : syracuseStep 295717 = 55447) (by norm_num)
theorem B262949 : Blo 171799 262949 := bbase (se 4 (by rfl) ⟨24651, by rfl⟩ : syracuseStep 262949 = 49303) (by norm_num)
theorem B394037 : Blo 171799 394037 := bbase (se 5 (by rfl) ⟨18470, by rfl⟩ : syracuseStep 394037 = 36941) (by norm_num)
theorem B262973 : Blo 171799 262973 := bbase (se 3 (by rfl) ⟨49307, by rfl⟩ : syracuseStep 262973 = 98615) (by norm_num)
theorem B197437 : Blo 171799 197437 := bbase (se 3 (by rfl) ⟨37019, by rfl⟩ : syracuseStep 197437 = 74039) (by norm_num)
theorem B394069 : Blo 171799 394069 := bbase (se 9 (by rfl) ⟨1154, by rfl⟩ : syracuseStep 394069 = 2309) (by norm_num)
theorem B262997 : Blo 171799 262997 := bbase (se 9 (by rfl) ⟨770, by rfl⟩ : syracuseStep 262997 = 1541) (by norm_num)
theorem B197473 : Blo 171799 197473 := bbase (se 2 (by rfl) ⟨74052, by rfl⟩ : syracuseStep 197473 = 148105) (by norm_num)
theorem B263021 : Blo 171799 263021 := bbase (se 3 (by rfl) ⟨49316, by rfl⟩ : syracuseStep 263021 = 98633) (by norm_num)
theorem B394109 : Blo 171799 394109 := bbase (se 3 (by rfl) ⟨73895, by rfl⟩ : syracuseStep 394109 = 147791) (by norm_num)
theorem B295805 : Blo 171799 295805 := bbase (se 3 (by rfl) ⟨55463, by rfl⟩ : syracuseStep 295805 = 110927) (by norm_num)
theorem B263045 : Blo 171799 263045 := bbase (se 4 (by rfl) ⟨24660, by rfl⟩ : syracuseStep 263045 = 49321) (by norm_num)
theorem B197509 : Blo 171799 197509 := bbase (se 4 (by rfl) ⟨18516, by rfl⟩ : syracuseStep 197509 = 37033) (by norm_num)
theorem B885653 : Blo 171799 885653 := bbase (se 6 (by rfl) ⟨20757, by rfl⟩ : syracuseStep 885653 = 41515) (by norm_num)
theorem B263069 : Blo 171799 263069 := bbase (se 3 (by rfl) ⟨49325, by rfl⟩ : syracuseStep 263069 = 98651) (by norm_num)
theorem B197545 : Blo 171799 197545 := bbase (se 2 (by rfl) ⟨74079, by rfl⟩ : syracuseStep 197545 = 148159) (by norm_num)
theorem B263093 : Blo 171799 263093 := bbase (se 5 (by rfl) ⟨12332, by rfl⟩ : syracuseStep 263093 = 24665) (by norm_num)
theorem B394181 : Blo 171799 394181 := bbase (se 4 (by rfl) ⟨36954, by rfl⟩ : syracuseStep 394181 = 73909) (by norm_num)
theorem B263117 : Blo 171799 263117 := bbase (se 3 (by rfl) ⟨49334, by rfl⟩ : syracuseStep 263117 = 98669) (by norm_num)
theorem B197581 : Blo 171799 197581 := bbase (se 3 (by rfl) ⟨37046, by rfl⟩ : syracuseStep 197581 = 74093) (by norm_num)
theorem B263141 : Blo 171799 263141 := bbase (se 4 (by rfl) ⟨24669, by rfl⟩ : syracuseStep 263141 = 49339) (by norm_num)
theorem B197617 : Blo 171799 197617 := bbase (se 2 (by rfl) ⟨74106, by rfl⟩ : syracuseStep 197617 = 148213) (by norm_num)
theorem B295933 : Blo 171799 295933 := bbase (se 3 (by rfl) ⟨55487, by rfl⟩ : syracuseStep 295933 = 110975) (by norm_num)
theorem B263165 : Blo 171799 263165 := bbase (se 3 (by rfl) ⟨49343, by rfl⟩ : syracuseStep 263165 = 98687) (by norm_num)
theorem B394253 : Blo 171799 394253 := bbase (se 3 (by rfl) ⟨73922, by rfl⟩ : syracuseStep 394253 = 147845) (by norm_num)
theorem B263189 : Blo 171799 263189 := bbase (se 6 (by rfl) ⟨6168, by rfl⟩ : syracuseStep 263189 = 12337) (by norm_num)
theorem B197653 : Blo 171799 197653 := bbase (se 6 (by rfl) ⟨4632, by rfl⟩ : syracuseStep 197653 = 9265) (by norm_num)
theorem B263213 : Blo 171799 263213 := bbase (se 3 (by rfl) ⟨49352, by rfl⟩ : syracuseStep 263213 = 98705) (by norm_num)
theorem B197689 : Blo 171799 197689 := bbase (se 2 (by rfl) ⟨74133, by rfl⟩ : syracuseStep 197689 = 148267) (by norm_num)
theorem B263237 : Blo 171799 263237 := bbase (se 4 (by rfl) ⟨24678, by rfl⟩ : syracuseStep 263237 = 49357) (by norm_num)
theorem B394325 : Blo 171799 394325 := bbase (se 8 (by rfl) ⟨2310, by rfl⟩ : syracuseStep 394325 = 4621) (by norm_num)
theorem B296021 : Blo 171799 296021 := bbase (se 8 (by rfl) ⟨1734, by rfl⟩ : syracuseStep 296021 = 3469) (by norm_num)
theorem B263261 : Blo 171799 263261 := bbase (se 3 (by rfl) ⟨49361, by rfl⟩ : syracuseStep 263261 = 98723) (by norm_num)
theorem B197725 : Blo 171799 197725 := bbase (se 3 (by rfl) ⟨37073, by rfl⟩ : syracuseStep 197725 = 74147) (by norm_num)
theorem B263285 : Blo 171799 263285 := bbase (se 5 (by rfl) ⟨12341, by rfl⟩ : syracuseStep 263285 = 24683) (by norm_num)
theorem B197761 : Blo 171799 197761 := bbase (se 2 (by rfl) ⟨74160, by rfl⟩ : syracuseStep 197761 = 148321) (by norm_num)
theorem B263309 : Blo 171799 263309 := bbase (se 3 (by rfl) ⟨49370, by rfl⟩ : syracuseStep 263309 = 98741) (by norm_num)
theorem B394397 : Blo 171799 394397 := bbase (se 3 (by rfl) ⟨73949, by rfl⟩ : syracuseStep 394397 = 147899) (by norm_num)
theorem B263333 : Blo 171799 263333 := bbase (se 4 (by rfl) ⟨24687, by rfl⟩ : syracuseStep 263333 = 49375) (by norm_num)
theorem B591029 : Blo 171799 591029 := bbase (se 5 (by rfl) ⟨27704, by rfl⟩ : syracuseStep 591029 = 55409) (by norm_num)
theorem B263357 : Blo 171799 263357 := bbase (se 3 (by rfl) ⟨49379, by rfl⟩ : syracuseStep 263357 = 98759) (by norm_num)
theorem B296149 : Blo 171799 296149 := bbase (se 7 (by rfl) ⟨3470, by rfl⟩ : syracuseStep 296149 = 6941) (by norm_num)
theorem B263381 : Blo 171799 263381 := bbase (se 7 (by rfl) ⟨3086, by rfl⟩ : syracuseStep 263381 = 6173) (by norm_num)
theorem B591077 : Blo 171799 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B394469 : Blo 171799 394469 := bbase (se 4 (by rfl) ⟨36981, by rfl⟩ : syracuseStep 394469 = 73963) (by norm_num)
theorem B263405 : Blo 171799 263405 := bbase (se 3 (by rfl) ⟨49388, by rfl⟩ : syracuseStep 263405 = 98777) (by norm_num)
theorem B263429 : Blo 171799 263429 := bbase (se 4 (by rfl) ⟨24696, by rfl⟩ : syracuseStep 263429 = 49393) (by norm_num)
theorem B263453 : Blo 171799 263453 := bbase (se 3 (by rfl) ⟨49397, by rfl⟩ : syracuseStep 263453 = 98795) (by norm_num)
theorem B394541 : Blo 171799 394541 := bbase (se 3 (by rfl) ⟨73976, by rfl⟩ : syracuseStep 394541 = 147953) (by norm_num)
theorem B296237 : Blo 171799 296237 := bbase (se 3 (by rfl) ⟨55544, by rfl⟩ : syracuseStep 296237 = 111089) (by norm_num)
theorem B656693 : Blo 171799 656693 := bbase (se 5 (by rfl) ⟨30782, by rfl⟩ : syracuseStep 656693 = 61565) (by norm_num)
theorem B263477 : Blo 171799 263477 := bbase (se 5 (by rfl) ⟨12350, by rfl⟩ : syracuseStep 263477 = 24701) (by norm_num)
theorem B263501 : Blo 171799 263501 := bbase (se 3 (by rfl) ⟨49406, by rfl⟩ : syracuseStep 263501 = 98813) (by norm_num)
theorem B263525 : Blo 171799 263525 := bbase (se 4 (by rfl) ⟨24705, by rfl⟩ : syracuseStep 263525 = 49411) (by norm_num)
theorem B394613 : Blo 171799 394613 := bbase (se 5 (by rfl) ⟨18497, by rfl⟩ : syracuseStep 394613 = 36995) (by norm_num)
theorem B263549 : Blo 171799 263549 := bbase (se 3 (by rfl) ⟨49415, by rfl⟩ : syracuseStep 263549 = 98831) (by norm_num)
theorem B263573 : Blo 171799 263573 := bbase (se 6 (by rfl) ⟨6177, by rfl⟩ : syracuseStep 263573 = 12355) (by norm_num)
theorem B296365 : Blo 171799 296365 := bbase (se 3 (by rfl) ⟨55568, by rfl⟩ : syracuseStep 296365 = 111137) (by norm_num)
theorem B263597 : Blo 171799 263597 := bbase (se 3 (by rfl) ⟨49424, by rfl⟩ : syracuseStep 263597 = 98849) (by norm_num)
theorem B394685 : Blo 171799 394685 := bbase (se 3 (by rfl) ⟨74003, by rfl⟩ : syracuseStep 394685 = 148007) (by norm_num)
theorem B263621 : Blo 171799 263621 := bbase (se 4 (by rfl) ⟨24714, by rfl⟩ : syracuseStep 263621 = 49429) (by norm_num)
theorem B263645 : Blo 171799 263645 := bbase (se 3 (by rfl) ⟨49433, by rfl⟩ : syracuseStep 263645 = 98867) (by norm_num)
theorem B329197 : Blo 171799 329197 := bbase (se 3 (by rfl) ⟨61724, by rfl⟩ : syracuseStep 329197 = 123449) (by norm_num)
theorem B263669 : Blo 171799 263669 := bbase (se 5 (by rfl) ⟨12359, by rfl⟩ : syracuseStep 263669 = 24719) (by norm_num)
theorem B394757 : Blo 171799 394757 := bbase (se 4 (by rfl) ⟨37008, by rfl⟩ : syracuseStep 394757 = 74017) (by norm_num)
theorem B296453 : Blo 171799 296453 := bbase (se 4 (by rfl) ⟨27792, by rfl⟩ : syracuseStep 296453 = 55585) (by norm_num)
theorem B263693 : Blo 171799 263693 := bbase (se 3 (by rfl) ⟨49442, by rfl⟩ : syracuseStep 263693 = 98885) (by norm_num)
theorem B394829 : Blo 171799 394829 := bbase (se 3 (by rfl) ⟨74030, by rfl⟩ : syracuseStep 394829 = 148061) (by norm_num)
theorem B656981 : Blo 171799 656981 := bbase (se 8 (by rfl) ⟨3849, by rfl⟩ : syracuseStep 656981 = 7699) (by norm_num)
theorem B591461 : Blo 171799 591461 := bbase (se 4 (by rfl) ⟨55449, by rfl⟩ : syracuseStep 591461 = 110899) (by norm_num)
theorem B329341 : Blo 171799 329341 := bbase (se 3 (by rfl) ⟨61751, by rfl⟩ : syracuseStep 329341 = 123503) (by norm_num)
theorem B296581 : Blo 171799 296581 := bbase (se 4 (by rfl) ⟨27804, by rfl⟩ : syracuseStep 296581 = 55609) (by norm_num)
theorem B394901 : Blo 171799 394901 := bbase (se 6 (by rfl) ⟨9255, by rfl⟩ : syracuseStep 394901 = 18511) (by norm_num)
theorem B394973 : Blo 171799 394973 := bbase (se 3 (by rfl) ⟨74057, by rfl⟩ : syracuseStep 394973 = 148115) (by norm_num)
theorem B329501 : Blo 171799 329501 := bbase (se 3 (by rfl) ⟨61781, by rfl⟩ : syracuseStep 329501 = 123563) (by norm_num)
theorem B395045 : Blo 171799 395045 := bbase (se 4 (by rfl) ⟨37035, by rfl⟩ : syracuseStep 395045 = 74071) (by norm_num)
theorem B493397 : Blo 171799 493397 := bbase (se 9 (by rfl) ⟨1445, by rfl⟩ : syracuseStep 493397 = 2891) (by norm_num)
theorem B198509 : Blo 171799 198509 := bbase (se 3 (by rfl) ⟨37220, by rfl⟩ : syracuseStep 198509 = 74441) (by norm_num)
theorem B395117 : Blo 171799 395117 := bbase (se 3 (by rfl) ⟨74084, by rfl⟩ : syracuseStep 395117 = 148169) (by norm_num)
theorem B427933 : Blo 171799 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B329645 : Blo 171799 329645 := bbase (se 3 (by rfl) ⟨61808, by rfl⟩ : syracuseStep 329645 = 123617) (by norm_num)
theorem B395189 : Blo 171799 395189 := bbase (se 5 (by rfl) ⟨18524, by rfl⟩ : syracuseStep 395189 = 37049) (by norm_num)
theorem B296893 : Blo 171799 296893 := bbase (se 3 (by rfl) ⟨55667, by rfl⟩ : syracuseStep 296893 = 111335) (by norm_num)
theorem B755669 : Blo 171799 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B395261 : Blo 171799 395261 := bbase (se 3 (by rfl) ⟨74111, by rfl⟩ : syracuseStep 395261 = 148223) (by norm_num)
theorem B591893 : Blo 171799 591893 := bbase (se 6 (by rfl) ⟨13872, by rfl⟩ : syracuseStep 591893 = 27745) (by norm_num)
theorem B395333 : Blo 171799 395333 := bbase (se 4 (by rfl) ⟨37062, by rfl⟩ : syracuseStep 395333 = 74125) (by norm_num)
theorem B395405 : Blo 171799 395405 := bbase (se 3 (by rfl) ⟨74138, by rfl⟩ : syracuseStep 395405 = 148277) (by norm_num)
theorem B886949 : Blo 171799 886949 := bbase (se 4 (by rfl) ⟨83151, by rfl⟩ : syracuseStep 886949 = 166303) (by norm_num)
theorem B329933 : Blo 171799 329933 := bbase (se 3 (by rfl) ⟨61862, by rfl⟩ : syracuseStep 329933 = 123725) (by norm_num)
theorem B395477 : Blo 171799 395477 := bbase (se 7 (by rfl) ⟨4634, by rfl⟩ : syracuseStep 395477 = 9269) (by norm_num)
theorem B2787605 : Blo 171799 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B395549 : Blo 171799 395549 := bbase (se 3 (by rfl) ⟨74165, by rfl⟩ : syracuseStep 395549 = 148331) (by norm_num)
theorem B330085 : Blo 171799 330085 := bbase (se 4 (by rfl) ⟨30945, by rfl⟩ : syracuseStep 330085 = 61891) (by norm_num)
theorem B592325 : Blo 171799 592325 := bbase (se 4 (by rfl) ⟨55530, by rfl⟩ : syracuseStep 592325 = 111061) (by norm_num)
theorem B625205 : Blo 171799 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B559685 : Blo 171799 559685 := bbase (se 4 (by rfl) ⟨52470, by rfl⟩ : syracuseStep 559685 = 104941) (by norm_num)
theorem B330389 : Blo 171799 330389 := bbase (se 6 (by rfl) ⟨7743, by rfl⟩ : syracuseStep 330389 = 15487) (by norm_num)
theorem B658165 : Blo 171799 658165 := bbase (se 5 (by rfl) ⟨30851, by rfl⟩ : syracuseStep 658165 = 61703) (by norm_num)
theorem B265037 : Blo 171799 265037 := bbase (se 3 (by rfl) ⟨49694, by rfl⟩ : syracuseStep 265037 = 99389) (by norm_num)
theorem B592757 : Blo 171799 592757 := bbase (se 5 (by rfl) ⟨27785, by rfl⟩ : syracuseStep 592757 = 55571) (by norm_num)
theorem B494581 : Blo 171799 494581 := bbase (se 5 (by rfl) ⟨23183, by rfl⟩ : syracuseStep 494581 = 46367) (by norm_num)
theorem B658469 : Blo 171799 658469 := bbase (se 4 (by rfl) ⟨61731, by rfl⟩ : syracuseStep 658469 = 123463) (by norm_num)
theorem B494741 : Blo 171799 494741 := bbase (se 6 (by rfl) ⟨11595, by rfl⟩ : syracuseStep 494741 = 23191) (by norm_num)
theorem B593189 : Blo 171799 593189 := bbase (se 4 (by rfl) ⟨55611, by rfl⟩ : syracuseStep 593189 = 111223) (by norm_num)
theorem B494981 : Blo 171799 494981 := bbase (se 4 (by rfl) ⟨46404, by rfl⟩ : syracuseStep 494981 = 92809) (by norm_num)
theorem B331141 : Blo 171799 331141 := bbase (se 4 (by rfl) ⟨31044, by rfl⟩ : syracuseStep 331141 = 62089) (by norm_num)
theorem B888245 : Blo 171799 888245 := bbase (se 5 (by rfl) ⟨41636, by rfl⟩ : syracuseStep 888245 = 83273) (by norm_num)
theorem B396733 : Blo 171799 396733 := bbase (se 3 (by rfl) ⟨74387, by rfl⟩ : syracuseStep 396733 = 148775) (by norm_num)
theorem B331285 : Blo 171799 331285 := bbase (se 6 (by rfl) ⟨7764, by rfl⟩ : syracuseStep 331285 = 15529) (by norm_num)
theorem B495173 : Blo 171799 495173 := bbase (se 4 (by rfl) ⟨46422, by rfl⟩ : syracuseStep 495173 = 92845) (by norm_num)
theorem B331445 : Blo 171799 331445 := bbase (se 5 (by rfl) ⟨15536, by rfl⟩ : syracuseStep 331445 = 31073) (by norm_num)
theorem B331589 : Blo 171799 331589 := bbase (se 4 (by rfl) ⟨31086, by rfl⟩ : syracuseStep 331589 = 62173) (by norm_num)
theorem B397181 : Blo 171799 397181 := bbase (se 3 (by rfl) ⟨74471, by rfl⟩ : syracuseStep 397181 = 148943) (by norm_num)
theorem B331877 : Blo 171799 331877 := bbase (se 4 (by rfl) ⟨31113, by rfl⟩ : syracuseStep 331877 = 62227) (by norm_num)
theorem B332029 : Blo 171799 332029 := bbase (se 3 (by rfl) ⟨62255, by rfl⟩ : syracuseStep 332029 = 124511) (by norm_num)
theorem B299261 : Blo 171799 299261 := bbase (se 3 (by rfl) ⟨56111, by rfl⟩ : syracuseStep 299261 = 112223) (by norm_num)
theorem B1118549 : Blo 171799 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B233869 : Blo 171799 233869 := bbase (se 3 (by rfl) ⟨43850, by rfl⟩ : syracuseStep 233869 = 87701) (by norm_num)
theorem B233933 : Blo 171799 233933 := bbase (se 3 (by rfl) ⟨43862, by rfl⟩ : syracuseStep 233933 = 87725) (by norm_num)
theorem B496165 : Blo 171799 496165 := bbase (se 4 (by rfl) ⟨46515, by rfl⟩ : syracuseStep 496165 = 93031) (by norm_num)
theorem B332333 : Blo 171799 332333 := bbase (se 3 (by rfl) ⟨62312, by rfl⟩ : syracuseStep 332333 = 124625) (by norm_num)
theorem B889541 : Blo 171799 889541 := bbase (se 4 (by rfl) ⟨83394, by rfl⟩ : syracuseStep 889541 = 166789) (by norm_num)
theorem B561941 : Blo 171799 561941 := bbase (se 6 (by rfl) ⟨13170, by rfl⟩ : syracuseStep 561941 = 26341) (by norm_num)
theorem B398141 : Blo 171799 398141 := bbase (se 3 (by rfl) ⟨74651, by rfl⟩ : syracuseStep 398141 = 149303) (by norm_num)
theorem B1676213 : Blo 171799 1676213 := bbase (se 5 (by rfl) ⟨78572, by rfl⟩ : syracuseStep 1676213 = 157145) (by norm_num)
theorem B660581 : Blo 171799 660581 := bbase (se 4 (by rfl) ⟨61929, by rfl⟩ : syracuseStep 660581 = 123859) (by norm_num)
theorem B333085 : Blo 171799 333085 := bbase (se 3 (by rfl) ⟨62453, by rfl⟩ : syracuseStep 333085 = 124907) (by norm_num)
theorem B660869 : Blo 171799 660869 := bbase (se 4 (by rfl) ⟨61956, by rfl⟩ : syracuseStep 660869 = 123913) (by norm_num)
theorem B333229 : Blo 171799 333229 := bbase (se 3 (by rfl) ⟨62480, by rfl⟩ : syracuseStep 333229 = 124961) (by norm_num)
theorem B562709 : Blo 171799 562709 := bbase (se 6 (by rfl) ⟨13188, by rfl⟩ : syracuseStep 562709 = 26377) (by norm_num)
theorem B333389 : Blo 171799 333389 := bbase (se 3 (by rfl) ⟨62510, by rfl⟩ : syracuseStep 333389 = 125021) (by norm_num)
theorem B497269 : Blo 171799 497269 := bbase (se 5 (by rfl) ⟨23309, by rfl⟩ : syracuseStep 497269 = 46619) (by norm_num)
theorem B333533 : Blo 171799 333533 := bbase (se 3 (by rfl) ⟨62537, by rfl⟩ : syracuseStep 333533 = 125075) (by norm_num)
theorem B399325 : Blo 171799 399325 := bbase (se 3 (by rfl) ⟨74873, by rfl⟩ : syracuseStep 399325 = 149747) (by norm_num)
theorem B563221 : Blo 171799 563221 := bbase (se 6 (by rfl) ⟨13200, by rfl⟩ : syracuseStep 563221 = 26401) (by norm_num)
theorem B5445845 : Blo 171799 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B891157 : Blo 171799 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B367109 : Blo 171799 367109 := bbase (se 4 (by rfl) ⟨34416, by rfl⟩ : syracuseStep 367109 = 68833) (by norm_num)
theorem B662053 : Blo 171799 662053 := bbase (se 4 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 662053 = 124135) (by norm_num)
theorem B367229 : Blo 171799 367229 := bbase (se 3 (by rfl) ⟨68855, by rfl⟩ : syracuseStep 367229 = 137711) (by norm_num)
theorem B662357 : Blo 171799 662357 := bbase (se 9 (by rfl) ⟨1940, by rfl⟩ : syracuseStep 662357 = 3881) (by norm_num)
theorem B891749 : Blo 171799 891749 := bbase (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) (by norm_num)
theorem B1579925 : Blo 171799 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B269333 : Blo 171799 269333 := bbase (se 6 (by rfl) ⟨6312, by rfl⟩ : syracuseStep 269333 = 12625) (by norm_num)
theorem B498773 : Blo 171799 498773 := bbase (se 8 (by rfl) ⟨2922, by rfl⟩ : syracuseStep 498773 = 5845) (by norm_num)
theorem B236701 : Blo 171799 236701 := bbase (se 3 (by rfl) ⟨44381, by rfl⟩ : syracuseStep 236701 = 88763) (by norm_num)
theorem B367861 : Blo 171799 367861 := bbase (se 5 (by rfl) ⟨17243, by rfl⟩ : syracuseStep 367861 = 34487) (by norm_num)
theorem B1318517 : Blo 171799 1318517 := bbase (se 5 (by rfl) ⟨61805, by rfl⟩ : syracuseStep 1318517 = 123611) (by norm_num)
theorem B335477 : Blo 171799 335477 := bbase (se 5 (by rfl) ⟨15725, by rfl⟩ : syracuseStep 335477 = 31451) (by norm_num)
theorem B466741 : Blo 171799 466741 := bbase (se 5 (by rfl) ⟨21878, by rfl⟩ : syracuseStep 466741 = 43757) (by norm_num)
theorem B630773 : Blo 171799 630773 := bbase (se 5 (by rfl) ⟨29567, by rfl⟩ : syracuseStep 630773 = 59135) (by norm_num)
theorem B401501 : Blo 171799 401501 := bbase (se 3 (by rfl) ⟨75281, by rfl⟩ : syracuseStep 401501 = 150563) (by norm_num)
theorem B368749 : Blo 171799 368749 := bbase (se 3 (by rfl) ⟨69140, by rfl⟩ : syracuseStep 368749 = 138281) (by norm_num)
theorem B991349 : Blo 171799 991349 := bbase (se 5 (by rfl) ⟨46469, by rfl⟩ : syracuseStep 991349 = 92939) (by norm_num)
theorem B2367701 : Blo 171799 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B368869 : Blo 171799 368869 := bbase (se 4 (by rfl) ⟨34581, by rfl⟩ : syracuseStep 368869 = 69163) (by norm_num)
theorem B827765 : Blo 171799 827765 := bbase (se 5 (by rfl) ⟨38801, by rfl⟩ : syracuseStep 827765 = 77603) (by norm_num)
theorem B631189 : Blo 171799 631189 := bbase (se 6 (by rfl) ⟨14793, by rfl⟩ : syracuseStep 631189 = 29587) (by norm_num)
theorem B369125 : Blo 171799 369125 := bbase (se 4 (by rfl) ⟨34605, by rfl⟩ : syracuseStep 369125 = 69211) (by norm_num)
theorem B1679957 : Blo 171799 1679957 := bbase (se 8 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 1679957 = 19687) (by norm_num)
theorem B500357 : Blo 171799 500357 := bbase (se 4 (by rfl) ⟨46908, by rfl⟩ : syracuseStep 500357 = 93817) (by norm_num)
theorem B828053 : Blo 171799 828053 := bbase (se 6 (by rfl) ⟨19407, by rfl⟩ : syracuseStep 828053 = 38815) (by norm_num)
theorem B434909 : Blo 171799 434909 := bbase (se 3 (by rfl) ⟨81545, by rfl⟩ : syracuseStep 434909 = 163091) (by norm_num)
theorem B795413 : Blo 171799 795413 := bbase (se 6 (by rfl) ⟨18642, by rfl⟩ : syracuseStep 795413 = 37285) (by norm_num)
theorem B664469 : Blo 171799 664469 := bbase (se 6 (by rfl) ⟨15573, by rfl⟩ : syracuseStep 664469 = 31147) (by norm_num)
theorem B435253 : Blo 171799 435253 := bbase (se 5 (by rfl) ⟨20402, by rfl⟩ : syracuseStep 435253 = 40805) (by norm_num)
theorem B631925 : Blo 171799 631925 := bbase (se 5 (by rfl) ⟨29621, by rfl⟩ : syracuseStep 631925 = 59243) (by norm_num)
theorem B435365 : Blo 171799 435365 := bbase (se 4 (by rfl) ⟨40815, by rfl⟩ : syracuseStep 435365 = 81631) (by norm_num)
theorem B664757 : Blo 171799 664757 := bbase (se 5 (by rfl) ⟨31160, by rfl⟩ : syracuseStep 664757 = 62321) (by norm_num)
theorem B795845 : Blo 171799 795845 := bbase (se 4 (by rfl) ⟨74610, by rfl⟩ : syracuseStep 795845 = 149221) (by norm_num)
theorem B992533 : Blo 171799 992533 := bbase (se 6 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 992533 = 46525) (by norm_num)
theorem B370013 : Blo 171799 370013 := bbase (se 3 (by rfl) ⟨69377, by rfl⟩ : syracuseStep 370013 = 138755) (by norm_num)
theorem B435557 : Blo 171799 435557 := bbase (se 4 (by rfl) ⟨40833, by rfl⟩ : syracuseStep 435557 = 81667) (by norm_num)
theorem B4793813 : Blo 171799 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B533989 : Blo 171799 533989 := bbase (se 4 (by rfl) ⟨50061, by rfl⟩ : syracuseStep 533989 = 100123) (by norm_num)
theorem B370253 : Blo 171799 370253 := bbase (se 3 (by rfl) ⟨69422, by rfl⟩ : syracuseStep 370253 = 138845) (by norm_num)
theorem B435901 : Blo 171799 435901 := bbase (se 3 (by rfl) ⟨81731, by rfl⟩ : syracuseStep 435901 = 163463) (by norm_num)
theorem B436013 : Blo 171799 436013 := bbase (se 3 (by rfl) ⟨81752, by rfl⟩ : syracuseStep 436013 = 163505) (by norm_num)
theorem B206653 : Blo 171799 206653 := bbase (se 3 (by rfl) ⟨38747, by rfl⟩ : syracuseStep 206653 = 77495) (by norm_num)
theorem B206749 : Blo 171799 206749 := bbase (se 3 (by rfl) ⟨38765, by rfl⟩ : syracuseStep 206749 = 77531) (by norm_num)
theorem B206797 : Blo 171799 206797 := bbase (se 3 (by rfl) ⟨38774, by rfl⟩ : syracuseStep 206797 = 77549) (by norm_num)
theorem B436205 : Blo 171799 436205 := bbase (se 3 (by rfl) ⟨81788, by rfl⟩ : syracuseStep 436205 = 163577) (by norm_num)
theorem B370757 : Blo 171799 370757 := bbase (se 4 (by rfl) ⟨34758, by rfl⟩ : syracuseStep 370757 = 69517) (by norm_num)
theorem B370765 : Blo 171799 370765 := bbase (se 3 (by rfl) ⟨69518, by rfl⟩ : syracuseStep 370765 = 139037) (by norm_num)
theorem B895157 : Blo 171799 895157 := bbase (se 5 (by rfl) ⟨41960, by rfl⟩ : syracuseStep 895157 = 83921) (by norm_num)
theorem B1124597 : Blo 171799 1124597 := bbase (se 5 (by rfl) ⟨52715, by rfl⟩ : syracuseStep 1124597 = 105431) (by norm_num)
theorem B436549 : Blo 171799 436549 := bbase (se 4 (by rfl) ⟨40926, by rfl⟩ : syracuseStep 436549 = 81853) (by norm_num)
theorem B665941 : Blo 171799 665941 := bbase (se 10 (by rfl) ⟨975, by rfl⟩ : syracuseStep 665941 = 1951) (by norm_num)
theorem B174493 : Blo 171799 174493 := bbase (se 3 (by rfl) ⟨32717, by rfl⟩ : syracuseStep 174493 = 65435) (by norm_num)
theorem B436661 : Blo 171799 436661 := bbase (se 5 (by rfl) ⟨20468, by rfl⟩ : syracuseStep 436661 = 40937) (by norm_num)
theorem B436853 : Blo 171799 436853 := bbase (se 5 (by rfl) ⟨20477, by rfl⟩ : syracuseStep 436853 = 40955) (by norm_num)
theorem B666245 : Blo 171799 666245 := bbase (se 4 (by rfl) ⟨62460, by rfl⟩ : syracuseStep 666245 = 124921) (by norm_num)
theorem B174745 : Blo 171799 174745 := bbase (se 2 (by rfl) ⟨65529, by rfl⟩ : syracuseStep 174745 = 131059) (by norm_num)
theorem B633509 : Blo 171799 633509 := bbase (se 4 (by rfl) ⟨59391, by rfl⟩ : syracuseStep 633509 = 118783) (by norm_num)
theorem B404165 : Blo 171799 404165 := bbase (se 4 (by rfl) ⟨37890, by rfl⟩ : syracuseStep 404165 = 75781) (by norm_num)
theorem B994069 : Blo 171799 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B469813 : Blo 171799 469813 := bbase (se 5 (by rfl) ⟨22022, by rfl⟩ : syracuseStep 469813 = 44045) (by norm_num)
theorem B699205 : Blo 171799 699205 := bbase (se 4 (by rfl) ⟨65550, by rfl⟩ : syracuseStep 699205 = 131101) (by norm_num)
theorem B437197 : Blo 171799 437197 := bbase (se 3 (by rfl) ⟨81974, by rfl⟩ : syracuseStep 437197 = 163949) (by norm_num)
theorem B175061 : Blo 171799 175061 := bbase (se 7 (by rfl) ⟨2051, by rfl⟩ : syracuseStep 175061 = 4103) (by norm_num)
theorem B797701 : Blo 171799 797701 := bbase (se 4 (by rfl) ⟨74784, by rfl⟩ : syracuseStep 797701 = 149569) (by norm_num)
theorem B437309 : Blo 171799 437309 := bbase (se 3 (by rfl) ⟨81995, by rfl⟩ : syracuseStep 437309 = 163991) (by norm_num)
theorem B208013 : Blo 171799 208013 := bbase (se 3 (by rfl) ⟨39002, by rfl⟩ : syracuseStep 208013 = 78005) (by norm_num)
theorem B797845 : Blo 171799 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B371893 : Blo 171799 371893 := bbase (se 5 (by rfl) ⟨17432, by rfl⟩ : syracuseStep 371893 = 34865) (by norm_num)
theorem B994517 : Blo 171799 994517 := bbase (se 7 (by rfl) ⟨11654, by rfl⟩ : syracuseStep 994517 = 23309) (by norm_num)
theorem B175321 : Blo 171799 175321 := bbase (se 2 (by rfl) ⟨65745, by rfl⟩ : syracuseStep 175321 = 131491) (by norm_num)
theorem B437501 : Blo 171799 437501 := bbase (se 3 (by rfl) ⟨82031, by rfl⟩ : syracuseStep 437501 = 164063) (by norm_num)
theorem B208181 : Blo 171799 208181 := bbase (se 5 (by rfl) ⟨9758, by rfl⟩ : syracuseStep 208181 = 19517) (by norm_num)
theorem B929141 : Blo 171799 929141 := bbase (se 5 (by rfl) ⟨43553, by rfl⟩ : syracuseStep 929141 = 87107) (by norm_num)
theorem B372269 : Blo 171799 372269 := bbase (se 3 (by rfl) ⟨69800, by rfl⟩ : syracuseStep 372269 = 139601) (by norm_num)
theorem B437845 : Blo 171799 437845 := bbase (se 8 (by rfl) ⟨2565, by rfl⟩ : syracuseStep 437845 = 5131) (by norm_num)
theorem B536149 : Blo 171799 536149 := bbase (se 8 (by rfl) ⟨3141, by rfl⟩ : syracuseStep 536149 = 6283) (by norm_num)
theorem B208489 : Blo 171799 208489 := bbase (se 2 (by rfl) ⟨78183, by rfl⟩ : syracuseStep 208489 = 156367) (by norm_num)
theorem B437957 : Blo 171799 437957 := bbase (se 4 (by rfl) ⟨41058, by rfl⟩ : syracuseStep 437957 = 82117) (by norm_num)
theorem B1486613 : Blo 171799 1486613 := bbase (se 6 (by rfl) ⟨34842, by rfl⟩ : syracuseStep 1486613 = 69685) (by norm_num)
theorem B208705 : Blo 171799 208705 := bbase (se 2 (by rfl) ⟨78264, by rfl⟩ : syracuseStep 208705 = 156529) (by norm_num)
theorem B2207573 : Blo 171799 2207573 := bbase (se 9 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 2207573 = 12935) (by norm_num)
theorem B1027957 : Blo 171799 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B438149 : Blo 171799 438149 := bbase (se 4 (by rfl) ⟨41076, by rfl⟩ : syracuseStep 438149 = 82153) (by norm_num)
theorem B372709 : Blo 171799 372709 := bbase (se 4 (by rfl) ⟨34941, by rfl⟩ : syracuseStep 372709 = 69883) (by norm_num)
theorem B209017 : Blo 171799 209017 := bbase (se 2 (by rfl) ⟨78381, by rfl⟩ : syracuseStep 209017 = 156763) (by norm_num)
theorem B897173 : Blo 171799 897173 := bbase (se 6 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 897173 = 42055) (by norm_num)
theorem B438493 : Blo 171799 438493 := bbase (se 3 (by rfl) ⟨82217, by rfl⟩ : syracuseStep 438493 = 164435) (by norm_num)
theorem B438605 : Blo 171799 438605 := bbase (se 3 (by rfl) ⟨82238, by rfl⟩ : syracuseStep 438605 = 164477) (by norm_num)
theorem B471413 : Blo 171799 471413 := bbase (se 5 (by rfl) ⟨22097, by rfl⟩ : syracuseStep 471413 = 44195) (by norm_num)
theorem B930197 : Blo 171799 930197 := bbase (se 6 (by rfl) ⟨21801, by rfl⟩ : syracuseStep 930197 = 43603) (by norm_num)
theorem B176549 : Blo 171799 176549 := bbase (se 4 (by rfl) ⟨16551, by rfl⟩ : syracuseStep 176549 = 33103) (by norm_num)
theorem B176569 : Blo 171799 176569 := bbase (se 2 (by rfl) ⟨66213, by rfl⟩ : syracuseStep 176569 = 132427) (by norm_num)
theorem B176585 : Blo 171799 176585 := bbase (se 2 (by rfl) ⟨66219, by rfl⟩ : syracuseStep 176585 = 132439) (by norm_num)
theorem B438797 : Blo 171799 438797 := bbase (se 3 (by rfl) ⟨82274, by rfl⟩ : syracuseStep 438797 = 164549) (by norm_num)
theorem B504517 : Blo 171799 504517 := bbase (se 4 (by rfl) ⟨47298, by rfl⟩ : syracuseStep 504517 = 94597) (by norm_num)
theorem B439141 : Blo 171799 439141 := bbase (se 4 (by rfl) ⟨41169, by rfl⟩ : syracuseStep 439141 = 82339) (by norm_num)
theorem B275357 : Blo 171799 275357 := bbase (se 3 (by rfl) ⟨51629, by rfl⟩ : syracuseStep 275357 = 103259) (by norm_num)
theorem B439253 : Blo 171799 439253 := bbase (se 7 (by rfl) ⟨5147, by rfl⟩ : syracuseStep 439253 = 10295) (by norm_num)
theorem B209893 : Blo 171799 209893 := bbase (se 4 (by rfl) ⟨19677, by rfl⟩ : syracuseStep 209893 = 39355) (by norm_num)
theorem B275557 : Blo 171799 275557 := bbase (se 4 (by rfl) ⟨25833, by rfl⟩ : syracuseStep 275557 = 51667) (by norm_num)
theorem B177269 : Blo 171799 177269 := bbase (se 5 (by rfl) ⟨8309, by rfl⟩ : syracuseStep 177269 = 16619) (by norm_num)
theorem B439445 : Blo 171799 439445 := bbase (se 6 (by rfl) ⟨10299, by rfl⟩ : syracuseStep 439445 = 20599) (by norm_num)
theorem B373909 : Blo 171799 373909 := bbase (se 6 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 373909 = 17527) (by norm_num)
theorem B472277 : Blo 171799 472277 := bbase (se 7 (by rfl) ⟨5534, by rfl⟩ : syracuseStep 472277 = 11069) (by norm_num)
theorem B701669 : Blo 171799 701669 := bbase (se 4 (by rfl) ⟨65781, by rfl⟩ : syracuseStep 701669 = 131563) (by norm_num)
theorem B832837 : Blo 171799 832837 := bbase (se 4 (by rfl) ⟨78078, by rfl⟩ : syracuseStep 832837 = 156157) (by norm_num)
theorem B177493 : Blo 171799 177493 := bbase (se 13 (by rfl) ⟨32, by rfl⟩ : syracuseStep 177493 = 65) (by norm_num)
theorem B275813 : Blo 171799 275813 := bbase (se 4 (by rfl) ⟨25857, by rfl⟩ : syracuseStep 275813 = 51715) (by norm_num)
theorem B996725 : Blo 171799 996725 := bbase (se 5 (by rfl) ⟨46721, by rfl⟩ : syracuseStep 996725 = 93443) (by norm_num)
theorem B210349 : Blo 171799 210349 := bbase (se 3 (by rfl) ⟨39440, by rfl⟩ : syracuseStep 210349 = 78881) (by norm_num)
theorem B439789 : Blo 171799 439789 := bbase (se 3 (by rfl) ⟨82460, by rfl⟩ : syracuseStep 439789 = 164921) (by norm_num)
theorem B210497 : Blo 171799 210497 := bbase (se 2 (by rfl) ⟨78936, by rfl⟩ : syracuseStep 210497 = 157873) (by norm_num)
theorem B439901 : Blo 171799 439901 := bbase (se 3 (by rfl) ⟨82481, by rfl⟩ : syracuseStep 439901 = 164963) (by norm_num)
theorem B210593 : Blo 171799 210593 := bbase (se 2 (by rfl) ⟨78972, by rfl⟩ : syracuseStep 210593 = 157945) (by norm_num)
theorem B210613 : Blo 171799 210613 := bbase (se 5 (by rfl) ⟨9872, by rfl⟩ : syracuseStep 210613 = 19745) (by norm_num)
theorem B341741 : Blo 171799 341741 := bbase (se 3 (by rfl) ⟨64076, by rfl⟩ : syracuseStep 341741 = 128153) (by norm_num)
theorem B440093 : Blo 171799 440093 := bbase (se 3 (by rfl) ⟨82517, by rfl⟩ : syracuseStep 440093 = 165035) (by norm_num)
theorem B210757 : Blo 171799 210757 := bbase (se 4 (by rfl) ⟨19758, by rfl⟩ : syracuseStep 210757 = 39517) (by norm_num)
theorem B374797 : Blo 171799 374797 := bbase (se 3 (by rfl) ⟨70274, by rfl⟩ : syracuseStep 374797 = 140549) (by norm_num)
theorem B440437 : Blo 171799 440437 := bbase (se 5 (by rfl) ⟨20645, by rfl⟩ : syracuseStep 440437 = 41291) (by norm_num)
theorem B440549 : Blo 171799 440549 := bbase (se 4 (by rfl) ⟨41301, by rfl⟩ : syracuseStep 440549 = 82603) (by norm_num)
theorem B899381 : Blo 171799 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B506261 : Blo 171799 506261 := bbase (se 6 (by rfl) ⟨11865, by rfl⟩ : syracuseStep 506261 = 23731) (by norm_num)
theorem B440741 : Blo 171799 440741 := bbase (se 4 (by rfl) ⟨41319, by rfl⟩ : syracuseStep 440741 = 82639) (by norm_num)
theorem B276941 : Blo 171799 276941 := bbase (se 3 (by rfl) ⟨51926, by rfl⟩ : syracuseStep 276941 = 103853) (by norm_num)
theorem B375293 : Blo 171799 375293 := bbase (se 3 (by rfl) ⟨70367, by rfl⟩ : syracuseStep 375293 = 140735) (by norm_num)
theorem B440909 : Blo 171799 440909 := bbase (se 3 (by rfl) ⟨82670, by rfl⟩ : syracuseStep 440909 = 165341) (by norm_num)
theorem B1489589 : Blo 171799 1489589 := bbase (se 5 (by rfl) ⟨69824, by rfl⟩ : syracuseStep 1489589 = 139649) (by norm_num)
theorem B441085 : Blo 171799 441085 := bbase (se 3 (by rfl) ⟨82703, by rfl⟩ : syracuseStep 441085 = 165407) (by norm_num)
theorem B441197 : Blo 171799 441197 := bbase (se 3 (by rfl) ⟨82724, by rfl⟩ : syracuseStep 441197 = 165449) (by norm_num)
theorem B277453 : Blo 171799 277453 := bbase (se 3 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 277453 = 104045) (by norm_num)
theorem B441389 : Blo 171799 441389 := bbase (se 3 (by rfl) ⟨82760, by rfl⟩ : syracuseStep 441389 = 165521) (by norm_num)
theorem B1326293 : Blo 171799 1326293 := bbase (se 7 (by rfl) ⟨15542, by rfl⟩ : syracuseStep 1326293 = 31085) (by norm_num)
theorem B441733 : Blo 171799 441733 := bbase (se 4 (by rfl) ⟨41412, by rfl⟩ : syracuseStep 441733 = 82825) (by norm_num)
theorem B179605 : Blo 171799 179605 := bbase (se 6 (by rfl) ⟨4209, by rfl⟩ : syracuseStep 179605 = 8419) (by norm_num)
theorem B4996565 : Blo 171799 4996565 := bbase (se 7 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 4996565 = 117107) (by norm_num)
theorem B277997 : Blo 171799 277997 := bbase (se 3 (by rfl) ⟨52124, by rfl⟩ : syracuseStep 277997 = 104249) (by norm_num)
theorem B441845 : Blo 171799 441845 := bbase (se 5 (by rfl) ⟨20711, by rfl⟩ : syracuseStep 441845 = 41423) (by norm_num)
theorem B212609 : Blo 171799 212609 := bbase (se 2 (by rfl) ⟨79728, by rfl⟩ : syracuseStep 212609 = 159457) (by norm_num)
theorem B442037 : Blo 171799 442037 := bbase (se 5 (by rfl) ⟨20720, by rfl⟩ : syracuseStep 442037 = 41441) (by norm_num)
theorem B245605 : Blo 171799 245605 := bbase (se 4 (by rfl) ⟨23025, by rfl⟩ : syracuseStep 245605 = 46051) (by norm_num)
theorem B442381 : Blo 171799 442381 := bbase (se 3 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 442381 = 165893) (by norm_num)
theorem B278549 : Blo 171799 278549 := bbase (se 6 (by rfl) ⟨6528, by rfl⟩ : syracuseStep 278549 = 13057) (by norm_num)
theorem B278581 : Blo 171799 278581 := bbase (se 5 (by rfl) ⟨13058, by rfl⟩ : syracuseStep 278581 = 26117) (by norm_num)
theorem B442493 : Blo 171799 442493 := bbase (se 3 (by rfl) ⟨82967, by rfl⟩ : syracuseStep 442493 = 165935) (by norm_num)
theorem B1589557 : Blo 171799 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B442685 : Blo 171799 442685 := bbase (se 3 (by rfl) ⟨83003, by rfl⟩ : syracuseStep 442685 = 166007) (by norm_num)
theorem B246197 : Blo 171799 246197 := bbase (se 5 (by rfl) ⟨11540, by rfl⟩ : syracuseStep 246197 = 23081) (by norm_num)
theorem B442837 : Blo 171799 442837 := bbase (se 7 (by rfl) ⟨5189, by rfl⟩ : syracuseStep 442837 = 10379) (by norm_num)
theorem B246277 : Blo 171799 246277 := bbase (se 4 (by rfl) ⟨23088, by rfl⟩ : syracuseStep 246277 = 46177) (by norm_num)
theorem B737909 : Blo 171799 737909 := bbase (se 5 (by rfl) ⟨34589, by rfl⟩ : syracuseStep 737909 = 69179) (by norm_num)
theorem B246397 : Blo 171799 246397 := bbase (se 3 (by rfl) ⟨46199, by rfl⟩ : syracuseStep 246397 = 92399) (by norm_num)
theorem B443029 : Blo 171799 443029 := bbase (se 6 (by rfl) ⟨10383, by rfl⟩ : syracuseStep 443029 = 20767) (by norm_num)
theorem B705205 : Blo 171799 705205 := bbase (se 5 (by rfl) ⟨33056, by rfl⟩ : syracuseStep 705205 = 66113) (by norm_num)
theorem B246493 : Blo 171799 246493 := bbase (se 3 (by rfl) ⟨46217, by rfl⟩ : syracuseStep 246493 = 92435) (by norm_num)
theorem B443141 : Blo 171799 443141 := bbase (se 4 (by rfl) ⟨41544, by rfl⟩ : syracuseStep 443141 = 83089) (by norm_num)
theorem B443333 : Blo 171799 443333 := bbase (se 4 (by rfl) ⟨41562, by rfl⟩ : syracuseStep 443333 = 83125) (by norm_num)
theorem B279509 : Blo 171799 279509 := bbase (se 7 (by rfl) ⟨3275, by rfl⟩ : syracuseStep 279509 = 6551) (by norm_num)
theorem B312445 : Blo 171799 312445 := bbase (se 3 (by rfl) ⟨58583, by rfl⟩ : syracuseStep 312445 = 117167) (by norm_num)
theorem B279733 : Blo 171799 279733 := bbase (se 5 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 279733 = 26225) (by norm_num)
theorem B246989 : Blo 171799 246989 := bbase (se 3 (by rfl) ⟨46310, by rfl⟩ : syracuseStep 246989 = 92621) (by norm_num)
theorem B836837 : Blo 171799 836837 := bbase (se 4 (by rfl) ⟨78453, by rfl⟩ : syracuseStep 836837 = 156907) (by norm_num)
theorem B443677 : Blo 171799 443677 := bbase (se 3 (by rfl) ⟨83189, by rfl⟩ : syracuseStep 443677 = 166379) (by norm_num)
theorem B443789 : Blo 171799 443789 := bbase (se 3 (by rfl) ⟨83210, by rfl⟩ : syracuseStep 443789 = 166421) (by norm_num)
theorem B837029 : Blo 171799 837029 := bbase (se 4 (by rfl) ⟨78471, by rfl⟩ : syracuseStep 837029 = 156943) (by norm_num)
theorem B1066517 : Blo 171799 1066517 := bbase (se 6 (by rfl) ⟨24996, by rfl⟩ : syracuseStep 1066517 = 49993) (by norm_num)
theorem B706117 : Blo 171799 706117 := bbase (se 4 (by rfl) ⟨66198, by rfl⟩ : syracuseStep 706117 = 132397) (by norm_num)
theorem B443981 : Blo 171799 443981 := bbase (se 3 (by rfl) ⟨83246, by rfl⟩ : syracuseStep 443981 = 166493) (by norm_num)
theorem B280189 : Blo 171799 280189 := bbase (se 3 (by rfl) ⟨52535, by rfl⟩ : syracuseStep 280189 = 105071) (by norm_num)
theorem B673429 : Blo 171799 673429 := bbase (se 6 (by rfl) ⟨15783, by rfl⟩ : syracuseStep 673429 = 31567) (by norm_num)
theorem B280253 : Blo 171799 280253 := bbase (se 3 (by rfl) ⟨52547, by rfl⟩ : syracuseStep 280253 = 105095) (by norm_num)
theorem B870101 : Blo 171799 870101 := bbase (se 7 (by rfl) ⟨10196, by rfl⟩ : syracuseStep 870101 = 20393) (by norm_num)
theorem B247541 : Blo 171799 247541 := bbase (se 5 (by rfl) ⟨11603, by rfl⟩ : syracuseStep 247541 = 23207) (by norm_num)
theorem B444325 : Blo 171799 444325 := bbase (se 4 (by rfl) ⟨41655, by rfl⟩ : syracuseStep 444325 = 83311) (by norm_num)
theorem B444437 : Blo 171799 444437 := bbase (se 6 (by rfl) ⟨10416, by rfl⟩ : syracuseStep 444437 = 20833) (by norm_num)
theorem B313541 : Blo 171799 313541 := bbase (se 4 (by rfl) ⟨29394, by rfl⟩ : syracuseStep 313541 = 58789) (by norm_num)
theorem B444629 : Blo 171799 444629 := bbase (se 7 (by rfl) ⟨5210, by rfl⟩ : syracuseStep 444629 = 10421) (by norm_num)
theorem B739685 : Blo 171799 739685 := bbase (se 4 (by rfl) ⟨69345, by rfl⟩ : syracuseStep 739685 = 138691) (by norm_num)
theorem B215473 : Blo 171799 215473 := bbase (se 2 (by rfl) ⟨80802, by rfl⟩ : syracuseStep 215473 = 161605) (by norm_num)
theorem B248293 : Blo 171799 248293 := bbase (se 4 (by rfl) ⟨23277, by rfl⟩ : syracuseStep 248293 = 46555) (by norm_num)
theorem B444973 : Blo 171799 444973 := bbase (se 3 (by rfl) ⟨83432, by rfl⟩ : syracuseStep 444973 = 166865) (by norm_num)
theorem B739925 : Blo 171799 739925 := bbase (se 8 (by rfl) ⟨4335, by rfl⟩ : syracuseStep 739925 = 8671) (by norm_num)
theorem B2378645 : Blo 171799 2378645 := bbase (se 6 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 2378645 = 111499) (by norm_num)
theorem B871397 : Blo 171799 871397 := bbase (se 4 (by rfl) ⟨81693, by rfl⟩ : syracuseStep 871397 = 163387) (by norm_num)
theorem B281573 : Blo 171799 281573 := bbase (se 4 (by rfl) ⟨26397, by rfl⟩ : syracuseStep 281573 = 52795) (by norm_num)
theorem B183469 : Blo 171799 183469 := bbase (se 3 (by rfl) ⟨34400, by rfl⟩ : syracuseStep 183469 = 68801) (by norm_num)
theorem B249085 : Blo 171799 249085 := bbase (se 3 (by rfl) ⟨46703, by rfl⟩ : syracuseStep 249085 = 93407) (by norm_num)
theorem B2379029 : Blo 171799 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B380189 : Blo 171799 380189 := bbase (se 3 (by rfl) ⟨71285, by rfl⟩ : syracuseStep 380189 = 142571) (by norm_num)
theorem B249421 : Blo 171799 249421 := bbase (se 3 (by rfl) ⟨46766, by rfl⟩ : syracuseStep 249421 = 93533) (by norm_num)
theorem B183913 : Blo 171799 183913 := bbase (se 2 (by rfl) ⟨68967, by rfl⟩ : syracuseStep 183913 = 137935) (by norm_num)
theorem B184033 : Blo 171799 184033 := bbase (se 2 (by rfl) ⟨69012, by rfl⟩ : syracuseStep 184033 = 138025) (by norm_num)
theorem B315133 : Blo 171799 315133 := bbase (se 3 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 315133 = 118175) (by norm_num)
theorem B249637 : Blo 171799 249637 := bbase (se 4 (by rfl) ⟨23403, by rfl⟩ : syracuseStep 249637 = 46807) (by norm_num)
theorem B708533 : Blo 171799 708533 := bbase (se 5 (by rfl) ⟨33212, by rfl⟩ : syracuseStep 708533 = 66425) (by norm_num)
theorem B184285 : Blo 171799 184285 := bbase (se 3 (by rfl) ⟨34553, by rfl⟩ : syracuseStep 184285 = 69107) (by norm_num)
theorem B184289 : Blo 171799 184289 := bbase (se 2 (by rfl) ⟨69108, by rfl⟩ : syracuseStep 184289 = 138217) (by norm_num)
theorem B708581 : Blo 171799 708581 := bbase (se 4 (by rfl) ⟨66429, by rfl⟩ : syracuseStep 708581 = 132859) (by norm_num)
theorem B250013 : Blo 171799 250013 := bbase (se 3 (by rfl) ⟨46877, by rfl⟩ : syracuseStep 250013 = 93755) (by norm_num)
theorem B872693 : Blo 171799 872693 := bbase (se 5 (by rfl) ⟨40907, by rfl⟩ : syracuseStep 872693 = 81815) (by norm_num)
theorem B348565 : Blo 171799 348565 := bbase (se 6 (by rfl) ⟨8169, by rfl⟩ : syracuseStep 348565 = 16339) (by norm_num)
theorem B217505 : Blo 171799 217505 := bbase (se 2 (by rfl) ⟨81564, by rfl⟩ : syracuseStep 217505 = 163129) (by norm_num)
theorem B348629 : Blo 171799 348629 := bbase (se 7 (by rfl) ⟨4085, by rfl⟩ : syracuseStep 348629 = 8171) (by norm_num)
theorem B217561 : Blo 171799 217561 := bbase (se 2 (by rfl) ⟨81585, by rfl⟩ : syracuseStep 217561 = 163171) (by norm_num)
theorem B184853 : Blo 171799 184853 := bbase (se 6 (by rfl) ⟨4332, by rfl⟩ : syracuseStep 184853 = 8665) (by norm_num)
theorem B217657 : Blo 171799 217657 := bbase (se 2 (by rfl) ⟨81621, by rfl⟩ : syracuseStep 217657 = 163243) (by norm_num)
theorem B185041 : Blo 171799 185041 := bbase (se 2 (by rfl) ⟨69390, by rfl⟩ : syracuseStep 185041 = 138781) (by norm_num)
theorem B217829 : Blo 171799 217829 := bbase (se 4 (by rfl) ⟨20421, by rfl⟩ : syracuseStep 217829 = 40843) (by norm_num)
theorem B217885 : Blo 171799 217885 := bbase (se 3 (by rfl) ⟨40853, by rfl⟩ : syracuseStep 217885 = 81707) (by norm_num)
theorem B414517 : Blo 171799 414517 := bbase (se 5 (by rfl) ⟨19430, by rfl⟩ : syracuseStep 414517 = 38861) (by norm_num)
theorem B742213 : Blo 171799 742213 := bbase (se 4 (by rfl) ⟨69582, by rfl⟩ : syracuseStep 742213 = 139165) (by norm_num)
theorem B7131989 : Blo 171799 7131989 := bbase (se 9 (by rfl) ⟨20894, by rfl⟩ : syracuseStep 7131989 = 41789) (by norm_num)
theorem B217981 : Blo 171799 217981 := bbase (se 3 (by rfl) ⟨40871, by rfl⟩ : syracuseStep 217981 = 81743) (by norm_num)
theorem B1659797 : Blo 171799 1659797 := bbase (se 6 (by rfl) ⟨38901, by rfl⟩ : syracuseStep 1659797 = 77803) (by norm_num)
theorem B316381 : Blo 171799 316381 := bbase (se 3 (by rfl) ⟨59321, by rfl⟩ : syracuseStep 316381 = 118643) (by norm_num)
theorem B218153 : Blo 171799 218153 := bbase (se 2 (by rfl) ⟨81807, by rfl⟩ : syracuseStep 218153 = 163615) (by norm_num)
theorem B218209 : Blo 171799 218209 := bbase (se 2 (by rfl) ⟨81828, by rfl⟩ : syracuseStep 218209 = 163657) (by norm_num)
theorem B218305 : Blo 171799 218305 := bbase (se 2 (by rfl) ⟨81864, by rfl⟩ : syracuseStep 218305 = 163729) (by norm_num)
theorem B316669 : Blo 171799 316669 := bbase (se 3 (by rfl) ⟨59375, by rfl⟩ : syracuseStep 316669 = 118751) (by norm_num)
theorem B218477 : Blo 171799 218477 := bbase (se 3 (by rfl) ⟨40964, by rfl⟩ : syracuseStep 218477 = 81929) (by norm_num)
theorem B218533 : Blo 171799 218533 := bbase (se 4 (by rfl) ⟨20487, by rfl⟩ : syracuseStep 218533 = 40975) (by norm_num)
theorem B841141 : Blo 171799 841141 := bbase (se 5 (by rfl) ⟨39428, by rfl⟩ : syracuseStep 841141 = 78857) (by norm_num)
theorem B415181 : Blo 171799 415181 := bbase (se 3 (by rfl) ⟨77846, by rfl⟩ : syracuseStep 415181 = 155693) (by norm_num)
theorem B873989 : Blo 171799 873989 := bbase (se 4 (by rfl) ⟨81936, by rfl⟩ : syracuseStep 873989 = 163873) (by norm_num)
theorem B218629 : Blo 171799 218629 := bbase (se 4 (by rfl) ⟨20496, by rfl⟩ : syracuseStep 218629 = 40993) (by norm_num)
theorem B185861 : Blo 171799 185861 := bbase (se 4 (by rfl) ⟨17424, by rfl⟩ : syracuseStep 185861 = 34849) (by norm_num)
theorem B349733 : Blo 171799 349733 := bbase (se 4 (by rfl) ⟨32787, by rfl⟩ : syracuseStep 349733 = 65575) (by norm_num)
theorem B218801 : Blo 171799 218801 := bbase (se 2 (by rfl) ⟨82050, by rfl⟩ : syracuseStep 218801 = 164101) (by norm_num)
theorem B218857 : Blo 171799 218857 := bbase (se 2 (by rfl) ⟨82071, by rfl⟩ : syracuseStep 218857 = 164143) (by norm_num)
theorem B218953 : Blo 171799 218953 := bbase (se 2 (by rfl) ⟨82107, by rfl⟩ : syracuseStep 218953 = 164215) (by norm_num)
theorem B186305 : Blo 171799 186305 := bbase (se 2 (by rfl) ⟨69864, by rfl⟩ : syracuseStep 186305 = 139729) (by norm_num)
theorem B219125 : Blo 171799 219125 := bbase (se 5 (by rfl) ⟨10271, by rfl⟩ : syracuseStep 219125 = 20543) (by norm_num)
theorem B186397 : Blo 171799 186397 := bbase (se 3 (by rfl) ⟨34949, by rfl⟩ : syracuseStep 186397 = 69899) (by norm_num)
theorem B219181 : Blo 171799 219181 := bbase (se 3 (by rfl) ⟨41096, by rfl⟩ : syracuseStep 219181 = 82193) (by norm_num)
theorem B219277 : Blo 171799 219277 := bbase (se 3 (by rfl) ⟨41114, by rfl⟩ : syracuseStep 219277 = 82229) (by norm_num)
theorem B2513045 : Blo 171799 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B186553 : Blo 171799 186553 := bbase (se 2 (by rfl) ⟨69957, by rfl⟩ : syracuseStep 186553 = 139915) (by norm_num)
theorem B743701 : Blo 171799 743701 := bbase (se 6 (by rfl) ⟨17430, by rfl⟩ : syracuseStep 743701 = 34861) (by norm_num)
theorem B743717 : Blo 171799 743717 := bbase (se 4 (by rfl) ⟨69723, by rfl⟩ : syracuseStep 743717 = 139447) (by norm_num)
theorem B219449 : Blo 171799 219449 := bbase (se 2 (by rfl) ⟨82293, by rfl⟩ : syracuseStep 219449 = 164587) (by norm_num)
theorem B219505 : Blo 171799 219505 := bbase (se 2 (by rfl) ⟨82314, by rfl⟩ : syracuseStep 219505 = 164629) (by norm_num)
theorem B186769 : Blo 171799 186769 := bbase (se 2 (by rfl) ⟨70038, by rfl⟩ : syracuseStep 186769 = 140077) (by norm_num)
theorem B219601 : Blo 171799 219601 := bbase (se 2 (by rfl) ⟨82350, by rfl⟩ : syracuseStep 219601 = 164701) (by norm_num)
theorem B186985 : Blo 171799 186985 := bbase (se 2 (by rfl) ⟨70119, by rfl⟩ : syracuseStep 186985 = 140239) (by norm_num)
theorem B219773 : Blo 171799 219773 := bbase (se 3 (by rfl) ⟨41207, by rfl⟩ : syracuseStep 219773 = 82415) (by norm_num)
theorem B580229 : Blo 171799 580229 := bbase (se 4 (by rfl) ⟨54396, by rfl⟩ : syracuseStep 580229 = 108793) (by norm_num)
theorem B187057 : Blo 171799 187057 := bbase (se 2 (by rfl) ⟨70146, by rfl⟩ : syracuseStep 187057 = 140293) (by norm_num)
theorem B219829 : Blo 171799 219829 := bbase (se 5 (by rfl) ⟨10304, by rfl⟩ : syracuseStep 219829 = 20609) (by norm_num)
theorem B875285 : Blo 171799 875285 := bbase (se 6 (by rfl) ⟨20514, by rfl⟩ : syracuseStep 875285 = 41029) (by norm_num)
theorem B219925 : Blo 171799 219925 := bbase (se 6 (by rfl) ⟨5154, by rfl⟩ : syracuseStep 219925 = 10309) (by norm_num)
theorem B1334069 : Blo 171799 1334069 := bbase (se 5 (by rfl) ⟨62534, by rfl⟩ : syracuseStep 1334069 = 125069) (by norm_num)
theorem B416573 : Blo 171799 416573 := bbase (se 3 (by rfl) ⟨78107, by rfl⟩ : syracuseStep 416573 = 156215) (by norm_num)
theorem B2087765 : Blo 171799 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B842645 : Blo 171799 842645 := bbase (se 6 (by rfl) ⟨19749, by rfl⟩ : syracuseStep 842645 = 39499) (by norm_num)
theorem B416669 : Blo 171799 416669 := bbase (se 3 (by rfl) ⟨78125, by rfl⟩ : syracuseStep 416669 = 156251) (by norm_num)
theorem B220097 : Blo 171799 220097 := bbase (se 2 (by rfl) ⟨82536, by rfl⟩ : syracuseStep 220097 = 165073) (by norm_num)
theorem B220153 : Blo 171799 220153 := bbase (se 2 (by rfl) ⟨82557, by rfl⟩ : syracuseStep 220153 = 165115) (by norm_num)
theorem B187429 : Blo 171799 187429 := bbase (se 4 (by rfl) ⟨17571, by rfl⟩ : syracuseStep 187429 = 35143) (by norm_num)
theorem B580661 : Blo 171799 580661 := bbase (se 5 (by rfl) ⟨27218, by rfl⟩ : syracuseStep 580661 = 54437) (by norm_num)
theorem B220249 : Blo 171799 220249 := bbase (se 2 (by rfl) ⟨82593, by rfl⟩ : syracuseStep 220249 = 165187) (by norm_num)
theorem B973973 : Blo 171799 973973 := bbase (se 6 (by rfl) ⟨22827, by rfl⟩ : syracuseStep 973973 = 45655) (by norm_num)
theorem B253085 : Blo 171799 253085 := bbase (se 3 (by rfl) ⟨47453, by rfl⟩ : syracuseStep 253085 = 94907) (by norm_num)
theorem B220421 : Blo 171799 220421 := bbase (se 4 (by rfl) ⟨20664, by rfl⟩ : syracuseStep 220421 = 41329) (by norm_num)
theorem B220477 : Blo 171799 220477 := bbase (se 3 (by rfl) ⟨41339, by rfl⟩ : syracuseStep 220477 = 82679) (by norm_num)
theorem B220573 : Blo 171799 220573 := bbase (se 3 (by rfl) ⟨41357, by rfl⟩ : syracuseStep 220573 = 82715) (by norm_num)
theorem B581093 : Blo 171799 581093 := bbase (se 4 (by rfl) ⟨54477, by rfl⟩ : syracuseStep 581093 = 108955) (by norm_num)
theorem B712165 : Blo 171799 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B843317 : Blo 171799 843317 := bbase (se 5 (by rfl) ⟨39530, by rfl⟩ : syracuseStep 843317 = 79061) (by norm_num)
theorem B220745 : Blo 171799 220745 := bbase (se 2 (by rfl) ⟨82779, by rfl⟩ : syracuseStep 220745 = 165559) (by norm_num)
theorem B220801 : Blo 171799 220801 := bbase (se 2 (by rfl) ⟨82800, by rfl⟩ : syracuseStep 220801 = 165601) (by norm_num)
theorem B2219669 : Blo 171799 2219669 := bbase (se 6 (by rfl) ⟨52023, by rfl⟩ : syracuseStep 2219669 = 104047) (by norm_num)
theorem B220897 : Blo 171799 220897 := bbase (se 2 (by rfl) ⟨82836, by rfl⟩ : syracuseStep 220897 = 165673) (by norm_num)
theorem B221069 : Blo 171799 221069 := bbase (se 3 (by rfl) ⟨41450, by rfl⟩ : syracuseStep 221069 = 82901) (by norm_num)
theorem B581525 : Blo 171799 581525 := bbase (se 6 (by rfl) ⟨13629, by rfl⟩ : syracuseStep 581525 = 27259) (by norm_num)
theorem B942005 : Blo 171799 942005 := bbase (se 5 (by rfl) ⟨44156, by rfl⟩ : syracuseStep 942005 = 88313) (by norm_num)
theorem B221125 : Blo 171799 221125 := bbase (se 4 (by rfl) ⟨20730, by rfl⟩ : syracuseStep 221125 = 41461) (by norm_num)
theorem B876581 : Blo 171799 876581 := bbase (se 4 (by rfl) ⟨82179, by rfl⟩ : syracuseStep 876581 = 164359) (by norm_num)
theorem B221221 : Blo 171799 221221 := bbase (se 4 (by rfl) ⟨20739, by rfl⟩ : syracuseStep 221221 = 41479) (by norm_num)
theorem B909413 : Blo 171799 909413 := bbase (se 4 (by rfl) ⟨85257, by rfl⟩ : syracuseStep 909413 = 170515) (by norm_num)
theorem B221393 : Blo 171799 221393 := bbase (se 2 (by rfl) ⟨83022, by rfl⟩ : syracuseStep 221393 = 166045) (by norm_num)
theorem B221449 : Blo 171799 221449 := bbase (se 2 (by rfl) ⟨83043, by rfl⟩ : syracuseStep 221449 = 166087) (by norm_num)
theorem B581957 : Blo 171799 581957 := bbase (se 4 (by rfl) ⟨54558, by rfl⟩ : syracuseStep 581957 = 109117) (by norm_num)
theorem B221545 : Blo 171799 221545 := bbase (se 2 (by rfl) ⟨83079, by rfl⟩ : syracuseStep 221545 = 166159) (by norm_num)
theorem B745973 : Blo 171799 745973 := bbase (se 5 (by rfl) ⟨34967, by rfl⟩ : syracuseStep 745973 = 69935) (by norm_num)
theorem B221717 : Blo 171799 221717 := bbase (se 6 (by rfl) ⟨5196, by rfl⟩ : syracuseStep 221717 = 10393) (by norm_num)
theorem B221773 : Blo 171799 221773 := bbase (se 3 (by rfl) ⟨41582, by rfl⟩ : syracuseStep 221773 = 83165) (by norm_num)
theorem B221869 : Blo 171799 221869 := bbase (se 3 (by rfl) ⟨41600, by rfl⟩ : syracuseStep 221869 = 83201) (by norm_num)
theorem B582389 : Blo 171799 582389 := bbase (se 5 (by rfl) ⟨27299, by rfl⟩ : syracuseStep 582389 = 54599) (by norm_num)
theorem B222041 : Blo 171799 222041 := bbase (se 2 (by rfl) ⟨83265, by rfl⟩ : syracuseStep 222041 = 166531) (by norm_num)
theorem B844661 : Blo 171799 844661 := bbase (se 5 (by rfl) ⟨39593, by rfl⟩ : syracuseStep 844661 = 79187) (by norm_num)
theorem B222097 : Blo 171799 222097 := bbase (se 2 (by rfl) ⟨83286, by rfl⟩ : syracuseStep 222097 = 166573) (by norm_num)
theorem B418765 : Blo 171799 418765 := bbase (se 3 (by rfl) ⟨78518, by rfl⟩ : syracuseStep 418765 = 157037) (by norm_num)
theorem B1369045 : Blo 171799 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B222193 : Blo 171799 222193 := bbase (se 2 (by rfl) ⟨83322, by rfl⟩ : syracuseStep 222193 = 166645) (by norm_num)
theorem B222365 : Blo 171799 222365 := bbase (se 3 (by rfl) ⟨41693, by rfl⟩ : syracuseStep 222365 = 83387) (by norm_num)
theorem B582821 : Blo 171799 582821 := bbase (se 4 (by rfl) ⟨54639, by rfl⟩ : syracuseStep 582821 = 109279) (by norm_num)
theorem B189653 : Blo 171799 189653 := bbase (se 7 (by rfl) ⟨2222, by rfl⟩ : syracuseStep 189653 = 4445) (by norm_num)
theorem B222421 : Blo 171799 222421 := bbase (se 7 (by rfl) ⟨2606, by rfl⟩ : syracuseStep 222421 = 5213) (by norm_num)
theorem B877877 : Blo 171799 877877 := bbase (se 5 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 877877 = 82301) (by norm_num)
theorem B386365 : Blo 171799 386365 := bbase (se 3 (by rfl) ⟨72443, by rfl⟩ : syracuseStep 386365 = 144887) (by norm_num)
theorem B419165 : Blo 171799 419165 := bbase (se 3 (by rfl) ⟨78593, by rfl⟩ : syracuseStep 419165 = 157187) (by norm_num)
theorem B222629 : Blo 171799 222629 := bbase (se 4 (by rfl) ⟨20871, by rfl⟩ : syracuseStep 222629 = 41743) (by norm_num)
theorem B386549 : Blo 171799 386549 := bbase (se 5 (by rfl) ⟨18119, by rfl⟩ : syracuseStep 386549 = 36239) (by norm_num)
theorem B419381 : Blo 171799 419381 := bbase (se 5 (by rfl) ⟨19658, by rfl⟩ : syracuseStep 419381 = 39317) (by norm_num)
theorem B386621 : Blo 171799 386621 := bbase (se 3 (by rfl) ⟨72491, by rfl⟩ : syracuseStep 386621 = 144983) (by norm_num)
theorem B583253 : Blo 171799 583253 := bbase (se 8 (by rfl) ⟨3417, by rfl⟩ : syracuseStep 583253 = 6835) (by norm_num)
theorem B386693 : Blo 171799 386693 := bbase (se 4 (by rfl) ⟨36252, by rfl⟩ : syracuseStep 386693 = 72505) (by norm_num)
theorem B648901 : Blo 171799 648901 := bbase (se 4 (by rfl) ⟨60834, by rfl⟩ : syracuseStep 648901 = 121669) (by norm_num)
theorem B386765 : Blo 171799 386765 := bbase (se 3 (by rfl) ⟨72518, by rfl⟩ : syracuseStep 386765 = 145037) (by norm_num)
theorem B386837 : Blo 171799 386837 := bbase (se 6 (by rfl) ⟨9066, by rfl⟩ : syracuseStep 386837 = 18133) (by norm_num)
theorem B386909 : Blo 171799 386909 := bbase (se 3 (by rfl) ⟨72545, by rfl⟩ : syracuseStep 386909 = 145091) (by norm_num)
theorem B419717 : Blo 171799 419717 := bbase (se 4 (by rfl) ⟨39348, by rfl⟩ : syracuseStep 419717 = 78697) (by norm_num)
theorem B386981 : Blo 171799 386981 := bbase (se 4 (by rfl) ⟨36279, by rfl⟩ : syracuseStep 386981 = 72559) (by norm_num)
theorem B387053 : Blo 171799 387053 := bbase (se 3 (by rfl) ⟨72572, by rfl⟩ : syracuseStep 387053 = 145145) (by norm_num)
theorem B583685 : Blo 171799 583685 := bbase (se 4 (by rfl) ⟨54720, by rfl⟩ : syracuseStep 583685 = 109441) (by norm_num)
theorem B1107989 : Blo 171799 1107989 := bbase (se 6 (by rfl) ⟨25968, by rfl⟩ : syracuseStep 1107989 = 51937) (by norm_num)
theorem B387125 : Blo 171799 387125 := bbase (se 5 (by rfl) ⟨18146, by rfl⟩ : syracuseStep 387125 = 36293) (by norm_num)
theorem B387197 : Blo 171799 387197 := bbase (se 3 (by rfl) ⟨72599, by rfl⟩ : syracuseStep 387197 = 145199) (by norm_num)
theorem B354461 : Blo 171799 354461 := bbase (se 3 (by rfl) ⟨66461, by rfl⟩ : syracuseStep 354461 = 132923) (by norm_num)
theorem B387269 : Blo 171799 387269 := bbase (se 4 (by rfl) ⟨36306, by rfl⟩ : syracuseStep 387269 = 72613) (by norm_num)
theorem B387341 : Blo 171799 387341 := bbase (se 3 (by rfl) ⟨72626, by rfl⟩ : syracuseStep 387341 = 145253) (by norm_num)
theorem B420109 : Blo 171799 420109 := bbase (se 3 (by rfl) ⟨78770, by rfl⟩ : syracuseStep 420109 = 157541) (by norm_num)
theorem B387413 : Blo 171799 387413 := bbase (se 10 (by rfl) ⟨567, by rfl⟩ : syracuseStep 387413 = 1135) (by norm_num)
theorem B387485 : Blo 171799 387485 := bbase (se 3 (by rfl) ⟨72653, by rfl⟩ : syracuseStep 387485 = 145307) (by norm_num)
theorem B584117 : Blo 171799 584117 := bbase (se 5 (by rfl) ⟨27380, by rfl⟩ : syracuseStep 584117 = 54761) (by norm_num)
theorem B387557 : Blo 171799 387557 := bbase (se 4 (by rfl) ⟨36333, by rfl⟩ : syracuseStep 387557 = 72667) (by norm_num)
theorem B387629 : Blo 171799 387629 := bbase (se 3 (by rfl) ⟨72680, by rfl⟩ : syracuseStep 387629 = 145361) (by norm_num)
theorem B879173 : Blo 171799 879173 := bbase (se 4 (by rfl) ⟨82422, by rfl⟩ : syracuseStep 879173 = 164845) (by norm_num)
theorem B387701 : Blo 171799 387701 := bbase (se 5 (by rfl) ⟨18173, by rfl⟩ : syracuseStep 387701 = 36347) (by norm_num)
theorem B387773 : Blo 171799 387773 := bbase (se 3 (by rfl) ⟨72707, by rfl⟩ : syracuseStep 387773 = 145415) (by norm_num)
theorem B2943701 : Blo 171799 2943701 := bbase (se 7 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 2943701 = 68993) (by norm_num)
theorem B387845 : Blo 171799 387845 := bbase (se 4 (by rfl) ⟨36360, by rfl⟩ : syracuseStep 387845 = 72721) (by norm_num)
theorem B387917 : Blo 171799 387917 := bbase (se 3 (by rfl) ⟨72734, by rfl⟩ : syracuseStep 387917 = 145469) (by norm_num)
theorem B584549 : Blo 171799 584549 := bbase (se 4 (by rfl) ⟨54801, by rfl⟩ : syracuseStep 584549 = 109603) (by norm_num)
theorem B387989 : Blo 171799 387989 := bbase (se 6 (by rfl) ⟨9093, by rfl⟩ : syracuseStep 387989 = 18187) (by norm_num)
theorem B388061 : Blo 171799 388061 := bbase (se 3 (by rfl) ⟨72761, by rfl⟩ : syracuseStep 388061 = 145523) (by norm_num)
theorem B388133 : Blo 171799 388133 := bbase (se 4 (by rfl) ⟨36387, by rfl⟩ : syracuseStep 388133 = 72775) (by norm_num)
theorem B388205 : Blo 171799 388205 := bbase (se 3 (by rfl) ⟨72788, by rfl⟩ : syracuseStep 388205 = 145577) (by norm_num)
theorem B421013 : Blo 171799 421013 := bbase (se 6 (by rfl) ⟨9867, by rfl⟩ : syracuseStep 421013 = 19735) (by norm_num)
theorem B289973 : Blo 171799 289973 := bbase (se 5 (by rfl) ⟨13592, by rfl⟩ : syracuseStep 289973 = 27185) (by norm_num)
theorem B388277 : Blo 171799 388277 := bbase (se 5 (by rfl) ⟨18200, by rfl⟩ : syracuseStep 388277 = 36401) (by norm_num)
theorem B388349 : Blo 171799 388349 := bbase (se 3 (by rfl) ⟨72815, by rfl⟩ : syracuseStep 388349 = 145631) (by norm_num)
theorem B584981 : Blo 171799 584981 := bbase (se 6 (by rfl) ⟨13710, by rfl⟩ : syracuseStep 584981 = 27421) (by norm_num)
theorem B290101 : Blo 171799 290101 := bbase (se 5 (by rfl) ⟨13598, by rfl⟩ : syracuseStep 290101 = 27197) (by norm_num)
theorem B388421 : Blo 171799 388421 := bbase (se 4 (by rfl) ⟨36414, by rfl⟩ : syracuseStep 388421 = 72829) (by norm_num)
theorem B290189 : Blo 171799 290189 := bbase (se 3 (by rfl) ⟨54410, by rfl⟩ : syracuseStep 290189 = 108821) (by norm_num)
theorem B388493 : Blo 171799 388493 := bbase (se 3 (by rfl) ⟨72842, by rfl⟩ : syracuseStep 388493 = 145685) (by norm_num)
theorem B388565 : Blo 171799 388565 := bbase (se 7 (by rfl) ⟨4553, by rfl⟩ : syracuseStep 388565 = 9107) (by norm_num)
theorem B290317 : Blo 171799 290317 := bbase (se 3 (by rfl) ⟨54434, by rfl⟩ : syracuseStep 290317 = 108869) (by norm_num)
theorem B388637 : Blo 171799 388637 := bbase (se 3 (by rfl) ⟨72869, by rfl⟩ : syracuseStep 388637 = 145739) (by norm_num)
theorem B224857 : Blo 171799 224857 := bbase (se 2 (by rfl) ⟨84321, by rfl⟩ : syracuseStep 224857 = 168643) (by norm_num)
theorem B290405 : Blo 171799 290405 := bbase (se 4 (by rfl) ⟨27225, by rfl⟩ : syracuseStep 290405 = 54451) (by norm_num)
theorem B388709 : Blo 171799 388709 := bbase (se 4 (by rfl) ⟨36441, by rfl⟩ : syracuseStep 388709 = 72883) (by norm_num)
theorem B388781 : Blo 171799 388781 := bbase (se 3 (by rfl) ⟨72896, by rfl⟩ : syracuseStep 388781 = 145793) (by norm_num)
theorem B257717 : Blo 171799 257717 := bbase (se 5 (by rfl) ⟨12080, by rfl⟩ : syracuseStep 257717 = 24161) (by norm_num)
theorem B585413 : Blo 171799 585413 := bbase (se 4 (by rfl) ⟨54882, by rfl⟩ : syracuseStep 585413 = 109765) (by norm_num)
theorem B257741 : Blo 171799 257741 := bbase (se 3 (by rfl) ⟨48326, by rfl⟩ : syracuseStep 257741 = 96653) (by norm_num)
theorem B257765 : Blo 171799 257765 := bbase (se 4 (by rfl) ⟨24165, by rfl⟩ : syracuseStep 257765 = 48331) (by norm_num)
theorem B290533 : Blo 171799 290533 := bbase (se 4 (by rfl) ⟨27237, by rfl⟩ : syracuseStep 290533 = 54475) (by norm_num)
theorem B454373 : Blo 171799 454373 := bbase (se 4 (by rfl) ⟨42597, by rfl⟩ : syracuseStep 454373 = 85195) (by norm_num)
theorem B388853 : Blo 171799 388853 := bbase (se 5 (by rfl) ⟨18227, by rfl⟩ : syracuseStep 388853 = 36455) (by norm_num)
theorem B257789 : Blo 171799 257789 := bbase (se 3 (by rfl) ⟨48335, by rfl⟩ : syracuseStep 257789 = 96671) (by norm_num)
theorem B913157 : Blo 171799 913157 := bbase (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) (by norm_num)
theorem B257813 : Blo 171799 257813 := bbase (se 6 (by rfl) ⟨6042, by rfl⟩ : syracuseStep 257813 = 12085) (by norm_num)
theorem B257837 : Blo 171799 257837 := bbase (se 3 (by rfl) ⟨48344, by rfl⟩ : syracuseStep 257837 = 96689) (by norm_num)
theorem B290621 : Blo 171799 290621 := bbase (se 3 (by rfl) ⟨54491, by rfl⟩ : syracuseStep 290621 = 108983) (by norm_num)
theorem B388925 : Blo 171799 388925 := bbase (se 3 (by rfl) ⟨72923, by rfl⟩ : syracuseStep 388925 = 145847) (by norm_num)
theorem B257861 : Blo 171799 257861 := bbase (se 4 (by rfl) ⟨24174, by rfl⟩ : syracuseStep 257861 = 48349) (by norm_num)
theorem B880469 : Blo 171799 880469 := bbase (se 9 (by rfl) ⟨2579, by rfl⟩ : syracuseStep 880469 = 5159) (by norm_num)
theorem B257885 : Blo 171799 257885 := bbase (se 3 (by rfl) ⟨48353, by rfl⟩ : syracuseStep 257885 = 96707) (by norm_num)
theorem B257909 : Blo 171799 257909 := bbase (se 5 (by rfl) ⟨12089, by rfl⟩ : syracuseStep 257909 = 24179) (by norm_num)
theorem B388997 : Blo 171799 388997 := bbase (se 4 (by rfl) ⟨36468, by rfl⟩ : syracuseStep 388997 = 72937) (by norm_num)
theorem B257933 : Blo 171799 257933 := bbase (se 3 (by rfl) ⟨48362, by rfl⟩ : syracuseStep 257933 = 96725) (by norm_num)
theorem B257957 : Blo 171799 257957 := bbase (se 4 (by rfl) ⟨24183, by rfl⟩ : syracuseStep 257957 = 48367) (by norm_num)
theorem B257981 : Blo 171799 257981 := bbase (se 3 (by rfl) ⟨48371, by rfl⟩ : syracuseStep 257981 = 96743) (by norm_num)
theorem B290749 : Blo 171799 290749 := bbase (se 3 (by rfl) ⟨54515, by rfl⟩ : syracuseStep 290749 = 109031) (by norm_num)
theorem B389069 : Blo 171799 389069 := bbase (se 3 (by rfl) ⟨72950, by rfl⟩ : syracuseStep 389069 = 145901) (by norm_num)
theorem B258005 : Blo 171799 258005 := bbase (se 7 (by rfl) ⟨3023, by rfl⟩ : syracuseStep 258005 = 6047) (by norm_num)
theorem B258029 : Blo 171799 258029 := bbase (se 3 (by rfl) ⟨48380, by rfl⟩ : syracuseStep 258029 = 96761) (by norm_num)
theorem B258053 : Blo 171799 258053 := bbase (se 4 (by rfl) ⟨24192, by rfl⟩ : syracuseStep 258053 = 48385) (by norm_num)
theorem B290837 : Blo 171799 290837 := bbase (se 6 (by rfl) ⟨6816, by rfl⟩ : syracuseStep 290837 = 13633) (by norm_num)
theorem B389141 : Blo 171799 389141 := bbase (se 6 (by rfl) ⟨9120, by rfl⟩ : syracuseStep 389141 = 18241) (by norm_num)
theorem B258077 : Blo 171799 258077 := bbase (se 3 (by rfl) ⟨48389, by rfl⟩ : syracuseStep 258077 = 96779) (by norm_num)
theorem B258101 : Blo 171799 258101 := bbase (se 5 (by rfl) ⟨12098, by rfl⟩ : syracuseStep 258101 = 24197) (by norm_num)
theorem B258125 : Blo 171799 258125 := bbase (se 3 (by rfl) ⟨48398, by rfl⟩ : syracuseStep 258125 = 96797) (by norm_num)
theorem B2093141 : Blo 171799 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B389213 : Blo 171799 389213 := bbase (se 3 (by rfl) ⟨72977, by rfl⟩ : syracuseStep 389213 = 145955) (by norm_num)
theorem B258149 : Blo 171799 258149 := bbase (se 4 (by rfl) ⟨24201, by rfl⟩ : syracuseStep 258149 = 48403) (by norm_num)
theorem B553061 : Blo 171799 553061 := bbase (se 4 (by rfl) ⟨51849, by rfl⟩ : syracuseStep 553061 = 103699) (by norm_num)
theorem B585845 : Blo 171799 585845 := bbase (se 5 (by rfl) ⟨27461, by rfl⟩ : syracuseStep 585845 = 54923) (by norm_num)
theorem B258173 : Blo 171799 258173 := bbase (se 3 (by rfl) ⟨48407, by rfl⟩ : syracuseStep 258173 = 96815) (by norm_num)
theorem B258197 : Blo 171799 258197 := bbase (se 6 (by rfl) ⟨6051, by rfl⟩ : syracuseStep 258197 = 12103) (by norm_num)
theorem B290965 : Blo 171799 290965 := bbase (se 6 (by rfl) ⟨6819, by rfl⟩ : syracuseStep 290965 = 13639) (by norm_num)
theorem B389285 : Blo 171799 389285 := bbase (se 4 (by rfl) ⟨36495, by rfl⟩ : syracuseStep 389285 = 72991) (by norm_num)
theorem B258221 : Blo 171799 258221 := bbase (se 3 (by rfl) ⟨48416, by rfl⟩ : syracuseStep 258221 = 96833) (by norm_num)
theorem B749749 : Blo 171799 749749 := bbase (se 5 (by rfl) ⟨35144, by rfl⟩ : syracuseStep 749749 = 70289) (by norm_num)
theorem B225461 : Blo 171799 225461 := bbase (se 5 (by rfl) ⟨10568, by rfl⟩ : syracuseStep 225461 = 21137) (by norm_num)
theorem B258245 : Blo 171799 258245 := bbase (se 4 (by rfl) ⟨24210, by rfl⟩ : syracuseStep 258245 = 48421) (by norm_num)
theorem B258269 : Blo 171799 258269 := bbase (se 3 (by rfl) ⟨48425, by rfl⟩ : syracuseStep 258269 = 96851) (by norm_num)
theorem B291053 : Blo 171799 291053 := bbase (se 3 (by rfl) ⟨54572, by rfl⟩ : syracuseStep 291053 = 109145) (by norm_num)
theorem B389357 : Blo 171799 389357 := bbase (se 3 (by rfl) ⟨73004, by rfl⟩ : syracuseStep 389357 = 146009) (by norm_num)
theorem B258293 : Blo 171799 258293 := bbase (se 5 (by rfl) ⟨12107, by rfl⟩ : syracuseStep 258293 = 24215) (by norm_num)
theorem B258317 : Blo 171799 258317 := bbase (se 3 (by rfl) ⟨48434, by rfl⟩ : syracuseStep 258317 = 96869) (by norm_num)
theorem B258341 : Blo 171799 258341 := bbase (se 4 (by rfl) ⟨24219, by rfl⟩ : syracuseStep 258341 = 48439) (by norm_num)
theorem B389429 : Blo 171799 389429 := bbase (se 5 (by rfl) ⟨18254, by rfl⟩ : syracuseStep 389429 = 36509) (by norm_num)
theorem B258365 : Blo 171799 258365 := bbase (se 3 (by rfl) ⟨48443, by rfl⟩ : syracuseStep 258365 = 96887) (by norm_num)
theorem B258389 : Blo 171799 258389 := bbase (se 10 (by rfl) ⟨378, by rfl⟩ : syracuseStep 258389 = 757) (by norm_num)
theorem B258413 : Blo 171799 258413 := bbase (se 3 (by rfl) ⟨48452, by rfl⟩ : syracuseStep 258413 = 96905) (by norm_num)
theorem B291181 : Blo 171799 291181 := bbase (se 3 (by rfl) ⟨54596, by rfl⟩ : syracuseStep 291181 = 109193) (by norm_num)
theorem B389501 : Blo 171799 389501 := bbase (se 3 (by rfl) ⟨73031, by rfl⟩ : syracuseStep 389501 = 146063) (by norm_num)
theorem B258437 : Blo 171799 258437 := bbase (se 4 (by rfl) ⟨24228, by rfl⟩ : syracuseStep 258437 = 48457) (by norm_num)
theorem B258461 : Blo 171799 258461 := bbase (se 3 (by rfl) ⟨48461, by rfl⟩ : syracuseStep 258461 = 96923) (by norm_num)
theorem B258485 : Blo 171799 258485 := bbase (se 5 (by rfl) ⟨12116, by rfl⟩ : syracuseStep 258485 = 24233) (by norm_num)
theorem B750005 : Blo 171799 750005 := bbase (se 5 (by rfl) ⟨35156, by rfl⟩ : syracuseStep 750005 = 70313) (by norm_num)
theorem B291269 : Blo 171799 291269 := bbase (se 4 (by rfl) ⟨27306, by rfl⟩ : syracuseStep 291269 = 54613) (by norm_num)
theorem B389573 : Blo 171799 389573 := bbase (se 4 (by rfl) ⟨36522, by rfl⟩ : syracuseStep 389573 = 73045) (by norm_num)
theorem B258509 : Blo 171799 258509 := bbase (se 3 (by rfl) ⟨48470, by rfl⟩ : syracuseStep 258509 = 96941) (by norm_num)
theorem B258533 : Blo 171799 258533 := bbase (se 4 (by rfl) ⟨24237, by rfl⟩ : syracuseStep 258533 = 48475) (by norm_num)
theorem B258557 : Blo 171799 258557 := bbase (se 3 (by rfl) ⟨48479, by rfl⟩ : syracuseStep 258557 = 96959) (by norm_num)
theorem B389645 : Blo 171799 389645 := bbase (se 3 (by rfl) ⟨73058, by rfl⟩ : syracuseStep 389645 = 146117) (by norm_num)
theorem B258581 : Blo 171799 258581 := bbase (se 6 (by rfl) ⟨6060, by rfl⟩ : syracuseStep 258581 = 12121) (by norm_num)
theorem B586277 : Blo 171799 586277 := bbase (se 4 (by rfl) ⟨54963, by rfl⟩ : syracuseStep 586277 = 109927) (by norm_num)
theorem B258605 : Blo 171799 258605 := bbase (se 3 (by rfl) ⟨48488, by rfl⟩ : syracuseStep 258605 = 96977) (by norm_num)
theorem B258629 : Blo 171799 258629 := bbase (se 4 (by rfl) ⟨24246, by rfl⟩ : syracuseStep 258629 = 48493) (by norm_num)
theorem B291397 : Blo 171799 291397 := bbase (se 4 (by rfl) ⟨27318, by rfl⟩ : syracuseStep 291397 = 54637) (by norm_num)
theorem B389717 : Blo 171799 389717 := bbase (se 8 (by rfl) ⟨2283, by rfl⟩ : syracuseStep 389717 = 4567) (by norm_num)
theorem B258653 : Blo 171799 258653 := bbase (se 3 (by rfl) ⟨48497, by rfl⟩ : syracuseStep 258653 = 96995) (by norm_num)
theorem B258677 : Blo 171799 258677 := bbase (se 5 (by rfl) ⟨12125, by rfl⟩ : syracuseStep 258677 = 24251) (by norm_num)
theorem B258701 : Blo 171799 258701 := bbase (se 3 (by rfl) ⟨48506, by rfl⟩ : syracuseStep 258701 = 97013) (by norm_num)
theorem B291485 : Blo 171799 291485 := bbase (se 3 (by rfl) ⟨54653, by rfl⟩ : syracuseStep 291485 = 109307) (by norm_num)
theorem B389789 : Blo 171799 389789 := bbase (se 3 (by rfl) ⟨73085, by rfl⟩ : syracuseStep 389789 = 146171) (by norm_num)
theorem B258725 : Blo 171799 258725 := bbase (se 4 (by rfl) ⟨24255, by rfl⟩ : syracuseStep 258725 = 48511) (by norm_num)
theorem B258749 : Blo 171799 258749 := bbase (se 3 (by rfl) ⟨48515, by rfl⟩ : syracuseStep 258749 = 97031) (by norm_num)
theorem B258773 : Blo 171799 258773 := bbase (se 7 (by rfl) ⟨3032, by rfl⟩ : syracuseStep 258773 = 6065) (by norm_num)
theorem B389861 : Blo 171799 389861 := bbase (se 4 (by rfl) ⟨36549, by rfl⟩ : syracuseStep 389861 = 73099) (by norm_num)
theorem B258797 : Blo 171799 258797 := bbase (se 3 (by rfl) ⟨48524, by rfl⟩ : syracuseStep 258797 = 97049) (by norm_num)
theorem B258821 : Blo 171799 258821 := bbase (se 4 (by rfl) ⟨24264, by rfl⟩ : syracuseStep 258821 = 48529) (by norm_num)
theorem B193297 : Blo 171799 193297 := bbase (se 2 (by rfl) ⟨72486, by rfl⟩ : syracuseStep 193297 = 144973) (by norm_num)
theorem B258845 : Blo 171799 258845 := bbase (se 3 (by rfl) ⟨48533, by rfl⟩ : syracuseStep 258845 = 97067) (by norm_num)
theorem B291613 : Blo 171799 291613 := bbase (se 3 (by rfl) ⟨54677, by rfl⟩ : syracuseStep 291613 = 109355) (by norm_num)
theorem B389933 : Blo 171799 389933 := bbase (se 3 (by rfl) ⟨73112, by rfl⟩ : syracuseStep 389933 = 146225) (by norm_num)
theorem B193333 : Blo 171799 193333 := bbase (se 5 (by rfl) ⟨9062, by rfl⟩ : syracuseStep 193333 = 18125) (by norm_num)
theorem B258869 : Blo 171799 258869 := bbase (se 5 (by rfl) ⟨12134, by rfl⟩ : syracuseStep 258869 = 24269) (by norm_num)
theorem B750389 : Blo 171799 750389 := bbase (se 5 (by rfl) ⟨35174, by rfl⟩ : syracuseStep 750389 = 70349) (by norm_num)
theorem B258893 : Blo 171799 258893 := bbase (se 3 (by rfl) ⟨48542, by rfl⟩ : syracuseStep 258893 = 97085) (by norm_num)
theorem B193369 : Blo 171799 193369 := bbase (se 2 (by rfl) ⟨72513, by rfl⟩ : syracuseStep 193369 = 145027) (by norm_num)
theorem B258917 : Blo 171799 258917 := bbase (se 4 (by rfl) ⟨24273, by rfl⟩ : syracuseStep 258917 = 48547) (by norm_num)
theorem B291701 : Blo 171799 291701 := bbase (se 5 (by rfl) ⟨13673, by rfl⟩ : syracuseStep 291701 = 27347) (by norm_num)
theorem B390005 : Blo 171799 390005 := bbase (se 5 (by rfl) ⟨18281, by rfl⟩ : syracuseStep 390005 = 36563) (by norm_num)
theorem B193405 : Blo 171799 193405 := bbase (se 3 (by rfl) ⟨36263, by rfl⟩ : syracuseStep 193405 = 72527) (by norm_num)
theorem B258941 : Blo 171799 258941 := bbase (se 3 (by rfl) ⟨48551, by rfl⟩ : syracuseStep 258941 = 97103) (by norm_num)
theorem B258965 : Blo 171799 258965 := bbase (se 6 (by rfl) ⟨6069, by rfl⟩ : syracuseStep 258965 = 12139) (by norm_num)
theorem B193441 : Blo 171799 193441 := bbase (se 2 (by rfl) ⟨72540, by rfl⟩ : syracuseStep 193441 = 145081) (by norm_num)
theorem B258989 : Blo 171799 258989 := bbase (se 3 (by rfl) ⟨48560, by rfl⟩ : syracuseStep 258989 = 97121) (by norm_num)
theorem B390077 : Blo 171799 390077 := bbase (se 3 (by rfl) ⟨73139, by rfl⟩ : syracuseStep 390077 = 146279) (by norm_num)
theorem B193477 : Blo 171799 193477 := bbase (se 4 (by rfl) ⟨18138, by rfl⟩ : syracuseStep 193477 = 36277) (by norm_num)
theorem B259013 : Blo 171799 259013 := bbase (se 4 (by rfl) ⟨24282, by rfl⟩ : syracuseStep 259013 = 48565) (by norm_num)
theorem B586709 : Blo 171799 586709 := bbase (se 7 (by rfl) ⟨6875, by rfl⟩ : syracuseStep 586709 = 13751) (by norm_num)
theorem B259037 : Blo 171799 259037 := bbase (se 3 (by rfl) ⟨48569, by rfl⟩ : syracuseStep 259037 = 97139) (by norm_num)
theorem B193513 : Blo 171799 193513 := bbase (se 2 (by rfl) ⟨72567, by rfl⟩ : syracuseStep 193513 = 145135) (by norm_num)
theorem B259061 : Blo 171799 259061 := bbase (se 5 (by rfl) ⟨12143, by rfl⟩ : syracuseStep 259061 = 24287) (by norm_num)
theorem B291829 : Blo 171799 291829 := bbase (se 5 (by rfl) ⟨13679, by rfl⟩ : syracuseStep 291829 = 27359) (by norm_num)
theorem B390149 : Blo 171799 390149 := bbase (se 4 (by rfl) ⟨36576, by rfl⟩ : syracuseStep 390149 = 73153) (by norm_num)
theorem B193549 : Blo 171799 193549 := bbase (se 3 (by rfl) ⟨36290, by rfl⟩ : syracuseStep 193549 = 72581) (by norm_num)
theorem B259085 : Blo 171799 259085 := bbase (se 3 (by rfl) ⟨48578, by rfl⟩ : syracuseStep 259085 = 97157) (by norm_num)
theorem B259109 : Blo 171799 259109 := bbase (se 4 (by rfl) ⟨24291, by rfl⟩ : syracuseStep 259109 = 48583) (by norm_num)
theorem B193585 : Blo 171799 193585 := bbase (se 2 (by rfl) ⟨72594, by rfl⟩ : syracuseStep 193585 = 145189) (by norm_num)
theorem B259133 : Blo 171799 259133 := bbase (se 3 (by rfl) ⟨48587, by rfl⟩ : syracuseStep 259133 = 97175) (by norm_num)
theorem B226373 : Blo 171799 226373 := bbase (se 4 (by rfl) ⟨21222, by rfl⟩ : syracuseStep 226373 = 42445) (by norm_num)
theorem B291917 : Blo 171799 291917 := bbase (se 3 (by rfl) ⟨54734, by rfl⟩ : syracuseStep 291917 = 109469) (by norm_num)
theorem B390221 : Blo 171799 390221 := bbase (se 3 (by rfl) ⟨73166, by rfl⟩ : syracuseStep 390221 = 146333) (by norm_num)
theorem B193621 : Blo 171799 193621 := bbase (se 8 (by rfl) ⟨1134, by rfl⟩ : syracuseStep 193621 = 2269) (by norm_num)
theorem B259157 : Blo 171799 259157 := bbase (se 8 (by rfl) ⟨1518, by rfl⟩ : syracuseStep 259157 = 3037) (by norm_num)
theorem B881765 : Blo 171799 881765 := bbase (se 4 (by rfl) ⟨82665, by rfl⟩ : syracuseStep 881765 = 165331) (by norm_num)
theorem B259181 : Blo 171799 259181 := bbase (se 3 (by rfl) ⟨48596, by rfl⟩ : syracuseStep 259181 = 97193) (by norm_num)
theorem B193657 : Blo 171799 193657 := bbase (se 2 (by rfl) ⟨72621, by rfl⟩ : syracuseStep 193657 = 145243) (by norm_num)
theorem B259205 : Blo 171799 259205 := bbase (se 4 (by rfl) ⟨24300, by rfl⟩ : syracuseStep 259205 = 48601) (by norm_num)
theorem B390293 : Blo 171799 390293 := bbase (se 6 (by rfl) ⟨9147, by rfl⟩ : syracuseStep 390293 = 18295) (by norm_num)
theorem B193693 : Blo 171799 193693 := bbase (se 3 (by rfl) ⟨36317, by rfl⟩ : syracuseStep 193693 = 72635) (by norm_num)
theorem B259229 : Blo 171799 259229 := bbase (se 3 (by rfl) ⟨48605, by rfl⟩ : syracuseStep 259229 = 97211) (by norm_num)
theorem B259253 : Blo 171799 259253 := bbase (se 5 (by rfl) ⟨12152, by rfl⟩ : syracuseStep 259253 = 24305) (by norm_num)
theorem B193729 : Blo 171799 193729 := bbase (se 2 (by rfl) ⟨72648, by rfl⟩ : syracuseStep 193729 = 145297) (by norm_num)
theorem B259277 : Blo 171799 259277 := bbase (se 3 (by rfl) ⟨48614, by rfl⟩ : syracuseStep 259277 = 97229) (by norm_num)
theorem B292045 : Blo 171799 292045 := bbase (se 3 (by rfl) ⟨54758, by rfl⟩ : syracuseStep 292045 = 109517) (by norm_num)
theorem B390365 : Blo 171799 390365 := bbase (se 3 (by rfl) ⟨73193, by rfl⟩ : syracuseStep 390365 = 146387) (by norm_num)
theorem B193765 : Blo 171799 193765 := bbase (se 4 (by rfl) ⟨18165, by rfl⟩ : syracuseStep 193765 = 36331) (by norm_num)
theorem B259301 : Blo 171799 259301 := bbase (se 4 (by rfl) ⟨24309, by rfl⟩ : syracuseStep 259301 = 48619) (by norm_num)
theorem B259325 : Blo 171799 259325 := bbase (se 3 (by rfl) ⟨48623, by rfl⟩ : syracuseStep 259325 = 97247) (by norm_num)
theorem B193801 : Blo 171799 193801 := bbase (se 2 (by rfl) ⟨72675, by rfl⟩ : syracuseStep 193801 = 145351) (by norm_num)
theorem B259349 : Blo 171799 259349 := bbase (se 6 (by rfl) ⟨6078, by rfl⟩ : syracuseStep 259349 = 12157) (by norm_num)
theorem B947477 : Blo 171799 947477 := bbase (se 6 (by rfl) ⟨22206, by rfl⟩ : syracuseStep 947477 = 44413) (by norm_num)
theorem B292133 : Blo 171799 292133 := bbase (se 4 (by rfl) ⟨27387, by rfl⟩ : syracuseStep 292133 = 54775) (by norm_num)
theorem B390437 : Blo 171799 390437 := bbase (se 4 (by rfl) ⟨36603, by rfl⟩ : syracuseStep 390437 = 73207) (by norm_num)
theorem B193837 : Blo 171799 193837 := bbase (se 3 (by rfl) ⟨36344, by rfl⟩ : syracuseStep 193837 = 72689) (by norm_num)
theorem B259373 : Blo 171799 259373 := bbase (se 3 (by rfl) ⟨48632, by rfl⟩ : syracuseStep 259373 = 97265) (by norm_num)
theorem B259397 : Blo 171799 259397 := bbase (se 4 (by rfl) ⟨24318, by rfl⟩ : syracuseStep 259397 = 48637) (by norm_num)
theorem B193873 : Blo 171799 193873 := bbase (se 2 (by rfl) ⟨72702, by rfl⟩ : syracuseStep 193873 = 145405) (by norm_num)
theorem B259421 : Blo 171799 259421 := bbase (se 3 (by rfl) ⟨48641, by rfl⟩ : syracuseStep 259421 = 97283) (by norm_num)
theorem B390509 : Blo 171799 390509 := bbase (se 3 (by rfl) ⟨73220, by rfl⟩ : syracuseStep 390509 = 146441) (by norm_num)
theorem B193909 : Blo 171799 193909 := bbase (se 5 (by rfl) ⟨9089, by rfl⟩ : syracuseStep 193909 = 18179) (by norm_num)
theorem B259445 : Blo 171799 259445 := bbase (se 5 (by rfl) ⟨12161, by rfl⟩ : syracuseStep 259445 = 24323) (by norm_num)
theorem B587141 : Blo 171799 587141 := bbase (se 4 (by rfl) ⟨55044, by rfl⟩ : syracuseStep 587141 = 110089) (by norm_num)
theorem B259469 : Blo 171799 259469 := bbase (se 3 (by rfl) ⟨48650, by rfl⟩ : syracuseStep 259469 = 97301) (by norm_num)
theorem B193945 : Blo 171799 193945 := bbase (se 2 (by rfl) ⟨72729, by rfl⟩ : syracuseStep 193945 = 145459) (by norm_num)
theorem B259493 : Blo 171799 259493 := bbase (se 4 (by rfl) ⟨24327, by rfl⟩ : syracuseStep 259493 = 48655) (by norm_num)
theorem B292261 : Blo 171799 292261 := bbase (se 4 (by rfl) ⟨27399, by rfl⟩ : syracuseStep 292261 = 54799) (by norm_num)
theorem B390581 : Blo 171799 390581 := bbase (se 5 (by rfl) ⟨18308, by rfl⟩ : syracuseStep 390581 = 36617) (by norm_num)
theorem B193981 : Blo 171799 193981 := bbase (se 3 (by rfl) ⟨36371, by rfl⟩ : syracuseStep 193981 = 72743) (by norm_num)
theorem B259517 : Blo 171799 259517 := bbase (se 3 (by rfl) ⟨48659, by rfl⟩ : syracuseStep 259517 = 97319) (by norm_num)
theorem B259541 : Blo 171799 259541 := bbase (se 7 (by rfl) ⟨3041, by rfl⟩ : syracuseStep 259541 = 6083) (by norm_num)
theorem B194017 : Blo 171799 194017 := bbase (se 2 (by rfl) ⟨72756, by rfl⟩ : syracuseStep 194017 = 145513) (by norm_num)
theorem B259565 : Blo 171799 259565 := bbase (se 3 (by rfl) ⟨48668, by rfl⟩ : syracuseStep 259565 = 97337) (by norm_num)
theorem B292349 : Blo 171799 292349 := bbase (se 3 (by rfl) ⟨54815, by rfl⟩ : syracuseStep 292349 = 109631) (by norm_num)
theorem B390653 : Blo 171799 390653 := bbase (se 3 (by rfl) ⟨73247, by rfl⟩ : syracuseStep 390653 = 146495) (by norm_num)
theorem B652805 : Blo 171799 652805 := bbase (se 4 (by rfl) ⟨61200, by rfl⟩ : syracuseStep 652805 = 122401) (by norm_num)
theorem B194053 : Blo 171799 194053 := bbase (se 4 (by rfl) ⟨18192, by rfl⟩ : syracuseStep 194053 = 36385) (by norm_num)
theorem B259589 : Blo 171799 259589 := bbase (se 4 (by rfl) ⟨24336, by rfl⟩ : syracuseStep 259589 = 48673) (by norm_num)
theorem B259613 : Blo 171799 259613 := bbase (se 3 (by rfl) ⟨48677, by rfl⟩ : syracuseStep 259613 = 97355) (by norm_num)
theorem B194089 : Blo 171799 194089 := bbase (se 2 (by rfl) ⟨72783, by rfl⟩ : syracuseStep 194089 = 145567) (by norm_num)
theorem B259637 : Blo 171799 259637 := bbase (se 5 (by rfl) ⟨12170, by rfl⟩ : syracuseStep 259637 = 24341) (by norm_num)
theorem B456245 : Blo 171799 456245 := bbase (se 5 (by rfl) ⟨21386, by rfl⟩ : syracuseStep 456245 = 42773) (by norm_num)
theorem B390725 : Blo 171799 390725 := bbase (se 4 (by rfl) ⟨36630, by rfl⟩ : syracuseStep 390725 = 73261) (by norm_num)
theorem B194125 : Blo 171799 194125 := bbase (se 3 (by rfl) ⟨36398, by rfl⟩ : syracuseStep 194125 = 72797) (by norm_num)
theorem B259661 : Blo 171799 259661 := bbase (se 3 (by rfl) ⟨48686, by rfl⟩ : syracuseStep 259661 = 97373) (by norm_num)
theorem B259685 : Blo 171799 259685 := bbase (se 4 (by rfl) ⟨24345, by rfl⟩ : syracuseStep 259685 = 48691) (by norm_num)
theorem B194161 : Blo 171799 194161 := bbase (se 2 (by rfl) ⟨72810, by rfl⟩ : syracuseStep 194161 = 145621) (by norm_num)
theorem B259709 : Blo 171799 259709 := bbase (se 3 (by rfl) ⟨48695, by rfl⟩ : syracuseStep 259709 = 97391) (by norm_num)
theorem B292477 : Blo 171799 292477 := bbase (se 3 (by rfl) ⟨54839, by rfl⟩ : syracuseStep 292477 = 109679) (by norm_num)
theorem B390797 : Blo 171799 390797 := bbase (se 3 (by rfl) ⟨73274, by rfl⟩ : syracuseStep 390797 = 146549) (by norm_num)
theorem B194197 : Blo 171799 194197 := bbase (se 6 (by rfl) ⟨4551, by rfl⟩ : syracuseStep 194197 = 9103) (by norm_num)
theorem B259733 : Blo 171799 259733 := bbase (se 6 (by rfl) ⟨6087, by rfl⟩ : syracuseStep 259733 = 12175) (by norm_num)
theorem B259757 : Blo 171799 259757 := bbase (se 3 (by rfl) ⟨48704, by rfl⟩ : syracuseStep 259757 = 97409) (by norm_num)
theorem B194233 : Blo 171799 194233 := bbase (se 2 (by rfl) ⟨72837, by rfl⟩ : syracuseStep 194233 = 145675) (by norm_num)
theorem B259781 : Blo 171799 259781 := bbase (se 4 (by rfl) ⟨24354, by rfl⟩ : syracuseStep 259781 = 48709) (by norm_num)
theorem B292565 : Blo 171799 292565 := bbase (se 7 (by rfl) ⟨3428, by rfl⟩ : syracuseStep 292565 = 6857) (by norm_num)
theorem B390869 : Blo 171799 390869 := bbase (se 7 (by rfl) ⟨4580, by rfl⟩ : syracuseStep 390869 = 9161) (by norm_num)
theorem B194269 : Blo 171799 194269 := bbase (se 3 (by rfl) ⟨36425, by rfl⟩ : syracuseStep 194269 = 72851) (by norm_num)
theorem B259805 : Blo 171799 259805 := bbase (se 3 (by rfl) ⟨48713, by rfl⟩ : syracuseStep 259805 = 97427) (by norm_num)
theorem B259829 : Blo 171799 259829 := bbase (se 5 (by rfl) ⟨12179, by rfl⟩ : syracuseStep 259829 = 24359) (by norm_num)
theorem B194305 : Blo 171799 194305 := bbase (se 2 (by rfl) ⟨72864, by rfl⟩ : syracuseStep 194305 = 145729) (by norm_num)
theorem B259853 : Blo 171799 259853 := bbase (se 3 (by rfl) ⟨48722, by rfl⟩ : syracuseStep 259853 = 97445) (by norm_num)
theorem B390941 : Blo 171799 390941 := bbase (se 3 (by rfl) ⟨73301, by rfl⟩ : syracuseStep 390941 = 146603) (by norm_num)
theorem B653093 : Blo 171799 653093 := bbase (se 4 (by rfl) ⟨61227, by rfl⟩ : syracuseStep 653093 = 122455) (by norm_num)
theorem B194341 : Blo 171799 194341 := bbase (se 4 (by rfl) ⟨18219, by rfl⟩ : syracuseStep 194341 = 36439) (by norm_num)
theorem B259877 : Blo 171799 259877 := bbase (se 4 (by rfl) ⟨24363, by rfl⟩ : syracuseStep 259877 = 48727) (by norm_num)
theorem B587573 : Blo 171799 587573 := bbase (se 5 (by rfl) ⟨27542, by rfl⟩ : syracuseStep 587573 = 55085) (by norm_num)
theorem B259901 : Blo 171799 259901 := bbase (se 3 (by rfl) ⟨48731, by rfl⟩ : syracuseStep 259901 = 97463) (by norm_num)
theorem B194377 : Blo 171799 194377 := bbase (se 2 (by rfl) ⟨72891, by rfl⟩ : syracuseStep 194377 = 145783) (by norm_num)
theorem B259925 : Blo 171799 259925 := bbase (se 9 (by rfl) ⟨761, by rfl⟩ : syracuseStep 259925 = 1523) (by norm_num)
theorem B292693 : Blo 171799 292693 := bbase (se 9 (by rfl) ⟨857, by rfl⟩ : syracuseStep 292693 = 1715) (by norm_num)
theorem B391013 : Blo 171799 391013 := bbase (se 4 (by rfl) ⟨36657, by rfl⟩ : syracuseStep 391013 = 73315) (by norm_num)
theorem B194413 : Blo 171799 194413 := bbase (se 3 (by rfl) ⟨36452, by rfl⟩ : syracuseStep 194413 = 72905) (by norm_num)
theorem B259949 : Blo 171799 259949 := bbase (se 3 (by rfl) ⟨48740, by rfl⟩ : syracuseStep 259949 = 97481) (by norm_num)
theorem B259973 : Blo 171799 259973 := bbase (se 4 (by rfl) ⟨24372, by rfl⟩ : syracuseStep 259973 = 48745) (by norm_num)
theorem B194449 : Blo 171799 194449 := bbase (se 2 (by rfl) ⟨72918, by rfl⟩ : syracuseStep 194449 = 145837) (by norm_num)
theorem B489365 : Blo 171799 489365 := bbase (se 6 (by rfl) ⟨11469, by rfl⟩ : syracuseStep 489365 = 22939) (by norm_num)
theorem B1963925 : Blo 171799 1963925 := bbase (se 6 (by rfl) ⟨46029, by rfl⟩ : syracuseStep 1963925 = 92059) (by norm_num)
theorem B259997 : Blo 171799 259997 := bbase (se 3 (by rfl) ⟨48749, by rfl⟩ : syracuseStep 259997 = 97499) (by norm_num)
theorem B292781 : Blo 171799 292781 := bbase (se 3 (by rfl) ⟨54896, by rfl⟩ : syracuseStep 292781 = 109793) (by norm_num)
theorem B391085 : Blo 171799 391085 := bbase (se 3 (by rfl) ⟨73328, by rfl⟩ : syracuseStep 391085 = 146657) (by norm_num)
theorem B194485 : Blo 171799 194485 := bbase (se 5 (by rfl) ⟨9116, by rfl⟩ : syracuseStep 194485 = 18233) (by norm_num)
theorem B260021 : Blo 171799 260021 := bbase (se 5 (by rfl) ⟨12188, by rfl⟩ : syracuseStep 260021 = 24377) (by norm_num)
theorem B260045 : Blo 171799 260045 := bbase (se 3 (by rfl) ⟨48758, by rfl⟩ : syracuseStep 260045 = 97517) (by norm_num)
theorem B194521 : Blo 171799 194521 := bbase (se 2 (by rfl) ⟨72945, by rfl⟩ : syracuseStep 194521 = 145891) (by norm_num)
theorem B260069 : Blo 171799 260069 := bbase (se 4 (by rfl) ⟨24381, by rfl⟩ : syracuseStep 260069 = 48763) (by norm_num)
theorem B391157 : Blo 171799 391157 := bbase (se 5 (by rfl) ⟨18335, by rfl⟩ : syracuseStep 391157 = 36671) (by norm_num)
theorem B194557 : Blo 171799 194557 := bbase (se 3 (by rfl) ⟨36479, by rfl⟩ : syracuseStep 194557 = 72959) (by norm_num)
theorem B260093 : Blo 171799 260093 := bbase (se 3 (by rfl) ⟨48767, by rfl⟩ : syracuseStep 260093 = 97535) (by norm_num)
theorem B260117 : Blo 171799 260117 := bbase (se 6 (by rfl) ⟨6096, by rfl⟩ : syracuseStep 260117 = 12193) (by norm_num)
theorem B194593 : Blo 171799 194593 := bbase (se 2 (by rfl) ⟨72972, by rfl⟩ : syracuseStep 194593 = 145945) (by norm_num)
theorem B260141 : Blo 171799 260141 := bbase (se 3 (by rfl) ⟨48776, by rfl⟩ : syracuseStep 260141 = 97553) (by norm_num)
theorem B292909 : Blo 171799 292909 := bbase (se 3 (by rfl) ⟨54920, by rfl⟩ : syracuseStep 292909 = 109841) (by norm_num)
theorem B391229 : Blo 171799 391229 := bbase (se 3 (by rfl) ⟨73355, by rfl⟩ : syracuseStep 391229 = 146711) (by norm_num)
theorem B194629 : Blo 171799 194629 := bbase (se 4 (by rfl) ⟨18246, by rfl⟩ : syracuseStep 194629 = 36493) (by norm_num)
theorem B260165 : Blo 171799 260165 := bbase (se 4 (by rfl) ⟨24390, by rfl⟩ : syracuseStep 260165 = 48781) (by norm_num)
theorem B260189 : Blo 171799 260189 := bbase (se 3 (by rfl) ⟨48785, by rfl⟩ : syracuseStep 260189 = 97571) (by norm_num)
theorem B194665 : Blo 171799 194665 := bbase (se 2 (by rfl) ⟨72999, by rfl⟩ : syracuseStep 194665 = 145999) (by norm_num)
theorem B260213 : Blo 171799 260213 := bbase (se 5 (by rfl) ⟨12197, by rfl⟩ : syracuseStep 260213 = 24395) (by norm_num)
theorem B292997 : Blo 171799 292997 := bbase (se 4 (by rfl) ⟨27468, by rfl⟩ : syracuseStep 292997 = 54937) (by norm_num)
theorem B391301 : Blo 171799 391301 := bbase (se 4 (by rfl) ⟨36684, by rfl⟩ : syracuseStep 391301 = 73369) (by norm_num)
theorem B194701 : Blo 171799 194701 := bbase (se 3 (by rfl) ⟨36506, by rfl⟩ : syracuseStep 194701 = 73013) (by norm_num)
theorem B260237 : Blo 171799 260237 := bbase (se 3 (by rfl) ⟨48794, by rfl⟩ : syracuseStep 260237 = 97589) (by norm_num)
theorem B260261 : Blo 171799 260261 := bbase (se 4 (by rfl) ⟨24399, by rfl⟩ : syracuseStep 260261 = 48799) (by norm_num)
theorem B194737 : Blo 171799 194737 := bbase (se 2 (by rfl) ⟨73026, by rfl⟩ : syracuseStep 194737 = 146053) (by norm_num)
theorem B260285 : Blo 171799 260285 := bbase (se 3 (by rfl) ⟨48803, by rfl⟩ : syracuseStep 260285 = 97607) (by norm_num)
theorem B391373 : Blo 171799 391373 := bbase (se 3 (by rfl) ⟨73382, by rfl⟩ : syracuseStep 391373 = 146765) (by norm_num)
theorem B194773 : Blo 171799 194773 := bbase (se 7 (by rfl) ⟨2282, by rfl⟩ : syracuseStep 194773 = 4565) (by norm_num)
theorem B260309 : Blo 171799 260309 := bbase (se 7 (by rfl) ⟨3050, by rfl⟩ : syracuseStep 260309 = 6101) (by norm_num)
theorem B588005 : Blo 171799 588005 := bbase (se 4 (by rfl) ⟨55125, by rfl⟩ : syracuseStep 588005 = 110251) (by norm_num)
theorem B260333 : Blo 171799 260333 := bbase (se 3 (by rfl) ⟨48812, by rfl⟩ : syracuseStep 260333 = 97625) (by norm_num)
theorem B194809 : Blo 171799 194809 := bbase (se 2 (by rfl) ⟨73053, by rfl⟩ : syracuseStep 194809 = 146107) (by norm_num)
theorem B260357 : Blo 171799 260357 := bbase (se 4 (by rfl) ⟨24408, by rfl⟩ : syracuseStep 260357 = 48817) (by norm_num)
theorem B293125 : Blo 171799 293125 := bbase (se 4 (by rfl) ⟨27480, by rfl⟩ : syracuseStep 293125 = 54961) (by norm_num)
theorem B391445 : Blo 171799 391445 := bbase (se 6 (by rfl) ⟨9174, by rfl⟩ : syracuseStep 391445 = 18349) (by norm_num)
theorem B194845 : Blo 171799 194845 := bbase (se 3 (by rfl) ⟨36533, by rfl⟩ : syracuseStep 194845 = 73067) (by norm_num)
theorem B260381 : Blo 171799 260381 := bbase (se 3 (by rfl) ⟨48821, by rfl⟩ : syracuseStep 260381 = 97643) (by norm_num)
theorem B260405 : Blo 171799 260405 := bbase (se 5 (by rfl) ⟨12206, by rfl⟩ : syracuseStep 260405 = 24413) (by norm_num)
theorem B194881 : Blo 171799 194881 := bbase (se 2 (by rfl) ⟨73080, by rfl⟩ : syracuseStep 194881 = 146161) (by norm_num)
theorem B489797 : Blo 171799 489797 := bbase (se 4 (by rfl) ⟨45918, by rfl⟩ : syracuseStep 489797 = 91837) (by norm_num)
theorem B260429 : Blo 171799 260429 := bbase (se 3 (by rfl) ⟨48830, by rfl⟩ : syracuseStep 260429 = 97661) (by norm_num)
theorem B293213 : Blo 171799 293213 := bbase (se 3 (by rfl) ⟨54977, by rfl⟩ : syracuseStep 293213 = 109955) (by norm_num)
theorem B391517 : Blo 171799 391517 := bbase (se 3 (by rfl) ⟨73409, by rfl⟩ : syracuseStep 391517 = 146819) (by norm_num)
theorem B194917 : Blo 171799 194917 := bbase (se 4 (by rfl) ⟨18273, by rfl⟩ : syracuseStep 194917 = 36547) (by norm_num)
theorem B260453 : Blo 171799 260453 := bbase (se 4 (by rfl) ⟨24417, by rfl⟩ : syracuseStep 260453 = 48835) (by norm_num)
theorem B883061 : Blo 171799 883061 := bbase (se 5 (by rfl) ⟨41393, by rfl⟩ : syracuseStep 883061 = 82787) (by norm_num)
theorem B260477 : Blo 171799 260477 := bbase (se 3 (by rfl) ⟨48839, by rfl⟩ : syracuseStep 260477 = 97679) (by norm_num)
theorem B194953 : Blo 171799 194953 := bbase (se 2 (by rfl) ⟨73107, by rfl⟩ : syracuseStep 194953 = 146215) (by norm_num)
theorem B260501 : Blo 171799 260501 := bbase (se 6 (by rfl) ⟨6105, by rfl⟩ : syracuseStep 260501 = 12211) (by norm_num)
theorem B391589 : Blo 171799 391589 := bbase (se 4 (by rfl) ⟨36711, by rfl⟩ : syracuseStep 391589 = 73423) (by norm_num)
theorem B194989 : Blo 171799 194989 := bbase (se 3 (by rfl) ⟨36560, by rfl⟩ : syracuseStep 194989 = 73121) (by norm_num)
theorem B260525 : Blo 171799 260525 := bbase (se 3 (by rfl) ⟨48848, by rfl⟩ : syracuseStep 260525 = 97697) (by norm_num)
theorem B1800629 : Blo 171799 1800629 := bbase (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) (by norm_num)
theorem B784837 : Blo 171799 784837 := bbase (se 4 (by rfl) ⟨73578, by rfl⟩ : syracuseStep 784837 = 147157) (by norm_num)
theorem B260549 : Blo 171799 260549 := bbase (se 4 (by rfl) ⟨24426, by rfl⟩ : syracuseStep 260549 = 48853) (by norm_num)
theorem B195025 : Blo 171799 195025 := bbase (se 2 (by rfl) ⟨73134, by rfl⟩ : syracuseStep 195025 = 146269) (by norm_num)
theorem B260573 : Blo 171799 260573 := bbase (se 3 (by rfl) ⟨48857, by rfl⟩ : syracuseStep 260573 = 97715) (by norm_num)
theorem B293341 : Blo 171799 293341 := bbase (se 3 (by rfl) ⟨55001, by rfl⟩ : syracuseStep 293341 = 110003) (by norm_num)
theorem B391661 : Blo 171799 391661 := bbase (se 3 (by rfl) ⟨73436, by rfl⟩ : syracuseStep 391661 = 146873) (by norm_num)
theorem B195061 : Blo 171799 195061 := bbase (se 5 (by rfl) ⟨9143, by rfl⟩ : syracuseStep 195061 = 18287) (by norm_num)
theorem B260597 : Blo 171799 260597 := bbase (se 5 (by rfl) ⟨12215, by rfl⟩ : syracuseStep 260597 = 24431) (by norm_num)
theorem B260621 : Blo 171799 260621 := bbase (se 3 (by rfl) ⟨48866, by rfl⟩ : syracuseStep 260621 = 97733) (by norm_num)
theorem B195097 : Blo 171799 195097 := bbase (se 2 (by rfl) ⟨73161, by rfl⟩ : syracuseStep 195097 = 146323) (by norm_num)
theorem B260645 : Blo 171799 260645 := bbase (se 4 (by rfl) ⟨24435, by rfl⟩ : syracuseStep 260645 = 48871) (by norm_num)
theorem B326197 : Blo 171799 326197 := bbase (se 5 (by rfl) ⟨15290, by rfl⟩ : syracuseStep 326197 = 30581) (by norm_num)
theorem B293429 : Blo 171799 293429 := bbase (se 5 (by rfl) ⟨13754, by rfl⟩ : syracuseStep 293429 = 27509) (by norm_num)
theorem B391733 : Blo 171799 391733 := bbase (se 5 (by rfl) ⟨18362, by rfl⟩ : syracuseStep 391733 = 36725) (by norm_num)
theorem B195133 : Blo 171799 195133 := bbase (se 3 (by rfl) ⟨36587, by rfl⟩ : syracuseStep 195133 = 73175) (by norm_num)
theorem B260669 : Blo 171799 260669 := bbase (se 3 (by rfl) ⟨48875, by rfl⟩ : syracuseStep 260669 = 97751) (by norm_num)
theorem B260693 : Blo 171799 260693 := bbase (se 8 (by rfl) ⟨1527, by rfl⟩ : syracuseStep 260693 = 3055) (by norm_num)
theorem B195169 : Blo 171799 195169 := bbase (se 2 (by rfl) ⟨73188, by rfl⟩ : syracuseStep 195169 = 146377) (by norm_num)
theorem B260717 : Blo 171799 260717 := bbase (se 3 (by rfl) ⟨48884, by rfl⟩ : syracuseStep 260717 = 97769) (by norm_num)
theorem B391805 : Blo 171799 391805 := bbase (se 3 (by rfl) ⟨73463, by rfl⟩ : syracuseStep 391805 = 146927) (by norm_num)
theorem B195205 : Blo 171799 195205 := bbase (se 4 (by rfl) ⟨18300, by rfl⟩ : syracuseStep 195205 = 36601) (by norm_num)
theorem B260741 : Blo 171799 260741 := bbase (se 4 (by rfl) ⟨24444, by rfl⟩ : syracuseStep 260741 = 48889) (by norm_num)
theorem B424597 : Blo 171799 424597 := bbase (se 6 (by rfl) ⟨9951, by rfl⟩ : syracuseStep 424597 = 19903) (by norm_num)
theorem B588437 : Blo 171799 588437 := bbase (se 6 (by rfl) ⟨13791, by rfl⟩ : syracuseStep 588437 = 27583) (by norm_num)
theorem B260765 : Blo 171799 260765 := bbase (se 3 (by rfl) ⟨48893, by rfl⟩ : syracuseStep 260765 = 97787) (by norm_num)
theorem B195241 : Blo 171799 195241 := bbase (se 2 (by rfl) ⟨73215, by rfl⟩ : syracuseStep 195241 = 146431) (by norm_num)
theorem B260789 : Blo 171799 260789 := bbase (se 5 (by rfl) ⟨12224, by rfl⟩ : syracuseStep 260789 = 24449) (by norm_num)
theorem B293557 : Blo 171799 293557 := bbase (se 5 (by rfl) ⟨13760, by rfl⟩ : syracuseStep 293557 = 27521) (by norm_num)
theorem B391877 : Blo 171799 391877 := bbase (se 4 (by rfl) ⟨36738, by rfl⟩ : syracuseStep 391877 = 73477) (by norm_num)
theorem B195277 : Blo 171799 195277 := bbase (se 3 (by rfl) ⟨36614, by rfl⟩ : syracuseStep 195277 = 73229) (by norm_num)
theorem B260813 : Blo 171799 260813 := bbase (se 3 (by rfl) ⟨48902, by rfl⟩ : syracuseStep 260813 = 97805) (by norm_num)
theorem B260837 : Blo 171799 260837 := bbase (se 4 (by rfl) ⟨24453, by rfl⟩ : syracuseStep 260837 = 48907) (by norm_num)
theorem B195313 : Blo 171799 195313 := bbase (se 2 (by rfl) ⟨73242, by rfl⟩ : syracuseStep 195313 = 146485) (by norm_num)
theorem B260861 : Blo 171799 260861 := bbase (se 3 (by rfl) ⟨48911, by rfl⟩ : syracuseStep 260861 = 97823) (by norm_num)
theorem B293645 : Blo 171799 293645 := bbase (se 3 (by rfl) ⟨55058, by rfl⟩ : syracuseStep 293645 = 110117) (by norm_num)
theorem B391949 : Blo 171799 391949 := bbase (se 3 (by rfl) ⟨73490, by rfl⟩ : syracuseStep 391949 = 146981) (by norm_num)
theorem B195349 : Blo 171799 195349 := bbase (se 6 (by rfl) ⟨4578, by rfl⟩ : syracuseStep 195349 = 9157) (by norm_num)
theorem B260885 : Blo 171799 260885 := bbase (se 6 (by rfl) ⟨6114, by rfl⟩ : syracuseStep 260885 = 12229) (by norm_num)
theorem B260909 : Blo 171799 260909 := bbase (se 3 (by rfl) ⟨48920, by rfl⟩ : syracuseStep 260909 = 97841) (by norm_num)
theorem B195385 : Blo 171799 195385 := bbase (se 2 (by rfl) ⟨73269, by rfl⟩ : syracuseStep 195385 = 146539) (by norm_num)
theorem B260933 : Blo 171799 260933 := bbase (se 4 (by rfl) ⟨24462, by rfl⟩ : syracuseStep 260933 = 48925) (by norm_num)
theorem B1604437 : Blo 171799 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B392021 : Blo 171799 392021 := bbase (se 9 (by rfl) ⟨1148, by rfl⟩ : syracuseStep 392021 = 2297) (by norm_num)
theorem B195421 : Blo 171799 195421 := bbase (se 3 (by rfl) ⟨36641, by rfl⟩ : syracuseStep 195421 = 73283) (by norm_num)
theorem B260957 : Blo 171799 260957 := bbase (se 3 (by rfl) ⟨48929, by rfl⟩ : syracuseStep 260957 = 97859) (by norm_num)
theorem B326501 : Blo 171799 326501 := bbase (se 4 (by rfl) ⟨30609, by rfl⟩ : syracuseStep 326501 = 61219) (by norm_num)
theorem B555893 : Blo 171799 555893 := bbase (se 5 (by rfl) ⟨26057, by rfl⟩ : syracuseStep 555893 = 52115) (by norm_num)
theorem B260981 : Blo 171799 260981 := bbase (se 5 (by rfl) ⟨12233, by rfl⟩ : syracuseStep 260981 = 24467) (by norm_num)
theorem B195457 : Blo 171799 195457 := bbase (se 2 (by rfl) ⟨73296, by rfl⟩ : syracuseStep 195457 = 146593) (by norm_num)
theorem B261005 : Blo 171799 261005 := bbase (se 3 (by rfl) ⟨48938, by rfl⟩ : syracuseStep 261005 = 97877) (by norm_num)
theorem B293773 : Blo 171799 293773 := bbase (se 3 (by rfl) ⟨55082, by rfl⟩ : syracuseStep 293773 = 110165) (by norm_num)
theorem B392093 : Blo 171799 392093 := bbase (se 3 (by rfl) ⟨73517, by rfl⟩ : syracuseStep 392093 = 147035) (by norm_num)
theorem B195493 : Blo 171799 195493 := bbase (se 4 (by rfl) ⟨18327, by rfl⟩ : syracuseStep 195493 = 36655) (by norm_num)
theorem B261029 : Blo 171799 261029 := bbase (se 4 (by rfl) ⟨24471, by rfl⟩ : syracuseStep 261029 = 48943) (by norm_num)
theorem B261053 : Blo 171799 261053 := bbase (se 3 (by rfl) ⟨48947, by rfl⟩ : syracuseStep 261053 = 97895) (by norm_num)
theorem B654277 : Blo 171799 654277 := bbase (se 4 (by rfl) ⟨61338, by rfl⟩ : syracuseStep 654277 = 122677) (by norm_num)
theorem B195529 : Blo 171799 195529 := bbase (se 2 (by rfl) ⟨73323, by rfl⟩ : syracuseStep 195529 = 146647) (by norm_num)
theorem B261077 : Blo 171799 261077 := bbase (se 7 (by rfl) ⟨3059, by rfl⟩ : syracuseStep 261077 = 6119) (by norm_num)
theorem B293861 : Blo 171799 293861 := bbase (se 4 (by rfl) ⟨27549, by rfl⟩ : syracuseStep 293861 = 55099) (by norm_num)
theorem B392165 : Blo 171799 392165 := bbase (se 4 (by rfl) ⟨36765, by rfl⟩ : syracuseStep 392165 = 73531) (by norm_num)
theorem B195565 : Blo 171799 195565 := bbase (se 3 (by rfl) ⟨36668, by rfl⟩ : syracuseStep 195565 = 73337) (by norm_num)
theorem B261101 : Blo 171799 261101 := bbase (se 3 (by rfl) ⟨48956, by rfl⟩ : syracuseStep 261101 = 97913) (by norm_num)
theorem B261125 : Blo 171799 261125 := bbase (se 4 (by rfl) ⟨24480, by rfl⟩ : syracuseStep 261125 = 48961) (by norm_num)
theorem B195601 : Blo 171799 195601 := bbase (se 2 (by rfl) ⟨73350, by rfl⟩ : syracuseStep 195601 = 146701) (by norm_num)
theorem B261149 : Blo 171799 261149 := bbase (se 3 (by rfl) ⟨48965, by rfl⟩ : syracuseStep 261149 = 97931) (by norm_num)
theorem B392237 : Blo 171799 392237 := bbase (se 3 (by rfl) ⟨73544, by rfl⟩ : syracuseStep 392237 = 147089) (by norm_num)
theorem B490549 : Blo 171799 490549 := bbase (se 5 (by rfl) ⟨22994, by rfl⟩ : syracuseStep 490549 = 45989) (by norm_num)
theorem B195637 : Blo 171799 195637 := bbase (se 5 (by rfl) ⟨9170, by rfl⟩ : syracuseStep 195637 = 18341) (by norm_num)
theorem B261173 : Blo 171799 261173 := bbase (se 5 (by rfl) ⟨12242, by rfl⟩ : syracuseStep 261173 = 24485) (by norm_num)
theorem B588869 : Blo 171799 588869 := bbase (se 4 (by rfl) ⟨55206, by rfl⟩ : syracuseStep 588869 = 110413) (by norm_num)
theorem B261197 : Blo 171799 261197 := bbase (se 3 (by rfl) ⟨48974, by rfl⟩ : syracuseStep 261197 = 97949) (by norm_num)
theorem B195673 : Blo 171799 195673 := bbase (se 2 (by rfl) ⟨73377, by rfl⟩ : syracuseStep 195673 = 146755) (by norm_num)
theorem B261221 : Blo 171799 261221 := bbase (se 4 (by rfl) ⟨24489, by rfl⟩ : syracuseStep 261221 = 48979) (by norm_num)
theorem B293989 : Blo 171799 293989 := bbase (se 4 (by rfl) ⟨27561, by rfl⟩ : syracuseStep 293989 = 55123) (by norm_num)
theorem B392309 : Blo 171799 392309 := bbase (se 5 (by rfl) ⟨18389, by rfl⟩ : syracuseStep 392309 = 36779) (by norm_num)
theorem B195709 : Blo 171799 195709 := bbase (se 3 (by rfl) ⟨36695, by rfl⟩ : syracuseStep 195709 = 73391) (by norm_num)
theorem B261245 : Blo 171799 261245 := bbase (se 3 (by rfl) ⟨48983, by rfl⟩ : syracuseStep 261245 = 97967) (by norm_num)
theorem B261269 : Blo 171799 261269 := bbase (se 6 (by rfl) ⟨6123, by rfl⟩ : syracuseStep 261269 = 12247) (by norm_num)
theorem B195745 : Blo 171799 195745 := bbase (se 2 (by rfl) ⟨73404, by rfl⟩ : syracuseStep 195745 = 146809) (by norm_num)
theorem B261293 : Blo 171799 261293 := bbase (se 3 (by rfl) ⟨48992, by rfl⟩ : syracuseStep 261293 = 97985) (by norm_num)
theorem B294077 : Blo 171799 294077 := bbase (se 3 (by rfl) ⟨55139, by rfl⟩ : syracuseStep 294077 = 110279) (by norm_num)
theorem B392381 : Blo 171799 392381 := bbase (se 3 (by rfl) ⟨73571, by rfl⟩ : syracuseStep 392381 = 147143) (by norm_num)
theorem B195781 : Blo 171799 195781 := bbase (se 4 (by rfl) ⟨18354, by rfl⟩ : syracuseStep 195781 = 36709) (by norm_num)
theorem B261317 : Blo 171799 261317 := bbase (se 4 (by rfl) ⟨24498, by rfl⟩ : syracuseStep 261317 = 48997) (by norm_num)
theorem B261341 : Blo 171799 261341 := bbase (se 3 (by rfl) ⟨49001, by rfl⟩ : syracuseStep 261341 = 98003) (by norm_num)
theorem B195817 : Blo 171799 195817 := bbase (se 2 (by rfl) ⟨73431, by rfl⟩ : syracuseStep 195817 = 146863) (by norm_num)
theorem B654581 : Blo 171799 654581 := bbase (se 5 (by rfl) ⟨30683, by rfl⟩ : syracuseStep 654581 = 61367) (by norm_num)
theorem B261365 : Blo 171799 261365 := bbase (se 5 (by rfl) ⟨12251, by rfl⟩ : syracuseStep 261365 = 24503) (by norm_num)
theorem B392453 : Blo 171799 392453 := bbase (se 4 (by rfl) ⟨36792, by rfl⟩ : syracuseStep 392453 = 73585) (by norm_num)
theorem B195853 : Blo 171799 195853 := bbase (se 3 (by rfl) ⟨36722, by rfl⟩ : syracuseStep 195853 = 73445) (by norm_num)
theorem B261389 : Blo 171799 261389 := bbase (se 3 (by rfl) ⟨49010, by rfl⟩ : syracuseStep 261389 = 98021) (by norm_num)
theorem B261413 : Blo 171799 261413 := bbase (se 4 (by rfl) ⟨24507, by rfl⟩ : syracuseStep 261413 = 49015) (by norm_num)
theorem B195889 : Blo 171799 195889 := bbase (se 2 (by rfl) ⟨73458, by rfl⟩ : syracuseStep 195889 = 146917) (by norm_num)
theorem B261437 : Blo 171799 261437 := bbase (se 3 (by rfl) ⟨49019, by rfl⟩ : syracuseStep 261437 = 98039) (by norm_num)
theorem B294205 : Blo 171799 294205 := bbase (se 3 (by rfl) ⟨55163, by rfl⟩ : syracuseStep 294205 = 110327) (by norm_num)
theorem B392525 : Blo 171799 392525 := bbase (se 3 (by rfl) ⟨73598, by rfl⟩ : syracuseStep 392525 = 147197) (by norm_num)
theorem B195925 : Blo 171799 195925 := bbase (se 11 (by rfl) ⟨143, by rfl⟩ : syracuseStep 195925 = 287) (by norm_num)
theorem B261461 : Blo 171799 261461 := bbase (se 11 (by rfl) ⟨191, by rfl⟩ : syracuseStep 261461 = 383) (by norm_num)
theorem B261485 : Blo 171799 261485 := bbase (se 3 (by rfl) ⟨49028, by rfl⟩ : syracuseStep 261485 = 98057) (by norm_num)
theorem B195961 : Blo 171799 195961 := bbase (se 2 (by rfl) ⟨73485, by rfl⟩ : syracuseStep 195961 = 146971) (by norm_num)
theorem B261509 : Blo 171799 261509 := bbase (se 4 (by rfl) ⟨24516, by rfl⟩ : syracuseStep 261509 = 49033) (by norm_num)
theorem B294293 : Blo 171799 294293 := bbase (se 6 (by rfl) ⟨6897, by rfl⟩ : syracuseStep 294293 = 13795) (by norm_num)
theorem B392597 : Blo 171799 392597 := bbase (se 6 (by rfl) ⟨9201, by rfl⟩ : syracuseStep 392597 = 18403) (by norm_num)
theorem B195997 : Blo 171799 195997 := bbase (se 3 (by rfl) ⟨36749, by rfl⟩ : syracuseStep 195997 = 73499) (by norm_num)
theorem B261533 : Blo 171799 261533 := bbase (se 3 (by rfl) ⟨49037, by rfl⟩ : syracuseStep 261533 = 98075) (by norm_num)
theorem B261557 : Blo 171799 261557 := bbase (se 5 (by rfl) ⟨12260, by rfl⟩ : syracuseStep 261557 = 24521) (by norm_num)
theorem B196033 : Blo 171799 196033 := bbase (se 2 (by rfl) ⟨73512, by rfl⟩ : syracuseStep 196033 = 147025) (by norm_num)
theorem B261581 : Blo 171799 261581 := bbase (se 3 (by rfl) ⟨49046, by rfl⟩ : syracuseStep 261581 = 98093) (by norm_num)
theorem B392669 : Blo 171799 392669 := bbase (se 3 (by rfl) ⟨73625, by rfl⟩ : syracuseStep 392669 = 147251) (by norm_num)
theorem B196069 : Blo 171799 196069 := bbase (se 4 (by rfl) ⟨18381, by rfl⟩ : syracuseStep 196069 = 36763) (by norm_num)
theorem B261605 : Blo 171799 261605 := bbase (se 4 (by rfl) ⟨24525, by rfl⟩ : syracuseStep 261605 = 49051) (by norm_num)
theorem B589301 : Blo 171799 589301 := bbase (se 5 (by rfl) ⟨27623, by rfl⟩ : syracuseStep 589301 = 55247) (by norm_num)
theorem B261629 : Blo 171799 261629 := bbase (se 3 (by rfl) ⟨49055, by rfl⟩ : syracuseStep 261629 = 98111) (by norm_num)
theorem B196105 : Blo 171799 196105 := bbase (se 2 (by rfl) ⟨73539, by rfl⟩ : syracuseStep 196105 = 147079) (by norm_num)
theorem B261653 : Blo 171799 261653 := bbase (se 6 (by rfl) ⟨6132, by rfl⟩ : syracuseStep 261653 = 12265) (by norm_num)
theorem B294421 : Blo 171799 294421 := bbase (se 6 (by rfl) ⟨6900, by rfl⟩ : syracuseStep 294421 = 13801) (by norm_num)
theorem B392741 : Blo 171799 392741 := bbase (se 4 (by rfl) ⟨36819, by rfl⟩ : syracuseStep 392741 = 73639) (by norm_num)
theorem B196141 : Blo 171799 196141 := bbase (se 3 (by rfl) ⟨36776, by rfl⟩ : syracuseStep 196141 = 73553) (by norm_num)
theorem B261677 : Blo 171799 261677 := bbase (se 3 (by rfl) ⟨49064, by rfl⟩ : syracuseStep 261677 = 98129) (by norm_num)
theorem B261701 : Blo 171799 261701 := bbase (se 4 (by rfl) ⟨24534, by rfl⟩ : syracuseStep 261701 = 49069) (by norm_num)
theorem B196177 : Blo 171799 196177 := bbase (se 2 (by rfl) ⟨73566, by rfl⟩ : syracuseStep 196177 = 147133) (by norm_num)
theorem B327253 : Blo 171799 327253 := bbase (se 8 (by rfl) ⟨1917, by rfl⟩ : syracuseStep 327253 = 3835) (by norm_num)
theorem B261725 : Blo 171799 261725 := bbase (se 3 (by rfl) ⟨49073, by rfl⟩ : syracuseStep 261725 = 98147) (by norm_num)
theorem B294509 : Blo 171799 294509 := bbase (se 3 (by rfl) ⟨55220, by rfl⟩ : syracuseStep 294509 = 110441) (by norm_num)
theorem B392813 : Blo 171799 392813 := bbase (se 3 (by rfl) ⟨73652, by rfl⟩ : syracuseStep 392813 = 147305) (by norm_num)
theorem B196213 : Blo 171799 196213 := bbase (se 5 (by rfl) ⟨9197, by rfl⟩ : syracuseStep 196213 = 18395) (by norm_num)
theorem B261749 : Blo 171799 261749 := bbase (se 5 (by rfl) ⟨12269, by rfl⟩ : syracuseStep 261749 = 24539) (by norm_num)
theorem B884357 : Blo 171799 884357 := bbase (se 4 (by rfl) ⟨82908, by rfl⟩ : syracuseStep 884357 = 165817) (by norm_num)
theorem B261773 : Blo 171799 261773 := bbase (se 3 (by rfl) ⟨49082, by rfl⟩ : syracuseStep 261773 = 98165) (by norm_num)
theorem B196249 : Blo 171799 196249 := bbase (se 2 (by rfl) ⟨73593, by rfl⟩ : syracuseStep 196249 = 147187) (by norm_num)
theorem B261797 : Blo 171799 261797 := bbase (se 4 (by rfl) ⟨24543, by rfl⟩ : syracuseStep 261797 = 49087) (by norm_num)
theorem B392885 : Blo 171799 392885 := bbase (se 5 (by rfl) ⟨18416, by rfl⟩ : syracuseStep 392885 = 36833) (by norm_num)
theorem B196285 : Blo 171799 196285 := bbase (se 3 (by rfl) ⟨36803, by rfl⟩ : syracuseStep 196285 = 73607) (by norm_num)
theorem B261821 : Blo 171799 261821 := bbase (se 3 (by rfl) ⟨49091, by rfl⟩ : syracuseStep 261821 = 98183) (by norm_num)
theorem B261845 : Blo 171799 261845 := bbase (se 7 (by rfl) ⟨3068, by rfl⟩ : syracuseStep 261845 = 6137) (by norm_num)
theorem B196321 : Blo 171799 196321 := bbase (se 2 (by rfl) ⟨73620, by rfl⟩ : syracuseStep 196321 = 147241) (by norm_num)
theorem B327397 : Blo 171799 327397 := bbase (se 4 (by rfl) ⟨30693, by rfl⟩ : syracuseStep 327397 = 61387) (by norm_num)
theorem B261869 : Blo 171799 261869 := bbase (se 3 (by rfl) ⟨49100, by rfl⟩ : syracuseStep 261869 = 98201) (by norm_num)
theorem B294637 : Blo 171799 294637 := bbase (se 3 (by rfl) ⟨55244, by rfl⟩ : syracuseStep 294637 = 110489) (by norm_num)
theorem B556789 : Blo 171799 556789 := bbase (se 5 (by rfl) ⟨26099, by rfl⟩ : syracuseStep 556789 = 52199) (by norm_num)
theorem B392957 : Blo 171799 392957 := bbase (se 3 (by rfl) ⟨73679, by rfl⟩ : syracuseStep 392957 = 147359) (by norm_num)
theorem B196357 : Blo 171799 196357 := bbase (se 4 (by rfl) ⟨18408, by rfl⟩ : syracuseStep 196357 = 36817) (by norm_num)
theorem B261893 : Blo 171799 261893 := bbase (se 4 (by rfl) ⟨24552, by rfl⟩ : syracuseStep 261893 = 49105) (by norm_num)
theorem B261917 : Blo 171799 261917 := bbase (se 3 (by rfl) ⟨49109, by rfl⟩ : syracuseStep 261917 = 98219) (by norm_num)
theorem B196393 : Blo 171799 196393 := bbase (se 2 (by rfl) ⟨73647, by rfl⟩ : syracuseStep 196393 = 147295) (by norm_num)
theorem B261941 : Blo 171799 261941 := bbase (se 5 (by rfl) ⟨12278, by rfl⟩ : syracuseStep 261941 = 24557) (by norm_num)
theorem B294725 : Blo 171799 294725 := bbase (se 4 (by rfl) ⟨27630, by rfl⟩ : syracuseStep 294725 = 55261) (by norm_num)
theorem B393029 : Blo 171799 393029 := bbase (se 4 (by rfl) ⟨36846, by rfl⟩ : syracuseStep 393029 = 73693) (by norm_num)
theorem B196429 : Blo 171799 196429 := bbase (se 3 (by rfl) ⟨36830, by rfl⟩ : syracuseStep 196429 = 73661) (by norm_num)
theorem B261965 : Blo 171799 261965 := bbase (se 3 (by rfl) ⟨49118, by rfl⟩ : syracuseStep 261965 = 98237) (by norm_num)
theorem B261989 : Blo 171799 261989 := bbase (se 4 (by rfl) ⟨24561, by rfl⟩ : syracuseStep 261989 = 49123) (by norm_num)
theorem B196465 : Blo 171799 196465 := bbase (se 2 (by rfl) ⟨73674, by rfl⟩ : syracuseStep 196465 = 147349) (by norm_num)
theorem B262013 : Blo 171799 262013 := bbase (se 3 (by rfl) ⟨49127, by rfl⟩ : syracuseStep 262013 = 98255) (by norm_num)
theorem B327557 : Blo 171799 327557 := bbase (se 4 (by rfl) ⟨30708, by rfl⟩ : syracuseStep 327557 = 61417) (by norm_num)
theorem B393101 : Blo 171799 393101 := bbase (se 3 (by rfl) ⟨73706, by rfl⟩ : syracuseStep 393101 = 147413) (by norm_num)
theorem B196501 : Blo 171799 196501 := bbase (se 6 (by rfl) ⟨4605, by rfl⟩ : syracuseStep 196501 = 9211) (by norm_num)
theorem B262037 : Blo 171799 262037 := bbase (se 6 (by rfl) ⟨6141, by rfl⟩ : syracuseStep 262037 = 12283) (by norm_num)
theorem B589733 : Blo 171799 589733 := bbase (se 4 (by rfl) ⟨55287, by rfl⟩ : syracuseStep 589733 = 110575) (by norm_num)
theorem B262061 : Blo 171799 262061 := bbase (se 3 (by rfl) ⟨49136, by rfl⟩ : syracuseStep 262061 = 98273) (by norm_num)
theorem B196537 : Blo 171799 196537 := bbase (se 2 (by rfl) ⟨73701, by rfl⟩ : syracuseStep 196537 = 147403) (by norm_num)
theorem B262085 : Blo 171799 262085 := bbase (se 4 (by rfl) ⟨24570, by rfl⟩ : syracuseStep 262085 = 49141) (by norm_num)
theorem B294853 : Blo 171799 294853 := bbase (se 4 (by rfl) ⟨27642, by rfl⟩ : syracuseStep 294853 = 55285) (by norm_num)
theorem B393173 : Blo 171799 393173 := bbase (se 7 (by rfl) ⟨4607, by rfl⟩ : syracuseStep 393173 = 9215) (by norm_num)
theorem B196573 : Blo 171799 196573 := bbase (se 3 (by rfl) ⟨36857, by rfl⟩ : syracuseStep 196573 = 73715) (by norm_num)
theorem B262109 : Blo 171799 262109 := bbase (se 3 (by rfl) ⟨49145, by rfl⟩ : syracuseStep 262109 = 98291) (by norm_num)
theorem B262133 : Blo 171799 262133 := bbase (se 5 (by rfl) ⟨12287, by rfl⟩ : syracuseStep 262133 = 24575) (by norm_num)
theorem B262145 : Blo 171799 262145 := bstep (se 2 (by rfl) ⟨98304, by rfl⟩ : syracuseStep 262145 = 196609) B196609
theorem B589841 : Blo 171799 589841 := bstep (se 2 (by rfl) ⟨221190, by rfl⟩ : syracuseStep 589841 = 442381) B442381
theorem B262163 : Blo 171799 262163 := bstep (se 1 (by rfl) ⟨196622, by rfl⟩ : syracuseStep 262163 = 393245) B393245
theorem B196627 : Blo 171799 196627 := bstep (se 1 (by rfl) ⟨147470, by rfl⟩ : syracuseStep 196627 = 294941) B294941
theorem B294961 : Blo 171799 294961 := bstep (se 2 (by rfl) ⟨110610, by rfl⟩ : syracuseStep 294961 = 221221) B221221
theorem B262193 : Blo 171799 262193 := bstep (se 2 (by rfl) ⟨98322, by rfl⟩ : syracuseStep 262193 = 196645) B196645
theorem B262211 : Blo 171799 262211 := bstep (se 1 (by rfl) ⟨196658, by rfl⟩ : syracuseStep 262211 = 393317) B393317
theorem B1998917 : Blo 171799 1998917 := bstep (se 4 (by rfl) ⟨187398, by rfl⟩ : syracuseStep 1998917 = 374797) B374797
theorem B294995 : Blo 171799 294995 := bstep (se 1 (by rfl) ⟨221246, by rfl⟩ : syracuseStep 294995 = 442493) B442493
theorem B262241 : Blo 171799 262241 := bstep (se 2 (by rfl) ⟨98340, by rfl⟩ : syracuseStep 262241 = 196681) B196681
theorem B262259 : Blo 171799 262259 := bstep (se 1 (by rfl) ⟨196694, by rfl⟩ : syracuseStep 262259 = 393389) B393389
theorem B491665 : Blo 171799 491665 := bstep (se 2 (by rfl) ⟨184374, by rfl⟩ : syracuseStep 491665 = 368749) B368749
theorem B262289 : Blo 171799 262289 := bstep (se 2 (by rfl) ⟨98358, by rfl⟩ : syracuseStep 262289 = 196717) B196717
theorem B655523 : Blo 171799 655523 := bstep (se 1 (by rfl) ⟨491642, by rfl⟩ : syracuseStep 655523 = 983285) B983285
theorem B262307 : Blo 171799 262307 := bstep (se 1 (by rfl) ⟨196730, by rfl⟩ : syracuseStep 262307 = 393461) B393461
theorem B196771 : Blo 171799 196771 := bstep (se 1 (by rfl) ⟨147578, by rfl⟩ : syracuseStep 196771 = 295157) B295157
theorem B262337 : Blo 171799 262337 := bstep (se 2 (by rfl) ⟨98376, by rfl⟩ : syracuseStep 262337 = 196753) B196753
theorem B393425 : Blo 171799 393425 := bstep (se 2 (by rfl) ⟨147534, by rfl⟩ : syracuseStep 393425 = 295069) B295069
theorem B295123 : Blo 171799 295123 := bstep (se 1 (by rfl) ⟨221342, by rfl⟩ : syracuseStep 295123 = 442685) B442685
theorem B262355 : Blo 171799 262355 := bstep (se 1 (by rfl) ⟨196766, by rfl⟩ : syracuseStep 262355 = 393533) B393533
theorem B393443 : Blo 171799 393443 := bstep (se 1 (by rfl) ⟨295082, by rfl⟩ : syracuseStep 393443 = 590165) B590165
theorem B262385 : Blo 171799 262385 := bstep (se 2 (by rfl) ⟨98394, by rfl⟩ : syracuseStep 262385 = 196789) B196789
theorem B262403 : Blo 171799 262403 := bstep (se 1 (by rfl) ⟨196802, by rfl⟩ : syracuseStep 262403 = 393605) B393605
theorem B885005 : Blo 171799 885005 := bstep (se 3 (by rfl) ⟨165938, by rfl⟩ : syracuseStep 885005 = 331877) B331877
theorem B262433 : Blo 171799 262433 := bstep (se 2 (by rfl) ⟨98412, by rfl⟩ : syracuseStep 262433 = 196825) B196825
theorem B491825 : Blo 171799 491825 := bstep (se 2 (by rfl) ⟨184434, by rfl⟩ : syracuseStep 491825 = 368869) B368869
theorem B262451 : Blo 171799 262451 := bstep (se 1 (by rfl) ⟨196838, by rfl⟩ : syracuseStep 262451 = 393677) B393677
theorem B196915 : Blo 171799 196915 := bstep (se 1 (by rfl) ⟨147686, by rfl⟩ : syracuseStep 196915 = 295373) B295373
theorem B262481 : Blo 171799 262481 := bstep (se 2 (by rfl) ⟨98430, by rfl⟩ : syracuseStep 262481 = 196861) B196861
theorem B295265 : Blo 171799 295265 := bstep (se 2 (by rfl) ⟨110724, by rfl⟩ : syracuseStep 295265 = 221449) B221449
theorem B262499 : Blo 171799 262499 := bstep (se 1 (by rfl) ⟨196874, by rfl⟩ : syracuseStep 262499 = 393749) B393749
theorem B262529 : Blo 171799 262529 := bstep (se 2 (by rfl) ⟨98448, by rfl⟩ : syracuseStep 262529 = 196897) B196897
theorem B262547 : Blo 171799 262547 := bstep (se 1 (by rfl) ⟨196910, by rfl⟩ : syracuseStep 262547 = 393821) B393821
theorem B491939 : Blo 171799 491939 := bstep (se 1 (by rfl) ⟨368954, by rfl⟩ : syracuseStep 491939 = 737909) B737909
theorem B262577 : Blo 171799 262577 := bstep (se 2 (by rfl) ⟨98466, by rfl⟩ : syracuseStep 262577 = 196933) B196933
theorem B262595 : Blo 171799 262595 := bstep (se 1 (by rfl) ⟨196946, by rfl⟩ : syracuseStep 262595 = 393893) B393893
theorem B197059 : Blo 171799 197059 := bstep (se 1 (by rfl) ⟨147794, by rfl⟩ : syracuseStep 197059 = 295589) B295589
theorem B295393 : Blo 171799 295393 := bstep (se 2 (by rfl) ⟨110772, by rfl⟩ : syracuseStep 295393 = 221545) B221545
theorem B262625 : Blo 171799 262625 := bstep (se 2 (by rfl) ⟨98484, by rfl⟩ : syracuseStep 262625 = 196969) B196969
theorem B393713 : Blo 171799 393713 := bstep (se 2 (by rfl) ⟨147642, by rfl⟩ : syracuseStep 393713 = 295285) B295285
theorem B262643 : Blo 171799 262643 := bstep (se 1 (by rfl) ⟨196982, by rfl⟩ : syracuseStep 262643 = 393965) B393965
theorem B393731 : Blo 171799 393731 := bstep (se 1 (by rfl) ⟨295298, by rfl⟩ : syracuseStep 393731 = 590597) B590597
theorem B295427 : Blo 171799 295427 := bstep (se 1 (by rfl) ⟨221570, by rfl⟩ : syracuseStep 295427 = 443141) B443141
theorem B262673 : Blo 171799 262673 := bstep (se 2 (by rfl) ⟨98502, by rfl⟩ : syracuseStep 262673 = 197005) B197005
theorem B262691 : Blo 171799 262691 := bstep (se 1 (by rfl) ⟨197018, by rfl⟩ : syracuseStep 262691 = 394037) B394037
theorem B590381 : Blo 171799 590381 := bstep (se 3 (by rfl) ⟨110696, by rfl⟩ : syracuseStep 590381 = 221393) B221393
theorem B262721 : Blo 171799 262721 := bstep (se 2 (by rfl) ⟨98520, by rfl⟩ : syracuseStep 262721 = 197041) B197041
theorem B262739 : Blo 171799 262739 := bstep (se 1 (by rfl) ⟨197054, by rfl⟩ : syracuseStep 262739 = 394109) B394109
theorem B197203 : Blo 171799 197203 := bstep (se 1 (by rfl) ⟨147902, by rfl⟩ : syracuseStep 197203 = 295805) B295805
theorem B590435 : Blo 171799 590435 := bstep (se 1 (by rfl) ⟨442826, by rfl⟩ : syracuseStep 590435 = 885653) B885653
theorem B590449 : Blo 171799 590449 := bstep (se 2 (by rfl) ⟨221418, by rfl⟩ : syracuseStep 590449 = 442837) B442837
theorem B262769 : Blo 171799 262769 := bstep (se 2 (by rfl) ⟨98538, by rfl⟩ : syracuseStep 262769 = 197077) B197077
theorem B295555 : Blo 171799 295555 := bstep (se 1 (by rfl) ⟨221666, by rfl⟩ : syracuseStep 295555 = 443333) B443333
theorem B262787 : Blo 171799 262787 := bstep (se 1 (by rfl) ⟨197090, by rfl⟩ : syracuseStep 262787 = 394181) B394181
theorem B262817 : Blo 171799 262817 := bstep (se 2 (by rfl) ⟨98556, by rfl⟩ : syracuseStep 262817 = 197113) B197113
theorem B328369 : Blo 171799 328369 := bstep (se 2 (by rfl) ⟨123138, by rfl⟩ : syracuseStep 328369 = 246277) B246277
theorem B262835 : Blo 171799 262835 := bstep (se 1 (by rfl) ⟨197126, by rfl⟩ : syracuseStep 262835 = 394253) B394253
theorem B262865 : Blo 171799 262865 := bstep (se 2 (by rfl) ⟨98574, by rfl⟩ : syracuseStep 262865 = 197149) B197149
theorem B262883 : Blo 171799 262883 := bstep (se 1 (by rfl) ⟨197162, by rfl⟩ : syracuseStep 262883 = 394325) B394325
theorem B197347 : Blo 171799 197347 := bstep (se 1 (by rfl) ⟨148010, by rfl⟩ : syracuseStep 197347 = 296021) B296021
theorem B262913 : Blo 171799 262913 := bstep (se 2 (by rfl) ⟨98592, by rfl⟩ : syracuseStep 262913 = 197185) B197185
theorem B394001 : Blo 171799 394001 := bstep (se 2 (by rfl) ⟨147750, by rfl⟩ : syracuseStep 394001 = 295501) B295501
theorem B295697 : Blo 171799 295697 := bstep (se 2 (by rfl) ⟨110886, by rfl⟩ : syracuseStep 295697 = 221773) B221773
theorem B262931 : Blo 171799 262931 := bstep (se 1 (by rfl) ⟨197198, by rfl⟩ : syracuseStep 262931 = 394397) B394397
theorem B394019 : Blo 171799 394019 := bstep (se 1 (by rfl) ⟨295514, by rfl⟩ : syracuseStep 394019 = 591029) B591029
theorem B262961 : Blo 171799 262961 := bstep (se 2 (by rfl) ⟨98610, by rfl⟩ : syracuseStep 262961 = 197221) B197221
theorem B557891 : Blo 171799 557891 := bstep (se 1 (by rfl) ⟨418418, by rfl⟩ : syracuseStep 557891 = 836837) B836837
theorem B262979 : Blo 171799 262979 := bstep (se 1 (by rfl) ⟨197234, by rfl⟩ : syracuseStep 262979 = 394469) B394469
theorem B328529 : Blo 171799 328529 := bstep (se 2 (by rfl) ⟨123198, by rfl⟩ : syracuseStep 328529 = 246397) B246397
theorem B263009 : Blo 171799 263009 := bstep (se 2 (by rfl) ⟨98628, by rfl⟩ : syracuseStep 263009 = 197257) B197257
theorem B590705 : Blo 171799 590705 := bstep (se 2 (by rfl) ⟨221514, by rfl⟩ : syracuseStep 590705 = 443029) B443029
theorem B263027 : Blo 171799 263027 := bstep (se 1 (by rfl) ⟨197270, by rfl⟩ : syracuseStep 263027 = 394541) B394541
theorem B197491 : Blo 171799 197491 := bstep (se 1 (by rfl) ⟨148118, by rfl⟩ : syracuseStep 197491 = 296237) B296237
theorem B295825 : Blo 171799 295825 := bstep (se 2 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 295825 = 221869) B221869
theorem B263057 : Blo 171799 263057 := bstep (se 2 (by rfl) ⟨98646, by rfl⟩ : syracuseStep 263057 = 197293) B197293
theorem B263075 : Blo 171799 263075 := bstep (se 1 (by rfl) ⟨197306, by rfl⟩ : syracuseStep 263075 = 394613) B394613
theorem B295859 : Blo 171799 295859 := bstep (se 1 (by rfl) ⟨221894, by rfl⟩ : syracuseStep 295859 = 443789) B443789
theorem B263105 : Blo 171799 263105 := bstep (se 2 (by rfl) ⟨98664, by rfl⟩ : syracuseStep 263105 = 197329) B197329
theorem B558019 : Blo 171799 558019 := bstep (se 1 (by rfl) ⟨418514, by rfl⟩ : syracuseStep 558019 = 837029) B837029
theorem B263123 : Blo 171799 263123 := bstep (se 1 (by rfl) ⟨197342, by rfl⟩ : syracuseStep 263123 = 394685) B394685
theorem B263153 : Blo 171799 263153 := bstep (se 2 (by rfl) ⟨98682, by rfl⟩ : syracuseStep 263153 = 197365) B197365
theorem B263171 : Blo 171799 263171 := bstep (se 1 (by rfl) ⟨197378, by rfl⟩ : syracuseStep 263171 = 394757) B394757
theorem B197635 : Blo 171799 197635 := bstep (se 1 (by rfl) ⟨148226, by rfl⟩ : syracuseStep 197635 = 296453) B296453
theorem B263201 : Blo 171799 263201 := bstep (se 2 (by rfl) ⟨98700, by rfl⟩ : syracuseStep 263201 = 197401) B197401
theorem B394289 : Blo 171799 394289 := bstep (se 2 (by rfl) ⟨147858, by rfl⟩ : syracuseStep 394289 = 295717) B295717
theorem B295987 : Blo 171799 295987 := bstep (se 1 (by rfl) ⟨221990, by rfl⟩ : syracuseStep 295987 = 443981) B443981
theorem B263219 : Blo 171799 263219 := bstep (se 1 (by rfl) ⟨197414, by rfl⟩ : syracuseStep 263219 = 394829) B394829
theorem B394307 : Blo 171799 394307 := bstep (se 1 (by rfl) ⟨295730, by rfl⟩ : syracuseStep 394307 = 591461) B591461
theorem B263249 : Blo 171799 263249 := bstep (se 2 (by rfl) ⟨98718, by rfl⟩ : syracuseStep 263249 = 197437) B197437
theorem B263267 : Blo 171799 263267 := bstep (se 1 (by rfl) ⟨197450, by rfl⟩ : syracuseStep 263267 = 394901) B394901
theorem B525425 : Blo 171799 525425 := bstep (se 2 (by rfl) ⟨197034, by rfl⟩ : syracuseStep 525425 = 394069) B394069
theorem B263297 : Blo 171799 263297 := bstep (se 2 (by rfl) ⟨98736, by rfl⟩ : syracuseStep 263297 = 197473) B197473
theorem B656525 : Blo 171799 656525 := bstep (se 3 (by rfl) ⟨123098, by rfl⟩ : syracuseStep 656525 = 246197) B246197
theorem B263315 : Blo 171799 263315 := bstep (se 1 (by rfl) ⟨197486, by rfl⟩ : syracuseStep 263315 = 394973) B394973
theorem B263345 : Blo 171799 263345 := bstep (se 2 (by rfl) ⟨98754, by rfl⟩ : syracuseStep 263345 = 197509) B197509
theorem B296129 : Blo 171799 296129 := bstep (se 2 (by rfl) ⟨111048, by rfl⟩ : syracuseStep 296129 = 222097) B222097
theorem B263363 : Blo 171799 263363 := bstep (se 1 (by rfl) ⟨197522, by rfl⟩ : syracuseStep 263363 = 395045) B395045
theorem B263393 : Blo 171799 263393 := bstep (se 2 (by rfl) ⟨98772, by rfl⟩ : syracuseStep 263393 = 197545) B197545
theorem B328931 : Blo 171799 328931 := bstep (se 1 (by rfl) ⟨246698, by rfl⟩ : syracuseStep 328931 = 493397) B493397
theorem B263411 : Blo 171799 263411 := bstep (se 1 (by rfl) ⟨197558, by rfl⟩ : syracuseStep 263411 = 395117) B395117
theorem B558353 : Blo 171799 558353 := bstep (se 2 (by rfl) ⟨209382, by rfl⟩ : syracuseStep 558353 = 418765) B418765
theorem B263441 : Blo 171799 263441 := bstep (se 2 (by rfl) ⟨98790, by rfl⟩ : syracuseStep 263441 = 197581) B197581
theorem B263459 : Blo 171799 263459 := bstep (se 1 (by rfl) ⟨197594, by rfl⟩ : syracuseStep 263459 = 395189) B395189
theorem B296257 : Blo 171799 296257 := bstep (se 2 (by rfl) ⟨111096, by rfl⟩ : syracuseStep 296257 = 222193) B222193
theorem B263489 : Blo 171799 263489 := bstep (se 2 (by rfl) ⟨98808, by rfl⟩ : syracuseStep 263489 = 197617) B197617
theorem B394577 : Blo 171799 394577 := bstep (se 2 (by rfl) ⟨147966, by rfl⟩ : syracuseStep 394577 = 295933) B295933
theorem B263507 : Blo 171799 263507 := bstep (se 1 (by rfl) ⟨197630, by rfl⟩ : syracuseStep 263507 = 395261) B395261
theorem B394595 : Blo 171799 394595 := bstep (se 1 (by rfl) ⟨295946, by rfl⟩ : syracuseStep 394595 = 591893) B591893
theorem B296291 : Blo 171799 296291 := bstep (se 1 (by rfl) ⟨222218, by rfl⟩ : syracuseStep 296291 = 444437) B444437
theorem B263537 : Blo 171799 263537 := bstep (se 2 (by rfl) ⟨98826, by rfl⟩ : syracuseStep 263537 = 197653) B197653
theorem B263555 : Blo 171799 263555 := bstep (se 1 (by rfl) ⟨197666, by rfl⟩ : syracuseStep 263555 = 395333) B395333
theorem B492941 : Blo 171799 492941 := bstep (se 3 (by rfl) ⟨92426, by rfl⟩ : syracuseStep 492941 = 184853) B184853
theorem B591245 : Blo 171799 591245 := bstep (se 3 (by rfl) ⟨110858, by rfl⟩ : syracuseStep 591245 = 221717) B221717
theorem B263585 : Blo 171799 263585 := bstep (se 2 (by rfl) ⟨98844, by rfl⟩ : syracuseStep 263585 = 197689) B197689
theorem B263603 : Blo 171799 263603 := bstep (se 1 (by rfl) ⟨197702, by rfl⟩ : syracuseStep 263603 = 395405) B395405
theorem B591299 : Blo 171799 591299 := bstep (se 1 (by rfl) ⟨443474, by rfl⟩ : syracuseStep 591299 = 886949) B886949
theorem B263633 : Blo 171799 263633 := bstep (se 2 (by rfl) ⟨98862, by rfl⟩ : syracuseStep 263633 = 197725) B197725
theorem B296419 : Blo 171799 296419 := bstep (se 1 (by rfl) ⟨222314, by rfl⟩ : syracuseStep 296419 = 444629) B444629
theorem B263651 : Blo 171799 263651 := bstep (se 1 (by rfl) ⟨197738, by rfl⟩ : syracuseStep 263651 = 395477) B395477
theorem B263681 : Blo 171799 263681 := bstep (se 2 (by rfl) ⟨98880, by rfl⟩ : syracuseStep 263681 = 197761) B197761
theorem B263699 : Blo 171799 263699 := bstep (se 1 (by rfl) ⟨197774, by rfl⟩ : syracuseStep 263699 = 395549) B395549
theorem B493123 : Blo 171799 493123 := bstep (se 1 (by rfl) ⟨369842, by rfl⟩ : syracuseStep 493123 = 739685) B739685
theorem B394865 : Blo 171799 394865 := bstep (se 2 (by rfl) ⟨148074, by rfl⟩ : syracuseStep 394865 = 296149) B296149
theorem B296561 : Blo 171799 296561 := bstep (se 2 (by rfl) ⟨111210, by rfl⟩ : syracuseStep 296561 = 222421) B222421
theorem B394883 : Blo 171799 394883 := bstep (se 1 (by rfl) ⟨296162, by rfl⟩ : syracuseStep 394883 = 592325) B592325
theorem B591569 : Blo 171799 591569 := bstep (se 2 (by rfl) ⟨221838, by rfl⟩ : syracuseStep 591569 = 443677) B443677
theorem B493283 : Blo 171799 493283 := bstep (se 1 (by rfl) ⟨369962, by rfl⟩ : syracuseStep 493283 = 739925) B739925
theorem B395153 : Blo 171799 395153 := bstep (se 2 (by rfl) ⟨148182, by rfl⟩ : syracuseStep 395153 = 296365) B296365
theorem B395171 : Blo 171799 395171 := bstep (se 1 (by rfl) ⟨296378, by rfl⟩ : syracuseStep 395171 = 592757) B592757
theorem B329827 : Blo 171799 329827 := bstep (se 1 (by rfl) ⟨247370, by rfl⟩ : syracuseStep 329827 = 494741) B494741
theorem B2001037 : Blo 171799 2001037 := bstep (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) B750389
theorem B395441 : Blo 171799 395441 := bstep (se 2 (by rfl) ⟨148290, by rfl⟩ : syracuseStep 395441 = 296581) B296581
theorem B395459 : Blo 171799 395459 := bstep (se 1 (by rfl) ⟨296594, by rfl⟩ : syracuseStep 395459 = 593189) B593189
theorem B592109 : Blo 171799 592109 := bstep (se 3 (by rfl) ⟨111020, by rfl⟩ : syracuseStep 592109 = 222041) B222041
theorem B329987 : Blo 171799 329987 := bstep (se 1 (by rfl) ⟨247490, by rfl⟩ : syracuseStep 329987 = 494981) B494981
theorem B592163 : Blo 171799 592163 := bstep (se 1 (by rfl) ⟨444122, by rfl⟩ : syracuseStep 592163 = 888245) B888245
theorem B592433 : Blo 171799 592433 := bstep (se 2 (by rfl) ⟨222162, by rfl⟩ : syracuseStep 592433 = 444325) B444325
theorem B395857 : Blo 171799 395857 := bstep (se 2 (by rfl) ⟨148446, by rfl⟩ : syracuseStep 395857 = 296893) B296893
theorem B494353 : Blo 171799 494353 := bstep (se 2 (by rfl) ⟨185382, by rfl⟩ : syracuseStep 494353 = 370765) B370765
theorem B199507 : Blo 171799 199507 := bstep (se 1 (by rfl) ⟨149630, by rfl⟩ : syracuseStep 199507 = 299261) B299261
theorem B592973 : Blo 171799 592973 := bstep (se 3 (by rfl) ⟨111182, by rfl⟩ : syracuseStep 592973 = 222365) B222365
theorem B887921 : Blo 171799 887921 := bstep (se 2 (by rfl) ⟨332970, by rfl⟩ : syracuseStep 887921 = 665941) B665941
theorem B593027 : Blo 171799 593027 := bstep (se 1 (by rfl) ⟨444770, by rfl⟩ : syracuseStep 593027 = 889541) B889541
theorem B658637 : Blo 171799 658637 := bstep (se 3 (by rfl) ⟨123494, by rfl⟩ : syracuseStep 658637 = 246989) B246989
theorem B265427 : Blo 171799 265427 := bstep (se 1 (by rfl) ⟨199070, by rfl⟩ : syracuseStep 265427 = 398141) B398141
theorem B4754659 : Blo 171799 4754659 := bstep (se 1 (by rfl) ⟨3565994, by rfl⟩ : syracuseStep 4754659 = 7131989) B7131989
theorem B1576205 : Blo 171799 1576205 := bstep (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) B591077
theorem B1117475 : Blo 171799 1117475 := bstep (se 1 (by rfl) ⟨838106, by rfl⟩ : syracuseStep 1117475 = 1676213) B1676213
theorem B331057 : Blo 171799 331057 := bstep (se 2 (by rfl) ⟨124146, by rfl⟩ : syracuseStep 331057 = 248293) B248293
theorem B593297 : Blo 171799 593297 := bstep (se 2 (by rfl) ⟨222486, by rfl⟩ : syracuseStep 593297 = 444973) B444973
theorem B232993 : Blo 171799 232993 := bstep (se 2 (by rfl) ⟨87372, by rfl⟩ : syracuseStep 232993 = 174745) B174745
theorem B986701 : Blo 171799 986701 := bstep (se 3 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 986701 = 370013) B370013
theorem B233155 : Blo 171799 233155 := bstep (se 1 (by rfl) ⟨174866, by rfl⟩ : syracuseStep 233155 = 349733) B349733
theorem B626417 : Blo 171799 626417 := bstep (se 2 (by rfl) ⟨234906, by rfl⟩ : syracuseStep 626417 = 469813) B469813
theorem B593677 : Blo 171799 593677 := bstep (se 3 (by rfl) ⟨111314, by rfl⟩ : syracuseStep 593677 = 222629) B222629
theorem B1314629 : Blo 171799 1314629 := bstep (se 4 (by rfl) ⟨123246, by rfl⟩ : syracuseStep 1314629 = 246493) B246493
theorem B659441 : Blo 171799 659441 := bstep (se 2 (by rfl) ⟨247290, by rfl⟩ : syracuseStep 659441 = 494581) B494581
theorem B495629 : Blo 171799 495629 := bstep (se 3 (by rfl) ⟨92930, by rfl⟩ : syracuseStep 495629 = 185861) B185861
theorem B1675363 : Blo 171799 1675363 := bstep (se 1 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 1675363 = 2513045) B2513045
theorem B561325 : Blo 171799 561325 := bstep (se 3 (by rfl) ⟨105248, by rfl⟩ : syracuseStep 561325 = 210497) B210497
theorem B495811 : Blo 171799 495811 := bstep (se 1 (by rfl) ⟨371858, by rfl⟩ : syracuseStep 495811 = 743717) B743717
theorem B495857 : Blo 171799 495857 := bstep (se 2 (by rfl) ⟨185946, by rfl⟩ : syracuseStep 495857 = 371893) B371893
theorem B233761 : Blo 171799 233761 := bstep (se 2 (by rfl) ⟨87660, by rfl⟩ : syracuseStep 233761 = 175321) B175321
theorem B332113 : Blo 171799 332113 := bstep (se 2 (by rfl) ⟨124542, by rfl⟩ : syracuseStep 332113 = 249085) B249085
theorem B561581 : Blo 171799 561581 := bstep (se 3 (by rfl) ⟨105296, by rfl⟩ : syracuseStep 561581 = 210593) B210593
theorem B8556997 : Blo 171799 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B889379 : Blo 171799 889379 := bstep (se 1 (by rfl) ⟨667034, by rfl⟩ : syracuseStep 889379 = 1334069) B1334069
theorem B528977 : Blo 171799 528977 := bstep (se 2 (by rfl) ⟨198366, by rfl⟩ : syracuseStep 528977 = 396733) B396733
theorem B561763 : Blo 171799 561763 := bstep (se 1 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 561763 = 842645) B842645
theorem B1053283 : Blo 171799 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B660109 : Blo 171799 660109 := bstep (se 3 (by rfl) ⟨123770, by rfl⟩ : syracuseStep 660109 = 247541) B247541
theorem B332515 : Blo 171799 332515 := bstep (se 1 (by rfl) ⟨249386, by rfl⟩ : syracuseStep 332515 = 498773) B498773
theorem B332561 : Blo 171799 332561 := bstep (se 2 (by rfl) ⟨124710, by rfl⟩ : syracuseStep 332561 = 249421) B249421
theorem B299809 : Blo 171799 299809 := bstep (se 2 (by rfl) ⟨112428, by rfl⟩ : syracuseStep 299809 = 224857) B224857
theorem B2495285 : Blo 171799 2495285 := bstep (se 5 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 2495285 = 233933) B233933
theorem B529357 : Blo 171799 529357 := bstep (se 3 (by rfl) ⟨99254, by rfl⟩ : syracuseStep 529357 = 198509) B198509
theorem B562211 : Blo 171799 562211 := bstep (se 1 (by rfl) ⟨421658, by rfl⟩ : syracuseStep 562211 = 843317) B843317
theorem B332849 : Blo 171799 332849 := bstep (se 2 (by rfl) ⟨124818, by rfl⟩ : syracuseStep 332849 = 249637) B249637
theorem B1479779 : Blo 171799 1479779 := bstep (se 1 (by rfl) ⟨1109834, by rfl⟩ : syracuseStep 1479779 = 2219669) B2219669
theorem B628003 : Blo 171799 628003 := bstep (se 1 (by rfl) ⟨471002, by rfl⟩ : syracuseStep 628003 = 942005) B942005
theorem B496945 : Blo 171799 496945 := bstep (se 2 (by rfl) ⟨186354, by rfl⟩ : syracuseStep 496945 = 372709) B372709
theorem B267667 : Blo 171799 267667 := bstep (se 1 (by rfl) ⟨200750, by rfl⟩ : syracuseStep 267667 = 401501) B401501
theorem B660899 : Blo 171799 660899 := bstep (se 1 (by rfl) ⟨495674, by rfl⟩ : syracuseStep 660899 = 991349) B991349
theorem B1578467 : Blo 171799 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B988685 : Blo 171799 988685 := bstep (se 3 (by rfl) ⟨185378, by rfl⟩ : syracuseStep 988685 = 370757) B370757
theorem B497315 : Blo 171799 497315 := bstep (se 1 (by rfl) ⟨372986, by rfl⟩ : syracuseStep 497315 = 745973) B745973
theorem B1119971 : Blo 171799 1119971 := bstep (se 1 (by rfl) ⟨839978, by rfl⟩ : syracuseStep 1119971 = 1679957) B1679957
theorem B333571 : Blo 171799 333571 := bstep (se 1 (by rfl) ⟨250178, by rfl⟩ : syracuseStep 333571 = 500357) B500357
theorem B530275 : Blo 171799 530275 := bstep (se 1 (by rfl) ⟨397706, by rfl⟩ : syracuseStep 530275 = 795413) B795413
theorem B464753 : Blo 171799 464753 := bstep (se 2 (by rfl) ⟨174282, by rfl⟩ : syracuseStep 464753 = 348565) B348565
theorem B563107 : Blo 171799 563107 := bstep (se 1 (by rfl) ⟨422330, by rfl⟩ : syracuseStep 563107 = 844661) B844661
theorem B661553 : Blo 171799 661553 := bstep (se 2 (by rfl) ⟨248082, by rfl⟩ : syracuseStep 661553 = 496165) B496165
theorem B530563 : Blo 171799 530563 := bstep (se 1 (by rfl) ⟨397922, by rfl⟩ : syracuseStep 530563 = 795845) B795845
theorem B2398349 : Blo 171799 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B1350029 : Blo 171799 1350029 := bstep (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) B506261
theorem B989617 : Blo 171799 989617 := bstep (se 2 (by rfl) ⟨371106, by rfl⟩ : syracuseStep 989617 = 742213) B742213
theorem B596771 : Blo 171799 596771 := bstep (se 1 (by rfl) ⟨447578, by rfl⟩ : syracuseStep 596771 = 895157) B895157
theorem B367409 : Blo 171799 367409 := bstep (se 2 (by rfl) ⟨137778, by rfl⟩ : syracuseStep 367409 = 275557) B275557
theorem B498545 : Blo 171799 498545 := bstep (se 2 (by rfl) ⟨186954, by rfl⟩ : syracuseStep 498545 = 373909) B373909
theorem B269443 : Blo 171799 269443 := bstep (se 1 (by rfl) ⟨202082, by rfl⟩ : syracuseStep 269443 = 404165) B404165
theorem B1121521 : Blo 171799 1121521 := bstep (se 2 (by rfl) ⟨420570, by rfl⟩ : syracuseStep 1121521 = 841141) B841141
theorem B663011 : Blo 171799 663011 := bstep (se 1 (by rfl) ⟨497258, by rfl⟩ : syracuseStep 663011 = 994517) B994517
theorem B663025 : Blo 171799 663025 := bstep (se 2 (by rfl) ⟨248634, by rfl⟩ : syracuseStep 663025 = 497269) B497269
theorem B1121861 : Blo 171799 1121861 := bstep (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) B210349
theorem B171811 : Blo 171799 171811 := bstep (se 1 (by rfl) ⟨128858, by rfl⟩ : syracuseStep 171811 = 257717) B257717
theorem B171827 : Blo 171799 171827 := bstep (se 1 (by rfl) ⟨128870, by rfl⟩ : syracuseStep 171827 = 257741) B257741
theorem B171843 : Blo 171799 171843 := bstep (se 1 (by rfl) ⟨128882, by rfl⟩ : syracuseStep 171843 = 257765) B257765
theorem B302915 : Blo 171799 302915 := bstep (se 1 (by rfl) ⟨227186, by rfl⟩ : syracuseStep 302915 = 454373) B454373
theorem B171859 : Blo 171799 171859 := bstep (se 1 (by rfl) ⟨128894, by rfl⟩ : syracuseStep 171859 = 257789) B257789
theorem B171875 : Blo 171799 171875 := bstep (se 1 (by rfl) ⟨128906, by rfl⟩ : syracuseStep 171875 = 257813) B257813
theorem B991075 : Blo 171799 991075 := bstep (se 1 (by rfl) ⟨743306, by rfl⟩ : syracuseStep 991075 = 1486613) B1486613
theorem B171891 : Blo 171799 171891 := bstep (se 1 (by rfl) ⟨128918, by rfl⟩ : syracuseStep 171891 = 257837) B257837
theorem B171907 : Blo 171799 171907 := bstep (se 1 (by rfl) ⟨128930, by rfl⟩ : syracuseStep 171907 = 257861) B257861
theorem B466829 : Blo 171799 466829 := bstep (se 3 (by rfl) ⟨87530, by rfl⟩ : syracuseStep 466829 = 175061) B175061
theorem B171923 : Blo 171799 171923 := bstep (se 1 (by rfl) ⟨128942, by rfl⟩ : syracuseStep 171923 = 257885) B257885
theorem B171939 : Blo 171799 171939 := bstep (se 1 (by rfl) ⟨128954, by rfl⟩ : syracuseStep 171939 = 257909) B257909
theorem B171955 : Blo 171799 171955 := bstep (se 1 (by rfl) ⟨128966, by rfl⟩ : syracuseStep 171955 = 257933) B257933
theorem B171971 : Blo 171799 171971 := bstep (se 1 (by rfl) ⟨128978, by rfl⟩ : syracuseStep 171971 = 257957) B257957
theorem B532433 : Blo 171799 532433 := bstep (se 2 (by rfl) ⟨199662, by rfl⟩ : syracuseStep 532433 = 399325) B399325
theorem B171987 : Blo 171799 171987 := bstep (se 1 (by rfl) ⟨128990, by rfl⟩ : syracuseStep 171987 = 257981) B257981
theorem B172003 : Blo 171799 172003 := bstep (se 1 (by rfl) ⟨129002, by rfl⟩ : syracuseStep 172003 = 258005) B258005
theorem B172019 : Blo 171799 172019 := bstep (se 1 (by rfl) ⟨129014, by rfl⟩ : syracuseStep 172019 = 258029) B258029
theorem B172035 : Blo 171799 172035 := bstep (se 1 (by rfl) ⟨129026, by rfl⟩ : syracuseStep 172035 = 258053) B258053
theorem B172051 : Blo 171799 172051 := bstep (se 1 (by rfl) ⟨129038, by rfl⟩ : syracuseStep 172051 = 258077) B258077
theorem B172067 : Blo 171799 172067 := bstep (se 1 (by rfl) ⟨129050, by rfl⟩ : syracuseStep 172067 = 258101) B258101
theorem B172083 : Blo 171799 172083 := bstep (se 1 (by rfl) ⟨129062, by rfl⟩ : syracuseStep 172083 = 258125) B258125
theorem B172099 : Blo 171799 172099 := bstep (se 1 (by rfl) ⟨129074, by rfl⟩ : syracuseStep 172099 = 258149) B258149
theorem B368707 : Blo 171799 368707 := bstep (se 1 (by rfl) ⟨276530, by rfl⟩ : syracuseStep 368707 = 553061) B553061
theorem B172115 : Blo 171799 172115 := bstep (se 1 (by rfl) ⟨129086, by rfl⟩ : syracuseStep 172115 = 258173) B258173
theorem B172131 : Blo 171799 172131 := bstep (se 1 (by rfl) ⟨129098, by rfl⟩ : syracuseStep 172131 = 258197) B258197
theorem B598115 : Blo 171799 598115 := bstep (se 1 (by rfl) ⟨448586, by rfl⟩ : syracuseStep 598115 = 897173) B897173
theorem B172147 : Blo 171799 172147 := bstep (se 1 (by rfl) ⟨129110, by rfl⟩ : syracuseStep 172147 = 258221) B258221
theorem B172163 : Blo 171799 172163 := bstep (se 1 (by rfl) ⟨129122, by rfl⟩ : syracuseStep 172163 = 258245) B258245
theorem B172179 : Blo 171799 172179 := bstep (se 1 (by rfl) ⟨129134, by rfl⟩ : syracuseStep 172179 = 258269) B258269
theorem B172195 : Blo 171799 172195 := bstep (se 1 (by rfl) ⟨129146, by rfl⟩ : syracuseStep 172195 = 258293) B258293
theorem B172211 : Blo 171799 172211 := bstep (se 1 (by rfl) ⟨129158, by rfl⟩ : syracuseStep 172211 = 258317) B258317
theorem B172227 : Blo 171799 172227 := bstep (se 1 (by rfl) ⟨129170, by rfl⟩ : syracuseStep 172227 = 258341) B258341
theorem B172243 : Blo 171799 172243 := bstep (se 1 (by rfl) ⟨129182, by rfl⟩ : syracuseStep 172243 = 258365) B258365
theorem B172259 : Blo 171799 172259 := bstep (se 1 (by rfl) ⟨129194, by rfl⟩ : syracuseStep 172259 = 258389) B258389
theorem B172275 : Blo 171799 172275 := bstep (se 1 (by rfl) ⟨129206, by rfl⟩ : syracuseStep 172275 = 258413) B258413
theorem B172291 : Blo 171799 172291 := bstep (se 1 (by rfl) ⟨129218, by rfl⟩ : syracuseStep 172291 = 258437) B258437
theorem B172307 : Blo 171799 172307 := bstep (se 1 (by rfl) ⟨129230, by rfl⟩ : syracuseStep 172307 = 258461) B258461
theorem B172323 : Blo 171799 172323 := bstep (se 1 (by rfl) ⟨129242, by rfl⟩ : syracuseStep 172323 = 258485) B258485
theorem B500003 : Blo 171799 500003 := bstep (se 1 (by rfl) ⟨375002, by rfl⟩ : syracuseStep 500003 = 750005) B750005
theorem B172339 : Blo 171799 172339 := bstep (se 1 (by rfl) ⟨129254, by rfl⟩ : syracuseStep 172339 = 258509) B258509
theorem B172355 : Blo 171799 172355 := bstep (se 1 (by rfl) ⟨129266, by rfl⟩ : syracuseStep 172355 = 258533) B258533
theorem B172371 : Blo 171799 172371 := bstep (se 1 (by rfl) ⟨129278, by rfl⟩ : syracuseStep 172371 = 258557) B258557
theorem B172387 : Blo 171799 172387 := bstep (se 1 (by rfl) ⟨129290, by rfl⟩ : syracuseStep 172387 = 258581) B258581
theorem B1188209 : Blo 171799 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B991601 : Blo 171799 991601 := bstep (se 2 (by rfl) ⟨371850, by rfl⟩ : syracuseStep 991601 = 743701) B743701
theorem B172403 : Blo 171799 172403 := bstep (se 1 (by rfl) ⟨129302, by rfl⟩ : syracuseStep 172403 = 258605) B258605
theorem B172419 : Blo 171799 172419 := bstep (se 1 (by rfl) ⟨129314, by rfl⟩ : syracuseStep 172419 = 258629) B258629
theorem B172435 : Blo 171799 172435 := bstep (se 1 (by rfl) ⟨129326, by rfl⟩ : syracuseStep 172435 = 258653) B258653
theorem B172451 : Blo 171799 172451 := bstep (se 1 (by rfl) ⟨129338, by rfl⟩ : syracuseStep 172451 = 258677) B258677
theorem B172467 : Blo 171799 172467 := bstep (se 1 (by rfl) ⟨129350, by rfl⟩ : syracuseStep 172467 = 258701) B258701
theorem B172483 : Blo 171799 172483 := bstep (se 1 (by rfl) ⟨129362, by rfl⟩ : syracuseStep 172483 = 258725) B258725
theorem B172499 : Blo 171799 172499 := bstep (se 1 (by rfl) ⟨129374, by rfl⟩ : syracuseStep 172499 = 258749) B258749
theorem B172515 : Blo 171799 172515 := bstep (se 1 (by rfl) ⟨129386, by rfl⟩ : syracuseStep 172515 = 258773) B258773
theorem B172531 : Blo 171799 172531 := bstep (se 1 (by rfl) ⟨129398, by rfl⟩ : syracuseStep 172531 = 258797) B258797
theorem B172547 : Blo 171799 172547 := bstep (se 1 (by rfl) ⟨129410, by rfl⟩ : syracuseStep 172547 = 258821) B258821
theorem B172563 : Blo 171799 172563 := bstep (se 1 (by rfl) ⟨129422, by rfl⟩ : syracuseStep 172563 = 258845) B258845
theorem B172579 : Blo 171799 172579 := bstep (se 1 (by rfl) ⟨129434, by rfl⟩ : syracuseStep 172579 = 258869) B258869
theorem B172595 : Blo 171799 172595 := bstep (se 1 (by rfl) ⟨129446, by rfl⟩ : syracuseStep 172595 = 258893) B258893
theorem B172611 : Blo 171799 172611 := bstep (se 1 (by rfl) ⟨129458, by rfl⟩ : syracuseStep 172611 = 258917) B258917
theorem B172627 : Blo 171799 172627 := bstep (se 1 (by rfl) ⟨129470, by rfl⟩ : syracuseStep 172627 = 258941) B258941
theorem B172643 : Blo 171799 172643 := bstep (se 1 (by rfl) ⟨129482, by rfl⟩ : syracuseStep 172643 = 258965) B258965
theorem B172659 : Blo 171799 172659 := bstep (se 1 (by rfl) ⟨129494, by rfl⟩ : syracuseStep 172659 = 258989) B258989
theorem B172675 : Blo 171799 172675 := bstep (se 1 (by rfl) ⟨129506, by rfl⟩ : syracuseStep 172675 = 259013) B259013
theorem B172691 : Blo 171799 172691 := bstep (se 1 (by rfl) ⟨129518, by rfl⟩ : syracuseStep 172691 = 259037) B259037
theorem B172707 : Blo 171799 172707 := bstep (se 1 (by rfl) ⟨129530, by rfl⟩ : syracuseStep 172707 = 259061) B259061
theorem B172723 : Blo 171799 172723 := bstep (se 1 (by rfl) ⟨129542, by rfl⟩ : syracuseStep 172723 = 259085) B259085
theorem B172739 : Blo 171799 172739 := bstep (se 1 (by rfl) ⟨129554, by rfl⟩ : syracuseStep 172739 = 259109) B259109
theorem B172755 : Blo 171799 172755 := bstep (se 1 (by rfl) ⟨129566, by rfl⟩ : syracuseStep 172755 = 259133) B259133
theorem B172771 : Blo 171799 172771 := bstep (se 1 (by rfl) ⟨129578, by rfl⟩ : syracuseStep 172771 = 259157) B259157
theorem B434929 : Blo 171799 434929 := bstep (se 2 (by rfl) ⟨163098, by rfl⟩ : syracuseStep 434929 = 326197) B326197
theorem B172787 : Blo 171799 172787 := bstep (se 1 (by rfl) ⟨129590, by rfl⟩ : syracuseStep 172787 = 259181) B259181
theorem B172803 : Blo 171799 172803 := bstep (se 1 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 172803 = 259205) B259205
theorem B172819 : Blo 171799 172819 := bstep (se 1 (by rfl) ⟨129614, by rfl⟩ : syracuseStep 172819 = 259229) B259229
theorem B172835 : Blo 171799 172835 := bstep (se 1 (by rfl) ⟨129626, by rfl⟩ : syracuseStep 172835 = 259253) B259253
theorem B172851 : Blo 171799 172851 := bstep (se 1 (by rfl) ⟨129638, by rfl⟩ : syracuseStep 172851 = 259277) B259277
theorem B172867 : Blo 171799 172867 := bstep (se 1 (by rfl) ⟨129650, by rfl⟩ : syracuseStep 172867 = 259301) B259301
theorem B467779 : Blo 171799 467779 := bstep (se 1 (by rfl) ⟨350834, by rfl⟩ : syracuseStep 467779 = 701669) B701669
theorem B172883 : Blo 171799 172883 := bstep (se 1 (by rfl) ⟨129662, by rfl⟩ : syracuseStep 172883 = 259325) B259325
theorem B172899 : Blo 171799 172899 := bstep (se 1 (by rfl) ⟨129674, by rfl⟩ : syracuseStep 172899 = 259349) B259349
theorem B631651 : Blo 171799 631651 := bstep (se 1 (by rfl) ⟨473738, by rfl⟩ : syracuseStep 631651 = 947477) B947477
theorem B566129 : Blo 171799 566129 := bstep (se 2 (by rfl) ⟨212298, by rfl⟩ : syracuseStep 566129 = 424597) B424597
theorem B172915 : Blo 171799 172915 := bstep (se 1 (by rfl) ⟨129686, by rfl⟩ : syracuseStep 172915 = 259373) B259373
theorem B172931 : Blo 171799 172931 := bstep (se 1 (by rfl) ⟨129698, by rfl⟩ : syracuseStep 172931 = 259397) B259397
theorem B172947 : Blo 171799 172947 := bstep (se 1 (by rfl) ⟨129710, by rfl⟩ : syracuseStep 172947 = 259421) B259421
theorem B172963 : Blo 171799 172963 := bstep (se 1 (by rfl) ⟨129722, by rfl⟩ : syracuseStep 172963 = 259445) B259445
theorem B664483 : Blo 171799 664483 := bstep (se 1 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 664483 = 996725) B996725
theorem B172979 : Blo 171799 172979 := bstep (se 1 (by rfl) ⟨129734, by rfl⟩ : syracuseStep 172979 = 259469) B259469
theorem B172995 : Blo 171799 172995 := bstep (se 1 (by rfl) ⟨129746, by rfl⟩ : syracuseStep 172995 = 259493) B259493
theorem B173011 : Blo 171799 173011 := bstep (se 1 (by rfl) ⟨129758, by rfl⟩ : syracuseStep 173011 = 259517) B259517
theorem B173027 : Blo 171799 173027 := bstep (se 1 (by rfl) ⟨129770, by rfl⟩ : syracuseStep 173027 = 259541) B259541
theorem B173043 : Blo 171799 173043 := bstep (se 1 (by rfl) ⟨129782, by rfl⟩ : syracuseStep 173043 = 259565) B259565
theorem B435203 : Blo 171799 435203 := bstep (se 1 (by rfl) ⟨326402, by rfl⟩ : syracuseStep 435203 = 652805) B652805
theorem B173059 : Blo 171799 173059 := bstep (se 1 (by rfl) ⟨129794, by rfl⟩ : syracuseStep 173059 = 259589) B259589
theorem B173075 : Blo 171799 173075 := bstep (se 1 (by rfl) ⟨129806, by rfl⟩ : syracuseStep 173075 = 259613) B259613
theorem B173091 : Blo 171799 173091 := bstep (se 1 (by rfl) ⟨129818, by rfl⟩ : syracuseStep 173091 = 259637) B259637
theorem B304163 : Blo 171799 304163 := bstep (se 1 (by rfl) ⟨228122, by rfl⟩ : syracuseStep 304163 = 456245) B456245
theorem B173107 : Blo 171799 173107 := bstep (se 1 (by rfl) ⟨129830, by rfl⟩ : syracuseStep 173107 = 259661) B259661
theorem B173123 : Blo 171799 173123 := bstep (se 1 (by rfl) ⟨129842, by rfl⟩ : syracuseStep 173123 = 259685) B259685
theorem B173139 : Blo 171799 173139 := bstep (se 1 (by rfl) ⟨129854, by rfl⟩ : syracuseStep 173139 = 259709) B259709
theorem B173155 : Blo 171799 173155 := bstep (se 1 (by rfl) ⟨129866, by rfl⟩ : syracuseStep 173155 = 259733) B259733
theorem B173171 : Blo 171799 173171 := bstep (se 1 (by rfl) ⟨129878, by rfl⟩ : syracuseStep 173171 = 259757) B259757
theorem B173187 : Blo 171799 173187 := bstep (se 1 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 173187 = 259781) B259781
theorem B173203 : Blo 171799 173203 := bstep (se 1 (by rfl) ⟨129902, by rfl⟩ : syracuseStep 173203 = 259805) B259805
theorem B173219 : Blo 171799 173219 := bstep (se 1 (by rfl) ⟨129914, by rfl⟩ : syracuseStep 173219 = 259829) B259829
theorem B173235 : Blo 171799 173235 := bstep (se 1 (by rfl) ⟨129926, by rfl⟩ : syracuseStep 173235 = 259853) B259853
theorem B435395 : Blo 171799 435395 := bstep (se 1 (by rfl) ⟨326546, by rfl⟩ : syracuseStep 435395 = 653093) B653093
theorem B173251 : Blo 171799 173251 := bstep (se 1 (by rfl) ⟨129938, by rfl⟩ : syracuseStep 173251 = 259877) B259877
theorem B173267 : Blo 171799 173267 := bstep (se 1 (by rfl) ⟨129950, by rfl⟩ : syracuseStep 173267 = 259901) B259901
theorem B173283 : Blo 171799 173283 := bstep (se 1 (by rfl) ⟨129962, by rfl⟩ : syracuseStep 173283 = 259925) B259925
theorem B173299 : Blo 171799 173299 := bstep (se 1 (by rfl) ⟨129974, by rfl⟩ : syracuseStep 173299 = 259949) B259949
theorem B173315 : Blo 171799 173315 := bstep (se 1 (by rfl) ⟨129986, by rfl⟩ : syracuseStep 173315 = 259973) B259973
theorem B369937 : Blo 171799 369937 := bstep (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) B277453
theorem B173331 : Blo 171799 173331 := bstep (se 1 (by rfl) ⟨129998, by rfl⟩ : syracuseStep 173331 = 259997) B259997
theorem B173347 : Blo 171799 173347 := bstep (se 1 (by rfl) ⟨130010, by rfl⟩ : syracuseStep 173347 = 260021) B260021
theorem B173363 : Blo 171799 173363 := bstep (se 1 (by rfl) ⟨130022, by rfl⟩ : syracuseStep 173363 = 260045) B260045
theorem B173379 : Blo 171799 173379 := bstep (se 1 (by rfl) ⟨130034, by rfl⟩ : syracuseStep 173379 = 260069) B260069
theorem B1680709 : Blo 171799 1680709 := bstep (se 4 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 1680709 = 315133) B315133
theorem B173395 : Blo 171799 173395 := bstep (se 1 (by rfl) ⟨130046, by rfl⟩ : syracuseStep 173395 = 260093) B260093
theorem B173411 : Blo 171799 173411 := bstep (se 1 (by rfl) ⟨130058, by rfl⟩ : syracuseStep 173411 = 260117) B260117
theorem B173427 : Blo 171799 173427 := bstep (se 1 (by rfl) ⟨130070, by rfl⟩ : syracuseStep 173427 = 260141) B260141
theorem B173443 : Blo 171799 173443 := bstep (se 1 (by rfl) ⟨130082, by rfl⟩ : syracuseStep 173443 = 260165) B260165
theorem B173459 : Blo 171799 173459 := bstep (se 1 (by rfl) ⟨130094, by rfl⟩ : syracuseStep 173459 = 260189) B260189
theorem B173475 : Blo 171799 173475 := bstep (se 1 (by rfl) ⟨130106, by rfl⟩ : syracuseStep 173475 = 260213) B260213
theorem B173491 : Blo 171799 173491 := bstep (se 1 (by rfl) ⟨130118, by rfl⟩ : syracuseStep 173491 = 260237) B260237
theorem B173507 : Blo 171799 173507 := bstep (se 1 (by rfl) ⟨130130, by rfl⟩ : syracuseStep 173507 = 260261) B260261
theorem B173523 : Blo 171799 173523 := bstep (se 1 (by rfl) ⟨130142, by rfl⟩ : syracuseStep 173523 = 260285) B260285
theorem B173539 : Blo 171799 173539 := bstep (se 1 (by rfl) ⟨130154, by rfl⟩ : syracuseStep 173539 = 260309) B260309
theorem B173555 : Blo 171799 173555 := bstep (se 1 (by rfl) ⟨130166, by rfl⟩ : syracuseStep 173555 = 260333) B260333
theorem B173571 : Blo 171799 173571 := bstep (se 1 (by rfl) ⟨130178, by rfl⟩ : syracuseStep 173571 = 260357) B260357
theorem B1320461 : Blo 171799 1320461 := bstep (se 3 (by rfl) ⟨247586, by rfl⟩ : syracuseStep 1320461 = 495173) B495173
theorem B173587 : Blo 171799 173587 := bstep (se 1 (by rfl) ⟨130190, by rfl⟩ : syracuseStep 173587 = 260381) B260381
theorem B173603 : Blo 171799 173603 := bstep (se 1 (by rfl) ⟨130202, by rfl⟩ : syracuseStep 173603 = 260405) B260405
theorem B173619 : Blo 171799 173619 := bstep (se 1 (by rfl) ⟨130214, by rfl⟩ : syracuseStep 173619 = 260429) B260429
theorem B173635 : Blo 171799 173635 := bstep (se 1 (by rfl) ⟨130226, by rfl⟩ : syracuseStep 173635 = 260453) B260453
theorem B173651 : Blo 171799 173651 := bstep (se 1 (by rfl) ⟨130238, by rfl⟩ : syracuseStep 173651 = 260477) B260477
theorem B173667 : Blo 171799 173667 := bstep (se 1 (by rfl) ⟨130250, by rfl⟩ : syracuseStep 173667 = 260501) B260501
theorem B173683 : Blo 171799 173683 := bstep (se 1 (by rfl) ⟨130262, by rfl⟩ : syracuseStep 173683 = 260525) B260525
theorem B173699 : Blo 171799 173699 := bstep (se 1 (by rfl) ⟨130274, by rfl⟩ : syracuseStep 173699 = 260549) B260549
theorem B173715 : Blo 171799 173715 := bstep (se 1 (by rfl) ⟨130286, by rfl⟩ : syracuseStep 173715 = 260573) B260573
theorem B173731 : Blo 171799 173731 := bstep (se 1 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 173731 = 260597) B260597
theorem B566957 : Blo 171799 566957 := bstep (se 3 (by rfl) ⟨106304, by rfl⟩ : syracuseStep 566957 = 212609) B212609
theorem B173747 : Blo 171799 173747 := bstep (se 1 (by rfl) ⟨130310, by rfl⟩ : syracuseStep 173747 = 260621) B260621
theorem B173763 : Blo 171799 173763 := bstep (se 1 (by rfl) ⟨130322, by rfl⟩ : syracuseStep 173763 = 260645) B260645
theorem B173779 : Blo 171799 173779 := bstep (se 1 (by rfl) ⟨130334, by rfl⟩ : syracuseStep 173779 = 260669) B260669
theorem B173795 : Blo 171799 173795 := bstep (se 1 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 173795 = 260693) B260693
theorem B173811 : Blo 171799 173811 := bstep (se 1 (by rfl) ⟨130358, by rfl⟩ : syracuseStep 173811 = 260717) B260717
theorem B173827 : Blo 171799 173827 := bstep (se 1 (by rfl) ⟨130370, by rfl⟩ : syracuseStep 173827 = 260741) B260741
theorem B173843 : Blo 171799 173843 := bstep (se 1 (by rfl) ⟨130382, by rfl⟩ : syracuseStep 173843 = 260765) B260765
theorem B173859 : Blo 171799 173859 := bstep (se 1 (by rfl) ⟨130394, by rfl⟩ : syracuseStep 173859 = 260789) B260789
theorem B993059 : Blo 171799 993059 := bstep (se 1 (by rfl) ⟨744794, by rfl⟩ : syracuseStep 993059 = 1489589) B1489589
theorem B173875 : Blo 171799 173875 := bstep (se 1 (by rfl) ⟨130406, by rfl⟩ : syracuseStep 173875 = 260813) B260813
theorem B173891 : Blo 171799 173891 := bstep (se 1 (by rfl) ⟨130418, by rfl⟩ : syracuseStep 173891 = 260837) B260837
theorem B173907 : Blo 171799 173907 := bstep (se 1 (by rfl) ⟨130430, by rfl⟩ : syracuseStep 173907 = 260861) B260861
theorem B173923 : Blo 171799 173923 := bstep (se 1 (by rfl) ⟨130442, by rfl⟩ : syracuseStep 173923 = 260885) B260885
theorem B239473 : Blo 171799 239473 := bstep (se 2 (by rfl) ⟨89802, by rfl⟩ : syracuseStep 239473 = 179605) B179605
theorem B173939 : Blo 171799 173939 := bstep (se 1 (by rfl) ⟨130454, by rfl⟩ : syracuseStep 173939 = 260909) B260909
theorem B173955 : Blo 171799 173955 := bstep (se 1 (by rfl) ⟨130466, by rfl⟩ : syracuseStep 173955 = 260933) B260933
theorem B173971 : Blo 171799 173971 := bstep (se 1 (by rfl) ⟨130478, by rfl⟩ : syracuseStep 173971 = 260957) B260957
theorem B370595 : Blo 171799 370595 := bstep (se 1 (by rfl) ⟨277946, by rfl⟩ : syracuseStep 370595 = 555893) B555893
theorem B173987 : Blo 171799 173987 := bstep (se 1 (by rfl) ⟨130490, by rfl⟩ : syracuseStep 173987 = 260981) B260981
theorem B174003 : Blo 171799 174003 := bstep (se 1 (by rfl) ⟨130502, by rfl⟩ : syracuseStep 174003 = 261005) B261005
theorem B174019 : Blo 171799 174019 := bstep (se 1 (by rfl) ⟨130514, by rfl⟩ : syracuseStep 174019 = 261029) B261029
theorem B174035 : Blo 171799 174035 := bstep (se 1 (by rfl) ⟨130526, by rfl⟩ : syracuseStep 174035 = 261053) B261053
theorem B174051 : Blo 171799 174051 := bstep (se 1 (by rfl) ⟨130538, by rfl⟩ : syracuseStep 174051 = 261077) B261077
theorem B174067 : Blo 171799 174067 := bstep (se 1 (by rfl) ⟨130550, by rfl⟩ : syracuseStep 174067 = 261101) B261101
theorem B174083 : Blo 171799 174083 := bstep (se 1 (by rfl) ⟨130562, by rfl⟩ : syracuseStep 174083 = 261125) B261125
theorem B174099 : Blo 171799 174099 := bstep (se 1 (by rfl) ⟨130574, by rfl⟩ : syracuseStep 174099 = 261149) B261149
theorem B174115 : Blo 171799 174115 := bstep (se 1 (by rfl) ⟨130586, by rfl⟩ : syracuseStep 174115 = 261173) B261173
theorem B174131 : Blo 171799 174131 := bstep (se 1 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 174131 = 261197) B261197
theorem B174147 : Blo 171799 174147 := bstep (se 1 (by rfl) ⟨130610, by rfl⟩ : syracuseStep 174147 = 261221) B261221
theorem B174163 : Blo 171799 174163 := bstep (se 1 (by rfl) ⟨130622, by rfl⟩ : syracuseStep 174163 = 261245) B261245
theorem B174179 : Blo 171799 174179 := bstep (se 1 (by rfl) ⟨130634, by rfl⟩ : syracuseStep 174179 = 261269) B261269
theorem B436337 : Blo 171799 436337 := bstep (se 2 (by rfl) ⟨163626, by rfl⟩ : syracuseStep 436337 = 327253) B327253
theorem B174195 : Blo 171799 174195 := bstep (se 1 (by rfl) ⟨130646, by rfl⟩ : syracuseStep 174195 = 261293) B261293
theorem B174211 : Blo 171799 174211 := bstep (se 1 (by rfl) ⟨130658, by rfl⟩ : syracuseStep 174211 = 261317) B261317
theorem B174227 : Blo 171799 174227 := bstep (se 1 (by rfl) ⟨130670, by rfl⟩ : syracuseStep 174227 = 261341) B261341
theorem B436387 : Blo 171799 436387 := bstep (se 1 (by rfl) ⟨327290, by rfl⟩ : syracuseStep 436387 = 654581) B654581
theorem B174243 : Blo 171799 174243 := bstep (se 1 (by rfl) ⟨130682, by rfl⟩ : syracuseStep 174243 = 261365) B261365
theorem B174259 : Blo 171799 174259 := bstep (se 1 (by rfl) ⟨130694, by rfl⟩ : syracuseStep 174259 = 261389) B261389
theorem B174275 : Blo 171799 174275 := bstep (se 1 (by rfl) ⟨130706, by rfl⟩ : syracuseStep 174275 = 261413) B261413
theorem B174291 : Blo 171799 174291 := bstep (se 1 (by rfl) ⟨130718, by rfl⟩ : syracuseStep 174291 = 261437) B261437
theorem B174307 : Blo 171799 174307 := bstep (se 1 (by rfl) ⟨130730, by rfl⟩ : syracuseStep 174307 = 261461) B261461
theorem B174323 : Blo 171799 174323 := bstep (se 1 (by rfl) ⟨130742, by rfl⟩ : syracuseStep 174323 = 261485) B261485
theorem B174339 : Blo 171799 174339 := bstep (se 1 (by rfl) ⟨130754, by rfl⟩ : syracuseStep 174339 = 261509) B261509
theorem B174355 : Blo 171799 174355 := bstep (se 1 (by rfl) ⟨130766, by rfl⟩ : syracuseStep 174355 = 261533) B261533
theorem B174371 : Blo 171799 174371 := bstep (se 1 (by rfl) ⟨130778, by rfl⟩ : syracuseStep 174371 = 261557) B261557
theorem B436529 : Blo 171799 436529 := bstep (se 2 (by rfl) ⟨163698, by rfl⟩ : syracuseStep 436529 = 327397) B327397
theorem B174387 : Blo 171799 174387 := bstep (se 1 (by rfl) ⟨130790, by rfl⟩ : syracuseStep 174387 = 261581) B261581
theorem B174403 : Blo 171799 174403 := bstep (se 1 (by rfl) ⟨130802, by rfl⟩ : syracuseStep 174403 = 261605) B261605
theorem B1059149 : Blo 171799 1059149 := bstep (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) B397181
theorem B174419 : Blo 171799 174419 := bstep (se 1 (by rfl) ⟨130814, by rfl⟩ : syracuseStep 174419 = 261629) B261629
theorem B174435 : Blo 171799 174435 := bstep (se 1 (by rfl) ⟨130826, by rfl⟩ : syracuseStep 174435 = 261653) B261653
theorem B174451 : Blo 171799 174451 := bstep (se 1 (by rfl) ⟨130838, by rfl⟩ : syracuseStep 174451 = 261677) B261677
theorem B174467 : Blo 171799 174467 := bstep (se 1 (by rfl) ⟨130850, by rfl⟩ : syracuseStep 174467 = 261701) B261701
theorem B174483 : Blo 171799 174483 := bstep (se 1 (by rfl) ⟨130862, by rfl⟩ : syracuseStep 174483 = 261725) B261725
theorem B174499 : Blo 171799 174499 := bstep (se 1 (by rfl) ⟨130874, by rfl⟩ : syracuseStep 174499 = 261749) B261749
theorem B174515 : Blo 171799 174515 := bstep (se 1 (by rfl) ⟨130886, by rfl⟩ : syracuseStep 174515 = 261773) B261773
theorem B174531 : Blo 171799 174531 := bstep (se 1 (by rfl) ⟨130898, by rfl⟩ : syracuseStep 174531 = 261797) B261797
theorem B174547 : Blo 171799 174547 := bstep (se 1 (by rfl) ⟨130910, by rfl⟩ : syracuseStep 174547 = 261821) B261821
theorem B174563 : Blo 171799 174563 := bstep (se 1 (by rfl) ⟨130922, by rfl⟩ : syracuseStep 174563 = 261845) B261845
theorem B174579 : Blo 171799 174579 := bstep (se 1 (by rfl) ⟨130934, by rfl⟩ : syracuseStep 174579 = 261869) B261869
theorem B174595 : Blo 171799 174595 := bstep (se 1 (by rfl) ⟨130946, by rfl⟩ : syracuseStep 174595 = 261893) B261893
theorem B174611 : Blo 171799 174611 := bstep (se 1 (by rfl) ⟨130958, by rfl⟩ : syracuseStep 174611 = 261917) B261917
theorem B174627 : Blo 171799 174627 := bstep (se 1 (by rfl) ⟨130970, by rfl⟩ : syracuseStep 174627 = 261941) B261941
theorem B174643 : Blo 171799 174643 := bstep (se 1 (by rfl) ⟨130982, by rfl⟩ : syracuseStep 174643 = 261965) B261965
theorem B174659 : Blo 171799 174659 := bstep (se 1 (by rfl) ⟨130994, by rfl⟩ : syracuseStep 174659 = 261989) B261989
theorem B174675 : Blo 171799 174675 := bstep (se 1 (by rfl) ⟨131006, by rfl⟩ : syracuseStep 174675 = 262013) B262013
theorem B174691 : Blo 171799 174691 := bstep (se 1 (by rfl) ⟨131018, by rfl⟩ : syracuseStep 174691 = 262037) B262037
theorem B174707 : Blo 171799 174707 := bstep (se 1 (by rfl) ⟨131030, by rfl⟩ : syracuseStep 174707 = 262061) B262061
theorem B174723 : Blo 171799 174723 := bstep (se 1 (by rfl) ⟨131042, by rfl⟩ : syracuseStep 174723 = 262085) B262085
theorem B174739 : Blo 171799 174739 := bstep (se 1 (by rfl) ⟨131054, by rfl⟩ : syracuseStep 174739 = 262109) B262109
theorem B174755 : Blo 171799 174755 := bstep (se 1 (by rfl) ⟨131066, by rfl⟩ : syracuseStep 174755 = 262133) B262133
theorem B174771 : Blo 171799 174771 := bstep (se 1 (by rfl) ⟨131078, by rfl⟩ : syracuseStep 174771 = 262157) B262157
theorem B174787 : Blo 171799 174787 := bstep (se 1 (by rfl) ⟨131090, by rfl⟩ : syracuseStep 174787 = 262181) B262181
theorem B174803 : Blo 171799 174803 := bstep (se 1 (by rfl) ⟨131102, by rfl⟩ : syracuseStep 174803 = 262205) B262205
theorem B174819 : Blo 171799 174819 := bstep (se 1 (by rfl) ⟨131114, by rfl⟩ : syracuseStep 174819 = 262229) B262229
theorem B371441 : Blo 171799 371441 := bstep (se 2 (by rfl) ⟨139290, by rfl⟩ : syracuseStep 371441 = 278581) B278581
theorem B174835 : Blo 171799 174835 := bstep (se 1 (by rfl) ⟨131126, by rfl⟩ : syracuseStep 174835 = 262253) B262253
theorem B174851 : Blo 171799 174851 := bstep (se 1 (by rfl) ⟨131138, by rfl⟩ : syracuseStep 174851 = 262277) B262277
theorem B174867 : Blo 171799 174867 := bstep (se 1 (by rfl) ⟨131150, by rfl⟩ : syracuseStep 174867 = 262301) B262301
theorem B174883 : Blo 171799 174883 := bstep (se 1 (by rfl) ⟨131162, by rfl⟩ : syracuseStep 174883 = 262325) B262325
theorem B174899 : Blo 171799 174899 := bstep (se 1 (by rfl) ⟨131174, by rfl⟩ : syracuseStep 174899 = 262349) B262349
theorem B174915 : Blo 171799 174915 := bstep (se 1 (by rfl) ⟨131186, by rfl⟩ : syracuseStep 174915 = 262373) B262373
theorem B994117 : Blo 171799 994117 := bstep (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) B186397
theorem B174931 : Blo 171799 174931 := bstep (se 1 (by rfl) ⟨131198, by rfl⟩ : syracuseStep 174931 = 262397) B262397
theorem B174947 : Blo 171799 174947 := bstep (se 1 (by rfl) ⟨131210, by rfl⟩ : syracuseStep 174947 = 262421) B262421
theorem B174963 : Blo 171799 174963 := bstep (se 1 (by rfl) ⟨131222, by rfl⟩ : syracuseStep 174963 = 262445) B262445
theorem B174979 : Blo 171799 174979 := bstep (se 1 (by rfl) ⟨131234, by rfl⟩ : syracuseStep 174979 = 262469) B262469
theorem B174995 : Blo 171799 174995 := bstep (se 1 (by rfl) ⟨131246, by rfl⟩ : syracuseStep 174995 = 262493) B262493
theorem B175011 : Blo 171799 175011 := bstep (se 1 (by rfl) ⟨131258, by rfl⟩ : syracuseStep 175011 = 262517) B262517
theorem B175027 : Blo 171799 175027 := bstep (se 1 (by rfl) ⟨131270, by rfl⟩ : syracuseStep 175027 = 262541) B262541
theorem B175043 : Blo 171799 175043 := bstep (se 1 (by rfl) ⟨131282, by rfl⟩ : syracuseStep 175043 = 262565) B262565
theorem B175059 : Blo 171799 175059 := bstep (se 1 (by rfl) ⟨131294, by rfl⟩ : syracuseStep 175059 = 262589) B262589
theorem B175075 : Blo 171799 175075 := bstep (se 1 (by rfl) ⟨131306, by rfl⟩ : syracuseStep 175075 = 262613) B262613
theorem B175091 : Blo 171799 175091 := bstep (se 1 (by rfl) ⟨131318, by rfl⟩ : syracuseStep 175091 = 262637) B262637
theorem B175107 : Blo 171799 175107 := bstep (se 1 (by rfl) ⟨131330, by rfl⟩ : syracuseStep 175107 = 262661) B262661
theorem B175123 : Blo 171799 175123 := bstep (se 1 (by rfl) ⟨131342, by rfl⟩ : syracuseStep 175123 = 262685) B262685
theorem B175139 : Blo 171799 175139 := bstep (se 1 (by rfl) ⟨131354, by rfl⟩ : syracuseStep 175139 = 262709) B262709
theorem B830513 : Blo 171799 830513 := bstep (se 2 (by rfl) ⟨311442, by rfl⟩ : syracuseStep 830513 = 622885) B622885
theorem B175155 : Blo 171799 175155 := bstep (se 1 (by rfl) ⟨131366, by rfl⟩ : syracuseStep 175155 = 262733) B262733
theorem B175171 : Blo 171799 175171 := bstep (se 1 (by rfl) ⟨131378, by rfl⟩ : syracuseStep 175171 = 262757) B262757
theorem B666701 : Blo 171799 666701 := bstep (se 3 (by rfl) ⟨125006, by rfl⟩ : syracuseStep 666701 = 250013) B250013
theorem B175187 : Blo 171799 175187 := bstep (se 1 (by rfl) ⟨131390, by rfl⟩ : syracuseStep 175187 = 262781) B262781
theorem B175203 : Blo 171799 175203 := bstep (se 1 (by rfl) ⟨131402, by rfl⟩ : syracuseStep 175203 = 262805) B262805
theorem B175219 : Blo 171799 175219 := bstep (se 1 (by rfl) ⟨131414, by rfl⟩ : syracuseStep 175219 = 262829) B262829
theorem B175235 : Blo 171799 175235 := bstep (se 1 (by rfl) ⟨131426, by rfl⟩ : syracuseStep 175235 = 262853) B262853
theorem B601229 : Blo 171799 601229 := bstep (se 3 (by rfl) ⟨112730, by rfl⟩ : syracuseStep 601229 = 225461) B225461
theorem B175251 : Blo 171799 175251 := bstep (se 1 (by rfl) ⟨131438, by rfl⟩ : syracuseStep 175251 = 262877) B262877
theorem B175267 : Blo 171799 175267 := bstep (se 1 (by rfl) ⟨131450, by rfl⟩ : syracuseStep 175267 = 262901) B262901
theorem B175283 : Blo 171799 175283 := bstep (se 1 (by rfl) ⟨131462, by rfl⟩ : syracuseStep 175283 = 262925) B262925
theorem B175299 : Blo 171799 175299 := bstep (se 1 (by rfl) ⟨131474, by rfl⟩ : syracuseStep 175299 = 262949) B262949
theorem B175315 : Blo 171799 175315 := bstep (se 1 (by rfl) ⟨131486, by rfl⟩ : syracuseStep 175315 = 262973) B262973
theorem B175331 : Blo 171799 175331 := bstep (se 1 (by rfl) ⟨131498, by rfl⟩ : syracuseStep 175331 = 262997) B262997
theorem B175347 : Blo 171799 175347 := bstep (se 1 (by rfl) ⟨131510, by rfl⟩ : syracuseStep 175347 = 263021) B263021
theorem B175363 : Blo 171799 175363 := bstep (se 1 (by rfl) ⟨131522, by rfl⟩ : syracuseStep 175363 = 263045) B263045
theorem B437521 : Blo 171799 437521 := bstep (se 2 (by rfl) ⟨164070, by rfl⟩ : syracuseStep 437521 = 328141) B328141
theorem B175379 : Blo 171799 175379 := bstep (se 1 (by rfl) ⟨131534, by rfl⟩ : syracuseStep 175379 = 263069) B263069
theorem B175395 : Blo 171799 175395 := bstep (se 1 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 175395 = 263093) B263093
theorem B175411 : Blo 171799 175411 := bstep (se 1 (by rfl) ⟨131558, by rfl⟩ : syracuseStep 175411 = 263117) B263117
theorem B175427 : Blo 171799 175427 := bstep (se 1 (by rfl) ⟨131570, by rfl⟩ : syracuseStep 175427 = 263141) B263141
theorem B175443 : Blo 171799 175443 := bstep (se 1 (by rfl) ⟨131582, by rfl⟩ : syracuseStep 175443 = 263165) B263165
theorem B175459 : Blo 171799 175459 := bstep (se 1 (by rfl) ⟨131594, by rfl⟩ : syracuseStep 175459 = 263189) B263189
theorem B175475 : Blo 171799 175475 := bstep (se 1 (by rfl) ⟨131606, by rfl⟩ : syracuseStep 175475 = 263213) B263213
theorem B175491 : Blo 171799 175491 := bstep (se 1 (by rfl) ⟨131618, by rfl⟩ : syracuseStep 175491 = 263237) B263237
theorem B175507 : Blo 171799 175507 := bstep (se 1 (by rfl) ⟨131630, by rfl⟩ : syracuseStep 175507 = 263261) B263261
theorem B175523 : Blo 171799 175523 := bstep (se 1 (by rfl) ⟨131642, by rfl⟩ : syracuseStep 175523 = 263285) B263285
theorem B175539 : Blo 171799 175539 := bstep (se 1 (by rfl) ⟨131654, by rfl⟩ : syracuseStep 175539 = 263309) B263309
theorem B175555 : Blo 171799 175555 := bstep (se 1 (by rfl) ⟨131666, by rfl⟩ : syracuseStep 175555 = 263333) B263333
theorem B175571 : Blo 171799 175571 := bstep (se 1 (by rfl) ⟨131678, by rfl⟩ : syracuseStep 175571 = 263357) B263357
theorem B175587 : Blo 171799 175587 := bstep (se 1 (by rfl) ⟨131690, by rfl⟩ : syracuseStep 175587 = 263381) B263381
theorem B175603 : Blo 171799 175603 := bstep (se 1 (by rfl) ⟨131702, by rfl⟩ : syracuseStep 175603 = 263405) B263405
theorem B175619 : Blo 171799 175619 := bstep (se 1 (by rfl) ⟨131714, by rfl⟩ : syracuseStep 175619 = 263429) B263429
theorem B175635 : Blo 171799 175635 := bstep (se 1 (by rfl) ⟨131726, by rfl⟩ : syracuseStep 175635 = 263453) B263453
theorem B437795 : Blo 171799 437795 := bstep (se 1 (by rfl) ⟨328346, by rfl⟩ : syracuseStep 437795 = 656693) B656693
theorem B175651 : Blo 171799 175651 := bstep (se 1 (by rfl) ⟨131738, by rfl⟩ : syracuseStep 175651 = 263477) B263477
theorem B175667 : Blo 171799 175667 := bstep (se 1 (by rfl) ⟨131750, by rfl⟩ : syracuseStep 175667 = 263501) B263501
theorem B175683 : Blo 171799 175683 := bstep (se 1 (by rfl) ⟨131762, by rfl⟩ : syracuseStep 175683 = 263525) B263525
theorem B175699 : Blo 171799 175699 := bstep (se 1 (by rfl) ⟨131774, by rfl⟩ : syracuseStep 175699 = 263549) B263549
theorem B175715 : Blo 171799 175715 := bstep (se 1 (by rfl) ⟨131786, by rfl⟩ : syracuseStep 175715 = 263573) B263573
theorem B175731 : Blo 171799 175731 := bstep (se 1 (by rfl) ⟨131798, by rfl⟩ : syracuseStep 175731 = 263597) B263597
theorem B175747 : Blo 171799 175747 := bstep (se 1 (by rfl) ⟨131810, by rfl⟩ : syracuseStep 175747 = 263621) B263621
theorem B994949 : Blo 171799 994949 := bstep (se 4 (by rfl) ⟨93276, by rfl⟩ : syracuseStep 994949 = 186553) B186553
theorem B175763 : Blo 171799 175763 := bstep (se 1 (by rfl) ⟨131822, by rfl⟩ : syracuseStep 175763 = 263645) B263645
theorem B175779 : Blo 171799 175779 := bstep (se 1 (by rfl) ⟨131834, by rfl⟩ : syracuseStep 175779 = 263669) B263669
theorem B175795 : Blo 171799 175795 := bstep (se 1 (by rfl) ⟨131846, by rfl⟩ : syracuseStep 175795 = 263693) B263693
theorem B437987 : Blo 171799 437987 := bstep (se 1 (by rfl) ⟨328490, by rfl⟩ : syracuseStep 437987 = 656981) B656981
theorem B929677 : Blo 171799 929677 := bstep (se 3 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 929677 = 348629) B348629
theorem B2240581 : Blo 171799 2240581 := bstep (se 4 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 2240581 = 420109) B420109
theorem B209027 : Blo 171799 209027 := bstep (se 1 (by rfl) ⟨156770, by rfl⟩ : syracuseStep 209027 = 313541) B313541
theorem B372977 : Blo 171799 372977 := bstep (se 2 (by rfl) ⟨139866, by rfl⟩ : syracuseStep 372977 = 279733) B279733
theorem B1323377 : Blo 171799 1323377 := bstep (se 2 (by rfl) ⟨496266, by rfl⟩ : syracuseStep 1323377 = 992533) B992533
theorem B373123 : Blo 171799 373123 := bstep (se 1 (by rfl) ⟨279842, by rfl⟩ : syracuseStep 373123 = 559685) B559685
theorem B1585763 : Blo 171799 1585763 := bstep (se 1 (by rfl) ⟨1189322, by rfl⟩ : syracuseStep 1585763 = 2378645) B2378645
theorem B438929 : Blo 171799 438929 := bstep (se 2 (by rfl) ⟨164598, by rfl⟩ : syracuseStep 438929 = 329197) B329197
theorem B438979 : Blo 171799 438979 := bstep (se 1 (by rfl) ⟨329234, by rfl⟩ : syracuseStep 438979 = 658469) B658469
theorem B996101 : Blo 171799 996101 := bstep (se 4 (by rfl) ⟨93384, by rfl⟩ : syracuseStep 996101 = 186769) B186769
theorem B930629 : Blo 171799 930629 := bstep (se 4 (by rfl) ⟨87246, by rfl⟩ : syracuseStep 930629 = 174493) B174493
theorem B373585 : Blo 171799 373585 := bstep (se 2 (by rfl) ⟨140094, by rfl⟩ : syracuseStep 373585 = 280189) B280189
theorem B439121 : Blo 171799 439121 := bstep (se 2 (by rfl) ⟨164670, by rfl⟩ : syracuseStep 439121 = 329341) B329341
theorem B897905 : Blo 171799 897905 := bstep (se 2 (by rfl) ⟨336714, by rfl⟩ : syracuseStep 897905 = 673429) B673429
theorem B734285 : Blo 171799 734285 := bstep (se 3 (by rfl) ⟨137678, by rfl⟩ : syracuseStep 734285 = 275357) B275357
theorem B275537 : Blo 171799 275537 := bstep (se 2 (by rfl) ⟨103326, by rfl⟩ : syracuseStep 275537 = 206653) B206653
theorem B275665 : Blo 171799 275665 := bstep (se 2 (by rfl) ⟨103374, by rfl⟩ : syracuseStep 275665 = 206749) B206749
theorem B570577 : Blo 171799 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B275729 : Blo 171799 275729 := bstep (se 2 (by rfl) ⟨103398, by rfl⟩ : syracuseStep 275729 = 206797) B206797
theorem B472355 : Blo 171799 472355 := bstep (se 1 (by rfl) ⟨354266, by rfl⟩ : syracuseStep 472355 = 708533) B708533
theorem B472387 : Blo 171799 472387 := bstep (se 1 (by rfl) ⟨354290, by rfl⟩ : syracuseStep 472387 = 708581) B708581
theorem B472717 : Blo 171799 472717 := bstep (se 3 (by rfl) ⟨88634, by rfl⟩ : syracuseStep 472717 = 177269) B177269
theorem B440113 : Blo 171799 440113 := bstep (se 2 (by rfl) ⟨165042, by rfl⟩ : syracuseStep 440113 = 330085) B330085
theorem B374627 : Blo 171799 374627 := bstep (se 1 (by rfl) ⟨280970, by rfl⟩ : syracuseStep 374627 = 561941) B561941
theorem B1259405 : Blo 171799 1259405 := bstep (se 3 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 1259405 = 472277) B472277
theorem B440387 : Blo 171799 440387 := bstep (se 1 (by rfl) ⟨330290, by rfl⟩ : syracuseStep 440387 = 660581) B660581
theorem B440579 : Blo 171799 440579 := bstep (se 1 (by rfl) ⟨330434, by rfl⟩ : syracuseStep 440579 = 660869) B660869
theorem B276787 : Blo 171799 276787 := bstep (se 1 (by rfl) ⟨207590, by rfl⟩ : syracuseStep 276787 = 415181) B415181
theorem B375139 : Blo 171799 375139 := bstep (se 1 (by rfl) ⟨281354, by rfl⟩ : syracuseStep 375139 = 562709) B562709
theorem B1325425 : Blo 171799 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B932273 : Blo 171799 932273 := bstep (se 2 (by rfl) ⟨349602, by rfl⟩ : syracuseStep 932273 = 699205) B699205
theorem B1063601 : Blo 171799 1063601 := bstep (se 2 (by rfl) ⟨398850, by rfl⟩ : syracuseStep 1063601 = 797701) B797701
theorem B1063793 : Blo 171799 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B244625 : Blo 171799 244625 := bstep (se 2 (by rfl) ⟨91734, by rfl⟩ : syracuseStep 244625 = 183469) B183469
theorem B244739 : Blo 171799 244739 := bstep (se 1 (by rfl) ⟨183554, by rfl⟩ : syracuseStep 244739 = 367109) B367109
theorem B1883189 : Blo 171799 1883189 := bstep (se 5 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 1883189 = 176549) B176549
theorem B244819 : Blo 171799 244819 := bstep (se 1 (by rfl) ⟨183614, by rfl⟩ : syracuseStep 244819 = 367229) B367229
theorem B441521 : Blo 171799 441521 := bstep (se 2 (by rfl) ⟨165570, by rfl⟩ : syracuseStep 441521 = 331141) B331141
theorem B277715 : Blo 171799 277715 := bstep (se 1 (by rfl) ⟨208286, by rfl⟩ : syracuseStep 277715 = 416573) B416573
theorem B1391843 : Blo 171799 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B441571 : Blo 171799 441571 := bstep (se 1 (by rfl) ⟨331178, by rfl⟩ : syracuseStep 441571 = 662357) B662357
theorem B179555 : Blo 171799 179555 := bstep (se 1 (by rfl) ⟨134666, by rfl⟩ : syracuseStep 179555 = 269333) B269333
theorem B441713 : Blo 171799 441713 := bstep (se 2 (by rfl) ⟨165642, by rfl⟩ : syracuseStep 441713 = 331285) B331285
theorem B1883573 : Blo 171799 1883573 := bstep (se 5 (by rfl) ⟨88292, by rfl⟩ : syracuseStep 1883573 = 176585) B176585
theorem B277985 : Blo 171799 277985 := bstep (se 2 (by rfl) ⟨104244, by rfl⟩ : syracuseStep 277985 = 208489) B208489
theorem B245377 : Blo 171799 245377 := bstep (se 2 (by rfl) ⟨92016, by rfl⟩ : syracuseStep 245377 = 184033) B184033
theorem B278273 : Blo 171799 278273 := bstep (se 2 (by rfl) ⟨104352, by rfl⟩ : syracuseStep 278273 = 208705) B208705
theorem B2015117 : Blo 171799 2015117 := bstep (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) B755669
theorem B606275 : Blo 171799 606275 := bstep (se 1 (by rfl) ⟨454706, by rfl⟩ : syracuseStep 606275 = 909413) B909413
theorem B278689 : Blo 171799 278689 := bstep (se 2 (by rfl) ⟨104508, by rfl⟩ : syracuseStep 278689 = 209017) B209017
theorem B999665 : Blo 171799 999665 := bstep (se 2 (by rfl) ⟨374874, by rfl⟩ : syracuseStep 999665 = 749749) B749749
theorem B246083 : Blo 171799 246083 := bstep (se 1 (by rfl) ⟨184562, by rfl⟩ : syracuseStep 246083 = 369125) B369125
theorem B442705 : Blo 171799 442705 := bstep (se 2 (by rfl) ⟨166014, by rfl⟩ : syracuseStep 442705 = 332029) B332029
theorem B311825 : Blo 171799 311825 := bstep (se 2 (by rfl) ⟨116934, by rfl⟩ : syracuseStep 311825 = 233869) B233869
theorem B442979 : Blo 171799 442979 := bstep (se 1 (by rfl) ⟨332234, by rfl⟩ : syracuseStep 442979 = 664469) B664469
theorem B443171 : Blo 171799 443171 := bstep (se 1 (by rfl) ⟨332378, by rfl⟩ : syracuseStep 443171 = 664757) B664757
theorem B1262405 : Blo 171799 1262405 := bstep (se 4 (by rfl) ⟨118350, by rfl⟩ : syracuseStep 1262405 = 236701) B236701
theorem B279443 : Blo 171799 279443 := bstep (se 1 (by rfl) ⟨209582, by rfl⟩ : syracuseStep 279443 = 419165) B419165
theorem B672689 : Blo 171799 672689 := bstep (se 2 (by rfl) ⟨252258, by rfl⟩ : syracuseStep 672689 = 504517) B504517
theorem B246721 : Blo 171799 246721 := bstep (se 2 (by rfl) ⟨92520, by rfl⟩ : syracuseStep 246721 = 185041) B185041
theorem B3195875 : Blo 171799 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B279587 : Blo 171799 279587 := bstep (se 1 (by rfl) ⟨209690, by rfl⟩ : syracuseStep 279587 = 419381) B419381
theorem B246835 : Blo 171799 246835 := bstep (se 1 (by rfl) ⟨185126, by rfl⟩ : syracuseStep 246835 = 370253) B370253
theorem B279811 : Blo 171799 279811 := bstep (se 1 (by rfl) ⟨209858, by rfl⟩ : syracuseStep 279811 = 419717) B419717
theorem B279857 : Blo 171799 279857 := bstep (se 2 (by rfl) ⟨104946, by rfl⟩ : syracuseStep 279857 = 209893) B209893
theorem B1000781 : Blo 171799 1000781 := bstep (se 3 (by rfl) ⟨187646, by rfl⟩ : syracuseStep 1000781 = 375293) B375293
theorem B738659 : Blo 171799 738659 := bstep (se 1 (by rfl) ⟨553994, by rfl⟩ : syracuseStep 738659 = 1107989) B1107989
theorem B444113 : Blo 171799 444113 := bstep (se 2 (by rfl) ⟨166542, by rfl⟩ : syracuseStep 444113 = 333085) B333085
theorem B444163 : Blo 171799 444163 := bstep (se 1 (by rfl) ⟨333122, by rfl⟩ : syracuseStep 444163 = 666245) B666245
theorem B3786517 : Blo 171799 3786517 := bstep (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) B177493
theorem B444305 : Blo 171799 444305 := bstep (se 2 (by rfl) ⟨166614, by rfl⟩ : syracuseStep 444305 = 333229) B333229
theorem B280675 : Blo 171799 280675 := bstep (se 1 (by rfl) ⟨210506, by rfl⟩ : syracuseStep 280675 = 421013) B421013
theorem B706765 : Blo 171799 706765 := bstep (se 3 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 706765 = 265037) B265037
theorem B280817 : Blo 171799 280817 := bstep (se 2 (by rfl) ⟨105306, by rfl⟩ : syracuseStep 280817 = 210613) B210613
theorem B2377997 : Blo 171799 2377997 := bstep (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) B891749
theorem B248179 : Blo 171799 248179 := bstep (se 1 (by rfl) ⟨186134, by rfl⟩ : syracuseStep 248179 = 372269) B372269
theorem B281009 : Blo 171799 281009 := bstep (se 2 (by rfl) ⟨105378, by rfl⟩ : syracuseStep 281009 = 210757) B210757
theorem B608771 : Blo 171799 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B1395427 : Blo 171799 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B314275 : Blo 171799 314275 := bstep (se 1 (by rfl) ⟨235706, by rfl⟩ : syracuseStep 314275 = 471413) B471413
theorem B674893 : Blo 171799 674893 := bstep (se 3 (by rfl) ⟨126542, by rfl⟩ : syracuseStep 674893 = 253085) B253085
theorem B6344077 : Blo 171799 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B249313 : Blo 171799 249313 := bstep (se 2 (by rfl) ⟨93492, by rfl⟩ : syracuseStep 249313 = 186985) B186985
theorem B249409 : Blo 171799 249409 := bstep (se 2 (by rfl) ⟨93528, by rfl⟩ : syracuseStep 249409 = 187057) B187057
theorem B183875 : Blo 171799 183875 := bstep (se 1 (by rfl) ⟨137906, by rfl⟩ : syracuseStep 183875 = 275813) B275813
theorem B3460805 : Blo 171799 3460805 := bstep (se 4 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 3460805 = 648901) B648901
theorem B872369 : Blo 171799 872369 := bstep (se 2 (by rfl) ⟨327138, by rfl⟩ : syracuseStep 872369 = 654277) B654277
theorem B741325 : Blo 171799 741325 := bstep (se 3 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 741325 = 277997) B277997
theorem B249905 : Blo 171799 249905 := bstep (se 2 (by rfl) ⟨93714, by rfl⟩ : syracuseStep 249905 = 187429) B187429
theorem B1200419 : Blo 171799 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B184627 : Blo 171799 184627 := bstep (se 1 (by rfl) ⟨138470, by rfl⟩ : syracuseStep 184627 = 276941) B276941
theorem B217667 : Blo 171799 217667 := bstep (se 1 (by rfl) ⟨163250, by rfl⟩ : syracuseStep 217667 = 326501) B326501
theorem B1987253 : Blo 171799 1987253 := bstep (se 5 (by rfl) ⟨93152, by rfl⟩ : syracuseStep 1987253 = 186305) B186305
theorem B3331043 : Blo 171799 3331043 := bstep (se 1 (by rfl) ⟨2498282, by rfl⟩ : syracuseStep 3331043 = 4996565) B4996565
theorem B742385 : Blo 171799 742385 := bstep (se 2 (by rfl) ⟨278394, by rfl⟩ : syracuseStep 742385 = 556789) B556789
theorem B218371 : Blo 171799 218371 := bstep (se 1 (by rfl) ⟨163778, by rfl⟩ : syracuseStep 218371 = 327557) B327557
theorem B873827 : Blo 171799 873827 := bstep (se 1 (by rfl) ⟨655370, by rfl⟩ : syracuseStep 873827 = 1310741) B1310741
theorem B218467 : Blo 171799 218467 := bstep (se 1 (by rfl) ⟨163850, by rfl⟩ : syracuseStep 218467 = 327701) B327701
theorem B185699 : Blo 171799 185699 := bstep (se 1 (by rfl) ⟨139274, by rfl⟩ : syracuseStep 185699 = 278549) B278549
theorem B415363 : Blo 171799 415363 := bstep (se 1 (by rfl) ⟨311522, by rfl⟩ : syracuseStep 415363 = 623045) B623045
theorem B2119409 : Blo 171799 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B218963 : Blo 171799 218963 := bstep (se 1 (by rfl) ⟨164222, by rfl⟩ : syracuseStep 218963 = 328445) B328445
theorem B841585 : Blo 171799 841585 := bstep (se 2 (by rfl) ⟨315594, by rfl⟩ : syracuseStep 841585 = 631189) B631189
theorem B2414645 : Blo 171799 2414645 := bstep (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) B226373
theorem B874637 : Blo 171799 874637 := bstep (se 3 (by rfl) ⟨163994, by rfl⟩ : syracuseStep 874637 = 327989) B327989
theorem B711011 : Blo 171799 711011 := bstep (se 1 (by rfl) ⟨533258, by rfl⟩ : syracuseStep 711011 = 1066517) B1066517
theorem B580013 : Blo 171799 580013 := bstep (se 3 (by rfl) ⟨108752, by rfl⟩ : syracuseStep 580013 = 217505) B217505
theorem B186835 : Blo 171799 186835 := bstep (se 1 (by rfl) ⟨140126, by rfl⟩ : syracuseStep 186835 = 280253) B280253
theorem B580067 : Blo 171799 580067 := bstep (se 1 (by rfl) ⟨435050, by rfl⟩ : syracuseStep 580067 = 870101) B870101
theorem B219667 : Blo 171799 219667 := bstep (se 1 (by rfl) ⟨164750, by rfl⟩ : syracuseStep 219667 = 329501) B329501
theorem B219763 : Blo 171799 219763 := bstep (se 1 (by rfl) ⟨164822, by rfl⟩ : syracuseStep 219763 = 329645) B329645
theorem B580337 : Blo 171799 580337 := bstep (se 2 (by rfl) ⟨217626, by rfl⟩ : syracuseStep 580337 = 435253) B435253
theorem B416593 : Blo 171799 416593 := bstep (se 2 (by rfl) ⟨156222, by rfl⟩ : syracuseStep 416593 = 312445) B312445
theorem B1858403 : Blo 171799 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B515153 : Blo 171799 515153 := bstep (se 2 (by rfl) ⟨193182, by rfl⟩ : syracuseStep 515153 = 386365) B386365
theorem B220259 : Blo 171799 220259 := bstep (se 1 (by rfl) ⟨165194, by rfl⟩ : syracuseStep 220259 = 330389) B330389
theorem B580877 : Blo 171799 580877 := bstep (se 3 (by rfl) ⟨108914, by rfl⟩ : syracuseStep 580877 = 217829) B217829
theorem B711985 : Blo 171799 711985 := bstep (se 2 (by rfl) ⟨266994, by rfl⟩ : syracuseStep 711985 = 533989) B533989
theorem B580931 : Blo 171799 580931 := bstep (se 1 (by rfl) ⟨435698, by rfl⟩ : syracuseStep 580931 = 871397) B871397
theorem B187715 : Blo 171799 187715 := bstep (se 1 (by rfl) ⟨140786, by rfl⟩ : syracuseStep 187715 = 281573) B281573
theorem B941489 : Blo 171799 941489 := bstep (se 2 (by rfl) ⟨353058, by rfl⟩ : syracuseStep 941489 = 706117) B706117
theorem B253459 : Blo 171799 253459 := bstep (se 1 (by rfl) ⟨190094, by rfl⟩ : syracuseStep 253459 = 380189) B380189
theorem B2022965 : Blo 171799 2022965 := bstep (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) B189653
theorem B581201 : Blo 171799 581201 := bstep (se 2 (by rfl) ⟨217950, by rfl⟩ : syracuseStep 581201 = 435901) B435901
theorem B941701 : Blo 171799 941701 := bstep (se 4 (by rfl) ⟨88284, by rfl⟩ : syracuseStep 941701 = 176569) B176569
theorem B220963 : Blo 171799 220963 := bstep (se 1 (by rfl) ⟨165722, by rfl⟩ : syracuseStep 220963 = 331445) B331445
theorem B221059 : Blo 171799 221059 := bstep (se 1 (by rfl) ⟨165794, by rfl⟩ : syracuseStep 221059 = 331589) B331589
theorem B745357 : Blo 171799 745357 := bstep (se 3 (by rfl) ⟨139754, by rfl⟩ : syracuseStep 745357 = 279509) B279509
theorem B581741 : Blo 171799 581741 := bstep (se 3 (by rfl) ⟨109076, by rfl⟩ : syracuseStep 581741 = 218153) B218153
theorem B581795 : Blo 171799 581795 := bstep (se 1 (by rfl) ⟨436346, by rfl⟩ : syracuseStep 581795 = 872693) B872693
theorem B745699 : Blo 171799 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B221555 : Blo 171799 221555 := bstep (se 1 (by rfl) ⟨166166, by rfl⟩ : syracuseStep 221555 = 332333) B332333
theorem B582065 : Blo 171799 582065 := bstep (se 2 (by rfl) ⟨218274, by rfl⟩ : syracuseStep 582065 = 436549) B436549
theorem B287297 : Blo 171799 287297 := bstep (se 2 (by rfl) ⟨107736, by rfl⟩ : syracuseStep 287297 = 215473) B215473
theorem B1106531 : Blo 171799 1106531 := bstep (se 1 (by rfl) ⟨829898, by rfl⟩ : syracuseStep 1106531 = 1659797) B1659797
theorem B3761093 : Blo 171799 3761093 := bstep (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) B705205
theorem B582605 : Blo 171799 582605 := bstep (se 3 (by rfl) ⟨109238, by rfl⟩ : syracuseStep 582605 = 218477) B218477
theorem B877553 : Blo 171799 877553 := bstep (se 2 (by rfl) ⟨329082, by rfl⟩ : syracuseStep 877553 = 658165) B658165
theorem B582659 : Blo 171799 582659 := bstep (se 1 (by rfl) ⟨436994, by rfl⟩ : syracuseStep 582659 = 873989) B873989
theorem B222259 : Blo 171799 222259 := bstep (se 1 (by rfl) ⟨166694, by rfl⟩ : syracuseStep 222259 = 333389) B333389
theorem B222355 : Blo 171799 222355 := bstep (se 1 (by rfl) ⟨166766, by rfl⟩ : syracuseStep 222355 = 333533) B333533
theorem B582929 : Blo 171799 582929 := bstep (se 2 (by rfl) ⟨218598, by rfl⟩ : syracuseStep 582929 = 437197) B437197
theorem B3630563 : Blo 171799 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B386801 : Blo 171799 386801 := bstep (se 2 (by rfl) ⟨145050, by rfl⟩ : syracuseStep 386801 = 290101) B290101
theorem B386819 : Blo 171799 386819 := bstep (se 1 (by rfl) ⟨290114, by rfl⟩ : syracuseStep 386819 = 580229) B580229
theorem B583469 : Blo 171799 583469 := bstep (se 3 (by rfl) ⟨109400, by rfl⟩ : syracuseStep 583469 = 218801) B218801
theorem B583523 : Blo 171799 583523 := bstep (se 1 (by rfl) ⟨437642, by rfl⟩ : syracuseStep 583523 = 875285) B875285
theorem B387089 : Blo 171799 387089 := bstep (se 2 (by rfl) ⟨145158, by rfl⟩ : syracuseStep 387089 = 290317) B290317
theorem B387107 : Blo 171799 387107 := bstep (se 1 (by rfl) ⟨290330, by rfl⟩ : syracuseStep 387107 = 580661) B580661
theorem B649315 : Blo 171799 649315 := bstep (se 1 (by rfl) ⟨486986, by rfl⟩ : syracuseStep 649315 = 973973) B973973
theorem B583793 : Blo 171799 583793 := bstep (se 2 (by rfl) ⟨218922, by rfl⟩ : syracuseStep 583793 = 437845) B437845
theorem B714865 : Blo 171799 714865 := bstep (se 2 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 714865 = 536149) B536149
theorem B387377 : Blo 171799 387377 := bstep (se 2 (by rfl) ⟨145266, by rfl⟩ : syracuseStep 387377 = 290533) B290533
theorem B387395 : Blo 171799 387395 := bstep (se 1 (by rfl) ⟨290546, by rfl⟩ : syracuseStep 387395 = 581093) B581093
theorem B879011 : Blo 171799 879011 := bstep (se 1 (by rfl) ⟨659258, by rfl⟩ : syracuseStep 879011 = 1318517) B1318517
theorem B223651 : Blo 171799 223651 := bstep (se 1 (by rfl) ⟨167738, by rfl⟩ : syracuseStep 223651 = 335477) B335477
theorem B7301573 : Blo 171799 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B1370609 : Blo 171799 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B387665 : Blo 171799 387665 := bstep (se 2 (by rfl) ⟨145374, by rfl⟩ : syracuseStep 387665 = 290749) B290749
theorem B387683 : Blo 171799 387683 := bstep (se 1 (by rfl) ⟨290762, by rfl⟩ : syracuseStep 387683 = 581525) B581525
theorem B584333 : Blo 171799 584333 := bstep (se 3 (by rfl) ⟨109562, by rfl⟩ : syracuseStep 584333 = 219125) B219125
theorem B420515 : Blo 171799 420515 := bstep (se 1 (by rfl) ⟨315386, by rfl⟩ : syracuseStep 420515 = 630773) B630773
theorem B584387 : Blo 171799 584387 := bstep (se 1 (by rfl) ⟨438290, by rfl⟩ : syracuseStep 584387 = 876581) B876581
theorem B387953 : Blo 171799 387953 := bstep (se 2 (by rfl) ⟨145482, by rfl⟩ : syracuseStep 387953 = 290965) B290965
theorem B387971 : Blo 171799 387971 := bstep (se 1 (by rfl) ⟨290978, by rfl⟩ : syracuseStep 387971 = 581957) B581957
theorem B551843 : Blo 171799 551843 := bstep (se 1 (by rfl) ⟨413882, by rfl⟩ : syracuseStep 551843 = 827765) B827765
theorem B584657 : Blo 171799 584657 := bstep (se 2 (by rfl) ⟨219246, by rfl⟩ : syracuseStep 584657 = 438493) B438493
theorem B945229 : Blo 171799 945229 := bstep (se 3 (by rfl) ⟨177230, by rfl⟩ : syracuseStep 945229 = 354461) B354461
theorem B552035 : Blo 171799 552035 := bstep (se 1 (by rfl) ⟨414026, by rfl⟩ : syracuseStep 552035 = 828053) B828053
theorem B388241 : Blo 171799 388241 := bstep (se 2 (by rfl) ⟨145590, by rfl⟩ : syracuseStep 388241 = 291181) B291181
theorem B289939 : Blo 171799 289939 := bstep (se 1 (by rfl) ⟨217454, by rfl⟩ : syracuseStep 289939 = 434909) B434909
theorem B388259 : Blo 171799 388259 := bstep (se 1 (by rfl) ⟨291194, by rfl⟩ : syracuseStep 388259 = 582389) B582389
theorem B879821 : Blo 171799 879821 := bstep (se 3 (by rfl) ⟨164966, by rfl⟩ : syracuseStep 879821 = 329933) B329933
theorem B290081 : Blo 171799 290081 := bstep (se 2 (by rfl) ⟨108780, by rfl⟩ : syracuseStep 290081 = 217561) B217561
theorem B290209 : Blo 171799 290209 := bstep (se 2 (by rfl) ⟨108828, by rfl⟩ : syracuseStep 290209 = 217657) B217657
theorem B421283 : Blo 171799 421283 := bstep (se 1 (by rfl) ⟨315962, by rfl⟩ : syracuseStep 421283 = 631925) B631925
theorem B388529 : Blo 171799 388529 := bstep (se 2 (by rfl) ⟨145698, by rfl⟩ : syracuseStep 388529 = 291397) B291397
theorem B290243 : Blo 171799 290243 := bstep (se 1 (by rfl) ⟨217682, by rfl⟩ : syracuseStep 290243 = 435365) B435365
theorem B388547 : Blo 171799 388547 := bstep (se 1 (by rfl) ⟨291410, by rfl⟩ : syracuseStep 388547 = 582821) B582821
theorem B585197 : Blo 171799 585197 := bstep (se 3 (by rfl) ⟨109724, by rfl⟩ : syracuseStep 585197 = 219449) B219449
theorem B585251 : Blo 171799 585251 := bstep (se 1 (by rfl) ⟨438938, by rfl⟩ : syracuseStep 585251 = 877877) B877877
theorem B290371 : Blo 171799 290371 := bstep (se 1 (by rfl) ⟨217778, by rfl⟩ : syracuseStep 290371 = 435557) B435557
theorem B257699 : Blo 171799 257699 := bstep (se 1 (by rfl) ⟨193274, by rfl⟩ : syracuseStep 257699 = 386549) B386549
theorem B257729 : Blo 171799 257729 := bstep (se 2 (by rfl) ⟨96648, by rfl⟩ : syracuseStep 257729 = 193297) B193297
theorem B290513 : Blo 171799 290513 := bstep (se 2 (by rfl) ⟨108942, by rfl⟩ : syracuseStep 290513 = 217885) B217885
theorem B388817 : Blo 171799 388817 := bstep (se 2 (by rfl) ⟨145806, by rfl⟩ : syracuseStep 388817 = 291613) B291613
theorem B257747 : Blo 171799 257747 := bstep (se 1 (by rfl) ⟨193310, by rfl⟩ : syracuseStep 257747 = 386621) B386621
theorem B388835 : Blo 171799 388835 := bstep (se 1 (by rfl) ⟨291626, by rfl⟩ : syracuseStep 388835 = 583253) B583253
theorem B257777 : Blo 171799 257777 := bstep (se 2 (by rfl) ⟨96666, by rfl⟩ : syracuseStep 257777 = 193333) B193333
theorem B552689 : Blo 171799 552689 := bstep (se 2 (by rfl) ⟨207258, by rfl⟩ : syracuseStep 552689 = 414517) B414517
theorem B257795 : Blo 171799 257795 := bstep (se 1 (by rfl) ⟨193346, by rfl⟩ : syracuseStep 257795 = 386693) B386693
theorem B257825 : Blo 171799 257825 := bstep (se 2 (by rfl) ⟨96684, by rfl⟩ : syracuseStep 257825 = 193369) B193369
theorem B585521 : Blo 171799 585521 := bstep (se 2 (by rfl) ⟨219570, by rfl⟩ : syracuseStep 585521 = 439141) B439141
theorem B257843 : Blo 171799 257843 := bstep (se 1 (by rfl) ⟨193382, by rfl⟩ : syracuseStep 257843 = 386765) B386765
theorem B257873 : Blo 171799 257873 := bstep (se 2 (by rfl) ⟨96702, by rfl⟩ : syracuseStep 257873 = 193405) B193405
theorem B290641 : Blo 171799 290641 := bstep (se 2 (by rfl) ⟨108990, by rfl⟩ : syracuseStep 290641 = 217981) B217981
theorem B257891 : Blo 171799 257891 := bstep (se 1 (by rfl) ⟨193418, by rfl⟩ : syracuseStep 257891 = 386837) B386837
theorem B290675 : Blo 171799 290675 := bstep (se 1 (by rfl) ⟨218006, by rfl⟩ : syracuseStep 290675 = 436013) B436013
theorem B257921 : Blo 171799 257921 := bstep (se 2 (by rfl) ⟨96720, by rfl⟩ : syracuseStep 257921 = 193441) B193441
theorem B257939 : Blo 171799 257939 := bstep (se 1 (by rfl) ⟨193454, by rfl⟩ : syracuseStep 257939 = 386909) B386909
theorem B257969 : Blo 171799 257969 := bstep (se 2 (by rfl) ⟨96738, by rfl⟩ : syracuseStep 257969 = 193477) B193477
theorem B257987 : Blo 171799 257987 := bstep (se 1 (by rfl) ⟨193490, by rfl⟩ : syracuseStep 257987 = 386981) B386981
theorem B421841 : Blo 171799 421841 := bstep (se 2 (by rfl) ⟨158190, by rfl⟩ : syracuseStep 421841 = 316381) B316381
theorem B258017 : Blo 171799 258017 := bstep (se 2 (by rfl) ⟨96756, by rfl⟩ : syracuseStep 258017 = 193513) B193513
theorem B389105 : Blo 171799 389105 := bstep (se 2 (by rfl) ⟨145914, by rfl⟩ : syracuseStep 389105 = 291829) B291829
theorem B258035 : Blo 171799 258035 := bstep (se 1 (by rfl) ⟨193526, by rfl⟩ : syracuseStep 258035 = 387053) B387053
theorem B290803 : Blo 171799 290803 := bstep (se 1 (by rfl) ⟨218102, by rfl⟩ : syracuseStep 290803 = 436205) B436205
theorem B389123 : Blo 171799 389123 := bstep (se 1 (by rfl) ⟨291842, by rfl⟩ : syracuseStep 389123 = 583685) B583685
theorem B258065 : Blo 171799 258065 := bstep (se 2 (by rfl) ⟨96774, by rfl⟩ : syracuseStep 258065 = 193549) B193549
theorem B258083 : Blo 171799 258083 := bstep (se 1 (by rfl) ⟨193562, by rfl⟩ : syracuseStep 258083 = 387125) B387125
theorem B258113 : Blo 171799 258113 := bstep (se 2 (by rfl) ⟨96792, by rfl⟩ : syracuseStep 258113 = 193585) B193585
theorem B258131 : Blo 171799 258131 := bstep (se 1 (by rfl) ⟨193598, by rfl⟩ : syracuseStep 258131 = 387197) B387197
theorem B258161 : Blo 171799 258161 := bstep (se 2 (by rfl) ⟨96810, by rfl⟩ : syracuseStep 258161 = 193621) B193621
theorem B290945 : Blo 171799 290945 := bstep (se 2 (by rfl) ⟨109104, by rfl⟩ : syracuseStep 290945 = 218209) B218209
theorem B258179 : Blo 171799 258179 := bstep (se 1 (by rfl) ⟨193634, by rfl⟩ : syracuseStep 258179 = 387269) B387269
theorem B1667213 : Blo 171799 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B258209 : Blo 171799 258209 := bstep (se 2 (by rfl) ⟨96828, by rfl⟩ : syracuseStep 258209 = 193657) B193657
theorem B749731 : Blo 171799 749731 := bstep (se 1 (by rfl) ⟨562298, by rfl⟩ : syracuseStep 749731 = 1124597) B1124597
theorem B258227 : Blo 171799 258227 := bstep (se 1 (by rfl) ⟨193670, by rfl⟩ : syracuseStep 258227 = 387341) B387341
theorem B258257 : Blo 171799 258257 := bstep (se 2 (by rfl) ⟨96846, by rfl⟩ : syracuseStep 258257 = 193693) B193693
theorem B258275 : Blo 171799 258275 := bstep (se 1 (by rfl) ⟨193706, by rfl⟩ : syracuseStep 258275 = 387413) B387413
theorem B258305 : Blo 171799 258305 := bstep (se 2 (by rfl) ⟨96864, by rfl⟩ : syracuseStep 258305 = 193729) B193729
theorem B291073 : Blo 171799 291073 := bstep (se 2 (by rfl) ⟨109152, by rfl⟩ : syracuseStep 291073 = 218305) B218305
theorem B389393 : Blo 171799 389393 := bstep (se 2 (by rfl) ⟨146022, by rfl⟩ : syracuseStep 389393 = 292045) B292045
theorem B258323 : Blo 171799 258323 := bstep (se 1 (by rfl) ⟨193742, by rfl⟩ : syracuseStep 258323 = 387485) B387485
theorem B291107 : Blo 171799 291107 := bstep (se 1 (by rfl) ⟨218330, by rfl⟩ : syracuseStep 291107 = 436661) B436661
theorem B389411 : Blo 171799 389411 := bstep (se 1 (by rfl) ⟨292058, by rfl⟩ : syracuseStep 389411 = 584117) B584117
theorem B258353 : Blo 171799 258353 := bstep (se 2 (by rfl) ⟨96882, by rfl⟩ : syracuseStep 258353 = 193765) B193765
theorem B258371 : Blo 171799 258371 := bstep (se 1 (by rfl) ⟨193778, by rfl⟩ : syracuseStep 258371 = 387557) B387557
theorem B586061 : Blo 171799 586061 := bstep (se 3 (by rfl) ⟨109886, by rfl⟩ : syracuseStep 586061 = 219773) B219773
theorem B422225 : Blo 171799 422225 := bstep (se 2 (by rfl) ⟨158334, by rfl⟩ : syracuseStep 422225 = 316669) B316669
theorem B258401 : Blo 171799 258401 := bstep (se 2 (by rfl) ⟨96900, by rfl⟩ : syracuseStep 258401 = 193801) B193801
theorem B258419 : Blo 171799 258419 := bstep (se 1 (by rfl) ⟨193814, by rfl⟩ : syracuseStep 258419 = 387629) B387629
theorem B586115 : Blo 171799 586115 := bstep (se 1 (by rfl) ⟨439586, by rfl⟩ : syracuseStep 586115 = 879173) B879173
theorem B258449 : Blo 171799 258449 := bstep (se 2 (by rfl) ⟨96918, by rfl⟩ : syracuseStep 258449 = 193837) B193837
theorem B258467 : Blo 171799 258467 := bstep (se 1 (by rfl) ⟨193850, by rfl⟩ : syracuseStep 258467 = 387701) B387701
theorem B291235 : Blo 171799 291235 := bstep (se 1 (by rfl) ⟨218426, by rfl⟩ : syracuseStep 291235 = 436853) B436853
theorem B1110449 : Blo 171799 1110449 := bstep (se 2 (by rfl) ⟨416418, by rfl⟩ : syracuseStep 1110449 = 832837) B832837
theorem B258497 : Blo 171799 258497 := bstep (se 2 (by rfl) ⟨96936, by rfl⟩ : syracuseStep 258497 = 193873) B193873
theorem B422339 : Blo 171799 422339 := bstep (se 1 (by rfl) ⟨316754, by rfl⟩ : syracuseStep 422339 = 633509) B633509
theorem B258515 : Blo 171799 258515 := bstep (se 1 (by rfl) ⟨193886, by rfl⟩ : syracuseStep 258515 = 387773) B387773
theorem B1962467 : Blo 171799 1962467 := bstep (se 1 (by rfl) ⟨1471850, by rfl⟩ : syracuseStep 1962467 = 2943701) B2943701
theorem B258545 : Blo 171799 258545 := bstep (se 2 (by rfl) ⟨96954, by rfl⟩ : syracuseStep 258545 = 193909) B193909
theorem B258563 : Blo 171799 258563 := bstep (se 1 (by rfl) ⟨193922, by rfl⟩ : syracuseStep 258563 = 387845) B387845
theorem B258593 : Blo 171799 258593 := bstep (se 2 (by rfl) ⟨96972, by rfl⟩ : syracuseStep 258593 = 193945) B193945
theorem B291377 : Blo 171799 291377 := bstep (se 2 (by rfl) ⟨109266, by rfl⟩ : syracuseStep 291377 = 218533) B218533
theorem B389681 : Blo 171799 389681 := bstep (se 2 (by rfl) ⟨146130, by rfl⟩ : syracuseStep 389681 = 292261) B292261
theorem B258611 : Blo 171799 258611 := bstep (se 1 (by rfl) ⟨193958, by rfl⟩ : syracuseStep 258611 = 387917) B387917
theorem B389699 : Blo 171799 389699 := bstep (se 1 (by rfl) ⟨292274, by rfl⟩ : syracuseStep 389699 = 584549) B584549
theorem B258641 : Blo 171799 258641 := bstep (se 2 (by rfl) ⟨96990, by rfl⟩ : syracuseStep 258641 = 193981) B193981
theorem B258659 : Blo 171799 258659 := bstep (se 1 (by rfl) ⟨193994, by rfl⟩ : syracuseStep 258659 = 387989) B387989
theorem B258689 : Blo 171799 258689 := bstep (se 2 (by rfl) ⟨97008, by rfl⟩ : syracuseStep 258689 = 194017) B194017
theorem B586385 : Blo 171799 586385 := bstep (se 2 (by rfl) ⟨219894, by rfl⟩ : syracuseStep 586385 = 439789) B439789
theorem B258707 : Blo 171799 258707 := bstep (se 1 (by rfl) ⟨194030, by rfl⟩ : syracuseStep 258707 = 388061) B388061
theorem B258737 : Blo 171799 258737 := bstep (se 2 (by rfl) ⟨97026, by rfl⟩ : syracuseStep 258737 = 194053) B194053
theorem B291505 : Blo 171799 291505 := bstep (se 2 (by rfl) ⟨109314, by rfl⟩ : syracuseStep 291505 = 218629) B218629
theorem B258755 : Blo 171799 258755 := bstep (se 1 (by rfl) ⟨194066, by rfl⟩ : syracuseStep 258755 = 388133) B388133
theorem B291539 : Blo 171799 291539 := bstep (se 1 (by rfl) ⟨218654, by rfl⟩ : syracuseStep 291539 = 437309) B437309
theorem B258785 : Blo 171799 258785 := bstep (se 2 (by rfl) ⟨97044, by rfl⟩ : syracuseStep 258785 = 194089) B194089
theorem B258803 : Blo 171799 258803 := bstep (se 1 (by rfl) ⟨194102, by rfl⟩ : syracuseStep 258803 = 388205) B388205
theorem B258833 : Blo 171799 258833 := bstep (se 2 (by rfl) ⟨97062, by rfl⟩ : syracuseStep 258833 = 194125) B194125
theorem B193315 : Blo 171799 193315 := bstep (se 1 (by rfl) ⟨144986, by rfl⟩ : syracuseStep 193315 = 289973) B289973
theorem B258851 : Blo 171799 258851 := bstep (se 1 (by rfl) ⟨194138, by rfl⟩ : syracuseStep 258851 = 388277) B388277
theorem B258881 : Blo 171799 258881 := bstep (se 2 (by rfl) ⟨97080, by rfl⟩ : syracuseStep 258881 = 194161) B194161
theorem B389969 : Blo 171799 389969 := bstep (se 2 (by rfl) ⟨146238, by rfl⟩ : syracuseStep 389969 = 292477) B292477
theorem B258899 : Blo 171799 258899 := bstep (se 1 (by rfl) ⟨194174, by rfl⟩ : syracuseStep 258899 = 388349) B388349
theorem B291667 : Blo 171799 291667 := bstep (se 1 (by rfl) ⟨218750, by rfl⟩ : syracuseStep 291667 = 437501) B437501
theorem B389987 : Blo 171799 389987 := bstep (se 1 (by rfl) ⟨292490, by rfl⟩ : syracuseStep 389987 = 584981) B584981
theorem B258929 : Blo 171799 258929 := bstep (se 2 (by rfl) ⟨97098, by rfl⟩ : syracuseStep 258929 = 194197) B194197
theorem B258947 : Blo 171799 258947 := bstep (se 1 (by rfl) ⟨194210, by rfl⟩ : syracuseStep 258947 = 388421) B388421
theorem B258977 : Blo 171799 258977 := bstep (se 2 (by rfl) ⟨97116, by rfl⟩ : syracuseStep 258977 = 194233) B194233
theorem B619427 : Blo 171799 619427 := bstep (se 1 (by rfl) ⟨464570, by rfl⟩ : syracuseStep 619427 = 929141) B929141
theorem B193459 : Blo 171799 193459 := bstep (se 1 (by rfl) ⟨145094, by rfl⟩ : syracuseStep 193459 = 290189) B290189
theorem B258995 : Blo 171799 258995 := bstep (se 1 (by rfl) ⟨194246, by rfl⟩ : syracuseStep 258995 = 388493) B388493
theorem B259025 : Blo 171799 259025 := bstep (se 2 (by rfl) ⟨97134, by rfl⟩ : syracuseStep 259025 = 194269) B194269
theorem B291809 : Blo 171799 291809 := bstep (se 2 (by rfl) ⟨109428, by rfl⟩ : syracuseStep 291809 = 218857) B218857
theorem B259043 : Blo 171799 259043 := bstep (se 1 (by rfl) ⟨194282, by rfl⟩ : syracuseStep 259043 = 388565) B388565
theorem B259073 : Blo 171799 259073 := bstep (se 2 (by rfl) ⟨97152, by rfl⟩ : syracuseStep 259073 = 194305) B194305
theorem B259091 : Blo 171799 259091 := bstep (se 1 (by rfl) ⟨194318, by rfl⟩ : syracuseStep 259091 = 388637) B388637
theorem B259121 : Blo 171799 259121 := bstep (se 2 (by rfl) ⟨97170, by rfl⟩ : syracuseStep 259121 = 194341) B194341
theorem B193603 : Blo 171799 193603 := bstep (se 1 (by rfl) ⟨145202, by rfl⟩ : syracuseStep 193603 = 290405) B290405
theorem B259139 : Blo 171799 259139 := bstep (se 1 (by rfl) ⟨194354, by rfl⟩ : syracuseStep 259139 = 388709) B388709
theorem B1111117 : Blo 171799 1111117 := bstep (se 3 (by rfl) ⟨208334, by rfl⟩ : syracuseStep 1111117 = 416669) B416669
theorem B259169 : Blo 171799 259169 := bstep (se 2 (by rfl) ⟨97188, by rfl⟩ : syracuseStep 259169 = 194377) B194377
theorem B291937 : Blo 171799 291937 := bstep (se 2 (by rfl) ⟨109476, by rfl⟩ : syracuseStep 291937 = 218953) B218953
theorem B390257 : Blo 171799 390257 := bstep (se 2 (by rfl) ⟨146346, by rfl⟩ : syracuseStep 390257 = 292693) B292693
theorem B259187 : Blo 171799 259187 := bstep (se 1 (by rfl) ⟨194390, by rfl⟩ : syracuseStep 259187 = 388781) B388781
theorem B291971 : Blo 171799 291971 := bstep (se 1 (by rfl) ⟨218978, by rfl⟩ : syracuseStep 291971 = 437957) B437957
theorem B390275 : Blo 171799 390275 := bstep (se 1 (by rfl) ⟨292706, by rfl⟩ : syracuseStep 390275 = 585413) B585413
theorem B259217 : Blo 171799 259217 := bstep (se 2 (by rfl) ⟨97206, by rfl⟩ : syracuseStep 259217 = 194413) B194413
theorem B259235 : Blo 171799 259235 := bstep (se 1 (by rfl) ⟨194426, by rfl⟩ : syracuseStep 259235 = 388853) B388853
theorem B586925 : Blo 171799 586925 := bstep (se 3 (by rfl) ⟨110048, by rfl⟩ : syracuseStep 586925 = 220097) B220097
theorem B259265 : Blo 171799 259265 := bstep (se 2 (by rfl) ⟨97224, by rfl⟩ : syracuseStep 259265 = 194449) B194449
theorem B193747 : Blo 171799 193747 := bstep (se 1 (by rfl) ⟨145310, by rfl⟩ : syracuseStep 193747 = 290621) B290621
theorem B259283 : Blo 171799 259283 := bstep (se 1 (by rfl) ⟨194462, by rfl⟩ : syracuseStep 259283 = 388925) B388925
theorem B1471715 : Blo 171799 1471715 := bstep (se 1 (by rfl) ⟨1103786, by rfl⟩ : syracuseStep 1471715 = 2207573) B2207573
theorem B586979 : Blo 171799 586979 := bstep (se 1 (by rfl) ⟨440234, by rfl⟩ : syracuseStep 586979 = 880469) B880469
theorem B259313 : Blo 171799 259313 := bstep (se 2 (by rfl) ⟨97242, by rfl⟩ : syracuseStep 259313 = 194485) B194485
theorem B259331 : Blo 171799 259331 := bstep (se 1 (by rfl) ⟨194498, by rfl⟩ : syracuseStep 259331 = 388997) B388997
theorem B292099 : Blo 171799 292099 := bstep (se 1 (by rfl) ⟨219074, by rfl⟩ : syracuseStep 292099 = 438149) B438149
theorem B259361 : Blo 171799 259361 := bstep (se 2 (by rfl) ⟨97260, by rfl⟩ : syracuseStep 259361 = 194521) B194521
theorem B259379 : Blo 171799 259379 := bstep (se 1 (by rfl) ⟨194534, by rfl⟩ : syracuseStep 259379 = 389069) B389069
theorem B259409 : Blo 171799 259409 := bstep (se 2 (by rfl) ⟨97278, by rfl⟩ : syracuseStep 259409 = 194557) B194557
theorem B193891 : Blo 171799 193891 := bstep (se 1 (by rfl) ⟨145418, by rfl⟩ : syracuseStep 193891 = 290837) B290837
theorem B259427 : Blo 171799 259427 := bstep (se 1 (by rfl) ⟨194570, by rfl⟩ : syracuseStep 259427 = 389141) B389141
theorem B750961 : Blo 171799 750961 := bstep (se 2 (by rfl) ⟨281610, by rfl⟩ : syracuseStep 750961 = 563221) B563221
theorem B259457 : Blo 171799 259457 := bstep (se 2 (by rfl) ⟨97296, by rfl⟩ : syracuseStep 259457 = 194593) B194593
theorem B292241 : Blo 171799 292241 := bstep (se 2 (by rfl) ⟨109590, by rfl⟩ : syracuseStep 292241 = 219181) B219181
theorem B259475 : Blo 171799 259475 := bstep (se 1 (by rfl) ⟨194606, by rfl⟩ : syracuseStep 259475 = 389213) B389213
theorem B390545 : Blo 171799 390545 := bstep (se 2 (by rfl) ⟨146454, by rfl⟩ : syracuseStep 390545 = 292909) B292909
theorem B390563 : Blo 171799 390563 := bstep (se 1 (by rfl) ⟨292922, by rfl⟩ : syracuseStep 390563 = 585845) B585845
theorem B259505 : Blo 171799 259505 := bstep (se 2 (by rfl) ⟨97314, by rfl⟩ : syracuseStep 259505 = 194629) B194629
theorem B259523 : Blo 171799 259523 := bstep (se 1 (by rfl) ⟨194642, by rfl⟩ : syracuseStep 259523 = 389285) B389285
theorem B259553 : Blo 171799 259553 := bstep (se 2 (by rfl) ⟨97332, by rfl⟩ : syracuseStep 259553 = 194665) B194665
theorem B587249 : Blo 171799 587249 := bstep (se 2 (by rfl) ⟨220218, by rfl⟩ : syracuseStep 587249 = 440437) B440437
theorem B194035 : Blo 171799 194035 := bstep (se 1 (by rfl) ⟨145526, by rfl⟩ : syracuseStep 194035 = 291053) B291053
theorem B259571 : Blo 171799 259571 := bstep (se 1 (by rfl) ⟨194678, by rfl⟩ : syracuseStep 259571 = 389357) B389357
theorem B259601 : Blo 171799 259601 := bstep (se 2 (by rfl) ⟨97350, by rfl⟩ : syracuseStep 259601 = 194701) B194701
theorem B292369 : Blo 171799 292369 := bstep (se 2 (by rfl) ⟨109638, by rfl⟩ : syracuseStep 292369 = 219277) B219277
theorem B259619 : Blo 171799 259619 := bstep (se 1 (by rfl) ⟨194714, by rfl⟩ : syracuseStep 259619 = 389429) B389429
theorem B292403 : Blo 171799 292403 := bstep (se 1 (by rfl) ⟨219302, by rfl⟩ : syracuseStep 292403 = 438605) B438605
theorem B259649 : Blo 171799 259649 := bstep (se 2 (by rfl) ⟨97368, by rfl⟩ : syracuseStep 259649 = 194737) B194737
theorem B259667 : Blo 171799 259667 := bstep (se 1 (by rfl) ⟨194750, by rfl⟩ : syracuseStep 259667 = 389501) B389501
theorem B620131 : Blo 171799 620131 := bstep (se 1 (by rfl) ⟨465098, by rfl⟩ : syracuseStep 620131 = 930197) B930197
theorem B259697 : Blo 171799 259697 := bstep (se 2 (by rfl) ⟨97386, by rfl⟩ : syracuseStep 259697 = 194773) B194773
theorem B194179 : Blo 171799 194179 := bstep (se 1 (by rfl) ⟨145634, by rfl⟩ : syracuseStep 194179 = 291269) B291269
theorem B259715 : Blo 171799 259715 := bstep (se 1 (by rfl) ⟨194786, by rfl⟩ : syracuseStep 259715 = 389573) B389573
theorem B259745 : Blo 171799 259745 := bstep (se 2 (by rfl) ⟨97404, by rfl⟩ : syracuseStep 259745 = 194809) B194809
theorem B390833 : Blo 171799 390833 := bstep (se 2 (by rfl) ⟨146562, by rfl⟩ : syracuseStep 390833 = 293125) B293125
theorem B259763 : Blo 171799 259763 := bstep (se 1 (by rfl) ⟨194822, by rfl⟩ : syracuseStep 259763 = 389645) B389645
theorem B292531 : Blo 171799 292531 := bstep (se 1 (by rfl) ⟨219398, by rfl⟩ : syracuseStep 292531 = 438797) B438797
theorem B390851 : Blo 171799 390851 := bstep (se 1 (by rfl) ⟨293138, by rfl⟩ : syracuseStep 390851 = 586277) B586277
theorem B554701 : Blo 171799 554701 := bstep (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) B208013
theorem B259793 : Blo 171799 259793 := bstep (se 2 (by rfl) ⟨97422, by rfl⟩ : syracuseStep 259793 = 194845) B194845
theorem B259811 : Blo 171799 259811 := bstep (se 1 (by rfl) ⟨194858, by rfl⟩ : syracuseStep 259811 = 389717) B389717
theorem B259841 : Blo 171799 259841 := bstep (se 2 (by rfl) ⟨97440, by rfl⟩ : syracuseStep 259841 = 194881) B194881
theorem B194323 : Blo 171799 194323 := bstep (se 1 (by rfl) ⟨145742, by rfl⟩ : syracuseStep 194323 = 291485) B291485
theorem B259859 : Blo 171799 259859 := bstep (se 1 (by rfl) ⟨194894, by rfl⟩ : syracuseStep 259859 = 389789) B389789
theorem B259889 : Blo 171799 259889 := bstep (se 2 (by rfl) ⟨97458, by rfl⟩ : syracuseStep 259889 = 194917) B194917
theorem B292673 : Blo 171799 292673 := bstep (se 2 (by rfl) ⟨109752, by rfl⟩ : syracuseStep 292673 = 219505) B219505
theorem B259907 : Blo 171799 259907 := bstep (se 1 (by rfl) ⟨194930, by rfl⟩ : syracuseStep 259907 = 389861) B389861
theorem B259937 : Blo 171799 259937 := bstep (se 2 (by rfl) ⟨97476, by rfl⟩ : syracuseStep 259937 = 194953) B194953
theorem B259955 : Blo 171799 259955 := bstep (se 1 (by rfl) ⟨194966, by rfl⟩ : syracuseStep 259955 = 389933) B389933
theorem B980869 : Blo 171799 980869 := bstep (se 4 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 980869 = 183913) B183913
theorem B259985 : Blo 171799 259985 := bstep (se 2 (by rfl) ⟨97494, by rfl⟩ : syracuseStep 259985 = 194989) B194989
theorem B194467 : Blo 171799 194467 := bstep (se 1 (by rfl) ⟨145850, by rfl⟩ : syracuseStep 194467 = 291701) B291701
theorem B260003 : Blo 171799 260003 := bstep (se 1 (by rfl) ⟨195002, by rfl⟩ : syracuseStep 260003 = 390005) B390005
theorem B1046449 : Blo 171799 1046449 := bstep (se 2 (by rfl) ⟨392418, by rfl⟩ : syracuseStep 1046449 = 784837) B784837
theorem B260033 : Blo 171799 260033 := bstep (se 2 (by rfl) ⟨97512, by rfl⟩ : syracuseStep 260033 = 195025) B195025
theorem B292801 : Blo 171799 292801 := bstep (se 2 (by rfl) ⟨109800, by rfl⟩ : syracuseStep 292801 = 219601) B219601
theorem B391121 : Blo 171799 391121 := bstep (se 2 (by rfl) ⟨146670, by rfl⟩ : syracuseStep 391121 = 293341) B293341
theorem B260051 : Blo 171799 260051 := bstep (se 1 (by rfl) ⟨195038, by rfl⟩ : syracuseStep 260051 = 390077) B390077
theorem B292835 : Blo 171799 292835 := bstep (se 1 (by rfl) ⟨219626, by rfl⟩ : syracuseStep 292835 = 439253) B439253
theorem B391139 : Blo 171799 391139 := bstep (se 1 (by rfl) ⟨293354, by rfl⟩ : syracuseStep 391139 = 586709) B586709
theorem B260081 : Blo 171799 260081 := bstep (se 2 (by rfl) ⟨97530, by rfl⟩ : syracuseStep 260081 = 195061) B195061
theorem B260099 : Blo 171799 260099 := bstep (se 1 (by rfl) ⟨195074, by rfl⟩ : syracuseStep 260099 = 390149) B390149
theorem B587789 : Blo 171799 587789 := bstep (se 3 (by rfl) ⟨110210, by rfl⟩ : syracuseStep 587789 = 220421) B220421
theorem B260129 : Blo 171799 260129 := bstep (se 2 (by rfl) ⟨97548, by rfl⟩ : syracuseStep 260129 = 195097) B195097
theorem B882737 : Blo 171799 882737 := bstep (se 2 (by rfl) ⟨331026, by rfl⟩ : syracuseStep 882737 = 662053) B662053
theorem B194611 : Blo 171799 194611 := bstep (se 1 (by rfl) ⟨145958, by rfl⟩ : syracuseStep 194611 = 291917) B291917
theorem B260147 : Blo 171799 260147 := bstep (se 1 (by rfl) ⟨195110, by rfl⟩ : syracuseStep 260147 = 390221) B390221
theorem B587843 : Blo 171799 587843 := bstep (se 1 (by rfl) ⟨440882, by rfl⟩ : syracuseStep 587843 = 881765) B881765
theorem B260177 : Blo 171799 260177 := bstep (se 2 (by rfl) ⟨97566, by rfl⟩ : syracuseStep 260177 = 195133) B195133
theorem B260195 : Blo 171799 260195 := bstep (se 1 (by rfl) ⟨195146, by rfl⟩ : syracuseStep 260195 = 390293) B390293
theorem B292963 : Blo 171799 292963 := bstep (se 1 (by rfl) ⟨219722, by rfl⟩ : syracuseStep 292963 = 439445) B439445
theorem B260225 : Blo 171799 260225 := bstep (se 2 (by rfl) ⟨97584, by rfl⟩ : syracuseStep 260225 = 195169) B195169
theorem B555149 : Blo 171799 555149 := bstep (se 3 (by rfl) ⟨104090, by rfl⟩ : syracuseStep 555149 = 208181) B208181
theorem B260243 : Blo 171799 260243 := bstep (se 1 (by rfl) ⟨195182, by rfl⟩ : syracuseStep 260243 = 390365) B390365
theorem B260273 : Blo 171799 260273 := bstep (se 2 (by rfl) ⟨97602, by rfl⟩ : syracuseStep 260273 = 195205) B195205
theorem B194755 : Blo 171799 194755 := bstep (se 1 (by rfl) ⟨146066, by rfl⟩ : syracuseStep 194755 = 292133) B292133
theorem B260291 : Blo 171799 260291 := bstep (se 1 (by rfl) ⟨195218, by rfl⟩ : syracuseStep 260291 = 390437) B390437
theorem B260321 : Blo 171799 260321 := bstep (se 2 (by rfl) ⟨97620, by rfl⟩ : syracuseStep 260321 = 195241) B195241
theorem B293105 : Blo 171799 293105 := bstep (se 2 (by rfl) ⟨109914, by rfl⟩ : syracuseStep 293105 = 219829) B219829
theorem B391409 : Blo 171799 391409 := bstep (se 2 (by rfl) ⟨146778, by rfl⟩ : syracuseStep 391409 = 293557) B293557
theorem B260339 : Blo 171799 260339 := bstep (se 1 (by rfl) ⟨195254, by rfl⟩ : syracuseStep 260339 = 390509) B390509
theorem B391427 : Blo 171799 391427 := bstep (se 1 (by rfl) ⟨293570, by rfl⟩ : syracuseStep 391427 = 587141) B587141
theorem B260369 : Blo 171799 260369 := bstep (se 2 (by rfl) ⟨97638, by rfl⟩ : syracuseStep 260369 = 195277) B195277
theorem B260387 : Blo 171799 260387 := bstep (se 1 (by rfl) ⟨195290, by rfl⟩ : syracuseStep 260387 = 390581) B390581
theorem B260417 : Blo 171799 260417 := bstep (se 2 (by rfl) ⟨97656, by rfl⟩ : syracuseStep 260417 = 195313) B195313
theorem B588113 : Blo 171799 588113 := bstep (se 2 (by rfl) ⟨220542, by rfl⟩ : syracuseStep 588113 = 441085) B441085
theorem B194899 : Blo 171799 194899 := bstep (se 1 (by rfl) ⟨146174, by rfl⟩ : syracuseStep 194899 = 292349) B292349
theorem B260435 : Blo 171799 260435 := bstep (se 1 (by rfl) ⟨195326, by rfl⟩ : syracuseStep 260435 = 390653) B390653
theorem B260465 : Blo 171799 260465 := bstep (se 2 (by rfl) ⟨97674, by rfl⟩ : syracuseStep 260465 = 195349) B195349
theorem B293233 : Blo 171799 293233 := bstep (se 2 (by rfl) ⟨109962, by rfl⟩ : syracuseStep 293233 = 219925) B219925
theorem B260483 : Blo 171799 260483 := bstep (se 1 (by rfl) ⟨195362, by rfl⟩ : syracuseStep 260483 = 390725) B390725
theorem B293267 : Blo 171799 293267 := bstep (se 1 (by rfl) ⟨219950, by rfl⟩ : syracuseStep 293267 = 439901) B439901
theorem B260513 : Blo 171799 260513 := bstep (se 2 (by rfl) ⟨97692, by rfl⟩ : syracuseStep 260513 = 195385) B195385
theorem B260531 : Blo 171799 260531 := bstep (se 1 (by rfl) ⟨195398, by rfl⟩ : syracuseStep 260531 = 390797) B390797
theorem B260561 : Blo 171799 260561 := bstep (se 2 (by rfl) ⟨97710, by rfl⟩ : syracuseStep 260561 = 195421) B195421
theorem B195043 : Blo 171799 195043 := bstep (se 1 (by rfl) ⟨146282, by rfl⟩ : syracuseStep 195043 = 292565) B292565
theorem B260579 : Blo 171799 260579 := bstep (se 1 (by rfl) ⟨195434, by rfl⟩ : syracuseStep 260579 = 390869) B390869
theorem B227827 : Blo 171799 227827 := bstep (se 1 (by rfl) ⟨170870, by rfl⟩ : syracuseStep 227827 = 341741) B341741
theorem B260609 : Blo 171799 260609 := bstep (se 2 (by rfl) ⟨97728, by rfl⟩ : syracuseStep 260609 = 195457) B195457
theorem B391697 : Blo 171799 391697 := bstep (se 2 (by rfl) ⟨146886, by rfl⟩ : syracuseStep 391697 = 293773) B293773
theorem B260627 : Blo 171799 260627 := bstep (se 1 (by rfl) ⟨195470, by rfl⟩ : syracuseStep 260627 = 390941) B390941
theorem B293395 : Blo 171799 293395 := bstep (se 1 (by rfl) ⟨220046, by rfl⟩ : syracuseStep 293395 = 440093) B440093
theorem B391715 : Blo 171799 391715 := bstep (se 1 (by rfl) ⟨293786, by rfl⟩ : syracuseStep 391715 = 587573) B587573
theorem B260657 : Blo 171799 260657 := bstep (se 2 (by rfl) ⟨97746, by rfl⟩ : syracuseStep 260657 = 195493) B195493
theorem B260675 : Blo 171799 260675 := bstep (se 1 (by rfl) ⟨195506, by rfl⟩ : syracuseStep 260675 = 391013) B391013
theorem B326243 : Blo 171799 326243 := bstep (se 1 (by rfl) ⟨244682, by rfl⟩ : syracuseStep 326243 = 489365) B489365
theorem B1309283 : Blo 171799 1309283 := bstep (se 1 (by rfl) ⟨981962, by rfl⟩ : syracuseStep 1309283 = 1963925) B1963925
theorem B260705 : Blo 171799 260705 := bstep (se 2 (by rfl) ⟨97764, by rfl⟩ : syracuseStep 260705 = 195529) B195529
theorem B195187 : Blo 171799 195187 := bstep (se 1 (by rfl) ⟨146390, by rfl⟩ : syracuseStep 195187 = 292781) B292781
theorem B260723 : Blo 171799 260723 := bstep (se 1 (by rfl) ⟨195542, by rfl⟩ : syracuseStep 260723 = 391085) B391085
theorem B260753 : Blo 171799 260753 := bstep (se 2 (by rfl) ⟨97782, by rfl⟩ : syracuseStep 260753 = 195565) B195565
theorem B293537 : Blo 171799 293537 := bstep (se 2 (by rfl) ⟨110076, by rfl⟩ : syracuseStep 293537 = 220153) B220153
theorem B260771 : Blo 171799 260771 := bstep (se 1 (by rfl) ⟨195578, by rfl⟩ : syracuseStep 260771 = 391157) B391157
theorem B260801 : Blo 171799 260801 := bstep (se 2 (by rfl) ⟨97800, by rfl⟩ : syracuseStep 260801 = 195601) B195601
theorem B260819 : Blo 171799 260819 := bstep (se 1 (by rfl) ⟨195614, by rfl⟩ : syracuseStep 260819 = 391229) B391229
theorem B654065 : Blo 171799 654065 := bstep (se 2 (by rfl) ⟨245274, by rfl⟩ : syracuseStep 654065 = 490549) B490549
theorem B260849 : Blo 171799 260849 := bstep (se 2 (by rfl) ⟨97818, by rfl⟩ : syracuseStep 260849 = 195637) B195637
theorem B195331 : Blo 171799 195331 := bstep (se 1 (by rfl) ⟨146498, by rfl⟩ : syracuseStep 195331 = 292997) B292997
theorem B260867 : Blo 171799 260867 := bstep (se 1 (by rfl) ⟨195650, by rfl⟩ : syracuseStep 260867 = 391301) B391301
theorem B260897 : Blo 171799 260897 := bstep (se 2 (by rfl) ⟨97836, by rfl⟩ : syracuseStep 260897 = 195673) B195673
theorem B293665 : Blo 171799 293665 := bstep (se 2 (by rfl) ⟨110124, by rfl⟩ : syracuseStep 293665 = 220249) B220249
theorem B391985 : Blo 171799 391985 := bstep (se 2 (by rfl) ⟨146994, by rfl⟩ : syracuseStep 391985 = 293989) B293989
theorem B260915 : Blo 171799 260915 := bstep (se 1 (by rfl) ⟨195686, by rfl⟩ : syracuseStep 260915 = 391373) B391373
theorem B293699 : Blo 171799 293699 := bstep (se 1 (by rfl) ⟨220274, by rfl⟩ : syracuseStep 293699 = 440549) B440549
theorem B392003 : Blo 171799 392003 := bstep (se 1 (by rfl) ⟨294002, by rfl⟩ : syracuseStep 392003 = 588005) B588005
theorem B260945 : Blo 171799 260945 := bstep (se 2 (by rfl) ⟨97854, by rfl⟩ : syracuseStep 260945 = 195709) B195709
theorem B260963 : Blo 171799 260963 := bstep (se 1 (by rfl) ⟨195722, by rfl⟩ : syracuseStep 260963 = 391445) B391445
theorem B588653 : Blo 171799 588653 := bstep (se 3 (by rfl) ⟨110372, by rfl⟩ : syracuseStep 588653 = 220745) B220745
theorem B260993 : Blo 171799 260993 := bstep (se 2 (by rfl) ⟨97872, by rfl⟩ : syracuseStep 260993 = 195745) B195745
theorem B326531 : Blo 171799 326531 := bstep (se 1 (by rfl) ⟨244898, by rfl⟩ : syracuseStep 326531 = 489797) B489797
theorem B195475 : Blo 171799 195475 := bstep (se 1 (by rfl) ⟨146606, by rfl⟩ : syracuseStep 195475 = 293213) B293213
theorem B261011 : Blo 171799 261011 := bstep (se 1 (by rfl) ⟨195758, by rfl⟩ : syracuseStep 261011 = 391517) B391517
theorem B588707 : Blo 171799 588707 := bstep (se 1 (by rfl) ⟨441530, by rfl⟩ : syracuseStep 588707 = 883061) B883061
theorem B261041 : Blo 171799 261041 := bstep (se 2 (by rfl) ⟨97890, by rfl⟩ : syracuseStep 261041 = 195781) B195781
theorem B293827 : Blo 171799 293827 := bstep (se 1 (by rfl) ⟨220370, by rfl⟩ : syracuseStep 293827 = 440741) B440741
theorem B261059 : Blo 171799 261059 := bstep (se 1 (by rfl) ⟨195794, by rfl⟩ : syracuseStep 261059 = 391589) B391589
theorem B2489285 : Blo 171799 2489285 := bstep (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) B466741
theorem B261089 : Blo 171799 261089 := bstep (se 2 (by rfl) ⟨97908, by rfl⟩ : syracuseStep 261089 = 195817) B195817
theorem B490481 : Blo 171799 490481 := bstep (se 2 (by rfl) ⟨183930, by rfl⟩ : syracuseStep 490481 = 367861) B367861
theorem B261107 : Blo 171799 261107 := bstep (se 1 (by rfl) ⟨195830, by rfl⟩ : syracuseStep 261107 = 391661) B391661
theorem B261137 : Blo 171799 261137 := bstep (se 2 (by rfl) ⟨97926, by rfl⟩ : syracuseStep 261137 = 195853) B195853
theorem B195619 : Blo 171799 195619 := bstep (se 1 (by rfl) ⟨146714, by rfl⟩ : syracuseStep 195619 = 293429) B293429
theorem B261155 : Blo 171799 261155 := bstep (se 1 (by rfl) ⟨195866, by rfl⟩ : syracuseStep 261155 = 391733) B391733
theorem B293939 : Blo 171799 293939 := bstep (se 1 (by rfl) ⟨220454, by rfl⟩ : syracuseStep 293939 = 440909) B440909
theorem B261185 : Blo 171799 261185 := bstep (se 2 (by rfl) ⟨97944, by rfl⟩ : syracuseStep 261185 = 195889) B195889
theorem B293969 : Blo 171799 293969 := bstep (se 2 (by rfl) ⟨110238, by rfl⟩ : syracuseStep 293969 = 220477) B220477
theorem B392273 : Blo 171799 392273 := bstep (se 2 (by rfl) ⟨147102, by rfl⟩ : syracuseStep 392273 = 294205) B294205
theorem B261203 : Blo 171799 261203 := bstep (se 1 (by rfl) ⟨195902, by rfl⟩ : syracuseStep 261203 = 391805) B391805
theorem B392291 : Blo 171799 392291 := bstep (se 1 (by rfl) ⟨294218, by rfl⟩ : syracuseStep 392291 = 588437) B588437
theorem B261233 : Blo 171799 261233 := bstep (se 2 (by rfl) ⟨97962, by rfl⟩ : syracuseStep 261233 = 195925) B195925
theorem B261251 : Blo 171799 261251 := bstep (se 1 (by rfl) ⟨195938, by rfl⟩ : syracuseStep 261251 = 391877) B391877
theorem B261281 : Blo 171799 261281 := bstep (se 2 (by rfl) ⟨97980, by rfl⟩ : syracuseStep 261281 = 195961) B195961
theorem B588977 : Blo 171799 588977 := bstep (se 2 (by rfl) ⟨220866, by rfl⟩ : syracuseStep 588977 = 441733) B441733
theorem B195763 : Blo 171799 195763 := bstep (se 1 (by rfl) ⟨146822, by rfl⟩ : syracuseStep 195763 = 293645) B293645
theorem B261299 : Blo 171799 261299 := bstep (se 1 (by rfl) ⟨195974, by rfl⟩ : syracuseStep 261299 = 391949) B391949
theorem B261329 : Blo 171799 261329 := bstep (se 2 (by rfl) ⟨97998, by rfl⟩ : syracuseStep 261329 = 195997) B195997
theorem B294097 : Blo 171799 294097 := bstep (se 2 (by rfl) ⟨110286, by rfl⟩ : syracuseStep 294097 = 220573) B220573
theorem B261347 : Blo 171799 261347 := bstep (se 1 (by rfl) ⟨196010, by rfl⟩ : syracuseStep 261347 = 392021) B392021
theorem B294131 : Blo 171799 294131 := bstep (se 1 (by rfl) ⟨220598, by rfl⟩ : syracuseStep 294131 = 441197) B441197
theorem B261377 : Blo 171799 261377 := bstep (se 2 (by rfl) ⟨98016, by rfl⟩ : syracuseStep 261377 = 196033) B196033
theorem B261395 : Blo 171799 261395 := bstep (se 1 (by rfl) ⟨196046, by rfl⟩ : syracuseStep 261395 = 392093) B392093
theorem B261425 : Blo 171799 261425 := bstep (se 2 (by rfl) ⟨98034, by rfl⟩ : syracuseStep 261425 = 196069) B196069
theorem B949553 : Blo 171799 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B195907 : Blo 171799 195907 := bstep (se 1 (by rfl) ⟨146930, by rfl⟩ : syracuseStep 195907 = 293861) B293861
theorem B261443 : Blo 171799 261443 := bstep (se 1 (by rfl) ⟨196082, by rfl⟩ : syracuseStep 261443 = 392165) B392165
theorem B261473 : Blo 171799 261473 := bstep (se 2 (by rfl) ⟨98052, by rfl⟩ : syracuseStep 261473 = 196105) B196105
theorem B392561 : Blo 171799 392561 := bstep (se 2 (by rfl) ⟨147210, by rfl⟩ : syracuseStep 392561 = 294421) B294421
theorem B261491 : Blo 171799 261491 := bstep (se 1 (by rfl) ⟨196118, by rfl⟩ : syracuseStep 261491 = 392237) B392237
theorem B294259 : Blo 171799 294259 := bstep (se 1 (by rfl) ⟨220694, by rfl⟩ : syracuseStep 294259 = 441389) B441389
theorem B392579 : Blo 171799 392579 := bstep (se 1 (by rfl) ⟨294434, by rfl⟩ : syracuseStep 392579 = 588869) B588869
theorem B261521 : Blo 171799 261521 := bstep (se 2 (by rfl) ⟨98070, by rfl⟩ : syracuseStep 261521 = 196141) B196141
theorem B261539 : Blo 171799 261539 := bstep (se 1 (by rfl) ⟨196154, by rfl⟩ : syracuseStep 261539 = 392309) B392309
theorem B261569 : Blo 171799 261569 := bstep (se 2 (by rfl) ⟨98088, by rfl⟩ : syracuseStep 261569 = 196177) B196177
theorem B196051 : Blo 171799 196051 := bstep (se 1 (by rfl) ⟨147038, by rfl⟩ : syracuseStep 196051 = 294077) B294077
theorem B261587 : Blo 171799 261587 := bstep (se 1 (by rfl) ⟨196190, by rfl⟩ : syracuseStep 261587 = 392381) B392381
theorem B884195 : Blo 171799 884195 := bstep (se 1 (by rfl) ⟨663146, by rfl⟩ : syracuseStep 884195 = 1326293) B1326293
theorem B261617 : Blo 171799 261617 := bstep (se 2 (by rfl) ⟨98106, by rfl⟩ : syracuseStep 261617 = 196213) B196213
theorem B294401 : Blo 171799 294401 := bstep (se 2 (by rfl) ⟨110400, by rfl⟩ : syracuseStep 294401 = 220801) B220801
theorem B261635 : Blo 171799 261635 := bstep (se 1 (by rfl) ⟨196226, by rfl⟩ : syracuseStep 261635 = 392453) B392453
theorem B261665 : Blo 171799 261665 := bstep (se 2 (by rfl) ⟨98124, by rfl⟩ : syracuseStep 261665 = 196249) B196249
theorem B261683 : Blo 171799 261683 := bstep (se 1 (by rfl) ⟨196262, by rfl⟩ : syracuseStep 261683 = 392525) B392525
theorem B261713 : Blo 171799 261713 := bstep (se 2 (by rfl) ⟨98142, by rfl⟩ : syracuseStep 261713 = 196285) B196285
theorem B196195 : Blo 171799 196195 := bstep (se 1 (by rfl) ⟨147146, by rfl⟩ : syracuseStep 196195 = 294293) B294293
theorem B261731 : Blo 171799 261731 := bstep (se 1 (by rfl) ⟨196298, by rfl⟩ : syracuseStep 261731 = 392597) B392597
theorem B261761 : Blo 171799 261761 := bstep (se 2 (by rfl) ⟨98160, by rfl⟩ : syracuseStep 261761 = 196321) B196321
theorem B294529 : Blo 171799 294529 := bstep (se 2 (by rfl) ⟨110448, by rfl⟩ : syracuseStep 294529 = 220897) B220897
theorem B392849 : Blo 171799 392849 := bstep (se 2 (by rfl) ⟨147318, by rfl⟩ : syracuseStep 392849 = 294637) B294637
theorem B261779 : Blo 171799 261779 := bstep (se 1 (by rfl) ⟨196334, by rfl⟩ : syracuseStep 261779 = 392669) B392669
theorem B294563 : Blo 171799 294563 := bstep (se 1 (by rfl) ⟨220922, by rfl⟩ : syracuseStep 294563 = 441845) B441845
theorem B392867 : Blo 171799 392867 := bstep (se 1 (by rfl) ⟨294650, by rfl⟩ : syracuseStep 392867 = 589301) B589301
theorem B261809 : Blo 171799 261809 := bstep (se 2 (by rfl) ⟨98178, by rfl⟩ : syracuseStep 261809 = 196357) B196357
theorem B261827 : Blo 171799 261827 := bstep (se 1 (by rfl) ⟨196370, by rfl⟩ : syracuseStep 261827 = 392741) B392741
theorem B589517 : Blo 171799 589517 := bstep (se 3 (by rfl) ⟨110534, by rfl⟩ : syracuseStep 589517 = 221069) B221069
theorem B261857 : Blo 171799 261857 := bstep (se 2 (by rfl) ⟨98196, by rfl⟩ : syracuseStep 261857 = 196393) B196393
theorem B196339 : Blo 171799 196339 := bstep (se 1 (by rfl) ⟨147254, by rfl⟩ : syracuseStep 196339 = 294509) B294509
theorem B261875 : Blo 171799 261875 := bstep (se 1 (by rfl) ⟨196406, by rfl⟩ : syracuseStep 261875 = 392813) B392813
theorem B589571 : Blo 171799 589571 := bstep (se 1 (by rfl) ⟨442178, by rfl⟩ : syracuseStep 589571 = 884357) B884357
theorem B261905 : Blo 171799 261905 := bstep (se 2 (by rfl) ⟨98214, by rfl⟩ : syracuseStep 261905 = 196429) B196429
theorem B261923 : Blo 171799 261923 := bstep (se 1 (by rfl) ⟨196442, by rfl⟩ : syracuseStep 261923 = 392885) B392885
theorem B294691 : Blo 171799 294691 := bstep (se 1 (by rfl) ⟨221018, by rfl⟩ : syracuseStep 294691 = 442037) B442037
theorem B327473 : Blo 171799 327473 := bstep (se 2 (by rfl) ⟨122802, by rfl⟩ : syracuseStep 327473 = 245605) B245605
theorem B261953 : Blo 171799 261953 := bstep (se 2 (by rfl) ⟨98232, by rfl⟩ : syracuseStep 261953 = 196465) B196465
theorem B982853 : Blo 171799 982853 := bstep (se 4 (by rfl) ⟨92142, by rfl⟩ : syracuseStep 982853 = 184285) B184285
theorem B261971 : Blo 171799 261971 := bstep (se 1 (by rfl) ⟨196478, by rfl⟩ : syracuseStep 261971 = 392957) B392957
theorem B262001 : Blo 171799 262001 := bstep (se 2 (by rfl) ⟨98250, by rfl⟩ : syracuseStep 262001 = 196501) B196501
theorem B196483 : Blo 171799 196483 := bstep (se 1 (by rfl) ⟨147362, by rfl⟩ : syracuseStep 196483 = 294725) B294725
theorem B262019 : Blo 171799 262019 := bstep (se 1 (by rfl) ⟨196514, by rfl⟩ : syracuseStep 262019 = 393029) B393029
theorem B262049 : Blo 171799 262049 := bstep (se 2 (by rfl) ⟨98268, by rfl⟩ : syracuseStep 262049 = 196537) B196537
theorem B491437 : Blo 171799 491437 := bstep (se 3 (by rfl) ⟨92144, by rfl⟩ : syracuseStep 491437 = 184289) B184289
theorem B294833 : Blo 171799 294833 := bstep (se 2 (by rfl) ⟨110562, by rfl⟩ : syracuseStep 294833 = 221125) B221125
theorem B393137 : Blo 171799 393137 := bstep (se 2 (by rfl) ⟨147426, by rfl⟩ : syracuseStep 393137 = 294853) B294853
theorem B262067 : Blo 171799 262067 := bstep (se 1 (by rfl) ⟨196550, by rfl⟩ : syracuseStep 262067 = 393101) B393101
theorem B393155 : Blo 171799 393155 := bstep (se 1 (by rfl) ⟨294866, by rfl⟩ : syracuseStep 393155 = 589733) B589733
theorem B262097 : Blo 171799 262097 := bstep (se 2 (by rfl) ⟨98286, by rfl⟩ : syracuseStep 262097 = 196573) B196573
theorem B262115 : Blo 171799 262115 := bstep (se 1 (by rfl) ⟨196586, by rfl⟩ : syracuseStep 262115 = 393173) B393173
theorem B393227 : Blo 171799 393227 := bstep (se 1 (by rfl) ⟨294920, by rfl⟩ : syracuseStep 393227 = 589841) B589841
theorem B262169 : Blo 171799 262169 := bstep (se 2 (by rfl) ⟨98313, by rfl⟩ : syracuseStep 262169 = 196627) B196627
theorem B196663 : Blo 171799 196663 := bstep (se 1 (by rfl) ⟨147497, by rfl⟩ : syracuseStep 196663 = 294995) B294995
theorem B393281 : Blo 171799 393281 := bstep (se 2 (by rfl) ⟨147480, by rfl⟩ : syracuseStep 393281 = 294961) B294961
theorem B491609 : Blo 171799 491609 := bstep (se 2 (by rfl) ⟨184353, by rfl⟩ : syracuseStep 491609 = 368707) B368707
theorem B262283 : Blo 171799 262283 := bstep (se 1 (by rfl) ⟨196712, by rfl⟩ : syracuseStep 262283 = 393425) B393425
theorem B262295 : Blo 171799 262295 := bstep (se 1 (by rfl) ⟨196721, by rfl⟩ : syracuseStep 262295 = 393443) B393443
theorem B590003 : Blo 171799 590003 := bstep (se 1 (by rfl) ⟨442502, by rfl⟩ : syracuseStep 590003 = 885005) B885005
theorem B655553 : Blo 171799 655553 := bstep (se 2 (by rfl) ⟨245832, by rfl⟩ : syracuseStep 655553 = 491665) B491665
theorem B327883 : Blo 171799 327883 := bstep (se 1 (by rfl) ⟨245912, by rfl⟩ : syracuseStep 327883 = 491825) B491825
theorem B262361 : Blo 171799 262361 := bstep (se 2 (by rfl) ⟨98385, by rfl⟩ : syracuseStep 262361 = 196771) B196771
theorem B196843 : Blo 171799 196843 := bstep (se 1 (by rfl) ⟨147632, by rfl⟩ : syracuseStep 196843 = 295265) B295265
theorem B327959 : Blo 171799 327959 := bstep (se 1 (by rfl) ⟨245969, by rfl⟩ : syracuseStep 327959 = 491939) B491939
theorem B393497 : Blo 171799 393497 := bstep (se 2 (by rfl) ⟨147561, by rfl⟩ : syracuseStep 393497 = 295123) B295123
theorem B262475 : Blo 171799 262475 := bstep (se 1 (by rfl) ⟨196856, by rfl⟩ : syracuseStep 262475 = 393713) B393713
theorem B262487 : Blo 171799 262487 := bstep (se 1 (by rfl) ⟨196865, by rfl⟩ : syracuseStep 262487 = 393731) B393731
theorem B196951 : Blo 171799 196951 := bstep (se 1 (by rfl) ⟨147713, by rfl⟩ : syracuseStep 196951 = 295427) B295427
theorem B557405 : Blo 171799 557405 := bstep (se 3 (by rfl) ⟨104513, by rfl⟩ : syracuseStep 557405 = 209027) B209027
theorem B393587 : Blo 171799 393587 := bstep (se 1 (by rfl) ⟨295190, by rfl⟩ : syracuseStep 393587 = 590381) B590381
theorem B393623 : Blo 171799 393623 := bstep (se 1 (by rfl) ⟨295217, by rfl⟩ : syracuseStep 393623 = 590435) B590435
theorem B295319 : Blo 171799 295319 := bstep (se 1 (by rfl) ⟨221489, by rfl⟩ : syracuseStep 295319 = 442979) B442979
theorem B262553 : Blo 171799 262553 := bstep (se 2 (by rfl) ⟨98457, by rfl⟩ : syracuseStep 262553 = 196915) B196915
theorem B590273 : Blo 171799 590273 := bstep (se 2 (by rfl) ⟨221352, by rfl⟩ : syracuseStep 590273 = 442705) B442705
theorem B262667 : Blo 171799 262667 := bstep (se 1 (by rfl) ⟨197000, by rfl⟩ : syracuseStep 262667 = 394001) B394001
theorem B197131 : Blo 171799 197131 := bstep (se 1 (by rfl) ⟨147848, by rfl⟩ : syracuseStep 197131 = 295697) B295697
theorem B295447 : Blo 171799 295447 := bstep (se 1 (by rfl) ⟨221585, by rfl⟩ : syracuseStep 295447 = 443171) B443171
theorem B262679 : Blo 171799 262679 := bstep (se 1 (by rfl) ⟨197009, by rfl⟩ : syracuseStep 262679 = 394019) B394019
theorem B393803 : Blo 171799 393803 := bstep (se 1 (by rfl) ⟨295352, by rfl⟩ : syracuseStep 393803 = 590705) B590705
theorem B262745 : Blo 171799 262745 := bstep (se 2 (by rfl) ⟨98529, by rfl⟩ : syracuseStep 262745 = 197059) B197059
theorem B197239 : Blo 171799 197239 := bstep (se 1 (by rfl) ⟨147929, by rfl⟩ : syracuseStep 197239 = 295859) B295859
theorem B393857 : Blo 171799 393857 := bstep (se 2 (by rfl) ⟨147696, by rfl⟩ : syracuseStep 393857 = 295393) B295393
theorem B2130583 : Blo 171799 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B262859 : Blo 171799 262859 := bstep (se 1 (by rfl) ⟨197144, by rfl⟩ : syracuseStep 262859 = 394289) B394289
theorem B262871 : Blo 171799 262871 := bstep (se 1 (by rfl) ⟨197153, by rfl⟩ : syracuseStep 262871 = 394307) B394307
theorem B262937 : Blo 171799 262937 := bstep (se 2 (by rfl) ⟨98601, by rfl⟩ : syracuseStep 262937 = 197203) B197203
theorem B197419 : Blo 171799 197419 := bstep (se 1 (by rfl) ⟨148064, by rfl⟩ : syracuseStep 197419 = 296129) B296129
theorem B787265 : Blo 171799 787265 := bstep (se 2 (by rfl) ⟨295224, by rfl⟩ : syracuseStep 787265 = 590449) B590449
theorem B394073 : Blo 171799 394073 := bstep (se 2 (by rfl) ⟨147777, by rfl⟩ : syracuseStep 394073 = 295555) B295555
theorem B656221 : Blo 171799 656221 := bstep (se 3 (by rfl) ⟨123041, by rfl⟩ : syracuseStep 656221 = 246083) B246083
theorem B263051 : Blo 171799 263051 := bstep (se 1 (by rfl) ⟨197288, by rfl⟩ : syracuseStep 263051 = 394577) B394577
theorem B263063 : Blo 171799 263063 := bstep (se 1 (by rfl) ⟨197297, by rfl⟩ : syracuseStep 263063 = 394595) B394595
theorem B197527 : Blo 171799 197527 := bstep (se 1 (by rfl) ⟨148145, by rfl⟩ : syracuseStep 197527 = 296291) B296291
theorem B328627 : Blo 171799 328627 := bstep (se 1 (by rfl) ⟨246470, by rfl⟩ : syracuseStep 328627 = 492941) B492941
theorem B394163 : Blo 171799 394163 := bstep (se 1 (by rfl) ⟨295622, by rfl⟩ : syracuseStep 394163 = 591245) B591245
theorem B394199 : Blo 171799 394199 := bstep (se 1 (by rfl) ⟨295649, by rfl⟩ : syracuseStep 394199 = 591299) B591299
theorem B263129 : Blo 171799 263129 := bstep (se 2 (by rfl) ⟨98673, by rfl⟩ : syracuseStep 263129 = 197347) B197347
theorem B590813 : Blo 171799 590813 := bstep (se 3 (by rfl) ⟨110777, by rfl⟩ : syracuseStep 590813 = 221555) B221555
theorem B263243 : Blo 171799 263243 := bstep (se 1 (by rfl) ⟨197432, by rfl⟩ : syracuseStep 263243 = 394865) B394865
theorem B197707 : Blo 171799 197707 := bstep (se 1 (by rfl) ⟨148280, by rfl⟩ : syracuseStep 197707 = 296561) B296561
theorem B263255 : Blo 171799 263255 := bstep (se 1 (by rfl) ⟨197441, by rfl⟩ : syracuseStep 263255 = 394883) B394883
theorem B623705 : Blo 171799 623705 := bstep (se 2 (by rfl) ⟨233889, by rfl⟩ : syracuseStep 623705 = 467779) B467779
theorem B394379 : Blo 171799 394379 := bstep (se 1 (by rfl) ⟨295784, by rfl⟩ : syracuseStep 394379 = 591569) B591569
theorem B296075 : Blo 171799 296075 := bstep (se 1 (by rfl) ⟨222056, by rfl⟩ : syracuseStep 296075 = 444113) B444113
theorem B328855 : Blo 171799 328855 := bstep (se 1 (by rfl) ⟨246641, by rfl⟩ : syracuseStep 328855 = 493283) B493283
theorem B263321 : Blo 171799 263321 := bstep (se 2 (by rfl) ⟨98745, by rfl⟩ : syracuseStep 263321 = 197491) B197491
theorem B394433 : Blo 171799 394433 := bstep (se 2 (by rfl) ⟨147912, by rfl⟩ : syracuseStep 394433 = 295825) B295825
theorem B885977 : Blo 171799 885977 := bstep (se 2 (by rfl) ⟨332241, by rfl⟩ : syracuseStep 885977 = 664483) B664483
theorem B328961 : Blo 171799 328961 := bstep (se 2 (by rfl) ⟨123360, by rfl⟩ : syracuseStep 328961 = 246721) B246721
theorem B296203 : Blo 171799 296203 := bstep (se 1 (by rfl) ⟨222152, by rfl⟩ : syracuseStep 296203 = 444305) B444305
theorem B263435 : Blo 171799 263435 := bstep (se 1 (by rfl) ⟨197576, by rfl⟩ : syracuseStep 263435 = 395153) B395153
theorem B263447 : Blo 171799 263447 := bstep (se 1 (by rfl) ⟨197585, by rfl⟩ : syracuseStep 263447 = 395171) B395171
theorem B263513 : Blo 171799 263513 := bstep (se 2 (by rfl) ⟨98817, by rfl⟩ : syracuseStep 263513 = 197635) B197635
theorem B329113 : Blo 171799 329113 := bstep (se 2 (by rfl) ⟨123417, by rfl⟩ : syracuseStep 329113 = 246835) B246835
theorem B394649 : Blo 171799 394649 := bstep (se 2 (by rfl) ⟨147993, by rfl⟩ : syracuseStep 394649 = 295987) B295987
theorem B296345 : Blo 171799 296345 := bstep (se 2 (by rfl) ⟨111129, by rfl⟩ : syracuseStep 296345 = 222259) B222259
theorem B263627 : Blo 171799 263627 := bstep (se 1 (by rfl) ⟨197720, by rfl⟩ : syracuseStep 263627 = 395441) B395441
theorem B263639 : Blo 171799 263639 := bstep (se 1 (by rfl) ⟨197729, by rfl⟩ : syracuseStep 263639 = 395459) B395459
theorem B394739 : Blo 171799 394739 := bstep (se 1 (by rfl) ⟨296054, by rfl⟩ : syracuseStep 394739 = 592109) B592109
theorem B394775 : Blo 171799 394775 := bstep (se 1 (by rfl) ⟨296081, by rfl⟩ : syracuseStep 394775 = 592163) B592163
theorem B296473 : Blo 171799 296473 := bstep (se 2 (by rfl) ⟨111177, by rfl⟩ : syracuseStep 296473 = 222355) B222355
theorem B1410605 : Blo 171799 1410605 := bstep (se 3 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 1410605 = 528977) B528977
theorem B493249 : Blo 171799 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B394955 : Blo 171799 394955 := bstep (se 1 (by rfl) ⟨296216, by rfl⟩ : syracuseStep 394955 = 592433) B592433
theorem B395009 : Blo 171799 395009 := bstep (se 2 (by rfl) ⟨148128, by rfl⟩ : syracuseStep 395009 = 296257) B296257
theorem B395225 : Blo 171799 395225 := bstep (se 2 (by rfl) ⟨148209, by rfl⟩ : syracuseStep 395225 = 296419) B296419
theorem B395315 : Blo 171799 395315 := bstep (se 1 (by rfl) ⟨296486, by rfl⟩ : syracuseStep 395315 = 592973) B592973
theorem B591947 : Blo 171799 591947 := bstep (se 1 (by rfl) ⟨443960, by rfl⟩ : syracuseStep 591947 = 887921) B887921
theorem B395351 : Blo 171799 395351 := bstep (se 1 (by rfl) ⟨296513, by rfl⟩ : syracuseStep 395351 = 593027) B593027
theorem B657497 : Blo 171799 657497 := bstep (se 2 (by rfl) ⟨246561, by rfl⟩ : syracuseStep 657497 = 493123) B493123
theorem B1050803 : Blo 171799 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B395531 : Blo 171799 395531 := bstep (se 1 (by rfl) ⟨296648, by rfl⟩ : syracuseStep 395531 = 593297) B593297
theorem B592217 : Blo 171799 592217 := bstep (se 2 (by rfl) ⟨222081, by rfl⟩ : syracuseStep 592217 = 444163) B444163
theorem B5048689 : Blo 171799 5048689 := bstep (se 2 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 5048689 = 3786517) B3786517
theorem B330419 : Blo 171799 330419 := bstep (se 1 (by rfl) ⟨247814, by rfl⟩ : syracuseStep 330419 = 495629) B495629
theorem B887597 : Blo 171799 887597 := bstep (se 3 (by rfl) ⟨166424, by rfl⟩ : syracuseStep 887597 = 332849) B332849
theorem B953153 : Blo 171799 953153 := bstep (se 2 (by rfl) ⟨357432, by rfl⟩ : syracuseStep 953153 = 714865) B714865
theorem B330571 : Blo 171799 330571 := bstep (se 1 (by rfl) ⟨247928, by rfl⟩ : syracuseStep 330571 = 495857) B495857
theorem B592919 : Blo 171799 592919 := bstep (se 1 (by rfl) ⟨444689, by rfl⟩ : syracuseStep 592919 = 889379) B889379
theorem B330905 : Blo 171799 330905 := bstep (se 2 (by rfl) ⟨124089, by rfl⟩ : syracuseStep 330905 = 248179) B248179
theorem B494923 : Blo 171799 494923 := bstep (se 1 (by rfl) ⟨371192, by rfl⟩ : syracuseStep 494923 = 742385) B742385
theorem B986519 : Blo 171799 986519 := bstep (se 1 (by rfl) ⟨739889, by rfl⟩ : syracuseStep 986519 = 1479779) B1479779
theorem B527809 : Blo 171799 527809 := bstep (se 2 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 527809 = 395857) B395857
theorem B1969757 : Blo 171799 1969757 := bstep (se 3 (by rfl) ⟨369329, by rfl⟩ : syracuseStep 1969757 = 738659) B738659
theorem B495197 : Blo 171799 495197 := bstep (se 3 (by rfl) ⟨92849, by rfl⟩ : syracuseStep 495197 = 185699) B185699
theorem B659123 : Blo 171799 659123 := bstep (se 1 (by rfl) ⟨494342, by rfl⟩ : syracuseStep 659123 = 988685) B988685
theorem B659137 : Blo 171799 659137 := bstep (se 2 (by rfl) ⟨247176, by rfl⟩ : syracuseStep 659137 = 494353) B494353
theorem B331543 : Blo 171799 331543 := bstep (se 1 (by rfl) ⟨248657, by rfl⟩ : syracuseStep 331543 = 497315) B497315
theorem B266009 : Blo 171799 266009 := bstep (se 2 (by rfl) ⟨99753, by rfl⟩ : syracuseStep 266009 = 199507) B199507
theorem B1412939 : Blo 171799 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B1609763 : Blo 171799 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B8458769 : Blo 171799 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B397847 : Blo 171799 397847 := bstep (se 1 (by rfl) ⟨298385, by rfl⟩ : syracuseStep 397847 = 596771) B596771
theorem B332363 : Blo 171799 332363 := bstep (se 1 (by rfl) ⟨249272, by rfl⟩ : syracuseStep 332363 = 498545) B498545
theorem B332417 : Blo 171799 332417 := bstep (se 2 (by rfl) ⟨124656, by rfl⟩ : syracuseStep 332417 = 249313) B249313
theorem B1315601 : Blo 171799 1315601 := bstep (se 2 (by rfl) ⟨493350, by rfl⟩ : syracuseStep 1315601 = 986701) B986701
theorem B627659 : Blo 171799 627659 := bstep (se 1 (by rfl) ⟨470744, by rfl⟩ : syracuseStep 627659 = 941489) B941489
theorem B791569 : Blo 171799 791569 := bstep (se 2 (by rfl) ⟨296838, by rfl⟩ : syracuseStep 791569 = 593677) B593677
theorem B1348643 : Blo 171799 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B201943 : Blo 171799 201943 := bstep (se 1 (by rfl) ⟨151457, by rfl⟩ : syracuseStep 201943 = 302915) B302915
theorem B988433 : Blo 171799 988433 := bstep (se 2 (by rfl) ⟨370662, by rfl⟩ : syracuseStep 988433 = 741325) B741325
theorem B2987441 : Blo 171799 2987441 := bstep (se 2 (by rfl) ⟨1120290, by rfl⟩ : syracuseStep 2987441 = 2240581) B2240581
theorem B2233817 : Blo 171799 2233817 := bstep (se 2 (by rfl) ⟨837681, by rfl⟩ : syracuseStep 2233817 = 1675363) B1675363
theorem B333335 : Blo 171799 333335 := bstep (se 1 (by rfl) ⟨250001, by rfl⟩ : syracuseStep 333335 = 500003) B500003
theorem B792139 : Blo 171799 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B661067 : Blo 171799 661067 := bstep (se 1 (by rfl) ⟨495800, by rfl⟩ : syracuseStep 661067 = 991601) B991601
theorem B661081 : Blo 171799 661081 := bstep (se 2 (by rfl) ⟨247905, by rfl⟩ : syracuseStep 661081 = 495811) B495811
theorem B497497 : Blo 171799 497497 := bstep (se 2 (by rfl) ⟨186561, by rfl⟩ : syracuseStep 497497 = 373123) B373123
theorem B11409329 : Blo 171799 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B202775 : Blo 171799 202775 := bstep (se 1 (by rfl) ⟨152081, by rfl⟩ : syracuseStep 202775 = 304163) B304163
theorem B399745 : Blo 171799 399745 := bstep (se 2 (by rfl) ⟨149904, by rfl⟩ : syracuseStep 399745 = 299809) B299809
theorem B498113 : Blo 171799 498113 := bstep (se 2 (by rfl) ⟨186792, by rfl⟩ : syracuseStep 498113 = 373585) B373585
theorem B662039 : Blo 171799 662039 := bstep (se 1 (by rfl) ⟨496529, by rfl⟩ : syracuseStep 662039 = 993059) B993059
theorem B1481489 : Blo 171799 1481489 := bstep (se 2 (by rfl) ⟨555558, by rfl⟩ : syracuseStep 1481489 = 1111117) B1111117
theorem B367553 : Blo 171799 367553 := bstep (se 2 (by rfl) ⟨137832, by rfl⟩ : syracuseStep 367553 = 275665) B275665
theorem B760769 : Blo 171799 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B662593 : Blo 171799 662593 := bstep (se 2 (by rfl) ⟨248472, by rfl⟩ : syracuseStep 662593 = 496945) B496945
theorem B629849 : Blo 171799 629849 := bstep (se 2 (by rfl) ⟨236193, by rfl⟩ : syracuseStep 629849 = 472387) B472387
theorem B367895 : Blo 171799 367895 := bstep (se 1 (by rfl) ⟨275921, by rfl⟩ : syracuseStep 367895 = 551843) B551843
theorem B400819 : Blo 171799 400819 := bstep (se 1 (by rfl) ⟨300614, by rfl⟩ : syracuseStep 400819 = 601229) B601229
theorem B826841 : Blo 171799 826841 := bstep (se 2 (by rfl) ⟨310065, by rfl⟩ : syracuseStep 826841 = 620131) B620131
theorem B630289 : Blo 171799 630289 := bstep (se 2 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 630289 = 472717) B472717
theorem B4955741 : Blo 171799 4955741 := bstep (se 3 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 4955741 = 1858403) B1858403
theorem B663299 : Blo 171799 663299 := bstep (se 1 (by rfl) ⟨497474, by rfl⟩ : syracuseStep 663299 = 994949) B994949
theorem B171799 : Blo 171799 171799 := bstep (se 1 (by rfl) ⟨128849, by rfl⟩ : syracuseStep 171799 = 257699) B257699
theorem B171819 : Blo 171799 171819 := bstep (se 1 (by rfl) ⟨128864, by rfl⟩ : syracuseStep 171819 = 257729) B257729
theorem B171831 : Blo 171799 171831 := bstep (se 1 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 171831 = 257747) B257747
theorem B1122113 : Blo 171799 1122113 := bstep (se 2 (by rfl) ⟨420792, by rfl⟩ : syracuseStep 1122113 = 841585) B841585
theorem B171851 : Blo 171799 171851 := bstep (se 1 (by rfl) ⟨128888, by rfl⟩ : syracuseStep 171851 = 257777) B257777
theorem B368459 : Blo 171799 368459 := bstep (se 1 (by rfl) ⟨276344, by rfl⟩ : syracuseStep 368459 = 552689) B552689
theorem B171863 : Blo 171799 171863 := bstep (se 1 (by rfl) ⟨128897, by rfl⟩ : syracuseStep 171863 = 257795) B257795
theorem B171883 : Blo 171799 171883 := bstep (se 1 (by rfl) ⟨128912, by rfl⟩ : syracuseStep 171883 = 257825) B257825
theorem B171895 : Blo 171799 171895 := bstep (se 1 (by rfl) ⟨128921, by rfl⟩ : syracuseStep 171895 = 257843) B257843
theorem B171915 : Blo 171799 171915 := bstep (se 1 (by rfl) ⟨128936, by rfl⟩ : syracuseStep 171915 = 257873) B257873
theorem B171927 : Blo 171799 171927 := bstep (se 1 (by rfl) ⟨128945, by rfl⟩ : syracuseStep 171927 = 257891) B257891
theorem B171947 : Blo 171799 171947 := bstep (se 1 (by rfl) ⟨128960, by rfl⟩ : syracuseStep 171947 = 257921) B257921
theorem B171959 : Blo 171799 171959 := bstep (se 1 (by rfl) ⟨128969, by rfl⟩ : syracuseStep 171959 = 257939) B257939
theorem B171979 : Blo 171799 171979 := bstep (se 1 (by rfl) ⟨128984, by rfl⟩ : syracuseStep 171979 = 257969) B257969
theorem B171991 : Blo 171799 171991 := bstep (se 1 (by rfl) ⟨128993, by rfl⟩ : syracuseStep 171991 = 257987) B257987
theorem B172011 : Blo 171799 172011 := bstep (se 1 (by rfl) ⟨129008, by rfl⟩ : syracuseStep 172011 = 258017) B258017
theorem B172023 : Blo 171799 172023 := bstep (se 1 (by rfl) ⟨129017, by rfl⟩ : syracuseStep 172023 = 258035) B258035
theorem B172043 : Blo 171799 172043 := bstep (se 1 (by rfl) ⟨129032, by rfl⟩ : syracuseStep 172043 = 258065) B258065
theorem B172055 : Blo 171799 172055 := bstep (se 1 (by rfl) ⟨129041, by rfl⟩ : syracuseStep 172055 = 258083) B258083
theorem B172075 : Blo 171799 172075 := bstep (se 1 (by rfl) ⟨129056, by rfl⟩ : syracuseStep 172075 = 258113) B258113
theorem B172087 : Blo 171799 172087 := bstep (se 1 (by rfl) ⟨129065, by rfl⟩ : syracuseStep 172087 = 258131) B258131
theorem B172107 : Blo 171799 172107 := bstep (se 1 (by rfl) ⟨129080, by rfl⟩ : syracuseStep 172107 = 258161) B258161
theorem B172119 : Blo 171799 172119 := bstep (se 1 (by rfl) ⟨129089, by rfl⟩ : syracuseStep 172119 = 258179) B258179
theorem B1351781 : Blo 171799 1351781 := bstep (se 4 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 1351781 = 253459) B253459
theorem B172139 : Blo 171799 172139 := bstep (se 1 (by rfl) ⟨129104, by rfl⟩ : syracuseStep 172139 = 258209) B258209
theorem B172151 : Blo 171799 172151 := bstep (se 1 (by rfl) ⟨129113, by rfl⟩ : syracuseStep 172151 = 258227) B258227
theorem B172171 : Blo 171799 172171 := bstep (se 1 (by rfl) ⟨129128, by rfl⟩ : syracuseStep 172171 = 258257) B258257
theorem B172183 : Blo 171799 172183 := bstep (se 1 (by rfl) ⟨129137, by rfl⟩ : syracuseStep 172183 = 258275) B258275
theorem B172203 : Blo 171799 172203 := bstep (se 1 (by rfl) ⟨129152, by rfl⟩ : syracuseStep 172203 = 258305) B258305
theorem B172215 : Blo 171799 172215 := bstep (se 1 (by rfl) ⟨129161, by rfl⟩ : syracuseStep 172215 = 258323) B258323
theorem B172235 : Blo 171799 172235 := bstep (se 1 (by rfl) ⟨129176, by rfl⟩ : syracuseStep 172235 = 258353) B258353
theorem B172247 : Blo 171799 172247 := bstep (se 1 (by rfl) ⟨129185, by rfl⟩ : syracuseStep 172247 = 258371) B258371
theorem B172267 : Blo 171799 172267 := bstep (se 1 (by rfl) ⟨129200, by rfl⟩ : syracuseStep 172267 = 258401) B258401
theorem B172279 : Blo 171799 172279 := bstep (se 1 (by rfl) ⟨129209, by rfl⟩ : syracuseStep 172279 = 258419) B258419
theorem B172299 : Blo 171799 172299 := bstep (se 1 (by rfl) ⟨129224, by rfl⟩ : syracuseStep 172299 = 258449) B258449
theorem B172311 : Blo 171799 172311 := bstep (se 1 (by rfl) ⟨129233, by rfl⟩ : syracuseStep 172311 = 258467) B258467
theorem B172331 : Blo 171799 172331 := bstep (se 1 (by rfl) ⟨129248, by rfl⟩ : syracuseStep 172331 = 258497) B258497
theorem B172343 : Blo 171799 172343 := bstep (se 1 (by rfl) ⟨129257, by rfl⟩ : syracuseStep 172343 = 258515) B258515
theorem B172363 : Blo 171799 172363 := bstep (se 1 (by rfl) ⟨129272, by rfl⟩ : syracuseStep 172363 = 258545) B258545
theorem B172375 : Blo 171799 172375 := bstep (se 1 (by rfl) ⟨129281, by rfl⟩ : syracuseStep 172375 = 258563) B258563
theorem B172395 : Blo 171799 172395 := bstep (se 1 (by rfl) ⟨129296, by rfl⟩ : syracuseStep 172395 = 258593) B258593
theorem B172407 : Blo 171799 172407 := bstep (se 1 (by rfl) ⟨129305, by rfl⟩ : syracuseStep 172407 = 258611) B258611
theorem B172427 : Blo 171799 172427 := bstep (se 1 (by rfl) ⟨129320, by rfl⟩ : syracuseStep 172427 = 258641) B258641
theorem B172439 : Blo 171799 172439 := bstep (se 1 (by rfl) ⟨129329, by rfl⟩ : syracuseStep 172439 = 258659) B258659
theorem B1057175 : Blo 171799 1057175 := bstep (se 1 (by rfl) ⟨792881, by rfl⟩ : syracuseStep 1057175 = 1585763) B1585763
theorem B369049 : Blo 171799 369049 := bstep (se 2 (by rfl) ⟨138393, by rfl⟩ : syracuseStep 369049 = 276787) B276787
theorem B172459 : Blo 171799 172459 := bstep (se 1 (by rfl) ⟨129344, by rfl⟩ : syracuseStep 172459 = 258689) B258689
theorem B172471 : Blo 171799 172471 := bstep (se 1 (by rfl) ⟨129353, by rfl⟩ : syracuseStep 172471 = 258707) B258707
theorem B172491 : Blo 171799 172491 := bstep (se 1 (by rfl) ⟨129368, by rfl⟩ : syracuseStep 172491 = 258737) B258737
theorem B172503 : Blo 171799 172503 := bstep (se 1 (by rfl) ⟨129377, by rfl⟩ : syracuseStep 172503 = 258755) B258755
theorem B500185 : Blo 171799 500185 := bstep (se 2 (by rfl) ⟨187569, by rfl⟩ : syracuseStep 500185 = 375139) B375139
theorem B172523 : Blo 171799 172523 := bstep (se 1 (by rfl) ⟨129392, by rfl⟩ : syracuseStep 172523 = 258785) B258785
theorem B172535 : Blo 171799 172535 := bstep (se 1 (by rfl) ⟨129401, by rfl⟩ : syracuseStep 172535 = 258803) B258803
theorem B664067 : Blo 171799 664067 := bstep (se 1 (by rfl) ⟨498050, by rfl⟩ : syracuseStep 664067 = 996101) B996101
theorem B172555 : Blo 171799 172555 := bstep (se 1 (by rfl) ⟨129416, by rfl⟩ : syracuseStep 172555 = 258833) B258833
theorem B172567 : Blo 171799 172567 := bstep (se 1 (by rfl) ⟨129425, by rfl⟩ : syracuseStep 172567 = 258851) B258851
theorem B172587 : Blo 171799 172587 := bstep (se 1 (by rfl) ⟨129440, by rfl⟩ : syracuseStep 172587 = 258881) B258881
theorem B172599 : Blo 171799 172599 := bstep (se 1 (by rfl) ⟨129449, by rfl⟩ : syracuseStep 172599 = 258899) B258899
theorem B1319489 : Blo 171799 1319489 := bstep (se 2 (by rfl) ⟨494808, by rfl⟩ : syracuseStep 1319489 = 989617) B989617
theorem B172619 : Blo 171799 172619 := bstep (se 1 (by rfl) ⟨129464, by rfl⟩ : syracuseStep 172619 = 258929) B258929
theorem B598603 : Blo 171799 598603 := bstep (se 1 (by rfl) ⟨448952, by rfl⟩ : syracuseStep 598603 = 897905) B897905
theorem B172631 : Blo 171799 172631 := bstep (se 1 (by rfl) ⟨129473, by rfl⟩ : syracuseStep 172631 = 258947) B258947
theorem B3711581 : Blo 171799 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B172651 : Blo 171799 172651 := bstep (se 1 (by rfl) ⟨129488, by rfl⟩ : syracuseStep 172651 = 258977) B258977
theorem B172663 : Blo 171799 172663 := bstep (se 1 (by rfl) ⟨129497, by rfl⟩ : syracuseStep 172663 = 258995) B258995
theorem B172683 : Blo 171799 172683 := bstep (se 1 (by rfl) ⟨129512, by rfl⟩ : syracuseStep 172683 = 259025) B259025
theorem B172695 : Blo 171799 172695 := bstep (se 1 (by rfl) ⟨129521, by rfl⟩ : syracuseStep 172695 = 259043) B259043
theorem B303769 : Blo 171799 303769 := bstep (se 2 (by rfl) ⟨113913, by rfl⟩ : syracuseStep 303769 = 227827) B227827
theorem B172715 : Blo 171799 172715 := bstep (se 1 (by rfl) ⟨129536, by rfl⟩ : syracuseStep 172715 = 259073) B259073
theorem B172727 : Blo 171799 172727 := bstep (se 1 (by rfl) ⟨129545, by rfl⟩ : syracuseStep 172727 = 259091) B259091
theorem B172747 : Blo 171799 172747 := bstep (se 1 (by rfl) ⟨129560, by rfl⟩ : syracuseStep 172747 = 259121) B259121
theorem B172759 : Blo 171799 172759 := bstep (se 1 (by rfl) ⟨129569, by rfl⟩ : syracuseStep 172759 = 259139) B259139
theorem B172779 : Blo 171799 172779 := bstep (se 1 (by rfl) ⟨129584, by rfl⟩ : syracuseStep 172779 = 259169) B259169
theorem B172791 : Blo 171799 172791 := bstep (se 1 (by rfl) ⟨129593, by rfl⟩ : syracuseStep 172791 = 259187) B259187
theorem B172811 : Blo 171799 172811 := bstep (se 1 (by rfl) ⟨129608, by rfl⟩ : syracuseStep 172811 = 259217) B259217
theorem B172823 : Blo 171799 172823 := bstep (se 1 (by rfl) ⟨129617, by rfl⟩ : syracuseStep 172823 = 259235) B259235
theorem B172843 : Blo 171799 172843 := bstep (se 1 (by rfl) ⟨129632, by rfl⟩ : syracuseStep 172843 = 259265) B259265
theorem B172855 : Blo 171799 172855 := bstep (se 1 (by rfl) ⟨129641, by rfl⟩ : syracuseStep 172855 = 259283) B259283
theorem B172875 : Blo 171799 172875 := bstep (se 1 (by rfl) ⟨129656, by rfl⟩ : syracuseStep 172875 = 259313) B259313
theorem B172887 : Blo 171799 172887 := bstep (se 1 (by rfl) ⟨129665, by rfl⟩ : syracuseStep 172887 = 259331) B259331
theorem B500573 : Blo 171799 500573 := bstep (se 3 (by rfl) ⟨93857, by rfl⟩ : syracuseStep 500573 = 187715) B187715
theorem B172907 : Blo 171799 172907 := bstep (se 1 (by rfl) ⟨129680, by rfl⟩ : syracuseStep 172907 = 259361) B259361
theorem B172919 : Blo 171799 172919 := bstep (se 1 (by rfl) ⟨129689, by rfl⟩ : syracuseStep 172919 = 259379) B259379
theorem B172939 : Blo 171799 172939 := bstep (se 1 (by rfl) ⟨129704, by rfl⟩ : syracuseStep 172939 = 259409) B259409
theorem B172951 : Blo 171799 172951 := bstep (se 1 (by rfl) ⟨129713, by rfl⟩ : syracuseStep 172951 = 259427) B259427
theorem B172971 : Blo 171799 172971 := bstep (se 1 (by rfl) ⟨129728, by rfl⟩ : syracuseStep 172971 = 259457) B259457
theorem B172983 : Blo 171799 172983 := bstep (se 1 (by rfl) ⟨129737, by rfl⟩ : syracuseStep 172983 = 259475) B259475
theorem B173003 : Blo 171799 173003 := bstep (se 1 (by rfl) ⟨129752, by rfl⟩ : syracuseStep 173003 = 259505) B259505
theorem B173015 : Blo 171799 173015 := bstep (se 1 (by rfl) ⟨129761, by rfl⟩ : syracuseStep 173015 = 259523) B259523
theorem B173035 : Blo 171799 173035 := bstep (se 1 (by rfl) ⟨129776, by rfl⟩ : syracuseStep 173035 = 259553) B259553
theorem B173047 : Blo 171799 173047 := bstep (se 1 (by rfl) ⟨129785, by rfl⟩ : syracuseStep 173047 = 259571) B259571
theorem B173067 : Blo 171799 173067 := bstep (se 1 (by rfl) ⟨129800, by rfl⟩ : syracuseStep 173067 = 259601) B259601
theorem B173079 : Blo 171799 173079 := bstep (se 1 (by rfl) ⟨129809, by rfl⟩ : syracuseStep 173079 = 259619) B259619
theorem B173099 : Blo 171799 173099 := bstep (se 1 (by rfl) ⟨129824, by rfl⟩ : syracuseStep 173099 = 259649) B259649
theorem B173111 : Blo 171799 173111 := bstep (se 1 (by rfl) ⟨129833, by rfl⟩ : syracuseStep 173111 = 259667) B259667
theorem B173131 : Blo 171799 173131 := bstep (se 1 (by rfl) ⟨129848, by rfl⟩ : syracuseStep 173131 = 259697) B259697
theorem B173143 : Blo 171799 173143 := bstep (se 1 (by rfl) ⟨129857, by rfl⟩ : syracuseStep 173143 = 259715) B259715
theorem B173163 : Blo 171799 173163 := bstep (se 1 (by rfl) ⟨129872, by rfl⟩ : syracuseStep 173163 = 259745) B259745
theorem B173175 : Blo 171799 173175 := bstep (se 1 (by rfl) ⟨129881, by rfl⟩ : syracuseStep 173175 = 259763) B259763
theorem B173195 : Blo 171799 173195 := bstep (se 1 (by rfl) ⟨129896, by rfl⟩ : syracuseStep 173195 = 259793) B259793
theorem B173207 : Blo 171799 173207 := bstep (se 1 (by rfl) ⟨129905, by rfl⟩ : syracuseStep 173207 = 259811) B259811
theorem B173227 : Blo 171799 173227 := bstep (se 1 (by rfl) ⟨129920, by rfl⟩ : syracuseStep 173227 = 259841) B259841
theorem B173239 : Blo 171799 173239 := bstep (se 1 (by rfl) ⟨129929, by rfl⟩ : syracuseStep 173239 = 259859) B259859
theorem B173259 : Blo 171799 173259 := bstep (se 1 (by rfl) ⟨129944, by rfl⟩ : syracuseStep 173259 = 259889) B259889
theorem B173271 : Blo 171799 173271 := bstep (se 1 (by rfl) ⟨129953, by rfl⟩ : syracuseStep 173271 = 259907) B259907
theorem B173291 : Blo 171799 173291 := bstep (se 1 (by rfl) ⟨129968, by rfl⟩ : syracuseStep 173291 = 259937) B259937
theorem B173303 : Blo 171799 173303 := bstep (se 1 (by rfl) ⟨129977, by rfl⟩ : syracuseStep 173303 = 259955) B259955
theorem B173323 : Blo 171799 173323 := bstep (se 1 (by rfl) ⟨129992, by rfl⟩ : syracuseStep 173323 = 259985) B259985
theorem B173335 : Blo 171799 173335 := bstep (se 1 (by rfl) ⟨130001, by rfl⟩ : syracuseStep 173335 = 260003) B260003
theorem B173355 : Blo 171799 173355 := bstep (se 1 (by rfl) ⟨130016, by rfl⟩ : syracuseStep 173355 = 260033) B260033
theorem B173367 : Blo 171799 173367 := bstep (se 1 (by rfl) ⟨130025, by rfl⟩ : syracuseStep 173367 = 260051) B260051
theorem B173387 : Blo 171799 173387 := bstep (se 1 (by rfl) ⟨130040, by rfl⟩ : syracuseStep 173387 = 260081) B260081
theorem B173399 : Blo 171799 173399 := bstep (se 1 (by rfl) ⟨130049, by rfl⟩ : syracuseStep 173399 = 260099) B260099
theorem B173419 : Blo 171799 173419 := bstep (se 1 (by rfl) ⟨130064, by rfl⟩ : syracuseStep 173419 = 260129) B260129
theorem B173431 : Blo 171799 173431 := bstep (se 1 (by rfl) ⟨130073, by rfl⟩ : syracuseStep 173431 = 260147) B260147
theorem B173451 : Blo 171799 173451 := bstep (se 1 (by rfl) ⟨130088, by rfl⟩ : syracuseStep 173451 = 260177) B260177
theorem B173463 : Blo 171799 173463 := bstep (se 1 (by rfl) ⟨130097, by rfl⟩ : syracuseStep 173463 = 260195) B260195
theorem B173483 : Blo 171799 173483 := bstep (se 1 (by rfl) ⟨130112, by rfl⟩ : syracuseStep 173483 = 260225) B260225
theorem B370099 : Blo 171799 370099 := bstep (se 1 (by rfl) ⟨277574, by rfl⟩ : syracuseStep 370099 = 555149) B555149
theorem B173495 : Blo 171799 173495 := bstep (se 1 (by rfl) ⟨130121, by rfl⟩ : syracuseStep 173495 = 260243) B260243
theorem B173515 : Blo 171799 173515 := bstep (se 1 (by rfl) ⟨130136, by rfl⟩ : syracuseStep 173515 = 260273) B260273
theorem B173527 : Blo 171799 173527 := bstep (se 1 (by rfl) ⟨130145, by rfl⟩ : syracuseStep 173527 = 260291) B260291
theorem B173547 : Blo 171799 173547 := bstep (se 1 (by rfl) ⟨130160, by rfl⟩ : syracuseStep 173547 = 260321) B260321
theorem B173559 : Blo 171799 173559 := bstep (se 1 (by rfl) ⟨130169, by rfl⟩ : syracuseStep 173559 = 260339) B260339
theorem B173579 : Blo 171799 173579 := bstep (se 1 (by rfl) ⟨130184, by rfl⟩ : syracuseStep 173579 = 260369) B260369
theorem B2991629 : Blo 171799 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B173591 : Blo 171799 173591 := bstep (se 1 (by rfl) ⟨130193, by rfl⟩ : syracuseStep 173591 = 260387) B260387
theorem B173611 : Blo 171799 173611 := bstep (se 1 (by rfl) ⟨130208, by rfl⟩ : syracuseStep 173611 = 260417) B260417
theorem B173623 : Blo 171799 173623 := bstep (se 1 (by rfl) ⟨130217, by rfl⟩ : syracuseStep 173623 = 260435) B260435
theorem B173643 : Blo 171799 173643 := bstep (se 1 (by rfl) ⟨130232, by rfl⟩ : syracuseStep 173643 = 260465) B260465
theorem B173655 : Blo 171799 173655 := bstep (se 1 (by rfl) ⟨130241, by rfl⟩ : syracuseStep 173655 = 260483) B260483
theorem B173675 : Blo 171799 173675 := bstep (se 1 (by rfl) ⟨130256, by rfl⟩ : syracuseStep 173675 = 260513) B260513
theorem B173687 : Blo 171799 173687 := bstep (se 1 (by rfl) ⟨130265, by rfl⟩ : syracuseStep 173687 = 260531) B260531
theorem B173707 : Blo 171799 173707 := bstep (se 1 (by rfl) ⟨130280, by rfl⟩ : syracuseStep 173707 = 260561) B260561
theorem B173719 : Blo 171799 173719 := bstep (se 1 (by rfl) ⟨130289, by rfl⟩ : syracuseStep 173719 = 260579) B260579
theorem B173739 : Blo 171799 173739 := bstep (se 1 (by rfl) ⟨130304, by rfl⟩ : syracuseStep 173739 = 260609) B260609
theorem B173751 : Blo 171799 173751 := bstep (se 1 (by rfl) ⟨130313, by rfl⟩ : syracuseStep 173751 = 260627) B260627
theorem B173771 : Blo 171799 173771 := bstep (se 1 (by rfl) ⟨130328, by rfl⟩ : syracuseStep 173771 = 260657) B260657
theorem B173783 : Blo 171799 173783 := bstep (se 1 (by rfl) ⟨130337, by rfl⟩ : syracuseStep 173783 = 260675) B260675
theorem B173803 : Blo 171799 173803 := bstep (se 1 (by rfl) ⟨130352, by rfl⟩ : syracuseStep 173803 = 260705) B260705
theorem B173815 : Blo 171799 173815 := bstep (se 1 (by rfl) ⟨130361, by rfl⟩ : syracuseStep 173815 = 260723) B260723
theorem B173835 : Blo 171799 173835 := bstep (se 1 (by rfl) ⟨130376, by rfl⟩ : syracuseStep 173835 = 260753) B260753
theorem B173847 : Blo 171799 173847 := bstep (se 1 (by rfl) ⟨130385, by rfl⟩ : syracuseStep 173847 = 260771) B260771
theorem B173867 : Blo 171799 173867 := bstep (se 1 (by rfl) ⟨130400, by rfl⟩ : syracuseStep 173867 = 260801) B260801
theorem B173879 : Blo 171799 173879 := bstep (se 1 (by rfl) ⟨130409, by rfl⟩ : syracuseStep 173879 = 260819) B260819
theorem B436043 : Blo 171799 436043 := bstep (se 1 (by rfl) ⟨327032, by rfl⟩ : syracuseStep 436043 = 654065) B654065
theorem B173899 : Blo 171799 173899 := bstep (se 1 (by rfl) ⟨130424, by rfl⟩ : syracuseStep 173899 = 260849) B260849
theorem B173911 : Blo 171799 173911 := bstep (se 1 (by rfl) ⟨130433, by rfl⟩ : syracuseStep 173911 = 260867) B260867
theorem B173931 : Blo 171799 173931 := bstep (se 1 (by rfl) ⟨130448, by rfl⟩ : syracuseStep 173931 = 260897) B260897
theorem B173943 : Blo 171799 173943 := bstep (se 1 (by rfl) ⟨130457, by rfl⟩ : syracuseStep 173943 = 260915) B260915
theorem B173963 : Blo 171799 173963 := bstep (se 1 (by rfl) ⟨130472, by rfl⟩ : syracuseStep 173963 = 260945) B260945
theorem B173975 : Blo 171799 173975 := bstep (se 1 (by rfl) ⟨130481, by rfl⟩ : syracuseStep 173975 = 260963) B260963
theorem B173995 : Blo 171799 173995 := bstep (se 1 (by rfl) ⟨130496, by rfl⟩ : syracuseStep 173995 = 260993) B260993
theorem B174007 : Blo 171799 174007 := bstep (se 1 (by rfl) ⟨130505, by rfl⟩ : syracuseStep 174007 = 261011) B261011
theorem B174027 : Blo 171799 174027 := bstep (se 1 (by rfl) ⟨130520, by rfl⟩ : syracuseStep 174027 = 261041) B261041
theorem B174039 : Blo 171799 174039 := bstep (se 1 (by rfl) ⟨130529, by rfl⟩ : syracuseStep 174039 = 261059) B261059
theorem B174059 : Blo 171799 174059 := bstep (se 1 (by rfl) ⟨130544, by rfl⟩ : syracuseStep 174059 = 261089) B261089
theorem B174071 : Blo 171799 174071 := bstep (se 1 (by rfl) ⟨130553, by rfl⟩ : syracuseStep 174071 = 261107) B261107
theorem B174091 : Blo 171799 174091 := bstep (se 1 (by rfl) ⟨130568, by rfl⟩ : syracuseStep 174091 = 261137) B261137
theorem B174103 : Blo 171799 174103 := bstep (se 1 (by rfl) ⟨130577, by rfl⟩ : syracuseStep 174103 = 261155) B261155
theorem B1255459 : Blo 171799 1255459 := bstep (se 1 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 1255459 = 1883189) B1883189
theorem B174123 : Blo 171799 174123 := bstep (se 1 (by rfl) ⟨130592, by rfl⟩ : syracuseStep 174123 = 261185) B261185
theorem B174135 : Blo 171799 174135 := bstep (se 1 (by rfl) ⟨130601, by rfl⟩ : syracuseStep 174135 = 261203) B261203
theorem B174155 : Blo 171799 174155 := bstep (se 1 (by rfl) ⟨130616, by rfl⟩ : syracuseStep 174155 = 261233) B261233
theorem B174167 : Blo 171799 174167 := bstep (se 1 (by rfl) ⟨130625, by rfl⟩ : syracuseStep 174167 = 261251) B261251
theorem B174187 : Blo 171799 174187 := bstep (se 1 (by rfl) ⟨130640, by rfl⟩ : syracuseStep 174187 = 261281) B261281
theorem B174199 : Blo 171799 174199 := bstep (se 1 (by rfl) ⟨130649, by rfl⟩ : syracuseStep 174199 = 261299) B261299
theorem B174219 : Blo 171799 174219 := bstep (se 1 (by rfl) ⟨130664, by rfl⟩ : syracuseStep 174219 = 261329) B261329
theorem B174231 : Blo 171799 174231 := bstep (se 1 (by rfl) ⟨130673, by rfl⟩ : syracuseStep 174231 = 261347) B261347
theorem B174251 : Blo 171799 174251 := bstep (se 1 (by rfl) ⟨130688, by rfl⟩ : syracuseStep 174251 = 261377) B261377
theorem B1255601 : Blo 171799 1255601 := bstep (se 2 (by rfl) ⟨470850, by rfl⟩ : syracuseStep 1255601 = 941701) B941701
theorem B174263 : Blo 171799 174263 := bstep (se 1 (by rfl) ⟨130697, by rfl⟩ : syracuseStep 174263 = 261395) B261395
theorem B174283 : Blo 171799 174283 := bstep (se 1 (by rfl) ⟨130712, by rfl⟩ : syracuseStep 174283 = 261425) B261425
theorem B633035 : Blo 171799 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B174295 : Blo 171799 174295 := bstep (se 1 (by rfl) ⟨130721, by rfl⟩ : syracuseStep 174295 = 261443) B261443
theorem B174315 : Blo 171799 174315 := bstep (se 1 (by rfl) ⟨130736, by rfl⟩ : syracuseStep 174315 = 261473) B261473
theorem B174327 : Blo 171799 174327 := bstep (se 1 (by rfl) ⟨130745, by rfl⟩ : syracuseStep 174327 = 261491) B261491
theorem B174347 : Blo 171799 174347 := bstep (se 1 (by rfl) ⟨130760, by rfl⟩ : syracuseStep 174347 = 261521) B261521
theorem B174359 : Blo 171799 174359 := bstep (se 1 (by rfl) ⟨130769, by rfl⟩ : syracuseStep 174359 = 261539) B261539
theorem B1255715 : Blo 171799 1255715 := bstep (se 1 (by rfl) ⟨941786, by rfl⟩ : syracuseStep 1255715 = 1883573) B1883573
theorem B174379 : Blo 171799 174379 := bstep (se 1 (by rfl) ⟨130784, by rfl⟩ : syracuseStep 174379 = 261569) B261569
theorem B174391 : Blo 171799 174391 := bstep (se 1 (by rfl) ⟨130793, by rfl⟩ : syracuseStep 174391 = 261587) B261587
theorem B174411 : Blo 171799 174411 := bstep (se 1 (by rfl) ⟨130808, by rfl⟩ : syracuseStep 174411 = 261617) B261617
theorem B174423 : Blo 171799 174423 := bstep (se 1 (by rfl) ⟨130817, by rfl⟩ : syracuseStep 174423 = 261635) B261635
theorem B174443 : Blo 171799 174443 := bstep (se 1 (by rfl) ⟨130832, by rfl⟩ : syracuseStep 174443 = 261665) B261665
theorem B174455 : Blo 171799 174455 := bstep (se 1 (by rfl) ⟨130841, by rfl⟩ : syracuseStep 174455 = 261683) B261683
theorem B174475 : Blo 171799 174475 := bstep (se 1 (by rfl) ⟨130856, by rfl⟩ : syracuseStep 174475 = 261713) B261713
theorem B174487 : Blo 171799 174487 := bstep (se 1 (by rfl) ⟨130865, by rfl⟩ : syracuseStep 174487 = 261731) B261731
theorem B174507 : Blo 171799 174507 := bstep (se 1 (by rfl) ⟨130880, by rfl⟩ : syracuseStep 174507 = 261761) B261761
theorem B174519 : Blo 171799 174519 := bstep (se 1 (by rfl) ⟨130889, by rfl⟩ : syracuseStep 174519 = 261779) B261779
theorem B174539 : Blo 171799 174539 := bstep (se 1 (by rfl) ⟨130904, by rfl⟩ : syracuseStep 174539 = 261809) B261809
theorem B174551 : Blo 171799 174551 := bstep (se 1 (by rfl) ⟨130913, by rfl⟩ : syracuseStep 174551 = 261827) B261827
theorem B1321433 : Blo 171799 1321433 := bstep (se 2 (by rfl) ⟨495537, by rfl⟩ : syracuseStep 1321433 = 991075) B991075
theorem B174571 : Blo 171799 174571 := bstep (se 1 (by rfl) ⟨130928, by rfl⟩ : syracuseStep 174571 = 261857) B261857
theorem B174583 : Blo 171799 174583 := bstep (se 1 (by rfl) ⟨130937, by rfl⟩ : syracuseStep 174583 = 261875) B261875
theorem B174603 : Blo 171799 174603 := bstep (se 1 (by rfl) ⟨130952, by rfl⟩ : syracuseStep 174603 = 261905) B261905
theorem B993809 : Blo 171799 993809 := bstep (se 2 (by rfl) ⟨372678, by rfl⟩ : syracuseStep 993809 = 745357) B745357
theorem B174615 : Blo 171799 174615 := bstep (se 1 (by rfl) ⟨130961, by rfl⟩ : syracuseStep 174615 = 261923) B261923
theorem B174635 : Blo 171799 174635 := bstep (se 1 (by rfl) ⟨130976, by rfl⟩ : syracuseStep 174635 = 261953) B261953
theorem B174647 : Blo 171799 174647 := bstep (se 1 (by rfl) ⟨130985, by rfl⟩ : syracuseStep 174647 = 261971) B261971
theorem B174667 : Blo 171799 174667 := bstep (se 1 (by rfl) ⟨131000, by rfl⟩ : syracuseStep 174667 = 262001) B262001
theorem B174679 : Blo 171799 174679 := bstep (se 1 (by rfl) ⟨131009, by rfl⟩ : syracuseStep 174679 = 262019) B262019
theorem B174699 : Blo 171799 174699 := bstep (se 1 (by rfl) ⟨131024, by rfl⟩ : syracuseStep 174699 = 262049) B262049
theorem B174711 : Blo 171799 174711 := bstep (se 1 (by rfl) ⟨131033, by rfl⟩ : syracuseStep 174711 = 262067) B262067
theorem B174731 : Blo 171799 174731 := bstep (se 1 (by rfl) ⟨131048, by rfl⟩ : syracuseStep 174731 = 262097) B262097
theorem B174743 : Blo 171799 174743 := bstep (se 1 (by rfl) ⟨131057, by rfl⟩ : syracuseStep 174743 = 262115) B262115
theorem B174763 : Blo 171799 174763 := bstep (se 1 (by rfl) ⟨131072, by rfl⟩ : syracuseStep 174763 = 262145) B262145
theorem B174775 : Blo 171799 174775 := bstep (se 1 (by rfl) ⟨131081, by rfl⟩ : syracuseStep 174775 = 262163) B262163
theorem B174795 : Blo 171799 174795 := bstep (se 1 (by rfl) ⟨131096, by rfl⟩ : syracuseStep 174795 = 262193) B262193
theorem B174807 : Blo 171799 174807 := bstep (se 1 (by rfl) ⟨131105, by rfl⟩ : syracuseStep 174807 = 262211) B262211
theorem B404183 : Blo 171799 404183 := bstep (se 1 (by rfl) ⟨303137, by rfl⟩ : syracuseStep 404183 = 606275) B606275
theorem B174827 : Blo 171799 174827 := bstep (se 1 (by rfl) ⟨131120, by rfl⟩ : syracuseStep 174827 = 262241) B262241
theorem B174839 : Blo 171799 174839 := bstep (se 1 (by rfl) ⟨131129, by rfl⟩ : syracuseStep 174839 = 262259) B262259
theorem B174859 : Blo 171799 174859 := bstep (se 1 (by rfl) ⟨131144, by rfl⟩ : syracuseStep 174859 = 262289) B262289
theorem B437015 : Blo 171799 437015 := bstep (se 1 (by rfl) ⟨327761, by rfl⟩ : syracuseStep 437015 = 655523) B655523
theorem B174871 : Blo 171799 174871 := bstep (se 1 (by rfl) ⟨131153, by rfl⟩ : syracuseStep 174871 = 262307) B262307
theorem B174891 : Blo 171799 174891 := bstep (se 1 (by rfl) ⟨131168, by rfl⟩ : syracuseStep 174891 = 262337) B262337
theorem B666413 : Blo 171799 666413 := bstep (se 3 (by rfl) ⟨124952, by rfl⟩ : syracuseStep 666413 = 249905) B249905
theorem B174903 : Blo 171799 174903 := bstep (se 1 (by rfl) ⟨131177, by rfl⟩ : syracuseStep 174903 = 262355) B262355
theorem B666443 : Blo 171799 666443 := bstep (se 1 (by rfl) ⟨499832, by rfl⟩ : syracuseStep 666443 = 999665) B999665
theorem B174923 : Blo 171799 174923 := bstep (se 1 (by rfl) ⟨131192, by rfl⟩ : syracuseStep 174923 = 262385) B262385
theorem B174935 : Blo 171799 174935 := bstep (se 1 (by rfl) ⟨131201, by rfl⟩ : syracuseStep 174935 = 262403) B262403
theorem B174955 : Blo 171799 174955 := bstep (se 1 (by rfl) ⟨131216, by rfl⟩ : syracuseStep 174955 = 262433) B262433
theorem B174967 : Blo 171799 174967 := bstep (se 1 (by rfl) ⟨131225, by rfl⟩ : syracuseStep 174967 = 262451) B262451
theorem B371585 : Blo 171799 371585 := bstep (se 2 (by rfl) ⟨139344, by rfl⟩ : syracuseStep 371585 = 278689) B278689
theorem B174987 : Blo 171799 174987 := bstep (se 1 (by rfl) ⟨131240, by rfl⟩ : syracuseStep 174987 = 262481) B262481
theorem B174999 : Blo 171799 174999 := bstep (se 1 (by rfl) ⟨131249, by rfl⟩ : syracuseStep 174999 = 262499) B262499
theorem B175019 : Blo 171799 175019 := bstep (se 1 (by rfl) ⟨131264, by rfl⟩ : syracuseStep 175019 = 262529) B262529
theorem B175031 : Blo 171799 175031 := bstep (se 1 (by rfl) ⟨131273, by rfl⟩ : syracuseStep 175031 = 262547) B262547
theorem B175051 : Blo 171799 175051 := bstep (se 1 (by rfl) ⟨131288, by rfl⟩ : syracuseStep 175051 = 262577) B262577
theorem B175063 : Blo 171799 175063 := bstep (se 1 (by rfl) ⟨131297, by rfl⟩ : syracuseStep 175063 = 262595) B262595
theorem B994265 : Blo 171799 994265 := bstep (se 2 (by rfl) ⟨372849, by rfl⟩ : syracuseStep 994265 = 745699) B745699
theorem B175083 : Blo 171799 175083 := bstep (se 1 (by rfl) ⟨131312, by rfl⟩ : syracuseStep 175083 = 262625) B262625
theorem B175095 : Blo 171799 175095 := bstep (se 1 (by rfl) ⟨131321, by rfl⟩ : syracuseStep 175095 = 262643) B262643
theorem B207883 : Blo 171799 207883 := bstep (se 1 (by rfl) ⟨155912, by rfl⟩ : syracuseStep 207883 = 311825) B311825
theorem B175115 : Blo 171799 175115 := bstep (se 1 (by rfl) ⟨131336, by rfl⟩ : syracuseStep 175115 = 262673) B262673
theorem B175127 : Blo 171799 175127 := bstep (se 1 (by rfl) ⟨131345, by rfl⟩ : syracuseStep 175127 = 262691) B262691
theorem B175147 : Blo 171799 175147 := bstep (se 1 (by rfl) ⟨131360, by rfl⟩ : syracuseStep 175147 = 262721) B262721
theorem B175159 : Blo 171799 175159 := bstep (se 1 (by rfl) ⟨131369, by rfl⟩ : syracuseStep 175159 = 262739) B262739
theorem B175179 : Blo 171799 175179 := bstep (se 1 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 175179 = 262769) B262769
theorem B175191 : Blo 171799 175191 := bstep (se 1 (by rfl) ⟨131393, by rfl⟩ : syracuseStep 175191 = 262787) B262787
theorem B175211 : Blo 171799 175211 := bstep (se 1 (by rfl) ⟨131408, by rfl⟩ : syracuseStep 175211 = 262817) B262817
theorem B175223 : Blo 171799 175223 := bstep (se 1 (by rfl) ⟨131417, by rfl⟩ : syracuseStep 175223 = 262835) B262835
theorem B175243 : Blo 171799 175243 := bstep (se 1 (by rfl) ⟨131432, by rfl⟩ : syracuseStep 175243 = 262865) B262865
theorem B175255 : Blo 171799 175255 := bstep (se 1 (by rfl) ⟨131441, by rfl⟩ : syracuseStep 175255 = 262883) B262883
theorem B175275 : Blo 171799 175275 := bstep (se 1 (by rfl) ⟨131456, by rfl⟩ : syracuseStep 175275 = 262913) B262913
theorem B175287 : Blo 171799 175287 := bstep (se 1 (by rfl) ⟨131465, by rfl⟩ : syracuseStep 175287 = 262931) B262931
theorem B175307 : Blo 171799 175307 := bstep (se 1 (by rfl) ⟨131480, by rfl⟩ : syracuseStep 175307 = 262961) B262961
theorem B371927 : Blo 171799 371927 := bstep (se 1 (by rfl) ⟨278945, by rfl⟩ : syracuseStep 371927 = 557891) B557891
theorem B175319 : Blo 171799 175319 := bstep (se 1 (by rfl) ⟨131489, by rfl⟩ : syracuseStep 175319 = 262979) B262979
theorem B175339 : Blo 171799 175339 := bstep (se 1 (by rfl) ⟨131504, by rfl⟩ : syracuseStep 175339 = 263009) B263009
theorem B175351 : Blo 171799 175351 := bstep (se 1 (by rfl) ⟨131513, by rfl⟩ : syracuseStep 175351 = 263027) B263027
theorem B175371 : Blo 171799 175371 := bstep (se 1 (by rfl) ⟨131528, by rfl⟩ : syracuseStep 175371 = 263057) B263057
theorem B175383 : Blo 171799 175383 := bstep (se 1 (by rfl) ⟨131537, by rfl⟩ : syracuseStep 175383 = 263075) B263075
theorem B175403 : Blo 171799 175403 := bstep (se 1 (by rfl) ⟨131552, by rfl⟩ : syracuseStep 175403 = 263105) B263105
theorem B175415 : Blo 171799 175415 := bstep (se 1 (by rfl) ⟨131561, by rfl⟩ : syracuseStep 175415 = 263123) B263123
theorem B175435 : Blo 171799 175435 := bstep (se 1 (by rfl) ⟨131576, by rfl⟩ : syracuseStep 175435 = 263153) B263153
theorem B175447 : Blo 171799 175447 := bstep (se 1 (by rfl) ⟨131585, by rfl⟩ : syracuseStep 175447 = 263171) B263171
theorem B175467 : Blo 171799 175467 := bstep (se 1 (by rfl) ⟨131600, by rfl⟩ : syracuseStep 175467 = 263201) B263201
theorem B175479 : Blo 171799 175479 := bstep (se 1 (by rfl) ⟨131609, by rfl⟩ : syracuseStep 175479 = 263219) B263219
theorem B175499 : Blo 171799 175499 := bstep (se 1 (by rfl) ⟨131624, by rfl⟩ : syracuseStep 175499 = 263249) B263249
theorem B175511 : Blo 171799 175511 := bstep (se 1 (by rfl) ⟨131633, by rfl⟩ : syracuseStep 175511 = 263267) B263267
theorem B175531 : Blo 171799 175531 := bstep (se 1 (by rfl) ⟨131648, by rfl⟩ : syracuseStep 175531 = 263297) B263297
theorem B437683 : Blo 171799 437683 := bstep (se 1 (by rfl) ⟨328262, by rfl⟩ : syracuseStep 437683 = 656525) B656525
theorem B175543 : Blo 171799 175543 := bstep (se 1 (by rfl) ⟨131657, by rfl⟩ : syracuseStep 175543 = 263315) B263315
theorem B175563 : Blo 171799 175563 := bstep (se 1 (by rfl) ⟨131672, by rfl⟩ : syracuseStep 175563 = 263345) B263345
theorem B175575 : Blo 171799 175575 := bstep (se 1 (by rfl) ⟨131681, by rfl⟩ : syracuseStep 175575 = 263363) B263363
theorem B175595 : Blo 171799 175595 := bstep (se 1 (by rfl) ⟨131696, by rfl⟩ : syracuseStep 175595 = 263393) B263393
theorem B175607 : Blo 171799 175607 := bstep (se 1 (by rfl) ⟨131705, by rfl⟩ : syracuseStep 175607 = 263411) B263411
theorem B372235 : Blo 171799 372235 := bstep (se 1 (by rfl) ⟨279176, by rfl⟩ : syracuseStep 372235 = 558353) B558353
theorem B175627 : Blo 171799 175627 := bstep (se 1 (by rfl) ⟨131720, by rfl⟩ : syracuseStep 175627 = 263441) B263441
theorem B175639 : Blo 171799 175639 := bstep (se 1 (by rfl) ⟨131729, by rfl⟩ : syracuseStep 175639 = 263459) B263459
theorem B175659 : Blo 171799 175659 := bstep (se 1 (by rfl) ⟨131744, by rfl⟩ : syracuseStep 175659 = 263489) B263489
theorem B667187 : Blo 171799 667187 := bstep (se 1 (by rfl) ⟨500390, by rfl⟩ : syracuseStep 667187 = 1000781) B1000781
theorem B175671 : Blo 171799 175671 := bstep (se 1 (by rfl) ⟨131753, by rfl⟩ : syracuseStep 175671 = 263507) B263507
theorem B437825 : Blo 171799 437825 := bstep (se 2 (by rfl) ⟨164184, by rfl⟩ : syracuseStep 437825 = 328369) B328369
theorem B175691 : Blo 171799 175691 := bstep (se 1 (by rfl) ⟨131768, by rfl⟩ : syracuseStep 175691 = 263537) B263537
theorem B175703 : Blo 171799 175703 := bstep (se 1 (by rfl) ⟨131777, by rfl⟩ : syracuseStep 175703 = 263555) B263555
theorem B175723 : Blo 171799 175723 := bstep (se 1 (by rfl) ⟨131792, by rfl⟩ : syracuseStep 175723 = 263585) B263585
theorem B175735 : Blo 171799 175735 := bstep (se 1 (by rfl) ⟨131801, by rfl⟩ : syracuseStep 175735 = 263603) B263603
theorem B175755 : Blo 171799 175755 := bstep (se 1 (by rfl) ⟨131816, by rfl⟩ : syracuseStep 175755 = 263633) B263633
theorem B175767 : Blo 171799 175767 := bstep (se 1 (by rfl) ⟨131825, by rfl⟩ : syracuseStep 175767 = 263651) B263651
theorem B175787 : Blo 171799 175787 := bstep (se 1 (by rfl) ⟨131840, by rfl⟩ : syracuseStep 175787 = 263681) B263681
theorem B175799 : Blo 171799 175799 := bstep (se 1 (by rfl) ⟨131849, by rfl⟩ : syracuseStep 175799 = 263699) B263699
theorem B2961197 : Blo 171799 2961197 := bstep (se 3 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 2961197 = 1110449) B1110449
theorem B1126237 : Blo 171799 1126237 := bstep (se 3 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 1126237 = 422339) B422339
theorem B1585331 : Blo 171799 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B405847 : Blo 171799 405847 := bstep (se 1 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 405847 = 608771) B608771
theorem B373081 : Blo 171799 373081 := bstep (se 2 (by rfl) ⟨139905, by rfl⟩ : syracuseStep 373081 = 279811) B279811
theorem B2240945 : Blo 171799 2240945 := bstep (se 2 (by rfl) ⟨840354, by rfl⟩ : syracuseStep 2240945 = 1680709) B1680709
theorem B439091 : Blo 171799 439091 := bstep (se 1 (by rfl) ⟨329318, by rfl⟩ : syracuseStep 439091 = 658637) B658637
theorem B176951 : Blo 171799 176951 := bstep (se 1 (by rfl) ⟨132713, by rfl⟩ : syracuseStep 176951 = 265427) B265427
theorem B1192805 : Blo 171799 1192805 := bstep (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) B223651
theorem B2307203 : Blo 171799 2307203 := bstep (se 1 (by rfl) ⟨1730402, by rfl⟩ : syracuseStep 2307203 = 3460805) B3460805
theorem B439627 : Blo 171799 439627 := bstep (se 1 (by rfl) ⟨329720, by rfl⟩ : syracuseStep 439627 = 659441) B659441
theorem B374233 : Blo 171799 374233 := bstep (se 2 (by rfl) ⟨140337, by rfl⟩ : syracuseStep 374233 = 280675) B280675
theorem B439769 : Blo 171799 439769 := bstep (se 2 (by rfl) ⟨164913, by rfl⟩ : syracuseStep 439769 = 329827) B329827
theorem B865753 : Blo 171799 865753 := bstep (se 2 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 865753 = 649315) B649315
theorem B2668049 : Blo 171799 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B800279 : Blo 171799 800279 := bstep (se 1 (by rfl) ⟨600209, by rfl⟩ : syracuseStep 800279 = 1200419) B1200419
theorem B374387 : Blo 171799 374387 := bstep (se 1 (by rfl) ⟨280790, by rfl⟩ : syracuseStep 374387 = 561581) B561581
theorem B1324835 : Blo 171799 1324835 := bstep (se 1 (by rfl) ⟨993626, by rfl⟩ : syracuseStep 1324835 = 1987253) B1987253
theorem B374807 : Blo 171799 374807 := bstep (se 1 (by rfl) ⟨281105, by rfl⟩ : syracuseStep 374807 = 562211) B562211
theorem B735277 : Blo 171799 735277 := bstep (se 3 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 735277 = 275729) B275729
theorem B440599 : Blo 171799 440599 := bstep (se 1 (by rfl) ⟨330449, by rfl⟩ : syracuseStep 440599 = 660899) B660899
theorem B1325489 : Blo 171799 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B309835 : Blo 171799 309835 := bstep (se 1 (by rfl) ⟨232376, by rfl⟩ : syracuseStep 309835 = 464753) B464753
theorem B4209245 : Blo 171799 4209245 := bstep (se 3 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 4209245 = 1578467) B1578467
theorem B441035 : Blo 171799 441035 := bstep (se 1 (by rfl) ⟨330776, by rfl⟩ : syracuseStep 441035 = 661553) B661553
theorem B1260305 : Blo 171799 1260305 := bstep (se 2 (by rfl) ⟨472614, by rfl⟩ : syracuseStep 1260305 = 945229) B945229
theorem B899857 : Blo 171799 899857 := bstep (se 2 (by rfl) ⟨337446, by rfl⟩ : syracuseStep 899857 = 674893) B674893
theorem B474007 : Blo 171799 474007 := bstep (se 1 (by rfl) ⟨355505, by rfl⟩ : syracuseStep 474007 = 711011) B711011
theorem B900019 : Blo 171799 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B6339545 : Blo 171799 6339545 := bstep (se 2 (by rfl) ⟨2377329, by rfl⟩ : syracuseStep 6339545 = 4754659) B4754659
theorem B441409 : Blo 171799 441409 := bstep (se 2 (by rfl) ⟨165528, by rfl⟩ : syracuseStep 441409 = 331057) B331057
theorem B244939 : Blo 171799 244939 := bstep (se 1 (by rfl) ⟨183704, by rfl⟩ : syracuseStep 244939 = 367409) B367409
theorem B310657 : Blo 171799 310657 := bstep (se 2 (by rfl) ⟨116496, by rfl⟩ : syracuseStep 310657 = 232993) B232993
theorem B343435 : Blo 171799 343435 := bstep (se 1 (by rfl) ⟨257576, by rfl⟩ : syracuseStep 343435 = 515153) B515153
theorem B310873 : Blo 171799 310873 := bstep (se 2 (by rfl) ⟨116577, by rfl⟩ : syracuseStep 310873 = 233155) B233155
theorem B442007 : Blo 171799 442007 := bstep (se 1 (by rfl) ⟨331505, by rfl⟩ : syracuseStep 442007 = 663011) B663011
theorem B311219 : Blo 171799 311219 := bstep (se 1 (by rfl) ⟨233414, by rfl⟩ : syracuseStep 311219 = 466829) B466829
theorem B999641 : Blo 171799 999641 := bstep (se 2 (by rfl) ⟨374865, by rfl⟩ : syracuseStep 999641 = 749731) B749731
theorem B311681 : Blo 171799 311681 := bstep (se 2 (by rfl) ⟨116880, by rfl⟩ : syracuseStep 311681 = 233761) B233761
theorem B737687 : Blo 171799 737687 := bstep (se 1 (by rfl) ⟨553265, by rfl⟩ : syracuseStep 737687 = 1106531) B1106531
theorem B246169 : Blo 171799 246169 := bstep (se 2 (by rfl) ⟨92313, by rfl⟩ : syracuseStep 246169 = 184627) B184627
theorem B442817 : Blo 171799 442817 := bstep (se 2 (by rfl) ⟨166056, by rfl⟩ : syracuseStep 442817 = 332113) B332113
theorem B377419 : Blo 171799 377419 := bstep (se 1 (by rfl) ⟨283064, by rfl⟩ : syracuseStep 377419 = 566129) B566129
theorem B2507395 : Blo 171799 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B443353 : Blo 171799 443353 := bstep (se 2 (by rfl) ⟨166257, by rfl⟩ : syracuseStep 443353 = 332515) B332515
theorem B377971 : Blo 171799 377971 := bstep (se 1 (by rfl) ⟨283478, by rfl⟩ : syracuseStep 377971 = 566957) B566957
theorem B705809 : Blo 171799 705809 := bstep (se 2 (by rfl) ⟨264678, by rfl⟩ : syracuseStep 705809 = 529357) B529357
theorem B247063 : Blo 171799 247063 := bstep (se 1 (by rfl) ⟨185297, by rfl⟩ : syracuseStep 247063 = 370595) B370595
theorem B706099 : Blo 171799 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B4867715 : Blo 171799 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B837337 : Blo 171799 837337 := bstep (se 2 (by rfl) ⟨314001, by rfl⟩ : syracuseStep 837337 = 628003) B628003
theorem B280343 : Blo 171799 280343 := bstep (se 1 (by rfl) ⟨210257, by rfl⟩ : syracuseStep 280343 = 420515) B420515
theorem B1001281 : Blo 171799 1001281 := bstep (se 2 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 1001281 = 750961) B750961
theorem B247627 : Blo 171799 247627 := bstep (se 1 (by rfl) ⟨185720, by rfl⟩ : syracuseStep 247627 = 371441) B371441
theorem B444467 : Blo 171799 444467 := bstep (se 1 (by rfl) ⟨333350, by rfl⟩ : syracuseStep 444467 = 666701) B666701
theorem B1427557 : Blo 171799 1427557 := bstep (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) B267667
theorem B739601 : Blo 171799 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B280855 : Blo 171799 280855 := bstep (se 1 (by rfl) ⟨210641, by rfl⟩ : syracuseStep 280855 = 421283) B421283
theorem B2836781 : Blo 171799 2836781 := bstep (se 3 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 2836781 = 1063793) B1063793
theorem B444761 : Blo 171799 444761 := bstep (se 2 (by rfl) ⟨166785, by rfl⟩ : syracuseStep 444761 = 333571) B333571
theorem B870749 : Blo 171799 870749 := bstep (se 3 (by rfl) ⟨163265, by rfl⟩ : syracuseStep 870749 = 326531) B326531
theorem B707033 : Blo 171799 707033 := bstep (se 2 (by rfl) ⟨265137, by rfl⟩ : syracuseStep 707033 = 530275) B530275
theorem B1395265 : Blo 171799 1395265 := bstep (se 2 (by rfl) ⟨523224, by rfl⟩ : syracuseStep 1395265 = 1046449) B1046449
theorem B281227 : Blo 171799 281227 := bstep (se 1 (by rfl) ⟨210920, by rfl⟩ : syracuseStep 281227 = 421841) B421841
theorem B2214701 : Blo 171799 2214701 := bstep (se 3 (by rfl) ⟨415256, by rfl⟩ : syracuseStep 2214701 = 830513) B830513
theorem B248651 : Blo 171799 248651 := bstep (se 1 (by rfl) ⟨186488, by rfl⟩ : syracuseStep 248651 = 372977) B372977
theorem B707417 : Blo 171799 707417 := bstep (se 2 (by rfl) ⟨265281, by rfl⟩ : syracuseStep 707417 = 530563) B530563
theorem B281483 : Blo 171799 281483 := bstep (se 1 (by rfl) ⟨211112, by rfl⟩ : syracuseStep 281483 = 422225) B422225
theorem B1330181 : Blo 171799 1330181 := bstep (se 4 (by rfl) ⟨124704, by rfl⟩ : syracuseStep 1330181 = 249409) B249409
theorem B740573 : Blo 171799 740573 := bstep (se 3 (by rfl) ⟨138857, by rfl⟩ : syracuseStep 740573 = 277715) B277715
theorem B412951 : Blo 171799 412951 := bstep (se 1 (by rfl) ⟨309713, by rfl⟩ : syracuseStep 412951 = 619427) B619427
theorem B249113 : Blo 171799 249113 := bstep (se 2 (by rfl) ⟨93417, by rfl⟩ : syracuseStep 249113 = 186835) B186835
theorem B183691 : Blo 171799 183691 := bstep (se 1 (by rfl) ⟨137768, by rfl⟩ : syracuseStep 183691 = 275537) B275537
theorem B314903 : Blo 171799 314903 := bstep (se 1 (by rfl) ⟨236177, by rfl⟩ : syracuseStep 314903 = 472355) B472355
theorem B478813 : Blo 171799 478813 := bstep (se 3 (by rfl) ⟨89777, by rfl⟩ : syracuseStep 478813 = 179555) B179555
theorem B249751 : Blo 171799 249751 := bstep (se 1 (by rfl) ⟨187313, by rfl⟩ : syracuseStep 249751 = 374627) B374627
theorem B839603 : Blo 171799 839603 := bstep (se 1 (by rfl) ⟨629702, by rfl⟩ : syracuseStep 839603 = 1259405) B1259405
theorem B1495361 : Blo 171799 1495361 := bstep (se 2 (by rfl) ⟨560760, by rfl⟩ : syracuseStep 1495361 = 1121521) B1121521
theorem B217495 : Blo 171799 217495 := bstep (se 1 (by rfl) ⟨163121, by rfl⟩ : syracuseStep 217495 = 326243) B326243
theorem B872855 : Blo 171799 872855 := bstep (se 1 (by rfl) ⟨654641, by rfl⟩ : syracuseStep 872855 = 1309283) B1309283
theorem B709067 : Blo 171799 709067 := bstep (se 1 (by rfl) ⟨531800, by rfl⟩ : syracuseStep 709067 = 1063601) B1063601
theorem B1659523 : Blo 171799 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B742061 : Blo 171799 742061 := bstep (se 3 (by rfl) ⟨139136, by rfl⟩ : syracuseStep 742061 = 278273) B278273
theorem B185323 : Blo 171799 185323 := bstep (se 1 (by rfl) ⟨138992, by rfl⟩ : syracuseStep 185323 = 277985) B277985
theorem B218315 : Blo 171799 218315 := bstep (se 1 (by rfl) ⟨163736, by rfl⟩ : syracuseStep 218315 = 327473) B327473
theorem B1332611 : Blo 171799 1332611 := bstep (se 1 (by rfl) ⟨999458, by rfl⟩ : syracuseStep 1332611 = 1998917) B1998917
theorem B1594973 : Blo 171799 1594973 := bstep (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) B598115
theorem B841603 : Blo 171799 841603 := bstep (se 1 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 841603 = 1262405) B1262405
theorem B219019 : Blo 171799 219019 := bstep (se 1 (by rfl) ⟨164264, by rfl⟩ : syracuseStep 219019 = 328529) B328529
theorem B186295 : Blo 171799 186295 := bstep (se 1 (by rfl) ⟨139721, by rfl⟩ : syracuseStep 186295 = 279443) B279443
theorem B448459 : Blo 171799 448459 := bstep (se 1 (by rfl) ⟨336344, by rfl⟩ : syracuseStep 448459 = 672689) B672689
theorem B186391 : Blo 171799 186391 := bstep (se 1 (by rfl) ⟨139793, by rfl⟩ : syracuseStep 186391 = 279587) B279587
theorem B219287 : Blo 171799 219287 := bstep (se 1 (by rfl) ⟨164465, by rfl⟩ : syracuseStep 219287 = 328931) B328931
theorem B186571 : Blo 171799 186571 := bstep (se 1 (by rfl) ⟨139928, by rfl⟩ : syracuseStep 186571 = 279857) B279857
theorem B579905 : Blo 171799 579905 := bstep (se 2 (by rfl) ⟨217464, by rfl⟩ : syracuseStep 579905 = 434929) B434929
theorem B842201 : Blo 171799 842201 := bstep (se 2 (by rfl) ⟨315825, by rfl⟩ : syracuseStep 842201 = 631651) B631651
theorem B744025 : Blo 171799 744025 := bstep (se 2 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 744025 = 558019) B558019
theorem B187211 : Blo 171799 187211 := bstep (se 1 (by rfl) ⟨140408, by rfl⟩ : syracuseStep 187211 = 280817) B280817
theorem B219991 : Blo 171799 219991 := bstep (se 1 (by rfl) ⟨164993, by rfl⟩ : syracuseStep 219991 = 329987) B329987
theorem B580445 : Blo 171799 580445 := bstep (se 3 (by rfl) ⟨108833, by rfl⟩ : syracuseStep 580445 = 217667) B217667
theorem B2481677 : Blo 171799 2481677 := bstep (se 3 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 2481677 = 930629) B930629
theorem B744983 : Blo 171799 744983 := bstep (se 1 (by rfl) ⟨558737, by rfl⟩ : syracuseStep 744983 = 1117475) B1117475
theorem B319297 : Blo 171799 319297 := bstep (se 2 (by rfl) ⟨119736, by rfl⟩ : syracuseStep 319297 = 239473) B239473
theorem B417611 : Blo 171799 417611 := bstep (se 1 (by rfl) ⟨313208, by rfl⟩ : syracuseStep 417611 = 626417) B626417
theorem B876419 : Blo 171799 876419 := bstep (se 1 (by rfl) ⟨657314, by rfl⟩ : syracuseStep 876419 = 1314629) B1314629
theorem B581579 : Blo 171799 581579 := bstep (se 1 (by rfl) ⟨436184, by rfl⟩ : syracuseStep 581579 = 872369) B872369
theorem B1958093 : Blo 171799 1958093 := bstep (se 3 (by rfl) ⟨367142, by rfl⟩ : syracuseStep 1958093 = 734285) B734285
theorem B581849 : Blo 171799 581849 := bstep (se 2 (by rfl) ⟨218193, by rfl⟩ : syracuseStep 581849 = 436387) B436387
theorem B942353 : Blo 171799 942353 := bstep (se 2 (by rfl) ⟨353382, by rfl⟩ : syracuseStep 942353 = 706765) B706765
theorem B1401133 : Blo 171799 1401133 := bstep (se 3 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 1401133 = 525425) B525425
theorem B221707 : Blo 171799 221707 := bstep (se 1 (by rfl) ⟨166280, by rfl⟩ : syracuseStep 221707 = 332561) B332561
theorem B1663523 : Blo 171799 1663523 := bstep (se 1 (by rfl) ⟨1247642, by rfl⟩ : syracuseStep 1663523 = 2495285) B2495285
theorem B2220695 : Blo 171799 2220695 := bstep (se 1 (by rfl) ⟨1665521, by rfl⟩ : syracuseStep 2220695 = 3331043) B3331043
theorem B582551 : Blo 171799 582551 := bstep (se 1 (by rfl) ⟨436913, by rfl⟩ : syracuseStep 582551 = 873827) B873827
theorem B1860569 : Blo 171799 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B746647 : Blo 171799 746647 := bstep (se 1 (by rfl) ⟨559985, by rfl⟩ : syracuseStep 746647 = 1119971) B1119971
theorem B419033 : Blo 171799 419033 := bstep (se 2 (by rfl) ⟨157137, by rfl⟩ : syracuseStep 419033 = 314275) B314275
theorem B583091 : Blo 171799 583091 := bstep (se 1 (by rfl) ⟨437318, by rfl⟩ : syracuseStep 583091 = 874637) B874637
theorem B1598899 : Blo 171799 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B386585 : Blo 171799 386585 := bstep (se 2 (by rfl) ⟨144969, by rfl⟩ : syracuseStep 386585 = 289939) B289939
theorem B386675 : Blo 171799 386675 := bstep (se 1 (by rfl) ⟨290006, by rfl⟩ : syracuseStep 386675 = 580013) B580013
theorem B386711 : Blo 171799 386711 := bstep (se 1 (by rfl) ⟨290033, by rfl⟩ : syracuseStep 386711 = 580067) B580067
theorem B583361 : Blo 171799 583361 := bstep (se 2 (by rfl) ⟨218760, by rfl⟩ : syracuseStep 583361 = 437521) B437521
theorem B386891 : Blo 171799 386891 := bstep (se 1 (by rfl) ⟨290168, by rfl⟩ : syracuseStep 386891 = 580337) B580337
theorem B386945 : Blo 171799 386945 := bstep (se 2 (by rfl) ⟨145104, by rfl⟩ : syracuseStep 386945 = 290209) B290209
theorem B387161 : Blo 171799 387161 := bstep (se 2 (by rfl) ⟨145185, by rfl⟩ : syracuseStep 387161 = 290371) B290371
theorem B387251 : Blo 171799 387251 := bstep (se 1 (by rfl) ⟨290438, by rfl⟩ : syracuseStep 387251 = 580877) B580877
theorem B387287 : Blo 171799 387287 := bstep (se 1 (by rfl) ⟨290465, by rfl⟩ : syracuseStep 387287 = 580931) B580931
theorem B583901 : Blo 171799 583901 := bstep (se 3 (by rfl) ⟨109481, by rfl⟩ : syracuseStep 583901 = 218963) B218963
theorem B387467 : Blo 171799 387467 := bstep (se 1 (by rfl) ⟨290600, by rfl⟩ : syracuseStep 387467 = 581201) B581201
theorem B387521 : Blo 171799 387521 := bstep (se 2 (by rfl) ⟨145320, by rfl⟩ : syracuseStep 387521 = 290641) B290641
theorem B1239569 : Blo 171799 1239569 := bstep (se 2 (by rfl) ⟨464838, by rfl⟩ : syracuseStep 1239569 = 929677) B929677
theorem B354955 : Blo 171799 354955 := bstep (se 1 (by rfl) ⟨266216, by rfl⟩ : syracuseStep 354955 = 532433) B532433
theorem B387737 : Blo 171799 387737 := bstep (se 2 (by rfl) ⟨145401, by rfl⟩ : syracuseStep 387737 = 290803) B290803
theorem B387827 : Blo 171799 387827 := bstep (se 1 (by rfl) ⟨290870, by rfl⟩ : syracuseStep 387827 = 581741) B581741
theorem B387863 : Blo 171799 387863 := bstep (se 1 (by rfl) ⟨290897, by rfl⟩ : syracuseStep 387863 = 581795) B581795
theorem B748433 : Blo 171799 748433 := bstep (se 2 (by rfl) ⟨280662, by rfl⟩ : syracuseStep 748433 = 561325) B561325
theorem B388043 : Blo 171799 388043 := bstep (se 1 (by rfl) ⟨291032, by rfl⟩ : syracuseStep 388043 = 582065) B582065
theorem B388097 : Blo 171799 388097 := bstep (se 2 (by rfl) ⟨145536, by rfl⟩ : syracuseStep 388097 = 291073) B291073
theorem B191531 : Blo 171799 191531 := bstep (se 1 (by rfl) ⟨143648, by rfl⟩ : syracuseStep 191531 = 287297) B287297
theorem B388313 : Blo 171799 388313 := bstep (se 2 (by rfl) ⟨145617, by rfl⟩ : syracuseStep 388313 = 291235) B291235
theorem B388403 : Blo 171799 388403 := bstep (se 1 (by rfl) ⟨291302, by rfl⟩ : syracuseStep 388403 = 582605) B582605
theorem B585035 : Blo 171799 585035 := bstep (se 1 (by rfl) ⟨438776, by rfl⟩ : syracuseStep 585035 = 877553) B877553
theorem B290135 : Blo 171799 290135 := bstep (se 1 (by rfl) ⟨217601, by rfl⟩ : syracuseStep 290135 = 435203) B435203
theorem B388439 : Blo 171799 388439 := bstep (se 1 (by rfl) ⟨291329, by rfl⟩ : syracuseStep 388439 = 582659) B582659
theorem B290263 : Blo 171799 290263 := bstep (se 1 (by rfl) ⟨217697, by rfl⟩ : syracuseStep 290263 = 435395) B435395
theorem B749017 : Blo 171799 749017 := bstep (se 2 (by rfl) ⟨280881, by rfl⟩ : syracuseStep 749017 = 561763) B561763
theorem B1404377 : Blo 171799 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B388619 : Blo 171799 388619 := bstep (se 1 (by rfl) ⟨291464, by rfl⟩ : syracuseStep 388619 = 582929) B582929
theorem B880145 : Blo 171799 880145 := bstep (se 2 (by rfl) ⟨330054, by rfl⟩ : syracuseStep 880145 = 660109) B660109
theorem B388673 : Blo 171799 388673 := bstep (se 2 (by rfl) ⟨145752, by rfl⟩ : syracuseStep 388673 = 291505) B291505
theorem B585305 : Blo 171799 585305 := bstep (se 2 (by rfl) ⟨219489, by rfl⟩ : syracuseStep 585305 = 438979) B438979
theorem B2420375 : Blo 171799 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B880307 : Blo 171799 880307 := bstep (se 1 (by rfl) ⟨660230, by rfl⟩ : syracuseStep 880307 = 1320461) B1320461
theorem B257753 : Blo 171799 257753 := bstep (se 2 (by rfl) ⟨96657, by rfl⟩ : syracuseStep 257753 = 193315) B193315
theorem B388889 : Blo 171799 388889 := bstep (se 2 (by rfl) ⟨145833, by rfl⟩ : syracuseStep 388889 = 291667) B291667
theorem B749357 : Blo 171799 749357 := bstep (se 3 (by rfl) ⟨140504, by rfl⟩ : syracuseStep 749357 = 281009) B281009
theorem B257867 : Blo 171799 257867 := bstep (se 1 (by rfl) ⟨193400, by rfl⟩ : syracuseStep 257867 = 386801) B386801
theorem B257879 : Blo 171799 257879 := bstep (se 1 (by rfl) ⟨193409, by rfl⟩ : syracuseStep 257879 = 386819) B386819
theorem B388979 : Blo 171799 388979 := bstep (se 1 (by rfl) ⟨291734, by rfl⟩ : syracuseStep 388979 = 583469) B583469
theorem B389015 : Blo 171799 389015 := bstep (se 1 (by rfl) ⟨291761, by rfl⟩ : syracuseStep 389015 = 583523) B583523
theorem B257945 : Blo 171799 257945 := bstep (se 2 (by rfl) ⟨96729, by rfl⟩ : syracuseStep 257945 = 193459) B193459
theorem B258059 : Blo 171799 258059 := bstep (se 1 (by rfl) ⟨193544, by rfl⟩ : syracuseStep 258059 = 387089) B387089
theorem B258071 : Blo 171799 258071 := bstep (se 1 (by rfl) ⟨193553, by rfl⟩ : syracuseStep 258071 = 387107) B387107
theorem B290891 : Blo 171799 290891 := bstep (se 1 (by rfl) ⟨218168, by rfl⟩ : syracuseStep 290891 = 436337) B436337
theorem B389195 : Blo 171799 389195 := bstep (se 1 (by rfl) ⟨291896, by rfl⟩ : syracuseStep 389195 = 583793) B583793
theorem B258137 : Blo 171799 258137 := bstep (se 2 (by rfl) ⟨96801, by rfl⟩ : syracuseStep 258137 = 193603) B193603
theorem B389249 : Blo 171799 389249 := bstep (se 2 (by rfl) ⟨145968, by rfl⟩ : syracuseStep 389249 = 291937) B291937
theorem B258251 : Blo 171799 258251 := bstep (se 1 (by rfl) ⟨193688, by rfl⟩ : syracuseStep 258251 = 387377) B387377
theorem B291019 : Blo 171799 291019 := bstep (se 1 (by rfl) ⟨218264, by rfl⟩ : syracuseStep 291019 = 436529) B436529
theorem B258263 : Blo 171799 258263 := bstep (se 1 (by rfl) ⟨193697, by rfl⟩ : syracuseStep 258263 = 387395) B387395
theorem B586007 : Blo 171799 586007 := bstep (se 1 (by rfl) ⟨439505, by rfl⟩ : syracuseStep 586007 = 879011) B879011
theorem B258329 : Blo 171799 258329 := bstep (se 2 (by rfl) ⟨96873, by rfl⟩ : syracuseStep 258329 = 193747) B193747
theorem B913739 : Blo 171799 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B291161 : Blo 171799 291161 := bstep (se 2 (by rfl) ⟨109185, by rfl⟩ : syracuseStep 291161 = 218371) B218371
theorem B389465 : Blo 171799 389465 := bstep (se 2 (by rfl) ⟨146049, by rfl⟩ : syracuseStep 389465 = 292099) B292099
theorem B258443 : Blo 171799 258443 := bstep (se 1 (by rfl) ⟨193832, by rfl⟩ : syracuseStep 258443 = 387665) B387665
theorem B258455 : Blo 171799 258455 := bstep (se 1 (by rfl) ⟨193841, by rfl⟩ : syracuseStep 258455 = 387683) B387683
theorem B389555 : Blo 171799 389555 := bstep (se 1 (by rfl) ⟨292166, by rfl⟩ : syracuseStep 389555 = 584333) B584333
theorem B389591 : Blo 171799 389591 := bstep (se 1 (by rfl) ⟨292193, by rfl⟩ : syracuseStep 389591 = 584387) B584387
theorem B258521 : Blo 171799 258521 := bstep (se 2 (by rfl) ⟨96945, by rfl⟩ : syracuseStep 258521 = 193891) B193891
theorem B291289 : Blo 171799 291289 := bstep (se 2 (by rfl) ⟨109233, by rfl⟩ : syracuseStep 291289 = 218467) B218467
theorem B258635 : Blo 171799 258635 := bstep (se 1 (by rfl) ⟨193976, by rfl⟩ : syracuseStep 258635 = 387953) B387953
theorem B258647 : Blo 171799 258647 := bstep (se 1 (by rfl) ⟨193985, by rfl⟩ : syracuseStep 258647 = 387971) B387971
theorem B389771 : Blo 171799 389771 := bstep (se 1 (by rfl) ⟨292328, by rfl⟩ : syracuseStep 389771 = 584657) B584657
theorem B258713 : Blo 171799 258713 := bstep (se 2 (by rfl) ⟨97017, by rfl⟩ : syracuseStep 258713 = 194035) B194035
theorem B389825 : Blo 171799 389825 := bstep (se 2 (by rfl) ⟨146184, by rfl⟩ : syracuseStep 389825 = 292369) B292369
theorem B258827 : Blo 171799 258827 := bstep (se 1 (by rfl) ⟨194120, by rfl⟩ : syracuseStep 258827 = 388241) B388241
theorem B258839 : Blo 171799 258839 := bstep (se 1 (by rfl) ⟨194129, by rfl⟩ : syracuseStep 258839 = 388259) B388259
theorem B586547 : Blo 171799 586547 := bstep (se 1 (by rfl) ⟨439910, by rfl⟩ : syracuseStep 586547 = 879821) B879821
theorem B258905 : Blo 171799 258905 := bstep (se 2 (by rfl) ⟨97089, by rfl⟩ : syracuseStep 258905 = 194179) B194179
theorem B553817 : Blo 171799 553817 := bstep (se 2 (by rfl) ⟨207681, by rfl⟩ : syracuseStep 553817 = 415363) B415363
theorem B193387 : Blo 171799 193387 := bstep (se 1 (by rfl) ⟨145040, by rfl⟩ : syracuseStep 193387 = 290081) B290081
theorem B390041 : Blo 171799 390041 := bstep (se 2 (by rfl) ⟨146265, by rfl⟩ : syracuseStep 390041 = 292531) B292531
theorem B259019 : Blo 171799 259019 := bstep (se 1 (by rfl) ⟨194264, by rfl⟩ : syracuseStep 259019 = 388529) B388529
theorem B193495 : Blo 171799 193495 := bstep (se 1 (by rfl) ⟨145121, by rfl⟩ : syracuseStep 193495 = 290243) B290243
theorem B259031 : Blo 171799 259031 := bstep (se 1 (by rfl) ⟨194273, by rfl⟩ : syracuseStep 259031 = 388547) B388547
theorem B390131 : Blo 171799 390131 := bstep (se 1 (by rfl) ⟨292598, by rfl⟩ : syracuseStep 390131 = 585197) B585197
theorem B291863 : Blo 171799 291863 := bstep (se 1 (by rfl) ⟨218897, by rfl⟩ : syracuseStep 291863 = 437795) B437795
theorem B390167 : Blo 171799 390167 := bstep (se 1 (by rfl) ⟨292625, by rfl⟩ : syracuseStep 390167 = 585251) B585251
theorem B259097 : Blo 171799 259097 := bstep (se 2 (by rfl) ⟨97161, by rfl⟩ : syracuseStep 259097 = 194323) B194323
theorem B652333 : Blo 171799 652333 := bstep (se 3 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 652333 = 244625) B244625
theorem B586817 : Blo 171799 586817 := bstep (se 2 (by rfl) ⟨220056, by rfl⟩ : syracuseStep 586817 = 440113) B440113
theorem B193675 : Blo 171799 193675 := bstep (se 1 (by rfl) ⟨145256, by rfl⟩ : syracuseStep 193675 = 290513) B290513
theorem B259211 : Blo 171799 259211 := bstep (se 1 (by rfl) ⟨194408, by rfl⟩ : syracuseStep 259211 = 388817) B388817
theorem B259223 : Blo 171799 259223 := bstep (se 1 (by rfl) ⟨194417, by rfl⟩ : syracuseStep 259223 = 388835) B388835
theorem B291991 : Blo 171799 291991 := bstep (se 1 (by rfl) ⟨218993, by rfl⟩ : syracuseStep 291991 = 437987) B437987
theorem B1307825 : Blo 171799 1307825 := bstep (se 2 (by rfl) ⟨490434, by rfl⟩ : syracuseStep 1307825 = 980869) B980869
theorem B390347 : Blo 171799 390347 := bstep (se 1 (by rfl) ⟨292760, by rfl⟩ : syracuseStep 390347 = 585521) B585521
theorem B259289 : Blo 171799 259289 := bstep (se 2 (by rfl) ⟨97233, by rfl⟩ : syracuseStep 259289 = 194467) B194467
theorem B750809 : Blo 171799 750809 := bstep (se 2 (by rfl) ⟨281553, by rfl⟩ : syracuseStep 750809 = 563107) B563107
theorem B193783 : Blo 171799 193783 := bstep (se 1 (by rfl) ⟨145337, by rfl⟩ : syracuseStep 193783 = 290675) B290675
theorem B390401 : Blo 171799 390401 := bstep (se 2 (by rfl) ⟨146400, by rfl⟩ : syracuseStep 390401 = 292801) B292801
theorem B259403 : Blo 171799 259403 := bstep (se 1 (by rfl) ⟨194552, by rfl⟩ : syracuseStep 259403 = 389105) B389105
theorem B259415 : Blo 171799 259415 := bstep (se 1 (by rfl) ⟨194561, by rfl⟩ : syracuseStep 259415 = 389123) B389123
theorem B652637 : Blo 171799 652637 := bstep (se 3 (by rfl) ⟨122369, by rfl⟩ : syracuseStep 652637 = 244739) B244739
theorem B259481 : Blo 171799 259481 := bstep (se 2 (by rfl) ⟨97305, by rfl⟩ : syracuseStep 259481 = 194611) B194611
theorem B193963 : Blo 171799 193963 := bstep (se 1 (by rfl) ⟨145472, by rfl⟩ : syracuseStep 193963 = 290945) B290945
theorem B1111475 : Blo 171799 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B390617 : Blo 171799 390617 := bstep (se 2 (by rfl) ⟨146481, by rfl⟩ : syracuseStep 390617 = 292963) B292963
theorem B259595 : Blo 171799 259595 := bstep (se 1 (by rfl) ⟨194696, by rfl⟩ : syracuseStep 259595 = 389393) B389393
theorem B194071 : Blo 171799 194071 := bstep (se 1 (by rfl) ⟨145553, by rfl⟩ : syracuseStep 194071 = 291107) B291107
theorem B259607 : Blo 171799 259607 := bstep (se 1 (by rfl) ⟨194705, by rfl⟩ : syracuseStep 259607 = 389411) B389411
theorem B390707 : Blo 171799 390707 := bstep (se 1 (by rfl) ⟨293030, by rfl⟩ : syracuseStep 390707 = 586061) B586061
theorem B882251 : Blo 171799 882251 := bstep (se 1 (by rfl) ⟨661688, by rfl⟩ : syracuseStep 882251 = 1323377) B1323377
theorem B390743 : Blo 171799 390743 := bstep (se 1 (by rfl) ⟨293057, by rfl⟩ : syracuseStep 390743 = 586115) B586115
theorem B259673 : Blo 171799 259673 := bstep (se 2 (by rfl) ⟨97377, by rfl⟩ : syracuseStep 259673 = 194755) B194755
theorem B1472093 : Blo 171799 1472093 := bstep (se 3 (by rfl) ⟨276017, by rfl⟩ : syracuseStep 1472093 = 552035) B552035
theorem B587357 : Blo 171799 587357 := bstep (se 3 (by rfl) ⟨110129, by rfl⟩ : syracuseStep 587357 = 220259) B220259
theorem B1308311 : Blo 171799 1308311 := bstep (se 1 (by rfl) ⟨981233, by rfl⟩ : syracuseStep 1308311 = 1962467) B1962467
theorem B194251 : Blo 171799 194251 := bstep (se 1 (by rfl) ⟨145688, by rfl⟩ : syracuseStep 194251 = 291377) B291377
theorem B259787 : Blo 171799 259787 := bstep (se 1 (by rfl) ⟨194840, by rfl⟩ : syracuseStep 259787 = 389681) B389681
theorem B259799 : Blo 171799 259799 := bstep (se 1 (by rfl) ⟨194849, by rfl⟩ : syracuseStep 259799 = 389699) B389699
theorem B292619 : Blo 171799 292619 := bstep (se 1 (by rfl) ⟨219464, by rfl⟩ : syracuseStep 292619 = 438929) B438929
theorem B390923 : Blo 171799 390923 := bstep (se 1 (by rfl) ⟨293192, by rfl⟩ : syracuseStep 390923 = 586385) B586385
theorem B259865 : Blo 171799 259865 := bstep (se 2 (by rfl) ⟨97449, by rfl⟩ : syracuseStep 259865 = 194899) B194899
theorem B194359 : Blo 171799 194359 := bstep (se 1 (by rfl) ⟨145769, by rfl⟩ : syracuseStep 194359 = 291539) B291539
theorem B1767233 : Blo 171799 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B390977 : Blo 171799 390977 := bstep (se 2 (by rfl) ⟨146616, by rfl⟩ : syracuseStep 390977 = 293233) B293233
theorem B259979 : Blo 171799 259979 := bstep (se 1 (by rfl) ⟨194984, by rfl⟩ : syracuseStep 259979 = 389969) B389969
theorem B292747 : Blo 171799 292747 := bstep (se 1 (by rfl) ⟨219560, by rfl⟩ : syracuseStep 292747 = 439121) B439121
theorem B259991 : Blo 171799 259991 := bstep (se 1 (by rfl) ⟨194993, by rfl⟩ : syracuseStep 259991 = 389987) B389987
theorem B260057 : Blo 171799 260057 := bstep (se 2 (by rfl) ⟨97521, by rfl⟩ : syracuseStep 260057 = 195043) B195043
theorem B194539 : Blo 171799 194539 := bstep (se 1 (by rfl) ⟨145904, by rfl⟩ : syracuseStep 194539 = 291809) B291809
theorem B292889 : Blo 171799 292889 := bstep (se 2 (by rfl) ⟨109833, by rfl⟩ : syracuseStep 292889 = 219667) B219667
theorem B391193 : Blo 171799 391193 := bstep (se 2 (by rfl) ⟨146697, by rfl⟩ : syracuseStep 391193 = 293395) B293395
theorem B260171 : Blo 171799 260171 := bstep (se 1 (by rfl) ⟨195128, by rfl⟩ : syracuseStep 260171 = 390257) B390257
theorem B194647 : Blo 171799 194647 := bstep (se 1 (by rfl) ⟨145985, by rfl⟩ : syracuseStep 194647 = 291971) B291971
theorem B260183 : Blo 171799 260183 := bstep (se 1 (by rfl) ⟨195137, by rfl⟩ : syracuseStep 260183 = 390275) B390275
theorem B391283 : Blo 171799 391283 := bstep (se 1 (by rfl) ⟨293462, by rfl⟩ : syracuseStep 391283 = 586925) B586925
theorem B981143 : Blo 171799 981143 := bstep (se 1 (by rfl) ⟨735857, by rfl⟩ : syracuseStep 981143 = 1471715) B1471715
theorem B391319 : Blo 171799 391319 := bstep (se 1 (by rfl) ⟨293489, by rfl⟩ : syracuseStep 391319 = 586979) B586979
theorem B260249 : Blo 171799 260249 := bstep (se 2 (by rfl) ⟨97593, by rfl⟩ : syracuseStep 260249 = 195187) B195187
theorem B293017 : Blo 171799 293017 := bstep (se 2 (by rfl) ⟨109881, by rfl⟩ : syracuseStep 293017 = 219763) B219763
theorem B194827 : Blo 171799 194827 := bstep (se 1 (by rfl) ⟨146120, by rfl⟩ : syracuseStep 194827 = 292241) B292241
theorem B260363 : Blo 171799 260363 := bstep (se 1 (by rfl) ⟨195272, by rfl⟩ : syracuseStep 260363 = 390545) B390545
theorem B260375 : Blo 171799 260375 := bstep (se 1 (by rfl) ⟨195281, by rfl⟩ : syracuseStep 260375 = 390563) B390563
theorem B391499 : Blo 171799 391499 := bstep (se 1 (by rfl) ⟨293624, by rfl⟩ : syracuseStep 391499 = 587249) B587249
theorem B260441 : Blo 171799 260441 := bstep (se 2 (by rfl) ⟨97665, by rfl⟩ : syracuseStep 260441 = 195331) B195331
theorem B194935 : Blo 171799 194935 := bstep (se 1 (by rfl) ⟨146201, by rfl⟩ : syracuseStep 194935 = 292403) B292403
theorem B391553 : Blo 171799 391553 := bstep (se 2 (by rfl) ⟨146832, by rfl⟩ : syracuseStep 391553 = 293665) B293665
theorem B555457 : Blo 171799 555457 := bstep (se 2 (by rfl) ⟨208296, by rfl⟩ : syracuseStep 555457 = 416593) B416593
theorem B260555 : Blo 171799 260555 := bstep (se 1 (by rfl) ⟨195416, by rfl⟩ : syracuseStep 260555 = 390833) B390833
theorem B260567 : Blo 171799 260567 := bstep (se 1 (by rfl) ⟨195425, by rfl⟩ : syracuseStep 260567 = 390851) B390851
theorem B260633 : Blo 171799 260633 := bstep (se 2 (by rfl) ⟨97737, by rfl⟩ : syracuseStep 260633 = 195475) B195475
theorem B195115 : Blo 171799 195115 := bstep (se 1 (by rfl) ⟨146336, by rfl⟩ : syracuseStep 195115 = 292673) B292673
theorem B391769 : Blo 171799 391769 := bstep (se 2 (by rfl) ⟨146913, by rfl⟩ : syracuseStep 391769 = 293827) B293827
theorem B260747 : Blo 171799 260747 := bstep (se 1 (by rfl) ⟨195560, by rfl⟩ : syracuseStep 260747 = 391121) B391121
theorem B195223 : Blo 171799 195223 := bstep (se 1 (by rfl) ⟨146417, by rfl⟩ : syracuseStep 195223 = 292835) B292835
theorem B260759 : Blo 171799 260759 := bstep (se 1 (by rfl) ⟨195569, by rfl⟩ : syracuseStep 260759 = 391139) B391139
theorem B391859 : Blo 171799 391859 := bstep (se 1 (by rfl) ⟨293894, by rfl⟩ : syracuseStep 391859 = 587789) B587789
theorem B588491 : Blo 171799 588491 := bstep (se 1 (by rfl) ⟨441368, by rfl⟩ : syracuseStep 588491 = 882737) B882737
theorem B293591 : Blo 171799 293591 := bstep (se 1 (by rfl) ⟨220193, by rfl⟩ : syracuseStep 293591 = 440387) B440387
theorem B391895 : Blo 171799 391895 := bstep (se 1 (by rfl) ⟨293921, by rfl⟩ : syracuseStep 391895 = 587843) B587843
theorem B260825 : Blo 171799 260825 := bstep (se 2 (by rfl) ⟨97809, by rfl⟩ : syracuseStep 260825 = 195619) B195619
theorem B326425 : Blo 171799 326425 := bstep (se 2 (by rfl) ⟨122409, by rfl⟩ : syracuseStep 326425 = 244819) B244819
theorem B195403 : Blo 171799 195403 := bstep (se 1 (by rfl) ⟨146552, by rfl⟩ : syracuseStep 195403 = 293105) B293105
theorem B260939 : Blo 171799 260939 := bstep (se 1 (by rfl) ⟨195704, by rfl⟩ : syracuseStep 260939 = 391409) B391409
theorem B260951 : Blo 171799 260951 := bstep (se 1 (by rfl) ⟨195713, by rfl⟩ : syracuseStep 260951 = 391427) B391427
theorem B293719 : Blo 171799 293719 := bstep (se 1 (by rfl) ⟨220289, by rfl⟩ : syracuseStep 293719 = 440579) B440579
theorem B359257 : Blo 171799 359257 := bstep (se 2 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 359257 = 269443) B269443
theorem B490333 : Blo 171799 490333 := bstep (se 3 (by rfl) ⟨91937, by rfl⟩ : syracuseStep 490333 = 183875) B183875
theorem B392075 : Blo 171799 392075 := bstep (se 1 (by rfl) ⟨294056, by rfl⟩ : syracuseStep 392075 = 588113) B588113
theorem B261017 : Blo 171799 261017 := bstep (se 2 (by rfl) ⟨97881, by rfl⟩ : syracuseStep 261017 = 195763) B195763
theorem B195511 : Blo 171799 195511 := bstep (se 1 (by rfl) ⟨146633, by rfl⟩ : syracuseStep 195511 = 293267) B293267
theorem B392129 : Blo 171799 392129 := bstep (se 2 (by rfl) ⟨147048, by rfl⟩ : syracuseStep 392129 = 294097) B294097
theorem B621515 : Blo 171799 621515 := bstep (se 1 (by rfl) ⟨466136, by rfl⟩ : syracuseStep 621515 = 932273) B932273
theorem B588761 : Blo 171799 588761 := bstep (se 2 (by rfl) ⟨220785, by rfl⟩ : syracuseStep 588761 = 441571) B441571
theorem B261131 : Blo 171799 261131 := bstep (se 1 (by rfl) ⟨195848, by rfl⟩ : syracuseStep 261131 = 391697) B391697
theorem B261143 : Blo 171799 261143 := bstep (se 1 (by rfl) ⟨195857, by rfl⟩ : syracuseStep 261143 = 391715) B391715
theorem B949313 : Blo 171799 949313 := bstep (se 2 (by rfl) ⟨355992, by rfl⟩ : syracuseStep 949313 = 711985) B711985
theorem B261209 : Blo 171799 261209 := bstep (se 2 (by rfl) ⟨97953, by rfl⟩ : syracuseStep 261209 = 195907) B195907
theorem B195691 : Blo 171799 195691 := bstep (se 1 (by rfl) ⟨146768, by rfl⟩ : syracuseStep 195691 = 293537) B293537
theorem B392345 : Blo 171799 392345 := bstep (se 2 (by rfl) ⟨147129, by rfl⟩ : syracuseStep 392345 = 294259) B294259
theorem B261323 : Blo 171799 261323 := bstep (se 1 (by rfl) ⟨195992, by rfl⟩ : syracuseStep 261323 = 391985) B391985
theorem B195799 : Blo 171799 195799 := bstep (se 1 (by rfl) ⟨146849, by rfl⟩ : syracuseStep 195799 = 293699) B293699
theorem B261335 : Blo 171799 261335 := bstep (se 1 (by rfl) ⟨196001, by rfl⟩ : syracuseStep 261335 = 392003) B392003
theorem B392435 : Blo 171799 392435 := bstep (se 1 (by rfl) ⟨294326, by rfl⟩ : syracuseStep 392435 = 588653) B588653
theorem B392471 : Blo 171799 392471 := bstep (se 1 (by rfl) ⟨294353, by rfl⟩ : syracuseStep 392471 = 588707) B588707
theorem B261401 : Blo 171799 261401 := bstep (se 2 (by rfl) ⟨98025, by rfl⟩ : syracuseStep 261401 = 196051) B196051
theorem B884033 : Blo 171799 884033 := bstep (se 2 (by rfl) ⟨331512, by rfl⟩ : syracuseStep 884033 = 663025) B663025
theorem B326987 : Blo 171799 326987 := bstep (se 1 (by rfl) ⟨245240, by rfl⟩ : syracuseStep 326987 = 490481) B490481
theorem B195959 : Blo 171799 195959 := bstep (se 1 (by rfl) ⟨146969, by rfl⟩ : syracuseStep 195959 = 293939) B293939
theorem B195979 : Blo 171799 195979 := bstep (se 1 (by rfl) ⟨146984, by rfl⟩ : syracuseStep 195979 = 293969) B293969
theorem B261515 : Blo 171799 261515 := bstep (se 1 (by rfl) ⟨196136, by rfl⟩ : syracuseStep 261515 = 392273) B392273
theorem B261527 : Blo 171799 261527 := bstep (se 1 (by rfl) ⟨196145, by rfl⟩ : syracuseStep 261527 = 392291) B392291
theorem B294347 : Blo 171799 294347 := bstep (se 1 (by rfl) ⟨220760, by rfl⟩ : syracuseStep 294347 = 441521) B441521
theorem B392651 : Blo 171799 392651 := bstep (se 1 (by rfl) ⟨294488, by rfl⟩ : syracuseStep 392651 = 588977) B588977
theorem B261593 : Blo 171799 261593 := bstep (se 2 (by rfl) ⟨98097, by rfl⟩ : syracuseStep 261593 = 196195) B196195
theorem B196087 : Blo 171799 196087 := bstep (se 1 (by rfl) ⟨147065, by rfl⟩ : syracuseStep 196087 = 294131) B294131
theorem B327169 : Blo 171799 327169 := bstep (se 2 (by rfl) ⟨122688, by rfl⟩ : syracuseStep 327169 = 245377) B245377
theorem B392705 : Blo 171799 392705 := bstep (se 2 (by rfl) ⟨147264, by rfl⟩ : syracuseStep 392705 = 294529) B294529
theorem B261707 : Blo 171799 261707 := bstep (se 1 (by rfl) ⟨196280, by rfl⟩ : syracuseStep 261707 = 392561) B392561
theorem B294475 : Blo 171799 294475 := bstep (se 1 (by rfl) ⟨220856, by rfl⟩ : syracuseStep 294475 = 441713) B441713
theorem B261719 : Blo 171799 261719 := bstep (se 1 (by rfl) ⟨196289, by rfl⟩ : syracuseStep 261719 = 392579) B392579
theorem B589463 : Blo 171799 589463 := bstep (se 1 (by rfl) ⟨442097, by rfl⟩ : syracuseStep 589463 = 884195) B884195
theorem B261785 : Blo 171799 261785 := bstep (se 2 (by rfl) ⟨98169, by rfl⟩ : syracuseStep 261785 = 196339) B196339
theorem B196267 : Blo 171799 196267 := bstep (se 1 (by rfl) ⟨147200, by rfl⟩ : syracuseStep 196267 = 294401) B294401
theorem B294617 : Blo 171799 294617 := bstep (se 2 (by rfl) ⟨110481, by rfl⟩ : syracuseStep 294617 = 220963) B220963
theorem B392921 : Blo 171799 392921 := bstep (se 2 (by rfl) ⟨147345, by rfl⟩ : syracuseStep 392921 = 294691) B294691
theorem B261899 : Blo 171799 261899 := bstep (se 1 (by rfl) ⟨196424, by rfl⟩ : syracuseStep 261899 = 392849) B392849
theorem B196375 : Blo 171799 196375 := bstep (se 1 (by rfl) ⟨147281, by rfl⟩ : syracuseStep 196375 = 294563) B294563
theorem B261911 : Blo 171799 261911 := bstep (se 1 (by rfl) ⟨196433, by rfl⟩ : syracuseStep 261911 = 392867) B392867
theorem B393011 : Blo 171799 393011 := bstep (se 1 (by rfl) ⟨294758, by rfl⟩ : syracuseStep 393011 = 589517) B589517
theorem B393047 : Blo 171799 393047 := bstep (se 1 (by rfl) ⟨294785, by rfl⟩ : syracuseStep 393047 = 589571) B589571
theorem B261977 : Blo 171799 261977 := bstep (se 2 (by rfl) ⟨98241, by rfl⟩ : syracuseStep 261977 = 196483) B196483
theorem B294745 : Blo 171799 294745 := bstep (se 2 (by rfl) ⟨110529, by rfl⟩ : syracuseStep 294745 = 221059) B221059
theorem B655235 : Blo 171799 655235 := bstep (se 1 (by rfl) ⟨491426, by rfl⟩ : syracuseStep 655235 = 982853) B982853
theorem B655249 : Blo 171799 655249 := bstep (se 2 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 655249 = 491437) B491437
theorem B1343411 : Blo 171799 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B196555 : Blo 171799 196555 := bstep (se 1 (by rfl) ⟨147416, by rfl⟩ : syracuseStep 196555 = 294833) B294833
theorem B262091 : Blo 171799 262091 := bstep (se 1 (by rfl) ⟨196568, by rfl⟩ : syracuseStep 262091 = 393137) B393137
theorem B262103 : Blo 171799 262103 := bstep (se 1 (by rfl) ⟨196577, by rfl⟩ : syracuseStep 262103 = 393155) B393155
theorem B262151 : Blo 171799 262151 := bstep (se 1 (by rfl) ⟨196613, by rfl⟩ : syracuseStep 262151 = 393227) B393227
theorem B262187 : Blo 171799 262187 := bstep (se 1 (by rfl) ⟨196640, by rfl⟩ : syracuseStep 262187 = 393281) B393281
theorem B327739 : Blo 171799 327739 := bstep (se 1 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 327739 = 491609) B491609
theorem B262217 : Blo 171799 262217 := bstep (se 2 (by rfl) ⟨98331, by rfl⟩ : syracuseStep 262217 = 196663) B196663
theorem B393335 : Blo 171799 393335 := bstep (se 1 (by rfl) ⟨295001, by rfl⟩ : syracuseStep 393335 = 590003) B590003
theorem B262331 : Blo 171799 262331 := bstep (se 1 (by rfl) ⟨196748, by rfl⟩ : syracuseStep 262331 = 393497) B393497
theorem B262391 : Blo 171799 262391 := bstep (se 1 (by rfl) ⟨196793, by rfl⟩ : syracuseStep 262391 = 393587) B393587
theorem B2162933 : Blo 171799 2162933 := bstep (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) B202775
theorem B491791 : Blo 171799 491791 := bstep (se 1 (by rfl) ⟨368843, by rfl⟩ : syracuseStep 491791 = 737687) B737687
theorem B262415 : Blo 171799 262415 := bstep (se 1 (by rfl) ⟨196811, by rfl⟩ : syracuseStep 262415 = 393623) B393623
theorem B196879 : Blo 171799 196879 := bstep (se 1 (by rfl) ⟨147659, by rfl⟩ : syracuseStep 196879 = 295319) B295319
theorem B393515 : Blo 171799 393515 := bstep (se 1 (by rfl) ⟨295136, by rfl⟩ : syracuseStep 393515 = 590273) B590273
theorem B295211 : Blo 171799 295211 := bstep (se 1 (by rfl) ⟨221408, by rfl⟩ : syracuseStep 295211 = 442817) B442817
theorem B262457 : Blo 171799 262457 := bstep (se 2 (by rfl) ⟨98421, by rfl⟩ : syracuseStep 262457 = 196843) B196843
theorem B17170805 : Blo 171799 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B262535 : Blo 171799 262535 := bstep (se 1 (by rfl) ⟨196901, by rfl⟩ : syracuseStep 262535 = 393803) B393803
theorem B1868177 : Blo 171799 1868177 := bstep (se 2 (by rfl) ⟨700566, by rfl⟩ : syracuseStep 1868177 = 1401133) B1401133
theorem B262571 : Blo 171799 262571 := bstep (se 1 (by rfl) ⟨196928, by rfl⟩ : syracuseStep 262571 = 393857) B393857
theorem B262601 : Blo 171799 262601 := bstep (se 2 (by rfl) ⟨98475, by rfl⟩ : syracuseStep 262601 = 196951) B196951
theorem B492065 : Blo 171799 492065 := bstep (se 2 (by rfl) ⟨184524, by rfl⟩ : syracuseStep 492065 = 369049) B369049
theorem B328225 : Blo 171799 328225 := bstep (se 2 (by rfl) ⟨123084, by rfl⟩ : syracuseStep 328225 = 246169) B246169
theorem B524843 : Blo 171799 524843 := bstep (se 1 (by rfl) ⟨393632, by rfl⟩ : syracuseStep 524843 = 787265) B787265
theorem B262715 : Blo 171799 262715 := bstep (se 1 (by rfl) ⟨197036, by rfl⟩ : syracuseStep 262715 = 394073) B394073
theorem B262775 : Blo 171799 262775 := bstep (se 1 (by rfl) ⟨197081, by rfl⟩ : syracuseStep 262775 = 394163) B394163
theorem B262799 : Blo 171799 262799 := bstep (se 1 (by rfl) ⟨197099, by rfl⟩ : syracuseStep 262799 = 394199) B394199
theorem B393875 : Blo 171799 393875 := bstep (se 1 (by rfl) ⟨295406, by rfl⟩ : syracuseStep 393875 = 590813) B590813
theorem B295609 : Blo 171799 295609 := bstep (se 2 (by rfl) ⟨110853, by rfl⟩ : syracuseStep 295609 = 221707) B221707
theorem B262841 : Blo 171799 262841 := bstep (se 2 (by rfl) ⟨98565, by rfl⟩ : syracuseStep 262841 = 197131) B197131
theorem B393929 : Blo 171799 393929 := bstep (se 2 (by rfl) ⟨147723, by rfl⟩ : syracuseStep 393929 = 295447) B295447
theorem B262919 : Blo 171799 262919 := bstep (se 1 (by rfl) ⟨197189, by rfl⟩ : syracuseStep 262919 = 394379) B394379
theorem B197383 : Blo 171799 197383 := bstep (se 1 (by rfl) ⟨148037, by rfl⟩ : syracuseStep 197383 = 296075) B296075
theorem B262955 : Blo 171799 262955 := bstep (se 1 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 262955 = 394433) B394433
theorem B590651 : Blo 171799 590651 := bstep (se 1 (by rfl) ⟨442988, by rfl⟩ : syracuseStep 590651 = 885977) B885977
theorem B262985 : Blo 171799 262985 := bstep (se 2 (by rfl) ⟨98619, by rfl⟩ : syracuseStep 262985 = 197239) B197239
theorem B3343193 : Blo 171799 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B6652853 : Blo 171799 6652853 := bstep (se 5 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 6652853 = 623705) B623705
theorem B263099 : Blo 171799 263099 := bstep (se 1 (by rfl) ⟨197324, by rfl⟩ : syracuseStep 263099 = 394649) B394649
theorem B197563 : Blo 171799 197563 := bstep (se 1 (by rfl) ⟨148172, by rfl⟩ : syracuseStep 197563 = 296345) B296345
theorem B263159 : Blo 171799 263159 := bstep (se 1 (by rfl) ⟨197369, by rfl⟩ : syracuseStep 263159 = 394739) B394739
theorem B263183 : Blo 171799 263183 := bstep (se 1 (by rfl) ⟨197387, by rfl⟩ : syracuseStep 263183 = 394775) B394775
theorem B263225 : Blo 171799 263225 := bstep (se 2 (by rfl) ⟨98709, by rfl⟩ : syracuseStep 263225 = 197419) B197419
theorem B3245143 : Blo 171799 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B263303 : Blo 171799 263303 := bstep (se 1 (by rfl) ⟨197477, by rfl⟩ : syracuseStep 263303 = 394955) B394955
theorem B263339 : Blo 171799 263339 := bstep (se 1 (by rfl) ⟨197504, by rfl⟩ : syracuseStep 263339 = 395009) B395009
theorem B263369 : Blo 171799 263369 := bstep (se 2 (by rfl) ⟨98763, by rfl⟩ : syracuseStep 263369 = 197527) B197527
theorem B591137 : Blo 171799 591137 := bstep (se 2 (by rfl) ⟨221676, by rfl⟩ : syracuseStep 591137 = 443353) B443353
theorem B263483 : Blo 171799 263483 := bstep (se 1 (by rfl) ⟨197612, by rfl⟩ : syracuseStep 263483 = 395225) B395225
theorem B296311 : Blo 171799 296311 := bstep (se 1 (by rfl) ⟨222233, by rfl⟩ : syracuseStep 296311 = 444467) B444467
theorem B263543 : Blo 171799 263543 := bstep (se 1 (by rfl) ⟨197657, by rfl⟩ : syracuseStep 263543 = 395315) B395315
theorem B394631 : Blo 171799 394631 := bstep (se 1 (by rfl) ⟨295973, by rfl⟩ : syracuseStep 394631 = 591947) B591947
theorem B263567 : Blo 171799 263567 := bstep (se 1 (by rfl) ⟨197675, by rfl⟩ : syracuseStep 263567 = 395351) B395351
theorem B263609 : Blo 171799 263609 := bstep (se 2 (by rfl) ⟨98853, by rfl⟩ : syracuseStep 263609 = 197707) B197707
theorem B263687 : Blo 171799 263687 := bstep (se 1 (by rfl) ⟨197765, by rfl⟩ : syracuseStep 263687 = 395531) B395531
theorem B493067 : Blo 171799 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B886301 : Blo 171799 886301 := bstep (se 3 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 886301 = 332363) B332363
theorem B394811 : Blo 171799 394811 := bstep (se 1 (by rfl) ⟨296108, by rfl⟩ : syracuseStep 394811 = 592217) B592217
theorem B296507 : Blo 171799 296507 := bstep (se 1 (by rfl) ⟨222380, by rfl⟩ : syracuseStep 296507 = 444761) B444761
theorem B394937 : Blo 171799 394937 := bstep (se 2 (by rfl) ⟨148101, by rfl⟩ : syracuseStep 394937 = 296203) B296203
theorem B329417 : Blo 171799 329417 := bstep (se 2 (by rfl) ⟨123531, by rfl⟩ : syracuseStep 329417 = 247063) B247063
theorem B1476467 : Blo 171799 1476467 := bstep (se 1 (by rfl) ⟨1107350, by rfl⟩ : syracuseStep 1476467 = 2214701) B2214701
theorem B591731 : Blo 171799 591731 := bstep (se 1 (by rfl) ⟨443798, by rfl⟩ : syracuseStep 591731 = 887597) B887597
theorem B2131865 : Blo 171799 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B493465 : Blo 171799 493465 := bstep (se 2 (by rfl) ⟨185049, by rfl⟩ : syracuseStep 493465 = 370099) B370099
theorem B886787 : Blo 171799 886787 := bstep (se 1 (by rfl) ⟨665090, by rfl⟩ : syracuseStep 886787 = 1330181) B1330181
theorem B395279 : Blo 171799 395279 := bstep (se 1 (by rfl) ⟨296459, by rfl⟩ : syracuseStep 395279 = 592919) B592919
theorem B395297 : Blo 171799 395297 := bstep (se 2 (by rfl) ⟨148236, by rfl⟩ : syracuseStep 395297 = 296473) B296473
theorem B493715 : Blo 171799 493715 := bstep (se 1 (by rfl) ⟨370286, by rfl⟩ : syracuseStep 493715 = 740573) B740573
theorem B657665 : Blo 171799 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B657679 : Blo 171799 657679 := bstep (se 1 (by rfl) ⟨493259, by rfl⟩ : syracuseStep 657679 = 986519) B986519
theorem B1116449 : Blo 171799 1116449 := bstep (se 2 (by rfl) ⟨418668, by rfl⟩ : syracuseStep 1116449 = 837337) B837337
theorem B1313171 : Blo 171799 1313171 := bstep (se 1 (by rfl) ⟨984878, by rfl⟩ : syracuseStep 1313171 = 1969757) B1969757
theorem B330131 : Blo 171799 330131 := bstep (se 1 (by rfl) ⟨247598, by rfl⟩ : syracuseStep 330131 = 495197) B495197
theorem B8063381 : Blo 171799 8063381 := bstep (se 6 (by rfl) ⟨188985, by rfl⟩ : syracuseStep 8063381 = 377971) B377971
theorem B330169 : Blo 171799 330169 := bstep (se 2 (by rfl) ⟨123813, by rfl⟩ : syracuseStep 330169 = 247627) B247627
theorem B1673945 : Blo 171799 1673945 := bstep (se 2 (by rfl) ⟨627729, by rfl⟩ : syracuseStep 1673945 = 1255459) B1255459
theorem B1903409 : Blo 171799 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B5639179 : Blo 171799 5639179 := bstep (se 1 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 5639179 = 8458769) B8458769
theorem B265231 : Blo 171799 265231 := bstep (se 1 (by rfl) ⟨198923, by rfl⟩ : syracuseStep 265231 = 397847) B397847
theorem B494707 : Blo 171799 494707 := bstep (se 1 (by rfl) ⟨371030, by rfl⟩ : syracuseStep 494707 = 742061) B742061
theorem B1117421 : Blo 171799 1117421 := bstep (se 3 (by rfl) ⟨209516, by rfl⟩ : syracuseStep 1117421 = 419033) B419033
theorem B658955 : Blo 171799 658955 := bstep (se 1 (by rfl) ⟨494216, by rfl⟩ : syracuseStep 658955 = 988433) B988433
theorem B888407 : Blo 171799 888407 := bstep (se 1 (by rfl) ⟨666305, by rfl⟩ : syracuseStep 888407 = 1332611) B1332611
theorem B7606219 : Blo 171799 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B888893 : Blo 171799 888893 := bstep (se 3 (by rfl) ⟨166667, by rfl⟩ : syracuseStep 888893 = 333335) B333335
theorem B332075 : Blo 171799 332075 := bstep (se 1 (by rfl) ⟨249056, by rfl⟩ : syracuseStep 332075 = 498113) B498113
theorem B561467 : Blo 171799 561467 := bstep (se 1 (by rfl) ⟨421100, by rfl⟩ : syracuseStep 561467 = 842201) B842201
theorem B659897 : Blo 171799 659897 := bstep (se 2 (by rfl) ⟨247461, by rfl⟩ : syracuseStep 659897 = 494923) B494923
theorem B987659 : Blo 171799 987659 := bstep (se 1 (by rfl) ⟨740744, by rfl⟩ : syracuseStep 987659 = 1481489) B1481489
theorem B496313 : Blo 171799 496313 := bstep (se 2 (by rfl) ⟨186117, by rfl⟩ : syracuseStep 496313 = 372235) B372235
theorem B496655 : Blo 171799 496655 := bstep (se 1 (by rfl) ⟨372491, by rfl⟩ : syracuseStep 496655 = 744983) B744983
theorem B333001 : Blo 171799 333001 := bstep (se 2 (by rfl) ⟨124875, by rfl⟩ : syracuseStep 333001 = 249751) B249751
theorem B628235 : Blo 171799 628235 := bstep (se 1 (by rfl) ⟨471176, by rfl⟩ : syracuseStep 628235 = 942353) B942353
theorem B1480463 : Blo 171799 1480463 := bstep (se 1 (by rfl) ⟨1110347, by rfl⟩ : syracuseStep 1480463 = 2220695) B2220695
theorem B497441 : Blo 171799 497441 := bstep (se 2 (by rfl) ⟨186540, by rfl⟩ : syracuseStep 497441 = 373081) B373081
theorem B333715 : Blo 171799 333715 := bstep (se 1 (by rfl) ⟨250286, by rfl⟩ : syracuseStep 333715 = 500573) B500573
theorem B1055425 : Blo 171799 1055425 := bstep (se 2 (by rfl) ⟨395784, by rfl⟩ : syracuseStep 1055425 = 791569) B791569
theorem B269257 : Blo 171799 269257 := bstep (se 2 (by rfl) ⟨100971, by rfl⟩ : syracuseStep 269257 = 201943) B201943
theorem B826379 : Blo 171799 826379 := bstep (se 1 (by rfl) ⟨619784, by rfl⟩ : syracuseStep 826379 = 1239569) B1239569
theorem B662539 : Blo 171799 662539 := bstep (se 1 (by rfl) ⟨496904, by rfl⟩ : syracuseStep 662539 = 993809) B993809
theorem B269455 : Blo 171799 269455 := bstep (se 1 (by rfl) ⟨202091, by rfl⟩ : syracuseStep 269455 = 404183) B404183
theorem B498955 : Blo 171799 498955 := bstep (se 1 (by rfl) ⟨374216, by rfl⟩ : syracuseStep 498955 = 748433) B748433
theorem B498977 : Blo 171799 498977 := bstep (se 2 (by rfl) ⟨187116, by rfl⟩ : syracuseStep 498977 = 374233) B374233
theorem B662843 : Blo 171799 662843 := bstep (se 1 (by rfl) ⟨497132, by rfl⟩ : syracuseStep 662843 = 994265) B994265
theorem B1056185 : Blo 171799 1056185 := bstep (se 2 (by rfl) ⟨396069, by rfl⟩ : syracuseStep 1056185 = 792139) B792139
theorem B499229 : Blo 171799 499229 := bstep (se 3 (by rfl) ⟨93605, by rfl⟩ : syracuseStep 499229 = 187211) B187211
theorem B990893 : Blo 171799 990893 := bstep (se 3 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 990893 = 371585) B371585
theorem B663329 : Blo 171799 663329 := bstep (se 2 (by rfl) ⟨248748, by rfl⟩ : syracuseStep 663329 = 497497) B497497
theorem B171835 : Blo 171799 171835 := bstep (se 1 (by rfl) ⟨128876, by rfl⟩ : syracuseStep 171835 = 257753) B257753
theorem B1122137 : Blo 171799 1122137 := bstep (se 2 (by rfl) ⟨420801, by rfl⟩ : syracuseStep 1122137 = 841603) B841603
theorem B1974131 : Blo 171799 1974131 := bstep (se 1 (by rfl) ⟨1480598, by rfl⟩ : syracuseStep 1974131 = 2961197) B2961197
theorem B499571 : Blo 171799 499571 := bstep (se 1 (by rfl) ⟨374678, by rfl⟩ : syracuseStep 499571 = 749357) B749357
theorem B171911 : Blo 171799 171911 := bstep (se 1 (by rfl) ⟨128933, by rfl⟩ : syracuseStep 171911 = 257867) B257867
theorem B171919 : Blo 171799 171919 := bstep (se 1 (by rfl) ⟨128939, by rfl⟩ : syracuseStep 171919 = 257879) B257879
theorem B171963 : Blo 171799 171963 := bstep (se 1 (by rfl) ⟨128972, by rfl⟩ : syracuseStep 171963 = 257945) B257945
theorem B172039 : Blo 171799 172039 := bstep (se 1 (by rfl) ⟨129029, by rfl⟩ : syracuseStep 172039 = 258059) B258059
theorem B172047 : Blo 171799 172047 := bstep (se 1 (by rfl) ⟨129035, by rfl⟩ : syracuseStep 172047 = 258071) B258071
theorem B172091 : Blo 171799 172091 := bstep (se 1 (by rfl) ⟨129068, by rfl⟩ : syracuseStep 172091 = 258137) B258137
theorem B1056887 : Blo 171799 1056887 := bstep (se 1 (by rfl) ⟨792665, by rfl⟩ : syracuseStep 1056887 = 1585331) B1585331
theorem B172167 : Blo 171799 172167 := bstep (se 1 (by rfl) ⟨129125, by rfl⟩ : syracuseStep 172167 = 258251) B258251
theorem B172175 : Blo 171799 172175 := bstep (se 1 (by rfl) ⟨129131, by rfl⟩ : syracuseStep 172175 = 258263) B258263
theorem B172219 : Blo 171799 172219 := bstep (se 1 (by rfl) ⟨129164, by rfl⟩ : syracuseStep 172219 = 258329) B258329
theorem B172295 : Blo 171799 172295 := bstep (se 1 (by rfl) ⟨129221, by rfl⟩ : syracuseStep 172295 = 258443) B258443
theorem B172303 : Blo 171799 172303 := bstep (se 1 (by rfl) ⟨129227, by rfl⟩ : syracuseStep 172303 = 258455) B258455
theorem B172347 : Blo 171799 172347 := bstep (se 1 (by rfl) ⟨129260, by rfl⟩ : syracuseStep 172347 = 258521) B258521
theorem B172423 : Blo 171799 172423 := bstep (se 1 (by rfl) ⟨129317, by rfl⟩ : syracuseStep 172423 = 258635) B258635
theorem B172431 : Blo 171799 172431 := bstep (se 1 (by rfl) ⟨129323, by rfl⟩ : syracuseStep 172431 = 258647) B258647
theorem B172475 : Blo 171799 172475 := bstep (se 1 (by rfl) ⟨129356, by rfl⟩ : syracuseStep 172475 = 258713) B258713
theorem B532993 : Blo 171799 532993 := bstep (se 2 (by rfl) ⟨199872, by rfl⟩ : syracuseStep 532993 = 399745) B399745
theorem B172551 : Blo 171799 172551 := bstep (se 1 (by rfl) ⟨129413, by rfl⟩ : syracuseStep 172551 = 258827) B258827
theorem B172559 : Blo 171799 172559 := bstep (se 1 (by rfl) ⟨129419, by rfl⟩ : syracuseStep 172559 = 258839) B258839
theorem B172603 : Blo 171799 172603 := bstep (se 1 (by rfl) ⟨129452, by rfl⟩ : syracuseStep 172603 = 258905) B258905
theorem B369211 : Blo 171799 369211 := bstep (se 1 (by rfl) ⟨276908, by rfl⟩ : syracuseStep 369211 = 553817) B553817
theorem B795203 : Blo 171799 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B172679 : Blo 171799 172679 := bstep (se 1 (by rfl) ⟨129509, by rfl⟩ : syracuseStep 172679 = 259019) B259019
theorem B172687 : Blo 171799 172687 := bstep (se 1 (by rfl) ⟨129515, by rfl⟩ : syracuseStep 172687 = 259031) B259031
theorem B172731 : Blo 171799 172731 := bstep (se 1 (by rfl) ⟨129548, by rfl⟩ : syracuseStep 172731 = 259097) B259097
theorem B664301 : Blo 171799 664301 := bstep (se 3 (by rfl) ⟨124556, by rfl⟩ : syracuseStep 664301 = 249113) B249113
theorem B172807 : Blo 171799 172807 := bstep (se 1 (by rfl) ⟨129605, by rfl⟩ : syracuseStep 172807 = 259211) B259211
theorem B172815 : Blo 171799 172815 := bstep (se 1 (by rfl) ⟨129611, by rfl⟩ : syracuseStep 172815 = 259223) B259223
theorem B992033 : Blo 171799 992033 := bstep (se 2 (by rfl) ⟨372012, by rfl⟩ : syracuseStep 992033 = 744025) B744025
theorem B172859 : Blo 171799 172859 := bstep (se 1 (by rfl) ⟨129644, by rfl⟩ : syracuseStep 172859 = 259289) B259289
theorem B500539 : Blo 171799 500539 := bstep (se 1 (by rfl) ⟨375404, by rfl⟩ : syracuseStep 500539 = 750809) B750809
theorem B172935 : Blo 171799 172935 := bstep (se 1 (by rfl) ⟨129701, by rfl⟩ : syracuseStep 172935 = 259403) B259403
theorem B172943 : Blo 171799 172943 := bstep (se 1 (by rfl) ⟨129707, by rfl⟩ : syracuseStep 172943 = 259415) B259415
theorem B435091 : Blo 171799 435091 := bstep (se 1 (by rfl) ⟨326318, by rfl⟩ : syracuseStep 435091 = 652637) B652637
theorem B172987 : Blo 171799 172987 := bstep (se 1 (by rfl) ⟨129740, by rfl⟩ : syracuseStep 172987 = 259481) B259481
theorem B173063 : Blo 171799 173063 := bstep (se 1 (by rfl) ⟨129797, by rfl⟩ : syracuseStep 173063 = 259595) B259595
theorem B1778699 : Blo 171799 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B173071 : Blo 171799 173071 := bstep (se 1 (by rfl) ⟨129803, by rfl⟩ : syracuseStep 173071 = 259607) B259607
theorem B533519 : Blo 171799 533519 := bstep (se 1 (by rfl) ⟨400139, by rfl⟩ : syracuseStep 533519 = 800279) B800279
theorem B435233 : Blo 171799 435233 := bstep (se 2 (by rfl) ⟨163212, by rfl⟩ : syracuseStep 435233 = 326425) B326425
theorem B173115 : Blo 171799 173115 := bstep (se 1 (by rfl) ⟨129836, by rfl⟩ : syracuseStep 173115 = 259673) B259673
theorem B173191 : Blo 171799 173191 := bstep (se 1 (by rfl) ⟨129893, by rfl⟩ : syracuseStep 173191 = 259787) B259787
theorem B173199 : Blo 171799 173199 := bstep (se 1 (by rfl) ⟨129899, by rfl⟩ : syracuseStep 173199 = 259799) B259799
theorem B173243 : Blo 171799 173243 := bstep (se 1 (by rfl) ⟨129932, by rfl⟩ : syracuseStep 173243 = 259865) B259865
theorem B632009 : Blo 171799 632009 := bstep (se 2 (by rfl) ⟨237003, by rfl⟩ : syracuseStep 632009 = 474007) B474007
theorem B173319 : Blo 171799 173319 := bstep (se 1 (by rfl) ⟨129989, by rfl⟩ : syracuseStep 173319 = 259979) B259979
theorem B173327 : Blo 171799 173327 := bstep (se 1 (by rfl) ⟨129995, by rfl⟩ : syracuseStep 173327 = 259991) B259991
theorem B173371 : Blo 171799 173371 := bstep (se 1 (by rfl) ⟨130028, by rfl⟩ : syracuseStep 173371 = 260057) B260057
theorem B173447 : Blo 171799 173447 := bstep (se 1 (by rfl) ⟨130085, by rfl⟩ : syracuseStep 173447 = 260171) B260171
theorem B173455 : Blo 171799 173455 := bstep (se 1 (by rfl) ⟨130091, by rfl⟩ : syracuseStep 173455 = 260183) B260183
theorem B173499 : Blo 171799 173499 := bstep (se 1 (by rfl) ⟨130124, by rfl⟩ : syracuseStep 173499 = 260249) B260249
theorem B173575 : Blo 171799 173575 := bstep (se 1 (by rfl) ⟨130181, by rfl⟩ : syracuseStep 173575 = 260363) B260363
theorem B173583 : Blo 171799 173583 := bstep (se 1 (by rfl) ⟨130187, by rfl⟩ : syracuseStep 173583 = 260375) B260375
theorem B173627 : Blo 171799 173627 := bstep (se 1 (by rfl) ⟨130220, by rfl⟩ : syracuseStep 173627 = 260441) B260441
theorem B173703 : Blo 171799 173703 := bstep (se 1 (by rfl) ⟨130277, by rfl⟩ : syracuseStep 173703 = 260555) B260555
theorem B173711 : Blo 171799 173711 := bstep (se 1 (by rfl) ⟨130283, by rfl⟩ : syracuseStep 173711 = 260567) B260567
theorem B173755 : Blo 171799 173755 := bstep (se 1 (by rfl) ⟨130316, by rfl⟩ : syracuseStep 173755 = 260633) B260633
theorem B173831 : Blo 171799 173831 := bstep (se 1 (by rfl) ⟨130373, by rfl⟩ : syracuseStep 173831 = 260747) B260747
theorem B173839 : Blo 171799 173839 := bstep (se 1 (by rfl) ⟨130379, by rfl⟩ : syracuseStep 173839 = 260759) B260759
theorem B173883 : Blo 171799 173883 := bstep (se 1 (by rfl) ⟨130412, by rfl⟩ : syracuseStep 173883 = 260825) B260825
theorem B173959 : Blo 171799 173959 := bstep (se 1 (by rfl) ⟨130469, by rfl⟩ : syracuseStep 173959 = 260939) B260939
theorem B173967 : Blo 171799 173967 := bstep (se 1 (by rfl) ⟨130475, by rfl⟩ : syracuseStep 173967 = 260951) B260951
theorem B174011 : Blo 171799 174011 := bstep (se 1 (by rfl) ⟨130508, by rfl⟩ : syracuseStep 174011 = 261017) B261017
theorem B436225 : Blo 171799 436225 := bstep (se 2 (by rfl) ⟨163584, by rfl⟩ : syracuseStep 436225 = 327169) B327169
theorem B174087 : Blo 171799 174087 := bstep (se 1 (by rfl) ⟨130565, by rfl⟩ : syracuseStep 174087 = 261131) B261131
theorem B174095 : Blo 171799 174095 := bstep (se 1 (by rfl) ⟨130571, by rfl⟩ : syracuseStep 174095 = 261143) B261143
theorem B632875 : Blo 171799 632875 := bstep (se 1 (by rfl) ⟨474656, by rfl⟩ : syracuseStep 632875 = 949313) B949313
theorem B174139 : Blo 171799 174139 := bstep (se 1 (by rfl) ⟨130604, by rfl⟩ : syracuseStep 174139 = 261209) B261209
theorem B174215 : Blo 171799 174215 := bstep (se 1 (by rfl) ⟨130661, by rfl⟩ : syracuseStep 174215 = 261323) B261323
theorem B174223 : Blo 171799 174223 := bstep (se 1 (by rfl) ⟨130667, by rfl⟩ : syracuseStep 174223 = 261335) B261335
theorem B174267 : Blo 171799 174267 := bstep (se 1 (by rfl) ⟨130700, by rfl⟩ : syracuseStep 174267 = 261401) B261401
theorem B174343 : Blo 171799 174343 := bstep (se 1 (by rfl) ⟨130757, by rfl⟩ : syracuseStep 174343 = 261515) B261515
theorem B174351 : Blo 171799 174351 := bstep (se 1 (by rfl) ⟨130763, by rfl⟩ : syracuseStep 174351 = 261527) B261527
theorem B174395 : Blo 171799 174395 := bstep (se 1 (by rfl) ⟨130796, by rfl⟩ : syracuseStep 174395 = 261593) B261593
theorem B174471 : Blo 171799 174471 := bstep (se 1 (by rfl) ⟨130853, by rfl⟩ : syracuseStep 174471 = 261707) B261707
theorem B174479 : Blo 171799 174479 := bstep (se 1 (by rfl) ⟨130859, by rfl⟩ : syracuseStep 174479 = 261719) B261719
theorem B174523 : Blo 171799 174523 := bstep (se 1 (by rfl) ⟨130892, by rfl⟩ : syracuseStep 174523 = 261785) B261785
theorem B2238941 : Blo 171799 2238941 := bstep (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) B839603
theorem B174599 : Blo 171799 174599 := bstep (se 1 (by rfl) ⟨130949, by rfl⟩ : syracuseStep 174599 = 261899) B261899
theorem B174607 : Blo 171799 174607 := bstep (se 1 (by rfl) ⟨130955, by rfl⟩ : syracuseStep 174607 = 261911) B261911
theorem B174651 : Blo 171799 174651 := bstep (se 1 (by rfl) ⟨130988, by rfl⟩ : syracuseStep 174651 = 261977) B261977
theorem B436823 : Blo 171799 436823 := bstep (se 1 (by rfl) ⟨327617, by rfl⟩ : syracuseStep 436823 = 655235) B655235
theorem B207479 : Blo 171799 207479 := bstep (se 1 (by rfl) ⟨155609, by rfl⟩ : syracuseStep 207479 = 311219) B311219
theorem B895607 : Blo 171799 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B174727 : Blo 171799 174727 := bstep (se 1 (by rfl) ⟨131045, by rfl⟩ : syracuseStep 174727 = 262091) B262091
theorem B174735 : Blo 171799 174735 := bstep (se 1 (by rfl) ⟨131051, by rfl⟩ : syracuseStep 174735 = 262103) B262103
theorem B174779 : Blo 171799 174779 := bstep (se 1 (by rfl) ⟨131084, by rfl⟩ : syracuseStep 174779 = 262169) B262169
theorem B174855 : Blo 171799 174855 := bstep (se 1 (by rfl) ⟨131141, by rfl⟩ : syracuseStep 174855 = 262283) B262283
theorem B174863 : Blo 171799 174863 := bstep (se 1 (by rfl) ⟨131147, by rfl⟩ : syracuseStep 174863 = 262295) B262295
theorem B437035 : Blo 171799 437035 := bstep (se 1 (by rfl) ⟨327776, by rfl⟩ : syracuseStep 437035 = 655553) B655553
theorem B174907 : Blo 171799 174907 := bstep (se 1 (by rfl) ⟨131180, by rfl⟩ : syracuseStep 174907 = 262361) B262361
theorem B666427 : Blo 171799 666427 := bstep (se 1 (by rfl) ⟨499820, by rfl⟩ : syracuseStep 666427 = 999641) B999641
theorem B174983 : Blo 171799 174983 := bstep (se 1 (by rfl) ⟨131237, by rfl⟩ : syracuseStep 174983 = 262475) B262475
theorem B174991 : Blo 171799 174991 := bstep (se 1 (by rfl) ⟨131243, by rfl⟩ : syracuseStep 174991 = 262487) B262487
theorem B371603 : Blo 171799 371603 := bstep (se 1 (by rfl) ⟨278702, by rfl⟩ : syracuseStep 371603 = 557405) B557405
theorem B207787 : Blo 171799 207787 := bstep (se 1 (by rfl) ⟨155840, by rfl⟩ : syracuseStep 207787 = 311681) B311681
theorem B437177 : Blo 171799 437177 := bstep (se 2 (by rfl) ⟨163941, by rfl⟩ : syracuseStep 437177 = 327883) B327883
theorem B175035 : Blo 171799 175035 := bstep (se 1 (by rfl) ⟨131276, by rfl⟩ : syracuseStep 175035 = 262553) B262553
theorem B175111 : Blo 171799 175111 := bstep (se 1 (by rfl) ⟨131333, by rfl⟩ : syracuseStep 175111 = 262667) B262667
theorem B175119 : Blo 171799 175119 := bstep (se 1 (by rfl) ⟨131339, by rfl⟩ : syracuseStep 175119 = 262679) B262679
theorem B175163 : Blo 171799 175163 := bstep (se 1 (by rfl) ⟨131372, by rfl⟩ : syracuseStep 175163 = 262745) B262745
theorem B175239 : Blo 171799 175239 := bstep (se 1 (by rfl) ⟨131429, by rfl⟩ : syracuseStep 175239 = 262859) B262859
theorem B175247 : Blo 171799 175247 := bstep (se 1 (by rfl) ⟨131435, by rfl⟩ : syracuseStep 175247 = 262871) B262871
theorem B175291 : Blo 171799 175291 := bstep (se 1 (by rfl) ⟨131468, by rfl⟩ : syracuseStep 175291 = 262937) B262937
theorem B175367 : Blo 171799 175367 := bstep (se 1 (by rfl) ⟨131525, by rfl⟩ : syracuseStep 175367 = 263051) B263051
theorem B175375 : Blo 171799 175375 := bstep (se 1 (by rfl) ⟨131531, by rfl⟩ : syracuseStep 175375 = 263063) B263063
theorem B666913 : Blo 171799 666913 := bstep (se 2 (by rfl) ⟨250092, by rfl⟩ : syracuseStep 666913 = 500185) B500185
theorem B175419 : Blo 171799 175419 := bstep (se 1 (by rfl) ⟨131564, by rfl⟩ : syracuseStep 175419 = 263129) B263129
theorem B175495 : Blo 171799 175495 := bstep (se 1 (by rfl) ⟨131621, by rfl⟩ : syracuseStep 175495 = 263243) B263243
theorem B175503 : Blo 171799 175503 := bstep (se 1 (by rfl) ⟨131627, by rfl⟩ : syracuseStep 175503 = 263255) B263255
theorem B503225 : Blo 171799 503225 := bstep (se 2 (by rfl) ⟨188709, by rfl⟩ : syracuseStep 503225 = 377419) B377419
theorem B798137 : Blo 171799 798137 := bstep (se 2 (by rfl) ⟨299301, by rfl⟩ : syracuseStep 798137 = 598603) B598603
theorem B175547 : Blo 171799 175547 := bstep (se 1 (by rfl) ⟨131660, by rfl⟩ : syracuseStep 175547 = 263321) B263321
theorem B175623 : Blo 171799 175623 := bstep (se 1 (by rfl) ⟨131717, by rfl⟩ : syracuseStep 175623 = 263435) B263435
theorem B470539 : Blo 171799 470539 := bstep (se 1 (by rfl) ⟨352904, by rfl⟩ : syracuseStep 470539 = 705809) B705809
theorem B175631 : Blo 171799 175631 := bstep (se 1 (by rfl) ⟨131723, by rfl⟩ : syracuseStep 175631 = 263447) B263447
theorem B2436637 : Blo 171799 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B175675 : Blo 171799 175675 := bstep (se 1 (by rfl) ⟨131756, by rfl⟩ : syracuseStep 175675 = 263513) B263513
theorem B175751 : Blo 171799 175751 := bstep (se 1 (by rfl) ⟨131813, by rfl⟩ : syracuseStep 175751 = 263627) B263627
theorem B175759 : Blo 171799 175759 := bstep (se 1 (by rfl) ⟨131819, by rfl⟩ : syracuseStep 175759 = 263639) B263639
theorem B438169 : Blo 171799 438169 := bstep (se 2 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 438169 = 328627) B328627
theorem B438331 : Blo 171799 438331 := bstep (se 1 (by rfl) ⟨328748, by rfl⟩ : syracuseStep 438331 = 657497) B657497
theorem B700535 : Blo 171799 700535 := bstep (se 1 (by rfl) ⟨525401, by rfl⟩ : syracuseStep 700535 = 1050803) B1050803
theorem B438473 : Blo 171799 438473 := bstep (se 2 (by rfl) ⟨164427, by rfl⟩ : syracuseStep 438473 = 328855) B328855
theorem B438817 : Blo 171799 438817 := bstep (se 2 (by rfl) ⟨164556, by rfl⟩ : syracuseStep 438817 = 329113) B329113
theorem B635435 : Blo 171799 635435 := bstep (se 1 (by rfl) ⟨476576, by rfl⟩ : syracuseStep 635435 = 953153) B953153
theorem B471611 : Blo 171799 471611 := bstep (se 1 (by rfl) ⟨353708, by rfl⟩ : syracuseStep 471611 = 707417) B707417
theorem B471869 : Blo 171799 471869 := bstep (se 3 (by rfl) ⟨88475, by rfl⟩ : syracuseStep 471869 = 176951) B176951
theorem B209935 : Blo 171799 209935 := bstep (se 1 (by rfl) ⟨157451, by rfl⟩ : syracuseStep 209935 = 314903) B314903
theorem B439415 : Blo 171799 439415 := bstep (se 1 (by rfl) ⟨329561, by rfl⟩ : syracuseStep 439415 = 659123) B659123
theorem B996907 : Blo 171799 996907 := bstep (se 1 (by rfl) ⟨747680, by rfl⟩ : syracuseStep 996907 = 1495361) B1495361
theorem B472711 : Blo 171799 472711 := bstep (se 1 (by rfl) ⟨354533, by rfl⟩ : syracuseStep 472711 = 709067) B709067
theorem B374473 : Blo 171799 374473 := bstep (se 2 (by rfl) ⟨140427, by rfl⟩ : syracuseStep 374473 = 280855) B280855
theorem B6731585 : Blo 171799 6731585 := bstep (se 2 (by rfl) ⟨2524344, by rfl⟩ : syracuseStep 6731585 = 5048689) B5048689
theorem B899095 : Blo 171799 899095 := bstep (se 1 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 899095 = 1348643) B1348643
theorem B1620101 : Blo 171799 1620101 := bstep (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) B303769
theorem B473273 : Blo 171799 473273 := bstep (se 2 (by rfl) ⟨177477, by rfl⟩ : syracuseStep 473273 = 354955) B354955
theorem B374969 : Blo 171799 374969 := bstep (se 2 (by rfl) ⟨140613, by rfl⟩ : syracuseStep 374969 = 281227) B281227
theorem B1489211 : Blo 171799 1489211 := bstep (se 1 (by rfl) ⟨1116908, by rfl⟩ : syracuseStep 1489211 = 2233817) B2233817
theorem B440711 : Blo 171799 440711 := bstep (se 1 (by rfl) ⟨330533, by rfl⟩ : syracuseStep 440711 = 661067) B661067
theorem B1063315 : Blo 171799 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B440761 : Blo 171799 440761 := bstep (se 2 (by rfl) ⟨165285, by rfl⟩ : syracuseStep 440761 = 330571) B330571
theorem B277177 : Blo 171799 277177 := bstep (se 2 (by rfl) ⟨103941, by rfl⟩ : syracuseStep 277177 = 207883) B207883
theorem B998365 : Blo 171799 998365 := bstep (se 3 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 998365 = 374387) B374387
theorem B441359 : Blo 171799 441359 := bstep (se 1 (by rfl) ⟨331019, by rfl⟩ : syracuseStep 441359 = 662039) B662039
theorem B703745 : Blo 171799 703745 := bstep (se 2 (by rfl) ⟨263904, by rfl⟩ : syracuseStep 703745 = 527809) B527809
theorem B998689 : Blo 171799 998689 := bstep (se 2 (by rfl) ⟨374508, by rfl⟩ : syracuseStep 998689 = 749017) B749017
theorem B245035 : Blo 171799 245035 := bstep (se 1 (by rfl) ⟨183776, by rfl⟩ : syracuseStep 245035 = 367553) B367553
theorem B507179 : Blo 171799 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B638417 : Blo 171799 638417 := bstep (se 2 (by rfl) ⟨239406, by rfl⟩ : syracuseStep 638417 = 478813) B478813
theorem B245263 : Blo 171799 245263 := bstep (se 1 (by rfl) ⟨183947, by rfl⟩ : syracuseStep 245263 = 367895) B367895
theorem B1654451 : Blo 171799 1654451 := bstep (se 1 (by rfl) ⟨1240838, by rfl⟩ : syracuseStep 1654451 = 2481677) B2481677
theorem B442057 : Blo 171799 442057 := bstep (se 2 (by rfl) ⟨165771, by rfl⟩ : syracuseStep 442057 = 331543) B331543
theorem B442199 : Blo 171799 442199 := bstep (se 1 (by rfl) ⟨331649, by rfl⟩ : syracuseStep 442199 = 663299) B663299
theorem B245639 : Blo 171799 245639 := bstep (se 1 (by rfl) ⟨184229, by rfl⟩ : syracuseStep 245639 = 368459) B368459
theorem B278407 : Blo 171799 278407 := bstep (se 1 (by rfl) ⟨208805, by rfl⟩ : syracuseStep 278407 = 417611) B417611
theorem B901187 : Blo 171799 901187 := bstep (se 1 (by rfl) ⟨675890, by rfl⟩ : syracuseStep 901187 = 1351781) B1351781
theorem B704783 : Blo 171799 704783 := bstep (se 1 (by rfl) ⟨528587, by rfl⟩ : syracuseStep 704783 = 1057175) B1057175
theorem B442711 : Blo 171799 442711 := bstep (se 1 (by rfl) ⟨332033, by rfl⟩ : syracuseStep 442711 = 664067) B664067
theorem B2474387 : Blo 171799 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B541129 : Blo 171799 541129 := bstep (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) B405847
theorem B3982117 : Blo 171799 3982117 := bstep (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) B746647
theorem B2212697 : Blo 171799 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B1885421 : Blo 171799 1885421 := bstep (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) B707033
theorem B247097 : Blo 171799 247097 := bstep (se 2 (by rfl) ⟨92661, by rfl⟩ : syracuseStep 247097 = 185323) B185323
theorem B869777 : Blo 171799 869777 := bstep (se 2 (by rfl) ⟨326166, by rfl⟩ : syracuseStep 869777 = 652333) B652333
theorem B837067 : Blo 171799 837067 := bstep (se 1 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 837067 = 1255601) B1255601
theorem B837143 : Blo 171799 837143 := bstep (se 1 (by rfl) ⟨627857, by rfl⟩ : syracuseStep 837143 = 1255715) B1255715
theorem B444275 : Blo 171799 444275 := bstep (se 1 (by rfl) ⟨333206, by rfl⟩ : syracuseStep 444275 = 666413) B666413
theorem B444295 : Blo 171799 444295 := bstep (se 1 (by rfl) ⟨333221, by rfl⟩ : syracuseStep 444295 = 666443) B666443
theorem B247951 : Blo 171799 247951 := bstep (se 1 (by rfl) ⟨185963, by rfl⟩ : syracuseStep 247951 = 371927) B371927
theorem B936251 : Blo 171799 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B444791 : Blo 171799 444791 := bstep (se 1 (by rfl) ⟨333593, by rfl⟩ : syracuseStep 444791 = 667187) B667187
theorem B248393 : Blo 171799 248393 := bstep (se 2 (by rfl) ⟨93147, by rfl⟩ : syracuseStep 248393 = 186295) B186295
theorem B248521 : Blo 171799 248521 := bstep (se 2 (by rfl) ⟨93195, by rfl⟩ : syracuseStep 248521 = 186391) B186391
theorem B510749 : Blo 171799 510749 := bstep (se 3 (by rfl) ⟨95765, by rfl⟩ : syracuseStep 510749 = 191531) B191531
theorem B2837429 : Blo 171799 2837429 := bstep (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) B266009
theorem B248761 : Blo 171799 248761 := bstep (se 2 (by rfl) ⟨93285, by rfl⟩ : syracuseStep 248761 = 186571) B186571
theorem B1493963 : Blo 171799 1493963 := bstep (se 1 (by rfl) ⟨1120472, by rfl⟩ : syracuseStep 1493963 = 2240945) B2240945
theorem B740609 : Blo 171799 740609 := bstep (se 2 (by rfl) ⟨277728, by rfl⟩ : syracuseStep 740609 = 555457) B555457
theorem B413113 : Blo 171799 413113 := bstep (se 2 (by rfl) ⟨154917, by rfl⟩ : syracuseStep 413113 = 309835) B309835
theorem B871883 : Blo 171799 871883 := bstep (se 1 (by rfl) ⟨653912, by rfl⟩ : syracuseStep 871883 = 1307825) B1307825
theorem B740983 : Blo 171799 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B1199809 : Blo 171799 1199809 := bstep (se 2 (by rfl) ⟨449928, by rfl⟩ : syracuseStep 1199809 = 899857) B899857
theorem B872207 : Blo 171799 872207 := bstep (se 1 (by rfl) ⟨654155, by rfl⟩ : syracuseStep 872207 = 1308311) B1308311
theorem B479009 : Blo 171799 479009 := bstep (se 2 (by rfl) ⟨179628, by rfl⟩ : syracuseStep 479009 = 359257) B359257
theorem B1200025 : Blo 171799 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B249871 : Blo 171799 249871 := bstep (se 1 (by rfl) ⟨187403, by rfl⟩ : syracuseStep 249871 = 374807) B374807
theorem B2806163 : Blo 171799 2806163 := bstep (se 1 (by rfl) ⟨2104622, by rfl⟩ : syracuseStep 2806163 = 4209245) B4209245
theorem B414209 : Blo 171799 414209 := bstep (se 2 (by rfl) ⟨155328, by rfl⟩ : syracuseStep 414209 = 310657) B310657
theorem B840203 : Blo 171799 840203 := bstep (se 1 (by rfl) ⟨630152, by rfl⟩ : syracuseStep 840203 = 1260305) B1260305
theorem B18469397 : Blo 171799 18469397 := bstep (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) B865753
theorem B414343 : Blo 171799 414343 := bstep (se 1 (by rfl) ⟨310757, by rfl⟩ : syracuseStep 414343 = 621515) B621515
theorem B840385 : Blo 171799 840385 := bstep (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) B630289
theorem B414497 : Blo 171799 414497 := bstep (se 2 (by rfl) ⟨155436, by rfl⟩ : syracuseStep 414497 = 310873) B310873
theorem B217991 : Blo 171799 217991 := bstep (se 1 (by rfl) ⟨163493, by rfl⟩ : syracuseStep 217991 = 326987) B326987
theorem B873665 : Blo 171799 873665 := bstep (se 2 (by rfl) ⟨327624, by rfl⟩ : syracuseStep 873665 = 655249) B655249
theorem B218639 : Blo 171799 218639 := bstep (se 1 (by rfl) ⟨163979, by rfl⟩ : syracuseStep 218639 = 327959) B327959
theorem B2840777 : Blo 171799 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B940403 : Blo 171799 940403 := bstep (se 1 (by rfl) ⟨705302, by rfl⟩ : syracuseStep 940403 = 1410605) B1410605
theorem B874961 : Blo 171799 874961 := bstep (se 2 (by rfl) ⟨328110, by rfl⟩ : syracuseStep 874961 = 656221) B656221
theorem B186895 : Blo 171799 186895 := bstep (se 1 (by rfl) ⟨140171, by rfl⟩ : syracuseStep 186895 = 280343) B280343
theorem B1891187 : Blo 171799 1891187 := bstep (se 1 (by rfl) ⟨1418390, by rfl⟩ : syracuseStep 1891187 = 2836781) B2836781
theorem B580499 : Blo 171799 580499 := bstep (se 1 (by rfl) ⟨435374, by rfl⟩ : syracuseStep 580499 = 870749) B870749
theorem B187655 : Blo 171799 187655 := bstep (se 1 (by rfl) ⟨140741, by rfl⟩ : syracuseStep 187655 = 281483) B281483
theorem B941465 : Blo 171799 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B1335041 : Blo 171799 1335041 := bstep (se 2 (by rfl) ⟨500640, by rfl⟩ : syracuseStep 1335041 = 1001281) B1001281
theorem B941959 : Blo 171799 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B581903 : Blo 171799 581903 := bstep (se 1 (by rfl) ⟨436427, by rfl⟩ : syracuseStep 581903 = 872855) B872855
theorem B221611 : Blo 171799 221611 := bstep (se 1 (by rfl) ⟨166208, by rfl⟩ : syracuseStep 221611 = 332417) B332417
theorem B877067 : Blo 171799 877067 := bstep (se 1 (by rfl) ⟨657800, by rfl⟩ : syracuseStep 877067 = 1315601) B1315601
theorem B582173 : Blo 171799 582173 := bstep (se 3 (by rfl) ⟨109157, by rfl⟩ : syracuseStep 582173 = 218315) B218315
theorem B418439 : Blo 171799 418439 := bstep (se 1 (by rfl) ⟨313829, by rfl⟩ : syracuseStep 418439 = 627659) B627659
theorem B877229 : Blo 171799 877229 := bstep (se 3 (by rfl) ⟨164480, by rfl⟩ : syracuseStep 877229 = 328961) B328961
theorem B1860353 : Blo 171799 1860353 := bstep (se 2 (by rfl) ⟨697632, by rfl⟩ : syracuseStep 1860353 = 1395265) B1395265
theorem B1991627 : Blo 171799 1991627 := bstep (se 1 (by rfl) ⟨1493720, by rfl⟩ : syracuseStep 1991627 = 2987441) B2987441
theorem B386603 : Blo 171799 386603 := bstep (se 1 (by rfl) ⟨289952, by rfl⟩ : syracuseStep 386603 = 579905) B579905
theorem B550601 : Blo 171799 550601 := bstep (se 2 (by rfl) ⟨206475, by rfl⟩ : syracuseStep 550601 = 412951) B412951
theorem B386963 : Blo 171799 386963 := bstep (se 1 (by rfl) ⟨290222, by rfl⟩ : syracuseStep 386963 = 580445) B580445
theorem B583577 : Blo 171799 583577 := bstep (se 2 (by rfl) ⟨218841, by rfl⟩ : syracuseStep 583577 = 437683) B437683
theorem B387017 : Blo 171799 387017 := bstep (se 2 (by rfl) ⟨145131, by rfl⟩ : syracuseStep 387017 = 290263) B290263
theorem B419899 : Blo 171799 419899 := bstep (se 1 (by rfl) ⟨314924, by rfl⟩ : syracuseStep 419899 = 629849) B629849
theorem B878849 : Blo 171799 878849 := bstep (se 2 (by rfl) ⟨329568, by rfl⟩ : syracuseStep 878849 = 659137) B659137
theorem B551227 : Blo 171799 551227 := bstep (se 1 (by rfl) ⟨413420, by rfl⟩ : syracuseStep 551227 = 826841) B826841
theorem B3303827 : Blo 171799 3303827 := bstep (se 1 (by rfl) ⟨2477870, by rfl⟩ : syracuseStep 3303827 = 4955741) B4955741
theorem B1501649 : Blo 171799 1501649 := bstep (se 2 (by rfl) ⟨563118, by rfl⟩ : syracuseStep 1501649 = 1126237) B1126237
theorem B748075 : Blo 171799 748075 := bstep (se 1 (by rfl) ⟨561056, by rfl⟩ : syracuseStep 748075 = 1122113) B1122113
theorem B584279 : Blo 171799 584279 := bstep (se 1 (by rfl) ⟨438209, by rfl⟩ : syracuseStep 584279 = 876419) B876419
theorem B387719 : Blo 171799 387719 := bstep (se 1 (by rfl) ⟨290789, by rfl⟩ : syracuseStep 387719 = 581579) B581579
theorem B1305395 : Blo 171799 1305395 := bstep (se 1 (by rfl) ⟨979046, by rfl⟩ : syracuseStep 1305395 = 1958093) B1958093
theorem B387899 : Blo 171799 387899 := bstep (se 1 (by rfl) ⟨290924, by rfl⟩ : syracuseStep 387899 = 581849) B581849
theorem B388025 : Blo 171799 388025 := bstep (se 2 (by rfl) ⟨145509, by rfl⟩ : syracuseStep 388025 = 291019) B291019
theorem B1109015 : Blo 171799 1109015 := bstep (se 1 (by rfl) ⟨831761, by rfl⟩ : syracuseStep 1109015 = 1663523) B1663523
theorem B879659 : Blo 171799 879659 := bstep (se 1 (by rfl) ⟨659744, by rfl⟩ : syracuseStep 879659 = 1319489) B1319489
theorem B584765 : Blo 171799 584765 := bstep (se 3 (by rfl) ⟨109643, by rfl⟩ : syracuseStep 584765 = 219287) B219287
theorem B289993 : Blo 171799 289993 := bstep (se 2 (by rfl) ⟨108747, by rfl⟩ : syracuseStep 289993 = 217495) B217495
theorem B388367 : Blo 171799 388367 := bstep (se 1 (by rfl) ⟨291275, by rfl⟩ : syracuseStep 388367 = 582551) B582551
theorem B388385 : Blo 171799 388385 := bstep (se 2 (by rfl) ⟨145644, by rfl⟩ : syracuseStep 388385 = 291289) B291289
theorem B1240379 : Blo 171799 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B388727 : Blo 171799 388727 := bstep (se 1 (by rfl) ⟨291545, by rfl⟩ : syracuseStep 388727 = 583091) B583091
theorem B1994419 : Blo 171799 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B257723 : Blo 171799 257723 := bstep (se 1 (by rfl) ⟨193292, by rfl⟩ : syracuseStep 257723 = 386585) B386585
theorem B257783 : Blo 171799 257783 := bstep (se 1 (by rfl) ⟨193337, by rfl⟩ : syracuseStep 257783 = 386675) B386675
theorem B257807 : Blo 171799 257807 := bstep (se 1 (by rfl) ⟨193355, by rfl⟩ : syracuseStep 257807 = 386711) B386711
theorem B388907 : Blo 171799 388907 := bstep (se 1 (by rfl) ⟨291680, by rfl⟩ : syracuseStep 388907 = 583361) B583361
theorem B3534637 : Blo 171799 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B257849 : Blo 171799 257849 := bstep (se 2 (by rfl) ⟨96693, by rfl⟩ : syracuseStep 257849 = 193387) B193387
theorem B257927 : Blo 171799 257927 := bstep (se 1 (by rfl) ⟨193445, by rfl⟩ : syracuseStep 257927 = 386891) B386891
theorem B290695 : Blo 171799 290695 := bstep (se 1 (by rfl) ⟨218021, by rfl⟩ : syracuseStep 290695 = 436043) B436043
theorem B257963 : Blo 171799 257963 := bstep (se 1 (by rfl) ⟨193472, by rfl⟩ : syracuseStep 257963 = 386945) B386945
theorem B257993 : Blo 171799 257993 := bstep (se 2 (by rfl) ⟨96747, by rfl⟩ : syracuseStep 257993 = 193495) B193495
theorem B258107 : Blo 171799 258107 := bstep (se 1 (by rfl) ⟨193580, by rfl⟩ : syracuseStep 258107 = 387161) B387161
theorem B258167 : Blo 171799 258167 := bstep (se 1 (by rfl) ⟨193625, by rfl⟩ : syracuseStep 258167 = 387251) B387251
theorem B422023 : Blo 171799 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B258191 : Blo 171799 258191 := bstep (se 1 (by rfl) ⟨193643, by rfl⟩ : syracuseStep 258191 = 387287) B387287
theorem B389267 : Blo 171799 389267 := bstep (se 1 (by rfl) ⟨291950, by rfl⟩ : syracuseStep 389267 = 583901) B583901
theorem B258233 : Blo 171799 258233 := bstep (se 2 (by rfl) ⟨96837, by rfl⟩ : syracuseStep 258233 = 193675) B193675
theorem B389321 : Blo 171799 389321 := bstep (se 2 (by rfl) ⟨145995, by rfl⟩ : syracuseStep 389321 = 291991) B291991
theorem B258311 : Blo 171799 258311 := bstep (se 1 (by rfl) ⟨193733, by rfl⟩ : syracuseStep 258311 = 387467) B387467
theorem B258347 : Blo 171799 258347 := bstep (se 1 (by rfl) ⟨193760, by rfl⟩ : syracuseStep 258347 = 387521) B387521
theorem B880955 : Blo 171799 880955 := bstep (se 1 (by rfl) ⟨660716, by rfl⟩ : syracuseStep 880955 = 1321433) B1321433
theorem B258377 : Blo 171799 258377 := bstep (se 2 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 258377 = 193783) B193783
theorem B586169 : Blo 171799 586169 := bstep (se 2 (by rfl) ⟨219813, by rfl⟩ : syracuseStep 586169 = 439627) B439627
theorem B258491 : Blo 171799 258491 := bstep (se 1 (by rfl) ⟨193868, by rfl⟩ : syracuseStep 258491 = 387737) B387737
theorem B881117 : Blo 171799 881117 := bstep (se 3 (by rfl) ⟨165209, by rfl⟩ : syracuseStep 881117 = 330419) B330419
theorem B258551 : Blo 171799 258551 := bstep (se 1 (by rfl) ⟨193913, by rfl⟩ : syracuseStep 258551 = 387827) B387827
theorem B258575 : Blo 171799 258575 := bstep (se 1 (by rfl) ⟨193931, by rfl⟩ : syracuseStep 258575 = 387863) B387863
theorem B291343 : Blo 171799 291343 := bstep (se 1 (by rfl) ⟨218507, by rfl⟩ : syracuseStep 291343 = 437015) B437015
theorem B258617 : Blo 171799 258617 := bstep (se 2 (by rfl) ⟨96981, by rfl⟩ : syracuseStep 258617 = 193963) B193963
theorem B258695 : Blo 171799 258695 := bstep (se 1 (by rfl) ⟨194021, by rfl⟩ : syracuseStep 258695 = 388043) B388043
theorem B258731 : Blo 171799 258731 := bstep (se 1 (by rfl) ⟨194048, by rfl⟩ : syracuseStep 258731 = 388097) B388097
theorem B258761 : Blo 171799 258761 := bstep (se 2 (by rfl) ⟨97035, by rfl⟩ : syracuseStep 258761 = 194071) B194071
theorem B979685 : Blo 171799 979685 := bstep (se 4 (by rfl) ⟨91845, by rfl⟩ : syracuseStep 979685 = 183691) B183691
theorem B881441 : Blo 171799 881441 := bstep (se 2 (by rfl) ⟨330540, by rfl⟩ : syracuseStep 881441 = 661081) B661081
theorem B258875 : Blo 171799 258875 := bstep (se 1 (by rfl) ⟨194156, by rfl⟩ : syracuseStep 258875 = 388313) B388313
theorem B258935 : Blo 171799 258935 := bstep (se 1 (by rfl) ⟨194201, by rfl⟩ : syracuseStep 258935 = 388403) B388403
theorem B390023 : Blo 171799 390023 := bstep (se 1 (by rfl) ⟨292517, by rfl⟩ : syracuseStep 390023 = 585035) B585035
theorem B193423 : Blo 171799 193423 := bstep (se 1 (by rfl) ⟨145067, by rfl⟩ : syracuseStep 193423 = 290135) B290135
theorem B258959 : Blo 171799 258959 := bstep (se 1 (by rfl) ⟨194219, by rfl⟩ : syracuseStep 258959 = 388439) B388439
theorem B259001 : Blo 171799 259001 := bstep (se 2 (by rfl) ⟨97125, by rfl⟩ : syracuseStep 259001 = 194251) B194251
theorem B259079 : Blo 171799 259079 := bstep (se 1 (by rfl) ⟨194309, by rfl⟩ : syracuseStep 259079 = 388619) B388619
theorem B586763 : Blo 171799 586763 := bstep (se 1 (by rfl) ⟨440072, by rfl⟩ : syracuseStep 586763 = 880145) B880145
theorem B259115 : Blo 171799 259115 := bstep (se 1 (by rfl) ⟨194336, by rfl⟩ : syracuseStep 259115 = 388673) B388673
theorem B291883 : Blo 171799 291883 := bstep (se 1 (by rfl) ⟨218912, by rfl⟩ : syracuseStep 291883 = 437825) B437825
theorem B390203 : Blo 171799 390203 := bstep (se 1 (by rfl) ⟨292652, by rfl⟩ : syracuseStep 390203 = 585305) B585305
theorem B259145 : Blo 171799 259145 := bstep (se 2 (by rfl) ⟨97179, by rfl⟩ : syracuseStep 259145 = 194359) B194359
theorem B586871 : Blo 171799 586871 := bstep (se 1 (by rfl) ⟨440153, by rfl⟩ : syracuseStep 586871 = 880307) B880307
theorem B292025 : Blo 171799 292025 := bstep (se 2 (by rfl) ⟨109509, by rfl⟩ : syracuseStep 292025 = 219019) B219019
theorem B259259 : Blo 171799 259259 := bstep (se 1 (by rfl) ⟨194444, by rfl⟩ : syracuseStep 259259 = 388889) B388889
theorem B390329 : Blo 171799 390329 := bstep (se 2 (by rfl) ⟨146373, by rfl⟩ : syracuseStep 390329 = 292747) B292747
theorem B259319 : Blo 171799 259319 := bstep (se 1 (by rfl) ⟨194489, by rfl⟩ : syracuseStep 259319 = 388979) B388979
theorem B259343 : Blo 171799 259343 := bstep (se 1 (by rfl) ⟨194507, by rfl⟩ : syracuseStep 259343 = 389015) B389015
theorem B259385 : Blo 171799 259385 := bstep (se 2 (by rfl) ⟨97269, by rfl⟩ : syracuseStep 259385 = 194539) B194539
theorem B193927 : Blo 171799 193927 := bstep (se 1 (by rfl) ⟨145445, by rfl⟩ : syracuseStep 193927 = 290891) B290891
theorem B259463 : Blo 171799 259463 := bstep (se 1 (by rfl) ⟨194597, by rfl⟩ : syracuseStep 259463 = 389195) B389195
theorem B980369 : Blo 171799 980369 := bstep (se 2 (by rfl) ⟨367638, by rfl⟩ : syracuseStep 980369 = 735277) B735277
theorem B259499 : Blo 171799 259499 := bstep (se 1 (by rfl) ⟨194624, by rfl⟩ : syracuseStep 259499 = 389249) B389249
theorem B259529 : Blo 171799 259529 := bstep (se 2 (by rfl) ⟨97323, by rfl⟩ : syracuseStep 259529 = 194647) B194647
theorem B390671 : Blo 171799 390671 := bstep (se 1 (by rfl) ⟨293003, by rfl⟩ : syracuseStep 390671 = 586007) B586007
theorem B390689 : Blo 171799 390689 := bstep (se 2 (by rfl) ⟨146508, by rfl⟩ : syracuseStep 390689 = 293017) B293017
theorem B194107 : Blo 171799 194107 := bstep (se 1 (by rfl) ⟨145580, by rfl⟩ : syracuseStep 194107 = 291161) B291161
theorem B259643 : Blo 171799 259643 := bstep (se 1 (by rfl) ⟨194732, by rfl⟩ : syracuseStep 259643 = 389465) B389465
theorem B259703 : Blo 171799 259703 := bstep (se 1 (by rfl) ⟨194777, by rfl⟩ : syracuseStep 259703 = 389555) B389555
theorem B259727 : Blo 171799 259727 := bstep (se 1 (by rfl) ⟨194795, by rfl⟩ : syracuseStep 259727 = 389591) B389591
theorem B259769 : Blo 171799 259769 := bstep (se 2 (by rfl) ⟨97413, by rfl⟩ : syracuseStep 259769 = 194827) B194827
theorem B587465 : Blo 171799 587465 := bstep (se 2 (by rfl) ⟨220299, by rfl⟩ : syracuseStep 587465 = 440599) B440599
theorem B882413 : Blo 171799 882413 := bstep (se 3 (by rfl) ⟨165452, by rfl⟩ : syracuseStep 882413 = 330905) B330905
theorem B259847 : Blo 171799 259847 := bstep (se 1 (by rfl) ⟨194885, by rfl⟩ : syracuseStep 259847 = 389771) B389771
theorem B259883 : Blo 171799 259883 := bstep (se 1 (by rfl) ⟨194912, by rfl⟩ : syracuseStep 259883 = 389825) B389825
theorem B259913 : Blo 171799 259913 := bstep (se 2 (by rfl) ⟨97467, by rfl⟩ : syracuseStep 259913 = 194935) B194935
theorem B292727 : Blo 171799 292727 := bstep (se 1 (by rfl) ⟨219545, by rfl⟩ : syracuseStep 292727 = 439091) B439091
theorem B391031 : Blo 171799 391031 := bstep (se 1 (by rfl) ⟨293273, by rfl⟩ : syracuseStep 391031 = 586547) B586547
theorem B260027 : Blo 171799 260027 := bstep (se 1 (by rfl) ⟨195020, by rfl⟩ : syracuseStep 260027 = 390041) B390041
theorem B260087 : Blo 171799 260087 := bstep (se 1 (by rfl) ⟨195065, by rfl⟩ : syracuseStep 260087 = 390131) B390131
theorem B194575 : Blo 171799 194575 := bstep (se 1 (by rfl) ⟨145931, by rfl⟩ : syracuseStep 194575 = 291863) B291863
theorem B260111 : Blo 171799 260111 := bstep (se 1 (by rfl) ⟨195083, by rfl⟩ : syracuseStep 260111 = 390167) B390167
theorem B391211 : Blo 171799 391211 := bstep (se 1 (by rfl) ⟨293408, by rfl⟩ : syracuseStep 391211 = 586817) B586817
theorem B260153 : Blo 171799 260153 := bstep (se 2 (by rfl) ⟨97557, by rfl⟩ : syracuseStep 260153 = 195115) B195115
theorem B1538135 : Blo 171799 1538135 := bstep (se 1 (by rfl) ⟨1153601, by rfl⟩ : syracuseStep 1538135 = 2307203) B2307203
theorem B2652277 : Blo 171799 2652277 := bstep (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) B248651
theorem B260231 : Blo 171799 260231 := bstep (se 1 (by rfl) ⟨195173, by rfl⟩ : syracuseStep 260231 = 390347) B390347
theorem B260267 : Blo 171799 260267 := bstep (se 1 (by rfl) ⟨195200, by rfl⟩ : syracuseStep 260267 = 390401) B390401
theorem B260297 : Blo 171799 260297 := bstep (se 2 (by rfl) ⟨97611, by rfl⟩ : syracuseStep 260297 = 195223) B195223
theorem B260411 : Blo 171799 260411 := bstep (se 1 (by rfl) ⟨195308, by rfl⟩ : syracuseStep 260411 = 390617) B390617
theorem B293179 : Blo 171799 293179 := bstep (se 1 (by rfl) ⟨219884, by rfl⟩ : syracuseStep 293179 = 439769) B439769
theorem B522557 : Blo 171799 522557 := bstep (se 3 (by rfl) ⟨97979, by rfl⟩ : syracuseStep 522557 = 195959) B195959
theorem B260471 : Blo 171799 260471 := bstep (se 1 (by rfl) ⟨195353, by rfl⟩ : syracuseStep 260471 = 390707) B390707
theorem B588167 : Blo 171799 588167 := bstep (se 1 (by rfl) ⟨441125, by rfl⟩ : syracuseStep 588167 = 882251) B882251
theorem B260495 : Blo 171799 260495 := bstep (se 1 (by rfl) ⟨195371, by rfl⟩ : syracuseStep 260495 = 390743) B390743
theorem B981395 : Blo 171799 981395 := bstep (se 1 (by rfl) ⟨736046, by rfl⟩ : syracuseStep 981395 = 1472093) B1472093
theorem B391571 : Blo 171799 391571 := bstep (se 1 (by rfl) ⟨293678, by rfl⟩ : syracuseStep 391571 = 587357) B587357
theorem B8550805 : Blo 171799 8550805 := bstep (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) B400819
theorem B260537 : Blo 171799 260537 := bstep (se 2 (by rfl) ⟨97701, by rfl⟩ : syracuseStep 260537 = 195403) B195403
theorem B293321 : Blo 171799 293321 := bstep (se 2 (by rfl) ⟨109995, by rfl⟩ : syracuseStep 293321 = 219991) B219991
theorem B391625 : Blo 171799 391625 := bstep (se 2 (by rfl) ⟨146859, by rfl⟩ : syracuseStep 391625 = 293719) B293719
theorem B653777 : Blo 171799 653777 := bstep (se 2 (by rfl) ⟨245166, by rfl⟩ : syracuseStep 653777 = 490333) B490333
theorem B195079 : Blo 171799 195079 := bstep (se 1 (by rfl) ⟨146309, by rfl⟩ : syracuseStep 195079 = 292619) B292619
theorem B260615 : Blo 171799 260615 := bstep (se 1 (by rfl) ⟨195461, by rfl⟩ : syracuseStep 260615 = 390923) B390923
theorem B883223 : Blo 171799 883223 := bstep (se 1 (by rfl) ⟨662417, by rfl⟩ : syracuseStep 883223 = 1324835) B1324835
theorem B1178155 : Blo 171799 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B260651 : Blo 171799 260651 := bstep (se 1 (by rfl) ⟨195488, by rfl⟩ : syracuseStep 260651 = 390977) B390977
theorem B260681 : Blo 171799 260681 := bstep (se 2 (by rfl) ⟨97755, by rfl⟩ : syracuseStep 260681 = 195511) B195511
theorem B195259 : Blo 171799 195259 := bstep (se 1 (by rfl) ⟨146444, by rfl⟩ : syracuseStep 195259 = 292889) B292889
theorem B260795 : Blo 171799 260795 := bstep (se 1 (by rfl) ⟨195596, by rfl⟩ : syracuseStep 260795 = 391193) B391193
theorem B260855 : Blo 171799 260855 := bstep (se 1 (by rfl) ⟨195641, by rfl⟩ : syracuseStep 260855 = 391283) B391283
theorem B883457 : Blo 171799 883457 := bstep (se 2 (by rfl) ⟨331296, by rfl⟩ : syracuseStep 883457 = 662593) B662593
theorem B588545 : Blo 171799 588545 := bstep (se 2 (by rfl) ⟨220704, by rfl⟩ : syracuseStep 588545 = 441409) B441409
theorem B654095 : Blo 171799 654095 := bstep (se 1 (by rfl) ⟨490571, by rfl⟩ : syracuseStep 654095 = 981143) B981143
theorem B260879 : Blo 171799 260879 := bstep (se 1 (by rfl) ⟨195659, by rfl⟩ : syracuseStep 260879 = 391319) B391319
theorem B260921 : Blo 171799 260921 := bstep (se 2 (by rfl) ⟨97845, by rfl⟩ : syracuseStep 260921 = 195691) B195691
theorem B260999 : Blo 171799 260999 := bstep (se 1 (by rfl) ⟨195749, by rfl⟩ : syracuseStep 260999 = 391499) B391499
theorem B261035 : Blo 171799 261035 := bstep (se 1 (by rfl) ⟨195776, by rfl⟩ : syracuseStep 261035 = 391553) B391553
theorem B326585 : Blo 171799 326585 := bstep (se 2 (by rfl) ⟨122469, by rfl⟩ : syracuseStep 326585 = 244939) B244939
theorem B261065 : Blo 171799 261065 := bstep (se 2 (by rfl) ⟨97899, by rfl⟩ : syracuseStep 261065 = 195799) B195799
theorem B261179 : Blo 171799 261179 := bstep (se 1 (by rfl) ⟨195884, by rfl⟩ : syracuseStep 261179 = 391769) B391769
theorem B6454333 : Blo 171799 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B261239 : Blo 171799 261239 := bstep (se 1 (by rfl) ⟨195929, by rfl⟩ : syracuseStep 261239 = 391859) B391859
theorem B294023 : Blo 171799 294023 := bstep (se 1 (by rfl) ⟨220517, by rfl⟩ : syracuseStep 294023 = 441035) B441035
theorem B392327 : Blo 171799 392327 := bstep (se 1 (by rfl) ⟨294245, by rfl⟩ : syracuseStep 392327 = 588491) B588491
theorem B195727 : Blo 171799 195727 := bstep (se 1 (by rfl) ⟨146795, by rfl⟩ : syracuseStep 195727 = 293591) B293591
theorem B261263 : Blo 171799 261263 := bstep (se 1 (by rfl) ⟨195947, by rfl⟩ : syracuseStep 261263 = 391895) B391895
theorem B457913 : Blo 171799 457913 := bstep (se 2 (by rfl) ⟨171717, by rfl⟩ : syracuseStep 457913 = 343435) B343435
theorem B261305 : Blo 171799 261305 := bstep (se 2 (by rfl) ⟨97989, by rfl⟩ : syracuseStep 261305 = 195979) B195979
theorem B261383 : Blo 171799 261383 := bstep (se 1 (by rfl) ⟨196037, by rfl⟩ : syracuseStep 261383 = 392075) B392075
theorem B261419 : Blo 171799 261419 := bstep (se 1 (by rfl) ⟨196064, by rfl⟩ : syracuseStep 261419 = 392129) B392129
theorem B4226363 : Blo 171799 4226363 := bstep (se 1 (by rfl) ⟨3169772, by rfl⟩ : syracuseStep 4226363 = 6339545) B6339545
theorem B392507 : Blo 171799 392507 := bstep (se 1 (by rfl) ⟨294380, by rfl⟩ : syracuseStep 392507 = 588761) B588761
theorem B261449 : Blo 171799 261449 := bstep (se 2 (by rfl) ⟨98043, by rfl⟩ : syracuseStep 261449 = 196087) B196087
theorem B392633 : Blo 171799 392633 := bstep (se 2 (by rfl) ⟨147237, by rfl⟩ : syracuseStep 392633 = 294475) B294475
theorem B261563 : Blo 171799 261563 := bstep (se 1 (by rfl) ⟨196172, by rfl⟩ : syracuseStep 261563 = 392345) B392345
theorem B261623 : Blo 171799 261623 := bstep (se 1 (by rfl) ⟨196217, by rfl⟩ : syracuseStep 261623 = 392435) B392435
theorem B261647 : Blo 171799 261647 := bstep (se 1 (by rfl) ⟨196235, by rfl⟩ : syracuseStep 261647 = 392471) B392471
theorem B589355 : Blo 171799 589355 := bstep (se 1 (by rfl) ⟨442016, by rfl⟩ : syracuseStep 589355 = 884033) B884033
theorem B261689 : Blo 171799 261689 := bstep (se 2 (by rfl) ⟨98133, by rfl⟩ : syracuseStep 261689 = 196267) B196267
theorem B196231 : Blo 171799 196231 := bstep (se 1 (by rfl) ⟨147173, by rfl⟩ : syracuseStep 196231 = 294347) B294347
theorem B261767 : Blo 171799 261767 := bstep (se 1 (by rfl) ⟨196325, by rfl⟩ : syracuseStep 261767 = 392651) B392651
theorem B261803 : Blo 171799 261803 := bstep (se 1 (by rfl) ⟨196352, by rfl⟩ : syracuseStep 261803 = 392705) B392705
theorem B261833 : Blo 171799 261833 := bstep (se 2 (by rfl) ⟨98187, by rfl⟩ : syracuseStep 261833 = 196375) B196375
theorem B2391781 : Blo 171799 2391781 := bstep (se 4 (by rfl) ⟨224229, by rfl⟩ : syracuseStep 2391781 = 448459) B448459
theorem B425729 : Blo 171799 425729 := bstep (se 2 (by rfl) ⟨159648, by rfl⟩ : syracuseStep 425729 = 319297) B319297
theorem B294671 : Blo 171799 294671 := bstep (se 1 (by rfl) ⟨221003, by rfl⟩ : syracuseStep 294671 = 442007) B442007
theorem B392975 : Blo 171799 392975 := bstep (se 1 (by rfl) ⟨294731, by rfl⟩ : syracuseStep 392975 = 589463) B589463
theorem B392993 : Blo 171799 392993 := bstep (se 2 (by rfl) ⟨147372, by rfl⟩ : syracuseStep 392993 = 294745) B294745
theorem B196411 : Blo 171799 196411 := bstep (se 1 (by rfl) ⟨147308, by rfl⟩ : syracuseStep 196411 = 294617) B294617
theorem B261947 : Blo 171799 261947 := bstep (se 1 (by rfl) ⟨196460, by rfl⟩ : syracuseStep 261947 = 392921) B392921
theorem B262007 : Blo 171799 262007 := bstep (se 1 (by rfl) ⟨196505, by rfl⟩ : syracuseStep 262007 = 393011) B393011
theorem B262031 : Blo 171799 262031 := bstep (se 1 (by rfl) ⟨196523, by rfl⟩ : syracuseStep 262031 = 393047) B393047
theorem B262073 : Blo 171799 262073 := bstep (se 2 (by rfl) ⟨98277, by rfl⟩ : syracuseStep 262073 = 196555) B196555
theorem B262223 : Blo 171799 262223 := bstep (se 1 (by rfl) ⟨196667, by rfl⟩ : syracuseStep 262223 = 393335) B393335
theorem B1441955 : Blo 171799 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B262343 : Blo 171799 262343 := bstep (se 1 (by rfl) ⟨196757, by rfl⟩ : syracuseStep 262343 = 393515) B393515
theorem B196807 : Blo 171799 196807 := bstep (se 1 (by rfl) ⟨147605, by rfl⟩ : syracuseStep 196807 = 295211) B295211
theorem B1245451 : Blo 171799 1245451 := bstep (se 1 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 1245451 = 1868177) B1868177
theorem B1868093 : Blo 171799 1868093 := bstep (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) B700535
theorem B655721 : Blo 171799 655721 := bstep (se 2 (by rfl) ⟨245895, by rfl⟩ : syracuseStep 655721 = 491791) B491791
theorem B262505 : Blo 171799 262505 := bstep (se 2 (by rfl) ⟨98439, by rfl⟩ : syracuseStep 262505 = 196879) B196879
theorem B328043 : Blo 171799 328043 := bstep (se 1 (by rfl) ⟨246032, by rfl⟩ : syracuseStep 328043 = 492065) B492065
theorem B262583 : Blo 171799 262583 := bstep (se 1 (by rfl) ⟨196937, by rfl⟩ : syracuseStep 262583 = 393875) B393875
theorem B262619 : Blo 171799 262619 := bstep (se 1 (by rfl) ⟨196964, by rfl⟩ : syracuseStep 262619 = 393929) B393929
theorem B393767 : Blo 171799 393767 := bstep (se 1 (by rfl) ⟨295325, by rfl⟩ : syracuseStep 393767 = 590651) B590651
theorem B295481 : Blo 171799 295481 := bstep (se 2 (by rfl) ⟨110805, by rfl⟩ : syracuseStep 295481 = 221611) B221611
theorem B1475131 : Blo 171799 1475131 := bstep (se 1 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 1475131 = 2212697) B2212697
theorem B2228795 : Blo 171799 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B721505 : Blo 171799 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B492281 : Blo 171799 492281 := bstep (se 2 (by rfl) ⟨184605, by rfl⟩ : syracuseStep 492281 = 369211) B369211
theorem B394091 : Blo 171799 394091 := bstep (se 1 (by rfl) ⟨295568, by rfl⟩ : syracuseStep 394091 = 591137) B591137
theorem B394145 : Blo 171799 394145 := bstep (se 2 (by rfl) ⟨147804, by rfl⟩ : syracuseStep 394145 = 295609) B295609
theorem B263087 : Blo 171799 263087 := bstep (se 1 (by rfl) ⟨197315, by rfl⟩ : syracuseStep 263087 = 394631) B394631
theorem B328711 : Blo 171799 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B263177 : Blo 171799 263177 := bstep (se 2 (by rfl) ⟨98691, by rfl⟩ : syracuseStep 263177 = 197383) B197383
theorem B558095 : Blo 171799 558095 := bstep (se 1 (by rfl) ⟨418571, by rfl⟩ : syracuseStep 558095 = 837143) B837143
theorem B590867 : Blo 171799 590867 := bstep (se 1 (by rfl) ⟨443150, by rfl⟩ : syracuseStep 590867 = 886301) B886301
theorem B263207 : Blo 171799 263207 := bstep (se 1 (by rfl) ⟨197405, by rfl⟩ : syracuseStep 263207 = 394811) B394811
theorem B197671 : Blo 171799 197671 := bstep (se 1 (by rfl) ⟨148253, by rfl⟩ : syracuseStep 197671 = 296507) B296507
theorem B5309489 : Blo 171799 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B263291 : Blo 171799 263291 := bstep (se 1 (by rfl) ⟨197468, by rfl⟩ : syracuseStep 263291 = 394937) B394937
theorem B984311 : Blo 171799 984311 := bstep (se 1 (by rfl) ⟨738233, by rfl⟩ : syracuseStep 984311 = 1476467) B1476467
theorem B394487 : Blo 171799 394487 := bstep (se 1 (by rfl) ⟨295865, by rfl⟩ : syracuseStep 394487 = 591731) B591731
theorem B296183 : Blo 171799 296183 := bstep (se 1 (by rfl) ⟨222137, by rfl⟩ : syracuseStep 296183 = 444275) B444275
theorem B263417 : Blo 171799 263417 := bstep (se 2 (by rfl) ⟨98781, by rfl⟩ : syracuseStep 263417 = 197563) B197563
theorem B591191 : Blo 171799 591191 := bstep (se 1 (by rfl) ⟨443393, by rfl⟩ : syracuseStep 591191 = 886787) B886787
theorem B263519 : Blo 171799 263519 := bstep (se 1 (by rfl) ⟨197639, by rfl⟩ : syracuseStep 263519 = 395279) B395279
theorem B263531 : Blo 171799 263531 := bstep (se 1 (by rfl) ⟨197648, by rfl⟩ : syracuseStep 263531 = 395297) B395297
theorem B4326857 : Blo 171799 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B624167 : Blo 171799 624167 := bstep (se 1 (by rfl) ⟨468125, by rfl⟩ : syracuseStep 624167 = 936251) B936251
theorem B296527 : Blo 171799 296527 := bstep (se 1 (by rfl) ⟨222395, by rfl⟩ : syracuseStep 296527 = 444791) B444791
theorem B5375587 : Blo 171799 5375587 := bstep (se 1 (by rfl) ⟨4031690, by rfl⟩ : syracuseStep 5375587 = 8063381) B8063381
theorem B2361125 : Blo 171799 2361125 := bstep (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) B442711
theorem B1115963 : Blo 171799 1115963 := bstep (se 1 (by rfl) ⟨836972, by rfl⟩ : syracuseStep 1115963 = 1673945) B1673945
theorem B395081 : Blo 171799 395081 := bstep (se 2 (by rfl) ⟨148155, by rfl⟩ : syracuseStep 395081 = 296311) B296311
theorem B1116089 : Blo 171799 1116089 := bstep (se 2 (by rfl) ⟨418533, by rfl⟩ : syracuseStep 1116089 = 837067) B837067
theorem B493739 : Blo 171799 493739 := bstep (se 1 (by rfl) ⟨370304, by rfl⟩ : syracuseStep 493739 = 740609) B740609
theorem B592271 : Blo 171799 592271 := bstep (se 1 (by rfl) ⟨444203, by rfl⟩ : syracuseStep 592271 = 888407) B888407
theorem B592393 : Blo 171799 592393 := bstep (se 2 (by rfl) ⟨222147, by rfl⟩ : syracuseStep 592393 = 444295) B444295
theorem B657953 : Blo 171799 657953 := bstep (se 2 (by rfl) ⟨246732, by rfl⟩ : syracuseStep 657953 = 493465) B493465
theorem B592595 : Blo 171799 592595 := bstep (se 1 (by rfl) ⟨444446, by rfl⟩ : syracuseStep 592595 = 888893) B888893
theorem B559865 : Blo 171799 559865 := bstep (se 2 (by rfl) ⟨209949, by rfl⟩ : syracuseStep 559865 = 419899) B419899
theorem B1870775 : Blo 171799 1870775 := bstep (se 1 (by rfl) ⟨1403081, by rfl⟩ : syracuseStep 1870775 = 2806163) B2806163
theorem B658439 : Blo 171799 658439 := bstep (se 1 (by rfl) ⟨493829, by rfl⟩ : syracuseStep 658439 = 987659) B987659
theorem B560135 : Blo 171799 560135 := bstep (se 1 (by rfl) ⟨420101, by rfl⟩ : syracuseStep 560135 = 840203) B840203
theorem B330875 : Blo 171799 330875 := bstep (se 1 (by rfl) ⟨248156, by rfl⟩ : syracuseStep 330875 = 496313) B496313
theorem B331103 : Blo 171799 331103 := bstep (se 1 (by rfl) ⟨248327, by rfl⟩ : syracuseStep 331103 = 496655) B496655
theorem B658925 : Blo 171799 658925 := bstep (se 3 (by rfl) ⟨123548, by rfl⟩ : syracuseStep 658925 = 247097) B247097
theorem B331361 : Blo 171799 331361 := bstep (se 2 (by rfl) ⟨124260, by rfl⟩ : syracuseStep 331361 = 248521) B248521
theorem B888569 : Blo 171799 888569 := bstep (se 2 (by rfl) ⟨333213, by rfl⟩ : syracuseStep 888569 = 666427) B666427
theorem B986975 : Blo 171799 986975 := bstep (se 1 (by rfl) ⟨740231, by rfl⟩ : syracuseStep 986975 = 1480463) B1480463
theorem B331627 : Blo 171799 331627 := bstep (se 1 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 331627 = 497441) B497441
theorem B659609 : Blo 171799 659609 := bstep (se 2 (by rfl) ⟨247353, by rfl⟩ : syracuseStep 659609 = 494707) B494707
theorem B626935 : Blo 171799 626935 := bstep (se 1 (by rfl) ⟨470201, by rfl⟩ : syracuseStep 626935 = 940403) B940403
theorem B889217 : Blo 171799 889217 := bstep (se 2 (by rfl) ⟨333456, by rfl⟩ : syracuseStep 889217 = 666913) B666913
theorem B627385 : Blo 171799 627385 := bstep (se 2 (by rfl) ⟨235269, by rfl⟩ : syracuseStep 627385 = 470539) B470539
theorem B3248849 : Blo 171799 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B987977 : Blo 171799 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B332651 : Blo 171799 332651 := bstep (se 1 (by rfl) ⟨249488, by rfl⟩ : syracuseStep 332651 = 498977) B498977
theorem B2659225 : Blo 171799 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B627643 : Blo 171799 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B332819 : Blo 171799 332819 := bstep (se 1 (by rfl) ⟨249614, by rfl⟩ : syracuseStep 332819 = 499229) B499229
theorem B660595 : Blo 171799 660595 := bstep (se 1 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 660595 = 990893) B990893
theorem B890027 : Blo 171799 890027 := bstep (se 1 (by rfl) ⟨667520, by rfl⟩ : syracuseStep 890027 = 1335041) B1335041
theorem B1316087 : Blo 171799 1316087 := bstep (se 1 (by rfl) ⟨987065, by rfl⟩ : syracuseStep 1316087 = 1974131) B1974131
theorem B333047 : Blo 171799 333047 := bstep (se 1 (by rfl) ⟨249785, by rfl⟩ : syracuseStep 333047 = 499571) B499571
theorem B333161 : Blo 171799 333161 := bstep (se 2 (by rfl) ⟨124935, by rfl⟩ : syracuseStep 333161 = 249871) B249871
theorem B1119653 : Blo 171799 1119653 := bstep (se 4 (by rfl) ⟨104967, by rfl⟩ : syracuseStep 1119653 = 209935) B209935
theorem B562697 : Blo 171799 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B530135 : Blo 171799 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B1316573 : Blo 171799 1316573 := bstep (se 3 (by rfl) ⟨246857, by rfl⟩ : syracuseStep 1316573 = 493715) B493715
theorem B661355 : Blo 171799 661355 := bstep (se 1 (by rfl) ⟨496016, by rfl⟩ : syracuseStep 661355 = 992033) B992033
theorem B1185799 : Blo 171799 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B367067 : Blo 171799 367067 := bstep (se 1 (by rfl) ⟨275300, by rfl⟩ : syracuseStep 367067 = 550601) B550601
theorem B662381 : Blo 171799 662381 := bstep (se 3 (by rfl) ⟨124196, by rfl⟩ : syracuseStep 662381 = 248393) B248393
theorem B2202551 : Blo 171799 2202551 := bstep (se 1 (by rfl) ⟨1651913, by rfl⟩ : syracuseStep 2202551 = 3303827) B3303827
theorem B597071 : Blo 171799 597071 := bstep (se 1 (by rfl) ⟨447803, by rfl⟩ : syracuseStep 597071 = 895607) B895607
theorem B630281 : Blo 171799 630281 := bstep (se 2 (by rfl) ⟨236355, by rfl⟩ : syracuseStep 630281 = 472711) B472711
theorem B826919 : Blo 171799 826919 := bstep (se 1 (by rfl) ⟨620189, by rfl⟩ : syracuseStep 826919 = 1240379) B1240379
theorem B499297 : Blo 171799 499297 := bstep (se 2 (by rfl) ⟨187236, by rfl⟩ : syracuseStep 499297 = 374473) B374473
theorem B335483 : Blo 171799 335483 := bstep (se 1 (by rfl) ⟨251612, by rfl⟩ : syracuseStep 335483 = 503225) B503225
theorem B532091 : Blo 171799 532091 := bstep (se 1 (by rfl) ⟨399068, by rfl⟩ : syracuseStep 532091 = 798137) B798137
theorem B171815 : Blo 171799 171815 := bstep (se 1 (by rfl) ⟨128861, by rfl⟩ : syracuseStep 171815 = 257723) B257723
theorem B171855 : Blo 171799 171855 := bstep (se 1 (by rfl) ⟨128891, by rfl⟩ : syracuseStep 171855 = 257783) B257783
theorem B171871 : Blo 171799 171871 := bstep (se 1 (by rfl) ⟨128903, by rfl⟩ : syracuseStep 171871 = 257807) B257807
theorem B171899 : Blo 171799 171899 := bstep (se 1 (by rfl) ⟨128924, by rfl⟩ : syracuseStep 171899 = 257849) B257849
theorem B171951 : Blo 171799 171951 := bstep (se 1 (by rfl) ⟨128963, by rfl⟩ : syracuseStep 171951 = 257927) B257927
theorem B171975 : Blo 171799 171975 := bstep (se 1 (by rfl) ⟨128981, by rfl⟩ : syracuseStep 171975 = 257963) B257963
theorem B171995 : Blo 171799 171995 := bstep (se 1 (by rfl) ⟨128996, by rfl⟩ : syracuseStep 171995 = 257993) B257993
theorem B172071 : Blo 171799 172071 := bstep (se 1 (by rfl) ⟨129053, by rfl⟩ : syracuseStep 172071 = 258107) B258107
theorem B172111 : Blo 171799 172111 := bstep (se 1 (by rfl) ⟨129083, by rfl⟩ : syracuseStep 172111 = 258167) B258167
theorem B172127 : Blo 171799 172127 := bstep (se 1 (by rfl) ⟨129095, by rfl⟩ : syracuseStep 172127 = 258191) B258191
theorem B172155 : Blo 171799 172155 := bstep (se 1 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 172155 = 258233) B258233
theorem B172207 : Blo 171799 172207 := bstep (se 1 (by rfl) ⟨129155, by rfl⟩ : syracuseStep 172207 = 258311) B258311
theorem B172231 : Blo 171799 172231 := bstep (se 1 (by rfl) ⟨129173, by rfl⟩ : syracuseStep 172231 = 258347) B258347
theorem B172251 : Blo 171799 172251 := bstep (se 1 (by rfl) ⟨129188, by rfl⟩ : syracuseStep 172251 = 258377) B258377
theorem B172327 : Blo 171799 172327 := bstep (se 1 (by rfl) ⟨129245, by rfl⟩ : syracuseStep 172327 = 258491) B258491
theorem B172367 : Blo 171799 172367 := bstep (se 1 (by rfl) ⟨129275, by rfl⟩ : syracuseStep 172367 = 258551) B258551
theorem B172383 : Blo 171799 172383 := bstep (se 1 (by rfl) ⟨129287, by rfl⟩ : syracuseStep 172383 = 258575) B258575
theorem B172411 : Blo 171799 172411 := bstep (se 1 (by rfl) ⟨129308, by rfl⟩ : syracuseStep 172411 = 258617) B258617
theorem B172463 : Blo 171799 172463 := bstep (se 1 (by rfl) ⟨129347, by rfl⟩ : syracuseStep 172463 = 258695) B258695
theorem B172487 : Blo 171799 172487 := bstep (se 1 (by rfl) ⟨129365, by rfl⟩ : syracuseStep 172487 = 258731) B258731
theorem B172507 : Blo 171799 172507 := bstep (se 1 (by rfl) ⟨129380, by rfl⟩ : syracuseStep 172507 = 258761) B258761
theorem B1417753 : Blo 171799 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B172583 : Blo 171799 172583 := bstep (se 1 (by rfl) ⟨129437, by rfl⟩ : syracuseStep 172583 = 258875) B258875
theorem B172623 : Blo 171799 172623 := bstep (se 1 (by rfl) ⟨129467, by rfl⟩ : syracuseStep 172623 = 258935) B258935
theorem B172639 : Blo 171799 172639 := bstep (se 1 (by rfl) ⟨129479, by rfl⟩ : syracuseStep 172639 = 258959) B258959
theorem B172667 : Blo 171799 172667 := bstep (se 1 (by rfl) ⟨129500, by rfl⟩ : syracuseStep 172667 = 259001) B259001
theorem B172719 : Blo 171799 172719 := bstep (se 1 (by rfl) ⟨129539, by rfl⟩ : syracuseStep 172719 = 259079) B259079
theorem B500413 : Blo 171799 500413 := bstep (se 3 (by rfl) ⟨93827, by rfl⟩ : syracuseStep 500413 = 187655) B187655
theorem B172743 : Blo 171799 172743 := bstep (se 1 (by rfl) ⟨129557, by rfl⟩ : syracuseStep 172743 = 259115) B259115
theorem B172763 : Blo 171799 172763 := bstep (se 1 (by rfl) ⟨129572, by rfl⟩ : syracuseStep 172763 = 259145) B259145
theorem B1352477 : Blo 171799 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B172839 : Blo 171799 172839 := bstep (se 1 (by rfl) ⟨129629, by rfl⟩ : syracuseStep 172839 = 259259) B259259
theorem B172879 : Blo 171799 172879 := bstep (se 1 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 172879 = 259319) B259319
theorem B172895 : Blo 171799 172895 := bstep (se 1 (by rfl) ⟨129671, by rfl⟩ : syracuseStep 172895 = 259343) B259343
theorem B172923 : Blo 171799 172923 := bstep (se 1 (by rfl) ⟨129692, by rfl⟩ : syracuseStep 172923 = 259385) B259385
theorem B369569 : Blo 171799 369569 := bstep (se 2 (by rfl) ⟨138588, by rfl⟩ : syracuseStep 369569 = 277177) B277177
theorem B172975 : Blo 171799 172975 := bstep (se 1 (by rfl) ⟨129731, by rfl⟩ : syracuseStep 172975 = 259463) B259463
theorem B172999 : Blo 171799 172999 := bstep (se 1 (by rfl) ⟨129749, by rfl⟩ : syracuseStep 172999 = 259499) B259499
theorem B173019 : Blo 171799 173019 := bstep (se 1 (by rfl) ⟨129764, by rfl⟩ : syracuseStep 173019 = 259529) B259529
theorem B173095 : Blo 171799 173095 := bstep (se 1 (by rfl) ⟨129821, by rfl⟩ : syracuseStep 173095 = 259643) B259643
theorem B173135 : Blo 171799 173135 := bstep (se 1 (by rfl) ⟨129851, by rfl⟩ : syracuseStep 173135 = 259703) B259703
theorem B173151 : Blo 171799 173151 := bstep (se 1 (by rfl) ⟨129863, by rfl⟩ : syracuseStep 173151 = 259727) B259727
theorem B173179 : Blo 171799 173179 := bstep (se 1 (by rfl) ⟨129884, by rfl⟩ : syracuseStep 173179 = 259769) B259769
theorem B173231 : Blo 171799 173231 := bstep (se 1 (by rfl) ⟨129923, by rfl⟩ : syracuseStep 173231 = 259847) B259847
theorem B173255 : Blo 171799 173255 := bstep (se 1 (by rfl) ⟨129941, by rfl⟩ : syracuseStep 173255 = 259883) B259883
theorem B173275 : Blo 171799 173275 := bstep (se 1 (by rfl) ⟨129956, by rfl⟩ : syracuseStep 173275 = 259913) B259913
theorem B173351 : Blo 171799 173351 := bstep (se 1 (by rfl) ⟨130013, by rfl⟩ : syracuseStep 173351 = 260027) B260027
theorem B173391 : Blo 171799 173391 := bstep (se 1 (by rfl) ⟨130043, by rfl⟩ : syracuseStep 173391 = 260087) B260087
theorem B173407 : Blo 171799 173407 := bstep (se 1 (by rfl) ⟨130055, by rfl⟩ : syracuseStep 173407 = 260111) B260111
theorem B173435 : Blo 171799 173435 := bstep (se 1 (by rfl) ⟨130076, by rfl⟩ : syracuseStep 173435 = 260153) B260153
theorem B1025423 : Blo 171799 1025423 := bstep (se 1 (by rfl) ⟨769067, by rfl⟩ : syracuseStep 1025423 = 1538135) B1538135
theorem B173487 : Blo 171799 173487 := bstep (se 1 (by rfl) ⟨130115, by rfl⟩ : syracuseStep 173487 = 260231) B260231
theorem B173511 : Blo 171799 173511 := bstep (se 1 (by rfl) ⟨130133, by rfl⟩ : syracuseStep 173511 = 260267) B260267
theorem B173531 : Blo 171799 173531 := bstep (se 1 (by rfl) ⟨130148, by rfl⟩ : syracuseStep 173531 = 260297) B260297
theorem B173607 : Blo 171799 173607 := bstep (se 1 (by rfl) ⟨130205, by rfl⟩ : syracuseStep 173607 = 260411) B260411
theorem B992807 : Blo 171799 992807 := bstep (se 1 (by rfl) ⟨744605, by rfl⟩ : syracuseStep 992807 = 1489211) B1489211
theorem B173647 : Blo 171799 173647 := bstep (se 1 (by rfl) ⟨130235, by rfl⟩ : syracuseStep 173647 = 260471) B260471
theorem B173663 : Blo 171799 173663 := bstep (se 1 (by rfl) ⟨130247, by rfl⟩ : syracuseStep 173663 = 260495) B260495
theorem B173691 : Blo 171799 173691 := bstep (se 1 (by rfl) ⟨130268, by rfl⟩ : syracuseStep 173691 = 260537) B260537
theorem B435851 : Blo 171799 435851 := bstep (se 1 (by rfl) ⟨326888, by rfl⟩ : syracuseStep 435851 = 653777) B653777
theorem B173743 : Blo 171799 173743 := bstep (se 1 (by rfl) ⟨130307, by rfl⟩ : syracuseStep 173743 = 260615) B260615
theorem B665273 : Blo 171799 665273 := bstep (se 2 (by rfl) ⟨249477, by rfl⟩ : syracuseStep 665273 = 498955) B498955
theorem B173767 : Blo 171799 173767 := bstep (se 1 (by rfl) ⟨130325, by rfl⟩ : syracuseStep 173767 = 260651) B260651
theorem B173787 : Blo 171799 173787 := bstep (se 1 (by rfl) ⟨130340, by rfl⟩ : syracuseStep 173787 = 260681) B260681
theorem B173863 : Blo 171799 173863 := bstep (se 1 (by rfl) ⟨130397, by rfl⟩ : syracuseStep 173863 = 260795) B260795
theorem B173903 : Blo 171799 173903 := bstep (se 1 (by rfl) ⟨130427, by rfl⟩ : syracuseStep 173903 = 260855) B260855
theorem B436063 : Blo 171799 436063 := bstep (se 1 (by rfl) ⟨327047, by rfl⟩ : syracuseStep 436063 = 654095) B654095
theorem B173919 : Blo 171799 173919 := bstep (se 1 (by rfl) ⟨130439, by rfl⟩ : syracuseStep 173919 = 260879) B260879
theorem B173947 : Blo 171799 173947 := bstep (se 1 (by rfl) ⟨130460, by rfl⟩ : syracuseStep 173947 = 260921) B260921
theorem B173999 : Blo 171799 173999 := bstep (se 1 (by rfl) ⟨130499, by rfl⟩ : syracuseStep 173999 = 260999) B260999
theorem B174023 : Blo 171799 174023 := bstep (se 1 (by rfl) ⟨130517, by rfl⟩ : syracuseStep 174023 = 261035) B261035
theorem B174043 : Blo 171799 174043 := bstep (se 1 (by rfl) ⟨130532, by rfl⟩ : syracuseStep 174043 = 261065) B261065
theorem B1484837 : Blo 171799 1484837 := bstep (se 4 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 1484837 = 278407) B278407
theorem B5023781 : Blo 171799 5023781 := bstep (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) B941959
theorem B174119 : Blo 171799 174119 := bstep (se 1 (by rfl) ⟨130589, by rfl⟩ : syracuseStep 174119 = 261179) B261179
theorem B174159 : Blo 171799 174159 := bstep (se 1 (by rfl) ⟨130619, by rfl⟩ : syracuseStep 174159 = 261239) B261239
theorem B174175 : Blo 171799 174175 := bstep (se 1 (by rfl) ⟨130631, by rfl⟩ : syracuseStep 174175 = 261263) B261263
theorem B305275 : Blo 171799 305275 := bstep (se 1 (by rfl) ⟨228956, by rfl⟩ : syracuseStep 305275 = 457913) B457913
theorem B174203 : Blo 171799 174203 := bstep (se 1 (by rfl) ⟨130652, by rfl⟩ : syracuseStep 174203 = 261305) B261305
theorem B6400133 : Blo 171799 6400133 := bstep (se 4 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 6400133 = 1200025) B1200025
theorem B469163 : Blo 171799 469163 := bstep (se 1 (by rfl) ⟨351872, by rfl⟩ : syracuseStep 469163 = 703745) B703745
theorem B174255 : Blo 171799 174255 := bstep (se 1 (by rfl) ⟨130691, by rfl⟩ : syracuseStep 174255 = 261383) B261383
theorem B174279 : Blo 171799 174279 := bstep (se 1 (by rfl) ⟨130709, by rfl⟩ : syracuseStep 174279 = 261419) B261419
theorem B174299 : Blo 171799 174299 := bstep (se 1 (by rfl) ⟨130724, by rfl⟩ : syracuseStep 174299 = 261449) B261449
theorem B174375 : Blo 171799 174375 := bstep (se 1 (by rfl) ⟨130781, by rfl⟩ : syracuseStep 174375 = 261563) B261563
theorem B3189041 : Blo 171799 3189041 := bstep (se 2 (by rfl) ⟨1195890, by rfl⟩ : syracuseStep 3189041 = 2391781) B2391781
theorem B174415 : Blo 171799 174415 := bstep (se 1 (by rfl) ⟨130811, by rfl⟩ : syracuseStep 174415 = 261623) B261623
theorem B174431 : Blo 171799 174431 := bstep (se 1 (by rfl) ⟨130823, by rfl⟩ : syracuseStep 174431 = 261647) B261647
theorem B174459 : Blo 171799 174459 := bstep (se 1 (by rfl) ⟨130844, by rfl⟩ : syracuseStep 174459 = 261689) B261689
theorem B174511 : Blo 171799 174511 := bstep (se 1 (by rfl) ⟨130883, by rfl⟩ : syracuseStep 174511 = 261767) B261767
theorem B174535 : Blo 171799 174535 := bstep (se 1 (by rfl) ⟨130901, by rfl⟩ : syracuseStep 174535 = 261803) B261803
theorem B174555 : Blo 171799 174555 := bstep (se 1 (by rfl) ⟨130916, by rfl⟩ : syracuseStep 174555 = 261833) B261833
theorem B174631 : Blo 171799 174631 := bstep (se 1 (by rfl) ⟨130973, by rfl⟩ : syracuseStep 174631 = 261947) B261947
theorem B174671 : Blo 171799 174671 := bstep (se 1 (by rfl) ⟨131003, by rfl⟩ : syracuseStep 174671 = 262007) B262007
theorem B174687 : Blo 171799 174687 := bstep (se 1 (by rfl) ⟨131015, by rfl⟩ : syracuseStep 174687 = 262031) B262031
theorem B174715 : Blo 171799 174715 := bstep (se 1 (by rfl) ⟨131036, by rfl⟩ : syracuseStep 174715 = 262073) B262073
theorem B174767 : Blo 171799 174767 := bstep (se 1 (by rfl) ⟨131075, by rfl⟩ : syracuseStep 174767 = 262151) B262151
theorem B174791 : Blo 171799 174791 := bstep (se 1 (by rfl) ⟨131093, by rfl⟩ : syracuseStep 174791 = 262187) B262187
theorem B600791 : Blo 171799 600791 := bstep (se 1 (by rfl) ⟨450593, by rfl⟩ : syracuseStep 600791 = 901187) B901187
theorem B174811 : Blo 171799 174811 := bstep (se 1 (by rfl) ⟨131108, by rfl⟩ : syracuseStep 174811 = 262217) B262217
theorem B436985 : Blo 171799 436985 := bstep (se 2 (by rfl) ⟨163869, by rfl⟩ : syracuseStep 436985 = 327739) B327739
theorem B174887 : Blo 171799 174887 := bstep (se 1 (by rfl) ⟨131165, by rfl⟩ : syracuseStep 174887 = 262331) B262331
theorem B174927 : Blo 171799 174927 := bstep (se 1 (by rfl) ⟨131195, by rfl⟩ : syracuseStep 174927 = 262391) B262391
theorem B469855 : Blo 171799 469855 := bstep (se 1 (by rfl) ⟨352391, by rfl⟩ : syracuseStep 469855 = 704783) B704783
theorem B174943 : Blo 171799 174943 := bstep (se 1 (by rfl) ⟨131207, by rfl⟩ : syracuseStep 174943 = 262415) B262415
theorem B174971 : Blo 171799 174971 := bstep (se 1 (by rfl) ⟨131228, by rfl⟩ : syracuseStep 174971 = 262457) B262457
theorem B11447203 : Blo 171799 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B175023 : Blo 171799 175023 := bstep (se 1 (by rfl) ⟨131267, by rfl⟩ : syracuseStep 175023 = 262535) B262535
theorem B1649591 : Blo 171799 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B175047 : Blo 171799 175047 := bstep (se 1 (by rfl) ⟨131285, by rfl⟩ : syracuseStep 175047 = 262571) B262571
theorem B175067 : Blo 171799 175067 := bstep (se 1 (by rfl) ⟨131300, by rfl⟩ : syracuseStep 175067 = 262601) B262601
theorem B175143 : Blo 171799 175143 := bstep (se 1 (by rfl) ⟨131357, by rfl⟩ : syracuseStep 175143 = 262715) B262715
theorem B175183 : Blo 171799 175183 := bstep (se 1 (by rfl) ⟨131387, by rfl⟩ : syracuseStep 175183 = 262775) B262775
theorem B175199 : Blo 171799 175199 := bstep (se 1 (by rfl) ⟨131399, by rfl⟩ : syracuseStep 175199 = 262799) B262799
theorem B175227 : Blo 171799 175227 := bstep (se 1 (by rfl) ⟨131420, by rfl⟩ : syracuseStep 175227 = 262841) B262841
theorem B175279 : Blo 171799 175279 := bstep (se 1 (by rfl) ⟨131459, by rfl⟩ : syracuseStep 175279 = 262919) B262919
theorem B175303 : Blo 171799 175303 := bstep (se 1 (by rfl) ⟨131477, by rfl⟩ : syracuseStep 175303 = 262955) B262955
theorem B175323 : Blo 171799 175323 := bstep (se 1 (by rfl) ⟨131492, by rfl⟩ : syracuseStep 175323 = 262985) B262985
theorem B4435235 : Blo 171799 4435235 := bstep (se 1 (by rfl) ⟨3326426, by rfl⟩ : syracuseStep 4435235 = 6652853) B6652853
theorem B175399 : Blo 171799 175399 := bstep (se 1 (by rfl) ⟨131549, by rfl⟩ : syracuseStep 175399 = 263099) B263099
theorem B175439 : Blo 171799 175439 := bstep (se 1 (by rfl) ⟨131579, by rfl⟩ : syracuseStep 175439 = 263159) B263159
theorem B175455 : Blo 171799 175455 := bstep (se 1 (by rfl) ⟨131591, by rfl⟩ : syracuseStep 175455 = 263183) B263183
theorem B175483 : Blo 171799 175483 := bstep (se 1 (by rfl) ⟨131612, by rfl⟩ : syracuseStep 175483 = 263225) B263225
theorem B437633 : Blo 171799 437633 := bstep (se 2 (by rfl) ⟨164112, by rfl⟩ : syracuseStep 437633 = 328225) B328225
theorem B1322405 : Blo 171799 1322405 := bstep (se 4 (by rfl) ⟨123975, by rfl⟩ : syracuseStep 1322405 = 247951) B247951
theorem B175535 : Blo 171799 175535 := bstep (se 1 (by rfl) ⟨131651, by rfl⟩ : syracuseStep 175535 = 263303) B263303
theorem B175559 : Blo 171799 175559 := bstep (se 1 (by rfl) ⟨131669, by rfl⟩ : syracuseStep 175559 = 263339) B263339
theorem B175579 : Blo 171799 175579 := bstep (se 1 (by rfl) ⟨131684, by rfl⟩ : syracuseStep 175579 = 263369) B263369
theorem B175655 : Blo 171799 175655 := bstep (se 1 (by rfl) ⟨131741, by rfl⟩ : syracuseStep 175655 = 263483) B263483
theorem B175695 : Blo 171799 175695 := bstep (se 1 (by rfl) ⟨131771, by rfl⟩ : syracuseStep 175695 = 263543) B263543
theorem B175711 : Blo 171799 175711 := bstep (se 1 (by rfl) ⟨131783, by rfl⟩ : syracuseStep 175711 = 263567) B263567
theorem B175739 : Blo 171799 175739 := bstep (se 1 (by rfl) ⟨131804, by rfl⟩ : syracuseStep 175739 = 263609) B263609
theorem B175791 : Blo 171799 175791 := bstep (se 1 (by rfl) ⟨131843, by rfl⟩ : syracuseStep 175791 = 263687) B263687
theorem B667385 : Blo 171799 667385 := bstep (se 2 (by rfl) ⟨250269, by rfl⟩ : syracuseStep 667385 = 500539) B500539
theorem B1421243 : Blo 171799 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B438443 : Blo 171799 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B340499 : Blo 171799 340499 := bstep (se 1 (by rfl) ⟨255374, by rfl⟩ : syracuseStep 340499 = 510749) B510749
theorem B995975 : Blo 171799 995975 := bstep (se 1 (by rfl) ⟨746981, by rfl⟩ : syracuseStep 995975 = 1493963) B1493963
theorem B439303 : Blo 171799 439303 := bstep (se 1 (by rfl) ⟨329477, by rfl⟩ : syracuseStep 439303 = 658955) B658955
theorem B374311 : Blo 171799 374311 := bstep (se 1 (by rfl) ⟨280733, by rfl⟩ : syracuseStep 374311 = 561467) B561467
theorem B439931 : Blo 171799 439931 := bstep (se 1 (by rfl) ⟨329948, by rfl⟩ : syracuseStep 439931 = 659897) B659897
theorem B276139 : Blo 171799 276139 := bstep (se 1 (by rfl) ⟨207104, by rfl⟩ : syracuseStep 276139 = 414209) B414209
theorem B734969 : Blo 171799 734969 := bstep (se 2 (by rfl) ⟨275613, by rfl⟩ : syracuseStep 734969 = 551227) B551227
theorem B1685357 : Blo 171799 1685357 := bstep (se 3 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 1685357 = 632009) B632009
theorem B440225 : Blo 171799 440225 := bstep (se 2 (by rfl) ⟨165084, by rfl⟩ : syracuseStep 440225 = 330169) B330169
theorem B5027789 : Blo 171799 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B997433 : Blo 171799 997433 := bstep (se 2 (by rfl) ⟨374037, by rfl⟩ : syracuseStep 997433 = 748075) B748075
theorem B277049 : Blo 171799 277049 := bstep (se 2 (by rfl) ⟨103893, by rfl⟩ : syracuseStep 277049 = 207787) B207787
theorem B7518905 : Blo 171799 7518905 := bstep (se 2 (by rfl) ⟨2819589, by rfl⟩ : syracuseStep 7518905 = 5639179) B5639179
theorem B1260791 : Blo 171799 1260791 := bstep (se 1 (by rfl) ⟨945593, by rfl⟩ : syracuseStep 1260791 = 1891187) B1891187
theorem B441895 : Blo 171799 441895 := bstep (se 1 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 441895 = 662843) B662843
theorem B704123 : Blo 171799 704123 := bstep (se 1 (by rfl) ⟨528092, by rfl⟩ : syracuseStep 704123 = 1056185) B1056185
theorem B1326725 : Blo 171799 1326725 := bstep (se 4 (by rfl) ⟨124380, by rfl⟩ : syracuseStep 1326725 = 248761) B248761
theorem B442219 : Blo 171799 442219 := bstep (se 1 (by rfl) ⟨331664, by rfl⟩ : syracuseStep 442219 = 663329) B663329
theorem B10141625 : Blo 171799 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B704591 : Blo 171799 704591 := bstep (se 1 (by rfl) ⟨528443, by rfl⟩ : syracuseStep 704591 = 1056887) B1056887
theorem B278959 : Blo 171799 278959 := bstep (se 1 (by rfl) ⟨209219, by rfl⟩ : syracuseStep 278959 = 418439) B418439
theorem B442867 : Blo 171799 442867 := bstep (se 1 (by rfl) ⟨332150, by rfl⟩ : syracuseStep 442867 = 664301) B664301
theorem B1327751 : Blo 171799 1327751 := bstep (se 1 (by rfl) ⟨995813, by rfl⟩ : syracuseStep 1327751 = 1991627) B1991627
theorem B444001 : Blo 171799 444001 := bstep (se 2 (by rfl) ⟨166500, by rfl⟩ : syracuseStep 444001 = 333001) B333001
theorem B1001099 : Blo 171799 1001099 := bstep (se 1 (by rfl) ⟨750824, by rfl⟩ : syracuseStep 1001099 = 1501649) B1501649
theorem B1492627 : Blo 171799 1492627 := bstep (se 1 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 1492627 = 2238941) B2238941
theorem B870263 : Blo 171799 870263 := bstep (se 1 (by rfl) ⟨652697, by rfl⟩ : syracuseStep 870263 = 1305395) B1305395
theorem B247735 : Blo 171799 247735 := bstep (se 1 (by rfl) ⟨185801, by rfl⟩ : syracuseStep 247735 = 371603) B371603
theorem B739343 : Blo 171799 739343 := bstep (se 1 (by rfl) ⟨554507, by rfl⟩ : syracuseStep 739343 = 1109015) B1109015
theorem B1329209 : Blo 171799 1329209 := bstep (se 2 (by rfl) ⟨498453, by rfl⟩ : syracuseStep 1329209 = 996907) B996907
theorem B444953 : Blo 171799 444953 := bstep (se 2 (by rfl) ⟨166857, by rfl⟩ : syracuseStep 444953 = 333715) B333715
theorem B1198793 : Blo 171799 1198793 := bstep (se 2 (by rfl) ⟨449547, by rfl⟩ : syracuseStep 1198793 = 899095) B899095
theorem B314407 : Blo 171799 314407 := bstep (se 1 (by rfl) ⟨235805, by rfl⟩ : syracuseStep 314407 = 471611) B471611
theorem B314579 : Blo 171799 314579 := bstep (se 1 (by rfl) ⟨235934, by rfl⟩ : syracuseStep 314579 = 471869) B471869
theorem B249193 : Blo 171799 249193 := bstep (se 2 (by rfl) ⟨93447, by rfl⟩ : syracuseStep 249193 = 186895) B186895
theorem B1331153 : Blo 171799 1331153 := bstep (se 2 (by rfl) ⟨499182, by rfl⟩ : syracuseStep 1331153 = 998365) B998365
theorem B8605777 : Blo 171799 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B315515 : Blo 171799 315515 := bstep (se 1 (by rfl) ⟨236636, by rfl⟩ : syracuseStep 315515 = 473273) B473273
theorem B249979 : Blo 171799 249979 := bstep (se 1 (by rfl) ⟨187484, by rfl⟩ : syracuseStep 249979 = 374969) B374969
theorem B348371 : Blo 171799 348371 := bstep (se 1 (by rfl) ⟨261278, by rfl⟩ : syracuseStep 348371 = 522557) B522557
theorem B1331585 : Blo 171799 1331585 := bstep (se 2 (by rfl) ⟨499344, by rfl⟩ : syracuseStep 1331585 = 998689) B998689
theorem B217723 : Blo 171799 217723 := bstep (se 1 (by rfl) ⟨163292, by rfl⟩ : syracuseStep 217723 = 326585) B326585
theorem B1102967 : Blo 171799 1102967 := bstep (se 1 (by rfl) ⟨827225, by rfl⟩ : syracuseStep 1102967 = 1654451) B1654451
theorem B283819 : Blo 171799 283819 := bstep (se 1 (by rfl) ⟨212864, by rfl⟩ : syracuseStep 283819 = 425729) B425729
theorem B349895 : Blo 171799 349895 := bstep (se 1 (by rfl) ⟨262421, by rfl⟩ : syracuseStep 349895 = 524843) B524843
theorem B22763477 : Blo 171799 22763477 := bstep (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) B533519
theorem B710657 : Blo 171799 710657 := bstep (se 2 (by rfl) ⟨266496, by rfl⟩ : syracuseStep 710657 = 532993) B532993
theorem B579851 : Blo 171799 579851 := bstep (se 1 (by rfl) ⟨434888, by rfl⟩ : syracuseStep 579851 = 869777) B869777
theorem B219611 : Blo 171799 219611 := bstep (se 1 (by rfl) ⟨164708, by rfl⟩ : syracuseStep 219611 = 329417) B329417
theorem B580121 : Blo 171799 580121 := bstep (se 2 (by rfl) ⟨217545, by rfl⟩ : syracuseStep 580121 = 435091) B435091
theorem B744299 : Blo 171799 744299 := bstep (se 1 (by rfl) ⟨558224, by rfl⟩ : syracuseStep 744299 = 1116449) B1116449
theorem B875447 : Blo 171799 875447 := bstep (se 1 (by rfl) ⟨656585, by rfl⟩ : syracuseStep 875447 = 1313171) B1313171
theorem B220087 : Blo 171799 220087 := bstep (se 1 (by rfl) ⟨165065, by rfl⟩ : syracuseStep 220087 = 330131) B330131
theorem B1268939 : Blo 171799 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B1891619 : Blo 171799 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B1105325 : Blo 171799 1105325 := bstep (se 3 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 1105325 = 414497) B414497
theorem B744947 : Blo 171799 744947 := bstep (se 1 (by rfl) ⟨558710, by rfl⟩ : syracuseStep 744947 = 1117421) B1117421
theorem B581255 : Blo 171799 581255 := bstep (se 1 (by rfl) ⟨435941, by rfl⟩ : syracuseStep 581255 = 871883) B871883
theorem B581309 : Blo 171799 581309 := bstep (se 3 (by rfl) ⟨108995, by rfl⟩ : syracuseStep 581309 = 217991) B217991
theorem B581471 : Blo 171799 581471 := bstep (se 1 (by rfl) ⟨436103, by rfl⟩ : syracuseStep 581471 = 872207) B872207
theorem B319339 : Blo 171799 319339 := bstep (se 1 (by rfl) ⟨239504, by rfl⟩ : syracuseStep 319339 = 479009) B479009
theorem B581633 : Blo 171799 581633 := bstep (se 2 (by rfl) ⟨218112, by rfl⟩ : syracuseStep 581633 = 436225) B436225
theorem B843833 : Blo 171799 843833 := bstep (se 2 (by rfl) ⟨316437, by rfl⟩ : syracuseStep 843833 = 632875) B632875
theorem B221383 : Blo 171799 221383 := bstep (se 1 (by rfl) ⟨166037, by rfl⟩ : syracuseStep 221383 = 332075) B332075
theorem B6283493 : Blo 171799 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B12312931 : Blo 171799 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B876905 : Blo 171799 876905 := bstep (se 2 (by rfl) ⟨328839, by rfl⟩ : syracuseStep 876905 = 657679) B657679
theorem B582443 : Blo 171799 582443 := bstep (se 1 (by rfl) ⟨436832, by rfl⟩ : syracuseStep 582443 = 873665) B873665
theorem B4482053 : Blo 171799 4482053 := bstep (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) B840385
theorem B418823 : Blo 171799 418823 := bstep (se 1 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 418823 = 628235) B628235
theorem B582713 : Blo 171799 582713 := bstep (se 2 (by rfl) ⟨218517, by rfl⟩ : syracuseStep 582713 = 437035) B437035
theorem B353641 : Blo 171799 353641 := bstep (se 2 (by rfl) ⟨132615, by rfl⟩ : syracuseStep 353641 = 265231) B265231
theorem B583037 : Blo 171799 583037 := bstep (se 3 (by rfl) ⟨109319, by rfl⟩ : syracuseStep 583037 = 218639) B218639
theorem B1893851 : Blo 171799 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B386657 : Blo 171799 386657 := bstep (se 2 (by rfl) ⟨144996, by rfl⟩ : syracuseStep 386657 = 289993) B289993
theorem B583307 : Blo 171799 583307 := bstep (se 1 (by rfl) ⟨437480, by rfl⟩ : syracuseStep 583307 = 874961) B874961
theorem B550817 : Blo 171799 550817 := bstep (se 2 (by rfl) ⟨206556, by rfl⟩ : syracuseStep 550817 = 413113) B413113
theorem B386999 : Blo 171799 386999 := bstep (se 1 (by rfl) ⟨290249, by rfl⟩ : syracuseStep 386999 = 580499) B580499
theorem B550919 : Blo 171799 550919 := bstep (se 1 (by rfl) ⟨413189, by rfl⟩ : syracuseStep 550919 = 826379) B826379
theorem B1599745 : Blo 171799 1599745 := bstep (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) B1199809
theorem B4712849 : Blo 171799 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B387593 : Blo 171799 387593 := bstep (se 2 (by rfl) ⟨145347, by rfl⟩ : syracuseStep 387593 = 290695) B290695
theorem B584225 : Blo 171799 584225 := bstep (se 2 (by rfl) ⟨219084, by rfl⟩ : syracuseStep 584225 = 438169) B438169
theorem B748091 : Blo 171799 748091 := bstep (se 1 (by rfl) ⟨561068, by rfl⟩ : syracuseStep 748091 = 1122137) B1122137
theorem B584441 : Blo 171799 584441 := bstep (se 2 (by rfl) ⟨219165, by rfl⟩ : syracuseStep 584441 = 438331) B438331
theorem B387935 : Blo 171799 387935 := bstep (se 1 (by rfl) ⟨290951, by rfl⟩ : syracuseStep 387935 = 581903) B581903
theorem B584711 : Blo 171799 584711 := bstep (se 1 (by rfl) ⟨438533, by rfl⟩ : syracuseStep 584711 = 877067) B877067
theorem B388115 : Blo 171799 388115 := bstep (se 1 (by rfl) ⟨291086, by rfl⟩ : syracuseStep 388115 = 582173) B582173
theorem B584819 : Blo 171799 584819 := bstep (se 1 (by rfl) ⟨438614, by rfl⟩ : syracuseStep 584819 = 877229) B877229
theorem B1240235 : Blo 171799 1240235 := bstep (se 1 (by rfl) ⟨930176, by rfl⟩ : syracuseStep 1240235 = 1860353) B1860353
theorem B388457 : Blo 171799 388457 := bstep (se 2 (by rfl) ⟨145671, by rfl⟩ : syracuseStep 388457 = 291343) B291343
theorem B290155 : Blo 171799 290155 := bstep (se 1 (by rfl) ⟨217616, by rfl⟩ : syracuseStep 290155 = 435233) B435233
theorem B585089 : Blo 171799 585089 := bstep (se 2 (by rfl) ⟨219408, by rfl⟩ : syracuseStep 585089 = 438817) B438817
theorem B552457 : Blo 171799 552457 := bstep (se 2 (by rfl) ⟨207171, by rfl⟩ : syracuseStep 552457 = 414343) B414343
theorem B257735 : Blo 171799 257735 := bstep (se 1 (by rfl) ⟨193301, by rfl⟩ : syracuseStep 257735 = 386603) B386603
theorem B257897 : Blo 171799 257897 := bstep (se 2 (by rfl) ⟨96711, by rfl⟩ : syracuseStep 257897 = 193423) B193423
theorem B257975 : Blo 171799 257975 := bstep (se 1 (by rfl) ⟨193481, by rfl⟩ : syracuseStep 257975 = 386963) B386963
theorem B389051 : Blo 171799 389051 := bstep (se 1 (by rfl) ⟨291788, by rfl⟩ : syracuseStep 389051 = 583577) B583577
theorem B258011 : Blo 171799 258011 := bstep (se 1 (by rfl) ⟨193508, by rfl⟩ : syracuseStep 258011 = 387017) B387017
theorem B389177 : Blo 171799 389177 := bstep (se 2 (by rfl) ⟨145941, by rfl⟩ : syracuseStep 389177 = 291883) B291883
theorem B585899 : Blo 171799 585899 := bstep (se 1 (by rfl) ⟨439424, by rfl⟩ : syracuseStep 585899 = 878849) B878849
theorem B1306853 : Blo 171799 1306853 := bstep (se 4 (by rfl) ⟨122517, by rfl⟩ : syracuseStep 1306853 = 245035) B245035
theorem B553277 : Blo 171799 553277 := bstep (se 3 (by rfl) ⟨103739, by rfl⟩ : syracuseStep 553277 = 207479) B207479
theorem B291215 : Blo 171799 291215 := bstep (se 1 (by rfl) ⟨218411, by rfl⟩ : syracuseStep 291215 = 436823) B436823
theorem B389519 : Blo 171799 389519 := bstep (se 1 (by rfl) ⟨292139, by rfl⟩ : syracuseStep 389519 = 584279) B584279
theorem B258479 : Blo 171799 258479 := bstep (se 1 (by rfl) ⟨193859, by rfl⟩ : syracuseStep 258479 = 387719) B387719
theorem B258569 : Blo 171799 258569 := bstep (se 2 (by rfl) ⟨96963, by rfl⟩ : syracuseStep 258569 = 193927) B193927
theorem B258599 : Blo 171799 258599 := bstep (se 1 (by rfl) ⟨193949, by rfl⟩ : syracuseStep 258599 = 387899) B387899
theorem B258683 : Blo 171799 258683 := bstep (se 1 (by rfl) ⟨194012, by rfl⟩ : syracuseStep 258683 = 388025) B388025
theorem B291451 : Blo 171799 291451 := bstep (se 1 (by rfl) ⟨218588, by rfl⟩ : syracuseStep 291451 = 437177) B437177
theorem B586439 : Blo 171799 586439 := bstep (se 1 (by rfl) ⟨439829, by rfl⟩ : syracuseStep 586439 = 879659) B879659
theorem B389843 : Blo 171799 389843 := bstep (se 1 (by rfl) ⟨292382, by rfl⟩ : syracuseStep 389843 = 584765) B584765
theorem B258809 : Blo 171799 258809 := bstep (se 2 (by rfl) ⟨97053, by rfl⟩ : syracuseStep 258809 = 194107) B194107
theorem B258911 : Blo 171799 258911 := bstep (se 1 (by rfl) ⟨194183, by rfl⟩ : syracuseStep 258911 = 388367) B388367
theorem B258923 : Blo 171799 258923 := bstep (se 1 (by rfl) ⟨194192, by rfl⟩ : syracuseStep 258923 = 388385) B388385
theorem B259151 : Blo 171799 259151 := bstep (se 1 (by rfl) ⟨194363, by rfl⟩ : syracuseStep 259151 = 388727) B388727
theorem B259271 : Blo 171799 259271 := bstep (se 1 (by rfl) ⟨194453, by rfl⟩ : syracuseStep 259271 = 388907) B388907
theorem B259433 : Blo 171799 259433 := bstep (se 2 (by rfl) ⟨97287, by rfl⟩ : syracuseStep 259433 = 194575) B194575
theorem B259511 : Blo 171799 259511 := bstep (se 1 (by rfl) ⟨194633, by rfl⟩ : syracuseStep 259511 = 389267) B389267
theorem B259547 : Blo 171799 259547 := bstep (se 1 (by rfl) ⟨194660, by rfl⟩ : syracuseStep 259547 = 389321) B389321
theorem B292315 : Blo 171799 292315 := bstep (se 1 (by rfl) ⟨219236, by rfl⟩ : syracuseStep 292315 = 438473) B438473
theorem B3536369 : Blo 171799 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B587303 : Blo 171799 587303 := bstep (se 1 (by rfl) ⟨440477, by rfl⟩ : syracuseStep 587303 = 880955) B880955
theorem B390779 : Blo 171799 390779 := bstep (se 1 (by rfl) ⟨293084, by rfl⟩ : syracuseStep 390779 = 586169) B586169
theorem B587411 : Blo 171799 587411 := bstep (se 1 (by rfl) ⟨440558, by rfl⟩ : syracuseStep 587411 = 881117) B881117
theorem B423623 : Blo 171799 423623 := bstep (se 1 (by rfl) ⟨317717, by rfl⟩ : syracuseStep 423623 = 635435) B635435
theorem B390905 : Blo 171799 390905 := bstep (se 2 (by rfl) ⟨146589, by rfl⟩ : syracuseStep 390905 = 293179) B293179
theorem B653123 : Blo 171799 653123 := bstep (se 1 (by rfl) ⟨489842, by rfl⟩ : syracuseStep 653123 = 979685) B979685
theorem B587627 : Blo 171799 587627 := bstep (se 1 (by rfl) ⟨440720, by rfl⟩ : syracuseStep 587627 = 881441) B881441
theorem B11401073 : Blo 171799 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B587681 : Blo 171799 587681 := bstep (se 2 (by rfl) ⟨220380, by rfl⟩ : syracuseStep 587681 = 440761) B440761
theorem B260015 : Blo 171799 260015 := bstep (se 1 (by rfl) ⟨195011, by rfl⟩ : syracuseStep 260015 = 390023) B390023
theorem B391175 : Blo 171799 391175 := bstep (se 1 (by rfl) ⟨293381, by rfl⟩ : syracuseStep 391175 = 586763) B586763
theorem B260105 : Blo 171799 260105 := bstep (se 2 (by rfl) ⟨97539, by rfl⟩ : syracuseStep 260105 = 195079) B195079
theorem B260135 : Blo 171799 260135 := bstep (se 1 (by rfl) ⟨195101, by rfl⟩ : syracuseStep 260135 = 390203) B390203
theorem B292943 : Blo 171799 292943 := bstep (se 1 (by rfl) ⟨219707, by rfl⟩ : syracuseStep 292943 = 439415) B439415
theorem B391247 : Blo 171799 391247 := bstep (se 1 (by rfl) ⟨293435, by rfl⟩ : syracuseStep 391247 = 586871) B586871
theorem B194683 : Blo 171799 194683 := bstep (se 1 (by rfl) ⟨146012, by rfl⟩ : syracuseStep 194683 = 292025) B292025
theorem B260219 : Blo 171799 260219 := bstep (se 1 (by rfl) ⟨195164, by rfl⟩ : syracuseStep 260219 = 390329) B390329
theorem B260345 : Blo 171799 260345 := bstep (se 2 (by rfl) ⟨97629, by rfl⟩ : syracuseStep 260345 = 195259) B195259
theorem B1407233 : Blo 171799 1407233 := bstep (se 2 (by rfl) ⟨527712, by rfl⟩ : syracuseStep 1407233 = 1055425) B1055425
theorem B653579 : Blo 171799 653579 := bstep (se 1 (by rfl) ⟨490184, by rfl⟩ : syracuseStep 653579 = 980369) B980369
theorem B260447 : Blo 171799 260447 := bstep (se 1 (by rfl) ⟨195335, by rfl⟩ : syracuseStep 260447 = 390671) B390671
theorem B260459 : Blo 171799 260459 := bstep (se 1 (by rfl) ⟨195344, by rfl⟩ : syracuseStep 260459 = 390689) B390689
theorem B391643 : Blo 171799 391643 := bstep (se 1 (by rfl) ⟨293732, by rfl⟩ : syracuseStep 391643 = 587465) B587465
theorem B588275 : Blo 171799 588275 := bstep (se 1 (by rfl) ⟨441206, by rfl⟩ : syracuseStep 588275 = 882413) B882413
theorem B4487723 : Blo 171799 4487723 := bstep (se 1 (by rfl) ⟨3365792, by rfl⟩ : syracuseStep 4487723 = 6731585) B6731585
theorem B195151 : Blo 171799 195151 := bstep (se 1 (by rfl) ⟨146363, by rfl⟩ : syracuseStep 195151 = 292727) B292727
theorem B260687 : Blo 171799 260687 := bstep (se 1 (by rfl) ⟨195515, by rfl⟩ : syracuseStep 260687 = 391031) B391031
theorem B359009 : Blo 171799 359009 := bstep (se 2 (by rfl) ⟨134628, by rfl⟩ : syracuseStep 359009 = 269257) B269257
theorem B883385 : Blo 171799 883385 := bstep (se 2 (by rfl) ⟨331269, by rfl⟩ : syracuseStep 883385 = 662539) B662539
theorem B260807 : Blo 171799 260807 := bstep (se 1 (by rfl) ⟨195605, by rfl⟩ : syracuseStep 260807 = 391211) B391211
theorem B1080067 : Blo 171799 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B260969 : Blo 171799 260969 := bstep (se 2 (by rfl) ⟨97863, by rfl⟩ : syracuseStep 260969 = 195727) B195727
theorem B359273 : Blo 171799 359273 := bstep (se 2 (by rfl) ⟨134727, by rfl⟩ : syracuseStep 359273 = 269455) B269455
theorem B293807 : Blo 171799 293807 := bstep (se 1 (by rfl) ⟨220355, by rfl⟩ : syracuseStep 293807 = 440711) B440711
theorem B392111 : Blo 171799 392111 := bstep (se 1 (by rfl) ⟨294083, by rfl⟩ : syracuseStep 392111 = 588167) B588167
theorem B654263 : Blo 171799 654263 := bstep (se 1 (by rfl) ⟨490697, by rfl⟩ : syracuseStep 654263 = 981395) B981395
theorem B261047 : Blo 171799 261047 := bstep (se 1 (by rfl) ⟨195785, by rfl⟩ : syracuseStep 261047 = 391571) B391571
theorem B195547 : Blo 171799 195547 := bstep (se 1 (by rfl) ⟨146660, by rfl⟩ : syracuseStep 195547 = 293321) B293321
theorem B261083 : Blo 171799 261083 := bstep (se 1 (by rfl) ⟨195812, by rfl⟩ : syracuseStep 261083 = 391625) B391625
theorem B588815 : Blo 171799 588815 := bstep (se 1 (by rfl) ⟨441611, by rfl⟩ : syracuseStep 588815 = 883223) B883223
theorem B588971 : Blo 171799 588971 := bstep (se 1 (by rfl) ⟨441728, by rfl⟩ : syracuseStep 588971 = 883457) B883457
theorem B392363 : Blo 171799 392363 := bstep (se 1 (by rfl) ⟨294272, by rfl⟩ : syracuseStep 392363 = 588545) B588545
theorem B294239 : Blo 171799 294239 := bstep (se 1 (by rfl) ⟨220679, by rfl⟩ : syracuseStep 294239 = 441359) B441359
theorem B327017 : Blo 171799 327017 := bstep (se 2 (by rfl) ⟨122631, by rfl⟩ : syracuseStep 327017 = 245263) B245263
theorem B196015 : Blo 171799 196015 := bstep (se 1 (by rfl) ⟨147011, by rfl⟩ : syracuseStep 196015 = 294023) B294023
theorem B261551 : Blo 171799 261551 := bstep (se 1 (by rfl) ⟨196163, by rfl⟩ : syracuseStep 261551 = 392327) B392327
theorem B261641 : Blo 171799 261641 := bstep (se 2 (by rfl) ⟨98115, by rfl⟩ : syracuseStep 261641 = 196231) B196231
theorem B2817575 : Blo 171799 2817575 := bstep (se 1 (by rfl) ⟨2113181, by rfl⟩ : syracuseStep 2817575 = 4226363) B4226363
theorem B261671 : Blo 171799 261671 := bstep (se 1 (by rfl) ⟨196253, by rfl⟩ : syracuseStep 261671 = 392507) B392507
theorem B589409 : Blo 171799 589409 := bstep (se 2 (by rfl) ⟨221028, by rfl⟩ : syracuseStep 589409 = 442057) B442057
theorem B261755 : Blo 171799 261755 := bstep (se 1 (by rfl) ⟨196316, by rfl⟩ : syracuseStep 261755 = 392633) B392633
theorem B425611 : Blo 171799 425611 := bstep (se 1 (by rfl) ⟨319208, by rfl⟩ : syracuseStep 425611 = 638417) B638417
theorem B655037 : Blo 171799 655037 := bstep (se 3 (by rfl) ⟨122819, by rfl⟩ : syracuseStep 655037 = 245639) B245639
theorem B392903 : Blo 171799 392903 := bstep (se 1 (by rfl) ⟨294677, by rfl⟩ : syracuseStep 392903 = 589355) B589355
theorem B261881 : Blo 171799 261881 := bstep (se 2 (by rfl) ⟨98205, by rfl⟩ : syracuseStep 261881 = 196411) B196411
theorem B196447 : Blo 171799 196447 := bstep (se 1 (by rfl) ⟨147335, by rfl⟩ : syracuseStep 196447 = 294671) B294671
theorem B261983 : Blo 171799 261983 := bstep (se 1 (by rfl) ⟨196487, by rfl⟩ : syracuseStep 261983 = 392975) B392975
theorem B261995 : Blo 171799 261995 := bstep (se 1 (by rfl) ⟨196496, by rfl⟩ : syracuseStep 261995 = 392993) B392993
theorem B294799 : Blo 171799 294799 := bstep (se 1 (by rfl) ⟨221099, by rfl⟩ : syracuseStep 294799 = 442199) B442199
theorem B1245395 : Blo 171799 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B295177 : Blo 171799 295177 := bstep (se 2 (by rfl) ⟨110691, by rfl⟩ : syracuseStep 295177 = 221383) B221383
theorem B262409 : Blo 171799 262409 := bstep (se 2 (by rfl) ⟨98403, by rfl⟩ : syracuseStep 262409 = 196807) B196807
theorem B262511 : Blo 171799 262511 := bstep (se 1 (by rfl) ⟨196883, by rfl⟩ : syracuseStep 262511 = 393767) B393767
theorem B196987 : Blo 171799 196987 := bstep (se 1 (by rfl) ⟨147740, by rfl⟩ : syracuseStep 196987 = 295481) B295481
theorem B885167 : Blo 171799 885167 := bstep (se 1 (by rfl) ⟨663875, by rfl⟩ : syracuseStep 885167 = 1327751) B1327751
theorem B16417241 : Blo 171799 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B328187 : Blo 171799 328187 := bstep (se 1 (by rfl) ⟨246140, by rfl⟩ : syracuseStep 328187 = 492281) B492281
theorem B262727 : Blo 171799 262727 := bstep (se 1 (by rfl) ⟨197045, by rfl⟩ : syracuseStep 262727 = 394091) B394091
theorem B262763 : Blo 171799 262763 := bstep (se 1 (by rfl) ⟨197072, by rfl⟩ : syracuseStep 262763 = 394145) B394145
theorem B590489 : Blo 171799 590489 := bstep (se 2 (by rfl) ⟨221433, by rfl⟩ : syracuseStep 590489 = 442867) B442867
theorem B393911 : Blo 171799 393911 := bstep (se 1 (by rfl) ⟨295433, by rfl⟩ : syracuseStep 393911 = 590867) B590867
theorem B3539659 : Blo 171799 3539659 := bstep (se 1 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 3539659 = 5309489) B5309489
theorem B1966841 : Blo 171799 1966841 := bstep (se 2 (by rfl) ⟨737565, by rfl⟩ : syracuseStep 1966841 = 1475131) B1475131
theorem B1475405 : Blo 171799 1475405 := bstep (se 3 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 1475405 = 553277) B553277
theorem B656207 : Blo 171799 656207 := bstep (se 1 (by rfl) ⟨492155, by rfl⟩ : syracuseStep 656207 = 984311) B984311
theorem B262991 : Blo 171799 262991 := bstep (se 1 (by rfl) ⟨197243, by rfl⟩ : syracuseStep 262991 = 394487) B394487
theorem B197455 : Blo 171799 197455 := bstep (se 1 (by rfl) ⟨148091, by rfl⟩ : syracuseStep 197455 = 296183) B296183
theorem B394127 : Blo 171799 394127 := bstep (se 1 (by rfl) ⟨295595, by rfl⟩ : syracuseStep 394127 = 591191) B591191
theorem B2884571 : Blo 171799 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B1574083 : Blo 171799 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B263387 : Blo 171799 263387 := bstep (se 1 (by rfl) ⟨197540, by rfl⟩ : syracuseStep 263387 = 395081) B395081
theorem B492895 : Blo 171799 492895 := bstep (se 1 (by rfl) ⟨369671, by rfl⟩ : syracuseStep 492895 = 739343) B739343
theorem B886139 : Blo 171799 886139 := bstep (se 1 (by rfl) ⟨664604, by rfl⟩ : syracuseStep 886139 = 1329209) B1329209
theorem B263561 : Blo 171799 263561 := bstep (se 2 (by rfl) ⟨98835, by rfl⟩ : syracuseStep 263561 = 197671) B197671
theorem B329159 : Blo 171799 329159 := bstep (se 1 (by rfl) ⟨246869, by rfl⟩ : syracuseStep 329159 = 493739) B493739
theorem B394847 : Blo 171799 394847 := bstep (se 1 (by rfl) ⟨296135, by rfl⟩ : syracuseStep 394847 = 592271) B592271
theorem B296635 : Blo 171799 296635 := bstep (se 1 (by rfl) ⟨222476, by rfl⟩ : syracuseStep 296635 = 444953) B444953
theorem B395063 : Blo 171799 395063 := bstep (se 1 (by rfl) ⟨296297, by rfl⟩ : syracuseStep 395063 = 592595) B592595
theorem B1247183 : Blo 171799 1247183 := bstep (se 1 (by rfl) ⟨935387, by rfl⟩ : syracuseStep 1247183 = 1870775) B1870775
theorem B3606605 : Blo 171799 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B395369 : Blo 171799 395369 := bstep (se 2 (by rfl) ⟨148263, by rfl⟩ : syracuseStep 395369 = 296527) B296527
theorem B592001 : Blo 171799 592001 := bstep (se 2 (by rfl) ⟨222000, by rfl⟩ : syracuseStep 592001 = 444001) B444001
theorem B985517 : Blo 171799 985517 := bstep (se 3 (by rfl) ⟨184784, by rfl⟩ : syracuseStep 985517 = 369569) B369569
theorem B592379 : Blo 171799 592379 := bstep (se 1 (by rfl) ⟨444284, by rfl⟩ : syracuseStep 592379 = 888569) B888569
theorem B657983 : Blo 171799 657983 := bstep (se 1 (by rfl) ⟨493487, by rfl⟩ : syracuseStep 657983 = 986975) B986975
theorem B330313 : Blo 171799 330313 := bstep (se 2 (by rfl) ⟨123867, by rfl⟩ : syracuseStep 330313 = 247735) B247735
theorem B887435 : Blo 171799 887435 := bstep (se 1 (by rfl) ⟨665576, by rfl⟩ : syracuseStep 887435 = 1331153) B1331153
theorem B232247 : Blo 171799 232247 := bstep (se 1 (by rfl) ⟨174185, by rfl⟩ : syracuseStep 232247 = 348371) B348371
theorem B887723 : Blo 171799 887723 := bstep (se 1 (by rfl) ⟨665792, by rfl⟩ : syracuseStep 887723 = 1331585) B1331585
theorem B592811 : Blo 171799 592811 := bstep (se 1 (by rfl) ⟨444608, by rfl⟩ : syracuseStep 592811 = 889217) B889217
theorem B2132993 : Blo 171799 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B658651 : Blo 171799 658651 := bstep (se 1 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 658651 = 987977) B987977
theorem B789857 : Blo 171799 789857 := bstep (se 2 (by rfl) ⟨296196, by rfl⟩ : syracuseStep 789857 = 592393) B592393
theorem B593351 : Blo 171799 593351 := bstep (se 1 (by rfl) ⟨445013, by rfl⟩ : syracuseStep 593351 = 890027) B890027
theorem B626473 : Blo 171799 626473 := bstep (se 2 (by rfl) ⟨234927, by rfl⟩ : syracuseStep 626473 = 469855) B469855
theorem B233263 : Blo 171799 233263 := bstep (se 1 (by rfl) ⟨174947, by rfl⟩ : syracuseStep 233263 = 349895) B349895
theorem B332257 : Blo 171799 332257 := bstep (se 2 (by rfl) ⟨124596, by rfl⟩ : syracuseStep 332257 = 249193) B249193
theorem B496199 : Blo 171799 496199 := bstep (se 1 (by rfl) ⟨372149, by rfl⟩ : syracuseStep 496199 = 744299) B744299
theorem B398047 : Blo 171799 398047 := bstep (se 1 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 398047 = 597071) B597071
theorem B496631 : Blo 171799 496631 := bstep (se 1 (by rfl) ⟨372473, by rfl⟩ : syracuseStep 496631 = 744947) B744947
theorem B13407437 : Blo 171799 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B562555 : Blo 171799 562555 := bstep (se 1 (by rfl) ⟨421916, by rfl⟩ : syracuseStep 562555 = 843833) B843833
theorem B11474369 : Blo 171799 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B333305 : Blo 171799 333305 := bstep (se 2 (by rfl) ⟨124989, by rfl⟩ : syracuseStep 333305 = 249979) B249979
theorem B1676837 : Blo 171799 1676837 := bstep (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) B314407
theorem B1251101 : Blo 171799 1251101 := bstep (se 3 (by rfl) ⟨234581, by rfl⟩ : syracuseStep 1251101 = 469163) B469163
theorem B2988035 : Blo 171799 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B661871 : Blo 171799 661871 := bstep (se 1 (by rfl) ⟨496403, by rfl⟩ : syracuseStep 661871 = 992807) B992807
theorem B3545633 : Blo 171799 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B367211 : Blo 171799 367211 := bstep (se 1 (by rfl) ⟨275408, by rfl⟩ : syracuseStep 367211 = 550817) B550817
theorem B989891 : Blo 171799 989891 := bstep (se 1 (by rfl) ⟨742418, by rfl⟩ : syracuseStep 989891 = 1484837) B1484837
theorem B3349187 : Blo 171799 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B4266755 : Blo 171799 4266755 := bstep (se 1 (by rfl) ⟨3200066, by rfl⟩ : syracuseStep 4266755 = 6400133) B6400133
theorem B498727 : Blo 171799 498727 := bstep (se 1 (by rfl) ⟨374045, by rfl⟩ : syracuseStep 498727 = 748091) B748091
theorem B499081 : Blo 171799 499081 := bstep (se 2 (by rfl) ⟨187155, by rfl⟩ : syracuseStep 499081 = 374311) B374311
theorem B826823 : Blo 171799 826823 := bstep (se 1 (by rfl) ⟨620117, by rfl⟩ : syracuseStep 826823 = 1240235) B1240235
theorem B2956823 : Blo 171799 2956823 := bstep (se 1 (by rfl) ⟨2217617, by rfl⟩ : syracuseStep 2956823 = 4435235) B4435235
theorem B958061 : Blo 171799 958061 := bstep (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) B359273
theorem B171823 : Blo 171799 171823 := bstep (se 1 (by rfl) ⟨128867, by rfl⟩ : syracuseStep 171823 = 257735) B257735
theorem B171931 : Blo 171799 171931 := bstep (se 1 (by rfl) ⟨128948, by rfl⟩ : syracuseStep 171931 = 257897) B257897
theorem B171983 : Blo 171799 171983 := bstep (se 1 (by rfl) ⟨128987, by rfl⟩ : syracuseStep 171983 = 257975) B257975
theorem B172007 : Blo 171799 172007 := bstep (se 1 (by rfl) ⟨129005, by rfl⟩ : syracuseStep 172007 = 258011) B258011
theorem B1581065 : Blo 171799 1581065 := bstep (se 2 (by rfl) ⟨592899, by rfl⟩ : syracuseStep 1581065 = 1185799) B1185799
theorem B172319 : Blo 171799 172319 := bstep (se 1 (by rfl) ⟨129239, by rfl⟩ : syracuseStep 172319 = 258479) B258479
theorem B172379 : Blo 171799 172379 := bstep (se 1 (by rfl) ⟨129284, by rfl⟩ : syracuseStep 172379 = 258569) B258569
theorem B172399 : Blo 171799 172399 := bstep (se 1 (by rfl) ⟨129299, by rfl⟩ : syracuseStep 172399 = 258599) B258599
theorem B172455 : Blo 171799 172455 := bstep (se 1 (by rfl) ⟨129341, by rfl⟩ : syracuseStep 172455 = 258683) B258683
theorem B663983 : Blo 171799 663983 := bstep (se 1 (by rfl) ⟨497987, by rfl⟩ : syracuseStep 663983 = 995975) B995975
theorem B172539 : Blo 171799 172539 := bstep (se 1 (by rfl) ⟨129404, by rfl⟩ : syracuseStep 172539 = 258809) B258809
theorem B172607 : Blo 171799 172607 := bstep (se 1 (by rfl) ⟨129455, by rfl⟩ : syracuseStep 172607 = 258911) B258911
theorem B172615 : Blo 171799 172615 := bstep (se 1 (by rfl) ⟨129461, by rfl⟩ : syracuseStep 172615 = 258923) B258923
theorem B172767 : Blo 171799 172767 := bstep (se 1 (by rfl) ⟨129575, by rfl⟩ : syracuseStep 172767 = 259151) B259151
theorem B172847 : Blo 171799 172847 := bstep (se 1 (by rfl) ⟨129635, by rfl⟩ : syracuseStep 172847 = 259271) B259271
theorem B172955 : Blo 171799 172955 := bstep (se 1 (by rfl) ⟨129716, by rfl⟩ : syracuseStep 172955 = 259433) B259433
theorem B173007 : Blo 171799 173007 := bstep (se 1 (by rfl) ⟨129755, by rfl⟩ : syracuseStep 173007 = 259511) B259511
theorem B173031 : Blo 171799 173031 := bstep (se 1 (by rfl) ⟨129773, by rfl⟩ : syracuseStep 173031 = 259547) B259547
theorem B435415 : Blo 171799 435415 := bstep (se 1 (by rfl) ⟨326561, by rfl⟩ : syracuseStep 435415 = 653123) B653123
theorem B1123571 : Blo 171799 1123571 := bstep (se 1 (by rfl) ⟨842678, by rfl⟩ : syracuseStep 1123571 = 1685357) B1685357
theorem B173343 : Blo 171799 173343 := bstep (se 1 (by rfl) ⟨130007, by rfl⟩ : syracuseStep 173343 = 260015) B260015
theorem B173403 : Blo 171799 173403 := bstep (se 1 (by rfl) ⟨130052, by rfl⟩ : syracuseStep 173403 = 260105) B260105
theorem B173423 : Blo 171799 173423 := bstep (se 1 (by rfl) ⟨130067, by rfl⟩ : syracuseStep 173423 = 260135) B260135
theorem B664955 : Blo 171799 664955 := bstep (se 1 (by rfl) ⟨498716, by rfl⟩ : syracuseStep 664955 = 997433) B997433
theorem B173479 : Blo 171799 173479 := bstep (se 1 (by rfl) ⟨130109, by rfl⟩ : syracuseStep 173479 = 260219) B260219
theorem B173563 : Blo 171799 173563 := bstep (se 1 (by rfl) ⟨130172, by rfl⟩ : syracuseStep 173563 = 260345) B260345
theorem B435719 : Blo 171799 435719 := bstep (se 1 (by rfl) ⟨326789, by rfl⟩ : syracuseStep 435719 = 653579) B653579
theorem B173631 : Blo 171799 173631 := bstep (se 1 (by rfl) ⟨130223, by rfl⟩ : syracuseStep 173631 = 260447) B260447
theorem B173639 : Blo 171799 173639 := bstep (se 1 (by rfl) ⟨130229, by rfl⟩ : syracuseStep 173639 = 260459) B260459
theorem B2991815 : Blo 171799 2991815 := bstep (se 1 (by rfl) ⟨2243861, by rfl⟩ : syracuseStep 2991815 = 4487723) B4487723
theorem B173791 : Blo 171799 173791 := bstep (se 1 (by rfl) ⟨130343, by rfl⟩ : syracuseStep 173791 = 260687) B260687
theorem B239339 : Blo 171799 239339 := bstep (se 1 (by rfl) ⟨179504, by rfl⟩ : syracuseStep 239339 = 359009) B359009
theorem B173871 : Blo 171799 173871 := bstep (se 1 (by rfl) ⟨130403, by rfl⟩ : syracuseStep 173871 = 260807) B260807
theorem B173979 : Blo 171799 173979 := bstep (se 1 (by rfl) ⟨130484, by rfl⟩ : syracuseStep 173979 = 260969) B260969
theorem B436175 : Blo 171799 436175 := bstep (se 1 (by rfl) ⟨327131, by rfl⟩ : syracuseStep 436175 = 654263) B654263
theorem B174031 : Blo 171799 174031 := bstep (se 1 (by rfl) ⟨130523, by rfl⟩ : syracuseStep 174031 = 261047) B261047
theorem B174055 : Blo 171799 174055 := bstep (se 1 (by rfl) ⟨130541, by rfl⟩ : syracuseStep 174055 = 261083) B261083
theorem B665729 : Blo 171799 665729 := bstep (se 2 (by rfl) ⟨249648, by rfl⟩ : syracuseStep 665729 = 499297) B499297
theorem B567481 : Blo 171799 567481 := bstep (se 2 (by rfl) ⟨212805, by rfl⟩ : syracuseStep 567481 = 425611) B425611
theorem B174367 : Blo 171799 174367 := bstep (se 1 (by rfl) ⟨130775, by rfl⟩ : syracuseStep 174367 = 261551) B261551
theorem B174427 : Blo 171799 174427 := bstep (se 1 (by rfl) ⟨130820, by rfl⟩ : syracuseStep 174427 = 261641) B261641
theorem B1878383 : Blo 171799 1878383 := bstep (se 1 (by rfl) ⟨1408787, by rfl⟩ : syracuseStep 1878383 = 2817575) B2817575
theorem B174447 : Blo 171799 174447 := bstep (se 1 (by rfl) ⟨130835, by rfl⟩ : syracuseStep 174447 = 261671) B261671
theorem B469415 : Blo 171799 469415 := bstep (se 1 (by rfl) ⟨352061, by rfl⟩ : syracuseStep 469415 = 704123) B704123
theorem B174503 : Blo 171799 174503 := bstep (se 1 (by rfl) ⟨130877, by rfl⟩ : syracuseStep 174503 = 261755) B261755
theorem B436691 : Blo 171799 436691 := bstep (se 1 (by rfl) ⟨327518, by rfl⟩ : syracuseStep 436691 = 655037) B655037
theorem B174587 : Blo 171799 174587 := bstep (se 1 (by rfl) ⟨130940, by rfl⟩ : syracuseStep 174587 = 261881) B261881
theorem B174655 : Blo 171799 174655 := bstep (se 1 (by rfl) ⟨130991, by rfl⟩ : syracuseStep 174655 = 261983) B261983
theorem B174663 : Blo 171799 174663 := bstep (se 1 (by rfl) ⟨130997, by rfl⟩ : syracuseStep 174663 = 261995) B261995
theorem B6761083 : Blo 171799 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B469727 : Blo 171799 469727 := bstep (se 1 (by rfl) ⟨352295, by rfl⟩ : syracuseStep 469727 = 704591) B704591
theorem B174815 : Blo 171799 174815 := bstep (se 1 (by rfl) ⟨131111, by rfl⟩ : syracuseStep 174815 = 262223) B262223
theorem B961303 : Blo 171799 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B174895 : Blo 171799 174895 := bstep (se 1 (by rfl) ⟨131171, by rfl⟩ : syracuseStep 174895 = 262343) B262343
theorem B437147 : Blo 171799 437147 := bstep (se 1 (by rfl) ⟨327860, by rfl⟩ : syracuseStep 437147 = 655721) B655721
theorem B175003 : Blo 171799 175003 := bstep (se 1 (by rfl) ⟨131252, by rfl⟩ : syracuseStep 175003 = 262505) B262505
theorem B175055 : Blo 171799 175055 := bstep (se 1 (by rfl) ⟨131291, by rfl⟩ : syracuseStep 175055 = 262583) B262583
theorem B175079 : Blo 171799 175079 := bstep (se 1 (by rfl) ⟨131309, by rfl⟩ : syracuseStep 175079 = 262619) B262619
theorem B1485863 : Blo 171799 1485863 := bstep (se 1 (by rfl) ⟨1114397, by rfl⟩ : syracuseStep 1485863 = 2228795) B2228795
theorem B371945 : Blo 171799 371945 := bstep (se 2 (by rfl) ⟨139479, by rfl⟩ : syracuseStep 371945 = 278959) B278959
theorem B175391 : Blo 171799 175391 := bstep (se 1 (by rfl) ⟨131543, by rfl⟩ : syracuseStep 175391 = 263087) B263087
theorem B175451 : Blo 171799 175451 := bstep (se 1 (by rfl) ⟨131588, by rfl⟩ : syracuseStep 175451 = 263177) B263177
theorem B175471 : Blo 171799 175471 := bstep (se 1 (by rfl) ⟨131603, by rfl⟩ : syracuseStep 175471 = 263207) B263207
theorem B175527 : Blo 171799 175527 := bstep (se 1 (by rfl) ⟨131645, by rfl⟩ : syracuseStep 175527 = 263291) B263291
theorem B175611 : Blo 171799 175611 := bstep (se 1 (by rfl) ⟨131708, by rfl⟩ : syracuseStep 175611 = 263417) B263417
theorem B175679 : Blo 171799 175679 := bstep (se 1 (by rfl) ⟨131759, by rfl⟩ : syracuseStep 175679 = 263519) B263519
theorem B175687 : Blo 171799 175687 := bstep (se 1 (by rfl) ⟨131765, by rfl⟩ : syracuseStep 175687 = 263531) B263531
theorem B667217 : Blo 171799 667217 := bstep (se 2 (by rfl) ⟨250206, by rfl⟩ : syracuseStep 667217 = 500413) B500413
theorem B667399 : Blo 171799 667399 := bstep (se 1 (by rfl) ⟨500549, by rfl⟩ : syracuseStep 667399 = 1001099) B1001099
theorem B438281 : Blo 171799 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B438635 : Blo 171799 438635 := bstep (se 1 (by rfl) ⟨328976, by rfl⟩ : syracuseStep 438635 = 657953) B657953
theorem B799195 : Blo 171799 799195 := bstep (se 1 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 799195 = 1198793) B1198793
theorem B471521 : Blo 171799 471521 := bstep (se 2 (by rfl) ⟨176820, by rfl⟩ : syracuseStep 471521 = 353641) B353641
theorem B373243 : Blo 171799 373243 := bstep (se 1 (by rfl) ⟨279932, by rfl⟩ : syracuseStep 373243 = 559865) B559865
theorem B8663597 : Blo 171799 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B438959 : Blo 171799 438959 := bstep (se 1 (by rfl) ⟨329219, by rfl⟩ : syracuseStep 438959 = 658439) B658439
theorem B373423 : Blo 171799 373423 := bstep (se 1 (by rfl) ⟨280067, by rfl⟩ : syracuseStep 373423 = 560135) B560135
theorem B209719 : Blo 171799 209719 := bstep (se 1 (by rfl) ⟨157289, by rfl⟩ : syracuseStep 209719 = 314579) B314579
theorem B439283 : Blo 171799 439283 := bstep (se 1 (by rfl) ⟨329462, by rfl⟩ : syracuseStep 439283 = 658925) B658925
theorem B1488253 : Blo 171799 1488253 := bstep (se 3 (by rfl) ⟨279047, by rfl⟩ : syracuseStep 1488253 = 558095) B558095
theorem B439739 : Blo 171799 439739 := bstep (se 1 (by rfl) ⟨329804, by rfl⟩ : syracuseStep 439739 = 659609) B659609
theorem B407033 : Blo 171799 407033 := bstep (se 2 (by rfl) ⟨152637, by rfl⟩ : syracuseStep 407033 = 305275) B305275
theorem B735311 : Blo 171799 735311 := bstep (se 1 (by rfl) ⟨551483, by rfl⟩ : syracuseStep 735311 = 1102967) B1102967
theorem B375131 : Blo 171799 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B440903 : Blo 171799 440903 := bstep (se 1 (by rfl) ⟨330677, by rfl⟩ : syracuseStep 440903 = 661355) B661355
theorem B473771 : Blo 171799 473771 := bstep (se 1 (by rfl) ⟨355328, by rfl⟩ : syracuseStep 473771 = 710657) B710657
theorem B244711 : Blo 171799 244711 := bstep (se 1 (by rfl) ⟨183533, by rfl⟩ : syracuseStep 244711 = 367067) B367067
theorem B441587 : Blo 171799 441587 := bstep (se 1 (by rfl) ⟨331190, by rfl⟩ : syracuseStep 441587 = 662381) B662381
theorem B736609 : Blo 171799 736609 := bstep (se 2 (by rfl) ⟨276228, by rfl⟩ : syracuseStep 736609 = 552457) B552457
theorem B1261079 : Blo 171799 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B736883 : Blo 171799 736883 := bstep (se 1 (by rfl) ⟨552662, by rfl⟩ : syracuseStep 736883 = 1105325) B1105325
theorem B442169 : Blo 171799 442169 := bstep (se 2 (by rfl) ⟨165813, by rfl⟩ : syracuseStep 442169 = 331627) B331627
theorem B60702605 : Blo 171799 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B835913 : Blo 171799 835913 := bstep (se 2 (by rfl) ⟨313467, by rfl⟩ : syracuseStep 835913 = 626935) B626935
theorem B279215 : Blo 171799 279215 := bstep (se 1 (by rfl) ⟨209411, by rfl⟩ : syracuseStep 279215 = 418823) B418823
theorem B836513 : Blo 171799 836513 := bstep (se 2 (by rfl) ⟨313692, by rfl⟩ : syracuseStep 836513 = 627385) B627385
theorem B1262567 : Blo 171799 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B443515 : Blo 171799 443515 := bstep (se 1 (by rfl) ⟨332636, by rfl⟩ : syracuseStep 443515 = 665273) B665273
theorem B836857 : Blo 171799 836857 := bstep (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) B627643
theorem B378425 : Blo 171799 378425 := bstep (se 2 (by rfl) ⟨141909, by rfl⟩ : syracuseStep 378425 = 283819) B283819
theorem B1099727 : Blo 171799 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B444923 : Blo 171799 444923 := bstep (se 1 (by rfl) ⟨333692, by rfl⟩ : syracuseStep 444923 = 667385) B667385
theorem B871235 : Blo 171799 871235 := bstep (se 1 (by rfl) ⟨653426, by rfl⟩ : syracuseStep 871235 = 1306853) B1306853
theorem B872045 : Blo 171799 872045 := bstep (se 3 (by rfl) ⟨163508, by rfl⟩ : syracuseStep 872045 = 327017) B327017
theorem B282415 : Blo 171799 282415 := bstep (se 1 (by rfl) ⟨211811, by rfl⟩ : syracuseStep 282415 = 423623) B423623
theorem B938155 : Blo 171799 938155 := bstep (se 1 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 938155 = 1407233) B1407233
theorem B184699 : Blo 171799 184699 := bstep (se 1 (by rfl) ⟨138524, by rfl⟩ : syracuseStep 184699 = 277049) B277049
theorem B840527 : Blo 171799 840527 := bstep (se 1 (by rfl) ⟨630395, by rfl⟩ : syracuseStep 840527 = 1260791) B1260791
theorem B218695 : Blo 171799 218695 := bstep (se 1 (by rfl) ⟨164021, by rfl⟩ : syracuseStep 218695 = 328043) B328043
theorem B841373 : Blo 171799 841373 := bstep (se 3 (by rfl) ⟨157757, by rfl⟩ : syracuseStep 841373 = 315515) B315515
theorem B1660601 : Blo 171799 1660601 := bstep (se 2 (by rfl) ⟨622725, by rfl⟩ : syracuseStep 1660601 = 1245451) B1245451
theorem B416111 : Blo 171799 416111 := bstep (se 1 (by rfl) ⟨312083, by rfl⟩ : syracuseStep 416111 = 624167) B624167
theorem B743975 : Blo 171799 743975 := bstep (se 1 (by rfl) ⟨557981, by rfl⟩ : syracuseStep 743975 = 1115963) B1115963
theorem B580175 : Blo 171799 580175 := bstep (se 1 (by rfl) ⟨435131, by rfl⟩ : syracuseStep 580175 = 870263) B870263
theorem B744059 : Blo 171799 744059 := bstep (se 1 (by rfl) ⟨558044, by rfl⟩ : syracuseStep 744059 = 1116089) B1116089
theorem B1924013 : Blo 171799 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B220583 : Blo 171799 220583 := bstep (se 1 (by rfl) ⟨165437, by rfl⟩ : syracuseStep 220583 = 330875) B330875
theorem B7167449 : Blo 171799 7167449 := bstep (se 2 (by rfl) ⟨2687793, by rfl⟩ : syracuseStep 7167449 = 5375587) B5375587
theorem B1990169 : Blo 171799 1990169 := bstep (se 2 (by rfl) ⟨746313, by rfl⟩ : syracuseStep 1990169 = 1492627) B1492627
theorem B220735 : Blo 171799 220735 := bstep (se 1 (by rfl) ⟨165551, by rfl⟩ : syracuseStep 220735 = 331103) B331103
theorem B220907 : Blo 171799 220907 := bstep (se 1 (by rfl) ⟨165680, by rfl⟩ : syracuseStep 220907 = 331361) B331361
theorem B581417 : Blo 171799 581417 := bstep (se 2 (by rfl) ⟨218031, by rfl⟩ : syracuseStep 581417 = 436063) B436063
theorem B7561349 : Blo 171799 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B221767 : Blo 171799 221767 := bstep (se 1 (by rfl) ⟨166325, by rfl⟩ : syracuseStep 221767 = 332651) B332651
theorem B221879 : Blo 171799 221879 := bstep (se 1 (by rfl) ⟨166409, by rfl⟩ : syracuseStep 221879 = 332819) B332819
theorem B877391 : Blo 171799 877391 := bstep (se 1 (by rfl) ⟨658043, by rfl⟩ : syracuseStep 877391 = 1316087) B1316087
theorem B222031 : Blo 171799 222031 := bstep (se 1 (by rfl) ⟨166523, by rfl⟩ : syracuseStep 222031 = 333047) B333047
theorem B222107 : Blo 171799 222107 := bstep (se 1 (by rfl) ⟨166580, by rfl⟩ : syracuseStep 222107 = 333161) B333161
theorem B746435 : Blo 171799 746435 := bstep (se 1 (by rfl) ⟨559826, by rfl⟩ : syracuseStep 746435 = 1119653) B1119653
theorem B353423 : Blo 171799 353423 := bstep (se 1 (by rfl) ⟨265067, by rfl⟩ : syracuseStep 353423 = 530135) B530135
theorem B877715 : Blo 171799 877715 := bstep (se 1 (by rfl) ⟨658286, by rfl⟩ : syracuseStep 877715 = 1316573) B1316573
theorem B15262937 : Blo 171799 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B386567 : Blo 171799 386567 := bstep (se 1 (by rfl) ⟨289925, by rfl⟩ : syracuseStep 386567 = 579851) B579851
theorem B386747 : Blo 171799 386747 := bstep (se 1 (by rfl) ⟨290060, by rfl⟩ : syracuseStep 386747 = 580121) B580121
theorem B386873 : Blo 171799 386873 := bstep (se 2 (by rfl) ⟨145077, by rfl⟩ : syracuseStep 386873 = 290155) B290155
theorem B1468367 : Blo 171799 1468367 := bstep (se 1 (by rfl) ⟨1101275, by rfl⟩ : syracuseStep 1468367 = 2202551) B2202551
theorem B583631 : Blo 171799 583631 := bstep (se 1 (by rfl) ⟨437723, by rfl⟩ : syracuseStep 583631 = 875447) B875447
theorem B845959 : Blo 171799 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B420187 : Blo 171799 420187 := bstep (se 1 (by rfl) ⟨315140, by rfl⟩ : syracuseStep 420187 = 630281) B630281
theorem B551279 : Blo 171799 551279 := bstep (se 1 (by rfl) ⟨413459, by rfl⟩ : syracuseStep 551279 = 826919) B826919
theorem B223655 : Blo 171799 223655 := bstep (se 1 (by rfl) ⟨167741, by rfl⟩ : syracuseStep 223655 = 335483) B335483
theorem B354727 : Blo 171799 354727 := bstep (se 1 (by rfl) ⟨266045, by rfl⟩ : syracuseStep 354727 = 532091) B532091
theorem B387503 : Blo 171799 387503 := bstep (se 1 (by rfl) ⟨290627, by rfl⟩ : syracuseStep 387503 = 581255) B581255
theorem B387539 : Blo 171799 387539 := bstep (se 1 (by rfl) ⟨290654, by rfl⟩ : syracuseStep 387539 = 581309) B581309
theorem B387647 : Blo 171799 387647 := bstep (se 1 (by rfl) ⟨290735, by rfl⟩ : syracuseStep 387647 = 581471) B581471
theorem B387755 : Blo 171799 387755 := bstep (se 1 (by rfl) ⟨290816, by rfl⟩ : syracuseStep 387755 = 581633) B581633
theorem B1469117 : Blo 171799 1469117 := bstep (se 3 (by rfl) ⟨275459, by rfl⟩ : syracuseStep 1469117 = 550919) B550919
theorem B4188995 : Blo 171799 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B584603 : Blo 171799 584603 := bstep (se 1 (by rfl) ⟨438452, by rfl⟩ : syracuseStep 584603 = 876905) B876905
theorem B388295 : Blo 171799 388295 := bstep (se 1 (by rfl) ⟨291221, by rfl⟩ : syracuseStep 388295 = 582443) B582443
theorem B388475 : Blo 171799 388475 := bstep (se 1 (by rfl) ⟨291356, by rfl⟩ : syracuseStep 388475 = 582713) B582713
theorem B290297 : Blo 171799 290297 := bstep (se 2 (by rfl) ⟨108861, by rfl⟩ : syracuseStep 290297 = 217723) B217723
theorem B388601 : Blo 171799 388601 := bstep (se 2 (by rfl) ⟨145725, by rfl⟩ : syracuseStep 388601 = 291451) B291451
theorem B388691 : Blo 171799 388691 := bstep (se 1 (by rfl) ⟨291518, by rfl⟩ : syracuseStep 388691 = 583037) B583037
theorem B683615 : Blo 171799 683615 := bstep (se 1 (by rfl) ⟨512711, by rfl⟩ : syracuseStep 683615 = 1025423) B1025423
theorem B257771 : Blo 171799 257771 := bstep (se 1 (by rfl) ⟨193328, by rfl⟩ : syracuseStep 257771 = 386657) B386657
theorem B290567 : Blo 171799 290567 := bstep (se 1 (by rfl) ⟨217925, by rfl⟩ : syracuseStep 290567 = 435851) B435851
theorem B388871 : Blo 171799 388871 := bstep (se 1 (by rfl) ⟨291653, by rfl⟩ : syracuseStep 388871 = 583307) B583307
theorem B585629 : Blo 171799 585629 := bstep (se 3 (by rfl) ⟨109805, by rfl⟩ : syracuseStep 585629 = 219611) B219611
theorem B257999 : Blo 171799 257999 := bstep (se 1 (by rfl) ⟨193499, by rfl⟩ : syracuseStep 257999 = 386999) B386999
theorem B585737 : Blo 171799 585737 := bstep (se 2 (by rfl) ⟨219651, by rfl⟩ : syracuseStep 585737 = 439303) B439303
theorem B880793 : Blo 171799 880793 := bstep (se 2 (by rfl) ⟨330297, by rfl⟩ : syracuseStep 880793 = 660595) B660595
theorem B2126027 : Blo 171799 2126027 := bstep (se 1 (by rfl) ⟨1594520, by rfl⟩ : syracuseStep 2126027 = 3189041) B3189041
theorem B3141899 : Blo 171799 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B258395 : Blo 171799 258395 := bstep (se 1 (by rfl) ⟨193796, by rfl⟩ : syracuseStep 258395 = 387593) B387593
theorem B389483 : Blo 171799 389483 := bstep (se 1 (by rfl) ⟨292112, by rfl⟩ : syracuseStep 389483 = 584225) B584225
theorem B291323 : Blo 171799 291323 := bstep (se 1 (by rfl) ⟨218492, by rfl⟩ : syracuseStep 291323 = 436985) B436985
theorem B389627 : Blo 171799 389627 := bstep (se 1 (by rfl) ⟨292220, by rfl⟩ : syracuseStep 389627 = 584441) B584441
theorem B1602109 : Blo 171799 1602109 := bstep (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) B600791
theorem B258623 : Blo 171799 258623 := bstep (se 1 (by rfl) ⟨193967, by rfl⟩ : syracuseStep 258623 = 387935) B387935
theorem B389753 : Blo 171799 389753 := bstep (se 2 (by rfl) ⟨146157, by rfl⟩ : syracuseStep 389753 = 292315) B292315
theorem B389807 : Blo 171799 389807 := bstep (se 1 (by rfl) ⟨292355, by rfl⟩ : syracuseStep 389807 = 584711) B584711
theorem B258743 : Blo 171799 258743 := bstep (se 1 (by rfl) ⟨194057, by rfl⟩ : syracuseStep 258743 = 388115) B388115
theorem B389879 : Blo 171799 389879 := bstep (se 1 (by rfl) ⟨292409, by rfl⟩ : syracuseStep 389879 = 584819) B584819
theorem B258971 : Blo 171799 258971 := bstep (se 1 (by rfl) ⟨194228, by rfl⟩ : syracuseStep 258971 = 388457) B388457
theorem B291755 : Blo 171799 291755 := bstep (se 1 (by rfl) ⟨218816, by rfl⟩ : syracuseStep 291755 = 437633) B437633
theorem B390059 : Blo 171799 390059 := bstep (se 1 (by rfl) ⟨292544, by rfl⟩ : syracuseStep 390059 = 585089) B585089
theorem B881603 : Blo 171799 881603 := bstep (se 1 (by rfl) ⟨661202, by rfl⟩ : syracuseStep 881603 = 1322405) B1322405
theorem B947495 : Blo 171799 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B259367 : Blo 171799 259367 := bstep (se 1 (by rfl) ⟨194525, by rfl⟩ : syracuseStep 259367 = 389051) B389051
theorem B259451 : Blo 171799 259451 := bstep (se 1 (by rfl) ⟨194588, by rfl⟩ : syracuseStep 259451 = 389177) B389177
theorem B292295 : Blo 171799 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B390599 : Blo 171799 390599 := bstep (se 1 (by rfl) ⟨292949, by rfl⟩ : syracuseStep 390599 = 585899) B585899
theorem B259577 : Blo 171799 259577 := bstep (se 2 (by rfl) ⟨97341, by rfl⟩ : syracuseStep 259577 = 194683) B194683
theorem B194143 : Blo 171799 194143 := bstep (se 1 (by rfl) ⟨145607, by rfl⟩ : syracuseStep 194143 = 291215) B291215
theorem B259679 : Blo 171799 259679 := bstep (se 1 (by rfl) ⟨194759, by rfl⟩ : syracuseStep 259679 = 389519) B389519
theorem B226999 : Blo 171799 226999 := bstep (se 1 (by rfl) ⟨170249, by rfl⟩ : syracuseStep 226999 = 340499) B340499
theorem B390959 : Blo 171799 390959 := bstep (se 1 (by rfl) ⟨293219, by rfl⟩ : syracuseStep 390959 = 586439) B586439
theorem B259895 : Blo 171799 259895 := bstep (se 1 (by rfl) ⟨194921, by rfl⟩ : syracuseStep 259895 = 389843) B389843
theorem B260201 : Blo 171799 260201 := bstep (se 2 (by rfl) ⟨97575, by rfl⟩ : syracuseStep 260201 = 195151) B195151
theorem B1472741 : Blo 171799 1472741 := bstep (se 4 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 1472741 = 276139) B276139
theorem B2357579 : Blo 171799 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B1440089 : Blo 171799 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B391535 : Blo 171799 391535 := bstep (se 1 (by rfl) ⟨293651, by rfl⟩ : syracuseStep 391535 = 587303) B587303
theorem B260519 : Blo 171799 260519 := bstep (se 1 (by rfl) ⟨195389, by rfl⟩ : syracuseStep 260519 = 390779) B390779
theorem B293287 : Blo 171799 293287 := bstep (se 1 (by rfl) ⟨219965, by rfl⟩ : syracuseStep 293287 = 439931) B439931
theorem B391607 : Blo 171799 391607 := bstep (se 1 (by rfl) ⟨293705, by rfl⟩ : syracuseStep 391607 = 587411) B587411
theorem B489979 : Blo 171799 489979 := bstep (se 1 (by rfl) ⟨367484, by rfl⟩ : syracuseStep 489979 = 734969) B734969
theorem B260603 : Blo 171799 260603 := bstep (se 1 (by rfl) ⟨195452, by rfl⟩ : syracuseStep 260603 = 390905) B390905
theorem B391751 : Blo 171799 391751 := bstep (se 1 (by rfl) ⟨293813, by rfl⟩ : syracuseStep 391751 = 587627) B587627
theorem B293449 : Blo 171799 293449 := bstep (se 2 (by rfl) ⟨110043, by rfl⟩ : syracuseStep 293449 = 220087) B220087
theorem B7600715 : Blo 171799 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B293483 : Blo 171799 293483 := bstep (se 1 (by rfl) ⟨220112, by rfl⟩ : syracuseStep 293483 = 440225) B440225
theorem B391787 : Blo 171799 391787 := bstep (se 1 (by rfl) ⟨293840, by rfl⟩ : syracuseStep 391787 = 587681) B587681
theorem B260729 : Blo 171799 260729 := bstep (se 2 (by rfl) ⟨97773, by rfl⟩ : syracuseStep 260729 = 195547) B195547
theorem B260783 : Blo 171799 260783 := bstep (se 1 (by rfl) ⟨195587, by rfl⟩ : syracuseStep 260783 = 391175) B391175
theorem B195295 : Blo 171799 195295 := bstep (se 1 (by rfl) ⟨146471, by rfl⟩ : syracuseStep 195295 = 292943) B292943
theorem B260831 : Blo 171799 260831 := bstep (se 1 (by rfl) ⟨195623, by rfl⟩ : syracuseStep 260831 = 391247) B391247
theorem B261095 : Blo 171799 261095 := bstep (se 1 (by rfl) ⟨195821, by rfl⟩ : syracuseStep 261095 = 391643) B391643
theorem B392183 : Blo 171799 392183 := bstep (se 1 (by rfl) ⟨294137, by rfl⟩ : syracuseStep 392183 = 588275) B588275
theorem B5012603 : Blo 171799 5012603 := bstep (se 1 (by rfl) ⟨3759452, by rfl⟩ : syracuseStep 5012603 = 7518905) B7518905
theorem B588923 : Blo 171799 588923 := bstep (se 1 (by rfl) ⟨441692, by rfl⟩ : syracuseStep 588923 = 883385) B883385
theorem B261353 : Blo 171799 261353 := bstep (se 2 (by rfl) ⟨98007, by rfl⟩ : syracuseStep 261353 = 196015) B196015
theorem B195871 : Blo 171799 195871 := bstep (se 1 (by rfl) ⟨146903, by rfl⟩ : syracuseStep 195871 = 293807) B293807
theorem B261407 : Blo 171799 261407 := bstep (se 1 (by rfl) ⟨196055, by rfl⟩ : syracuseStep 261407 = 392111) B392111
theorem B392543 : Blo 171799 392543 := bstep (se 1 (by rfl) ⟨294407, by rfl⟩ : syracuseStep 392543 = 588815) B588815
theorem B589193 : Blo 171799 589193 := bstep (se 2 (by rfl) ⟨220947, by rfl⟩ : syracuseStep 589193 = 441895) B441895
theorem B392647 : Blo 171799 392647 := bstep (se 1 (by rfl) ⟨294485, by rfl⟩ : syracuseStep 392647 = 588971) B588971
theorem B261575 : Blo 171799 261575 := bstep (se 1 (by rfl) ⟨196181, by rfl⟩ : syracuseStep 261575 = 392363) B392363
theorem B196159 : Blo 171799 196159 := bstep (se 1 (by rfl) ⟨147119, by rfl⟩ : syracuseStep 196159 = 294239) B294239
theorem B392939 : Blo 171799 392939 := bstep (se 1 (by rfl) ⟨294704, by rfl⟩ : syracuseStep 392939 = 589409) B589409
theorem B884483 : Blo 171799 884483 := bstep (se 1 (by rfl) ⟨663362, by rfl⟩ : syracuseStep 884483 = 1326725) B1326725
theorem B261929 : Blo 171799 261929 := bstep (se 2 (by rfl) ⟨98223, by rfl⟩ : syracuseStep 261929 = 196447) B196447
theorem B261935 : Blo 171799 261935 := bstep (se 1 (by rfl) ⟨196451, by rfl⟩ : syracuseStep 261935 = 392903) B392903
theorem B589625 : Blo 171799 589625 := bstep (se 2 (by rfl) ⟨221109, by rfl⟩ : syracuseStep 589625 = 442219) B442219
theorem B425785 : Blo 171799 425785 := bstep (se 2 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 425785 = 319339) B319339
theorem B393065 : Blo 171799 393065 := bstep (se 2 (by rfl) ⟨147399, by rfl⟩ : syracuseStep 393065 = 294799) B294799
theorem B557275 : Blo 171799 557275 := bstep (se 1 (by rfl) ⟨417956, by rfl⟩ : syracuseStep 557275 = 835913) B835913
theorem B590111 : Blo 171799 590111 := bstep (se 1 (by rfl) ⟨442583, by rfl⟩ : syracuseStep 590111 = 885167) B885167
theorem B10944827 : Blo 171799 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B393569 : Blo 171799 393569 := bstep (se 2 (by rfl) ⟨147588, by rfl⟩ : syracuseStep 393569 = 295177) B295177
theorem B393659 : Blo 171799 393659 := bstep (se 1 (by rfl) ⟨295244, by rfl⟩ : syracuseStep 393659 = 590489) B590489
theorem B262607 : Blo 171799 262607 := bstep (se 1 (by rfl) ⟨196955, by rfl⟩ : syracuseStep 262607 = 393911) B393911
theorem B262649 : Blo 171799 262649 := bstep (se 2 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 262649 = 196987) B196987
theorem B1311227 : Blo 171799 1311227 := bstep (se 1 (by rfl) ⟨983420, by rfl⟩ : syracuseStep 1311227 = 1966841) B1966841
theorem B983603 : Blo 171799 983603 := bstep (se 1 (by rfl) ⟨737702, by rfl⟩ : syracuseStep 983603 = 1475405) B1475405
theorem B262751 : Blo 171799 262751 := bstep (se 1 (by rfl) ⟨197063, by rfl⟩ : syracuseStep 262751 = 394127) B394127
theorem B557675 : Blo 171799 557675 := bstep (se 1 (by rfl) ⟨418256, by rfl⟩ : syracuseStep 557675 = 836513) B836513
theorem B590759 : Blo 171799 590759 := bstep (se 1 (by rfl) ⟨443069, by rfl⟩ : syracuseStep 590759 = 886139) B886139
theorem B4719545 : Blo 171799 4719545 := bstep (se 2 (by rfl) ⟨1769829, by rfl⟩ : syracuseStep 4719545 = 3539659) B3539659
theorem B263231 : Blo 171799 263231 := bstep (se 1 (by rfl) ⟨197423, by rfl⟩ : syracuseStep 263231 = 394847) B394847
theorem B296041 : Blo 171799 296041 := bstep (se 2 (by rfl) ⟨111015, by rfl⟩ : syracuseStep 296041 = 222031) B222031
theorem B263273 : Blo 171799 263273 := bstep (se 2 (by rfl) ⟨98727, by rfl⟩ : syracuseStep 263273 = 197455) B197455
theorem B263375 : Blo 171799 263375 := bstep (se 1 (by rfl) ⟨197531, by rfl⟩ : syracuseStep 263375 = 395063) B395063
theorem B263579 : Blo 171799 263579 := bstep (se 1 (by rfl) ⟨197684, by rfl⟩ : syracuseStep 263579 = 395369) B395369
theorem B394667 : Blo 171799 394667 := bstep (se 1 (by rfl) ⟨296000, by rfl⟩ : syracuseStep 394667 = 592001) B592001
theorem B591353 : Blo 171799 591353 := bstep (se 2 (by rfl) ⟨221757, by rfl⟩ : syracuseStep 591353 = 443515) B443515
theorem B657011 : Blo 171799 657011 := bstep (se 1 (by rfl) ⟨492758, by rfl⟩ : syracuseStep 657011 = 985517) B985517
theorem B394919 : Blo 171799 394919 := bstep (se 1 (by rfl) ⟨296189, by rfl⟩ : syracuseStep 394919 = 592379) B592379
theorem B296615 : Blo 171799 296615 := bstep (se 1 (by rfl) ⟨222461, by rfl⟩ : syracuseStep 296615 = 444923) B444923
theorem B591623 : Blo 171799 591623 := bstep (se 1 (by rfl) ⟨443717, by rfl⟩ : syracuseStep 591623 = 887435) B887435
theorem B657193 : Blo 171799 657193 := bstep (se 2 (by rfl) ⟨246447, by rfl⟩ : syracuseStep 657193 = 492895) B492895
theorem B591677 : Blo 171799 591677 := bstep (se 3 (by rfl) ⟨110939, by rfl⟩ : syracuseStep 591677 = 221879) B221879
theorem B591815 : Blo 171799 591815 := bstep (se 1 (by rfl) ⟨443861, by rfl⟩ : syracuseStep 591815 = 887723) B887723
theorem B395207 : Blo 171799 395207 := bstep (se 1 (by rfl) ⟨296405, by rfl⟩ : syracuseStep 395207 = 592811) B592811
theorem B985061 : Blo 171799 985061 := bstep (se 4 (by rfl) ⟨92349, by rfl⟩ : syracuseStep 985061 = 184699) B184699
theorem B526571 : Blo 171799 526571 := bstep (se 1 (by rfl) ⟨394928, by rfl⟩ : syracuseStep 526571 = 789857) B789857
theorem B395513 : Blo 171799 395513 := bstep (se 2 (by rfl) ⟨148317, by rfl⟩ : syracuseStep 395513 = 296635) B296635
theorem B395567 : Blo 171799 395567 := bstep (se 1 (by rfl) ⟨296675, by rfl⟩ : syracuseStep 395567 = 593351) B593351
theorem B592285 : Blo 171799 592285 := bstep (se 3 (by rfl) ⟨111053, by rfl⟩ : syracuseStep 592285 = 222107) B222107
theorem B756641 : Blo 171799 756641 := bstep (se 2 (by rfl) ⟨283740, by rfl⟩ : syracuseStep 756641 = 567481) B567481
theorem B1182757 : Blo 171799 1182757 := bstep (se 4 (by rfl) ⟨110883, by rfl⟩ : syracuseStep 1182757 = 221767) B221767
theorem B330799 : Blo 171799 330799 := bstep (se 1 (by rfl) ⟨248099, by rfl⟩ : syracuseStep 330799 = 496199) B496199
theorem B560249 : Blo 171799 560249 := bstep (se 2 (by rfl) ⟨210093, by rfl⟩ : syracuseStep 560249 = 420187) B420187
theorem B560351 : Blo 171799 560351 := bstep (se 1 (by rfl) ⟨420263, by rfl⟩ : syracuseStep 560351 = 840527) B840527
theorem B2526653 : Blo 171799 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B9014777 : Blo 171799 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B1117891 : Blo 171799 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B1281737 : Blo 171799 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B560915 : Blo 171799 560915 := bstep (se 1 (by rfl) ⟨420686, by rfl⟩ : syracuseStep 560915 = 841373) B841373
theorem B2363755 : Blo 171799 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B495983 : Blo 171799 495983 := bstep (se 1 (by rfl) ⟨371987, by rfl⟩ : syracuseStep 495983 = 743975) B743975
theorem B496039 : Blo 171799 496039 := bstep (se 1 (by rfl) ⟨372029, by rfl⟩ : syracuseStep 496039 = 744059) B744059
theorem B659927 : Blo 171799 659927 := bstep (se 1 (by rfl) ⟨494945, by rfl⟩ : syracuseStep 659927 = 989891) B989891
theorem B2232791 : Blo 171799 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B889865 : Blo 171799 889865 := bstep (se 2 (by rfl) ⟨333699, by rfl⟩ : syracuseStep 889865 = 667399) B667399
theorem B1971215 : Blo 171799 1971215 := bstep (se 1 (by rfl) ⟨1478411, by rfl⟩ : syracuseStep 1971215 = 2956823) B2956823
theorem B1054043 : Blo 171799 1054043 := bstep (se 1 (by rfl) ⟨790532, by rfl⟩ : syracuseStep 1054043 = 1581065) B1581065
theorem B1250873 : Blo 171799 1250873 := bstep (se 2 (by rfl) ⟨469077, by rfl⟩ : syracuseStep 1250873 = 938155) B938155
theorem B497623 : Blo 171799 497623 := bstep (se 1 (by rfl) ⟨373217, by rfl⟩ : syracuseStep 497623 = 746435) B746435
theorem B497657 : Blo 171799 497657 := bstep (se 2 (by rfl) ⟨186621, by rfl⟩ : syracuseStep 497657 = 373243) B373243
theorem B2136145 : Blo 171799 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B497897 : Blo 171799 497897 := bstep (se 2 (by rfl) ⟨186711, by rfl⟩ : syracuseStep 497897 = 373423) B373423
theorem B530729 : Blo 171799 530729 := bstep (se 2 (by rfl) ⟨199023, by rfl⟩ : syracuseStep 530729 = 398047) B398047
theorem B8395109 : Blo 171799 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B596413 : Blo 171799 596413 := bstep (se 3 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 596413 = 223655) B223655
theorem B4463237 : Blo 171799 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B367519 : Blo 171799 367519 := bstep (se 1 (by rfl) ⟨275639, by rfl⟩ : syracuseStep 367519 = 551279) B551279
theorem B1252255 : Blo 171799 1252255 := bstep (se 1 (by rfl) ⟨939191, by rfl⟩ : syracuseStep 1252255 = 1878383) B1878383
theorem B2792663 : Blo 171799 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B990575 : Blo 171799 990575 := bstep (se 1 (by rfl) ⟨742931, by rfl⟩ : syracuseStep 990575 = 1485863) B1485863
theorem B302665 : Blo 171799 302665 := bstep (se 2 (by rfl) ⟨113499, by rfl⟩ : syracuseStep 302665 = 226999) B226999
theorem B171847 : Blo 171799 171847 := bstep (se 1 (by rfl) ⟨128885, by rfl⟩ : syracuseStep 171847 = 257771) B257771
theorem B171999 : Blo 171799 171999 := bstep (se 1 (by rfl) ⟨128999, by rfl⟩ : syracuseStep 171999 = 257999) B257999
theorem B1417351 : Blo 171799 1417351 := bstep (se 1 (by rfl) ⟨1063013, by rfl⟩ : syracuseStep 1417351 = 2126027) B2126027
theorem B172263 : Blo 171799 172263 := bstep (se 1 (by rfl) ⟨129197, by rfl⟩ : syracuseStep 172263 = 258395) B258395
theorem B5775731 : Blo 171799 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B172415 : Blo 171799 172415 := bstep (se 1 (by rfl) ⟨129311, by rfl⟩ : syracuseStep 172415 = 258623) B258623
theorem B172495 : Blo 171799 172495 := bstep (se 1 (by rfl) ⟨129371, by rfl⟩ : syracuseStep 172495 = 258743) B258743
theorem B172647 : Blo 171799 172647 := bstep (se 1 (by rfl) ⟨129485, by rfl⟩ : syracuseStep 172647 = 258971) B258971
theorem B172911 : Blo 171799 172911 := bstep (se 1 (by rfl) ⟨129683, by rfl⟩ : syracuseStep 172911 = 259367) B259367
theorem B172967 : Blo 171799 172967 := bstep (se 1 (by rfl) ⟨129725, by rfl⟩ : syracuseStep 172967 = 259451) B259451
theorem B173051 : Blo 171799 173051 := bstep (se 1 (by rfl) ⟨129788, by rfl⟩ : syracuseStep 173051 = 259577) B259577
theorem B271355 : Blo 171799 271355 := bstep (se 1 (by rfl) ⟨203516, by rfl⟩ : syracuseStep 271355 = 407033) B407033
theorem B173119 : Blo 171799 173119 := bstep (se 1 (by rfl) ⟨129839, by rfl⟩ : syracuseStep 173119 = 259679) B259679
theorem B173263 : Blo 171799 173263 := bstep (se 1 (by rfl) ⟨129947, by rfl⟩ : syracuseStep 173263 = 259895) B259895
theorem B664969 : Blo 171799 664969 := bstep (se 2 (by rfl) ⟨249363, by rfl⟩ : syracuseStep 664969 = 498727) B498727
theorem B173467 : Blo 171799 173467 := bstep (se 1 (by rfl) ⟨130100, by rfl⟩ : syracuseStep 173467 = 260201) B260201
theorem B960059 : Blo 171799 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B173679 : Blo 171799 173679 := bstep (se 1 (by rfl) ⟨130259, by rfl⟩ : syracuseStep 173679 = 260519) B260519
theorem B173735 : Blo 171799 173735 := bstep (se 1 (by rfl) ⟨130301, by rfl⟩ : syracuseStep 173735 = 260603) B260603
theorem B173819 : Blo 171799 173819 := bstep (se 1 (by rfl) ⟨130364, by rfl⟩ : syracuseStep 173819 = 260729) B260729
theorem B173855 : Blo 171799 173855 := bstep (se 1 (by rfl) ⟨130391, by rfl⟩ : syracuseStep 173855 = 260783) B260783
theorem B173887 : Blo 171799 173887 := bstep (se 1 (by rfl) ⟨130415, by rfl⟩ : syracuseStep 173887 = 260831) B260831
theorem B665441 : Blo 171799 665441 := bstep (se 2 (by rfl) ⟨249540, by rfl⟩ : syracuseStep 665441 = 499081) B499081
theorem B174063 : Blo 171799 174063 := bstep (se 1 (by rfl) ⟨130547, by rfl⟩ : syracuseStep 174063 = 261095) B261095
theorem B174235 : Blo 171799 174235 := bstep (se 1 (by rfl) ⟨130676, by rfl⟩ : syracuseStep 174235 = 261353) B261353
theorem B174271 : Blo 171799 174271 := bstep (se 1 (by rfl) ⟨130703, by rfl⟩ : syracuseStep 174271 = 261407) B261407
theorem B174383 : Blo 171799 174383 := bstep (se 1 (by rfl) ⟨130787, by rfl⟩ : syracuseStep 174383 = 261575) B261575
theorem B567713 : Blo 171799 567713 := bstep (se 2 (by rfl) ⟨212892, by rfl⟩ : syracuseStep 567713 = 425785) B425785
theorem B174619 : Blo 171799 174619 := bstep (se 1 (by rfl) ⟨130964, by rfl⟩ : syracuseStep 174619 = 261929) B261929
theorem B174623 : Blo 171799 174623 := bstep (se 1 (by rfl) ⟨130967, by rfl⟩ : syracuseStep 174623 = 261935) B261935
theorem B830263 : Blo 171799 830263 := bstep (se 1 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 830263 = 1245395) B1245395
theorem B174939 : Blo 171799 174939 := bstep (se 1 (by rfl) ⟨131204, by rfl⟩ : syracuseStep 174939 = 262409) B262409
theorem B175007 : Blo 171799 175007 := bstep (se 1 (by rfl) ⟨131255, by rfl⟩ : syracuseStep 175007 = 262511) B262511
theorem B175151 : Blo 171799 175151 := bstep (se 1 (by rfl) ⟨131363, by rfl⟩ : syracuseStep 175151 = 262727) B262727
theorem B175175 : Blo 171799 175175 := bstep (se 1 (by rfl) ⟨131381, by rfl⟩ : syracuseStep 175175 = 262763) B262763
theorem B437471 : Blo 171799 437471 := bstep (se 1 (by rfl) ⟨328103, by rfl⟩ : syracuseStep 437471 = 656207) B656207
theorem B175327 : Blo 171799 175327 := bstep (se 1 (by rfl) ⟨131495, by rfl⟩ : syracuseStep 175327 = 262991) B262991
theorem B175591 : Blo 171799 175591 := bstep (se 1 (by rfl) ⟨131693, by rfl⟩ : syracuseStep 175591 = 263387) B263387
theorem B175707 : Blo 171799 175707 := bstep (se 1 (by rfl) ⟨131780, by rfl⟩ : syracuseStep 175707 = 263561) B263561
theorem B1257389 : Blo 171799 1257389 := bstep (se 3 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 1257389 = 471521) B471521
theorem B831455 : Blo 171799 831455 := bstep (se 1 (by rfl) ⟨623591, by rfl⟩ : syracuseStep 831455 = 1247183) B1247183
theorem B733151 : Blo 171799 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B2404403 : Blo 171799 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B438655 : Blo 171799 438655 := bstep (se 1 (by rfl) ⟨328991, by rfl⟩ : syracuseStep 438655 = 657983) B657983
theorem B1421995 : Blo 171799 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B1324349 : Blo 171799 1324349 := bstep (se 3 (by rfl) ⟨248315, by rfl⟩ : syracuseStep 1324349 = 496631) B496631
theorem B1127945 : Blo 171799 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B472969 : Blo 171799 472969 := bstep (se 2 (by rfl) ⟨177363, by rfl⟩ : syracuseStep 472969 = 354727) B354727
theorem B2996189 : Blo 171799 2996189 := bstep (se 3 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 2996189 = 1123571) B1123571
theorem B440417 : Blo 171799 440417 := bstep (se 2 (by rfl) ⟨165156, by rfl⟩ : syracuseStep 440417 = 330313) B330313
theorem B7649579 : Blo 171799 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B834067 : Blo 171799 834067 := bstep (se 1 (by rfl) ⟨625550, by rfl⟩ : syracuseStep 834067 = 1251101) B1251101
theorem B441247 : Blo 171799 441247 := bstep (se 1 (by rfl) ⟨330935, by rfl⟩ : syracuseStep 441247 = 661871) B661871
theorem B638237 : Blo 171799 638237 := bstep (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) B239339
theorem B1326779 : Blo 171799 1326779 := bstep (se 1 (by rfl) ⟨995084, by rfl⟩ : syracuseStep 1326779 = 1990169) B1990169
theorem B376553 : Blo 171799 376553 := bstep (se 2 (by rfl) ⟨141207, by rfl⟩ : syracuseStep 376553 = 282415) B282415
theorem B638707 : Blo 171799 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B442655 : Blo 171799 442655 := bstep (se 1 (by rfl) ⟨331991, by rfl⟩ : syracuseStep 442655 = 663983) B663983
theorem B1065593 : Blo 171799 1065593 := bstep (se 2 (by rfl) ⟨399597, by rfl⟩ : syracuseStep 1065593 = 799195) B799195
theorem B443009 : Blo 171799 443009 := bstep (se 2 (by rfl) ⟨166128, by rfl⟩ : syracuseStep 443009 = 332257) B332257
theorem B10175291 : Blo 171799 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B1000349 : Blo 171799 1000349 := bstep (se 3 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 1000349 = 375131) B375131
theorem B443303 : Blo 171799 443303 := bstep (se 1 (by rfl) ⟨332477, by rfl⟩ : syracuseStep 443303 = 664955) B664955
theorem B279625 : Blo 171799 279625 := bstep (se 2 (by rfl) ⟨104859, by rfl⟩ : syracuseStep 279625 = 209719) B209719
theorem B443819 : Blo 171799 443819 := bstep (se 1 (by rfl) ⟨332864, by rfl⟩ : syracuseStep 443819 = 665729) B665729
theorem B312943 : Blo 171799 312943 := bstep (se 1 (by rfl) ⟨234707, by rfl⟩ : syracuseStep 312943 = 469415) B469415
theorem B313151 : Blo 171799 313151 := bstep (se 1 (by rfl) ⟨234863, by rfl⟩ : syracuseStep 313151 = 469727) B469727
theorem B1984337 : Blo 171799 1984337 := bstep (se 2 (by rfl) ⟨744126, by rfl⟩ : syracuseStep 1984337 = 1488253) B1488253
theorem B247963 : Blo 171799 247963 := bstep (se 1 (by rfl) ⟨185972, by rfl⟩ : syracuseStep 247963 = 371945) B371945
theorem B444811 : Blo 171799 444811 := bstep (se 1 (by rfl) ⟨333608, by rfl⟩ : syracuseStep 444811 = 667217) B667217
theorem B5130701 : Blo 171799 5130701 := bstep (se 3 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 5130701 = 1924013) B1924013
theorem B5067143 : Blo 171799 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B315847 : Blo 171799 315847 := bstep (se 1 (by rfl) ⟨236885, by rfl⟩ : syracuseStep 315847 = 473771) B473771
theorem B840719 : Blo 171799 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B218791 : Blo 171799 218791 := bstep (se 1 (by rfl) ⟨164093, by rfl⟩ : syracuseStep 218791 = 328187) B328187
theorem B186143 : Blo 171799 186143 := bstep (se 1 (by rfl) ⟨139607, by rfl⟩ : syracuseStep 186143 = 279215) B279215
theorem B1923047 : Blo 171799 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B841711 : Blo 171799 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B219439 : Blo 171799 219439 := bstep (se 1 (by rfl) ⟨164579, by rfl⟩ : syracuseStep 219439 = 329159) B329159
theorem B252283 : Blo 171799 252283 := bstep (se 1 (by rfl) ⟨189212, by rfl⟩ : syracuseStep 252283 = 378425) B378425
theorem B580553 : Blo 171799 580553 := bstep (se 2 (by rfl) ⟨217707, by rfl⟩ : syracuseStep 580553 = 435415) B435415
theorem B580823 : Blo 171799 580823 := bstep (se 1 (by rfl) ⟨435617, by rfl⟩ : syracuseStep 580823 = 871235) B871235
theorem B581363 : Blo 171799 581363 := bstep (se 1 (by rfl) ⟨436022, by rfl⟩ : syracuseStep 581363 = 872045) B872045
theorem B942461 : Blo 171799 942461 := bstep (se 3 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 942461 = 353423) B353423
theorem B8938291 : Blo 171799 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B222203 : Blo 171799 222203 := bstep (se 1 (by rfl) ⟨166652, by rfl⟩ : syracuseStep 222203 = 333305) B333305
theorem B1107067 : Blo 171799 1107067 := bstep (se 1 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 1107067 = 1660601) B1660601
theorem B1992023 : Blo 171799 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B878201 : Blo 171799 878201 := bstep (se 2 (by rfl) ⟨329325, by rfl⟩ : syracuseStep 878201 = 658651) B658651
theorem B386783 : Blo 171799 386783 := bstep (se 1 (by rfl) ⟨290087, by rfl⟩ : syracuseStep 386783 = 580175) B580175
theorem B2844503 : Blo 171799 2844503 := bstep (se 1 (by rfl) ⟨2133377, by rfl⟩ : syracuseStep 2844503 = 4266755) B4266755
theorem B551215 : Blo 171799 551215 := bstep (se 1 (by rfl) ⟨413411, by rfl⟩ : syracuseStep 551215 = 826823) B826823
theorem B4778299 : Blo 171799 4778299 := bstep (se 1 (by rfl) ⟨3583724, by rfl⟩ : syracuseStep 4778299 = 7167449) B7167449
theorem B387611 : Blo 171799 387611 := bstep (se 1 (by rfl) ⟨290708, by rfl⟩ : syracuseStep 387611 = 581417) B581417
theorem B5040899 : Blo 171799 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B584927 : Blo 171799 584927 := bstep (se 1 (by rfl) ⟨438695, by rfl⟩ : syracuseStep 584927 = 877391) B877391
theorem B585143 : Blo 171799 585143 := bstep (se 1 (by rfl) ⟨438857, by rfl⟩ : syracuseStep 585143 = 877715) B877715
theorem B1109629 : Blo 171799 1109629 := bstep (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) B416111
theorem B257711 : Blo 171799 257711 := bstep (se 1 (by rfl) ⟨193283, by rfl⟩ : syracuseStep 257711 = 386567) B386567
theorem B290479 : Blo 171799 290479 := bstep (se 1 (by rfl) ⟨217859, by rfl⟩ : syracuseStep 290479 = 435719) B435719
theorem B257831 : Blo 171799 257831 := bstep (se 1 (by rfl) ⟨193373, by rfl⟩ : syracuseStep 257831 = 386747) B386747
theorem B1994543 : Blo 171799 1994543 := bstep (se 1 (by rfl) ⟨1495907, by rfl⟩ : syracuseStep 1994543 = 2991815) B2991815
theorem B257915 : Blo 171799 257915 := bstep (se 1 (by rfl) ⟨193436, by rfl⟩ : syracuseStep 257915 = 386873) B386873
theorem B978911 : Blo 171799 978911 := bstep (se 1 (by rfl) ⟨734183, by rfl⟩ : syracuseStep 978911 = 1468367) B1468367
theorem B290783 : Blo 171799 290783 := bstep (se 1 (by rfl) ⟨218087, by rfl⟩ : syracuseStep 290783 = 436175) B436175
theorem B389087 : Blo 171799 389087 := bstep (se 1 (by rfl) ⟨291815, by rfl⟩ : syracuseStep 389087 = 583631) B583631
theorem B979229 : Blo 171799 979229 := bstep (se 3 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 979229 = 367211) B367211
theorem B258335 : Blo 171799 258335 := bstep (se 1 (by rfl) ⟨193751, by rfl⟩ : syracuseStep 258335 = 387503) B387503
theorem B291127 : Blo 171799 291127 := bstep (se 1 (by rfl) ⟨218345, by rfl⟩ : syracuseStep 291127 = 436691) B436691
theorem B258359 : Blo 171799 258359 := bstep (se 1 (by rfl) ⟨193769, by rfl⟩ : syracuseStep 258359 = 387539) B387539
theorem B258431 : Blo 171799 258431 := bstep (se 1 (by rfl) ⟨193823, by rfl⟩ : syracuseStep 258431 = 387647) B387647
theorem B258503 : Blo 171799 258503 := bstep (se 1 (by rfl) ⟨193877, by rfl⟩ : syracuseStep 258503 = 387755) B387755
theorem B979411 : Blo 171799 979411 := bstep (se 1 (by rfl) ⟨734558, by rfl⟩ : syracuseStep 979411 = 1469117) B1469117
theorem B750073 : Blo 171799 750073 := bstep (se 2 (by rfl) ⟨281277, by rfl⟩ : syracuseStep 750073 = 562555) B562555
theorem B291431 : Blo 171799 291431 := bstep (se 1 (by rfl) ⟨218573, by rfl⟩ : syracuseStep 291431 = 437147) B437147
theorem B389735 : Blo 171799 389735 := bstep (se 1 (by rfl) ⟨292301, by rfl⟩ : syracuseStep 389735 = 584603) B584603
theorem B291593 : Blo 171799 291593 := bstep (se 2 (by rfl) ⟨109347, by rfl⟩ : syracuseStep 291593 = 218695) B218695
theorem B258857 : Blo 171799 258857 := bstep (se 2 (by rfl) ⟨97071, by rfl⟩ : syracuseStep 258857 = 194143) B194143
theorem B258863 : Blo 171799 258863 := bstep (se 1 (by rfl) ⟨194147, by rfl⟩ : syracuseStep 258863 = 388295) B388295
theorem B619325 : Blo 171799 619325 := bstep (se 3 (by rfl) ⟨116123, by rfl⟩ : syracuseStep 619325 = 232247) B232247
theorem B258983 : Blo 171799 258983 := bstep (se 1 (by rfl) ⟨194237, by rfl⟩ : syracuseStep 258983 = 388475) B388475
theorem B193531 : Blo 171799 193531 := bstep (se 1 (by rfl) ⟨145148, by rfl⟩ : syracuseStep 193531 = 290297) B290297
theorem B259067 : Blo 171799 259067 := bstep (se 1 (by rfl) ⟨194300, by rfl⟩ : syracuseStep 259067 = 388601) B388601
theorem B259127 : Blo 171799 259127 := bstep (se 1 (by rfl) ⟨194345, by rfl⟩ : syracuseStep 259127 = 388691) B388691
theorem B455743 : Blo 171799 455743 := bstep (se 1 (by rfl) ⟨341807, by rfl⟩ : syracuseStep 455743 = 683615) B683615
theorem B193711 : Blo 171799 193711 := bstep (se 1 (by rfl) ⟨145283, by rfl⟩ : syracuseStep 193711 = 290567) B290567
theorem B259247 : Blo 171799 259247 := bstep (se 1 (by rfl) ⟨194435, by rfl⟩ : syracuseStep 259247 = 388871) B388871
theorem B390419 : Blo 171799 390419 := bstep (se 1 (by rfl) ⟨292814, by rfl⟩ : syracuseStep 390419 = 585629) B585629
theorem B292187 : Blo 171799 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B390491 : Blo 171799 390491 := bstep (se 1 (by rfl) ⟨292868, by rfl⟩ : syracuseStep 390491 = 585737) B585737
theorem B587195 : Blo 171799 587195 := bstep (se 1 (by rfl) ⟨440396, by rfl⟩ : syracuseStep 587195 = 880793) B880793
theorem B2094599 : Blo 171799 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B259655 : Blo 171799 259655 := bstep (se 1 (by rfl) ⟨194741, by rfl⟩ : syracuseStep 259655 = 389483) B389483
theorem B292423 : Blo 171799 292423 := bstep (se 1 (by rfl) ⟨219317, by rfl⟩ : syracuseStep 292423 = 438635) B438635
theorem B194215 : Blo 171799 194215 := bstep (se 1 (by rfl) ⟨145661, by rfl⟩ : syracuseStep 194215 = 291323) B291323
theorem B259751 : Blo 171799 259751 := bstep (se 1 (by rfl) ⟨194813, by rfl⟩ : syracuseStep 259751 = 389627) B389627
theorem B259835 : Blo 171799 259835 := bstep (se 1 (by rfl) ⟨194876, by rfl⟩ : syracuseStep 259835 = 389753) B389753
theorem B259871 : Blo 171799 259871 := bstep (se 1 (by rfl) ⟨194903, by rfl⟩ : syracuseStep 259871 = 389807) B389807
theorem B292639 : Blo 171799 292639 := bstep (se 1 (by rfl) ⟨219479, by rfl⟩ : syracuseStep 292639 = 438959) B438959
theorem B259919 : Blo 171799 259919 := bstep (se 1 (by rfl) ⟨194939, by rfl⟩ : syracuseStep 259919 = 389879) B389879
theorem B391049 : Blo 171799 391049 := bstep (se 2 (by rfl) ⟨146643, by rfl⟩ : syracuseStep 391049 = 293287) B293287
theorem B194503 : Blo 171799 194503 := bstep (se 1 (by rfl) ⟨145877, by rfl⟩ : syracuseStep 194503 = 291755) B291755
theorem B260039 : Blo 171799 260039 := bstep (se 1 (by rfl) ⟨195029, by rfl⟩ : syracuseStep 260039 = 390059) B390059
theorem B587735 : Blo 171799 587735 := bstep (se 1 (by rfl) ⟨440801, by rfl⟩ : syracuseStep 587735 = 881603) B881603
theorem B292855 : Blo 171799 292855 := bstep (se 1 (by rfl) ⟨219641, by rfl⟩ : syracuseStep 292855 = 439283) B439283
theorem B653305 : Blo 171799 653305 := bstep (se 2 (by rfl) ⟨244989, by rfl⟩ : syracuseStep 653305 = 489979) B489979
theorem B391265 : Blo 171799 391265 := bstep (se 2 (by rfl) ⟨146724, by rfl⟩ : syracuseStep 391265 = 293449) B293449
theorem B293159 : Blo 171799 293159 := bstep (se 1 (by rfl) ⟨219869, by rfl⟩ : syracuseStep 293159 = 439739) B439739
theorem B260393 : Blo 171799 260393 := bstep (se 2 (by rfl) ⟨97647, by rfl⟩ : syracuseStep 260393 = 195295) B195295
theorem B194863 : Blo 171799 194863 := bstep (se 1 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 194863 = 292295) B292295
theorem B260399 : Blo 171799 260399 := bstep (se 1 (by rfl) ⟨195299, by rfl⟩ : syracuseStep 260399 = 390599) B390599
theorem B588221 : Blo 171799 588221 := bstep (se 3 (by rfl) ⟨110291, by rfl⟩ : syracuseStep 588221 = 220583) B220583
theorem B260639 : Blo 171799 260639 := bstep (se 1 (by rfl) ⟨195479, by rfl⟩ : syracuseStep 260639 = 390959) B390959
theorem B326281 : Blo 171799 326281 := bstep (se 2 (by rfl) ⟨122355, by rfl⟩ : syracuseStep 326281 = 244711) B244711
theorem B490207 : Blo 171799 490207 := bstep (se 1 (by rfl) ⟨367655, by rfl⟩ : syracuseStep 490207 = 735311) B735311
theorem B981827 : Blo 171799 981827 := bstep (se 1 (by rfl) ⟨736370, by rfl⟩ : syracuseStep 981827 = 1472741) B1472741
theorem B3341189 : Blo 171799 3341189 := bstep (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) B626473
theorem B1571719 : Blo 171799 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B261023 : Blo 171799 261023 := bstep (se 1 (by rfl) ⟨195767, by rfl⟩ : syracuseStep 261023 = 391535) B391535
theorem B1244069 : Blo 171799 1244069 := bstep (se 4 (by rfl) ⟨116631, by rfl⟩ : syracuseStep 1244069 = 233263) B233263
theorem B261071 : Blo 171799 261071 := bstep (se 1 (by rfl) ⟨195803, by rfl⟩ : syracuseStep 261071 = 391607) B391607
theorem B261161 : Blo 171799 261161 := bstep (se 2 (by rfl) ⟨97935, by rfl⟩ : syracuseStep 261161 = 195871) B195871
theorem B261167 : Blo 171799 261167 := bstep (se 1 (by rfl) ⟨195875, by rfl⟩ : syracuseStep 261167 = 391751) B391751
theorem B293935 : Blo 171799 293935 := bstep (se 1 (by rfl) ⟨220451, by rfl⟩ : syracuseStep 293935 = 440903) B440903
theorem B195655 : Blo 171799 195655 := bstep (se 1 (by rfl) ⟨146741, by rfl⟩ : syracuseStep 195655 = 293483) B293483
theorem B261191 : Blo 171799 261191 := bstep (se 1 (by rfl) ⟨195893, by rfl⟩ : syracuseStep 261191 = 391787) B391787
theorem B982145 : Blo 171799 982145 := bstep (se 2 (by rfl) ⟨368304, by rfl⟩ : syracuseStep 982145 = 736609) B736609
theorem B523529 : Blo 171799 523529 := bstep (se 2 (by rfl) ⟨196323, by rfl⟩ : syracuseStep 523529 = 392647) B392647
theorem B589085 : Blo 171799 589085 := bstep (se 3 (by rfl) ⟨110453, by rfl⟩ : syracuseStep 589085 = 220907) B220907
theorem B261455 : Blo 171799 261455 := bstep (se 1 (by rfl) ⟨196091, by rfl⟩ : syracuseStep 261455 = 392183) B392183
theorem B3341735 : Blo 171799 3341735 := bstep (se 1 (by rfl) ⟨2506301, by rfl⟩ : syracuseStep 3341735 = 5012603) B5012603
theorem B392615 : Blo 171799 392615 := bstep (se 1 (by rfl) ⟨294461, by rfl⟩ : syracuseStep 392615 = 588923) B588923
theorem B261545 : Blo 171799 261545 := bstep (se 2 (by rfl) ⟨98079, by rfl⟩ : syracuseStep 261545 = 196159) B196159
theorem B294313 : Blo 171799 294313 := bstep (se 2 (by rfl) ⟨110367, by rfl⟩ : syracuseStep 294313 = 220735) B220735
theorem B294391 : Blo 171799 294391 := bstep (se 1 (by rfl) ⟨220793, by rfl⟩ : syracuseStep 294391 = 441587) B441587
theorem B261695 : Blo 171799 261695 := bstep (se 1 (by rfl) ⟨196271, by rfl⟩ : syracuseStep 261695 = 392543) B392543
theorem B392795 : Blo 171799 392795 := bstep (se 1 (by rfl) ⟨294596, by rfl⟩ : syracuseStep 392795 = 589193) B589193
theorem B491255 : Blo 171799 491255 := bstep (se 1 (by rfl) ⟨368441, by rfl⟩ : syracuseStep 491255 = 736883) B736883
theorem B261959 : Blo 171799 261959 := bstep (se 1 (by rfl) ⟨196469, by rfl⟩ : syracuseStep 261959 = 392939) B392939
theorem B589655 : Blo 171799 589655 := bstep (se 1 (by rfl) ⟨442241, by rfl⟩ : syracuseStep 589655 = 884483) B884483
theorem B294779 : Blo 171799 294779 := bstep (se 1 (by rfl) ⟨221084, by rfl⟩ : syracuseStep 294779 = 442169) B442169
theorem B393083 : Blo 171799 393083 := bstep (se 1 (by rfl) ⟨294812, by rfl⟩ : syracuseStep 393083 = 589625) B589625
theorem B262043 : Blo 171799 262043 := bstep (se 1 (by rfl) ⟨196532, by rfl⟩ : syracuseStep 262043 = 393065) B393065
theorem B40468403 : Blo 171799 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B393407 : Blo 171799 393407 := bstep (se 1 (by rfl) ⟨295055, by rfl⟩ : syracuseStep 393407 = 590111) B590111
theorem B295103 : Blo 171799 295103 := bstep (se 1 (by rfl) ⟨221327, by rfl⟩ : syracuseStep 295103 = 442655) B442655
theorem B262379 : Blo 171799 262379 := bstep (se 1 (by rfl) ⟨196784, by rfl⟩ : syracuseStep 262379 = 393569) B393569
theorem B262439 : Blo 171799 262439 := bstep (se 1 (by rfl) ⟨196829, by rfl⟩ : syracuseStep 262439 = 393659) B393659
theorem B655735 : Blo 171799 655735 := bstep (se 1 (by rfl) ⟨491801, by rfl⟩ : syracuseStep 655735 = 983603) B983603
theorem B295339 : Blo 171799 295339 := bstep (se 1 (by rfl) ⟨221504, by rfl⟩ : syracuseStep 295339 = 443009) B443009
theorem B6783527 : Blo 171799 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B393839 : Blo 171799 393839 := bstep (se 1 (by rfl) ⟨295379, by rfl⟩ : syracuseStep 393839 = 590759) B590759
theorem B295535 : Blo 171799 295535 := bstep (se 1 (by rfl) ⟨221651, by rfl⟩ : syracuseStep 295535 = 443303) B443303
theorem B3146363 : Blo 171799 3146363 := bstep (se 1 (by rfl) ⟨2359772, by rfl⟩ : syracuseStep 3146363 = 4719545) B4719545
theorem B295879 : Blo 171799 295879 := bstep (se 1 (by rfl) ⟨221909, by rfl⟩ : syracuseStep 295879 = 443819) B443819
theorem B263111 : Blo 171799 263111 := bstep (se 1 (by rfl) ⟨197333, by rfl⟩ : syracuseStep 263111 = 394667) B394667
theorem B394235 : Blo 171799 394235 := bstep (se 1 (by rfl) ⟨295676, by rfl⟩ : syracuseStep 394235 = 591353) B591353
theorem B263279 : Blo 171799 263279 := bstep (se 1 (by rfl) ⟨197459, by rfl⟩ : syracuseStep 263279 = 394919) B394919
theorem B197743 : Blo 171799 197743 := bstep (se 1 (by rfl) ⟨148307, by rfl⟩ : syracuseStep 197743 = 296615) B296615
theorem B394415 : Blo 171799 394415 := bstep (se 1 (by rfl) ⟨295811, by rfl⟩ : syracuseStep 394415 = 591623) B591623
theorem B394451 : Blo 171799 394451 := bstep (se 1 (by rfl) ⟨295838, by rfl⟩ : syracuseStep 394451 = 591677) B591677
theorem B394543 : Blo 171799 394543 := bstep (se 1 (by rfl) ⟨295907, by rfl⟩ : syracuseStep 394543 = 591815) B591815
theorem B263471 : Blo 171799 263471 := bstep (se 1 (by rfl) ⟨197603, by rfl⟩ : syracuseStep 263471 = 395207) B395207
theorem B656707 : Blo 171799 656707 := bstep (se 1 (by rfl) ⟨492530, by rfl⟩ : syracuseStep 656707 = 985061) B985061
theorem B394721 : Blo 171799 394721 := bstep (se 2 (by rfl) ⟨148020, by rfl⟩ : syracuseStep 394721 = 296041) B296041
theorem B1476089 : Blo 171799 1476089 := bstep (se 2 (by rfl) ⟨553533, by rfl⟩ : syracuseStep 1476089 = 1107067) B1107067
theorem B263675 : Blo 171799 263675 := bstep (se 1 (by rfl) ⟨197756, by rfl⟩ : syracuseStep 263675 = 395513) B395513
theorem B263711 : Blo 171799 263711 := bstep (se 1 (by rfl) ⟨197783, by rfl⟩ : syracuseStep 263711 = 395567) B395567
theorem B886625 : Blo 171799 886625 := bstep (se 2 (by rfl) ⟨332484, by rfl⟩ : syracuseStep 886625 = 664969) B664969
theorem B3180869 : Blo 171799 3180869 := bstep (se 4 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 3180869 = 596413) B596413
theorem B854491 : Blo 171799 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B592541 : Blo 171799 592541 := bstep (se 3 (by rfl) ⟨111101, by rfl⟩ : syracuseStep 592541 = 222203) B222203
theorem B330617 : Blo 171799 330617 := bstep (se 2 (by rfl) ⟨123981, by rfl⟩ : syracuseStep 330617 = 247963) B247963
theorem B330655 : Blo 171799 330655 := bstep (se 1 (by rfl) ⟨247991, by rfl⟩ : syracuseStep 330655 = 495983) B495983
theorem B3378095 : Blo 171799 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B593081 : Blo 171799 593081 := bstep (se 2 (by rfl) ⟨222405, by rfl⟩ : syracuseStep 593081 = 444811) B444811
theorem B789713 : Blo 171799 789713 := bstep (se 2 (by rfl) ⟨296142, by rfl⟩ : syracuseStep 789713 = 592285) B592285
theorem B593243 : Blo 171799 593243 := bstep (se 1 (by rfl) ⟨444932, by rfl⟩ : syracuseStep 593243 = 889865) B889865
theorem B1314143 : Blo 171799 1314143 := bstep (se 1 (by rfl) ⟨985607, by rfl⟩ : syracuseStep 1314143 = 1971215) B1971215
theorem B1282031 : Blo 171799 1282031 := bstep (se 1 (by rfl) ⟨961523, by rfl⟩ : syracuseStep 1282031 = 1923047) B1923047
theorem B331771 : Blo 171799 331771 := bstep (se 1 (by rfl) ⟨248828, by rfl⟩ : syracuseStep 331771 = 497657) B497657
theorem B1577009 : Blo 171799 1577009 := bstep (se 2 (by rfl) ⟨591378, by rfl⟩ : syracuseStep 1577009 = 1182757) B1182757
theorem B331931 : Blo 171799 331931 := bstep (se 1 (by rfl) ⟨248948, by rfl⟩ : syracuseStep 331931 = 497897) B497897
theorem B2560157 : Blo 171799 2560157 := bstep (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) B960059
theorem B496381 : Blo 171799 496381 := bstep (se 3 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 496381 = 186143) B186143
theorem B1479505 : Blo 171799 1479505 := bstep (se 2 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 1479505 = 1109629) B1109629
theorem B660383 : Blo 171799 660383 := bstep (se 1 (by rfl) ⟨495287, by rfl⟩ : syracuseStep 660383 = 990575) B990575
theorem B628307 : Blo 171799 628307 := bstep (se 1 (by rfl) ⟨471230, by rfl⟩ : syracuseStep 628307 = 942461) B942461
theorem B3151673 : Blo 171799 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B661385 : Blo 171799 661385 := bstep (se 2 (by rfl) ⟨248019, by rfl⟩ : syracuseStep 661385 = 496039) B496039
theorem B171807 : Blo 171799 171807 := bstep (se 1 (by rfl) ⟨128855, by rfl⟩ : syracuseStep 171807 = 257711) B257711
theorem B171887 : Blo 171799 171887 := bstep (se 1 (by rfl) ⟨128915, by rfl⟩ : syracuseStep 171887 = 257831) B257831
theorem B171943 : Blo 171799 171943 := bstep (se 1 (by rfl) ⟨128957, by rfl⟩ : syracuseStep 171943 = 257915) B257915
theorem B663497 : Blo 171799 663497 := bstep (se 2 (by rfl) ⟨248811, by rfl⟩ : syracuseStep 663497 = 497623) B497623
theorem B1122281 : Blo 171799 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B172223 : Blo 171799 172223 := bstep (se 1 (by rfl) ⟨129167, by rfl⟩ : syracuseStep 172223 = 258335) B258335
theorem B172239 : Blo 171799 172239 := bstep (se 1 (by rfl) ⟨129179, by rfl⟩ : syracuseStep 172239 = 258359) B258359
theorem B172287 : Blo 171799 172287 := bstep (se 1 (by rfl) ⟨129215, by rfl⟩ : syracuseStep 172287 = 258431) B258431
theorem B172335 : Blo 171799 172335 := bstep (se 1 (by rfl) ⟨129251, by rfl⟩ : syracuseStep 172335 = 258503) B258503
theorem B336377 : Blo 171799 336377 := bstep (se 2 (by rfl) ⟨126141, by rfl⟩ : syracuseStep 336377 = 252283) B252283
theorem B172571 : Blo 171799 172571 := bstep (se 1 (by rfl) ⟨129428, by rfl⟩ : syracuseStep 172571 = 258857) B258857
theorem B172575 : Blo 171799 172575 := bstep (se 1 (by rfl) ⟨129431, by rfl⟩ : syracuseStep 172575 = 258863) B258863
theorem B172655 : Blo 171799 172655 := bstep (se 1 (by rfl) ⟨129491, by rfl⟩ : syracuseStep 172655 = 258983) B258983
theorem B172711 : Blo 171799 172711 := bstep (se 1 (by rfl) ⟨129533, by rfl⟩ : syracuseStep 172711 = 259067) B259067
theorem B172751 : Blo 171799 172751 := bstep (se 1 (by rfl) ⟨129563, by rfl⟩ : syracuseStep 172751 = 259127) B259127
theorem B172831 : Blo 171799 172831 := bstep (se 1 (by rfl) ⟨129623, by rfl⟩ : syracuseStep 172831 = 259247) B259247
theorem B435041 : Blo 171799 435041 := bstep (se 2 (by rfl) ⟨163140, by rfl⟩ : syracuseStep 435041 = 326281) B326281
theorem B173103 : Blo 171799 173103 := bstep (se 1 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 173103 = 259655) B259655
theorem B173167 : Blo 171799 173167 := bstep (se 1 (by rfl) ⟨129875, by rfl⟩ : syracuseStep 173167 = 259751) B259751
theorem B173223 : Blo 171799 173223 := bstep (se 1 (by rfl) ⟨129917, by rfl⟩ : syracuseStep 173223 = 259835) B259835
theorem B173247 : Blo 171799 173247 := bstep (se 1 (by rfl) ⟨129935, by rfl⟩ : syracuseStep 173247 = 259871) B259871
theorem B173279 : Blo 171799 173279 := bstep (se 1 (by rfl) ⟨129959, by rfl⟩ : syracuseStep 173279 = 259919) B259919
theorem B173359 : Blo 171799 173359 := bstep (se 1 (by rfl) ⟨130019, by rfl⟩ : syracuseStep 173359 = 260039) B260039
theorem B173595 : Blo 171799 173595 := bstep (se 1 (by rfl) ⟨130196, by rfl⟩ : syracuseStep 173595 = 260393) B260393
theorem B173599 : Blo 171799 173599 := bstep (se 1 (by rfl) ⟨130199, by rfl⟩ : syracuseStep 173599 = 260399) B260399
theorem B173759 : Blo 171799 173759 := bstep (se 1 (by rfl) ⟨130319, by rfl⟩ : syracuseStep 173759 = 260639) B260639
theorem B174015 : Blo 171799 174015 := bstep (se 1 (by rfl) ⟨130511, by rfl⟩ : syracuseStep 174015 = 261023) B261023
theorem B829379 : Blo 171799 829379 := bstep (se 1 (by rfl) ⟨622034, by rfl⟩ : syracuseStep 829379 = 1244069) B1244069
theorem B174047 : Blo 171799 174047 := bstep (se 1 (by rfl) ⟨130535, by rfl⟩ : syracuseStep 174047 = 261071) B261071
theorem B174107 : Blo 171799 174107 := bstep (se 1 (by rfl) ⟨130580, by rfl⟩ : syracuseStep 174107 = 261161) B261161
theorem B174111 : Blo 171799 174111 := bstep (se 1 (by rfl) ⟨130583, by rfl⟩ : syracuseStep 174111 = 261167) B261167
theorem B174127 : Blo 171799 174127 := bstep (se 1 (by rfl) ⟨130595, by rfl⟩ : syracuseStep 174127 = 261191) B261191
theorem B403553 : Blo 171799 403553 := bstep (se 2 (by rfl) ⟨151332, by rfl⟩ : syracuseStep 403553 = 302665) B302665
theorem B174303 : Blo 171799 174303 := bstep (se 1 (by rfl) ⟨130727, by rfl⟩ : syracuseStep 174303 = 261455) B261455
theorem B174363 : Blo 171799 174363 := bstep (se 1 (by rfl) ⟨130772, by rfl⟩ : syracuseStep 174363 = 261545) B261545
theorem B174463 : Blo 171799 174463 := bstep (se 1 (by rfl) ⟨130847, by rfl⟩ : syracuseStep 174463 = 261695) B261695
theorem B174639 : Blo 171799 174639 := bstep (se 1 (by rfl) ⟨130979, by rfl⟩ : syracuseStep 174639 = 261959) B261959
theorem B174695 : Blo 171799 174695 := bstep (se 1 (by rfl) ⟨131021, by rfl⟩ : syracuseStep 174695 = 262043) B262043
theorem B2894453 : Blo 171799 2894453 := bstep (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) B271355
theorem B26978935 : Blo 171799 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B175071 : Blo 171799 175071 := bstep (se 1 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 175071 = 262607) B262607
theorem B175099 : Blo 171799 175099 := bstep (se 1 (by rfl) ⟨131324, by rfl⟩ : syracuseStep 175099 = 262649) B262649
theorem B175167 : Blo 171799 175167 := bstep (se 1 (by rfl) ⟨131375, by rfl⟩ : syracuseStep 175167 = 262751) B262751
theorem B371783 : Blo 171799 371783 := bstep (se 1 (by rfl) ⟨278837, by rfl⟩ : syracuseStep 371783 = 557675) B557675
theorem B666899 : Blo 171799 666899 := bstep (se 1 (by rfl) ⟨500174, by rfl⟩ : syracuseStep 666899 = 1000349) B1000349
theorem B175487 : Blo 171799 175487 := bstep (se 1 (by rfl) ⟨131615, by rfl⟩ : syracuseStep 175487 = 263231) B263231
theorem B175515 : Blo 171799 175515 := bstep (se 1 (by rfl) ⟨131636, by rfl⟩ : syracuseStep 175515 = 263273) B263273
theorem B175583 : Blo 171799 175583 := bstep (se 1 (by rfl) ⟨131687, by rfl⟩ : syracuseStep 175583 = 263375) B263375
theorem B175719 : Blo 171799 175719 := bstep (se 1 (by rfl) ⟨131789, by rfl⟩ : syracuseStep 175719 = 263579) B263579
theorem B438007 : Blo 171799 438007 := bstep (se 1 (by rfl) ⟨328505, by rfl⟩ : syracuseStep 438007 = 657011) B657011
theorem B1322891 : Blo 171799 1322891 := bstep (se 1 (by rfl) ⟨992168, by rfl⟩ : syracuseStep 1322891 = 1984337) B1984337
theorem B372833 : Blo 171799 372833 := bstep (se 2 (by rfl) ⟨139812, by rfl⟩ : syracuseStep 372833 = 279625) B279625
theorem B3420467 : Blo 171799 3420467 := bstep (se 1 (by rfl) ⟨2565350, by rfl⟩ : syracuseStep 3420467 = 5130701) B5130701
theorem B504427 : Blo 171799 504427 := bstep (se 1 (by rfl) ⟨378320, by rfl⟩ : syracuseStep 504427 = 756641) B756641
theorem B373499 : Blo 171799 373499 := bstep (se 1 (by rfl) ⟨280124, by rfl⟩ : syracuseStep 373499 = 560249) B560249
theorem B373567 : Blo 171799 373567 := bstep (se 1 (by rfl) ⟨280175, by rfl⟩ : syracuseStep 373567 = 560351) B560351
theorem B1684435 : Blo 171799 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B6009851 : Blo 171799 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B373943 : Blo 171799 373943 := bstep (se 1 (by rfl) ⟨280457, by rfl⟩ : syracuseStep 373943 = 560915) B560915
theorem B2241917 : Blo 171799 2241917 := bstep (se 3 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 2241917 = 840719) B840719
theorem B439951 : Blo 171799 439951 := bstep (se 1 (by rfl) ⟨329963, by rfl⟩ : syracuseStep 439951 = 659927) B659927
theorem B1488527 : Blo 171799 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B734953 : Blo 171799 734953 := bstep (se 2 (by rfl) ⟨275607, by rfl⟩ : syracuseStep 734953 = 551215) B551215
theorem B6371065 : Blo 171799 6371065 := bstep (se 2 (by rfl) ⟨2389149, by rfl⟩ : syracuseStep 6371065 = 4778299) B4778299
theorem B702695 : Blo 171799 702695 := bstep (se 1 (by rfl) ⟨527021, by rfl⟩ : syracuseStep 702695 = 1054043) B1054043
theorem B833915 : Blo 171799 833915 := bstep (se 1 (by rfl) ⟨625436, by rfl⟩ : syracuseStep 833915 = 1250873) B1250873
theorem B5585597 : Blo 171799 5585597 := bstep (se 3 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 5585597 = 2094599) B2094599
theorem B441065 : Blo 171799 441065 := bstep (se 2 (by rfl) ⟨165399, by rfl⟩ : syracuseStep 441065 = 330799) B330799
theorem B835069 : Blo 171799 835069 := bstep (se 3 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 835069 = 313151) B313151
theorem B1490521 : Blo 171799 1490521 := bstep (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) B1117891
theorem B3850487 : Blo 171799 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B1000097 : Blo 171799 1000097 := bstep (se 2 (by rfl) ⟨375036, by rfl⟩ : syracuseStep 1000097 = 750073) B750073
theorem B1328015 : Blo 171799 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B443627 : Blo 171799 443627 := bstep (se 1 (by rfl) ⟨332720, by rfl⟩ : syracuseStep 443627 = 665441) B665441
theorem B607657 : Blo 171799 607657 := bstep (se 2 (by rfl) ⟨227871, by rfl⟩ : syracuseStep 607657 = 455743) B455743
theorem B378475 : Blo 171799 378475 := bstep (se 1 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 378475 = 567713) B567713
theorem B3360599 : Blo 171799 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B1329695 : Blo 171799 1329695 := bstep (se 1 (by rfl) ⟨997271, by rfl⟩ : syracuseStep 1329695 = 1994543) B1994543
theorem B838259 : Blo 171799 838259 := bstep (se 1 (by rfl) ⟨628694, by rfl⟩ : syracuseStep 838259 = 1257389) B1257389
theorem B871073 : Blo 171799 871073 := bstep (se 2 (by rfl) ⟨326652, by rfl⟩ : syracuseStep 871073 = 653305) B653305
theorem B412883 : Blo 171799 412883 := bstep (se 1 (by rfl) ⟨309662, by rfl⟩ : syracuseStep 412883 = 619325) B619325
theorem B5099719 : Blo 171799 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B1004141 : Blo 171799 1004141 := bstep (se 3 (by rfl) ⟨188276, by rfl⟩ : syracuseStep 1004141 = 376553) B376553
theorem B349019 : Blo 171799 349019 := bstep (se 1 (by rfl) ⟨261764, by rfl⟩ : syracuseStep 349019 = 523529) B523529
theorem B1889801 : Blo 171799 1889801 := bstep (se 2 (by rfl) ⟨708675, by rfl⟩ : syracuseStep 1889801 = 1417351) B1417351
theorem B7296551 : Blo 171799 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B743033 : Blo 171799 743033 := bstep (se 2 (by rfl) ⟨278637, by rfl⟩ : syracuseStep 743033 = 557275) B557275
theorem B874151 : Blo 171799 874151 := bstep (se 1 (by rfl) ⟨655613, by rfl⟩ : syracuseStep 874151 = 1311227) B1311227
theorem B11917721 : Blo 171799 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B351047 : Blo 171799 351047 := bstep (se 1 (by rfl) ⟨263285, by rfl⟩ : syracuseStep 351047 = 526571) B526571
theorem B2841581 : Blo 171799 2841581 := bstep (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) B1065593
theorem B417257 : Blo 171799 417257 := bstep (se 2 (by rfl) ⟨156471, by rfl⟩ : syracuseStep 417257 = 312943) B312943
theorem B876257 : Blo 171799 876257 := bstep (se 2 (by rfl) ⟨328596, by rfl⟩ : syracuseStep 876257 = 657193) B657193
theorem B4448357 : Blo 171799 4448357 := bstep (se 4 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 4448357 = 834067) B834067
theorem B1107017 : Blo 171799 1107017 := bstep (se 2 (by rfl) ⟨415131, by rfl⟩ : syracuseStep 1107017 = 830263) B830263
theorem B3007853 : Blo 171799 3007853 := bstep (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) B1127945
theorem B353819 : Blo 171799 353819 := bstep (se 1 (by rfl) ⟨265364, by rfl⟩ : syracuseStep 353819 = 530729) B530729
theorem B5596739 : Blo 171799 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B2975491 : Blo 171799 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B387035 : Blo 171799 387035 := bstep (se 1 (by rfl) ⟨290276, by rfl⟩ : syracuseStep 387035 = 580553) B580553
theorem B387215 : Blo 171799 387215 := bstep (se 1 (by rfl) ⟨290411, by rfl⟩ : syracuseStep 387215 = 580823) B580823
theorem B1861775 : Blo 171799 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B387305 : Blo 171799 387305 := bstep (se 2 (by rfl) ⟨145239, by rfl⟩ : syracuseStep 387305 = 290479) B290479
theorem B387575 : Blo 171799 387575 := bstep (se 1 (by rfl) ⟨290681, by rfl⟩ : syracuseStep 387575 = 581363) B581363
theorem B388169 : Blo 171799 388169 := bstep (se 2 (by rfl) ⟨145563, by rfl⟩ : syracuseStep 388169 = 291127) B291127
theorem B584873 : Blo 171799 584873 := bstep (se 2 (by rfl) ⟨219327, by rfl⟩ : syracuseStep 584873 = 438655) B438655
theorem B421129 : Blo 171799 421129 := bstep (se 2 (by rfl) ⟨157923, by rfl⟩ : syracuseStep 421129 = 315847) B315847
theorem B1305881 : Blo 171799 1305881 := bstep (se 2 (by rfl) ⟨489705, by rfl⟩ : syracuseStep 1305881 = 979411) B979411
theorem B1895993 : Blo 171799 1895993 := bstep (se 2 (by rfl) ⟨710997, by rfl⟩ : syracuseStep 1895993 = 1421995) B1421995
theorem B585467 : Blo 171799 585467 := bstep (se 1 (by rfl) ⟨439100, by rfl⟩ : syracuseStep 585467 = 878201) B878201
theorem B257855 : Blo 171799 257855 := bstep (se 1 (by rfl) ⟨193391, by rfl⟩ : syracuseStep 257855 = 386783) B386783
theorem B1896335 : Blo 171799 1896335 := bstep (se 1 (by rfl) ⟨1422251, by rfl⟩ : syracuseStep 1896335 = 2844503) B2844503
theorem B258041 : Blo 171799 258041 := bstep (se 2 (by rfl) ⟨96765, by rfl⟩ : syracuseStep 258041 = 193531) B193531
theorem B258281 : Blo 171799 258281 := bstep (se 2 (by rfl) ⟨96855, by rfl⟩ : syracuseStep 258281 = 193711) B193711
theorem B258407 : Blo 171799 258407 := bstep (se 1 (by rfl) ⟨193805, by rfl⟩ : syracuseStep 258407 = 387611) B387611
theorem B389897 : Blo 171799 389897 := bstep (se 2 (by rfl) ⟨146211, by rfl⟩ : syracuseStep 389897 = 292423) B292423
theorem B291647 : Blo 171799 291647 := bstep (se 1 (by rfl) ⟨218735, by rfl⟩ : syracuseStep 291647 = 437471) B437471
theorem B389951 : Blo 171799 389951 := bstep (se 1 (by rfl) ⟨292463, by rfl⟩ : syracuseStep 389951 = 584927) B584927
theorem B258953 : Blo 171799 258953 := bstep (se 2 (by rfl) ⟨97107, by rfl⟩ : syracuseStep 258953 = 194215) B194215
theorem B291721 : Blo 171799 291721 := bstep (se 2 (by rfl) ⟨109395, by rfl⟩ : syracuseStep 291721 = 218791) B218791
theorem B390095 : Blo 171799 390095 := bstep (se 1 (by rfl) ⟨292571, by rfl⟩ : syracuseStep 390095 = 585143) B585143
theorem B390185 : Blo 171799 390185 := bstep (se 2 (by rfl) ⟨146319, by rfl⟩ : syracuseStep 390185 = 292639) B292639
theorem B259337 : Blo 171799 259337 := bstep (se 2 (by rfl) ⟨97251, by rfl⟩ : syracuseStep 259337 = 194503) B194503
theorem B652607 : Blo 171799 652607 := bstep (se 1 (by rfl) ⟨489455, by rfl⟩ : syracuseStep 652607 = 978911) B978911
theorem B193855 : Blo 171799 193855 := bstep (se 1 (by rfl) ⟨145391, by rfl⟩ : syracuseStep 193855 = 290783) B290783
theorem B259391 : Blo 171799 259391 := bstep (se 1 (by rfl) ⟨194543, by rfl⟩ : syracuseStep 259391 = 389087) B389087
theorem B554303 : Blo 171799 554303 := bstep (se 1 (by rfl) ⟨415727, by rfl⟩ : syracuseStep 554303 = 831455) B831455
theorem B488767 : Blo 171799 488767 := bstep (se 1 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 488767 = 733151) B733151
theorem B390473 : Blo 171799 390473 := bstep (se 2 (by rfl) ⟨146427, by rfl⟩ : syracuseStep 390473 = 292855) B292855
theorem B1602935 : Blo 171799 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B2848193 : Blo 171799 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B652819 : Blo 171799 652819 := bstep (se 1 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 652819 = 979229) B979229
theorem B259817 : Blo 171799 259817 := bstep (se 2 (by rfl) ⟨97431, by rfl⟩ : syracuseStep 259817 = 194863) B194863
theorem B292585 : Blo 171799 292585 := bstep (se 2 (by rfl) ⟨109719, by rfl⟩ : syracuseStep 292585 = 219439) B219439
theorem B194287 : Blo 171799 194287 := bstep (se 1 (by rfl) ⟨145715, by rfl⟩ : syracuseStep 194287 = 291431) B291431
theorem B259823 : Blo 171799 259823 := bstep (se 1 (by rfl) ⟨194867, by rfl⟩ : syracuseStep 259823 = 389735) B389735
theorem B194395 : Blo 171799 194395 := bstep (se 1 (by rfl) ⟨145796, by rfl⟩ : syracuseStep 194395 = 291593) B291593
theorem B1701965 : Blo 171799 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B260279 : Blo 171799 260279 := bstep (se 1 (by rfl) ⟨195209, by rfl⟩ : syracuseStep 260279 = 390419) B390419
theorem B882899 : Blo 171799 882899 := bstep (se 1 (by rfl) ⟨662174, by rfl⟩ : syracuseStep 882899 = 1324349) B1324349
theorem B194791 : Blo 171799 194791 := bstep (se 1 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 194791 = 292187) B292187
theorem B260327 : Blo 171799 260327 := bstep (se 1 (by rfl) ⟨195245, by rfl⟩ : syracuseStep 260327 = 390491) B390491
theorem B391463 : Blo 171799 391463 := bstep (se 1 (by rfl) ⟨293597, by rfl⟩ : syracuseStep 391463 = 587195) B587195
theorem B653609 : Blo 171799 653609 := bstep (se 2 (by rfl) ⟨245103, by rfl⟩ : syracuseStep 653609 = 490207) B490207
theorem B2095625 : Blo 171799 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B490025 : Blo 171799 490025 := bstep (se 2 (by rfl) ⟨183759, by rfl⟩ : syracuseStep 490025 = 367519) B367519
theorem B1669673 : Blo 171799 1669673 := bstep (se 2 (by rfl) ⟨626127, by rfl⟩ : syracuseStep 1669673 = 1252255) B1252255
theorem B588329 : Blo 171799 588329 := bstep (se 2 (by rfl) ⟨220623, by rfl⟩ : syracuseStep 588329 = 441247) B441247
theorem B260699 : Blo 171799 260699 := bstep (se 1 (by rfl) ⟨195524, by rfl⟩ : syracuseStep 260699 = 391049) B391049
theorem B391823 : Blo 171799 391823 := bstep (se 1 (by rfl) ⟨293867, by rfl⟩ : syracuseStep 391823 = 587735) B587735
theorem B1997459 : Blo 171799 1997459 := bstep (se 1 (by rfl) ⟨1498094, by rfl⟩ : syracuseStep 1997459 = 2996189) B2996189
theorem B391913 : Blo 171799 391913 := bstep (se 2 (by rfl) ⟨146967, by rfl⟩ : syracuseStep 391913 = 293935) B293935
theorem B260843 : Blo 171799 260843 := bstep (se 1 (by rfl) ⟨195632, by rfl⟩ : syracuseStep 260843 = 391265) B391265
theorem B293611 : Blo 171799 293611 := bstep (se 1 (by rfl) ⟨220208, by rfl⟩ : syracuseStep 293611 = 440417) B440417
theorem B260873 : Blo 171799 260873 := bstep (se 2 (by rfl) ⟨97827, by rfl⟩ : syracuseStep 260873 = 195655) B195655
theorem B195439 : Blo 171799 195439 := bstep (se 1 (by rfl) ⟨146579, by rfl⟩ : syracuseStep 195439 = 293159) B293159
theorem B392147 : Blo 171799 392147 := bstep (se 1 (by rfl) ⟨294110, by rfl⟩ : syracuseStep 392147 = 588221) B588221
theorem B654551 : Blo 171799 654551 := bstep (se 1 (by rfl) ⟨490913, by rfl⟩ : syracuseStep 654551 = 981827) B981827
theorem B392417 : Blo 171799 392417 := bstep (se 2 (by rfl) ⟨147156, by rfl⟩ : syracuseStep 392417 = 294313) B294313
theorem B2227459 : Blo 171799 2227459 := bstep (se 1 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 2227459 = 3341189) B3341189
theorem B392521 : Blo 171799 392521 := bstep (se 2 (by rfl) ⟨147195, by rfl⟩ : syracuseStep 392521 = 294391) B294391
theorem B2522501 : Blo 171799 2522501 := bstep (se 4 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 2522501 = 472969) B472969
theorem B654763 : Blo 171799 654763 := bstep (se 1 (by rfl) ⟨491072, by rfl⟩ : syracuseStep 654763 = 982145) B982145
theorem B392723 : Blo 171799 392723 := bstep (se 1 (by rfl) ⟨294542, by rfl⟩ : syracuseStep 392723 = 589085) B589085
theorem B2227823 : Blo 171799 2227823 := bstep (se 1 (by rfl) ⟨1670867, by rfl⟩ : syracuseStep 2227823 = 3341735) B3341735
theorem B261743 : Blo 171799 261743 := bstep (se 1 (by rfl) ⟨196307, by rfl⟩ : syracuseStep 261743 = 392615) B392615
theorem B851609 : Blo 171799 851609 := bstep (se 2 (by rfl) ⟨319353, by rfl⟩ : syracuseStep 851609 = 638707) B638707
theorem B261863 : Blo 171799 261863 := bstep (se 1 (by rfl) ⟨196397, by rfl⟩ : syracuseStep 261863 = 392795) B392795
theorem B884519 : Blo 171799 884519 := bstep (se 1 (by rfl) ⟨663389, by rfl⟩ : syracuseStep 884519 = 1326779) B1326779
theorem B327503 : Blo 171799 327503 := bstep (se 1 (by rfl) ⟨245627, by rfl⟩ : syracuseStep 327503 = 491255) B491255
theorem B393103 : Blo 171799 393103 := bstep (se 1 (by rfl) ⟨294827, by rfl⟩ : syracuseStep 393103 = 589655) B589655
theorem B196519 : Blo 171799 196519 := bstep (se 1 (by rfl) ⟨147389, by rfl⟩ : syracuseStep 196519 = 294779) B294779
theorem B262055 : Blo 171799 262055 := bstep (se 1 (by rfl) ⟨196541, by rfl⟩ : syracuseStep 262055 = 393083) B393083
theorem B262271 : Blo 171799 262271 := bstep (se 1 (by rfl) ⟨196703, by rfl⟩ : syracuseStep 262271 = 393407) B393407
theorem B196735 : Blo 171799 196735 := bstep (se 1 (by rfl) ⟨147551, by rfl⟩ : syracuseStep 196735 = 295103) B295103
theorem B262559 : Blo 171799 262559 := bstep (se 1 (by rfl) ⟨196919, by rfl⟩ : syracuseStep 262559 = 393839) B393839
theorem B197023 : Blo 171799 197023 := bstep (se 1 (by rfl) ⟨147767, by rfl⟩ : syracuseStep 197023 = 295535) B295535
theorem B2097575 : Blo 171799 2097575 := bstep (se 1 (by rfl) ⟨1573181, by rfl⟩ : syracuseStep 2097575 = 3146363) B3146363
theorem B393785 : Blo 171799 393785 := bstep (se 2 (by rfl) ⟨147669, by rfl⟩ : syracuseStep 393785 = 295339) B295339
theorem B885343 : Blo 171799 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B262823 : Blo 171799 262823 := bstep (se 1 (by rfl) ⟨197117, by rfl⟩ : syracuseStep 262823 = 394235) B394235
theorem B262943 : Blo 171799 262943 := bstep (se 1 (by rfl) ⟨197207, by rfl⟩ : syracuseStep 262943 = 394415) B394415
theorem B262967 : Blo 171799 262967 := bstep (se 1 (by rfl) ⟨197225, by rfl⟩ : syracuseStep 262967 = 394451) B394451
theorem B295751 : Blo 171799 295751 := bstep (se 1 (by rfl) ⟨221813, by rfl⟩ : syracuseStep 295751 = 443627) B443627
theorem B263147 : Blo 171799 263147 := bstep (se 1 (by rfl) ⟨197360, by rfl⟩ : syracuseStep 263147 = 394721) B394721
theorem B984059 : Blo 171799 984059 := bstep (se 1 (by rfl) ⟨738044, by rfl⟩ : syracuseStep 984059 = 1476089) B1476089
theorem B591083 : Blo 171799 591083 := bstep (se 1 (by rfl) ⟨443312, by rfl⟩ : syracuseStep 591083 = 886625) B886625
theorem B394505 : Blo 171799 394505 := bstep (se 2 (by rfl) ⟨147939, by rfl⟩ : syracuseStep 394505 = 295879) B295879
theorem B18089405 : Blo 171799 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B263657 : Blo 171799 263657 := bstep (se 2 (by rfl) ⟨98871, by rfl⟩ : syracuseStep 263657 = 197743) B197743
theorem B886463 : Blo 171799 886463 := bstep (se 1 (by rfl) ⟨664847, by rfl⟩ : syracuseStep 886463 = 1329695) B1329695
theorem B526057 : Blo 171799 526057 := bstep (se 2 (by rfl) ⟨197271, by rfl⟩ : syracuseStep 526057 = 394543) B394543
theorem B558839 : Blo 171799 558839 := bstep (se 1 (by rfl) ⟨419129, by rfl⟩ : syracuseStep 558839 = 838259) B838259
theorem B395027 : Blo 171799 395027 := bstep (se 1 (by rfl) ⟨296270, by rfl⟩ : syracuseStep 395027 = 592541) B592541
theorem B395387 : Blo 171799 395387 := bstep (se 1 (by rfl) ⟨296540, by rfl⟩ : syracuseStep 395387 = 593081) B593081
theorem B526475 : Blo 171799 526475 := bstep (se 1 (by rfl) ⟨394856, by rfl⟩ : syracuseStep 526475 = 789713) B789713
theorem B395495 : Blo 171799 395495 := bstep (se 1 (by rfl) ⟨296621, by rfl⟩ : syracuseStep 395495 = 593243) B593243
theorem B3967321 : Blo 171799 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B854687 : Blo 171799 854687 := bstep (se 1 (by rfl) ⟨641015, by rfl⟩ : syracuseStep 854687 = 1282031) B1282031
theorem B1051339 : Blo 171799 1051339 := bstep (se 1 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 1051339 = 1577009) B1577009
theorem B1706771 : Blo 171799 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B232679 : Blo 171799 232679 := bstep (se 1 (by rfl) ⟨174509, by rfl⟩ : syracuseStep 232679 = 349019) B349019
theorem B2101115 : Blo 171799 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B561505 : Blo 171799 561505 := bstep (se 2 (by rfl) ⟨210564, by rfl⟩ : syracuseStep 561505 = 421129) B421129
theorem B234031 : Blo 171799 234031 := bstep (se 1 (by rfl) ⟨175523, by rfl⟩ : syracuseStep 234031 = 351047) B351047
theorem B2005235 : Blo 171799 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B661841 : Blo 171799 661841 := bstep (se 2 (by rfl) ⟨248190, by rfl⟩ : syracuseStep 661841 = 496381) B496381
theorem B235879 : Blo 171799 235879 := bstep (se 1 (by rfl) ⟨176909, by rfl⟩ : syracuseStep 235879 = 353819) B353819
theorem B498089 : Blo 171799 498089 := bstep (se 2 (by rfl) ⟨186783, by rfl⟩ : syracuseStep 498089 = 373567) B373567
theorem B1972673 : Blo 171799 1972673 := bstep (se 2 (by rfl) ⟨739752, by rfl⟩ : syracuseStep 1972673 = 1479505) B1479505
theorem B8494753 : Blo 171799 8494753 := bstep (se 2 (by rfl) ⟨3185532, by rfl⟩ : syracuseStep 8494753 = 6371065) B6371065
theorem B171903 : Blo 171799 171903 := bstep (se 1 (by rfl) ⟨128927, by rfl⟩ : syracuseStep 171903 = 257855) B257855
theorem B172027 : Blo 171799 172027 := bstep (se 1 (by rfl) ⟨129020, by rfl⟩ : syracuseStep 172027 = 258041) B258041
theorem B172187 : Blo 171799 172187 := bstep (se 1 (by rfl) ⟨129140, by rfl⟩ : syracuseStep 172187 = 258281) B258281
theorem B172271 : Blo 171799 172271 := bstep (se 1 (by rfl) ⟨129203, by rfl⟩ : syracuseStep 172271 = 258407) B258407
theorem B172635 : Blo 171799 172635 := bstep (se 1 (by rfl) ⟨129476, by rfl⟩ : syracuseStep 172635 = 258953) B258953
theorem B4006567 : Blo 171799 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B172891 : Blo 171799 172891 := bstep (se 1 (by rfl) ⟨129668, by rfl⟩ : syracuseStep 172891 = 259337) B259337
theorem B435071 : Blo 171799 435071 := bstep (se 1 (by rfl) ⟨326303, by rfl⟩ : syracuseStep 435071 = 652607) B652607
theorem B172927 : Blo 171799 172927 := bstep (se 1 (by rfl) ⟨129695, by rfl⟩ : syracuseStep 172927 = 259391) B259391
theorem B369535 : Blo 171799 369535 := bstep (se 1 (by rfl) ⟨277151, by rfl⟩ : syracuseStep 369535 = 554303) B554303
theorem B992351 : Blo 171799 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B173211 : Blo 171799 173211 := bstep (se 1 (by rfl) ⟨129908, by rfl⟩ : syracuseStep 173211 = 259817) B259817
theorem B173215 : Blo 171799 173215 := bstep (se 1 (by rfl) ⟨129911, by rfl⟩ : syracuseStep 173215 = 259823) B259823
theorem B173519 : Blo 171799 173519 := bstep (se 1 (by rfl) ⟨130139, by rfl⟩ : syracuseStep 173519 = 260279) B260279
theorem B468463 : Blo 171799 468463 := bstep (se 1 (by rfl) ⟨351347, by rfl⟩ : syracuseStep 468463 = 702695) B702695
theorem B173551 : Blo 171799 173551 := bstep (se 1 (by rfl) ⟨130163, by rfl⟩ : syracuseStep 173551 = 260327) B260327
theorem B435739 : Blo 171799 435739 := bstep (se 1 (by rfl) ⟨326804, by rfl⟩ : syracuseStep 435739 = 653609) B653609
theorem B173799 : Blo 171799 173799 := bstep (se 1 (by rfl) ⟨130349, by rfl⟩ : syracuseStep 173799 = 260699) B260699
theorem B173895 : Blo 171799 173895 := bstep (se 1 (by rfl) ⟨130421, by rfl⟩ : syracuseStep 173895 = 260843) B260843
theorem B173915 : Blo 171799 173915 := bstep (se 1 (by rfl) ⟨130436, by rfl⟩ : syracuseStep 173915 = 260873) B260873
theorem B436367 : Blo 171799 436367 := bstep (se 1 (by rfl) ⟨327275, by rfl⟩ : syracuseStep 436367 = 654551) B654551
theorem B1681667 : Blo 171799 1681667 := bstep (se 1 (by rfl) ⟨1261250, by rfl⟩ : syracuseStep 1681667 = 2522501) B2522501
theorem B1485215 : Blo 171799 1485215 := bstep (se 1 (by rfl) ⟨1113911, by rfl⟩ : syracuseStep 1485215 = 2227823) B2227823
theorem B174495 : Blo 171799 174495 := bstep (se 1 (by rfl) ⟨130871, by rfl⟩ : syracuseStep 174495 = 261743) B261743
theorem B567739 : Blo 171799 567739 := bstep (se 1 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 567739 = 851609) B851609
theorem B174575 : Blo 171799 174575 := bstep (se 1 (by rfl) ⟨130931, by rfl⟩ : syracuseStep 174575 = 261863) B261863
theorem B174703 : Blo 171799 174703 := bstep (se 1 (by rfl) ⟨131027, by rfl⟩ : syracuseStep 174703 = 262055) B262055
theorem B174919 : Blo 171799 174919 := bstep (se 1 (by rfl) ⟨131189, by rfl⟩ : syracuseStep 174919 = 262379) B262379
theorem B2566991 : Blo 171799 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B174959 : Blo 171799 174959 := bstep (se 1 (by rfl) ⟨131219, by rfl⟩ : syracuseStep 174959 = 262439) B262439
theorem B666731 : Blo 171799 666731 := bstep (se 1 (by rfl) ⟨500048, by rfl⟩ : syracuseStep 666731 = 1000097) B1000097
theorem B175407 : Blo 171799 175407 := bstep (se 1 (by rfl) ⟨131555, by rfl⟩ : syracuseStep 175407 = 263111) B263111
theorem B175519 : Blo 171799 175519 := bstep (se 1 (by rfl) ⟨131639, by rfl⟩ : syracuseStep 175519 = 263279) B263279
theorem B175647 : Blo 171799 175647 := bstep (se 1 (by rfl) ⟨131735, by rfl⟩ : syracuseStep 175647 = 263471) B263471
theorem B175783 : Blo 171799 175783 := bstep (se 1 (by rfl) ⟨131837, by rfl⟩ : syracuseStep 175783 = 263675) B263675
theorem B175807 : Blo 171799 175807 := bstep (se 1 (by rfl) ⟨131855, by rfl⟩ : syracuseStep 175807 = 263711) B263711
theorem B2240399 : Blo 171799 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B275255 : Blo 171799 275255 := bstep (se 1 (by rfl) ⟨206441, by rfl⟩ : syracuseStep 275255 = 412883) B412883
theorem B669427 : Blo 171799 669427 := bstep (se 1 (by rfl) ⟨502070, by rfl⟩ : syracuseStep 669427 = 1004141) B1004141
theorem B997181 : Blo 171799 997181 := bstep (se 3 (by rfl) ⟨186971, by rfl⟩ : syracuseStep 997181 = 373943) B373943
theorem B440255 : Blo 171799 440255 := bstep (se 1 (by rfl) ⟨330191, by rfl⟩ : syracuseStep 440255 = 660383) B660383
theorem B1259867 : Blo 171799 1259867 := bstep (se 1 (by rfl) ⟨944900, by rfl⟩ : syracuseStep 1259867 = 1889801) B1889801
theorem B4864367 : Blo 171799 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B440873 : Blo 171799 440873 := bstep (se 2 (by rfl) ⟨165327, by rfl⟩ : syracuseStep 440873 = 330655) B330655
theorem B440923 : Blo 171799 440923 := bstep (se 1 (by rfl) ⟨330692, by rfl⟩ : syracuseStep 440923 = 661385) B661385
theorem B7945147 : Blo 171799 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B1981421 : Blo 171799 1981421 := bstep (se 3 (by rfl) ⟨371516, by rfl⟩ : syracuseStep 1981421 = 743033) B743033
theorem B278171 : Blo 171799 278171 := bstep (se 1 (by rfl) ⟨208628, by rfl⟩ : syracuseStep 278171 = 417257) B417257
theorem B442331 : Blo 171799 442331 := bstep (se 1 (by rfl) ⟨331748, by rfl⟩ : syracuseStep 442331 = 663497) B663497
theorem B442361 : Blo 171799 442361 := bstep (se 2 (by rfl) ⟨165885, by rfl⟩ : syracuseStep 442361 = 331771) B331771
theorem B2965571 : Blo 171799 2965571 := bstep (se 1 (by rfl) ⟨2224178, by rfl⟩ : syracuseStep 2965571 = 4448357) B4448357
theorem B6799625 : Blo 171799 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B738011 : Blo 171799 738011 := bstep (se 1 (by rfl) ⟨553508, by rfl⟩ : syracuseStep 738011 = 1107017) B1107017
theorem B672569 : Blo 171799 672569 := bstep (se 2 (by rfl) ⟨252213, by rfl⟩ : syracuseStep 672569 = 504427) B504427
theorem B2245913 : Blo 171799 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B870425 : Blo 171799 870425 := bstep (se 2 (by rfl) ⟨326409, by rfl⟩ : syracuseStep 870425 = 652819) B652819
theorem B247855 : Blo 171799 247855 := bstep (se 1 (by rfl) ⟨185891, by rfl⟩ : syracuseStep 247855 = 371783) B371783
theorem B444599 : Blo 171799 444599 := bstep (se 1 (by rfl) ⟨333449, by rfl⟩ : syracuseStep 444599 = 666899) B666899
theorem B870587 : Blo 171799 870587 := bstep (se 1 (by rfl) ⟨652940, by rfl⟩ : syracuseStep 870587 = 1305881) B1305881
theorem B1263995 : Blo 171799 1263995 := bstep (se 1 (by rfl) ⟨947996, by rfl⟩ : syracuseStep 1263995 = 1895993) B1895993
theorem B1264223 : Blo 171799 1264223 := bstep (se 1 (by rfl) ⟨948167, by rfl⟩ : syracuseStep 1264223 = 1896335) B1896335
theorem B248555 : Blo 171799 248555 := bstep (se 1 (by rfl) ⟨186416, by rfl⟩ : syracuseStep 248555 = 372833) B372833
theorem B2280311 : Blo 171799 2280311 := bstep (se 1 (by rfl) ⟨1710233, by rfl⟩ : syracuseStep 2280311 = 3420467) B3420467
theorem B248999 : Blo 171799 248999 := bstep (se 1 (by rfl) ⟨186749, by rfl⟩ : syracuseStep 248999 = 373499) B373499
theorem B2018533 : Blo 171799 2018533 := bstep (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) B378475
theorem B1068623 : Blo 171799 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B1494611 : Blo 171799 1494611 := bstep (se 1 (by rfl) ⟨1120958, by rfl⟩ : syracuseStep 1494611 = 2241917) B2241917
theorem B1134643 : Blo 171799 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B2969945 : Blo 171799 2969945 := bstep (se 2 (by rfl) ⟨1113729, by rfl⟩ : syracuseStep 2969945 = 2227459) B2227459
theorem B1397083 : Blo 171799 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B1331639 : Blo 171799 1331639 := bstep (se 1 (by rfl) ⟨998729, by rfl⟩ : syracuseStep 1331639 = 1997459) B1997459
theorem B3723731 : Blo 171799 3723731 := bstep (se 1 (by rfl) ⟨2792798, by rfl⟩ : syracuseStep 3723731 = 5585597) B5585597
theorem B873017 : Blo 171799 873017 := bstep (se 2 (by rfl) ⟨327381, by rfl⟩ : syracuseStep 873017 = 654763) B654763
theorem B1987361 : Blo 171799 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B873341 : Blo 171799 873341 := bstep (se 3 (by rfl) ⟨163751, by rfl⟩ : syracuseStep 873341 = 327503) B327503
theorem B874313 : Blo 171799 874313 := bstep (se 2 (by rfl) ⟨327867, by rfl⟩ : syracuseStep 874313 = 655735) B655735
theorem B2120579 : Blo 171799 2120579 := bstep (se 1 (by rfl) ⟨1590434, by rfl⟩ : syracuseStep 2120579 = 3180869) B3180869
theorem B875609 : Blo 171799 875609 := bstep (se 2 (by rfl) ⟨328353, by rfl⟩ : syracuseStep 875609 = 656707) B656707
theorem B580715 : Blo 171799 580715 := bstep (se 1 (by rfl) ⟨435536, by rfl⟩ : syracuseStep 580715 = 871073) B871073
theorem B810209 : Blo 171799 810209 := bstep (se 2 (by rfl) ⟨303828, by rfl⟩ : syracuseStep 810209 = 607657) B607657
theorem B220411 : Blo 171799 220411 := bstep (se 1 (by rfl) ⟨165308, by rfl⟩ : syracuseStep 220411 = 330617) B330617
theorem B2252063 : Blo 171799 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B876095 : Blo 171799 876095 := bstep (se 1 (by rfl) ⟨657071, by rfl⟩ : syracuseStep 876095 = 1314143) B1314143
theorem B221287 : Blo 171799 221287 := bstep (se 1 (by rfl) ⟨165965, by rfl⟩ : syracuseStep 221287 = 331931) B331931
theorem B1139321 : Blo 171799 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B35971913 : Blo 171799 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B418871 : Blo 171799 418871 := bstep (se 1 (by rfl) ⟨314153, by rfl⟩ : syracuseStep 418871 = 628307) B628307
theorem B582767 : Blo 171799 582767 := bstep (se 1 (by rfl) ⟨437075, by rfl⟩ : syracuseStep 582767 = 874151) B874151
theorem B1894387 : Blo 171799 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B584009 : Blo 171799 584009 := bstep (se 2 (by rfl) ⟨219003, by rfl⟩ : syracuseStep 584009 = 438007) B438007
theorem B584171 : Blo 171799 584171 := bstep (se 1 (by rfl) ⟨438128, by rfl⟩ : syracuseStep 584171 = 876257) B876257
theorem B748187 : Blo 171799 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B1076141 : Blo 171799 1076141 := bstep (se 3 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 1076141 = 403553) B403553
theorem B224251 : Blo 171799 224251 := bstep (se 1 (by rfl) ⟨168188, by rfl⟩ : syracuseStep 224251 = 336377) B336377
theorem B290027 : Blo 171799 290027 := bstep (se 1 (by rfl) ⟨217520, by rfl⟩ : syracuseStep 290027 = 435041) B435041
theorem B3731159 : Blo 171799 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B388961 : Blo 171799 388961 := bstep (se 2 (by rfl) ⟨145860, by rfl⟩ : syracuseStep 388961 = 291721) B291721
theorem B552919 : Blo 171799 552919 := bstep (se 1 (by rfl) ⟨414689, by rfl⟩ : syracuseStep 552919 = 829379) B829379
theorem B258023 : Blo 171799 258023 := bstep (se 1 (by rfl) ⟨193517, by rfl⟩ : syracuseStep 258023 = 387035) B387035
theorem B258143 : Blo 171799 258143 := bstep (se 1 (by rfl) ⟨193607, by rfl⟩ : syracuseStep 258143 = 387215) B387215
theorem B1241183 : Blo 171799 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B258203 : Blo 171799 258203 := bstep (se 1 (by rfl) ⟨193652, by rfl⟩ : syracuseStep 258203 = 387305) B387305
theorem B258383 : Blo 171799 258383 := bstep (se 1 (by rfl) ⟨193787, by rfl⟩ : syracuseStep 258383 = 387575) B387575
theorem B1929635 : Blo 171799 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B258473 : Blo 171799 258473 := bstep (se 2 (by rfl) ⟨96927, by rfl⟩ : syracuseStep 258473 = 193855) B193855
theorem B651689 : Blo 171799 651689 := bstep (se 2 (by rfl) ⟨244383, by rfl⟩ : syracuseStep 651689 = 488767) B488767
theorem B258779 : Blo 171799 258779 := bstep (se 1 (by rfl) ⟨194084, by rfl⟩ : syracuseStep 258779 = 388169) B388169
theorem B389915 : Blo 171799 389915 := bstep (se 1 (by rfl) ⟨292436, by rfl⟩ : syracuseStep 389915 = 584873) B584873
theorem B586601 : Blo 171799 586601 := bstep (se 2 (by rfl) ⟨219975, by rfl⟩ : syracuseStep 586601 = 439951) B439951
theorem B979937 : Blo 171799 979937 := bstep (se 2 (by rfl) ⟨367476, by rfl⟩ : syracuseStep 979937 = 734953) B734953
theorem B390113 : Blo 171799 390113 := bstep (se 2 (by rfl) ⟨146292, by rfl⟩ : syracuseStep 390113 = 292585) B292585
theorem B259049 : Blo 171799 259049 := bstep (se 2 (by rfl) ⟨97143, by rfl⟩ : syracuseStep 259049 = 194287) B194287
theorem B259193 : Blo 171799 259193 := bstep (se 2 (by rfl) ⟨97197, by rfl⟩ : syracuseStep 259193 = 194395) B194395
theorem B390311 : Blo 171799 390311 := bstep (se 1 (by rfl) ⟨292733, by rfl⟩ : syracuseStep 390311 = 585467) B585467
theorem B881927 : Blo 171799 881927 := bstep (se 1 (by rfl) ⟨661445, by rfl⟩ : syracuseStep 881927 = 1322891) B1322891
theorem B259721 : Blo 171799 259721 := bstep (se 2 (by rfl) ⟨97395, by rfl⟩ : syracuseStep 259721 = 194791) B194791
theorem B259931 : Blo 171799 259931 := bstep (se 1 (by rfl) ⟨194948, by rfl⟩ : syracuseStep 259931 = 389897) B389897
theorem B194431 : Blo 171799 194431 := bstep (se 1 (by rfl) ⟨145823, by rfl⟩ : syracuseStep 194431 = 291647) B291647
theorem B259967 : Blo 171799 259967 := bstep (se 1 (by rfl) ⟨194975, by rfl⟩ : syracuseStep 259967 = 389951) B389951
theorem B260063 : Blo 171799 260063 := bstep (se 1 (by rfl) ⟨195047, by rfl⟩ : syracuseStep 260063 = 390095) B390095
theorem B260123 : Blo 171799 260123 := bstep (se 1 (by rfl) ⟨195092, by rfl⟩ : syracuseStep 260123 = 390185) B390185
theorem B260315 : Blo 171799 260315 := bstep (se 1 (by rfl) ⟨195236, by rfl⟩ : syracuseStep 260315 = 390473) B390473
theorem B1898795 : Blo 171799 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B391481 : Blo 171799 391481 := bstep (se 2 (by rfl) ⟨146805, by rfl⟩ : syracuseStep 391481 = 293611) B293611
theorem B260585 : Blo 171799 260585 := bstep (se 2 (by rfl) ⟨97719, by rfl⟩ : syracuseStep 260585 = 195439) B195439
theorem B588599 : Blo 171799 588599 := bstep (se 1 (by rfl) ⟨441449, by rfl⟩ : syracuseStep 588599 = 882899) B882899
theorem B260975 : Blo 171799 260975 := bstep (se 1 (by rfl) ⟨195731, by rfl⟩ : syracuseStep 260975 = 391463) B391463
theorem B555943 : Blo 171799 555943 := bstep (se 1 (by rfl) ⟨416957, by rfl⟩ : syracuseStep 555943 = 833915) B833915
theorem B326683 : Blo 171799 326683 := bstep (se 1 (by rfl) ⟨245012, by rfl⟩ : syracuseStep 326683 = 490025) B490025
theorem B1113115 : Blo 171799 1113115 := bstep (se 1 (by rfl) ⟨834836, by rfl⟩ : syracuseStep 1113115 = 1669673) B1669673
theorem B392219 : Blo 171799 392219 := bstep (se 1 (by rfl) ⟨294164, by rfl⟩ : syracuseStep 392219 = 588329) B588329
theorem B261215 : Blo 171799 261215 := bstep (se 1 (by rfl) ⟨195911, by rfl⟩ : syracuseStep 261215 = 391823) B391823
theorem B523361 : Blo 171799 523361 := bstep (se 2 (by rfl) ⟨196260, by rfl⟩ : syracuseStep 523361 = 392521) B392521
theorem B261275 : Blo 171799 261275 := bstep (se 1 (by rfl) ⟨195956, by rfl⟩ : syracuseStep 261275 = 391913) B391913
theorem B294043 : Blo 171799 294043 := bstep (se 1 (by rfl) ⟨220532, by rfl⟩ : syracuseStep 294043 = 441065) B441065
theorem B261431 : Blo 171799 261431 := bstep (se 1 (by rfl) ⟨196073, by rfl⟩ : syracuseStep 261431 = 392147) B392147
theorem B1113425 : Blo 171799 1113425 := bstep (se 2 (by rfl) ⟨417534, by rfl⟩ : syracuseStep 1113425 = 835069) B835069
theorem B2096549 : Blo 171799 2096549 := bstep (se 4 (by rfl) ⟨196551, by rfl⟩ : syracuseStep 2096549 = 393103) B393103
theorem B261611 : Blo 171799 261611 := bstep (se 1 (by rfl) ⟨196208, by rfl⟩ : syracuseStep 261611 = 392417) B392417
theorem B261815 : Blo 171799 261815 := bstep (se 1 (by rfl) ⟨196361, by rfl⟩ : syracuseStep 261815 = 392723) B392723
theorem B589679 : Blo 171799 589679 := bstep (se 1 (by rfl) ⟨442259, by rfl⟩ : syracuseStep 589679 = 884519) B884519
theorem B262025 : Blo 171799 262025 := bstep (se 2 (by rfl) ⟨98259, by rfl⟩ : syracuseStep 262025 = 196519) B196519
theorem B295049 : Blo 171799 295049 := bstep (se 2 (by rfl) ⟨110643, by rfl⟩ : syracuseStep 295049 = 221287) B221287
theorem B262313 : Blo 171799 262313 := bstep (se 2 (by rfl) ⟨98367, by rfl⟩ : syracuseStep 262313 = 196735) B196735
theorem B3309821 : Blo 171799 3309821 := bstep (se 3 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 3309821 = 1241183) B1241183
theorem B262523 : Blo 171799 262523 := bstep (se 1 (by rfl) ⟨196892, by rfl⟩ : syracuseStep 262523 = 393785) B393785
theorem B492007 : Blo 171799 492007 := bstep (se 1 (by rfl) ⟨369005, by rfl⟩ : syracuseStep 492007 = 738011) B738011
theorem B262697 : Blo 171799 262697 := bstep (se 2 (by rfl) ⟨98511, by rfl⟩ : syracuseStep 262697 = 197023) B197023
theorem B197167 : Blo 171799 197167 := bstep (se 1 (by rfl) ⟨147875, by rfl⟩ : syracuseStep 197167 = 295751) B295751
theorem B656039 : Blo 171799 656039 := bstep (se 1 (by rfl) ⟨492029, by rfl⟩ : syracuseStep 656039 = 984059) B984059
theorem B1180457 : Blo 171799 1180457 := bstep (se 2 (by rfl) ⟨442671, by rfl⟩ : syracuseStep 1180457 = 885343) B885343
theorem B394055 : Blo 171799 394055 := bstep (se 1 (by rfl) ⟨295541, by rfl⟩ : syracuseStep 394055 = 591083) B591083
theorem B263003 : Blo 171799 263003 := bstep (se 1 (by rfl) ⟨197252, by rfl⟩ : syracuseStep 263003 = 394505) B394505
theorem B12059603 : Blo 171799 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B590975 : Blo 171799 590975 := bstep (se 1 (by rfl) ⟨443231, by rfl⟩ : syracuseStep 590975 = 886463) B886463
theorem B492713 : Blo 171799 492713 := bstep (se 2 (by rfl) ⟨184767, by rfl⟩ : syracuseStep 492713 = 369535) B369535
theorem B263351 : Blo 171799 263351 := bstep (se 1 (by rfl) ⟨197513, by rfl⟩ : syracuseStep 263351 = 395027) B395027
theorem B263591 : Blo 171799 263591 := bstep (se 1 (by rfl) ⟨197693, by rfl⟩ : syracuseStep 263591 = 395387) B395387
theorem B296399 : Blo 171799 296399 := bstep (se 1 (by rfl) ⟨222299, by rfl⟩ : syracuseStep 296399 = 444599) B444599
theorem B263663 : Blo 171799 263663 := bstep (se 1 (by rfl) ⟨197747, by rfl⟩ : syracuseStep 263663 = 395495) B395495
theorem B624617 : Blo 171799 624617 := bstep (se 2 (by rfl) ⟨234231, by rfl⟩ : syracuseStep 624617 = 468463) B468463
theorem B2525849 : Blo 171799 2525849 := bstep (se 2 (by rfl) ⟨947193, by rfl⟩ : syracuseStep 2525849 = 1894387) B1894387
theorem B330473 : Blo 171799 330473 := bstep (se 2 (by rfl) ⟨123927, by rfl⟩ : syracuseStep 330473 = 247855) B247855
theorem B1116989 : Blo 171799 1116989 := bstep (se 3 (by rfl) ⟨209435, by rfl⟩ : syracuseStep 1116989 = 418871) B418871
theorem B887759 : Blo 171799 887759 := bstep (se 1 (by rfl) ⟨665819, by rfl⟩ : syracuseStep 887759 = 1331639) B1331639
theorem B756985 : Blo 171799 756985 := bstep (se 2 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 756985 = 567739) B567739
theorem B21368357 : Blo 171799 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B1315115 : Blo 171799 1315115 := bstep (se 1 (by rfl) ⟨986336, by rfl⟩ : syracuseStep 1315115 = 1972673) B1972673
theorem B2691377 : Blo 171799 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B6951349 : Blo 171799 6951349 := bstep (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) B651689
theorem B1413719 : Blo 171799 1413719 := bstep (se 1 (by rfl) ⟨1060289, by rfl⟩ : syracuseStep 1413719 = 2120579) B2120579
theorem B234409 : Blo 171799 234409 := bstep (se 2 (by rfl) ⟨87903, by rfl⟩ : syracuseStep 234409 = 175807) B175807
theorem B42374117 : Blo 171799 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B1512857 : Blo 171799 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B759547 : Blo 171799 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B661567 : Blo 171799 661567 := bstep (se 1 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 661567 = 992351) B992351
theorem B1121111 : Blo 171799 1121111 := bstep (se 1 (by rfl) ⟨840833, by rfl⟩ : syracuseStep 1121111 = 1681667) B1681667
theorem B990143 : Blo 171799 990143 := bstep (se 1 (by rfl) ⟨742607, by rfl⟩ : syracuseStep 990143 = 1485215) B1485215
theorem B498791 : Blo 171799 498791 := bstep (se 1 (by rfl) ⟨374093, by rfl⟩ : syracuseStep 498791 = 748187) B748187
theorem B662813 : Blo 171799 662813 := bstep (se 3 (by rfl) ⟨124277, by rfl⟩ : syracuseStep 662813 = 248555) B248555
theorem B172015 : Blo 171799 172015 := bstep (se 1 (by rfl) ⟨129011, by rfl⟩ : syracuseStep 172015 = 258023) B258023
theorem B172095 : Blo 171799 172095 := bstep (se 1 (by rfl) ⟨129071, by rfl⟩ : syracuseStep 172095 = 258143) B258143
theorem B172135 : Blo 171799 172135 := bstep (se 1 (by rfl) ⟨129101, by rfl⟩ : syracuseStep 172135 = 258203) B258203
theorem B172255 : Blo 171799 172255 := bstep (se 1 (by rfl) ⟨129191, by rfl⟩ : syracuseStep 172255 = 258383) B258383
theorem B1286423 : Blo 171799 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B172315 : Blo 171799 172315 := bstep (se 1 (by rfl) ⟨129236, by rfl⟩ : syracuseStep 172315 = 258473) B258473
theorem B663997 : Blo 171799 663997 := bstep (se 3 (by rfl) ⟨124499, by rfl⟩ : syracuseStep 663997 = 248999) B248999
theorem B172519 : Blo 171799 172519 := bstep (se 1 (by rfl) ⟨129389, by rfl⟩ : syracuseStep 172519 = 258779) B258779
theorem B172699 : Blo 171799 172699 := bstep (se 1 (by rfl) ⟨129524, by rfl⟩ : syracuseStep 172699 = 259049) B259049
theorem B172795 : Blo 171799 172795 := bstep (se 1 (by rfl) ⟨129596, by rfl⟩ : syracuseStep 172795 = 259193) B259193
theorem B173147 : Blo 171799 173147 := bstep (se 1 (by rfl) ⟨129860, by rfl⟩ : syracuseStep 173147 = 259721) B259721
theorem B664787 : Blo 171799 664787 := bstep (se 1 (by rfl) ⟨498590, by rfl⟩ : syracuseStep 664787 = 997181) B997181
theorem B173287 : Blo 171799 173287 := bstep (se 1 (by rfl) ⟨129965, by rfl⟩ : syracuseStep 173287 = 259931) B259931
theorem B173311 : Blo 171799 173311 := bstep (se 1 (by rfl) ⟨129983, by rfl⟩ : syracuseStep 173311 = 259967) B259967
theorem B173375 : Blo 171799 173375 := bstep (se 1 (by rfl) ⟨130031, by rfl⟩ : syracuseStep 173375 = 260063) B260063
theorem B173415 : Blo 171799 173415 := bstep (se 1 (by rfl) ⟨130061, by rfl⟩ : syracuseStep 173415 = 260123) B260123
theorem B435577 : Blo 171799 435577 := bstep (se 2 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 435577 = 326683) B326683
theorem B1484153 : Blo 171799 1484153 := bstep (se 2 (by rfl) ⟨556557, by rfl⟩ : syracuseStep 1484153 = 1113115) B1113115
theorem B173543 : Blo 171799 173543 := bstep (se 1 (by rfl) ⟨130157, by rfl⟩ : syracuseStep 173543 = 260315) B260315
theorem B173723 : Blo 171799 173723 := bstep (se 1 (by rfl) ⟨130292, by rfl⟩ : syracuseStep 173723 = 260585) B260585
theorem B173983 : Blo 171799 173983 := bstep (se 1 (by rfl) ⟨130487, by rfl⟩ : syracuseStep 173983 = 260975) B260975
theorem B1320947 : Blo 171799 1320947 := bstep (se 1 (by rfl) ⟨990710, by rfl⟩ : syracuseStep 1320947 = 1981421) B1981421
theorem B174143 : Blo 171799 174143 := bstep (se 1 (by rfl) ⟨130607, by rfl⟩ : syracuseStep 174143 = 261215) B261215
theorem B174183 : Blo 171799 174183 := bstep (se 1 (by rfl) ⟨130637, by rfl⟩ : syracuseStep 174183 = 261275) B261275
theorem B174287 : Blo 171799 174287 := bstep (se 1 (by rfl) ⟨130715, by rfl⟩ : syracuseStep 174287 = 261431) B261431
theorem B174407 : Blo 171799 174407 := bstep (se 1 (by rfl) ⟨130805, by rfl⟩ : syracuseStep 174407 = 261611) B261611
theorem B174543 : Blo 171799 174543 := bstep (se 1 (by rfl) ⟨130907, by rfl⟩ : syracuseStep 174543 = 261815) B261815
theorem B174683 : Blo 171799 174683 := bstep (se 1 (by rfl) ⟨131012, by rfl⟩ : syracuseStep 174683 = 262025) B262025
theorem B1977047 : Blo 171799 1977047 := bstep (se 1 (by rfl) ⟨1482785, by rfl⟩ : syracuseStep 1977047 = 2965571) B2965571
theorem B174847 : Blo 171799 174847 := bstep (se 1 (by rfl) ⟨131135, by rfl⟩ : syracuseStep 174847 = 262271) B262271
theorem B4533083 : Blo 171799 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B175039 : Blo 171799 175039 := bstep (se 1 (by rfl) ⟨131279, by rfl⟩ : syracuseStep 175039 = 262559) B262559
theorem B175215 : Blo 171799 175215 := bstep (se 1 (by rfl) ⟨131411, by rfl⟩ : syracuseStep 175215 = 262823) B262823
theorem B175295 : Blo 171799 175295 := bstep (se 1 (by rfl) ⟨131471, by rfl⟩ : syracuseStep 175295 = 262943) B262943
theorem B175311 : Blo 171799 175311 := bstep (se 1 (by rfl) ⟨131483, by rfl⟩ : syracuseStep 175311 = 262967) B262967
theorem B175431 : Blo 171799 175431 := bstep (se 1 (by rfl) ⟨131573, by rfl⟩ : syracuseStep 175431 = 263147) B263147
theorem B175771 : Blo 171799 175771 := bstep (se 1 (by rfl) ⟨131828, by rfl⟩ : syracuseStep 175771 = 263657) B263657
theorem B569791 : Blo 171799 569791 := bstep (se 1 (by rfl) ⟨427343, by rfl⟩ : syracuseStep 569791 = 854687) B854687
theorem B1258021 : Blo 171799 1258021 := bstep (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) B235879
theorem B1520207 : Blo 171799 1520207 := bstep (se 1 (by rfl) ⟨1140155, by rfl⟩ : syracuseStep 1520207 = 2280311) B2280311
theorem B996407 : Blo 171799 996407 := bstep (se 1 (by rfl) ⟨747305, by rfl⟩ : syracuseStep 996407 = 1494611) B1494611
theorem B1979963 : Blo 171799 1979963 := bstep (se 1 (by rfl) ⟨1484972, by rfl⟩ : syracuseStep 1979963 = 2969945) B2969945
theorem B5289761 : Blo 171799 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B1324907 : Blo 171799 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B441227 : Blo 171799 441227 := bstep (se 1 (by rfl) ⟨330920, by rfl⟩ : syracuseStep 441227 = 661841) B661841
theorem B1490237 : Blo 171799 1490237 := bstep (se 3 (by rfl) ⟨279419, by rfl⟩ : syracuseStep 1490237 = 558839) B558839
theorem B737225 : Blo 171799 737225 := bstep (se 2 (by rfl) ⟨276459, by rfl⟩ : syracuseStep 737225 = 552919) B552919
theorem B1196005 : Blo 171799 1196005 := bstep (se 4 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 1196005 = 224251) B224251
theorem B312041 : Blo 171799 312041 := bstep (se 2 (by rfl) ⟨117015, by rfl⟩ : syracuseStep 312041 = 234031) B234031
theorem B1328237 : Blo 171799 1328237 := bstep (se 3 (by rfl) ⟨249044, by rfl⟩ : syracuseStep 1328237 = 498089) B498089
theorem B444487 : Blo 171799 444487 := bstep (se 1 (by rfl) ⟨333365, by rfl⟩ : syracuseStep 444487 = 666731) B666731
theorem B1493599 : Blo 171799 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B183503 : Blo 171799 183503 := bstep (se 1 (by rfl) ⟨137627, by rfl⟩ : syracuseStep 183503 = 275255) B275255
theorem B2805637 : Blo 171799 2805637 := bstep (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) B526057
theorem B741257 : Blo 171799 741257 := bstep (se 2 (by rfl) ⟨277971, by rfl⟩ : syracuseStep 741257 = 555943) B555943
theorem B1265863 : Blo 171799 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B839911 : Blo 171799 839911 := bstep (se 1 (by rfl) ⟨629933, by rfl⟩ : syracuseStep 839911 = 1259867) B1259867
theorem B348907 : Blo 171799 348907 := bstep (se 1 (by rfl) ⟨261680, by rfl⟩ : syracuseStep 348907 = 523361) B523361
theorem B11326337 : Blo 171799 11326337 := bstep (se 2 (by rfl) ⟨4247376, by rfl⟩ : syracuseStep 11326337 = 8494753) B8494753
theorem B742283 : Blo 171799 742283 := bstep (se 1 (by rfl) ⟨556712, by rfl⟩ : syracuseStep 742283 = 1113425) B1113425
theorem B1397699 : Blo 171799 1397699 := bstep (se 1 (by rfl) ⟨1048274, by rfl⟩ : syracuseStep 1397699 = 2096549) B2096549
theorem B185447 : Blo 171799 185447 := bstep (se 1 (by rfl) ⟨139085, by rfl⟩ : syracuseStep 185447 = 278171) B278171
theorem B1398383 : Blo 171799 1398383 := bstep (se 1 (by rfl) ⟨1048787, by rfl⟩ : syracuseStep 1398383 = 2097575) B2097575
theorem B448379 : Blo 171799 448379 := bstep (se 1 (by rfl) ⟨336284, by rfl⟩ : syracuseStep 448379 = 672569) B672569
theorem B1497275 : Blo 171799 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B580283 : Blo 171799 580283 := bstep (se 1 (by rfl) ⟨435212, by rfl⟩ : syracuseStep 580283 = 870425) B870425
theorem B350983 : Blo 171799 350983 := bstep (se 1 (by rfl) ⟨263237, by rfl⟩ : syracuseStep 350983 = 526475) B526475
theorem B580391 : Blo 171799 580391 := bstep (se 1 (by rfl) ⟨435293, by rfl⟩ : syracuseStep 580391 = 870587) B870587
theorem B842663 : Blo 171799 842663 := bstep (se 1 (by rfl) ⟨631997, by rfl⟩ : syracuseStep 842663 = 1263995) B1263995
theorem B842815 : Blo 171799 842815 := bstep (se 1 (by rfl) ⟨632111, by rfl⟩ : syracuseStep 842815 = 1264223) B1264223
theorem B580985 : Blo 171799 580985 := bstep (se 2 (by rfl) ⟨217869, by rfl⟩ : syracuseStep 580985 = 435739) B435739
theorem B712415 : Blo 171799 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B1400743 : Blo 171799 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B2482487 : Blo 171799 2482487 := bstep (se 1 (by rfl) ⟨1861865, by rfl⟩ : syracuseStep 2482487 = 3723731) B3723731
theorem B582011 : Blo 171799 582011 := bstep (se 1 (by rfl) ⟨436508, by rfl⟩ : syracuseStep 582011 = 873017) B873017
theorem B582227 : Blo 171799 582227 := bstep (se 1 (by rfl) ⟨436670, by rfl⟩ : syracuseStep 582227 = 873341) B873341
theorem B1401785 : Blo 171799 1401785 := bstep (se 2 (by rfl) ⟨525669, by rfl⟩ : syracuseStep 1401785 = 1051339) B1051339
theorem B582875 : Blo 171799 582875 := bstep (se 1 (by rfl) ⟨437156, by rfl⟩ : syracuseStep 582875 = 874313) B874313
theorem B1336823 : Blo 171799 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B583739 : Blo 171799 583739 := bstep (se 1 (by rfl) ⟨437804, by rfl⟩ : syracuseStep 583739 = 875609) B875609
theorem B387143 : Blo 171799 387143 := bstep (se 1 (by rfl) ⟨290357, by rfl⟩ : syracuseStep 387143 = 580715) B580715
theorem B1501375 : Blo 171799 1501375 := bstep (se 1 (by rfl) ⟨1126031, by rfl⟩ : syracuseStep 1501375 = 2252063) B2252063
theorem B584063 : Blo 171799 584063 := bstep (se 1 (by rfl) ⟨438047, by rfl⟩ : syracuseStep 584063 = 876095) B876095
theorem B1862777 : Blo 171799 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B748673 : Blo 171799 748673 := bstep (se 2 (by rfl) ⟨280752, by rfl⟩ : syracuseStep 748673 = 561505) B561505
theorem B23981275 : Blo 171799 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B290047 : Blo 171799 290047 := bstep (se 1 (by rfl) ⟨217535, by rfl⟩ : syracuseStep 290047 = 435071) B435071
theorem B388511 : Blo 171799 388511 := bstep (se 1 (by rfl) ⟨291383, by rfl⟩ : syracuseStep 388511 = 582767) B582767
theorem B290911 : Blo 171799 290911 := bstep (se 1 (by rfl) ⟨218183, by rfl⟩ : syracuseStep 290911 = 436367) B436367
theorem B389339 : Blo 171799 389339 := bstep (se 1 (by rfl) ⟨292004, by rfl⟩ : syracuseStep 389339 = 584009) B584009
theorem B389447 : Blo 171799 389447 := bstep (se 1 (by rfl) ⟨292085, by rfl⟩ : syracuseStep 389447 = 584171) B584171
theorem B717427 : Blo 171799 717427 := bstep (se 1 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 717427 = 1076141) B1076141
theorem B4551389 : Blo 171799 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B193351 : Blo 171799 193351 := bstep (se 1 (by rfl) ⟨145013, by rfl⟩ : syracuseStep 193351 = 290027) B290027
theorem B6845309 : Blo 171799 6845309 := bstep (se 3 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 6845309 = 2566991) B2566991
theorem B2487439 : Blo 171799 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B259241 : Blo 171799 259241 := bstep (se 2 (by rfl) ⟨97215, by rfl⟩ : syracuseStep 259241 = 194431) B194431
theorem B259307 : Blo 171799 259307 := bstep (se 1 (by rfl) ⟨194480, by rfl⟩ : syracuseStep 259307 = 388961) B388961
theorem B259943 : Blo 171799 259943 := bstep (se 1 (by rfl) ⟨194957, by rfl⟩ : syracuseStep 259943 = 389915) B389915
theorem B391067 : Blo 171799 391067 := bstep (se 1 (by rfl) ⟨293300, by rfl⟩ : syracuseStep 391067 = 586601) B586601
theorem B2160557 : Blo 171799 2160557 := bstep (se 3 (by rfl) ⟨405104, by rfl⟩ : syracuseStep 2160557 = 810209) B810209
theorem B620477 : Blo 171799 620477 := bstep (se 3 (by rfl) ⟨116339, by rfl⟩ : syracuseStep 620477 = 232679) B232679
theorem B653291 : Blo 171799 653291 := bstep (se 1 (by rfl) ⟨489968, by rfl⟩ : syracuseStep 653291 = 979937) B979937
theorem B260075 : Blo 171799 260075 := bstep (se 1 (by rfl) ⟨195056, by rfl⟩ : syracuseStep 260075 = 390113) B390113
theorem B260207 : Blo 171799 260207 := bstep (se 1 (by rfl) ⟨195155, by rfl⟩ : syracuseStep 260207 = 390311) B390311
theorem B587897 : Blo 171799 587897 := bstep (se 2 (by rfl) ⟨220461, by rfl⟩ : syracuseStep 587897 = 440923) B440923
theorem B587951 : Blo 171799 587951 := bstep (se 1 (by rfl) ⟨440963, by rfl⟩ : syracuseStep 587951 = 881927) B881927
theorem B3570277 : Blo 171799 3570277 := bstep (se 4 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 3570277 = 669427) B669427
theorem B293503 : Blo 171799 293503 := bstep (se 1 (by rfl) ⟨220127, by rfl⟩ : syracuseStep 293503 = 440255) B440255
theorem B392057 : Blo 171799 392057 := bstep (se 2 (by rfl) ⟨147021, by rfl⟩ : syracuseStep 392057 = 294043) B294043
theorem B260987 : Blo 171799 260987 := bstep (se 1 (by rfl) ⟨195740, by rfl⟩ : syracuseStep 260987 = 391481) B391481
theorem B3242911 : Blo 171799 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B293881 : Blo 171799 293881 := bstep (se 2 (by rfl) ⟨110205, by rfl⟩ : syracuseStep 293881 = 220411) B220411
theorem B293915 : Blo 171799 293915 := bstep (se 1 (by rfl) ⟨220436, by rfl⟩ : syracuseStep 293915 = 440873) B440873
theorem B392399 : Blo 171799 392399 := bstep (se 1 (by rfl) ⟨294299, by rfl⟩ : syracuseStep 392399 = 588599) B588599
theorem B261479 : Blo 171799 261479 := bstep (se 1 (by rfl) ⟨196109, by rfl⟩ : syracuseStep 261479 = 392219) B392219
theorem B393119 : Blo 171799 393119 := bstep (se 1 (by rfl) ⟨294839, by rfl⟩ : syracuseStep 393119 = 589679) B589679
theorem B294887 : Blo 171799 294887 := bstep (se 1 (by rfl) ⟨221165, by rfl⟩ : syracuseStep 294887 = 442331) B442331
theorem B294907 : Blo 171799 294907 := bstep (se 1 (by rfl) ⟨221180, by rfl⟩ : syracuseStep 294907 = 442361) B442361
theorem B196699 : Blo 171799 196699 := bstep (se 1 (by rfl) ⟨147524, by rfl⟩ : syracuseStep 196699 = 295049) B295049
theorem B786971 : Blo 171799 786971 := bstep (se 1 (by rfl) ⟨590228, by rfl⟩ : syracuseStep 786971 = 1180457) B1180457
theorem B262703 : Blo 171799 262703 := bstep (se 1 (by rfl) ⟨197027, by rfl⟩ : syracuseStep 262703 = 394055) B394055
theorem B885329 : Blo 171799 885329 := bstep (se 2 (by rfl) ⟨331998, by rfl⟩ : syracuseStep 885329 = 663997) B663997
theorem B656009 : Blo 171799 656009 := bstep (se 2 (by rfl) ⟨246003, by rfl⟩ : syracuseStep 656009 = 492007) B492007
theorem B262889 : Blo 171799 262889 := bstep (se 2 (by rfl) ⟨98583, by rfl⟩ : syracuseStep 262889 = 197167) B197167
theorem B885491 : Blo 171799 885491 := bstep (se 1 (by rfl) ⟨664118, by rfl⟩ : syracuseStep 885491 = 1328237) B1328237
theorem B393983 : Blo 171799 393983 := bstep (se 1 (by rfl) ⟨295487, by rfl⟩ : syracuseStep 393983 = 590975) B590975
theorem B328475 : Blo 171799 328475 := bstep (se 1 (by rfl) ⟨246356, by rfl⟩ : syracuseStep 328475 = 492713) B492713
theorem B54887381 : Blo 171799 54887381 := bstep (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) B1286423
theorem B197599 : Blo 171799 197599 := bstep (se 1 (by rfl) ⟨148199, by rfl⟩ : syracuseStep 197599 = 296399) B296399
theorem B591839 : Blo 171799 591839 := bstep (se 1 (by rfl) ⟨443879, by rfl⟩ : syracuseStep 591839 = 887759) B887759
theorem B494171 : Blo 171799 494171 := bstep (se 1 (by rfl) ⟨370628, by rfl⟩ : syracuseStep 494171 = 741257) B741257
theorem B592649 : Blo 171799 592649 := bstep (se 2 (by rfl) ⟨222243, by rfl⟩ : syracuseStep 592649 = 444487) B444487
theorem B2001833 : Blo 171799 2001833 := bstep (se 2 (by rfl) ⟨750687, by rfl⟩ : syracuseStep 2001833 = 1501375) B1501375
theorem B494525 : Blo 171799 494525 := bstep (se 3 (by rfl) ⟨92723, by rfl⟩ : syracuseStep 494525 = 185447) B185447
theorem B494855 : Blo 171799 494855 := bstep (se 1 (by rfl) ⟨371141, by rfl⟩ : syracuseStep 494855 = 742283) B742283
theorem B28249411 : Blo 171799 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B4034285 : Blo 171799 4034285 := bstep (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) B1512857
theorem B298919 : Blo 171799 298919 := bstep (se 1 (by rfl) ⟨224189, by rfl⟩ : syracuseStep 298919 = 448379) B448379
theorem B561775 : Blo 171799 561775 := bstep (se 1 (by rfl) ⟨421331, by rfl⟩ : syracuseStep 561775 = 842663) B842663
theorem B660095 : Blo 171799 660095 := bstep (se 1 (by rfl) ⟨495071, by rfl⟩ : syracuseStep 660095 = 990143) B990143
theorem B332527 : Blo 171799 332527 := bstep (se 1 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 332527 = 498791) B498791
theorem B3740849 : Blo 171799 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B1119881 : Blo 171799 1119881 := bstep (se 2 (by rfl) ⟨419955, by rfl⟩ : syracuseStep 1119881 = 839911) B839911
theorem B759721 : Blo 171799 759721 := bstep (se 2 (by rfl) ⟨284895, by rfl⟩ : syracuseStep 759721 = 569791) B569791
theorem B1677361 : Blo 171799 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B956569 : Blo 171799 956569 := bstep (se 2 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 956569 = 717427) B717427
theorem B989435 : Blo 171799 989435 := bstep (se 1 (by rfl) ⟨742076, by rfl⟩ : syracuseStep 989435 = 1484153) B1484153
theorem B465209 : Blo 171799 465209 := bstep (se 2 (by rfl) ⟨174453, by rfl⟩ : syracuseStep 465209 = 348907) B348907
theorem B891215 : Blo 171799 891215 := bstep (se 1 (by rfl) ⟨668411, by rfl⟩ : syracuseStep 891215 = 1336823) B1336823
theorem B3316585 : Blo 171799 3316585 := bstep (se 2 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 3316585 = 2487439) B2487439
theorem B1318031 : Blo 171799 1318031 := bstep (se 1 (by rfl) ⟨988523, by rfl⟩ : syracuseStep 1318031 = 1977047) B1977047
theorem B3022055 : Blo 171799 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B499115 : Blo 171799 499115 := bstep (se 1 (by rfl) ⟨374336, by rfl⟩ : syracuseStep 499115 = 748673) B748673
theorem B4563539 : Blo 171799 4563539 := bstep (se 1 (by rfl) ⟨3422654, by rfl⟩ : syracuseStep 4563539 = 6845309) B6845309
theorem B664271 : Blo 171799 664271 := bstep (se 1 (by rfl) ⟨498203, by rfl⟩ : syracuseStep 664271 = 996407) B996407
theorem B172827 : Blo 171799 172827 := bstep (se 1 (by rfl) ⟨129620, by rfl⟩ : syracuseStep 172827 = 259241) B259241
theorem B4760369 : Blo 171799 4760369 := bstep (se 2 (by rfl) ⟨1785138, by rfl⟩ : syracuseStep 4760369 = 3570277) B3570277
theorem B172871 : Blo 171799 172871 := bstep (se 1 (by rfl) ⟨129653, by rfl⟩ : syracuseStep 172871 = 259307) B259307
theorem B467977 : Blo 171799 467977 := bstep (se 2 (by rfl) ⟨175491, by rfl⟩ : syracuseStep 467977 = 350983) B350983
theorem B1319975 : Blo 171799 1319975 := bstep (se 1 (by rfl) ⟨989981, by rfl⟩ : syracuseStep 1319975 = 1979963) B1979963
theorem B173295 : Blo 171799 173295 := bstep (se 1 (by rfl) ⟨129971, by rfl⟩ : syracuseStep 173295 = 259943) B259943
theorem B435527 : Blo 171799 435527 := bstep (se 1 (by rfl) ⟨326645, by rfl⟩ : syracuseStep 435527 = 653291) B653291
theorem B173383 : Blo 171799 173383 := bstep (se 1 (by rfl) ⟨130037, by rfl⟩ : syracuseStep 173383 = 260075) B260075
theorem B173471 : Blo 171799 173471 := bstep (se 1 (by rfl) ⟨130103, by rfl⟩ : syracuseStep 173471 = 260207) B260207
theorem B1123753 : Blo 171799 1123753 := bstep (se 2 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 1123753 = 842815) B842815
theorem B173991 : Blo 171799 173991 := bstep (se 1 (by rfl) ⟨130493, by rfl⟩ : syracuseStep 173991 = 260987) B260987
theorem B993491 : Blo 171799 993491 := bstep (se 1 (by rfl) ⟨745118, by rfl⟩ : syracuseStep 993491 = 1490237) B1490237
theorem B174319 : Blo 171799 174319 := bstep (se 1 (by rfl) ⟨130739, by rfl⟩ : syracuseStep 174319 = 261479) B261479
theorem B174875 : Blo 171799 174875 := bstep (se 1 (by rfl) ⟨131156, by rfl⟩ : syracuseStep 174875 = 262313) B262313
theorem B2206547 : Blo 171799 2206547 := bstep (se 1 (by rfl) ⟨1654910, by rfl⟩ : syracuseStep 2206547 = 3309821) B3309821
theorem B175015 : Blo 171799 175015 := bstep (se 1 (by rfl) ⟨131261, by rfl⟩ : syracuseStep 175015 = 262523) B262523
theorem B175131 : Blo 171799 175131 := bstep (se 1 (by rfl) ⟨131348, by rfl⟩ : syracuseStep 175131 = 262697) B262697
theorem B437359 : Blo 171799 437359 := bstep (se 1 (by rfl) ⟨328019, by rfl⟩ : syracuseStep 437359 = 656039) B656039
theorem B208027 : Blo 171799 208027 := bstep (se 1 (by rfl) ⟨156020, by rfl⟩ : syracuseStep 208027 = 312041) B312041
theorem B175335 : Blo 171799 175335 := bstep (se 1 (by rfl) ⟨131501, by rfl⟩ : syracuseStep 175335 = 263003) B263003
theorem B8039735 : Blo 171799 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B175567 : Blo 171799 175567 := bstep (se 1 (by rfl) ⟨131675, by rfl⟩ : syracuseStep 175567 = 263351) B263351
theorem B175727 : Blo 171799 175727 := bstep (se 1 (by rfl) ⟨131795, by rfl⟩ : syracuseStep 175727 = 263591) B263591
theorem B175775 : Blo 171799 175775 := bstep (se 1 (by rfl) ⟨131831, by rfl⟩ : syracuseStep 175775 = 263663) B263663
theorem B1683899 : Blo 171799 1683899 := bstep (se 1 (by rfl) ⟨1262924, by rfl⟩ : syracuseStep 1683899 = 2525849) B2525849
theorem B7550891 : Blo 171799 7550891 := bstep (se 1 (by rfl) ⟨5663168, by rfl⟩ : syracuseStep 7550891 = 11326337) B11326337
theorem B931799 : Blo 171799 931799 := bstep (se 1 (by rfl) ⟨698849, by rfl⟩ : syracuseStep 931799 = 1397699) B1397699
theorem B932255 : Blo 171799 932255 := bstep (se 1 (by rfl) ⟨699191, by rfl⟩ : syracuseStep 932255 = 1398383) B1398383
theorem B998183 : Blo 171799 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B441875 : Blo 171799 441875 := bstep (se 1 (by rfl) ⟨331406, by rfl⟩ : syracuseStep 441875 = 662813) B662813
theorem B1654991 : Blo 171799 1654991 := bstep (se 1 (by rfl) ⟨1241243, by rfl⟩ : syracuseStep 1654991 = 2482487) B2482487
theorem B1687817 : Blo 171799 1687817 := bstep (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) B1265863
theorem B934523 : Blo 171799 934523 := bstep (se 1 (by rfl) ⟨700892, by rfl⟩ : syracuseStep 934523 = 1401785) B1401785
theorem B443191 : Blo 171799 443191 := bstep (se 1 (by rfl) ⟨332393, by rfl⟩ : syracuseStep 443191 = 664787) B664787
theorem B312545 : Blo 171799 312545 := bstep (se 2 (by rfl) ⟨117204, by rfl⟩ : syracuseStep 312545 = 234409) B234409
theorem B3034259 : Blo 171799 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B3526507 : Blo 171799 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B413651 : Blo 171799 413651 := bstep (se 1 (by rfl) ⟨310238, by rfl⟩ : syracuseStep 413651 = 620477) B620477
theorem B4050917 : Blo 171799 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B1594673 : Blo 171799 1594673 := bstep (se 2 (by rfl) ⟨598002, by rfl⟩ : syracuseStep 1594673 = 1196005) B1196005
theorem B416411 : Blo 171799 416411 := bstep (se 1 (by rfl) ⟨312308, by rfl⟩ : syracuseStep 416411 = 624617) B624617
theorem B220315 : Blo 171799 220315 := bstep (se 1 (by rfl) ⟨165236, by rfl⟩ : syracuseStep 220315 = 330473) B330473
theorem B580769 : Blo 171799 580769 := bstep (se 2 (by rfl) ⟨217788, by rfl⟩ : syracuseStep 580769 = 435577) B435577
theorem B744659 : Blo 171799 744659 := bstep (se 1 (by rfl) ⟨558494, by rfl⟩ : syracuseStep 744659 = 1116989) B1116989
theorem B14245571 : Blo 171799 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B876743 : Blo 171799 876743 := bstep (se 1 (by rfl) ⟨657557, by rfl⟩ : syracuseStep 876743 = 1315115) B1315115
theorem B1794251 : Blo 171799 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B942479 : Blo 171799 942479 := bstep (se 1 (by rfl) ⟨706859, by rfl⟩ : syracuseStep 942479 = 1413719) B1413719
theorem B1991465 : Blo 171799 1991465 := bstep (se 2 (by rfl) ⟨746799, by rfl⟩ : syracuseStep 1991465 = 1493599) B1493599
theorem B31975033 : Blo 171799 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B1009313 : Blo 171799 1009313 := bstep (se 2 (by rfl) ⟨378492, by rfl⟩ : syracuseStep 1009313 = 756985) B756985
theorem B386729 : Blo 171799 386729 := bstep (se 2 (by rfl) ⟨145023, by rfl⟩ : syracuseStep 386729 = 290047) B290047
theorem B386855 : Blo 171799 386855 := bstep (se 1 (by rfl) ⟨290141, by rfl⟩ : syracuseStep 386855 = 580283) B580283
theorem B386927 : Blo 171799 386927 := bstep (se 1 (by rfl) ⟨290195, by rfl⟩ : syracuseStep 386927 = 580391) B580391
theorem B747407 : Blo 171799 747407 := bstep (se 1 (by rfl) ⟨560555, by rfl⟩ : syracuseStep 747407 = 1121111) B1121111
theorem B387323 : Blo 171799 387323 := bstep (se 1 (by rfl) ⟨290492, by rfl⟩ : syracuseStep 387323 = 580985) B580985
theorem B387881 : Blo 171799 387881 := bstep (se 2 (by rfl) ⟨145455, by rfl⟩ : syracuseStep 387881 = 290911) B290911
theorem B388007 : Blo 171799 388007 := bstep (se 1 (by rfl) ⟨291005, by rfl⟩ : syracuseStep 388007 = 582011) B582011
theorem B388151 : Blo 171799 388151 := bstep (se 1 (by rfl) ⟨291113, by rfl⟩ : syracuseStep 388151 = 582227) B582227
theorem B9268465 : Blo 171799 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B388583 : Blo 171799 388583 := bstep (se 1 (by rfl) ⟨291437, by rfl⟩ : syracuseStep 388583 = 582875) B582875
theorem B257801 : Blo 171799 257801 := bstep (se 2 (by rfl) ⟨96675, by rfl⟩ : syracuseStep 257801 = 193351) B193351
theorem B880631 : Blo 171799 880631 := bstep (se 1 (by rfl) ⟨660473, by rfl⟩ : syracuseStep 880631 = 1320947) B1320947
theorem B389159 : Blo 171799 389159 := bstep (se 1 (by rfl) ⟨291869, by rfl⟩ : syracuseStep 389159 = 583739) B583739
theorem B258095 : Blo 171799 258095 := bstep (se 1 (by rfl) ⟨193571, by rfl⟩ : syracuseStep 258095 = 387143) B387143
theorem B389375 : Blo 171799 389375 := bstep (se 1 (by rfl) ⟨292031, by rfl⟩ : syracuseStep 389375 = 584063) B584063
theorem B1241851 : Blo 171799 1241851 := bstep (se 1 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 1241851 = 1862777) B1862777
theorem B259007 : Blo 171799 259007 := bstep (se 1 (by rfl) ⟨194255, by rfl⟩ : syracuseStep 259007 = 388511) B388511
theorem B882089 : Blo 171799 882089 := bstep (se 2 (by rfl) ⟨330783, by rfl⟩ : syracuseStep 882089 = 661567) B661567
theorem B259559 : Blo 171799 259559 := bstep (se 1 (by rfl) ⟨194669, by rfl⟩ : syracuseStep 259559 = 389339) B389339
theorem B259631 : Blo 171799 259631 := bstep (se 1 (by rfl) ⟨194723, by rfl⟩ : syracuseStep 259631 = 389447) B389447
theorem B1013471 : Blo 171799 1013471 := bstep (se 1 (by rfl) ⟨760103, by rfl⟩ : syracuseStep 1013471 = 1520207) B1520207
theorem B489341 : Blo 171799 489341 := bstep (se 3 (by rfl) ⟨91751, by rfl⟩ : syracuseStep 489341 = 183503) B183503
theorem B391337 : Blo 171799 391337 := bstep (se 2 (by rfl) ⟨146751, by rfl⟩ : syracuseStep 391337 = 293503) B293503
theorem B4323881 : Blo 171799 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B883271 : Blo 171799 883271 := bstep (se 1 (by rfl) ⟨662453, by rfl⟩ : syracuseStep 883271 = 1324907) B1324907
theorem B260711 : Blo 171799 260711 := bstep (se 1 (by rfl) ⟨195533, by rfl⟩ : syracuseStep 260711 = 391067) B391067
theorem B1440371 : Blo 171799 1440371 := bstep (se 1 (by rfl) ⟨1080278, by rfl⟩ : syracuseStep 1440371 = 2160557) B2160557
theorem B391841 : Blo 171799 391841 := bstep (se 2 (by rfl) ⟨146940, by rfl⟩ : syracuseStep 391841 = 293881) B293881
theorem B391931 : Blo 171799 391931 := bstep (se 1 (by rfl) ⟨293948, by rfl⟩ : syracuseStep 391931 = 587897) B587897
theorem B391967 : Blo 171799 391967 := bstep (se 1 (by rfl) ⟨293975, by rfl⟩ : syracuseStep 391967 = 587951) B587951
theorem B261371 : Blo 171799 261371 := bstep (se 1 (by rfl) ⟨196028, by rfl⟩ : syracuseStep 261371 = 392057) B392057
theorem B1899773 : Blo 171799 1899773 := bstep (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) B712415
theorem B294151 : Blo 171799 294151 := bstep (se 1 (by rfl) ⟨220613, by rfl⟩ : syracuseStep 294151 = 441227) B441227
theorem B195943 : Blo 171799 195943 := bstep (se 1 (by rfl) ⟨146957, by rfl⟩ : syracuseStep 195943 = 293915) B293915
theorem B261599 : Blo 171799 261599 := bstep (se 1 (by rfl) ⟨196199, by rfl⟩ : syracuseStep 261599 = 392399) B392399
theorem B1867657 : Blo 171799 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B262079 : Blo 171799 262079 := bstep (se 1 (by rfl) ⟨196559, by rfl⟩ : syracuseStep 262079 = 393119) B393119
theorem B491483 : Blo 171799 491483 := bstep (se 1 (by rfl) ⟨368612, by rfl⟩ : syracuseStep 491483 = 737225) B737225
theorem B196591 : Blo 171799 196591 := bstep (se 1 (by rfl) ⟨147443, by rfl⟩ : syracuseStep 196591 = 294887) B294887
theorem B393209 : Blo 171799 393209 := bstep (se 2 (by rfl) ⟨147453, by rfl⟩ : syracuseStep 393209 = 294907) B294907
theorem B262265 : Blo 171799 262265 := bstep (se 2 (by rfl) ⟨98349, by rfl⟩ : syracuseStep 262265 = 196699) B196699
theorem B524647 : Blo 171799 524647 := bstep (se 1 (by rfl) ⟨393485, by rfl⟩ : syracuseStep 524647 = 786971) B786971
theorem B590219 : Blo 171799 590219 := bstep (se 1 (by rfl) ⟨442664, by rfl⟩ : syracuseStep 590219 = 885329) B885329
theorem B623015 : Blo 171799 623015 := bstep (se 1 (by rfl) ⟨467261, by rfl⟩ : syracuseStep 623015 = 934523) B934523
theorem B590327 : Blo 171799 590327 := bstep (se 1 (by rfl) ⟨442745, by rfl⟩ : syracuseStep 590327 = 885491) B885491
theorem B262655 : Blo 171799 262655 := bstep (se 1 (by rfl) ⟨196991, by rfl⟩ : syracuseStep 262655 = 393983) B393983
theorem B590921 : Blo 171799 590921 := bstep (se 2 (by rfl) ⟨221595, by rfl⟩ : syracuseStep 590921 = 443191) B443191
theorem B263465 : Blo 171799 263465 := bstep (se 2 (by rfl) ⟨98799, by rfl⟩ : syracuseStep 263465 = 197599) B197599
theorem B394559 : Blo 171799 394559 := bstep (se 1 (by rfl) ⟨295919, by rfl⟩ : syracuseStep 394559 = 591839) B591839
theorem B623969 : Blo 171799 623969 := bstep (se 2 (by rfl) ⟨233988, by rfl⟩ : syracuseStep 623969 = 467977) B467977
theorem B329447 : Blo 171799 329447 := bstep (se 1 (by rfl) ⟨247085, by rfl⟩ : syracuseStep 329447 = 494171) B494171
theorem B395099 : Blo 171799 395099 := bstep (se 1 (by rfl) ⟨296324, by rfl⟩ : syracuseStep 395099 = 592649) B592649
theorem B329683 : Blo 171799 329683 := bstep (se 1 (by rfl) ⟨247262, by rfl⟩ : syracuseStep 329683 = 494525) B494525
theorem B42633377 : Blo 171799 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B329903 : Blo 171799 329903 := bstep (se 1 (by rfl) ⟨247427, by rfl⟩ : syracuseStep 329903 = 494855) B494855
theorem B2689523 : Blo 171799 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B199279 : Blo 171799 199279 := bstep (se 1 (by rfl) ⟨149459, by rfl⟩ : syracuseStep 199279 = 298919) B298919
theorem B2493899 : Blo 171799 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B659623 : Blo 171799 659623 := bstep (se 1 (by rfl) ⟨494717, by rfl⟩ : syracuseStep 659623 = 989435) B989435
theorem B594143 : Blo 171799 594143 := bstep (se 1 (by rfl) ⟨445607, by rfl⟩ : syracuseStep 594143 = 891215) B891215
theorem B12357953 : Blo 171799 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B496439 : Blo 171799 496439 := bstep (se 1 (by rfl) ⟨372329, by rfl⟩ : syracuseStep 496439 = 744659) B744659
theorem B332743 : Blo 171799 332743 := bstep (se 1 (by rfl) ⟨249557, by rfl⟩ : syracuseStep 332743 = 499115) B499115
theorem B628319 : Blo 171799 628319 := bstep (se 1 (by rfl) ⟨471239, by rfl⟩ : syracuseStep 628319 = 942479) B942479
theorem B662327 : Blo 171799 662327 := bstep (se 1 (by rfl) ⟨496745, by rfl⟩ : syracuseStep 662327 = 993491) B993491
theorem B171867 : Blo 171799 171867 := bstep (se 1 (by rfl) ⟨128900, by rfl⟩ : syracuseStep 171867 = 257801) B257801
theorem B262139 : Blo 171799 262139 := bstep (se 1 (by rfl) ⟨196604, by rfl⟩ : syracuseStep 262139 = 393209) B393209
theorem B172063 : Blo 171799 172063 := bstep (se 1 (by rfl) ⟨129047, by rfl⟩ : syracuseStep 172063 = 258095) B258095
theorem B2236481 : Blo 171799 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B1122599 : Blo 171799 1122599 := bstep (se 1 (by rfl) ⟨841949, by rfl⟩ : syracuseStep 1122599 = 1683899) B1683899
theorem B172671 : Blo 171799 172671 := bstep (se 1 (by rfl) ⟨129503, by rfl⟩ : syracuseStep 172671 = 259007) B259007
theorem B173039 : Blo 171799 173039 := bstep (se 1 (by rfl) ⟨129779, by rfl⟩ : syracuseStep 173039 = 259559) B259559
theorem B173087 : Blo 171799 173087 := bstep (se 1 (by rfl) ⟨129815, by rfl⟩ : syracuseStep 173087 = 259631) B259631
theorem B173807 : Blo 171799 173807 := bstep (se 1 (by rfl) ⟨130355, by rfl⟩ : syracuseStep 173807 = 260711) B260711
theorem B960247 : Blo 171799 960247 := bstep (se 1 (by rfl) ⟨720185, by rfl⟩ : syracuseStep 960247 = 1440371) B1440371
theorem B37988189 : Blo 171799 37988189 := bstep (se 3 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 37988189 = 14245571) B14245571
theorem B665455 : Blo 171799 665455 := bstep (se 1 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 665455 = 998183) B998183
theorem B174247 : Blo 171799 174247 := bstep (se 1 (by rfl) ⟨130685, by rfl⟩ : syracuseStep 174247 = 261371) B261371
theorem B174399 : Blo 171799 174399 := bstep (se 1 (by rfl) ⟨130799, by rfl⟩ : syracuseStep 174399 = 261599) B261599
theorem B174719 : Blo 171799 174719 := bstep (se 1 (by rfl) ⟨131039, by rfl⟩ : syracuseStep 174719 = 262079) B262079
theorem B175135 : Blo 171799 175135 := bstep (se 1 (by rfl) ⟨131351, by rfl⟩ : syracuseStep 175135 = 262703) B262703
theorem B437339 : Blo 171799 437339 := bstep (se 1 (by rfl) ⟨328004, by rfl⟩ : syracuseStep 437339 = 656009) B656009
theorem B175259 : Blo 171799 175259 := bstep (se 1 (by rfl) ⟨131444, by rfl⟩ : syracuseStep 175259 = 262889) B262889
theorem B4500845 : Blo 171799 4500845 := bstep (se 3 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 4500845 = 1687817) B1687817
theorem B275767 : Blo 171799 275767 := bstep (se 1 (by rfl) ⟨206825, by rfl⟩ : syracuseStep 275767 = 413651) B413651
theorem B2700611 : Blo 171799 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B440063 : Blo 171799 440063 := bstep (se 1 (by rfl) ⟨330047, by rfl⟩ : syracuseStep 440063 = 660095) B660095
theorem B833453 : Blo 171799 833453 := bstep (se 3 (by rfl) ⟨156272, by rfl⟩ : syracuseStep 833453 = 312545) B312545
theorem B1063115 : Blo 171799 1063115 := bstep (se 1 (by rfl) ⟨797336, by rfl⟩ : syracuseStep 1063115 = 1594673) B1594673
theorem B310139 : Blo 171799 310139 := bstep (se 1 (by rfl) ⟨232604, by rfl⟩ : syracuseStep 310139 = 465209) B465209
theorem B37665881 : Blo 171799 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B277607 : Blo 171799 277607 := bstep (se 1 (by rfl) ⟨208205, by rfl⟩ : syracuseStep 277607 = 416411) B416411
theorem B2014703 : Blo 171799 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B4702009 : Blo 171799 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B1196167 : Blo 171799 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B442847 : Blo 171799 442847 := bstep (se 1 (by rfl) ⟨332135, by rfl⟩ : syracuseStep 442847 = 664271) B664271
theorem B1327643 : Blo 171799 1327643 := bstep (se 1 (by rfl) ⟨995732, by rfl⟩ : syracuseStep 1327643 = 1991465) B1991465
theorem B443369 : Blo 171799 443369 := bstep (se 2 (by rfl) ⟨166263, by rfl⟩ : syracuseStep 443369 = 332527) B332527
theorem B1655801 : Blo 171799 1655801 := bstep (se 2 (by rfl) ⟨620925, by rfl⟩ : syracuseStep 1655801 = 1241851) B1241851
theorem B672875 : Blo 171799 672875 := bstep (se 1 (by rfl) ⟨504656, by rfl⟩ : syracuseStep 672875 = 1009313) B1009313
theorem B5359823 : Blo 171799 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B675647 : Blo 171799 675647 := bstep (se 1 (by rfl) ⟨506735, by rfl⟩ : syracuseStep 675647 = 1013471) B1013471
theorem B5033927 : Blo 171799 5033927 := bstep (se 1 (by rfl) ⟨3775445, by rfl⟩ : syracuseStep 5033927 = 7550891) B7550891
theorem B1266515 : Blo 171799 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B1103327 : Blo 171799 1103327 := bstep (se 1 (by rfl) ⟨827495, by rfl⟩ : syracuseStep 1103327 = 1654991) B1654991
theorem B36591587 : Blo 171799 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B1498337 : Blo 171799 1498337 := bstep (se 2 (by rfl) ⟨561876, by rfl⟩ : syracuseStep 1498337 = 1123753) B1123753
theorem B1334555 : Blo 171799 1334555 := bstep (se 1 (by rfl) ⟨1000916, by rfl⟩ : syracuseStep 1334555 = 2001833) B2001833
theorem B875933 : Blo 171799 875933 := bstep (se 3 (by rfl) ⟨164237, by rfl⟩ : syracuseStep 875933 = 328475) B328475
theorem B2022839 : Blo 171799 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B746587 : Blo 171799 746587 := bstep (se 1 (by rfl) ⟨559940, by rfl⟩ : syracuseStep 746587 = 1119881) B1119881
theorem B583145 : Blo 171799 583145 := bstep (se 2 (by rfl) ⟨218679, by rfl⟩ : syracuseStep 583145 = 437359) B437359
theorem B878687 : Blo 171799 878687 := bstep (se 1 (by rfl) ⟨659015, by rfl⟩ : syracuseStep 878687 = 1318031) B1318031
theorem B387179 : Blo 171799 387179 := bstep (se 1 (by rfl) ⟨290384, by rfl⟩ : syracuseStep 387179 = 580769) B580769
theorem B1304909 : Blo 171799 1304909 := bstep (se 3 (by rfl) ⟨244670, by rfl⟩ : syracuseStep 1304909 = 489341) B489341
theorem B1993085 : Blo 171799 1993085 := bstep (se 3 (by rfl) ⟨373703, by rfl⟩ : syracuseStep 1993085 = 747407) B747407
theorem B584495 : Blo 171799 584495 := bstep (se 1 (by rfl) ⟨438371, by rfl⟩ : syracuseStep 584495 = 876743) B876743
theorem B3042359 : Blo 171799 3042359 := bstep (se 1 (by rfl) ⟨2281769, by rfl⟩ : syracuseStep 3042359 = 4563539) B4563539
theorem B3173579 : Blo 171799 3173579 := bstep (se 1 (by rfl) ⟨2380184, by rfl⟩ : syracuseStep 3173579 = 4760369) B4760369
theorem B879983 : Blo 171799 879983 := bstep (se 1 (by rfl) ⟨659987, by rfl⟩ : syracuseStep 879983 = 1319975) B1319975
theorem B1109477 : Blo 171799 1109477 := bstep (se 4 (by rfl) ⟨104013, by rfl⟩ : syracuseStep 1109477 = 208027) B208027
theorem B749033 : Blo 171799 749033 := bstep (se 2 (by rfl) ⟨280887, by rfl⟩ : syracuseStep 749033 = 561775) B561775
theorem B290351 : Blo 171799 290351 := bstep (se 1 (by rfl) ⟨217763, by rfl⟩ : syracuseStep 290351 = 435527) B435527
theorem B257819 : Blo 171799 257819 := bstep (se 1 (by rfl) ⟨193364, by rfl⟩ : syracuseStep 257819 = 386729) B386729
theorem B257903 : Blo 171799 257903 := bstep (se 1 (by rfl) ⟨193427, by rfl⟩ : syracuseStep 257903 = 386855) B386855
theorem B257951 : Blo 171799 257951 := bstep (se 1 (by rfl) ⟨193463, by rfl⟩ : syracuseStep 257951 = 386927) B386927
theorem B258215 : Blo 171799 258215 := bstep (se 1 (by rfl) ⟨193661, by rfl⟩ : syracuseStep 258215 = 387323) B387323
theorem B2355389 : Blo 171799 2355389 := bstep (se 3 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 2355389 = 883271) B883271
theorem B258587 : Blo 171799 258587 := bstep (se 1 (by rfl) ⟨193940, by rfl⟩ : syracuseStep 258587 = 387881) B387881
theorem B1471031 : Blo 171799 1471031 := bstep (se 1 (by rfl) ⟨1103273, by rfl⟩ : syracuseStep 1471031 = 2206547) B2206547
theorem B258671 : Blo 171799 258671 := bstep (se 1 (by rfl) ⟨194003, by rfl⟩ : syracuseStep 258671 = 388007) B388007
theorem B258767 : Blo 171799 258767 := bstep (se 1 (by rfl) ⟨194075, by rfl⟩ : syracuseStep 258767 = 388151) B388151
theorem B259055 : Blo 171799 259055 := bstep (se 1 (by rfl) ⟨194291, by rfl⟩ : syracuseStep 259055 = 388583) B388583
theorem B1012961 : Blo 171799 1012961 := bstep (se 2 (by rfl) ⟨379860, by rfl⟩ : syracuseStep 1012961 = 759721) B759721
theorem B587087 : Blo 171799 587087 := bstep (se 1 (by rfl) ⟨440315, by rfl⟩ : syracuseStep 587087 = 880631) B880631
theorem B259439 : Blo 171799 259439 := bstep (se 1 (by rfl) ⟨194579, by rfl⟩ : syracuseStep 259439 = 389159) B389159
theorem B259583 : Blo 171799 259583 := bstep (se 1 (by rfl) ⟨194687, by rfl⟩ : syracuseStep 259583 = 389375) B389375
theorem B1275425 : Blo 171799 1275425 := bstep (se 2 (by rfl) ⟨478284, by rfl⟩ : syracuseStep 1275425 = 956569) B956569
theorem B588059 : Blo 171799 588059 := bstep (se 1 (by rfl) ⟨441044, by rfl⟩ : syracuseStep 588059 = 882089) B882089
theorem B4422113 : Blo 171799 4422113 := bstep (se 2 (by rfl) ⟨1658292, by rfl⟩ : syracuseStep 4422113 = 3316585) B3316585
theorem B621199 : Blo 171799 621199 := bstep (se 1 (by rfl) ⟨465899, by rfl⟩ : syracuseStep 621199 = 931799) B931799
theorem B260891 : Blo 171799 260891 := bstep (se 1 (by rfl) ⟨195668, by rfl⟩ : syracuseStep 260891 = 391337) B391337
theorem B293753 : Blo 171799 293753 := bstep (se 2 (by rfl) ⟨110157, by rfl⟩ : syracuseStep 293753 = 220315) B220315
theorem B621503 : Blo 171799 621503 := bstep (se 1 (by rfl) ⟨466127, by rfl⟩ : syracuseStep 621503 = 932255) B932255
theorem B392201 : Blo 171799 392201 := bstep (se 2 (by rfl) ⟨147075, by rfl⟩ : syracuseStep 392201 = 294151) B294151
theorem B2882587 : Blo 171799 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B261227 : Blo 171799 261227 := bstep (se 1 (by rfl) ⟨195920, by rfl⟩ : syracuseStep 261227 = 391841) B391841
theorem B261257 : Blo 171799 261257 := bstep (se 2 (by rfl) ⟨97971, by rfl⟩ : syracuseStep 261257 = 195943) B195943
theorem B261287 : Blo 171799 261287 := bstep (se 1 (by rfl) ⟨195965, by rfl⟩ : syracuseStep 261287 = 391931) B391931
theorem B261311 : Blo 171799 261311 := bstep (se 1 (by rfl) ⟨195983, by rfl⟩ : syracuseStep 261311 = 391967) B391967
theorem B294583 : Blo 171799 294583 := bstep (se 1 (by rfl) ⟨220937, by rfl⟩ : syracuseStep 294583 = 441875) B441875
theorem B2490209 : Blo 171799 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B327655 : Blo 171799 327655 := bstep (se 1 (by rfl) ⟨245741, by rfl⟩ : syracuseStep 327655 = 491483) B491483
theorem B262121 : Blo 171799 262121 := bstep (se 2 (by rfl) ⟨98295, by rfl⟩ : syracuseStep 262121 = 196591) B196591
theorem B393479 : Blo 171799 393479 := bstep (se 1 (by rfl) ⟨295109, by rfl⟩ : syracuseStep 393479 = 590219) B590219
theorem B295231 : Blo 171799 295231 := bstep (se 1 (by rfl) ⟨221423, by rfl⟩ : syracuseStep 295231 = 442847) B442847
theorem B393551 : Blo 171799 393551 := bstep (se 1 (by rfl) ⟨295163, by rfl⟩ : syracuseStep 393551 = 590327) B590327
theorem B885095 : Blo 171799 885095 := bstep (se 1 (by rfl) ⟨663821, by rfl⟩ : syracuseStep 885095 = 1327643) B1327643
theorem B295579 : Blo 171799 295579 := bstep (se 1 (by rfl) ⟨221684, by rfl⟩ : syracuseStep 295579 = 443369) B443369
theorem B393947 : Blo 171799 393947 := bstep (se 1 (by rfl) ⟨295460, by rfl⟩ : syracuseStep 393947 = 590921) B590921
theorem B263039 : Blo 171799 263039 := bstep (se 1 (by rfl) ⟨197279, by rfl⟩ : syracuseStep 263039 = 394559) B394559
theorem B263399 : Blo 171799 263399 := bstep (se 1 (by rfl) ⟨197549, by rfl⟩ : syracuseStep 263399 = 395099) B395099
theorem B3573215 : Blo 171799 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B1280329 : Blo 171799 1280329 := bstep (se 2 (by rfl) ⟨480123, by rfl⟩ : syracuseStep 1280329 = 960247) B960247
theorem B887273 : Blo 171799 887273 := bstep (se 2 (by rfl) ⟨332727, by rfl⟩ : syracuseStep 887273 = 665455) B665455
theorem B396095 : Blo 171799 396095 := bstep (se 1 (by rfl) ⟨297071, by rfl⟩ : syracuseStep 396095 = 594143) B594143
theorem B330959 : Blo 171799 330959 := bstep (se 1 (by rfl) ⟨248219, by rfl⟩ : syracuseStep 330959 = 496439) B496439
theorem B889703 : Blo 171799 889703 := bstep (se 1 (by rfl) ⟨667277, by rfl⟩ : syracuseStep 889703 = 1334555) B1334555
theorem B1348559 : Blo 171799 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B499355 : Blo 171799 499355 := bstep (se 1 (by rfl) ⟨374516, by rfl⟩ : syracuseStep 499355 = 749033) B749033
theorem B171879 : Blo 171799 171879 := bstep (se 1 (by rfl) ⟨128909, by rfl⟩ : syracuseStep 171879 = 257819) B257819
theorem B171935 : Blo 171799 171935 := bstep (se 1 (by rfl) ⟨128951, by rfl⟩ : syracuseStep 171935 = 257903) B257903
theorem B171967 : Blo 171799 171967 := bstep (se 1 (by rfl) ⟨128975, by rfl⟩ : syracuseStep 171967 = 257951) B257951
theorem B172143 : Blo 171799 172143 := bstep (se 1 (by rfl) ⟨129107, by rfl⟩ : syracuseStep 172143 = 258215) B258215
theorem B172391 : Blo 171799 172391 := bstep (se 1 (by rfl) ⟨129293, by rfl⟩ : syracuseStep 172391 = 258587) B258587
theorem B172447 : Blo 171799 172447 := bstep (se 1 (by rfl) ⟨129335, by rfl⟩ : syracuseStep 172447 = 258671) B258671
theorem B172511 : Blo 171799 172511 := bstep (se 1 (by rfl) ⟨129383, by rfl⟩ : syracuseStep 172511 = 258767) B258767
theorem B172703 : Blo 171799 172703 := bstep (se 1 (by rfl) ⟨129527, by rfl⟩ : syracuseStep 172703 = 259055) B259055
theorem B828265 : Blo 171799 828265 := bstep (se 2 (by rfl) ⟨310599, by rfl⟩ : syracuseStep 828265 = 621199) B621199
theorem B172959 : Blo 171799 172959 := bstep (se 1 (by rfl) ⟨129719, by rfl⟩ : syracuseStep 172959 = 259439) B259439
theorem B173055 : Blo 171799 173055 := bstep (se 1 (by rfl) ⟨129791, by rfl⟩ : syracuseStep 173055 = 259583) B259583
theorem B3843449 : Blo 171799 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B173927 : Blo 171799 173927 := bstep (se 1 (by rfl) ⟨130445, by rfl⟩ : syracuseStep 173927 = 260891) B260891
theorem B206759 : Blo 171799 206759 := bstep (se 1 (by rfl) ⟨155069, by rfl⟩ : syracuseStep 206759 = 310139) B310139
theorem B25110587 : Blo 171799 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B174151 : Blo 171799 174151 := bstep (se 1 (by rfl) ⟨130613, by rfl⟩ : syracuseStep 174151 = 261227) B261227
theorem B174171 : Blo 171799 174171 := bstep (se 1 (by rfl) ⟨130628, by rfl⟩ : syracuseStep 174171 = 261257) B261257
theorem B174191 : Blo 171799 174191 := bstep (se 1 (by rfl) ⟨130643, by rfl⟩ : syracuseStep 174191 = 261287) B261287
theorem B174207 : Blo 171799 174207 := bstep (se 1 (by rfl) ⟨130655, by rfl⟩ : syracuseStep 174207 = 261311) B261311
theorem B6269345 : Blo 171799 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B436873 : Blo 171799 436873 := bstep (se 2 (by rfl) ⟨163827, by rfl⟩ : syracuseStep 436873 = 327655) B327655
theorem B174747 : Blo 171799 174747 := bstep (se 1 (by rfl) ⟨131060, by rfl⟩ : syracuseStep 174747 = 262121) B262121
theorem B174759 : Blo 171799 174759 := bstep (se 1 (by rfl) ⟨131069, by rfl⟩ : syracuseStep 174759 = 262139) B262139
theorem B174843 : Blo 171799 174843 := bstep (se 1 (by rfl) ⟨131132, by rfl⟩ : syracuseStep 174843 = 262265) B262265
theorem B175103 : Blo 171799 175103 := bstep (se 1 (by rfl) ⟨131327, by rfl⟩ : syracuseStep 175103 = 262655) B262655
theorem B699529 : Blo 171799 699529 := bstep (se 2 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 699529 = 524647) B524647
theorem B175643 : Blo 171799 175643 := bstep (se 1 (by rfl) ⟨131732, by rfl⟩ : syracuseStep 175643 = 263465) B263465
theorem B28422251 : Blo 171799 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B995449 : Blo 171799 995449 := bstep (se 2 (by rfl) ⟨373293, by rfl⟩ : syracuseStep 995449 = 746587) B746587
theorem B439577 : Blo 171799 439577 := bstep (se 2 (by rfl) ⟨164841, by rfl⟩ : syracuseStep 439577 = 329683) B329683
theorem B3355951 : Blo 171799 3355951 := bstep (se 1 (by rfl) ⟨2516963, by rfl⟩ : syracuseStep 3355951 = 5033927) B5033927
theorem B8238635 : Blo 171799 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B1062821 : Blo 171799 1062821 := bstep (se 4 (by rfl) ⟨99639, by rfl⟩ : syracuseStep 1062821 = 199279) B199279
theorem B735551 : Blo 171799 735551 := bstep (se 1 (by rfl) ⟨551663, by rfl⟩ : syracuseStep 735551 = 1103327) B1103327
theorem B24394391 : Blo 171799 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B441551 : Blo 171799 441551 := bstep (se 1 (by rfl) ⟨331163, by rfl⟩ : syracuseStep 441551 = 662327) B662327
theorem B998891 : Blo 171799 998891 := bstep (se 1 (by rfl) ⟨749168, by rfl⟩ : syracuseStep 998891 = 1498337) B1498337
theorem B1490987 : Blo 171799 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B443657 : Blo 171799 443657 := bstep (se 2 (by rfl) ⟨166371, by rfl⟩ : syracuseStep 443657 = 332743) B332743
theorem B869939 : Blo 171799 869939 := bstep (se 1 (by rfl) ⟨652454, by rfl⟩ : syracuseStep 869939 = 1304909) B1304909
theorem B1328723 : Blo 171799 1328723 := bstep (se 1 (by rfl) ⟨996542, by rfl⟩ : syracuseStep 1328723 = 1993085) B1993085
theorem B2115719 : Blo 171799 2115719 := bstep (se 1 (by rfl) ⟨1586789, by rfl⟩ : syracuseStep 2115719 = 3173579) B3173579
theorem B3000563 : Blo 171799 3000563 := bstep (se 1 (by rfl) ⟨2250422, by rfl⟩ : syracuseStep 3000563 = 4500845) B4500845
theorem B739651 : Blo 171799 739651 := bstep (se 1 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 739651 = 1109477) B1109477
theorem B740285 : Blo 171799 740285 := bstep (se 3 (by rfl) ⟨138803, by rfl⟩ : syracuseStep 740285 = 277607) B277607
theorem B675307 : Blo 171799 675307 := bstep (se 1 (by rfl) ⟨506480, by rfl⟩ : syracuseStep 675307 = 1012961) B1012961
theorem B708743 : Blo 171799 708743 := bstep (se 1 (by rfl) ⟨531557, by rfl⟩ : syracuseStep 708743 = 1063115) B1063115
theorem B414335 : Blo 171799 414335 := bstep (se 1 (by rfl) ⟨310751, by rfl⟩ : syracuseStep 414335 = 621503) B621503
theorem B1660139 : Blo 171799 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B1594889 : Blo 171799 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B415343 : Blo 171799 415343 := bstep (se 1 (by rfl) ⟨311507, by rfl⟩ : syracuseStep 415343 = 623015) B623015
theorem B1103867 : Blo 171799 1103867 := bstep (se 1 (by rfl) ⟨827900, by rfl⟩ : syracuseStep 1103867 = 1655801) B1655801
theorem B448583 : Blo 171799 448583 := bstep (se 1 (by rfl) ⟨336437, by rfl⟩ : syracuseStep 448583 = 672875) B672875
theorem B415979 : Blo 171799 415979 := bstep (se 1 (by rfl) ⟨311984, by rfl⟩ : syracuseStep 415979 = 623969) B623969
theorem B219935 : Blo 171799 219935 := bstep (se 1 (by rfl) ⟨164951, by rfl⟩ : syracuseStep 219935 = 329903) B329903
theorem B1793015 : Blo 171799 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B1662599 : Blo 171799 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B450431 : Blo 171799 450431 := bstep (se 1 (by rfl) ⟨337823, by rfl⟩ : syracuseStep 450431 = 675647) B675647
theorem B844343 : Blo 171799 844343 := bstep (se 1 (by rfl) ⟨633257, by rfl⟩ : syracuseStep 844343 = 1266515) B1266515
theorem B418879 : Blo 171799 418879 := bstep (se 1 (by rfl) ⟨314159, by rfl⟩ : syracuseStep 418879 = 628319) B628319
theorem B878525 : Blo 171799 878525 := bstep (se 3 (by rfl) ⟨164723, by rfl⟩ : syracuseStep 878525 = 329447) B329447
theorem B583955 : Blo 171799 583955 := bstep (se 1 (by rfl) ⟨437966, by rfl⟩ : syracuseStep 583955 = 875933) B875933
theorem B748399 : Blo 171799 748399 := bstep (se 1 (by rfl) ⟨561299, by rfl⟩ : syracuseStep 748399 = 1122599) B1122599
theorem B879497 : Blo 171799 879497 := bstep (se 2 (by rfl) ⟨329811, by rfl⟩ : syracuseStep 879497 = 659623) B659623
theorem B388763 : Blo 171799 388763 := bstep (se 1 (by rfl) ⟨291572, by rfl⟩ : syracuseStep 388763 = 583145) B583145
theorem B25325459 : Blo 171799 25325459 := bstep (se 1 (by rfl) ⟨18994094, by rfl⟩ : syracuseStep 25325459 = 37988189) B37988189
theorem B585791 : Blo 171799 585791 := bstep (se 1 (by rfl) ⟨439343, by rfl⟩ : syracuseStep 585791 = 878687) B878687
theorem B258119 : Blo 171799 258119 := bstep (se 1 (by rfl) ⟨193589, by rfl⟩ : syracuseStep 258119 = 387179) B387179
theorem B1470757 : Blo 171799 1470757 := bstep (se 4 (by rfl) ⟨137883, by rfl⟩ : syracuseStep 1470757 = 275767) B275767
theorem B389663 : Blo 171799 389663 := bstep (se 1 (by rfl) ⟨292247, by rfl⟩ : syracuseStep 389663 = 584495) B584495
theorem B2028239 : Blo 171799 2028239 := bstep (se 1 (by rfl) ⟨1521179, by rfl⟩ : syracuseStep 2028239 = 3042359) B3042359
theorem B291559 : Blo 171799 291559 := bstep (se 1 (by rfl) ⟨218669, by rfl⟩ : syracuseStep 291559 = 437339) B437339
theorem B586655 : Blo 171799 586655 := bstep (se 1 (by rfl) ⟨439991, by rfl⟩ : syracuseStep 586655 = 879983) B879983
theorem B193567 : Blo 171799 193567 := bstep (se 1 (by rfl) ⟨145175, by rfl⟩ : syracuseStep 193567 = 290351) B290351
theorem B1570259 : Blo 171799 1570259 := bstep (se 1 (by rfl) ⟨1177694, by rfl⟩ : syracuseStep 1570259 = 2355389) B2355389
theorem B980687 : Blo 171799 980687 := bstep (se 1 (by rfl) ⟨735515, by rfl⟩ : syracuseStep 980687 = 1471031) B1471031
theorem B1800407 : Blo 171799 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B391391 : Blo 171799 391391 := bstep (se 1 (by rfl) ⟨293543, by rfl⟩ : syracuseStep 391391 = 587087) B587087
theorem B850283 : Blo 171799 850283 := bstep (se 1 (by rfl) ⟨637712, by rfl⟩ : syracuseStep 850283 = 1275425) B1275425
theorem B293375 : Blo 171799 293375 := bstep (se 1 (by rfl) ⟨220031, by rfl⟩ : syracuseStep 293375 = 440063) B440063
theorem B555635 : Blo 171799 555635 := bstep (se 1 (by rfl) ⟨416726, by rfl⟩ : syracuseStep 555635 = 833453) B833453
theorem B392039 : Blo 171799 392039 := bstep (se 1 (by rfl) ⟨294029, by rfl⟩ : syracuseStep 392039 = 588059) B588059
theorem B2948075 : Blo 171799 2948075 := bstep (se 1 (by rfl) ⟨2211056, by rfl⟩ : syracuseStep 2948075 = 4422113) B4422113
theorem B195835 : Blo 171799 195835 := bstep (se 1 (by rfl) ⟨146876, by rfl⟩ : syracuseStep 195835 = 293753) B293753
theorem B261467 : Blo 171799 261467 := bstep (se 1 (by rfl) ⟨196100, by rfl⟩ : syracuseStep 261467 = 392201) B392201
theorem B392777 : Blo 171799 392777 := bstep (se 2 (by rfl) ⟨147291, by rfl⟩ : syracuseStep 392777 = 294583) B294583
theorem B1343135 : Blo 171799 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B262319 : Blo 171799 262319 := bstep (se 1 (by rfl) ⟨196739, by rfl⟩ : syracuseStep 262319 = 393479) B393479
theorem B262367 : Blo 171799 262367 := bstep (se 1 (by rfl) ⟨196775, by rfl⟩ : syracuseStep 262367 = 393551) B393551
theorem B590063 : Blo 171799 590063 := bstep (se 1 (by rfl) ⟨442547, by rfl⟩ : syracuseStep 590063 = 885095) B885095
theorem B393641 : Blo 171799 393641 := bstep (se 2 (by rfl) ⟨147615, by rfl⟩ : syracuseStep 393641 = 295231) B295231
theorem B262631 : Blo 171799 262631 := bstep (se 1 (by rfl) ⟨196973, by rfl⟩ : syracuseStep 262631 = 393947) B393947
theorem B295771 : Blo 171799 295771 := bstep (se 1 (by rfl) ⟨221828, by rfl⟩ : syracuseStep 295771 = 443657) B443657
theorem B885815 : Blo 171799 885815 := bstep (se 1 (by rfl) ⟨664361, by rfl⟩ : syracuseStep 885815 = 1328723) B1328723
theorem B558505 : Blo 171799 558505 := bstep (se 2 (by rfl) ⟨209439, by rfl⟩ : syracuseStep 558505 = 418879) B418879
theorem B1410479 : Blo 171799 1410479 := bstep (se 1 (by rfl) ⟨1057859, by rfl⟩ : syracuseStep 1410479 = 2115719) B2115719
theorem B2000375 : Blo 171799 2000375 := bstep (se 1 (by rfl) ⟨1500281, by rfl⟩ : syracuseStep 2000375 = 3000563) B3000563
theorem B591515 : Blo 171799 591515 := bstep (se 1 (by rfl) ⟨443636, by rfl⟩ : syracuseStep 591515 = 887273) B887273
theorem B493523 : Blo 171799 493523 := bstep (se 1 (by rfl) ⟨370142, by rfl⟩ : syracuseStep 493523 = 740285) B740285
theorem B986201 : Blo 171799 986201 := bstep (se 2 (by rfl) ⟨369825, by rfl⟩ : syracuseStep 986201 = 739651) B739651
theorem B593135 : Blo 171799 593135 := bstep (se 1 (by rfl) ⟨444851, by rfl⟩ : syracuseStep 593135 = 889703) B889703
theorem B1576421 : Blo 171799 1576421 := bstep (se 4 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 1576421 = 295579) B295579
theorem B332903 : Blo 171799 332903 := bstep (se 1 (by rfl) ⟨249677, by rfl⟩ : syracuseStep 332903 = 499355) B499355
theorem B300287 : Blo 171799 300287 := bstep (se 1 (by rfl) ⟨225215, by rfl⟩ : syracuseStep 300287 = 450431) B450431
theorem B562895 : Blo 171799 562895 := bstep (se 1 (by rfl) ⟨422171, by rfl⟩ : syracuseStep 562895 = 844343) B844343
theorem B2562299 : Blo 171799 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B1056253 : Blo 171799 1056253 := bstep (se 3 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 1056253 = 396095) B396095
theorem B16883639 : Blo 171799 16883639 := bstep (se 1 (by rfl) ⟨12662729, by rfl⟩ : syracuseStep 16883639 = 25325459) B25325459
theorem B172079 : Blo 171799 172079 := bstep (se 1 (by rfl) ⟨129059, by rfl⟩ : syracuseStep 172079 = 258119) B258119
theorem B18948167 : Blo 171799 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B1352159 : Blo 171799 1352159 := bstep (se 1 (by rfl) ⟨1014119, by rfl⟩ : syracuseStep 1352159 = 2028239) B2028239
theorem B566855 : Blo 171799 566855 := bstep (se 1 (by rfl) ⟨425141, by rfl⟩ : syracuseStep 566855 = 850283) B850283
theorem B370423 : Blo 171799 370423 := bstep (se 1 (by rfl) ⟨277817, by rfl⟩ : syracuseStep 370423 = 555635) B555635
theorem B16262927 : Blo 171799 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B174311 : Blo 171799 174311 := bstep (se 1 (by rfl) ⟨130733, by rfl⟩ : syracuseStep 174311 = 261467) B261467
theorem B665927 : Blo 171799 665927 := bstep (se 1 (by rfl) ⟨499445, by rfl⟩ : syracuseStep 665927 = 998891) B998891
theorem B895423 : Blo 171799 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B993991 : Blo 171799 993991 := bstep (se 1 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 993991 = 1490987) B1490987
theorem B175359 : Blo 171799 175359 := bstep (se 1 (by rfl) ⟨131519, by rfl⟩ : syracuseStep 175359 = 263039) B263039
theorem B175599 : Blo 171799 175599 := bstep (se 1 (by rfl) ⟨131699, by rfl⟩ : syracuseStep 175599 = 263399) B263399
theorem B472495 : Blo 171799 472495 := bstep (se 1 (by rfl) ⟨354371, by rfl⟩ : syracuseStep 472495 = 708743) B708743
theorem B276223 : Blo 171799 276223 := bstep (se 1 (by rfl) ⟨207167, by rfl⟩ : syracuseStep 276223 = 414335) B414335
theorem B899039 : Blo 171799 899039 := bstep (se 1 (by rfl) ⟨674279, by rfl⟩ : syracuseStep 899039 = 1348559) B1348559
theorem B1063259 : Blo 171799 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B276895 : Blo 171799 276895 := bstep (se 1 (by rfl) ⟨207671, by rfl⟩ : syracuseStep 276895 = 415343) B415343
theorem B997865 : Blo 171799 997865 := bstep (se 2 (by rfl) ⟨374199, by rfl⟩ : syracuseStep 997865 = 748399) B748399
theorem B735911 : Blo 171799 735911 := bstep (se 1 (by rfl) ⟨551933, by rfl⟩ : syracuseStep 735911 = 1103867) B1103867
theorem B277319 : Blo 171799 277319 := bstep (se 1 (by rfl) ⟨207989, by rfl⟩ : syracuseStep 277319 = 415979) B415979
theorem B932705 : Blo 171799 932705 := bstep (se 2 (by rfl) ⟨349764, by rfl⟩ : syracuseStep 932705 = 699529) B699529
theorem B900409 : Blo 171799 900409 := bstep (se 2 (by rfl) ⟨337653, by rfl⟩ : syracuseStep 900409 = 675307) B675307
theorem B1195343 : Blo 171799 1195343 := bstep (se 1 (by rfl) ⟨896507, by rfl⟩ : syracuseStep 1195343 = 1793015) B1793015
theorem B1327265 : Blo 171799 1327265 := bstep (se 2 (by rfl) ⟨497724, by rfl⟩ : syracuseStep 1327265 = 995449) B995449
theorem B1196221 : Blo 171799 1196221 := bstep (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) B448583
theorem B27313685 : Blo 171799 27313685 := bstep (se 6 (by rfl) ⟨640164, by rfl⟩ : syracuseStep 27313685 = 1280329) B1280329
theorem B4179563 : Blo 171799 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B4474601 : Blo 171799 4474601 := bstep (se 2 (by rfl) ⟨1677975, by rfl⟩ : syracuseStep 4474601 = 3355951) B3355951
theorem B5492423 : Blo 171799 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B708547 : Blo 171799 708547 := bstep (se 1 (by rfl) ⟨531410, by rfl⟩ : syracuseStep 708547 = 1062821) B1062821
theorem B1200271 : Blo 171799 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B2382143 : Blo 171799 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B579959 : Blo 171799 579959 := bstep (se 1 (by rfl) ⟨434969, by rfl⟩ : syracuseStep 579959 = 869939) B869939
theorem B1104353 : Blo 171799 1104353 := bstep (se 2 (by rfl) ⟨414132, by rfl⟩ : syracuseStep 1104353 = 828265) B828265
theorem B220639 : Blo 171799 220639 := bstep (se 1 (by rfl) ⟨165479, by rfl⟩ : syracuseStep 220639 = 330959) B330959
theorem B1106759 : Blo 171799 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B582497 : Blo 171799 582497 := bstep (se 2 (by rfl) ⟨218436, by rfl⟩ : syracuseStep 582497 = 436873) B436873
theorem B1108399 : Blo 171799 1108399 := bstep (se 1 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 1108399 = 1662599) B1662599
theorem B551357 : Blo 171799 551357 := bstep (se 3 (by rfl) ⟨103379, by rfl⟩ : syracuseStep 551357 = 206759) B206759
theorem B1961009 : Blo 171799 1961009 := bstep (se 2 (by rfl) ⟨735378, by rfl⟩ : syracuseStep 1961009 = 1470757) B1470757
theorem B388745 : Blo 171799 388745 := bstep (se 2 (by rfl) ⟨145779, by rfl⟩ : syracuseStep 388745 = 291559) B291559
theorem B585683 : Blo 171799 585683 := bstep (se 1 (by rfl) ⟨439262, by rfl⟩ : syracuseStep 585683 = 878525) B878525
theorem B16740391 : Blo 171799 16740391 := bstep (se 1 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 16740391 = 25110587) B25110587
theorem B258089 : Blo 171799 258089 := bstep (se 2 (by rfl) ⟨96783, by rfl⟩ : syracuseStep 258089 = 193567) B193567
theorem B389303 : Blo 171799 389303 := bstep (se 1 (by rfl) ⟨291977, by rfl⟩ : syracuseStep 389303 = 583955) B583955
theorem B586331 : Blo 171799 586331 := bstep (se 1 (by rfl) ⟨439748, by rfl⟩ : syracuseStep 586331 = 879497) B879497
theorem B586493 : Blo 171799 586493 := bstep (se 3 (by rfl) ⟨109967, by rfl⟩ : syracuseStep 586493 = 219935) B219935
theorem B259175 : Blo 171799 259175 := bstep (se 1 (by rfl) ⟨194381, by rfl⟩ : syracuseStep 259175 = 388763) B388763
theorem B390527 : Blo 171799 390527 := bstep (se 1 (by rfl) ⟨292895, by rfl⟩ : syracuseStep 390527 = 585791) B585791
theorem B259775 : Blo 171799 259775 := bstep (se 1 (by rfl) ⟨194831, by rfl⟩ : syracuseStep 259775 = 389663) B389663
theorem B391103 : Blo 171799 391103 := bstep (se 1 (by rfl) ⟨293327, by rfl⟩ : syracuseStep 391103 = 586655) B586655
theorem B293051 : Blo 171799 293051 := bstep (se 1 (by rfl) ⟨219788, by rfl⟩ : syracuseStep 293051 = 439577) B439577
theorem B1046839 : Blo 171799 1046839 := bstep (se 1 (by rfl) ⟨785129, by rfl⟩ : syracuseStep 1046839 = 1570259) B1570259
theorem B653791 : Blo 171799 653791 := bstep (se 1 (by rfl) ⟨490343, by rfl⟩ : syracuseStep 653791 = 980687) B980687
theorem B260927 : Blo 171799 260927 := bstep (se 1 (by rfl) ⟨195695, by rfl⟩ : syracuseStep 260927 = 391391) B391391
theorem B490367 : Blo 171799 490367 := bstep (se 1 (by rfl) ⟨367775, by rfl⟩ : syracuseStep 490367 = 735551) B735551
theorem B261113 : Blo 171799 261113 := bstep (se 2 (by rfl) ⟨97917, by rfl⟩ : syracuseStep 261113 = 195835) B195835
theorem B195583 : Blo 171799 195583 := bstep (se 1 (by rfl) ⟨146687, by rfl⟩ : syracuseStep 195583 = 293375) B293375
theorem B261359 : Blo 171799 261359 := bstep (se 1 (by rfl) ⟨196019, by rfl⟩ : syracuseStep 261359 = 392039) B392039
theorem B1965383 : Blo 171799 1965383 := bstep (se 1 (by rfl) ⟨1474037, by rfl⟩ : syracuseStep 1965383 = 2948075) B2948075
theorem B294367 : Blo 171799 294367 := bstep (se 1 (by rfl) ⟨220775, by rfl⟩ : syracuseStep 294367 = 441551) B441551
theorem B261851 : Blo 171799 261851 := bstep (se 1 (by rfl) ⟨196388, by rfl⟩ : syracuseStep 261851 = 392777) B392777
theorem B884843 : Blo 171799 884843 := bstep (se 1 (by rfl) ⟨663632, by rfl⟩ : syracuseStep 884843 = 1327265) B1327265
theorem B262427 : Blo 171799 262427 := bstep (se 1 (by rfl) ⟨196820, by rfl⟩ : syracuseStep 262427 = 393641) B393641
theorem B1573501 : Blo 171799 1573501 := bstep (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) B590063
theorem B590543 : Blo 171799 590543 := bstep (se 1 (by rfl) ⟨442907, by rfl⟩ : syracuseStep 590543 = 885815) B885815
theorem B2786375 : Blo 171799 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B394343 : Blo 171799 394343 := bstep (se 1 (by rfl) ⟨295757, by rfl⟩ : syracuseStep 394343 = 591515) B591515
theorem B394361 : Blo 171799 394361 := bstep (se 2 (by rfl) ⟨147885, by rfl⟩ : syracuseStep 394361 = 295771) B295771
theorem B2983067 : Blo 171799 2983067 := bstep (se 1 (by rfl) ⟨2237300, by rfl⟩ : syracuseStep 2983067 = 4474601) B4474601
theorem B329015 : Blo 171799 329015 := bstep (se 1 (by rfl) ⟨246761, by rfl⟩ : syracuseStep 329015 = 493523) B493523
theorem B657467 : Blo 171799 657467 := bstep (se 1 (by rfl) ⟨493100, by rfl⟩ : syracuseStep 657467 = 986201) B986201
theorem B395423 : Blo 171799 395423 := bstep (se 1 (by rfl) ⟨296567, by rfl⟩ : syracuseStep 395423 = 593135) B593135
theorem B1050947 : Blo 171799 1050947 := bstep (se 1 (by rfl) ⟨788210, by rfl⟩ : syracuseStep 1050947 = 1576421) B1576421
theorem B1477865 : Blo 171799 1477865 := bstep (se 2 (by rfl) ⟨554199, by rfl⟩ : syracuseStep 1477865 = 1108399) B1108399
theorem B1708199 : Blo 171799 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B22320521 : Blo 171799 22320521 := bstep (se 2 (by rfl) ⟨8370195, by rfl⟩ : syracuseStep 22320521 = 16740391) B16740391
theorem B367571 : Blo 171799 367571 := bstep (se 1 (by rfl) ⟨275678, by rfl⟩ : syracuseStep 367571 = 551357) B551357
theorem B629993 : Blo 171799 629993 := bstep (se 2 (by rfl) ⟨236247, by rfl⟩ : syracuseStep 629993 = 472495) B472495
theorem B368297 : Blo 171799 368297 := bstep (se 2 (by rfl) ⟨138111, by rfl⟩ : syracuseStep 368297 = 276223) B276223
theorem B172059 : Blo 171799 172059 := bstep (se 1 (by rfl) ⟨129044, by rfl⟩ : syracuseStep 172059 = 258089) B258089
theorem B369193 : Blo 171799 369193 := bstep (se 2 (by rfl) ⟨138447, by rfl⟩ : syracuseStep 369193 = 276895) B276895
theorem B172783 : Blo 171799 172783 := bstep (se 1 (by rfl) ⟨129587, by rfl⟩ : syracuseStep 172783 = 259175) B259175
theorem B173183 : Blo 171799 173183 := bstep (se 1 (by rfl) ⟨129887, by rfl⟩ : syracuseStep 173183 = 259775) B259775
theorem B1975589 : Blo 171799 1975589 := bstep (se 4 (by rfl) ⟨185211, by rfl⟩ : syracuseStep 1975589 = 370423) B370423
theorem B599359 : Blo 171799 599359 := bstep (se 1 (by rfl) ⟨449519, by rfl⟩ : syracuseStep 599359 = 899039) B899039
theorem B665243 : Blo 171799 665243 := bstep (se 1 (by rfl) ⟨498932, by rfl⟩ : syracuseStep 665243 = 997865) B997865
theorem B173951 : Blo 171799 173951 := bstep (se 1 (by rfl) ⟨130463, by rfl⟩ : syracuseStep 173951 = 260927) B260927
theorem B174075 : Blo 171799 174075 := bstep (se 1 (by rfl) ⟨130556, by rfl⟩ : syracuseStep 174075 = 261113) B261113
theorem B174239 : Blo 171799 174239 := bstep (se 1 (by rfl) ⟨130679, by rfl⟩ : syracuseStep 174239 = 261359) B261359
theorem B796895 : Blo 171799 796895 := bstep (se 1 (by rfl) ⟨597671, by rfl⟩ : syracuseStep 796895 = 1195343) B1195343
theorem B174567 : Blo 171799 174567 := bstep (se 1 (by rfl) ⟨130925, by rfl⟩ : syracuseStep 174567 = 261851) B261851
theorem B174879 : Blo 171799 174879 := bstep (se 1 (by rfl) ⟨131159, by rfl⟩ : syracuseStep 174879 = 262319) B262319
theorem B174911 : Blo 171799 174911 := bstep (se 1 (by rfl) ⟨131183, by rfl⟩ : syracuseStep 174911 = 262367) B262367
theorem B175087 : Blo 171799 175087 := bstep (se 1 (by rfl) ⟨131315, by rfl⟩ : syracuseStep 175087 = 262631) B262631
theorem B1193897 : Blo 171799 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B800765 : Blo 171799 800765 := bstep (se 3 (by rfl) ⟨150143, by rfl⟩ : syracuseStep 800765 = 300287) B300287
theorem B1325321 : Blo 171799 1325321 := bstep (se 2 (by rfl) ⟨496995, by rfl⟩ : syracuseStep 1325321 = 993991) B993991
theorem B375263 : Blo 171799 375263 := bstep (se 1 (by rfl) ⟨281447, by rfl⟩ : syracuseStep 375263 = 562895) B562895
theorem B736235 : Blo 171799 736235 := bstep (se 1 (by rfl) ⟨552176, by rfl⟩ : syracuseStep 736235 = 1104353) B1104353
theorem B11255759 : Blo 171799 11255759 := bstep (se 1 (by rfl) ⟨8441819, by rfl⟩ : syracuseStep 11255759 = 16883639) B16883639
theorem B12632111 : Blo 171799 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B901439 : Blo 171799 901439 := bstep (se 1 (by rfl) ⟨676079, by rfl⟩ : syracuseStep 901439 = 1352159) B1352159
theorem B737839 : Blo 171799 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B377903 : Blo 171799 377903 := bstep (se 1 (by rfl) ⟨283427, by rfl⟩ : syracuseStep 377903 = 566855) B566855
theorem B443951 : Blo 171799 443951 := bstep (se 1 (by rfl) ⟨332963, by rfl⟩ : syracuseStep 443951 = 665927) B665927
theorem B1395785 : Blo 171799 1395785 := bstep (se 2 (by rfl) ⟨523419, by rfl⟩ : syracuseStep 1395785 = 1046839) B1046839
theorem B871721 : Blo 171799 871721 := bstep (se 2 (by rfl) ⟨326895, by rfl⟩ : syracuseStep 871721 = 653791) B653791
theorem B708839 : Blo 171799 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B1200545 : Blo 171799 1200545 := bstep (se 2 (by rfl) ⟨450204, by rfl⟩ : syracuseStep 1200545 = 900409) B900409
theorem B184879 : Blo 171799 184879 := bstep (se 1 (by rfl) ⟨138659, by rfl⟩ : syracuseStep 184879 = 277319) B277319
theorem B1594961 : Blo 171799 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B940319 : Blo 171799 940319 := bstep (se 1 (by rfl) ⟨705239, by rfl⟩ : syracuseStep 940319 = 1410479) B1410479
theorem B1333583 : Blo 171799 1333583 := bstep (se 1 (by rfl) ⟨1000187, by rfl⟩ : syracuseStep 1333583 = 2000375) B2000375
theorem B18209123 : Blo 171799 18209123 := bstep (se 1 (by rfl) ⟨13656842, by rfl⟩ : syracuseStep 18209123 = 27313685) B27313685
theorem B3661615 : Blo 171799 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B221935 : Blo 171799 221935 := bstep (se 1 (by rfl) ⟨166451, by rfl⟩ : syracuseStep 221935 = 332903) B332903
theorem B386639 : Blo 171799 386639 := bstep (se 1 (by rfl) ⟨289979, by rfl⟩ : syracuseStep 386639 = 579959) B579959
theorem B944729 : Blo 171799 944729 := bstep (se 2 (by rfl) ⟨354273, by rfl⟩ : syracuseStep 944729 = 708547) B708547
theorem B1600361 : Blo 171799 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B388331 : Blo 171799 388331 := bstep (se 1 (by rfl) ⟨291248, by rfl⟩ : syracuseStep 388331 = 582497) B582497
theorem B6352381 : Blo 171799 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B10841951 : Blo 171799 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B1307339 : Blo 171799 1307339 := bstep (se 1 (by rfl) ⟨980504, by rfl⟩ : syracuseStep 1307339 = 1961009) B1961009
theorem B2978693 : Blo 171799 2978693 := bstep (se 4 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 2978693 = 558505) B558505
theorem B259163 : Blo 171799 259163 := bstep (se 1 (by rfl) ⟨194372, by rfl⟩ : syracuseStep 259163 = 388745) B388745
theorem B390455 : Blo 171799 390455 := bstep (se 1 (by rfl) ⟨292841, by rfl⟩ : syracuseStep 390455 = 585683) B585683
theorem B259535 : Blo 171799 259535 := bstep (se 1 (by rfl) ⟨194651, by rfl⟩ : syracuseStep 259535 = 389303) B389303
theorem B390887 : Blo 171799 390887 := bstep (se 1 (by rfl) ⟨293165, by rfl⟩ : syracuseStep 390887 = 586331) B586331
theorem B390995 : Blo 171799 390995 := bstep (se 1 (by rfl) ⟨293246, by rfl⟩ : syracuseStep 390995 = 586493) B586493
theorem B260351 : Blo 171799 260351 := bstep (se 1 (by rfl) ⟨195263, by rfl⟩ : syracuseStep 260351 = 390527) B390527
theorem B260735 : Blo 171799 260735 := bstep (se 1 (by rfl) ⟨195551, by rfl⟩ : syracuseStep 260735 = 391103) B391103
theorem B260777 : Blo 171799 260777 := bstep (se 2 (by rfl) ⟨97791, by rfl⟩ : syracuseStep 260777 = 195583) B195583
theorem B195367 : Blo 171799 195367 := bstep (se 1 (by rfl) ⟨146525, by rfl⟩ : syracuseStep 195367 = 293051) B293051
theorem B490607 : Blo 171799 490607 := bstep (se 1 (by rfl) ⟨367955, by rfl⟩ : syracuseStep 490607 = 735911) B735911
theorem B621803 : Blo 171799 621803 := bstep (se 1 (by rfl) ⟨466352, by rfl⟩ : syracuseStep 621803 = 932705) B932705
theorem B326911 : Blo 171799 326911 := bstep (se 1 (by rfl) ⟨245183, by rfl⟩ : syracuseStep 326911 = 490367) B490367
theorem B294185 : Blo 171799 294185 := bstep (se 2 (by rfl) ⟨110319, by rfl⟩ : syracuseStep 294185 = 220639) B220639
theorem B392489 : Blo 171799 392489 := bstep (se 2 (by rfl) ⟨147183, by rfl⟩ : syracuseStep 392489 = 294367) B294367
theorem B1408337 : Blo 171799 1408337 := bstep (se 2 (by rfl) ⟨528126, by rfl⟩ : syracuseStep 1408337 = 1056253) B1056253
theorem B1310255 : Blo 171799 1310255 := bstep (se 1 (by rfl) ⟨982691, by rfl⟩ : syracuseStep 1310255 = 1965383) B1965383
theorem B8421407 : Blo 171799 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B589895 : Blo 171799 589895 := bstep (se 1 (by rfl) ⟨442421, by rfl⟩ : syracuseStep 589895 = 884843) B884843
theorem B393695 : Blo 171799 393695 := bstep (se 1 (by rfl) ⟨295271, by rfl⟩ : syracuseStep 393695 = 590543) B590543
theorem B492257 : Blo 171799 492257 := bstep (se 2 (by rfl) ⟨184596, by rfl⟩ : syracuseStep 492257 = 369193) B369193
theorem B983785 : Blo 171799 983785 := bstep (se 2 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 983785 = 737839) B737839
theorem B262895 : Blo 171799 262895 := bstep (se 1 (by rfl) ⟨197171, by rfl⟩ : syracuseStep 262895 = 394343) B394343
theorem B262907 : Blo 171799 262907 := bstep (se 1 (by rfl) ⟨197180, by rfl⟩ : syracuseStep 262907 = 394361) B394361
theorem B2098001 : Blo 171799 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B295913 : Blo 171799 295913 := bstep (se 2 (by rfl) ⟨110967, by rfl⟩ : syracuseStep 295913 = 221935) B221935
theorem B295967 : Blo 171799 295967 := bstep (se 1 (by rfl) ⟨221975, by rfl⟩ : syracuseStep 295967 = 443951) B443951
theorem B263615 : Blo 171799 263615 := bstep (se 1 (by rfl) ⟨197711, by rfl⟩ : syracuseStep 263615 = 395423) B395423
theorem B985243 : Blo 171799 985243 := bstep (se 1 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 985243 = 1477865) B1477865
theorem B14880347 : Blo 171799 14880347 := bstep (se 1 (by rfl) ⟨11160260, by rfl⟩ : syracuseStep 14880347 = 22320521) B22320521
theorem B626879 : Blo 171799 626879 := bstep (se 1 (by rfl) ⟨470159, by rfl⟩ : syracuseStep 626879 = 940319) B940319
theorem B889055 : Blo 171799 889055 := bstep (se 1 (by rfl) ⟨666791, by rfl⟩ : syracuseStep 889055 = 1333583) B1333583
theorem B3183725 : Blo 171799 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B1317059 : Blo 171799 1317059 := bstep (se 1 (by rfl) ⟨987794, by rfl⟩ : syracuseStep 1317059 = 1975589) B1975589
theorem B531263 : Blo 171799 531263 := bstep (se 1 (by rfl) ⟨398447, by rfl⟩ : syracuseStep 531263 = 796895) B796895
theorem B629819 : Blo 171799 629819 := bstep (se 1 (by rfl) ⟨472364, by rfl⟩ : syracuseStep 629819 = 944729) B944729
theorem B172775 : Blo 171799 172775 := bstep (se 1 (by rfl) ⟨129581, by rfl⟩ : syracuseStep 172775 = 259163) B259163
theorem B173023 : Blo 171799 173023 := bstep (se 1 (by rfl) ⟨129767, by rfl⟩ : syracuseStep 173023 = 259535) B259535
theorem B533843 : Blo 171799 533843 := bstep (se 1 (by rfl) ⟨400382, by rfl⟩ : syracuseStep 533843 = 800765) B800765
theorem B173567 : Blo 171799 173567 := bstep (se 1 (by rfl) ⟨130175, by rfl⟩ : syracuseStep 173567 = 260351) B260351
theorem B435881 : Blo 171799 435881 := bstep (se 2 (by rfl) ⟨163455, by rfl⟩ : syracuseStep 435881 = 326911) B326911
theorem B173823 : Blo 171799 173823 := bstep (se 1 (by rfl) ⟨130367, by rfl⟩ : syracuseStep 173823 = 260735) B260735
theorem B173851 : Blo 171799 173851 := bstep (se 1 (by rfl) ⟨130388, by rfl⟩ : syracuseStep 173851 = 260777) B260777
theorem B174951 : Blo 171799 174951 := bstep (se 1 (by rfl) ⟨131213, by rfl⟩ : syracuseStep 174951 = 262427) B262427
theorem B600959 : Blo 171799 600959 := bstep (se 1 (by rfl) ⟨450719, by rfl⟩ : syracuseStep 600959 = 901439) B901439
theorem B438311 : Blo 171799 438311 := bstep (se 1 (by rfl) ⟨328733, by rfl⟩ : syracuseStep 438311 = 657467) B657467
theorem B700631 : Blo 171799 700631 := bstep (se 1 (by rfl) ⟨525473, by rfl⟩ : syracuseStep 700631 = 1050947) B1050947
theorem B799145 : Blo 171799 799145 := bstep (se 2 (by rfl) ⟨299679, by rfl⟩ : syracuseStep 799145 = 599359) B599359
theorem B930523 : Blo 171799 930523 := bstep (se 1 (by rfl) ⟨697892, by rfl⟩ : syracuseStep 930523 = 1395785) B1395785
theorem B472559 : Blo 171799 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B800363 : Blo 171799 800363 := bstep (se 1 (by rfl) ⟨600272, by rfl⟩ : syracuseStep 800363 = 1200545) B1200545
theorem B1063307 : Blo 171799 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B12139415 : Blo 171799 12139415 := bstep (se 1 (by rfl) ⟨9104561, by rfl⟩ : syracuseStep 12139415 = 18209123) B18209123
theorem B245047 : Blo 171799 245047 := bstep (se 1 (by rfl) ⟨183785, by rfl⟩ : syracuseStep 245047 = 367571) B367571
theorem B8469841 : Blo 171799 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B245531 : Blo 171799 245531 := bstep (se 1 (by rfl) ⟨184148, by rfl⟩ : syracuseStep 245531 = 368297) B368297
theorem B246505 : Blo 171799 246505 := bstep (se 2 (by rfl) ⟨92439, by rfl⟩ : syracuseStep 246505 = 184879) B184879
theorem B443495 : Blo 171799 443495 := bstep (se 1 (by rfl) ⟨332621, by rfl⟩ : syracuseStep 443495 = 665243) B665243
theorem B1066907 : Blo 171799 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B7227967 : Blo 171799 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B871559 : Blo 171799 871559 := bstep (se 1 (by rfl) ⟨653669, by rfl⟩ : syracuseStep 871559 = 1307339) B1307339
theorem B1985795 : Blo 171799 1985795 := bstep (se 1 (by rfl) ⟨1489346, by rfl⟩ : syracuseStep 1985795 = 2978693) B2978693
theorem B1658141 : Blo 171799 1658141 := bstep (se 3 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 1658141 = 621803) B621803
theorem B250175 : Blo 171799 250175 := bstep (se 1 (by rfl) ⟨187631, by rfl⟩ : syracuseStep 250175 = 375263) B375263
theorem B938891 : Blo 171799 938891 := bstep (se 1 (by rfl) ⟨704168, by rfl⟩ : syracuseStep 938891 = 1408337) B1408337
theorem B873503 : Blo 171799 873503 := bstep (se 1 (by rfl) ⟨655127, by rfl⟩ : syracuseStep 873503 = 1310255) B1310255
theorem B251935 : Blo 171799 251935 := bstep (se 1 (by rfl) ⟨188951, by rfl⟩ : syracuseStep 251935 = 377903) B377903
theorem B1857583 : Blo 171799 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B1988711 : Blo 171799 1988711 := bstep (se 1 (by rfl) ⟨1491533, by rfl⟩ : syracuseStep 1988711 = 2983067) B2983067
theorem B219343 : Blo 171799 219343 := bstep (se 1 (by rfl) ⟨164507, by rfl⟩ : syracuseStep 219343 = 329015) B329015
theorem B581147 : Blo 171799 581147 := bstep (se 1 (by rfl) ⟨435860, by rfl⟩ : syracuseStep 581147 = 871721) B871721
theorem B1138799 : Blo 171799 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B419995 : Blo 171799 419995 := bstep (se 1 (by rfl) ⟨314996, by rfl⟩ : syracuseStep 419995 = 629993) B629993
theorem B257759 : Blo 171799 257759 := bstep (se 1 (by rfl) ⟨193319, by rfl⟩ : syracuseStep 257759 = 386639) B386639
theorem B258887 : Blo 171799 258887 := bstep (se 1 (by rfl) ⟨194165, by rfl⟩ : syracuseStep 258887 = 388331) B388331
theorem B260303 : Blo 171799 260303 := bstep (se 1 (by rfl) ⟨195227, by rfl⟩ : syracuseStep 260303 = 390455) B390455
theorem B260489 : Blo 171799 260489 := bstep (se 2 (by rfl) ⟨97683, by rfl⟩ : syracuseStep 260489 = 195367) B195367
theorem B260591 : Blo 171799 260591 := bstep (se 1 (by rfl) ⟨195443, by rfl⟩ : syracuseStep 260591 = 390887) B390887
theorem B260663 : Blo 171799 260663 := bstep (se 1 (by rfl) ⟨195497, by rfl⟩ : syracuseStep 260663 = 390995) B390995
theorem B883547 : Blo 171799 883547 := bstep (se 1 (by rfl) ⟨662660, by rfl⟩ : syracuseStep 883547 = 1325321) B1325321
theorem B19528613 : Blo 171799 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B490823 : Blo 171799 490823 := bstep (se 1 (by rfl) ⟨368117, by rfl⟩ : syracuseStep 490823 = 736235) B736235
theorem B327071 : Blo 171799 327071 := bstep (se 1 (by rfl) ⟨245303, by rfl⟩ : syracuseStep 327071 = 490607) B490607
theorem B196123 : Blo 171799 196123 := bstep (se 1 (by rfl) ⟨147092, by rfl⟩ : syracuseStep 196123 = 294185) B294185
theorem B261659 : Blo 171799 261659 := bstep (se 1 (by rfl) ⟨196244, by rfl⟩ : syracuseStep 261659 = 392489) B392489
theorem B7503839 : Blo 171799 7503839 := bstep (se 1 (by rfl) ⟨5627879, by rfl⟩ : syracuseStep 7503839 = 11255759) B11255759
theorem B393263 : Blo 171799 393263 := bstep (se 1 (by rfl) ⟨294947, by rfl⟩ : syracuseStep 393263 = 589895) B589895
theorem B262463 : Blo 171799 262463 := bstep (se 1 (by rfl) ⟨196847, by rfl⟩ : syracuseStep 262463 = 393695) B393695
theorem B5374613 : Blo 171799 5374613 := bstep (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) B251935
theorem B197275 : Blo 171799 197275 := bstep (se 1 (by rfl) ⟨147956, by rfl⟩ : syracuseStep 197275 = 295913) B295913
theorem B197311 : Blo 171799 197311 := bstep (se 1 (by rfl) ⟨147983, by rfl⟩ : syracuseStep 197311 = 295967) B295967
theorem B295663 : Blo 171799 295663 := bstep (se 1 (by rfl) ⟨221747, by rfl⟩ : syracuseStep 295663 = 443495) B443495
theorem B1311713 : Blo 171799 1311713 := bstep (se 2 (by rfl) ⟨491892, by rfl⟩ : syracuseStep 1311713 = 983785) B983785
theorem B328673 : Blo 171799 328673 := bstep (se 2 (by rfl) ⟨123252, by rfl⟩ : syracuseStep 328673 = 246505) B246505
theorem B1312685 : Blo 171799 1312685 := bstep (se 3 (by rfl) ⟨246128, by rfl⟩ : syracuseStep 1312685 = 492257) B492257
theorem B592703 : Blo 171799 592703 := bstep (se 1 (by rfl) ⟨444527, by rfl⟩ : syracuseStep 592703 = 889055) B889055
theorem B1313657 : Blo 171799 1313657 := bstep (se 2 (by rfl) ⟨492621, by rfl⟩ : syracuseStep 1313657 = 985243) B985243
theorem B559993 : Blo 171799 559993 := bstep (se 2 (by rfl) ⟨209997, by rfl⟩ : syracuseStep 559993 = 419995) B419995
theorem B625927 : Blo 171799 625927 := bstep (se 1 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 625927 = 938891) B938891
theorem B9637289 : Blo 171799 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B400639 : Blo 171799 400639 := bstep (se 1 (by rfl) ⟨300479, by rfl⟩ : syracuseStep 400639 = 600959) B600959
theorem B1416701 : Blo 171799 1416701 := bstep (se 3 (by rfl) ⟨265631, by rfl⟩ : syracuseStep 1416701 = 531263) B531263
theorem B171839 : Blo 171799 171839 := bstep (se 1 (by rfl) ⟨128879, by rfl⟩ : syracuseStep 171839 = 257759) B257759
theorem B467087 : Blo 171799 467087 := bstep (se 1 (by rfl) ⟨350315, by rfl⟩ : syracuseStep 467087 = 700631) B700631
theorem B532763 : Blo 171799 532763 := bstep (se 1 (by rfl) ⟨399572, by rfl⟩ : syracuseStep 532763 = 799145) B799145
theorem B172591 : Blo 171799 172591 := bstep (se 1 (by rfl) ⟨129443, by rfl⟩ : syracuseStep 172591 = 258887) B258887
theorem B533575 : Blo 171799 533575 := bstep (se 1 (by rfl) ⟨400181, by rfl⟩ : syracuseStep 533575 = 800363) B800363
theorem B173535 : Blo 171799 173535 := bstep (se 1 (by rfl) ⟨130151, by rfl⟩ : syracuseStep 173535 = 260303) B260303
theorem B173659 : Blo 171799 173659 := bstep (se 1 (by rfl) ⟨130244, by rfl⟩ : syracuseStep 173659 = 260489) B260489
theorem B173727 : Blo 171799 173727 := bstep (se 1 (by rfl) ⟨130295, by rfl⟩ : syracuseStep 173727 = 260591) B260591
theorem B173775 : Blo 171799 173775 := bstep (se 1 (by rfl) ⟨130331, by rfl⟩ : syracuseStep 173775 = 260663) B260663
theorem B13019075 : Blo 171799 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B174439 : Blo 171799 174439 := bstep (se 1 (by rfl) ⟨130829, by rfl⟩ : syracuseStep 174439 = 261659) B261659
theorem B5614271 : Blo 171799 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B175263 : Blo 171799 175263 := bstep (se 1 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 175263 = 262895) B262895
theorem B175271 : Blo 171799 175271 := bstep (se 1 (by rfl) ⟨131453, by rfl⟩ : syracuseStep 175271 = 262907) B262907
theorem B667133 : Blo 171799 667133 := bstep (se 3 (by rfl) ⟨125087, by rfl⟩ : syracuseStep 667133 = 250175) B250175
theorem B175743 : Blo 171799 175743 := bstep (se 1 (by rfl) ⟨131807, by rfl⟩ : syracuseStep 175743 = 263615) B263615
theorem B1323863 : Blo 171799 1323863 := bstep (se 1 (by rfl) ⟨992897, by rfl⟩ : syracuseStep 1323863 = 1985795) B1985795
theorem B1260157 : Blo 171799 1260157 := bstep (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) B472559
theorem B1325807 : Blo 171799 1325807 := bstep (se 1 (by rfl) ⟨994355, by rfl⟩ : syracuseStep 1325807 = 1988711) B1988711
theorem B2804213 : Blo 171799 2804213 := bstep (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) B262895
theorem B2476777 : Blo 171799 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B708871 : Blo 171799 708871 := bstep (se 1 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 708871 = 1063307) B1063307
theorem B11293121 : Blo 171799 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B218047 : Blo 171799 218047 := bstep (se 1 (by rfl) ⟨163535, by rfl⟩ : syracuseStep 218047 = 327071) B327071
theorem B5002559 : Blo 171799 5002559 := bstep (se 1 (by rfl) ⟨3751919, by rfl⟩ : syracuseStep 5002559 = 7503839) B7503839
theorem B3036797 : Blo 171799 3036797 := bstep (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) B1138799
theorem B1398667 : Blo 171799 1398667 := bstep (se 1 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 1398667 = 2098001) B2098001
theorem B711271 : Blo 171799 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B581039 : Blo 171799 581039 := bstep (se 1 (by rfl) ⟨435779, by rfl⟩ : syracuseStep 581039 = 871559) B871559
theorem B1105427 : Blo 171799 1105427 := bstep (se 1 (by rfl) ⟨829070, by rfl⟩ : syracuseStep 1105427 = 1658141) B1658141
theorem B9920231 : Blo 171799 9920231 := bstep (se 1 (by rfl) ⟨7440173, by rfl⟩ : syracuseStep 9920231 = 14880347) B14880347
theorem B417919 : Blo 171799 417919 := bstep (se 1 (by rfl) ⟨313439, by rfl⟩ : syracuseStep 417919 = 626879) B626879
theorem B582335 : Blo 171799 582335 := bstep (se 1 (by rfl) ⟨436751, by rfl⟩ : syracuseStep 582335 = 873503) B873503
theorem B2122483 : Blo 171799 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B878039 : Blo 171799 878039 := bstep (se 1 (by rfl) ⟨658529, by rfl⟩ : syracuseStep 878039 = 1317059) B1317059
theorem B419879 : Blo 171799 419879 := bstep (se 1 (by rfl) ⟨314909, by rfl⟩ : syracuseStep 419879 = 629819) B629819
theorem B387431 : Blo 171799 387431 := bstep (se 1 (by rfl) ⟨290573, by rfl⟩ : syracuseStep 387431 = 581147) B581147
theorem B355895 : Blo 171799 355895 := bstep (se 1 (by rfl) ⟨266921, by rfl⟩ : syracuseStep 355895 = 533843) B533843
theorem B1240697 : Blo 171799 1240697 := bstep (se 2 (by rfl) ⟨465261, by rfl⟩ : syracuseStep 1240697 = 930523) B930523
theorem B290587 : Blo 171799 290587 := bstep (se 1 (by rfl) ⟨217940, by rfl⟩ : syracuseStep 290587 = 435881) B435881
theorem B292207 : Blo 171799 292207 := bstep (se 1 (by rfl) ⟨219155, by rfl⟩ : syracuseStep 292207 = 438311) B438311
theorem B292457 : Blo 171799 292457 := bstep (se 2 (by rfl) ⟨109671, by rfl⟩ : syracuseStep 292457 = 219343) B219343
theorem B326729 : Blo 171799 326729 := bstep (se 2 (by rfl) ⟨122523, by rfl⟩ : syracuseStep 326729 = 245047) B245047
theorem B589031 : Blo 171799 589031 := bstep (se 1 (by rfl) ⟨441773, by rfl⟩ : syracuseStep 589031 = 883547) B883547
theorem B8092943 : Blo 171799 8092943 := bstep (se 1 (by rfl) ⟨6069707, by rfl⟩ : syracuseStep 8092943 = 12139415) B12139415
theorem B261497 : Blo 171799 261497 := bstep (se 2 (by rfl) ⟨98061, by rfl⟩ : syracuseStep 261497 = 196123) B196123
theorem B654749 : Blo 171799 654749 := bstep (se 3 (by rfl) ⟨122765, by rfl⟩ : syracuseStep 654749 = 245531) B245531
theorem B327215 : Blo 171799 327215 := bstep (se 1 (by rfl) ⟨245411, by rfl⟩ : syracuseStep 327215 = 490823) B490823
theorem B262175 : Blo 171799 262175 := bstep (se 1 (by rfl) ⟨196631, by rfl⟩ : syracuseStep 262175 = 393263) B393263
theorem B557225 : Blo 171799 557225 := bstep (se 2 (by rfl) ⟨208959, by rfl⟩ : syracuseStep 557225 = 417919) B417919
theorem B1245565 : Blo 171799 1245565 := bstep (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) B467087
theorem B263033 : Blo 171799 263033 := bstep (se 2 (by rfl) ⟨98637, by rfl⟩ : syracuseStep 263033 = 197275) B197275
theorem B263081 : Blo 171799 263081 := bstep (se 2 (by rfl) ⟨98655, by rfl⟩ : syracuseStep 263081 = 197311) B197311
theorem B394217 : Blo 171799 394217 := bstep (se 2 (by rfl) ⟨147831, by rfl⟩ : syracuseStep 394217 = 295663) B295663
theorem B1869475 : Blo 171799 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B395135 : Blo 171799 395135 := bstep (se 1 (by rfl) ⟨296351, by rfl⟩ : syracuseStep 395135 = 592703) B592703
theorem B6424859 : Blo 171799 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B3742847 : Blo 171799 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B237263 : Blo 171799 237263 := bstep (se 1 (by rfl) ⟨177947, by rfl⟩ : syracuseStep 237263 = 355895) B355895
theorem B827131 : Blo 171799 827131 := bstep (se 1 (by rfl) ⟨620348, by rfl⟩ : syracuseStep 827131 = 1240697) B1240697
theorem B1680209 : Blo 171799 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B534185 : Blo 171799 534185 := bstep (se 2 (by rfl) ⟨200319, by rfl⟩ : syracuseStep 534185 = 400639) B400639
theorem B174331 : Blo 171799 174331 := bstep (se 1 (by rfl) ⟨130748, by rfl⟩ : syracuseStep 174331 = 261497) B261497
theorem B436499 : Blo 171799 436499 := bstep (se 1 (by rfl) ⟨327374, by rfl⟩ : syracuseStep 436499 = 654749) B654749
theorem B174975 : Blo 171799 174975 := bstep (se 1 (by rfl) ⟨131231, by rfl⟩ : syracuseStep 174975 = 262463) B262463
theorem B2829977 : Blo 171799 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B14332301 : Blo 171799 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B834569 : Blo 171799 834569 := bstep (se 2 (by rfl) ⟨312963, by rfl⟩ : syracuseStep 834569 = 625927) B625927
theorem B736951 : Blo 171799 736951 := bstep (se 1 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 736951 = 1105427) B1105427
theorem B279919 : Blo 171799 279919 := bstep (se 1 (by rfl) ⟨209939, by rfl⟩ : syracuseStep 279919 = 419879) B419879
theorem B444755 : Blo 171799 444755 := bstep (se 1 (by rfl) ⟨333566, by rfl⟩ : syracuseStep 444755 = 667133) B667133
theorem B217819 : Blo 171799 217819 := bstep (se 1 (by rfl) ⟨163364, by rfl⟩ : syracuseStep 217819 = 326729) B326729
theorem B5395295 : Blo 171799 5395295 := bstep (se 1 (by rfl) ⟨4046471, by rfl⟩ : syracuseStep 5395295 = 8092943) B8092943
theorem B218143 : Blo 171799 218143 := bstep (se 1 (by rfl) ⟨163607, by rfl⟩ : syracuseStep 218143 = 327215) B327215
theorem B874475 : Blo 171799 874475 := bstep (se 1 (by rfl) ⟨655856, by rfl⟩ : syracuseStep 874475 = 1311713) B1311713
theorem B219115 : Blo 171799 219115 := bstep (se 1 (by rfl) ⟨164336, by rfl⟩ : syracuseStep 219115 = 328673) B328673
theorem B875123 : Blo 171799 875123 := bstep (se 1 (by rfl) ⟨656342, by rfl⟩ : syracuseStep 875123 = 1312685) B1312685
theorem B711433 : Blo 171799 711433 := bstep (se 2 (by rfl) ⟨266787, by rfl⟩ : syracuseStep 711433 = 533575) B533575
theorem B875771 : Blo 171799 875771 := bstep (se 1 (by rfl) ⟨656828, by rfl⟩ : syracuseStep 875771 = 1313657) B1313657
theorem B7528747 : Blo 171799 7528747 := bstep (se 1 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 7528747 = 11293121) B11293121
theorem B3335039 : Blo 171799 3335039 := bstep (se 1 (by rfl) ⟨2501279, by rfl⟩ : syracuseStep 3335039 = 5002559) B5002559
theorem B3302369 : Blo 171799 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B2024531 : Blo 171799 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B746657 : Blo 171799 746657 := bstep (se 2 (by rfl) ⟨279996, by rfl⟩ : syracuseStep 746657 = 559993) B559993
theorem B387359 : Blo 171799 387359 := bstep (se 1 (by rfl) ⟨290519, by rfl⟩ : syracuseStep 387359 = 581039) B581039
theorem B944467 : Blo 171799 944467 := bstep (se 1 (by rfl) ⟨708350, by rfl⟩ : syracuseStep 944467 = 1416701) B1416701
theorem B387449 : Blo 171799 387449 := bstep (se 2 (by rfl) ⟨145293, by rfl⟩ : syracuseStep 387449 = 290587) B290587
theorem B6613487 : Blo 171799 6613487 := bstep (se 1 (by rfl) ⟨4960115, by rfl⟩ : syracuseStep 6613487 = 9920231) B9920231
theorem B355175 : Blo 171799 355175 := bstep (se 1 (by rfl) ⟨266381, by rfl⟩ : syracuseStep 355175 = 532763) B532763
theorem B945161 : Blo 171799 945161 := bstep (se 2 (by rfl) ⟨354435, by rfl⟩ : syracuseStep 945161 = 708871) B708871
theorem B388223 : Blo 171799 388223 := bstep (se 1 (by rfl) ⟨291167, by rfl⟩ : syracuseStep 388223 = 582335) B582335
theorem B585359 : Blo 171799 585359 := bstep (se 1 (by rfl) ⟨439019, by rfl⟩ : syracuseStep 585359 = 878039) B878039
theorem B290729 : Blo 171799 290729 := bstep (se 2 (by rfl) ⟨109023, by rfl⟩ : syracuseStep 290729 = 218047) B218047
theorem B8679383 : Blo 171799 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B258287 : Blo 171799 258287 := bstep (se 1 (by rfl) ⟨193715, by rfl⟩ : syracuseStep 258287 = 387431) B387431
theorem B389609 : Blo 171799 389609 := bstep (se 2 (by rfl) ⟨146103, by rfl⟩ : syracuseStep 389609 = 292207) B292207
theorem B1864889 : Blo 171799 1864889 := bstep (se 2 (by rfl) ⟨699333, by rfl⟩ : syracuseStep 1864889 = 1398667) B1398667
theorem B882575 : Blo 171799 882575 := bstep (se 1 (by rfl) ⟨661931, by rfl⟩ : syracuseStep 882575 = 1323863) B1323863
theorem B948361 : Blo 171799 948361 := bstep (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) B711271
theorem B194971 : Blo 171799 194971 := bstep (se 1 (by rfl) ⟨146228, by rfl⟩ : syracuseStep 194971 = 292457) B292457
theorem B883871 : Blo 171799 883871 := bstep (se 1 (by rfl) ⟨662903, by rfl⟩ : syracuseStep 883871 = 1325807) B1325807
theorem B392687 : Blo 171799 392687 := bstep (se 1 (by rfl) ⟨294515, by rfl⟩ : syracuseStep 392687 = 589031) B589031
theorem B262811 : Blo 171799 262811 := bstep (se 1 (by rfl) ⟨197108, by rfl⟩ : syracuseStep 262811 = 394217) B394217
theorem B263423 : Blo 171799 263423 := bstep (se 1 (by rfl) ⟨197567, by rfl⟩ : syracuseStep 263423 = 395135) B395135
theorem B296503 : Blo 171799 296503 := bstep (se 1 (by rfl) ⟨222377, by rfl⟩ : syracuseStep 296503 = 444755) B444755
theorem B2492633 : Blo 171799 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B14387453 : Blo 171799 14387453 := bstep (se 3 (by rfl) ⟨2697647, by rfl⟩ : syracuseStep 14387453 = 5395295) B5395295
theorem B2495231 : Blo 171799 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B1120139 : Blo 171799 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B2201579 : Blo 171799 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B1349687 : Blo 171799 1349687 := bstep (se 1 (by rfl) ⟨1012265, by rfl⟩ : syracuseStep 1349687 = 2024531) B2024531
theorem B497771 : Blo 171799 497771 := bstep (se 1 (by rfl) ⟨373328, by rfl⟩ : syracuseStep 497771 = 746657) B746657
theorem B236783 : Blo 171799 236783 := bstep (se 1 (by rfl) ⟨177587, by rfl⟩ : syracuseStep 236783 = 355175) B355175
theorem B630107 : Blo 171799 630107 := bstep (se 1 (by rfl) ⟨472580, by rfl⟩ : syracuseStep 630107 = 945161) B945161
theorem B172191 : Blo 171799 172191 := bstep (se 1 (by rfl) ⟨129143, by rfl⟩ : syracuseStep 172191 = 258287) B258287
theorem B632701 : Blo 171799 632701 := bstep (se 3 (by rfl) ⟨118631, by rfl⟩ : syracuseStep 632701 = 237263) B237263
theorem B174783 : Blo 171799 174783 := bstep (se 1 (by rfl) ⟨131087, by rfl⟩ : syracuseStep 174783 = 262175) B262175
theorem B371483 : Blo 171799 371483 := bstep (se 1 (by rfl) ⟨278612, by rfl⟩ : syracuseStep 371483 = 557225) B557225
theorem B10038329 : Blo 171799 10038329 := bstep (se 2 (by rfl) ⟨3764373, by rfl⟩ : syracuseStep 10038329 = 7528747) B7528747
theorem B175355 : Blo 171799 175355 := bstep (se 1 (by rfl) ⟨131516, by rfl⟩ : syracuseStep 175355 = 263033) B263033
theorem B175387 : Blo 171799 175387 := bstep (se 1 (by rfl) ⟨131540, by rfl⟩ : syracuseStep 175387 = 263081) B263081
theorem B4408991 : Blo 171799 4408991 := bstep (se 1 (by rfl) ⟨3306743, by rfl⟩ : syracuseStep 4408991 = 6613487) B6613487
theorem B1492901 : Blo 171799 1492901 := bstep (se 4 (by rfl) ⟨139959, by rfl⟩ : syracuseStep 1492901 = 279919) B279919
theorem B1886651 : Blo 171799 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B5786255 : Blo 171799 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B1264481 : Blo 171799 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B9554867 : Blo 171799 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B1102841 : Blo 171799 1102841 := bstep (se 2 (by rfl) ⟨413565, by rfl⟩ : syracuseStep 1102841 = 827131) B827131
theorem B1660753 : Blo 171799 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B4283239 : Blo 171799 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B5037157 : Blo 171799 5037157 := bstep (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) B944467
theorem B582983 : Blo 171799 582983 := bstep (se 1 (by rfl) ⟨437237, by rfl⟩ : syracuseStep 582983 = 874475) B874475
theorem B3794309 : Blo 171799 3794309 := bstep (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) B711433
theorem B583415 : Blo 171799 583415 := bstep (se 1 (by rfl) ⟨437561, by rfl⟩ : syracuseStep 583415 = 875123) B875123
theorem B583847 : Blo 171799 583847 := bstep (se 1 (by rfl) ⟨437885, by rfl⟩ : syracuseStep 583847 = 875771) B875771
theorem B2223359 : Blo 171799 2223359 := bstep (se 1 (by rfl) ⟨1667519, by rfl⟩ : syracuseStep 2223359 = 3335039) B3335039
theorem B290425 : Blo 171799 290425 := bstep (se 2 (by rfl) ⟨108909, by rfl⟩ : syracuseStep 290425 = 217819) B217819
theorem B356123 : Blo 171799 356123 := bstep (se 1 (by rfl) ⟨267092, by rfl⟩ : syracuseStep 356123 = 534185) B534185
theorem B290857 : Blo 171799 290857 := bstep (se 2 (by rfl) ⟨109071, by rfl⟩ : syracuseStep 290857 = 218143) B218143
theorem B290999 : Blo 171799 290999 := bstep (se 1 (by rfl) ⟨218249, by rfl⟩ : syracuseStep 290999 = 436499) B436499
theorem B258239 : Blo 171799 258239 := bstep (se 1 (by rfl) ⟨193679, by rfl⟩ : syracuseStep 258239 = 387359) B387359
theorem B258299 : Blo 171799 258299 := bstep (se 1 (by rfl) ⟨193724, by rfl⟩ : syracuseStep 258299 = 387449) B387449
theorem B258815 : Blo 171799 258815 := bstep (se 1 (by rfl) ⟨194111, by rfl⟩ : syracuseStep 258815 = 388223) B388223
theorem B390239 : Blo 171799 390239 := bstep (se 1 (by rfl) ⟨292679, by rfl⟩ : syracuseStep 390239 = 585359) B585359
theorem B193819 : Blo 171799 193819 := bstep (se 1 (by rfl) ⟨145364, by rfl⟩ : syracuseStep 193819 = 290729) B290729
theorem B292153 : Blo 171799 292153 := bstep (se 2 (by rfl) ⟨109557, by rfl⟩ : syracuseStep 292153 = 219115) B219115
theorem B259739 : Blo 171799 259739 := bstep (se 1 (by rfl) ⟨194804, by rfl⟩ : syracuseStep 259739 = 389609) B389609
theorem B259961 : Blo 171799 259961 := bstep (se 2 (by rfl) ⟨97485, by rfl⟩ : syracuseStep 259961 = 194971) B194971
theorem B1243259 : Blo 171799 1243259 := bstep (se 1 (by rfl) ⟨932444, by rfl⟩ : syracuseStep 1243259 = 1864889) B1864889
theorem B588383 : Blo 171799 588383 := bstep (se 1 (by rfl) ⟨441287, by rfl⟩ : syracuseStep 588383 = 882575) B882575
theorem B556379 : Blo 171799 556379 := bstep (se 1 (by rfl) ⟨417284, by rfl⟩ : syracuseStep 556379 = 834569) B834569
theorem B589247 : Blo 171799 589247 := bstep (se 1 (by rfl) ⟨441935, by rfl⟩ : syracuseStep 589247 = 883871) B883871
theorem B982601 : Blo 171799 982601 := bstep (se 2 (by rfl) ⟨368475, by rfl⟩ : syracuseStep 982601 = 736951) B736951
theorem B261791 : Blo 171799 261791 := bstep (se 1 (by rfl) ⟨196343, by rfl⟩ : syracuseStep 261791 = 392687) B392687
theorem B6325397 : Blo 171799 6325397 := bstep (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) B296503
theorem B331847 : Blo 171799 331847 := bstep (se 1 (by rfl) ⟨248885, by rfl⟩ : syracuseStep 331847 = 497771) B497771
theorem B2529539 : Blo 171799 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B6692219 : Blo 171799 6692219 := bstep (se 1 (by rfl) ⟨5019164, by rfl⟩ : syracuseStep 6692219 = 10038329) B10038329
theorem B1482239 : Blo 171799 1482239 := bstep (se 1 (by rfl) ⟨1111679, by rfl⟩ : syracuseStep 1482239 = 2223359) B2223359
theorem B237415 : Blo 171799 237415 := bstep (se 1 (by rfl) ⟨178061, by rfl⟩ : syracuseStep 237415 = 356123) B356123
theorem B172159 : Blo 171799 172159 := bstep (se 1 (by rfl) ⟨129119, by rfl⟩ : syracuseStep 172159 = 258239) B258239
theorem B172199 : Blo 171799 172199 := bstep (se 1 (by rfl) ⟨129149, by rfl⟩ : syracuseStep 172199 = 258299) B258299
theorem B172543 : Blo 171799 172543 := bstep (se 1 (by rfl) ⟨129407, by rfl⟩ : syracuseStep 172543 = 258815) B258815
theorem B631421 : Blo 171799 631421 := bstep (se 3 (by rfl) ⟨118391, by rfl⟩ : syracuseStep 631421 = 236783) B236783
theorem B173159 : Blo 171799 173159 := bstep (se 1 (by rfl) ⟨129869, by rfl⟩ : syracuseStep 173159 = 259739) B259739
theorem B5710985 : Blo 171799 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B173307 : Blo 171799 173307 := bstep (se 1 (by rfl) ⟨129980, by rfl⟩ : syracuseStep 173307 = 259961) B259961
theorem B828839 : Blo 171799 828839 := bstep (se 1 (by rfl) ⟨621629, by rfl⟩ : syracuseStep 828839 = 1243259) B1243259
theorem B370919 : Blo 171799 370919 := bstep (se 1 (by rfl) ⟨278189, by rfl⟩ : syracuseStep 370919 = 556379) B556379
theorem B174527 : Blo 171799 174527 := bstep (se 1 (by rfl) ⟨130895, by rfl⟩ : syracuseStep 174527 = 261791) B261791
theorem B175207 : Blo 171799 175207 := bstep (se 1 (by rfl) ⟨131405, by rfl⟩ : syracuseStep 175207 = 262811) B262811
theorem B175615 : Blo 171799 175615 := bstep (se 1 (by rfl) ⟨131711, by rfl⟩ : syracuseStep 175615 = 263423) B263423
theorem B995267 : Blo 171799 995267 := bstep (se 1 (by rfl) ⟨746450, by rfl⟩ : syracuseStep 995267 = 1492901) B1492901
theorem B1257767 : Blo 171799 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B6369911 : Blo 171799 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B735227 : Blo 171799 735227 := bstep (se 1 (by rfl) ⟨551420, by rfl⟩ : syracuseStep 735227 = 1102841) B1102841
theorem B899791 : Blo 171799 899791 := bstep (se 1 (by rfl) ⟨674843, by rfl⟩ : syracuseStep 899791 = 1349687) B1349687
theorem B247655 : Blo 171799 247655 := bstep (se 1 (by rfl) ⟨185741, by rfl⟩ : syracuseStep 247655 = 371483) B371483
theorem B2214337 : Blo 171799 2214337 := bstep (se 2 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 2214337 = 1660753) B1660753
theorem B2939327 : Blo 171799 2939327 := bstep (se 1 (by rfl) ⟨2204495, by rfl⟩ : syracuseStep 2939327 = 4408991) B4408991
theorem B1661755 : Blo 171799 1661755 := bstep (se 1 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 1661755 = 2492633) B2492633
theorem B9591635 : Blo 171799 9591635 := bstep (se 1 (by rfl) ⟨7193726, by rfl⟩ : syracuseStep 9591635 = 14387453) B14387453
theorem B3857503 : Blo 171799 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B842987 : Blo 171799 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B1663487 : Blo 171799 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B746759 : Blo 171799 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B1467719 : Blo 171799 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B387233 : Blo 171799 387233 := bstep (se 2 (by rfl) ⟨145212, by rfl⟩ : syracuseStep 387233 = 290425) B290425
theorem B420071 : Blo 171799 420071 := bstep (se 1 (by rfl) ⟨315053, by rfl⟩ : syracuseStep 420071 = 630107) B630107
theorem B387809 : Blo 171799 387809 := bstep (se 2 (by rfl) ⟨145428, by rfl⟩ : syracuseStep 387809 = 290857) B290857
theorem B388655 : Blo 171799 388655 := bstep (se 1 (by rfl) ⟨291491, by rfl⟩ : syracuseStep 388655 = 582983) B582983
theorem B388943 : Blo 171799 388943 := bstep (se 1 (by rfl) ⟨291707, by rfl⟩ : syracuseStep 388943 = 583415) B583415
theorem B389231 : Blo 171799 389231 := bstep (se 1 (by rfl) ⟨291923, by rfl⟩ : syracuseStep 389231 = 583847) B583847
theorem B258425 : Blo 171799 258425 := bstep (se 2 (by rfl) ⟨96909, by rfl⟩ : syracuseStep 258425 = 193819) B193819
theorem B389537 : Blo 171799 389537 := bstep (se 2 (by rfl) ⟨146076, by rfl⟩ : syracuseStep 389537 = 292153) B292153
theorem B193999 : Blo 171799 193999 := bstep (se 1 (by rfl) ⟨145499, by rfl⟩ : syracuseStep 193999 = 290999) B290999
theorem B260159 : Blo 171799 260159 := bstep (se 1 (by rfl) ⟨195119, by rfl⟩ : syracuseStep 260159 = 390239) B390239
theorem B6716209 : Blo 171799 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B392255 : Blo 171799 392255 := bstep (se 1 (by rfl) ⟨294191, by rfl⟩ : syracuseStep 392255 = 588383) B588383
theorem B3374405 : Blo 171799 3374405 := bstep (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) B632701
theorem B392831 : Blo 171799 392831 := bstep (se 1 (by rfl) ⟨294623, by rfl⟩ : syracuseStep 392831 = 589247) B589247
theorem B655067 : Blo 171799 655067 := bstep (se 1 (by rfl) ⟨491300, by rfl⟩ : syracuseStep 655067 = 982601) B982601
theorem B2952449 : Blo 171799 2952449 := bstep (se 2 (by rfl) ⟨1107168, by rfl⟩ : syracuseStep 2952449 = 2214337) B2214337
theorem B6394423 : Blo 171799 6394423 := bstep (se 1 (by rfl) ⟨4795817, by rfl⟩ : syracuseStep 6394423 = 9591635) B9591635
theorem B561991 : Blo 171799 561991 := bstep (se 1 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 561991 = 842987) B842987
theorem B4461479 : Blo 171799 4461479 := bstep (se 1 (by rfl) ⟨3346109, by rfl⟩ : syracuseStep 4461479 = 6692219) B6692219
theorem B660413 : Blo 171799 660413 := bstep (se 3 (by rfl) ⟨123827, by rfl⟩ : syracuseStep 660413 = 247655) B247655
theorem B988159 : Blo 171799 988159 := bstep (se 1 (by rfl) ⟨741119, by rfl⟩ : syracuseStep 988159 = 1482239) B1482239
theorem B989117 : Blo 171799 989117 := bstep (se 3 (by rfl) ⟨185459, by rfl⟩ : syracuseStep 989117 = 370919) B370919
theorem B1120189 : Blo 171799 1120189 := bstep (se 3 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 1120189 = 420071) B420071
theorem B3807323 : Blo 171799 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B497839 : Blo 171799 497839 := bstep (se 1 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 497839 = 746759) B746759
theorem B663511 : Blo 171799 663511 := bstep (se 1 (by rfl) ⟨497633, by rfl⟩ : syracuseStep 663511 = 995267) B995267
theorem B172283 : Blo 171799 172283 := bstep (se 1 (by rfl) ⟨129212, by rfl⟩ : syracuseStep 172283 = 258425) B258425
theorem B8954945 : Blo 171799 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B173439 : Blo 171799 173439 := bstep (se 1 (by rfl) ⟨130079, by rfl⟩ : syracuseStep 173439 = 260159) B260159
theorem B436711 : Blo 171799 436711 := bstep (se 1 (by rfl) ⟨327533, by rfl⟩ : syracuseStep 436711 = 655067) B655067
theorem B2210237 : Blo 171799 2210237 := bstep (se 3 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 2210237 = 828839) B828839
theorem B1686359 : Blo 171799 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B838511 : Blo 171799 838511 := bstep (se 1 (by rfl) ⟨628883, by rfl⟩ : syracuseStep 838511 = 1257767) B1257767
theorem B4246607 : Blo 171799 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B2215673 : Blo 171799 2215673 := bstep (se 2 (by rfl) ⟨830877, by rfl⟩ : syracuseStep 2215673 = 1661755) B1661755
theorem B2249603 : Blo 171799 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B316553 : Blo 171799 316553 := bstep (se 2 (by rfl) ⟨118707, by rfl⟩ : syracuseStep 316553 = 237415) B237415
theorem B4216931 : Blo 171799 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B221231 : Blo 171799 221231 := bstep (se 1 (by rfl) ⟨165923, by rfl⟩ : syracuseStep 221231 = 331847) B331847
theorem B1959551 : Blo 171799 1959551 := bstep (se 1 (by rfl) ⟨1469663, by rfl⟩ : syracuseStep 1959551 = 2939327) B2939327
theorem B19195541 : Blo 171799 19195541 := bstep (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) B899791
theorem B1108991 : Blo 171799 1108991 := bstep (se 1 (by rfl) ⟨831743, by rfl⟩ : syracuseStep 1108991 = 1663487) B1663487
theorem B420947 : Blo 171799 420947 := bstep (se 1 (by rfl) ⟨315710, by rfl⟩ : syracuseStep 420947 = 631421) B631421
theorem B978479 : Blo 171799 978479 := bstep (se 1 (by rfl) ⟨733859, by rfl⟩ : syracuseStep 978479 = 1467719) B1467719
theorem B258155 : Blo 171799 258155 := bstep (se 1 (by rfl) ⟨193616, by rfl⟩ : syracuseStep 258155 = 387233) B387233
theorem B258539 : Blo 171799 258539 := bstep (se 1 (by rfl) ⟨193904, by rfl⟩ : syracuseStep 258539 = 387809) B387809
theorem B258665 : Blo 171799 258665 := bstep (se 2 (by rfl) ⟨96999, by rfl⟩ : syracuseStep 258665 = 193999) B193999
theorem B259103 : Blo 171799 259103 := bstep (se 1 (by rfl) ⟨194327, by rfl⟩ : syracuseStep 259103 = 388655) B388655
theorem B259295 : Blo 171799 259295 := bstep (se 1 (by rfl) ⟨194471, by rfl⟩ : syracuseStep 259295 = 388943) B388943
theorem B259487 : Blo 171799 259487 := bstep (se 1 (by rfl) ⟨194615, by rfl⟩ : syracuseStep 259487 = 389231) B389231
theorem B259691 : Blo 171799 259691 := bstep (se 1 (by rfl) ⟨194768, by rfl⟩ : syracuseStep 259691 = 389537) B389537
theorem B490151 : Blo 171799 490151 := bstep (se 1 (by rfl) ⟨367613, by rfl⟩ : syracuseStep 490151 = 735227) B735227
theorem B5143337 : Blo 171799 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B261503 : Blo 171799 261503 := bstep (se 1 (by rfl) ⟨196127, by rfl⟩ : syracuseStep 261503 = 392255) B392255
theorem B261887 : Blo 171799 261887 := bstep (se 1 (by rfl) ⟨196415, by rfl⟩ : syracuseStep 261887 = 392831) B392831
theorem B589949 : Blo 171799 589949 := bstep (se 3 (by rfl) ⟨110615, by rfl⟩ : syracuseStep 589949 = 221231) B221231
theorem B559007 : Blo 171799 559007 := bstep (se 1 (by rfl) ⟨419255, by rfl⟩ : syracuseStep 559007 = 838511) B838511
theorem B1968299 : Blo 171799 1968299 := bstep (se 1 (by rfl) ⟨1476224, by rfl⟩ : syracuseStep 1968299 = 2952449) B2952449
theorem B1477115 : Blo 171799 1477115 := bstep (se 1 (by rfl) ⟨1107836, by rfl⟩ : syracuseStep 1477115 = 2215673) B2215673
theorem B659411 : Blo 171799 659411 := bstep (se 1 (by rfl) ⟨494558, by rfl⟩ : syracuseStep 659411 = 989117) B989117
theorem B5969963 : Blo 171799 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B8525897 : Blo 171799 8525897 := bstep (se 2 (by rfl) ⟨3197211, by rfl⟩ : syracuseStep 8525897 = 6394423) B6394423
theorem B1317545 : Blo 171799 1317545 := bstep (se 2 (by rfl) ⟨494079, by rfl⟩ : syracuseStep 1317545 = 988159) B988159
theorem B172103 : Blo 171799 172103 := bstep (se 1 (by rfl) ⟨129077, by rfl⟩ : syracuseStep 172103 = 258155) B258155
theorem B663785 : Blo 171799 663785 := bstep (se 2 (by rfl) ⟨248919, by rfl⟩ : syracuseStep 663785 = 497839) B497839
theorem B172359 : Blo 171799 172359 := bstep (se 1 (by rfl) ⟨129269, by rfl⟩ : syracuseStep 172359 = 258539) B258539
theorem B172443 : Blo 171799 172443 := bstep (se 1 (by rfl) ⟨129332, by rfl⟩ : syracuseStep 172443 = 258665) B258665
theorem B172735 : Blo 171799 172735 := bstep (se 1 (by rfl) ⟨129551, by rfl⟩ : syracuseStep 172735 = 259103) B259103
theorem B172863 : Blo 171799 172863 := bstep (se 1 (by rfl) ⟨129647, by rfl⟩ : syracuseStep 172863 = 259295) B259295
theorem B172991 : Blo 171799 172991 := bstep (se 1 (by rfl) ⟨129743, by rfl⟩ : syracuseStep 172991 = 259487) B259487
theorem B173127 : Blo 171799 173127 := bstep (se 1 (by rfl) ⟨129845, by rfl⟩ : syracuseStep 173127 = 259691) B259691
theorem B1124239 : Blo 171799 1124239 := bstep (se 1 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 1124239 = 1686359) B1686359
theorem B174335 : Blo 171799 174335 := bstep (se 1 (by rfl) ⟨130751, by rfl⟩ : syracuseStep 174335 = 261503) B261503
theorem B174591 : Blo 171799 174591 := bstep (se 1 (by rfl) ⟨130943, by rfl⟩ : syracuseStep 174591 = 261887) B261887
theorem B2831071 : Blo 171799 2831071 := bstep (se 1 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 2831071 = 4246607) B4246607
theorem B440275 : Blo 171799 440275 := bstep (se 1 (by rfl) ⟨330206, by rfl⟩ : syracuseStep 440275 = 660413) B660413
theorem B2538215 : Blo 171799 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B12797027 : Blo 171799 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B739327 : Blo 171799 739327 := bstep (se 1 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 739327 = 1108991) B1108991
theorem B280631 : Blo 171799 280631 := bstep (se 1 (by rfl) ⟨210473, by rfl⟩ : syracuseStep 280631 = 420947) B420947
theorem B1493585 : Blo 171799 1493585 := bstep (se 2 (by rfl) ⟨560094, by rfl⟩ : syracuseStep 1493585 = 1120189) B1120189
theorem B3428891 : Blo 171799 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B844141 : Blo 171799 844141 := bstep (se 3 (by rfl) ⟨158276, by rfl⟩ : syracuseStep 844141 = 316553) B316553
theorem B1499735 : Blo 171799 1499735 := bstep (se 1 (by rfl) ⟨1124801, by rfl⟩ : syracuseStep 1499735 = 2249603) B2249603
theorem B2974319 : Blo 171799 2974319 := bstep (se 1 (by rfl) ⟨2230739, by rfl⟩ : syracuseStep 2974319 = 4461479) B4461479
theorem B582281 : Blo 171799 582281 := bstep (se 2 (by rfl) ⟨218355, by rfl⟩ : syracuseStep 582281 = 436711) B436711
theorem B2811287 : Blo 171799 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B1306367 : Blo 171799 1306367 := bstep (se 1 (by rfl) ⟨979775, by rfl⟩ : syracuseStep 1306367 = 1959551) B1959551
theorem B749321 : Blo 171799 749321 := bstep (se 2 (by rfl) ⟨280995, by rfl⟩ : syracuseStep 749321 = 561991) B561991
theorem B652319 : Blo 171799 652319 := bstep (se 1 (by rfl) ⟨489239, by rfl⟩ : syracuseStep 652319 = 978479) B978479
theorem B1473491 : Blo 171799 1473491 := bstep (se 1 (by rfl) ⟨1105118, by rfl⟩ : syracuseStep 1473491 = 2210237) B2210237
theorem B326767 : Blo 171799 326767 := bstep (se 1 (by rfl) ⟨245075, by rfl⟩ : syracuseStep 326767 = 490151) B490151
theorem B884681 : Blo 171799 884681 := bstep (se 2 (by rfl) ⟨331755, by rfl⟩ : syracuseStep 884681 = 663511) B663511
theorem B393299 : Blo 171799 393299 := bstep (se 1 (by rfl) ⟨294974, by rfl⟩ : syracuseStep 393299 = 589949) B589949
theorem B1312199 : Blo 171799 1312199 := bstep (se 1 (by rfl) ⟨984149, by rfl⟩ : syracuseStep 1312199 = 1968299) B1968299
theorem B984743 : Blo 171799 984743 := bstep (se 1 (by rfl) ⟨738557, by rfl⟩ : syracuseStep 984743 = 1477115) B1477115
theorem B985769 : Blo 171799 985769 := bstep (se 2 (by rfl) ⟨369663, by rfl⟩ : syracuseStep 985769 = 739327) B739327
theorem B1874191 : Blo 171799 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B3774761 : Blo 171799 3774761 := bstep (se 2 (by rfl) ⟨1415535, by rfl⟩ : syracuseStep 3774761 = 2831071) B2831071
theorem B499547 : Blo 171799 499547 := bstep (se 1 (by rfl) ⟨374660, by rfl⟩ : syracuseStep 499547 = 749321) B749321
theorem B434879 : Blo 171799 434879 := bstep (se 1 (by rfl) ⟨326159, by rfl⟩ : syracuseStep 434879 = 652319) B652319
theorem B435689 : Blo 171799 435689 := bstep (se 2 (by rfl) ⟨163383, by rfl⟩ : syracuseStep 435689 = 326767) B326767
theorem B1125521 : Blo 171799 1125521 := bstep (se 2 (by rfl) ⟨422070, by rfl⟩ : syracuseStep 1125521 = 844141) B844141
theorem B8531351 : Blo 171799 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B372671 : Blo 171799 372671 := bstep (se 1 (by rfl) ⟨279503, by rfl⟩ : syracuseStep 372671 = 559007) B559007
theorem B995723 : Blo 171799 995723 := bstep (se 1 (by rfl) ⟨746792, by rfl⟩ : syracuseStep 995723 = 1493585) B1493585
theorem B439607 : Blo 171799 439607 := bstep (se 1 (by rfl) ⟨329705, by rfl⟩ : syracuseStep 439607 = 659411) B659411
theorem B3979975 : Blo 171799 3979975 := bstep (se 1 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 3979975 = 5969963) B5969963
theorem B5683931 : Blo 171799 5683931 := bstep (se 1 (by rfl) ⟨4262948, by rfl⟩ : syracuseStep 5683931 = 8525897) B8525897
theorem B442523 : Blo 171799 442523 := bstep (se 1 (by rfl) ⟨331892, by rfl⟩ : syracuseStep 442523 = 663785) B663785
theorem B999823 : Blo 171799 999823 := bstep (se 1 (by rfl) ⟨749867, by rfl⟩ : syracuseStep 999823 = 1499735) B1499735
theorem B1982879 : Blo 171799 1982879 := bstep (se 1 (by rfl) ⟨1487159, by rfl⟩ : syracuseStep 1982879 = 2974319) B2974319
theorem B870911 : Blo 171799 870911 := bstep (se 1 (by rfl) ⟨653183, by rfl⟩ : syracuseStep 870911 = 1306367) B1306367
theorem B1692143 : Blo 171799 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B1498985 : Blo 171799 1498985 := bstep (se 2 (by rfl) ⟨562119, by rfl⟩ : syracuseStep 1498985 = 1124239) B1124239
theorem B2285927 : Blo 171799 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B878363 : Blo 171799 878363 := bstep (se 1 (by rfl) ⟨658772, by rfl⟩ : syracuseStep 878363 = 1317545) B1317545
theorem B748349 : Blo 171799 748349 := bstep (se 3 (by rfl) ⟨140315, by rfl⟩ : syracuseStep 748349 = 280631) B280631
theorem B388187 : Blo 171799 388187 := bstep (se 1 (by rfl) ⟨291140, by rfl⟩ : syracuseStep 388187 = 582281) B582281
theorem B587033 : Blo 171799 587033 := bstep (se 2 (by rfl) ⟨220137, by rfl⟩ : syracuseStep 587033 = 440275) B440275
theorem B982327 : Blo 171799 982327 := bstep (se 1 (by rfl) ⟨736745, by rfl⟩ : syracuseStep 982327 = 1473491) B1473491
theorem B589787 : Blo 171799 589787 := bstep (se 1 (by rfl) ⟨442340, by rfl⟩ : syracuseStep 589787 = 884681) B884681
theorem B262199 : Blo 171799 262199 := bstep (se 1 (by rfl) ⟨196649, by rfl⟩ : syracuseStep 262199 = 393299) B393299
theorem B295015 : Blo 171799 295015 := bstep (se 1 (by rfl) ⟨221261, by rfl⟩ : syracuseStep 295015 = 442523) B442523
theorem B656495 : Blo 171799 656495 := bstep (se 1 (by rfl) ⟨492371, by rfl⟩ : syracuseStep 656495 = 984743) B984743
theorem B657179 : Blo 171799 657179 := bstep (se 1 (by rfl) ⟨492884, by rfl⟩ : syracuseStep 657179 = 985769) B985769
theorem B498899 : Blo 171799 498899 := bstep (se 1 (by rfl) ⟨374174, by rfl⟩ : syracuseStep 498899 = 748349) B748349
theorem B663815 : Blo 171799 663815 := bstep (se 1 (by rfl) ⟨497861, by rfl⟩ : syracuseStep 663815 = 995723) B995723
theorem B2498921 : Blo 171799 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B1321919 : Blo 171799 1321919 := bstep (se 1 (by rfl) ⟨991439, by rfl⟩ : syracuseStep 1321919 = 1982879) B1982879
theorem B1128095 : Blo 171799 1128095 := bstep (se 1 (by rfl) ⟨846071, by rfl⟩ : syracuseStep 1128095 = 1692143) B1692143
theorem B999323 : Blo 171799 999323 := bstep (se 1 (by rfl) ⟨749492, by rfl⟩ : syracuseStep 999323 = 1498985) B1498985
theorem B1523951 : Blo 171799 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B5687567 : Blo 171799 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B248447 : Blo 171799 248447 := bstep (se 1 (by rfl) ⟨186335, by rfl⟩ : syracuseStep 248447 = 372671) B372671
theorem B3789287 : Blo 171799 3789287 := bstep (se 1 (by rfl) ⟨2841965, by rfl⟩ : syracuseStep 3789287 = 5683931) B5683931
theorem B1332125 : Blo 171799 1332125 := bstep (se 3 (by rfl) ⟨249773, by rfl⟩ : syracuseStep 1332125 = 499547) B499547
theorem B1333097 : Blo 171799 1333097 := bstep (se 2 (by rfl) ⟨499911, by rfl⟩ : syracuseStep 1333097 = 999823) B999823
theorem B874799 : Blo 171799 874799 := bstep (se 1 (by rfl) ⟨656099, by rfl⟩ : syracuseStep 874799 = 1312199) B1312199
theorem B580607 : Blo 171799 580607 := bstep (se 1 (by rfl) ⟨435455, by rfl⟩ : syracuseStep 580607 = 870911) B870911
theorem B2516507 : Blo 171799 2516507 := bstep (se 1 (by rfl) ⟨1887380, by rfl⟩ : syracuseStep 2516507 = 3774761) B3774761
theorem B289919 : Blo 171799 289919 := bstep (se 1 (by rfl) ⟨217439, by rfl⟩ : syracuseStep 289919 = 434879) B434879
theorem B290459 : Blo 171799 290459 := bstep (se 1 (by rfl) ⟨217844, by rfl⟩ : syracuseStep 290459 = 435689) B435689
theorem B585575 : Blo 171799 585575 := bstep (se 1 (by rfl) ⟨439181, by rfl⟩ : syracuseStep 585575 = 878363) B878363
theorem B258791 : Blo 171799 258791 := bstep (se 1 (by rfl) ⟨194093, by rfl⟩ : syracuseStep 258791 = 388187) B388187
theorem B750347 : Blo 171799 750347 := bstep (se 1 (by rfl) ⟨562760, by rfl⟩ : syracuseStep 750347 = 1125521) B1125521
theorem B391355 : Blo 171799 391355 := bstep (se 1 (by rfl) ⟨293516, by rfl⟩ : syracuseStep 391355 = 587033) B587033
theorem B293071 : Blo 171799 293071 := bstep (se 1 (by rfl) ⟨219803, by rfl⟩ : syracuseStep 293071 = 439607) B439607
theorem B5306633 : Blo 171799 5306633 := bstep (se 2 (by rfl) ⟨1989987, by rfl⟩ : syracuseStep 5306633 = 3979975) B3979975
theorem B1309769 : Blo 171799 1309769 := bstep (se 2 (by rfl) ⟨491163, by rfl⟩ : syracuseStep 1309769 = 982327) B982327
theorem B393191 : Blo 171799 393191 := bstep (se 1 (by rfl) ⟨294893, by rfl⟩ : syracuseStep 393191 = 589787) B589787
theorem B393353 : Blo 171799 393353 := bstep (se 2 (by rfl) ⟨147507, by rfl⟩ : syracuseStep 393353 = 295015) B295015
theorem B1015967 : Blo 171799 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B2526191 : Blo 171799 2526191 := bstep (se 1 (by rfl) ⟨1894643, by rfl⟩ : syracuseStep 2526191 = 3789287) B3789287
theorem B888083 : Blo 171799 888083 := bstep (se 1 (by rfl) ⟨666062, by rfl⟩ : syracuseStep 888083 = 1332125) B1332125
theorem B888731 : Blo 171799 888731 := bstep (se 1 (by rfl) ⟨666548, by rfl⟩ : syracuseStep 888731 = 1333097) B1333097
theorem B332599 : Blo 171799 332599 := bstep (se 1 (by rfl) ⟨249449, by rfl⟩ : syracuseStep 332599 = 498899) B498899
theorem B1677671 : Blo 171799 1677671 := bstep (se 1 (by rfl) ⟨1258253, by rfl⟩ : syracuseStep 1677671 = 2516507) B2516507
theorem B662525 : Blo 171799 662525 := bstep (se 3 (by rfl) ⟨124223, by rfl⟩ : syracuseStep 662525 = 248447) B248447
theorem B172527 : Blo 171799 172527 := bstep (se 1 (by rfl) ⟨129395, by rfl⟩ : syracuseStep 172527 = 258791) B258791
theorem B500231 : Blo 171799 500231 := bstep (se 1 (by rfl) ⟨375173, by rfl⟩ : syracuseStep 500231 = 750347) B750347
theorem B666215 : Blo 171799 666215 := bstep (se 1 (by rfl) ⟨499661, by rfl⟩ : syracuseStep 666215 = 999323) B999323
theorem B174799 : Blo 171799 174799 := bstep (se 1 (by rfl) ⟨131099, by rfl⟩ : syracuseStep 174799 = 262199) B262199
theorem B437663 : Blo 171799 437663 := bstep (se 1 (by rfl) ⟨328247, by rfl⟩ : syracuseStep 437663 = 656495) B656495
theorem B438119 : Blo 171799 438119 := bstep (se 1 (by rfl) ⟨328589, by rfl⟩ : syracuseStep 438119 = 657179) B657179
theorem B442543 : Blo 171799 442543 := bstep (se 1 (by rfl) ⟨331907, by rfl⟩ : syracuseStep 442543 = 663815) B663815
theorem B873179 : Blo 171799 873179 := bstep (se 1 (by rfl) ⟨654884, by rfl⟩ : syracuseStep 873179 = 1309769) B1309769
theorem B3791711 : Blo 171799 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B583199 : Blo 171799 583199 := bstep (se 1 (by rfl) ⟨437399, by rfl⟩ : syracuseStep 583199 = 874799) B874799
theorem B387071 : Blo 171799 387071 := bstep (se 1 (by rfl) ⟨290303, by rfl⟩ : syracuseStep 387071 = 580607) B580607
theorem B1665947 : Blo 171799 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B881279 : Blo 171799 881279 := bstep (se 1 (by rfl) ⟨660959, by rfl⟩ : syracuseStep 881279 = 1321919) B1321919
theorem B193279 : Blo 171799 193279 := bstep (se 1 (by rfl) ⟨144959, by rfl⟩ : syracuseStep 193279 = 289919) B289919
theorem B193639 : Blo 171799 193639 := bstep (se 1 (by rfl) ⟨145229, by rfl⟩ : syracuseStep 193639 = 290459) B290459
theorem B390383 : Blo 171799 390383 := bstep (se 1 (by rfl) ⟨292787, by rfl⟩ : syracuseStep 390383 = 585575) B585575
theorem B390761 : Blo 171799 390761 := bstep (se 2 (by rfl) ⟨146535, by rfl⟩ : syracuseStep 390761 = 293071) B293071
theorem B752063 : Blo 171799 752063 := bstep (se 1 (by rfl) ⟨564047, by rfl⟩ : syracuseStep 752063 = 1128095) B1128095
theorem B260903 : Blo 171799 260903 := bstep (se 1 (by rfl) ⟨195677, by rfl⟩ : syracuseStep 260903 = 391355) B391355
theorem B3537755 : Blo 171799 3537755 := bstep (se 1 (by rfl) ⟨2653316, by rfl⟩ : syracuseStep 3537755 = 5306633) B5306633
theorem B262127 : Blo 171799 262127 := bstep (se 1 (by rfl) ⟨196595, by rfl⟩ : syracuseStep 262127 = 393191) B393191
theorem B262235 : Blo 171799 262235 := bstep (se 1 (by rfl) ⟨196676, by rfl⟩ : syracuseStep 262235 = 393353) B393353
theorem B590057 : Blo 171799 590057 := bstep (se 2 (by rfl) ⟨221271, by rfl⟩ : syracuseStep 590057 = 442543) B442543
theorem B592055 : Blo 171799 592055 := bstep (se 1 (by rfl) ⟨444041, by rfl⟩ : syracuseStep 592055 = 888083) B888083
theorem B592487 : Blo 171799 592487 := bstep (se 1 (by rfl) ⟨444365, by rfl⟩ : syracuseStep 592487 = 888731) B888731
theorem B1118447 : Blo 171799 1118447 := bstep (se 1 (by rfl) ⟨838835, by rfl⟩ : syracuseStep 1118447 = 1677671) B1677671
theorem B2527807 : Blo 171799 2527807 := bstep (se 1 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 2527807 = 3791711) B3791711
theorem B333487 : Blo 171799 333487 := bstep (se 1 (by rfl) ⟨250115, by rfl⟩ : syracuseStep 333487 = 500231) B500231
theorem B2005501 : Blo 171799 2005501 := bstep (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) B752063
theorem B173935 : Blo 171799 173935 := bstep (se 1 (by rfl) ⟨130451, by rfl⟩ : syracuseStep 173935 = 260903) B260903
theorem B174751 : Blo 171799 174751 := bstep (se 1 (by rfl) ⟨131063, by rfl⟩ : syracuseStep 174751 = 262127) B262127
theorem B1684127 : Blo 171799 1684127 := bstep (se 1 (by rfl) ⟨1263095, by rfl⟩ : syracuseStep 1684127 = 2526191) B2526191
theorem B441683 : Blo 171799 441683 := bstep (se 1 (by rfl) ⟨331262, by rfl⟩ : syracuseStep 441683 = 662525) B662525
theorem B443465 : Blo 171799 443465 := bstep (se 2 (by rfl) ⟨166299, by rfl⟩ : syracuseStep 443465 = 332599) B332599
theorem B444143 : Blo 171799 444143 := bstep (se 1 (by rfl) ⟨333107, by rfl⟩ : syracuseStep 444143 = 666215) B666215
theorem B2709245 : Blo 171799 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B582119 : Blo 171799 582119 := bstep (se 1 (by rfl) ⟨436589, by rfl⟩ : syracuseStep 582119 = 873179) B873179
theorem B257705 : Blo 171799 257705 := bstep (se 2 (by rfl) ⟨96639, by rfl⟩ : syracuseStep 257705 = 193279) B193279
theorem B388799 : Blo 171799 388799 := bstep (se 1 (by rfl) ⟨291599, by rfl⟩ : syracuseStep 388799 = 583199) B583199
theorem B258047 : Blo 171799 258047 := bstep (se 1 (by rfl) ⟨193535, by rfl⟩ : syracuseStep 258047 = 387071) B387071
theorem B258185 : Blo 171799 258185 := bstep (se 2 (by rfl) ⟨96819, by rfl⟩ : syracuseStep 258185 = 193639) B193639
theorem B1110631 : Blo 171799 1110631 := bstep (se 1 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 1110631 = 1665947) B1665947
theorem B291775 : Blo 171799 291775 := bstep (se 1 (by rfl) ⟨218831, by rfl⟩ : syracuseStep 291775 = 437663) B437663
theorem B292079 : Blo 171799 292079 := bstep (se 1 (by rfl) ⟨219059, by rfl⟩ : syracuseStep 292079 = 438119) B438119
theorem B587519 : Blo 171799 587519 := bstep (se 1 (by rfl) ⟨440639, by rfl⟩ : syracuseStep 587519 = 881279) B881279
theorem B260255 : Blo 171799 260255 := bstep (se 1 (by rfl) ⟨195191, by rfl⟩ : syracuseStep 260255 = 390383) B390383
theorem B260507 : Blo 171799 260507 := bstep (se 1 (by rfl) ⟨195380, by rfl⟩ : syracuseStep 260507 = 390761) B390761
theorem B2358503 : Blo 171799 2358503 := bstep (se 1 (by rfl) ⟨1768877, by rfl⟩ : syracuseStep 2358503 = 3537755) B3537755
theorem B393371 : Blo 171799 393371 := bstep (se 1 (by rfl) ⟨295028, by rfl⟩ : syracuseStep 393371 = 590057) B590057
theorem B295643 : Blo 171799 295643 := bstep (se 1 (by rfl) ⟨221732, by rfl⟩ : syracuseStep 295643 = 443465) B443465
theorem B296095 : Blo 171799 296095 := bstep (se 1 (by rfl) ⟨222071, by rfl⟩ : syracuseStep 296095 = 444143) B444143
theorem B394703 : Blo 171799 394703 := bstep (se 1 (by rfl) ⟨296027, by rfl⟩ : syracuseStep 394703 = 592055) B592055
theorem B394991 : Blo 171799 394991 := bstep (se 1 (by rfl) ⟨296243, by rfl⟩ : syracuseStep 394991 = 592487) B592487
theorem B1480841 : Blo 171799 1480841 := bstep (se 2 (by rfl) ⟨555315, by rfl⟩ : syracuseStep 1480841 = 1110631) B1110631
theorem B171803 : Blo 171799 171803 := bstep (se 1 (by rfl) ⟨128852, by rfl⟩ : syracuseStep 171803 = 257705) B257705
theorem B172031 : Blo 171799 172031 := bstep (se 1 (by rfl) ⟨129023, by rfl⟩ : syracuseStep 172031 = 258047) B258047
theorem B172123 : Blo 171799 172123 := bstep (se 1 (by rfl) ⟨129092, by rfl⟩ : syracuseStep 172123 = 258185) B258185
theorem B1122751 : Blo 171799 1122751 := bstep (se 1 (by rfl) ⟨842063, by rfl⟩ : syracuseStep 1122751 = 1684127) B1684127
theorem B173503 : Blo 171799 173503 := bstep (se 1 (by rfl) ⟨130127, by rfl⟩ : syracuseStep 173503 = 260255) B260255
theorem B173671 : Blo 171799 173671 := bstep (se 1 (by rfl) ⟨130253, by rfl⟩ : syracuseStep 173671 = 260507) B260507
theorem B174823 : Blo 171799 174823 := bstep (se 1 (by rfl) ⟨131117, by rfl⟩ : syracuseStep 174823 = 262235) B262235
theorem B7224653 : Blo 171799 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B444649 : Blo 171799 444649 := bstep (se 2 (by rfl) ⟨166743, by rfl⟩ : syracuseStep 444649 = 333487) B333487
theorem B2674001 : Blo 171799 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B745631 : Blo 171799 745631 := bstep (se 1 (by rfl) ⟨559223, by rfl⟩ : syracuseStep 745631 = 1118447) B1118447
theorem B388079 : Blo 171799 388079 := bstep (se 1 (by rfl) ⟨291059, by rfl⟩ : syracuseStep 388079 = 582119) B582119
theorem B3370409 : Blo 171799 3370409 := bstep (se 2 (by rfl) ⟨1263903, by rfl⟩ : syracuseStep 3370409 = 2527807) B2527807
theorem B389033 : Blo 171799 389033 := bstep (se 2 (by rfl) ⟨145887, by rfl⟩ : syracuseStep 389033 = 291775) B291775
theorem B259199 : Blo 171799 259199 := bstep (se 1 (by rfl) ⟨194399, by rfl⟩ : syracuseStep 259199 = 388799) B388799
theorem B194719 : Blo 171799 194719 := bstep (se 1 (by rfl) ⟨146039, by rfl⟩ : syracuseStep 194719 = 292079) B292079
theorem B391679 : Blo 171799 391679 := bstep (se 1 (by rfl) ⟨293759, by rfl⟩ : syracuseStep 391679 = 587519) B587519
theorem B1572335 : Blo 171799 1572335 := bstep (se 1 (by rfl) ⟨1179251, by rfl⟩ : syracuseStep 1572335 = 2358503) B2358503
theorem B294455 : Blo 171799 294455 := bstep (se 1 (by rfl) ⟨220841, by rfl⟩ : syracuseStep 294455 = 441683) B441683
theorem B262247 : Blo 171799 262247 := bstep (se 1 (by rfl) ⟨196685, by rfl⟩ : syracuseStep 262247 = 393371) B393371
theorem B197095 : Blo 171799 197095 := bstep (se 1 (by rfl) ⟨147821, by rfl⟩ : syracuseStep 197095 = 295643) B295643
theorem B263135 : Blo 171799 263135 := bstep (se 1 (by rfl) ⟨197351, by rfl⟩ : syracuseStep 263135 = 394703) B394703
theorem B263327 : Blo 171799 263327 := bstep (se 1 (by rfl) ⟨197495, by rfl⟩ : syracuseStep 263327 = 394991) B394991
theorem B394793 : Blo 171799 394793 := bstep (se 2 (by rfl) ⟨148047, by rfl⟩ : syracuseStep 394793 = 296095) B296095
theorem B592865 : Blo 171799 592865 := bstep (se 2 (by rfl) ⟨222324, by rfl⟩ : syracuseStep 592865 = 444649) B444649
theorem B987227 : Blo 171799 987227 := bstep (se 1 (by rfl) ⟨740420, by rfl⟩ : syracuseStep 987227 = 1480841) B1480841
theorem B497087 : Blo 171799 497087 := bstep (se 1 (by rfl) ⟨372815, by rfl⟩ : syracuseStep 497087 = 745631) B745631
theorem B172799 : Blo 171799 172799 := bstep (se 1 (by rfl) ⟨129599, by rfl⟩ : syracuseStep 172799 = 259199) B259199
theorem B1782667 : Blo 171799 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B2246939 : Blo 171799 2246939 := bstep (se 1 (by rfl) ⟨1685204, by rfl⟩ : syracuseStep 2246939 = 3370409) B3370409
theorem B1497001 : Blo 171799 1497001 := bstep (se 2 (by rfl) ⟨561375, by rfl⟩ : syracuseStep 1497001 = 1122751) B1122751
theorem B258719 : Blo 171799 258719 := bstep (se 1 (by rfl) ⟨194039, by rfl⟩ : syracuseStep 258719 = 388079) B388079
theorem B259355 : Blo 171799 259355 := bstep (se 1 (by rfl) ⟨194516, by rfl⟩ : syracuseStep 259355 = 389033) B389033
theorem B259625 : Blo 171799 259625 := bstep (se 2 (by rfl) ⟨97359, by rfl⟩ : syracuseStep 259625 = 194719) B194719
theorem B261119 : Blo 171799 261119 := bstep (se 1 (by rfl) ⟨195839, by rfl⟩ : syracuseStep 261119 = 391679) B391679
theorem B4816435 : Blo 171799 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B1048223 : Blo 171799 1048223 := bstep (se 1 (by rfl) ⟨786167, by rfl⟩ : syracuseStep 1048223 = 1572335) B1572335
theorem B196303 : Blo 171799 196303 := bstep (se 1 (by rfl) ⟨147227, by rfl⟩ : syracuseStep 196303 = 294455) B294455
theorem B262793 : Blo 171799 262793 := bstep (se 2 (by rfl) ⟨98547, by rfl⟩ : syracuseStep 262793 = 197095) B197095
theorem B263195 : Blo 171799 263195 := bstep (se 1 (by rfl) ⟨197396, by rfl⟩ : syracuseStep 263195 = 394793) B394793
theorem B395243 : Blo 171799 395243 := bstep (se 1 (by rfl) ⟨296432, by rfl⟩ : syracuseStep 395243 = 592865) B592865
theorem B658151 : Blo 171799 658151 := bstep (se 1 (by rfl) ⟨493613, by rfl⟩ : syracuseStep 658151 = 987227) B987227
theorem B331391 : Blo 171799 331391 := bstep (se 1 (by rfl) ⟨248543, by rfl⟩ : syracuseStep 331391 = 497087) B497087
theorem B9507557 : Blo 171799 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B172479 : Blo 171799 172479 := bstep (se 1 (by rfl) ⟨129359, by rfl⟩ : syracuseStep 172479 = 258719) B258719
theorem B172903 : Blo 171799 172903 := bstep (se 1 (by rfl) ⟨129677, by rfl⟩ : syracuseStep 172903 = 259355) B259355
theorem B173083 : Blo 171799 173083 := bstep (se 1 (by rfl) ⟨129812, by rfl⟩ : syracuseStep 173083 = 259625) B259625
theorem B174079 : Blo 171799 174079 := bstep (se 1 (by rfl) ⟨130559, by rfl⟩ : syracuseStep 174079 = 261119) B261119
theorem B698815 : Blo 171799 698815 := bstep (se 1 (by rfl) ⟨524111, by rfl⟩ : syracuseStep 698815 = 1048223) B1048223
theorem B174831 : Blo 171799 174831 := bstep (se 1 (by rfl) ⟨131123, by rfl⟩ : syracuseStep 174831 = 262247) B262247
theorem B175423 : Blo 171799 175423 := bstep (se 1 (by rfl) ⟨131567, by rfl⟩ : syracuseStep 175423 = 263135) B263135
theorem B175551 : Blo 171799 175551 := bstep (se 1 (by rfl) ⟨131663, by rfl⟩ : syracuseStep 175551 = 263327) B263327
theorem B1497959 : Blo 171799 1497959 := bstep (se 1 (by rfl) ⟨1123469, by rfl⟩ : syracuseStep 1497959 = 2246939) B2246939
theorem B1996001 : Blo 171799 1996001 := bstep (se 2 (by rfl) ⟨748500, by rfl⟩ : syracuseStep 1996001 = 1497001) B1497001
theorem B6421913 : Blo 171799 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B261737 : Blo 171799 261737 := bstep (se 2 (by rfl) ⟨98151, by rfl⟩ : syracuseStep 261737 = 196303) B196303
theorem B263495 : Blo 171799 263495 := bstep (se 1 (by rfl) ⟨197621, by rfl⟩ : syracuseStep 263495 = 395243) B395243
theorem B174491 : Blo 171799 174491 := bstep (se 1 (by rfl) ⟨130868, by rfl⟩ : syracuseStep 174491 = 261737) B261737
theorem B175195 : Blo 171799 175195 := bstep (se 1 (by rfl) ⟨131396, by rfl⟩ : syracuseStep 175195 = 262793) B262793
theorem B175463 : Blo 171799 175463 := bstep (se 1 (by rfl) ⟨131597, by rfl⟩ : syracuseStep 175463 = 263195) B263195
theorem B438767 : Blo 171799 438767 := bstep (se 1 (by rfl) ⟨329075, by rfl⟩ : syracuseStep 438767 = 658151) B658151
theorem B6338371 : Blo 171799 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B931753 : Blo 171799 931753 := bstep (se 2 (by rfl) ⟨349407, by rfl⟩ : syracuseStep 931753 = 698815) B698815
theorem B998639 : Blo 171799 998639 := bstep (se 1 (by rfl) ⟨748979, by rfl⟩ : syracuseStep 998639 = 1497959) B1497959
theorem B1330667 : Blo 171799 1330667 := bstep (se 1 (by rfl) ⟨998000, by rfl⟩ : syracuseStep 1330667 = 1996001) B1996001
theorem B4281275 : Blo 171799 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B883709 : Blo 171799 883709 := bstep (se 3 (by rfl) ⟨165695, by rfl⟩ : syracuseStep 883709 = 331391) B331391
theorem B887111 : Blo 171799 887111 := bstep (se 1 (by rfl) ⟨665333, by rfl⟩ : syracuseStep 887111 = 1330667) B1330667
theorem B665759 : Blo 171799 665759 := bstep (se 1 (by rfl) ⟨499319, by rfl⟩ : syracuseStep 665759 = 998639) B998639
theorem B175663 : Blo 171799 175663 := bstep (se 1 (by rfl) ⟨131747, by rfl⟩ : syracuseStep 175663 = 263495) B263495
theorem B11416733 : Blo 171799 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B8451161 : Blo 171799 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B1242337 : Blo 171799 1242337 := bstep (se 2 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 1242337 = 931753) B931753
theorem B292511 : Blo 171799 292511 := bstep (se 1 (by rfl) ⟨219383, by rfl⟩ : syracuseStep 292511 = 438767) B438767
theorem B589139 : Blo 171799 589139 := bstep (se 1 (by rfl) ⟨441854, by rfl⟩ : syracuseStep 589139 = 883709) B883709
theorem B591407 : Blo 171799 591407 := bstep (se 1 (by rfl) ⟨443555, by rfl⟩ : syracuseStep 591407 = 887111) B887111
theorem B7611155 : Blo 171799 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B443839 : Blo 171799 443839 := bstep (se 1 (by rfl) ⟨332879, by rfl⟩ : syracuseStep 443839 = 665759) B665759
theorem B1656449 : Blo 171799 1656449 := bstep (se 2 (by rfl) ⟨621168, by rfl⟩ : syracuseStep 1656449 = 1242337) B1242337
theorem B5634107 : Blo 171799 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B195007 : Blo 171799 195007 := bstep (se 1 (by rfl) ⟨146255, by rfl⟩ : syracuseStep 195007 = 292511) B292511
theorem B392759 : Blo 171799 392759 := bstep (se 1 (by rfl) ⟨294569, by rfl⟩ : syracuseStep 392759 = 589139) B589139
theorem B394271 : Blo 171799 394271 := bstep (se 1 (by rfl) ⟨295703, by rfl⟩ : syracuseStep 394271 = 591407) B591407
theorem B591785 : Blo 171799 591785 := bstep (se 2 (by rfl) ⟨221919, by rfl⟩ : syracuseStep 591785 = 443839) B443839
theorem B3756071 : Blo 171799 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B1104299 : Blo 171799 1104299 := bstep (se 1 (by rfl) ⟨828224, by rfl⟩ : syracuseStep 1104299 = 1656449) B1656449
theorem B5074103 : Blo 171799 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B260009 : Blo 171799 260009 := bstep (se 2 (by rfl) ⟨97503, by rfl⟩ : syracuseStep 260009 = 195007) B195007
theorem B261839 : Blo 171799 261839 := bstep (se 1 (by rfl) ⟨196379, by rfl⟩ : syracuseStep 261839 = 392759) B392759
theorem B262847 : Blo 171799 262847 := bstep (se 1 (by rfl) ⟨197135, by rfl⟩ : syracuseStep 262847 = 394271) B394271
theorem B394523 : Blo 171799 394523 := bstep (se 1 (by rfl) ⟨295892, by rfl⟩ : syracuseStep 394523 = 591785) B591785
theorem B3382735 : Blo 171799 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B173339 : Blo 171799 173339 := bstep (se 1 (by rfl) ⟨130004, by rfl⟩ : syracuseStep 173339 = 260009) B260009
theorem B174559 : Blo 171799 174559 := bstep (se 1 (by rfl) ⟨130919, by rfl⟩ : syracuseStep 174559 = 261839) B261839
theorem B2504047 : Blo 171799 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B736199 : Blo 171799 736199 := bstep (se 1 (by rfl) ⟨552149, by rfl⟩ : syracuseStep 736199 = 1104299) B1104299
theorem B263015 : Blo 171799 263015 := bstep (se 1 (by rfl) ⟨197261, by rfl⟩ : syracuseStep 263015 = 394523) B394523
theorem B175231 : Blo 171799 175231 := bstep (se 1 (by rfl) ⟨131423, by rfl⟩ : syracuseStep 175231 = 262847) B262847
theorem B4510313 : Blo 171799 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B3338729 : Blo 171799 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B490799 : Blo 171799 490799 := bstep (se 1 (by rfl) ⟨368099, by rfl⟩ : syracuseStep 490799 = 736199) B736199
theorem B175343 : Blo 171799 175343 := bstep (se 1 (by rfl) ⟨131507, by rfl⟩ : syracuseStep 175343 = 263015) B263015
theorem B3006875 : Blo 171799 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B2225819 : Blo 171799 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B1308797 : Blo 171799 1308797 := bstep (se 3 (by rfl) ⟨245399, by rfl⟩ : syracuseStep 1308797 = 490799) B490799
theorem B2004583 : Blo 171799 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B1483879 : Blo 171799 1483879 := bstep (se 1 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 1483879 = 2225819) B2225819
theorem B872531 : Blo 171799 872531 := bstep (se 1 (by rfl) ⟨654398, by rfl⟩ : syracuseStep 872531 = 1308797) B1308797
theorem B1978505 : Blo 171799 1978505 := bstep (se 2 (by rfl) ⟨741939, by rfl⟩ : syracuseStep 1978505 = 1483879) B1483879
theorem B2672777 : Blo 171799 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B581687 : Blo 171799 581687 := bstep (se 1 (by rfl) ⟨436265, by rfl⟩ : syracuseStep 581687 = 872531) B872531
theorem B1319003 : Blo 171799 1319003 := bstep (se 1 (by rfl) ⟨989252, by rfl⟩ : syracuseStep 1319003 = 1978505) B1978505
theorem B1781851 : Blo 171799 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B387791 : Blo 171799 387791 := bstep (se 1 (by rfl) ⟨290843, by rfl⟩ : syracuseStep 387791 = 581687) B581687
theorem B2375801 : Blo 171799 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B879335 : Blo 171799 879335 := bstep (se 1 (by rfl) ⟨659501, by rfl⟩ : syracuseStep 879335 = 1319003) B1319003
theorem B258527 : Blo 171799 258527 := bstep (se 1 (by rfl) ⟨193895, by rfl⟩ : syracuseStep 258527 = 387791) B387791
theorem B172351 : Blo 171799 172351 := bstep (se 1 (by rfl) ⟨129263, by rfl⟩ : syracuseStep 172351 = 258527) B258527
theorem B1583867 : Blo 171799 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B586223 : Blo 171799 586223 := bstep (se 1 (by rfl) ⟨439667, by rfl⟩ : syracuseStep 586223 = 879335) B879335
theorem B1055911 : Blo 171799 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B390815 : Blo 171799 390815 := bstep (se 1 (by rfl) ⟨293111, by rfl⟩ : syracuseStep 390815 = 586223) B586223
theorem B260543 : Blo 171799 260543 := bstep (se 1 (by rfl) ⟨195407, by rfl⟩ : syracuseStep 260543 = 390815) B390815
theorem B1407881 : Blo 171799 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B173695 : Blo 171799 173695 := bstep (se 1 (by rfl) ⟨130271, by rfl⟩ : syracuseStep 173695 = 260543) B260543
theorem B3754349 : Blo 171799 3754349 := bstep (se 3 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 3754349 = 1407881) B1407881
theorem B2502899 : Blo 171799 2502899 := bstep (se 1 (by rfl) ⟨1877174, by rfl⟩ : syracuseStep 2502899 = 3754349) B3754349
theorem B1668599 : Blo 171799 1668599 := bstep (se 1 (by rfl) ⟨1251449, by rfl⟩ : syracuseStep 1668599 = 2502899) B2502899
theorem B1112399 : Blo 171799 1112399 := bstep (se 1 (by rfl) ⟨834299, by rfl⟩ : syracuseStep 1112399 = 1668599) B1668599
theorem B741599 : Blo 171799 741599 := bstep (se 1 (by rfl) ⟨556199, by rfl⟩ : syracuseStep 741599 = 1112399) B1112399
theorem B494399 : Blo 171799 494399 := bstep (se 1 (by rfl) ⟨370799, by rfl⟩ : syracuseStep 494399 = 741599) B741599
theorem B329599 : Blo 171799 329599 := bstep (se 1 (by rfl) ⟨247199, by rfl⟩ : syracuseStep 329599 = 494399) B494399
theorem B439465 : Blo 171799 439465 := bstep (se 2 (by rfl) ⟨164799, by rfl⟩ : syracuseStep 439465 = 329599) B329599
theorem B585953 : Blo 171799 585953 := bstep (se 2 (by rfl) ⟨219732, by rfl⟩ : syracuseStep 585953 = 439465) B439465
theorem B390635 : Blo 171799 390635 := bstep (se 1 (by rfl) ⟨292976, by rfl⟩ : syracuseStep 390635 = 585953) B585953
theorem B260423 : Blo 171799 260423 := bstep (se 1 (by rfl) ⟨195317, by rfl⟩ : syracuseStep 260423 = 390635) B390635
theorem B173615 : Blo 171799 173615 := bstep (se 1 (by rfl) ⟨130211, by rfl⟩ : syracuseStep 173615 = 260423) B260423

theorem C0 (j : ℕ) (h1 : 42949 ≤ j) (h2 : j ≤ 43648) : Blo 171799 (4 * j + 3) := by
  interval_cases j
  · exact B171799
  · exact B171803
  · exact B171807
  · exact B171811
  · exact B171815
  · exact B171819
  · exact B171823
  · exact B171827
  · exact B171831
  · exact B171835
  · exact B171839
  · exact B171843
  · exact B171847
  · exact B171851
  · exact B171855
  · exact B171859
  · exact B171863
  · exact B171867
  · exact B171871
  · exact B171875
  · exact B171879
  · exact B171883
  · exact B171887
  · exact B171891
  · exact B171895
  · exact B171899
  · exact B171903
  · exact B171907
  · exact B171911
  · exact B171915
  · exact B171919
  · exact B171923
  · exact B171927
  · exact B171931
  · exact B171935
  · exact B171939
  · exact B171943
  · exact B171947
  · exact B171951
  · exact B171955
  · exact B171959
  · exact B171963
  · exact B171967
  · exact B171971
  · exact B171975
  · exact B171979
  · exact B171983
  · exact B171987
  · exact B171991
  · exact B171995
  · exact B171999
  · exact B172003
  · exact B172007
  · exact B172011
  · exact B172015
  · exact B172019
  · exact B172023
  · exact B172027
  · exact B172031
  · exact B172035
  · exact B172039
  · exact B172043
  · exact B172047
  · exact B172051
  · exact B172055
  · exact B172059
  · exact B172063
  · exact B172067
  · exact B172071
  · exact B172075
  · exact B172079
  · exact B172083
  · exact B172087
  · exact B172091
  · exact B172095
  · exact B172099
  · exact B172103
  · exact B172107
  · exact B172111
  · exact B172115
  · exact B172119
  · exact B172123
  · exact B172127
  · exact B172131
  · exact B172135
  · exact B172139
  · exact B172143
  · exact B172147
  · exact B172151
  · exact B172155
  · exact B172159
  · exact B172163
  · exact B172167
  · exact B172171
  · exact B172175
  · exact B172179
  · exact B172183
  · exact B172187
  · exact B172191
  · exact B172195
  · exact B172199
  · exact B172203
  · exact B172207
  · exact B172211
  · exact B172215
  · exact B172219
  · exact B172223
  · exact B172227
  · exact B172231
  · exact B172235
  · exact B172239
  · exact B172243
  · exact B172247
  · exact B172251
  · exact B172255
  · exact B172259
  · exact B172263
  · exact B172267
  · exact B172271
  · exact B172275
  · exact B172279
  · exact B172283
  · exact B172287
  · exact B172291
  · exact B172295
  · exact B172299
  · exact B172303
  · exact B172307
  · exact B172311
  · exact B172315
  · exact B172319
  · exact B172323
  · exact B172327
  · exact B172331
  · exact B172335
  · exact B172339
  · exact B172343
  · exact B172347
  · exact B172351
  · exact B172355
  · exact B172359
  · exact B172363
  · exact B172367
  · exact B172371
  · exact B172375
  · exact B172379
  · exact B172383
  · exact B172387
  · exact B172391
  · exact B172395
  · exact B172399
  · exact B172403
  · exact B172407
  · exact B172411
  · exact B172415
  · exact B172419
  · exact B172423
  · exact B172427
  · exact B172431
  · exact B172435
  · exact B172439
  · exact B172443
  · exact B172447
  · exact B172451
  · exact B172455
  · exact B172459
  · exact B172463
  · exact B172467
  · exact B172471
  · exact B172475
  · exact B172479
  · exact B172483
  · exact B172487
  · exact B172491
  · exact B172495
  · exact B172499
  · exact B172503
  · exact B172507
  · exact B172511
  · exact B172515
  · exact B172519
  · exact B172523
  · exact B172527
  · exact B172531
  · exact B172535
  · exact B172539
  · exact B172543
  · exact B172547
  · exact B172551
  · exact B172555
  · exact B172559
  · exact B172563
  · exact B172567
  · exact B172571
  · exact B172575
  · exact B172579
  · exact B172583
  · exact B172587
  · exact B172591
  · exact B172595
  · exact B172599
  · exact B172603
  · exact B172607
  · exact B172611
  · exact B172615
  · exact B172619
  · exact B172623
  · exact B172627
  · exact B172631
  · exact B172635
  · exact B172639
  · exact B172643
  · exact B172647
  · exact B172651
  · exact B172655
  · exact B172659
  · exact B172663
  · exact B172667
  · exact B172671
  · exact B172675
  · exact B172679
  · exact B172683
  · exact B172687
  · exact B172691
  · exact B172695
  · exact B172699
  · exact B172703
  · exact B172707
  · exact B172711
  · exact B172715
  · exact B172719
  · exact B172723
  · exact B172727
  · exact B172731
  · exact B172735
  · exact B172739
  · exact B172743
  · exact B172747
  · exact B172751
  · exact B172755
  · exact B172759
  · exact B172763
  · exact B172767
  · exact B172771
  · exact B172775
  · exact B172779
  · exact B172783
  · exact B172787
  · exact B172791
  · exact B172795
  · exact B172799
  · exact B172803
  · exact B172807
  · exact B172811
  · exact B172815
  · exact B172819
  · exact B172823
  · exact B172827
  · exact B172831
  · exact B172835
  · exact B172839
  · exact B172843
  · exact B172847
  · exact B172851
  · exact B172855
  · exact B172859
  · exact B172863
  · exact B172867
  · exact B172871
  · exact B172875
  · exact B172879
  · exact B172883
  · exact B172887
  · exact B172891
  · exact B172895
  · exact B172899
  · exact B172903
  · exact B172907
  · exact B172911
  · exact B172915
  · exact B172919
  · exact B172923
  · exact B172927
  · exact B172931
  · exact B172935
  · exact B172939
  · exact B172943
  · exact B172947
  · exact B172951
  · exact B172955
  · exact B172959
  · exact B172963
  · exact B172967
  · exact B172971
  · exact B172975
  · exact B172979
  · exact B172983
  · exact B172987
  · exact B172991
  · exact B172995
  · exact B172999
  · exact B173003
  · exact B173007
  · exact B173011
  · exact B173015
  · exact B173019
  · exact B173023
  · exact B173027
  · exact B173031
  · exact B173035
  · exact B173039
  · exact B173043
  · exact B173047
  · exact B173051
  · exact B173055
  · exact B173059
  · exact B173063
  · exact B173067
  · exact B173071
  · exact B173075
  · exact B173079
  · exact B173083
  · exact B173087
  · exact B173091
  · exact B173095
  · exact B173099
  · exact B173103
  · exact B173107
  · exact B173111
  · exact B173115
  · exact B173119
  · exact B173123
  · exact B173127
  · exact B173131
  · exact B173135
  · exact B173139
  · exact B173143
  · exact B173147
  · exact B173151
  · exact B173155
  · exact B173159
  · exact B173163
  · exact B173167
  · exact B173171
  · exact B173175
  · exact B173179
  · exact B173183
  · exact B173187
  · exact B173191
  · exact B173195
  · exact B173199
  · exact B173203
  · exact B173207
  · exact B173211
  · exact B173215
  · exact B173219
  · exact B173223
  · exact B173227
  · exact B173231
  · exact B173235
  · exact B173239
  · exact B173243
  · exact B173247
  · exact B173251
  · exact B173255
  · exact B173259
  · exact B173263
  · exact B173267
  · exact B173271
  · exact B173275
  · exact B173279
  · exact B173283
  · exact B173287
  · exact B173291
  · exact B173295
  · exact B173299
  · exact B173303
  · exact B173307
  · exact B173311
  · exact B173315
  · exact B173319
  · exact B173323
  · exact B173327
  · exact B173331
  · exact B173335
  · exact B173339
  · exact B173343
  · exact B173347
  · exact B173351
  · exact B173355
  · exact B173359
  · exact B173363
  · exact B173367
  · exact B173371
  · exact B173375
  · exact B173379
  · exact B173383
  · exact B173387
  · exact B173391
  · exact B173395
  · exact B173399
  · exact B173403
  · exact B173407
  · exact B173411
  · exact B173415
  · exact B173419
  · exact B173423
  · exact B173427
  · exact B173431
  · exact B173435
  · exact B173439
  · exact B173443
  · exact B173447
  · exact B173451
  · exact B173455
  · exact B173459
  · exact B173463
  · exact B173467
  · exact B173471
  · exact B173475
  · exact B173479
  · exact B173483
  · exact B173487
  · exact B173491
  · exact B173495
  · exact B173499
  · exact B173503
  · exact B173507
  · exact B173511
  · exact B173515
  · exact B173519
  · exact B173523
  · exact B173527
  · exact B173531
  · exact B173535
  · exact B173539
  · exact B173543
  · exact B173547
  · exact B173551
  · exact B173555
  · exact B173559
  · exact B173563
  · exact B173567
  · exact B173571
  · exact B173575
  · exact B173579
  · exact B173583
  · exact B173587
  · exact B173591
  · exact B173595
  · exact B173599
  · exact B173603
  · exact B173607
  · exact B173611
  · exact B173615
  · exact B173619
  · exact B173623
  · exact B173627
  · exact B173631
  · exact B173635
  · exact B173639
  · exact B173643
  · exact B173647
  · exact B173651
  · exact B173655
  · exact B173659
  · exact B173663
  · exact B173667
  · exact B173671
  · exact B173675
  · exact B173679
  · exact B173683
  · exact B173687
  · exact B173691
  · exact B173695
  · exact B173699
  · exact B173703
  · exact B173707
  · exact B173711
  · exact B173715
  · exact B173719
  · exact B173723
  · exact B173727
  · exact B173731
  · exact B173735
  · exact B173739
  · exact B173743
  · exact B173747
  · exact B173751
  · exact B173755
  · exact B173759
  · exact B173763
  · exact B173767
  · exact B173771
  · exact B173775
  · exact B173779
  · exact B173783
  · exact B173787
  · exact B173791
  · exact B173795
  · exact B173799
  · exact B173803
  · exact B173807
  · exact B173811
  · exact B173815
  · exact B173819
  · exact B173823
  · exact B173827
  · exact B173831
  · exact B173835
  · exact B173839
  · exact B173843
  · exact B173847
  · exact B173851
  · exact B173855
  · exact B173859
  · exact B173863
  · exact B173867
  · exact B173871
  · exact B173875
  · exact B173879
  · exact B173883
  · exact B173887
  · exact B173891
  · exact B173895
  · exact B173899
  · exact B173903
  · exact B173907
  · exact B173911
  · exact B173915
  · exact B173919
  · exact B173923
  · exact B173927
  · exact B173931
  · exact B173935
  · exact B173939
  · exact B173943
  · exact B173947
  · exact B173951
  · exact B173955
  · exact B173959
  · exact B173963
  · exact B173967
  · exact B173971
  · exact B173975
  · exact B173979
  · exact B173983
  · exact B173987
  · exact B173991
  · exact B173995
  · exact B173999
  · exact B174003
  · exact B174007
  · exact B174011
  · exact B174015
  · exact B174019
  · exact B174023
  · exact B174027
  · exact B174031
  · exact B174035
  · exact B174039
  · exact B174043
  · exact B174047
  · exact B174051
  · exact B174055
  · exact B174059
  · exact B174063
  · exact B174067
  · exact B174071
  · exact B174075
  · exact B174079
  · exact B174083
  · exact B174087
  · exact B174091
  · exact B174095
  · exact B174099
  · exact B174103
  · exact B174107
  · exact B174111
  · exact B174115
  · exact B174119
  · exact B174123
  · exact B174127
  · exact B174131
  · exact B174135
  · exact B174139
  · exact B174143
  · exact B174147
  · exact B174151
  · exact B174155
  · exact B174159
  · exact B174163
  · exact B174167
  · exact B174171
  · exact B174175
  · exact B174179
  · exact B174183
  · exact B174187
  · exact B174191
  · exact B174195
  · exact B174199
  · exact B174203
  · exact B174207
  · exact B174211
  · exact B174215
  · exact B174219
  · exact B174223
  · exact B174227
  · exact B174231
  · exact B174235
  · exact B174239
  · exact B174243
  · exact B174247
  · exact B174251
  · exact B174255
  · exact B174259
  · exact B174263
  · exact B174267
  · exact B174271
  · exact B174275
  · exact B174279
  · exact B174283
  · exact B174287
  · exact B174291
  · exact B174295
  · exact B174299
  · exact B174303
  · exact B174307
  · exact B174311
  · exact B174315
  · exact B174319
  · exact B174323
  · exact B174327
  · exact B174331
  · exact B174335
  · exact B174339
  · exact B174343
  · exact B174347
  · exact B174351
  · exact B174355
  · exact B174359
  · exact B174363
  · exact B174367
  · exact B174371
  · exact B174375
  · exact B174379
  · exact B174383
  · exact B174387
  · exact B174391
  · exact B174395
  · exact B174399
  · exact B174403
  · exact B174407
  · exact B174411
  · exact B174415
  · exact B174419
  · exact B174423
  · exact B174427
  · exact B174431
  · exact B174435
  · exact B174439
  · exact B174443
  · exact B174447
  · exact B174451
  · exact B174455
  · exact B174459
  · exact B174463
  · exact B174467
  · exact B174471
  · exact B174475
  · exact B174479
  · exact B174483
  · exact B174487
  · exact B174491
  · exact B174495
  · exact B174499
  · exact B174503
  · exact B174507
  · exact B174511
  · exact B174515
  · exact B174519
  · exact B174523
  · exact B174527
  · exact B174531
  · exact B174535
  · exact B174539
  · exact B174543
  · exact B174547
  · exact B174551
  · exact B174555
  · exact B174559
  · exact B174563
  · exact B174567
  · exact B174571
  · exact B174575
  · exact B174579
  · exact B174583
  · exact B174587
  · exact B174591
  · exact B174595

theorem C1 (j : ℕ) (h1 : 43649 ≤ j) (h2 : j ≤ 43949) : Blo 171799 (4 * j + 3) := by
  interval_cases j
  · exact B174599
  · exact B174603
  · exact B174607
  · exact B174611
  · exact B174615
  · exact B174619
  · exact B174623
  · exact B174627
  · exact B174631
  · exact B174635
  · exact B174639
  · exact B174643
  · exact B174647
  · exact B174651
  · exact B174655
  · exact B174659
  · exact B174663
  · exact B174667
  · exact B174671
  · exact B174675
  · exact B174679
  · exact B174683
  · exact B174687
  · exact B174691
  · exact B174695
  · exact B174699
  · exact B174703
  · exact B174707
  · exact B174711
  · exact B174715
  · exact B174719
  · exact B174723
  · exact B174727
  · exact B174731
  · exact B174735
  · exact B174739
  · exact B174743
  · exact B174747
  · exact B174751
  · exact B174755
  · exact B174759
  · exact B174763
  · exact B174767
  · exact B174771
  · exact B174775
  · exact B174779
  · exact B174783
  · exact B174787
  · exact B174791
  · exact B174795
  · exact B174799
  · exact B174803
  · exact B174807
  · exact B174811
  · exact B174815
  · exact B174819
  · exact B174823
  · exact B174827
  · exact B174831
  · exact B174835
  · exact B174839
  · exact B174843
  · exact B174847
  · exact B174851
  · exact B174855
  · exact B174859
  · exact B174863
  · exact B174867
  · exact B174871
  · exact B174875
  · exact B174879
  · exact B174883
  · exact B174887
  · exact B174891
  · exact B174895
  · exact B174899
  · exact B174903
  · exact B174907
  · exact B174911
  · exact B174915
  · exact B174919
  · exact B174923
  · exact B174927
  · exact B174931
  · exact B174935
  · exact B174939
  · exact B174943
  · exact B174947
  · exact B174951
  · exact B174955
  · exact B174959
  · exact B174963
  · exact B174967
  · exact B174971
  · exact B174975
  · exact B174979
  · exact B174983
  · exact B174987
  · exact B174991
  · exact B174995
  · exact B174999
  · exact B175003
  · exact B175007
  · exact B175011
  · exact B175015
  · exact B175019
  · exact B175023
  · exact B175027
  · exact B175031
  · exact B175035
  · exact B175039
  · exact B175043
  · exact B175047
  · exact B175051
  · exact B175055
  · exact B175059
  · exact B175063
  · exact B175067
  · exact B175071
  · exact B175075
  · exact B175079
  · exact B175083
  · exact B175087
  · exact B175091
  · exact B175095
  · exact B175099
  · exact B175103
  · exact B175107
  · exact B175111
  · exact B175115
  · exact B175119
  · exact B175123
  · exact B175127
  · exact B175131
  · exact B175135
  · exact B175139
  · exact B175143
  · exact B175147
  · exact B175151
  · exact B175155
  · exact B175159
  · exact B175163
  · exact B175167
  · exact B175171
  · exact B175175
  · exact B175179
  · exact B175183
  · exact B175187
  · exact B175191
  · exact B175195
  · exact B175199
  · exact B175203
  · exact B175207
  · exact B175211
  · exact B175215
  · exact B175219
  · exact B175223
  · exact B175227
  · exact B175231
  · exact B175235
  · exact B175239
  · exact B175243
  · exact B175247
  · exact B175251
  · exact B175255
  · exact B175259
  · exact B175263
  · exact B175267
  · exact B175271
  · exact B175275
  · exact B175279
  · exact B175283
  · exact B175287
  · exact B175291
  · exact B175295
  · exact B175299
  · exact B175303
  · exact B175307
  · exact B175311
  · exact B175315
  · exact B175319
  · exact B175323
  · exact B175327
  · exact B175331
  · exact B175335
  · exact B175339
  · exact B175343
  · exact B175347
  · exact B175351
  · exact B175355
  · exact B175359
  · exact B175363
  · exact B175367
  · exact B175371
  · exact B175375
  · exact B175379
  · exact B175383
  · exact B175387
  · exact B175391
  · exact B175395
  · exact B175399
  · exact B175403
  · exact B175407
  · exact B175411
  · exact B175415
  · exact B175419
  · exact B175423
  · exact B175427
  · exact B175431
  · exact B175435
  · exact B175439
  · exact B175443
  · exact B175447
  · exact B175451
  · exact B175455
  · exact B175459
  · exact B175463
  · exact B175467
  · exact B175471
  · exact B175475
  · exact B175479
  · exact B175483
  · exact B175487
  · exact B175491
  · exact B175495
  · exact B175499
  · exact B175503
  · exact B175507
  · exact B175511
  · exact B175515
  · exact B175519
  · exact B175523
  · exact B175527
  · exact B175531
  · exact B175535
  · exact B175539
  · exact B175543
  · exact B175547
  · exact B175551
  · exact B175555
  · exact B175559
  · exact B175563
  · exact B175567
  · exact B175571
  · exact B175575
  · exact B175579
  · exact B175583
  · exact B175587
  · exact B175591
  · exact B175595
  · exact B175599
  · exact B175603
  · exact B175607
  · exact B175611
  · exact B175615
  · exact B175619
  · exact B175623
  · exact B175627
  · exact B175631
  · exact B175635
  · exact B175639
  · exact B175643
  · exact B175647
  · exact B175651
  · exact B175655
  · exact B175659
  · exact B175663
  · exact B175667
  · exact B175671
  · exact B175675
  · exact B175679
  · exact B175683
  · exact B175687
  · exact B175691
  · exact B175695
  · exact B175699
  · exact B175703
  · exact B175707
  · exact B175711
  · exact B175715
  · exact B175719
  · exact B175723
  · exact B175727
  · exact B175731
  · exact B175735
  · exact B175739
  · exact B175743
  · exact B175747
  · exact B175751
  · exact B175755
  · exact B175759
  · exact B175763
  · exact B175767
  · exact B175771
  · exact B175775
  · exact B175779
  · exact B175783
  · exact B175787
  · exact B175791
  · exact B175795
  · exact B175799

theorem solution (m : ℕ) (hlo : 171799 ≤ m) (hhi : m ≤ 175799) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 42949 ≤ j := by omega
    have hj2 : j ≤ 43949 := by omega
    have hb : Blo 171799 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 43649 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
