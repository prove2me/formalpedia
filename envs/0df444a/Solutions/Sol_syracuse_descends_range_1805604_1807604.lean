-- Prove2me | solution 1 for syracuse_descends_range_1805604_1807604
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:51:53.334062+00:00
-- url     : https://prove2.me/submissions/497dfb67-d854-4f00-9037-d946fba64dd4

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


theorem B3047429 : Blo 1805604 3047429 := bbase (se 4 (by rfl) ⟨285696, by rfl⟩ : syracuseStep 3047429 = 571393) (by norm_num)
theorem B2031637 : Blo 1805604 2031637 := bbase (se 6 (by rfl) ⟨47616, by rfl⟩ : syracuseStep 2031637 = 95233) (by norm_num)
theorem B2285597 : Blo 1805604 2285597 := bbase (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) (by norm_num)
theorem B13713461 : Blo 1805604 13713461 := bbase (se 5 (by rfl) ⟨642818, by rfl⟩ : syracuseStep 13713461 = 1285637) (by norm_num)
theorem B2031673 : Blo 1805604 2031673 := bbase (se 2 (by rfl) ⟨761877, by rfl⟩ : syracuseStep 2031673 = 1523755) (by norm_num)
theorem B2170945 : Blo 1805604 2170945 := bbase (se 2 (by rfl) ⟨814104, by rfl⟩ : syracuseStep 2170945 = 1628209) (by norm_num)
theorem B4063301 : Blo 1805604 4063301 := bbase (se 4 (by rfl) ⟨380934, by rfl⟩ : syracuseStep 4063301 = 761869) (by norm_num)
theorem B2285653 : Blo 1805604 2285653 := bbase (se 8 (by rfl) ⟨13392, by rfl⟩ : syracuseStep 2285653 = 26785) (by norm_num)
theorem B2031709 : Blo 1805604 2031709 := bbase (se 3 (by rfl) ⟨380945, by rfl⟩ : syracuseStep 2031709 = 761891) (by norm_num)
theorem B2031745 : Blo 1805604 2031745 := bbase (se 2 (by rfl) ⟨761904, by rfl⟩ : syracuseStep 2031745 = 1523809) (by norm_num)
theorem B3047557 : Blo 1805604 3047557 := bbase (se 4 (by rfl) ⟨285708, by rfl⟩ : syracuseStep 3047557 = 571417) (by norm_num)
theorem B4063373 : Blo 1805604 4063373 := bbase (se 3 (by rfl) ⟨761882, by rfl⟩ : syracuseStep 4063373 = 1523765) (by norm_num)
theorem B2031781 : Blo 1805604 2031781 := bbase (se 4 (by rfl) ⟨190479, by rfl⟩ : syracuseStep 2031781 = 380959) (by norm_num)
theorem B2285749 : Blo 1805604 2285749 := bbase (se 5 (by rfl) ⟨107144, by rfl⟩ : syracuseStep 2285749 = 214289) (by norm_num)
theorem B9142469 : Blo 1805604 9142469 := bbase (se 4 (by rfl) ⟨857106, by rfl⟩ : syracuseStep 9142469 = 1714213) (by norm_num)
theorem B2031817 : Blo 1805604 2031817 := bbase (se 2 (by rfl) ⟨761931, by rfl⟩ : syracuseStep 2031817 = 1523863) (by norm_num)
theorem B1982665 : Blo 1805604 1982665 := bbase (se 2 (by rfl) ⟨743499, by rfl⟩ : syracuseStep 1982665 = 1486999) (by norm_num)
theorem B4063445 : Blo 1805604 4063445 := bbase (se 7 (by rfl) ⟨47618, by rfl⟩ : syracuseStep 4063445 = 95237) (by norm_num)
theorem B3047645 : Blo 1805604 3047645 := bbase (se 3 (by rfl) ⟨571433, by rfl⟩ : syracuseStep 3047645 = 1142867) (by norm_num)
theorem B2031853 : Blo 1805604 2031853 := bbase (se 3 (by rfl) ⟨380972, by rfl⟩ : syracuseStep 2031853 = 761945) (by norm_num)
theorem B2031889 : Blo 1805604 2031889 := bbase (se 2 (by rfl) ⟨761958, by rfl⟩ : syracuseStep 2031889 = 1523917) (by norm_num)
theorem B4063517 : Blo 1805604 4063517 := bbase (se 3 (by rfl) ⟨761909, by rfl⟩ : syracuseStep 4063517 = 1523819) (by norm_num)
theorem B2572573 : Blo 1805604 2572573 := bbase (se 3 (by rfl) ⟨482357, by rfl⟩ : syracuseStep 2572573 = 964715) (by norm_num)
theorem B6095141 : Blo 1805604 6095141 := bbase (se 4 (by rfl) ⟨571419, by rfl⟩ : syracuseStep 6095141 = 1142839) (by norm_num)
theorem B4571437 : Blo 1805604 4571437 := bbase (se 3 (by rfl) ⟨857144, by rfl⟩ : syracuseStep 4571437 = 1714289) (by norm_num)
theorem B2031925 : Blo 1805604 2031925 := bbase (se 5 (by rfl) ⟨95246, by rfl⟩ : syracuseStep 2031925 = 190493) (by norm_num)
theorem B3858749 : Blo 1805604 3858749 := bbase (se 3 (by rfl) ⟨723515, by rfl⟩ : syracuseStep 3858749 = 1447031) (by norm_num)
theorem B2031961 : Blo 1805604 2031961 := bbase (se 2 (by rfl) ⟨761985, by rfl⟩ : syracuseStep 2031961 = 1523971) (by norm_num)
theorem B3047773 : Blo 1805604 3047773 := bbase (se 3 (by rfl) ⟨571457, by rfl⟩ : syracuseStep 3047773 = 1142915) (by norm_num)
theorem B2285921 : Blo 1805604 2285921 := bbase (se 2 (by rfl) ⟨857220, by rfl⟩ : syracuseStep 2285921 = 1714441) (by norm_num)
theorem B4063589 : Blo 1805604 4063589 := bbase (se 4 (by rfl) ⟨380961, by rfl⟩ : syracuseStep 4063589 = 761923) (by norm_num)
theorem B3662189 : Blo 1805604 3662189 := bbase (se 3 (by rfl) ⟨686660, by rfl⟩ : syracuseStep 3662189 = 1373321) (by norm_num)
theorem B2031997 : Blo 1805604 2031997 := bbase (se 3 (by rfl) ⟨380999, by rfl⟩ : syracuseStep 2031997 = 761999) (by norm_num)
theorem B15638933 : Blo 1805604 15638933 := bbase (se 6 (by rfl) ⟨366537, by rfl⟩ : syracuseStep 15638933 = 733075) (by norm_num)
theorem B2285977 : Blo 1805604 2285977 := bbase (se 2 (by rfl) ⟨857241, by rfl⟩ : syracuseStep 2285977 = 1714483) (by norm_num)
theorem B4571549 : Blo 1805604 4571549 := bbase (se 3 (by rfl) ⟨857165, by rfl⟩ : syracuseStep 4571549 = 1714331) (by norm_num)
theorem B2032033 : Blo 1805604 2032033 := bbase (se 2 (by rfl) ⟨762012, by rfl⟩ : syracuseStep 2032033 = 1524025) (by norm_num)
theorem B4063661 : Blo 1805604 4063661 := bbase (se 3 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 4063661 = 1523873) (by norm_num)
theorem B3047861 : Blo 1805604 3047861 := bbase (se 5 (by rfl) ⟨142868, by rfl⟩ : syracuseStep 3047861 = 285737) (by norm_num)
theorem B2032069 : Blo 1805604 2032069 := bbase (se 4 (by rfl) ⟨190506, by rfl⟩ : syracuseStep 2032069 = 381013) (by norm_num)
theorem B2032105 : Blo 1805604 2032105 := bbase (se 2 (by rfl) ⟨762039, by rfl⟩ : syracuseStep 2032105 = 1524079) (by norm_num)
theorem B4063733 : Blo 1805604 4063733 := bbase (se 5 (by rfl) ⟨190487, by rfl⟩ : syracuseStep 4063733 = 380975) (by norm_num)
theorem B2286073 : Blo 1805604 2286073 := bbase (se 2 (by rfl) ⟨857277, by rfl⟩ : syracuseStep 2286073 = 1714555) (by norm_num)
theorem B2032141 : Blo 1805604 2032141 := bbase (se 3 (by rfl) ⟨381026, by rfl⟩ : syracuseStep 2032141 = 762053) (by norm_num)
theorem B2032177 : Blo 1805604 2032177 := bbase (se 2 (by rfl) ⟨762066, by rfl⟩ : syracuseStep 2032177 = 1524133) (by norm_num)
theorem B3047989 : Blo 1805604 3047989 := bbase (se 5 (by rfl) ⟨142874, by rfl⟩ : syracuseStep 3047989 = 285749) (by norm_num)
theorem B4063805 : Blo 1805604 4063805 := bbase (se 3 (by rfl) ⟨761963, by rfl⟩ : syracuseStep 4063805 = 1523927) (by norm_num)
theorem B2032213 : Blo 1805604 2032213 := bbase (se 8 (by rfl) ⟨11907, by rfl⟩ : syracuseStep 2032213 = 23815) (by norm_num)
theorem B4571741 : Blo 1805604 4571741 := bbase (se 3 (by rfl) ⟨857201, by rfl⟩ : syracuseStep 4571741 = 1714403) (by norm_num)
theorem B2032249 : Blo 1805604 2032249 := bbase (se 2 (by rfl) ⟨762093, by rfl⟩ : syracuseStep 2032249 = 1524187) (by norm_num)
theorem B4063877 : Blo 1805604 4063877 := bbase (se 4 (by rfl) ⟨380988, by rfl⟩ : syracuseStep 4063877 = 761977) (by norm_num)
theorem B3048077 : Blo 1805604 3048077 := bbase (se 3 (by rfl) ⟨571514, by rfl⟩ : syracuseStep 3048077 = 1143029) (by norm_num)
theorem B2032285 : Blo 1805604 2032285 := bbase (se 3 (by rfl) ⟨381053, by rfl⟩ : syracuseStep 2032285 = 762107) (by norm_num)
theorem B2286245 : Blo 1805604 2286245 := bbase (se 4 (by rfl) ⟨214335, by rfl⟩ : syracuseStep 2286245 = 428671) (by norm_num)
theorem B2032321 : Blo 1805604 2032321 := bbase (se 2 (by rfl) ⟨762120, by rfl⟩ : syracuseStep 2032321 = 1524241) (by norm_num)
theorem B4063949 : Blo 1805604 4063949 := bbase (se 3 (by rfl) ⟨761990, by rfl⟩ : syracuseStep 4063949 = 1523981) (by norm_num)
theorem B6095573 : Blo 1805604 6095573 := bbase (se 7 (by rfl) ⟨71432, by rfl⟩ : syracuseStep 6095573 = 142865) (by norm_num)
theorem B2286301 : Blo 1805604 2286301 := bbase (se 3 (by rfl) ⟨428681, by rfl⟩ : syracuseStep 2286301 = 857363) (by norm_num)
theorem B2032357 : Blo 1805604 2032357 := bbase (se 4 (by rfl) ⟨190533, by rfl⟩ : syracuseStep 2032357 = 381067) (by norm_num)
theorem B2032393 : Blo 1805604 2032393 := bbase (se 2 (by rfl) ⟨762147, by rfl⟩ : syracuseStep 2032393 = 1524295) (by norm_num)
theorem B3048205 : Blo 1805604 3048205 := bbase (se 3 (by rfl) ⟨571538, by rfl⟩ : syracuseStep 3048205 = 1143077) (by norm_num)
theorem B4064021 : Blo 1805604 4064021 := bbase (se 6 (by rfl) ⟨95250, by rfl⟩ : syracuseStep 4064021 = 190501) (by norm_num)
theorem B2032429 : Blo 1805604 2032429 := bbase (se 3 (by rfl) ⟨381080, by rfl⟩ : syracuseStep 2032429 = 762161) (by norm_num)
theorem B15434549 : Blo 1805604 15434549 := bbase (se 5 (by rfl) ⟨723494, by rfl⟩ : syracuseStep 15434549 = 1446989) (by norm_num)
theorem B2286397 : Blo 1805604 2286397 := bbase (se 3 (by rfl) ⟨428699, by rfl⟩ : syracuseStep 2286397 = 857399) (by norm_num)
theorem B4399933 : Blo 1805604 4399933 := bbase (se 3 (by rfl) ⟨824987, by rfl⟩ : syracuseStep 4399933 = 1649975) (by norm_num)
theorem B2032465 : Blo 1805604 2032465 := bbase (se 2 (by rfl) ⟨762174, by rfl⟩ : syracuseStep 2032465 = 1524349) (by norm_num)
theorem B4064093 : Blo 1805604 4064093 := bbase (se 3 (by rfl) ⟨762017, by rfl⟩ : syracuseStep 4064093 = 1524035) (by norm_num)
theorem B3048293 : Blo 1805604 3048293 := bbase (se 4 (by rfl) ⟨285777, by rfl⟩ : syracuseStep 3048293 = 571555) (by norm_num)
theorem B2573165 : Blo 1805604 2573165 := bbase (se 3 (by rfl) ⟨482468, by rfl⟩ : syracuseStep 2573165 = 964937) (by norm_num)
theorem B2032501 : Blo 1805604 2032501 := bbase (se 5 (by rfl) ⟨95273, by rfl⟩ : syracuseStep 2032501 = 190547) (by norm_num)
theorem B2032537 : Blo 1805604 2032537 := bbase (se 2 (by rfl) ⟨762201, by rfl⟩ : syracuseStep 2032537 = 1524403) (by norm_num)
theorem B4064165 : Blo 1805604 4064165 := bbase (se 4 (by rfl) ⟨381015, by rfl⟩ : syracuseStep 4064165 = 762031) (by norm_num)
theorem B4572085 : Blo 1805604 4572085 := bbase (se 5 (by rfl) ⟨214316, by rfl⟩ : syracuseStep 4572085 = 428633) (by norm_num)
theorem B2032573 : Blo 1805604 2032573 := bbase (se 3 (by rfl) ⟨381107, by rfl⟩ : syracuseStep 2032573 = 762215) (by norm_num)
theorem B4121533 : Blo 1805604 4121533 := bbase (se 3 (by rfl) ⟨772787, by rfl⟩ : syracuseStep 4121533 = 1545575) (by norm_num)
theorem B2573245 : Blo 1805604 2573245 := bbase (se 3 (by rfl) ⟨482483, by rfl⟩ : syracuseStep 2573245 = 964967) (by norm_num)
theorem B2032609 : Blo 1805604 2032609 := bbase (se 2 (by rfl) ⟨762228, by rfl⟩ : syracuseStep 2032609 = 1524457) (by norm_num)
theorem B3048421 : Blo 1805604 3048421 := bbase (se 4 (by rfl) ⟨285789, by rfl⟩ : syracuseStep 3048421 = 571579) (by norm_num)
theorem B2286569 : Blo 1805604 2286569 := bbase (se 2 (by rfl) ⟨857463, by rfl⟩ : syracuseStep 2286569 = 1714927) (by norm_num)
theorem B4064237 : Blo 1805604 4064237 := bbase (se 3 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 4064237 = 1524089) (by norm_num)
theorem B2032645 : Blo 1805604 2032645 := bbase (se 4 (by rfl) ⟨190560, by rfl⟩ : syracuseStep 2032645 = 381121) (by norm_num)
theorem B2286625 : Blo 1805604 2286625 := bbase (se 2 (by rfl) ⟨857484, by rfl⟩ : syracuseStep 2286625 = 1714969) (by norm_num)
theorem B4572197 : Blo 1805604 4572197 := bbase (se 4 (by rfl) ⟨428643, by rfl⟩ : syracuseStep 4572197 = 857287) (by norm_num)
theorem B2032681 : Blo 1805604 2032681 := bbase (se 2 (by rfl) ⟨762255, by rfl⟩ : syracuseStep 2032681 = 1524511) (by norm_num)
theorem B3859501 : Blo 1805604 3859501 := bbase (se 3 (by rfl) ⟨723656, by rfl⟩ : syracuseStep 3859501 = 1447313) (by norm_num)
theorem B4064309 : Blo 1805604 4064309 := bbase (se 5 (by rfl) ⟨190514, by rfl⟩ : syracuseStep 4064309 = 381029) (by norm_num)
theorem B2573365 : Blo 1805604 2573365 := bbase (se 5 (by rfl) ⟨120626, by rfl⟩ : syracuseStep 2573365 = 241253) (by norm_num)
theorem B3048509 : Blo 1805604 3048509 := bbase (se 3 (by rfl) ⟨571595, by rfl⟩ : syracuseStep 3048509 = 1143191) (by norm_num)
theorem B2032717 : Blo 1805604 2032717 := bbase (se 3 (by rfl) ⟨381134, by rfl⟩ : syracuseStep 2032717 = 762269) (by norm_num)
theorem B2032753 : Blo 1805604 2032753 := bbase (se 2 (by rfl) ⟨762282, by rfl⟩ : syracuseStep 2032753 = 1524565) (by norm_num)
theorem B4064381 : Blo 1805604 4064381 := bbase (se 3 (by rfl) ⟨762071, by rfl⟩ : syracuseStep 4064381 = 1524143) (by norm_num)
theorem B2286721 : Blo 1805604 2286721 := bbase (se 2 (by rfl) ⟨857520, by rfl⟩ : syracuseStep 2286721 = 1715041) (by norm_num)
theorem B6096005 : Blo 1805604 6096005 := bbase (se 4 (by rfl) ⟨571500, by rfl⟩ : syracuseStep 6096005 = 1143001) (by norm_num)
theorem B2032789 : Blo 1805604 2032789 := bbase (se 6 (by rfl) ⟨47643, by rfl⟩ : syracuseStep 2032789 = 95287) (by norm_num)
theorem B2573461 : Blo 1805604 2573461 := bbase (se 6 (by rfl) ⟨60315, by rfl⟩ : syracuseStep 2573461 = 120631) (by norm_num)
theorem B2032825 : Blo 1805604 2032825 := bbase (se 2 (by rfl) ⟨762309, by rfl⟩ : syracuseStep 2032825 = 1524619) (by norm_num)
theorem B3048637 : Blo 1805604 3048637 := bbase (se 3 (by rfl) ⟨571619, by rfl⟩ : syracuseStep 3048637 = 1143239) (by norm_num)
theorem B3859645 : Blo 1805604 3859645 := bbase (se 3 (by rfl) ⟨723683, by rfl⟩ : syracuseStep 3859645 = 1447367) (by norm_num)
theorem B4064453 : Blo 1805604 4064453 := bbase (se 4 (by rfl) ⟨381042, by rfl⟩ : syracuseStep 4064453 = 762085) (by norm_num)
theorem B2032861 : Blo 1805604 2032861 := bbase (se 3 (by rfl) ⟨381161, by rfl⟩ : syracuseStep 2032861 = 762323) (by norm_num)
theorem B4572389 : Blo 1805604 4572389 := bbase (se 4 (by rfl) ⟨428661, by rfl⟩ : syracuseStep 4572389 = 857323) (by norm_num)
theorem B2032897 : Blo 1805604 2032897 := bbase (se 2 (by rfl) ⟨762336, by rfl⟩ : syracuseStep 2032897 = 1524673) (by norm_num)
theorem B4064525 : Blo 1805604 4064525 := bbase (se 3 (by rfl) ⟨762098, by rfl⟩ : syracuseStep 4064525 = 1524197) (by norm_num)
theorem B3048725 : Blo 1805604 3048725 := bbase (se 6 (by rfl) ⟨71454, by rfl⟩ : syracuseStep 3048725 = 142909) (by norm_num)
theorem B2032933 : Blo 1805604 2032933 := bbase (se 4 (by rfl) ⟨190587, by rfl⟩ : syracuseStep 2032933 = 381175) (by norm_num)
theorem B2286893 : Blo 1805604 2286893 := bbase (se 3 (by rfl) ⟨428792, by rfl⟩ : syracuseStep 2286893 = 857585) (by norm_num)
theorem B6858053 : Blo 1805604 6858053 := bbase (se 4 (by rfl) ⟨642942, by rfl⟩ : syracuseStep 6858053 = 1285885) (by norm_num)
theorem B2032969 : Blo 1805604 2032969 := bbase (se 2 (by rfl) ⟨762363, by rfl⟩ : syracuseStep 2032969 = 1524727) (by norm_num)
theorem B4064597 : Blo 1805604 4064597 := bbase (se 12 (by rfl) ⟨1488, by rfl⟩ : syracuseStep 4064597 = 2977) (by norm_num)
theorem B20579669 : Blo 1805604 20579669 := bbase (se 12 (by rfl) ⟨7536, by rfl⟩ : syracuseStep 20579669 = 15073) (by norm_num)
theorem B2286949 : Blo 1805604 2286949 := bbase (se 4 (by rfl) ⟨214401, by rfl⟩ : syracuseStep 2286949 = 428803) (by norm_num)
theorem B2033005 : Blo 1805604 2033005 := bbase (se 3 (by rfl) ⟨381188, by rfl⟩ : syracuseStep 2033005 = 762377) (by norm_num)
theorem B2033041 : Blo 1805604 2033041 := bbase (se 2 (by rfl) ⟨762390, by rfl⟩ : syracuseStep 2033041 = 1524781) (by norm_num)
theorem B3048853 : Blo 1805604 3048853 := bbase (se 6 (by rfl) ⟨71457, by rfl⟩ : syracuseStep 3048853 = 142915) (by norm_num)
theorem B4064669 : Blo 1805604 4064669 := bbase (se 3 (by rfl) ⟨762125, by rfl⟩ : syracuseStep 4064669 = 1524251) (by norm_num)
theorem B2033077 : Blo 1805604 2033077 := bbase (se 5 (by rfl) ⟨95300, by rfl⟩ : syracuseStep 2033077 = 190601) (by norm_num)
theorem B2287045 : Blo 1805604 2287045 := bbase (se 4 (by rfl) ⟨214410, by rfl⟩ : syracuseStep 2287045 = 428821) (by norm_num)
theorem B2893261 : Blo 1805604 2893261 := bbase (se 3 (by rfl) ⟨542486, by rfl⟩ : syracuseStep 2893261 = 1084973) (by norm_num)
theorem B8676821 : Blo 1805604 8676821 := bbase (se 7 (by rfl) ⟨101681, by rfl⟩ : syracuseStep 8676821 = 203363) (by norm_num)
theorem B9143765 : Blo 1805604 9143765 := bbase (se 7 (by rfl) ⟨107153, by rfl⟩ : syracuseStep 9143765 = 214307) (by norm_num)
theorem B2033113 : Blo 1805604 2033113 := bbase (se 2 (by rfl) ⟨762417, by rfl⟩ : syracuseStep 2033113 = 1524835) (by norm_num)
theorem B4064741 : Blo 1805604 4064741 := bbase (se 4 (by rfl) ⟨381069, by rfl⟩ : syracuseStep 4064741 = 762139) (by norm_num)
theorem B3048941 : Blo 1805604 3048941 := bbase (se 3 (by rfl) ⟨571676, by rfl⟩ : syracuseStep 3048941 = 1143353) (by norm_num)
theorem B2033149 : Blo 1805604 2033149 := bbase (se 3 (by rfl) ⟨381215, by rfl⟩ : syracuseStep 2033149 = 762431) (by norm_num)
theorem B3663389 : Blo 1805604 3663389 := bbase (se 3 (by rfl) ⟨686885, by rfl⟩ : syracuseStep 3663389 = 1373771) (by norm_num)
theorem B2033185 : Blo 1805604 2033185 := bbase (se 2 (by rfl) ⟨762444, by rfl⟩ : syracuseStep 2033185 = 1524889) (by norm_num)
theorem B4064813 : Blo 1805604 4064813 := bbase (se 3 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 4064813 = 1524305) (by norm_num)
theorem B6096437 : Blo 1805604 6096437 := bbase (se 5 (by rfl) ⟨285770, by rfl⟩ : syracuseStep 6096437 = 571541) (by norm_num)
theorem B3860021 : Blo 1805604 3860021 := bbase (se 5 (by rfl) ⟨180938, by rfl⟩ : syracuseStep 3860021 = 361877) (by norm_num)
theorem B6956597 : Blo 1805604 6956597 := bbase (se 5 (by rfl) ⟨326090, by rfl⟩ : syracuseStep 6956597 = 652181) (by norm_num)
theorem B4572733 : Blo 1805604 4572733 := bbase (se 3 (by rfl) ⟨857387, by rfl⟩ : syracuseStep 4572733 = 1714775) (by norm_num)
theorem B2033221 : Blo 1805604 2033221 := bbase (se 4 (by rfl) ⟨190614, by rfl⟩ : syracuseStep 2033221 = 381229) (by norm_num)
theorem B6858341 : Blo 1805604 6858341 := bbase (se 4 (by rfl) ⟨642969, by rfl⟩ : syracuseStep 6858341 = 1285939) (by norm_num)
theorem B2033257 : Blo 1805604 2033257 := bbase (se 2 (by rfl) ⟨762471, by rfl⟩ : syracuseStep 2033257 = 1524943) (by norm_num)
theorem B3049069 : Blo 1805604 3049069 := bbase (se 3 (by rfl) ⟨571700, by rfl⟩ : syracuseStep 3049069 = 1143401) (by norm_num)
theorem B2287217 : Blo 1805604 2287217 := bbase (se 2 (by rfl) ⟨857706, by rfl⟩ : syracuseStep 2287217 = 1715413) (by norm_num)
theorem B4064885 : Blo 1805604 4064885 := bbase (se 5 (by rfl) ⟨190541, by rfl⟩ : syracuseStep 4064885 = 381083) (by norm_num)
theorem B2033293 : Blo 1805604 2033293 := bbase (se 3 (by rfl) ⟨381242, by rfl⟩ : syracuseStep 2033293 = 762485) (by norm_num)
theorem B14845589 : Blo 1805604 14845589 := bbase (se 6 (by rfl) ⟨347943, by rfl⟩ : syracuseStep 14845589 = 695887) (by norm_num)
theorem B5785253 : Blo 1805604 5785253 := bbase (se 4 (by rfl) ⟨542367, by rfl⟩ : syracuseStep 5785253 = 1084735) (by norm_num)
theorem B2287273 : Blo 1805604 2287273 := bbase (se 2 (by rfl) ⟨857727, by rfl⟩ : syracuseStep 2287273 = 1715455) (by norm_num)
theorem B4572845 : Blo 1805604 4572845 := bbase (se 3 (by rfl) ⟨857408, by rfl⟩ : syracuseStep 4572845 = 1714817) (by norm_num)
theorem B2033329 : Blo 1805604 2033329 := bbase (se 2 (by rfl) ⟨762498, by rfl⟩ : syracuseStep 2033329 = 1524997) (by norm_num)
theorem B4064957 : Blo 1805604 4064957 := bbase (se 3 (by rfl) ⟨762179, by rfl⟩ : syracuseStep 4064957 = 1524359) (by norm_num)
theorem B3049157 : Blo 1805604 3049157 := bbase (se 4 (by rfl) ⟨285858, by rfl⟩ : syracuseStep 3049157 = 571717) (by norm_num)
theorem B17368789 : Blo 1805604 17368789 := bbase (se 7 (by rfl) ⟨203540, by rfl⟩ : syracuseStep 17368789 = 407081) (by norm_num)
theorem B2033365 : Blo 1805604 2033365 := bbase (se 7 (by rfl) ⟨23828, by rfl⟩ : syracuseStep 2033365 = 47657) (by norm_num)
theorem B3253981 : Blo 1805604 3253981 := bbase (se 3 (by rfl) ⟨610121, by rfl⟩ : syracuseStep 3253981 = 1220243) (by norm_num)
theorem B2033401 : Blo 1805604 2033401 := bbase (se 2 (by rfl) ⟨762525, by rfl⟩ : syracuseStep 2033401 = 1525051) (by norm_num)
theorem B4065029 : Blo 1805604 4065029 := bbase (se 4 (by rfl) ⟨381096, by rfl⟩ : syracuseStep 4065029 = 762193) (by norm_num)
theorem B2287369 : Blo 1805604 2287369 := bbase (se 2 (by rfl) ⟨857763, by rfl⟩ : syracuseStep 2287369 = 1715527) (by norm_num)
theorem B2033437 : Blo 1805604 2033437 := bbase (se 3 (by rfl) ⟨381269, by rfl⟩ : syracuseStep 2033437 = 762539) (by norm_num)
theorem B3254069 : Blo 1805604 3254069 := bbase (se 5 (by rfl) ⟨152534, by rfl⟩ : syracuseStep 3254069 = 305069) (by norm_num)
theorem B2033473 : Blo 1805604 2033473 := bbase (se 2 (by rfl) ⟨762552, by rfl⟩ : syracuseStep 2033473 = 1525105) (by norm_num)
theorem B3049285 : Blo 1805604 3049285 := bbase (se 4 (by rfl) ⟨285870, by rfl⟩ : syracuseStep 3049285 = 571741) (by norm_num)
theorem B4065101 : Blo 1805604 4065101 := bbase (se 3 (by rfl) ⟨762206, by rfl⟩ : syracuseStep 4065101 = 1524413) (by norm_num)
theorem B2033509 : Blo 1805604 2033509 := bbase (se 4 (by rfl) ⟨190641, by rfl⟩ : syracuseStep 2033509 = 381283) (by norm_num)
theorem B4573037 : Blo 1805604 4573037 := bbase (se 3 (by rfl) ⟨857444, by rfl⟩ : syracuseStep 4573037 = 1714889) (by norm_num)
theorem B2033545 : Blo 1805604 2033545 := bbase (se 2 (by rfl) ⟨762579, by rfl⟩ : syracuseStep 2033545 = 1525159) (by norm_num)
theorem B2893709 : Blo 1805604 2893709 := bbase (se 3 (by rfl) ⟨542570, by rfl⟩ : syracuseStep 2893709 = 1085141) (by norm_num)
theorem B4065173 : Blo 1805604 4065173 := bbase (se 6 (by rfl) ⟨95277, by rfl⟩ : syracuseStep 4065173 = 190555) (by norm_num)
theorem B3049373 : Blo 1805604 3049373 := bbase (se 3 (by rfl) ⟨571757, by rfl⟩ : syracuseStep 3049373 = 1143515) (by norm_num)
theorem B3860389 : Blo 1805604 3860389 := bbase (se 4 (by rfl) ⟨361911, by rfl⟩ : syracuseStep 3860389 = 723823) (by norm_num)
theorem B2287541 : Blo 1805604 2287541 := bbase (se 5 (by rfl) ⟨107228, by rfl⟩ : syracuseStep 2287541 = 214457) (by norm_num)
theorem B10291157 : Blo 1805604 10291157 := bbase (se 7 (by rfl) ⟨120599, by rfl⟩ : syracuseStep 10291157 = 241199) (by norm_num)
theorem B4065245 : Blo 1805604 4065245 := bbase (se 3 (by rfl) ⟨762233, by rfl⟩ : syracuseStep 4065245 = 1524467) (by norm_num)
theorem B2934749 : Blo 1805604 2934749 := bbase (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) (by norm_num)
theorem B6096869 : Blo 1805604 6096869 := bbase (se 4 (by rfl) ⟨571581, by rfl⟩ : syracuseStep 6096869 = 1143163) (by norm_num)
theorem B2287597 : Blo 1805604 2287597 := bbase (se 3 (by rfl) ⟨428924, by rfl⟩ : syracuseStep 2287597 = 857849) (by norm_num)
theorem B5646341 : Blo 1805604 5646341 := bbase (se 4 (by rfl) ⟨529344, by rfl⟩ : syracuseStep 5646341 = 1058689) (by norm_num)
theorem B3049501 : Blo 1805604 3049501 := bbase (se 3 (by rfl) ⟨571781, by rfl⟩ : syracuseStep 3049501 = 1143563) (by norm_num)
theorem B4065317 : Blo 1805604 4065317 := bbase (se 4 (by rfl) ⟨381123, by rfl⟩ : syracuseStep 4065317 = 762247) (by norm_num)
theorem B2287693 : Blo 1805604 2287693 := bbase (se 3 (by rfl) ⟨428942, by rfl⟩ : syracuseStep 2287693 = 857885) (by norm_num)
theorem B3254357 : Blo 1805604 3254357 := bbase (se 8 (by rfl) ⟨19068, by rfl⟩ : syracuseStep 3254357 = 38137) (by norm_num)
theorem B4065389 : Blo 1805604 4065389 := bbase (se 3 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 4065389 = 1524521) (by norm_num)
theorem B3049589 : Blo 1805604 3049589 := bbase (se 5 (by rfl) ⟨142949, by rfl⟩ : syracuseStep 3049589 = 285899) (by norm_num)
theorem B4065461 : Blo 1805604 4065461 := bbase (se 5 (by rfl) ⟨190568, by rfl⟩ : syracuseStep 4065461 = 381137) (by norm_num)
theorem B4573381 : Blo 1805604 4573381 := bbase (se 4 (by rfl) ⟨428754, by rfl⟩ : syracuseStep 4573381 = 857509) (by norm_num)
theorem B3049717 : Blo 1805604 3049717 := bbase (se 5 (by rfl) ⟨142955, by rfl⟩ : syracuseStep 3049717 = 285911) (by norm_num)
theorem B4065533 : Blo 1805604 4065533 := bbase (se 3 (by rfl) ⟨762287, by rfl⟩ : syracuseStep 4065533 = 1524575) (by norm_num)
theorem B3254573 : Blo 1805604 3254573 := bbase (se 3 (by rfl) ⟨610232, by rfl⟩ : syracuseStep 3254573 = 1220465) (by norm_num)
theorem B4573493 : Blo 1805604 4573493 := bbase (se 5 (by rfl) ⟨214382, by rfl⟩ : syracuseStep 4573493 = 428765) (by norm_num)
theorem B4065605 : Blo 1805604 4065605 := bbase (se 4 (by rfl) ⟨381150, by rfl⟩ : syracuseStep 4065605 = 762301) (by norm_num)
theorem B8685893 : Blo 1805604 8685893 := bbase (se 4 (by rfl) ⟨814302, by rfl⟩ : syracuseStep 8685893 = 1628605) (by norm_num)
theorem B3049805 : Blo 1805604 3049805 := bbase (se 3 (by rfl) ⟨571838, by rfl⟩ : syracuseStep 3049805 = 1143677) (by norm_num)
theorem B4065677 : Blo 1805604 4065677 := bbase (se 3 (by rfl) ⟨762314, by rfl⟩ : syracuseStep 4065677 = 1524629) (by norm_num)
theorem B6097301 : Blo 1805604 6097301 := bbase (se 6 (by rfl) ⟨142905, by rfl⟩ : syracuseStep 6097301 = 285811) (by norm_num)
theorem B2746813 : Blo 1805604 2746813 := bbase (se 3 (by rfl) ⟨515027, by rfl⟩ : syracuseStep 2746813 = 1030055) (by norm_num)
theorem B3049933 : Blo 1805604 3049933 := bbase (se 3 (by rfl) ⟨571862, by rfl⟩ : syracuseStep 3049933 = 1143725) (by norm_num)
theorem B4065749 : Blo 1805604 4065749 := bbase (se 7 (by rfl) ⟨47645, by rfl⟩ : syracuseStep 4065749 = 95291) (by norm_num)
theorem B4573685 : Blo 1805604 4573685 := bbase (se 5 (by rfl) ⟨214391, by rfl⟩ : syracuseStep 4573685 = 428783) (by norm_num)
theorem B4065821 : Blo 1805604 4065821 := bbase (se 3 (by rfl) ⟨762341, by rfl⟩ : syracuseStep 4065821 = 1524683) (by norm_num)
theorem B3050021 : Blo 1805604 3050021 := bbase (se 4 (by rfl) ⟨285939, by rfl⟩ : syracuseStep 3050021 = 571879) (by norm_num)
theorem B12364373 : Blo 1805604 12364373 := bbase (se 8 (by rfl) ⟨72447, by rfl⟩ : syracuseStep 12364373 = 144895) (by norm_num)
theorem B4065893 : Blo 1805604 4065893 := bbase (se 4 (by rfl) ⟨381177, by rfl⟩ : syracuseStep 4065893 = 762355) (by norm_num)
theorem B3050149 : Blo 1805604 3050149 := bbase (se 4 (by rfl) ⟨285951, by rfl⟩ : syracuseStep 3050149 = 571903) (by norm_num)
theorem B4065965 : Blo 1805604 4065965 := bbase (se 3 (by rfl) ⟨762368, by rfl⟩ : syracuseStep 4065965 = 1524737) (by norm_num)
theorem B5147333 : Blo 1805604 5147333 := bbase (se 4 (by rfl) ⟨482562, by rfl⟩ : syracuseStep 5147333 = 965125) (by norm_num)
theorem B9145061 : Blo 1805604 9145061 := bbase (se 4 (by rfl) ⟨857349, by rfl⟩ : syracuseStep 9145061 = 1714699) (by norm_num)
theorem B4066037 : Blo 1805604 4066037 := bbase (se 5 (by rfl) ⟨190595, by rfl⟩ : syracuseStep 4066037 = 381191) (by norm_num)
theorem B3050237 : Blo 1805604 3050237 := bbase (se 3 (by rfl) ⟨571919, by rfl⟩ : syracuseStep 3050237 = 1143839) (by norm_num)
theorem B6859525 : Blo 1805604 6859525 := bbase (se 4 (by rfl) ⟨643080, by rfl⟩ : syracuseStep 6859525 = 1286161) (by norm_num)
theorem B7326517 : Blo 1805604 7326517 := bbase (se 5 (by rfl) ⟨343430, by rfl⟩ : syracuseStep 7326517 = 686861) (by norm_num)
theorem B4066109 : Blo 1805604 4066109 := bbase (se 3 (by rfl) ⟨762395, by rfl⟩ : syracuseStep 4066109 = 1524791) (by norm_num)
theorem B3132229 : Blo 1805604 3132229 := bbase (se 4 (by rfl) ⟨293646, by rfl⟩ : syracuseStep 3132229 = 587293) (by norm_num)
theorem B6097733 : Blo 1805604 6097733 := bbase (se 4 (by rfl) ⟨571662, by rfl⟩ : syracuseStep 6097733 = 1143325) (by norm_num)
theorem B4574029 : Blo 1805604 4574029 := bbase (se 3 (by rfl) ⟨857630, by rfl⟩ : syracuseStep 4574029 = 1715261) (by norm_num)
theorem B4066181 : Blo 1805604 4066181 := bbase (se 4 (by rfl) ⟨381204, by rfl⟩ : syracuseStep 4066181 = 762409) (by norm_num)
theorem B7818133 : Blo 1805604 7818133 := bbase (se 6 (by rfl) ⟨183237, by rfl⟩ : syracuseStep 7818133 = 366475) (by norm_num)
theorem B3476405 : Blo 1805604 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B4574141 : Blo 1805604 4574141 := bbase (se 3 (by rfl) ⟨857651, by rfl⟩ : syracuseStep 4574141 = 1715303) (by norm_num)
theorem B4066253 : Blo 1805604 4066253 := bbase (se 3 (by rfl) ⟨762422, by rfl⟩ : syracuseStep 4066253 = 1524845) (by norm_num)
theorem B5786597 : Blo 1805604 5786597 := bbase (se 4 (by rfl) ⟨542493, by rfl⟩ : syracuseStep 5786597 = 1084987) (by norm_num)
theorem B4066325 : Blo 1805604 4066325 := bbase (se 6 (by rfl) ⟨95304, by rfl⟩ : syracuseStep 4066325 = 190609) (by norm_num)
theorem B6859829 : Blo 1805604 6859829 := bbase (se 5 (by rfl) ⟨321554, by rfl⟩ : syracuseStep 6859829 = 643109) (by norm_num)
theorem B1928281 : Blo 1805604 1928281 := bbase (se 2 (by rfl) ⟨723105, by rfl⟩ : syracuseStep 1928281 = 1446211) (by norm_num)
theorem B4066397 : Blo 1805604 4066397 := bbase (se 3 (by rfl) ⟨762449, by rfl⟩ : syracuseStep 4066397 = 1524899) (by norm_num)
theorem B6261877 : Blo 1805604 6261877 := bbase (se 5 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 6261877 = 587051) (by norm_num)
theorem B4574333 : Blo 1805604 4574333 := bbase (se 3 (by rfl) ⟨857687, by rfl⟩ : syracuseStep 4574333 = 1715375) (by norm_num)
theorem B4066469 : Blo 1805604 4066469 := bbase (se 4 (by rfl) ⟨381231, by rfl⟩ : syracuseStep 4066469 = 762463) (by norm_num)
theorem B3714221 : Blo 1805604 3714221 := bbase (se 3 (by rfl) ⟨696416, by rfl⟩ : syracuseStep 3714221 = 1392833) (by norm_num)
theorem B3255509 : Blo 1805604 3255509 := bbase (se 7 (by rfl) ⟨38150, by rfl⟩ : syracuseStep 3255509 = 76301) (by norm_num)
theorem B4066541 : Blo 1805604 4066541 := bbase (se 3 (by rfl) ⟨762476, by rfl⟩ : syracuseStep 4066541 = 1524953) (by norm_num)
theorem B6098165 : Blo 1805604 6098165 := bbase (se 5 (by rfl) ⟨285851, by rfl⟩ : syracuseStep 6098165 = 571703) (by norm_num)
theorem B3255589 : Blo 1805604 3255589 := bbase (se 4 (by rfl) ⟨305211, by rfl⟩ : syracuseStep 3255589 = 610423) (by norm_num)
theorem B4066613 : Blo 1805604 4066613 := bbase (se 5 (by rfl) ⟨190622, by rfl⟩ : syracuseStep 4066613 = 381245) (by norm_num)
theorem B2895221 : Blo 1805604 2895221 := bbase (se 5 (by rfl) ⟨135713, by rfl⟩ : syracuseStep 2895221 = 271427) (by norm_num)
theorem B4066685 : Blo 1805604 4066685 := bbase (se 3 (by rfl) ⟨762503, by rfl⟩ : syracuseStep 4066685 = 1525007) (by norm_num)
theorem B4066757 : Blo 1805604 4066757 := bbase (se 4 (by rfl) ⟨381258, by rfl⟩ : syracuseStep 4066757 = 762517) (by norm_num)
theorem B1928657 : Blo 1805604 1928657 := bbase (se 2 (by rfl) ⟨723246, by rfl⟩ : syracuseStep 1928657 = 1446493) (by norm_num)
theorem B4574677 : Blo 1805604 4574677 := bbase (se 7 (by rfl) ⟨53609, by rfl⟩ : syracuseStep 4574677 = 107219) (by norm_num)
theorem B3476957 : Blo 1805604 3476957 := bbase (se 3 (by rfl) ⟨651929, by rfl⟩ : syracuseStep 3476957 = 1303859) (by norm_num)
theorem B2895349 : Blo 1805604 2895349 := bbase (se 5 (by rfl) ⟨135719, by rfl⟩ : syracuseStep 2895349 = 271439) (by norm_num)
theorem B4066829 : Blo 1805604 4066829 := bbase (se 3 (by rfl) ⟨762530, by rfl⟩ : syracuseStep 4066829 = 1525061) (by norm_num)
theorem B1928729 : Blo 1805604 1928729 := bbase (se 2 (by rfl) ⟨723273, by rfl⟩ : syracuseStep 1928729 = 1446547) (by norm_num)
theorem B4574789 : Blo 1805604 4574789 := bbase (se 4 (by rfl) ⟨428886, by rfl⟩ : syracuseStep 4574789 = 857773) (by norm_num)
theorem B2059853 : Blo 1805604 2059853 := bbase (se 3 (by rfl) ⟨386222, by rfl⟩ : syracuseStep 2059853 = 772445) (by norm_num)
theorem B2747981 : Blo 1805604 2747981 := bbase (se 3 (by rfl) ⟨515246, by rfl⟩ : syracuseStep 2747981 = 1030493) (by norm_num)
theorem B4066901 : Blo 1805604 4066901 := bbase (se 8 (by rfl) ⟨23829, by rfl⟩ : syracuseStep 4066901 = 47659) (by norm_num)
theorem B3427933 : Blo 1805604 3427933 := bbase (se 3 (by rfl) ⟨642737, by rfl⟩ : syracuseStep 3427933 = 1285475) (by norm_num)
theorem B7048853 : Blo 1805604 7048853 := bbase (se 6 (by rfl) ⟨165207, by rfl⟩ : syracuseStep 7048853 = 330415) (by norm_num)
theorem B4066973 : Blo 1805604 4066973 := bbase (se 3 (by rfl) ⟨762557, by rfl⟩ : syracuseStep 4066973 = 1525115) (by norm_num)
theorem B6098597 : Blo 1805604 6098597 := bbase (se 4 (by rfl) ⟨571743, by rfl⟩ : syracuseStep 6098597 = 1143487) (by norm_num)
theorem B2608805 : Blo 1805604 2608805 := bbase (se 4 (by rfl) ⟨244575, by rfl⟩ : syracuseStep 2608805 = 489151) (by norm_num)
theorem B1928917 : Blo 1805604 1928917 := bbase (se 7 (by rfl) ⟨22604, by rfl⟩ : syracuseStep 1928917 = 45209) (by norm_num)
theorem B4067045 : Blo 1805604 4067045 := bbase (se 4 (by rfl) ⟨381285, by rfl⟩ : syracuseStep 4067045 = 762571) (by norm_num)
theorem B3428077 : Blo 1805604 3428077 := bbase (se 3 (by rfl) ⟨642764, by rfl⟩ : syracuseStep 3428077 = 1285529) (by norm_num)
theorem B4574981 : Blo 1805604 4574981 := bbase (se 4 (by rfl) ⟨428904, by rfl⟩ : syracuseStep 4574981 = 857809) (by norm_num)
theorem B1830673 : Blo 1805604 1830673 := bbase (se 2 (by rfl) ⟨686502, by rfl⟩ : syracuseStep 1830673 = 1373005) (by norm_num)
theorem B3428237 : Blo 1805604 3428237 := bbase (se 3 (by rfl) ⟨642794, by rfl⟩ : syracuseStep 3428237 = 1285589) (by norm_num)
theorem B1929101 : Blo 1805604 1929101 := bbase (se 3 (by rfl) ⟨361706, by rfl⟩ : syracuseStep 1929101 = 723413) (by norm_num)
theorem B4063229 : Blo 1805604 4063229 := bbase (se 3 (by rfl) ⟨761855, by rfl⟩ : syracuseStep 4063229 = 1523711) (by norm_num)
theorem B9146357 : Blo 1805604 9146357 := bbase (se 5 (by rfl) ⟨428735, by rfl⟩ : syracuseStep 9146357 = 857471) (by norm_num)
theorem B3428381 : Blo 1805604 3428381 := bbase (se 3 (by rfl) ⟨642821, by rfl⟩ : syracuseStep 3428381 = 1285643) (by norm_num)
theorem B4952117 : Blo 1805604 4952117 := bbase (se 5 (by rfl) ⟨232130, by rfl⟩ : syracuseStep 4952117 = 464261) (by norm_num)
theorem B11751509 : Blo 1805604 11751509 := bbase (se 8 (by rfl) ⟨68856, by rfl⟩ : syracuseStep 11751509 = 137713) (by norm_num)
theorem B6099029 : Blo 1805604 6099029 := bbase (se 8 (by rfl) ⟨35736, by rfl⟩ : syracuseStep 6099029 = 71473) (by norm_num)
theorem B4575325 : Blo 1805604 4575325 := bbase (se 3 (by rfl) ⟨857873, by rfl⟩ : syracuseStep 4575325 = 1715747) (by norm_num)
theorem B2060401 : Blo 1805604 2060401 := bbase (se 2 (by rfl) ⟨772650, by rfl⟩ : syracuseStep 2060401 = 1545301) (by norm_num)
theorem B11571349 : Blo 1805604 11571349 := bbase (se 6 (by rfl) ⟨271203, by rfl⟩ : syracuseStep 11571349 = 542407) (by norm_num)
theorem B4575437 : Blo 1805604 4575437 := bbase (se 3 (by rfl) ⟨857894, by rfl⟩ : syracuseStep 4575437 = 1715789) (by norm_num)
theorem B9523493 : Blo 1805604 9523493 := bbase (se 4 (by rfl) ⟨892827, by rfl⟩ : syracuseStep 9523493 = 1785655) (by norm_num)
theorem B3428669 : Blo 1805604 3428669 := bbase (se 3 (by rfl) ⟨642875, by rfl⟩ : syracuseStep 3428669 = 1285751) (by norm_num)
theorem B3428821 : Blo 1805604 3428821 := bbase (se 7 (by rfl) ⟨40181, by rfl⟩ : syracuseStep 3428821 = 80363) (by norm_num)
theorem B3477973 : Blo 1805604 3477973 := bbase (se 7 (by rfl) ⟨40757, by rfl⟩ : syracuseStep 3477973 = 81515) (by norm_num)
theorem B6099461 : Blo 1805604 6099461 := bbase (se 4 (by rfl) ⟨571824, by rfl⟩ : syracuseStep 6099461 = 1143649) (by norm_num)
theorem B1831529 : Blo 1805604 1831529 := bbase (se 2 (by rfl) ⟨686823, by rfl⟩ : syracuseStep 1831529 = 1373647) (by norm_num)
theorem B6509173 : Blo 1805604 6509173 := bbase (se 5 (by rfl) ⟨305117, by rfl⟩ : syracuseStep 6509173 = 610235) (by norm_num)
theorem B1929853 : Blo 1805604 1929853 := bbase (se 3 (by rfl) ⟨361847, by rfl⟩ : syracuseStep 1929853 = 723695) (by norm_num)
theorem B7713413 : Blo 1805604 7713413 := bbase (se 4 (by rfl) ⟨723132, by rfl⟩ : syracuseStep 7713413 = 1446265) (by norm_num)
theorem B2200253 : Blo 1805604 2200253 := bbase (se 3 (by rfl) ⟨412547, by rfl⟩ : syracuseStep 2200253 = 825095) (by norm_num)
theorem B4338373 : Blo 1805604 4338373 := bbase (se 4 (by rfl) ⟨406722, by rfl⟩ : syracuseStep 4338373 = 813445) (by norm_num)
theorem B1929925 : Blo 1805604 1929925 := bbase (se 4 (by rfl) ⟨180930, by rfl⟩ : syracuseStep 1929925 = 361861) (by norm_num)
theorem B3429125 : Blo 1805604 3429125 := bbase (se 4 (by rfl) ⟨321480, by rfl⟩ : syracuseStep 3429125 = 642961) (by norm_num)
theorem B4633357 : Blo 1805604 4633357 := bbase (se 3 (by rfl) ⟨868754, by rfl⟩ : syracuseStep 4633357 = 1737509) (by norm_num)
theorem B3175229 : Blo 1805604 3175229 := bbase (se 3 (by rfl) ⟨595355, by rfl⟩ : syracuseStep 3175229 = 1190711) (by norm_num)
theorem B1930105 : Blo 1805604 1930105 := bbase (se 2 (by rfl) ⟨723789, by rfl⟩ : syracuseStep 1930105 = 1447579) (by norm_num)
theorem B1856389 : Blo 1805604 1856389 := bbase (se 4 (by rfl) ⟨174036, by rfl⟩ : syracuseStep 1856389 = 348073) (by norm_num)
theorem B3478421 : Blo 1805604 3478421 := bbase (se 6 (by rfl) ⟨81525, by rfl⟩ : syracuseStep 3478421 = 163051) (by norm_num)
theorem B5788597 : Blo 1805604 5788597 := bbase (se 5 (by rfl) ⟨271340, by rfl⟩ : syracuseStep 5788597 = 542681) (by norm_num)
theorem B6099893 : Blo 1805604 6099893 := bbase (se 5 (by rfl) ⟨285932, by rfl⟩ : syracuseStep 6099893 = 571865) (by norm_num)
theorem B2823101 : Blo 1805604 2823101 := bbase (se 3 (by rfl) ⟨529331, by rfl⟩ : syracuseStep 2823101 = 1058663) (by norm_num)
theorem B2708429 : Blo 1805604 2708429 := bbase (se 3 (by rfl) ⟨507830, by rfl⟩ : syracuseStep 2708429 = 1015661) (by norm_num)
theorem B1831889 : Blo 1805604 1831889 := bbase (se 2 (by rfl) ⟨686958, by rfl⟩ : syracuseStep 1831889 = 1373917) (by norm_num)
theorem B2200537 : Blo 1805604 2200537 := bbase (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) (by norm_num)
theorem B2708453 : Blo 1805604 2708453 := bbase (se 4 (by rfl) ⟨253917, by rfl⟩ : syracuseStep 2708453 = 507835) (by norm_num)
theorem B2708477 : Blo 1805604 2708477 := bbase (se 3 (by rfl) ⟨507839, by rfl⟩ : syracuseStep 2708477 = 1015679) (by norm_num)
theorem B2708501 : Blo 1805604 2708501 := bbase (se 6 (by rfl) ⟨63480, by rfl⟩ : syracuseStep 2708501 = 126961) (by norm_num)
theorem B2708525 : Blo 1805604 2708525 := bbase (se 3 (by rfl) ⟨507848, by rfl⟩ : syracuseStep 2708525 = 1015697) (by norm_num)
theorem B2708549 : Blo 1805604 2708549 := bbase (se 4 (by rfl) ⟨253926, by rfl⟩ : syracuseStep 2708549 = 507853) (by norm_num)
theorem B2708573 : Blo 1805604 2708573 := bbase (se 3 (by rfl) ⟨507857, by rfl⟩ : syracuseStep 2708573 = 1015715) (by norm_num)
theorem B2708597 : Blo 1805604 2708597 := bbase (se 5 (by rfl) ⟨126965, by rfl⟩ : syracuseStep 2708597 = 253931) (by norm_num)
theorem B6861941 : Blo 1805604 6861941 := bbase (se 5 (by rfl) ⟨321653, by rfl⟩ : syracuseStep 6861941 = 643307) (by norm_num)
theorem B2708621 : Blo 1805604 2708621 := bbase (se 3 (by rfl) ⟨507866, by rfl⟩ : syracuseStep 2708621 = 1015733) (by norm_num)
theorem B2708645 : Blo 1805604 2708645 := bbase (se 4 (by rfl) ⟨253935, by rfl⟩ : syracuseStep 2708645 = 507871) (by norm_num)
theorem B2708669 : Blo 1805604 2708669 := bbase (se 3 (by rfl) ⟨507875, by rfl⟩ : syracuseStep 2708669 = 1015751) (by norm_num)
theorem B2708693 : Blo 1805604 2708693 := bbase (se 7 (by rfl) ⟨31742, by rfl⟩ : syracuseStep 2708693 = 63485) (by norm_num)
theorem B2708717 : Blo 1805604 2708717 := bbase (se 3 (by rfl) ⟨507884, by rfl⟩ : syracuseStep 2708717 = 1015769) (by norm_num)
theorem B2708741 : Blo 1805604 2708741 := bbase (se 4 (by rfl) ⟨253944, by rfl⟩ : syracuseStep 2708741 = 507889) (by norm_num)
theorem B4338949 : Blo 1805604 4338949 := bbase (se 4 (by rfl) ⟨406776, by rfl⟩ : syracuseStep 4338949 = 813553) (by norm_num)
theorem B9147653 : Blo 1805604 9147653 := bbase (se 4 (by rfl) ⟨857592, by rfl⟩ : syracuseStep 9147653 = 1715185) (by norm_num)
theorem B2708765 : Blo 1805604 2708765 := bbase (se 3 (by rfl) ⟨507893, by rfl⟩ : syracuseStep 2708765 = 1015787) (by norm_num)
theorem B2708789 : Blo 1805604 2708789 := bbase (se 5 (by rfl) ⟨126974, by rfl⟩ : syracuseStep 2708789 = 253949) (by norm_num)
theorem B2708813 : Blo 1805604 2708813 := bbase (se 3 (by rfl) ⟨507902, by rfl⟩ : syracuseStep 2708813 = 1015805) (by norm_num)
theorem B2708837 : Blo 1805604 2708837 := bbase (se 4 (by rfl) ⟨253953, by rfl⟩ : syracuseStep 2708837 = 507907) (by norm_num)
theorem B6100325 : Blo 1805604 6100325 := bbase (se 4 (by rfl) ⟨571905, by rfl⟩ : syracuseStep 6100325 = 1143811) (by norm_num)
theorem B2708861 : Blo 1805604 2708861 := bbase (se 3 (by rfl) ⟨507911, by rfl⟩ : syracuseStep 2708861 = 1015823) (by norm_num)
theorem B2708885 : Blo 1805604 2708885 := bbase (se 6 (by rfl) ⟨63489, by rfl⟩ : syracuseStep 2708885 = 126979) (by norm_num)
theorem B13202837 : Blo 1805604 13202837 := bbase (se 6 (by rfl) ⟨309441, by rfl⟩ : syracuseStep 13202837 = 618883) (by norm_num)
theorem B10990997 : Blo 1805604 10990997 := bbase (se 6 (by rfl) ⟨257601, by rfl⟩ : syracuseStep 10990997 = 515203) (by norm_num)
theorem B6862229 : Blo 1805604 6862229 := bbase (se 6 (by rfl) ⟨160833, by rfl⟩ : syracuseStep 6862229 = 321667) (by norm_num)
theorem B2348453 : Blo 1805604 2348453 := bbase (se 4 (by rfl) ⟨220167, by rfl⟩ : syracuseStep 2348453 = 440335) (by norm_num)
theorem B2708909 : Blo 1805604 2708909 := bbase (se 3 (by rfl) ⟨507920, by rfl⟩ : syracuseStep 2708909 = 1015841) (by norm_num)
theorem B2708933 : Blo 1805604 2708933 := bbase (se 4 (by rfl) ⟨253962, by rfl⟩ : syracuseStep 2708933 = 507925) (by norm_num)
theorem B2708957 : Blo 1805604 2708957 := bbase (se 3 (by rfl) ⟨507929, by rfl⟩ : syracuseStep 2708957 = 1015859) (by norm_num)
theorem B2708981 : Blo 1805604 2708981 := bbase (se 5 (by rfl) ⟨126983, by rfl⟩ : syracuseStep 2708981 = 253967) (by norm_num)
theorem B3429877 : Blo 1805604 3429877 := bbase (se 5 (by rfl) ⟨160775, by rfl⟩ : syracuseStep 3429877 = 321551) (by norm_num)
theorem B2709005 : Blo 1805604 2709005 := bbase (se 3 (by rfl) ⟨507938, by rfl⟩ : syracuseStep 2709005 = 1015877) (by norm_num)
theorem B2709029 : Blo 1805604 2709029 := bbase (se 4 (by rfl) ⟨253971, by rfl⟩ : syracuseStep 2709029 = 507943) (by norm_num)
theorem B2709053 : Blo 1805604 2709053 := bbase (se 3 (by rfl) ⟨507947, by rfl⟩ : syracuseStep 2709053 = 1015895) (by norm_num)
theorem B4339277 : Blo 1805604 4339277 := bbase (se 3 (by rfl) ⟨813614, by rfl⟩ : syracuseStep 4339277 = 1627229) (by norm_num)
theorem B2709077 : Blo 1805604 2709077 := bbase (se 8 (by rfl) ⟨15873, by rfl⟩ : syracuseStep 2709077 = 31747) (by norm_num)
theorem B1955425 : Blo 1805604 1955425 := bbase (se 2 (by rfl) ⟨733284, by rfl⟩ : syracuseStep 1955425 = 1466569) (by norm_num)
theorem B2709101 : Blo 1805604 2709101 := bbase (se 3 (by rfl) ⟨507956, by rfl⟩ : syracuseStep 2709101 = 1015913) (by norm_num)
theorem B4339333 : Blo 1805604 4339333 := bbase (se 4 (by rfl) ⟨406812, by rfl⟩ : syracuseStep 4339333 = 813625) (by norm_num)
theorem B2709125 : Blo 1805604 2709125 := bbase (se 4 (by rfl) ⟨253980, by rfl⟩ : syracuseStep 2709125 = 507961) (by norm_num)
theorem B3430021 : Blo 1805604 3430021 := bbase (se 4 (by rfl) ⟨321564, by rfl⟩ : syracuseStep 3430021 = 643129) (by norm_num)
theorem B2709149 : Blo 1805604 2709149 := bbase (se 3 (by rfl) ⟨507965, by rfl⟩ : syracuseStep 2709149 = 1015931) (by norm_num)
theorem B2709173 : Blo 1805604 2709173 := bbase (se 5 (by rfl) ⟨126992, by rfl⟩ : syracuseStep 2709173 = 253985) (by norm_num)
theorem B2709197 : Blo 1805604 2709197 := bbase (se 3 (by rfl) ⟨507974, by rfl⟩ : syracuseStep 2709197 = 1015949) (by norm_num)
theorem B2709221 : Blo 1805604 2709221 := bbase (se 4 (by rfl) ⟨253989, by rfl⟩ : syracuseStep 2709221 = 507979) (by norm_num)
theorem B2709245 : Blo 1805604 2709245 := bbase (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) (by norm_num)
theorem B2709269 : Blo 1805604 2709269 := bbase (se 6 (by rfl) ⟨63498, by rfl⟩ : syracuseStep 2709269 = 126997) (by norm_num)
theorem B3430181 : Blo 1805604 3430181 := bbase (se 4 (by rfl) ⟨321579, by rfl⟩ : syracuseStep 3430181 = 643159) (by norm_num)
theorem B2709293 : Blo 1805604 2709293 := bbase (se 3 (by rfl) ⟨507992, by rfl⟩ : syracuseStep 2709293 = 1015985) (by norm_num)
theorem B2709317 : Blo 1805604 2709317 := bbase (se 4 (by rfl) ⟨253998, by rfl⟩ : syracuseStep 2709317 = 507997) (by norm_num)
theorem B2709341 : Blo 1805604 2709341 := bbase (se 3 (by rfl) ⟨508001, by rfl⟩ : syracuseStep 2709341 = 1016003) (by norm_num)
theorem B4339565 : Blo 1805604 4339565 := bbase (se 3 (by rfl) ⟨813668, by rfl⟩ : syracuseStep 4339565 = 1627337) (by norm_num)
theorem B2709365 : Blo 1805604 2709365 := bbase (se 5 (by rfl) ⟨127001, by rfl⟩ : syracuseStep 2709365 = 254003) (by norm_num)
theorem B2709389 : Blo 1805604 2709389 := bbase (se 3 (by rfl) ⟨508010, by rfl⟩ : syracuseStep 2709389 = 1016021) (by norm_num)
theorem B2709413 : Blo 1805604 2709413 := bbase (se 4 (by rfl) ⟨254007, by rfl⟩ : syracuseStep 2709413 = 508015) (by norm_num)
theorem B3430325 : Blo 1805604 3430325 := bbase (se 5 (by rfl) ⟨160796, by rfl⟩ : syracuseStep 3430325 = 321593) (by norm_num)
theorem B2709437 : Blo 1805604 2709437 := bbase (se 3 (by rfl) ⟨508019, by rfl⟩ : syracuseStep 2709437 = 1016039) (by norm_num)
theorem B2709461 : Blo 1805604 2709461 := bbase (se 7 (by rfl) ⟨31751, by rfl⟩ : syracuseStep 2709461 = 63503) (by norm_num)
theorem B2709485 : Blo 1805604 2709485 := bbase (se 3 (by rfl) ⟨508028, by rfl⟩ : syracuseStep 2709485 = 1016057) (by norm_num)
theorem B2709509 : Blo 1805604 2709509 := bbase (se 4 (by rfl) ⟨254016, by rfl⟩ : syracuseStep 2709509 = 508033) (by norm_num)
theorem B9771029 : Blo 1805604 9771029 := bbase (se 6 (by rfl) ⟨229008, by rfl⟩ : syracuseStep 9771029 = 458017) (by norm_num)
theorem B2709533 : Blo 1805604 2709533 := bbase (se 3 (by rfl) ⟨508037, by rfl⟩ : syracuseStep 2709533 = 1016075) (by norm_num)
theorem B4339757 : Blo 1805604 4339757 := bbase (se 3 (by rfl) ⟨813704, by rfl⟩ : syracuseStep 4339757 = 1627409) (by norm_num)
theorem B2709557 : Blo 1805604 2709557 := bbase (se 5 (by rfl) ⟨127010, by rfl⟩ : syracuseStep 2709557 = 254021) (by norm_num)
theorem B2709581 : Blo 1805604 2709581 := bbase (se 3 (by rfl) ⟨508046, by rfl⟩ : syracuseStep 2709581 = 1016093) (by norm_num)
theorem B5142629 : Blo 1805604 5142629 := bbase (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) (by norm_num)
theorem B2709605 : Blo 1805604 2709605 := bbase (se 4 (by rfl) ⟨254025, by rfl⟩ : syracuseStep 2709605 = 508051) (by norm_num)
theorem B3856501 : Blo 1805604 3856501 := bbase (se 5 (by rfl) ⟨180773, by rfl⟩ : syracuseStep 3856501 = 361547) (by norm_num)
theorem B2709629 : Blo 1805604 2709629 := bbase (se 3 (by rfl) ⟨508055, by rfl⟩ : syracuseStep 2709629 = 1016111) (by norm_num)
theorem B2709653 : Blo 1805604 2709653 := bbase (se 6 (by rfl) ⟨63507, by rfl⟩ : syracuseStep 2709653 = 127015) (by norm_num)
theorem B1955989 : Blo 1805604 1955989 := bbase (se 6 (by rfl) ⟨45843, by rfl⟩ : syracuseStep 1955989 = 91687) (by norm_num)
theorem B2709677 : Blo 1805604 2709677 := bbase (se 3 (by rfl) ⟨508064, by rfl⟩ : syracuseStep 2709677 = 1016129) (by norm_num)
theorem B2709701 : Blo 1805604 2709701 := bbase (se 4 (by rfl) ⟨254034, by rfl⟩ : syracuseStep 2709701 = 508069) (by norm_num)
theorem B3430613 : Blo 1805604 3430613 := bbase (se 7 (by rfl) ⟨40202, by rfl⟩ : syracuseStep 3430613 = 80405) (by norm_num)
theorem B2709725 : Blo 1805604 2709725 := bbase (se 3 (by rfl) ⟨508073, by rfl⟩ : syracuseStep 2709725 = 1016147) (by norm_num)
theorem B2709749 : Blo 1805604 2709749 := bbase (se 5 (by rfl) ⟨127019, by rfl⟩ : syracuseStep 2709749 = 254039) (by norm_num)
theorem B6183173 : Blo 1805604 6183173 := bbase (se 4 (by rfl) ⟨579672, by rfl⟩ : syracuseStep 6183173 = 1159345) (by norm_num)
theorem B2709773 : Blo 1805604 2709773 := bbase (se 3 (by rfl) ⟨508082, by rfl⟩ : syracuseStep 2709773 = 1016165) (by norm_num)
theorem B3299621 : Blo 1805604 3299621 := bbase (se 4 (by rfl) ⟨309339, by rfl⟩ : syracuseStep 3299621 = 618679) (by norm_num)
theorem B2709797 : Blo 1805604 2709797 := bbase (se 4 (by rfl) ⟨254043, by rfl⟩ : syracuseStep 2709797 = 508087) (by norm_num)
theorem B2709821 : Blo 1805604 2709821 := bbase (se 3 (by rfl) ⟨508091, by rfl⟩ : syracuseStep 2709821 = 1016183) (by norm_num)
theorem B2709845 : Blo 1805604 2709845 := bbase (se 10 (by rfl) ⟨3969, by rfl⟩ : syracuseStep 2709845 = 7939) (by norm_num)
theorem B2709869 : Blo 1805604 2709869 := bbase (se 3 (by rfl) ⟨508100, by rfl⟩ : syracuseStep 2709869 = 1016201) (by norm_num)
theorem B3430765 : Blo 1805604 3430765 := bbase (se 3 (by rfl) ⟨643268, by rfl⟩ : syracuseStep 3430765 = 1286537) (by norm_num)
theorem B7715189 : Blo 1805604 7715189 := bbase (se 5 (by rfl) ⟨361649, by rfl⟩ : syracuseStep 7715189 = 723299) (by norm_num)
theorem B2709893 : Blo 1805604 2709893 := bbase (se 4 (by rfl) ⟨254052, by rfl⟩ : syracuseStep 2709893 = 508105) (by norm_num)
theorem B2709917 : Blo 1805604 2709917 := bbase (se 3 (by rfl) ⟨508109, by rfl⟩ : syracuseStep 2709917 = 1016219) (by norm_num)
theorem B2709941 : Blo 1805604 2709941 := bbase (se 5 (by rfl) ⟨127028, by rfl⟩ : syracuseStep 2709941 = 254057) (by norm_num)
theorem B2709965 : Blo 1805604 2709965 := bbase (se 3 (by rfl) ⟨508118, by rfl⟩ : syracuseStep 2709965 = 1016237) (by norm_num)
theorem B2709989 : Blo 1805604 2709989 := bbase (se 4 (by rfl) ⟨254061, by rfl⟩ : syracuseStep 2709989 = 508123) (by norm_num)
theorem B2710013 : Blo 1805604 2710013 := bbase (se 3 (by rfl) ⟨508127, by rfl⟩ : syracuseStep 2710013 = 1016255) (by norm_num)
theorem B2710037 : Blo 1805604 2710037 := bbase (se 6 (by rfl) ⟨63516, by rfl⟩ : syracuseStep 2710037 = 127033) (by norm_num)
theorem B9148949 : Blo 1805604 9148949 := bbase (se 6 (by rfl) ⟨214428, by rfl⟩ : syracuseStep 9148949 = 428857) (by norm_num)
theorem B2710061 : Blo 1805604 2710061 := bbase (se 3 (by rfl) ⟨508136, by rfl⟩ : syracuseStep 2710061 = 1016273) (by norm_num)
theorem B2710085 : Blo 1805604 2710085 := bbase (se 4 (by rfl) ⟨254070, by rfl⟩ : syracuseStep 2710085 = 508141) (by norm_num)
theorem B2710109 : Blo 1805604 2710109 := bbase (se 3 (by rfl) ⟨508145, by rfl⟩ : syracuseStep 2710109 = 1016291) (by norm_num)
theorem B3856997 : Blo 1805604 3856997 := bbase (se 4 (by rfl) ⟨361593, by rfl⟩ : syracuseStep 3856997 = 723187) (by norm_num)
theorem B2710133 : Blo 1805604 2710133 := bbase (se 5 (by rfl) ⟨127037, by rfl⟩ : syracuseStep 2710133 = 254075) (by norm_num)
theorem B2710157 : Blo 1805604 2710157 := bbase (se 3 (by rfl) ⟨508154, by rfl⟩ : syracuseStep 2710157 = 1016309) (by norm_num)
theorem B3431069 : Blo 1805604 3431069 := bbase (se 3 (by rfl) ⟨643325, by rfl⟩ : syracuseStep 3431069 = 1286651) (by norm_num)
theorem B2710181 : Blo 1805604 2710181 := bbase (se 4 (by rfl) ⟨254079, by rfl⟩ : syracuseStep 2710181 = 508159) (by norm_num)
theorem B2710205 : Blo 1805604 2710205 := bbase (se 3 (by rfl) ⟨508163, by rfl⟩ : syracuseStep 2710205 = 1016327) (by norm_num)
theorem B2710229 : Blo 1805604 2710229 := bbase (se 7 (by rfl) ⟨31760, by rfl⟩ : syracuseStep 2710229 = 63521) (by norm_num)
theorem B2710253 : Blo 1805604 2710253 := bbase (se 3 (by rfl) ⟨508172, by rfl⟩ : syracuseStep 2710253 = 1016345) (by norm_num)
theorem B5143301 : Blo 1805604 5143301 := bbase (se 4 (by rfl) ⟨482184, by rfl⟩ : syracuseStep 5143301 = 964369) (by norm_num)
theorem B2710277 : Blo 1805604 2710277 := bbase (se 4 (by rfl) ⟨254088, by rfl⟩ : syracuseStep 2710277 = 508177) (by norm_num)
theorem B34716437 : Blo 1805604 34716437 := bbase (se 6 (by rfl) ⟨813666, by rfl⟩ : syracuseStep 34716437 = 1627333) (by norm_num)
theorem B2710301 : Blo 1805604 2710301 := bbase (se 3 (by rfl) ⟨508181, by rfl⟩ : syracuseStep 2710301 = 1016363) (by norm_num)
theorem B2710325 : Blo 1805604 2710325 := bbase (se 5 (by rfl) ⟨127046, by rfl⟩ : syracuseStep 2710325 = 254093) (by norm_num)
theorem B2710349 : Blo 1805604 2710349 := bbase (se 3 (by rfl) ⟨508190, by rfl⟩ : syracuseStep 2710349 = 1016381) (by norm_num)
theorem B2710373 : Blo 1805604 2710373 := bbase (se 4 (by rfl) ⟨254097, by rfl⟩ : syracuseStep 2710373 = 508195) (by norm_num)
theorem B15432565 : Blo 1805604 15432565 := bbase (se 5 (by rfl) ⟨723401, by rfl⟩ : syracuseStep 15432565 = 1446803) (by norm_num)
theorem B2710397 : Blo 1805604 2710397 := bbase (se 3 (by rfl) ⟨508199, by rfl⟩ : syracuseStep 2710397 = 1016399) (by norm_num)
theorem B2571149 : Blo 1805604 2571149 := bbase (se 3 (by rfl) ⟨482090, by rfl⟩ : syracuseStep 2571149 = 964181) (by norm_num)
theorem B2710421 : Blo 1805604 2710421 := bbase (se 6 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 2710421 = 127051) (by norm_num)
theorem B2710445 : Blo 1805604 2710445 := bbase (se 3 (by rfl) ⟨508208, by rfl⟩ : syracuseStep 2710445 = 1016417) (by norm_num)
theorem B9141173 : Blo 1805604 9141173 := bbase (se 5 (by rfl) ⟨428492, by rfl⟩ : syracuseStep 9141173 = 856985) (by norm_num)
theorem B11574197 : Blo 1805604 11574197 := bbase (se 5 (by rfl) ⟨542540, by rfl⟩ : syracuseStep 11574197 = 1085081) (by norm_num)
theorem B2710469 : Blo 1805604 2710469 := bbase (se 4 (by rfl) ⟨254106, by rfl⟩ : syracuseStep 2710469 = 508213) (by norm_num)
theorem B2710493 : Blo 1805604 2710493 := bbase (se 3 (by rfl) ⟨508217, by rfl⟩ : syracuseStep 2710493 = 1016435) (by norm_num)
theorem B4340717 : Blo 1805604 4340717 := bbase (se 3 (by rfl) ⟨813884, by rfl⟩ : syracuseStep 4340717 = 1627769) (by norm_num)
theorem B2710517 : Blo 1805604 2710517 := bbase (se 5 (by rfl) ⟨127055, by rfl⟩ : syracuseStep 2710517 = 254111) (by norm_num)
theorem B2710541 : Blo 1805604 2710541 := bbase (se 3 (by rfl) ⟨508226, by rfl⟩ : syracuseStep 2710541 = 1016453) (by norm_num)
theorem B2710565 : Blo 1805604 2710565 := bbase (se 4 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 2710565 = 508231) (by norm_num)
theorem B5495861 : Blo 1805604 5495861 := bbase (se 5 (by rfl) ⟨257618, by rfl⟩ : syracuseStep 5495861 = 515237) (by norm_num)
theorem B2710589 : Blo 1805604 2710589 := bbase (se 3 (by rfl) ⟨508235, by rfl⟩ : syracuseStep 2710589 = 1016471) (by norm_num)
theorem B2710613 : Blo 1805604 2710613 := bbase (se 8 (by rfl) ⟨15882, by rfl⟩ : syracuseStep 2710613 = 31765) (by norm_num)
theorem B2710637 : Blo 1805604 2710637 := bbase (se 3 (by rfl) ⟨508244, by rfl⟩ : syracuseStep 2710637 = 1016489) (by norm_num)
theorem B2710661 : Blo 1805604 2710661 := bbase (se 4 (by rfl) ⟨254124, by rfl⟩ : syracuseStep 2710661 = 508249) (by norm_num)
theorem B2710685 : Blo 1805604 2710685 := bbase (se 3 (by rfl) ⟨508253, by rfl⟩ : syracuseStep 2710685 = 1016507) (by norm_num)
theorem B5143733 : Blo 1805604 5143733 := bbase (se 5 (by rfl) ⟨241112, by rfl⟩ : syracuseStep 5143733 = 482225) (by norm_num)
theorem B2710709 : Blo 1805604 2710709 := bbase (se 5 (by rfl) ⟨127064, by rfl⟩ : syracuseStep 2710709 = 254129) (by norm_num)
theorem B2710733 : Blo 1805604 2710733 := bbase (se 3 (by rfl) ⟨508262, by rfl⟩ : syracuseStep 2710733 = 1016525) (by norm_num)
theorem B3661021 : Blo 1805604 3661021 := bbase (se 3 (by rfl) ⟨686441, by rfl⟩ : syracuseStep 3661021 = 1372883) (by norm_num)
theorem B2170085 : Blo 1805604 2170085 := bbase (se 4 (by rfl) ⟨203445, by rfl⟩ : syracuseStep 2170085 = 406891) (by norm_num)
theorem B4119781 : Blo 1805604 4119781 := bbase (se 4 (by rfl) ⟨386229, by rfl⟩ : syracuseStep 4119781 = 772459) (by norm_num)
theorem B2710757 : Blo 1805604 2710757 := bbase (se 4 (by rfl) ⟨254133, by rfl⟩ : syracuseStep 2710757 = 508267) (by norm_num)
theorem B2170109 : Blo 1805604 2170109 := bbase (se 3 (by rfl) ⟨406895, by rfl⟩ : syracuseStep 2170109 = 813791) (by norm_num)
theorem B2710781 : Blo 1805604 2710781 := bbase (se 3 (by rfl) ⟨508271, by rfl⟩ : syracuseStep 2710781 = 1016543) (by norm_num)
theorem B6855941 : Blo 1805604 6855941 := bbase (se 4 (by rfl) ⟨642744, by rfl⟩ : syracuseStep 6855941 = 1285489) (by norm_num)
theorem B2710805 : Blo 1805604 2710805 := bbase (se 6 (by rfl) ⟨63534, by rfl⟩ : syracuseStep 2710805 = 127069) (by norm_num)
theorem B2710829 : Blo 1805604 2710829 := bbase (se 3 (by rfl) ⟨508280, by rfl⟩ : syracuseStep 2710829 = 1016561) (by norm_num)
theorem B7929157 : Blo 1805604 7929157 := bbase (se 4 (by rfl) ⟨743358, by rfl⟩ : syracuseStep 7929157 = 1486717) (by norm_num)
theorem B2710853 : Blo 1805604 2710853 := bbase (se 4 (by rfl) ⟨254142, by rfl⟩ : syracuseStep 2710853 = 508285) (by norm_num)
theorem B4570445 : Blo 1805604 4570445 := bbase (se 3 (by rfl) ⟨856958, by rfl⟩ : syracuseStep 4570445 = 1713917) (by norm_num)
theorem B7716181 : Blo 1805604 7716181 := bbase (se 11 (by rfl) ⟨5651, by rfl⟩ : syracuseStep 7716181 = 11303) (by norm_num)
theorem B2710877 : Blo 1805604 2710877 := bbase (se 3 (by rfl) ⟨508289, by rfl⟩ : syracuseStep 2710877 = 1016579) (by norm_num)
theorem B2710901 : Blo 1805604 2710901 := bbase (se 5 (by rfl) ⟨127073, by rfl⟩ : syracuseStep 2710901 = 254147) (by norm_num)
theorem B2710925 : Blo 1805604 2710925 := bbase (se 3 (by rfl) ⟨508298, by rfl⟩ : syracuseStep 2710925 = 1016597) (by norm_num)
theorem B2710949 : Blo 1805604 2710949 := bbase (se 4 (by rfl) ⟨254151, by rfl⟩ : syracuseStep 2710949 = 508303) (by norm_num)
theorem B13016501 : Blo 1805604 13016501 := bbase (se 5 (by rfl) ⟨610148, by rfl⟩ : syracuseStep 13016501 = 1220297) (by norm_num)
theorem B4062653 : Blo 1805604 4062653 := bbase (se 3 (by rfl) ⟨761747, by rfl⟩ : syracuseStep 4062653 = 1523495) (by norm_num)
theorem B2710973 : Blo 1805604 2710973 := bbase (se 3 (by rfl) ⟨508307, by rfl⟩ : syracuseStep 2710973 = 1016615) (by norm_num)
theorem B6094277 : Blo 1805604 6094277 := bbase (se 4 (by rfl) ⟨571338, by rfl⟩ : syracuseStep 6094277 = 1142677) (by norm_num)
theorem B3857861 : Blo 1805604 3857861 := bbase (se 4 (by rfl) ⟨361674, by rfl⟩ : syracuseStep 3857861 = 723349) (by norm_num)
theorem B65158613 : Blo 1805604 65158613 := bbase (se 7 (by rfl) ⟨763577, by rfl⟩ : syracuseStep 65158613 = 1527155) (by norm_num)
theorem B2710997 : Blo 1805604 2710997 := bbase (se 7 (by rfl) ⟨31769, by rfl⟩ : syracuseStep 2710997 = 63539) (by norm_num)
theorem B2711021 : Blo 1805604 2711021 := bbase (se 3 (by rfl) ⟨508316, by rfl⟩ : syracuseStep 2711021 = 1016633) (by norm_num)
theorem B4062725 : Blo 1805604 4062725 := bbase (se 4 (by rfl) ⟨380880, by rfl⟩ : syracuseStep 4062725 = 761761) (by norm_num)
theorem B2711045 : Blo 1805604 2711045 := bbase (se 4 (by rfl) ⟨254160, by rfl⟩ : syracuseStep 2711045 = 508321) (by norm_num)
theorem B2711069 : Blo 1805604 2711069 := bbase (se 3 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 2711069 = 1016651) (by norm_num)
theorem B2170417 : Blo 1805604 2170417 := bbase (se 2 (by rfl) ⟨813906, by rfl⟩ : syracuseStep 2170417 = 1627813) (by norm_num)
theorem B2711093 : Blo 1805604 2711093 := bbase (se 5 (by rfl) ⟨127082, by rfl⟩ : syracuseStep 2711093 = 254165) (by norm_num)
theorem B5496373 : Blo 1805604 5496373 := bbase (se 5 (by rfl) ⟨257642, by rfl⟩ : syracuseStep 5496373 = 515285) (by norm_num)
theorem B4062797 : Blo 1805604 4062797 := bbase (se 3 (by rfl) ⟨761774, by rfl⟩ : syracuseStep 4062797 = 1523549) (by norm_num)
theorem B2711117 : Blo 1805604 2711117 := bbase (se 3 (by rfl) ⟨508334, by rfl⟩ : syracuseStep 2711117 = 1016669) (by norm_num)
theorem B3046997 : Blo 1805604 3046997 := bbase (se 8 (by rfl) ⟨17853, by rfl⟩ : syracuseStep 3046997 = 35707) (by norm_num)
theorem B3858005 : Blo 1805604 3858005 := bbase (se 8 (by rfl) ⟨22605, by rfl⟩ : syracuseStep 3858005 = 45211) (by norm_num)
theorem B8683109 : Blo 1805604 8683109 := bbase (se 4 (by rfl) ⟨814041, by rfl⟩ : syracuseStep 8683109 = 1628083) (by norm_num)
theorem B2711141 : Blo 1805604 2711141 := bbase (se 4 (by rfl) ⟨254169, by rfl⟩ : syracuseStep 2711141 = 508339) (by norm_num)
theorem B2711165 : Blo 1805604 2711165 := bbase (se 3 (by rfl) ⟨508343, by rfl⟩ : syracuseStep 2711165 = 1016687) (by norm_num)
theorem B4062869 : Blo 1805604 4062869 := bbase (se 6 (by rfl) ⟨95223, by rfl⟩ : syracuseStep 4062869 = 190447) (by norm_num)
theorem B13721237 : Blo 1805604 13721237 := bbase (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) (by norm_num)
theorem B2711189 : Blo 1805604 2711189 := bbase (se 6 (by rfl) ⟨63543, by rfl⟩ : syracuseStep 2711189 = 127087) (by norm_num)
theorem B4570789 : Blo 1805604 4570789 := bbase (se 4 (by rfl) ⟨428511, by rfl⟩ : syracuseStep 4570789 = 857023) (by norm_num)
theorem B2711213 : Blo 1805604 2711213 := bbase (se 3 (by rfl) ⟨508352, by rfl⟩ : syracuseStep 2711213 = 1016705) (by norm_num)
theorem B2711237 : Blo 1805604 2711237 := bbase (se 4 (by rfl) ⟨254178, by rfl⟩ : syracuseStep 2711237 = 508357) (by norm_num)
theorem B2031313 : Blo 1805604 2031313 := bbase (se 2 (by rfl) ⟨761742, by rfl⟩ : syracuseStep 2031313 = 1523485) (by norm_num)
theorem B3047125 : Blo 1805604 3047125 := bbase (se 7 (by rfl) ⟨35708, by rfl⟩ : syracuseStep 3047125 = 71417) (by norm_num)
theorem B2285273 : Blo 1805604 2285273 := bbase (se 2 (by rfl) ⟨856977, by rfl⟩ : syracuseStep 2285273 = 1713955) (by norm_num)
theorem B4062941 : Blo 1805604 4062941 := bbase (se 3 (by rfl) ⟨761801, by rfl⟩ : syracuseStep 4062941 = 1523603) (by norm_num)
theorem B2170589 : Blo 1805604 2170589 := bbase (se 3 (by rfl) ⟨406985, by rfl⟩ : syracuseStep 2170589 = 813971) (by norm_num)
theorem B2711261 : Blo 1805604 2711261 := bbase (se 3 (by rfl) ⟨508361, by rfl⟩ : syracuseStep 2711261 = 1016723) (by norm_num)
theorem B2031349 : Blo 1805604 2031349 := bbase (se 5 (by rfl) ⟨95219, by rfl⟩ : syracuseStep 2031349 = 190439) (by norm_num)
theorem B2711285 : Blo 1805604 2711285 := bbase (se 5 (by rfl) ⟨127091, by rfl⟩ : syracuseStep 2711285 = 254183) (by norm_num)
theorem B2711309 : Blo 1805604 2711309 := bbase (se 3 (by rfl) ⟨508370, by rfl⟩ : syracuseStep 2711309 = 1016741) (by norm_num)
theorem B2285329 : Blo 1805604 2285329 := bbase (se 2 (by rfl) ⟨856998, by rfl⟩ : syracuseStep 2285329 = 1713997) (by norm_num)
theorem B4570901 : Blo 1805604 4570901 := bbase (se 6 (by rfl) ⟨107130, by rfl⟩ : syracuseStep 4570901 = 214261) (by norm_num)
theorem B2031385 : Blo 1805604 2031385 := bbase (se 2 (by rfl) ⟨761769, by rfl⟩ : syracuseStep 2031385 = 1523539) (by norm_num)
theorem B4063013 : Blo 1805604 4063013 := bbase (se 4 (by rfl) ⟨380907, by rfl⟩ : syracuseStep 4063013 = 761815) (by norm_num)
theorem B9150245 : Blo 1805604 9150245 := bbase (se 4 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 9150245 = 1715671) (by norm_num)
theorem B2711333 : Blo 1805604 2711333 := bbase (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) (by norm_num)
theorem B3047213 : Blo 1805604 3047213 := bbase (se 3 (by rfl) ⟨571352, by rfl⟩ : syracuseStep 3047213 = 1142705) (by norm_num)
theorem B2031421 : Blo 1805604 2031421 := bbase (se 3 (by rfl) ⟨380891, by rfl⟩ : syracuseStep 2031421 = 761783) (by norm_num)
theorem B2711357 : Blo 1805604 2711357 := bbase (se 3 (by rfl) ⟨508379, by rfl⟩ : syracuseStep 2711357 = 1016759) (by norm_num)
theorem B2170705 : Blo 1805604 2170705 := bbase (se 2 (by rfl) ⟨814014, by rfl⟩ : syracuseStep 2170705 = 1628029) (by norm_num)
theorem B2711381 : Blo 1805604 2711381 := bbase (se 9 (by rfl) ⟨7943, by rfl⟩ : syracuseStep 2711381 = 15887) (by norm_num)
theorem B2031457 : Blo 1805604 2031457 := bbase (se 2 (by rfl) ⟨761796, by rfl⟩ : syracuseStep 2031457 = 1523593) (by norm_num)
theorem B4063085 : Blo 1805604 4063085 := bbase (se 3 (by rfl) ⟨761828, by rfl⟩ : syracuseStep 4063085 = 1523657) (by norm_num)
theorem B2711405 : Blo 1805604 2711405 := bbase (se 3 (by rfl) ⟨508388, by rfl⟩ : syracuseStep 2711405 = 1016777) (by norm_num)
theorem B2285425 : Blo 1805604 2285425 := bbase (se 2 (by rfl) ⟨857034, by rfl⟩ : syracuseStep 2285425 = 1714069) (by norm_num)
theorem B6094709 : Blo 1805604 6094709 := bbase (se 5 (by rfl) ⟨285689, by rfl⟩ : syracuseStep 6094709 = 571379) (by norm_num)
theorem B16490357 : Blo 1805604 16490357 := bbase (se 5 (by rfl) ⟨772985, by rfl⟩ : syracuseStep 16490357 = 1545971) (by norm_num)
theorem B2031493 : Blo 1805604 2031493 := bbase (se 4 (by rfl) ⟨190452, by rfl⟩ : syracuseStep 2031493 = 380905) (by norm_num)
theorem B2932613 : Blo 1805604 2932613 := bbase (se 4 (by rfl) ⟨274932, by rfl⟩ : syracuseStep 2932613 = 549865) (by norm_num)
theorem B5144485 : Blo 1805604 5144485 := bbase (se 4 (by rfl) ⟨482295, by rfl⟩ : syracuseStep 5144485 = 964591) (by norm_num)
theorem B2031529 : Blo 1805604 2031529 := bbase (se 2 (by rfl) ⟨761823, by rfl⟩ : syracuseStep 2031529 = 1523647) (by norm_num)
theorem B3047341 : Blo 1805604 3047341 := bbase (se 3 (by rfl) ⟨571376, by rfl⟩ : syracuseStep 3047341 = 1142753) (by norm_num)
theorem B2170801 : Blo 1805604 2170801 := bbase (se 2 (by rfl) ⟨814050, by rfl⟩ : syracuseStep 2170801 = 1628101) (by norm_num)
theorem B4063157 : Blo 1805604 4063157 := bbase (se 5 (by rfl) ⟨190460, by rfl⟩ : syracuseStep 4063157 = 380921) (by norm_num)
theorem B2031565 : Blo 1805604 2031565 := bbase (se 3 (by rfl) ⟨380918, by rfl⟩ : syracuseStep 2031565 = 761837) (by norm_num)
theorem B4571093 : Blo 1805604 4571093 := bbase (se 7 (by rfl) ⟨53567, by rfl⟩ : syracuseStep 4571093 = 107135) (by norm_num)
theorem B2031601 : Blo 1805604 2031601 := bbase (se 2 (by rfl) ⟨761850, by rfl⟩ : syracuseStep 2031601 = 1523701) (by norm_num)
theorem B2031619 : Blo 1805604 2031619 := bstep (se 1 (by rfl) ⟨1523714, by rfl⟩ : syracuseStep 2031619 = 3047429) B3047429
theorem B2285587 : Blo 1805604 2285587 := bstep (se 1 (by rfl) ⟨1714190, by rfl⟩ : syracuseStep 2285587 = 3428381) B3428381
theorem B9142307 : Blo 1805604 9142307 := bstep (se 1 (by rfl) ⟨6856730, by rfl⟩ : syracuseStep 9142307 = 13713461) B13713461
theorem B3301411 : Blo 1805604 3301411 := bstep (se 1 (by rfl) ⟨2476058, by rfl⟩ : syracuseStep 3301411 = 4952117) B4952117
theorem B6094925 : Blo 1805604 6094925 := bstep (se 3 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 6094925 = 2285597) B2285597
theorem B3047537 : Blo 1805604 3047537 := bstep (se 2 (by rfl) ⟨1142826, by rfl⟩ : syracuseStep 3047537 = 2285653) B2285653
theorem B6094979 : Blo 1805604 6094979 := bstep (se 1 (by rfl) ⟨4571234, by rfl⟩ : syracuseStep 6094979 = 9142469) B9142469
theorem B14655629 : Blo 1805604 14655629 := bstep (se 3 (by rfl) ⟨2747930, by rfl⟩ : syracuseStep 14655629 = 5495861) B5495861
theorem B2031763 : Blo 1805604 2031763 := bstep (se 1 (by rfl) ⟨1523822, by rfl⟩ : syracuseStep 2031763 = 3047645) B3047645
theorem B4063409 : Blo 1805604 4063409 := bstep (se 2 (by rfl) ⟨1523778, by rfl⟩ : syracuseStep 4063409 = 3047557) B3047557
theorem B4063427 : Blo 1805604 4063427 := bstep (se 1 (by rfl) ⟨3047570, by rfl⟩ : syracuseStep 4063427 = 6095141) B6095141
theorem B6348995 : Blo 1805604 6348995 := bstep (se 1 (by rfl) ⟨4761746, by rfl⟩ : syracuseStep 6348995 = 9523493) B9523493
theorem B2572499 : Blo 1805604 2572499 := bstep (se 1 (by rfl) ⟨1929374, by rfl⟩ : syracuseStep 2572499 = 3858749) B3858749
theorem B3047665 : Blo 1805604 3047665 := bstep (se 2 (by rfl) ⟨1142874, by rfl⟩ : syracuseStep 3047665 = 2285749) B2285749
theorem B2441459 : Blo 1805604 2441459 := bstep (se 1 (by rfl) ⟨1831094, by rfl⟩ : syracuseStep 2441459 = 3662189) B3662189
theorem B3047699 : Blo 1805604 3047699 := bstep (se 1 (by rfl) ⟨2285774, by rfl⟩ : syracuseStep 3047699 = 4571549) B4571549
theorem B2031907 : Blo 1805604 2031907 := bstep (se 1 (by rfl) ⟨1523930, by rfl⟩ : syracuseStep 2031907 = 3047861) B3047861
theorem B6095249 : Blo 1805604 6095249 := bstep (se 2 (by rfl) ⟨2285718, by rfl⟩ : syracuseStep 6095249 = 4571437) B4571437
theorem B3047827 : Blo 1805604 3047827 := bstep (se 1 (by rfl) ⟨2285870, by rfl⟩ : syracuseStep 3047827 = 4571741) B4571741
theorem B2032051 : Blo 1805604 2032051 := bstep (se 1 (by rfl) ⟨1524038, by rfl⟩ : syracuseStep 2032051 = 3048077) B3048077
theorem B9904589 : Blo 1805604 9904589 := bstep (se 3 (by rfl) ⟨1857110, by rfl⟩ : syracuseStep 9904589 = 3714221) B3714221
theorem B4063697 : Blo 1805604 4063697 := bstep (se 2 (by rfl) ⟨1523886, by rfl⟩ : syracuseStep 4063697 = 3047773) B3047773
theorem B4063715 : Blo 1805604 4063715 := bstep (se 1 (by rfl) ⟨3047786, by rfl⟩ : syracuseStep 4063715 = 6095573) B6095573
theorem B2286083 : Blo 1805604 2286083 := bstep (se 1 (by rfl) ⟨1714562, by rfl⟩ : syracuseStep 2286083 = 3429125) B3429125
theorem B3047969 : Blo 1805604 3047969 := bstep (se 2 (by rfl) ⟨1142988, by rfl⟩ : syracuseStep 3047969 = 2285977) B2285977
theorem B10289699 : Blo 1805604 10289699 := bstep (se 1 (by rfl) ⟨7717274, by rfl⟩ : syracuseStep 10289699 = 15434549) B15434549
theorem B2032195 : Blo 1805604 2032195 := bstep (se 1 (by rfl) ⟨1524146, by rfl⟩ : syracuseStep 2032195 = 3048293) B3048293
theorem B3662417 : Blo 1805604 3662417 := bstep (se 2 (by rfl) ⟨1373406, by rfl⟩ : syracuseStep 3662417 = 2746813) B2746813
theorem B4571761 : Blo 1805604 4571761 := bstep (se 2 (by rfl) ⟨1714410, by rfl⟩ : syracuseStep 4571761 = 3428821) B3428821
theorem B4637297 : Blo 1805604 4637297 := bstep (se 2 (by rfl) ⟨1738986, by rfl⟩ : syracuseStep 4637297 = 3477973) B3477973
theorem B3048097 : Blo 1805604 3048097 := bstep (se 2 (by rfl) ⟨1143036, by rfl⟩ : syracuseStep 3048097 = 2286073) B2286073
theorem B3048131 : Blo 1805604 3048131 := bstep (se 1 (by rfl) ⟨2286098, by rfl⟩ : syracuseStep 3048131 = 4572197) B4572197
theorem B2032339 : Blo 1805604 2032339 := bstep (se 1 (by rfl) ⟨1524254, by rfl⟩ : syracuseStep 2032339 = 3048509) B3048509
theorem B4063985 : Blo 1805604 4063985 := bstep (se 2 (by rfl) ⟨1523994, by rfl⟩ : syracuseStep 4063985 = 3047989) B3047989
theorem B4064003 : Blo 1805604 4064003 := bstep (se 1 (by rfl) ⟨3048002, by rfl⟩ : syracuseStep 4064003 = 6096005) B6096005
theorem B8798989 : Blo 1805604 8798989 := bstep (se 3 (by rfl) ⟨1649810, by rfl⟩ : syracuseStep 8798989 = 3299621) B3299621
theorem B3048259 : Blo 1805604 3048259 := bstep (se 1 (by rfl) ⟨2286194, by rfl⟩ : syracuseStep 3048259 = 4572389) B4572389
theorem B9143117 : Blo 1805604 9143117 := bstep (se 3 (by rfl) ⟨1714334, by rfl⟩ : syracuseStep 9143117 = 3428669) B3428669
theorem B2573137 : Blo 1805604 2573137 := bstep (se 2 (by rfl) ⟨964926, by rfl⟩ : syracuseStep 2573137 = 1929853) B1929853
theorem B2032483 : Blo 1805604 2032483 := bstep (se 1 (by rfl) ⟨1524362, by rfl⟩ : syracuseStep 2032483 = 3048725) B3048725
theorem B4572035 : Blo 1805604 4572035 := bstep (se 1 (by rfl) ⟨3429026, by rfl⟩ : syracuseStep 4572035 = 6858053) B6858053
theorem B6095789 : Blo 1805604 6095789 := bstep (se 3 (by rfl) ⟨1142960, by rfl⟩ : syracuseStep 6095789 = 2285921) B2285921
theorem B5784497 : Blo 1805604 5784497 := bstep (se 2 (by rfl) ⟨2169186, by rfl⟩ : syracuseStep 5784497 = 4338373) B4338373
theorem B3048401 : Blo 1805604 3048401 := bstep (se 2 (by rfl) ⟨1143150, by rfl⟩ : syracuseStep 3048401 = 2286301) B2286301
theorem B5784547 : Blo 1805604 5784547 := bstep (se 1 (by rfl) ⟨4338410, by rfl⟩ : syracuseStep 5784547 = 8676821) B8676821
theorem B6095843 : Blo 1805604 6095843 := bstep (se 1 (by rfl) ⟨4571882, by rfl⟩ : syracuseStep 6095843 = 9143765) B9143765
theorem B2032627 : Blo 1805604 2032627 := bstep (se 1 (by rfl) ⟨1524470, by rfl⟩ : syracuseStep 2032627 = 3048941) B3048941
theorem B6177809 : Blo 1805604 6177809 := bstep (se 2 (by rfl) ⟨2316678, by rfl⟩ : syracuseStep 6177809 = 4633357) B4633357
theorem B4064273 : Blo 1805604 4064273 := bstep (se 2 (by rfl) ⟨1524102, by rfl⟩ : syracuseStep 4064273 = 3048205) B3048205
theorem B2442259 : Blo 1805604 2442259 := bstep (se 1 (by rfl) ⟨1831694, by rfl⟩ : syracuseStep 2442259 = 3663389) B3663389
theorem B4064291 : Blo 1805604 4064291 := bstep (se 1 (by rfl) ⟨3048218, by rfl⟩ : syracuseStep 4064291 = 6096437) B6096437
theorem B4637731 : Blo 1805604 4637731 := bstep (se 1 (by rfl) ⟨3478298, by rfl⟩ : syracuseStep 4637731 = 6956597) B6956597
theorem B2892851 : Blo 1805604 2892851 := bstep (se 1 (by rfl) ⟨2169638, by rfl⟩ : syracuseStep 2892851 = 4339277) B4339277
theorem B4572227 : Blo 1805604 4572227 := bstep (se 1 (by rfl) ⟨3429170, by rfl⟩ : syracuseStep 4572227 = 6858341) B6858341
theorem B3048529 : Blo 1805604 3048529 := bstep (se 2 (by rfl) ⟨1143198, by rfl⟩ : syracuseStep 3048529 = 2286397) B2286397
theorem B5866577 : Blo 1805604 5866577 := bstep (se 2 (by rfl) ⟨2199966, by rfl⟩ : syracuseStep 5866577 = 4399933) B4399933
theorem B9897059 : Blo 1805604 9897059 := bstep (se 1 (by rfl) ⟨7422794, by rfl⟩ : syracuseStep 9897059 = 14845589) B14845589
theorem B3048563 : Blo 1805604 3048563 := bstep (se 1 (by rfl) ⟨2286422, by rfl⟩ : syracuseStep 3048563 = 4572845) B4572845
theorem B2032771 : Blo 1805604 2032771 := bstep (se 1 (by rfl) ⟨1524578, by rfl⟩ : syracuseStep 2032771 = 3049157) B3049157
theorem B2573473 : Blo 1805604 2573473 := bstep (se 2 (by rfl) ⟨965052, by rfl⟩ : syracuseStep 2573473 = 1930105) B1930105
theorem B2286787 : Blo 1805604 2286787 := bstep (se 1 (by rfl) ⟨1715090, by rfl⟩ : syracuseStep 2286787 = 3430181) B3430181
theorem B6096113 : Blo 1805604 6096113 := bstep (se 2 (by rfl) ⟨2286042, by rfl⟩ : syracuseStep 6096113 = 4572085) B4572085
theorem B7718129 : Blo 1805604 7718129 := bstep (se 2 (by rfl) ⟨2894298, by rfl⟩ : syracuseStep 7718129 = 5788597) B5788597
theorem B2893043 : Blo 1805604 2893043 := bstep (se 1 (by rfl) ⟨2169782, by rfl⟩ : syracuseStep 2893043 = 4339565) B4339565
theorem B3048691 : Blo 1805604 3048691 := bstep (se 1 (by rfl) ⟨2286518, by rfl⟩ : syracuseStep 3048691 = 4573037) B4573037
theorem B2032915 : Blo 1805604 2032915 := bstep (se 1 (by rfl) ⟨1524686, by rfl⟩ : syracuseStep 2032915 = 3049373) B3049373
theorem B2934049 : Blo 1805604 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B2286883 : Blo 1805604 2286883 := bstep (se 1 (by rfl) ⟨1715162, by rfl⟩ : syracuseStep 2286883 = 3430325) B3430325
theorem B4064561 : Blo 1805604 4064561 := bstep (se 2 (by rfl) ⟨1524210, by rfl⟩ : syracuseStep 4064561 = 3048421) B3048421
theorem B4064579 : Blo 1805604 4064579 := bstep (se 1 (by rfl) ⟨3048434, by rfl⟩ : syracuseStep 4064579 = 6096869) B6096869
theorem B6514019 : Blo 1805604 6514019 := bstep (se 1 (by rfl) ⟨4885514, by rfl⟩ : syracuseStep 6514019 = 9771029) B9771029
theorem B2893171 : Blo 1805604 2893171 := bstep (se 1 (by rfl) ⟨2169878, by rfl⟩ : syracuseStep 2893171 = 4339757) B4339757
theorem B3048833 : Blo 1805604 3048833 := bstep (se 2 (by rfl) ⟨1143312, by rfl⟩ : syracuseStep 3048833 = 2286625) B2286625
theorem B5146001 : Blo 1805604 5146001 := bstep (se 2 (by rfl) ⟨1929750, by rfl⟩ : syracuseStep 5146001 = 3859501) B3859501
theorem B2033059 : Blo 1805604 2033059 := bstep (se 1 (by rfl) ⟨1524794, by rfl⟩ : syracuseStep 2033059 = 3049589) B3049589
theorem B8349169 : Blo 1805604 8349169 := bstep (se 2 (by rfl) ⟨3130938, by rfl⟩ : syracuseStep 8349169 = 6261877) B6261877
theorem B3048961 : Blo 1805604 3048961 := bstep (se 2 (by rfl) ⟨1143360, by rfl⟩ : syracuseStep 3048961 = 2286721) B2286721
theorem B3048995 : Blo 1805604 3048995 := bstep (se 1 (by rfl) ⟨2286746, by rfl⟩ : syracuseStep 3048995 = 4573493) B4573493
theorem B2033203 : Blo 1805604 2033203 := bstep (se 1 (by rfl) ⟨1524902, by rfl⟩ : syracuseStep 2033203 = 3049805) B3049805
theorem B4064849 : Blo 1805604 4064849 := bstep (se 2 (by rfl) ⟨1524318, by rfl⟩ : syracuseStep 4064849 = 3048637) B3048637
theorem B5146193 : Blo 1805604 5146193 := bstep (se 2 (by rfl) ⟨1929822, by rfl⟩ : syracuseStep 5146193 = 3859645) B3859645
theorem B4064867 : Blo 1805604 4064867 := bstep (se 1 (by rfl) ⟨3048650, by rfl⟩ : syracuseStep 4064867 = 6097301) B6097301
theorem B4884077 : Blo 1805604 4884077 := bstep (se 3 (by rfl) ⟨915764, by rfl⟩ : syracuseStep 4884077 = 1831529) B1831529
theorem B3049123 : Blo 1805604 3049123 := bstep (se 1 (by rfl) ⟨2286842, by rfl⟩ : syracuseStep 3049123 = 4573685) B4573685
theorem B5785265 : Blo 1805604 5785265 := bstep (se 2 (by rfl) ⟨2169474, by rfl⟩ : syracuseStep 5785265 = 4338949) B4338949
theorem B2033347 : Blo 1805604 2033347 := bstep (se 1 (by rfl) ⟨1525010, by rfl⟩ : syracuseStep 2033347 = 3050021) B3050021
theorem B6096653 : Blo 1805604 6096653 := bstep (se 3 (by rfl) ⟨1143122, by rfl⟩ : syracuseStep 6096653 = 2286245) B2286245
theorem B6956813 : Blo 1805604 6956813 := bstep (se 3 (by rfl) ⟨1304402, by rfl⟩ : syracuseStep 6956813 = 2608805) B2608805
theorem B2287379 : Blo 1805604 2287379 := bstep (se 1 (by rfl) ⟨1715534, by rfl⟩ : syracuseStep 2287379 = 3431069) B3431069
theorem B3049265 : Blo 1805604 3049265 := bstep (se 2 (by rfl) ⟨1143474, by rfl⟩ : syracuseStep 3049265 = 2286949) B2286949
theorem B6096707 : Blo 1805604 6096707 := bstep (se 1 (by rfl) ⟨4572530, by rfl⟩ : syracuseStep 6096707 = 9145061) B9145061
theorem B2033491 : Blo 1805604 2033491 := bstep (se 1 (by rfl) ⟨1525118, by rfl⟩ : syracuseStep 2033491 = 3050237) B3050237
theorem B23144291 : Blo 1805604 23144291 := bstep (se 1 (by rfl) ⟨17358218, by rfl⟩ : syracuseStep 23144291 = 34716437) B34716437
theorem B4065137 : Blo 1805604 4065137 := bstep (se 2 (by rfl) ⟨1524426, by rfl⟩ : syracuseStep 4065137 = 3048853) B3048853
theorem B4065155 : Blo 1805604 4065155 := bstep (se 1 (by rfl) ⟨3048866, by rfl⟩ : syracuseStep 4065155 = 6097733) B6097733
theorem B3049393 : Blo 1805604 3049393 := bstep (se 2 (by rfl) ⟨1143522, by rfl⟩ : syracuseStep 3049393 = 2287045) B2287045
theorem B3049427 : Blo 1805604 3049427 := bstep (se 1 (by rfl) ⟨2287070, by rfl⟩ : syracuseStep 3049427 = 4574141) B4574141
theorem B4573169 : Blo 1805604 4573169 := bstep (se 2 (by rfl) ⟨1714938, by rfl⟩ : syracuseStep 4573169 = 3429877) B3429877
theorem B3860465 : Blo 1805604 3860465 := bstep (se 2 (by rfl) ⟨1447674, by rfl⟩ : syracuseStep 3860465 = 2895349) B2895349
theorem B2893811 : Blo 1805604 2893811 := bstep (se 1 (by rfl) ⟨2170358, by rfl⟩ : syracuseStep 2893811 = 4340717) B4340717
theorem B4573219 : Blo 1805604 4573219 := bstep (se 1 (by rfl) ⟨3429914, by rfl⟩ : syracuseStep 4573219 = 6859829) B6859829
theorem B2893889 : Blo 1805604 2893889 := bstep (se 2 (by rfl) ⟨1085208, by rfl⟩ : syracuseStep 2893889 = 2170417) B2170417
theorem B6096977 : Blo 1805604 6096977 := bstep (se 2 (by rfl) ⟨2286366, by rfl⟩ : syracuseStep 6096977 = 4572733) B4572733
theorem B3049555 : Blo 1805604 3049555 := bstep (se 1 (by rfl) ⟨2287166, by rfl⟩ : syracuseStep 3049555 = 4574333) B4574333
theorem B2607233 : Blo 1805604 2607233 := bstep (se 2 (by rfl) ⟨977712, by rfl⟩ : syracuseStep 2607233 = 1955425) B1955425
theorem B4065425 : Blo 1805604 4065425 := bstep (se 2 (by rfl) ⟨1524534, by rfl⟩ : syracuseStep 4065425 = 3049069) B3049069
theorem B4065443 : Blo 1805604 4065443 := bstep (se 1 (by rfl) ⟨3049082, by rfl⟩ : syracuseStep 4065443 = 6098165) B6098165
theorem B5785777 : Blo 1805604 5785777 := bstep (se 2 (by rfl) ⟨2169666, by rfl⟩ : syracuseStep 5785777 = 4339333) B4339333
theorem B4573361 : Blo 1805604 4573361 := bstep (se 2 (by rfl) ⟨1715010, by rfl⟩ : syracuseStep 4573361 = 3430021) B3430021
theorem B3049697 : Blo 1805604 3049697 := bstep (se 2 (by rfl) ⟨1143636, by rfl⟩ : syracuseStep 3049697 = 2287273) B2287273
theorem B8677667 : Blo 1805604 8677667 := bstep (se 1 (by rfl) ⟨6508250, by rfl⟩ : syracuseStep 8677667 = 13016501) B13016501
theorem B23152949 : Blo 1805604 23152949 := bstep (se 5 (by rfl) ⟨1085294, by rfl⟩ : syracuseStep 23152949 = 2170589) B2170589
theorem B37087541 : Blo 1805604 37087541 := bstep (se 5 (by rfl) ⟨1738478, by rfl⟩ : syracuseStep 37087541 = 3476957) B3476957
theorem B3049825 : Blo 1805604 3049825 := bstep (se 2 (by rfl) ⟨1143684, by rfl⟩ : syracuseStep 3049825 = 2287369) B2287369
theorem B3049859 : Blo 1805604 3049859 := bstep (se 1 (by rfl) ⟨2287394, by rfl⟩ : syracuseStep 3049859 = 4574789) B4574789
theorem B9275789 : Blo 1805604 9275789 := bstep (se 3 (by rfl) ⟨1739210, by rfl⟩ : syracuseStep 9275789 = 3478421) B3478421
theorem B4065713 : Blo 1805604 4065713 := bstep (se 2 (by rfl) ⟨1524642, by rfl⟩ : syracuseStep 4065713 = 3049285) B3049285
theorem B2894273 : Blo 1805604 2894273 := bstep (se 2 (by rfl) ⟨1085352, by rfl⟩ : syracuseStep 2894273 = 2170705) B2170705
theorem B4065731 : Blo 1805604 4065731 := bstep (se 1 (by rfl) ⟨3049298, by rfl⟩ : syracuseStep 4065731 = 6098597) B6098597
theorem B3049987 : Blo 1805604 3049987 := bstep (se 1 (by rfl) ⟨2287490, by rfl⟩ : syracuseStep 3049987 = 4574981) B4574981
theorem B4885037 : Blo 1805604 4885037 := bstep (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) B1831889
theorem B6859313 : Blo 1805604 6859313 := bstep (se 2 (by rfl) ⟨2572242, by rfl⟩ : syracuseStep 6859313 = 5144485) B5144485
theorem B5147185 : Blo 1805604 5147185 := bstep (se 2 (by rfl) ⟨1930194, by rfl⟩ : syracuseStep 5147185 = 3860389) B3860389
theorem B2894401 : Blo 1805604 2894401 := bstep (se 2 (by rfl) ⟨1085400, by rfl⟩ : syracuseStep 2894401 = 2170801) B2170801
theorem B7825997 : Blo 1805604 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B6097517 : Blo 1805604 6097517 := bstep (se 3 (by rfl) ⟨1143284, by rfl⟩ : syracuseStep 6097517 = 2286569) B2286569
theorem B3050129 : Blo 1805604 3050129 := bstep (se 2 (by rfl) ⟨1143798, by rfl⟩ : syracuseStep 3050129 = 2287597) B2287597
theorem B6097571 : Blo 1805604 6097571 := bstep (se 1 (by rfl) ⟨4573178, by rfl⟩ : syracuseStep 6097571 = 9146357) B9146357
theorem B4066001 : Blo 1805604 4066001 := bstep (se 2 (by rfl) ⟨1524750, by rfl⟩ : syracuseStep 4066001 = 3049501) B3049501
theorem B7834339 : Blo 1805604 7834339 := bstep (se 1 (by rfl) ⟨5875754, by rfl⟩ : syracuseStep 7834339 = 11751509) B11751509
theorem B4066019 : Blo 1805604 4066019 := bstep (se 1 (by rfl) ⟨3049514, by rfl⟩ : syracuseStep 4066019 = 6099029) B6099029
theorem B3050257 : Blo 1805604 3050257 := bstep (se 2 (by rfl) ⟨1143846, by rfl⟩ : syracuseStep 3050257 = 2287693) B2287693
theorem B3050291 : Blo 1805604 3050291 := bstep (se 1 (by rfl) ⟨2287718, by rfl⟩ : syracuseStep 3050291 = 4575437) B4575437
theorem B2747201 : Blo 1805604 2747201 := bstep (se 2 (by rfl) ⟨1030200, by rfl⟩ : syracuseStep 2747201 = 2060401) B2060401
theorem B15428465 : Blo 1805604 15428465 := bstep (se 2 (by rfl) ⟨5785674, by rfl⟩ : syracuseStep 15428465 = 11571349) B11571349
theorem B2607985 : Blo 1805604 2607985 := bstep (se 2 (by rfl) ⟨977994, by rfl⟩ : syracuseStep 2607985 = 1955989) B1955989
theorem B6097841 : Blo 1805604 6097841 := bstep (se 2 (by rfl) ⟨2286690, by rfl⟩ : syracuseStep 6097841 = 4573381) B4573381
theorem B4066289 : Blo 1805604 4066289 := bstep (se 2 (by rfl) ⟨1524858, by rfl⟩ : syracuseStep 4066289 = 3049717) B3049717
theorem B4066307 : Blo 1805604 4066307 := bstep (se 1 (by rfl) ⟨3049730, by rfl⟩ : syracuseStep 4066307 = 6099461) B6099461
theorem B11578373 : Blo 1805604 11578373 := bstep (se 4 (by rfl) ⟨1085472, by rfl⟩ : syracuseStep 11578373 = 2170945) B2170945
theorem B158411861 : Blo 1805604 158411861 := bstep (se 8 (by rfl) ⟨928194, by rfl⟩ : syracuseStep 158411861 = 1856389) B1856389
theorem B4574353 : Blo 1805604 4574353 := bstep (se 2 (by rfl) ⟨1715382, by rfl⟩ : syracuseStep 4574353 = 3430765) B3430765
theorem B2116819 : Blo 1805604 2116819 := bstep (se 1 (by rfl) ⟨1587614, by rfl⟩ : syracuseStep 2116819 = 3175229) B3175229
theorem B5786893 : Blo 1805604 5786893 := bstep (se 3 (by rfl) ⟨1085042, by rfl⟩ : syracuseStep 5786893 = 2170085) B2170085
theorem B4066577 : Blo 1805604 4066577 := bstep (se 2 (by rfl) ⟨1524966, by rfl⟩ : syracuseStep 4066577 = 3049933) B3049933
theorem B4066595 : Blo 1805604 4066595 := bstep (se 1 (by rfl) ⟨3049946, by rfl⟩ : syracuseStep 4066595 = 6099893) B6099893
theorem B1805619 : Blo 1805604 1805619 := bstep (se 1 (by rfl) ⟨1354214, by rfl⟩ : syracuseStep 1805619 = 2708429) B2708429
theorem B1805635 : Blo 1805604 1805635 := bstep (se 1 (by rfl) ⟨1354226, by rfl⟩ : syracuseStep 1805635 = 2708453) B2708453
theorem B5786957 : Blo 1805604 5786957 := bstep (se 3 (by rfl) ⟨1085054, by rfl⟩ : syracuseStep 5786957 = 2170109) B2170109
theorem B1805651 : Blo 1805604 1805651 := bstep (se 1 (by rfl) ⟨1354238, by rfl⟩ : syracuseStep 1805651 = 2708477) B2708477
theorem B1805667 : Blo 1805604 1805667 := bstep (se 1 (by rfl) ⟨1354250, by rfl⟩ : syracuseStep 1805667 = 2708501) B2708501
theorem B1805683 : Blo 1805604 1805683 := bstep (se 1 (by rfl) ⟨1354262, by rfl⟩ : syracuseStep 1805683 = 2708525) B2708525
theorem B1805699 : Blo 1805604 1805699 := bstep (se 1 (by rfl) ⟨1354274, by rfl⟩ : syracuseStep 1805699 = 2708549) B2708549
theorem B1805715 : Blo 1805604 1805715 := bstep (se 1 (by rfl) ⟨1354286, by rfl⟩ : syracuseStep 1805715 = 2708573) B2708573
theorem B1805731 : Blo 1805604 1805731 := bstep (se 1 (by rfl) ⟨1354298, by rfl⟩ : syracuseStep 1805731 = 2708597) B2708597
theorem B4574627 : Blo 1805604 4574627 := bstep (se 1 (by rfl) ⟨3430970, by rfl⟩ : syracuseStep 4574627 = 6861941) B6861941
theorem B1805747 : Blo 1805604 1805747 := bstep (se 1 (by rfl) ⟨1354310, by rfl⟩ : syracuseStep 1805747 = 2708621) B2708621
theorem B1805763 : Blo 1805604 1805763 := bstep (se 1 (by rfl) ⟨1354322, by rfl⟩ : syracuseStep 1805763 = 2708645) B2708645
theorem B13725125 : Blo 1805604 13725125 := bstep (se 4 (by rfl) ⟨1286730, by rfl⟩ : syracuseStep 13725125 = 2573461) B2573461
theorem B6098381 : Blo 1805604 6098381 := bstep (se 3 (by rfl) ⟨1143446, by rfl⟩ : syracuseStep 6098381 = 2286893) B2286893
theorem B1805779 : Blo 1805604 1805779 := bstep (se 1 (by rfl) ⟨1354334, by rfl⟩ : syracuseStep 1805779 = 2708669) B2708669
theorem B1805795 : Blo 1805604 1805795 := bstep (se 1 (by rfl) ⟨1354346, by rfl⟩ : syracuseStep 1805795 = 2708693) B2708693
theorem B8678897 : Blo 1805604 8678897 := bstep (se 2 (by rfl) ⟨3254586, by rfl⟩ : syracuseStep 8678897 = 6509173) B6509173
theorem B1805811 : Blo 1805604 1805811 := bstep (se 1 (by rfl) ⟨1354358, by rfl⟩ : syracuseStep 1805811 = 2708717) B2708717
theorem B1805827 : Blo 1805604 1805827 := bstep (se 1 (by rfl) ⟨1354370, by rfl⟩ : syracuseStep 1805827 = 2708741) B2708741
theorem B6098435 : Blo 1805604 6098435 := bstep (se 1 (by rfl) ⟨4573826, by rfl⟩ : syracuseStep 6098435 = 9147653) B9147653
theorem B23162381 : Blo 1805604 23162381 := bstep (se 3 (by rfl) ⟨4342946, by rfl⟩ : syracuseStep 23162381 = 8685893) B8685893
theorem B1805843 : Blo 1805604 1805843 := bstep (se 1 (by rfl) ⟨1354382, by rfl⟩ : syracuseStep 1805843 = 2708765) B2708765
theorem B1805859 : Blo 1805604 1805859 := bstep (se 1 (by rfl) ⟨1354394, by rfl⟩ : syracuseStep 1805859 = 2708789) B2708789
theorem B4066865 : Blo 1805604 4066865 := bstep (se 2 (by rfl) ⟨1525074, by rfl⟩ : syracuseStep 4066865 = 3050149) B3050149
theorem B1805875 : Blo 1805604 1805875 := bstep (se 1 (by rfl) ⟨1354406, by rfl⟩ : syracuseStep 1805875 = 2708813) B2708813
theorem B1805891 : Blo 1805604 1805891 := bstep (se 1 (by rfl) ⟨1354418, by rfl⟩ : syracuseStep 1805891 = 2708837) B2708837
theorem B4066883 : Blo 1805604 4066883 := bstep (se 1 (by rfl) ⟨3050162, by rfl⟩ : syracuseStep 4066883 = 6100325) B6100325
theorem B1805907 : Blo 1805604 1805907 := bstep (se 1 (by rfl) ⟨1354430, by rfl⟩ : syracuseStep 1805907 = 2708861) B2708861
theorem B1805923 : Blo 1805604 1805923 := bstep (se 1 (by rfl) ⟨1354442, by rfl⟩ : syracuseStep 1805923 = 2708885) B2708885
theorem B8801891 : Blo 1805604 8801891 := bstep (se 1 (by rfl) ⟨6601418, by rfl⟩ : syracuseStep 8801891 = 13202837) B13202837
theorem B7327331 : Blo 1805604 7327331 := bstep (se 1 (by rfl) ⟨5495498, by rfl⟩ : syracuseStep 7327331 = 10990997) B10990997
theorem B4574819 : Blo 1805604 4574819 := bstep (se 1 (by rfl) ⟨3431114, by rfl⟩ : syracuseStep 4574819 = 6862229) B6862229
theorem B1805939 : Blo 1805604 1805939 := bstep (se 1 (by rfl) ⟨1354454, by rfl⟩ : syracuseStep 1805939 = 2708909) B2708909
theorem B1805955 : Blo 1805604 1805955 := bstep (se 1 (by rfl) ⟨1354466, by rfl⟩ : syracuseStep 1805955 = 2708933) B2708933
theorem B20573837 : Blo 1805604 20573837 := bstep (se 3 (by rfl) ⟨3857594, by rfl⟩ : syracuseStep 20573837 = 7715189) B7715189
theorem B7720589 : Blo 1805604 7720589 := bstep (se 3 (by rfl) ⟨1447610, by rfl⟩ : syracuseStep 7720589 = 2895221) B2895221
theorem B1805971 : Blo 1805604 1805971 := bstep (se 1 (by rfl) ⟨1354478, by rfl⟩ : syracuseStep 1805971 = 2708957) B2708957
theorem B1805987 : Blo 1805604 1805987 := bstep (se 1 (by rfl) ⟨1354490, by rfl⟩ : syracuseStep 1805987 = 2708981) B2708981
theorem B9146033 : Blo 1805604 9146033 := bstep (se 2 (by rfl) ⟨3429762, by rfl⟩ : syracuseStep 9146033 = 6859525) B6859525
theorem B1806003 : Blo 1805604 1806003 := bstep (se 1 (by rfl) ⟨1354502, by rfl⟩ : syracuseStep 1806003 = 2709005) B2709005
theorem B1806019 : Blo 1805604 1806019 := bstep (se 1 (by rfl) ⟨1354514, by rfl⟩ : syracuseStep 1806019 = 2709029) B2709029
theorem B10292933 : Blo 1805604 10292933 := bstep (se 4 (by rfl) ⟨964962, by rfl⟩ : syracuseStep 10292933 = 1929925) B1929925
theorem B1806035 : Blo 1805604 1806035 := bstep (se 1 (by rfl) ⟨1354526, by rfl⟩ : syracuseStep 1806035 = 2709053) B2709053
theorem B1806051 : Blo 1805604 1806051 := bstep (se 1 (by rfl) ⟨1354538, by rfl⟩ : syracuseStep 1806051 = 2709077) B2709077
theorem B9768689 : Blo 1805604 9768689 := bstep (se 2 (by rfl) ⟨3663258, by rfl⟩ : syracuseStep 9768689 = 7326517) B7326517
theorem B1806067 : Blo 1805604 1806067 := bstep (se 1 (by rfl) ⟨1354550, by rfl⟩ : syracuseStep 1806067 = 2709101) B2709101
theorem B1806083 : Blo 1805604 1806083 := bstep (se 1 (by rfl) ⟨1354562, by rfl⟩ : syracuseStep 1806083 = 2709125) B2709125
theorem B6262541 : Blo 1805604 6262541 := bstep (se 3 (by rfl) ⟨1174226, by rfl⟩ : syracuseStep 6262541 = 2348453) B2348453
theorem B6098705 : Blo 1805604 6098705 := bstep (se 2 (by rfl) ⟨2287014, by rfl⟩ : syracuseStep 6098705 = 4574029) B4574029
theorem B1806099 : Blo 1805604 1806099 := bstep (se 1 (by rfl) ⟨1354574, by rfl⟩ : syracuseStep 1806099 = 2709149) B2709149
theorem B1806115 : Blo 1805604 1806115 := bstep (se 1 (by rfl) ⟨1354586, by rfl⟩ : syracuseStep 1806115 = 2709173) B2709173
theorem B1806131 : Blo 1805604 1806131 := bstep (se 1 (by rfl) ⟨1354598, by rfl⟩ : syracuseStep 1806131 = 2709197) B2709197
theorem B1806147 : Blo 1805604 1806147 := bstep (se 1 (by rfl) ⟨1354610, by rfl⟩ : syracuseStep 1806147 = 2709221) B2709221
theorem B19525445 : Blo 1805604 19525445 := bstep (se 4 (by rfl) ⟨1830510, by rfl⟩ : syracuseStep 19525445 = 3661021) B3661021
theorem B1806163 : Blo 1805604 1806163 := bstep (se 1 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 1806163 = 2709245) B2709245
theorem B1806179 : Blo 1805604 1806179 := bstep (se 1 (by rfl) ⟨1354634, by rfl⟩ : syracuseStep 1806179 = 2709269) B2709269
theorem B10424177 : Blo 1805604 10424177 := bstep (se 2 (by rfl) ⟨3909066, by rfl⟩ : syracuseStep 10424177 = 7818133) B7818133
theorem B1806195 : Blo 1805604 1806195 := bstep (se 1 (by rfl) ⟨1354646, by rfl⟩ : syracuseStep 1806195 = 2709293) B2709293
theorem B1806211 : Blo 1805604 1806211 := bstep (se 1 (by rfl) ⟨1354658, by rfl⟩ : syracuseStep 1806211 = 2709317) B2709317
theorem B1806227 : Blo 1805604 1806227 := bstep (se 1 (by rfl) ⟨1354670, by rfl⟩ : syracuseStep 1806227 = 2709341) B2709341
theorem B1806243 : Blo 1805604 1806243 := bstep (se 1 (by rfl) ⟨1354682, by rfl⟩ : syracuseStep 1806243 = 2709365) B2709365
theorem B1806259 : Blo 1805604 1806259 := bstep (se 1 (by rfl) ⟨1354694, by rfl⟩ : syracuseStep 1806259 = 2709389) B2709389
theorem B1929139 : Blo 1805604 1929139 := bstep (se 1 (by rfl) ⟨1446854, by rfl⟩ : syracuseStep 1929139 = 2893709) B2893709
theorem B1806275 : Blo 1805604 1806275 := bstep (se 1 (by rfl) ⟨1354706, by rfl⟩ : syracuseStep 1806275 = 2709413) B2709413
theorem B1806291 : Blo 1805604 1806291 := bstep (se 1 (by rfl) ⟨1354718, by rfl⟩ : syracuseStep 1806291 = 2709437) B2709437
theorem B1806307 : Blo 1805604 1806307 := bstep (se 1 (by rfl) ⟨1354730, by rfl⟩ : syracuseStep 1806307 = 2709461) B2709461
theorem B6860771 : Blo 1805604 6860771 := bstep (se 1 (by rfl) ⟨5145578, by rfl⟩ : syracuseStep 6860771 = 10291157) B10291157
theorem B1806323 : Blo 1805604 1806323 := bstep (se 1 (by rfl) ⟨1354742, by rfl⟩ : syracuseStep 1806323 = 2709485) B2709485
theorem B1806339 : Blo 1805604 1806339 := bstep (se 1 (by rfl) ⟨1354754, by rfl⟩ : syracuseStep 1806339 = 2709509) B2709509
theorem B3764227 : Blo 1805604 3764227 := bstep (se 1 (by rfl) ⟨2823170, by rfl⟩ : syracuseStep 3764227 = 5646341) B5646341
theorem B1806355 : Blo 1805604 1806355 := bstep (se 1 (by rfl) ⟨1354766, by rfl⟩ : syracuseStep 1806355 = 2709533) B2709533
theorem B1806371 : Blo 1805604 1806371 := bstep (se 1 (by rfl) ⟨1354778, by rfl⟩ : syracuseStep 1806371 = 2709557) B2709557
theorem B1806387 : Blo 1805604 1806387 := bstep (se 1 (by rfl) ⟨1354790, by rfl⟩ : syracuseStep 1806387 = 2709581) B2709581
theorem B3428419 : Blo 1805604 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B1806403 : Blo 1805604 1806403 := bstep (se 1 (by rfl) ⟨1354802, by rfl⟩ : syracuseStep 1806403 = 2709605) B2709605
theorem B1806419 : Blo 1805604 1806419 := bstep (se 1 (by rfl) ⟨1354814, by rfl⟩ : syracuseStep 1806419 = 2709629) B2709629
theorem B1806435 : Blo 1805604 1806435 := bstep (se 1 (by rfl) ⟨1354826, by rfl⟩ : syracuseStep 1806435 = 2709653) B2709653
theorem B1806451 : Blo 1805604 1806451 := bstep (se 1 (by rfl) ⟨1354838, by rfl⟩ : syracuseStep 1806451 = 2709677) B2709677
theorem B1806467 : Blo 1805604 1806467 := bstep (se 1 (by rfl) ⟨1354850, by rfl⟩ : syracuseStep 1806467 = 2709701) B2709701
theorem B10293389 : Blo 1805604 10293389 := bstep (se 3 (by rfl) ⟨1930010, by rfl⟩ : syracuseStep 10293389 = 3860021) B3860021
theorem B1806483 : Blo 1805604 1806483 := bstep (se 1 (by rfl) ⟨1354862, by rfl⟩ : syracuseStep 1806483 = 2709725) B2709725
theorem B1806499 : Blo 1805604 1806499 := bstep (se 1 (by rfl) ⟨1354874, by rfl⟩ : syracuseStep 1806499 = 2709749) B2709749
theorem B1806515 : Blo 1805604 1806515 := bstep (se 1 (by rfl) ⟨1354886, by rfl⟩ : syracuseStep 1806515 = 2709773) B2709773
theorem B1806531 : Blo 1805604 1806531 := bstep (se 1 (by rfl) ⟨1354898, by rfl⟩ : syracuseStep 1806531 = 2709797) B2709797
theorem B5492941 : Blo 1805604 5492941 := bstep (se 3 (by rfl) ⟨1029926, by rfl⟩ : syracuseStep 5492941 = 2059853) B2059853
theorem B1806547 : Blo 1805604 1806547 := bstep (se 1 (by rfl) ⟨1354910, by rfl⟩ : syracuseStep 1806547 = 2709821) B2709821
theorem B1806563 : Blo 1805604 1806563 := bstep (se 1 (by rfl) ⟨1354922, by rfl⟩ : syracuseStep 1806563 = 2709845) B2709845
theorem B1806579 : Blo 1805604 1806579 := bstep (se 1 (by rfl) ⟨1354934, by rfl⟩ : syracuseStep 1806579 = 2709869) B2709869
theorem B1806595 : Blo 1805604 1806595 := bstep (se 1 (by rfl) ⟨1354946, by rfl⟩ : syracuseStep 1806595 = 2709893) B2709893
theorem B10285325 : Blo 1805604 10285325 := bstep (se 3 (by rfl) ⟨1928498, by rfl⟩ : syracuseStep 10285325 = 3856997) B3856997
theorem B1806611 : Blo 1805604 1806611 := bstep (se 1 (by rfl) ⟨1354958, by rfl⟩ : syracuseStep 1806611 = 2709917) B2709917
theorem B1806627 : Blo 1805604 1806627 := bstep (se 1 (by rfl) ⟨1354970, by rfl⟩ : syracuseStep 1806627 = 2709941) B2709941
theorem B6099245 : Blo 1805604 6099245 := bstep (se 3 (by rfl) ⟨1143608, by rfl⟩ : syracuseStep 6099245 = 2287217) B2287217
theorem B5493041 : Blo 1805604 5493041 := bstep (se 2 (by rfl) ⟨2059890, by rfl⟩ : syracuseStep 5493041 = 4119781) B4119781
theorem B1806643 : Blo 1805604 1806643 := bstep (se 1 (by rfl) ⟨1354982, by rfl⟩ : syracuseStep 1806643 = 2709965) B2709965
theorem B1806659 : Blo 1805604 1806659 := bstep (se 1 (by rfl) ⟨1354994, by rfl⟩ : syracuseStep 1806659 = 2709989) B2709989
theorem B1806675 : Blo 1805604 1806675 := bstep (se 1 (by rfl) ⟨1355006, by rfl⟩ : syracuseStep 1806675 = 2710013) B2710013
theorem B1806691 : Blo 1805604 1806691 := bstep (se 1 (by rfl) ⟨1355018, by rfl⟩ : syracuseStep 1806691 = 2710037) B2710037
theorem B6099299 : Blo 1805604 6099299 := bstep (se 1 (by rfl) ⟨4574474, by rfl⟩ : syracuseStep 6099299 = 9148949) B9148949
theorem B1806707 : Blo 1805604 1806707 := bstep (se 1 (by rfl) ⟨1355030, by rfl⟩ : syracuseStep 1806707 = 2710061) B2710061
theorem B1806723 : Blo 1805604 1806723 := bstep (se 1 (by rfl) ⟨1355042, by rfl⟩ : syracuseStep 1806723 = 2710085) B2710085
theorem B1806739 : Blo 1805604 1806739 := bstep (se 1 (by rfl) ⟨1355054, by rfl⟩ : syracuseStep 1806739 = 2710109) B2710109
theorem B1806755 : Blo 1805604 1806755 := bstep (se 1 (by rfl) ⟨1355066, by rfl⟩ : syracuseStep 1806755 = 2710133) B2710133
theorem B10572209 : Blo 1805604 10572209 := bstep (se 2 (by rfl) ⟨3964578, by rfl⟩ : syracuseStep 10572209 = 7929157) B7929157
theorem B1806771 : Blo 1805604 1806771 := bstep (se 1 (by rfl) ⟨1355078, by rfl⟩ : syracuseStep 1806771 = 2710157) B2710157
theorem B1806787 : Blo 1805604 1806787 := bstep (se 1 (by rfl) ⟨1355090, by rfl⟩ : syracuseStep 1806787 = 2710181) B2710181
theorem B1806803 : Blo 1805604 1806803 := bstep (se 1 (by rfl) ⟨1355102, by rfl⟩ : syracuseStep 1806803 = 2710205) B2710205
theorem B1806819 : Blo 1805604 1806819 := bstep (se 1 (by rfl) ⟨1355114, by rfl⟩ : syracuseStep 1806819 = 2710229) B2710229
theorem B1806835 : Blo 1805604 1806835 := bstep (se 1 (by rfl) ⟨1355126, by rfl⟩ : syracuseStep 1806835 = 2710253) B2710253
theorem B3428867 : Blo 1805604 3428867 := bstep (se 1 (by rfl) ⟨2571650, by rfl⟩ : syracuseStep 3428867 = 5143301) B5143301
theorem B1806851 : Blo 1805604 1806851 := bstep (se 1 (by rfl) ⟨1355138, by rfl⟩ : syracuseStep 1806851 = 2710277) B2710277
theorem B1806867 : Blo 1805604 1806867 := bstep (se 1 (by rfl) ⟨1355150, by rfl⟩ : syracuseStep 1806867 = 2710301) B2710301
theorem B1806883 : Blo 1805604 1806883 := bstep (se 1 (by rfl) ⟨1355162, by rfl⟩ : syracuseStep 1806883 = 2710325) B2710325
theorem B1806899 : Blo 1805604 1806899 := bstep (se 1 (by rfl) ⟨1355174, by rfl⟩ : syracuseStep 1806899 = 2710349) B2710349
theorem B1806915 : Blo 1805604 1806915 := bstep (se 1 (by rfl) ⟨1355186, by rfl⟩ : syracuseStep 1806915 = 2710373) B2710373
theorem B1806931 : Blo 1805604 1806931 := bstep (se 1 (by rfl) ⟨1355198, by rfl⟩ : syracuseStep 1806931 = 2710397) B2710397
theorem B1806947 : Blo 1805604 1806947 := bstep (se 1 (by rfl) ⟨1355210, by rfl⟩ : syracuseStep 1806947 = 2710421) B2710421
theorem B6099569 : Blo 1805604 6099569 := bstep (se 2 (by rfl) ⟨2287338, by rfl⟩ : syracuseStep 6099569 = 4574677) B4574677
theorem B1806963 : Blo 1805604 1806963 := bstep (se 1 (by rfl) ⟨1355222, by rfl⟩ : syracuseStep 1806963 = 2710445) B2710445
theorem B1806979 : Blo 1805604 1806979 := bstep (se 1 (by rfl) ⟨1355234, by rfl⟩ : syracuseStep 1806979 = 2710469) B2710469
theorem B1806995 : Blo 1805604 1806995 := bstep (se 1 (by rfl) ⟨1355246, by rfl⟩ : syracuseStep 1806995 = 2710493) B2710493
theorem B1807011 : Blo 1805604 1807011 := bstep (se 1 (by rfl) ⟨1355258, by rfl⟩ : syracuseStep 1807011 = 2710517) B2710517
theorem B1807027 : Blo 1805604 1807027 := bstep (se 1 (by rfl) ⟨1355270, by rfl⟩ : syracuseStep 1807027 = 2710541) B2710541
theorem B1807043 : Blo 1805604 1807043 := bstep (se 1 (by rfl) ⟨1355282, by rfl⟩ : syracuseStep 1807043 = 2710565) B2710565
theorem B1807059 : Blo 1805604 1807059 := bstep (se 1 (by rfl) ⟨1355294, by rfl⟩ : syracuseStep 1807059 = 2710589) B2710589
theorem B1807075 : Blo 1805604 1807075 := bstep (se 1 (by rfl) ⟨1355306, by rfl⟩ : syracuseStep 1807075 = 2710613) B2710613
theorem B7328497 : Blo 1805604 7328497 := bstep (se 2 (by rfl) ⟨2748186, by rfl⟩ : syracuseStep 7328497 = 5496373) B5496373
theorem B1807091 : Blo 1805604 1807091 := bstep (se 1 (by rfl) ⟨1355318, by rfl⟩ : syracuseStep 1807091 = 2710637) B2710637
theorem B1807107 : Blo 1805604 1807107 := bstep (se 1 (by rfl) ⟨1355330, by rfl⟩ : syracuseStep 1807107 = 2710661) B2710661
theorem B1807123 : Blo 1805604 1807123 := bstep (se 1 (by rfl) ⟨1355342, by rfl⟩ : syracuseStep 1807123 = 2710685) B2710685
theorem B3429155 : Blo 1805604 3429155 := bstep (se 1 (by rfl) ⟨2571866, by rfl⟩ : syracuseStep 3429155 = 5143733) B5143733
theorem B1807139 : Blo 1805604 1807139 := bstep (se 1 (by rfl) ⟨1355354, by rfl⟩ : syracuseStep 1807139 = 2710709) B2710709
theorem B1807155 : Blo 1805604 1807155 := bstep (se 1 (by rfl) ⟨1355366, by rfl⟩ : syracuseStep 1807155 = 2710733) B2710733
theorem B1807171 : Blo 1805604 1807171 := bstep (se 1 (by rfl) ⟨1355378, by rfl⟩ : syracuseStep 1807171 = 2710757) B2710757
theorem B1807187 : Blo 1805604 1807187 := bstep (se 1 (by rfl) ⟨1355390, by rfl⟩ : syracuseStep 1807187 = 2710781) B2710781
theorem B1807203 : Blo 1805604 1807203 := bstep (se 1 (by rfl) ⟨1355402, by rfl⟩ : syracuseStep 1807203 = 2710805) B2710805
theorem B1807219 : Blo 1805604 1807219 := bstep (se 1 (by rfl) ⟨1355414, by rfl⟩ : syracuseStep 1807219 = 2710829) B2710829
theorem B1807235 : Blo 1805604 1807235 := bstep (se 1 (by rfl) ⟨1355426, by rfl⟩ : syracuseStep 1807235 = 2710853) B2710853
theorem B1807251 : Blo 1805604 1807251 := bstep (se 1 (by rfl) ⟨1355438, by rfl⟩ : syracuseStep 1807251 = 2710877) B2710877
theorem B1807267 : Blo 1805604 1807267 := bstep (se 1 (by rfl) ⟨1355450, by rfl⟩ : syracuseStep 1807267 = 2710901) B2710901
theorem B1807283 : Blo 1805604 1807283 := bstep (se 1 (by rfl) ⟨1355462, by rfl⟩ : syracuseStep 1807283 = 2710925) B2710925
theorem B2708417 : Blo 1805604 2708417 := bstep (se 2 (by rfl) ⟨1015656, by rfl⟩ : syracuseStep 2708417 = 2031313) B2031313
theorem B1807299 : Blo 1805604 1807299 := bstep (se 1 (by rfl) ⟨1355474, by rfl⟩ : syracuseStep 1807299 = 2710949) B2710949
theorem B6861773 : Blo 1805604 6861773 := bstep (se 3 (by rfl) ⟨1286582, by rfl⟩ : syracuseStep 6861773 = 2573165) B2573165
theorem B4338641 : Blo 1805604 4338641 := bstep (se 2 (by rfl) ⟨1626990, by rfl⟩ : syracuseStep 4338641 = 3253981) B3253981
theorem B2708435 : Blo 1805604 2708435 := bstep (se 1 (by rfl) ⟨2031326, by rfl⟩ : syracuseStep 2708435 = 4062653) B4062653
theorem B1807315 : Blo 1805604 1807315 := bstep (se 1 (by rfl) ⟨1355486, by rfl⟩ : syracuseStep 1807315 = 2710973) B2710973
theorem B43439075 : Blo 1805604 43439075 := bstep (se 1 (by rfl) ⟨32579306, by rfl⟩ : syracuseStep 43439075 = 65158613) B65158613
theorem B1807331 : Blo 1805604 1807331 := bstep (se 1 (by rfl) ⟨1355498, by rfl⟩ : syracuseStep 1807331 = 2710997) B2710997
theorem B2708465 : Blo 1805604 2708465 := bstep (se 2 (by rfl) ⟨1015674, by rfl⟩ : syracuseStep 2708465 = 2031349) B2031349
theorem B1807347 : Blo 1805604 1807347 := bstep (se 1 (by rfl) ⟨1355510, by rfl⟩ : syracuseStep 1807347 = 2711021) B2711021
theorem B2708483 : Blo 1805604 2708483 := bstep (se 1 (by rfl) ⟨2031362, by rfl⟩ : syracuseStep 2708483 = 4062725) B4062725
theorem B1807363 : Blo 1805604 1807363 := bstep (se 1 (by rfl) ⟨1355522, by rfl⟩ : syracuseStep 1807363 = 2711045) B2711045
theorem B1807379 : Blo 1805604 1807379 := bstep (se 1 (by rfl) ⟨1355534, by rfl⟩ : syracuseStep 1807379 = 2711069) B2711069
theorem B2708513 : Blo 1805604 2708513 := bstep (se 2 (by rfl) ⟨1015692, by rfl⟩ : syracuseStep 2708513 = 2031385) B2031385
theorem B1807395 : Blo 1805604 1807395 := bstep (se 1 (by rfl) ⟨1355546, by rfl⟩ : syracuseStep 1807395 = 2711093) B2711093
theorem B2708531 : Blo 1805604 2708531 := bstep (se 1 (by rfl) ⟨2031398, by rfl⟩ : syracuseStep 2708531 = 4062797) B4062797
theorem B1831987 : Blo 1805604 1831987 := bstep (se 1 (by rfl) ⟨1373990, by rfl⟩ : syracuseStep 1831987 = 2747981) B2747981
theorem B1807411 : Blo 1805604 1807411 := bstep (se 1 (by rfl) ⟨1355558, by rfl⟩ : syracuseStep 1807411 = 2711117) B2711117
theorem B5788739 : Blo 1805604 5788739 := bstep (se 1 (by rfl) ⟨4341554, by rfl⟩ : syracuseStep 5788739 = 8683109) B8683109
theorem B1807427 : Blo 1805604 1807427 := bstep (se 1 (by rfl) ⟨1355570, by rfl⟩ : syracuseStep 1807427 = 2711141) B2711141
theorem B2708561 : Blo 1805604 2708561 := bstep (se 2 (by rfl) ⟨1015710, by rfl⟩ : syracuseStep 2708561 = 2031421) B2031421
theorem B1807443 : Blo 1805604 1807443 := bstep (se 1 (by rfl) ⟨1355582, by rfl⟩ : syracuseStep 1807443 = 2711165) B2711165
theorem B2708579 : Blo 1805604 2708579 := bstep (se 1 (by rfl) ⟨2031434, by rfl⟩ : syracuseStep 2708579 = 4062869) B4062869
theorem B4699235 : Blo 1805604 4699235 := bstep (se 1 (by rfl) ⟨3524426, by rfl⟩ : syracuseStep 4699235 = 7048853) B7048853
theorem B9147491 : Blo 1805604 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B1807459 : Blo 1805604 1807459 := bstep (se 1 (by rfl) ⟨1355594, by rfl⟩ : syracuseStep 1807459 = 2711189) B2711189
theorem B1807475 : Blo 1805604 1807475 := bstep (se 1 (by rfl) ⟨1355606, by rfl⟩ : syracuseStep 1807475 = 2711213) B2711213
theorem B2708609 : Blo 1805604 2708609 := bstep (se 2 (by rfl) ⟨1015728, by rfl⟩ : syracuseStep 2708609 = 2031457) B2031457
theorem B1807491 : Blo 1805604 1807491 := bstep (se 1 (by rfl) ⟨1355618, by rfl⟩ : syracuseStep 1807491 = 2711237) B2711237
theorem B9270413 : Blo 1805604 9270413 := bstep (se 3 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 9270413 = 3476405) B3476405
theorem B6100109 : Blo 1805604 6100109 := bstep (se 3 (by rfl) ⟨1143770, by rfl⟩ : syracuseStep 6100109 = 2287541) B2287541
theorem B2708627 : Blo 1805604 2708627 := bstep (se 1 (by rfl) ⟨2031470, by rfl⟩ : syracuseStep 2708627 = 4062941) B4062941
theorem B1807507 : Blo 1805604 1807507 := bstep (se 1 (by rfl) ⟨1355630, by rfl⟩ : syracuseStep 1807507 = 2711261) B2711261
theorem B1807523 : Blo 1805604 1807523 := bstep (se 1 (by rfl) ⟨1355642, by rfl⟩ : syracuseStep 1807523 = 2711285) B2711285
theorem B2708657 : Blo 1805604 2708657 := bstep (se 2 (by rfl) ⟨1015746, by rfl⟩ : syracuseStep 2708657 = 2031493) B2031493
theorem B1807539 : Blo 1805604 1807539 := bstep (se 1 (by rfl) ⟨1355654, by rfl⟩ : syracuseStep 1807539 = 2711309) B2711309
theorem B2708675 : Blo 1805604 2708675 := bstep (se 1 (by rfl) ⟨2031506, by rfl⟩ : syracuseStep 2708675 = 4063013) B4063013
theorem B6100163 : Blo 1805604 6100163 := bstep (se 1 (by rfl) ⟨4575122, by rfl⟩ : syracuseStep 6100163 = 9150245) B9150245
theorem B1807555 : Blo 1805604 1807555 := bstep (se 1 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 1807555 = 2711333) B2711333
theorem B1807571 : Blo 1805604 1807571 := bstep (se 1 (by rfl) ⟨1355678, by rfl⟩ : syracuseStep 1807571 = 2711357) B2711357
theorem B2708705 : Blo 1805604 2708705 := bstep (se 2 (by rfl) ⟨1015764, by rfl⟩ : syracuseStep 2708705 = 2031529) B2031529
theorem B1807587 : Blo 1805604 1807587 := bstep (se 1 (by rfl) ⟨1355690, by rfl⟩ : syracuseStep 1807587 = 2711381) B2711381
theorem B2708723 : Blo 1805604 2708723 := bstep (se 1 (by rfl) ⟨2031542, by rfl⟩ : syracuseStep 2708723 = 4063085) B4063085
theorem B1807603 : Blo 1805604 1807603 := bstep (se 1 (by rfl) ⟨1355702, by rfl⟩ : syracuseStep 1807603 = 2711405) B2711405
theorem B1955075 : Blo 1805604 1955075 := bstep (se 1 (by rfl) ⟨1466306, by rfl⟩ : syracuseStep 1955075 = 2932613) B2932613
theorem B15430925 : Blo 1805604 15430925 := bstep (se 3 (by rfl) ⟨2893298, by rfl⟩ : syracuseStep 15430925 = 5786597) B5786597
theorem B2708753 : Blo 1805604 2708753 := bstep (se 2 (by rfl) ⟨1015782, by rfl⟩ : syracuseStep 2708753 = 2031565) B2031565
theorem B2708771 : Blo 1805604 2708771 := bstep (se 1 (by rfl) ⟨2031578, by rfl⟩ : syracuseStep 2708771 = 4063157) B4063157
theorem B2708801 : Blo 1805604 2708801 := bstep (se 2 (by rfl) ⟨1015800, by rfl⟩ : syracuseStep 2708801 = 2031601) B2031601
theorem B2708819 : Blo 1805604 2708819 := bstep (se 1 (by rfl) ⟨2031614, by rfl⟩ : syracuseStep 2708819 = 4063229) B4063229
theorem B2708849 : Blo 1805604 2708849 := bstep (se 2 (by rfl) ⟨1015818, by rfl⟩ : syracuseStep 2708849 = 2031637) B2031637
theorem B2708867 : Blo 1805604 2708867 := bstep (se 1 (by rfl) ⟨2031650, by rfl⟩ : syracuseStep 2708867 = 4063301) B4063301
theorem B2708897 : Blo 1805604 2708897 := bstep (se 2 (by rfl) ⟨1015836, by rfl⟩ : syracuseStep 2708897 = 2031673) B2031673
theorem B2708915 : Blo 1805604 2708915 := bstep (se 1 (by rfl) ⟨2031686, by rfl⟩ : syracuseStep 2708915 = 4063373) B4063373
theorem B2708945 : Blo 1805604 2708945 := bstep (se 2 (by rfl) ⟨1015854, by rfl⟩ : syracuseStep 2708945 = 2031709) B2031709
theorem B6100433 : Blo 1805604 6100433 := bstep (se 2 (by rfl) ⟨2287662, by rfl⟩ : syracuseStep 6100433 = 4575325) B4575325
theorem B2708963 : Blo 1805604 2708963 := bstep (se 1 (by rfl) ⟨2031722, by rfl⟩ : syracuseStep 2708963 = 4063445) B4063445
theorem B2708993 : Blo 1805604 2708993 := bstep (se 2 (by rfl) ⟨1015872, by rfl⟩ : syracuseStep 2708993 = 2031745) B2031745
theorem B2709011 : Blo 1805604 2709011 := bstep (se 1 (by rfl) ⟨2031758, by rfl⟩ : syracuseStep 2709011 = 4063517) B4063517
theorem B2709041 : Blo 1805604 2709041 := bstep (se 2 (by rfl) ⟨1015890, by rfl⟩ : syracuseStep 2709041 = 2031781) B2031781
theorem B2709059 : Blo 1805604 2709059 := bstep (se 1 (by rfl) ⟨2031794, by rfl⟩ : syracuseStep 2709059 = 4063589) B4063589
theorem B2709089 : Blo 1805604 2709089 := bstep (se 2 (by rfl) ⟨1015908, by rfl⟩ : syracuseStep 2709089 = 2031817) B2031817
theorem B2709107 : Blo 1805604 2709107 := bstep (se 1 (by rfl) ⟨2031830, by rfl⟩ : syracuseStep 2709107 = 4063661) B4063661
theorem B2709137 : Blo 1805604 2709137 := bstep (se 2 (by rfl) ⟨1015926, by rfl⟩ : syracuseStep 2709137 = 2031853) B2031853
theorem B2709155 : Blo 1805604 2709155 := bstep (se 1 (by rfl) ⟨2031866, by rfl⟩ : syracuseStep 2709155 = 4063733) B4063733
theorem B2709185 : Blo 1805604 2709185 := bstep (se 2 (by rfl) ⟨1015944, by rfl⟩ : syracuseStep 2709185 = 2031889) B2031889
theorem B3430097 : Blo 1805604 3430097 := bstep (se 2 (by rfl) ⟨1286286, by rfl⟩ : syracuseStep 3430097 = 2572573) B2572573
theorem B2709203 : Blo 1805604 2709203 := bstep (se 1 (by rfl) ⟨2031902, by rfl⟩ : syracuseStep 2709203 = 4063805) B4063805
theorem B2709233 : Blo 1805604 2709233 := bstep (se 2 (by rfl) ⟨1015962, by rfl⟩ : syracuseStep 2709233 = 2031925) B2031925
theorem B5142275 : Blo 1805604 5142275 := bstep (se 1 (by rfl) ⟨3856706, by rfl⟩ : syracuseStep 5142275 = 7713413) B7713413
theorem B2709251 : Blo 1805604 2709251 := bstep (se 1 (by rfl) ⟨2031938, by rfl⟩ : syracuseStep 2709251 = 4063877) B4063877
theorem B2709281 : Blo 1805604 2709281 := bstep (se 2 (by rfl) ⟨1015980, by rfl⟩ : syracuseStep 2709281 = 2031961) B2031961
theorem B2709299 : Blo 1805604 2709299 := bstep (se 1 (by rfl) ⟨2031974, by rfl⟩ : syracuseStep 2709299 = 4063949) B4063949
theorem B2709329 : Blo 1805604 2709329 := bstep (se 2 (by rfl) ⟨1015998, by rfl⟩ : syracuseStep 2709329 = 2031997) B2031997
theorem B2709347 : Blo 1805604 2709347 := bstep (se 1 (by rfl) ⟨2032010, by rfl⟩ : syracuseStep 2709347 = 4064021) B4064021
theorem B2709377 : Blo 1805604 2709377 := bstep (se 2 (by rfl) ⟨1016016, by rfl⟩ : syracuseStep 2709377 = 2032033) B2032033
theorem B8681357 : Blo 1805604 8681357 := bstep (se 3 (by rfl) ⟨1627754, by rfl⟩ : syracuseStep 8681357 = 3255509) B3255509
theorem B9148301 : Blo 1805604 9148301 := bstep (se 3 (by rfl) ⟨1715306, by rfl⟩ : syracuseStep 9148301 = 3430613) B3430613
theorem B2709395 : Blo 1805604 2709395 := bstep (se 1 (by rfl) ⟨2032046, by rfl⟩ : syracuseStep 2709395 = 4064093) B4064093
theorem B2709425 : Blo 1805604 2709425 := bstep (se 2 (by rfl) ⟨1016034, by rfl⟩ : syracuseStep 2709425 = 2032069) B2032069
theorem B2709443 : Blo 1805604 2709443 := bstep (se 1 (by rfl) ⟨2032082, by rfl⟩ : syracuseStep 2709443 = 4064165) B4064165
theorem B20568005 : Blo 1805604 20568005 := bstep (se 4 (by rfl) ⟨1928250, by rfl⟩ : syracuseStep 20568005 = 3856501) B3856501
theorem B1882067 : Blo 1805604 1882067 := bstep (se 1 (by rfl) ⟨1411550, by rfl⟩ : syracuseStep 1882067 = 2823101) B2823101
theorem B2709473 : Blo 1805604 2709473 := bstep (se 2 (by rfl) ⟨1016052, by rfl⟩ : syracuseStep 2709473 = 2032105) B2032105
theorem B2709491 : Blo 1805604 2709491 := bstep (se 1 (by rfl) ⟨2032118, by rfl⟩ : syracuseStep 2709491 = 4064237) B4064237
theorem B16488461 : Blo 1805604 16488461 := bstep (se 3 (by rfl) ⟨3091586, by rfl⟩ : syracuseStep 16488461 = 6183173) B6183173
theorem B2709521 : Blo 1805604 2709521 := bstep (se 2 (by rfl) ⟨1016070, by rfl⟩ : syracuseStep 2709521 = 2032141) B2032141
theorem B2709539 : Blo 1805604 2709539 := bstep (se 1 (by rfl) ⟨2032154, by rfl⟩ : syracuseStep 2709539 = 4064309) B4064309
theorem B2709569 : Blo 1805604 2709569 := bstep (se 2 (by rfl) ⟨1016088, by rfl⟩ : syracuseStep 2709569 = 2032177) B2032177
theorem B2709587 : Blo 1805604 2709587 := bstep (se 1 (by rfl) ⟨2032190, by rfl⟩ : syracuseStep 2709587 = 4064381) B4064381
theorem B169187413 : Blo 1805604 169187413 := bstep (se 8 (by rfl) ⟨991332, by rfl⟩ : syracuseStep 169187413 = 1982665) B1982665
theorem B2709617 : Blo 1805604 2709617 := bstep (se 2 (by rfl) ⟨1016106, by rfl⟩ : syracuseStep 2709617 = 2032213) B2032213
theorem B2709635 : Blo 1805604 2709635 := bstep (se 1 (by rfl) ⟨2032226, by rfl⟩ : syracuseStep 2709635 = 4064453) B4064453
theorem B2709665 : Blo 1805604 2709665 := bstep (se 2 (by rfl) ⟨1016124, by rfl⟩ : syracuseStep 2709665 = 2032249) B2032249
theorem B2709683 : Blo 1805604 2709683 := bstep (se 1 (by rfl) ⟨2032262, by rfl⟩ : syracuseStep 2709683 = 4064525) B4064525
theorem B2709713 : Blo 1805604 2709713 := bstep (se 2 (by rfl) ⟨1016142, by rfl⟩ : syracuseStep 2709713 = 2032285) B2032285
theorem B2709731 : Blo 1805604 2709731 := bstep (se 1 (by rfl) ⟨2032298, by rfl⟩ : syracuseStep 2709731 = 4064597) B4064597
theorem B13719779 : Blo 1805604 13719779 := bstep (se 1 (by rfl) ⟨10289834, by rfl⟩ : syracuseStep 13719779 = 20579669) B20579669
theorem B2709761 : Blo 1805604 2709761 := bstep (se 2 (by rfl) ⟨1016160, by rfl⟩ : syracuseStep 2709761 = 2032321) B2032321
theorem B2709779 : Blo 1805604 2709779 := bstep (se 1 (by rfl) ⟨2032334, by rfl⟩ : syracuseStep 2709779 = 4064669) B4064669
theorem B2709809 : Blo 1805604 2709809 := bstep (se 2 (by rfl) ⟨1016178, by rfl⟩ : syracuseStep 2709809 = 2032357) B2032357
theorem B2709827 : Blo 1805604 2709827 := bstep (se 1 (by rfl) ⟨2032370, by rfl⟩ : syracuseStep 2709827 = 4064741) B4064741
theorem B2709857 : Blo 1805604 2709857 := bstep (se 2 (by rfl) ⟨1016196, by rfl⟩ : syracuseStep 2709857 = 2032393) B2032393
theorem B2709875 : Blo 1805604 2709875 := bstep (se 1 (by rfl) ⟨2032406, by rfl⟩ : syracuseStep 2709875 = 4064813) B4064813
theorem B41703821 : Blo 1805604 41703821 := bstep (se 3 (by rfl) ⟨7819466, by rfl⟩ : syracuseStep 41703821 = 15638933) B15638933
theorem B2709905 : Blo 1805604 2709905 := bstep (se 2 (by rfl) ⟨1016214, by rfl⟩ : syracuseStep 2709905 = 2032429) B2032429
theorem B2709923 : Blo 1805604 2709923 := bstep (se 1 (by rfl) ⟨2032442, by rfl⟩ : syracuseStep 2709923 = 4064885) B4064885
theorem B4176305 : Blo 1805604 4176305 := bstep (se 2 (by rfl) ⟨1566114, by rfl⟩ : syracuseStep 4176305 = 3132229) B3132229
theorem B2709953 : Blo 1805604 2709953 := bstep (se 2 (by rfl) ⟨1016232, by rfl⟩ : syracuseStep 2709953 = 2032465) B2032465
theorem B3856835 : Blo 1805604 3856835 := bstep (se 1 (by rfl) ⟨2892626, by rfl⟩ : syracuseStep 3856835 = 5785253) B5785253
theorem B10287557 : Blo 1805604 10287557 := bstep (se 4 (by rfl) ⟨964458, by rfl⟩ : syracuseStep 10287557 = 1928917) B1928917
theorem B2709971 : Blo 1805604 2709971 := bstep (se 1 (by rfl) ⟨2032478, by rfl⟩ : syracuseStep 2709971 = 4064957) B4064957
theorem B20576753 : Blo 1805604 20576753 := bstep (se 2 (by rfl) ⟨7716282, by rfl⟩ : syracuseStep 20576753 = 15432565) B15432565
theorem B2710001 : Blo 1805604 2710001 := bstep (se 2 (by rfl) ⟨1016250, by rfl⟩ : syracuseStep 2710001 = 2032501) B2032501
theorem B2710019 : Blo 1805604 2710019 := bstep (se 1 (by rfl) ⟨2032514, by rfl⟩ : syracuseStep 2710019 = 4065029) B4065029
theorem B2710049 : Blo 1805604 2710049 := bstep (se 2 (by rfl) ⟨1016268, by rfl⟩ : syracuseStep 2710049 = 2032537) B2032537
theorem B2169379 : Blo 1805604 2169379 := bstep (se 1 (by rfl) ⟨1627034, by rfl⟩ : syracuseStep 2169379 = 3254069) B3254069
theorem B5143085 : Blo 1805604 5143085 := bstep (se 3 (by rfl) ⟨964328, by rfl⟩ : syracuseStep 5143085 = 1928657) B1928657
theorem B2710067 : Blo 1805604 2710067 := bstep (se 1 (by rfl) ⟨2032550, by rfl⟩ : syracuseStep 2710067 = 4065101) B4065101
theorem B2710097 : Blo 1805604 2710097 := bstep (se 2 (by rfl) ⟨1016286, by rfl⟩ : syracuseStep 2710097 = 2032573) B2032573
theorem B5495377 : Blo 1805604 5495377 := bstep (se 2 (by rfl) ⟨2060766, by rfl⟩ : syracuseStep 5495377 = 4121533) B4121533
theorem B3430993 : Blo 1805604 3430993 := bstep (se 2 (by rfl) ⟨1286622, by rfl⟩ : syracuseStep 3430993 = 2573245) B2573245
theorem B2710115 : Blo 1805604 2710115 := bstep (se 1 (by rfl) ⟨2032586, by rfl⟩ : syracuseStep 2710115 = 4065173) B4065173
theorem B2710145 : Blo 1805604 2710145 := bstep (se 2 (by rfl) ⟨1016304, by rfl⟩ : syracuseStep 2710145 = 2032609) B2032609
theorem B2710163 : Blo 1805604 2710163 := bstep (se 1 (by rfl) ⟨2032622, by rfl⟩ : syracuseStep 2710163 = 4065245) B4065245
theorem B2710193 : Blo 1805604 2710193 := bstep (se 2 (by rfl) ⟨1016322, by rfl⟩ : syracuseStep 2710193 = 2032645) B2032645
theorem B2710211 : Blo 1805604 2710211 := bstep (se 1 (by rfl) ⟨2032658, by rfl⟩ : syracuseStep 2710211 = 4065317) B4065317
theorem B2710241 : Blo 1805604 2710241 := bstep (se 2 (by rfl) ⟨1016340, by rfl⟩ : syracuseStep 2710241 = 2032681) B2032681
theorem B2169571 : Blo 1805604 2169571 := bstep (se 1 (by rfl) ⟨1627178, by rfl⟩ : syracuseStep 2169571 = 3254357) B3254357
theorem B5143277 : Blo 1805604 5143277 := bstep (se 3 (by rfl) ⟨964364, by rfl⟩ : syracuseStep 5143277 = 1928729) B1928729
theorem B3431153 : Blo 1805604 3431153 := bstep (se 2 (by rfl) ⟨1286682, by rfl⟩ : syracuseStep 3431153 = 2573365) B2573365
theorem B2710259 : Blo 1805604 2710259 := bstep (se 1 (by rfl) ⟨2032694, by rfl⟩ : syracuseStep 2710259 = 4065389) B4065389
theorem B2710289 : Blo 1805604 2710289 := bstep (se 2 (by rfl) ⟨1016358, by rfl⟩ : syracuseStep 2710289 = 2032717) B2032717
theorem B2571041 : Blo 1805604 2571041 := bstep (se 2 (by rfl) ⟨964140, by rfl⟩ : syracuseStep 2571041 = 1928281) B1928281
theorem B2710307 : Blo 1805604 2710307 := bstep (se 1 (by rfl) ⟨2032730, by rfl⟩ : syracuseStep 2710307 = 4065461) B4065461
theorem B2710337 : Blo 1805604 2710337 := bstep (se 2 (by rfl) ⟨1016376, by rfl⟩ : syracuseStep 2710337 = 2032753) B2032753
theorem B2710355 : Blo 1805604 2710355 := bstep (se 1 (by rfl) ⟨2032766, by rfl⟩ : syracuseStep 2710355 = 4065533) B4065533
theorem B2710385 : Blo 1805604 2710385 := bstep (se 2 (by rfl) ⟨1016394, by rfl⟩ : syracuseStep 2710385 = 2032789) B2032789
theorem B2169715 : Blo 1805604 2169715 := bstep (se 1 (by rfl) ⟨1627286, by rfl⟩ : syracuseStep 2169715 = 3254573) B3254573
theorem B2710403 : Blo 1805604 2710403 := bstep (se 1 (by rfl) ⟨2032802, by rfl⟩ : syracuseStep 2710403 = 4065605) B4065605
theorem B32971661 : Blo 1805604 32971661 := bstep (se 3 (by rfl) ⟨6182186, by rfl⟩ : syracuseStep 32971661 = 12364373) B12364373
theorem B2710433 : Blo 1805604 2710433 := bstep (se 2 (by rfl) ⟨1016412, by rfl⟩ : syracuseStep 2710433 = 2032825) B2032825
theorem B2710451 : Blo 1805604 2710451 := bstep (se 1 (by rfl) ⟨2032838, by rfl⟩ : syracuseStep 2710451 = 4065677) B4065677
theorem B2710481 : Blo 1805604 2710481 := bstep (se 2 (by rfl) ⟨1016430, by rfl⟩ : syracuseStep 2710481 = 2032861) B2032861
theorem B2710499 : Blo 1805604 2710499 := bstep (se 1 (by rfl) ⟨2032874, by rfl⟩ : syracuseStep 2710499 = 4065749) B4065749
theorem B2710529 : Blo 1805604 2710529 := bstep (se 2 (by rfl) ⟨1016448, by rfl⟩ : syracuseStep 2710529 = 2032897) B2032897
theorem B2710547 : Blo 1805604 2710547 := bstep (se 1 (by rfl) ⟨2032910, by rfl⟩ : syracuseStep 2710547 = 4065821) B4065821
theorem B4340785 : Blo 1805604 4340785 := bstep (se 2 (by rfl) ⟨1627794, by rfl⟩ : syracuseStep 4340785 = 3255589) B3255589
theorem B2710577 : Blo 1805604 2710577 := bstep (se 2 (by rfl) ⟨1016466, by rfl⟩ : syracuseStep 2710577 = 2032933) B2032933
theorem B2710595 : Blo 1805604 2710595 := bstep (se 1 (by rfl) ⟨2032946, by rfl⟩ : syracuseStep 2710595 = 4065893) B4065893
theorem B2710625 : Blo 1805604 2710625 := bstep (se 2 (by rfl) ⟨1016484, by rfl⟩ : syracuseStep 2710625 = 2032969) B2032969
theorem B10288241 : Blo 1805604 10288241 := bstep (se 2 (by rfl) ⟨3858090, by rfl⟩ : syracuseStep 10288241 = 7716181) B7716181
theorem B2710643 : Blo 1805604 2710643 := bstep (se 1 (by rfl) ⟨2032982, by rfl⟩ : syracuseStep 2710643 = 4065965) B4065965
theorem B3431555 : Blo 1805604 3431555 := bstep (se 1 (by rfl) ⟨2573666, by rfl⟩ : syracuseStep 3431555 = 5147333) B5147333
theorem B2710673 : Blo 1805604 2710673 := bstep (se 2 (by rfl) ⟨1016502, by rfl⟩ : syracuseStep 2710673 = 2033005) B2033005
theorem B2710691 : Blo 1805604 2710691 := bstep (se 1 (by rfl) ⟨2033018, by rfl⟩ : syracuseStep 2710691 = 4066037) B4066037
theorem B2710721 : Blo 1805604 2710721 := bstep (se 2 (by rfl) ⟨1016520, by rfl⟩ : syracuseStep 2710721 = 2033041) B2033041
theorem B2710739 : Blo 1805604 2710739 := bstep (se 1 (by rfl) ⟨2033054, by rfl⟩ : syracuseStep 2710739 = 4066109) B4066109
theorem B6094061 : Blo 1805604 6094061 := bstep (se 3 (by rfl) ⟨1142636, by rfl⟩ : syracuseStep 6094061 = 2285273) B2285273
theorem B2710769 : Blo 1805604 2710769 := bstep (se 2 (by rfl) ⟨1016538, by rfl⟩ : syracuseStep 2710769 = 2033077) B2033077
theorem B2710787 : Blo 1805604 2710787 := bstep (se 1 (by rfl) ⟨2033090, by rfl⟩ : syracuseStep 2710787 = 4066181) B4066181
theorem B3857681 : Blo 1805604 3857681 := bstep (se 2 (by rfl) ⟨1446630, by rfl⟩ : syracuseStep 3857681 = 2893261) B2893261
theorem B2710817 : Blo 1805604 2710817 := bstep (se 2 (by rfl) ⟨1016556, by rfl⟩ : syracuseStep 2710817 = 2033113) B2033113
theorem B6094115 : Blo 1805604 6094115 := bstep (se 1 (by rfl) ⟨4570586, by rfl⟩ : syracuseStep 6094115 = 9141173) B9141173
theorem B7716131 : Blo 1805604 7716131 := bstep (se 1 (by rfl) ⟨5787098, by rfl⟩ : syracuseStep 7716131 = 11574197) B11574197
theorem B2710835 : Blo 1805604 2710835 := bstep (se 1 (by rfl) ⟨2033126, by rfl⟩ : syracuseStep 2710835 = 4066253) B4066253
theorem B23469365 : Blo 1805604 23469365 := bstep (se 5 (by rfl) ⟨1100126, by rfl⟩ : syracuseStep 23469365 = 2200253) B2200253
theorem B2710865 : Blo 1805604 2710865 := bstep (se 2 (by rfl) ⟨1016574, by rfl⟩ : syracuseStep 2710865 = 2033149) B2033149
theorem B2710883 : Blo 1805604 2710883 := bstep (se 1 (by rfl) ⟨2033162, by rfl⟩ : syracuseStep 2710883 = 4066325) B4066325
theorem B2710913 : Blo 1805604 2710913 := bstep (se 2 (by rfl) ⟨1016592, by rfl⟩ : syracuseStep 2710913 = 2033185) B2033185
theorem B2710931 : Blo 1805604 2710931 := bstep (se 1 (by rfl) ⟨2033198, by rfl⟩ : syracuseStep 2710931 = 4066397) B4066397
theorem B2710961 : Blo 1805604 2710961 := bstep (se 2 (by rfl) ⟨1016610, by rfl⟩ : syracuseStep 2710961 = 2033221) B2033221
theorem B2710979 : Blo 1805604 2710979 := bstep (se 1 (by rfl) ⟨2033234, by rfl⟩ : syracuseStep 2710979 = 4066469) B4066469
theorem B4570577 : Blo 1805604 4570577 := bstep (se 2 (by rfl) ⟨1713966, by rfl⟩ : syracuseStep 4570577 = 3427933) B3427933
theorem B2711009 : Blo 1805604 2711009 := bstep (se 2 (by rfl) ⟨1016628, by rfl⟩ : syracuseStep 2711009 = 2033257) B2033257
theorem B2711027 : Blo 1805604 2711027 := bstep (se 1 (by rfl) ⟨2033270, by rfl⟩ : syracuseStep 2711027 = 4066541) B4066541
theorem B4570627 : Blo 1805604 4570627 := bstep (se 1 (by rfl) ⟨3427970, by rfl⟩ : syracuseStep 4570627 = 6855941) B6855941
theorem B2711057 : Blo 1805604 2711057 := bstep (se 2 (by rfl) ⟨1016646, by rfl⟩ : syracuseStep 2711057 = 2033293) B2033293
theorem B2711075 : Blo 1805604 2711075 := bstep (se 1 (by rfl) ⟨2033306, by rfl⟩ : syracuseStep 2711075 = 4066613) B4066613
theorem B6094385 : Blo 1805604 6094385 := bstep (se 2 (by rfl) ⟨2285394, by rfl⟩ : syracuseStep 6094385 = 4570789) B4570789
theorem B3046963 : Blo 1805604 3046963 := bstep (se 1 (by rfl) ⟨2285222, by rfl⟩ : syracuseStep 3046963 = 4570445) B4570445
theorem B2711105 : Blo 1805604 2711105 := bstep (se 2 (by rfl) ⟨1016664, by rfl⟩ : syracuseStep 2711105 = 2033329) B2033329
theorem B2711123 : Blo 1805604 2711123 := bstep (se 1 (by rfl) ⟨2033342, by rfl⟩ : syracuseStep 2711123 = 4066685) B4066685
theorem B4062833 : Blo 1805604 4062833 := bstep (se 2 (by rfl) ⟨1523562, by rfl⟩ : syracuseStep 4062833 = 3047125) B3047125
theorem B23158385 : Blo 1805604 23158385 := bstep (se 2 (by rfl) ⟨8684394, by rfl⟩ : syracuseStep 23158385 = 17368789) B17368789
theorem B2711153 : Blo 1805604 2711153 := bstep (se 2 (by rfl) ⟨1016682, by rfl⟩ : syracuseStep 2711153 = 2033365) B2033365
theorem B2571907 : Blo 1805604 2571907 := bstep (se 1 (by rfl) ⟨1928930, by rfl⟩ : syracuseStep 2571907 = 3857861) B3857861
theorem B4062851 : Blo 1805604 4062851 := bstep (se 1 (by rfl) ⟨3047138, by rfl⟩ : syracuseStep 4062851 = 6094277) B6094277
theorem B2711171 : Blo 1805604 2711171 := bstep (se 1 (by rfl) ⟨2033378, by rfl⟩ : syracuseStep 2711171 = 4066757) B4066757
theorem B4570769 : Blo 1805604 4570769 := bstep (se 2 (by rfl) ⟨1714038, by rfl⟩ : syracuseStep 4570769 = 3428077) B3428077
theorem B2711201 : Blo 1805604 2711201 := bstep (se 2 (by rfl) ⟨1016700, by rfl⟩ : syracuseStep 2711201 = 2033401) B2033401
theorem B2711219 : Blo 1805604 2711219 := bstep (se 1 (by rfl) ⟨2033414, by rfl⟩ : syracuseStep 2711219 = 4066829) B4066829
theorem B3047105 : Blo 1805604 3047105 := bstep (se 2 (by rfl) ⟨1142664, by rfl⟩ : syracuseStep 3047105 = 2285329) B2285329
theorem B2440897 : Blo 1805604 2440897 := bstep (se 2 (by rfl) ⟨915336, by rfl⟩ : syracuseStep 2440897 = 1830673) B1830673
theorem B6856397 : Blo 1805604 6856397 := bstep (se 3 (by rfl) ⟨1285574, by rfl⟩ : syracuseStep 6856397 = 2571149) B2571149
theorem B5144269 : Blo 1805604 5144269 := bstep (se 3 (by rfl) ⟨964550, by rfl⟩ : syracuseStep 5144269 = 1929101) B1929101
theorem B2711249 : Blo 1805604 2711249 := bstep (se 2 (by rfl) ⟨1016718, by rfl⟩ : syracuseStep 2711249 = 2033437) B2033437
theorem B2031331 : Blo 1805604 2031331 := bstep (se 1 (by rfl) ⟨1523498, by rfl⟩ : syracuseStep 2031331 = 3046997) B3046997
theorem B2572003 : Blo 1805604 2572003 := bstep (se 1 (by rfl) ⟨1929002, by rfl⟩ : syracuseStep 2572003 = 3858005) B3858005
theorem B2711267 : Blo 1805604 2711267 := bstep (se 1 (by rfl) ⟨2033450, by rfl⟩ : syracuseStep 2711267 = 4066901) B4066901
theorem B2711297 : Blo 1805604 2711297 := bstep (se 2 (by rfl) ⟨1016736, by rfl⟩ : syracuseStep 2711297 = 2033473) B2033473
theorem B2711315 : Blo 1805604 2711315 := bstep (se 1 (by rfl) ⟨2033486, by rfl⟩ : syracuseStep 2711315 = 4066973) B4066973
theorem B2711345 : Blo 1805604 2711345 := bstep (se 2 (by rfl) ⟨1016754, by rfl⟩ : syracuseStep 2711345 = 2033509) B2033509
theorem B3047233 : Blo 1805604 3047233 := bstep (se 2 (by rfl) ⟨1142712, by rfl⟩ : syracuseStep 3047233 = 2285425) B2285425
theorem B2711363 : Blo 1805604 2711363 := bstep (se 1 (by rfl) ⟨2033522, by rfl⟩ : syracuseStep 2711363 = 4067045) B4067045
theorem B3047267 : Blo 1805604 3047267 := bstep (se 1 (by rfl) ⟨2285450, by rfl⟩ : syracuseStep 3047267 = 4570901) B4570901
theorem B2711393 : Blo 1805604 2711393 := bstep (se 2 (by rfl) ⟨1016772, by rfl⟩ : syracuseStep 2711393 = 2033545) B2033545
theorem B2031475 : Blo 1805604 2031475 := bstep (se 1 (by rfl) ⟨1523606, by rfl⟩ : syracuseStep 2031475 = 3047213) B3047213
theorem B4063121 : Blo 1805604 4063121 := bstep (se 2 (by rfl) ⟨1523670, by rfl⟩ : syracuseStep 4063121 = 3047341) B3047341
theorem B4063139 : Blo 1805604 4063139 := bstep (se 1 (by rfl) ⟨3047354, by rfl⟩ : syracuseStep 4063139 = 6094709) B6094709
theorem B10993571 : Blo 1805604 10993571 := bstep (se 1 (by rfl) ⟨8245178, by rfl⟩ : syracuseStep 10993571 = 16490357) B16490357
theorem B2285491 : Blo 1805604 2285491 := bstep (se 1 (by rfl) ⟨1714118, by rfl⟩ : syracuseStep 2285491 = 3428237) B3428237
theorem B3047395 : Blo 1805604 3047395 := bstep (se 1 (by rfl) ⟨2285546, by rfl⟩ : syracuseStep 3047395 = 4571093) B4571093
theorem B6094871 : Blo 1805604 6094871 := bstep (se 1 (by rfl) ⟨4571153, by rfl⟩ : syracuseStep 6094871 = 9142307) B9142307
theorem B3047449 : Blo 1805604 3047449 := bstep (se 2 (by rfl) ⟨1142793, by rfl⟩ : syracuseStep 3047449 = 2285587) B2285587
theorem B4063283 : Blo 1805604 4063283 := bstep (se 1 (by rfl) ⟨3047462, by rfl⟩ : syracuseStep 4063283 = 6094925) B6094925
theorem B2031691 : Blo 1805604 2031691 := bstep (se 1 (by rfl) ⟨1523768, by rfl⟩ : syracuseStep 2031691 = 3047537) B3047537
theorem B4063319 : Blo 1805604 4063319 := bstep (se 1 (by rfl) ⟨3047489, by rfl⟩ : syracuseStep 4063319 = 6094979) B6094979
theorem B4571225 : Blo 1805604 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B225583217 : Blo 1805604 225583217 := bstep (se 2 (by rfl) ⟨84593706, by rfl⟩ : syracuseStep 225583217 = 169187413) B169187413
theorem B6856883 : Blo 1805604 6856883 := bstep (se 1 (by rfl) ⟨5142662, by rfl⟩ : syracuseStep 6856883 = 10285325) B10285325
theorem B2031799 : Blo 1805604 2031799 := bstep (se 1 (by rfl) ⟨1523849, by rfl⟩ : syracuseStep 2031799 = 3047699) B3047699
theorem B3662027 : Blo 1805604 3662027 := bstep (se 1 (by rfl) ⟨2746520, by rfl⟩ : syracuseStep 3662027 = 5493041) B5493041
theorem B4063499 : Blo 1805604 4063499 := bstep (se 1 (by rfl) ⟨3047624, by rfl⟩ : syracuseStep 4063499 = 6095249) B6095249
theorem B6603059 : Blo 1805604 6603059 := bstep (se 1 (by rfl) ⟨4952294, by rfl⟩ : syracuseStep 6603059 = 9904589) B9904589
theorem B4063553 : Blo 1805604 4063553 := bstep (se 2 (by rfl) ⟨1523832, by rfl⟩ : syracuseStep 4063553 = 3047665) B3047665
theorem B2285911 : Blo 1805604 2285911 := bstep (se 1 (by rfl) ⟨1714433, by rfl⟩ : syracuseStep 2285911 = 3428867) B3428867
theorem B2031979 : Blo 1805604 2031979 := bstep (se 1 (by rfl) ⟨1523984, by rfl⟩ : syracuseStep 2031979 = 3047969) B3047969
theorem B2441611 : Blo 1805604 2441611 := bstep (se 1 (by rfl) ⟨1831208, by rfl⟩ : syracuseStep 2441611 = 3662417) B3662417
theorem B2032087 : Blo 1805604 2032087 := bstep (se 1 (by rfl) ⟨1524065, by rfl⟩ : syracuseStep 2032087 = 3048131) B3048131
theorem B4063769 : Blo 1805604 4063769 := bstep (se 2 (by rfl) ⟨1523913, by rfl⟩ : syracuseStep 4063769 = 3047827) B3047827
theorem B6095411 : Blo 1805604 6095411 := bstep (se 1 (by rfl) ⟨4571558, by rfl⟩ : syracuseStep 6095411 = 9143117) B9143117
theorem B3048023 : Blo 1805604 3048023 := bstep (se 1 (by rfl) ⟨2286017, by rfl⟩ : syracuseStep 3048023 = 4572035) B4572035
theorem B4063859 : Blo 1805604 4063859 := bstep (se 1 (by rfl) ⟨3047894, by rfl⟩ : syracuseStep 4063859 = 6095789) B6095789
theorem B2032267 : Blo 1805604 2032267 := bstep (se 1 (by rfl) ⟨1524200, by rfl⟩ : syracuseStep 2032267 = 3048401) B3048401
theorem B4063895 : Blo 1805604 4063895 := bstep (se 1 (by rfl) ⟨3047921, by rfl⟩ : syracuseStep 4063895 = 6095843) B6095843
theorem B28959383 : Blo 1805604 28959383 := bstep (se 1 (by rfl) ⟨21719537, by rfl⟩ : syracuseStep 28959383 = 43439075) B43439075
theorem B29303477 : Blo 1805604 29303477 := bstep (se 5 (by rfl) ⟨1373600, by rfl⟩ : syracuseStep 29303477 = 2747201) B2747201
theorem B3048151 : Blo 1805604 3048151 := bstep (se 1 (by rfl) ⟨2286113, by rfl⟩ : syracuseStep 3048151 = 4572227) B4572227
theorem B3859159 : Blo 1805604 3859159 := bstep (se 1 (by rfl) ⟨2894369, by rfl⟩ : syracuseStep 3859159 = 5788739) B5788739
theorem B2892505 : Blo 1805604 2892505 := bstep (se 2 (by rfl) ⟨1084689, by rfl⟩ : syracuseStep 2892505 = 2169379) B2169379
theorem B2032375 : Blo 1805604 2032375 := bstep (se 1 (by rfl) ⟨1524281, by rfl⟩ : syracuseStep 2032375 = 3048563) B3048563
theorem B3859201 : Blo 1805604 3859201 := bstep (se 2 (by rfl) ⟨1447200, by rfl⟩ : syracuseStep 3859201 = 2894401) B2894401
theorem B6095681 : Blo 1805604 6095681 := bstep (se 2 (by rfl) ⟨2285880, by rfl⟩ : syracuseStep 6095681 = 4571761) B4571761
theorem B4064075 : Blo 1805604 4064075 := bstep (se 1 (by rfl) ⟨3048056, by rfl⟩ : syracuseStep 4064075 = 6096113) B6096113
theorem B5145419 : Blo 1805604 5145419 := bstep (se 1 (by rfl) ⟨3859064, by rfl⟩ : syracuseStep 5145419 = 7718129) B7718129
theorem B4064129 : Blo 1805604 4064129 := bstep (se 2 (by rfl) ⟨1524048, by rfl⟩ : syracuseStep 4064129 = 3048097) B3048097
theorem B4342679 : Blo 1805604 4342679 := bstep (se 1 (by rfl) ⟨3257009, by rfl⟩ : syracuseStep 4342679 = 6514019) B6514019
theorem B2032555 : Blo 1805604 2032555 := bstep (se 1 (by rfl) ⟨1524416, by rfl⟩ : syracuseStep 2032555 = 3048833) B3048833
theorem B2892761 : Blo 1805604 2892761 := bstep (se 2 (by rfl) ⟨1084785, by rfl⟩ : syracuseStep 2892761 = 2169571) B2169571
theorem B13018117 : Blo 1805604 13018117 := bstep (se 4 (by rfl) ⟨1220448, by rfl⟩ : syracuseStep 13018117 = 2440897) B2440897
theorem B11731985 : Blo 1805604 11731985 := bstep (se 2 (by rfl) ⟨4399494, by rfl⟩ : syracuseStep 11731985 = 8798989) B8798989
theorem B2032663 : Blo 1805604 2032663 := bstep (se 1 (by rfl) ⟨1524497, by rfl⟩ : syracuseStep 2032663 = 3048995) B3048995
theorem B29295685 : Blo 1805604 29295685 := bstep (se 4 (by rfl) ⟨2746470, by rfl⟩ : syracuseStep 29295685 = 5492941) B5492941
theorem B4064345 : Blo 1805604 4064345 := bstep (se 2 (by rfl) ⟨1524129, by rfl⟩ : syracuseStep 4064345 = 3048259) B3048259
theorem B11289701 : Blo 1805604 11289701 := bstep (se 4 (by rfl) ⟨1058409, by rfl⟩ : syracuseStep 11289701 = 2116819) B2116819
theorem B2286731 : Blo 1805604 2286731 := bstep (se 1 (by rfl) ⟨1715048, by rfl⟩ : syracuseStep 2286731 = 3430097) B3430097
theorem B2892953 : Blo 1805604 2892953 := bstep (se 2 (by rfl) ⟨1084857, by rfl⟩ : syracuseStep 2892953 = 2169715) B2169715
theorem B4064435 : Blo 1805604 4064435 := bstep (se 1 (by rfl) ⟨3048326, by rfl⟩ : syracuseStep 4064435 = 6096653) B6096653
theorem B2032843 : Blo 1805604 2032843 := bstep (se 1 (by rfl) ⟨1524632, by rfl⟩ : syracuseStep 2032843 = 3049265) B3049265
theorem B4064471 : Blo 1805604 4064471 := bstep (se 1 (by rfl) ⟨3048353, by rfl⟩ : syracuseStep 4064471 = 6096707) B6096707
theorem B2032951 : Blo 1805604 2032951 := bstep (se 1 (by rfl) ⟨1524713, by rfl⟩ : syracuseStep 2032951 = 3049427) B3049427
theorem B3048779 : Blo 1805604 3048779 := bstep (se 1 (by rfl) ⟨2286584, by rfl⟩ : syracuseStep 3048779 = 4573169) B4573169
theorem B6096221 : Blo 1805604 6096221 := bstep (se 3 (by rfl) ⟨1143041, by rfl⟩ : syracuseStep 6096221 = 2286083) B2286083
theorem B4064651 : Blo 1805604 4064651 := bstep (se 1 (by rfl) ⟨3048488, by rfl⟩ : syracuseStep 4064651 = 6096977) B6096977
theorem B2442649 : Blo 1805604 2442649 := bstep (se 2 (by rfl) ⟨915993, by rfl⟩ : syracuseStep 2442649 = 1831987) B1831987
theorem B4064705 : Blo 1805604 4064705 := bstep (se 2 (by rfl) ⟨1524264, by rfl⟩ : syracuseStep 4064705 = 3048529) B3048529
theorem B3048907 : Blo 1805604 3048907 := bstep (se 1 (by rfl) ⟨2286680, by rfl⟩ : syracuseStep 3048907 = 4573361) B4573361
theorem B2033131 : Blo 1805604 2033131 := bstep (se 1 (by rfl) ⟨1524848, by rfl⟩ : syracuseStep 2033131 = 3049697) B3049697
theorem B5785111 : Blo 1805604 5785111 := bstep (se 1 (by rfl) ⟨4338833, by rfl⟩ : syracuseStep 5785111 = 8677667) B8677667
theorem B15435299 : Blo 1805604 15435299 := bstep (se 1 (by rfl) ⟨11576474, by rfl⟩ : syracuseStep 15435299 = 23152949) B23152949
theorem B24725027 : Blo 1805604 24725027 := bstep (se 1 (by rfl) ⟨18543770, by rfl⟩ : syracuseStep 24725027 = 37087541) B37087541
theorem B13723181 : Blo 1805604 13723181 := bstep (se 3 (by rfl) ⟨2573096, by rfl⟩ : syracuseStep 13723181 = 5146193) B5146193
theorem B2033239 : Blo 1805604 2033239 := bstep (se 1 (by rfl) ⟨1524929, by rfl⟩ : syracuseStep 2033239 = 3049859) B3049859
theorem B3049049 : Blo 1805604 3049049 := bstep (se 2 (by rfl) ⟨1143393, by rfl⟩ : syracuseStep 3049049 = 2286787) B2286787
theorem B6858371 : Blo 1805604 6858371 := bstep (se 1 (by rfl) ⟨5143778, by rfl⟩ : syracuseStep 6858371 = 10287557) B10287557
theorem B4064921 : Blo 1805604 4064921 := bstep (se 2 (by rfl) ⟨1524345, by rfl⟩ : syracuseStep 4064921 = 3048691) B3048691
theorem B4572875 : Blo 1805604 4572875 := bstep (se 1 (by rfl) ⟨3429656, by rfl⟩ : syracuseStep 4572875 = 6859313) B6859313
theorem B3049177 : Blo 1805604 3049177 := bstep (se 2 (by rfl) ⟨1143441, by rfl⟩ : syracuseStep 3049177 = 2286883) B2286883
theorem B4065011 : Blo 1805604 4065011 := bstep (se 1 (by rfl) ⟨3048758, by rfl⟩ : syracuseStep 4065011 = 6097517) B6097517
theorem B2033419 : Blo 1805604 2033419 := bstep (se 1 (by rfl) ⟨1525064, by rfl⟩ : syracuseStep 2033419 = 3050129) B3050129
theorem B4065047 : Blo 1805604 4065047 := bstep (se 1 (by rfl) ⟨3048785, by rfl⟩ : syracuseStep 4065047 = 6097571) B6097571
theorem B2287435 : Blo 1805604 2287435 := bstep (se 1 (by rfl) ⟨1715576, by rfl⟩ : syracuseStep 2287435 = 3431153) B3431153
theorem B2033527 : Blo 1805604 2033527 := bstep (se 1 (by rfl) ⟨1525145, by rfl⟩ : syracuseStep 2033527 = 3050291) B3050291
theorem B21981107 : Blo 1805604 21981107 := bstep (se 1 (by rfl) ⟨16485830, by rfl⟩ : syracuseStep 21981107 = 32971661) B32971661
theorem B4065227 : Blo 1805604 4065227 := bstep (se 1 (by rfl) ⟨3048920, by rfl⟩ : syracuseStep 4065227 = 6097841) B6097841
theorem B13715405 : Blo 1805604 13715405 := bstep (se 3 (by rfl) ⟨2571638, by rfl⟩ : syracuseStep 13715405 = 5143277) B5143277
theorem B4065281 : Blo 1805604 4065281 := bstep (se 2 (by rfl) ⟨1524480, by rfl⟩ : syracuseStep 4065281 = 3048961) B3048961
theorem B7718915 : Blo 1805604 7718915 := bstep (se 1 (by rfl) ⟨5789186, by rfl⟩ : syracuseStep 7718915 = 11578373) B11578373
theorem B6858827 : Blo 1805604 6858827 := bstep (se 1 (by rfl) ⟨5144120, by rfl⟩ : syracuseStep 6858827 = 10288241) B10288241
theorem B2287703 : Blo 1805604 2287703 := bstep (se 1 (by rfl) ⟨1715777, by rfl⟩ : syracuseStep 2287703 = 3431555) B3431555
theorem B9144413 : Blo 1805604 9144413 := bstep (se 3 (by rfl) ⟨1714577, by rfl⟩ : syracuseStep 9144413 = 3429155) B3429155
theorem B4065497 : Blo 1805604 4065497 := bstep (se 2 (by rfl) ⟨1524561, by rfl⟩ : syracuseStep 4065497 = 3049123) B3049123
theorem B6859025 : Blo 1805604 6859025 := bstep (se 2 (by rfl) ⟨2572134, by rfl⟩ : syracuseStep 6859025 = 5144269) B5144269
theorem B3049751 : Blo 1805604 3049751 := bstep (se 1 (by rfl) ⟨2287313, by rfl⟩ : syracuseStep 3049751 = 4574627) B4574627
theorem B4065587 : Blo 1805604 4065587 := bstep (se 1 (by rfl) ⟨3049190, by rfl⟩ : syracuseStep 4065587 = 6098381) B6098381
theorem B5785931 : Blo 1805604 5785931 := bstep (se 1 (by rfl) ⟨4339448, by rfl⟩ : syracuseStep 5785931 = 8678897) B8678897
theorem B4065623 : Blo 1805604 4065623 := bstep (se 1 (by rfl) ⟨3049217, by rfl⟩ : syracuseStep 4065623 = 6098435) B6098435
theorem B5867927 : Blo 1805604 5867927 := bstep (se 1 (by rfl) ⟨4400945, by rfl⟩ : syracuseStep 5867927 = 8801891) B8801891
theorem B4884887 : Blo 1805604 4884887 := bstep (se 1 (by rfl) ⟨3663665, by rfl⟩ : syracuseStep 4884887 = 7327331) B7327331
theorem B3049879 : Blo 1805604 3049879 := bstep (se 1 (by rfl) ⟨2287409, by rfl⟩ : syracuseStep 3049879 = 4574819) B4574819
theorem B13715891 : Blo 1805604 13715891 := bstep (se 1 (by rfl) ⟨10286918, by rfl⟩ : syracuseStep 13715891 = 20573837) B20573837
theorem B5147059 : Blo 1805604 5147059 := bstep (se 1 (by rfl) ⟨3860294, by rfl⟩ : syracuseStep 5147059 = 7720589) B7720589
theorem B6097355 : Blo 1805604 6097355 := bstep (se 1 (by rfl) ⟨4573016, by rfl⟩ : syracuseStep 6097355 = 9146033) B9146033
theorem B4065803 : Blo 1805604 4065803 := bstep (se 1 (by rfl) ⟨3049352, by rfl⟩ : syracuseStep 4065803 = 6098705) B6098705
theorem B11569709 : Blo 1805604 11569709 := bstep (se 3 (by rfl) ⟨2169320, by rfl⟩ : syracuseStep 11569709 = 4338641) B4338641
theorem B4065857 : Blo 1805604 4065857 := bstep (se 2 (by rfl) ⟨1524696, by rfl⟩ : syracuseStep 4065857 = 3049393) B3049393
theorem B6949451 : Blo 1805604 6949451 := bstep (se 1 (by rfl) ⟨5212088, by rfl⟩ : syracuseStep 6949451 = 10424177) B10424177
theorem B4573847 : Blo 1805604 4573847 := bstep (se 1 (by rfl) ⟨3430385, by rfl⟩ : syracuseStep 4573847 = 6860771) B6860771
theorem B6097625 : Blo 1805604 6097625 := bstep (se 2 (by rfl) ⟨2286609, by rfl⟩ : syracuseStep 6097625 = 4573219) B4573219
theorem B4401881 : Blo 1805604 4401881 := bstep (se 2 (by rfl) ⟨1650705, by rfl⟩ : syracuseStep 4401881 = 3301411) B3301411
theorem B4066073 : Blo 1805604 4066073 := bstep (se 2 (by rfl) ⟨1524777, by rfl⟩ : syracuseStep 4066073 = 3049555) B3049555
theorem B4066163 : Blo 1805604 4066163 := bstep (se 1 (by rfl) ⟨3049622, by rfl⟩ : syracuseStep 4066163 = 6099245) B6099245
theorem B4066199 : Blo 1805604 4066199 := bstep (se 1 (by rfl) ⟨3049649, by rfl⟩ : syracuseStep 4066199 = 6099299) B6099299
theorem B7048139 : Blo 1805604 7048139 := bstep (se 1 (by rfl) ⟨5286104, by rfl⟩ : syracuseStep 7048139 = 10572209) B10572209
theorem B6859799 : Blo 1805604 6859799 := bstep (se 1 (by rfl) ⟨5144849, by rfl⟩ : syracuseStep 6859799 = 10289699) B10289699
theorem B4066379 : Blo 1805604 4066379 := bstep (se 1 (by rfl) ⟨3049784, by rfl⟩ : syracuseStep 4066379 = 6099569) B6099569
theorem B4066433 : Blo 1805604 4066433 := bstep (se 2 (by rfl) ⟨1524912, by rfl⟩ : syracuseStep 4066433 = 3049825) B3049825
theorem B6859997 : Blo 1805604 6859997 := bstep (se 3 (by rfl) ⟨1286249, by rfl⟩ : syracuseStep 6859997 = 2572499) B2572499
theorem B1805611 : Blo 1805604 1805611 := bstep (se 1 (by rfl) ⟨1354208, by rfl⟩ : syracuseStep 1805611 = 2708417) B2708417
theorem B4574515 : Blo 1805604 4574515 := bstep (se 1 (by rfl) ⟨3430886, by rfl⟩ : syracuseStep 4574515 = 6861773) B6861773
theorem B1805623 : Blo 1805604 1805623 := bstep (se 1 (by rfl) ⟨1354217, by rfl⟩ : syracuseStep 1805623 = 2708435) B2708435
theorem B1805643 : Blo 1805604 1805643 := bstep (se 1 (by rfl) ⟨1354232, by rfl⟩ : syracuseStep 1805643 = 2708465) B2708465
theorem B1805655 : Blo 1805604 1805655 := bstep (se 1 (by rfl) ⟨1354241, by rfl⟩ : syracuseStep 1805655 = 2708483) B2708483
theorem B4066649 : Blo 1805604 4066649 := bstep (se 2 (by rfl) ⟨1524993, by rfl⟩ : syracuseStep 4066649 = 3049987) B3049987
theorem B5213533 : Blo 1805604 5213533 := bstep (se 3 (by rfl) ⟨977537, by rfl⟩ : syracuseStep 5213533 = 1955075) B1955075
theorem B1805675 : Blo 1805604 1805675 := bstep (se 1 (by rfl) ⟨1354256, by rfl⟩ : syracuseStep 1805675 = 2708513) B2708513
theorem B1805687 : Blo 1805604 1805687 := bstep (se 1 (by rfl) ⟨1354265, by rfl⟩ : syracuseStep 1805687 = 2708531) B2708531
theorem B1928567 : Blo 1805604 1928567 := bstep (se 1 (by rfl) ⟨1446425, by rfl⟩ : syracuseStep 1928567 = 2892851) B2892851
theorem B1805707 : Blo 1805604 1805707 := bstep (se 1 (by rfl) ⟨1354280, by rfl⟩ : syracuseStep 1805707 = 2708561) B2708561
theorem B3911051 : Blo 1805604 3911051 := bstep (se 1 (by rfl) ⟨2933288, by rfl⟩ : syracuseStep 3911051 = 5866577) B5866577
theorem B1805719 : Blo 1805604 1805719 := bstep (se 1 (by rfl) ⟨1354289, by rfl⟩ : syracuseStep 1805719 = 2708579) B2708579
theorem B6598039 : Blo 1805604 6598039 := bstep (se 1 (by rfl) ⟨4948529, by rfl⟩ : syracuseStep 6598039 = 9897059) B9897059
theorem B3132823 : Blo 1805604 3132823 := bstep (se 1 (by rfl) ⟨2349617, by rfl⟩ : syracuseStep 3132823 = 4699235) B4699235
theorem B6098327 : Blo 1805604 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B1805739 : Blo 1805604 1805739 := bstep (se 1 (by rfl) ⟨1354304, by rfl⟩ : syracuseStep 1805739 = 2708609) B2708609
theorem B6180275 : Blo 1805604 6180275 := bstep (se 1 (by rfl) ⟨4635206, by rfl⟩ : syracuseStep 6180275 = 9270413) B9270413
theorem B4066739 : Blo 1805604 4066739 := bstep (se 1 (by rfl) ⟨3050054, by rfl⟩ : syracuseStep 4066739 = 6100109) B6100109
theorem B1805751 : Blo 1805604 1805751 := bstep (se 1 (by rfl) ⟨1354313, by rfl⟩ : syracuseStep 1805751 = 2708627) B2708627
theorem B7327169 : Blo 1805604 7327169 := bstep (se 2 (by rfl) ⟨2747688, by rfl⟩ : syracuseStep 7327169 = 5495377) B5495377
theorem B4574657 : Blo 1805604 4574657 := bstep (se 2 (by rfl) ⟨1715496, by rfl⟩ : syracuseStep 4574657 = 3430993) B3430993
theorem B1805771 : Blo 1805604 1805771 := bstep (se 1 (by rfl) ⟨1354328, by rfl⟩ : syracuseStep 1805771 = 2708657) B2708657
theorem B1805783 : Blo 1805604 1805783 := bstep (se 1 (by rfl) ⟨1354337, by rfl⟩ : syracuseStep 1805783 = 2708675) B2708675
theorem B4066775 : Blo 1805604 4066775 := bstep (se 1 (by rfl) ⟨3050081, by rfl⟩ : syracuseStep 4066775 = 6100163) B6100163
theorem B1805803 : Blo 1805604 1805803 := bstep (se 1 (by rfl) ⟨1354352, by rfl⟩ : syracuseStep 1805803 = 2708705) B2708705
theorem B1805815 : Blo 1805604 1805815 := bstep (se 1 (by rfl) ⟨1354361, by rfl⟩ : syracuseStep 1805815 = 2708723) B2708723
theorem B1928695 : Blo 1805604 1928695 := bstep (se 1 (by rfl) ⟨1446521, by rfl⟩ : syracuseStep 1928695 = 2893043) B2893043
theorem B1805835 : Blo 1805604 1805835 := bstep (se 1 (by rfl) ⟨1354376, by rfl⟩ : syracuseStep 1805835 = 2708753) B2708753
theorem B1805847 : Blo 1805604 1805847 := bstep (se 1 (by rfl) ⟨1354385, by rfl⟩ : syracuseStep 1805847 = 2708771) B2708771
theorem B1805867 : Blo 1805604 1805867 := bstep (se 1 (by rfl) ⟨1354400, by rfl⟩ : syracuseStep 1805867 = 2708801) B2708801
theorem B1805879 : Blo 1805604 1805879 := bstep (se 1 (by rfl) ⟨1354409, by rfl⟩ : syracuseStep 1805879 = 2708819) B2708819
theorem B1805899 : Blo 1805604 1805899 := bstep (se 1 (by rfl) ⟨1354424, by rfl⟩ : syracuseStep 1805899 = 2708849) B2708849
theorem B1805911 : Blo 1805604 1805911 := bstep (se 1 (by rfl) ⟨1354433, by rfl⟩ : syracuseStep 1805911 = 2708867) B2708867
theorem B1805931 : Blo 1805604 1805931 := bstep (se 1 (by rfl) ⟨1354448, by rfl⟩ : syracuseStep 1805931 = 2708897) B2708897
theorem B1805943 : Blo 1805604 1805943 := bstep (se 1 (by rfl) ⟨1354457, by rfl⟩ : syracuseStep 1805943 = 2708915) B2708915
theorem B1805963 : Blo 1805604 1805963 := bstep (se 1 (by rfl) ⟨1354472, by rfl⟩ : syracuseStep 1805963 = 2708945) B2708945
theorem B4066955 : Blo 1805604 4066955 := bstep (se 1 (by rfl) ⟨3050216, by rfl⟩ : syracuseStep 4066955 = 6100433) B6100433
theorem B1805975 : Blo 1805604 1805975 := bstep (se 1 (by rfl) ⟨1354481, by rfl⟩ : syracuseStep 1805975 = 2708963) B2708963
theorem B1805995 : Blo 1805604 1805995 := bstep (se 1 (by rfl) ⟨1354496, by rfl⟩ : syracuseStep 1805995 = 2708993) B2708993
theorem B1806007 : Blo 1805604 1806007 := bstep (se 1 (by rfl) ⟨1354505, by rfl⟩ : syracuseStep 1806007 = 2709011) B2709011
theorem B4067009 : Blo 1805604 4067009 := bstep (se 2 (by rfl) ⟨1525128, by rfl⟩ : syracuseStep 4067009 = 3050257) B3050257
theorem B1806027 : Blo 1805604 1806027 := bstep (se 1 (by rfl) ⟨1354520, by rfl⟩ : syracuseStep 1806027 = 2709041) B2709041
theorem B1806039 : Blo 1805604 1806039 := bstep (se 1 (by rfl) ⟨1354529, by rfl⟩ : syracuseStep 1806039 = 2709059) B2709059
theorem B1806059 : Blo 1805604 1806059 := bstep (se 1 (by rfl) ⟨1354544, by rfl⟩ : syracuseStep 1806059 = 2709089) B2709089
theorem B3256051 : Blo 1805604 3256051 := bstep (se 1 (by rfl) ⟨2442038, by rfl⟩ : syracuseStep 3256051 = 4884077) B4884077
theorem B1806071 : Blo 1805604 1806071 := bstep (se 1 (by rfl) ⟨1354553, by rfl⟩ : syracuseStep 1806071 = 2709107) B2709107
theorem B1806091 : Blo 1805604 1806091 := bstep (se 1 (by rfl) ⟨1354568, by rfl⟩ : syracuseStep 1806091 = 2709137) B2709137
theorem B1806103 : Blo 1805604 1806103 := bstep (se 1 (by rfl) ⟨1354577, by rfl⟩ : syracuseStep 1806103 = 2709155) B2709155
theorem B1806123 : Blo 1805604 1806123 := bstep (se 1 (by rfl) ⟨1354592, by rfl⟩ : syracuseStep 1806123 = 2709185) B2709185
theorem B1806135 : Blo 1805604 1806135 := bstep (se 1 (by rfl) ⟨1354601, by rfl⟩ : syracuseStep 1806135 = 2709203) B2709203
theorem B3477313 : Blo 1805604 3477313 := bstep (se 2 (by rfl) ⟨1303992, by rfl⟩ : syracuseStep 3477313 = 2607985) B2607985
theorem B1806155 : Blo 1805604 1806155 := bstep (se 1 (by rfl) ⟨1354616, by rfl⟩ : syracuseStep 1806155 = 2709233) B2709233
theorem B3428183 : Blo 1805604 3428183 := bstep (se 1 (by rfl) ⟨2571137, by rfl⟩ : syracuseStep 3428183 = 5142275) B5142275
theorem B1806167 : Blo 1805604 1806167 := bstep (se 1 (by rfl) ⟨1354625, by rfl⟩ : syracuseStep 1806167 = 2709251) B2709251
theorem B10284893 : Blo 1805604 10284893 := bstep (se 3 (by rfl) ⟨1928417, by rfl⟩ : syracuseStep 10284893 = 3856835) B3856835
theorem B41783141 : Blo 1805604 41783141 := bstep (se 4 (by rfl) ⟨3917169, by rfl⟩ : syracuseStep 41783141 = 7834339) B7834339
theorem B13717349 : Blo 1805604 13717349 := bstep (se 4 (by rfl) ⟨1286001, by rfl⟩ : syracuseStep 13717349 = 2572003) B2572003
theorem B1806187 : Blo 1805604 1806187 := bstep (se 1 (by rfl) ⟨1354640, by rfl⟩ : syracuseStep 1806187 = 2709281) B2709281
theorem B1806199 : Blo 1805604 1806199 := bstep (se 1 (by rfl) ⟨1354649, by rfl⟩ : syracuseStep 1806199 = 2709299) B2709299
theorem B1806219 : Blo 1805604 1806219 := bstep (se 1 (by rfl) ⟨1354664, by rfl⟩ : syracuseStep 1806219 = 2709329) B2709329
theorem B15429527 : Blo 1805604 15429527 := bstep (se 1 (by rfl) ⟨11572145, by rfl⟩ : syracuseStep 15429527 = 23144291) B23144291
theorem B1806231 : Blo 1805604 1806231 := bstep (se 1 (by rfl) ⟨1354673, by rfl⟩ : syracuseStep 1806231 = 2709347) B2709347
theorem B1806251 : Blo 1805604 1806251 := bstep (se 1 (by rfl) ⟨1354688, by rfl⟩ : syracuseStep 1806251 = 2709377) B2709377
theorem B6098867 : Blo 1805604 6098867 := bstep (se 1 (by rfl) ⟨4574150, by rfl⟩ : syracuseStep 6098867 = 9148301) B9148301
theorem B1806263 : Blo 1805604 1806263 := bstep (se 1 (by rfl) ⟨1354697, by rfl⟩ : syracuseStep 1806263 = 2709395) B2709395
theorem B1806283 : Blo 1805604 1806283 := bstep (se 1 (by rfl) ⟨1354712, by rfl⟩ : syracuseStep 1806283 = 2709425) B2709425
theorem B1806295 : Blo 1805604 1806295 := bstep (se 1 (by rfl) ⟨1354721, by rfl⟩ : syracuseStep 1806295 = 2709443) B2709443
theorem B7712729 : Blo 1805604 7712729 := bstep (se 2 (by rfl) ⟨2892273, by rfl⟩ : syracuseStep 7712729 = 5784547) B5784547
theorem B1806315 : Blo 1805604 1806315 := bstep (se 1 (by rfl) ⟨1354736, by rfl⟩ : syracuseStep 1806315 = 2709473) B2709473
theorem B1806327 : Blo 1805604 1806327 := bstep (se 1 (by rfl) ⟨1354745, by rfl⟩ : syracuseStep 1806327 = 2709491) B2709491
theorem B1806347 : Blo 1805604 1806347 := bstep (se 1 (by rfl) ⟨1354760, by rfl⟩ : syracuseStep 1806347 = 2709521) B2709521
theorem B1806359 : Blo 1805604 1806359 := bstep (se 1 (by rfl) ⟨1354769, by rfl⟩ : syracuseStep 1806359 = 2709539) B2709539
theorem B3256345 : Blo 1805604 3256345 := bstep (se 2 (by rfl) ⟨1221129, by rfl⟩ : syracuseStep 3256345 = 2442259) B2442259
theorem B1806379 : Blo 1805604 1806379 := bstep (se 1 (by rfl) ⟨1354784, by rfl⟩ : syracuseStep 1806379 = 2709569) B2709569
theorem B1929259 : Blo 1805604 1929259 := bstep (se 1 (by rfl) ⟨1446944, by rfl⟩ : syracuseStep 1929259 = 2893889) B2893889
theorem B1806391 : Blo 1805604 1806391 := bstep (se 1 (by rfl) ⟨1354793, by rfl⟩ : syracuseStep 1806391 = 2709587) B2709587
theorem B5787713 : Blo 1805604 5787713 := bstep (se 2 (by rfl) ⟨2170392, by rfl⟩ : syracuseStep 5787713 = 4340785) B4340785
theorem B1806411 : Blo 1805604 1806411 := bstep (se 1 (by rfl) ⟨1354808, by rfl⟩ : syracuseStep 1806411 = 2709617) B2709617
theorem B1806423 : Blo 1805604 1806423 := bstep (se 1 (by rfl) ⟨1354817, by rfl⟩ : syracuseStep 1806423 = 2709635) B2709635
theorem B1806443 : Blo 1805604 1806443 := bstep (se 1 (by rfl) ⟨1354832, by rfl⟩ : syracuseStep 1806443 = 2709665) B2709665
theorem B1806455 : Blo 1805604 1806455 := bstep (se 1 (by rfl) ⟨1354841, by rfl⟩ : syracuseStep 1806455 = 2709683) B2709683
theorem B1806475 : Blo 1805604 1806475 := bstep (se 1 (by rfl) ⟨1354856, by rfl⟩ : syracuseStep 1806475 = 2709713) B2709713
theorem B1806487 : Blo 1805604 1806487 := bstep (se 1 (by rfl) ⟨1354865, by rfl⟩ : syracuseStep 1806487 = 2709731) B2709731
theorem B9146519 : Blo 1805604 9146519 := bstep (se 1 (by rfl) ⟨6859889, by rfl⟩ : syracuseStep 9146519 = 13719779) B13719779
theorem B1806507 : Blo 1805604 1806507 := bstep (se 1 (by rfl) ⟨1354880, by rfl⟩ : syracuseStep 1806507 = 2709761) B2709761
theorem B1806519 : Blo 1805604 1806519 := bstep (se 1 (by rfl) ⟨1354889, by rfl⟩ : syracuseStep 1806519 = 2709779) B2709779
theorem B6099137 : Blo 1805604 6099137 := bstep (se 2 (by rfl) ⟨2287176, by rfl⟩ : syracuseStep 6099137 = 4574353) B4574353
theorem B1806539 : Blo 1805604 1806539 := bstep (se 1 (by rfl) ⟨1354904, by rfl⟩ : syracuseStep 1806539 = 2709809) B2709809
theorem B1806551 : Blo 1805604 1806551 := bstep (se 1 (by rfl) ⟨1354913, by rfl⟩ : syracuseStep 1806551 = 2709827) B2709827
theorem B1806571 : Blo 1805604 1806571 := bstep (se 1 (by rfl) ⟨1354928, by rfl⟩ : syracuseStep 1806571 = 2709857) B2709857
theorem B1806583 : Blo 1805604 1806583 := bstep (se 1 (by rfl) ⟨1354937, by rfl⟩ : syracuseStep 1806583 = 2709875) B2709875
theorem B1806603 : Blo 1805604 1806603 := bstep (se 1 (by rfl) ⟨1354952, by rfl⟩ : syracuseStep 1806603 = 2709905) B2709905
theorem B1806615 : Blo 1805604 1806615 := bstep (se 1 (by rfl) ⟨1354961, by rfl⟩ : syracuseStep 1806615 = 2709923) B2709923
theorem B1806635 : Blo 1805604 1806635 := bstep (se 1 (by rfl) ⟨1354976, by rfl⟩ : syracuseStep 1806635 = 2709953) B2709953
theorem B1929515 : Blo 1805604 1929515 := bstep (se 1 (by rfl) ⟨1447136, by rfl⟩ : syracuseStep 1929515 = 2894273) B2894273
theorem B12366125 : Blo 1805604 12366125 := bstep (se 3 (by rfl) ⟨2318648, by rfl⟩ : syracuseStep 12366125 = 4637297) B4637297
theorem B1806647 : Blo 1805604 1806647 := bstep (se 1 (by rfl) ⟨1354985, by rfl⟩ : syracuseStep 1806647 = 2709971) B2709971
theorem B13717835 : Blo 1805604 13717835 := bstep (se 1 (by rfl) ⟨10288376, by rfl⟩ : syracuseStep 13717835 = 20576753) B20576753
theorem B1806667 : Blo 1805604 1806667 := bstep (se 1 (by rfl) ⟨1355000, by rfl⟩ : syracuseStep 1806667 = 2710001) B2710001
theorem B1806679 : Blo 1805604 1806679 := bstep (se 1 (by rfl) ⟨1355009, by rfl⟩ : syracuseStep 1806679 = 2710019) B2710019
theorem B1806699 : Blo 1805604 1806699 := bstep (se 1 (by rfl) ⟨1355024, by rfl⟩ : syracuseStep 1806699 = 2710049) B2710049
theorem B3428723 : Blo 1805604 3428723 := bstep (se 1 (by rfl) ⟨2571542, by rfl⟩ : syracuseStep 3428723 = 5143085) B5143085
theorem B1806711 : Blo 1805604 1806711 := bstep (se 1 (by rfl) ⟨1355033, by rfl⟩ : syracuseStep 1806711 = 2710067) B2710067
theorem B3256691 : Blo 1805604 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B3912065 : Blo 1805604 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B1806731 : Blo 1805604 1806731 := bstep (se 1 (by rfl) ⟨1355048, by rfl⟩ : syracuseStep 1806731 = 2710097) B2710097
theorem B1806743 : Blo 1805604 1806743 := bstep (se 1 (by rfl) ⟨1355057, by rfl⟩ : syracuseStep 1806743 = 2710115) B2710115
theorem B1806763 : Blo 1805604 1806763 := bstep (se 1 (by rfl) ⟨1355072, by rfl⟩ : syracuseStep 1806763 = 2710145) B2710145
theorem B1806775 : Blo 1805604 1806775 := bstep (se 1 (by rfl) ⟨1355081, by rfl⟩ : syracuseStep 1806775 = 2710163) B2710163
theorem B1806795 : Blo 1805604 1806795 := bstep (se 1 (by rfl) ⟨1355096, by rfl⟩ : syracuseStep 1806795 = 2710193) B2710193
theorem B1806807 : Blo 1805604 1806807 := bstep (se 1 (by rfl) ⟨1355105, by rfl⟩ : syracuseStep 1806807 = 2710211) B2710211
theorem B1806827 : Blo 1805604 1806827 := bstep (se 1 (by rfl) ⟨1355120, by rfl⟩ : syracuseStep 1806827 = 2710241) B2710241
theorem B1806839 : Blo 1805604 1806839 := bstep (se 1 (by rfl) ⟨1355129, by rfl⟩ : syracuseStep 1806839 = 2710259) B2710259
theorem B1806859 : Blo 1805604 1806859 := bstep (se 1 (by rfl) ⟨1355144, by rfl⟩ : syracuseStep 1806859 = 2710289) B2710289
theorem B1806871 : Blo 1805604 1806871 := bstep (se 1 (by rfl) ⟨1355153, by rfl⟩ : syracuseStep 1806871 = 2710307) B2710307
theorem B1806891 : Blo 1805604 1806891 := bstep (se 1 (by rfl) ⟨1355168, by rfl⟩ : syracuseStep 1806891 = 2710337) B2710337
theorem B1806903 : Blo 1805604 1806903 := bstep (se 1 (by rfl) ⟨1355177, by rfl⟩ : syracuseStep 1806903 = 2710355) B2710355
theorem B10285643 : Blo 1805604 10285643 := bstep (se 1 (by rfl) ⟨7714232, by rfl⟩ : syracuseStep 10285643 = 15428465) B15428465
theorem B1806923 : Blo 1805604 1806923 := bstep (se 1 (by rfl) ⟨1355192, by rfl⟩ : syracuseStep 1806923 = 2710385) B2710385
theorem B1806935 : Blo 1805604 1806935 := bstep (se 1 (by rfl) ⟨1355201, by rfl⟩ : syracuseStep 1806935 = 2710403) B2710403
theorem B1806955 : Blo 1805604 1806955 := bstep (se 1 (by rfl) ⟨1355216, by rfl⟩ : syracuseStep 1806955 = 2710433) B2710433
theorem B1806967 : Blo 1805604 1806967 := bstep (se 1 (by rfl) ⟨1355225, by rfl⟩ : syracuseStep 1806967 = 2710451) B2710451
theorem B1806987 : Blo 1805604 1806987 := bstep (se 1 (by rfl) ⟨1355240, by rfl⟩ : syracuseStep 1806987 = 2710481) B2710481
theorem B1806999 : Blo 1805604 1806999 := bstep (se 1 (by rfl) ⟨1355249, by rfl⟩ : syracuseStep 1806999 = 2710499) B2710499
theorem B1807019 : Blo 1805604 1807019 := bstep (se 1 (by rfl) ⟨1355264, by rfl⟩ : syracuseStep 1807019 = 2710529) B2710529
theorem B1807031 : Blo 1805604 1807031 := bstep (se 1 (by rfl) ⟨1355273, by rfl⟩ : syracuseStep 1807031 = 2710547) B2710547
theorem B1807051 : Blo 1805604 1807051 := bstep (se 1 (by rfl) ⟨1355288, by rfl⟩ : syracuseStep 1807051 = 2710577) B2710577
theorem B18551501 : Blo 1805604 18551501 := bstep (se 3 (by rfl) ⟨3478406, by rfl⟩ : syracuseStep 18551501 = 6956813) B6956813
theorem B1807063 : Blo 1805604 1807063 := bstep (se 1 (by rfl) ⟨1355297, by rfl⟩ : syracuseStep 1807063 = 2710595) B2710595
theorem B6099677 : Blo 1805604 6099677 := bstep (se 3 (by rfl) ⟨1143689, by rfl⟩ : syracuseStep 6099677 = 2287379) B2287379
theorem B105607907 : Blo 1805604 105607907 := bstep (se 1 (by rfl) ⟨79205930, by rfl⟩ : syracuseStep 105607907 = 158411861) B158411861
theorem B1807083 : Blo 1805604 1807083 := bstep (se 1 (by rfl) ⟨1355312, by rfl⟩ : syracuseStep 1807083 = 2710625) B2710625
theorem B1807095 : Blo 1805604 1807095 := bstep (se 1 (by rfl) ⟨1355321, by rfl⟩ : syracuseStep 1807095 = 2710643) B2710643
theorem B1807115 : Blo 1805604 1807115 := bstep (se 1 (by rfl) ⟨1355336, by rfl⟩ : syracuseStep 1807115 = 2710673) B2710673
theorem B1807127 : Blo 1805604 1807127 := bstep (se 1 (by rfl) ⟨1355345, by rfl⟩ : syracuseStep 1807127 = 2710691) B2710691
theorem B1807147 : Blo 1805604 1807147 := bstep (se 1 (by rfl) ⟨1355360, by rfl⟩ : syracuseStep 1807147 = 2710721) B2710721
theorem B1807159 : Blo 1805604 1807159 := bstep (se 1 (by rfl) ⟨1355369, by rfl⟩ : syracuseStep 1807159 = 2710739) B2710739
theorem B1807179 : Blo 1805604 1807179 := bstep (se 1 (by rfl) ⟨1355384, by rfl⟩ : syracuseStep 1807179 = 2710769) B2710769
theorem B1807191 : Blo 1805604 1807191 := bstep (se 1 (by rfl) ⟨1355393, by rfl⟩ : syracuseStep 1807191 = 2710787) B2710787
theorem B3429209 : Blo 1805604 3429209 := bstep (se 2 (by rfl) ⟨1285953, by rfl⟩ : syracuseStep 3429209 = 2571907) B2571907
theorem B1807211 : Blo 1805604 1807211 := bstep (se 1 (by rfl) ⟨1355408, by rfl⟩ : syracuseStep 1807211 = 2710817) B2710817
theorem B1807223 : Blo 1805604 1807223 := bstep (se 1 (by rfl) ⟨1355417, by rfl⟩ : syracuseStep 1807223 = 2710835) B2710835
theorem B1807243 : Blo 1805604 1807243 := bstep (se 1 (by rfl) ⟨1355432, by rfl⟩ : syracuseStep 1807243 = 2710865) B2710865
theorem B1807255 : Blo 1805604 1807255 := bstep (se 1 (by rfl) ⟨1355441, by rfl⟩ : syracuseStep 1807255 = 2710883) B2710883
theorem B1807275 : Blo 1805604 1807275 := bstep (se 1 (by rfl) ⟨1355456, by rfl⟩ : syracuseStep 1807275 = 2710913) B2710913
theorem B1807287 : Blo 1805604 1807287 := bstep (se 1 (by rfl) ⟨1355465, by rfl⟩ : syracuseStep 1807287 = 2710931) B2710931
theorem B1807307 : Blo 1805604 1807307 := bstep (se 1 (by rfl) ⟨1355480, by rfl⟩ : syracuseStep 1807307 = 2710961) B2710961
theorem B1807319 : Blo 1805604 1807319 := bstep (se 1 (by rfl) ⟨1355489, by rfl⟩ : syracuseStep 1807319 = 2710979) B2710979
theorem B2708441 : Blo 1805604 2708441 := bstep (se 2 (by rfl) ⟨1015665, by rfl⟩ : syracuseStep 2708441 = 2031331) B2031331
theorem B1807339 : Blo 1805604 1807339 := bstep (se 1 (by rfl) ⟨1355504, by rfl⟩ : syracuseStep 1807339 = 2711009) B2711009
theorem B1807351 : Blo 1805604 1807351 := bstep (se 1 (by rfl) ⟨1355513, by rfl⟩ : syracuseStep 1807351 = 2711027) B2711027
theorem B1807371 : Blo 1805604 1807371 := bstep (se 1 (by rfl) ⟨1355528, by rfl⟩ : syracuseStep 1807371 = 2711057) B2711057
theorem B1807383 : Blo 1805604 1807383 := bstep (se 1 (by rfl) ⟨1355537, by rfl⟩ : syracuseStep 1807383 = 2711075) B2711075
theorem B1807403 : Blo 1805604 1807403 := bstep (se 1 (by rfl) ⟨1355552, by rfl⟩ : syracuseStep 1807403 = 2711105) B2711105
theorem B1807415 : Blo 1805604 1807415 := bstep (se 1 (by rfl) ⟨1355561, by rfl⟩ : syracuseStep 1807415 = 2711123) B2711123
theorem B2708555 : Blo 1805604 2708555 := bstep (se 1 (by rfl) ⟨2031416, by rfl⟩ : syracuseStep 2708555 = 4062833) B4062833
theorem B15438923 : Blo 1805604 15438923 := bstep (se 1 (by rfl) ⟨11579192, by rfl⟩ : syracuseStep 15438923 = 23158385) B23158385
theorem B1807435 : Blo 1805604 1807435 := bstep (se 1 (by rfl) ⟨1355576, by rfl⟩ : syracuseStep 1807435 = 2711153) B2711153
theorem B2708567 : Blo 1805604 2708567 := bstep (se 1 (by rfl) ⟨2031425, by rfl⟩ : syracuseStep 2708567 = 4062851) B4062851
theorem B1807447 : Blo 1805604 1807447 := bstep (se 1 (by rfl) ⟨1355585, by rfl⟩ : syracuseStep 1807447 = 2711171) B2711171
theorem B1807467 : Blo 1805604 1807467 := bstep (se 1 (by rfl) ⟨1355600, by rfl⟩ : syracuseStep 1807467 = 2711201) B2711201
theorem B1807479 : Blo 1805604 1807479 := bstep (se 1 (by rfl) ⟨1355609, by rfl⟩ : syracuseStep 1807479 = 2711219) B2711219
theorem B6861955 : Blo 1805604 6861955 := bstep (se 1 (by rfl) ⟨5146466, by rfl⟩ : syracuseStep 6861955 = 10292933) B10292933
theorem B1807499 : Blo 1805604 1807499 := bstep (se 1 (by rfl) ⟨1355624, by rfl⟩ : syracuseStep 1807499 = 2711249) B2711249
theorem B1807511 : Blo 1805604 1807511 := bstep (se 1 (by rfl) ⟨1355633, by rfl⟩ : syracuseStep 1807511 = 2711267) B2711267
theorem B2708633 : Blo 1805604 2708633 := bstep (se 2 (by rfl) ⟨1015737, by rfl⟩ : syracuseStep 2708633 = 2031475) B2031475
theorem B1807531 : Blo 1805604 1807531 := bstep (se 1 (by rfl) ⟨1355648, by rfl⟩ : syracuseStep 1807531 = 2711297) B2711297
theorem B4175027 : Blo 1805604 4175027 := bstep (se 1 (by rfl) ⟨3131270, by rfl⟩ : syracuseStep 4175027 = 6262541) B6262541
theorem B1807543 : Blo 1805604 1807543 := bstep (se 1 (by rfl) ⟨1355657, by rfl⟩ : syracuseStep 1807543 = 2711315) B2711315
theorem B1807563 : Blo 1805604 1807563 := bstep (se 1 (by rfl) ⟨1355672, by rfl⟩ : syracuseStep 1807563 = 2711345) B2711345
theorem B1807575 : Blo 1805604 1807575 := bstep (se 1 (by rfl) ⟨1355681, by rfl⟩ : syracuseStep 1807575 = 2711363) B2711363
theorem B5018845 : Blo 1805604 5018845 := bstep (se 3 (by rfl) ⟨941033, by rfl⟩ : syracuseStep 5018845 = 1882067) B1882067
theorem B1807595 : Blo 1805604 1807595 := bstep (se 1 (by rfl) ⟨1355696, by rfl⟩ : syracuseStep 1807595 = 2711393) B2711393
theorem B2708747 : Blo 1805604 2708747 := bstep (se 1 (by rfl) ⟨2031560, by rfl⟩ : syracuseStep 2708747 = 4063121) B4063121
theorem B2708759 : Blo 1805604 2708759 := bstep (se 1 (by rfl) ⟨2031569, by rfl⟩ : syracuseStep 2708759 = 4063139) B4063139
theorem B7329047 : Blo 1805604 7329047 := bstep (se 1 (by rfl) ⟨5496785, by rfl⟩ : syracuseStep 7329047 = 10993571) B10993571
theorem B10294573 : Blo 1805604 10294573 := bstep (se 3 (by rfl) ⟨1930232, by rfl⟩ : syracuseStep 10294573 = 3860465) B3860465
theorem B2708825 : Blo 1805604 2708825 := bstep (se 2 (by rfl) ⟨1015809, by rfl⟩ : syracuseStep 2708825 = 2031619) B2031619
theorem B5018969 : Blo 1805604 5018969 := bstep (se 2 (by rfl) ⟨1882113, by rfl⟩ : syracuseStep 5018969 = 3764227) B3764227
theorem B9770419 : Blo 1805604 9770419 := bstep (se 1 (by rfl) ⟨7327814, by rfl⟩ : syracuseStep 9770419 = 14655629) B14655629
theorem B6862259 : Blo 1805604 6862259 := bstep (se 1 (by rfl) ⟨5146694, by rfl⟩ : syracuseStep 6862259 = 10293389) B10293389
theorem B2708939 : Blo 1805604 2708939 := bstep (se 1 (by rfl) ⟨2031704, by rfl⟩ : syracuseStep 2708939 = 4063409) B4063409
theorem B2708951 : Blo 1805604 2708951 := bstep (se 1 (by rfl) ⟨2031713, by rfl⟩ : syracuseStep 2708951 = 4063427) B4063427
theorem B4232663 : Blo 1805604 4232663 := bstep (se 1 (by rfl) ⟨3174497, by rfl⟩ : syracuseStep 4232663 = 6348995) B6348995
theorem B2709017 : Blo 1805604 2709017 := bstep (se 2 (by rfl) ⟨1015881, by rfl⟩ : syracuseStep 2709017 = 2031763) B2031763
theorem B7714369 : Blo 1805604 7714369 := bstep (se 2 (by rfl) ⟨2892888, by rfl⟩ : syracuseStep 7714369 = 5785777) B5785777
theorem B2709131 : Blo 1805604 2709131 := bstep (se 1 (by rfl) ⟨2031848, by rfl⟩ : syracuseStep 2709131 = 4063697) B4063697
theorem B2709143 : Blo 1805604 2709143 := bstep (se 1 (by rfl) ⟨2031857, by rfl⟩ : syracuseStep 2709143 = 4063715) B4063715
theorem B2709209 : Blo 1805604 2709209 := bstep (se 2 (by rfl) ⟨1015953, by rfl⟩ : syracuseStep 2709209 = 2031907) B2031907
theorem B2709323 : Blo 1805604 2709323 := bstep (se 1 (by rfl) ⟨2031992, by rfl⟩ : syracuseStep 2709323 = 4063985) B4063985
theorem B2709335 : Blo 1805604 2709335 := bstep (se 1 (by rfl) ⟨2032001, by rfl⟩ : syracuseStep 2709335 = 4064003) B4064003
theorem B2709401 : Blo 1805604 2709401 := bstep (se 2 (by rfl) ⟨1016025, by rfl⟩ : syracuseStep 2709401 = 2032051) B2032051
theorem B3856331 : Blo 1805604 3856331 := bstep (se 1 (by rfl) ⟨2892248, by rfl⟩ : syracuseStep 3856331 = 5784497) B5784497
theorem B6510557 : Blo 1805604 6510557 := bstep (se 3 (by rfl) ⟨1220729, by rfl⟩ : syracuseStep 6510557 = 2441459) B2441459
theorem B4118539 : Blo 1805604 4118539 := bstep (se 1 (by rfl) ⟨3088904, by rfl⟩ : syracuseStep 4118539 = 6177809) B6177809
theorem B2709515 : Blo 1805604 2709515 := bstep (se 1 (by rfl) ⟨2032136, by rfl⟩ : syracuseStep 2709515 = 4064273) B4064273
theorem B2709527 : Blo 1805604 2709527 := bstep (se 1 (by rfl) ⟨2032145, by rfl⟩ : syracuseStep 2709527 = 4064291) B4064291
theorem B6862913 : Blo 1805604 6862913 := bstep (se 2 (by rfl) ⟨2573592, by rfl⟩ : syracuseStep 6862913 = 5147185) B5147185
theorem B2709593 : Blo 1805604 2709593 := bstep (se 2 (by rfl) ⟨1016097, by rfl⟩ : syracuseStep 2709593 = 2032195) B2032195
theorem B10287283 : Blo 1805604 10287283 := bstep (se 1 (by rfl) ⟨7715462, by rfl⟩ : syracuseStep 10287283 = 15430925) B15430925
theorem B2709707 : Blo 1805604 2709707 := bstep (se 1 (by rfl) ⟨2032280, by rfl⟩ : syracuseStep 2709707 = 4064561) B4064561
theorem B2709719 : Blo 1805604 2709719 := bstep (se 1 (by rfl) ⟨2032289, by rfl⟩ : syracuseStep 2709719 = 4064579) B4064579
theorem B3430667 : Blo 1805604 3430667 := bstep (se 1 (by rfl) ⟨2573000, by rfl⟩ : syracuseStep 3430667 = 5146001) B5146001
theorem B2709785 : Blo 1805604 2709785 := bstep (se 2 (by rfl) ⟨1016169, by rfl⟩ : syracuseStep 2709785 = 2032339) B2032339
theorem B9771329 : Blo 1805604 9771329 := bstep (se 2 (by rfl) ⟨3664248, by rfl⟩ : syracuseStep 9771329 = 7328497) B7328497
theorem B2709899 : Blo 1805604 2709899 := bstep (se 1 (by rfl) ⟨2032424, by rfl⟩ : syracuseStep 2709899 = 4064849) B4064849
theorem B2709911 : Blo 1805604 2709911 := bstep (se 1 (by rfl) ⟨2032433, by rfl⟩ : syracuseStep 2709911 = 4064867) B4064867
theorem B3430849 : Blo 1805604 3430849 := bstep (se 2 (by rfl) ⟨1286568, by rfl⟩ : syracuseStep 3430849 = 2573137) B2573137
theorem B3856843 : Blo 1805604 3856843 := bstep (se 1 (by rfl) ⟨2892632, by rfl⟩ : syracuseStep 3856843 = 5785265) B5785265
theorem B2709977 : Blo 1805604 2709977 := bstep (se 2 (by rfl) ⟨1016241, by rfl⟩ : syracuseStep 2709977 = 2032483) B2032483
theorem B2710091 : Blo 1805604 2710091 := bstep (se 1 (by rfl) ⟨2032568, by rfl⟩ : syracuseStep 2710091 = 4065137) B4065137
theorem B2710103 : Blo 1805604 2710103 := bstep (se 1 (by rfl) ⟨2032577, by rfl⟩ : syracuseStep 2710103 = 4065155) B4065155
theorem B13712003 : Blo 1805604 13712003 := bstep (se 1 (by rfl) ⟨10284002, by rfl⟩ : syracuseStep 13712003 = 20568005) B20568005
theorem B2710169 : Blo 1805604 2710169 := bstep (se 2 (by rfl) ⟨1016313, by rfl⟩ : syracuseStep 2710169 = 2032627) B2032627
theorem B10992307 : Blo 1805604 10992307 := bstep (se 1 (by rfl) ⟨8244230, by rfl⟩ : syracuseStep 10992307 = 16488461) B16488461
theorem B27810485 : Blo 1805604 27810485 := bstep (se 5 (by rfl) ⟨1303616, by rfl⟩ : syracuseStep 27810485 = 2607233) B2607233
theorem B6183641 : Blo 1805604 6183641 := bstep (se 2 (by rfl) ⟨2318865, by rfl⟩ : syracuseStep 6183641 = 4637731) B4637731
theorem B2710283 : Blo 1805604 2710283 := bstep (se 1 (by rfl) ⟨2032712, by rfl⟩ : syracuseStep 2710283 = 4065425) B4065425
theorem B2710295 : Blo 1805604 2710295 := bstep (se 1 (by rfl) ⟨2032721, by rfl⟩ : syracuseStep 2710295 = 4065443) B4065443
theorem B2710361 : Blo 1805604 2710361 := bstep (se 2 (by rfl) ⟨1016385, by rfl⟩ : syracuseStep 2710361 = 2032771) B2032771
theorem B3431297 : Blo 1805604 3431297 := bstep (se 2 (by rfl) ⟨1286736, by rfl⟩ : syracuseStep 3431297 = 2573473) B2573473
theorem B27802547 : Blo 1805604 27802547 := bstep (se 1 (by rfl) ⟨20851910, by rfl⟩ : syracuseStep 27802547 = 41703821) B41703821
theorem B6183859 : Blo 1805604 6183859 := bstep (se 1 (by rfl) ⟨4637894, by rfl⟩ : syracuseStep 6183859 = 9275789) B9275789
theorem B2784203 : Blo 1805604 2784203 := bstep (se 1 (by rfl) ⟨2088152, by rfl⟩ : syracuseStep 2784203 = 4176305) B4176305
theorem B2710475 : Blo 1805604 2710475 := bstep (se 1 (by rfl) ⟨2032856, by rfl⟩ : syracuseStep 2710475 = 4065713) B4065713
theorem B2710487 : Blo 1805604 2710487 := bstep (se 1 (by rfl) ⟨2032865, by rfl⟩ : syracuseStep 2710487 = 4065731) B4065731
theorem B7715857 : Blo 1805604 7715857 := bstep (se 2 (by rfl) ⟨2893446, by rfl⟩ : syracuseStep 7715857 = 5786893) B5786893
theorem B2710553 : Blo 1805604 2710553 := bstep (se 2 (by rfl) ⟨1016457, by rfl⟩ : syracuseStep 2710553 = 2032915) B2032915
theorem B5217331 : Blo 1805604 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B2710667 : Blo 1805604 2710667 := bstep (se 1 (by rfl) ⟨2033000, by rfl⟩ : syracuseStep 2710667 = 4066001) B4066001
theorem B2710679 : Blo 1805604 2710679 := bstep (se 1 (by rfl) ⟨2033009, by rfl⟩ : syracuseStep 2710679 = 4066019) B4066019
theorem B3857561 : Blo 1805604 3857561 := bstep (se 2 (by rfl) ⟨1446585, by rfl⟩ : syracuseStep 3857561 = 2893171) B2893171
theorem B2710745 : Blo 1805604 2710745 := bstep (se 2 (by rfl) ⟨1016529, by rfl⟩ : syracuseStep 2710745 = 2033059) B2033059
theorem B11132225 : Blo 1805604 11132225 := bstep (se 2 (by rfl) ⟨4174584, by rfl⟩ : syracuseStep 11132225 = 8349169) B8349169
theorem B2710859 : Blo 1805604 2710859 := bstep (se 1 (by rfl) ⟨2033144, by rfl⟩ : syracuseStep 2710859 = 4066289) B4066289
theorem B2710871 : Blo 1805604 2710871 := bstep (se 1 (by rfl) ⟨2033153, by rfl⟩ : syracuseStep 2710871 = 4066307) B4066307
theorem B6094169 : Blo 1805604 6094169 := bstep (se 2 (by rfl) ⟨2285313, by rfl⟩ : syracuseStep 6094169 = 4570627) B4570627
theorem B4062617 : Blo 1805604 4062617 := bstep (se 2 (by rfl) ⟨1523481, by rfl⟩ : syracuseStep 4062617 = 3046963) B3046963
theorem B2710937 : Blo 1805604 2710937 := bstep (se 2 (by rfl) ⟨1016601, by rfl⟩ : syracuseStep 2710937 = 2033203) B2033203
theorem B6856109 : Blo 1805604 6856109 := bstep (se 3 (by rfl) ⟨1285520, by rfl⟩ : syracuseStep 6856109 = 2571041) B2571041
theorem B4062707 : Blo 1805604 4062707 := bstep (se 1 (by rfl) ⟨3047030, by rfl⟩ : syracuseStep 4062707 = 6094061) B6094061
theorem B2571787 : Blo 1805604 2571787 := bstep (se 1 (by rfl) ⟨1928840, by rfl⟩ : syracuseStep 2571787 = 3857681) B3857681
theorem B2711051 : Blo 1805604 2711051 := bstep (se 1 (by rfl) ⟨2033288, by rfl⟩ : syracuseStep 2711051 = 4066577) B4066577
theorem B4062743 : Blo 1805604 4062743 := bstep (se 1 (by rfl) ⟨3047057, by rfl⟩ : syracuseStep 4062743 = 6094115) B6094115
theorem B5144087 : Blo 1805604 5144087 := bstep (se 1 (by rfl) ⟨3858065, by rfl⟩ : syracuseStep 5144087 = 7716131) B7716131
theorem B2711063 : Blo 1805604 2711063 := bstep (se 1 (by rfl) ⟨2033297, by rfl⟩ : syracuseStep 2711063 = 4066595) B4066595
theorem B15646243 : Blo 1805604 15646243 := bstep (se 1 (by rfl) ⟨11734682, by rfl⟩ : syracuseStep 15646243 = 23469365) B23469365
theorem B3857971 : Blo 1805604 3857971 := bstep (se 1 (by rfl) ⟨2893478, by rfl⟩ : syracuseStep 3857971 = 5786957) B5786957
theorem B2711129 : Blo 1805604 2711129 := bstep (se 2 (by rfl) ⟨1016673, by rfl⟩ : syracuseStep 2711129 = 2033347) B2033347
theorem B10288741 : Blo 1805604 10288741 := bstep (se 4 (by rfl) ⟨964569, by rfl⟩ : syracuseStep 10288741 = 1929139) B1929139
theorem B9150083 : Blo 1805604 9150083 := bstep (se 1 (by rfl) ⟨6862562, by rfl⟩ : syracuseStep 9150083 = 13725125) B13725125
theorem B3047051 : Blo 1805604 3047051 := bstep (se 1 (by rfl) ⟨2285288, by rfl⟩ : syracuseStep 3047051 = 4570577) B4570577
theorem B15441587 : Blo 1805604 15441587 := bstep (se 1 (by rfl) ⟨11581190, by rfl⟩ : syracuseStep 15441587 = 23162381) B23162381
theorem B4062923 : Blo 1805604 4062923 := bstep (se 1 (by rfl) ⟨3047192, by rfl⟩ : syracuseStep 4062923 = 6094385) B6094385
theorem B2711243 : Blo 1805604 2711243 := bstep (se 1 (by rfl) ⟨2033432, by rfl⟩ : syracuseStep 2711243 = 4066865) B4066865
theorem B23150285 : Blo 1805604 23150285 := bstep (se 3 (by rfl) ⟨4340678, by rfl⟩ : syracuseStep 23150285 = 8681357) B8681357
theorem B2711255 : Blo 1805604 2711255 := bstep (se 1 (by rfl) ⟨2033441, by rfl⟩ : syracuseStep 2711255 = 4066883) B4066883
theorem B4062977 : Blo 1805604 4062977 := bstep (se 2 (by rfl) ⟨1523616, by rfl⟩ : syracuseStep 4062977 = 3047233) B3047233
theorem B3047179 : Blo 1805604 3047179 := bstep (se 1 (by rfl) ⟨2285384, by rfl⟩ : syracuseStep 3047179 = 4570769) B4570769
theorem B2711321 : Blo 1805604 2711321 := bstep (se 2 (by rfl) ⟨1016745, by rfl⟩ : syracuseStep 2711321 = 2033491) B2033491
theorem B2031403 : Blo 1805604 2031403 := bstep (se 1 (by rfl) ⟨1523552, by rfl⟩ : syracuseStep 2031403 = 3047105) B3047105
theorem B4570931 : Blo 1805604 4570931 := bstep (se 1 (by rfl) ⟨3428198, by rfl⟩ : syracuseStep 4570931 = 6856397) B6856397
theorem B6512459 : Blo 1805604 6512459 := bstep (se 1 (by rfl) ⟨4884344, by rfl⟩ : syracuseStep 6512459 = 9768689) B9768689
theorem B30867317 : Blo 1805604 30867317 := bstep (se 5 (by rfl) ⟨1446905, by rfl⟩ : syracuseStep 30867317 = 2893811) B2893811
theorem B13016963 : Blo 1805604 13016963 := bstep (se 1 (by rfl) ⟨9762722, by rfl⟩ : syracuseStep 13016963 = 19525445) B19525445
theorem B2031511 : Blo 1805604 2031511 := bstep (se 1 (by rfl) ⟨1523633, by rfl⟩ : syracuseStep 2031511 = 3047267) B3047267
theorem B3047321 : Blo 1805604 3047321 := bstep (se 2 (by rfl) ⟨1142745, by rfl⟩ : syracuseStep 3047321 = 2285491) B2285491
theorem B4063193 : Blo 1805604 4063193 := bstep (se 2 (by rfl) ⟨1523697, by rfl⟩ : syracuseStep 4063193 = 3047395) B3047395
theorem B4063247 : Blo 1805604 4063247 := bstep (se 1 (by rfl) ⟨3047435, by rfl⟩ : syracuseStep 4063247 = 6094871) B6094871
theorem B4063265 : Blo 1805604 4063265 := bstep (se 2 (by rfl) ⟨1523724, by rfl⟩ : syracuseStep 4063265 = 3047449) B3047449
theorem B2572345 : Blo 1805604 2572345 := bstep (se 2 (by rfl) ⟨964629, by rfl⟩ : syracuseStep 2572345 = 1929259) B1929259
theorem B3047483 : Blo 1805604 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B150388811 : Blo 1805604 150388811 := bstep (se 1 (by rfl) ⟨112791608, by rfl⟩ : syracuseStep 150388811 = 225583217) B225583217
theorem B4571255 : Blo 1805604 4571255 := bstep (se 1 (by rfl) ⟨3428441, by rfl⟩ : syracuseStep 4571255 = 6856883) B6856883
theorem B17367173 : Blo 1805604 17367173 := bstep (se 4 (by rfl) ⟨1628172, by rfl⟩ : syracuseStep 17367173 = 3256345) B3256345
theorem B2441351 : Blo 1805604 2441351 := bstep (se 1 (by rfl) ⟨1831013, by rfl⟩ : syracuseStep 2441351 = 3662027) B3662027
theorem B15433901 : Blo 1805604 15433901 := bstep (se 3 (by rfl) ⟨2893856, by rfl⟩ : syracuseStep 15433901 = 5787713) B5787713
theorem B78176501 : Blo 1805604 78176501 := bstep (se 5 (by rfl) ⟨3664523, by rfl⟩ : syracuseStep 78176501 = 7329047) B7329047
theorem B2285815 : Blo 1805604 2285815 := bstep (se 1 (by rfl) ⟨1714361, by rfl⟩ : syracuseStep 2285815 = 3428723) B3428723
theorem B4063607 : Blo 1805604 4063607 := bstep (se 1 (by rfl) ⟨3047705, by rfl⟩ : syracuseStep 4063607 = 6095411) B6095411
theorem B6857095 : Blo 1805604 6857095 := bstep (se 1 (by rfl) ⟨5142821, by rfl⟩ : syracuseStep 6857095 = 10285643) B10285643
theorem B2032015 : Blo 1805604 2032015 := bstep (se 1 (by rfl) ⟨1524011, by rfl⟩ : syracuseStep 2032015 = 3048023) B3048023
theorem B3047881 : Blo 1805604 3047881 := bstep (se 2 (by rfl) ⟨1142955, by rfl⟩ : syracuseStep 3047881 = 2285911) B2285911
theorem B4063787 : Blo 1805604 4063787 := bstep (se 1 (by rfl) ⟨3047840, by rfl⟩ : syracuseStep 4063787 = 6095681) B6095681
theorem B2286139 : Blo 1805604 2286139 := bstep (se 1 (by rfl) ⟨1714604, by rfl⟩ : syracuseStep 2286139 = 3429209) B3429209
theorem B5145373 : Blo 1805604 5145373 := bstep (se 3 (by rfl) ⟨964757, by rfl⟩ : syracuseStep 5145373 = 1929515) B1929515
theorem B2032519 : Blo 1805604 2032519 := bstep (se 1 (by rfl) ⟨1524389, by rfl⟩ : syracuseStep 2032519 = 3048779) B3048779
theorem B4064147 : Blo 1805604 4064147 := bstep (se 1 (by rfl) ⟨3048110, by rfl⟩ : syracuseStep 4064147 = 6096221) B6096221
theorem B14656409 : Blo 1805604 14656409 := bstep (se 2 (by rfl) ⟨5496153, by rfl⟩ : syracuseStep 14656409 = 10992307) B10992307
theorem B4064201 : Blo 1805604 4064201 := bstep (se 2 (by rfl) ⟨1524075, by rfl⟩ : syracuseStep 4064201 = 3048151) B3048151
theorem B5145545 : Blo 1805604 5145545 := bstep (se 2 (by rfl) ⟨1929579, by rfl⟩ : syracuseStep 5145545 = 3859159) B3859159
theorem B8684509 : Blo 1805604 8684509 := bstep (se 3 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 8684509 = 3256691) B3256691
theorem B5145601 : Blo 1805604 5145601 := bstep (se 2 (by rfl) ⟨1929600, by rfl⟩ : syracuseStep 5145601 = 3859201) B3859201
theorem B10290199 : Blo 1805604 10290199 := bstep (se 1 (by rfl) ⟨7717649, by rfl⟩ : syracuseStep 10290199 = 15435299) B15435299
theorem B16483351 : Blo 1805604 16483351 := bstep (se 1 (by rfl) ⟨12362513, by rfl⟩ : syracuseStep 16483351 = 24725027) B24725027
theorem B10429469 : Blo 1805604 10429469 := bstep (se 3 (by rfl) ⟨1955525, by rfl⟩ : syracuseStep 10429469 = 3911051) B3911051
theorem B2032699 : Blo 1805604 2032699 := bstep (se 1 (by rfl) ⟨1524524, by rfl⟩ : syracuseStep 2032699 = 3049049) B3049049
theorem B13026365 : Blo 1805604 13026365 := bstep (se 3 (by rfl) ⟨2442443, by rfl⟩ : syracuseStep 13026365 = 4884887) B4884887
theorem B4572247 : Blo 1805604 4572247 := bstep (se 1 (by rfl) ⟨3429185, by rfl⟩ : syracuseStep 4572247 = 6858371) B6858371
theorem B3048583 : Blo 1805604 3048583 := bstep (se 1 (by rfl) ⟨2286437, by rfl⟩ : syracuseStep 3048583 = 4572875) B4572875
theorem B9143603 : Blo 1805604 9143603 := bstep (se 1 (by rfl) ⟨6857702, by rfl⟩ : syracuseStep 9143603 = 13715405) B13715405
theorem B5145943 : Blo 1805604 5145943 := bstep (se 1 (by rfl) ⟨3859457, by rfl⟩ : syracuseStep 5145943 = 7718915) B7718915
theorem B4572551 : Blo 1805604 4572551 := bstep (se 1 (by rfl) ⟨3429413, by rfl⟩ : syracuseStep 4572551 = 6858827) B6858827
theorem B6096275 : Blo 1805604 6096275 := bstep (se 1 (by rfl) ⟨4572206, by rfl⟩ : syracuseStep 6096275 = 9144413) B9144413
theorem B6956441 : Blo 1805604 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B2287111 : Blo 1805604 2287111 := bstep (se 1 (by rfl) ⟨1715333, by rfl⟩ : syracuseStep 2287111 = 3430667) B3430667
theorem B4572683 : Blo 1805604 4572683 := bstep (se 1 (by rfl) ⟨3429512, by rfl⟩ : syracuseStep 4572683 = 6859025) B6859025
theorem B2033167 : Blo 1805604 2033167 := bstep (se 1 (by rfl) ⟨1524875, by rfl⟩ : syracuseStep 2033167 = 3049751) B3049751
theorem B6514219 : Blo 1805604 6514219 := bstep (se 1 (by rfl) ⟨4885664, by rfl⟩ : syracuseStep 6514219 = 9771329) B9771329
theorem B9143927 : Blo 1805604 9143927 := bstep (se 1 (by rfl) ⟨6857945, by rfl⟩ : syracuseStep 9143927 = 13715891) B13715891
theorem B4064903 : Blo 1805604 4064903 := bstep (se 1 (by rfl) ⟨3048677, by rfl⟩ : syracuseStep 4064903 = 6097355) B6097355
theorem B3049231 : Blo 1805604 3049231 := bstep (se 1 (by rfl) ⟨2286923, by rfl⟩ : syracuseStep 3049231 = 4573847) B4573847
theorem B18540323 : Blo 1805604 18540323 := bstep (se 1 (by rfl) ⟨13905242, by rfl⟩ : syracuseStep 18540323 = 27810485) B27810485
theorem B4065083 : Blo 1805604 4065083 := bstep (se 1 (by rfl) ⟨3048812, by rfl⟩ : syracuseStep 4065083 = 6097625) B6097625
theorem B2934587 : Blo 1805604 2934587 := bstep (se 1 (by rfl) ⟨2200940, by rfl⟩ : syracuseStep 2934587 = 4401881) B4401881
theorem B4122427 : Blo 1805604 4122427 := bstep (se 1 (by rfl) ⟨3091820, by rfl⟩ : syracuseStep 4122427 = 6183641) B6183641
theorem B13027225 : Blo 1805604 13027225 := bstep (se 2 (by rfl) ⟨4885209, by rfl⟩ : syracuseStep 13027225 = 9770419) B9770419
theorem B2287531 : Blo 1805604 2287531 := bstep (se 1 (by rfl) ⟨1715648, by rfl⟩ : syracuseStep 2287531 = 3431297) B3431297
theorem B4065209 : Blo 1805604 4065209 := bstep (se 2 (by rfl) ⟨1524453, by rfl⟩ : syracuseStep 4065209 = 3048907) B3048907
theorem B4573199 : Blo 1805604 4573199 := bstep (se 1 (by rfl) ⟨3429899, by rfl⟩ : syracuseStep 4573199 = 6859799) B6859799
theorem B4573331 : Blo 1805604 4573331 := bstep (se 1 (by rfl) ⟨3429998, by rfl⟩ : syracuseStep 4573331 = 6859997) B6859997
theorem B4065551 : Blo 1805604 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B4065569 : Blo 1805604 4065569 := bstep (se 2 (by rfl) ⟨1524588, by rfl⟩ : syracuseStep 4065569 = 3049177) B3049177
theorem B4884779 : Blo 1805604 4884779 := bstep (se 1 (by rfl) ⟨3663584, by rfl⟩ : syracuseStep 4884779 = 7327169) B7327169
theorem B3049771 : Blo 1805604 3049771 := bstep (se 1 (by rfl) ⟨2287328, by rfl⟩ : syracuseStep 3049771 = 4574657) B4574657
theorem B3049913 : Blo 1805604 3049913 := bstep (se 2 (by rfl) ⟨1143717, by rfl⟩ : syracuseStep 3049913 = 2287435) B2287435
theorem B18795037 : Blo 1805604 18795037 := bstep (se 3 (by rfl) ⟨3524069, by rfl⟩ : syracuseStep 18795037 = 7048139) B7048139
theorem B27855427 : Blo 1805604 27855427 := bstep (se 1 (by rfl) ⟨20891570, by rfl⟩ : syracuseStep 27855427 = 41783141) B41783141
theorem B9144899 : Blo 1805604 9144899 := bstep (se 1 (by rfl) ⟨6858674, by rfl⟩ : syracuseStep 9144899 = 13717349) B13717349
theorem B17361485 : Blo 1805604 17361485 := bstep (se 3 (by rfl) ⟨3255278, by rfl⟩ : syracuseStep 17361485 = 6510557) B6510557
theorem B8677975 : Blo 1805604 8677975 := bstep (se 1 (by rfl) ⟨6508481, by rfl⟩ : syracuseStep 8677975 = 13016963) B13016963
theorem B4065911 : Blo 1805604 4065911 := bstep (se 1 (by rfl) ⟨3049433, by rfl⟩ : syracuseStep 4065911 = 6098867) B6098867
theorem B5491385 : Blo 1805604 5491385 := bstep (se 2 (by rfl) ⟨2059269, by rfl⟩ : syracuseStep 5491385 = 4118539) B4118539
theorem B6097679 : Blo 1805604 6097679 := bstep (se 1 (by rfl) ⟨4573259, by rfl⟩ : syracuseStep 6097679 = 9146519) B9146519
theorem B4066091 : Blo 1805604 4066091 := bstep (se 1 (by rfl) ⟨3049568, by rfl⟩ : syracuseStep 4066091 = 6099137) B6099137
theorem B8244083 : Blo 1805604 8244083 := bstep (se 1 (by rfl) ⟨6183062, by rfl⟩ : syracuseStep 8244083 = 12366125) B12366125
theorem B4402039 : Blo 1805604 4402039 := bstep (se 1 (by rfl) ⟨3301529, by rfl⟩ : syracuseStep 4402039 = 6603059) B6603059
theorem B9145223 : Blo 1805604 9145223 := bstep (se 1 (by rfl) ⟨6858917, by rfl⟩ : syracuseStep 9145223 = 13717835) B13717835
theorem B13716377 : Blo 1805604 13716377 := bstep (se 2 (by rfl) ⟨5143641, by rfl⟩ : syracuseStep 13716377 = 10287283) B10287283
theorem B2608043 : Blo 1805604 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B6097949 : Blo 1805604 6097949 := bstep (se 3 (by rfl) ⟨1143365, by rfl⟩ : syracuseStep 6097949 = 2286731) B2286731
theorem B4066451 : Blo 1805604 4066451 := bstep (se 1 (by rfl) ⟨3049838, by rfl⟩ : syracuseStep 4066451 = 6099677) B6099677
theorem B70405271 : Blo 1805604 70405271 := bstep (se 1 (by rfl) ⟨52803953, by rfl⟩ : syracuseStep 70405271 = 105607907) B105607907
theorem B3255481 : Blo 1805604 3255481 := bstep (se 2 (by rfl) ⟨1220805, by rfl⟩ : syracuseStep 3255481 = 2441611) B2441611
theorem B4066505 : Blo 1805604 4066505 := bstep (se 2 (by rfl) ⟨1524939, by rfl⟩ : syracuseStep 4066505 = 3049879) B3049879
theorem B4574465 : Blo 1805604 4574465 := bstep (se 2 (by rfl) ⟨1715424, by rfl⟩ : syracuseStep 4574465 = 3430849) B3430849
theorem B2895119 : Blo 1805604 2895119 := bstep (se 1 (by rfl) ⟨2171339, by rfl⟩ : syracuseStep 2895119 = 4342679) B4342679
theorem B1805627 : Blo 1805604 1805627 := bstep (se 1 (by rfl) ⟨1354220, by rfl⟩ : syracuseStep 1805627 = 2708441) B2708441
theorem B1928507 : Blo 1805604 1928507 := bstep (se 1 (by rfl) ⟨1446380, by rfl⟩ : syracuseStep 1928507 = 2892761) B2892761
theorem B1805703 : Blo 1805604 1805703 := bstep (se 1 (by rfl) ⟨1354277, by rfl⟩ : syracuseStep 1805703 = 2708555) B2708555
theorem B10292615 : Blo 1805604 10292615 := bstep (se 1 (by rfl) ⟨7719461, by rfl⟩ : syracuseStep 10292615 = 15438923) B15438923
theorem B1805711 : Blo 1805604 1805711 := bstep (se 1 (by rfl) ⟨1354283, by rfl⟩ : syracuseStep 1805711 = 2708567) B2708567
theorem B1805755 : Blo 1805604 1805755 := bstep (se 1 (by rfl) ⟨1354316, by rfl⟩ : syracuseStep 1805755 = 2708633) B2708633
theorem B1805831 : Blo 1805604 1805831 := bstep (se 1 (by rfl) ⟨1354373, by rfl⟩ : syracuseStep 1805831 = 2708747) B2708747
theorem B1805839 : Blo 1805604 1805839 := bstep (se 1 (by rfl) ⟨1354379, by rfl⟩ : syracuseStep 1805839 = 2708759) B2708759
theorem B15429149 : Blo 1805604 15429149 := bstep (se 3 (by rfl) ⟨2892965, by rfl⟩ : syracuseStep 15429149 = 5785931) B5785931
theorem B1805883 : Blo 1805604 1805883 := bstep (se 1 (by rfl) ⟨1354412, by rfl⟩ : syracuseStep 1805883 = 2708825) B2708825
theorem B4574839 : Blo 1805604 4574839 := bstep (se 1 (by rfl) ⟨3431129, by rfl⟩ : syracuseStep 4574839 = 6862259) B6862259
theorem B1805959 : Blo 1805604 1805959 := bstep (se 1 (by rfl) ⟨1354469, by rfl⟩ : syracuseStep 1805959 = 2708939) B2708939
theorem B2821775 : Blo 1805604 2821775 := bstep (se 1 (by rfl) ⟨2116331, by rfl⟩ : syracuseStep 2821775 = 4232663) B4232663
theorem B1805967 : Blo 1805604 1805967 := bstep (se 1 (by rfl) ⟨1354475, by rfl⟩ : syracuseStep 1805967 = 2708951) B2708951
theorem B1806011 : Blo 1805604 1806011 := bstep (se 1 (by rfl) ⟨1354508, by rfl⟩ : syracuseStep 1806011 = 2709017) B2709017
theorem B1806087 : Blo 1805604 1806087 := bstep (se 1 (by rfl) ⟨1354565, by rfl⟩ : syracuseStep 1806087 = 2709131) B2709131
theorem B1806095 : Blo 1805604 1806095 := bstep (se 1 (by rfl) ⟨1354571, by rfl⟩ : syracuseStep 1806095 = 2709143) B2709143
theorem B1806139 : Blo 1805604 1806139 := bstep (se 1 (by rfl) ⟨1354604, by rfl⟩ : syracuseStep 1806139 = 2709209) B2709209
theorem B1806215 : Blo 1805604 1806215 := bstep (se 1 (by rfl) ⟨1354661, by rfl⟩ : syracuseStep 1806215 = 2709323) B2709323
theorem B1806223 : Blo 1805604 1806223 := bstep (se 1 (by rfl) ⟨1354667, by rfl⟩ : syracuseStep 1806223 = 2709335) B2709335
theorem B8245145 : Blo 1805604 8245145 := bstep (se 2 (by rfl) ⟨3091929, by rfl⟩ : syracuseStep 8245145 = 6183859) B6183859
theorem B1806267 : Blo 1805604 1806267 := bstep (se 1 (by rfl) ⟨1354700, by rfl⟩ : syracuseStep 1806267 = 2709401) B2709401
theorem B1806343 : Blo 1805604 1806343 := bstep (se 1 (by rfl) ⟨1354757, by rfl⟩ : syracuseStep 1806343 = 2709515) B2709515
theorem B1806351 : Blo 1805604 1806351 := bstep (se 1 (by rfl) ⟨1354763, by rfl⟩ : syracuseStep 1806351 = 2709527) B2709527
theorem B4575275 : Blo 1805604 4575275 := bstep (se 1 (by rfl) ⟨3431456, by rfl⟩ : syracuseStep 4575275 = 6862913) B6862913
theorem B1806395 : Blo 1805604 1806395 := bstep (se 1 (by rfl) ⟨1354796, by rfl⟩ : syracuseStep 1806395 = 2709593) B2709593
theorem B1806471 : Blo 1805604 1806471 := bstep (se 1 (by rfl) ⟨1354853, by rfl⟩ : syracuseStep 1806471 = 2709707) B2709707
theorem B1806479 : Blo 1805604 1806479 := bstep (se 1 (by rfl) ⟨1354859, by rfl⟩ : syracuseStep 1806479 = 2709719) B2709719
theorem B1806523 : Blo 1805604 1806523 := bstep (se 1 (by rfl) ⟨1354892, by rfl⟩ : syracuseStep 1806523 = 2709785) B2709785
theorem B1806599 : Blo 1805604 1806599 := bstep (se 1 (by rfl) ⟨1354949, by rfl⟩ : syracuseStep 1806599 = 2709899) B2709899
theorem B1806607 : Blo 1805604 1806607 := bstep (se 1 (by rfl) ⟨1354955, by rfl⟩ : syracuseStep 1806607 = 2709911) B2709911
theorem B3911951 : Blo 1805604 3911951 := bstep (se 1 (by rfl) ⟨2933963, by rfl⟩ : syracuseStep 3911951 = 5867927) B5867927
theorem B1806651 : Blo 1805604 1806651 := bstep (se 1 (by rfl) ⟨1354988, by rfl⟩ : syracuseStep 1806651 = 2709977) B2709977
theorem B7713139 : Blo 1805604 7713139 := bstep (se 1 (by rfl) ⟨5784854, by rfl⟩ : syracuseStep 7713139 = 11569709) B11569709
theorem B4632967 : Blo 1805604 4632967 := bstep (se 1 (by rfl) ⟨3474725, by rfl⟩ : syracuseStep 4632967 = 6949451) B6949451
theorem B1806727 : Blo 1805604 1806727 := bstep (se 1 (by rfl) ⟨1355045, by rfl⟩ : syracuseStep 1806727 = 2710091) B2710091
theorem B1806735 : Blo 1805604 1806735 := bstep (se 1 (by rfl) ⟨1355051, by rfl⟩ : syracuseStep 1806735 = 2710103) B2710103
theorem B13726097 : Blo 1805604 13726097 := bstep (se 2 (by rfl) ⟨5147286, by rfl⟩ : syracuseStep 13726097 = 10294573) B10294573
theorem B6099353 : Blo 1805604 6099353 := bstep (se 2 (by rfl) ⟨2287257, by rfl⟩ : syracuseStep 6099353 = 4574515) B4574515
theorem B1806779 : Blo 1805604 1806779 := bstep (se 1 (by rfl) ⟨1355084, by rfl⟩ : syracuseStep 1806779 = 2710169) B2710169
theorem B6951377 : Blo 1805604 6951377 := bstep (se 2 (by rfl) ⟨2606766, by rfl⟩ : syracuseStep 6951377 = 5213533) B5213533
theorem B1806855 : Blo 1805604 1806855 := bstep (se 1 (by rfl) ⟨1355141, by rfl⟩ : syracuseStep 1806855 = 2710283) B2710283
theorem B1806863 : Blo 1805604 1806863 := bstep (se 1 (by rfl) ⟨1355147, by rfl⟩ : syracuseStep 1806863 = 2710295) B2710295
theorem B3256865 : Blo 1805604 3256865 := bstep (se 2 (by rfl) ⟨1221324, by rfl⟩ : syracuseStep 3256865 = 2442649) B2442649
theorem B1806907 : Blo 1805604 1806907 := bstep (se 1 (by rfl) ⟨1355180, by rfl⟩ : syracuseStep 1806907 = 2710361) B2710361
theorem B18535031 : Blo 1805604 18535031 := bstep (se 1 (by rfl) ⟨13901273, by rfl⟩ : syracuseStep 18535031 = 27802547) B27802547
theorem B1856135 : Blo 1805604 1856135 := bstep (se 1 (by rfl) ⟨1392101, by rfl⟩ : syracuseStep 1856135 = 2784203) B2784203
theorem B1806983 : Blo 1805604 1806983 := bstep (se 1 (by rfl) ⟨1355237, by rfl⟩ : syracuseStep 1806983 = 2710475) B2710475
theorem B1806991 : Blo 1805604 1806991 := bstep (se 1 (by rfl) ⟨1355243, by rfl⟩ : syracuseStep 1806991 = 2710487) B2710487
theorem B3429049 : Blo 1805604 3429049 := bstep (se 2 (by rfl) ⟨1285893, by rfl⟩ : syracuseStep 3429049 = 2571787) B2571787
theorem B1807035 : Blo 1805604 1807035 := bstep (se 1 (by rfl) ⟨1355276, by rfl⟩ : syracuseStep 1807035 = 2710553) B2710553
theorem B7713481 : Blo 1805604 7713481 := bstep (se 2 (by rfl) ⟨2892555, by rfl⟩ : syracuseStep 7713481 = 5785111) B5785111
theorem B20861657 : Blo 1805604 20861657 := bstep (se 2 (by rfl) ⟨7823121, by rfl⟩ : syracuseStep 20861657 = 15646243) B15646243
theorem B10285825 : Blo 1805604 10285825 := bstep (se 2 (by rfl) ⟨3857184, by rfl⟩ : syracuseStep 10285825 = 7714369) B7714369
theorem B1807111 : Blo 1805604 1807111 := bstep (se 1 (by rfl) ⟨1355333, by rfl⟩ : syracuseStep 1807111 = 2710667) B2710667
theorem B1807119 : Blo 1805604 1807119 := bstep (se 1 (by rfl) ⟨1355339, by rfl⟩ : syracuseStep 1807119 = 2710679) B2710679
theorem B13718321 : Blo 1805604 13718321 := bstep (se 2 (by rfl) ⟨5144370, by rfl⟩ : syracuseStep 13718321 = 10288741) B10288741
theorem B1807163 : Blo 1805604 1807163 := bstep (se 1 (by rfl) ⟨1355372, by rfl⟩ : syracuseStep 1807163 = 2710745) B2710745
theorem B1807239 : Blo 1805604 1807239 := bstep (se 1 (by rfl) ⟨1355429, by rfl⟩ : syracuseStep 1807239 = 2710859) B2710859
theorem B1807247 : Blo 1805604 1807247 := bstep (se 1 (by rfl) ⟨1355435, by rfl⟩ : syracuseStep 1807247 = 2710871) B2710871
theorem B2708411 : Blo 1805604 2708411 := bstep (se 1 (by rfl) ⟨2031308, by rfl⟩ : syracuseStep 2708411 = 4062617) B4062617
theorem B1807291 : Blo 1805604 1807291 := bstep (se 1 (by rfl) ⟨1355468, by rfl⟩ : syracuseStep 1807291 = 2710937) B2710937
theorem B2708471 : Blo 1805604 2708471 := bstep (se 1 (by rfl) ⟨2031353, by rfl⟩ : syracuseStep 2708471 = 4062707) B4062707
theorem B1807367 : Blo 1805604 1807367 := bstep (se 1 (by rfl) ⟨1355525, by rfl⟩ : syracuseStep 1807367 = 2711051) B2711051
theorem B2708495 : Blo 1805604 2708495 := bstep (se 1 (by rfl) ⟨2031371, by rfl⟩ : syracuseStep 2708495 = 4062743) B4062743
theorem B3429391 : Blo 1805604 3429391 := bstep (se 1 (by rfl) ⟨2572043, by rfl⟩ : syracuseStep 3429391 = 5144087) B5144087
theorem B1807375 : Blo 1805604 1807375 := bstep (se 1 (by rfl) ⟨1355531, by rfl⟩ : syracuseStep 1807375 = 2711063) B2711063
theorem B2708537 : Blo 1805604 2708537 := bstep (se 2 (by rfl) ⟨1015701, by rfl⟩ : syracuseStep 2708537 = 2031403) B2031403
theorem B1807419 : Blo 1805604 1807419 := bstep (se 1 (by rfl) ⟨1355564, by rfl⟩ : syracuseStep 1807419 = 2711129) B2711129
theorem B6100055 : Blo 1805604 6100055 := bstep (se 1 (by rfl) ⟨4575041, by rfl⟩ : syracuseStep 6100055 = 9150083) B9150083
theorem B10294391 : Blo 1805604 10294391 := bstep (se 1 (by rfl) ⟨7720793, by rfl⟩ : syracuseStep 10294391 = 15441587) B15441587
theorem B2708615 : Blo 1805604 2708615 := bstep (se 1 (by rfl) ⟨2031461, by rfl⟩ : syracuseStep 2708615 = 4062923) B4062923
theorem B1807495 : Blo 1805604 1807495 := bstep (se 1 (by rfl) ⟨1355621, by rfl⟩ : syracuseStep 1807495 = 2711243) B2711243
theorem B1807503 : Blo 1805604 1807503 := bstep (se 1 (by rfl) ⟨1355627, by rfl⟩ : syracuseStep 1807503 = 2711255) B2711255
theorem B2708651 : Blo 1805604 2708651 := bstep (se 1 (by rfl) ⟨2031488, by rfl⟩ : syracuseStep 2708651 = 4062977) B4062977
theorem B1807547 : Blo 1805604 1807547 := bstep (se 1 (by rfl) ⟨1355660, by rfl⟩ : syracuseStep 1807547 = 2711321) B2711321
theorem B2708681 : Blo 1805604 2708681 := bstep (se 2 (by rfl) ⟨1015755, by rfl⟩ : syracuseStep 2708681 = 2031511) B2031511
theorem B10286351 : Blo 1805604 10286351 := bstep (se 1 (by rfl) ⟨7714763, by rfl⟩ : syracuseStep 10286351 = 15429527) B15429527
theorem B5141819 : Blo 1805604 5141819 := bstep (se 1 (by rfl) ⟨3856364, by rfl⟩ : syracuseStep 5141819 = 7712729) B7712729
theorem B2708795 : Blo 1805604 2708795 := bstep (se 1 (by rfl) ⟨2031596, by rfl⟩ : syracuseStep 2708795 = 4063193) B4063193
theorem B2708855 : Blo 1805604 2708855 := bstep (se 1 (by rfl) ⟨2031641, by rfl⟩ : syracuseStep 2708855 = 4063283) B4063283
theorem B2708879 : Blo 1805604 2708879 := bstep (se 1 (by rfl) ⟨2031659, by rfl⟩ : syracuseStep 2708879 = 4063319) B4063319
theorem B2708921 : Blo 1805604 2708921 := bstep (se 2 (by rfl) ⟨1015845, by rfl⟩ : syracuseStep 2708921 = 2031691) B2031691
theorem B2708999 : Blo 1805604 2708999 := bstep (se 1 (by rfl) ⟨2031749, by rfl⟩ : syracuseStep 2708999 = 4063499) B4063499
theorem B2709035 : Blo 1805604 2709035 := bstep (se 1 (by rfl) ⟨2031776, by rfl⟩ : syracuseStep 2709035 = 4063553) B4063553
theorem B6100541 : Blo 1805604 6100541 := bstep (se 3 (by rfl) ⟨1143851, by rfl⟩ : syracuseStep 6100541 = 2287703) B2287703
theorem B2709065 : Blo 1805604 2709065 := bstep (se 2 (by rfl) ⟨1015899, by rfl⟩ : syracuseStep 2709065 = 2031799) B2031799
theorem B2709179 : Blo 1805604 2709179 := bstep (se 1 (by rfl) ⟨2031884, by rfl⟩ : syracuseStep 2709179 = 4063769) B4063769
theorem B156243653 : Blo 1805604 156243653 := bstep (se 4 (by rfl) ⟨14647842, by rfl⟩ : syracuseStep 156243653 = 29295685) B29295685
theorem B7714541 : Blo 1805604 7714541 := bstep (se 3 (by rfl) ⟨1446476, by rfl⟩ : syracuseStep 7714541 = 2892953) B2892953
theorem B2709239 : Blo 1805604 2709239 := bstep (se 1 (by rfl) ⟨2031929, by rfl⟩ : syracuseStep 2709239 = 4063859) B4063859
theorem B2709263 : Blo 1805604 2709263 := bstep (se 1 (by rfl) ⟨2031947, by rfl⟩ : syracuseStep 2709263 = 4063895) B4063895
theorem B19535651 : Blo 1805604 19535651 := bstep (se 1 (by rfl) ⟨14651738, by rfl⟩ : syracuseStep 19535651 = 29303477) B29303477
theorem B12367667 : Blo 1805604 12367667 := bstep (se 1 (by rfl) ⟨9275750, by rfl⟩ : syracuseStep 12367667 = 18551501) B18551501
theorem B2709305 : Blo 1805604 2709305 := bstep (se 2 (by rfl) ⟨1015989, by rfl⟩ : syracuseStep 2709305 = 2031979) B2031979
theorem B2709383 : Blo 1805604 2709383 := bstep (se 1 (by rfl) ⟨2032037, by rfl⟩ : syracuseStep 2709383 = 4064075) B4064075
theorem B3430279 : Blo 1805604 3430279 := bstep (se 1 (by rfl) ⟨2572709, by rfl⟩ : syracuseStep 3430279 = 5145419) B5145419
theorem B6862745 : Blo 1805604 6862745 := bstep (se 2 (by rfl) ⟨2573529, by rfl⟩ : syracuseStep 6862745 = 5147059) B5147059
theorem B2709419 : Blo 1805604 2709419 := bstep (se 1 (by rfl) ⟨2032064, by rfl⟩ : syracuseStep 2709419 = 4064129) B4064129
theorem B5142457 : Blo 1805604 5142457 := bstep (se 2 (by rfl) ⟨1928421, by rfl⟩ : syracuseStep 5142457 = 3856843) B3856843
theorem B2709449 : Blo 1805604 2709449 := bstep (se 2 (by rfl) ⟨1016043, by rfl⟩ : syracuseStep 2709449 = 2032087) B2032087
theorem B7821323 : Blo 1805604 7821323 := bstep (se 1 (by rfl) ⟨5865992, by rfl⟩ : syracuseStep 7821323 = 11731985) B11731985
theorem B2709563 : Blo 1805604 2709563 := bstep (se 1 (by rfl) ⟨2032172, by rfl⟩ : syracuseStep 2709563 = 4064345) B4064345
theorem B7526467 : Blo 1805604 7526467 := bstep (se 1 (by rfl) ⟨5644850, by rfl⟩ : syracuseStep 7526467 = 11289701) B11289701
theorem B2783351 : Blo 1805604 2783351 := bstep (se 1 (by rfl) ⟨2087513, by rfl⟩ : syracuseStep 2783351 = 4175027) B4175027
theorem B2709623 : Blo 1805604 2709623 := bstep (se 1 (by rfl) ⟨2032217, by rfl⟩ : syracuseStep 2709623 = 4064435) B4064435
theorem B2709647 : Blo 1805604 2709647 := bstep (se 1 (by rfl) ⟨2032235, by rfl⟩ : syracuseStep 2709647 = 4064471) B4064471
theorem B2709689 : Blo 1805604 2709689 := bstep (se 2 (by rfl) ⟨1016133, by rfl⟩ : syracuseStep 2709689 = 2032267) B2032267
theorem B13383917 : Blo 1805604 13383917 := bstep (se 3 (by rfl) ⟨2509484, by rfl⟩ : syracuseStep 13383917 = 5018969) B5018969
theorem B2709767 : Blo 1805604 2709767 := bstep (se 1 (by rfl) ⟨2032325, by rfl⟩ : syracuseStep 2709767 = 4064651) B4064651
theorem B3856673 : Blo 1805604 3856673 := bstep (se 2 (by rfl) ⟨1446252, by rfl⟩ : syracuseStep 3856673 = 2892505) B2892505
theorem B2709803 : Blo 1805604 2709803 := bstep (se 1 (by rfl) ⟨2032352, by rfl⟩ : syracuseStep 2709803 = 4064705) B4064705
theorem B5142845 : Blo 1805604 5142845 := bstep (se 3 (by rfl) ⟨964283, by rfl⟩ : syracuseStep 5142845 = 1928567) B1928567
theorem B2709833 : Blo 1805604 2709833 := bstep (se 2 (by rfl) ⟨1016187, by rfl⟩ : syracuseStep 2709833 = 2032375) B2032375
theorem B9148787 : Blo 1805604 9148787 := bstep (se 1 (by rfl) ⟨6861590, by rfl⟩ : syracuseStep 9148787 = 13723181) B13723181
theorem B2709947 : Blo 1805604 2709947 := bstep (se 1 (by rfl) ⟨2032460, by rfl⟩ : syracuseStep 2709947 = 4064921) B4064921
theorem B2710007 : Blo 1805604 2710007 := bstep (se 1 (by rfl) ⟨2032505, by rfl⟩ : syracuseStep 2710007 = 4065011) B4065011
theorem B2710031 : Blo 1805604 2710031 := bstep (se 1 (by rfl) ⟨2032523, by rfl⟩ : syracuseStep 2710031 = 4065047) B4065047
theorem B2710073 : Blo 1805604 2710073 := bstep (se 2 (by rfl) ⟨1016277, by rfl⟩ : syracuseStep 2710073 = 2032555) B2032555
theorem B14654071 : Blo 1805604 14654071 := bstep (se 1 (by rfl) ⟨10990553, by rfl⟩ : syracuseStep 14654071 = 21981107) B21981107
theorem B2570887 : Blo 1805604 2570887 := bstep (se 1 (by rfl) ⟨1928165, by rfl⟩ : syracuseStep 2570887 = 3856331) B3856331
theorem B2710151 : Blo 1805604 2710151 := bstep (se 1 (by rfl) ⟨2032613, by rfl⟩ : syracuseStep 2710151 = 4065227) B4065227
theorem B2710187 : Blo 1805604 2710187 := bstep (se 1 (by rfl) ⟨2032640, by rfl⟩ : syracuseStep 2710187 = 4065281) B4065281
theorem B17357489 : Blo 1805604 17357489 := bstep (se 2 (by rfl) ⟨6509058, by rfl⟩ : syracuseStep 17357489 = 13018117) B13018117
theorem B10287809 : Blo 1805604 10287809 := bstep (se 2 (by rfl) ⟨3857928, by rfl⟩ : syracuseStep 10287809 = 7715857) B7715857
theorem B2710217 : Blo 1805604 2710217 := bstep (se 2 (by rfl) ⟨1016331, by rfl⟩ : syracuseStep 2710217 = 2032663) B2032663
theorem B2710331 : Blo 1805604 2710331 := bstep (se 1 (by rfl) ⟨2032748, by rfl⟩ : syracuseStep 2710331 = 4065497) B4065497
theorem B9149273 : Blo 1805604 9149273 := bstep (se 2 (by rfl) ⟨3430977, by rfl⟩ : syracuseStep 9149273 = 6861955) B6861955
theorem B2710391 : Blo 1805604 2710391 := bstep (se 1 (by rfl) ⟨2032793, by rfl⟩ : syracuseStep 2710391 = 4065587) B4065587
theorem B2710415 : Blo 1805604 2710415 := bstep (se 1 (by rfl) ⟨2032811, by rfl⟩ : syracuseStep 2710415 = 4065623) B4065623
theorem B2710457 : Blo 1805604 2710457 := bstep (se 2 (by rfl) ⟨1016421, by rfl⟩ : syracuseStep 2710457 = 2032843) B2032843
theorem B6691793 : Blo 1805604 6691793 := bstep (se 2 (by rfl) ⟨2509422, by rfl⟩ : syracuseStep 6691793 = 5018845) B5018845
theorem B18545669 : Blo 1805604 18545669 := bstep (se 4 (by rfl) ⟨1738656, by rfl⟩ : syracuseStep 18545669 = 3477313) B3477313
theorem B2710535 : Blo 1805604 2710535 := bstep (se 1 (by rfl) ⟨2032901, by rfl⟩ : syracuseStep 2710535 = 4065803) B4065803
theorem B2710571 : Blo 1805604 2710571 := bstep (se 1 (by rfl) ⟨2032928, by rfl⟩ : syracuseStep 2710571 = 4065857) B4065857
theorem B77225021 : Blo 1805604 77225021 := bstep (se 3 (by rfl) ⟨14479691, by rfl⟩ : syracuseStep 77225021 = 28959383) B28959383
theorem B2710601 : Blo 1805604 2710601 := bstep (se 2 (by rfl) ⟨1016475, by rfl⟩ : syracuseStep 2710601 = 2032951) B2032951
theorem B9141335 : Blo 1805604 9141335 := bstep (se 1 (by rfl) ⟨6856001, by rfl⟩ : syracuseStep 9141335 = 13712003) B13712003
theorem B2710715 : Blo 1805604 2710715 := bstep (se 1 (by rfl) ⟨2033036, by rfl⟩ : syracuseStep 2710715 = 4066073) B4066073
theorem B8797385 : Blo 1805604 8797385 := bstep (se 2 (by rfl) ⟨3299019, by rfl⟩ : syracuseStep 8797385 = 6598039) B6598039
theorem B4177097 : Blo 1805604 4177097 := bstep (se 2 (by rfl) ⟨1566411, by rfl⟩ : syracuseStep 4177097 = 3132823) B3132823
theorem B2710775 : Blo 1805604 2710775 := bstep (se 1 (by rfl) ⟨2033081, by rfl⟩ : syracuseStep 2710775 = 4066163) B4066163
theorem B2710799 : Blo 1805604 2710799 := bstep (se 1 (by rfl) ⟨2033099, by rfl⟩ : syracuseStep 2710799 = 4066199) B4066199
theorem B2710841 : Blo 1805604 2710841 := bstep (se 2 (by rfl) ⟨1016565, by rfl⟩ : syracuseStep 2710841 = 2033131) B2033131
theorem B2571593 : Blo 1805604 2571593 := bstep (se 2 (by rfl) ⟨964347, by rfl⟩ : syracuseStep 2571593 = 1928695) B1928695
theorem B2710919 : Blo 1805604 2710919 := bstep (se 1 (by rfl) ⟨2033189, by rfl⟩ : syracuseStep 2710919 = 4066379) B4066379
theorem B5143961 : Blo 1805604 5143961 := bstep (se 2 (by rfl) ⟨1928985, by rfl⟩ : syracuseStep 5143961 = 3857971) B3857971
theorem B2710955 : Blo 1805604 2710955 := bstep (se 1 (by rfl) ⟨2033216, by rfl⟩ : syracuseStep 2710955 = 4066433) B4066433
theorem B2571707 : Blo 1805604 2571707 := bstep (se 1 (by rfl) ⟨1928780, by rfl⟩ : syracuseStep 2571707 = 3857561) B3857561
theorem B2710985 : Blo 1805604 2710985 := bstep (se 2 (by rfl) ⟨1016619, by rfl⟩ : syracuseStep 2710985 = 2033239) B2033239
theorem B17366557 : Blo 1805604 17366557 := bstep (se 3 (by rfl) ⟨3256229, by rfl⟩ : syracuseStep 17366557 = 6512459) B6512459
theorem B7421483 : Blo 1805604 7421483 := bstep (se 1 (by rfl) ⟨5566112, by rfl⟩ : syracuseStep 7421483 = 11132225) B11132225
theorem B4062779 : Blo 1805604 4062779 := bstep (se 1 (by rfl) ⟨3047084, by rfl⟩ : syracuseStep 4062779 = 6094169) B6094169
theorem B2711099 : Blo 1805604 2711099 := bstep (se 1 (by rfl) ⟨2033324, by rfl⟩ : syracuseStep 2711099 = 4066649) B4066649
theorem B9141821 : Blo 1805604 9141821 := bstep (se 3 (by rfl) ⟨1714091, by rfl⟩ : syracuseStep 9141821 = 3428183) B3428183
theorem B4570739 : Blo 1805604 4570739 := bstep (se 1 (by rfl) ⟨3428054, by rfl⟩ : syracuseStep 4570739 = 6856109) B6856109
theorem B4120183 : Blo 1805604 4120183 := bstep (se 1 (by rfl) ⟨3090137, by rfl⟩ : syracuseStep 4120183 = 6180275) B6180275
theorem B2711159 : Blo 1805604 2711159 := bstep (se 1 (by rfl) ⟨2033369, by rfl⟩ : syracuseStep 2711159 = 4066739) B4066739
theorem B2711183 : Blo 1805604 2711183 := bstep (se 1 (by rfl) ⟨2033387, by rfl⟩ : syracuseStep 2711183 = 4066775) B4066775
theorem B4341401 : Blo 1805604 4341401 := bstep (se 2 (by rfl) ⟨1628025, by rfl⟩ : syracuseStep 4341401 = 3256051) B3256051
theorem B4062905 : Blo 1805604 4062905 := bstep (se 2 (by rfl) ⟨1523589, by rfl⟩ : syracuseStep 4062905 = 3047179) B3047179
theorem B2711225 : Blo 1805604 2711225 := bstep (se 2 (by rfl) ⟨1016709, by rfl⟩ : syracuseStep 2711225 = 2033419) B2033419
theorem B2031367 : Blo 1805604 2031367 := bstep (se 1 (by rfl) ⟨1523525, by rfl⟩ : syracuseStep 2031367 = 3047051) B3047051
theorem B2711303 : Blo 1805604 2711303 := bstep (se 1 (by rfl) ⟨2033477, by rfl⟩ : syracuseStep 2711303 = 4066955) B4066955
theorem B2711339 : Blo 1805604 2711339 := bstep (se 1 (by rfl) ⟨2033504, by rfl⟩ : syracuseStep 2711339 = 4067009) B4067009
theorem B15433523 : Blo 1805604 15433523 := bstep (se 1 (by rfl) ⟨11575142, by rfl⟩ : syracuseStep 15433523 = 23150285) B23150285
theorem B2711369 : Blo 1805604 2711369 := bstep (se 2 (by rfl) ⟨1016763, by rfl⟩ : syracuseStep 2711369 = 2033527) B2033527
theorem B3047287 : Blo 1805604 3047287 := bstep (se 1 (by rfl) ⟨2285465, by rfl⟩ : syracuseStep 3047287 = 4570931) B4570931
theorem B6856595 : Blo 1805604 6856595 := bstep (se 1 (by rfl) ⟨5142446, by rfl⟩ : syracuseStep 6856595 = 10284893) B10284893
theorem B20578211 : Blo 1805604 20578211 := bstep (se 1 (by rfl) ⟨15433658, by rfl⟩ : syracuseStep 20578211 = 30867317) B30867317
theorem B2031547 : Blo 1805604 2031547 := bstep (se 1 (by rfl) ⟨1523660, by rfl⟩ : syracuseStep 2031547 = 3047321) B3047321
theorem B2031655 : Blo 1805604 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B3047503 : Blo 1805604 3047503 := bstep (se 1 (by rfl) ⟨2285627, by rfl⟩ : syracuseStep 3047503 = 4571255) B4571255
theorem B10035289 : Blo 1805604 10035289 := bstep (se 2 (by rfl) ⟨3763233, by rfl⟩ : syracuseStep 10035289 = 7526467) B7526467
theorem B10289267 : Blo 1805604 10289267 := bstep (se 1 (by rfl) ⟨7716950, by rfl⟩ : syracuseStep 10289267 = 15433901) B15433901
theorem B52117667 : Blo 1805604 52117667 := bstep (se 1 (by rfl) ⟨39088250, by rfl⟩ : syracuseStep 52117667 = 78176501) B78176501
theorem B9150731 : Blo 1805604 9150731 := bstep (se 1 (by rfl) ⟨6863048, by rfl⟩ : syracuseStep 9150731 = 13726097) B13726097
theorem B3047753 : Blo 1805604 3047753 := bstep (se 2 (by rfl) ⟨1142907, by rfl⟩ : syracuseStep 3047753 = 2285815) B2285815
theorem B2171243 : Blo 1805604 2171243 := bstep (se 1 (by rfl) ⟨1628432, by rfl⟩ : syracuseStep 2171243 = 3256865) B3256865
theorem B6177289 : Blo 1805604 6177289 := bstep (se 2 (by rfl) ⟨2316483, by rfl⟩ : syracuseStep 6177289 = 4632967) B4632967
theorem B9142793 : Blo 1805604 9142793 := bstep (se 2 (by rfl) ⟨3428547, by rfl⟩ : syracuseStep 9142793 = 6857095) B6857095
theorem B4063841 : Blo 1805604 4063841 := bstep (se 2 (by rfl) ⟨1523940, by rfl⟩ : syracuseStep 4063841 = 3047881) B3047881
theorem B25060049 : Blo 1805604 25060049 := bstep (se 2 (by rfl) ⟨9397518, by rfl⟩ : syracuseStep 25060049 = 18795037) B18795037
theorem B8684243 : Blo 1805604 8684243 := bstep (se 1 (by rfl) ⟨6513182, by rfl⟩ : syracuseStep 8684243 = 13026365) B13026365
theorem B3048185 : Blo 1805604 3048185 := bstep (se 2 (by rfl) ⟨1143069, by rfl⟩ : syracuseStep 3048185 = 2286139) B2286139
theorem B19538761 : Blo 1805604 19538761 := bstep (se 2 (by rfl) ⟨7327035, by rfl⟩ : syracuseStep 19538761 = 14654071) B14654071
theorem B6857567 : Blo 1805604 6857567 := bstep (se 1 (by rfl) ⟨5143175, by rfl⟩ : syracuseStep 6857567 = 10286351) B10286351
theorem B6857581 : Blo 1805604 6857581 := bstep (se 3 (by rfl) ⟨1285796, by rfl⟩ : syracuseStep 6857581 = 2571593) B2571593
theorem B6095735 : Blo 1805604 6095735 := bstep (se 1 (by rfl) ⟨4571801, by rfl⟩ : syracuseStep 6095735 = 9143603) B9143603
theorem B4572065 : Blo 1805604 4572065 := bstep (se 2 (by rfl) ⟨1714524, by rfl⟩ : syracuseStep 4572065 = 3429049) B3429049
theorem B3048367 : Blo 1805604 3048367 := bstep (se 1 (by rfl) ⟨2286275, by rfl⟩ : syracuseStep 3048367 = 4572551) B4572551
theorem B4064183 : Blo 1805604 4064183 := bstep (se 1 (by rfl) ⟨3048137, by rfl⟩ : syracuseStep 4064183 = 6096275) B6096275
theorem B4637627 : Blo 1805604 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B13714433 : Blo 1805604 13714433 := bstep (se 2 (by rfl) ⟨5142912, by rfl⟩ : syracuseStep 13714433 = 10285825) B10285825
theorem B3048455 : Blo 1805604 3048455 := bstep (se 1 (by rfl) ⟨2286341, by rfl⟩ : syracuseStep 3048455 = 4572683) B4572683
theorem B6095951 : Blo 1805604 6095951 := bstep (se 1 (by rfl) ⟨4571963, by rfl⟩ : syracuseStep 6095951 = 9143927) B9143927
theorem B104162435 : Blo 1805604 104162435 := bstep (se 1 (by rfl) ⟨78121826, by rfl⟩ : syracuseStep 104162435 = 156243653) B156243653
theorem B6857885 : Blo 1805604 6857885 := bstep (se 3 (by rfl) ⟨1285853, by rfl⟩ : syracuseStep 6857885 = 2571707) B2571707
theorem B3048799 : Blo 1805604 3048799 := bstep (se 1 (by rfl) ⟨2286599, by rfl⟩ : syracuseStep 3048799 = 4573199) B4573199
theorem B4572521 : Blo 1805604 4572521 := bstep (se 2 (by rfl) ⟨1714695, by rfl⟩ : syracuseStep 4572521 = 3429391) B3429391
theorem B3048887 : Blo 1805604 3048887 := bstep (se 1 (by rfl) ⟨2286665, by rfl⟩ : syracuseStep 3048887 = 4573331) B4573331
theorem B6096329 : Blo 1805604 6096329 := bstep (se 2 (by rfl) ⟨2286123, by rfl⟩ : syracuseStep 6096329 = 4572247) B4572247
theorem B8922611 : Blo 1805604 8922611 := bstep (se 1 (by rfl) ⟨6691958, by rfl⟩ : syracuseStep 8922611 = 13383917) B13383917
theorem B4064777 : Blo 1805604 4064777 := bstep (se 2 (by rfl) ⟨1524291, by rfl⟩ : syracuseStep 4064777 = 3048583) B3048583
theorem B2033275 : Blo 1805604 2033275 := bstep (se 1 (by rfl) ⟨1524956, by rfl⟩ : syracuseStep 2033275 = 3049913) B3049913
theorem B4949693 : Blo 1805604 4949693 := bstep (se 3 (by rfl) ⟨928067, by rfl⟩ : syracuseStep 4949693 = 1856135) B1856135
theorem B6096599 : Blo 1805604 6096599 := bstep (se 1 (by rfl) ⟨4572449, by rfl⟩ : syracuseStep 6096599 = 9144899) B9144899
theorem B6858539 : Blo 1805604 6858539 := bstep (se 1 (by rfl) ⟨5143904, by rfl⟩ : syracuseStep 6858539 = 10287809) B10287809
theorem B4065119 : Blo 1805604 4065119 := bstep (se 1 (by rfl) ⟨3048839, by rfl⟩ : syracuseStep 4065119 = 6097679) B6097679
theorem B6096815 : Blo 1805604 6096815 := bstep (se 1 (by rfl) ⟨4572611, by rfl⟩ : syracuseStep 6096815 = 9145223) B9145223
theorem B9144251 : Blo 1805604 9144251 := bstep (se 1 (by rfl) ⟨6858188, by rfl⟩ : syracuseStep 9144251 = 13716377) B13716377
theorem B12363779 : Blo 1805604 12363779 := bstep (se 1 (by rfl) ⟨9272834, by rfl⟩ : syracuseStep 12363779 = 18545669) B18545669
theorem B3049481 : Blo 1805604 3049481 := bstep (se 2 (by rfl) ⟨1143555, by rfl⟩ : syracuseStep 3049481 = 2287111) B2287111
theorem B4065299 : Blo 1805604 4065299 := bstep (se 1 (by rfl) ⟨3048974, by rfl⟩ : syracuseStep 4065299 = 6097949) B6097949
theorem B8685625 : Blo 1805604 8685625 := bstep (se 2 (by rfl) ⟨3257109, by rfl⟩ : syracuseStep 8685625 = 6514219) B6514219
theorem B7825565 : Blo 1805604 7825565 := bstep (se 3 (by rfl) ⟨1467293, by rfl⟩ : syracuseStep 7825565 = 2934587) B2934587
theorem B3049643 : Blo 1805604 3049643 := bstep (se 1 (by rfl) ⟨2287232, by rfl⟩ : syracuseStep 3049643 = 4574465) B4574465
theorem B4065641 : Blo 1805604 4065641 := bstep (se 2 (by rfl) ⟨1524615, by rfl⟩ : syracuseStep 4065641 = 3049231) B3049231
theorem B2894267 : Blo 1805604 2894267 := bstep (se 1 (by rfl) ⟨2170700, by rfl⟩ : syracuseStep 2894267 = 4341401) B4341401
theorem B4573705 : Blo 1805604 4573705 := bstep (se 2 (by rfl) ⟨1715139, by rfl⟩ : syracuseStep 4573705 = 3430279) B3430279
theorem B17369633 : Blo 1805604 17369633 := bstep (se 2 (by rfl) ⟨6513612, by rfl⟩ : syracuseStep 17369633 = 13027225) B13027225
theorem B17844781 : Blo 1805604 17844781 := bstep (se 3 (by rfl) ⟨3345896, by rfl⟩ : syracuseStep 17844781 = 6691793) B6691793
theorem B3050041 : Blo 1805604 3050041 := bstep (se 2 (by rfl) ⟨1143765, by rfl⟩ : syracuseStep 3050041 = 2287531) B2287531
theorem B3050183 : Blo 1805604 3050183 := bstep (se 1 (by rfl) ⟨2287637, by rfl⟩ : syracuseStep 3050183 = 4575275) B4575275
theorem B11578115 : Blo 1805604 11578115 := bstep (se 1 (by rfl) ⟨8683586, by rfl⟩ : syracuseStep 11578115 = 17367173) B17367173
theorem B2607967 : Blo 1805604 2607967 := bstep (se 1 (by rfl) ⟨1955975, by rfl⟩ : syracuseStep 2607967 = 3911951) B3911951
theorem B4066235 : Blo 1805604 4066235 := bstep (se 1 (by rfl) ⟨3049676, by rfl⟩ : syracuseStep 4066235 = 6099353) B6099353
theorem B4066361 : Blo 1805604 4066361 := bstep (se 2 (by rfl) ⟨1524885, by rfl⟩ : syracuseStep 4066361 = 3049771) B3049771
theorem B12356687 : Blo 1805604 12356687 := bstep (se 1 (by rfl) ⟨9267515, by rfl⟩ : syracuseStep 12356687 = 18535031) B18535031
theorem B10284185 : Blo 1805604 10284185 := bstep (se 2 (by rfl) ⟨3856569, by rfl⟩ : syracuseStep 10284185 = 7713139) B7713139
theorem B9145547 : Blo 1805604 9145547 := bstep (se 1 (by rfl) ⟨6859160, by rfl⟩ : syracuseStep 9145547 = 13718321) B13718321
theorem B1805607 : Blo 1805604 1805607 := bstep (se 1 (by rfl) ⟨1354205, by rfl⟩ : syracuseStep 1805607 = 2708411) B2708411
theorem B1805647 : Blo 1805604 1805647 := bstep (se 1 (by rfl) ⟨1354235, by rfl⟩ : syracuseStep 1805647 = 2708471) B2708471
theorem B1805663 : Blo 1805604 1805663 := bstep (se 1 (by rfl) ⟨1354247, by rfl⟩ : syracuseStep 1805663 = 2708495) B2708495
theorem B1805691 : Blo 1805604 1805691 := bstep (se 1 (by rfl) ⟨1354268, by rfl⟩ : syracuseStep 1805691 = 2708537) B2708537
theorem B4066703 : Blo 1805604 4066703 := bstep (se 1 (by rfl) ⟨3050027, by rfl⟩ : syracuseStep 4066703 = 6100055) B6100055
theorem B1805743 : Blo 1805604 1805743 := bstep (se 1 (by rfl) ⟨1354307, by rfl⟩ : syracuseStep 1805743 = 2708615) B2708615
theorem B1805767 : Blo 1805604 1805767 := bstep (se 1 (by rfl) ⟨1354325, by rfl⟩ : syracuseStep 1805767 = 2708651) B2708651
theorem B11570633 : Blo 1805604 11570633 := bstep (se 2 (by rfl) ⟨4338987, by rfl⟩ : syracuseStep 11570633 = 8677975) B8677975
theorem B1805787 : Blo 1805604 1805787 := bstep (se 1 (by rfl) ⟨1354340, by rfl⟩ : syracuseStep 1805787 = 2708681) B2708681
theorem B3427849 : Blo 1805604 3427849 := bstep (se 2 (by rfl) ⟨1285443, by rfl⟩ : syracuseStep 3427849 = 2570887) B2570887
theorem B1805863 : Blo 1805604 1805863 := bstep (se 1 (by rfl) ⟨1354397, by rfl⟩ : syracuseStep 1805863 = 2708795) B2708795
theorem B1805903 : Blo 1805604 1805903 := bstep (se 1 (by rfl) ⟨1354427, by rfl⟩ : syracuseStep 1805903 = 2708855) B2708855
theorem B1805919 : Blo 1805604 1805919 := bstep (se 1 (by rfl) ⟨1354439, by rfl⟩ : syracuseStep 1805919 = 2708879) B2708879
theorem B10284641 : Blo 1805604 10284641 := bstep (se 2 (by rfl) ⟨3856740, by rfl⟩ : syracuseStep 10284641 = 7713481) B7713481
theorem B1805947 : Blo 1805604 1805947 := bstep (se 1 (by rfl) ⟨1354460, by rfl⟩ : syracuseStep 1805947 = 2708921) B2708921
theorem B1805999 : Blo 1805604 1805999 := bstep (se 1 (by rfl) ⟨1354499, by rfl⟩ : syracuseStep 1805999 = 2708999) B2708999
theorem B1806023 : Blo 1805604 1806023 := bstep (se 1 (by rfl) ⟨1354517, by rfl⟩ : syracuseStep 1806023 = 2709035) B2709035
theorem B6860497 : Blo 1805604 6860497 := bstep (se 2 (by rfl) ⟨2572686, by rfl⟩ : syracuseStep 6860497 = 5145373) B5145373
theorem B4067027 : Blo 1805604 4067027 := bstep (se 1 (by rfl) ⟨3050270, by rfl⟩ : syracuseStep 4067027 = 6100541) B6100541
theorem B1806043 : Blo 1805604 1806043 := bstep (se 1 (by rfl) ⟨1354532, by rfl⟩ : syracuseStep 1806043 = 2709065) B2709065
theorem B1806119 : Blo 1805604 1806119 := bstep (se 1 (by rfl) ⟨1354589, by rfl⟩ : syracuseStep 1806119 = 2709179) B2709179
theorem B5869385 : Blo 1805604 5869385 := bstep (se 2 (by rfl) ⟨2201019, by rfl⟩ : syracuseStep 5869385 = 4402039) B4402039
theorem B1806159 : Blo 1805604 1806159 := bstep (se 1 (by rfl) ⟨1354619, by rfl⟩ : syracuseStep 1806159 = 2709239) B2709239
theorem B1806175 : Blo 1805604 1806175 := bstep (se 1 (by rfl) ⟨1354631, by rfl⟩ : syracuseStep 1806175 = 2709263) B2709263
theorem B8245111 : Blo 1805604 8245111 := bstep (se 1 (by rfl) ⟨6183833, by rfl⟩ : syracuseStep 8245111 = 12367667) B12367667
theorem B1806203 : Blo 1805604 1806203 := bstep (se 1 (by rfl) ⟨1354652, by rfl⟩ : syracuseStep 1806203 = 2709305) B2709305
theorem B1806255 : Blo 1805604 1806255 := bstep (se 1 (by rfl) ⟨1354691, by rfl⟩ : syracuseStep 1806255 = 2709383) B2709383
theorem B4575163 : Blo 1805604 4575163 := bstep (se 1 (by rfl) ⟨3431372, by rfl⟩ : syracuseStep 4575163 = 6862745) B6862745
theorem B1806279 : Blo 1805604 1806279 := bstep (se 1 (by rfl) ⟨1354709, by rfl⟩ : syracuseStep 1806279 = 2709419) B2709419
theorem B11579345 : Blo 1805604 11579345 := bstep (se 2 (by rfl) ⟨4342254, by rfl⟩ : syracuseStep 11579345 = 8684509) B8684509
theorem B1806299 : Blo 1805604 1806299 := bstep (se 1 (by rfl) ⟨1354724, by rfl⟩ : syracuseStep 1806299 = 2709449) B2709449
theorem B6860801 : Blo 1805604 6860801 := bstep (se 2 (by rfl) ⟨2572800, by rfl⟩ : syracuseStep 6860801 = 5145601) B5145601
theorem B5214215 : Blo 1805604 5214215 := bstep (se 1 (by rfl) ⟨3910661, by rfl⟩ : syracuseStep 5214215 = 7821323) B7821323
theorem B1806375 : Blo 1805604 1806375 := bstep (se 1 (by rfl) ⟨1354781, by rfl⟩ : syracuseStep 1806375 = 2709563) B2709563
theorem B1855567 : Blo 1805604 1855567 := bstep (se 1 (by rfl) ⟨1391675, by rfl⟩ : syracuseStep 1855567 = 2783351) B2783351
theorem B1806415 : Blo 1805604 1806415 := bstep (se 1 (by rfl) ⟨1354811, by rfl⟩ : syracuseStep 1806415 = 2709623) B2709623
theorem B1806431 : Blo 1805604 1806431 := bstep (se 1 (by rfl) ⟨1354823, by rfl⟩ : syracuseStep 1806431 = 2709647) B2709647
theorem B1806459 : Blo 1805604 1806459 := bstep (se 1 (by rfl) ⟨1354844, by rfl⟩ : syracuseStep 1806459 = 2709689) B2709689
theorem B1806511 : Blo 1805604 1806511 := bstep (se 1 (by rfl) ⟨1354883, by rfl⟩ : syracuseStep 1806511 = 2709767) B2709767
theorem B1806535 : Blo 1805604 1806535 := bstep (se 1 (by rfl) ⟨1354901, by rfl⟩ : syracuseStep 1806535 = 2709803) B2709803
theorem B3256519 : Blo 1805604 3256519 := bstep (se 1 (by rfl) ⟨2442389, by rfl⟩ : syracuseStep 3256519 = 4884779) B4884779
theorem B3428563 : Blo 1805604 3428563 := bstep (se 1 (by rfl) ⟨2571422, by rfl⟩ : syracuseStep 3428563 = 5142845) B5142845
theorem B1806555 : Blo 1805604 1806555 := bstep (se 1 (by rfl) ⟨1354916, by rfl⟩ : syracuseStep 1806555 = 2709833) B2709833
theorem B6099191 : Blo 1805604 6099191 := bstep (se 1 (by rfl) ⟨4574393, by rfl⟩ : syracuseStep 6099191 = 9148787) B9148787
theorem B1806631 : Blo 1805604 1806631 := bstep (se 1 (by rfl) ⟨1354973, by rfl⟩ : syracuseStep 1806631 = 2709947) B2709947
theorem B1806671 : Blo 1805604 1806671 := bstep (se 1 (by rfl) ⟨1355003, by rfl⟩ : syracuseStep 1806671 = 2710007) B2710007
theorem B1806687 : Blo 1805604 1806687 := bstep (se 1 (by rfl) ⟨1355015, by rfl⟩ : syracuseStep 1806687 = 2710031) B2710031
theorem B1806715 : Blo 1805604 1806715 := bstep (se 1 (by rfl) ⟨1355036, by rfl⟩ : syracuseStep 1806715 = 2710073) B2710073
theorem B7524733 : Blo 1805604 7524733 := bstep (se 3 (by rfl) ⟨1410887, by rfl⟩ : syracuseStep 7524733 = 2821775) B2821775
theorem B1806767 : Blo 1805604 1806767 := bstep (se 1 (by rfl) ⟨1355075, by rfl⟩ : syracuseStep 1806767 = 2710151) B2710151
theorem B1806791 : Blo 1805604 1806791 := bstep (se 1 (by rfl) ⟨1355093, by rfl⟩ : syracuseStep 1806791 = 2710187) B2710187
theorem B6861257 : Blo 1805604 6861257 := bstep (se 2 (by rfl) ⟨2572971, by rfl⟩ : syracuseStep 6861257 = 5145943) B5145943
theorem B11571659 : Blo 1805604 11571659 := bstep (se 1 (by rfl) ⟨8678744, by rfl⟩ : syracuseStep 11571659 = 17357489) B17357489
theorem B1806811 : Blo 1805604 1806811 := bstep (se 1 (by rfl) ⟨1355108, by rfl⟩ : syracuseStep 1806811 = 2710217) B2710217
theorem B1806887 : Blo 1805604 1806887 := bstep (se 1 (by rfl) ⟨1355165, by rfl⟩ : syracuseStep 1806887 = 2710331) B2710331
theorem B6099515 : Blo 1805604 6099515 := bstep (se 1 (by rfl) ⟨4574636, by rfl⟩ : syracuseStep 6099515 = 9149273) B9149273
theorem B1806927 : Blo 1805604 1806927 := bstep (se 1 (by rfl) ⟨1355195, by rfl⟩ : syracuseStep 1806927 = 2710391) B2710391
theorem B1806943 : Blo 1805604 1806943 := bstep (se 1 (by rfl) ⟨1355207, by rfl⟩ : syracuseStep 1806943 = 2710415) B2710415
theorem B1806971 : Blo 1805604 1806971 := bstep (se 1 (by rfl) ⟨1355228, by rfl⟩ : syracuseStep 1806971 = 2710457) B2710457
theorem B1807023 : Blo 1805604 1807023 := bstep (se 1 (by rfl) ⟨1355267, by rfl⟩ : syracuseStep 1807023 = 2710535) B2710535
theorem B1807047 : Blo 1805604 1807047 := bstep (se 1 (by rfl) ⟨1355285, by rfl⟩ : syracuseStep 1807047 = 2710571) B2710571
theorem B23155409 : Blo 1805604 23155409 := bstep (se 2 (by rfl) ⟨8683278, by rfl⟩ : syracuseStep 23155409 = 17366557) B17366557
theorem B51483347 : Blo 1805604 51483347 := bstep (se 1 (by rfl) ⟨38612510, by rfl⟩ : syracuseStep 51483347 = 77225021) B77225021
theorem B1807067 : Blo 1805604 1807067 := bstep (se 1 (by rfl) ⟨1355300, by rfl⟩ : syracuseStep 1807067 = 2710601) B2710601
theorem B46936847 : Blo 1805604 46936847 := bstep (se 1 (by rfl) ⟨35202635, by rfl⟩ : syracuseStep 46936847 = 70405271) B70405271
theorem B1807143 : Blo 1805604 1807143 := bstep (se 1 (by rfl) ⟨1355357, by rfl⟩ : syracuseStep 1807143 = 2710715) B2710715
theorem B5493577 : Blo 1805604 5493577 := bstep (se 2 (by rfl) ⟨2060091, by rfl⟩ : syracuseStep 5493577 = 4120183) B4120183
theorem B6099785 : Blo 1805604 6099785 := bstep (se 2 (by rfl) ⟨2287419, by rfl⟩ : syracuseStep 6099785 = 4574839) B4574839
theorem B1807183 : Blo 1805604 1807183 := bstep (se 1 (by rfl) ⟨1355387, by rfl⟩ : syracuseStep 1807183 = 2710775) B2710775
theorem B1807199 : Blo 1805604 1807199 := bstep (se 1 (by rfl) ⟨1355399, by rfl⟩ : syracuseStep 1807199 = 2710799) B2710799
theorem B1930079 : Blo 1805604 1930079 := bstep (se 1 (by rfl) ⟨1447559, by rfl⟩ : syracuseStep 1930079 = 2895119) B2895119
theorem B1807227 : Blo 1805604 1807227 := bstep (se 1 (by rfl) ⟨1355420, by rfl⟩ : syracuseStep 1807227 = 2710841) B2710841
theorem B6861743 : Blo 1805604 6861743 := bstep (se 1 (by rfl) ⟨5146307, by rfl⟩ : syracuseStep 6861743 = 10292615) B10292615
theorem B1807279 : Blo 1805604 1807279 := bstep (se 1 (by rfl) ⟨1355459, by rfl⟩ : syracuseStep 1807279 = 2710919) B2710919
theorem B3429307 : Blo 1805604 3429307 := bstep (se 1 (by rfl) ⟨2571980, by rfl⟩ : syracuseStep 3429307 = 5143961) B5143961
theorem B1807303 : Blo 1805604 1807303 := bstep (se 1 (by rfl) ⟨1355477, by rfl⟩ : syracuseStep 1807303 = 2710955) B2710955
theorem B1807323 : Blo 1805604 1807323 := bstep (se 1 (by rfl) ⟨1355492, by rfl⟩ : syracuseStep 1807323 = 2710985) B2710985
theorem B2708489 : Blo 1805604 2708489 := bstep (se 2 (by rfl) ⟨1015683, by rfl⟩ : syracuseStep 2708489 = 2031367) B2031367
theorem B10286099 : Blo 1805604 10286099 := bstep (se 1 (by rfl) ⟨7714574, by rfl⟩ : syracuseStep 10286099 = 15429149) B15429149
theorem B2708519 : Blo 1805604 2708519 := bstep (se 1 (by rfl) ⟨2031389, by rfl⟩ : syracuseStep 2708519 = 4062779) B4062779
theorem B1807399 : Blo 1805604 1807399 := bstep (se 1 (by rfl) ⟨1355549, by rfl⟩ : syracuseStep 1807399 = 2711099) B2711099
theorem B1807439 : Blo 1805604 1807439 := bstep (se 1 (by rfl) ⟨1355579, by rfl⟩ : syracuseStep 1807439 = 2711159) B2711159
theorem B1807455 : Blo 1805604 1807455 := bstep (se 1 (by rfl) ⟨1355591, by rfl⟩ : syracuseStep 1807455 = 2711183) B2711183
theorem B2708603 : Blo 1805604 2708603 := bstep (se 1 (by rfl) ⟨2031452, by rfl⟩ : syracuseStep 2708603 = 4062905) B4062905
theorem B1807483 : Blo 1805604 1807483 := bstep (se 1 (by rfl) ⟨1355612, by rfl⟩ : syracuseStep 1807483 = 2711225) B2711225
theorem B1807535 : Blo 1805604 1807535 := bstep (se 1 (by rfl) ⟨1355651, by rfl⟩ : syracuseStep 1807535 = 2711303) B2711303
theorem B1807559 : Blo 1805604 1807559 := bstep (se 1 (by rfl) ⟨1355669, by rfl⟩ : syracuseStep 1807559 = 2711339) B2711339
theorem B1807579 : Blo 1805604 1807579 := bstep (se 1 (by rfl) ⟨1355684, by rfl⟩ : syracuseStep 1807579 = 2711369) B2711369
theorem B2708729 : Blo 1805604 2708729 := bstep (se 2 (by rfl) ⟨1015773, by rfl⟩ : syracuseStep 2708729 = 2031547) B2031547
theorem B13718807 : Blo 1805604 13718807 := bstep (se 1 (by rfl) ⟨10289105, by rfl⟩ : syracuseStep 13718807 = 20578211) B20578211
theorem B2708831 : Blo 1805604 2708831 := bstep (se 1 (by rfl) ⟨2031623, by rfl⟩ : syracuseStep 2708831 = 4063247) B4063247
theorem B2708843 : Blo 1805604 2708843 := bstep (se 1 (by rfl) ⟨2031632, by rfl⟩ : syracuseStep 2708843 = 4063265) B4063265
theorem B100259207 : Blo 1805604 100259207 := bstep (se 1 (by rfl) ⟨75194405, by rfl⟩ : syracuseStep 100259207 = 150388811) B150388811
theorem B3429793 : Blo 1805604 3429793 := bstep (se 2 (by rfl) ⟨1286172, by rfl⟩ : syracuseStep 3429793 = 2572345) B2572345
theorem B2709071 : Blo 1805604 2709071 := bstep (se 1 (by rfl) ⟨2031803, by rfl⟩ : syracuseStep 2709071 = 4063607) B4063607
theorem B6510269 : Blo 1805604 6510269 := bstep (se 3 (by rfl) ⟨1220675, by rfl⟩ : syracuseStep 6510269 = 2441351) B2441351
theorem B2709191 : Blo 1805604 2709191 := bstep (se 1 (by rfl) ⟨2031893, by rfl⟩ : syracuseStep 2709191 = 4063787) B4063787
theorem B13907771 : Blo 1805604 13907771 := bstep (se 1 (by rfl) ⟨10430828, by rfl⟩ : syracuseStep 13907771 = 20861657) B20861657
theorem B2709353 : Blo 1805604 2709353 := bstep (se 2 (by rfl) ⟨1016007, by rfl⟩ : syracuseStep 2709353 = 2032015) B2032015
theorem B2709431 : Blo 1805604 2709431 := bstep (se 1 (by rfl) ⟨2032073, by rfl⟩ : syracuseStep 2709431 = 4064147) B4064147
theorem B9770939 : Blo 1805604 9770939 := bstep (se 1 (by rfl) ⟨7328204, by rfl⟩ : syracuseStep 9770939 = 14656409) B14656409
theorem B2709467 : Blo 1805604 2709467 := bstep (se 1 (by rfl) ⟨2032100, by rfl⟩ : syracuseStep 2709467 = 4064201) B4064201
theorem B3430363 : Blo 1805604 3430363 := bstep (se 1 (by rfl) ⟨2572772, by rfl⟩ : syracuseStep 3430363 = 5145545) B5145545
theorem B6952979 : Blo 1805604 6952979 := bstep (se 1 (by rfl) ⟨5214734, by rfl⟩ : syracuseStep 6952979 = 10429469) B10429469
theorem B6862927 : Blo 1805604 6862927 := bstep (se 1 (by rfl) ⟨5147195, by rfl⟩ : syracuseStep 6862927 = 10294391) B10294391
theorem B37140569 : Blo 1805604 37140569 := bstep (se 2 (by rfl) ⟨13927713, by rfl⟩ : syracuseStep 37140569 = 27855427) B27855427
theorem B13711517 : Blo 1805604 13711517 := bstep (se 3 (by rfl) ⟨2570909, by rfl⟩ : syracuseStep 13711517 = 5141819) B5141819
theorem B5142685 : Blo 1805604 5142685 := bstep (se 3 (by rfl) ⟨964253, by rfl⟩ : syracuseStep 5142685 = 1928507) B1928507
theorem B2709935 : Blo 1805604 2709935 := bstep (se 1 (by rfl) ⟨2032451, by rfl⟩ : syracuseStep 2709935 = 4064903) B4064903
theorem B5143027 : Blo 1805604 5143027 := bstep (se 1 (by rfl) ⟨3857270, by rfl⟩ : syracuseStep 5143027 = 7714541) B7714541
theorem B2710025 : Blo 1805604 2710025 := bstep (se 2 (by rfl) ⟨1016259, by rfl⟩ : syracuseStep 2710025 = 2032519) B2032519
theorem B12360215 : Blo 1805604 12360215 := bstep (se 1 (by rfl) ⟨9270161, by rfl⟩ : syracuseStep 12360215 = 18540323) B18540323
theorem B13023767 : Blo 1805604 13023767 := bstep (se 1 (by rfl) ⟨9767825, by rfl⟩ : syracuseStep 13023767 = 19535651) B19535651
theorem B2710055 : Blo 1805604 2710055 := bstep (se 1 (by rfl) ⟨2032541, by rfl⟩ : syracuseStep 2710055 = 4065083) B4065083
theorem B18537005 : Blo 1805604 18537005 := bstep (se 3 (by rfl) ⟨3475688, by rfl⟩ : syracuseStep 18537005 = 6951377) B6951377
theorem B2710139 : Blo 1805604 2710139 := bstep (se 1 (by rfl) ⟨2032604, by rfl⟩ : syracuseStep 2710139 = 4065209) B4065209
theorem B13720265 : Blo 1805604 13720265 := bstep (se 2 (by rfl) ⟨5145099, by rfl⟩ : syracuseStep 13720265 = 10290199) B10290199
theorem B21977801 : Blo 1805604 21977801 := bstep (se 2 (by rfl) ⟨8241675, by rfl⟩ : syracuseStep 21977801 = 16483351) B16483351
theorem B2710265 : Blo 1805604 2710265 := bstep (se 2 (by rfl) ⟨1016349, by rfl⟩ : syracuseStep 2710265 = 2032699) B2032699
theorem B2710367 : Blo 1805604 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B2571115 : Blo 1805604 2571115 := bstep (se 1 (by rfl) ⟨1928336, by rfl⟩ : syracuseStep 2571115 = 3856673) B3856673
theorem B2710379 : Blo 1805604 2710379 := bstep (se 1 (by rfl) ⟨2032784, by rfl⟩ : syracuseStep 2710379 = 4065569) B4065569
theorem B4340641 : Blo 1805604 4340641 := bstep (se 2 (by rfl) ⟨1627740, by rfl⟩ : syracuseStep 4340641 = 3255481) B3255481
theorem B11574323 : Blo 1805604 11574323 := bstep (se 1 (by rfl) ⟨8680742, by rfl⟩ : syracuseStep 11574323 = 17361485) B17361485
theorem B2710607 : Blo 1805604 2710607 := bstep (se 1 (by rfl) ⟨2032955, by rfl⟩ : syracuseStep 2710607 = 4065911) B4065911
theorem B3660923 : Blo 1805604 3660923 := bstep (se 1 (by rfl) ⟨2745692, by rfl⟩ : syracuseStep 3660923 = 5491385) B5491385
theorem B2710727 : Blo 1805604 2710727 := bstep (se 1 (by rfl) ⟨2033045, by rfl⟩ : syracuseStep 2710727 = 4066091) B4066091
theorem B5496055 : Blo 1805604 5496055 := bstep (se 1 (by rfl) ⟨4122041, by rfl⟩ : syracuseStep 5496055 = 8244083) B8244083
theorem B2710889 : Blo 1805604 2710889 := bstep (se 2 (by rfl) ⟨1016583, by rfl⟩ : syracuseStep 2710889 = 2033167) B2033167
theorem B6094223 : Blo 1805604 6094223 := bstep (se 1 (by rfl) ⟨4570667, by rfl⟩ : syracuseStep 6094223 = 9141335) B9141335
theorem B2710967 : Blo 1805604 2710967 := bstep (se 1 (by rfl) ⟨2033225, by rfl⟩ : syracuseStep 2710967 = 4066451) B4066451
theorem B5864923 : Blo 1805604 5864923 := bstep (se 1 (by rfl) ⟨4398692, by rfl⟩ : syracuseStep 5864923 = 8797385) B8797385
theorem B2784731 : Blo 1805604 2784731 := bstep (se 1 (by rfl) ⟨2088548, by rfl⟩ : syracuseStep 2784731 = 4177097) B4177097
theorem B2711003 : Blo 1805604 2711003 := bstep (se 1 (by rfl) ⟨2033252, by rfl⟩ : syracuseStep 2711003 = 4066505) B4066505
theorem B4947655 : Blo 1805604 4947655 := bstep (se 1 (by rfl) ⟨3710741, by rfl⟩ : syracuseStep 4947655 = 7421483) B7421483
theorem B6094547 : Blo 1805604 6094547 := bstep (se 1 (by rfl) ⟨4570910, by rfl⟩ : syracuseStep 6094547 = 9141821) B9141821
theorem B3047159 : Blo 1805604 3047159 := bstep (se 1 (by rfl) ⟨2285369, by rfl⟩ : syracuseStep 3047159 = 4570739) B4570739
theorem B5496569 : Blo 1805604 5496569 := bstep (se 2 (by rfl) ⟨2061213, by rfl⟩ : syracuseStep 5496569 = 4122427) B4122427
theorem B6954781 : Blo 1805604 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B4063049 : Blo 1805604 4063049 := bstep (se 2 (by rfl) ⟨1523643, by rfl⟩ : syracuseStep 4063049 = 3047287) B3047287
theorem B10289015 : Blo 1805604 10289015 := bstep (se 1 (by rfl) ⟨7716761, by rfl⟩ : syracuseStep 10289015 = 15433523) B15433523
theorem B6856609 : Blo 1805604 6856609 := bstep (se 2 (by rfl) ⟨2571228, by rfl⟩ : syracuseStep 6856609 = 5142457) B5142457
theorem B4571063 : Blo 1805604 4571063 := bstep (se 1 (by rfl) ⟨3428297, by rfl⟩ : syracuseStep 4571063 = 6856595) B6856595
theorem B5496763 : Blo 1805604 5496763 := bstep (se 1 (by rfl) ⟨4122572, by rfl⟩ : syracuseStep 5496763 = 8245145) B8245145
theorem B4063337 : Blo 1805604 4063337 := bstep (se 2 (by rfl) ⟨1523751, by rfl⟩ : syracuseStep 4063337 = 3047503) B3047503
theorem B9150569 : Blo 1805604 9150569 := bstep (se 2 (by rfl) ⟨3431463, by rfl⟩ : syracuseStep 9150569 = 6862927) B6862927
theorem B6856913 : Blo 1805604 6856913 := bstep (se 2 (by rfl) ⟨2571342, by rfl⟩ : syracuseStep 6856913 = 5142685) B5142685
theorem B2031835 : Blo 1805604 2031835 := bstep (se 1 (by rfl) ⟨1523876, by rfl⟩ : syracuseStep 2031835 = 3047753) B3047753
theorem B4342025 : Blo 1805604 4342025 := bstep (se 2 (by rfl) ⟨1628259, by rfl⟩ : syracuseStep 4342025 = 3256519) B3256519
theorem B4571417 : Blo 1805604 4571417 := bstep (se 2 (by rfl) ⟨1714281, by rfl⟩ : syracuseStep 4571417 = 3428563) B3428563
theorem B6095195 : Blo 1805604 6095195 := bstep (se 1 (by rfl) ⟨4571396, by rfl⟩ : syracuseStep 6095195 = 9142793) B9142793
theorem B9896357 : Blo 1805604 9896357 := bstep (se 4 (by rfl) ⟨927783, by rfl⟩ : syracuseStep 9896357 = 1855567) B1855567
theorem B2032123 : Blo 1805604 2032123 := bstep (se 1 (by rfl) ⟨1524092, by rfl⟩ : syracuseStep 2032123 = 3048185) B3048185
theorem B4571711 : Blo 1805604 4571711 := bstep (se 1 (by rfl) ⟨3428783, by rfl⟩ : syracuseStep 4571711 = 6857567) B6857567
theorem B4063823 : Blo 1805604 4063823 := bstep (se 1 (by rfl) ⟨3047867, by rfl⟩ : syracuseStep 4063823 = 6095735) B6095735
theorem B3048043 : Blo 1805604 3048043 := bstep (se 1 (by rfl) ⟨2286032, by rfl⟩ : syracuseStep 3048043 = 4572065) B4572065
theorem B6857369 : Blo 1805604 6857369 := bstep (se 2 (by rfl) ⟨2571513, by rfl⟩ : syracuseStep 6857369 = 5143027) B5143027
theorem B9142955 : Blo 1805604 9142955 := bstep (se 1 (by rfl) ⟨6857216, by rfl⟩ : syracuseStep 9142955 = 13714433) B13714433
theorem B2032303 : Blo 1805604 2032303 := bstep (se 1 (by rfl) ⟨1524227, by rfl⟩ : syracuseStep 2032303 = 3048455) B3048455
theorem B6857399 : Blo 1805604 6857399 := bstep (se 1 (by rfl) ⟨5143049, by rfl⟩ : syracuseStep 6857399 = 10286099) B10286099
theorem B4063967 : Blo 1805604 4063967 := bstep (se 1 (by rfl) ⟨3047975, by rfl⟩ : syracuseStep 4063967 = 6095951) B6095951
theorem B4571923 : Blo 1805604 4571923 := bstep (se 1 (by rfl) ⟨3428942, by rfl⟩ : syracuseStep 4571923 = 6857885) B6857885
theorem B3048347 : Blo 1805604 3048347 := bstep (se 1 (by rfl) ⟨2286260, by rfl⟩ : syracuseStep 3048347 = 4572521) B4572521
theorem B66839471 : Blo 1805604 66839471 := bstep (se 1 (by rfl) ⟨50129603, by rfl⟩ : syracuseStep 66839471 = 100259207) B100259207
theorem B2032591 : Blo 1805604 2032591 := bstep (se 1 (by rfl) ⟨1524443, by rfl⟩ : syracuseStep 2032591 = 3048887) B3048887
theorem B4064219 : Blo 1805604 4064219 := bstep (se 1 (by rfl) ⟨3048164, by rfl⟩ : syracuseStep 4064219 = 6096329) B6096329
theorem B5948407 : Blo 1805604 5948407 := bstep (se 1 (by rfl) ⟨4461305, by rfl⟩ : syracuseStep 5948407 = 8922611) B8922611
theorem B7324769 : Blo 1805604 7324769 := bstep (se 2 (by rfl) ⟨2746788, by rfl⟩ : syracuseStep 7324769 = 5493577) B5493577
theorem B26051681 : Blo 1805604 26051681 := bstep (se 2 (by rfl) ⟨9769380, by rfl⟩ : syracuseStep 26051681 = 19538761) B19538761
theorem B4064399 : Blo 1805604 4064399 := bstep (se 1 (by rfl) ⟨3048299, by rfl⟩ : syracuseStep 4064399 = 6096599) B6096599
theorem B9143441 : Blo 1805604 9143441 := bstep (se 2 (by rfl) ⟨3428790, by rfl⟩ : syracuseStep 9143441 = 6857581) B6857581
theorem B4572359 : Blo 1805604 4572359 := bstep (se 1 (by rfl) ⟨3429269, by rfl⟩ : syracuseStep 4572359 = 6858539) B6858539
theorem B4064489 : Blo 1805604 4064489 := bstep (se 2 (by rfl) ⟨1524183, by rfl⟩ : syracuseStep 4064489 = 3048367) B3048367
theorem B4572409 : Blo 1805604 4572409 := bstep (se 2 (by rfl) ⟨1714653, by rfl⟩ : syracuseStep 4572409 = 3429307) B3429307
theorem B4064543 : Blo 1805604 4064543 := bstep (se 1 (by rfl) ⟨3048407, by rfl⟩ : syracuseStep 4064543 = 6096815) B6096815
theorem B29312293 : Blo 1805604 29312293 := bstep (se 4 (by rfl) ⟨2748027, by rfl⟩ : syracuseStep 29312293 = 5496055) B5496055
theorem B6096167 : Blo 1805604 6096167 := bstep (se 1 (by rfl) ⟨4572125, by rfl⟩ : syracuseStep 6096167 = 9144251) B9144251
theorem B6513959 : Blo 1805604 6513959 := bstep (se 1 (by rfl) ⟨4885469, by rfl⟩ : syracuseStep 6513959 = 9770939) B9770939
theorem B8242519 : Blo 1805604 8242519 := bstep (se 1 (by rfl) ⟨6181889, by rfl⟩ : syracuseStep 8242519 = 12363779) B12363779
theorem B2032987 : Blo 1805604 2032987 := bstep (se 1 (by rfl) ⟨1524740, by rfl⟩ : syracuseStep 2032987 = 3049481) B3049481
theorem B2033095 : Blo 1805604 2033095 := bstep (se 1 (by rfl) ⟨1524821, by rfl⟩ : syracuseStep 2033095 = 3049643) B3049643
theorem B4065065 : Blo 1805604 4065065 := bstep (se 2 (by rfl) ⟨1524399, by rfl⟩ : syracuseStep 4065065 = 3048799) B3048799
theorem B2033455 : Blo 1805604 2033455 := bstep (se 1 (by rfl) ⟨1525091, by rfl⟩ : syracuseStep 2033455 = 3050183) B3050183
theorem B7718743 : Blo 1805604 7718743 := bstep (se 1 (by rfl) ⟨5789057, by rfl⟩ : syracuseStep 7718743 = 11578115) B11578115
theorem B4573057 : Blo 1805604 4573057 := bstep (se 2 (by rfl) ⟨1714896, by rfl⟩ : syracuseStep 4573057 = 3429793) B3429793
theorem B6097031 : Blo 1805604 6097031 := bstep (se 1 (by rfl) ⟨4572773, by rfl⟩ : syracuseStep 6097031 = 9145547) B9145547
theorem B5146877 : Blo 1805604 5146877 := bstep (se 3 (by rfl) ⟨965039, by rfl⟩ : syracuseStep 5146877 = 1930079) B1930079
theorem B6596873 : Blo 1805604 6596873 := bstep (se 2 (by rfl) ⟨2473827, by rfl⟩ : syracuseStep 6596873 = 4947655) B4947655
theorem B3664379 : Blo 1805604 3664379 := bstep (se 1 (by rfl) ⟨2748284, by rfl⟩ : syracuseStep 3664379 = 5496569) B5496569
theorem B6859343 : Blo 1805604 6859343 := bstep (se 1 (by rfl) ⟨5144507, by rfl⟩ : syracuseStep 6859343 = 10289015) B10289015
theorem B4573817 : Blo 1805604 4573817 := bstep (se 2 (by rfl) ⟨1715181, by rfl⟩ : syracuseStep 4573817 = 3430363) B3430363
theorem B7719563 : Blo 1805604 7719563 := bstep (se 1 (by rfl) ⟨5789672, by rfl⟩ : syracuseStep 7719563 = 11579345) B11579345
theorem B4573867 : Blo 1805604 4573867 := bstep (se 1 (by rfl) ⟨3430400, by rfl⟩ : syracuseStep 4573867 = 6860801) B6860801
theorem B3476143 : Blo 1805604 3476143 := bstep (se 1 (by rfl) ⟨2607107, by rfl⟩ : syracuseStep 3476143 = 5214215) B5214215
theorem B6859511 : Blo 1805604 6859511 := bstep (se 1 (by rfl) ⟨5144633, by rfl⟩ : syracuseStep 6859511 = 10289267) B10289267
theorem B34745111 : Blo 1805604 34745111 := bstep (se 1 (by rfl) ⟨26058833, by rfl⟩ : syracuseStep 34745111 = 52117667) B52117667
theorem B13380385 : Blo 1805604 13380385 := bstep (se 2 (by rfl) ⟨5017644, by rfl⟩ : syracuseStep 13380385 = 10035289) B10035289
theorem B4066127 : Blo 1805604 4066127 := bstep (se 1 (by rfl) ⟨3049595, by rfl⟩ : syracuseStep 4066127 = 6099191) B6099191
theorem B4574171 : Blo 1805604 4574171 := bstep (se 1 (by rfl) ⟨3430628, by rfl⟩ : syracuseStep 4574171 = 6861257) B6861257
theorem B4066343 : Blo 1805604 4066343 := bstep (se 1 (by rfl) ⟨3049757, by rfl⟩ : syracuseStep 4066343 = 6099515) B6099515
theorem B16706699 : Blo 1805604 16706699 := bstep (se 1 (by rfl) ⟨12530024, by rfl⟩ : syracuseStep 16706699 = 25060049) B25060049
theorem B15436939 : Blo 1805604 15436939 := bstep (se 1 (by rfl) ⟨11577704, by rfl⟩ : syracuseStep 15436939 = 23155409) B23155409
theorem B4066523 : Blo 1805604 4066523 := bstep (se 1 (by rfl) ⟨3049892, by rfl⟩ : syracuseStep 4066523 = 6099785) B6099785
theorem B4574495 : Blo 1805604 4574495 := bstep (se 1 (by rfl) ⟨3430871, by rfl⟩ : syracuseStep 4574495 = 6861743) B6861743
theorem B3091751 : Blo 1805604 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B1805659 : Blo 1805604 1805659 := bstep (se 1 (by rfl) ⟨1354244, by rfl⟩ : syracuseStep 1805659 = 2708489) B2708489
theorem B8236385 : Blo 1805604 8236385 := bstep (se 2 (by rfl) ⟨3088644, by rfl⟩ : syracuseStep 8236385 = 6177289) B6177289
theorem B6098273 : Blo 1805604 6098273 := bstep (se 2 (by rfl) ⟨2286852, by rfl⟩ : syracuseStep 6098273 = 4573705) B4573705
theorem B1805679 : Blo 1805604 1805679 := bstep (se 1 (by rfl) ⟨1354259, by rfl⟩ : syracuseStep 1805679 = 2708519) B2708519
theorem B23793041 : Blo 1805604 23793041 := bstep (se 2 (by rfl) ⟨8922390, by rfl⟩ : syracuseStep 23793041 = 17844781) B17844781
theorem B4066721 : Blo 1805604 4066721 := bstep (se 2 (by rfl) ⟨1525020, by rfl⟩ : syracuseStep 4066721 = 3050041) B3050041
theorem B1805735 : Blo 1805604 1805735 := bstep (se 1 (by rfl) ⟨1354301, by rfl⟩ : syracuseStep 1805735 = 2708603) B2708603
theorem B1805819 : Blo 1805604 1805819 := bstep (se 1 (by rfl) ⟨1354364, by rfl⟩ : syracuseStep 1805819 = 2708729) B2708729
theorem B9145871 : Blo 1805604 9145871 := bstep (se 1 (by rfl) ⟨6859403, by rfl⟩ : syracuseStep 9145871 = 13718807) B13718807
theorem B1805887 : Blo 1805604 1805887 := bstep (se 1 (by rfl) ⟨1354415, by rfl⟩ : syracuseStep 1805887 = 2708831) B2708831
theorem B1805895 : Blo 1805604 1805895 := bstep (se 1 (by rfl) ⟨1354421, by rfl⟩ : syracuseStep 1805895 = 2708843) B2708843
theorem B1806047 : Blo 1805604 1806047 := bstep (se 1 (by rfl) ⟨1354535, by rfl⟩ : syracuseStep 1806047 = 2709071) B2709071
theorem B3477289 : Blo 1805604 3477289 := bstep (se 2 (by rfl) ⟨1303983, by rfl⟩ : syracuseStep 3477289 = 2607967) B2607967
theorem B1806127 : Blo 1805604 1806127 := bstep (se 1 (by rfl) ⟨1354595, by rfl⟩ : syracuseStep 1806127 = 2709191) B2709191
theorem B3428153 : Blo 1805604 3428153 := bstep (se 2 (by rfl) ⟨1285557, by rfl⟩ : syracuseStep 3428153 = 2571115) B2571115
theorem B5787521 : Blo 1805604 5787521 := bstep (se 2 (by rfl) ⟨2170320, by rfl⟩ : syracuseStep 5787521 = 4340641) B4340641
theorem B1806235 : Blo 1805604 1806235 := bstep (se 1 (by rfl) ⟨1354676, by rfl⟩ : syracuseStep 1806235 = 2709353) B2709353
theorem B1806287 : Blo 1805604 1806287 := bstep (se 1 (by rfl) ⟨1354715, by rfl⟩ : syracuseStep 1806287 = 2709431) B2709431
theorem B1806311 : Blo 1805604 1806311 := bstep (se 1 (by rfl) ⟨1354733, by rfl⟩ : syracuseStep 1806311 = 2709467) B2709467
theorem B24760379 : Blo 1805604 24760379 := bstep (se 1 (by rfl) ⟨18570284, by rfl⟩ : syracuseStep 24760379 = 37140569) B37140569
theorem B1806623 : Blo 1805604 1806623 := bstep (se 1 (by rfl) ⟨1354967, by rfl⟩ : syracuseStep 1806623 = 2709935) B2709935
theorem B1929511 : Blo 1805604 1929511 := bstep (se 1 (by rfl) ⟨1447133, by rfl⟩ : syracuseStep 1929511 = 2894267) B2894267
theorem B1806683 : Blo 1805604 1806683 := bstep (se 1 (by rfl) ⟨1355012, by rfl⟩ : syracuseStep 1806683 = 2710025) B2710025
theorem B11579755 : Blo 1805604 11579755 := bstep (se 1 (by rfl) ⟨8684816, by rfl⟩ : syracuseStep 11579755 = 17369633) B17369633
theorem B1806703 : Blo 1805604 1806703 := bstep (se 1 (by rfl) ⟨1355027, by rfl⟩ : syracuseStep 1806703 = 2710055) B2710055
theorem B12358003 : Blo 1805604 12358003 := bstep (se 1 (by rfl) ⟨9268502, by rfl⟩ : syracuseStep 12358003 = 18537005) B18537005
theorem B1806759 : Blo 1805604 1806759 := bstep (se 1 (by rfl) ⟨1355069, by rfl⟩ : syracuseStep 1806759 = 2710139) B2710139
theorem B9146843 : Blo 1805604 9146843 := bstep (se 1 (by rfl) ⟨6860132, by rfl⟩ : syracuseStep 9146843 = 13720265) B13720265
theorem B14651867 : Blo 1805604 14651867 := bstep (se 1 (by rfl) ⟨10988900, by rfl⟩ : syracuseStep 14651867 = 21977801) B21977801
theorem B1806843 : Blo 1805604 1806843 := bstep (se 1 (by rfl) ⟨1355132, by rfl⟩ : syracuseStep 1806843 = 2710265) B2710265
theorem B1806911 : Blo 1805604 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B1806919 : Blo 1805604 1806919 := bstep (se 1 (by rfl) ⟨1355189, by rfl⟩ : syracuseStep 1806919 = 2710379) B2710379
theorem B7819897 : Blo 1805604 7819897 := bstep (se 2 (by rfl) ⟨2932461, by rfl⟩ : syracuseStep 7819897 = 5864923) B5864923
theorem B8237791 : Blo 1805604 8237791 := bstep (se 1 (by rfl) ⟨6178343, by rfl⟩ : syracuseStep 8237791 = 12356687) B12356687
theorem B1807071 : Blo 1805604 1807071 := bstep (se 1 (by rfl) ⟨1355303, by rfl⟩ : syracuseStep 1807071 = 2710607) B2710607
theorem B1807151 : Blo 1805604 1807151 := bstep (se 1 (by rfl) ⟨1355363, by rfl⟩ : syracuseStep 1807151 = 2710727) B2710727
theorem B1807259 : Blo 1805604 1807259 := bstep (se 1 (by rfl) ⟨1355444, by rfl⟩ : syracuseStep 1807259 = 2710889) B2710889
theorem B9147329 : Blo 1805604 9147329 := bstep (se 2 (by rfl) ⟨3430248, by rfl⟩ : syracuseStep 9147329 = 6860497) B6860497
theorem B1807311 : Blo 1805604 1807311 := bstep (se 1 (by rfl) ⟨1355483, by rfl⟩ : syracuseStep 1807311 = 2710967) B2710967
theorem B7713755 : Blo 1805604 7713755 := bstep (se 1 (by rfl) ⟨5785316, by rfl⟩ : syracuseStep 7713755 = 11570633) B11570633
theorem B1807335 : Blo 1805604 1807335 := bstep (se 1 (by rfl) ⟨1355501, by rfl⟩ : syracuseStep 1807335 = 2711003) B2711003
theorem B2708699 : Blo 1805604 2708699 := bstep (se 1 (by rfl) ⟨2031524, by rfl⟩ : syracuseStep 2708699 = 4063049) B4063049
theorem B3912923 : Blo 1805604 3912923 := bstep (se 1 (by rfl) ⟨2934692, by rfl⟩ : syracuseStep 3912923 = 5869385) B5869385
theorem B6100217 : Blo 1805604 6100217 := bstep (se 2 (by rfl) ⟨2287581, by rfl⟩ : syracuseStep 6100217 = 4575163) B4575163
theorem B7329017 : Blo 1805604 7329017 := bstep (se 2 (by rfl) ⟨2748381, by rfl⟩ : syracuseStep 7329017 = 5496763) B5496763
theorem B2708873 : Blo 1805604 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B11580833 : Blo 1805604 11580833 := bstep (se 2 (by rfl) ⟨4342812, by rfl⟩ : syracuseStep 11580833 = 8685625) B8685625
theorem B6100487 : Blo 1805604 6100487 := bstep (se 1 (by rfl) ⟨4575365, by rfl⟩ : syracuseStep 6100487 = 9150731) B9150731
theorem B7714439 : Blo 1805604 7714439 := bstep (se 1 (by rfl) ⟨5785829, by rfl⟩ : syracuseStep 7714439 = 11571659) B11571659
theorem B9762461 : Blo 1805604 9762461 := bstep (se 3 (by rfl) ⟨1830461, by rfl⟩ : syracuseStep 9762461 = 3660923) B3660923
theorem B2709227 : Blo 1805604 2709227 := bstep (se 1 (by rfl) ⟨2031920, by rfl⟩ : syracuseStep 2709227 = 4063841) B4063841
theorem B34322231 : Blo 1805604 34322231 := bstep (se 1 (by rfl) ⟨25741673, by rfl⟩ : syracuseStep 34322231 = 51483347) B51483347
theorem B5789495 : Blo 1805604 5789495 := bstep (se 1 (by rfl) ⟨4342121, by rfl⟩ : syracuseStep 5789495 = 8684243) B8684243
theorem B10032977 : Blo 1805604 10032977 := bstep (se 2 (by rfl) ⟨3762366, by rfl⟩ : syracuseStep 10032977 = 7524733) B7524733
theorem B31291231 : Blo 1805604 31291231 := bstep (se 1 (by rfl) ⟨23468423, by rfl⟩ : syracuseStep 31291231 = 46936847) B46936847
theorem B2709455 : Blo 1805604 2709455 := bstep (se 1 (by rfl) ⟨2032091, by rfl⟩ : syracuseStep 2709455 = 4064183) B4064183
theorem B69441623 : Blo 1805604 69441623 := bstep (se 1 (by rfl) ⟨52081217, by rfl⟩ : syracuseStep 69441623 = 104162435) B104162435
theorem B5789981 : Blo 1805604 5789981 := bstep (se 3 (by rfl) ⟨1085621, by rfl⟩ : syracuseStep 5789981 = 2171243) B2171243
theorem B2709851 : Blo 1805604 2709851 := bstep (se 1 (by rfl) ⟨2032388, by rfl⟩ : syracuseStep 2709851 = 4064777) B4064777
theorem B4340179 : Blo 1805604 4340179 := bstep (se 1 (by rfl) ⟨3255134, by rfl⟩ : syracuseStep 4340179 = 6510269) B6510269
theorem B3299795 : Blo 1805604 3299795 := bstep (se 1 (by rfl) ⟨2474846, by rfl⟩ : syracuseStep 3299795 = 4949693) B4949693
theorem B9271847 : Blo 1805604 9271847 := bstep (se 1 (by rfl) ⟨6953885, by rfl⟩ : syracuseStep 9271847 = 13907771) B13907771
theorem B2710079 : Blo 1805604 2710079 := bstep (se 1 (by rfl) ⟨2032559, by rfl⟩ : syracuseStep 2710079 = 4065119) B4065119
theorem B4635319 : Blo 1805604 4635319 := bstep (se 1 (by rfl) ⟨3476489, by rfl⟩ : syracuseStep 4635319 = 6952979) B6952979
theorem B2710199 : Blo 1805604 2710199 := bstep (se 1 (by rfl) ⟨2032649, by rfl⟩ : syracuseStep 2710199 = 4065299) B4065299
theorem B9141011 : Blo 1805604 9141011 := bstep (se 1 (by rfl) ⟨6855758, by rfl⟩ : syracuseStep 9141011 = 13711517) B13711517
theorem B5217043 : Blo 1805604 5217043 := bstep (se 1 (by rfl) ⟨3912782, by rfl⟩ : syracuseStep 5217043 = 7825565) B7825565
theorem B2710427 : Blo 1805604 2710427 := bstep (se 1 (by rfl) ⟨2032820, by rfl⟩ : syracuseStep 2710427 = 4065641) B4065641
theorem B8240143 : Blo 1805604 8240143 := bstep (se 1 (by rfl) ⟨6180107, by rfl⟩ : syracuseStep 8240143 = 12360215) B12360215
theorem B8682511 : Blo 1805604 8682511 := bstep (se 1 (by rfl) ⟨6511883, by rfl⟩ : syracuseStep 8682511 = 13023767) B13023767
theorem B2710823 : Blo 1805604 2710823 := bstep (se 1 (by rfl) ⟨2033117, by rfl⟩ : syracuseStep 2710823 = 4066235) B4066235
theorem B4570465 : Blo 1805604 4570465 := bstep (se 2 (by rfl) ⟨1713924, by rfl⟩ : syracuseStep 4570465 = 3427849) B3427849
theorem B7716215 : Blo 1805604 7716215 := bstep (se 1 (by rfl) ⟨5787161, by rfl⟩ : syracuseStep 7716215 = 11574323) B11574323
theorem B2710907 : Blo 1805604 2710907 := bstep (se 1 (by rfl) ⟨2033180, by rfl⟩ : syracuseStep 2710907 = 4066361) B4066361
theorem B6856123 : Blo 1805604 6856123 := bstep (se 1 (by rfl) ⟨5142092, by rfl⟩ : syracuseStep 6856123 = 10284185) B10284185
theorem B2711033 : Blo 1805604 2711033 := bstep (se 2 (by rfl) ⟨1016637, by rfl⟩ : syracuseStep 2711033 = 2033275) B2033275
theorem B4062815 : Blo 1805604 4062815 := bstep (se 1 (by rfl) ⟨3047111, by rfl⟩ : syracuseStep 4062815 = 6094223) B6094223
theorem B2711135 : Blo 1805604 2711135 := bstep (se 1 (by rfl) ⟨2033351, by rfl⟩ : syracuseStep 2711135 = 4066703) B4066703
theorem B29703797 : Blo 1805604 29703797 := bstep (se 5 (by rfl) ⟨1392365, by rfl⟩ : syracuseStep 29703797 = 2784731) B2784731
theorem B9273041 : Blo 1805604 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B6856427 : Blo 1805604 6856427 := bstep (se 1 (by rfl) ⟨5142320, by rfl⟩ : syracuseStep 6856427 = 10284641) B10284641
theorem B4063031 : Blo 1805604 4063031 := bstep (se 1 (by rfl) ⟨3047273, by rfl⟩ : syracuseStep 4063031 = 6094547) B6094547
theorem B2711351 : Blo 1805604 2711351 := bstep (se 1 (by rfl) ⟨2033513, by rfl⟩ : syracuseStep 2711351 = 4067027) B4067027
theorem B10993481 : Blo 1805604 10993481 := bstep (se 2 (by rfl) ⟨4122555, by rfl⟩ : syracuseStep 10993481 = 8245111) B8245111
theorem B2031439 : Blo 1805604 2031439 := bstep (se 1 (by rfl) ⟨1523579, by rfl⟩ : syracuseStep 2031439 = 3047159) B3047159
theorem B9142145 : Blo 1805604 9142145 := bstep (se 2 (by rfl) ⟨3428304, by rfl⟩ : syracuseStep 9142145 = 6856609) B6856609
theorem B3047375 : Blo 1805604 3047375 := bstep (se 1 (by rfl) ⟨2285531, by rfl⟩ : syracuseStep 3047375 = 4571063) B4571063
theorem B16506919 : Blo 1805604 16506919 := bstep (se 1 (by rfl) ⟨12380189, by rfl⟩ : syracuseStep 16506919 = 24760379) B24760379
theorem B4571275 : Blo 1805604 4571275 := bstep (se 1 (by rfl) ⟨3428456, by rfl⟩ : syracuseStep 4571275 = 6856913) B6856913
theorem B3047611 : Blo 1805604 3047611 := bstep (se 1 (by rfl) ⟨2285708, by rfl⟩ : syracuseStep 3047611 = 4571417) B4571417
theorem B4063463 : Blo 1805604 4063463 := bstep (se 1 (by rfl) ⟨3047597, by rfl⟩ : syracuseStep 4063463 = 6095195) B6095195
theorem B3047807 : Blo 1805604 3047807 := bstep (se 1 (by rfl) ⟨2285855, by rfl⟩ : syracuseStep 3047807 = 4571711) B4571711
theorem B4571579 : Blo 1805604 4571579 := bstep (se 1 (by rfl) ⟨3428684, by rfl⟩ : syracuseStep 4571579 = 6857369) B6857369
theorem B6095303 : Blo 1805604 6095303 := bstep (se 1 (by rfl) ⟨4571477, by rfl⟩ : syracuseStep 6095303 = 9142955) B9142955
theorem B4571599 : Blo 1805604 4571599 := bstep (se 1 (by rfl) ⟨3428699, by rfl⟩ : syracuseStep 4571599 = 6857399) B6857399
theorem B2032231 : Blo 1805604 2032231 := bstep (se 1 (by rfl) ⟨1524173, by rfl⟩ : syracuseStep 2032231 = 3048347) B3048347
theorem B4883179 : Blo 1805604 4883179 := bstep (se 1 (by rfl) ⟨3662384, by rfl⟩ : syracuseStep 4883179 = 7324769) B7324769
theorem B17367787 : Blo 1805604 17367787 := bstep (se 1 (by rfl) ⟨13025840, by rfl⟩ : syracuseStep 17367787 = 26051681) B26051681
theorem B6095627 : Blo 1805604 6095627 := bstep (se 1 (by rfl) ⟨4571720, by rfl⟩ : syracuseStep 6095627 = 9143441) B9143441
theorem B3048239 : Blo 1805604 3048239 := bstep (se 1 (by rfl) ⟨2286179, by rfl⟩ : syracuseStep 3048239 = 4572359) B4572359
theorem B4064057 : Blo 1805604 4064057 := bstep (se 2 (by rfl) ⟨1524021, by rfl⟩ : syracuseStep 4064057 = 3048043) B3048043
theorem B4064111 : Blo 1805604 4064111 := bstep (se 1 (by rfl) ⟨3048083, by rfl⟩ : syracuseStep 4064111 = 6096167) B6096167
theorem B6095897 : Blo 1805604 6095897 := bstep (se 2 (by rfl) ⟨2285961, by rfl⟩ : syracuseStep 6095897 = 4571923) B4571923
theorem B6956057 : Blo 1805604 6956057 := bstep (se 2 (by rfl) ⟨2608521, by rfl⟩ : syracuseStep 6956057 = 5217043) B5217043
theorem B43934885 : Blo 1805604 43934885 := bstep (se 4 (by rfl) ⟨4118895, by rfl⟩ : syracuseStep 43934885 = 8237791) B8237791
theorem B3859663 : Blo 1805604 3859663 := bstep (se 1 (by rfl) ⟨2894747, by rfl⟩ : syracuseStep 3859663 = 5789495) B5789495
theorem B7931209 : Blo 1805604 7931209 := bstep (se 2 (by rfl) ⟨2974203, by rfl⟩ : syracuseStep 7931209 = 5948407) B5948407
theorem B10986857 : Blo 1805604 10986857 := bstep (se 2 (by rfl) ⟨4120071, by rfl⟩ : syracuseStep 10986857 = 8240143) B8240143
theorem B11576681 : Blo 1805604 11576681 := bstep (se 2 (by rfl) ⟨4341255, by rfl⟩ : syracuseStep 11576681 = 8682511) B8682511
theorem B46294415 : Blo 1805604 46294415 := bstep (se 1 (by rfl) ⟨34720811, by rfl⟩ : syracuseStep 46294415 = 69441623) B69441623
theorem B4064687 : Blo 1805604 4064687 := bstep (se 1 (by rfl) ⟨3048515, by rfl⟩ : syracuseStep 4064687 = 6097031) B6097031
theorem B24724925 : Blo 1805604 24724925 := bstep (se 3 (by rfl) ⟨4635923, by rfl⟩ : syracuseStep 24724925 = 9271847) B9271847
theorem B3859987 : Blo 1805604 3859987 := bstep (se 1 (by rfl) ⟨2894990, by rfl⟩ : syracuseStep 3859987 = 5789981) B5789981
theorem B10290725 : Blo 1805604 10290725 := bstep (se 4 (by rfl) ⟨964755, by rfl⟩ : syracuseStep 10290725 = 1929511) B1929511
theorem B6096545 : Blo 1805604 6096545 := bstep (se 2 (by rfl) ⟨2286204, by rfl⟩ : syracuseStep 6096545 = 4572409) B4572409
theorem B4572895 : Blo 1805604 4572895 := bstep (se 1 (by rfl) ⟨3429671, by rfl⟩ : syracuseStep 4572895 = 6859343) B6859343
theorem B3049211 : Blo 1805604 3049211 := bstep (se 1 (by rfl) ⟨2286908, by rfl⟩ : syracuseStep 3049211 = 4573817) B4573817
theorem B4573007 : Blo 1805604 4573007 := bstep (se 1 (by rfl) ⟨3429755, by rfl⟩ : syracuseStep 4573007 = 6859511) B6859511
theorem B3049447 : Blo 1805604 3049447 := bstep (se 1 (by rfl) ⟨2287085, by rfl⟩ : syracuseStep 3049447 = 4574171) B4574171
theorem B3049663 : Blo 1805604 3049663 := bstep (se 1 (by rfl) ⟨2287247, by rfl⟩ : syracuseStep 3049663 = 4574495) B4574495
theorem B5490923 : Blo 1805604 5490923 := bstep (se 1 (by rfl) ⟨4118192, by rfl⟩ : syracuseStep 5490923 = 8236385) B8236385
theorem B4065515 : Blo 1805604 4065515 := bstep (se 1 (by rfl) ⟨3049136, by rfl⟩ : syracuseStep 4065515 = 6098273) B6098273
theorem B15862027 : Blo 1805604 15862027 := bstep (se 1 (by rfl) ⟨11896520, by rfl⟩ : syracuseStep 15862027 = 23793041) B23793041
theorem B6097247 : Blo 1805604 6097247 := bstep (se 1 (by rfl) ⟨4572935, by rfl⟩ : syracuseStep 6097247 = 9145871) B9145871
theorem B19802531 : Blo 1805604 19802531 := bstep (se 1 (by rfl) ⟨14851898, by rfl⟩ : syracuseStep 19802531 = 29703797) B29703797
theorem B10291657 : Blo 1805604 10291657 := bstep (se 2 (by rfl) ⟨3859371, by rfl⟩ : syracuseStep 10291657 = 7718743) B7718743
theorem B6097409 : Blo 1805604 6097409 := bstep (se 2 (by rfl) ⟨2286528, by rfl⟩ : syracuseStep 6097409 = 4573057) B4573057
theorem B2894683 : Blo 1805604 2894683 := bstep (se 1 (by rfl) ⟨2171012, by rfl⟩ : syracuseStep 2894683 = 4342025) B4342025
theorem B6097895 : Blo 1805604 6097895 := bstep (se 1 (by rfl) ⟨4573421, by rfl⟩ : syracuseStep 6097895 = 9146843) B9146843
theorem B16477337 : Blo 1805604 16477337 := bstep (se 2 (by rfl) ⟨6179001, by rfl⟩ : syracuseStep 16477337 = 12358003) B12358003
theorem B5786905 : Blo 1805604 5786905 := bstep (se 2 (by rfl) ⟨2170089, by rfl⟩ : syracuseStep 5786905 = 4340179) B4340179
theorem B44559647 : Blo 1805604 44559647 := bstep (se 1 (by rfl) ⟨33419735, by rfl⟩ : syracuseStep 44559647 = 66839471) B66839471
theorem B6098219 : Blo 1805604 6098219 := bstep (se 1 (by rfl) ⟨4573664, by rfl⟩ : syracuseStep 6098219 = 9147329) B9147329
theorem B17370557 : Blo 1805604 17370557 := bstep (se 3 (by rfl) ⟨3256979, by rfl⟩ : syracuseStep 17370557 = 6513959) B6513959
theorem B1805799 : Blo 1805604 1805799 := bstep (se 1 (by rfl) ⟨1354349, by rfl⟩ : syracuseStep 1805799 = 2708699) B2708699
theorem B2608615 : Blo 1805604 2608615 := bstep (se 1 (by rfl) ⟨1956461, by rfl⟩ : syracuseStep 2608615 = 3912923) B3912923
theorem B4066811 : Blo 1805604 4066811 := bstep (se 1 (by rfl) ⟨3050108, by rfl⟩ : syracuseStep 4066811 = 6100217) B6100217
theorem B4886011 : Blo 1805604 4886011 := bstep (se 1 (by rfl) ⟨3664508, by rfl⟩ : syracuseStep 4886011 = 7329017) B7329017
theorem B6098489 : Blo 1805604 6098489 := bstep (se 2 (by rfl) ⟨2286933, by rfl⟩ : syracuseStep 6098489 = 4573867) B4573867
theorem B6180425 : Blo 1805604 6180425 := bstep (se 2 (by rfl) ⟨2317659, by rfl⟩ : syracuseStep 6180425 = 4635319) B4635319
theorem B1805915 : Blo 1805604 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B7720555 : Blo 1805604 7720555 := bstep (se 1 (by rfl) ⟨5790416, by rfl⟩ : syracuseStep 7720555 = 11580833) B11580833
theorem B4066991 : Blo 1805604 4066991 := bstep (se 1 (by rfl) ⟨3050243, by rfl⟩ : syracuseStep 4066991 = 6100487) B6100487
theorem B26390285 : Blo 1805604 26390285 := bstep (se 3 (by rfl) ⟨4948178, by rfl⟩ : syracuseStep 26390285 = 9896357) B9896357
theorem B6508307 : Blo 1805604 6508307 := bstep (se 1 (by rfl) ⟨4881230, by rfl⟩ : syracuseStep 6508307 = 9762461) B9762461
theorem B1806151 : Blo 1805604 1806151 := bstep (se 1 (by rfl) ⟨1354613, by rfl⟩ : syracuseStep 1806151 = 2709227) B2709227
theorem B6688651 : Blo 1805604 6688651 := bstep (se 1 (by rfl) ⟨5016488, by rfl⟩ : syracuseStep 6688651 = 10032977) B10032977
theorem B39071645 : Blo 1805604 39071645 := bstep (se 3 (by rfl) ⟨7325933, by rfl⟩ : syracuseStep 39071645 = 14651867) B14651867
theorem B1806303 : Blo 1805604 1806303 := bstep (se 1 (by rfl) ⟨1354727, by rfl⟩ : syracuseStep 1806303 = 2709455) B2709455
theorem B20582585 : Blo 1805604 20582585 := bstep (se 2 (by rfl) ⟨7718469, by rfl⟩ : syracuseStep 20582585 = 15436939) B15436939
theorem B1806567 : Blo 1805604 1806567 := bstep (se 1 (by rfl) ⟨1354925, by rfl⟩ : syracuseStep 1806567 = 2709851) B2709851
theorem B2199863 : Blo 1805604 2199863 := bstep (se 1 (by rfl) ⟨1649897, by rfl⟩ : syracuseStep 2199863 = 3299795) B3299795
theorem B1806719 : Blo 1805604 1806719 := bstep (se 1 (by rfl) ⟨1355039, by rfl⟩ : syracuseStep 1806719 = 2710079) B2710079
theorem B10990025 : Blo 1805604 10990025 := bstep (se 2 (by rfl) ⟨4121259, by rfl⟩ : syracuseStep 10990025 = 8242519) B8242519
theorem B1806799 : Blo 1805604 1806799 := bstep (se 1 (by rfl) ⟨1355099, by rfl⟩ : syracuseStep 1806799 = 2710199) B2710199
theorem B23163407 : Blo 1805604 23163407 := bstep (se 1 (by rfl) ⟨17372555, by rfl⟩ : syracuseStep 23163407 = 34745111) B34745111
theorem B1806951 : Blo 1805604 1806951 := bstep (se 1 (by rfl) ⟨1355213, by rfl⟩ : syracuseStep 1806951 = 2710427) B2710427
theorem B11137799 : Blo 1805604 11137799 := bstep (se 1 (by rfl) ⟨8353349, by rfl⟩ : syracuseStep 11137799 = 16706699) B16706699
theorem B91525949 : Blo 1805604 91525949 := bstep (se 3 (by rfl) ⟨17161115, by rfl⟩ : syracuseStep 91525949 = 34322231) B34322231
theorem B1807215 : Blo 1805604 1807215 := bstep (se 1 (by rfl) ⟨1355411, by rfl⟩ : syracuseStep 1807215 = 2710823) B2710823
theorem B2061167 : Blo 1805604 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B1807271 : Blo 1805604 1807271 := bstep (se 1 (by rfl) ⟨1355453, by rfl⟩ : syracuseStep 1807271 = 2710907) B2710907
theorem B1807355 : Blo 1805604 1807355 := bstep (se 1 (by rfl) ⟨1355516, by rfl⟩ : syracuseStep 1807355 = 2711033) B2711033
theorem B2708543 : Blo 1805604 2708543 := bstep (se 1 (by rfl) ⟨2031407, by rfl⟩ : syracuseStep 2708543 = 4062815) B4062815
theorem B1807423 : Blo 1805604 1807423 := bstep (se 1 (by rfl) ⟨1355567, by rfl⟩ : syracuseStep 1807423 = 2711135) B2711135
theorem B2708585 : Blo 1805604 2708585 := bstep (se 2 (by rfl) ⟨1015719, by rfl⟩ : syracuseStep 2708585 = 2031439) B2031439
theorem B6182027 : Blo 1805604 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B2708687 : Blo 1805604 2708687 := bstep (se 1 (by rfl) ⟨2031515, by rfl⟩ : syracuseStep 2708687 = 4063031) B4063031
theorem B1807567 : Blo 1805604 1807567 := bstep (se 1 (by rfl) ⟨1355675, by rfl⟩ : syracuseStep 1807567 = 2711351) B2711351
theorem B7328987 : Blo 1805604 7328987 := bstep (se 1 (by rfl) ⟨5496740, by rfl⟩ : syracuseStep 7328987 = 10993481) B10993481
theorem B2708891 : Blo 1805604 2708891 := bstep (se 1 (by rfl) ⟨2031668, by rfl⟩ : syracuseStep 2708891 = 4063337) B4063337
theorem B6100379 : Blo 1805604 6100379 := bstep (se 1 (by rfl) ⟨4575284, by rfl⟩ : syracuseStep 6100379 = 9150569) B9150569
theorem B2709113 : Blo 1805604 2709113 := bstep (se 2 (by rfl) ⟨1015917, by rfl⟩ : syracuseStep 2709113 = 2031835) B2031835
theorem B2709215 : Blo 1805604 2709215 := bstep (se 1 (by rfl) ⟨2031911, by rfl⟩ : syracuseStep 2709215 = 4063823) B4063823
theorem B15439673 : Blo 1805604 15439673 := bstep (se 2 (by rfl) ⟨5789877, by rfl⟩ : syracuseStep 15439673 = 11579755) B11579755
theorem B2709311 : Blo 1805604 2709311 := bstep (se 1 (by rfl) ⟨2031983, by rfl⟩ : syracuseStep 2709311 = 4063967) B4063967
theorem B5142503 : Blo 1805604 5142503 := bstep (se 1 (by rfl) ⟨3856877, by rfl⟩ : syracuseStep 5142503 = 7713755) B7713755
theorem B2709479 : Blo 1805604 2709479 := bstep (se 1 (by rfl) ⟨2032109, by rfl⟩ : syracuseStep 2709479 = 4064219) B4064219
theorem B2709497 : Blo 1805604 2709497 := bstep (se 2 (by rfl) ⟨1016061, by rfl⟩ : syracuseStep 2709497 = 2032123) B2032123
theorem B2709599 : Blo 1805604 2709599 := bstep (se 1 (by rfl) ⟨2032199, by rfl⟩ : syracuseStep 2709599 = 4064399) B4064399
theorem B2709659 : Blo 1805604 2709659 := bstep (se 1 (by rfl) ⟨2032244, by rfl⟩ : syracuseStep 2709659 = 4064489) B4064489
theorem B10426529 : Blo 1805604 10426529 := bstep (se 2 (by rfl) ⟨3909948, by rfl⟩ : syracuseStep 10426529 = 7819897) B7819897
theorem B2709695 : Blo 1805604 2709695 := bstep (se 1 (by rfl) ⟨2032271, by rfl⟩ : syracuseStep 2709695 = 4064543) B4064543
theorem B4634857 : Blo 1805604 4634857 := bstep (se 2 (by rfl) ⟨1738071, by rfl⟩ : syracuseStep 4634857 = 3476143) B3476143
theorem B2709737 : Blo 1805604 2709737 := bstep (se 2 (by rfl) ⟨1016151, by rfl⟩ : syracuseStep 2709737 = 2032303) B2032303
theorem B17840513 : Blo 1805604 17840513 := bstep (se 2 (by rfl) ⟨6690192, by rfl⟩ : syracuseStep 17840513 = 13380385) B13380385
theorem B5142959 : Blo 1805604 5142959 := bstep (se 1 (by rfl) ⟨3857219, by rfl⟩ : syracuseStep 5142959 = 7714439) B7714439
theorem B2710043 : Blo 1805604 2710043 := bstep (se 1 (by rfl) ⟨2032532, by rfl⟩ : syracuseStep 2710043 = 4065065) B4065065
theorem B2710121 : Blo 1805604 2710121 := bstep (se 2 (by rfl) ⟨1016295, by rfl⟩ : syracuseStep 2710121 = 2032591) B2032591
theorem B9771677 : Blo 1805604 9771677 := bstep (se 3 (by rfl) ⟨1832189, by rfl⟩ : syracuseStep 9771677 = 3664379) B3664379
theorem B3431251 : Blo 1805604 3431251 := bstep (se 1 (by rfl) ⟨2573438, by rfl⟩ : syracuseStep 3431251 = 5146877) B5146877
theorem B4397915 : Blo 1805604 4397915 := bstep (se 1 (by rfl) ⟨3298436, by rfl⟩ : syracuseStep 4397915 = 6596873) B6596873
theorem B20585501 : Blo 1805604 20585501 := bstep (se 3 (by rfl) ⟨3859781, by rfl⟩ : syracuseStep 20585501 = 7719563) B7719563
theorem B39083057 : Blo 1805604 39083057 := bstep (se 2 (by rfl) ⟨14656146, by rfl⟩ : syracuseStep 39083057 = 29312293) B29312293
theorem B2710649 : Blo 1805604 2710649 := bstep (se 2 (by rfl) ⟨1016493, by rfl⟩ : syracuseStep 2710649 = 2032987) B2032987
theorem B6093953 : Blo 1805604 6093953 := bstep (se 2 (by rfl) ⟨2285232, by rfl⟩ : syracuseStep 6093953 = 4570465) B4570465
theorem B6094007 : Blo 1805604 6094007 := bstep (se 1 (by rfl) ⟨4570505, by rfl⟩ : syracuseStep 6094007 = 9141011) B9141011
theorem B2710751 : Blo 1805604 2710751 := bstep (se 1 (by rfl) ⟨2033063, by rfl⟩ : syracuseStep 2710751 = 4066127) B4066127
theorem B9141497 : Blo 1805604 9141497 := bstep (se 2 (by rfl) ⟨3428061, by rfl⟩ : syracuseStep 9141497 = 6856123) B6856123
theorem B2710793 : Blo 1805604 2710793 := bstep (se 2 (by rfl) ⟨1016547, by rfl⟩ : syracuseStep 2710793 = 2033095) B2033095
theorem B2710895 : Blo 1805604 2710895 := bstep (se 1 (by rfl) ⟨2033171, by rfl⟩ : syracuseStep 2710895 = 4066343) B4066343
theorem B2711015 : Blo 1805604 2711015 := bstep (se 1 (by rfl) ⟨2033261, by rfl⟩ : syracuseStep 2711015 = 4066523) B4066523
theorem B5144143 : Blo 1805604 5144143 := bstep (se 1 (by rfl) ⟨3858107, by rfl⟩ : syracuseStep 5144143 = 7716215) B7716215
theorem B2711147 : Blo 1805604 2711147 := bstep (se 1 (by rfl) ⟨2033360, by rfl⟩ : syracuseStep 2711147 = 4066721) B4066721
theorem B4636385 : Blo 1805604 4636385 := bstep (se 2 (by rfl) ⟨1738644, by rfl⟩ : syracuseStep 4636385 = 3477289) B3477289
theorem B2711273 : Blo 1805604 2711273 := bstep (se 2 (by rfl) ⟨1016727, by rfl⟩ : syracuseStep 2711273 = 2033455) B2033455
theorem B41721641 : Blo 1805604 41721641 := bstep (se 2 (by rfl) ⟨15645615, by rfl⟩ : syracuseStep 41721641 = 31291231) B31291231
theorem B4570951 : Blo 1805604 4570951 := bstep (se 1 (by rfl) ⟨3428213, by rfl⟩ : syracuseStep 4570951 = 6856427) B6856427
theorem B2285435 : Blo 1805604 2285435 := bstep (se 1 (by rfl) ⟨1714076, by rfl⟩ : syracuseStep 2285435 = 3428153) B3428153
theorem B6094763 : Blo 1805604 6094763 := bstep (se 1 (by rfl) ⟨4571072, by rfl⟩ : syracuseStep 6094763 = 9142145) B9142145
theorem B3858347 : Blo 1805604 3858347 := bstep (se 1 (by rfl) ⟨2893760, by rfl⟩ : syracuseStep 3858347 = 5787521) B5787521
theorem B2031583 : Blo 1805604 2031583 := bstep (se 1 (by rfl) ⟨1523687, by rfl⟩ : syracuseStep 2031583 = 3047375) B3047375
theorem B13721723 : Blo 1805604 13721723 := bstep (se 1 (by rfl) ⟨10291292, by rfl⟩ : syracuseStep 13721723 = 20582585) B20582585
theorem B6095033 : Blo 1805604 6095033 := bstep (se 2 (by rfl) ⟨2285637, by rfl⟩ : syracuseStep 6095033 = 4571275) B4571275
theorem B4063481 : Blo 1805604 4063481 := bstep (se 2 (by rfl) ⟨1523805, by rfl⟩ : syracuseStep 4063481 = 3047611) B3047611
theorem B2031871 : Blo 1805604 2031871 := bstep (se 1 (by rfl) ⟨1523903, by rfl⟩ : syracuseStep 2031871 = 3047807) B3047807
theorem B3047719 : Blo 1805604 3047719 := bstep (se 1 (by rfl) ⟨2285789, by rfl⟩ : syracuseStep 3047719 = 4571579) B4571579
theorem B4063535 : Blo 1805604 4063535 := bstep (se 1 (by rfl) ⟨3047651, by rfl⟩ : syracuseStep 4063535 = 6095303) B6095303
theorem B15442271 : Blo 1805604 15442271 := bstep (se 1 (by rfl) ⟨11581703, by rfl⟩ : syracuseStep 15442271 = 23163407) B23163407
theorem B4063751 : Blo 1805604 4063751 := bstep (se 1 (by rfl) ⟨3047813, by rfl⟩ : syracuseStep 4063751 = 6095627) B6095627
theorem B2032159 : Blo 1805604 2032159 := bstep (se 1 (by rfl) ⟨1524119, by rfl⟩ : syracuseStep 2032159 = 3048239) B3048239
theorem B13722209 : Blo 1805604 13722209 := bstep (se 2 (by rfl) ⟨5145828, by rfl⟩ : syracuseStep 13722209 = 10291657) B10291657
theorem B6095465 : Blo 1805604 6095465 := bstep (se 2 (by rfl) ⟨2285799, by rfl⟩ : syracuseStep 6095465 = 4571599) B4571599
theorem B4063931 : Blo 1805604 4063931 := bstep (se 1 (by rfl) ⟨3047948, by rfl⟩ : syracuseStep 4063931 = 6095897) B6095897
theorem B4637371 : Blo 1805604 4637371 := bstep (se 1 (by rfl) ⟨3478028, by rfl⟩ : syracuseStep 4637371 = 6956057) B6956057
theorem B4121351 : Blo 1805604 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B5866301 : Blo 1805604 5866301 := bstep (se 3 (by rfl) ⟨1099931, by rfl⟩ : syracuseStep 5866301 = 2199863) B2199863
theorem B7324571 : Blo 1805604 7324571 := bstep (se 1 (by rfl) ⟨5493428, by rfl⟩ : syracuseStep 7324571 = 10986857) B10986857
theorem B7717787 : Blo 1805604 7717787 := bstep (se 1 (by rfl) ⟨5788340, by rfl⟩ : syracuseStep 7717787 = 11576681) B11576681
theorem B16483283 : Blo 1805604 16483283 := bstep (se 1 (by rfl) ⟨12362462, by rfl⟩ : syracuseStep 16483283 = 24724925) B24724925
theorem B4064363 : Blo 1805604 4064363 := bstep (se 1 (by rfl) ⟨3048272, by rfl⟩ : syracuseStep 4064363 = 6096545) B6096545
theorem B3859577 : Blo 1805604 3859577 := bstep (se 2 (by rfl) ⟨1447341, by rfl⟩ : syracuseStep 3859577 = 2894683) B2894683
theorem B2032807 : Blo 1805604 2032807 := bstep (se 1 (by rfl) ⟨1524605, by rfl⟩ : syracuseStep 2032807 = 3049211) B3049211
theorem B3048671 : Blo 1805604 3048671 := bstep (se 1 (by rfl) ⟨2286503, by rfl⟩ : syracuseStep 3048671 = 4573007) B4573007
theorem B4064831 : Blo 1805604 4064831 := bstep (se 1 (by rfl) ⟨3048623, by rfl⟩ : syracuseStep 4064831 = 6097247) B6097247
theorem B5146217 : Blo 1805604 5146217 := bstep (se 2 (by rfl) ⟨1929831, by rfl⟩ : syracuseStep 5146217 = 3859663) B3859663
theorem B4064939 : Blo 1805604 4064939 := bstep (se 1 (by rfl) ⟨3048704, by rfl⟩ : syracuseStep 4064939 = 6097409) B6097409
theorem B6514451 : Blo 1805604 6514451 := bstep (se 1 (by rfl) ⟨4885838, by rfl⟩ : syracuseStep 6514451 = 9771677) B9771677
theorem B4065263 : Blo 1805604 4065263 := bstep (se 1 (by rfl) ⟨3048947, by rfl⟩ : syracuseStep 4065263 = 6097895) B6097895
theorem B6514681 : Blo 1805604 6514681 := bstep (se 2 (by rfl) ⟨2443005, by rfl⟩ : syracuseStep 6514681 = 4886011) B4886011
theorem B13723667 : Blo 1805604 13723667 := bstep (se 1 (by rfl) ⟨10292750, by rfl⟩ : syracuseStep 13723667 = 20585501) B20585501
theorem B5146649 : Blo 1805604 5146649 := bstep (se 2 (by rfl) ⟨1929993, by rfl⟩ : syracuseStep 5146649 = 3859987) B3859987
theorem B6858857 : Blo 1805604 6858857 := bstep (se 2 (by rfl) ⟨2572071, by rfl⟩ : syracuseStep 6858857 = 5144143) B5144143
theorem B29706431 : Blo 1805604 29706431 := bstep (se 1 (by rfl) ⟨22279823, by rfl⟩ : syracuseStep 29706431 = 44559647) B44559647
theorem B4065479 : Blo 1805604 4065479 := bstep (se 1 (by rfl) ⟨3049109, by rfl⟩ : syracuseStep 4065479 = 6098219) B6098219
theorem B6097193 : Blo 1805604 6097193 := bstep (se 2 (by rfl) ⟨2286447, by rfl⟩ : syracuseStep 6097193 = 4572895) B4572895
theorem B4065659 : Blo 1805604 4065659 := bstep (se 1 (by rfl) ⟨3049244, by rfl⟩ : syracuseStep 4065659 = 6098489) B6098489
theorem B3090923 : Blo 1805604 3090923 := bstep (se 1 (by rfl) ⟨2318192, by rfl⟩ : syracuseStep 3090923 = 4636385) B4636385
theorem B27814427 : Blo 1805604 27814427 := bstep (se 1 (by rfl) ⟨20860820, by rfl⟩ : syracuseStep 27814427 = 41721641) B41721641
theorem B4065929 : Blo 1805604 4065929 := bstep (se 2 (by rfl) ⟨1524723, by rfl⟩ : syracuseStep 4065929 = 3049447) B3049447
theorem B4066217 : Blo 1805604 4066217 := bstep (se 2 (by rfl) ⟨1524831, by rfl⟩ : syracuseStep 4066217 = 3049663) B3049663
theorem B7326683 : Blo 1805604 7326683 := bstep (se 1 (by rfl) ⟨5495012, by rfl⟩ : syracuseStep 7326683 = 10990025) B10990025
theorem B6179809 : Blo 1805604 6179809 := bstep (se 2 (by rfl) ⟨2317428, by rfl⟩ : syracuseStep 6179809 = 4634857) B4634857
theorem B7425199 : Blo 1805604 7425199 := bstep (se 1 (by rfl) ⟨5568899, by rfl⟩ : syracuseStep 7425199 = 11137799) B11137799
theorem B61017299 : Blo 1805604 61017299 := bstep (se 1 (by rfl) ⟨45762974, by rfl⟩ : syracuseStep 61017299 = 91525949) B91525949
theorem B14642461 : Blo 1805604 14642461 := bstep (se 3 (by rfl) ⟨2745461, by rfl⟩ : syracuseStep 14642461 = 5490923) B5490923
theorem B1805695 : Blo 1805604 1805695 := bstep (se 1 (by rfl) ⟨1354271, by rfl⟩ : syracuseStep 1805695 = 2708543) B2708543
theorem B1805723 : Blo 1805604 1805723 := bstep (se 1 (by rfl) ⟨1354292, by rfl⟩ : syracuseStep 1805723 = 2708585) B2708585
theorem B29289923 : Blo 1805604 29289923 := bstep (se 1 (by rfl) ⟨21967442, by rfl⟩ : syracuseStep 29289923 = 43934885) B43934885
theorem B1805791 : Blo 1805604 1805791 := bstep (se 1 (by rfl) ⟨1354343, by rfl⟩ : syracuseStep 1805791 = 2708687) B2708687
theorem B4885991 : Blo 1805604 4885991 := bstep (se 1 (by rfl) ⟨3664493, by rfl⟩ : syracuseStep 4885991 = 7328987) B7328987
theorem B30862943 : Blo 1805604 30862943 := bstep (se 1 (by rfl) ⟨23147207, by rfl⟩ : syracuseStep 30862943 = 46294415) B46294415
theorem B1805927 : Blo 1805604 1805927 := bstep (se 1 (by rfl) ⟨1354445, by rfl⟩ : syracuseStep 1805927 = 2708891) B2708891
theorem B4066919 : Blo 1805604 4066919 := bstep (se 1 (by rfl) ⟨3050189, by rfl⟩ : syracuseStep 4066919 = 6100379) B6100379
theorem B47574701 : Blo 1805604 47574701 := bstep (se 3 (by rfl) ⟨8920256, by rfl⟩ : syracuseStep 47574701 = 17840513) B17840513
theorem B6860483 : Blo 1805604 6860483 := bstep (se 1 (by rfl) ⟨5145362, by rfl⟩ : syracuseStep 6860483 = 10290725) B10290725
theorem B1806075 : Blo 1805604 1806075 := bstep (se 1 (by rfl) ⟨1354556, by rfl⟩ : syracuseStep 1806075 = 2709113) B2709113
theorem B4575001 : Blo 1805604 4575001 := bstep (se 2 (by rfl) ⟨1715625, by rfl⟩ : syracuseStep 4575001 = 3431251) B3431251
theorem B1806143 : Blo 1805604 1806143 := bstep (se 1 (by rfl) ⟨1354607, by rfl⟩ : syracuseStep 1806143 = 2709215) B2709215
theorem B10293115 : Blo 1805604 10293115 := bstep (se 1 (by rfl) ⟨7719836, by rfl⟩ : syracuseStep 10293115 = 15439673) B15439673
theorem B1806207 : Blo 1805604 1806207 := bstep (se 1 (by rfl) ⟨1354655, by rfl⟩ : syracuseStep 1806207 = 2709311) B2709311
theorem B3428335 : Blo 1805604 3428335 := bstep (se 1 (by rfl) ⟨2571251, by rfl⟩ : syracuseStep 3428335 = 5142503) B5142503
theorem B1806319 : Blo 1805604 1806319 := bstep (se 1 (by rfl) ⟨1354739, by rfl⟩ : syracuseStep 1806319 = 2709479) B2709479
theorem B1806331 : Blo 1805604 1806331 := bstep (se 1 (by rfl) ⟨1354748, by rfl⟩ : syracuseStep 1806331 = 2709497) B2709497
theorem B1806399 : Blo 1805604 1806399 := bstep (se 1 (by rfl) ⟨1354799, by rfl⟩ : syracuseStep 1806399 = 2709599) B2709599
theorem B1806439 : Blo 1805604 1806439 := bstep (se 1 (by rfl) ⟨1354829, by rfl⟩ : syracuseStep 1806439 = 2709659) B2709659
theorem B6951019 : Blo 1805604 6951019 := bstep (se 1 (by rfl) ⟨5213264, by rfl⟩ : syracuseStep 6951019 = 10426529) B10426529
theorem B1806463 : Blo 1805604 1806463 := bstep (se 1 (by rfl) ⟨1354847, by rfl⟩ : syracuseStep 1806463 = 2709695) B2709695
theorem B1806491 : Blo 1805604 1806491 := bstep (se 1 (by rfl) ⟨1354868, by rfl⟩ : syracuseStep 1806491 = 2709737) B2709737
theorem B13201687 : Blo 1805604 13201687 := bstep (se 1 (by rfl) ⟨9901265, by rfl⟩ : syracuseStep 13201687 = 19802531) B19802531
theorem B3428639 : Blo 1805604 3428639 := bstep (se 1 (by rfl) ⟨2571479, by rfl⟩ : syracuseStep 3428639 = 5142959) B5142959
theorem B1806695 : Blo 1805604 1806695 := bstep (se 1 (by rfl) ⟨1355021, by rfl⟩ : syracuseStep 1806695 = 2710043) B2710043
theorem B1806747 : Blo 1805604 1806747 := bstep (se 1 (by rfl) ⟨1355060, by rfl⟩ : syracuseStep 1806747 = 2710121) B2710121
theorem B3478153 : Blo 1805604 3478153 := bstep (se 2 (by rfl) ⟨1304307, by rfl⟩ : syracuseStep 3478153 = 2608615) B2608615
theorem B26055371 : Blo 1805604 26055371 := bstep (se 1 (by rfl) ⟨19541528, by rfl⟩ : syracuseStep 26055371 = 39083057) B39083057
theorem B17355485 : Blo 1805604 17355485 := bstep (se 3 (by rfl) ⟨3254153, by rfl⟩ : syracuseStep 17355485 = 6508307) B6508307
theorem B1807099 : Blo 1805604 1807099 := bstep (se 1 (by rfl) ⟨1355324, by rfl⟩ : syracuseStep 1807099 = 2710649) B2710649
theorem B10294073 : Blo 1805604 10294073 := bstep (se 2 (by rfl) ⟨3860277, by rfl⟩ : syracuseStep 10294073 = 7720555) B7720555
theorem B1807167 : Blo 1805604 1807167 := bstep (se 1 (by rfl) ⟨1355375, by rfl⟩ : syracuseStep 1807167 = 2710751) B2710751
theorem B1807195 : Blo 1805604 1807195 := bstep (se 1 (by rfl) ⟨1355396, by rfl⟩ : syracuseStep 1807195 = 2710793) B2710793
theorem B11727773 : Blo 1805604 11727773 := bstep (se 3 (by rfl) ⟨2198957, by rfl⟩ : syracuseStep 11727773 = 4397915) B4397915
theorem B1807263 : Blo 1805604 1807263 := bstep (se 1 (by rfl) ⟨1355447, by rfl⟩ : syracuseStep 1807263 = 2710895) B2710895
theorem B11580371 : Blo 1805604 11580371 := bstep (se 1 (by rfl) ⟨8685278, by rfl⟩ : syracuseStep 11580371 = 17370557) B17370557
theorem B1807343 : Blo 1805604 1807343 := bstep (se 1 (by rfl) ⟨1355507, by rfl⟩ : syracuseStep 1807343 = 2711015) B2711015
theorem B1807431 : Blo 1805604 1807431 := bstep (se 1 (by rfl) ⟨1355573, by rfl⟩ : syracuseStep 1807431 = 2711147) B2711147
theorem B1807515 : Blo 1805604 1807515 := bstep (se 1 (by rfl) ⟨1355636, by rfl⟩ : syracuseStep 1807515 = 2711273) B2711273
theorem B17593523 : Blo 1805604 17593523 := bstep (se 1 (by rfl) ⟨13195142, by rfl⟩ : syracuseStep 17593523 = 26390285) B26390285
theorem B8918201 : Blo 1805604 8918201 := bstep (se 2 (by rfl) ⟨3344325, by rfl⟩ : syracuseStep 8918201 = 6688651) B6688651
theorem B26047763 : Blo 1805604 26047763 := bstep (se 1 (by rfl) ⟨19535822, by rfl⟩ : syracuseStep 26047763 = 39071645) B39071645
theorem B2708777 : Blo 1805604 2708777 := bstep (se 2 (by rfl) ⟨1015791, by rfl⟩ : syracuseStep 2708777 = 2031583) B2031583
theorem B2708975 : Blo 1805604 2708975 := bstep (se 1 (by rfl) ⟨2031731, by rfl⟩ : syracuseStep 2708975 = 4063463) B4063463
theorem B88036901 : Blo 1805604 88036901 := bstep (se 4 (by rfl) ⟨8253459, by rfl⟩ : syracuseStep 88036901 = 16506919) B16506919
theorem B21149369 : Blo 1805604 21149369 := bstep (se 2 (by rfl) ⟨7931013, by rfl⟩ : syracuseStep 21149369 = 15862027) B15862027
theorem B2709371 : Blo 1805604 2709371 := bstep (se 1 (by rfl) ⟨2032028, by rfl⟩ : syracuseStep 2709371 = 4064057) B4064057
theorem B2709407 : Blo 1805604 2709407 := bstep (se 1 (by rfl) ⟨2032055, by rfl⟩ : syracuseStep 2709407 = 4064111) B4064111
theorem B2709641 : Blo 1805604 2709641 := bstep (se 2 (by rfl) ⟨1016115, by rfl⟩ : syracuseStep 2709641 = 2032231) B2032231
theorem B2709791 : Blo 1805604 2709791 := bstep (se 1 (by rfl) ⟨2032343, by rfl⟩ : syracuseStep 2709791 = 4064687) B4064687
theorem B6510905 : Blo 1805604 6510905 := bstep (se 2 (by rfl) ⟨2441589, by rfl⟩ : syracuseStep 6510905 = 4883179) B4883179
theorem B23157049 : Blo 1805604 23157049 := bstep (se 2 (by rfl) ⟨8683893, by rfl⟩ : syracuseStep 23157049 = 17367787) B17367787
theorem B2710343 : Blo 1805604 2710343 := bstep (se 1 (by rfl) ⟨2032757, by rfl⟩ : syracuseStep 2710343 = 4065515) B4065515
theorem B7715873 : Blo 1805604 7715873 := bstep (se 2 (by rfl) ⟨2893452, by rfl⟩ : syracuseStep 7715873 = 5786905) B5786905
theorem B10574945 : Blo 1805604 10574945 := bstep (se 2 (by rfl) ⟨3965604, by rfl⟩ : syracuseStep 10574945 = 7931209) B7931209
theorem B4062635 : Blo 1805604 4062635 := bstep (se 1 (by rfl) ⟨3046976, by rfl⟩ : syracuseStep 4062635 = 6093953) B6093953
theorem B10984891 : Blo 1805604 10984891 := bstep (se 1 (by rfl) ⟨8238668, by rfl⟩ : syracuseStep 10984891 = 16477337) B16477337
theorem B4062671 : Blo 1805604 4062671 := bstep (se 1 (by rfl) ⟨3047003, by rfl⟩ : syracuseStep 4062671 = 6094007) B6094007
theorem B6094331 : Blo 1805604 6094331 := bstep (se 1 (by rfl) ⟨4570748, by rfl⟩ : syracuseStep 6094331 = 9141497) B9141497
theorem B5496445 : Blo 1805604 5496445 := bstep (se 3 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 5496445 = 2061167) B2061167
theorem B6094493 : Blo 1805604 6094493 := bstep (se 3 (by rfl) ⟨1142717, by rfl⟩ : syracuseStep 6094493 = 2285435) B2285435
theorem B2711207 : Blo 1805604 2711207 := bstep (se 1 (by rfl) ⟨2033405, by rfl⟩ : syracuseStep 2711207 = 4066811) B4066811
theorem B4120283 : Blo 1805604 4120283 := bstep (se 1 (by rfl) ⟨3090212, by rfl⟩ : syracuseStep 4120283 = 6180425) B6180425
theorem B6094601 : Blo 1805604 6094601 := bstep (se 2 (by rfl) ⟨2285475, by rfl⟩ : syracuseStep 6094601 = 4570951) B4570951
theorem B2711327 : Blo 1805604 2711327 := bstep (se 1 (by rfl) ⟨2033495, by rfl⟩ : syracuseStep 2711327 = 4066991) B4066991
theorem B4063175 : Blo 1805604 4063175 := bstep (se 1 (by rfl) ⟨3047381, by rfl⟩ : syracuseStep 4063175 = 6094763) B6094763
theorem B2572231 : Blo 1805604 2572231 := bstep (se 1 (by rfl) ⟨1929173, by rfl⟩ : syracuseStep 2572231 = 3858347) B3858347
theorem B4063355 : Blo 1805604 4063355 := bstep (se 1 (by rfl) ⟨3047516, by rfl⟩ : syracuseStep 4063355 = 6095033) B6095033
theorem B2285759 : Blo 1805604 2285759 := bstep (se 1 (by rfl) ⟨1714319, by rfl⟩ : syracuseStep 2285759 = 3428639) B3428639
theorem B4063625 : Blo 1805604 4063625 := bstep (se 2 (by rfl) ⟨1523859, by rfl⟩ : syracuseStep 4063625 = 3047719) B3047719
theorem B4063643 : Blo 1805604 4063643 := bstep (se 1 (by rfl) ⟨3047732, by rfl⟩ : syracuseStep 4063643 = 6095465) B6095465
theorem B30876065 : Blo 1805604 30876065 := bstep (se 2 (by rfl) ⟨11578524, by rfl⟩ : syracuseStep 30876065 = 23157049) B23157049
theorem B79217149 : Blo 1805604 79217149 := bstep (se 3 (by rfl) ⟨14853215, by rfl⟩ : syracuseStep 79217149 = 29706431) B29706431
theorem B4883047 : Blo 1805604 4883047 := bstep (se 1 (by rfl) ⟨3662285, by rfl⟩ : syracuseStep 4883047 = 7324571) B7324571
theorem B5145191 : Blo 1805604 5145191 := bstep (se 1 (by rfl) ⟨3858893, by rfl⟩ : syracuseStep 5145191 = 7717787) B7717787
theorem B2573051 : Blo 1805604 2573051 := bstep (se 1 (by rfl) ⟨1929788, by rfl⟩ : syracuseStep 2573051 = 3859577) B3859577
theorem B2032447 : Blo 1805604 2032447 := bstep (se 1 (by rfl) ⟨1524335, by rfl⟩ : syracuseStep 2032447 = 3048671) B3048671
theorem B4637537 : Blo 1805604 4637537 := bstep (se 2 (by rfl) ⟨1739076, by rfl⟩ : syracuseStep 4637537 = 3478153) B3478153
theorem B14099579 : Blo 1805604 14099579 := bstep (se 1 (by rfl) ⟨10574684, by rfl⟩ : syracuseStep 14099579 = 21149369) B21149369
theorem B4342967 : Blo 1805604 4342967 := bstep (se 1 (by rfl) ⟨3257225, by rfl⟩ : syracuseStep 4342967 = 6514451) B6514451
theorem B4572571 : Blo 1805604 4572571 := bstep (se 1 (by rfl) ⟨3429428, by rfl⟩ : syracuseStep 4572571 = 6858857) B6858857
theorem B4064795 : Blo 1805604 4064795 := bstep (se 1 (by rfl) ⟨3048596, by rfl⟩ : syracuseStep 4064795 = 6097193) B6097193
theorem B19523281 : Blo 1805604 19523281 := bstep (se 2 (by rfl) ⟨7321230, by rfl⟩ : syracuseStep 19523281 = 14642461) B14642461
theorem B4884455 : Blo 1805604 4884455 := bstep (se 1 (by rfl) ⟨3663341, by rfl⟩ : syracuseStep 4884455 = 7326683) B7326683
theorem B4573655 : Blo 1805604 4573655 := bstep (se 1 (by rfl) ⟨3430241, by rfl⟩ : syracuseStep 4573655 = 6860483) B6860483
theorem B2746855 : Blo 1805604 2746855 := bstep (se 1 (by rfl) ⟨2060141, by rfl⟩ : syracuseStep 2746855 = 4120283) B4120283
theorem B13724153 : Blo 1805604 13724153 := bstep (se 2 (by rfl) ⟨5146557, by rfl⟩ : syracuseStep 13724153 = 10293115) B10293115
theorem B8686241 : Blo 1805604 8686241 := bstep (se 2 (by rfl) ⟨3257340, by rfl⟩ : syracuseStep 8686241 = 6514681) B6514681
theorem B9268025 : Blo 1805604 9268025 := bstep (se 2 (by rfl) ⟨3475509, by rfl⟩ : syracuseStep 9268025 = 6951019) B6951019
theorem B2747567 : Blo 1805604 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B7818515 : Blo 1805604 7818515 := bstep (se 1 (by rfl) ⟨5863886, by rfl⟩ : syracuseStep 7818515 = 11727773) B11727773
theorem B10988855 : Blo 1805604 10988855 := bstep (se 1 (by rfl) ⟨8241641, by rfl⟩ : syracuseStep 10988855 = 16483283) B16483283
theorem B7720247 : Blo 1805604 7720247 := bstep (se 1 (by rfl) ⟨5790185, by rfl⟩ : syracuseStep 7720247 = 11580371) B11580371
theorem B1805851 : Blo 1805604 1805851 := bstep (se 1 (by rfl) ⟨1354388, by rfl⟩ : syracuseStep 1805851 = 2708777) B2708777
theorem B1805983 : Blo 1805604 1805983 := bstep (se 1 (by rfl) ⟨1354487, by rfl⟩ : syracuseStep 1805983 = 2708975) B2708975
theorem B58691267 : Blo 1805604 58691267 := bstep (se 1 (by rfl) ⟨44018450, by rfl⟩ : syracuseStep 58691267 = 88036901) B88036901
theorem B1806247 : Blo 1805604 1806247 := bstep (se 1 (by rfl) ⟨1354685, by rfl⟩ : syracuseStep 1806247 = 2709371) B2709371
theorem B1806271 : Blo 1805604 1806271 := bstep (se 1 (by rfl) ⟨1354703, by rfl⟩ : syracuseStep 1806271 = 2709407) B2709407
theorem B1806427 : Blo 1805604 1806427 := bstep (se 1 (by rfl) ⟨1354820, by rfl⟩ : syracuseStep 1806427 = 2709641) B2709641
theorem B1806527 : Blo 1805604 1806527 := bstep (se 1 (by rfl) ⟨1354895, by rfl⟩ : syracuseStep 1806527 = 2709791) B2709791
theorem B9900265 : Blo 1805604 9900265 := bstep (se 2 (by rfl) ⟨3712599, by rfl⟩ : syracuseStep 9900265 = 7425199) B7425199
theorem B18542951 : Blo 1805604 18542951 := bstep (se 1 (by rfl) ⟨13907213, by rfl⟩ : syracuseStep 18542951 = 27814427) B27814427
theorem B69480989 : Blo 1805604 69480989 := bstep (se 3 (by rfl) ⟨13027685, by rfl⟩ : syracuseStep 69480989 = 26055371) B26055371
theorem B1806895 : Blo 1805604 1806895 := bstep (se 1 (by rfl) ⟨1355171, by rfl⟩ : syracuseStep 1806895 = 2710343) B2710343
theorem B46281293 : Blo 1805604 46281293 := bstep (se 3 (by rfl) ⟨8677742, by rfl⟩ : syracuseStep 46281293 = 17355485) B17355485
theorem B7049963 : Blo 1805604 7049963 := bstep (se 1 (by rfl) ⟨5287472, by rfl⟩ : syracuseStep 7049963 = 10574945) B10574945
theorem B40678199 : Blo 1805604 40678199 := bstep (se 1 (by rfl) ⟨30508649, by rfl⟩ : syracuseStep 40678199 = 61017299) B61017299
theorem B15643469 : Blo 1805604 15643469 := bstep (se 3 (by rfl) ⟨2933150, by rfl⟩ : syracuseStep 15643469 = 5866301) B5866301
theorem B7328593 : Blo 1805604 7328593 := bstep (se 2 (by rfl) ⟨2748222, by rfl⟩ : syracuseStep 7328593 = 5496445) B5496445
theorem B2708423 : Blo 1805604 2708423 := bstep (se 1 (by rfl) ⟨2031317, by rfl⟩ : syracuseStep 2708423 = 4062635) B4062635
theorem B19526615 : Blo 1805604 19526615 := bstep (se 1 (by rfl) ⟨14644961, by rfl⟩ : syracuseStep 19526615 = 29289923) B29289923
theorem B2708447 : Blo 1805604 2708447 := bstep (se 1 (by rfl) ⟨2031335, by rfl⟩ : syracuseStep 2708447 = 4062671) B4062671
theorem B3257327 : Blo 1805604 3257327 := bstep (se 1 (by rfl) ⟨2442995, by rfl⟩ : syracuseStep 3257327 = 4885991) B4885991
theorem B6100001 : Blo 1805604 6100001 := bstep (se 2 (by rfl) ⟨2287500, by rfl⟩ : syracuseStep 6100001 = 4575001) B4575001
theorem B20575295 : Blo 1805604 20575295 := bstep (se 1 (by rfl) ⟨15431471, by rfl⟩ : syracuseStep 20575295 = 30862943) B30862943
theorem B1807471 : Blo 1805604 1807471 := bstep (se 1 (by rfl) ⟨1355603, by rfl⟩ : syracuseStep 1807471 = 2711207) B2711207
theorem B31716467 : Blo 1805604 31716467 := bstep (se 1 (by rfl) ⟨23787350, by rfl⟩ : syracuseStep 31716467 = 47574701) B47574701
theorem B32969845 : Blo 1805604 32969845 := bstep (se 5 (by rfl) ⟨1545461, by rfl⟩ : syracuseStep 32969845 = 3090923) B3090923
theorem B1807551 : Blo 1805604 1807551 := bstep (se 1 (by rfl) ⟨1355663, by rfl⟩ : syracuseStep 1807551 = 2711327) B2711327
theorem B3429641 : Blo 1805604 3429641 := bstep (se 2 (by rfl) ⟨1286115, by rfl⟩ : syracuseStep 3429641 = 2572231) B2572231
theorem B2708783 : Blo 1805604 2708783 := bstep (se 1 (by rfl) ⟨2031587, by rfl⟩ : syracuseStep 2708783 = 4063175) B4063175
theorem B9147815 : Blo 1805604 9147815 := bstep (se 1 (by rfl) ⟨6860861, by rfl⟩ : syracuseStep 9147815 = 13721723) B13721723
theorem B2708987 : Blo 1805604 2708987 := bstep (se 1 (by rfl) ⟨2031740, by rfl⟩ : syracuseStep 2708987 = 4063481) B4063481
theorem B2709023 : Blo 1805604 2709023 := bstep (se 1 (by rfl) ⟨2031767, by rfl⟩ : syracuseStep 2709023 = 4063535) B4063535
theorem B10294847 : Blo 1805604 10294847 := bstep (se 1 (by rfl) ⟨7721135, by rfl⟩ : syracuseStep 10294847 = 15442271) B15442271
theorem B2709161 : Blo 1805604 2709161 := bstep (se 2 (by rfl) ⟨1015935, by rfl⟩ : syracuseStep 2709161 = 2031871) B2031871
theorem B2709167 : Blo 1805604 2709167 := bstep (se 1 (by rfl) ⟨2031875, by rfl⟩ : syracuseStep 2709167 = 4063751) B4063751
theorem B9148139 : Blo 1805604 9148139 := bstep (se 1 (by rfl) ⟨6861104, by rfl⟩ : syracuseStep 9148139 = 13722209) B13722209
theorem B2709287 : Blo 1805604 2709287 := bstep (se 1 (by rfl) ⟨2031965, by rfl⟩ : syracuseStep 2709287 = 4063931) B4063931
theorem B6862715 : Blo 1805604 6862715 := bstep (se 1 (by rfl) ⟨5147036, by rfl⟩ : syracuseStep 6862715 = 10294073) B10294073
theorem B2709545 : Blo 1805604 2709545 := bstep (se 2 (by rfl) ⟨1016079, by rfl⟩ : syracuseStep 2709545 = 2032159) B2032159
theorem B2709575 : Blo 1805604 2709575 := bstep (se 1 (by rfl) ⟨2032181, by rfl⟩ : syracuseStep 2709575 = 4064363) B4064363
theorem B11729015 : Blo 1805604 11729015 := bstep (se 1 (by rfl) ⟨8796761, by rfl⟩ : syracuseStep 11729015 = 17593523) B17593523
theorem B5945467 : Blo 1805604 5945467 := bstep (se 1 (by rfl) ⟨4459100, by rfl⟩ : syracuseStep 5945467 = 8918201) B8918201
theorem B17365175 : Blo 1805604 17365175 := bstep (se 1 (by rfl) ⟨13023881, by rfl⟩ : syracuseStep 17365175 = 26047763) B26047763
theorem B6183161 : Blo 1805604 6183161 := bstep (se 2 (by rfl) ⟨2318685, by rfl⟩ : syracuseStep 6183161 = 4637371) B4637371
theorem B2709887 : Blo 1805604 2709887 := bstep (se 1 (by rfl) ⟨2032415, by rfl⟩ : syracuseStep 2709887 = 4064831) B4064831
theorem B3430811 : Blo 1805604 3430811 := bstep (se 1 (by rfl) ⟨2573108, by rfl⟩ : syracuseStep 3430811 = 5146217) B5146217
theorem B2709959 : Blo 1805604 2709959 := bstep (se 1 (by rfl) ⟨2032469, by rfl⟩ : syracuseStep 2709959 = 4064939) B4064939
theorem B8239745 : Blo 1805604 8239745 := bstep (se 2 (by rfl) ⟨3089904, by rfl⟩ : syracuseStep 8239745 = 6179809) B6179809
theorem B2710175 : Blo 1805604 2710175 := bstep (se 1 (by rfl) ⟨2032631, by rfl⟩ : syracuseStep 2710175 = 4065263) B4065263
theorem B9149111 : Blo 1805604 9149111 := bstep (se 1 (by rfl) ⟨6861833, by rfl⟩ : syracuseStep 9149111 = 13723667) B13723667
theorem B3431099 : Blo 1805604 3431099 := bstep (se 1 (by rfl) ⟨2573324, by rfl⟩ : syracuseStep 3431099 = 5146649) B5146649
theorem B70408997 : Blo 1805604 70408997 := bstep (se 4 (by rfl) ⟨6600843, by rfl⟩ : syracuseStep 70408997 = 13201687) B13201687
theorem B2710319 : Blo 1805604 2710319 := bstep (se 1 (by rfl) ⟨2032739, by rfl⟩ : syracuseStep 2710319 = 4065479) B4065479
theorem B4340603 : Blo 1805604 4340603 := bstep (se 1 (by rfl) ⟨3255452, by rfl⟩ : syracuseStep 4340603 = 6510905) B6510905
theorem B2710409 : Blo 1805604 2710409 := bstep (se 2 (by rfl) ⟨1016403, by rfl⟩ : syracuseStep 2710409 = 2032807) B2032807
theorem B2710439 : Blo 1805604 2710439 := bstep (se 1 (by rfl) ⟨2032829, by rfl⟩ : syracuseStep 2710439 = 4065659) B4065659
theorem B2710619 : Blo 1805604 2710619 := bstep (se 1 (by rfl) ⟨2032964, by rfl⟩ : syracuseStep 2710619 = 4065929) B4065929
theorem B14646521 : Blo 1805604 14646521 := bstep (se 2 (by rfl) ⟨5492445, by rfl⟩ : syracuseStep 14646521 = 10984891) B10984891
theorem B2710811 : Blo 1805604 2710811 := bstep (se 1 (by rfl) ⟨2033108, by rfl⟩ : syracuseStep 2710811 = 4066217) B4066217
theorem B5143915 : Blo 1805604 5143915 := bstep (se 1 (by rfl) ⟨3857936, by rfl⟩ : syracuseStep 5143915 = 7715873) B7715873
theorem B4062887 : Blo 1805604 4062887 := bstep (se 1 (by rfl) ⟨3047165, by rfl⟩ : syracuseStep 4062887 = 6094331) B6094331
theorem B2711279 : Blo 1805604 2711279 := bstep (se 1 (by rfl) ⟨2033459, by rfl⟩ : syracuseStep 2711279 = 4066919) B4066919
theorem B4062995 : Blo 1805604 4062995 := bstep (se 1 (by rfl) ⟨3047246, by rfl⟩ : syracuseStep 4062995 = 6094493) B6094493
theorem B4063067 : Blo 1805604 4063067 := bstep (se 1 (by rfl) ⟨3047300, by rfl⟩ : syracuseStep 4063067 = 6094601) B6094601
theorem B4571113 : Blo 1805604 4571113 := bstep (se 2 (by rfl) ⟨1714167, by rfl⟩ : syracuseStep 4571113 = 3428335) B3428335
theorem B12361967 : Blo 1805604 12361967 := bstep (se 1 (by rfl) ⟨9271475, by rfl⟩ : syracuseStep 12361967 = 18542951) B18542951
theorem B6095357 : Blo 1805604 6095357 := bstep (se 3 (by rfl) ⟨1142879, by rfl⟩ : syracuseStep 6095357 = 2285759) B2285759
theorem B26042917 : Blo 1805604 26042917 := bstep (se 4 (by rfl) ⟨2441523, by rfl⟩ : syracuseStep 26042917 = 4883047) B4883047
theorem B13017743 : Blo 1805604 13017743 := bstep (se 1 (by rfl) ⟨9763307, by rfl⟩ : syracuseStep 13017743 = 19526615) B19526615
theorem B2171551 : Blo 1805604 2171551 := bstep (se 1 (by rfl) ⟨1628663, by rfl⟩ : syracuseStep 2171551 = 3257327) B3257327
theorem B21144311 : Blo 1805604 21144311 := bstep (se 1 (by rfl) ⟨15858233, by rfl⟩ : syracuseStep 21144311 = 31716467) B31716467
theorem B11576783 : Blo 1805604 11576783 := bstep (se 1 (by rfl) ⟨8682587, by rfl⟩ : syracuseStep 11576783 = 17365175) B17365175
theorem B43959793 : Blo 1805604 43959793 := bstep (se 2 (by rfl) ⟨16484922, by rfl⟩ : syracuseStep 43959793 = 32969845) B32969845
theorem B4122107 : Blo 1805604 4122107 := bstep (se 1 (by rfl) ⟨3091580, by rfl⟩ : syracuseStep 4122107 = 6183161) B6183161
theorem B2287207 : Blo 1805604 2287207 := bstep (se 1 (by rfl) ⟨1715405, by rfl⟩ : syracuseStep 2287207 = 3430811) B3430811
theorem B3049103 : Blo 1805604 3049103 := bstep (se 1 (by rfl) ⟨2286827, by rfl⟩ : syracuseStep 3049103 = 4573655) B4573655
theorem B21972653 : Blo 1805604 21972653 := bstep (se 3 (by rfl) ⟨4119872, by rfl⟩ : syracuseStep 21972653 = 8239745) B8239745
theorem B6858553 : Blo 1805604 6858553 := bstep (se 2 (by rfl) ⟨2571957, by rfl⟩ : syracuseStep 6858553 = 5143915) B5143915
theorem B6096761 : Blo 1805604 6096761 := bstep (se 2 (by rfl) ⟨2286285, by rfl⟩ : syracuseStep 6096761 = 4572571) B4572571
theorem B2893735 : Blo 1805604 2893735 := bstep (se 1 (by rfl) ⟨2170301, by rfl⟩ : syracuseStep 2893735 = 4340603) B4340603
theorem B5212343 : Blo 1805604 5212343 := bstep (se 1 (by rfl) ⟨3909257, by rfl⟩ : syracuseStep 5212343 = 7818515) B7818515
theorem B41715917 : Blo 1805604 41715917 := bstep (se 3 (by rfl) ⟨7821734, by rfl⟩ : syracuseStep 41715917 = 15643469) B15643469
theorem B7325903 : Blo 1805604 7325903 := bstep (se 1 (by rfl) ⟨5494427, by rfl⟩ : syracuseStep 7325903 = 10988855) B10988855
theorem B5146831 : Blo 1805604 5146831 := bstep (se 1 (by rfl) ⟨3860123, by rfl⟩ : syracuseStep 5146831 = 7720247) B7720247
theorem B39127511 : Blo 1805604 39127511 := bstep (se 1 (by rfl) ⟨29345633, by rfl⟩ : syracuseStep 39127511 = 58691267) B58691267
theorem B14649893 : Blo 1805604 14649893 := bstep (se 4 (by rfl) ⟨1373427, by rfl⟩ : syracuseStep 14649893 = 2746855) B2746855
theorem B13200353 : Blo 1805604 13200353 := bstep (se 2 (by rfl) ⟨4950132, by rfl⟩ : syracuseStep 13200353 = 9900265) B9900265
theorem B46320659 : Blo 1805604 46320659 := bstep (se 1 (by rfl) ⟨34740494, by rfl⟩ : syracuseStep 46320659 = 69480989) B69480989
theorem B30854195 : Blo 1805604 30854195 := bstep (se 1 (by rfl) ⟨23140646, by rfl⟩ : syracuseStep 30854195 = 46281293) B46281293
theorem B7326845 : Blo 1805604 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B27118799 : Blo 1805604 27118799 := bstep (se 1 (by rfl) ⟨20339099, by rfl⟩ : syracuseStep 27118799 = 40678199) B40678199
theorem B3091691 : Blo 1805604 3091691 := bstep (se 1 (by rfl) ⟨2318768, by rfl⟩ : syracuseStep 3091691 = 4637537) B4637537
theorem B1805615 : Blo 1805604 1805615 := bstep (se 1 (by rfl) ⟨1354211, by rfl⟩ : syracuseStep 1805615 = 2708423) B2708423
theorem B1805631 : Blo 1805604 1805631 := bstep (se 1 (by rfl) ⟨1354223, by rfl⟩ : syracuseStep 1805631 = 2708447) B2708447
theorem B105622865 : Blo 1805604 105622865 := bstep (se 2 (by rfl) ⟨39608574, by rfl⟩ : syracuseStep 105622865 = 79217149) B79217149
theorem B4066667 : Blo 1805604 4066667 := bstep (se 1 (by rfl) ⟨3050000, by rfl⟩ : syracuseStep 4066667 = 6100001) B6100001
theorem B9145709 : Blo 1805604 9145709 := bstep (se 3 (by rfl) ⟨1714820, by rfl⟩ : syracuseStep 9145709 = 3429641) B3429641
theorem B13716863 : Blo 1805604 13716863 := bstep (se 1 (by rfl) ⟨10287647, by rfl⟩ : syracuseStep 13716863 = 20575295) B20575295
theorem B9399719 : Blo 1805604 9399719 := bstep (se 1 (by rfl) ⟨7049789, by rfl⟩ : syracuseStep 9399719 = 14099579) B14099579
theorem B2895311 : Blo 1805604 2895311 := bstep (se 1 (by rfl) ⟨2171483, by rfl⟩ : syracuseStep 2895311 = 4342967) B4342967
theorem B1805855 : Blo 1805604 1805855 := bstep (se 1 (by rfl) ⟨1354391, by rfl⟩ : syracuseStep 1805855 = 2708783) B2708783
theorem B6098543 : Blo 1805604 6098543 := bstep (se 1 (by rfl) ⟨4573907, by rfl⟩ : syracuseStep 6098543 = 9147815) B9147815
theorem B1805991 : Blo 1805604 1805991 := bstep (se 1 (by rfl) ⟨1354493, by rfl⟩ : syracuseStep 1805991 = 2708987) B2708987
theorem B1806015 : Blo 1805604 1806015 := bstep (se 1 (by rfl) ⟨1354511, by rfl⟩ : syracuseStep 1806015 = 2709023) B2709023
theorem B1806107 : Blo 1805604 1806107 := bstep (se 1 (by rfl) ⟨1354580, by rfl⟩ : syracuseStep 1806107 = 2709161) B2709161
theorem B1806111 : Blo 1805604 1806111 := bstep (se 1 (by rfl) ⟨1354583, by rfl⟩ : syracuseStep 1806111 = 2709167) B2709167
theorem B6098759 : Blo 1805604 6098759 := bstep (se 1 (by rfl) ⟨4574069, by rfl⟩ : syracuseStep 6098759 = 9148139) B9148139
theorem B1806191 : Blo 1805604 1806191 := bstep (se 1 (by rfl) ⟨1354643, by rfl⟩ : syracuseStep 1806191 = 2709287) B2709287
theorem B4575143 : Blo 1805604 4575143 := bstep (se 1 (by rfl) ⟨3431357, by rfl⟩ : syracuseStep 4575143 = 6862715) B6862715
theorem B3256303 : Blo 1805604 3256303 := bstep (se 1 (by rfl) ⟨2442227, by rfl⟩ : syracuseStep 3256303 = 4884455) B4884455
theorem B1806363 : Blo 1805604 1806363 := bstep (se 1 (by rfl) ⟨1354772, by rfl⟩ : syracuseStep 1806363 = 2709545) B2709545
theorem B1806383 : Blo 1805604 1806383 := bstep (se 1 (by rfl) ⟨1354787, by rfl⟩ : syracuseStep 1806383 = 2709575) B2709575
theorem B7819343 : Blo 1805604 7819343 := bstep (se 1 (by rfl) ⟨5864507, by rfl⟩ : syracuseStep 7819343 = 11729015) B11729015
theorem B1806591 : Blo 1805604 1806591 := bstep (se 1 (by rfl) ⟨1354943, by rfl⟩ : syracuseStep 1806591 = 2709887) B2709887
theorem B1806639 : Blo 1805604 1806639 := bstep (se 1 (by rfl) ⟨1354979, by rfl⟩ : syracuseStep 1806639 = 2709959) B2709959
theorem B1806783 : Blo 1805604 1806783 := bstep (se 1 (by rfl) ⟨1355087, by rfl⟩ : syracuseStep 1806783 = 2710175) B2710175
theorem B6099407 : Blo 1805604 6099407 := bstep (se 1 (by rfl) ⟨4574555, by rfl⟩ : syracuseStep 6099407 = 9149111) B9149111
theorem B1806879 : Blo 1805604 1806879 := bstep (se 1 (by rfl) ⟨1355159, by rfl⟩ : syracuseStep 1806879 = 2710319) B2710319
theorem B1806939 : Blo 1805604 1806939 := bstep (se 1 (by rfl) ⟨1355204, by rfl⟩ : syracuseStep 1806939 = 2710409) B2710409
theorem B1806959 : Blo 1805604 1806959 := bstep (se 1 (by rfl) ⟨1355219, by rfl⟩ : syracuseStep 1806959 = 2710439) B2710439
theorem B6861469 : Blo 1805604 6861469 := bstep (se 3 (by rfl) ⟨1286525, by rfl⟩ : syracuseStep 6861469 = 2573051) B2573051
theorem B1807079 : Blo 1805604 1807079 := bstep (se 1 (by rfl) ⟨1355309, by rfl⟩ : syracuseStep 1807079 = 2710619) B2710619
theorem B1807207 : Blo 1805604 1807207 := bstep (se 1 (by rfl) ⟨1355405, by rfl⟩ : syracuseStep 1807207 = 2710811) B2710811
theorem B26031041 : Blo 1805604 26031041 := bstep (se 2 (by rfl) ⟨9761640, by rfl⟩ : syracuseStep 26031041 = 19523281) B19523281
theorem B2708591 : Blo 1805604 2708591 := bstep (se 1 (by rfl) ⟨2031443, by rfl⟩ : syracuseStep 2708591 = 4062887) B4062887
theorem B1807519 : Blo 1805604 1807519 := bstep (se 1 (by rfl) ⟨1355639, by rfl⟩ : syracuseStep 1807519 = 2711279) B2711279
theorem B2708663 : Blo 1805604 2708663 := bstep (se 1 (by rfl) ⟨2031497, by rfl⟩ : syracuseStep 2708663 = 4062995) B4062995
theorem B2708711 : Blo 1805604 2708711 := bstep (se 1 (by rfl) ⟨2031533, by rfl⟩ : syracuseStep 2708711 = 4063067) B4063067
theorem B2708903 : Blo 1805604 2708903 := bstep (se 1 (by rfl) ⟨2031677, by rfl⟩ : syracuseStep 2708903 = 4063355) B4063355
theorem B7927289 : Blo 1805604 7927289 := bstep (se 2 (by rfl) ⟨2972733, by rfl⟩ : syracuseStep 7927289 = 5945467) B5945467
theorem B2709083 : Blo 1805604 2709083 := bstep (se 1 (by rfl) ⟨2031812, by rfl⟩ : syracuseStep 2709083 = 4063625) B4063625
theorem B2709095 : Blo 1805604 2709095 := bstep (se 1 (by rfl) ⟨2031821, by rfl⟩ : syracuseStep 2709095 = 4063643) B4063643
theorem B20584043 : Blo 1805604 20584043 := bstep (se 1 (by rfl) ⟨15438032, by rfl⟩ : syracuseStep 20584043 = 30876065) B30876065
theorem B3430127 : Blo 1805604 3430127 := bstep (se 1 (by rfl) ⟨2572595, by rfl⟩ : syracuseStep 3430127 = 5145191) B5145191
theorem B2709863 : Blo 1805604 2709863 := bstep (se 1 (by rfl) ⟨2032397, by rfl⟩ : syracuseStep 2709863 = 4064795) B4064795
theorem B6863231 : Blo 1805604 6863231 := bstep (se 1 (by rfl) ⟨5147423, by rfl⟩ : syracuseStep 6863231 = 10294847) B10294847
theorem B2709929 : Blo 1805604 2709929 := bstep (se 2 (by rfl) ⟨1016223, by rfl⟩ : syracuseStep 2709929 = 2032447) B2032447
theorem B9771457 : Blo 1805604 9771457 := bstep (se 2 (by rfl) ⟨3664296, by rfl⟩ : syracuseStep 9771457 = 7328593) B7328593
theorem B9149435 : Blo 1805604 9149435 := bstep (se 1 (by rfl) ⟨6862076, by rfl⟩ : syracuseStep 9149435 = 13724153) B13724153
theorem B5790827 : Blo 1805604 5790827 := bstep (se 1 (by rfl) ⟨4343120, by rfl⟩ : syracuseStep 5790827 = 8686241) B8686241
theorem B9149597 : Blo 1805604 9149597 := bstep (se 3 (by rfl) ⟨1715549, by rfl⟩ : syracuseStep 9149597 = 3431099) B3431099
theorem B46939331 : Blo 1805604 46939331 := bstep (se 1 (by rfl) ⟨35204498, by rfl⟩ : syracuseStep 46939331 = 70408997) B70408997
theorem B18799901 : Blo 1805604 18799901 := bstep (se 3 (by rfl) ⟨3524981, by rfl⟩ : syracuseStep 18799901 = 7049963) B7049963
theorem B24714733 : Blo 1805604 24714733 := bstep (se 3 (by rfl) ⟨4634012, by rfl⟩ : syracuseStep 24714733 = 9268025) B9268025
theorem B9764347 : Blo 1805604 9764347 := bstep (se 1 (by rfl) ⟨7323260, by rfl⟩ : syracuseStep 9764347 = 14646521) B14646521
theorem B6094817 : Blo 1805604 6094817 := bstep (se 2 (by rfl) ⟨2285556, by rfl⟩ : syracuseStep 6094817 = 4571113) B4571113
theorem B8241311 : Blo 1805604 8241311 := bstep (se 1 (by rfl) ⟨6180983, by rfl⟩ : syracuseStep 8241311 = 12361967) B12361967
theorem B4063571 : Blo 1805604 4063571 := bstep (se 1 (by rfl) ⟨3047678, by rfl⟩ : syracuseStep 4063571 = 6095357) B6095357
theorem B7717855 : Blo 1805604 7717855 := bstep (se 1 (by rfl) ⟨5788391, by rfl⟩ : syracuseStep 7717855 = 11576783) B11576783
theorem B13722695 : Blo 1805604 13722695 := bstep (se 1 (by rfl) ⟨10292021, by rfl⟩ : syracuseStep 13722695 = 20584043) B20584043
theorem B2032735 : Blo 1805604 2032735 := bstep (se 1 (by rfl) ⟨1524551, by rfl⟩ : syracuseStep 2032735 = 3049103) B3049103
theorem B14648435 : Blo 1805604 14648435 := bstep (se 1 (by rfl) ⟨10986326, by rfl⟩ : syracuseStep 14648435 = 21972653) B21972653
theorem B4064507 : Blo 1805604 4064507 := bstep (se 1 (by rfl) ⟨3048380, by rfl⟩ : syracuseStep 4064507 = 6096761) B6096761
theorem B3474895 : Blo 1805604 3474895 := bstep (se 1 (by rfl) ⟨2606171, by rfl⟩ : syracuseStep 3474895 = 5212343) B5212343
theorem B26085007 : Blo 1805604 26085007 := bstep (se 1 (by rfl) ⟨19563755, by rfl⟩ : syracuseStep 26085007 = 39127511) B39127511
theorem B9766595 : Blo 1805604 9766595 := bstep (se 1 (by rfl) ⟨7324946, by rfl⟩ : syracuseStep 9766595 = 14649893) B14649893
theorem B8800235 : Blo 1805604 8800235 := bstep (se 1 (by rfl) ⟨6600176, by rfl⟩ : syracuseStep 8800235 = 13200353) B13200353
theorem B13019129 : Blo 1805604 13019129 := bstep (se 2 (by rfl) ⟨4882173, by rfl⟩ : syracuseStep 13019129 = 9764347) B9764347
theorem B3860551 : Blo 1805604 3860551 := bstep (se 1 (by rfl) ⟨2895413, by rfl⟩ : syracuseStep 3860551 = 5790827) B5790827
theorem B4884563 : Blo 1805604 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B3049609 : Blo 1805604 3049609 := bstep (se 2 (by rfl) ⟨1143603, by rfl⟩ : syracuseStep 3049609 = 2287207) B2287207
theorem B6097139 : Blo 1805604 6097139 := bstep (se 1 (by rfl) ⟨4572854, by rfl⟩ : syracuseStep 6097139 = 9145709) B9145709
theorem B9144575 : Blo 1805604 9144575 := bstep (se 1 (by rfl) ⟨6858431, by rfl⟩ : syracuseStep 9144575 = 13716863) B13716863
theorem B4065695 : Blo 1805604 4065695 := bstep (se 1 (by rfl) ⟨3049271, by rfl⟩ : syracuseStep 4065695 = 6098543) B6098543
theorem B9144737 : Blo 1805604 9144737 := bstep (se 2 (by rfl) ⟨3429276, by rfl⟩ : syracuseStep 9144737 = 6858553) B6858553
theorem B4065839 : Blo 1805604 4065839 := bstep (se 1 (by rfl) ⟨3049379, by rfl⟩ : syracuseStep 4065839 = 6098759) B6098759
theorem B3050095 : Blo 1805604 3050095 := bstep (se 1 (by rfl) ⟨2287571, by rfl⟩ : syracuseStep 3050095 = 4575143) B4575143
theorem B5212895 : Blo 1805604 5212895 := bstep (se 1 (by rfl) ⟨3909671, by rfl⟩ : syracuseStep 5212895 = 7819343) B7819343
theorem B4066271 : Blo 1805604 4066271 := bstep (se 1 (by rfl) ⟨3049703, by rfl⟩ : syracuseStep 4066271 = 6099407) B6099407
theorem B8678495 : Blo 1805604 8678495 := bstep (se 1 (by rfl) ⟨6508871, by rfl⟩ : syracuseStep 8678495 = 13017743) B13017743
theorem B13028609 : Blo 1805604 13028609 := bstep (se 2 (by rfl) ⟨4885728, by rfl⟩ : syracuseStep 13028609 = 9771457) B9771457
theorem B17354027 : Blo 1805604 17354027 := bstep (se 1 (by rfl) ⟨13015520, by rfl⟩ : syracuseStep 17354027 = 26031041) B26031041
theorem B1805727 : Blo 1805604 1805727 := bstep (se 1 (by rfl) ⟨1354295, by rfl⟩ : syracuseStep 1805727 = 2708591) B2708591
theorem B1805775 : Blo 1805604 1805775 := bstep (se 1 (by rfl) ⟨1354331, by rfl⟩ : syracuseStep 1805775 = 2708663) B2708663
theorem B1805807 : Blo 1805604 1805807 := bstep (se 1 (by rfl) ⟨1354355, by rfl⟩ : syracuseStep 1805807 = 2708711) B2708711
theorem B2895401 : Blo 1805604 2895401 := bstep (se 2 (by rfl) ⟨1085775, by rfl⟩ : syracuseStep 2895401 = 2171551) B2171551
theorem B1805935 : Blo 1805604 1805935 := bstep (se 1 (by rfl) ⟨1354451, by rfl⟩ : syracuseStep 1805935 = 2708903) B2708903
theorem B2748071 : Blo 1805604 2748071 := bstep (se 1 (by rfl) ⟨2061053, by rfl⟩ : syracuseStep 2748071 = 4122107) B4122107
theorem B1806055 : Blo 1805604 1806055 := bstep (se 1 (by rfl) ⟨1354541, by rfl⟩ : syracuseStep 1806055 = 2709083) B2709083
theorem B1806063 : Blo 1805604 1806063 := bstep (se 1 (by rfl) ⟨1354547, by rfl⟩ : syracuseStep 1806063 = 2709095) B2709095
theorem B7720829 : Blo 1805604 7720829 := bstep (se 3 (by rfl) ⟨1447655, by rfl⟩ : syracuseStep 7720829 = 2895311) B2895311
theorem B1806575 : Blo 1805604 1806575 := bstep (se 1 (by rfl) ⟨1354931, by rfl⟩ : syracuseStep 1806575 = 2709863) B2709863
theorem B4575487 : Blo 1805604 4575487 := bstep (se 1 (by rfl) ⟨3431615, by rfl⟩ : syracuseStep 4575487 = 6863231) B6863231
theorem B1806619 : Blo 1805604 1806619 := bstep (se 1 (by rfl) ⟨1354964, by rfl⟩ : syracuseStep 1806619 = 2709929) B2709929
theorem B9147005 : Blo 1805604 9147005 := bstep (se 3 (by rfl) ⟨1715063, by rfl⟩ : syracuseStep 9147005 = 3430127) B3430127
theorem B32952977 : Blo 1805604 32952977 := bstep (se 2 (by rfl) ⟨12357366, by rfl⟩ : syracuseStep 32952977 = 24714733) B24714733
theorem B6099623 : Blo 1805604 6099623 := bstep (se 1 (by rfl) ⟨4574717, by rfl⟩ : syracuseStep 6099623 = 9149435) B9149435
theorem B30880439 : Blo 1805604 30880439 := bstep (se 1 (by rfl) ⟨23160329, by rfl⟩ : syracuseStep 30880439 = 46320659) B46320659
theorem B6099731 : Blo 1805604 6099731 := bstep (se 1 (by rfl) ⟨4574798, by rfl⟩ : syracuseStep 6099731 = 9149597) B9149597
theorem B2061127 : Blo 1805604 2061127 := bstep (se 1 (by rfl) ⟨1545845, by rfl⟩ : syracuseStep 2061127 = 3091691) B3091691
theorem B70415243 : Blo 1805604 70415243 := bstep (se 1 (by rfl) ⟨52811432, by rfl⟩ : syracuseStep 70415243 = 105622865) B105622865
theorem B6862441 : Blo 1805604 6862441 := bstep (se 2 (by rfl) ⟨2573415, by rfl⟩ : syracuseStep 6862441 = 5146831) B5146831
theorem B14096207 : Blo 1805604 14096207 := bstep (se 1 (by rfl) ⟨10572155, by rfl⟩ : syracuseStep 14096207 = 21144311) B21144311
theorem B19535741 : Blo 1805604 19535741 := bstep (se 3 (by rfl) ⟨3662951, by rfl⟩ : syracuseStep 19535741 = 7325903) B7325903
theorem B34723889 : Blo 1805604 34723889 := bstep (se 2 (by rfl) ⟨13021458, by rfl⟩ : syracuseStep 34723889 = 26042917) B26042917
theorem B9148625 : Blo 1805604 9148625 := bstep (se 2 (by rfl) ⟨3430734, by rfl⟩ : syracuseStep 9148625 = 6861469) B6861469
theorem B27810611 : Blo 1805604 27810611 := bstep (se 1 (by rfl) ⟨20857958, by rfl⟩ : syracuseStep 27810611 = 41715917) B41715917
theorem B58613057 : Blo 1805604 58613057 := bstep (se 2 (by rfl) ⟨21979896, by rfl⟩ : syracuseStep 58613057 = 43959793) B43959793
theorem B20569463 : Blo 1805604 20569463 := bstep (se 1 (by rfl) ⟨15427097, by rfl⟩ : syracuseStep 20569463 = 30854195) B30854195
theorem B31292887 : Blo 1805604 31292887 := bstep (se 1 (by rfl) ⟨23469665, by rfl⟩ : syracuseStep 31292887 = 46939331) B46939331
theorem B18079199 : Blo 1805604 18079199 := bstep (se 1 (by rfl) ⟨13559399, by rfl⟩ : syracuseStep 18079199 = 27118799) B27118799
theorem B12533267 : Blo 1805604 12533267 := bstep (se 1 (by rfl) ⟨9399950, by rfl⟩ : syracuseStep 12533267 = 18799901) B18799901
theorem B2711111 : Blo 1805604 2711111 := bstep (se 1 (by rfl) ⟨2033333, by rfl⟩ : syracuseStep 2711111 = 4066667) B4066667
theorem B6266479 : Blo 1805604 6266479 := bstep (se 1 (by rfl) ⟨4699859, by rfl⟩ : syracuseStep 6266479 = 9399719) B9399719
theorem B3858313 : Blo 1805604 3858313 := bstep (se 2 (by rfl) ⟨1446867, by rfl⟩ : syracuseStep 3858313 = 2893735) B2893735
theorem B84557749 : Blo 1805604 84557749 := bstep (se 5 (by rfl) ⟨3963644, by rfl⟩ : syracuseStep 84557749 = 7927289) B7927289
theorem B4341737 : Blo 1805604 4341737 := bstep (se 2 (by rfl) ⟨1628151, by rfl⟩ : syracuseStep 4341737 = 3256303) B3256303
theorem B4063211 : Blo 1805604 4063211 := bstep (se 1 (by rfl) ⟨3047408, by rfl⟩ : syracuseStep 4063211 = 6094817) B6094817
theorem B20586959 : Blo 1805604 20586959 := bstep (se 1 (by rfl) ⟨15440219, by rfl⟩ : syracuseStep 20586959 = 30880439) B30880439
theorem B9765623 : Blo 1805604 9765623 := bstep (se 1 (by rfl) ⟨7324217, by rfl⟩ : syracuseStep 9765623 = 14648435) B14648435
theorem B9397471 : Blo 1805604 9397471 := bstep (se 1 (by rfl) ⟨7048103, by rfl⟩ : syracuseStep 9397471 = 14096207) B14096207
theorem B10290473 : Blo 1805604 10290473 := bstep (se 2 (by rfl) ⟨3858927, by rfl⟩ : syracuseStep 10290473 = 7717855) B7717855
theorem B5866823 : Blo 1805604 5866823 := bstep (se 1 (by rfl) ⟨4400117, by rfl⟩ : syracuseStep 5866823 = 8800235) B8800235
theorem B4064759 : Blo 1805604 4064759 := bstep (se 1 (by rfl) ⟨3048569, by rfl⟩ : syracuseStep 4064759 = 6097139) B6097139
theorem B6096383 : Blo 1805604 6096383 := bstep (se 1 (by rfl) ⟨4572287, by rfl⟩ : syracuseStep 6096383 = 9144575) B9144575
theorem B6096491 : Blo 1805604 6096491 := bstep (se 1 (by rfl) ⟨4572368, by rfl⟩ : syracuseStep 6096491 = 9144737) B9144737
theorem B26044253 : Blo 1805604 26044253 := bstep (se 3 (by rfl) ⟨4883297, by rfl⟩ : syracuseStep 26044253 = 9766595) B9766595
theorem B18540407 : Blo 1805604 18540407 := bstep (se 1 (by rfl) ⟨13905305, by rfl⟩ : syracuseStep 18540407 = 27810611) B27810611
theorem B41723849 : Blo 1805604 41723849 := bstep (se 2 (by rfl) ⟨15646443, by rfl⟩ : syracuseStep 41723849 = 31292887) B31292887
theorem B5785663 : Blo 1805604 5785663 := bstep (se 1 (by rfl) ⟨4339247, by rfl⟩ : syracuseStep 5785663 = 8678495) B8678495
theorem B8685739 : Blo 1805604 8685739 := bstep (se 1 (by rfl) ⟨6514304, by rfl⟩ : syracuseStep 8685739 = 13028609) B13028609
theorem B11569351 : Blo 1805604 11569351 := bstep (se 1 (by rfl) ⟨8677013, by rfl⟩ : syracuseStep 11569351 = 17354027) B17354027
theorem B12052799 : Blo 1805604 12052799 := bstep (se 1 (by rfl) ⟨9039599, by rfl⟩ : syracuseStep 12052799 = 18079199) B18079199
theorem B5147219 : Blo 1805604 5147219 := bstep (se 1 (by rfl) ⟨3860414, by rfl⟩ : syracuseStep 5147219 = 7720829) B7720829
theorem B2894491 : Blo 1805604 2894491 := bstep (se 1 (by rfl) ⟨2170868, by rfl⟩ : syracuseStep 2894491 = 4341737) B4341737
theorem B5147401 : Blo 1805604 5147401 := bstep (se 2 (by rfl) ⟨1930275, by rfl⟩ : syracuseStep 5147401 = 3860551) B3860551
theorem B4066145 : Blo 1805604 4066145 := bstep (se 2 (by rfl) ⟨1524804, by rfl⟩ : syracuseStep 4066145 = 3049609) B3049609
theorem B6098003 : Blo 1805604 6098003 := bstep (se 1 (by rfl) ⟨4573502, by rfl⟩ : syracuseStep 6098003 = 9147005) B9147005
theorem B4066415 : Blo 1805604 4066415 := bstep (se 1 (by rfl) ⟨3049811, by rfl⟩ : syracuseStep 4066415 = 6099623) B6099623
theorem B4066487 : Blo 1805604 4066487 := bstep (se 1 (by rfl) ⟨3049865, by rfl⟩ : syracuseStep 4066487 = 6099731) B6099731
theorem B46943495 : Blo 1805604 46943495 := bstep (se 1 (by rfl) ⟨35207621, by rfl⟩ : syracuseStep 46943495 = 70415243) B70415243
theorem B4066793 : Blo 1805604 4066793 := bstep (se 2 (by rfl) ⟨1525047, by rfl⟩ : syracuseStep 4066793 = 3050095) B3050095
theorem B2748169 : Blo 1805604 2748169 := bstep (se 2 (by rfl) ⟨1030563, by rfl⟩ : syracuseStep 2748169 = 2061127) B2061127
theorem B8679419 : Blo 1805604 8679419 := bstep (se 1 (by rfl) ⟨6509564, by rfl⟩ : syracuseStep 8679419 = 13019129) B13019129
theorem B3256375 : Blo 1805604 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B6099083 : Blo 1805604 6099083 := bstep (se 1 (by rfl) ⟨4574312, by rfl⟩ : syracuseStep 6099083 = 9148625) B9148625
theorem B7328189 : Blo 1805604 7328189 := bstep (se 3 (by rfl) ⟨1374035, by rfl⟩ : syracuseStep 7328189 = 2748071) B2748071
theorem B4633193 : Blo 1805604 4633193 := bstep (se 2 (by rfl) ⟨1737447, by rfl⟩ : syracuseStep 4633193 = 3474895) B3474895
theorem B34780009 : Blo 1805604 34780009 := bstep (se 2 (by rfl) ⟨13042503, by rfl⟩ : syracuseStep 34780009 = 26085007) B26085007
theorem B1930267 : Blo 1805604 1930267 := bstep (se 1 (by rfl) ⟨1447700, by rfl⟩ : syracuseStep 1930267 = 2895401) B2895401
theorem B1807407 : Blo 1805604 1807407 := bstep (se 1 (by rfl) ⟨1355555, by rfl⟩ : syracuseStep 1807407 = 2711111) B2711111
theorem B112743665 : Blo 1805604 112743665 := bstep (se 2 (by rfl) ⟨42278874, by rfl⟩ : syracuseStep 112743665 = 84557749) B84557749
theorem B2708807 : Blo 1805604 2708807 := bstep (se 1 (by rfl) ⟨2031605, by rfl⟩ : syracuseStep 2708807 = 4063211) B4063211
theorem B2709047 : Blo 1805604 2709047 := bstep (se 1 (by rfl) ⟨2031785, by rfl⟩ : syracuseStep 2709047 = 4063571) B4063571
theorem B6100649 : Blo 1805604 6100649 := bstep (se 2 (by rfl) ⟨2287743, by rfl⟩ : syracuseStep 6100649 = 4575487) B4575487
theorem B21976829 : Blo 1805604 21976829 := bstep (se 3 (by rfl) ⟨4120655, by rfl⟩ : syracuseStep 21976829 = 8241311) B8241311
theorem B21968651 : Blo 1805604 21968651 := bstep (se 1 (by rfl) ⟨16476488, by rfl⟩ : syracuseStep 21968651 = 32952977) B32952977
theorem B9148463 : Blo 1805604 9148463 := bstep (se 1 (by rfl) ⟨6861347, by rfl⟩ : syracuseStep 9148463 = 13722695) B13722695
theorem B2709671 : Blo 1805604 2709671 := bstep (se 1 (by rfl) ⟨2032253, by rfl⟩ : syracuseStep 2709671 = 4064507) B4064507
theorem B13023827 : Blo 1805604 13023827 := bstep (se 1 (by rfl) ⟨9767870, by rfl⟩ : syracuseStep 13023827 = 19535741) B19535741
theorem B23149259 : Blo 1805604 23149259 := bstep (se 1 (by rfl) ⟨17361944, by rfl⟩ : syracuseStep 23149259 = 34723889) B34723889
theorem B2710313 : Blo 1805604 2710313 := bstep (se 2 (by rfl) ⟨1016367, by rfl⟩ : syracuseStep 2710313 = 2032735) B2032735
theorem B2710463 : Blo 1805604 2710463 := bstep (se 1 (by rfl) ⟨2032847, by rfl⟩ : syracuseStep 2710463 = 4065695) B4065695
theorem B2710559 : Blo 1805604 2710559 := bstep (se 1 (by rfl) ⟨2032919, by rfl⟩ : syracuseStep 2710559 = 4065839) B4065839
theorem B13901053 : Blo 1805604 13901053 := bstep (se 3 (by rfl) ⟨2606447, by rfl⟩ : syracuseStep 13901053 = 5212895) B5212895
theorem B2710847 : Blo 1805604 2710847 := bstep (se 1 (by rfl) ⟨2033135, by rfl⟩ : syracuseStep 2710847 = 4066271) B4066271
theorem B9149921 : Blo 1805604 9149921 := bstep (se 2 (by rfl) ⟨3431220, by rfl⟩ : syracuseStep 9149921 = 6862441) B6862441
theorem B8355305 : Blo 1805604 8355305 := bstep (se 2 (by rfl) ⟨3133239, by rfl⟩ : syracuseStep 8355305 = 6266479) B6266479
theorem B39075371 : Blo 1805604 39075371 := bstep (se 1 (by rfl) ⟨29306528, by rfl⟩ : syracuseStep 39075371 = 58613057) B58613057
theorem B13712975 : Blo 1805604 13712975 := bstep (se 1 (by rfl) ⟨10284731, by rfl⟩ : syracuseStep 13712975 = 20569463) B20569463
theorem B8355511 : Blo 1805604 8355511 := bstep (se 1 (by rfl) ⟨6266633, by rfl⟩ : syracuseStep 8355511 = 12533267) B12533267
theorem B5144417 : Blo 1805604 5144417 := bstep (se 2 (by rfl) ⟨1929156, by rfl⟩ : syracuseStep 5144417 = 3858313) B3858313
theorem B4341833 : Blo 1805604 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B15425801 : Blo 1805604 15425801 := bstep (se 2 (by rfl) ⟨5784675, by rfl⟩ : syracuseStep 15425801 = 11569351) B11569351
theorem B3088795 : Blo 1805604 3088795 := bstep (se 1 (by rfl) ⟨2316596, by rfl⟩ : syracuseStep 3088795 = 4633193) B4633193
theorem B75162443 : Blo 1805604 75162443 := bstep (se 1 (by rfl) ⟨56371832, by rfl⟩ : syracuseStep 75162443 = 112743665) B112743665
theorem B3859321 : Blo 1805604 3859321 := bstep (se 2 (by rfl) ⟨1447245, by rfl⟩ : syracuseStep 3859321 = 2894491) B2894491
theorem B4064255 : Blo 1805604 4064255 := bstep (se 1 (by rfl) ⟨3048191, by rfl⟩ : syracuseStep 4064255 = 6096383) B6096383
theorem B4064327 : Blo 1805604 4064327 := bstep (se 1 (by rfl) ⟨3048245, by rfl⟩ : syracuseStep 4064327 = 6096491) B6096491
theorem B2573689 : Blo 1805604 2573689 := bstep (se 2 (by rfl) ⟨965133, by rfl⟩ : syracuseStep 2573689 = 1930267) B1930267
theorem B4065335 : Blo 1805604 4065335 := bstep (se 1 (by rfl) ⟨3049001, by rfl⟩ : syracuseStep 4065335 = 6098003) B6098003
theorem B31295663 : Blo 1805604 31295663 := bstep (se 1 (by rfl) ⟨23471747, by rfl⟩ : syracuseStep 31295663 = 46943495) B46943495
theorem B3664225 : Blo 1805604 3664225 := bstep (se 2 (by rfl) ⟨1374084, by rfl⟩ : syracuseStep 3664225 = 2748169) B2748169
theorem B5786279 : Blo 1805604 5786279 := bstep (se 1 (by rfl) ⟨4339709, by rfl⟩ : syracuseStep 5786279 = 8679419) B8679419
theorem B4066055 : Blo 1805604 4066055 := bstep (se 1 (by rfl) ⟨3049541, by rfl⟩ : syracuseStep 4066055 = 6099083) B6099083
theorem B13724639 : Blo 1805604 13724639 := bstep (se 1 (by rfl) ⟨10293479, by rfl⟩ : syracuseStep 13724639 = 20586959) B20586959
theorem B6860315 : Blo 1805604 6860315 := bstep (se 1 (by rfl) ⟨5145236, by rfl⟩ : syracuseStep 6860315 = 10290473) B10290473
theorem B1805871 : Blo 1805604 1805871 := bstep (se 1 (by rfl) ⟨1354403, by rfl⟩ : syracuseStep 1805871 = 2708807) B2708807
theorem B3911215 : Blo 1805604 3911215 := bstep (se 1 (by rfl) ⟨2933411, by rfl⟩ : syracuseStep 3911215 = 5866823) B5866823
theorem B1806031 : Blo 1805604 1806031 := bstep (se 1 (by rfl) ⟨1354523, by rfl⟩ : syracuseStep 1806031 = 2709047) B2709047
theorem B4067099 : Blo 1805604 4067099 := bstep (se 1 (by rfl) ⟨3050324, by rfl⟩ : syracuseStep 4067099 = 6100649) B6100649
theorem B19541837 : Blo 1805604 19541837 := bstep (se 3 (by rfl) ⟨3664094, by rfl⟩ : syracuseStep 19541837 = 7328189) B7328189
theorem B14651219 : Blo 1805604 14651219 := bstep (se 1 (by rfl) ⟨10988414, by rfl⟩ : syracuseStep 14651219 = 21976829) B21976829
theorem B17362835 : Blo 1805604 17362835 := bstep (se 1 (by rfl) ⟨13022126, by rfl⟩ : syracuseStep 17362835 = 26044253) B26044253
theorem B27815899 : Blo 1805604 27815899 := bstep (se 1 (by rfl) ⟨20861924, by rfl⟩ : syracuseStep 27815899 = 41723849) B41723849
theorem B6098975 : Blo 1805604 6098975 := bstep (se 1 (by rfl) ⟨4574231, by rfl⟩ : syracuseStep 6098975 = 9148463) B9148463
theorem B1806447 : Blo 1805604 1806447 := bstep (se 1 (by rfl) ⟨1354835, by rfl⟩ : syracuseStep 1806447 = 2709671) B2709671
theorem B12529961 : Blo 1805604 12529961 := bstep (se 2 (by rfl) ⟨4698735, by rfl⟩ : syracuseStep 12529961 = 9397471) B9397471
theorem B18534737 : Blo 1805604 18534737 := bstep (se 2 (by rfl) ⟨6950526, by rfl⟩ : syracuseStep 18534737 = 13901053) B13901053
theorem B1806875 : Blo 1805604 1806875 := bstep (se 1 (by rfl) ⟨1355156, by rfl⟩ : syracuseStep 1806875 = 2710313) B2710313
theorem B1806975 : Blo 1805604 1806975 := bstep (se 1 (by rfl) ⟨1355231, by rfl⟩ : syracuseStep 1806975 = 2710463) B2710463
theorem B1807039 : Blo 1805604 1807039 := bstep (se 1 (by rfl) ⟨1355279, by rfl⟩ : syracuseStep 1807039 = 2710559) B2710559
theorem B1807231 : Blo 1805604 1807231 := bstep (se 1 (by rfl) ⟨1355423, by rfl⟩ : syracuseStep 1807231 = 2710847) B2710847
theorem B6099947 : Blo 1805604 6099947 := bstep (se 1 (by rfl) ⟨4574960, by rfl⟩ : syracuseStep 6099947 = 9149921) B9149921
theorem B3429611 : Blo 1805604 3429611 := bstep (se 1 (by rfl) ⟨2572208, by rfl⟩ : syracuseStep 3429611 = 5144417) B5144417
theorem B7714217 : Blo 1805604 7714217 := bstep (se 2 (by rfl) ⟨2892831, by rfl⟩ : syracuseStep 7714217 = 5785663) B5785663
theorem B11580985 : Blo 1805604 11580985 := bstep (se 2 (by rfl) ⟨4342869, by rfl⟩ : syracuseStep 11580985 = 8685739) B8685739
theorem B6510415 : Blo 1805604 6510415 := bstep (se 1 (by rfl) ⟨4882811, by rfl⟩ : syracuseStep 6510415 = 9765623) B9765623
theorem B2709839 : Blo 1805604 2709839 := bstep (se 1 (by rfl) ⟨2032379, by rfl⟩ : syracuseStep 2709839 = 4064759) B4064759
theorem B6863201 : Blo 1805604 6863201 := bstep (se 2 (by rfl) ⟨2573700, by rfl⟩ : syracuseStep 6863201 = 5147401) B5147401
theorem B46373345 : Blo 1805604 46373345 := bstep (se 2 (by rfl) ⟨17390004, by rfl⟩ : syracuseStep 46373345 = 34780009) B34780009
theorem B14645767 : Blo 1805604 14645767 := bstep (se 1 (by rfl) ⟨10984325, by rfl⟩ : syracuseStep 14645767 = 21968651) B21968651
theorem B12360271 : Blo 1805604 12360271 := bstep (se 1 (by rfl) ⟨9270203, by rfl⟩ : syracuseStep 12360271 = 18540407) B18540407
theorem B8035199 : Blo 1805604 8035199 := bstep (se 1 (by rfl) ⟨6026399, by rfl⟩ : syracuseStep 8035199 = 12052799) B12052799
theorem B8682551 : Blo 1805604 8682551 := bstep (se 1 (by rfl) ⟨6511913, by rfl⟩ : syracuseStep 8682551 = 13023827) B13023827
theorem B3431479 : Blo 1805604 3431479 := bstep (se 1 (by rfl) ⟨2573609, by rfl⟩ : syracuseStep 3431479 = 5147219) B5147219
theorem B15432839 : Blo 1805604 15432839 := bstep (se 1 (by rfl) ⟨11574629, by rfl⟩ : syracuseStep 15432839 = 23149259) B23149259
theorem B2710763 : Blo 1805604 2710763 := bstep (se 1 (by rfl) ⟨2033072, by rfl⟩ : syracuseStep 2710763 = 4066145) B4066145
theorem B2710943 : Blo 1805604 2710943 := bstep (se 1 (by rfl) ⟨2033207, by rfl⟩ : syracuseStep 2710943 = 4066415) B4066415
theorem B2710991 : Blo 1805604 2710991 := bstep (se 1 (by rfl) ⟨2033243, by rfl⟩ : syracuseStep 2710991 = 4066487) B4066487
theorem B11140681 : Blo 1805604 11140681 := bstep (se 2 (by rfl) ⟨4177755, by rfl⟩ : syracuseStep 11140681 = 8355511) B8355511
theorem B5570203 : Blo 1805604 5570203 := bstep (se 1 (by rfl) ⟨4177652, by rfl⟩ : syracuseStep 5570203 = 8355305) B8355305
theorem B2711195 : Blo 1805604 2711195 := bstep (se 1 (by rfl) ⟨2033396, by rfl⟩ : syracuseStep 2711195 = 4066793) B4066793
theorem B26050247 : Blo 1805604 26050247 := bstep (se 1 (by rfl) ⟨19537685, by rfl⟩ : syracuseStep 26050247 = 39075371) B39075371
theorem B9141983 : Blo 1805604 9141983 := bstep (se 1 (by rfl) ⟨6856487, by rfl⟩ : syracuseStep 9141983 = 13712975) B13712975
theorem B2286407 : Blo 1805604 2286407 := bstep (se 1 (by rfl) ⟨1714805, by rfl⟩ : syracuseStep 2286407 = 3429611) B3429611
theorem B5145761 : Blo 1805604 5145761 := bstep (se 2 (by rfl) ⟨1929660, by rfl⟩ : syracuseStep 5145761 = 3859321) B3859321
theorem B14854241 : Blo 1805604 14854241 := bstep (se 2 (by rfl) ⟨5570340, by rfl⟩ : syracuseStep 14854241 = 11140681) B11140681
theorem B4573543 : Blo 1805604 4573543 := bstep (se 1 (by rfl) ⟨3430157, by rfl⟩ : syracuseStep 4573543 = 6860315) B6860315
theorem B13027891 : Blo 1805604 13027891 := bstep (se 1 (by rfl) ⟨9770918, by rfl⟩ : syracuseStep 13027891 = 19541837) B19541837
theorem B9767479 : Blo 1805604 9767479 := bstep (se 1 (by rfl) ⟨7325609, by rfl⟩ : syracuseStep 9767479 = 14651219) B14651219
theorem B37087865 : Blo 1805604 37087865 := bstep (se 2 (by rfl) ⟨13907949, by rfl⟩ : syracuseStep 37087865 = 27815899) B27815899
theorem B4065983 : Blo 1805604 4065983 := bstep (se 1 (by rfl) ⟨3049487, by rfl⟩ : syracuseStep 4065983 = 6098975) B6098975
theorem B2894555 : Blo 1805604 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B10283867 : Blo 1805604 10283867 := bstep (se 1 (by rfl) ⟨7712900, by rfl⟩ : syracuseStep 10283867 = 15425801) B15425801
theorem B12356491 : Blo 1805604 12356491 := bstep (se 1 (by rfl) ⟨9267368, by rfl⟩ : syracuseStep 12356491 = 18534737) B18534737
theorem B4885633 : Blo 1805604 4885633 := bstep (se 2 (by rfl) ⟨1832112, by rfl⟩ : syracuseStep 4885633 = 3664225) B3664225
theorem B4066631 : Blo 1805604 4066631 := bstep (se 1 (by rfl) ⟨3049973, by rfl⟩ : syracuseStep 4066631 = 6099947) B6099947
theorem B4575305 : Blo 1805604 4575305 := bstep (se 2 (by rfl) ⟨1715739, by rfl⟩ : syracuseStep 4575305 = 3431479) B3431479
theorem B1806559 : Blo 1805604 1806559 := bstep (se 1 (by rfl) ⟨1354919, by rfl⟩ : syracuseStep 1806559 = 2709839) B2709839
theorem B4575467 : Blo 1805604 4575467 := bstep (se 1 (by rfl) ⟨3431600, by rfl⟩ : syracuseStep 4575467 = 6863201) B6863201
theorem B5788367 : Blo 1805604 5788367 := bstep (se 1 (by rfl) ⟨4341275, by rfl⟩ : syracuseStep 5788367 = 8682551) B8682551
theorem B5214953 : Blo 1805604 5214953 := bstep (se 2 (by rfl) ⟨1955607, by rfl⟩ : syracuseStep 5214953 = 3911215) B3911215
theorem B1807175 : Blo 1805604 1807175 := bstep (se 1 (by rfl) ⟨1355381, by rfl⟩ : syracuseStep 1807175 = 2710763) B2710763
theorem B7426937 : Blo 1805604 7426937 := bstep (se 2 (by rfl) ⟨2785101, by rfl⟩ : syracuseStep 7426937 = 5570203) B5570203
theorem B1807295 : Blo 1805604 1807295 := bstep (se 1 (by rfl) ⟨1355471, by rfl⟩ : syracuseStep 1807295 = 2710943) B2710943
theorem B1807327 : Blo 1805604 1807327 := bstep (se 1 (by rfl) ⟨1355495, by rfl⟩ : syracuseStep 1807327 = 2710991) B2710991
theorem B1807463 : Blo 1805604 1807463 := bstep (se 1 (by rfl) ⟨1355597, by rfl⟩ : syracuseStep 1807463 = 2711195) B2711195
theorem B8680553 : Blo 1805604 8680553 := bstep (se 2 (by rfl) ⟨3255207, by rfl⟩ : syracuseStep 8680553 = 6510415) B6510415
theorem B8353307 : Blo 1805604 8353307 := bstep (se 1 (by rfl) ⟨6264980, by rfl⟩ : syracuseStep 8353307 = 12529961) B12529961
theorem B4118393 : Blo 1805604 4118393 := bstep (se 2 (by rfl) ⟨1544397, by rfl⟩ : syracuseStep 4118393 = 3088795) B3088795
theorem B2709503 : Blo 1805604 2709503 := bstep (se 1 (by rfl) ⟨2032127, by rfl⟩ : syracuseStep 2709503 = 4064255) B4064255
theorem B19527689 : Blo 1805604 19527689 := bstep (se 2 (by rfl) ⟨7322883, by rfl⟩ : syracuseStep 19527689 = 14645767) B14645767
theorem B2709551 : Blo 1805604 2709551 := bstep (se 1 (by rfl) ⟨2032163, by rfl⟩ : syracuseStep 2709551 = 4064327) B4064327
theorem B16480361 : Blo 1805604 16480361 := bstep (se 2 (by rfl) ⟨6180135, by rfl⟩ : syracuseStep 16480361 = 12360271) B12360271
theorem B801732725 : Blo 1805604 801732725 := bstep (se 5 (by rfl) ⟨37581221, by rfl⟩ : syracuseStep 801732725 = 75162443) B75162443
theorem B5142811 : Blo 1805604 5142811 := bstep (se 1 (by rfl) ⟨3857108, by rfl⟩ : syracuseStep 5142811 = 7714217) B7714217
theorem B2710223 : Blo 1805604 2710223 := bstep (se 1 (by rfl) ⟨2032667, by rfl⟩ : syracuseStep 2710223 = 4065335) B4065335
theorem B20863775 : Blo 1805604 20863775 := bstep (se 1 (by rfl) ⟨15647831, by rfl⟩ : syracuseStep 20863775 = 31295663) B31295663
theorem B30915563 : Blo 1805604 30915563 := bstep (se 1 (by rfl) ⟨23186672, by rfl⟩ : syracuseStep 30915563 = 46373345) B46373345
theorem B3857519 : Blo 1805604 3857519 := bstep (se 1 (by rfl) ⟨2893139, by rfl⟩ : syracuseStep 3857519 = 5786279) B5786279
theorem B3431585 : Blo 1805604 3431585 := bstep (se 2 (by rfl) ⟨1286844, by rfl⟩ : syracuseStep 3431585 = 2573689) B2573689
theorem B2710703 : Blo 1805604 2710703 := bstep (se 1 (by rfl) ⟨2033027, by rfl⟩ : syracuseStep 2710703 = 4066055) B4066055
theorem B5356799 : Blo 1805604 5356799 := bstep (se 1 (by rfl) ⟨4017599, by rfl⟩ : syracuseStep 5356799 = 8035199) B8035199
theorem B9149759 : Blo 1805604 9149759 := bstep (se 1 (by rfl) ⟨6862319, by rfl⟩ : syracuseStep 9149759 = 13724639) B13724639
theorem B15441313 : Blo 1805604 15441313 := bstep (se 2 (by rfl) ⟨5790492, by rfl⟩ : syracuseStep 15441313 = 11580985) B11580985
theorem B10288559 : Blo 1805604 10288559 := bstep (se 1 (by rfl) ⟨7716419, by rfl⟩ : syracuseStep 10288559 = 15432839) B15432839
theorem B17366831 : Blo 1805604 17366831 := bstep (se 1 (by rfl) ⟨13025123, by rfl⟩ : syracuseStep 17366831 = 26050247) B26050247
theorem B6094655 : Blo 1805604 6094655 := bstep (se 1 (by rfl) ⟨4570991, by rfl⟩ : syracuseStep 6094655 = 9141983) B9141983
theorem B2711399 : Blo 1805604 2711399 := bstep (se 1 (by rfl) ⟨2033549, by rfl⟩ : syracuseStep 2711399 = 4067099) B4067099
theorem B11575223 : Blo 1805604 11575223 := bstep (se 1 (by rfl) ⟨8681417, by rfl⟩ : syracuseStep 11575223 = 17362835) B17362835
theorem B6857081 : Blo 1805604 6857081 := bstep (se 2 (by rfl) ⟨2571405, by rfl⟩ : syracuseStep 6857081 = 5142811) B5142811
theorem B9150893 : Blo 1805604 9150893 := bstep (se 3 (by rfl) ⟨1715792, by rfl⟩ : syracuseStep 9150893 = 3431585) B3431585
theorem B3858911 : Blo 1805604 3858911 := bstep (se 1 (by rfl) ⟨2894183, by rfl⟩ : syracuseStep 3858911 = 5788367) B5788367
theorem B16475321 : Blo 1805604 16475321 := bstep (se 2 (by rfl) ⟨6178245, by rfl⟩ : syracuseStep 16475321 = 12356491) B12356491
theorem B2745595 : Blo 1805604 2745595 := bstep (se 1 (by rfl) ⟨2059196, by rfl⟩ : syracuseStep 2745595 = 4118393) B4118393
theorem B22275485 : Blo 1805604 22275485 := bstep (se 3 (by rfl) ⟨4176653, by rfl⟩ : syracuseStep 22275485 = 8353307) B8353307
theorem B534488483 : Blo 1805604 534488483 := bstep (se 1 (by rfl) ⟨400866362, by rfl⟩ : syracuseStep 534488483 = 801732725) B801732725
theorem B6514177 : Blo 1805604 6514177 := bstep (se 2 (by rfl) ⟨2442816, by rfl⟩ : syracuseStep 6514177 = 4885633) B4885633
theorem B24725243 : Blo 1805604 24725243 := bstep (se 1 (by rfl) ⟨18543932, by rfl⟩ : syracuseStep 24725243 = 37087865) B37087865
theorem B20588417 : Blo 1805604 20588417 := bstep (se 2 (by rfl) ⟨7720656, by rfl⟩ : syracuseStep 20588417 = 15441313) B15441313
theorem B7718813 : Blo 1805604 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B6097085 : Blo 1805604 6097085 := bstep (se 3 (by rfl) ⟨1143203, by rfl⟩ : syracuseStep 6097085 = 2286407) B2286407
theorem B6859039 : Blo 1805604 6859039 := bstep (se 1 (by rfl) ⟨5144279, by rfl⟩ : syracuseStep 6859039 = 10288559) B10288559
theorem B11577887 : Blo 1805604 11577887 := bstep (se 1 (by rfl) ⟨8683415, by rfl⟩ : syracuseStep 11577887 = 17366831) B17366831
theorem B3050203 : Blo 1805604 3050203 := bstep (se 1 (by rfl) ⟨2287652, by rfl⟩ : syracuseStep 3050203 = 4575305) B4575305
theorem B3050311 : Blo 1805604 3050311 := bstep (se 1 (by rfl) ⟨2287733, by rfl⟩ : syracuseStep 3050311 = 4575467) B4575467
theorem B6098057 : Blo 1805604 6098057 := bstep (se 2 (by rfl) ⟨2286771, by rfl⟩ : syracuseStep 6098057 = 4573543) B4573543
theorem B5787035 : Blo 1805604 5787035 := bstep (se 1 (by rfl) ⟨4340276, by rfl⟩ : syracuseStep 5787035 = 8680553) B8680553
theorem B17370521 : Blo 1805604 17370521 := bstep (se 2 (by rfl) ⟨6513945, by rfl⟩ : syracuseStep 17370521 = 13027891) B13027891
theorem B1806335 : Blo 1805604 1806335 := bstep (se 1 (by rfl) ⟨1354751, by rfl⟩ : syracuseStep 1806335 = 2709503) B2709503
theorem B1806367 : Blo 1805604 1806367 := bstep (se 1 (by rfl) ⟨1354775, by rfl⟩ : syracuseStep 1806367 = 2709551) B2709551
theorem B1806815 : Blo 1805604 1806815 := bstep (se 1 (by rfl) ⟨1355111, by rfl⟩ : syracuseStep 1806815 = 2710223) B2710223
theorem B13906541 : Blo 1805604 13906541 := bstep (se 3 (by rfl) ⟨2607476, by rfl⟩ : syracuseStep 13906541 = 5214953) B5214953
theorem B55636733 : Blo 1805604 55636733 := bstep (se 3 (by rfl) ⟨10431887, by rfl⟩ : syracuseStep 55636733 = 20863775) B20863775
theorem B1807135 : Blo 1805604 1807135 := bstep (se 1 (by rfl) ⟨1355351, by rfl⟩ : syracuseStep 1807135 = 2710703) B2710703
theorem B6099839 : Blo 1805604 6099839 := bstep (se 1 (by rfl) ⟨4574879, by rfl⟩ : syracuseStep 6099839 = 9149759) B9149759
theorem B19805165 : Blo 1805604 19805165 := bstep (se 3 (by rfl) ⟨3713468, by rfl⟩ : syracuseStep 19805165 = 7426937) B7426937
theorem B329766005 : Blo 1805604 329766005 := bstep (se 5 (by rfl) ⟨15457781, by rfl⟩ : syracuseStep 329766005 = 30915563) B30915563
theorem B1807599 : Blo 1805604 1807599 := bstep (se 1 (by rfl) ⟨1355699, by rfl⟩ : syracuseStep 1807599 = 2711399) B2711399
theorem B52073837 : Blo 1805604 52073837 := bstep (se 3 (by rfl) ⟨9763844, by rfl⟩ : syracuseStep 52073837 = 19527689) B19527689
theorem B43947629 : Blo 1805604 43947629 := bstep (se 3 (by rfl) ⟨8240180, by rfl⟩ : syracuseStep 43947629 = 16480361) B16480361
theorem B13023305 : Blo 1805604 13023305 := bstep (se 2 (by rfl) ⟨4883739, by rfl⟩ : syracuseStep 13023305 = 9767479) B9767479
theorem B3430507 : Blo 1805604 3430507 := bstep (se 1 (by rfl) ⟨2572880, by rfl⟩ : syracuseStep 3430507 = 5145761) B5145761
theorem B9902827 : Blo 1805604 9902827 := bstep (se 1 (by rfl) ⟨7427120, by rfl⟩ : syracuseStep 9902827 = 14854241) B14854241
theorem B2710655 : Blo 1805604 2710655 := bstep (se 1 (by rfl) ⟨2032991, by rfl⟩ : syracuseStep 2710655 = 4065983) B4065983
theorem B6855911 : Blo 1805604 6855911 := bstep (se 1 (by rfl) ⟨5141933, by rfl⟩ : syracuseStep 6855911 = 10283867) B10283867
theorem B2571679 : Blo 1805604 2571679 := bstep (se 1 (by rfl) ⟨1928759, by rfl⟩ : syracuseStep 2571679 = 3857519) B3857519
theorem B3571199 : Blo 1805604 3571199 := bstep (se 1 (by rfl) ⟨2678399, by rfl⟩ : syracuseStep 3571199 = 5356799) B5356799
theorem B2711087 : Blo 1805604 2711087 := bstep (se 1 (by rfl) ⟨2033315, by rfl⟩ : syracuseStep 2711087 = 4066631) B4066631
theorem B4063103 : Blo 1805604 4063103 := bstep (se 1 (by rfl) ⟨3047327, by rfl⟩ : syracuseStep 4063103 = 6094655) B6094655
theorem B7716815 : Blo 1805604 7716815 := bstep (se 1 (by rfl) ⟨5787611, by rfl⟩ : syracuseStep 7716815 = 11575223) B11575223
theorem B4571387 : Blo 1805604 4571387 := bstep (se 1 (by rfl) ⟨3428540, by rfl⟩ : syracuseStep 4571387 = 6857081) B6857081
theorem B2572607 : Blo 1805604 2572607 := bstep (se 1 (by rfl) ⟨1929455, by rfl⟩ : syracuseStep 2572607 = 3858911) B3858911
theorem B16483495 : Blo 1805604 16483495 := bstep (se 1 (by rfl) ⟨12362621, by rfl⟩ : syracuseStep 16483495 = 24725243) B24725243
theorem B5145875 : Blo 1805604 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B4064723 : Blo 1805604 4064723 := bstep (se 1 (by rfl) ⟨3048542, by rfl⟩ : syracuseStep 4064723 = 6097085) B6097085
theorem B7718591 : Blo 1805604 7718591 := bstep (se 1 (by rfl) ⟨5788943, by rfl⟩ : syracuseStep 7718591 = 11577887) B11577887
theorem B8685569 : Blo 1805604 8685569 := bstep (se 2 (by rfl) ⟨3257088, by rfl⟩ : syracuseStep 8685569 = 6514177) B6514177
theorem B4065371 : Blo 1805604 4065371 := bstep (se 1 (by rfl) ⟨3049028, by rfl⟩ : syracuseStep 4065371 = 6098057) B6098057
theorem B4574009 : Blo 1805604 4574009 := bstep (se 2 (by rfl) ⟨1715253, by rfl⟩ : syracuseStep 4574009 = 3430507) B3430507
theorem B9145385 : Blo 1805604 9145385 := bstep (se 2 (by rfl) ⟨3429519, by rfl⟩ : syracuseStep 9145385 = 6859039) B6859039
theorem B4066559 : Blo 1805604 4066559 := bstep (se 1 (by rfl) ⟨3049919, by rfl⟩ : syracuseStep 4066559 = 6099839) B6099839
theorem B219844003 : Blo 1805604 219844003 := bstep (se 1 (by rfl) ⟨164883002, by rfl⟩ : syracuseStep 219844003 = 329766005) B329766005
theorem B4066937 : Blo 1805604 4066937 := bstep (se 2 (by rfl) ⟨1525101, by rfl⟩ : syracuseStep 4066937 = 3050203) B3050203
theorem B29298419 : Blo 1805604 29298419 := bstep (se 1 (by rfl) ⟨21973814, by rfl⟩ : syracuseStep 29298419 = 43947629) B43947629
theorem B4067081 : Blo 1805604 4067081 := bstep (se 2 (by rfl) ⟨1525155, by rfl⟩ : syracuseStep 4067081 = 3050311) B3050311
theorem B13725611 : Blo 1805604 13725611 := bstep (se 1 (by rfl) ⟨10294208, by rfl⟩ : syracuseStep 13725611 = 20588417) B20588417
theorem B14643173 : Blo 1805604 14643173 := bstep (se 4 (by rfl) ⟨1372797, by rfl⟩ : syracuseStep 14643173 = 2745595) B2745595
theorem B3428905 : Blo 1805604 3428905 := bstep (se 2 (by rfl) ⟨1285839, by rfl⟩ : syracuseStep 3428905 = 2571679) B2571679
theorem B1807103 : Blo 1805604 1807103 := bstep (se 1 (by rfl) ⟨1355327, by rfl⟩ : syracuseStep 1807103 = 2710655) B2710655
theorem B11580347 : Blo 1805604 11580347 := bstep (se 1 (by rfl) ⟨8685260, by rfl⟩ : syracuseStep 11580347 = 17370521) B17370521
theorem B2380799 : Blo 1805604 2380799 := bstep (se 1 (by rfl) ⟨1785599, by rfl⟩ : syracuseStep 2380799 = 3571199) B3571199
theorem B1807391 : Blo 1805604 1807391 := bstep (se 1 (by rfl) ⟨1355543, by rfl⟩ : syracuseStep 1807391 = 2711087) B2711087
theorem B2708735 : Blo 1805604 2708735 := bstep (se 1 (by rfl) ⟨2031551, by rfl⟩ : syracuseStep 2708735 = 4063103) B4063103
theorem B6100595 : Blo 1805604 6100595 := bstep (se 1 (by rfl) ⟨4575446, by rfl⟩ : syracuseStep 6100595 = 9150893) B9150893
theorem B9271027 : Blo 1805604 9271027 := bstep (se 1 (by rfl) ⟨6953270, by rfl⟩ : syracuseStep 9271027 = 13906541) B13906541
theorem B37091155 : Blo 1805604 37091155 := bstep (se 1 (by rfl) ⟨27818366, by rfl⟩ : syracuseStep 37091155 = 55636733) B55636733
theorem B13203443 : Blo 1805604 13203443 := bstep (se 1 (by rfl) ⟨9902582, by rfl⟩ : syracuseStep 13203443 = 19805165) B19805165
theorem B10983547 : Blo 1805604 10983547 := bstep (se 1 (by rfl) ⟨8237660, by rfl⟩ : syracuseStep 10983547 = 16475321) B16475321
theorem B34715891 : Blo 1805604 34715891 := bstep (se 1 (by rfl) ⟨26036918, by rfl⟩ : syracuseStep 34715891 = 52073837) B52073837
theorem B14850323 : Blo 1805604 14850323 := bstep (se 1 (by rfl) ⟨11137742, by rfl⟩ : syracuseStep 14850323 = 22275485) B22275485
theorem B356325655 : Blo 1805604 356325655 := bstep (se 1 (by rfl) ⟨267244241, by rfl⟩ : syracuseStep 356325655 = 534488483) B534488483
theorem B13203769 : Blo 1805604 13203769 := bstep (se 2 (by rfl) ⟨4951413, by rfl⟩ : syracuseStep 13203769 = 9902827) B9902827
theorem B8682203 : Blo 1805604 8682203 := bstep (se 1 (by rfl) ⟨6511652, by rfl⟩ : syracuseStep 8682203 = 13023305) B13023305
theorem B4570607 : Blo 1805604 4570607 := bstep (se 1 (by rfl) ⟨3427955, by rfl⟩ : syracuseStep 4570607 = 6855911) B6855911
theorem B3858023 : Blo 1805604 3858023 := bstep (se 1 (by rfl) ⟨2893517, by rfl⟩ : syracuseStep 3858023 = 5787035) B5787035
theorem B5144543 : Blo 1805604 5144543 := bstep (se 1 (by rfl) ⟨3858407, by rfl⟩ : syracuseStep 5144543 = 7716815) B7716815
theorem B3047591 : Blo 1805604 3047591 := bstep (se 1 (by rfl) ⟨2285693, by rfl⟩ : syracuseStep 3047591 = 4571387) B4571387
theorem B17605025 : Blo 1805604 17605025 := bstep (se 2 (by rfl) ⟨6601884, by rfl⟩ : syracuseStep 17605025 = 13203769) B13203769
theorem B4571873 : Blo 1805604 4571873 := bstep (se 2 (by rfl) ⟨1714452, by rfl⟩ : syracuseStep 4571873 = 3428905) B3428905
theorem B5145727 : Blo 1805604 5145727 := bstep (se 1 (by rfl) ⟨3859295, by rfl⟩ : syracuseStep 5145727 = 7718591) B7718591
theorem B23143927 : Blo 1805604 23143927 := bstep (se 1 (by rfl) ⟨17357945, by rfl⟩ : syracuseStep 23143927 = 34715891) B34715891
theorem B3049339 : Blo 1805604 3049339 := bstep (se 1 (by rfl) ⟨2287004, by rfl⟩ : syracuseStep 3049339 = 4574009) B4574009
theorem B6096923 : Blo 1805604 6096923 := bstep (se 1 (by rfl) ⟨4572692, by rfl⟩ : syracuseStep 6096923 = 9145385) B9145385
theorem B19532279 : Blo 1805604 19532279 := bstep (se 1 (by rfl) ⟨14649209, by rfl⟩ : syracuseStep 19532279 = 29298419) B29298419
theorem B7720231 : Blo 1805604 7720231 := bstep (se 1 (by rfl) ⟨5790173, by rfl⟩ : syracuseStep 7720231 = 11580347) B11580347
theorem B6860285 : Blo 1805604 6860285 := bstep (se 3 (by rfl) ⟨1286303, by rfl⟩ : syracuseStep 6860285 = 2572607) B2572607
theorem B1805823 : Blo 1805604 1805823 := bstep (se 1 (by rfl) ⟨1354367, by rfl⟩ : syracuseStep 1805823 = 2708735) B2708735
theorem B4067063 : Blo 1805604 4067063 := bstep (se 1 (by rfl) ⟨3050297, by rfl⟩ : syracuseStep 4067063 = 6100595) B6100595
theorem B9900215 : Blo 1805604 9900215 := bstep (se 1 (by rfl) ⟨7425161, by rfl⟩ : syracuseStep 9900215 = 14850323) B14850323
theorem B5788135 : Blo 1805604 5788135 := bstep (se 1 (by rfl) ⟨4341101, by rfl⟩ : syracuseStep 5788135 = 8682203) B8682203
theorem B3429695 : Blo 1805604 3429695 := bstep (se 1 (by rfl) ⟨2572271, by rfl⟩ : syracuseStep 3429695 = 5144543) B5144543
theorem B9762115 : Blo 1805604 9762115 := bstep (se 1 (by rfl) ⟨7321586, by rfl⟩ : syracuseStep 9762115 = 14643173) B14643173
theorem B14644729 : Blo 1805604 14644729 := bstep (se 2 (by rfl) ⟨5491773, by rfl⟩ : syracuseStep 14644729 = 10983547) B10983547
theorem B475100873 : Blo 1805604 475100873 := bstep (se 2 (by rfl) ⟨178162827, by rfl⟩ : syracuseStep 475100873 = 356325655) B356325655
theorem B3430583 : Blo 1805604 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B2709815 : Blo 1805604 2709815 := bstep (se 1 (by rfl) ⟨2032361, by rfl⟩ : syracuseStep 2709815 = 4064723) B4064723
theorem B5790379 : Blo 1805604 5790379 := bstep (se 1 (by rfl) ⟨4342784, by rfl⟩ : syracuseStep 5790379 = 8685569) B8685569
theorem B2710247 : Blo 1805604 2710247 := bstep (se 1 (by rfl) ⟨2032685, by rfl⟩ : syracuseStep 2710247 = 4065371) B4065371
theorem B21977993 : Blo 1805604 21977993 := bstep (se 2 (by rfl) ⟨8241747, by rfl⟩ : syracuseStep 21977993 = 16483495) B16483495
theorem B293125337 : Blo 1805604 293125337 := bstep (se 2 (by rfl) ⟨109922001, by rfl⟩ : syracuseStep 293125337 = 219844003) B219844003
theorem B2711039 : Blo 1805604 2711039 := bstep (se 1 (by rfl) ⟨2033279, by rfl⟩ : syracuseStep 2711039 = 4066559) B4066559
theorem B12361369 : Blo 1805604 12361369 := bstep (se 2 (by rfl) ⟨4635513, by rfl⟩ : syracuseStep 12361369 = 9271027) B9271027
theorem B3047071 : Blo 1805604 3047071 := bstep (se 1 (by rfl) ⟨2285303, by rfl⟩ : syracuseStep 3047071 = 4570607) B4570607
theorem B2572015 : Blo 1805604 2572015 := bstep (se 1 (by rfl) ⟨1929011, by rfl⟩ : syracuseStep 2572015 = 3858023) B3858023
theorem B2711291 : Blo 1805604 2711291 := bstep (se 1 (by rfl) ⟨2033468, by rfl⟩ : syracuseStep 2711291 = 4066937) B4066937
theorem B49454873 : Blo 1805604 49454873 := bstep (se 2 (by rfl) ⟨18545577, by rfl⟩ : syracuseStep 49454873 = 37091155) B37091155
theorem B2711387 : Blo 1805604 2711387 := bstep (se 1 (by rfl) ⟨2033540, by rfl⟩ : syracuseStep 2711387 = 4067081) B4067081
theorem B9150407 : Blo 1805604 9150407 := bstep (se 1 (by rfl) ⟨6862805, by rfl⟩ : syracuseStep 9150407 = 13725611) B13725611
theorem B35209181 : Blo 1805604 35209181 := bstep (se 3 (by rfl) ⟨6601721, by rfl⟩ : syracuseStep 35209181 = 13203443) B13203443
theorem B6348797 : Blo 1805604 6348797 := bstep (se 3 (by rfl) ⟨1190399, by rfl⟩ : syracuseStep 6348797 = 2380799) B2380799
theorem B2031727 : Blo 1805604 2031727 := bstep (se 1 (by rfl) ⟨1523795, by rfl⟩ : syracuseStep 2031727 = 3047591) B3047591
theorem B3047915 : Blo 1805604 3047915 := bstep (se 1 (by rfl) ⟨2285936, by rfl⟩ : syracuseStep 3047915 = 4571873) B4571873
theorem B7717513 : Blo 1805604 7717513 := bstep (se 2 (by rfl) ⟨2894067, by rfl⟩ : syracuseStep 7717513 = 5788135) B5788135
theorem B2286463 : Blo 1805604 2286463 := bstep (se 1 (by rfl) ⟨1714847, by rfl⟩ : syracuseStep 2286463 = 3429695) B3429695
theorem B4064615 : Blo 1805604 4064615 := bstep (se 1 (by rfl) ⟨3048461, by rfl⟩ : syracuseStep 4064615 = 6096923) B6096923
theorem B2287055 : Blo 1805604 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B4573523 : Blo 1805604 4573523 := bstep (se 1 (by rfl) ⟨3430142, by rfl⟩ : syracuseStep 4573523 = 6860285) B6860285
theorem B4065785 : Blo 1805604 4065785 := bstep (se 2 (by rfl) ⟨1524669, by rfl⟩ : syracuseStep 4065785 = 3049339) B3049339
theorem B78105221 : Blo 1805604 78105221 := bstep (se 4 (by rfl) ⟨7322364, by rfl⟩ : syracuseStep 78105221 = 14644729) B14644729
theorem B23472787 : Blo 1805604 23472787 := bstep (se 1 (by rfl) ⟨17604590, by rfl⟩ : syracuseStep 23472787 = 35209181) B35209181
theorem B7720505 : Blo 1805604 7720505 := bstep (se 2 (by rfl) ⟨2895189, by rfl⟩ : syracuseStep 7720505 = 5790379) B5790379
theorem B6860969 : Blo 1805604 6860969 := bstep (se 2 (by rfl) ⟨2572863, by rfl⟩ : syracuseStep 6860969 = 5145727) B5145727
theorem B1806543 : Blo 1805604 1806543 := bstep (se 1 (by rfl) ⟨1354907, by rfl⟩ : syracuseStep 1806543 = 2709815) B2709815
theorem B13021519 : Blo 1805604 13021519 := bstep (se 1 (by rfl) ⟨9766139, by rfl⟩ : syracuseStep 13021519 = 19532279) B19532279
theorem B10293641 : Blo 1805604 10293641 := bstep (se 2 (by rfl) ⟨3860115, by rfl⟩ : syracuseStep 10293641 = 7720231) B7720231
theorem B1806831 : Blo 1805604 1806831 := bstep (se 1 (by rfl) ⟨1355123, by rfl⟩ : syracuseStep 1806831 = 2710247) B2710247
theorem B14651995 : Blo 1805604 14651995 := bstep (se 1 (by rfl) ⟨10988996, by rfl⟩ : syracuseStep 14651995 = 21977993) B21977993
theorem B195416891 : Blo 1805604 195416891 := bstep (se 1 (by rfl) ⟨146562668, by rfl⟩ : syracuseStep 195416891 = 293125337) B293125337
theorem B3429353 : Blo 1805604 3429353 := bstep (se 2 (by rfl) ⟨1286007, by rfl⟩ : syracuseStep 3429353 = 2572015) B2572015
theorem B1807359 : Blo 1805604 1807359 := bstep (se 1 (by rfl) ⟨1355519, by rfl⟩ : syracuseStep 1807359 = 2711039) B2711039
theorem B1807527 : Blo 1805604 1807527 := bstep (se 1 (by rfl) ⟨1355645, by rfl⟩ : syracuseStep 1807527 = 2711291) B2711291
theorem B32969915 : Blo 1805604 32969915 := bstep (se 1 (by rfl) ⟨24727436, by rfl⟩ : syracuseStep 32969915 = 49454873) B49454873
theorem B1807591 : Blo 1805604 1807591 := bstep (se 1 (by rfl) ⟨1355693, by rfl⟩ : syracuseStep 1807591 = 2711387) B2711387
theorem B6100271 : Blo 1805604 6100271 := bstep (se 1 (by rfl) ⟨4575203, by rfl⟩ : syracuseStep 6100271 = 9150407) B9150407
theorem B4232531 : Blo 1805604 4232531 := bstep (se 1 (by rfl) ⟨3174398, by rfl⟩ : syracuseStep 4232531 = 6348797) B6348797
theorem B6600143 : Blo 1805604 6600143 := bstep (se 1 (by rfl) ⟨4950107, by rfl⟩ : syracuseStep 6600143 = 9900215) B9900215
theorem B11736683 : Blo 1805604 11736683 := bstep (se 1 (by rfl) ⟨8802512, by rfl⟩ : syracuseStep 11736683 = 17605025) B17605025
theorem B316733915 : Blo 1805604 316733915 := bstep (se 1 (by rfl) ⟨237550436, by rfl⟩ : syracuseStep 316733915 = 475100873) B475100873
theorem B13016153 : Blo 1805604 13016153 := bstep (se 2 (by rfl) ⟨4881057, by rfl⟩ : syracuseStep 13016153 = 9762115) B9762115
theorem B30858569 : Blo 1805604 30858569 := bstep (se 2 (by rfl) ⟨11571963, by rfl⟩ : syracuseStep 30858569 = 23143927) B23143927
theorem B16481825 : Blo 1805604 16481825 := bstep (se 2 (by rfl) ⟨6180684, by rfl⟩ : syracuseStep 16481825 = 12361369) B12361369
theorem B4062761 : Blo 1805604 4062761 := bstep (se 2 (by rfl) ⟨1523535, by rfl⟩ : syracuseStep 4062761 = 3047071) B3047071
theorem B2711375 : Blo 1805604 2711375 := bstep (se 1 (by rfl) ⟨2033531, by rfl⟩ : syracuseStep 2711375 = 4067063) B4067063
theorem B34709741 : Blo 1805604 34709741 := bstep (se 3 (by rfl) ⟨6508076, by rfl⟩ : syracuseStep 34709741 = 13016153) B13016153
theorem B2031943 : Blo 1805604 2031943 := bstep (se 1 (by rfl) ⟨1523957, by rfl⟩ : syracuseStep 2031943 = 3047915) B3047915
theorem B130277927 : Blo 1805604 130277927 := bstep (se 1 (by rfl) ⟨97708445, by rfl⟩ : syracuseStep 130277927 = 195416891) B195416891
theorem B2286235 : Blo 1805604 2286235 := bstep (se 1 (by rfl) ⟨1714676, by rfl⟩ : syracuseStep 2286235 = 3429353) B3429353
theorem B21979943 : Blo 1805604 21979943 := bstep (se 1 (by rfl) ⟨16484957, by rfl⟩ : syracuseStep 21979943 = 32969915) B32969915
theorem B10290017 : Blo 1805604 10290017 := bstep (se 2 (by rfl) ⟨3858756, by rfl⟩ : syracuseStep 10290017 = 7717513) B7717513
theorem B7824455 : Blo 1805604 7824455 := bstep (se 1 (by rfl) ⟨5868341, by rfl⟩ : syracuseStep 7824455 = 11736683) B11736683
theorem B3048617 : Blo 1805604 3048617 := bstep (se 2 (by rfl) ⟨1143231, by rfl⟩ : syracuseStep 3048617 = 2286463) B2286463
theorem B3049015 : Blo 1805604 3049015 := bstep (se 1 (by rfl) ⟨2286761, by rfl⟩ : syracuseStep 3049015 = 4573523) B4573523
theorem B52070147 : Blo 1805604 52070147 := bstep (se 1 (by rfl) ⟨39052610, by rfl⟩ : syracuseStep 52070147 = 78105221) B78105221
theorem B20572379 : Blo 1805604 20572379 := bstep (se 1 (by rfl) ⟨15429284, by rfl⟩ : syracuseStep 20572379 = 30858569) B30858569
theorem B10987883 : Blo 1805604 10987883 := bstep (se 1 (by rfl) ⟨8240912, by rfl⟩ : syracuseStep 10987883 = 16481825) B16481825
theorem B5147003 : Blo 1805604 5147003 := bstep (se 1 (by rfl) ⟨3860252, by rfl⟩ : syracuseStep 5147003 = 7720505) B7720505
theorem B4573979 : Blo 1805604 4573979 := bstep (se 1 (by rfl) ⟨3430484, by rfl⟩ : syracuseStep 4573979 = 6860969) B6860969
theorem B17362025 : Blo 1805604 17362025 := bstep (se 2 (by rfl) ⟨6510759, by rfl⟩ : syracuseStep 17362025 = 13021519) B13021519
theorem B31297049 : Blo 1805604 31297049 := bstep (se 2 (by rfl) ⟨11736393, by rfl⟩ : syracuseStep 31297049 = 23472787) B23472787
theorem B4066847 : Blo 1805604 4066847 := bstep (se 1 (by rfl) ⟨3050135, by rfl⟩ : syracuseStep 4066847 = 6100271) B6100271
theorem B17600381 : Blo 1805604 17600381 := bstep (se 3 (by rfl) ⟨3300071, by rfl⟩ : syracuseStep 17600381 = 6600143) B6600143
theorem B6098813 : Blo 1805604 6098813 := bstep (se 3 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 6098813 = 2287055) B2287055
theorem B2708507 : Blo 1805604 2708507 := bstep (se 1 (by rfl) ⟨2031380, by rfl⟩ : syracuseStep 2708507 = 4062761) B4062761
theorem B1807583 : Blo 1805604 1807583 := bstep (se 1 (by rfl) ⟨1355687, by rfl⟩ : syracuseStep 1807583 = 2711375) B2711375
theorem B2708969 : Blo 1805604 2708969 := bstep (se 2 (by rfl) ⟨1015863, by rfl⟩ : syracuseStep 2708969 = 2031727) B2031727
theorem B6862427 : Blo 1805604 6862427 := bstep (se 1 (by rfl) ⟨5146820, by rfl⟩ : syracuseStep 6862427 = 10293641) B10293641
theorem B19535993 : Blo 1805604 19535993 := bstep (se 2 (by rfl) ⟨7325997, by rfl⟩ : syracuseStep 19535993 = 14651995) B14651995
theorem B11286749 : Blo 1805604 11286749 := bstep (se 3 (by rfl) ⟨2116265, by rfl⟩ : syracuseStep 11286749 = 4232531) B4232531
theorem B2709743 : Blo 1805604 2709743 := bstep (se 1 (by rfl) ⟨2032307, by rfl⟩ : syracuseStep 2709743 = 4064615) B4064615
theorem B211155943 : Blo 1805604 211155943 := bstep (se 1 (by rfl) ⟨158366957, by rfl⟩ : syracuseStep 211155943 = 316733915) B316733915
theorem B2710523 : Blo 1805604 2710523 := bstep (se 1 (by rfl) ⟨2032892, by rfl⟩ : syracuseStep 2710523 = 4065785) B4065785
theorem B2032411 : Blo 1805604 2032411 := bstep (se 1 (by rfl) ⟨1524308, by rfl⟩ : syracuseStep 2032411 = 3048617) B3048617
theorem B3048313 : Blo 1805604 3048313 := bstep (se 2 (by rfl) ⟨1143117, by rfl⟩ : syracuseStep 3048313 = 2286235) B2286235
theorem B347407805 : Blo 1805604 347407805 := bstep (se 3 (by rfl) ⟨65138963, by rfl⟩ : syracuseStep 347407805 = 130277927) B130277927
theorem B13714919 : Blo 1805604 13714919 := bstep (se 1 (by rfl) ⟨10286189, by rfl⟩ : syracuseStep 13714919 = 20572379) B20572379
theorem B7325255 : Blo 1805604 7325255 := bstep (se 1 (by rfl) ⟨5493941, by rfl⟩ : syracuseStep 7325255 = 10987883) B10987883
theorem B3049319 : Blo 1805604 3049319 := bstep (se 1 (by rfl) ⟨2286989, by rfl⟩ : syracuseStep 3049319 = 4573979) B4573979
theorem B4065353 : Blo 1805604 4065353 := bstep (se 2 (by rfl) ⟨1524507, by rfl⟩ : syracuseStep 4065353 = 3049015) B3049015
theorem B11733587 : Blo 1805604 11733587 := bstep (se 1 (by rfl) ⟨8800190, by rfl⟩ : syracuseStep 11733587 = 17600381) B17600381
theorem B4065875 : Blo 1805604 4065875 := bstep (se 1 (by rfl) ⟨3049406, by rfl⟩ : syracuseStep 4065875 = 6098813) B6098813
theorem B6860011 : Blo 1805604 6860011 := bstep (se 1 (by rfl) ⟨5145008, by rfl⟩ : syracuseStep 6860011 = 10290017) B10290017
theorem B1805671 : Blo 1805604 1805671 := bstep (se 1 (by rfl) ⟨1354253, by rfl⟩ : syracuseStep 1805671 = 2708507) B2708507
theorem B1805979 : Blo 1805604 1805979 := bstep (se 1 (by rfl) ⟨1354484, by rfl⟩ : syracuseStep 1805979 = 2708969) B2708969
theorem B4574951 : Blo 1805604 4574951 := bstep (se 1 (by rfl) ⟨3431213, by rfl⟩ : syracuseStep 4574951 = 6862427) B6862427
theorem B34713431 : Blo 1805604 34713431 := bstep (se 1 (by rfl) ⟨26035073, by rfl⟩ : syracuseStep 34713431 = 52070147) B52070147
theorem B7524499 : Blo 1805604 7524499 := bstep (se 1 (by rfl) ⟨5643374, by rfl⟩ : syracuseStep 7524499 = 11286749) B11286749
theorem B1806495 : Blo 1805604 1806495 := bstep (se 1 (by rfl) ⟨1354871, by rfl⟩ : syracuseStep 1806495 = 2709743) B2709743
theorem B1807015 : Blo 1805604 1807015 := bstep (se 1 (by rfl) ⟨1355261, by rfl⟩ : syracuseStep 1807015 = 2710523) B2710523
theorem B23139827 : Blo 1805604 23139827 := bstep (se 1 (by rfl) ⟨17354870, by rfl⟩ : syracuseStep 23139827 = 34709741) B34709741
theorem B2709257 : Blo 1805604 2709257 := bstep (se 2 (by rfl) ⟨1015971, by rfl⟩ : syracuseStep 2709257 = 2031943) B2031943
theorem B14653295 : Blo 1805604 14653295 := bstep (se 1 (by rfl) ⟨10989971, by rfl⟩ : syracuseStep 14653295 = 21979943) B21979943
theorem B5216303 : Blo 1805604 5216303 := bstep (se 1 (by rfl) ⟨3912227, by rfl⟩ : syracuseStep 5216303 = 7824455) B7824455
theorem B281541257 : Blo 1805604 281541257 := bstep (se 2 (by rfl) ⟨105577971, by rfl⟩ : syracuseStep 281541257 = 211155943) B211155943
theorem B13023995 : Blo 1805604 13023995 := bstep (se 1 (by rfl) ⟨9767996, by rfl⟩ : syracuseStep 13023995 = 19535993) B19535993
theorem B3431335 : Blo 1805604 3431335 := bstep (se 1 (by rfl) ⟨2573501, by rfl⟩ : syracuseStep 3431335 = 5147003) B5147003
theorem B11574683 : Blo 1805604 11574683 := bstep (se 1 (by rfl) ⟨8681012, by rfl⟩ : syracuseStep 11574683 = 17362025) B17362025
theorem B20864699 : Blo 1805604 20864699 := bstep (se 1 (by rfl) ⟨15648524, by rfl⟩ : syracuseStep 20864699 = 31297049) B31297049
theorem B2711231 : Blo 1805604 2711231 := bstep (se 1 (by rfl) ⟨2033423, by rfl⟩ : syracuseStep 2711231 = 4066847) B4066847
theorem B231605203 : Blo 1805604 231605203 := bstep (se 1 (by rfl) ⟨173703902, by rfl⟩ : syracuseStep 231605203 = 347407805) B347407805
theorem B9143279 : Blo 1805604 9143279 := bstep (se 1 (by rfl) ⟨6857459, by rfl⟩ : syracuseStep 9143279 = 13714919) B13714919
theorem B15426551 : Blo 1805604 15426551 := bstep (se 1 (by rfl) ⟨11569913, by rfl⟩ : syracuseStep 15426551 = 23139827) B23139827
theorem B4883503 : Blo 1805604 4883503 := bstep (se 1 (by rfl) ⟨3662627, by rfl⟩ : syracuseStep 4883503 = 7325255) B7325255
theorem B4064417 : Blo 1805604 4064417 := bstep (se 2 (by rfl) ⟨1524156, by rfl⟩ : syracuseStep 4064417 = 3048313) B3048313
theorem B2032879 : Blo 1805604 2032879 := bstep (se 1 (by rfl) ⟨1524659, by rfl⟩ : syracuseStep 2032879 = 3049319) B3049319
theorem B3049967 : Blo 1805604 3049967 := bstep (se 1 (by rfl) ⟨2287475, by rfl⟩ : syracuseStep 3049967 = 4574951) B4574951
theorem B1806171 : Blo 1805604 1806171 := bstep (se 1 (by rfl) ⟨1354628, by rfl⟩ : syracuseStep 1806171 = 2709257) B2709257
theorem B4575113 : Blo 1805604 4575113 := bstep (se 2 (by rfl) ⟨1715667, by rfl⟩ : syracuseStep 4575113 = 3431335) B3431335
theorem B9768863 : Blo 1805604 9768863 := bstep (se 1 (by rfl) ⟨7326647, by rfl⟩ : syracuseStep 9768863 = 14653295) B14653295
theorem B3477535 : Blo 1805604 3477535 := bstep (se 1 (by rfl) ⟨2608151, by rfl⟩ : syracuseStep 3477535 = 5216303) B5216303
theorem B9146681 : Blo 1805604 9146681 := bstep (se 2 (by rfl) ⟨3430005, by rfl⟩ : syracuseStep 9146681 = 6860011) B6860011
theorem B34730653 : Blo 1805604 34730653 := bstep (se 3 (by rfl) ⟨6511997, by rfl⟩ : syracuseStep 34730653 = 13023995) B13023995
theorem B1807487 : Blo 1805604 1807487 := bstep (se 1 (by rfl) ⟨1355615, by rfl⟩ : syracuseStep 1807487 = 2711231) B2711231
theorem B10032665 : Blo 1805604 10032665 := bstep (se 2 (by rfl) ⟨3762249, by rfl⟩ : syracuseStep 10032665 = 7524499) B7524499
theorem B2709881 : Blo 1805604 2709881 := bstep (se 2 (by rfl) ⟨1016205, by rfl⟩ : syracuseStep 2709881 = 2032411) B2032411
theorem B2710235 : Blo 1805604 2710235 := bstep (se 1 (by rfl) ⟨2032676, by rfl⟩ : syracuseStep 2710235 = 4065353) B4065353
theorem B7822391 : Blo 1805604 7822391 := bstep (se 1 (by rfl) ⟨5866793, by rfl⟩ : syracuseStep 7822391 = 11733587) B11733587
theorem B2710583 : Blo 1805604 2710583 := bstep (se 1 (by rfl) ⟨2032937, by rfl⟩ : syracuseStep 2710583 = 4065875) B4065875
theorem B187694171 : Blo 1805604 187694171 := bstep (se 1 (by rfl) ⟨140770628, by rfl⟩ : syracuseStep 187694171 = 281541257) B281541257
theorem B7716455 : Blo 1805604 7716455 := bstep (se 1 (by rfl) ⟨5787341, by rfl⟩ : syracuseStep 7716455 = 11574683) B11574683
theorem B13909799 : Blo 1805604 13909799 := bstep (se 1 (by rfl) ⟨10432349, by rfl⟩ : syracuseStep 13909799 = 20864699) B20864699
theorem B23142287 : Blo 1805604 23142287 := bstep (se 1 (by rfl) ⟨17356715, by rfl⟩ : syracuseStep 23142287 = 34713431) B34713431
theorem B74187413 : Blo 1805604 74187413 := bstep (se 6 (by rfl) ⟨1738767, by rfl⟩ : syracuseStep 74187413 = 3477535) B3477535
theorem B6095519 : Blo 1805604 6095519 := bstep (se 1 (by rfl) ⟨4571639, by rfl⟩ : syracuseStep 6095519 = 9143279) B9143279
theorem B308806937 : Blo 1805604 308806937 := bstep (se 2 (by rfl) ⟨115802601, by rfl⟩ : syracuseStep 308806937 = 231605203) B231605203
theorem B2033311 : Blo 1805604 2033311 := bstep (se 1 (by rfl) ⟨1524983, by rfl⟩ : syracuseStep 2033311 = 3049967) B3049967
theorem B3050075 : Blo 1805604 3050075 := bstep (se 1 (by rfl) ⟨2287556, by rfl⟩ : syracuseStep 3050075 = 4575113) B4575113
theorem B15428191 : Blo 1805604 15428191 := bstep (se 1 (by rfl) ⟨11571143, by rfl⟩ : syracuseStep 15428191 = 23142287) B23142287
theorem B20859709 : Blo 1805604 20859709 := bstep (se 3 (by rfl) ⟨3911195, by rfl⟩ : syracuseStep 20859709 = 7822391) B7822391
theorem B6097787 : Blo 1805604 6097787 := bstep (se 1 (by rfl) ⟨4573340, by rfl⟩ : syracuseStep 6097787 = 9146681) B9146681
theorem B10284367 : Blo 1805604 10284367 := bstep (se 1 (by rfl) ⟨7713275, by rfl⟩ : syracuseStep 10284367 = 15426551) B15426551
theorem B1806587 : Blo 1805604 1806587 := bstep (se 1 (by rfl) ⟨1354940, by rfl⟩ : syracuseStep 1806587 = 2709881) B2709881
theorem B1806823 : Blo 1805604 1806823 := bstep (se 1 (by rfl) ⟨1355117, by rfl⟩ : syracuseStep 1806823 = 2710235) B2710235
theorem B1807055 : Blo 1805604 1807055 := bstep (se 1 (by rfl) ⟨1355291, by rfl⟩ : syracuseStep 1807055 = 2710583) B2710583
theorem B125129447 : Blo 1805604 125129447 := bstep (se 1 (by rfl) ⟨93847085, by rfl⟩ : syracuseStep 125129447 = 187694171) B187694171
theorem B2709611 : Blo 1805604 2709611 := bstep (se 1 (by rfl) ⟨2032208, by rfl⟩ : syracuseStep 2709611 = 4064417) B4064417
theorem B46307537 : Blo 1805604 46307537 := bstep (se 2 (by rfl) ⟨17365326, by rfl⟩ : syracuseStep 46307537 = 34730653) B34730653
theorem B6511337 : Blo 1805604 6511337 := bstep (se 2 (by rfl) ⟨2441751, by rfl⟩ : syracuseStep 6511337 = 4883503) B4883503
theorem B26753773 : Blo 1805604 26753773 := bstep (se 3 (by rfl) ⟨5016332, by rfl⟩ : syracuseStep 26753773 = 10032665) B10032665
theorem B2710505 : Blo 1805604 2710505 := bstep (se 2 (by rfl) ⟨1016439, by rfl⟩ : syracuseStep 2710505 = 2032879) B2032879
theorem B5144303 : Blo 1805604 5144303 := bstep (se 1 (by rfl) ⟨3858227, by rfl⟩ : syracuseStep 5144303 = 7716455) B7716455
theorem B9273199 : Blo 1805604 9273199 := bstep (se 1 (by rfl) ⟨6954899, by rfl⟩ : syracuseStep 9273199 = 13909799) B13909799
theorem B6512575 : Blo 1805604 6512575 := bstep (se 1 (by rfl) ⟨4884431, by rfl⟩ : syracuseStep 6512575 = 9768863) B9768863
theorem B4063679 : Blo 1805604 4063679 := bstep (se 1 (by rfl) ⟨3047759, by rfl⟩ : syracuseStep 4063679 = 6095519) B6095519
theorem B83419631 : Blo 1805604 83419631 := bstep (se 1 (by rfl) ⟨62564723, by rfl⟩ : syracuseStep 83419631 = 125129447) B125129447
theorem B20570921 : Blo 1805604 20570921 := bstep (se 2 (by rfl) ⟨7714095, by rfl⟩ : syracuseStep 20570921 = 15428191) B15428191
theorem B27812945 : Blo 1805604 27812945 := bstep (se 2 (by rfl) ⟨10429854, by rfl⟩ : syracuseStep 27812945 = 20859709) B20859709
theorem B2033383 : Blo 1805604 2033383 := bstep (se 1 (by rfl) ⟨1525037, by rfl⟩ : syracuseStep 2033383 = 3050075) B3050075
theorem B4065191 : Blo 1805604 4065191 := bstep (se 1 (by rfl) ⟨3048893, by rfl⟩ : syracuseStep 4065191 = 6097787) B6097787
theorem B12364265 : Blo 1805604 12364265 := bstep (se 2 (by rfl) ⟨4636599, by rfl⟩ : syracuseStep 12364265 = 9273199) B9273199
theorem B49458275 : Blo 1805604 49458275 := bstep (se 1 (by rfl) ⟨37093706, by rfl⟩ : syracuseStep 49458275 = 74187413) B74187413
theorem B35671697 : Blo 1805604 35671697 := bstep (se 2 (by rfl) ⟨13376886, by rfl⟩ : syracuseStep 35671697 = 26753773) B26753773
theorem B1806407 : Blo 1805604 1806407 := bstep (se 1 (by rfl) ⟨1354805, by rfl⟩ : syracuseStep 1806407 = 2709611) B2709611
theorem B30871691 : Blo 1805604 30871691 := bstep (se 1 (by rfl) ⟨23153768, by rfl⟩ : syracuseStep 30871691 = 46307537) B46307537
theorem B1807003 : Blo 1805604 1807003 := bstep (se 1 (by rfl) ⟨1355252, by rfl⟩ : syracuseStep 1807003 = 2710505) B2710505
theorem B3429535 : Blo 1805604 3429535 := bstep (se 1 (by rfl) ⟨2572151, by rfl⟩ : syracuseStep 3429535 = 5144303) B5144303
theorem B205871291 : Blo 1805604 205871291 := bstep (se 1 (by rfl) ⟨154403468, by rfl⟩ : syracuseStep 205871291 = 308806937) B308806937
theorem B13712489 : Blo 1805604 13712489 := bstep (se 2 (by rfl) ⟨5142183, by rfl⟩ : syracuseStep 13712489 = 10284367) B10284367
theorem B4340891 : Blo 1805604 4340891 := bstep (se 1 (by rfl) ⟨3255668, by rfl⟩ : syracuseStep 4340891 = 6511337) B6511337
theorem B2711081 : Blo 1805604 2711081 := bstep (se 2 (by rfl) ⟨1016655, by rfl⟩ : syracuseStep 2711081 = 2033311) B2033311
theorem B8683433 : Blo 1805604 8683433 := bstep (se 2 (by rfl) ⟨3256287, by rfl⟩ : syracuseStep 8683433 = 6512575) B6512575
theorem B11575709 : Blo 1805604 11575709 := bstep (se 3 (by rfl) ⟨2170445, by rfl⟩ : syracuseStep 11575709 = 4340891) B4340891
theorem B13713947 : Blo 1805604 13713947 := bstep (se 1 (by rfl) ⟨10285460, by rfl⟩ : syracuseStep 13713947 = 20570921) B20570921
theorem B4572713 : Blo 1805604 4572713 := bstep (se 2 (by rfl) ⟨1714767, by rfl⟩ : syracuseStep 4572713 = 3429535) B3429535
theorem B20581127 : Blo 1805604 20581127 := bstep (se 1 (by rfl) ⟨15435845, by rfl⟩ : syracuseStep 20581127 = 30871691) B30871691
theorem B18541963 : Blo 1805604 18541963 := bstep (se 1 (by rfl) ⟨13906472, by rfl⟩ : syracuseStep 18541963 = 27812945) B27812945
theorem B1807387 : Blo 1805604 1807387 := bstep (se 1 (by rfl) ⟨1355540, by rfl⟩ : syracuseStep 1807387 = 2711081) B2711081
theorem B5788955 : Blo 1805604 5788955 := bstep (se 1 (by rfl) ⟨4341716, by rfl⟩ : syracuseStep 5788955 = 8683433) B8683433
theorem B2709119 : Blo 1805604 2709119 := bstep (se 1 (by rfl) ⟨2031839, by rfl⟩ : syracuseStep 2709119 = 4063679) B4063679
theorem B55613087 : Blo 1805604 55613087 := bstep (se 1 (by rfl) ⟨41709815, by rfl⟩ : syracuseStep 55613087 = 83419631) B83419631
theorem B32971373 : Blo 1805604 32971373 := bstep (se 3 (by rfl) ⟨6182132, by rfl⟩ : syracuseStep 32971373 = 12364265) B12364265
theorem B2710127 : Blo 1805604 2710127 := bstep (se 1 (by rfl) ⟨2032595, by rfl⟩ : syracuseStep 2710127 = 4065191) B4065191
theorem B137247527 : Blo 1805604 137247527 := bstep (se 1 (by rfl) ⟨102935645, by rfl⟩ : syracuseStep 137247527 = 205871291) B205871291
theorem B32972183 : Blo 1805604 32972183 := bstep (se 1 (by rfl) ⟨24729137, by rfl⟩ : syracuseStep 32972183 = 49458275) B49458275
theorem B9141659 : Blo 1805604 9141659 := bstep (se 1 (by rfl) ⟨6856244, by rfl⟩ : syracuseStep 9141659 = 13712489) B13712489
theorem B2711177 : Blo 1805604 2711177 := bstep (se 2 (by rfl) ⟨1016691, by rfl⟩ : syracuseStep 2711177 = 2033383) B2033383
theorem B23781131 : Blo 1805604 23781131 := bstep (se 1 (by rfl) ⟨17835848, by rfl⟩ : syracuseStep 23781131 = 35671697) B35671697
theorem B7717139 : Blo 1805604 7717139 := bstep (se 1 (by rfl) ⟨5787854, by rfl⟩ : syracuseStep 7717139 = 11575709) B11575709
theorem B9142631 : Blo 1805604 9142631 := bstep (se 1 (by rfl) ⟨6856973, by rfl⟩ : syracuseStep 9142631 = 13713947) B13713947
theorem B3048475 : Blo 1805604 3048475 := bstep (se 1 (by rfl) ⟨2286356, by rfl⟩ : syracuseStep 3048475 = 4572713) B4572713
theorem B21980915 : Blo 1805604 21980915 := bstep (se 1 (by rfl) ⟨16485686, by rfl⟩ : syracuseStep 21980915 = 32971373) B32971373
theorem B91498351 : Blo 1805604 91498351 := bstep (se 1 (by rfl) ⟨68623763, by rfl⟩ : syracuseStep 91498351 = 137247527) B137247527
theorem B21981455 : Blo 1805604 21981455 := bstep (se 1 (by rfl) ⟨16486091, by rfl⟩ : syracuseStep 21981455 = 32972183) B32972183
theorem B15854087 : Blo 1805604 15854087 := bstep (se 1 (by rfl) ⟨11890565, by rfl⟩ : syracuseStep 15854087 = 23781131) B23781131
theorem B15437213 : Blo 1805604 15437213 := bstep (se 3 (by rfl) ⟨2894477, by rfl⟩ : syracuseStep 15437213 = 5788955) B5788955
theorem B1806079 : Blo 1805604 1806079 := bstep (se 1 (by rfl) ⟨1354559, by rfl⟩ : syracuseStep 1806079 = 2709119) B2709119
theorem B1806751 : Blo 1805604 1806751 := bstep (se 1 (by rfl) ⟨1355063, by rfl⟩ : syracuseStep 1806751 = 2710127) B2710127
theorem B98890469 : Blo 1805604 98890469 := bstep (se 4 (by rfl) ⟨9270981, by rfl⟩ : syracuseStep 98890469 = 18541963) B18541963
theorem B1807451 : Blo 1805604 1807451 := bstep (se 1 (by rfl) ⟨1355588, by rfl⟩ : syracuseStep 1807451 = 2711177) B2711177
theorem B37075391 : Blo 1805604 37075391 := bstep (se 1 (by rfl) ⟨27806543, by rfl⟩ : syracuseStep 37075391 = 55613087) B55613087
theorem B13720751 : Blo 1805604 13720751 := bstep (se 1 (by rfl) ⟨10290563, by rfl⟩ : syracuseStep 13720751 = 20581127) B20581127
theorem B6094439 : Blo 1805604 6094439 := bstep (se 1 (by rfl) ⟨4570829, by rfl⟩ : syracuseStep 6094439 = 9141659) B9141659
theorem B5144759 : Blo 1805604 5144759 := bstep (se 1 (by rfl) ⟨3858569, by rfl⟩ : syracuseStep 5144759 = 7717139) B7717139
theorem B6095087 : Blo 1805604 6095087 := bstep (se 1 (by rfl) ⟨4571315, by rfl⟩ : syracuseStep 6095087 = 9142631) B9142631
theorem B4064633 : Blo 1805604 4064633 := bstep (se 2 (by rfl) ⟨1524237, by rfl⟩ : syracuseStep 4064633 = 3048475) B3048475
theorem B24716927 : Blo 1805604 24716927 := bstep (se 1 (by rfl) ⟨18537695, by rfl⟩ : syracuseStep 24716927 = 37075391) B37075391
theorem B10291475 : Blo 1805604 10291475 := bstep (se 1 (by rfl) ⟨7718606, by rfl⟩ : syracuseStep 10291475 = 15437213) B15437213
theorem B121997801 : Blo 1805604 121997801 := bstep (se 2 (by rfl) ⟨45749175, by rfl⟩ : syracuseStep 121997801 = 91498351) B91498351
theorem B9147167 : Blo 1805604 9147167 := bstep (se 1 (by rfl) ⟨6860375, by rfl⟩ : syracuseStep 9147167 = 13720751) B13720751
theorem B65926979 : Blo 1805604 65926979 := bstep (se 1 (by rfl) ⟨49445234, by rfl⟩ : syracuseStep 65926979 = 98890469) B98890469
theorem B14653943 : Blo 1805604 14653943 := bstep (se 1 (by rfl) ⟨10990457, by rfl⟩ : syracuseStep 14653943 = 21980915) B21980915
theorem B42277565 : Blo 1805604 42277565 := bstep (se 3 (by rfl) ⟨7927043, by rfl⟩ : syracuseStep 42277565 = 15854087) B15854087
theorem B14654303 : Blo 1805604 14654303 := bstep (se 1 (by rfl) ⟨10990727, by rfl⟩ : syracuseStep 14654303 = 21981455) B21981455
theorem B4062959 : Blo 1805604 4062959 := bstep (se 1 (by rfl) ⟨3047219, by rfl⟩ : syracuseStep 4062959 = 6094439) B6094439
theorem B4063391 : Blo 1805604 4063391 := bstep (se 1 (by rfl) ⟨3047543, by rfl⟩ : syracuseStep 4063391 = 6095087) B6095087
theorem B43951319 : Blo 1805604 43951319 := bstep (se 1 (by rfl) ⟨32963489, by rfl⟩ : syracuseStep 43951319 = 65926979) B65926979
theorem B81331867 : Blo 1805604 81331867 := bstep (se 1 (by rfl) ⟨60998900, by rfl⟩ : syracuseStep 81331867 = 121997801) B121997801
theorem B6098111 : Blo 1805604 6098111 := bstep (se 1 (by rfl) ⟨4573583, by rfl⟩ : syracuseStep 6098111 = 9147167) B9147167
theorem B6860983 : Blo 1805604 6860983 := bstep (se 1 (by rfl) ⟨5145737, by rfl⟩ : syracuseStep 6860983 = 10291475) B10291475
theorem B9769295 : Blo 1805604 9769295 := bstep (se 1 (by rfl) ⟨7326971, by rfl⟩ : syracuseStep 9769295 = 14653943) B14653943
theorem B28185043 : Blo 1805604 28185043 := bstep (se 1 (by rfl) ⟨21138782, by rfl⟩ : syracuseStep 28185043 = 42277565) B42277565
theorem B9769535 : Blo 1805604 9769535 := bstep (se 1 (by rfl) ⟨7327151, by rfl⟩ : syracuseStep 9769535 = 14654303) B14654303
theorem B2708639 : Blo 1805604 2708639 := bstep (se 1 (by rfl) ⟨2031479, by rfl⟩ : syracuseStep 2708639 = 4062959) B4062959
theorem B3429839 : Blo 1805604 3429839 := bstep (se 1 (by rfl) ⟨2572379, by rfl⟩ : syracuseStep 3429839 = 5144759) B5144759
theorem B2709755 : Blo 1805604 2709755 := bstep (se 1 (by rfl) ⟨2032316, by rfl⟩ : syracuseStep 2709755 = 4064633) B4064633
theorem B65911805 : Blo 1805604 65911805 := bstep (se 3 (by rfl) ⟨12358463, by rfl⟩ : syracuseStep 65911805 = 24716927) B24716927
theorem B6513023 : Blo 1805604 6513023 := bstep (se 1 (by rfl) ⟨4884767, by rfl⟩ : syracuseStep 6513023 = 9769535) B9769535
theorem B26051453 : Blo 1805604 26051453 := bstep (se 3 (by rfl) ⟨4884647, by rfl⟩ : syracuseStep 26051453 = 9769295) B9769295
theorem B2286559 : Blo 1805604 2286559 := bstep (se 1 (by rfl) ⟨1714919, by rfl⟩ : syracuseStep 2286559 = 3429839) B3429839
theorem B4065407 : Blo 1805604 4065407 := bstep (se 1 (by rfl) ⟨3049055, by rfl⟩ : syracuseStep 4065407 = 6098111) B6098111
theorem B37580057 : Blo 1805604 37580057 := bstep (se 2 (by rfl) ⟨14092521, by rfl⟩ : syracuseStep 37580057 = 28185043) B28185043
theorem B1805759 : Blo 1805604 1805759 := bstep (se 1 (by rfl) ⟨1354319, by rfl⟩ : syracuseStep 1805759 = 2708639) B2708639
theorem B1806503 : Blo 1805604 1806503 := bstep (se 1 (by rfl) ⟨1354877, by rfl⟩ : syracuseStep 1806503 = 2709755) B2709755
theorem B108442489 : Blo 1805604 108442489 := bstep (se 2 (by rfl) ⟨40665933, by rfl⟩ : syracuseStep 108442489 = 81331867) B81331867
theorem B2708927 : Blo 1805604 2708927 := bstep (se 1 (by rfl) ⟨2031695, by rfl⟩ : syracuseStep 2708927 = 4063391) B4063391
theorem B9147977 : Blo 1805604 9147977 := bstep (se 2 (by rfl) ⟨3430491, by rfl⟩ : syracuseStep 9147977 = 6860983) B6860983
theorem B29300879 : Blo 1805604 29300879 := bstep (se 1 (by rfl) ⟨21975659, by rfl⟩ : syracuseStep 29300879 = 43951319) B43951319
theorem B43941203 : Blo 1805604 43941203 := bstep (se 1 (by rfl) ⟨32955902, by rfl⟩ : syracuseStep 43941203 = 65911805) B65911805
theorem B4342015 : Blo 1805604 4342015 := bstep (se 1 (by rfl) ⟨3256511, by rfl⟩ : syracuseStep 4342015 = 6513023) B6513023
theorem B17367635 : Blo 1805604 17367635 := bstep (se 1 (by rfl) ⟨13025726, by rfl⟩ : syracuseStep 17367635 = 26051453) B26051453
theorem B144589985 : Blo 1805604 144589985 := bstep (se 2 (by rfl) ⟨54221244, by rfl⟩ : syracuseStep 144589985 = 108442489) B108442489
theorem B3048745 : Blo 1805604 3048745 := bstep (se 2 (by rfl) ⟨1143279, by rfl⟩ : syracuseStep 3048745 = 2286559) B2286559
theorem B25053371 : Blo 1805604 25053371 := bstep (se 1 (by rfl) ⟨18790028, by rfl⟩ : syracuseStep 25053371 = 37580057) B37580057
theorem B1805951 : Blo 1805604 1805951 := bstep (se 1 (by rfl) ⟨1354463, by rfl⟩ : syracuseStep 1805951 = 2708927) B2708927
theorem B6098651 : Blo 1805604 6098651 := bstep (se 1 (by rfl) ⟨4573988, by rfl⟩ : syracuseStep 6098651 = 9147977) B9147977
theorem B19533919 : Blo 1805604 19533919 := bstep (se 1 (by rfl) ⟨14650439, by rfl⟩ : syracuseStep 19533919 = 29300879) B29300879
theorem B2710271 : Blo 1805604 2710271 := bstep (se 1 (by rfl) ⟨2032703, by rfl⟩ : syracuseStep 2710271 = 4065407) B4065407
theorem B29294135 : Blo 1805604 29294135 := bstep (se 1 (by rfl) ⟨21970601, by rfl⟩ : syracuseStep 29294135 = 43941203) B43941203
theorem B4064993 : Blo 1805604 4064993 := bstep (se 2 (by rfl) ⟨1524372, by rfl⟩ : syracuseStep 4064993 = 3048745) B3048745
theorem B4065767 : Blo 1805604 4065767 := bstep (se 1 (by rfl) ⟨3049325, by rfl⟩ : syracuseStep 4065767 = 6098651) B6098651
theorem B26045225 : Blo 1805604 26045225 := bstep (se 2 (by rfl) ⟨9766959, by rfl⟩ : syracuseStep 26045225 = 19533919) B19533919
theorem B11578423 : Blo 1805604 11578423 := bstep (se 1 (by rfl) ⟨8683817, by rfl⟩ : syracuseStep 11578423 = 17367635) B17367635
theorem B1806847 : Blo 1805604 1806847 := bstep (se 1 (by rfl) ⟨1355135, by rfl⟩ : syracuseStep 1806847 = 2710271) B2710271
theorem B96393323 : Blo 1805604 96393323 := bstep (se 1 (by rfl) ⟨72294992, by rfl⟩ : syracuseStep 96393323 = 144589985) B144589985
theorem B23157413 : Blo 1805604 23157413 := bstep (se 4 (by rfl) ⟨2171007, by rfl⟩ : syracuseStep 23157413 = 4342015) B4342015
theorem B16702247 : Blo 1805604 16702247 := bstep (se 1 (by rfl) ⟨12526685, by rfl⟩ : syracuseStep 16702247 = 25053371) B25053371
theorem B19529423 : Blo 1805604 19529423 := bstep (se 1 (by rfl) ⟨14647067, by rfl⟩ : syracuseStep 19529423 = 29294135) B29294135
theorem B11134831 : Blo 1805604 11134831 := bstep (se 1 (by rfl) ⟨8351123, by rfl⟩ : syracuseStep 11134831 = 16702247) B16702247
theorem B13019615 : Blo 1805604 13019615 := bstep (se 1 (by rfl) ⟨9764711, by rfl⟩ : syracuseStep 13019615 = 19529423) B19529423
theorem B64262215 : Blo 1805604 64262215 := bstep (se 1 (by rfl) ⟨48196661, by rfl⟩ : syracuseStep 64262215 = 96393323) B96393323
theorem B15437897 : Blo 1805604 15437897 := bstep (se 2 (by rfl) ⟨5789211, by rfl⟩ : syracuseStep 15437897 = 11578423) B11578423
theorem B15438275 : Blo 1805604 15438275 := bstep (se 1 (by rfl) ⟨11578706, by rfl⟩ : syracuseStep 15438275 = 23157413) B23157413
theorem B17363483 : Blo 1805604 17363483 := bstep (se 1 (by rfl) ⟨13022612, by rfl⟩ : syracuseStep 17363483 = 26045225) B26045225
theorem B2709995 : Blo 1805604 2709995 := bstep (se 1 (by rfl) ⟨2032496, by rfl⟩ : syracuseStep 2709995 = 4064993) B4064993
theorem B2710511 : Blo 1805604 2710511 := bstep (se 1 (by rfl) ⟨2032883, by rfl⟩ : syracuseStep 2710511 = 4065767) B4065767
theorem B11575655 : Blo 1805604 11575655 := bstep (se 1 (by rfl) ⟨8681741, by rfl⟩ : syracuseStep 11575655 = 17363483) B17363483
theorem B14846441 : Blo 1805604 14846441 := bstep (se 2 (by rfl) ⟨5567415, by rfl⟩ : syracuseStep 14846441 = 11134831) B11134831
theorem B10291931 : Blo 1805604 10291931 := bstep (se 1 (by rfl) ⟨7718948, by rfl⟩ : syracuseStep 10291931 = 15437897) B15437897
theorem B85682953 : Blo 1805604 85682953 := bstep (se 2 (by rfl) ⟨32131107, by rfl⟩ : syracuseStep 85682953 = 64262215) B64262215
theorem B10292183 : Blo 1805604 10292183 := bstep (se 1 (by rfl) ⟨7719137, by rfl⟩ : syracuseStep 10292183 = 15438275) B15438275
theorem B8679743 : Blo 1805604 8679743 := bstep (se 1 (by rfl) ⟨6509807, by rfl⟩ : syracuseStep 8679743 = 13019615) B13019615
theorem B1806663 : Blo 1805604 1806663 := bstep (se 1 (by rfl) ⟨1354997, by rfl⟩ : syracuseStep 1806663 = 2709995) B2709995
theorem B1807007 : Blo 1805604 1807007 := bstep (se 1 (by rfl) ⟨1355255, by rfl⟩ : syracuseStep 1807007 = 2710511) B2710511
theorem B7717103 : Blo 1805604 7717103 := bstep (se 1 (by rfl) ⟨5787827, by rfl⟩ : syracuseStep 7717103 = 11575655) B11575655
theorem B456975749 : Blo 1805604 456975749 := bstep (se 4 (by rfl) ⟨42841476, by rfl⟩ : syracuseStep 456975749 = 85682953) B85682953
theorem B158362037 : Blo 1805604 158362037 := bstep (se 5 (by rfl) ⟨7423220, by rfl⟩ : syracuseStep 158362037 = 14846441) B14846441
theorem B5786495 : Blo 1805604 5786495 := bstep (se 1 (by rfl) ⟨4339871, by rfl⟩ : syracuseStep 5786495 = 8679743) B8679743
theorem B6861287 : Blo 1805604 6861287 := bstep (se 1 (by rfl) ⟨5145965, by rfl⟩ : syracuseStep 6861287 = 10291931) B10291931
theorem B6861455 : Blo 1805604 6861455 := bstep (se 1 (by rfl) ⟨5146091, by rfl⟩ : syracuseStep 6861455 = 10292183) B10292183
theorem B5144735 : Blo 1805604 5144735 := bstep (se 1 (by rfl) ⟨3858551, by rfl⟩ : syracuseStep 5144735 = 7717103) B7717103
theorem B4574191 : Blo 1805604 4574191 := bstep (se 1 (by rfl) ⟨3430643, by rfl⟩ : syracuseStep 4574191 = 6861287) B6861287
theorem B4574303 : Blo 1805604 4574303 := bstep (se 1 (by rfl) ⟨3430727, by rfl⟩ : syracuseStep 4574303 = 6861455) B6861455
theorem B105574691 : Blo 1805604 105574691 := bstep (se 1 (by rfl) ⟨79181018, by rfl⟩ : syracuseStep 105574691 = 158362037) B158362037
theorem B304650499 : Blo 1805604 304650499 := bstep (se 1 (by rfl) ⟨228487874, by rfl⟩ : syracuseStep 304650499 = 456975749) B456975749
theorem B3857663 : Blo 1805604 3857663 := bstep (se 1 (by rfl) ⟨2893247, by rfl⟩ : syracuseStep 3857663 = 5786495) B5786495
theorem B406200665 : Blo 1805604 406200665 := bstep (se 2 (by rfl) ⟨152325249, by rfl⟩ : syracuseStep 406200665 = 304650499) B304650499
theorem B3049535 : Blo 1805604 3049535 := bstep (se 1 (by rfl) ⟨2287151, by rfl⟩ : syracuseStep 3049535 = 4574303) B4574303
theorem B6098921 : Blo 1805604 6098921 := bstep (se 2 (by rfl) ⟨2287095, by rfl⟩ : syracuseStep 6098921 = 4574191) B4574191
theorem B13719293 : Blo 1805604 13719293 := bstep (se 3 (by rfl) ⟨2572367, by rfl⟩ : syracuseStep 13719293 = 5144735) B5144735
theorem B10287101 : Blo 1805604 10287101 := bstep (se 3 (by rfl) ⟨1928831, by rfl⟩ : syracuseStep 10287101 = 3857663) B3857663
theorem B281532509 : Blo 1805604 281532509 := bstep (se 3 (by rfl) ⟨52787345, by rfl⟩ : syracuseStep 281532509 = 105574691) B105574691
theorem B6858067 : Blo 1805604 6858067 := bstep (se 1 (by rfl) ⟨5143550, by rfl⟩ : syracuseStep 6858067 = 10287101) B10287101
theorem B2033023 : Blo 1805604 2033023 := bstep (se 1 (by rfl) ⟨1524767, by rfl⟩ : syracuseStep 2033023 = 3049535) B3049535
theorem B187688339 : Blo 1805604 187688339 := bstep (se 1 (by rfl) ⟨140766254, by rfl⟩ : syracuseStep 187688339 = 281532509) B281532509
theorem B4065947 : Blo 1805604 4065947 := bstep (se 1 (by rfl) ⟨3049460, by rfl⟩ : syracuseStep 4065947 = 6098921) B6098921
theorem B9146195 : Blo 1805604 9146195 := bstep (se 1 (by rfl) ⟨6859646, by rfl⟩ : syracuseStep 9146195 = 13719293) B13719293
theorem B270800443 : Blo 1805604 270800443 := bstep (se 1 (by rfl) ⟨203100332, by rfl⟩ : syracuseStep 270800443 = 406200665) B406200665
theorem B125125559 : Blo 1805604 125125559 := bstep (se 1 (by rfl) ⟨93844169, by rfl⟩ : syracuseStep 125125559 = 187688339) B187688339
theorem B9144089 : Blo 1805604 9144089 := bstep (se 2 (by rfl) ⟨3429033, by rfl⟩ : syracuseStep 9144089 = 6858067) B6858067
theorem B6097463 : Blo 1805604 6097463 := bstep (se 1 (by rfl) ⟨4573097, by rfl⟩ : syracuseStep 6097463 = 9146195) B9146195
theorem B361067257 : Blo 1805604 361067257 := bstep (se 2 (by rfl) ⟨135400221, by rfl⟩ : syracuseStep 361067257 = 270800443) B270800443
theorem B2710631 : Blo 1805604 2710631 := bstep (se 1 (by rfl) ⟨2032973, by rfl⟩ : syracuseStep 2710631 = 4065947) B4065947
theorem B2710697 : Blo 1805604 2710697 := bstep (se 2 (by rfl) ⟨1016511, by rfl⟩ : syracuseStep 2710697 = 2033023) B2033023
theorem B6096059 : Blo 1805604 6096059 := bstep (se 1 (by rfl) ⟨4572044, by rfl⟩ : syracuseStep 6096059 = 9144089) B9144089
theorem B4064975 : Blo 1805604 4064975 := bstep (se 1 (by rfl) ⟨3048731, by rfl⟩ : syracuseStep 4064975 = 6097463) B6097463
theorem B481423009 : Blo 1805604 481423009 := bstep (se 2 (by rfl) ⟨180533628, by rfl⟩ : syracuseStep 481423009 = 361067257) B361067257
theorem B1807087 : Blo 1805604 1807087 := bstep (se 1 (by rfl) ⟨1355315, by rfl⟩ : syracuseStep 1807087 = 2710631) B2710631
theorem B1807131 : Blo 1805604 1807131 := bstep (se 1 (by rfl) ⟨1355348, by rfl⟩ : syracuseStep 1807131 = 2710697) B2710697
theorem B83417039 : Blo 1805604 83417039 := bstep (se 1 (by rfl) ⟨62562779, by rfl⟩ : syracuseStep 83417039 = 125125559) B125125559
theorem B4064039 : Blo 1805604 4064039 := bstep (se 1 (by rfl) ⟨3048029, by rfl⟩ : syracuseStep 4064039 = 6096059) B6096059
theorem B55611359 : Blo 1805604 55611359 := bstep (se 1 (by rfl) ⟨41708519, by rfl⟩ : syracuseStep 55611359 = 83417039) B83417039
theorem B641897345 : Blo 1805604 641897345 := bstep (se 2 (by rfl) ⟨240711504, by rfl⟩ : syracuseStep 641897345 = 481423009) B481423009
theorem B2709983 : Blo 1805604 2709983 := bstep (se 1 (by rfl) ⟨2032487, by rfl⟩ : syracuseStep 2709983 = 4064975) B4064975
theorem B1806655 : Blo 1805604 1806655 := bstep (se 1 (by rfl) ⟨1354991, by rfl⟩ : syracuseStep 1806655 = 2709983) B2709983
theorem B37074239 : Blo 1805604 37074239 := bstep (se 1 (by rfl) ⟨27805679, by rfl⟩ : syracuseStep 37074239 = 55611359) B55611359
theorem B2709359 : Blo 1805604 2709359 := bstep (se 1 (by rfl) ⟨2032019, by rfl⟩ : syracuseStep 2709359 = 4064039) B4064039
theorem B1711726253 : Blo 1805604 1711726253 := bstep (se 3 (by rfl) ⟨320948672, by rfl⟩ : syracuseStep 1711726253 = 641897345) B641897345
theorem B24716159 : Blo 1805604 24716159 := bstep (se 1 (by rfl) ⟨18537119, by rfl⟩ : syracuseStep 24716159 = 37074239) B37074239
theorem B1806239 : Blo 1805604 1806239 := bstep (se 1 (by rfl) ⟨1354679, by rfl⟩ : syracuseStep 1806239 = 2709359) B2709359
theorem B1141150835 : Blo 1805604 1141150835 := bstep (se 1 (by rfl) ⟨855863126, by rfl⟩ : syracuseStep 1141150835 = 1711726253) B1711726253
theorem B760767223 : Blo 1805604 760767223 := bstep (se 1 (by rfl) ⟨570575417, by rfl⟩ : syracuseStep 760767223 = 1141150835) B1141150835
theorem B16477439 : Blo 1805604 16477439 := bstep (se 1 (by rfl) ⟨12358079, by rfl⟩ : syracuseStep 16477439 = 24716159) B24716159
theorem B43939837 : Blo 1805604 43939837 := bstep (se 3 (by rfl) ⟨8238719, by rfl⟩ : syracuseStep 43939837 = 16477439) B16477439
theorem B1014356297 : Blo 1805604 1014356297 := bstep (se 2 (by rfl) ⟨380383611, by rfl⟩ : syracuseStep 1014356297 = 760767223) B760767223
theorem B676237531 : Blo 1805604 676237531 := bstep (se 1 (by rfl) ⟨507178148, by rfl⟩ : syracuseStep 676237531 = 1014356297) B1014356297
theorem B58586449 : Blo 1805604 58586449 := bstep (se 2 (by rfl) ⟨21969918, by rfl⟩ : syracuseStep 58586449 = 43939837) B43939837
theorem B78115265 : Blo 1805604 78115265 := bstep (se 2 (by rfl) ⟨29293224, by rfl⟩ : syracuseStep 78115265 = 58586449) B58586449
theorem B901650041 : Blo 1805604 901650041 := bstep (se 2 (by rfl) ⟨338118765, by rfl⟩ : syracuseStep 901650041 = 676237531) B676237531
theorem B52076843 : Blo 1805604 52076843 := bstep (se 1 (by rfl) ⟨39057632, by rfl⟩ : syracuseStep 52076843 = 78115265) B78115265
theorem B601100027 : Blo 1805604 601100027 := bstep (se 1 (by rfl) ⟨450825020, by rfl⟩ : syracuseStep 601100027 = 901650041) B901650041
theorem B34717895 : Blo 1805604 34717895 := bstep (se 1 (by rfl) ⟨26038421, by rfl⟩ : syracuseStep 34717895 = 52076843) B52076843
theorem B400733351 : Blo 1805604 400733351 := bstep (se 1 (by rfl) ⟨300550013, by rfl⟩ : syracuseStep 400733351 = 601100027) B601100027
theorem B23145263 : Blo 1805604 23145263 := bstep (se 1 (by rfl) ⟨17358947, by rfl⟩ : syracuseStep 23145263 = 34717895) B34717895
theorem B267155567 : Blo 1805604 267155567 := bstep (se 1 (by rfl) ⟨200366675, by rfl⟩ : syracuseStep 267155567 = 400733351) B400733351
theorem B178103711 : Blo 1805604 178103711 := bstep (se 1 (by rfl) ⟨133577783, by rfl⟩ : syracuseStep 178103711 = 267155567) B267155567
theorem B15430175 : Blo 1805604 15430175 := bstep (se 1 (by rfl) ⟨11572631, by rfl⟩ : syracuseStep 15430175 = 23145263) B23145263
theorem B118735807 : Blo 1805604 118735807 := bstep (se 1 (by rfl) ⟨89051855, by rfl⟩ : syracuseStep 118735807 = 178103711) B178103711
theorem B10286783 : Blo 1805604 10286783 := bstep (se 1 (by rfl) ⟨7715087, by rfl⟩ : syracuseStep 10286783 = 15430175) B15430175
theorem B6857855 : Blo 1805604 6857855 := bstep (se 1 (by rfl) ⟨5143391, by rfl⟩ : syracuseStep 6857855 = 10286783) B10286783
theorem B158314409 : Blo 1805604 158314409 := bstep (se 2 (by rfl) ⟨59367903, by rfl⟩ : syracuseStep 158314409 = 118735807) B118735807
theorem B4571903 : Blo 1805604 4571903 := bstep (se 1 (by rfl) ⟨3428927, by rfl⟩ : syracuseStep 4571903 = 6857855) B6857855
theorem B105542939 : Blo 1805604 105542939 := bstep (se 1 (by rfl) ⟨79157204, by rfl⟩ : syracuseStep 105542939 = 158314409) B158314409
theorem B3047935 : Blo 1805604 3047935 := bstep (se 1 (by rfl) ⟨2285951, by rfl⟩ : syracuseStep 3047935 = 4571903) B4571903
theorem B70361959 : Blo 1805604 70361959 := bstep (se 1 (by rfl) ⟨52771469, by rfl⟩ : syracuseStep 70361959 = 105542939) B105542939
theorem B4063913 : Blo 1805604 4063913 := bstep (se 2 (by rfl) ⟨1523967, by rfl⟩ : syracuseStep 4063913 = 3047935) B3047935
theorem B93815945 : Blo 1805604 93815945 := bstep (se 2 (by rfl) ⟨35180979, by rfl⟩ : syracuseStep 93815945 = 70361959) B70361959
theorem B2709275 : Blo 1805604 2709275 := bstep (se 1 (by rfl) ⟨2031956, by rfl⟩ : syracuseStep 2709275 = 4063913) B4063913
theorem B62543963 : Blo 1805604 62543963 := bstep (se 1 (by rfl) ⟨46907972, by rfl⟩ : syracuseStep 62543963 = 93815945) B93815945
theorem B1806183 : Blo 1805604 1806183 := bstep (se 1 (by rfl) ⟨1354637, by rfl⟩ : syracuseStep 1806183 = 2709275) B2709275
theorem B41695975 : Blo 1805604 41695975 := bstep (se 1 (by rfl) ⟨31271981, by rfl⟩ : syracuseStep 41695975 = 62543963) B62543963
theorem B55594633 : Blo 1805604 55594633 := bstep (se 2 (by rfl) ⟨20847987, by rfl⟩ : syracuseStep 55594633 = 41695975) B41695975
theorem B74126177 : Blo 1805604 74126177 := bstep (se 2 (by rfl) ⟨27797316, by rfl⟩ : syracuseStep 74126177 = 55594633) B55594633
theorem B49417451 : Blo 1805604 49417451 := bstep (se 1 (by rfl) ⟨37063088, by rfl⟩ : syracuseStep 49417451 = 74126177) B74126177
theorem B32944967 : Blo 1805604 32944967 := bstep (se 1 (by rfl) ⟨24708725, by rfl⟩ : syracuseStep 32944967 = 49417451) B49417451
theorem B21963311 : Blo 1805604 21963311 := bstep (se 1 (by rfl) ⟨16472483, by rfl⟩ : syracuseStep 21963311 = 32944967) B32944967
theorem B14642207 : Blo 1805604 14642207 := bstep (se 1 (by rfl) ⟨10981655, by rfl⟩ : syracuseStep 14642207 = 21963311) B21963311
theorem B9761471 : Blo 1805604 9761471 := bstep (se 1 (by rfl) ⟨7321103, by rfl⟩ : syracuseStep 9761471 = 14642207) B14642207
theorem B6507647 : Blo 1805604 6507647 := bstep (se 1 (by rfl) ⟨4880735, by rfl⟩ : syracuseStep 6507647 = 9761471) B9761471
theorem B4338431 : Blo 1805604 4338431 := bstep (se 1 (by rfl) ⟨3253823, by rfl⟩ : syracuseStep 4338431 = 6507647) B6507647
theorem B2892287 : Blo 1805604 2892287 := bstep (se 1 (by rfl) ⟨2169215, by rfl⟩ : syracuseStep 2892287 = 4338431) B4338431
theorem B7712765 : Blo 1805604 7712765 := bstep (se 3 (by rfl) ⟨1446143, by rfl⟩ : syracuseStep 7712765 = 2892287) B2892287
theorem B5141843 : Blo 1805604 5141843 := bstep (se 1 (by rfl) ⟨3856382, by rfl⟩ : syracuseStep 5141843 = 7712765) B7712765
theorem B3427895 : Blo 1805604 3427895 := bstep (se 1 (by rfl) ⟨2570921, by rfl⟩ : syracuseStep 3427895 = 5141843) B5141843
theorem B2285263 : Blo 1805604 2285263 := bstep (se 1 (by rfl) ⟨1713947, by rfl⟩ : syracuseStep 2285263 = 3427895) B3427895
theorem B3047017 : Blo 1805604 3047017 := bstep (se 2 (by rfl) ⟨1142631, by rfl⟩ : syracuseStep 3047017 = 2285263) B2285263
theorem B4062689 : Blo 1805604 4062689 := bstep (se 2 (by rfl) ⟨1523508, by rfl⟩ : syracuseStep 4062689 = 3047017) B3047017
theorem B2708459 : Blo 1805604 2708459 := bstep (se 1 (by rfl) ⟨2031344, by rfl⟩ : syracuseStep 2708459 = 4062689) B4062689
theorem B1805639 : Blo 1805604 1805639 := bstep (se 1 (by rfl) ⟨1354229, by rfl⟩ : syracuseStep 1805639 = 2708459) B2708459

theorem C0 (j : ℕ) (h1 : 451401 ≤ j) (h2 : j ≤ 451900) : Blo 1805604 (4 * j + 3) := by
  interval_cases j
  · exact B1805607
  · exact B1805611
  · exact B1805615
  · exact B1805619
  · exact B1805623
  · exact B1805627
  · exact B1805631
  · exact B1805635
  · exact B1805639
  · exact B1805643
  · exact B1805647
  · exact B1805651
  · exact B1805655
  · exact B1805659
  · exact B1805663
  · exact B1805667
  · exact B1805671
  · exact B1805675
  · exact B1805679
  · exact B1805683
  · exact B1805687
  · exact B1805691
  · exact B1805695
  · exact B1805699
  · exact B1805703
  · exact B1805707
  · exact B1805711
  · exact B1805715
  · exact B1805719
  · exact B1805723
  · exact B1805727
  · exact B1805731
  · exact B1805735
  · exact B1805739
  · exact B1805743
  · exact B1805747
  · exact B1805751
  · exact B1805755
  · exact B1805759
  · exact B1805763
  · exact B1805767
  · exact B1805771
  · exact B1805775
  · exact B1805779
  · exact B1805783
  · exact B1805787
  · exact B1805791
  · exact B1805795
  · exact B1805799
  · exact B1805803
  · exact B1805807
  · exact B1805811
  · exact B1805815
  · exact B1805819
  · exact B1805823
  · exact B1805827
  · exact B1805831
  · exact B1805835
  · exact B1805839
  · exact B1805843
  · exact B1805847
  · exact B1805851
  · exact B1805855
  · exact B1805859
  · exact B1805863
  · exact B1805867
  · exact B1805871
  · exact B1805875
  · exact B1805879
  · exact B1805883
  · exact B1805887
  · exact B1805891
  · exact B1805895
  · exact B1805899
  · exact B1805903
  · exact B1805907
  · exact B1805911
  · exact B1805915
  · exact B1805919
  · exact B1805923
  · exact B1805927
  · exact B1805931
  · exact B1805935
  · exact B1805939
  · exact B1805943
  · exact B1805947
  · exact B1805951
  · exact B1805955
  · exact B1805959
  · exact B1805963
  · exact B1805967
  · exact B1805971
  · exact B1805975
  · exact B1805979
  · exact B1805983
  · exact B1805987
  · exact B1805991
  · exact B1805995
  · exact B1805999
  · exact B1806003
  · exact B1806007
  · exact B1806011
  · exact B1806015
  · exact B1806019
  · exact B1806023
  · exact B1806027
  · exact B1806031
  · exact B1806035
  · exact B1806039
  · exact B1806043
  · exact B1806047
  · exact B1806051
  · exact B1806055
  · exact B1806059
  · exact B1806063
  · exact B1806067
  · exact B1806071
  · exact B1806075
  · exact B1806079
  · exact B1806083
  · exact B1806087
  · exact B1806091
  · exact B1806095
  · exact B1806099
  · exact B1806103
  · exact B1806107
  · exact B1806111
  · exact B1806115
  · exact B1806119
  · exact B1806123
  · exact B1806127
  · exact B1806131
  · exact B1806135
  · exact B1806139
  · exact B1806143
  · exact B1806147
  · exact B1806151
  · exact B1806155
  · exact B1806159
  · exact B1806163
  · exact B1806167
  · exact B1806171
  · exact B1806175
  · exact B1806179
  · exact B1806183
  · exact B1806187
  · exact B1806191
  · exact B1806195
  · exact B1806199
  · exact B1806203
  · exact B1806207
  · exact B1806211
  · exact B1806215
  · exact B1806219
  · exact B1806223
  · exact B1806227
  · exact B1806231
  · exact B1806235
  · exact B1806239
  · exact B1806243
  · exact B1806247
  · exact B1806251
  · exact B1806255
  · exact B1806259
  · exact B1806263
  · exact B1806267
  · exact B1806271
  · exact B1806275
  · exact B1806279
  · exact B1806283
  · exact B1806287
  · exact B1806291
  · exact B1806295
  · exact B1806299
  · exact B1806303
  · exact B1806307
  · exact B1806311
  · exact B1806315
  · exact B1806319
  · exact B1806323
  · exact B1806327
  · exact B1806331
  · exact B1806335
  · exact B1806339
  · exact B1806343
  · exact B1806347
  · exact B1806351
  · exact B1806355
  · exact B1806359
  · exact B1806363
  · exact B1806367
  · exact B1806371
  · exact B1806375
  · exact B1806379
  · exact B1806383
  · exact B1806387
  · exact B1806391
  · exact B1806395
  · exact B1806399
  · exact B1806403
  · exact B1806407
  · exact B1806411
  · exact B1806415
  · exact B1806419
  · exact B1806423
  · exact B1806427
  · exact B1806431
  · exact B1806435
  · exact B1806439
  · exact B1806443
  · exact B1806447
  · exact B1806451
  · exact B1806455
  · exact B1806459
  · exact B1806463
  · exact B1806467
  · exact B1806471
  · exact B1806475
  · exact B1806479
  · exact B1806483
  · exact B1806487
  · exact B1806491
  · exact B1806495
  · exact B1806499
  · exact B1806503
  · exact B1806507
  · exact B1806511
  · exact B1806515
  · exact B1806519
  · exact B1806523
  · exact B1806527
  · exact B1806531
  · exact B1806535
  · exact B1806539
  · exact B1806543
  · exact B1806547
  · exact B1806551
  · exact B1806555
  · exact B1806559
  · exact B1806563
  · exact B1806567
  · exact B1806571
  · exact B1806575
  · exact B1806579
  · exact B1806583
  · exact B1806587
  · exact B1806591
  · exact B1806595
  · exact B1806599
  · exact B1806603
  · exact B1806607
  · exact B1806611
  · exact B1806615
  · exact B1806619
  · exact B1806623
  · exact B1806627
  · exact B1806631
  · exact B1806635
  · exact B1806639
  · exact B1806643
  · exact B1806647
  · exact B1806651
  · exact B1806655
  · exact B1806659
  · exact B1806663
  · exact B1806667
  · exact B1806671
  · exact B1806675
  · exact B1806679
  · exact B1806683
  · exact B1806687
  · exact B1806691
  · exact B1806695
  · exact B1806699
  · exact B1806703
  · exact B1806707
  · exact B1806711
  · exact B1806715
  · exact B1806719
  · exact B1806723
  · exact B1806727
  · exact B1806731
  · exact B1806735
  · exact B1806739
  · exact B1806743
  · exact B1806747
  · exact B1806751
  · exact B1806755
  · exact B1806759
  · exact B1806763
  · exact B1806767
  · exact B1806771
  · exact B1806775
  · exact B1806779
  · exact B1806783
  · exact B1806787
  · exact B1806791
  · exact B1806795
  · exact B1806799
  · exact B1806803
  · exact B1806807
  · exact B1806811
  · exact B1806815
  · exact B1806819
  · exact B1806823
  · exact B1806827
  · exact B1806831
  · exact B1806835
  · exact B1806839
  · exact B1806843
  · exact B1806847
  · exact B1806851
  · exact B1806855
  · exact B1806859
  · exact B1806863
  · exact B1806867
  · exact B1806871
  · exact B1806875
  · exact B1806879
  · exact B1806883
  · exact B1806887
  · exact B1806891
  · exact B1806895
  · exact B1806899
  · exact B1806903
  · exact B1806907
  · exact B1806911
  · exact B1806915
  · exact B1806919
  · exact B1806923
  · exact B1806927
  · exact B1806931
  · exact B1806935
  · exact B1806939
  · exact B1806943
  · exact B1806947
  · exact B1806951
  · exact B1806955
  · exact B1806959
  · exact B1806963
  · exact B1806967
  · exact B1806971
  · exact B1806975
  · exact B1806979
  · exact B1806983
  · exact B1806987
  · exact B1806991
  · exact B1806995
  · exact B1806999
  · exact B1807003
  · exact B1807007
  · exact B1807011
  · exact B1807015
  · exact B1807019
  · exact B1807023
  · exact B1807027
  · exact B1807031
  · exact B1807035
  · exact B1807039
  · exact B1807043
  · exact B1807047
  · exact B1807051
  · exact B1807055
  · exact B1807059
  · exact B1807063
  · exact B1807067
  · exact B1807071
  · exact B1807075
  · exact B1807079
  · exact B1807083
  · exact B1807087
  · exact B1807091
  · exact B1807095
  · exact B1807099
  · exact B1807103
  · exact B1807107
  · exact B1807111
  · exact B1807115
  · exact B1807119
  · exact B1807123
  · exact B1807127
  · exact B1807131
  · exact B1807135
  · exact B1807139
  · exact B1807143
  · exact B1807147
  · exact B1807151
  · exact B1807155
  · exact B1807159
  · exact B1807163
  · exact B1807167
  · exact B1807171
  · exact B1807175
  · exact B1807179
  · exact B1807183
  · exact B1807187
  · exact B1807191
  · exact B1807195
  · exact B1807199
  · exact B1807203
  · exact B1807207
  · exact B1807211
  · exact B1807215
  · exact B1807219
  · exact B1807223
  · exact B1807227
  · exact B1807231
  · exact B1807235
  · exact B1807239
  · exact B1807243
  · exact B1807247
  · exact B1807251
  · exact B1807255
  · exact B1807259
  · exact B1807263
  · exact B1807267
  · exact B1807271
  · exact B1807275
  · exact B1807279
  · exact B1807283
  · exact B1807287
  · exact B1807291
  · exact B1807295
  · exact B1807299
  · exact B1807303
  · exact B1807307
  · exact B1807311
  · exact B1807315
  · exact B1807319
  · exact B1807323
  · exact B1807327
  · exact B1807331
  · exact B1807335
  · exact B1807339
  · exact B1807343
  · exact B1807347
  · exact B1807351
  · exact B1807355
  · exact B1807359
  · exact B1807363
  · exact B1807367
  · exact B1807371
  · exact B1807375
  · exact B1807379
  · exact B1807383
  · exact B1807387
  · exact B1807391
  · exact B1807395
  · exact B1807399
  · exact B1807403
  · exact B1807407
  · exact B1807411
  · exact B1807415
  · exact B1807419
  · exact B1807423
  · exact B1807427
  · exact B1807431
  · exact B1807435
  · exact B1807439
  · exact B1807443
  · exact B1807447
  · exact B1807451
  · exact B1807455
  · exact B1807459
  · exact B1807463
  · exact B1807467
  · exact B1807471
  · exact B1807475
  · exact B1807479
  · exact B1807483
  · exact B1807487
  · exact B1807491
  · exact B1807495
  · exact B1807499
  · exact B1807503
  · exact B1807507
  · exact B1807511
  · exact B1807515
  · exact B1807519
  · exact B1807523
  · exact B1807527
  · exact B1807531
  · exact B1807535
  · exact B1807539
  · exact B1807543
  · exact B1807547
  · exact B1807551
  · exact B1807555
  · exact B1807559
  · exact B1807563
  · exact B1807567
  · exact B1807571
  · exact B1807575
  · exact B1807579
  · exact B1807583
  · exact B1807587
  · exact B1807591
  · exact B1807595
  · exact B1807599
  · exact B1807603

theorem solution (m : ℕ) (hlo : 1805604 ≤ m) (hhi : m ≤ 1807604) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 451401 ≤ j := by omega
    have hj2 : j ≤ 451900 := by omega
    have hb : Blo 1805604 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
